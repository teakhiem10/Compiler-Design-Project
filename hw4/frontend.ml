open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

let string_of_ctxt (c:Ctxt.t) : string = 
  let helper (id, (ty, op)) : string = 
    Printf.sprintf "%s: %s %s" id (Llutil.string_of_ty ty) (Llutil.string_of_operand op)
  in List.map helper c |> String.concat "\n"

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

     *)
let cmp_bop (bop:Ast.binop) :Ll.bop = 
  match bop with
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | And -> And
  | Or -> Or
  | IAnd -> And
  | IOr -> Or
  | Shl -> Shl
  | Shr -> Lshr
  | Sar -> Ashr
  | _ -> failwith "Not a valid bop!"

let cmp_condition (bop:Ast.binop) : Ll.cnd = 
  match bop with 
  | Eq -> Eq
  | Neq -> Ne
  | Lt -> Slt
  | Lte -> Sle
  | Gt -> Sgt
  | Gte -> Sge
  | _ -> failwith "Not a valid condition!"


let handle_bop (bop:Ast.binop) (rt:Ast.ty) (o1:operand) (o2:operand) : Ll.insn = 
  let (t1,t2,_) = typ_of_binop bop in
  match bop with
  | Add | Sub | Mul | And | Or | IAnd | IOr | Shl | Shr | Sar -> 
    Binop (cmp_bop bop, cmp_ty rt, o1, o2)
  | Eq | Neq | Lt | Lte | Gt | Gte -> 
    Icmp (cmp_condition bop, cmp_ty t1, o1, o2)

let handle_call (cmp_exp:(exp node -> (Ll.ty * Ll.operand * stream))) (f:Ast.exp node) (args: Ast.exp node list) (op:id) : (Ll.ty * stream) = 
  let f_ty, f_op, f_stream = cmp_exp f in
    begin match f_ty with
    | Ptr (Fun (_,fty)) -> 
      let compiled_args = List.map cmp_exp args in 
      let compiled_ops = List.map (fun (ty, op, _) -> (ty, op)) compiled_args in
      let streams = List.map (fun (_,_,strm) -> strm) compiled_args |> List.flatten in
      fty, streams >@ f_stream >@ [I (op, Call (fty, f_op, compiled_ops))]
    | _ -> failwith "Not a valid function type"
    end

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  let (resty,resop,resstream) =
  match exp.elt with
  | CNull rty -> Ptr (cmp_rty rty), Null, []
  | CInt i -> I64, Const i, []
  | CBool b -> I1, Const (if b then 1L else 0L), []
  | CStr s -> 
    let ty = Array (String.length s + 1, I8) in
    let tempstr = gensym "tempstr" in
    let convert = gensym "bcaststr" in
    let idstr = gensym "s" in
    let bitcaststr = [G (convert, (Ptr I8,(GBitcast (Ptr ty, GGid tempstr, Ptr I8))))] in
    (Ptr I8), Id idstr, [G (tempstr, (ty, GString s))] >@ bitcaststr >@ [I (idstr,Load (Ptr (Ptr I8) ,Gid convert))]
  | CArr (ty, elm_exps) -> let arr = gensym "tmparr" in
                            let raw_arr = gensym "rawarr" in
                            let arr_ty = Struct [I64; Array (0, cmp_ty ty)] in
                            let compiled_exps = List.map (cmp_exp c) elm_exps in
                            let elm_ops = List.map (fun (_,o,_) -> o) compiled_exps in
                            let elm_streams = List.map (fun (_,_,s) -> s) compiled_exps |> List.flatten in
                            let assn_stream = List.mapi (fun i -> fun op -> 
                              let index_id = gensym "index" in
                              [
                                I ("", Store (cmp_ty ty, op, Id index_id));
                                I (index_id, Gep (Ptr arr_ty, Id arr, [Const 0L; Const 1L; Const (Int64.of_int i)]));
                                ]) elm_ops |> List.flatten in
                            (Ptr arr_ty, Id arr,[
                              I (arr, Bitcast (Ptr I64, Id raw_arr, Ptr arr_ty)); 
                              I (raw_arr, Call (Ptr (I64), Gid "oat_alloc_array", [I64, Const (Int64.of_int @@ List.length elm_exps)]));
                            ] >@ elm_streams >@ assn_stream)
  | NewArr (ty, length_exp) -> 
    let tmp_arr = gensym "tmparr" in
    let raw_arr = gensym "rawarr" in
    let arr_ty = Struct [I64; Array (0, cmp_ty ty)] in
    let len_ty, len_op, len_strm = cmp_exp c length_exp in
    (Ptr (arr_ty), Id tmp_arr, len_strm >@ [
      I (tmp_arr, Bitcast (Ptr I64, Id raw_arr, Ptr arr_ty)); 
      I (raw_arr, Call (Ptr (I64), Gid "oat_alloc_array", [len_ty, len_op]))
    ])
  | Index (arr_exp, index_exp) -> 
    let index_id = gensym "index" in
    let id = gensym "arr_val" in
    let arr_ty, arr_op, arr_strm = cmp_exp c arr_exp in
    let index_ty, index_op, index_strm = cmp_exp c index_exp in
    begin match arr_ty with
    | Ptr (Struct [I64; Array (0, ty)]) -> 
      (ty, Id id, arr_strm >@ index_strm >@ [
        I (id, Load (Ptr ty, Id index_id));
        I (index_id, Gep (Ptr (Struct [I64; Array (0, ty)]), arr_op, [Const 0L; Const 1L; index_op]))
      ])
    | _ -> print_endline @@ string_of_ctxt c; failwith (Printf.sprintf "not a valid array type for indexing: %s, %s" (string_of_ty arr_ty) (Astlib.string_of_exp arr_exp))
    end
  | Id i -> 
    let ty, op = Ctxt.lookup i c in
    begin match op with
    | Id _ -> 
      let id = gensym i in
      ty, Id id, [I (id, Load (Ptr ty, op))]
    | Gid _ ->
      begin match ty with
      | Ptr (Fun _) -> ty, op, []
      | _ ->
        let id = gensym i in
        ty, Id id, [I (id, Load (Ptr ty, op))]
      end
    | _ -> ty, op, []
    end
  | Call (fn_exp, args) -> 
      let op = gensym "call_result" in
    let f_ty, f_stream = handle_call (cmp_exp c) fn_exp args op in
    f_ty, Id op, f_stream
  | Bop (bop, e1, e2) -> 
    let _, _, rt = typ_of_binop bop in
    let _, o1, s1 = cmp_exp c e1 in
    let _, o2, s2 = cmp_exp c e2 in
    let op = gensym "x" in
    let insn = handle_bop bop rt o1 o2 in
    cmp_ty rt, Id op, s1 >@ s2 >@ [I (op, insn)]
  | Uop (op, e) -> let _, rt = typ_of_unop op in
                   let _, o, s = cmp_exp c e in
                   let t = cmp_ty rt in
                   let temp = gensym "a" in 
                    begin match op with
                    | Neg -> t, Id temp, s >@ [I (temp, Binop (Sub, t, (Const 0L), o))]
                    | Lognot -> t, Id temp, s >@ [I (temp, Icmp (Eq, t, (Const 0L), o))]
                    | Bitnot -> t, Id temp, s >@ [I (temp, Binop (Xor, t, (Const Int64.max_int), o))]
                    end
  | _ -> failwith "cmp_exp not implemented"
  in
  match resop with
              | Gid i -> let (_,oper) = Ctxt.lookup i c in 
                        (resty, oper, resstream)
              | _ -> (resty, resop, resstream)


(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)


let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  (*print_endline @@ string_of_ctxt c;*)
  match stmt.elt with 
  | Assn (p,e) -> let (ty,op1,s) = cmp_exp c e in 
                  let op = begin match op1 with
                            | Gid i -> let (typeret,ret) = Ctxt.lookup i c in
                                        ret
                            | _ -> op1
                           end 
                    in
                    begin match p.elt with
                    | Id id -> let (_,store_op) = Ctxt.lookup id c in
                                begin match store_op with
                                | Gid _ -> c,s >@ [I ("", Store (ty, op, Gid id))]
                                | _ -> c,s >@ [I ("", Store (ty, op, store_op))]
                                end
                    | Index (arr, index) -> 
                      let arr_ty, arr_op, arr_strm = cmp_exp c arr in
                      let index_ty, index_op, index_strm = cmp_exp c index in
                      let arr_index = gensym "arr_index" in
                      c, s >@ arr_strm >@ index_strm >@ [I ("", Store (ty, op, Id arr_index)); I (arr_index, Gep (arr_ty, arr_op, [Const 0L; Const 1L; index_op]))]
                    | _ -> failwith ("not a valid lhs to assignment: " ^ (Astlib.string_of_exp p))
                    end
  | Ret e_opt -> begin 
      match e_opt with 
      | None -> c, [T (Ret (Void, None))]
      | Some exp -> let ty, op, s = cmp_exp c exp in 
                      match op with
                      | Gid i -> let (ty1,ret) =(Ctxt.lookup i c) in
                             c, s >@ [(T (Ret (ty1, Some ret)))]
                      | _ -> c, s >@ [(T (Ret (ty, Some op)))]
    end
  | Decl (id, exp) -> let ty, op, s = cmp_exp c exp in 
                      (Ctxt.add c id (ty, Id id)), s >@ [I (id, Store (ty, op, Id id));E (id, (Alloca ty));]
  | SCall (f, args) -> 
    let v_call = gensym "void_call" in
    let _, f_stream = handle_call (cmp_exp c) f args v_call in 
    c, f_stream
  | If (e, b1, b2) ->  cmp_if c rt (e,b1,b2)
  | While (e,b) -> cmp_while c rt (e,b)
  | For (v, e, cond, b) -> cmp_for c rt (v, e, cond, b)

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts
(*compiles if-statements*)
and cmp_if (c:Ctxt.t) (rt:Ll.ty)  ((e, b1, b2):exp node * stmt node list * stmt node list): Ctxt.t * stream = 
      let (ty, op, s_e) = cmp_exp c e in
      let ifs = gensym "if" in
      let el = gensym "else" in
      let end_if = gensym "end" in
      let (c1,s1) = cmp_block c rt b1 in 
      let (c2,s2) = cmp_block c1 rt b2 in 
      let end_if_stream = [(T (Br end_if))] in 
      let if_block = [(L ifs)] >@ s1 >@ end_if_stream in
      let else_block = [(L el)] >@ s2 >@ end_if_stream in
      let end_lbl = [(L end_if)] in
      let s1_term = match s1 with | [] -> None | l -> Some (List.hd s1) in
      let end_stream:stream = begin match s2 with
                                | [] -> []
                                | _ -> let s2_term = List.hd s2 in
                                       begin match (s1_term, s2_term) with
                                          |  (Some T(Ret (Void, None)), T(Ret (Void, None))) -> [(T (Ret (Void, None)))]
                                          | (Some T (Ret (s1ty, Some s1op) ), T(Ret (_, Some _))) -> [(T (Ret (s1ty, Some s1op)))]
                                          | _ -> []
                                        end
                                end
      in
      if s2 = [] then
        c2, s_e >@ [T (Cbr (op, ifs, end_if))] >@ if_block >@ end_lbl
      else
        c2, s_e >@ [T (Cbr (op, ifs, el))] >@ if_block >@ else_block >@ end_lbl >@ end_stream
and cmp_while (c:Ctxt.t) (rt:Ll.ty) ((e, b):exp node * stmt node list): Ctxt.t * stream = 
      let (ty, op, s_e) = cmp_exp c e in
      let wh = gensym "while" in
      let stmtb = gensym "stm_block" in
      let end_wh = gensym "end" in
      let (c1,s_b) = cmp_block c rt b in 
      let wh_block = [T (Br wh)] >@ [(L wh)] >@ s_e >@ [T (Cbr (op, stmtb, end_wh))] in
      let stmt_block = [(L stmtb)] >@s_b >@ [T (Br (wh))] in
      let end_lbl = [(L end_wh)] in
      c1, wh_block >@ stmt_block >@ end_lbl
      
and cmp_for (c:Ctxt.t) (rt:Ll.ty) ((vlist, e, st_change, b): vdecl list * exp node option * stmt node option * stmt node list): Ctxt.t * stream = 
  let for_entry_lbl = gensym "forentry" in
  let helper ((helpc, st): Ctxt.t * stream ) ((idh,exh): vdecl) : Ctxt.t * stream =
    let idh_lbl = gensym idh in
    let (help_exp_ty, help_exp_op, helps) = cmp_exp c exh in
    let helpstream = [I (idh_lbl,Alloca help_exp_ty)] >@ [I ("", Store (help_exp_ty, help_exp_op, Id idh_lbl))] in
    (Ctxt.add helpc idh (help_exp_ty,Id idh_lbl)), st >@ helps >@ helpstream
  in
  let (forctxt, vdecl_stream) = List.fold_left helper (c,[]) vlist in
  let for_entry_stream = [T (Br for_entry_lbl)] >@ [L for_entry_lbl] >@ vdecl_stream in
  let stmt_avail = match st_change with
  | None -> []
  | Some a -> [a] in
  let (_,for_blocks_stream) = begin match e with
                                              | None -> cmp_while forctxt rt ({elt = (CBool true); loc = ("",(0,0),(0,0)) }, b @ stmt_avail)
                                              | Some a ->  cmp_while forctxt rt (a, b @ stmt_avail)
                                              end 
      in 
  (*print_endline @@ string_of_ctxt forctxt;*)
  c, for_entry_stream >@ for_blocks_stream

      (* Adds each function identifer to the context at an
        appropriately translated type.  

        NOTE: The Gid of a function is just its source name
      *)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
        let ft = TRef (RFun (List.map fst args, frtyp)) in
        Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  let helper (c:Ctxt.t) (d:Ast.decl) : Ctxt.t = 
    begin match d with
    | Gfdecl _ -> c
    | Gvdecl {elt; _} -> 
      let id = elt.name in 
      let rhs = begin match elt.init.elt with
      | CNull rty -> 
        begin match rty with 
        | RArray _ -> Ptr (cmp_rty rty), Gid id
        | _ -> cmp_rty rty, Gid id
        end
      | CBool _ -> I1, Gid id
      | CInt _ -> I64, Gid id
      | CStr _ -> Ptr I8, Gid id
      | CArr (ty, _) -> Ptr (Struct [I64; Array (0, cmp_ty ty)]), Gid id
      | _ -> failwith @@ Astlib.string_of_exp elt.init
      end in
      Ctxt.add c id rhs
    end
    in
  List.fold_left helper c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

 let rec find_strings_exp (e:exp node) : (string list) = 
  match e.elt with
  | CNull _ | CBool _ | CInt _ -> []
  | CStr s -> [s]
  | CArr (_, els) -> List.map find_strings_exp els |> List.flatten
  | NewArr (_, exp) -> find_strings_exp exp
  | Call (_, args) -> List.map find_strings_exp args |> List.flatten
  | _ -> []

let find_strings (statement:stmt node) : (string list) = 
  match statement.elt with 
  | Assn (_, e) | Decl (_, e) | Ret (Some e) -> find_strings_exp e
  | SCall (_, args)-> List.map find_strings_exp args |> List.flatten
  | _ -> []

let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let fn = f.elt in
  let compiled_args = List.map (fun (ty, id) -> (id, (cmp_ty ty, gensym id))) fn.args in
  let new_ctxt = List.fold_left (fun ctxt -> fun (oat_id, (ty, llvm_id)) -> Ctxt.add ctxt oat_id (ty, Id llvm_id)) c compiled_args in
  let allocas = List.map (fun (id, (ty, operand)) -> [E (operand, Store (ty, Id id, Id operand)); E (operand, Alloca ty)]) compiled_args |> List.flatten in
  let newer_ctxt = List.map find_strings fn.body |> List.flatten |> List.fold_left (fun ctxt -> fun s -> Ctxt.add ctxt s (Ptr I8, Gid (gensym "str"))) new_ctxt in
  let block_ctxt, block_stream = cmp_block newer_ctxt (cmp_ret_ty fn.frtyp) fn.body in
  let cfg, _ = cfg_of_stream (block_stream >@ allocas >:: T (Ret (Void, None))) in
  (*List.iter (fun elt -> match elt with | G (gid, gdecl) -> print_endline @@ Printf.sprintf "%s: %s" gid (string_of_gdecl gdecl) | _ -> ()) block_stream;*)
  {
    f_ty = List.map (fun (ty, _) -> cmp_ty ty) fn.args, cmp_ret_ty fn.frtyp; 
    f_param = List.map snd f.elt.args; 
    f_cfg = cfg
  }, List.filter_map (fun elt -> match elt with | G (gid, gdecl) -> Some (gid, gdecl) | _ -> None) block_stream
  (*failwith "cmp_fdecl not implemented"*)

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with 
  | CNull rty -> begin match rty with 
    | RArray ty -> (Ptr (Struct [I64; Array (0, cmp_ty ty)]), GNull), []
    | RString -> (Ptr I8, GNull), []
    | _ -> (cmp_rty rty, GNull), []
    end
  | CBool b -> (I1, GInt (if b then 1L else 0L)), []
  | CInt i -> (I64, GInt i), []
  | CStr s -> let gl_string = gensym "gstr" in
              let type_str = Array (String.length s + 1, I8) in
                ((Ptr I8), GBitcast (Ptr type_str,GGid gl_string, Ptr I8)), [(gl_string,((type_str, GString s)))]
  | CArr (ty, arr_exp) -> 
      let gl_arr = gensym "garr" in
      let arr_ty = Struct [I64; Array (0, cmp_ty ty)] in
      let arr_ty_num = Struct [I64; Array (List.length arr_exp, cmp_ty ty)] in
      let compiled_exps = List.map (cmp_gexp c) arr_exp in
      let arg_decls = List.map fst compiled_exps in
      let additional_decls = List.map snd compiled_exps |> List.flatten in
      (Ptr arr_ty, GBitcast (Ptr arr_ty_num, GGid gl_arr, Ptr arr_ty)), 
      [(gl_arr, (arr_ty_num, GStruct [I64, GInt (Int64.of_int @@ List.length arr_exp); Array (List.length arr_exp, cmp_ty ty), GArray (arg_decls)]))] >@ additional_decls
  | _ -> failwith "Not valid gexp"

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
