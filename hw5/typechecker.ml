open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))

let subtype_error (l : 'a node) (t1:ty) (t2:ty) =
  type_error l (Printf.sprintf "%s not a subtype of %s" (string_of_ty t1) (string_of_ty t2))

(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

let string_of_fields (fs:field list) : string = 
  "{" ^ 
  (List.map (fun {fieldName=id;ftyp=ty} -> Printf.sprintf "%s: %s" id (string_of_ty ty)) fs|> String.concat ", ") ^ 
  "}"


let string_of_id_tuple (f : 'a -> string) (lst : (id * 'a) list) : string =
  List.map (fun (id, x) -> Printf.sprintf "%s: %s" id (f x)) lst |> String.concat "\n"

let string_of_ctxt ({locals=l; globals=g; structs=s}:Tctxt.t) : string = 
  let l_str = string_of_id_tuple string_of_ty l in 
  let g_str = string_of_id_tuple string_of_ty g in
  let s_str = string_of_id_tuple string_of_fields s in
  String.concat "\n\n" [l_str; g_str; s_str]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
   - assumes that H contains the declarations of all the possible struct types

   - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)

(*take the first n elements in the list*)
let rec split_list (a:'a list) (n:int) : 'a list= 
  match a,n with
  | [], _ -> []
  | _, 0 -> []
  | (x::xs),_ -> x :: split_list xs (n-1)

let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1,t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TRef tref1, TRef tref2 -> subtype_ref c tref1 tref2
  | TNullRef tref1, TNullRef tref2 -> subtype_ref c tref1 tref2
  | TRef tref1, TNullRef tref2 -> subtype_ref c tref1 tref2
  | _  -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true
  | RArray t1, RArray t2 -> t1 = t2
  | RStruct id1, RStruct id2 -> let struct1 = Tctxt.lookup_struct id1 c in
                                let struct2 = Tctxt.lookup_struct id2 c in
                                subtype_struct struct1 struct2
  | RFun (args1,ret1), RFun (args2,ret2) -> let subtype_args = fun l1 l2 -> List.fold_right (subtype_fun c) (List.combine l1 l2) true in
                                            let subtype_ret = subtype_rty c ret1 ret2 in
                                        (List.length args1 == List.length args2) && (subtype_args args2 args1) && subtype_ret
  | _ -> false
and subtype_fun (c:Tctxt.t) ((t1,t2):Ast.ty * Ast.ty) (b:bool) : bool = 
  let check_type = (subtype c t1 t2) in
  (*(if not check_type then
    print_endline @@ (Astlib.string_of_ty t1) ^ " " ^ (Astlib.string_of_ty t1));*)
  check_type && b
and subtype_rty (c:Tctxt.t) (rty1 : Ast.ret_ty) (rty2 : Ast.ret_ty) : bool = 
  match rty1,rty2 with
  | RetVoid, RetVoid -> true
  | RetVal t1, RetVal t2 -> subtype c t1 t2
  | _ -> false
and subtype_struct (f1:Ast.field list) (f2:Ast.field list): bool = 
  let check_length = List.length f1 >= List.length f2 in
  let check_same = fun (x) (y) -> x=y in
  let hd_part = fun x -> split_list x (List.length f2) in
  check_length && List.for_all2 check_same (hd_part f1) f2



(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

   - the function should succeed by returning () if the type is well-formed
      according to the rules

   - the function should fail using the "type_error" helper function if the 
      type is not well-formed

   - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

   - tc contains the structure definition context
*)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt -> ()
  | TBool -> ()
  | TRef refty-> typecheck_rty l tc refty
  | TNullRef refty -> typecheck_rty l tc refty

and typecheck_rty(l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray tarr -> typecheck_ty l tc tarr
  | RFun (tlist,retty) -> List.iter (typecheck_ty l tc) tlist;
    typecheck_ret_ty l tc retty
  | RStruct sid -> let struct1 = Tctxt.lookup_struct_option sid tc in 
    match struct1 with
    | None -> type_error l (Printf.sprintf "Struct %s not found" sid)
    | Some _ -> ()
and typecheck_ret_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal t -> typecheck_ty l tc t
(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)
let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull t -> typecheck_rty e c t;
    TNullRef t
  | CInt _-> TInt
  | CBool _ -> TBool
  | CStr _ -> TRef RString
  | Id id -> let ctxtlook = lookup_option id c in
    begin match ctxtlook with
      | Some t -> typecheck_ty e c t; t
      | None -> type_error e ("Id not found in context: " ^ id)
    end
  | CArr (ty, exps) -> 
    let exp_tys = List.map (typecheck_exp c) exps in
    List.iter (fun exp_ty -> 
        if subtype c exp_ty ty then () 
        else subtype_error e exp_ty ty)
      exp_tys;
    TRef (RArray ty)
  | NewArr (ty, len_exp, id, gen_exp) -> 
    begin match lookup_local_option id c with
      | Some _ -> type_error e (id ^ " Already defined in this context")
      | None -> 
        let len_ty = typecheck_exp c len_exp in
        begin match len_ty with
          | TInt -> 
            let gen_ty = typecheck_exp (add_local c id TInt) gen_exp in 
            if subtype c gen_ty ty then () else subtype_error e gen_ty ty;
            TRef (RArray ty)
          | _ -> type_error len_exp "length is not of type TInt"
        end
    end 
  | Index (arr_exp, index_exp) -> 
    begin match typecheck_exp c index_exp with
      | TInt -> 
        let arr_ty = typecheck_exp c arr_exp in
        begin match arr_ty with
          | TRef (RArray ty) -> ty
          | _ -> type_error arr_exp @@ "Array expression is not of an array type: " ^ (Astlib.string_of_ty arr_ty)
        end
      | _ -> type_error index_exp "index expression is not of type TInt"
    end
  | Length arr_exp -> 
    begin match typecheck_exp c arr_exp with
      | TRef (RArray _) -> TInt
      | TNullRef(RArray _) -> TInt
      | _ -> type_error arr_exp @@ "Array expression is not of an array type, Exp: " ^ Astlib.string_of_exp arr_exp
              ^ " ty: " ^ (Astlib.string_of_ty @@typecheck_exp c arr_exp)
    end
  | CStruct (id, named_exps) -> 
    begin match lookup_struct_option id c with
      | Some styp -> 
        if List.length styp = List.length named_exps then () else type_error e "Wrong number of struct fields";
        let sorted_struct_fields = List.sort (fun f1 -> fun f2 -> String.compare f1.fieldName f2.fieldName) styp in
        let sorted_named_exps = List.sort (fun (id1, _) -> fun (id2, _) -> String.compare id1 id2) named_exps in
        List.iter2 (fun {fieldName = fieldName; ftyp = fieldType} -> fun (exp_id, exp) -> 
            if not @@ String.equal fieldName exp_id then type_error e (Printf.sprintf "Could not find attribute %s of struct %s" exp_id id)
            else 
              let exp_ty = typecheck_exp c exp in
              if subtype c exp_ty fieldType then () else
                subtype_error exp exp_ty fieldType) 
          sorted_struct_fields sorted_named_exps;
        TRef (RStruct id)
      | None -> type_error e ("Could not find struct named " ^ id)
    end
  | Proj (s_exp, field_id) -> 
    let styp = typecheck_exp c s_exp in
    begin match styp with
      | TRef (RStruct sid) -> 
        begin match lookup_field_option sid field_id c with
          | None -> type_error e (Printf.sprintf "Could not find field called %s in struct %s" field_id sid)
          | Some field_ty -> field_ty
        end
      | _ -> type_error e "Tried to projec of a non-struct type"
    end
  | Call (f_exp, arg_exps) -> 
    let ftype = typecheck_exp c f_exp in
    let supplied_arg_types = List.map (typecheck_exp c) arg_exps in
    begin match ftype with 
      | TRef (RFun (arg_types, RetVal t_ret)) ->  
        if (List.length arg_types) = (List.length supplied_arg_types) then () else type_error e "Wrong number of arguments";
        List.iter2 (fun supp_ty -> fun ty -> if subtype c supp_ty ty then () else subtype_error e supp_ty ty) supplied_arg_types arg_types;
        t_ret
      | _ -> type_error f_exp "Not a valid function type"
    end
  | Bop (bop, e1, e2) -> 
    let t1 = typecheck_exp c e1 in
    let t2 = typecheck_exp c e2 in
    begin match bop with
      | Eq | Neq -> 
        if subtype c t1 t2 then 
          if subtype c t2 t1 then TBool
          else subtype_error e t2 t1
        else subtype_error e t1 t2
      | _ -> 
        let (bt1, bt2, btret) = typ_of_binop bop in
        if (t1 = bt1 ) && (t2 = bt2) then btret 
        else type_error e "Types do not match the binary expression"
    end
  | Uop (uop, exp) ->
    let (ut, t_ret) = typ_of_unop uop in
    let exp_ty = typecheck_exp c exp in
    if ut = exp_ty then t_ret else type_error exp "Wrong type for unary expression"

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.  

   Inputs:
   - tc: the type context
   - s: the statement node
   - to_ret: the desired return type (from the function declaration)

   Returns:
   - the new type context (which includes newly declared variables in scope
       after this statement
   - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.

        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)
let rec get_id (e: Ast.exp node) : id = 
  begin match e.elt with 
                | Id i -> i
                | Index (idarr,ind)-> get_id idarr
                | Proj (id1,id2) -> get_id id1
                  (* need to somehow rule out global functions here *)     
                | _ -> type_error e "Invalid lhs of assignment"
    end 

let rec typecheck_block: 'a. Tctxt.t -> block -> ret_ty -> 'a Ast.node -> Tctxt.t * bool = 
  fun (tc : Tctxt.t) (b : block) (ret_ty:ret_ty) (l : 'a Ast.node) ->
  let helper ((c, r):Tctxt.t * bool) (stmt : stmt node) : (Tctxt.t * bool) = begin
    if r then type_error l "Early return not allowed" else ();
    let new_ctxt, returns = typecheck_stmt c stmt ret_ty in
    new_ctxt, returns || r
  end
  in
  List.fold_left helper (tc, false) b
and typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  match s.elt with 
  | Assn (lhs_exp, rhs_exp) ->
    let lhs_ty = typecheck_exp tc lhs_exp in
    let rhs_ty = typecheck_exp tc rhs_exp in
    let lhsid = get_id lhs_exp in
    (*print_endline @@ "Assn:";
    print_endline @@ "lhs: " ^ Astlib.string_of_exp lhs_exp ^ ", rhs: " ^ Astlib.string_of_exp rhs_exp;
    print_endline @@ "lhs: " ^ Astlib.string_of_ty lhs_ty ^ ", rhs: " ^ Astlib.string_of_ty rhs_ty;*)
    (*check if it has a local or global id*)
    if((lookup_local_option lhsid tc) = None && not(lookup_global_option lhsid tc = None && lookup_struct_option lhsid tc = None)) then 
      type_error s @@ "lhs doesn't have local declaration and not global definition, lhs: " ^ (Astlib.string_of_exp lhs_exp);
    if subtype tc rhs_ty lhs_ty then tc, false 
    else type_error s @@ "rhs is not a subtype of lhs in assignment, lhs: " ^ (Astlib.string_of_ty lhs_ty) ^ ", rhs: " ^ (Astlib.string_of_ty rhs_ty)
  | Decl (id, exp) ->
    begin match lookup_local_option id tc with
    | Some _ -> type_error s "Cannot redeclare local variable"
    | None -> 
      let exp_ty = typecheck_exp tc exp in
      (*print_endline @@ "Decl: ";
      print_endline @@ "exp: " ^ Astlib.ml_string_of_exp exp;
      print_endline @@ "ty: " ^ Astlib.string_of_ty exp_ty;*)
      add_local tc id exp_ty, false  
    end
  | Ret e -> begin match e, to_ret with
      | None, RetVoid -> tc, true
      | Some exp, RetVal ty -> 
        let exp_ty = typecheck_exp tc exp in
        if subtype tc exp_ty ty then tc, true 
        else type_error s "expression type is not subtype of declared return type"
      | _, _ -> type_error s "Void and expression mismatch in return statement"
    end
  | SCall (f_exp, arg_exps) -> 
    let f_ty = typecheck_exp tc f_exp in
    let arg_tys = List.map (typecheck_exp tc) arg_exps in
    begin match f_ty with 
      | TRef (RFun (reported_arg_tys, RetVoid)) -> 
        List.iter2 (fun arg_ty -> fun rep_ty -> 
            if subtype tc arg_ty rep_ty then ()
            else subtype_error s arg_ty rep_ty) arg_tys reported_arg_tys; 
        tc, false
      | _ -> type_error s "Not a valid function to call"
    end
  | If (cond_exp, b1, b2) ->
    if (typecheck_exp tc cond_exp) = TBool then begin
      let _,b1_r = typecheck_block tc b1 to_ret s in
      let _,b2_r = typecheck_block tc b2 to_ret s in
      tc, b1_r && b2_r
    end
    else type_error s "Condition is not of type TBool in if-statement"
  | Cast (target_ty, id, rhs_exp, b1, b2) ->
    let rhs_ty = typecheck_exp tc rhs_exp in
    begin match rhs_ty with
      | TNullRef rhs_rty -> 
        if subtype_ref tc rhs_rty target_ty then
          let new_tctxt = add_local tc id (TRef target_ty) in
          let tc1,b1_r = typecheck_block new_tctxt b1 to_ret s in
          let tc2,b2_r = typecheck_block tc1 b2 to_ret s in
          tc2, b1_r && b2_r
        else subtype_error s (TRef rhs_rty) (TRef target_ty)
      | _ -> type_error s "rhs is not ref?"
    end
  | For (vdecls, exp_opt, stmt_opt, b) ->
    begin match exp_opt, stmt_opt with
      | Some e, Some stmt ->
        let new_tctxt = List.fold_left (fun c (id, exp) -> add_local c id (typecheck_exp tc exp)) tc vdecls in
        let exp_ty = typecheck_exp new_tctxt e in
        if exp_ty = TBool then 
          let _, returns = typecheck_stmt new_tctxt stmt to_ret in
          if returns then type_error s "Cannot return in for statement"
          else let _ = typecheck_block new_tctxt b to_ret s in
            tc, false
        else type_error s "Expression in for loop must be type TBool"
      | _, _ -> type_error s "Only uspport full for-loop variant"
    end
  | While (cond_exp, b) ->
    let cond_ty = typecheck_exp tc cond_exp in
    if cond_ty = TBool then 
      let _ = typecheck_block tc b to_ret s in 
      tc, false
    else type_error s "Condition expression does not have type TBool in While"

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
*)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
   - extends the local context with the types of the formal parameters to the 
      function
   - typechecks the body of the function (passing in the expected return type
   - checks that the function actually returns
*)

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let f_tc = List.fold_left (fun c -> fun (ty, id) -> add_local c id ty) tc f.args in
  if snd @@ typecheck_block f_tc f.body f.frtyp l then () else type_error l "Function does not return"

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let helper (c:Tctxt.t) (decl:decl) : Tctxt.t = 
    begin match decl with 
      | Gvdecl _ | Gfdecl _ -> c
      | Gtdecl ({elt=(id, fields);_} as l) -> 
        begin match lookup_struct_option id c with
        | Some _ -> type_error (no_loc decl) "Struct with this name already exists"
        | None -> 
          let new_ctxt = Tctxt.add_struct c id fields in
          typecheck_tdecl new_ctxt id fields l;
          new_ctxt
        end
    end in
  List.fold_left helper Tctxt.empty p

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let helper (c:Tctxt.t) (decl:decl) : Tctxt.t = 
    begin match decl with
      | Gvdecl _ | Gtdecl _ -> c
      | Gfdecl ({elt={frtyp=ret_ty; fname=id; args=args;_};_} as l) -> 
        begin match lookup_global_option id c with
          | Some _ -> type_error l "duplicated function name"
          | None ->  
            let arg_fields = List.map (fun (ty, id) -> {fieldName=id; ftyp=ty}) args in
            typecheck_tdecl c id arg_fields l;
            let arg_types = List.map fst args in
            add_global c id (TRef (RFun (arg_types, ret_ty)))
        end
    end in
  let builtins_p = List.map (fun (id, (arg_tys, ret_ty)) -> Gfdecl (no_loc {frtyp=ret_ty; fname=id; args=List.mapi (fun i ty -> (ty, string_of_int i)) arg_tys; body=[]})) builtins in
  List.fold_left helper tc (p @ builtins_p) 

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let helper (c:Tctxt.t) (decl:decl) : (Tctxt.t) = 
    begin match decl with
      | Gfdecl _ | Gtdecl _ -> c
      | Gvdecl ({elt={name=id; init=init_exp};_} as l) -> 
        begin match lookup_global_option id c with
          | Some _ -> type_error l (Printf.sprintf "global declaration %s arleady exists" id)
          | None -> Tctxt.add_global c id (typecheck_exp tc init_exp)
        end
    end
  in
  List.fold_left helper tc p


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  (*print_endline @@ string_of_ctxt tc;*)
  List.iter (fun p ->
      match p with
      | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
      | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
      | _ -> ()) p
