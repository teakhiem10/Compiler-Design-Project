(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Helper registers to use to store temporary results*)

let temp1 = Reg Rax
let temp2 = Reg Rcx

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge

let string_of_ll_operand (op:Ll.operand) : string = 
  match op with 
  | Null -> "Null"
  | Const num -> Int64.to_string num
  | Gid gid -> Printf.sprintf "Gid %s" gid
  | Id uid -> Printf.sprintf "Uid %s" uid

(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be represented
   in 64 bit. This greatly simplifies code generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

let string_of_layout (l:layout) : string = 
  Printf.sprintf "Layout: %s" (String.concat ", " (List.map (fun a -> fst a ^ ": " ^ (string_of_operand (snd a))) l))
(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  function op -> 
    begin match op with
      | Null -> (Movq, [(Imm (Lit 0L)); dest])
      | Const x -> (Movq, [Imm (Lit x); dest]) 
      | Gid glbl -> let gid = (Platform.mangle glbl) in 
        let o = Ind3 (Lbl gid, Rip) in
        (Leaq, [o; dest])
      | Id x -> let operandLL_in_x86 = lookup ctxt.layout x in 
        (Movq, [operandLL_in_x86; dest])
    end

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)

let arg_loc (n : int) : operand =
  begin match n with
    | 0 -> Reg Rdi
    | 1 -> Reg Rsi
    | 2 -> Reg Rdx
    | 3 -> Reg Rcx
    | 4 -> Reg R08
    | 5 -> Reg R09
    | _ -> 
      let offset = Int64.mul (Int64.sub (Int64.of_int n) 4L) 8L in 
      Ind3 (Lit offset, Rbp)
  end

(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

let rec sublist (list :'a list) (l:int) (r:int) : 'a list = 
  match list, l, r with
  | [], _, _ -> []
  | _, 0, 0 -> []
  | (x::xs), 0, n -> x :: sublist xs 0 (n-1)
  | (_::xs), n, m -> sublist xs (n-1) (m-1)

let compile_call (ctxt:ctxt) (uid:uid) (t:ty) (fn:Ll.operand) (ops: (ty * Ll.operand) list) : ins list = 
  let label = 
    match fn with
    | Null | Const _ -> failwith "Invalid function operand"
    | Gid id | Id id ->  Platform.mangle id
  in
  let register_args = sublist ops 0 6 in
  let memory_args = sublist ops 6 (-1) in
  let store_register_arg = fun i -> fun  (_, op)  -> 
    if i < 6 then [
      compile_operand ctxt temp1 op;
      (Movq, [temp1; arg_loc i])
    ] else failwith "Too many register arguments" in
  let store_memory_arg = fun (_, op) -> [compile_operand ctxt temp1 op; (Pushq, [temp1])] in

  let stack_alignment_init = [
    (Movq, [Reg Rsp; Reg Rbx]); (* Store stack pointer in rbx before aligning (rbx is callee saved )*)
    (Movq, [Reg Rsp; temp1]);
    (Shrq, [Imm(Lit 4L); temp1]); (* First align to 16 bytes by discarding bottom 4 bits*)
    (Shlq, [Imm(Lit 4L); temp1])
  ] @ begin
    if ((List.length memory_args) mod 2) = 0 then []
       else [(Subq, [Imm (Lit 8L); temp1])] (* If uneven number of memory operands, 
                                    subtract 8 from rsp to make it 16 byte aligned after args are pushed*)
      end 
      @ [(Movq, [temp1; Reg Rsp])]
    in

  let store_arguments = 
    (register_args |> List.mapi store_register_arg) @
    (memory_args |> List.rev |> List.map store_memory_arg) |> List.flatten in
  let assignment = 
    match t with
    | Void -> [] 
    | _ -> [(Movq, [Reg Rax; lookup ctxt.layout uid])]
  in
  let cleanup = [(Movq, [Reg Rbx; Reg Rsp])] in
  stack_alignment_init @ 
  store_arguments @ 
  [(Callq, [Imm (Lbl label)])] @ 
  assignment @ 
  cleanup


(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  match t with
  | I1 | I64 | Ptr _  -> 8
  | Array (n, ty) -> n * (size_ty tdecls ty)
  | Namedt tid -> size_ty tdecls (lookup tdecls tid)
  | Struct types -> 
    List.map (size_ty tdecls) types |> 
    List.fold_left (+) 0 
  | Void |Fun _ | I8 -> 0






(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

   - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

   - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

   - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let count_offset_struct (ctxt:ctxt) (t : Ll.ty list) (i:int64) : int64 =
let rec helper (rest: Ll.ty list) (curr:int64) =
match rest with
| [] ->  failwith "over the max index"
|(x::xs)->  if curr < i then
              Int64.add (size_ty ctxt.tdecls x|> Int64.of_int) (helper xs (Int64.add curr 1L))
            else
              0L
in
helper t 0L
let helper_gep (ctxt:ctxt) (curr:ty) (path:Ll.operand list) : ins list =
  let compile_temp2 = compile_operand ctxt temp2 in
  let rec helper (curr_type:ty) (curr_path:Ll.operand list) : ins list =
    begin match curr_type, curr_path with
      | _, [] -> []

      | Struct st, (Const i)::xs -> let offset = count_offset_struct ctxt st i in (*calculate offset until 
                                                                                  right part of struct*)
                              let compile_offset = compile_temp2 (Const offset) in (*offset saved in %Rcx*)
                              [compile_offset ; (Addq, [temp2; temp1])] @ (*Calc current offset from Base Address*)
                                            helper (List.nth st (Int64.to_int i)) xs
      | Struct _, _ -> failwith "not Const for Struct"
      | Array (_,t), x::xs -> let compile_arr_op = compile_temp2 x in (*move index to %Rcx*)
                              let array_type_size = size_ty ctxt.tdecls t |> Int64.of_int in 
                              (*calculate index for memory address*)
                              [compile_arr_op; 
                              (Imulq, [Imm (Lit array_type_size); temp2]);
                              (Addq, [temp2; temp1])]
                              @ helper t xs           
      | Namedt t, x -> helper (lookup ctxt.tdecls t) x
      | _ ,_ -> failwith "not valid type"
    end
in helper curr path


let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
let (t, point_addr) = op in
let compile_temp1 = compile_operand ctxt temp1 in
let compile_index = compile_temp1 point_addr in
begin match t with
| Ptr t1 -> [compile_index] @ helper_gep ctxt (Array (1,t1)) path
| _ -> failwith "not pointer"
end



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let get_op (op:Ll.operand) (layout:layout)=
  match op with
  | Null -> Imm (Lit 0L)
  | Const n -> Imm (Lit n)
  | Gid id ->
    let mgld_lbl = Platform.mangle id in
    lookup layout mgld_lbl
  | Id id -> lookup layout id

let compile_bop (bop:bop) : X86.ins list = 
  begin match bop with
    | Add -> [(Addq, [temp2; temp1])]; 
    | Sub -> [(Subq, [temp2; temp1])];
    | Mul -> [(Imulq,[temp2; temp1])];
    | And -> [(Andq, [temp2; temp1])];
    | Xor -> [(Xorq, [temp2; temp1])];
    | Or ->  [(Orq,  [temp2; temp1])];
    | Shl -> [(Shlq, [temp2; temp1])]
    | Lshr -> [(Shrq, [temp2; temp1])]
    | Ashr -> [(Sarq, [temp2; temp1])]
  end

let load_data (ctxt:ctxt) (src:Ll.operand) (dst:X86.operand) (ty:ty) : ins list = 
  let size_bytes = size_ty ctxt.tdecls ty in
  let size_quads = size_bytes / 8 in
  if size_quads > 1 then
    failwith "Invalid type for loading"
  else
    begin match src with 
      | Null | Const _ -> failwith "Invalid pointers Null / Const"
      | Id _ | Gid _  -> [
          compile_operand ctxt (Reg Rax) src; 
          (Movq, [Ind2 Rax; Reg Rax]);
          (Movq, [Reg Rax; dst])]
    end

let store_data (ctxt:ctxt) (src:Ll.operand) (dst:Ll.operand) (ty:ty) : ins list = 
  [
    compile_operand ctxt (Reg Rax) src; 
    compile_operand ctxt (Reg Rcx) dst;
    (Movq, [Reg Rax; Ind2 Rcx])
  ]

let load_data (ctxt:ctxt) (src:Ll.operand) (dst:X86.operand) (ty:ty) : ins list = 
  let size_bytes = size_ty ctxt.tdecls ty in
  let size_quads = size_bytes / 8 in
  if size_quads > 1 then
    failwith "Invalid type for loading"
  else
    begin match src with 
      | Null | Const _ -> failwith "Invalid pointers Null / Const"
      | Id _ | Gid _  -> [
          compile_operand ctxt (Reg Rax) src; 
          (Movq, [Ind2 Rax; Reg Rax]);
          (Movq, [Reg Rax; dst])]
    end

let store_data (ctxt:ctxt) (src:Ll.operand) (dst:Ll.operand) (ty:ty) : ins list = 
  [
    compile_operand ctxt (Reg Rax) src; 
    compile_operand ctxt (Reg Rcx) dst;
    (Movq, [Reg Rax; Ind2 Rcx])
  ]

let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  let compile_op1 = compile_operand ctxt temp1 in
  let compile_op2 = compile_operand ctxt temp2 in
  begin match i with 
    | Binop _ | Icmp _ | Alloca _ | Load _ | Gep _ ->
      let dst = lookup ctxt.layout uid in
      begin match i with
        | Binop  (bop, _, op1, op2)->  [compile_op1 op1] @ [compile_op2 op2] @ 
                                       (compile_bop bop) @
                                       [(Movq, [temp1; dst])];
        | Icmp (cnd, _, o1, o2) -> 
          let op_1 = compile_op1 o1 in
          let op_2 = compile_op2 o2 in
          [
            op_1; 
            op_2; 
            (Movq, [Imm (Lit 0L); dst]);
            (Cmpq, [Reg Rcx; Reg Rax]); 
            (Set (compile_cnd cnd), [dst]);
          ]
        | Alloca ty -> [
            (Subq, [Imm (Lit (size_ty ctxt.tdecls ty |> Int64.of_int)); Reg Rsp]);
            (Movq, [Reg Rsp; dst])
          ]
        | Load (ty, op) -> 
          begin match ty with
            | Ptr t -> load_data ctxt op dst t
            | _ -> failwith "Invalid type to load"
          end
        | Gep (t,op,path) -> compile_gep ctxt (t,op) path @ [(Movq, [temp1; dst])]
        | _ -> failwith "Thou shall not be here"
      end
    | Store (ty, op1, op2) -> store_data ctxt op1 op2 ty
    | Call (ty, fn, ops) -> compile_call ctxt uid ty fn ops
    | Bitcast (_, op, _) -> [compile_operand ctxt temp1 op; (Movq, [Reg Rax; lookup ctxt.layout uid])]
  end



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let store_operand = compile_operand ctxt (Reg Rax)
  in
  match t with
  | Ret (ty, op) -> 
    let restore_stack = [(Movq, [Reg Rbp; Reg Rsp]); (Popq, [Reg Rbp]); (Retq, [])] in
    begin match op with
      | Some operand -> store_operand operand :: restore_stack
      | None -> restore_stack
    end
  | Br lbl -> [(Jmp, [Imm (Lbl (Platform.mangle (mk_lbl fn lbl)))])]
  | Cbr (operand, lbl1, lbl2) -> 
    let label1 = Platform.mangle (mk_lbl fn lbl1) in
    let label2 = Platform.mangle (mk_lbl fn lbl2) in 
    [
      store_operand operand;
      (Cmpq, [Imm (Lit 1L); Reg Rax]); (* Check if operand is equal to 1*)
      (J Eq, [Imm (Lbl label1)]); 
      (Jmp, [Imm (Lbl label2)])
    ]


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  let x86_insns = List.map (compile_insn ctxt) blk.insns 
                  |> List.flatten in
  let x86_terminator = compile_terminator fn ctxt (snd blk.term) in
  x86_insns @ x86_terminator

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let right_instr (i:insn) : bool = 
  begin match i with
    | Binop _| Alloca _ | Load _ | Icmp _
    | Bitcast _ | Gep _ -> true
    | Call (Void, _, _) -> false
    | Call _ -> true
    | _ -> false
  end


let rec stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let rec helper (args : uid list) ((block, lbled_blocks):cfg) (n:int64) : layout =
    let curr_stack =  Ind3(Lit (Int64.mul n (-8L)), Rbp) in
    begin match args, block, lbled_blocks with
      | [], {insns = []; _},[] -> []
      | [], {insns = []; _ }, (_, next)::xs -> helper [] (next,xs) n
      | [], {insns = ((id,instr)::xs); term }, _ -> let new_block : block = {insns = xs; term = term} in 
        if right_instr instr then
          (id, curr_stack) :: (helper args (new_block, lbled_blocks) (Int64.add n 1L))
        else
          helper args (new_block, lbled_blocks) n

      | (arg :: x),_,_ -> (arg, curr_stack) :: (helper x (block, lbled_blocks) (Int64.add n 1L))
    end
  in helper args (block, lbled_blocks) 1L

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let make_entry_instr (arg: uid list) (l:layout): ins list =
  let rec helper (rest: uid list) (i:int) : ins list =
    begin match rest with
      | [] -> []
      | x::xs -> [
        (Movq, [arg_loc i; temp1]); (* Moving argument to register first, as it could be a memory location *)
        (Movq, [temp1; lookup l x])
       ] @ helper xs (i+1) (*only arguments copy*)
    end
  in 
  let num_stack_bytes = Int64.mul 8L (Int64.of_int (List.length l)) in
  let stack_allocation = [
    (Pushq,  [Reg Rbp]); 
    (Movq, [Reg Rsp; Reg Rbp]); 
    (Subq, [Imm (Lit num_stack_bytes); Reg Rsp])
  ] in
  stack_allocation @ (helper arg 0)

let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  let st_layout = stack_layout f_param f_cfg in
  let ctxt = {tdecls = tdecls; layout = st_layout} in
  let entry = make_entry_instr f_param st_layout in
  let entry_block = Asm.gtext name (entry @ compile_block name ctxt (fst f_cfg)) in
  let block_helper = fun (lbl, block) -> compile_lbl_block name lbl ctxt block in
  let other_blocks = List.map block_helper (snd f_cfg) in
  entry_block :: other_blocks



(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
