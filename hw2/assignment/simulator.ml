(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun (c:cnd) -> begin match c with
                                                            | Eq -> fz
                                                            | Neq -> not fz
                                                            | Gt -> (not fz) && fs = fo
                                                            | Ge -> fs = fo
                                                            | Lt -> not(fs = fo)
                                                            | Le -> not(fs = fo) || fz
                                                            end

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option = if addr < mem_bot || addr >= mem_top then   
                                          None  
                                        else  
                                          Some (Int64.to_int(Int64.sub addr mem_bot))

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let get_register_value (m:mach) (reg:reg) : int64 = 
  Array.get m.regs (rind reg)

let store_in_register (m:mach) (reg:reg) (data:int64) : unit =
  Array.set m.regs (rind reg) data

let get_memory_value (m:mach) (addr:int64) : int64 = 
  let array_index_option = map_addr addr in
  match array_index_option with
  | None -> failwith "Address outside range"
  | Some array_index -> int64_of_sbytes (Array.to_list (Array.sub m.mem array_index 8))

let get_instruction_from_memory (m:mach) : sbyte = 
  let array_index_option = map_addr (get_register_value m Rip) in
  match array_index_option with
  | None -> failwith "Rip points to invalid memory location"
  | Some array_index -> Array.get m.mem array_index

let store_in_memory (m:mach) (addr:int64) (data:int64): unit = 
  let sbytes = sbytes_of_int64 data in
  let array_index_option = map_addr addr in
  match array_index_option with
  | None -> failwith "Address outside range"
  | Some array_index -> 
    let insert_at_location = fun (index:int) (b:sbyte) : unit ->
      Array.set m.mem (array_index + index) b
    in
    List.iteri insert_at_location sbytes

let get_num_from_operand (m:mach) (op:operand): int64 = 
  match op with
  | Imm imm -> 
    (match imm with
    | Lit lit -> lit
    | _ -> failwith "Cannot get number from label"
    )
  | Reg reg -> get_register_value m reg
  | Ind1 imm -> 
    (match imm with
    | Lit lit -> get_memory_value m lit
    | _ -> failwith "Cannot get value of label"
    )

let store_value_at_operand (m:mach) (op:operand) (data:int64) : unit = 
  match op with 
  | Reg reg -> store_in_register m reg data
  | Ind1 imm -> 
    (match imm with
    | Lit lit -> store_in_memory m lit data
    | _ -> failwith "Cannot store at label"
    )
  | _ -> failwith "Cannot store at immediate"

let increment_rip (m:mach) : unit = 
    store_in_register m Rip (Int64.add 8L (get_register_value m Rip))

    (* Make all indirect operands into Ind1 *)
let handle_operands (m:mach) (operands: operand list) : operand list = 
  let handle_operand (op:operand) : operand = 
    match op with 
    | Imm _
    | Reg _
    | Ind1 _ -> op
    | Ind2 register -> Ind1 (Lit (get_register_value m register))
    | Ind3 (imm, register) -> 
      (match imm with
      | Lit lit -> Ind1 (Lit (Int64.add (get_register_value m register)  lit))
      | _ -> failwith "Cannot handle label in handle_operands"
      )
  in
  List.map handle_operand operands

let get_bit (num:int64) (amt:int) : int = Int64.to_int (Int64.shift_right_logical (Int64.shift_left num (63 - amt)) 63)

(* extracts sign bit from num *)
let get_sign (num: int64) : int = get_bit num 63

let truncate_and_get_flags (num: Big_int.big_int): (bool * bool * bool * int64) = 
  let oF = Big_int.gt_big_int num (Big_int.big_int_of_int64 Int64.max_int)
        || Big_int.lt_big_int num (Big_int.big_int_of_int64 Int64.min_int) in
  let modulus = Big_int.shift_left_big_int Big_int.unit_big_int 64 in
  let wrapped = Big_int.mod_big_int num modulus in
  let result = 
  if Big_int.le_big_int wrapped (Big_int.big_int_of_int64 Int64.max_int) then
    Big_int.int64_of_big_int wrapped
  else
    Big_int.int64_of_big_int (Big_int.sub_big_int wrapped modulus)
  in
  let sF = 1 = (get_sign result) in
  let zF = Int64.equal 0L result in 
  (oF, sF, zF, result)

let handle_unary_exp (op:opcode) (num:int64) : Big_int.big_int = 
    let bNum = Big_int.big_int_of_int64 num in
    match op with
    | Negq -> Big_int.sub_big_int Big_int.zero_big_int bNum
    | Incq -> Big_int.add_big_int bNum Big_int.unit_big_int
    | Decq -> Big_int.sub_big_int bNum Big_int.unit_big_int
    | Notq -> Big_int.big_int_of_int64 (Int64.lognot num)
  
let handle_binary_exp (op:opcode) (num1:int64) (num2:int64) : Big_int.big_int = 
    let b1 = Big_int.big_int_of_int64 num1 in
    let b2 = Big_int.big_int_of_int64 num2 in
    match op with
    | Addq -> Big_int.add_big_int b2 b1
    | Subq -> Big_int.sub_big_int b2 b1
    | Imulq -> Big_int.mult_big_int b2 b1
    | Andq -> Big_int.and_big_int b2 b1
    | Orq -> Big_int.or_big_int b2 b1
    | Xorq -> Big_int.xor_big_int b2 b1
    | Sarq | Shlq | Shrq -> 
      let amt = Int64.to_int num1 in
      let result = 
        match op with
        | Sarq -> Int64.shift_right num2 amt
        | Shlq -> Int64.shift_left num2 amt
        | Shrq -> Int64.shift_right_logical num2 amt
      in Big_int.big_int_of_int64 result

let handle_exp (m:mach) (op:opcode) (operands: operand list) : (int * int * int * int64) = 
  let aux = get_num_from_operand m in
  let numbers = List.map aux operands in
  let big_int_result = 
    match op with
    | Negq | Incq | Decq | Notq -> handle_unary_exp op (List.hd numbers)
    | Addq | Subq | Imulq | Andq | Orq | Xorq | Sarq | Shlq | Shrq -> handle_binary_exp op (List.hd numbers) (List.nth numbers 1)
    in
  let (oF, sF, zF, result) = truncate_and_get_flags big_int_result in 
  let sf_return = 
    match op with
    | Negq | Addq | Subq | Incq | Decq | Andq | Orq | Xorq -> Bool.to_int sF
    | Sarq | Shlq | Shrq -> if Int64.equal (List.hd numbers) 0L then -1 else Bool.to_int sF
    | Imulq | Notq -> -1
  in 
  let zF_return = 
    match op with
    | Negq | Addq | Subq | Incq | Decq | Andq | Orq | Xorq -> Bool.to_int zF
    | Sarq | Shlq | Shrq -> if Int64.equal (List.hd numbers) 0L then -1 else Bool.to_int zF
    | Imulq | Notq -> -1
  in
  let of_return =
    match op with
    | Negq | Subq | Decq -> if Int64.equal (List.hd numbers) Int64.min_int or oF then 1 else 0
    | Andq | Orq | Xorq -> 0
    | Notq -> -1
    | Addq | Imulq | Incq  -> Bool.to_int oF
    | Sarq | Shlq | Shrq -> if (Int64.equal (List.hd numbers) 0L) || not (Int64.equal (List.hd numbers) 1L) then -1 else 
      match op with
      | Sarq -> 0
      | Shlq -> if (get_bit (List.nth numbers 1) 63) = (get_bit (List.nth numbers 1) 62) then 0 else 1
      | Shrq -> get_sign (List.nth numbers 1)
  in 
  (of_return, sf_return, zF_return, result)

let handle_data_movement (m:mach) (op:opcode) (operands: operand list) : unit = 
  let operand1 = List.hd operands in
  let result = 
    match op with 
    | Leaq -> let ind = operand1 in 
      (match ind with
      | Ind1 imm -> 
        (match imm with 
        | Lit lit -> lit
        | _ -> failwith "Cannot interpret label"
        )
      | _ -> failwith "Operand should be simplified to Ind1 before passing to this function"
      )
    | Movq -> get_num_from_operand m operand1
    | Pushq -> get_num_from_operand m operand1
    | Popq -> get_memory_value m (get_register_value m Rsp)
  in 
    match op with 
    | Leaq | Movq -> 
      let operand2 = List.nth operands 1 in 
      (match operand2 with
      | Reg reg -> store_in_register m reg result
      | Ind1 imm -> 
        (match imm with 
        | Lit lit -> store_in_memory m lit result
        | _ -> failwith "Cannot store into label"
        )
      | _ -> failwith "Invalid storage type"
      )
    | Pushq -> 
      store_in_register m Rsp (Int64.sub (get_register_value m Rsp) 8L);
      store_in_memory m (get_register_value m Rsp) result
    | Popq -> 
      (match operand1 with
      | Reg reg -> 
        (store_in_register m reg result;
        store_in_register m Rsp (Int64.add 8L (get_register_value m Rsp)))
      | _ -> failwith "I think this is illegal?"
      )

let handle_conditional (m:mach) (op:opcode) (cc:cnd) (operand:operand) : unit = 
  let cc_true = interp_cnd m.flags cc in
  match op with
  | Set _ -> 
    let mask = (Int64.logor (Int64.lognot 255L) (if cc_true then 1L else 0L)) in
    let tmp = get_num_from_operand m operand in
    let result = Int64.logand (Int64.logor tmp 255L) mask in
    store_value_at_operand m operand result
  | J _ ->
    if cc_true then store_in_register m Rip (get_num_from_operand m operand)
    else increment_rip m
  | _ -> failwith "You should not be here"

let handle_control_flow (m:mach) (op:opcode) (operands: operand list) : unit = 
  match op with
  | Retq -> handle_data_movement m Popq [Reg Rip]
  | _ -> let operand1 = List.hd operands in
    (match op with
    | Jmp -> store_in_register m Rip (get_num_from_operand m operand1)
    | Callq -> 
      handle_data_movement m Pushq [Reg Rip];
      store_in_register m Rip (get_num_from_operand m operand1);
    )

let update_flags (m:mach) (oF:int) (sF:int) (zF:int) : unit = 
  (if -1 = sF then () else m.flags.fs <- sF = 1; 
  if -1 = zF then () else m.flags.fz <- zF = 1;
  if -1 = oF then () else m.flags.fo <- oF = 1;)

let get_destination_for_expression (operands: operand list) : operand =
  if List.length operands > 1 then List.nth operands 1 else List.hd operands

let do_instruction (m:mach) (op:opcode) (operands: operand list) : unit = 
  match op with
  | Leaq | Movq | Pushq | Popq -> handle_data_movement m op operands
  | Set cnd | J cnd -> handle_conditional m op cnd (List.hd operands)
  | Retq | Jmp | Callq -> handle_control_flow m op operands
  | Cmpq -> 
    let (oF, sF, zF, _) = handle_exp m Subq operands in
    update_flags m oF sF zF;
  | _ -> 
    let (oF, sF, zF, result) = handle_exp m op operands in
    let destination = get_destination_for_expression operands in
    store_value_at_operand m destination result;
    update_flags m oF sF zF

let step (m:mach) : unit =
  let ins_byte = get_instruction_from_memory m in
    match ins_byte with 
    | InsFrag | Byte _ -> failwith "Instruction pointer does not point to an instruction"
    | InsB0 (opcode, operands) -> 
      let simpler_operands = handle_operands m operands in
      do_instruction m opcode simpler_operands;
      match opcode with
      | Jmp | Callq | Retq | J _ -> ()
      | _ -> increment_rip m

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)
  
(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
    - separate the text and data segments
    - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

    - resolve the labels to concrete addresses and 'patch' the instructions to 
      replace Lbl values with the corresponding Imm values.

    - the text segment starts at the lowest address
    - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
  *)
let assemble (p:prog) : exec =
failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)

let rec set_memory_at_location (mem:mem) (location: quad) (data: sbyte list) : mem = 
  let data_array = Array.of_list data in
  let set_sbyte_at_location = fun i b  -> 
    let index_option = map_addr (Int64.add location (Int64.of_int i)) in
    match index_option with
    | None -> failwith "Invalid location in set_memory_at_location"
    | Some index -> Array.set mem index b;
  in
  Array.iteri set_sbyte_at_location data_array;
  mem


let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
  let max_legal_address = Int64.sub mem_top 8L in
  let reg_values = fun index _ -> 
    match index with
    | 16 -> entry
    | 7 -> max_legal_address
    | _ -> 0L
  in
  let init_mem = Array.make mem_size (Byte '\x00') in
  let text_mem = set_memory_at_location init_mem text_pos text_seg in
  let data_memory = set_memory_at_location text_mem data_pos data_seg in
  let memory = set_memory_at_location data_memory max_legal_address (sbytes_of_int64 exit_addr) in
  { flags = {fo = false; fs = false; fz = false}
  ; regs = Array.mapi reg_values (Array.make nregs 0L)
  ; mem = memory
  }
