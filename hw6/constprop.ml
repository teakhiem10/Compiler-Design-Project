open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t

let get_op (op:Ll.operand) (d:fact) : Ll.operand =
  begin match op with
  | Id id | Gid id -> 
    let op_res = UidM.find_opt id d in
    begin match op_res with
    | Some (SymConst.Const a) -> Ll.Const a
    | _ -> op
    end
  | _ -> op
  end

(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow (u,i:uid * insn) (d:fact) : fact =
  begin match i with
  | Binop (biop,t,op1,op2) -> let new_op1 = get_op op1 d in
                              let new_op2 = get_op op2 d in
                              begin match new_op1 with
                              | Const val1 -> 
                                begin match new_op2 with
                                | Const val2 ->
                                  let new_val = 
                                    begin match biop with
                                    | Add -> Int64.add val1 val2
                                    | Sub -> Int64.sub val1 val2
                                    | Mul -> Int64.mul val1 val2
                                    | Shl -> Int64.shift_left val1 (Int64.to_int val2)
                                    | Lshr -> Int64.shift_right_logical val1 (Int64.to_int val2)
                                    | Ashr -> Int64.shift_right val1 (Int64.to_int val2)
                                    | And -> Int64.logand val1 val2
                                    | Or -> Int64.logor val1 val2
                                    | Xor -> Int64.logxor val1 val2 
                                    end
                                  in
                                  UidM.add u (SymConst.Const new_val) d
                                | _ -> UidM.add u SymConst.NonConst d
                                end
                              | _ -> UidM.add u SymConst.NonConst d
                              end
  | Icmp (cnd,t,op1,op2)-> let op1 = get_op op1 d in
                          let op2 = get_op op2 d in
                          begin match op1 with
                          | Const val1 -> 
                            begin match op2 with
                            | Const val2 -> 
                              let new_val = 
                                begin match cnd with
                                | Eq -> val1 = val2
                                | Ne -> not(val1 = val2)
                                | Slt -> val1 < val2
                                | Sle -> val1 <= val2
                                | Sgt -> val1 > val2
                                | Sge -> val1 >= val2
                                end
                              in
                              UidM.add u (SymConst.Const (if new_val then 1L else 0L)) d
                            | _ -> UidM.add u SymConst.NonConst d
                            end
                          | _ -> UidM.add u SymConst.NonConst d
                          end
  | Call (t,_,_) -> 
    begin match t with
    | Void -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d
    end
  | Store (t,_,_) -> begin match t with
                    | Void -> UidM.add u SymConst.UndefConst d
                    | _ -> d
                    end
  | Alloca _ | Load _ | Bitcast _ | Gep _ -> UidM.add u SymConst.NonConst d
  | _ -> failwith "insflow not fully implemented"
  end
(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = 
      let helper1 (a: SymConst.t) (b: SymConst.t) : SymConst.t =
        match a, b with
        | (Const a, _) | (_, Const a) -> Const a
        | _ -> NonConst
      in
      let helper2 (u:uid) (a:'a option) (b:'b option) =
        begin match a,b with
        | Some var, None | None, Some var-> Some var
        | Some var1, Some var2 -> Some (helper1 var1 var2)
        | None, None -> None
        end
      in
      let merge (uidm1: 'a UidM.t) (uidm2: 'b UidM.t)= UidM.merge helper2 uidm1 uidm2 in
      List.fold_left merge UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg

let get_op_block (id:uid) (d:fact) : Ll.operand =
  let op = UidM.find_opt id d in
  match op with
  | Some (SymConst.Const value) -> Const value
  | _ -> Id id

let ins_helper (uid : uid) (t : terminator) (cb : uid -> Fact.t) ((id,insn) : Ll.uid * Ll.insn) : (uid * Ll.insn) = 
  let new_ins =
  begin match insn with
  | Binop (bop, ty, Id id1, Id id2) -> Binop(bop, ty, get_op_block id1 (cb id), get_op_block id2 (cb id))
  | Binop (bop, ty, Id id1, op2) -> Binop(bop, ty, get_op_block id1 (cb id), op2)
  | Binop (bop, ty, op1, Id id2) -> Binop(bop, ty, op1, get_op_block id2 (cb id))
  | Call (ty, op, ops) -> 
    let help ((t:ty), (o:operand)) = begin match o with
                                  | Id id1 -> (t, get_op_block id1 (cb id))
                                  | _ -> (t, o)
                                end 
    in
    Call (ty, op, List.map help ops)
  | Bitcast (ty1, Id id1, ty2) -> Bitcast (ty1, get_op_block id1 (cb id), ty2)
  | Store (ty, Id id1, op) -> Store (ty, get_op_block id1 (cb id), op)
  | Icmp (cnd, ty, Id id1, Id id2) -> Icmp (cnd, ty, get_op_block id1 (cb id), get_op_block id2 (cb id))
  | Icmp (cnd, ty, Id id1, op2) -> Icmp (cnd, ty, get_op_block id1 (cb id), op2)
  | Icmp (cnd, ty, op1, Id id2) -> Icmp (cnd, ty, op1, get_op_block id2 (cb id))
  | _ -> insn
  end
  in (id, new_ins)
(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let tuid,termin = b.term in
    Cfg.add_block  l 
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
