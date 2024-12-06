  (** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let dce_block (lb:uid -> Liveness.Fact.t) 
              (ab:uid -> Alias.fact)
              (b:Ll.block) : Ll.block =
    let helper (uid,insn : Ll.uid * Ll.insn) : bool = 
      let liveness_set = lb uid in
      let alias_map = ab uid in
      begin match insn with 
      | Call _ -> true
      | Store (_, _, dst) -> 
        begin match dst with 
        | Id u -> 
          let aliasing = UidM.find_opt u alias_map in
          let aliased = begin match aliasing with 
          | Some Alias.SymPtr.MayAlias -> true
          | _ -> false
          end
          in
          let live = UidS.mem u liveness_set in
          live || aliased
        | _ -> true
        end
      | _ -> UidS.mem uid liveness_set
      end 
    in
    {insns=List.filter helper b.insns; term=b.term}

let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

