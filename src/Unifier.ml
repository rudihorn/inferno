(******************************************************************************)
(*                                                                            *)
(*                                  Inferno                                   *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*  Copyright Inria. All rights reserved. This file is distributed under the  *)
(*  terms of the MIT License, as described in the file LICENSE.               *)
(*                                                                            *)
(******************************************************************************)

open UnifierSig

module Make (S : STRUCTURE) = struct

type 'a structure = 'a S.structure

(* -------------------------------------------------------------------------- *)

(* The data structure maintained by the unifier is as follows. *)

(* A unifier variable is a point of the union-find algorithm. *)

type variable =
    descriptor TUnionFind.point

(* Every equivalence class carries a descriptor which contains the following
   information. *)

(* Some of the fields below are mutable, because our client sometimes needs to
   update them. However, this is never done by the unifier itself, hence never
   done during unification. The unification algorithm is transactional: it
   writes only [TRef]s, so that all changes can be rolled back if unification
   fails. *)

and descriptor = {

  (* Every equivalence class carries a globally unique identifier. When
     a new equivalence class is created, a fresh identifier is chosen,
     and when two classes are merged, one of the two identifiers is kept.
     This identifier can be used as a key in a hash table. One should be
     aware, though, that identifiers are stable only as long as no unions
     are performed. *)

  id : int;

  (* Every equivalence class carries a structure, which is either [None],
     which means that the variable is just that, a variable; or [Some t],
     which means that the variable represents (has been equated with) the
     type [t]. *)

  mutable structure : variable structure option;

  (* Every equivalence class carries an integer rank. When two classes are
     merged, the minimum rank is retained. *)

  mutable rank : int;


  (* FEMRICH:
     We may consider merging {skolem} and {monomorphic} into one flag, whose value
     can be one of
      - Skolem: skolem, therefore it doesn't make sense to track monomorphism
      - Monomorphic
      - Unconstrained: "flexible", non-monomorphic variable

     This would exclude the case that {monomorphic} and {skolem} are true at the
     same time, which is an invalid state. On the other hand, it seems more
     confusing. *)
  mutable monomorphic : bool;

  mutable skolem : bool;

}

(* -------------------------------------------------------------------------- *)

(* Accessors. *)

let id v =
  (TUnionFind.find v).id

let structure v =
  (TUnionFind.find v).structure

let set_structure v structure =
  (TUnionFind.find v).structure <- structure

let has_structure v =
  (TUnionFind.find v).structure != None

let rank v =
  (TUnionFind.find v).rank

let set_rank v rank =
  (TUnionFind.find v).rank <- rank

let adjust_rank v k =
  let desc = TUnionFind.find v in
  if k < desc.rank then
    desc.rank <- k

let is_skolem v =
  (TUnionFind.find v).skolem

let skolemize v =
  let descriptor = TUnionFind.find v in
  assert (not (descriptor.monomorphic));
  descriptor.skolem <- true

let unskolemize v =
  (TUnionFind.find v).skolem <- false

let is_monomorphic v =
  (TUnionFind.find v).monomorphic

let unmonomorphize v =
  (TUnionFind.find v).monomorphic <- false

(* -------------------------------------------------------------------------- *)

let print (fuel : int) f v =
  let open PPrint in
  if (fuel > 0) then begin
  lbrace ^^
  string "id" ^^ equals ^^ string (string_of_int (id v)) ^^
  begin
    match structure v with
    | None -> empty
    | Some s ->
       comma ^^ space ^^ string "structure" ^^ equals ^^ f (fuel - 1) s
  end ^^
  begin
    if Debug.print_ranks then
      comma ^^ space ^^
      string "rank" ^^ equals ^^ string (string_of_int (rank v))
    else
      empty
  end ^^
  begin
    if ( (TUnionFind.find v).skolem ) then
      comma ^^ space ^^ string "skolem"
    else
      empty
  end ^^
  begin
    if ( (TUnionFind.find v).monomorphic ) then
      comma ^^ space ^^ string "mono"
    else
      empty
  end ^^
  rbrace
  end
  else
    lbrace ^^
    string "⋯" ^^
    rbrace

(* -------------------------------------------------------------------------- *)

(* Hash tables whose keys are variables. *)

module VarMap =
  Hashtbl.Make(struct
    type t = variable
    let equal = TUnionFind.equivalent
    let hash v = Hashtbl.hash (id v)
  end)

module PureVarMap =
  Map.Make(struct
    type t      = variable
    (* let equal   = TUnionFind.equivalent *)
    let compare = TUnionFind.compare
  end)

(* -------------------------------------------------------------------------- *)

(* [r++]. *)

let postincrement r =
  let v = !r in
  r := v + 1;
  v

(* -------------------------------------------------------------------------- *)

(* [fresh] creates a fresh variable with specified structure and rank. *)

let fresh =
  let id = ref 0 in
  fun structure rank ->
    TUnionFind.fresh {
      id = postincrement id;
      structure = structure;
      rank = rank;
      skolem = false;
      monomorphic = false;
    }

(* -------------------------------------------------------------------------- *)

(*
exception UnifyInternal (* JSTOLAREK: might be unused - see #8 *)
   *)
exception Unify of variable * variable

exception UnifySkolemInternal
exception UnifySkolem of variable * variable

(* FIXME FEMRICH: We probably want to add more info to this, to aid error
  messages.
  It can't be just a term variable: We may unify two type vars that are both
  monomorphic and whose mono constraints originate from different term
  variables. Further, if we consider non-generalizing let at some point, there
  isn't a term variable imposing the monomorphism. *)
exception UnifyMono

(* The internal function [unify t v1 v2] equates the variables [v1] and [v2]
   and propagates the consequences of this equation until an inconsistency is
   found or a solved form is reached. In the former case, [S.Iter2] is
   raised. The parameter [t] is a transaction. *)

let rec unify (t : _ TRef.transaction) (v1 : variable) (v2 : variable) : unit =

  (* If the two variables already belong to the same equivalence class, there
     is nothing to do, and [unify_descriptors] is not invoked. Furthermore, if
     there is something to do, then [unify_descriptors] is invoked only after
     the two equivalence classes have been merged. This is not just an
     optimization; it is essential in guaranteeing termination, since we are
     dealing with potentially cyclic structures. *)

  try
    TUnionFind.union t (unify_descriptors t) v1 v2
  with
  | UnifySkolemInternal ->
     raise (UnifySkolem (v1, v2))
  (* | UnifyInternal ->
     raise (Unify (v1, v2)) *)

(* -------------------------------------------------------------------------- *)

and monomorphize_variable visited v =
  if VarMap.mem visited v then
    () (* cyclic types considered not monomorphic *)
  else
    let desc = TUnionFind.find v in
    if desc.skolem then
      (* nothing to do, skolems are never monomorphic *)
      ()
    else
      desc.monomorphic <- true;
    VarMap.add visited v ();
    monomorphize_structure visited desc.structure

and monomorphize_structure visited s_opt =
  match s_opt with
  | None   -> ()
  | Some s ->
     if S.isForall s then
       raise UnifyMono
     else
       S.iter (fun v ->  monomorphize_variable visited v) s


(* [unify_descriptors desc1 desc2] combines the descriptors [desc1] and
   [desc2], producing a descriptor for the merged equivalence class. *)

and unify_descriptors t desc1 desc2 =
  match desc1, desc2 with
  (* Skolems can't have a structure. Ever. *)
  | _, { skolem = true; structure = Some _; _ }
  |    { skolem = true; structure = Some _; _ }, _ ->
     assert false

  (* We should never attempt to unify unregistered variables *)
  | _, { rank = 0; _ }
  |    { rank = 0; _ }, _ ->
     assert false

  | { id = id1; skolem = true; _ }, { id = id2; skolem = true; _ } ->
     (* Skolem can't unify with other skolem but can unify with itself.
        Skolems are never monomorphic. *)
     if (id1 <> id2) then raise UnifySkolemInternal;
     assert (desc1.structure = None);
     assert (desc2.structure = None);
     assert (desc1.rank = desc2.rank);
     {
      id          = id1;
      structure   = None;
      rank        = desc1.rank;
      skolem      = true;
      monomorphic = false
     }

  | { id = _id1; skolem = true; _ }, { structure = Some _; _ }
  | { structure = Some _; _ }, { id = _id1; skolem = true; _ } ->
     (* Skolems don't unify with variables that have a structure *)
     raise UnifySkolemInternal

  | _, _ ->
     (* Mixed-preifx unification: don't unify quantified type variables with
        out-of-scope existentials. *)
     if (desc2.skolem && desc1.rank != -1) || (desc1.skolem && desc2.rank != -1)
     then raise UnifySkolemInternal;

      (* skolemize *)
     let skolem = desc1.skolem || desc2.skolem in
     let new_desc =
       { (* We pick the skolem identifier if there is such *)
         id          = if desc2.skolem then desc2.id else desc1.id;
         structure   = unify_structures t desc1.structure desc2.structure;
         rank        = min desc1.rank desc2.rank;
         skolem;
         monomorphic = not skolem && (desc1.monomorphic || desc2.monomorphic)
       }
       in
       if new_desc.monomorphic then
         (* Propagate the monomorphism to all type vars used on the
          structure, if it exists. *)
         monomorphize_structure (VarMap.create 128) new_desc.structure;
       new_desc


(* -------------------------------------------------------------------------- *)

(* [unify_structures structure1 structure2] combines two structures. If one of
   them is undefined, we just keep the other. If both are defined, we unify
   them recursively. *)

and unify_structures t structure1 structure2 =
  Option.multiply (fun t1 t2 ->
    S.iter2 (unify t) t1 t2;
    t2 (* arbitrary; [t1] and [t2] are now equal anyway *)
  ) structure1 structure2

(* -------------------------------------------------------------------------- *)

(* The public version of [unify] wraps the unification process in a
   transaction, so that a failed unification attempt does not alter the state
   of the unifier. *)

let unify v1 v2 =
  try
    TRef.tentatively (fun t ->
      unify t v1 v2
    )
  with S.Iter2 ->
    raise (Unify (v1, v2))

(* -------------------------------------------------------------------------- *)

let monomorphize v =
  monomorphize_variable (VarMap.create 128) v

(* -------------------------------------------------------------------------- *)

let equivalent =
  TUnionFind.equivalent

let is_representative =
  TUnionFind.is_representative

(* -------------------------------------------------------------------------- *)

(* The occurs check, which detects cycles in the graph, cannot be defined as
   an instance of the cyclic decoder, for several reasons. For one thing, the
   cyclic decoder is inefficient, as it does not (cannot) mark the nodes that
   have been visited. Furthermore, the occurs check explores only the young
   generation, whereas the decoders explore everything. *)

exception Cycle of variable

let new_occurs_check (is_young : variable -> bool) =

  (* This hash table records the variables that are being visited (they are
     mapped to [false]) or have been visited (they are mapped to [true]). *)

  let table : bool VarMap.t = VarMap.create 128 in

  let rec traverse v =
    if is_young v then
      try
        let visited = VarMap.find table v in
        if not visited then
          (* This node is in the table, but has not been fully visited.
             Hence, it is being visited. A cycle has been found. *)
          raise (Cycle v)
      with Not_found ->
        (* Mark this variable as being visited. *)
        VarMap.add table v false;
        (* Visit its successors. *)
        Option.iter (S.iter traverse) (structure v);
        (* Mark this variable as fully visited. *)
        VarMap.replace table v true
  in

  traverse

(* -------------------------------------------------------------------------- *)

(* Bottom-up computation over an acyclic graph. *)

let new_acyclic_decoder
  (leaf :     variable -> 'a)
  (fold : 'a structure -> 'a)
        :     variable -> 'a =

  (* This hash table records the variables that have been visited and the
     value that has been computed for them. *)

  let visited : 'a VarMap.t = VarMap.create 128 in

  let rec decode v =
    try
      VarMap.find visited v
    with Not_found ->
      (* Because the graph is assumed to be acyclic, it is ok to update
         the hash table only after the recursive call. *)
      let a =
        match structure v with
        | None ->
            leaf v
        | Some t ->
            fold (S.map decode t)
      in
      VarMap.add visited v a;
      a

  in
  decode

(* -------------------------------------------------------------------------- *)

(* The cyclic decoder is designed mainly with the goal of constructing
   recursive types using [\mu] syntax. We must ensure that every use of a
   [\mu]-bound variable is dominated by its binder. This makes it impossible
   to use a table of [visited] nodes and share their value; we would risk
   entering an already-visited cycle via a different path. In order to avoid
   this problem, we define a decoder that uses a [visiting] table, but no
   [visited] table. This makes it correct, but potentially exponentially
   inefficient. Use with caution! *)

(* This cyclic decoder doesn't have persistent state: the table is
   initially empty and finally empty. Two toplevel calls to the
   decoder with the same arguments produce the same results. *)

(* A hash table records the variables that are being visited and also
   records whether they have been recursively re-discovered (i.e., they
   participate in a cycle). *)

type status =
    (* this variable is being visited: *)
  | Active
    (* this variable is being visited and participates in a cycle: *)
  | Rediscovered

let new_cyclic_decoder
  (leaf      :       variable -> 'a)
  (fold      :   'a structure -> 'a)
  (mu        : variable -> 'a -> 'a)
             :       variable -> 'a =

  let table : status VarMap.t = VarMap.create 128 in

  let rec decode v =
    match structure v with
    | None ->
        (* Begin with the easy case where there is no structure.
           In this case, this variable cannot participate in a
           cycle. The table isn't needed. *)
        leaf v
    | Some t ->
        (* There is some structure [t]. *)
        if VarMap.mem table v then begin
          (* We have just rediscovered this variable. Change its status
             in the table (which could be [Active] or [Rediscovered])
             to [Rediscovered], and stop the traversal. *)
          VarMap.replace table v Rediscovered;
          leaf v
        end
        else begin
          (* This variable is not being visited. Before the recursive call,
             mark it as being visited. *)
          VarMap.add table v Active;
          (* Perform the recursive traversal. *)
          let a = fold (S.map decode t) in
          (* Mark this variable as no longer being visited. If it was recursively
             rediscovered during the recursive call, then introduce a \mu binder. *)
          let status = try VarMap.find table v with Not_found -> assert false in
          VarMap.remove table v;
          match status with Active -> a | Rediscovered -> mu v a
        end

  in
  decode

end
