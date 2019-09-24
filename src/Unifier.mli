open UnifierSig

(* The unifier is parameterized over the type structure. *)

module Make (S : STRUCTURE) : UNIFIER with type 'a structure = 'a S.structure

