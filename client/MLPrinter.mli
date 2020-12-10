(* A pretty-printer for FreezeML. *)

open PPrint
open Lang

val print_term: ML.term -> document
val print_type: ML.ty   -> document
