(* A pretty-printer for FreezeML. *)

open PPrint
open Client.ML

(* -------------------------------------------------------------------------- *)

(* Terms. *)

let print_qs (qs : int list) =
  let qs = List.map (fun f -> string (string_of_int f)) qs in
  separate comma qs

let print_type (qs, ty) =
  match qs with
  | [] -> FPrinter.print_type ty
  | _  ->
     string "forall " ^^
     print_qs qs ^^
     dot ^^ space ^^
     FPrinter.print_type ty

let rec print_term_aux level t =
  assert (level >= 0);
  match t with
  | Var x ->
      string x
  | FrozenVar x ->
      tilde ^^
      string x
  | App (t1, t2) ->
      if level >= 1 then
        print_term_aux 1 t1 ^^
        space ^^
        print_term_aux 0 t2
      else
        parens (print_term t)
  | Abs (x, None, m) ->
      if level >= 2 then
        string "fun " ^^
        string x ^^
        string " -> " ^^
        print_term_aux 2 m
      else
        parens (print_term t)
  | Abs (x, Some ty, m) ->
      if level >= 2 then
        string "fun (" ^^
        string x ^^
        string " : " ^^
        print_type ty ^^
        string ") -> " ^^
        print_term_aux 2 m
      else
        parens (print_term t)
  | Let (x, None, t1, t2) ->
      if level >= 2 then
        string "let " ^^
        string x ^^
        string " = " ^^
        print_term t1 ^^
        string " in " ^^
        print_term_aux 2 t2
      else
        parens (print_term t)
  | Let (x, Some ty, t1, t2) ->
      if level >= 2 then
        string "let (" ^^
        string x ^^
        string " : " ^^
        print_type ty ^^
        string ") = " ^^
        print_term t1 ^^
        string " in " ^^
        print_term_aux 2 t2
      else
        parens (print_term t)
 | Pair (t1, t2) ->
      parens (
        print_term t1 ^^
        comma ^^ space ^^
        print_term t2
      )
  | Proj (i, t2) ->
      (* like [App] *)
      if level >= 1 then
        string "proj" ^^
        OCaml.int i ^^
        space ^^
        print_term_aux 0 t2
      else
        parens (print_term t)
  | Int i ->
     string (string_of_int i)

and print_term t =
  print_term_aux 2 t
