(* A pretty-printer for FreezeML. *)

open PPrint
open Client.ML
open Client

(* -------------------------------------------------------------------------- *)

let let_hardlines = true

(* Terms. *)

let print_qs (qs : int list) =
  let qs = List.map (fun f -> string (string_of_int f)) qs in
  separate comma qs

let print_type ty =
  match O.to_scheme ty with
  | ([], _) -> FPrinter.print_type ty
  | (qs, ty)  ->
     string "∀ " ^^
     lbracket ^^ print_qs qs ^^ rbracket ^^
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
          (if let_hardlines then hardline else empty) ^^
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
          (if let_hardlines then hardline else empty) ^^
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
  | Bool b ->
     string (string_of_bool b)

and print_term t =
  print_term_aux 2 t
