open Client
open F

let verbose =
  true

(* -------------------------------------------------------------------------- *)

(* Facilities for dealing with exceptions. *)

(* A log is a mutable list of actions that produce output, stored in reverse
   order. It is used to suppress the printing of progress messages as long as
   everything goes well. If a problem occurs, then the printing actions are
   executed. *)

type log = {
  mutable actions: (unit -> unit) list
}

let create_log () =
  { actions = [] }

let log_action log action =
  log.actions <- action :: log.actions

let log_msg log msg =
  log_action log (fun () ->
    output_string stdout msg
  )

let print_log log =
  List.iter (fun action ->
    action();
    (* Flush after every action, as the action itself could raise an
       exception, and we will want to know which one failed. *)
    flush stdout
  ) (List.rev log.actions)

let attempt log msg f x =
  log_msg log msg;
  try
    f x
  with e ->
    print_log log;
    begin
    match e with
    | FTypeChecker.NotAnArrow ty ->
       let doc = PPrint.(string "Exception: not an arrow type:" ^^ hardline ^^
         string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
       PPrint.ToChannel.pretty 0.9 80 stdout doc
    | FTypeChecker.NotAProduct ty ->
       let doc = PPrint.(string "Exception: not a product type:" ^^ hardline ^^
         string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
       PPrint.ToChannel.pretty 0.9 80 stdout doc
    | FTypeChecker.NotAForall ty ->
       let doc = PPrint.(string "Exception: not a forall type:" ^^ hardline ^^
         string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
       PPrint.ToChannel.pretty 0.9 80 stdout doc
    | _ -> Printf.printf "%s\n" (Printexc.to_string e)
    end;
    Printexc.print_backtrace stdout;
    flush stdout;
    exit 1

(* -------------------------------------------------------------------------- *)

(* A wrapper over the client's [translate] function. We consider ill-typedness
   as normal, since our terms are randomly generated, so we translate the client
   exceptions to [None]. *)

let print_type ty =
  PPrint.(ToChannel.pretty 0.9 80 stdout (FPrinter.print_type ty ^^ hardline))

let print_ml_term m =
  PPrint.(ToChannel.pretty 0.9 80 stdout (MLPrinter.print_term m ^^ hardline))

let translate log t =
  try
    Some (Client.translate t)
  with
  | Client.Cycle ty ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: a cyclic type arose.\n";
        print_type ty
       );
     None
  | Client.Unify (ty1, ty2) ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: type mismatch.\n";
        Printf.fprintf stdout "Type error: mismatch between the type:\n";
        print_type ty1;
        Printf.fprintf stdout "and the type:\n";
        print_type ty2;
        Printf.fprintf stdout "when translating the term:\n";
        print_ml_term t
       );
     None
  | Client.UnifySkolem (ty1, ty2) ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: type mismatch.\n";
        Printf.fprintf stdout "Type error: skolem unification error between types:\n";
        print_type ty1;
        Printf.fprintf stdout "and the type:\n";
        print_type ty2;
        Printf.fprintf stdout "when translating the term:\n";
        print_ml_term t
       );
     None

(* -------------------------------------------------------------------------- *)

(* Running all passes over a single ML term. *)

type example = { name : string
               ; term : ML.term
               ; typ  : debruijn_type option }

let test { name; term; typ } : unit =
  let log = create_log() in
  log_action log (fun () ->
      Printf.printf "\n===========================================\n\n%!";
      Printf.printf "Running example %s\n%!" name;
    );
  let outcome =
    attempt log
      "Type inference and translation to System F...\n"
      (translate log) term
  in
  match outcome, typ with
  | None, None ->
      (* Term is ill typed and is expected to be as such *)
     log_action log (fun () ->
         Printf.printf "Example %s was rejected by the typechecker as expected.\n" name;
       );
     if verbose then
       print_log log;
     Printf.printf "\027[32mExample %s works as expected\027[0m\n" name; flush stdout
  | Some (t : F.nominal_term), Some exp_ty ->
      log_action log (fun () ->
        Printf.printf "Formatting the System F term...\n%!";
        let doc = PPrint.(string "  " ^^ nest 2 (FPrinter.print_term t) ^^ hardline) in
        Printf.printf "Pretty-printing the System F term...\n%!";
        PPrint.ToChannel.pretty 0.9 80 stdout doc
      );
      let t : F.debruijn_term =
        attempt log
          "Converting the System F term to de Bruijn style...\n"
          F.translate t
      in
      let ty : F.debruijn_type =
        attempt log
          "Type-checking the System F term...\n"
          FTypeChecker.typeof t
      in
      log_action log (fun () ->
        if ( exp_ty = ty ) then
          begin
            Printf.printf "Pretty-printing the System F de Bruijn type...\n%!";
            let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
            PPrint.ToChannel.pretty 0.9 80 stdout doc;
          end
        else
          begin
            Printf.printf "Expected type does not match actual type!\n";
            Printf.printf "Expected:\n";
            let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type exp_ty ^^ hardline) in
            PPrint.ToChannel.pretty 0.9 80 stdout doc;
            Printf.printf "Actual:\n";
            let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
            PPrint.ToChannel.pretty 0.9 80 stdout doc;
          end
      );
      if verbose then
        print_log log;
      if ( exp_ty = ty ) then
        Printf.printf "\027[32mExample %s works as expected\027[0m\n" name
      else
        Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name

  | None, Some exp_ty ->
     log_action log (fun () ->
         Printf.printf "Example %s expected to have a type:" name;
         let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type exp_ty ^^ hardline) in
         PPrint.ToChannel.pretty 0.9 80 stdout doc;
         Printf.printf "but was determined ill-typed.\n";
       );
     if verbose then
       print_log log;
     Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name
  | Some t, None ->
      log_action log (fun () ->
        Printf.printf "Formatting the System F term...\n%!";
        let doc = PPrint.(string "  " ^^ nest 2 (FPrinter.print_term t) ^^ hardline) in
        Printf.printf "Pretty-printing the System F term...\n%!";
        PPrint.ToChannel.pretty 0.9 80 stdout doc
      );
      let t : F.debruijn_term =
        attempt log
          "Converting the System F term to de Bruijn style...\n"
          F.translate t
      in
      let ty : F.debruijn_type =
        attempt log
          "Type-checking the System F term...\n"
          FTypeChecker.typeof t
      in
      log_action log (fun () ->
          Printf.printf "Pretty-printing the System F de Bruijn type...\n%!";
          let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
          PPrint.ToChannel.pretty 0.9 80 stdout doc;
          Printf.printf "Example %s epected to be ill-typed but typechecks.\n" name;
        );
      if verbose then
        print_log log;
      Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name

(* -------------------------------------------------------------------------- *)

let var x =
  ML.Var x

let frozen x =
  ML.FrozenVar x

let app x y =
  ML.App (x, y)

let x =
  var "x"

let y =
  var "y"

let f =
  var "f"

let id =
  var "id"

let choose =
  var "choose"

let auto =
  var "auto"

let auto' =
  var "auto'"

let poly =
  var "poly"

let one =
  ML.Int 1

let forall_a_a_to_a = Some ([1], F.TyArrow (F.TyVar 1, F.TyVar 1))

(* FreezeML examples from PLDI paper*)

let (<<) f g x = f(g(x))

(* Environment with some functions from Figure 2 *)
(* JSTOLAREK: implementing pair and pair' requires annotations on let *)

(* id : forall a. a -> a *)
let fml_id k = ML.let_ ("id", ML.abs ("x", x), k)

(* choose : forall a. a -> a -> a *)
let fml_choose k = ML.Let ("choose",
  Some ([1], F.TyArrow (F.TyVar 1, F.TyArrow (F.TyVar 1, F.TyVar 1))),
  ML.abs ("x", (ML.abs ("y", x))), k)

(* auto : (forall a. a -> a) -> (forall a. a -> a) *)
let fml_auto k = ML.let_ ("auto", ML.Abs ("x", forall_a_a_to_a,
                                               app x (frozen "x")), k)

(* auto' : forall b. (forall a. a -> a) -> b -> b *)
let fml_autoprim k = ML.let_ ("auto'", ML.Abs ("x", forall_a_a_to_a, app x x), k)

(* app : forall a b. (a -> b) -> a -> b *)
let fml_app k = ML.let_ ("app", ML.abs ("f", ML.abs ("x", app f x)), k)

(* revapp : forall a b. b -> (a -> b) -> b *)
let fml_revapp k = ML.let_ ("revapp", ML.abs ("x", ML.abs ("f", app f x)), k)

(* zero : Int -> Int.  Turns every Int into 0.  This function replaces `inc`
   from FreezeML paper for all intents and purposes, since we only care about
   typing *)
let fml_zero k = ML.let_ ("zero", ML.Abs ("x", Some ([], F.TyInt), ML.Int 0), k)

(* poly : (forall a. a -> a) -> (Int × Bool) *)
let fml_poly k = ML.let_ ("poly", ML.Abs ("f", forall_a_a_to_a,
   ML.Pair (app f one, app f (ML.Bool true))), k)

let env k = (
    fml_id       <<
    fml_choose   <<
    fml_auto     <<
    fml_autoprim <<
    fml_app      <<
    fml_revapp   <<
    fml_zero     <<
    fml_poly
  ) k

(* Polymorphic instantiation *)

(* example            : A1
   term               : λx y.y
   inferred type      : ∀ b. ∀ a. a → b → b
   type in PLDI paper : a → b → b
*)
let a1 =
  { name = "A1"
  ; term = ML.abs ("x", ML.abs ("y", y))
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 0, TyArrow (TyVar 1, TyVar 1)))))
  }

(* example            : A1∘
   term               : $(λx y.y)
   inferred type      : ∀ b. ∀ a. a → b → b
   type in PLDI paper : ∀ a b. a → b → b
 *)
let a1_dot =
  { name = "A1̣∘"
  ; term = ML.gen (ML.abs ("x", ML.abs ("y", y)))
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 0, TyArrow (TyVar 1, TyVar 1)))))
  }

(* example            : A2
   term               : choose id
   inferred type      : ∀a. (a → a) → (a → a)
   type in PLDI paper : (a → a) → (a → a)
 *)
let a2 =
  { name = "A2"
  ; term = (fml_id << fml_choose)
           (app choose id)
  ; typ  = Some (TyForall ((),
             TyArrow (TyArrow (TyVar 0, TyVar 0), TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A2∘
   term               : choose ~id
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a2_dot =
  { name = "A2∘"
  ; term = (fml_id << fml_choose)
           (app choose (frozen "id"))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  }

(* MISSING: A3: choose [] ids *)

(* example            : A4
   term               : λ(x : ∀ a. a → a). x x
   inferred type      : ∀b. (∀a. a → a) → b → b
   type in PLDI paper : (∀ a. a → a) → (b → b)
 *)
let a4 =
  { name = "A4"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x x)
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A4̣∘
   term               : λ(x : ∀ a. a → a). x ~x
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a4_dot =
  { name = "A4̣∘"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x (frozen "x"))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A5
   term               : id auto
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a5 =
  { name = "A5"
  ; term = (fml_id << fml_auto)
           (app id auto)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A6
   term               : id auto'
   inferred type      : ∀b. (∀a. a → a) → b → b
   type in PLDI paper : (∀ a. a → a) → (b → b)
 *)
let a6 =
  { name = "A6"
  ; term = (fml_id << fml_autoprim)
           (app id auto')
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A6∘
   term               : id ~auto'
   inferred type      : ∀ b. (∀ a. a → a) → (b → b)
   type in PLDI paper : ∀ b. (∀ a. a → a) → (b → b)
 *)
let a6_dot =
  { name = "A6∘"
  ; term = (fml_id << fml_autoprim)
           (app id (frozen "auto'"))
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A7
   term               : choose id auto
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a7 =
  { name = "A7"
  ; term = (fml_id << fml_choose << fml_auto)
           (app (app choose id) auto)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A8
   term               : choose id auto'
   inferred type      : X
   type in PLDI paper : X
 *)
let a8 =
  { name = "A8"
  ; term = (fml_id << fml_choose << fml_autoprim)
           (app (app choose id) auto')
  ; typ  = None
  }

(* MISSING : A9⋆: f (choose ~id) ids *)

(* example            : A10⋆
   term               : poly ~id
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let a10_star =
  { name = "A10⋆"
  ; term = (fml_id << fml_poly)
           (app poly (frozen "id"))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* example            : A11⋆
   term               : poly $(λx. x)
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let a11_star =
  { name = "A11⋆"
  ; term = (fml_poly)
           (app poly (ML.gen (ML.abs ("x", x))))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* example            : A12⋆
   term               : id poly $(λx. x)
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let a12_star =
  { name = "A12⋆"
  ; term = (fml_id << fml_poly)
           (app (app id poly) (ML.gen (ML.abs ("x", x))))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* Examples that were not in the PLDI paper *)

(* This was causing an exception in FTypeChecker because I didn't extend type
   equality checker with TyInt

   term : λ(x : ∀ a. a → a). x 1
   type : (∀ a. a → a) → Int
 *)
let fml_id_to_int =
  { name = "id_to_int"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x one)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)), TyInt))
  }

(* Two simple functions to test correctness of Bool implementation *)
(*
   term : λ(x : ∀ a. a → a). x true
   type : (∀ a. a → a) → Bool
*)
let fml_id_to_bool =
  { name = "id_to_bool"
  ; term = ML.Abs ("x", forall_a_a_to_a, app x (ML.Bool false))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)), TyBool))
  }

(*
   term : λ(x : bool). false
   type : Bool → Bool
*)
let fml_const_false =
  { name = "const_false"
  ; term = ML.Abs ("x", Some ([], F.TyBool), ML.Bool false)
  ; typ  = Some (TyArrow (TyBool, TyBool))
  }

(* Some examples to test correct instantiation of quantified types *)
(*
   term : (let id = λx.x in id) 1
   type : Int
*)
let fml_inst_1 =
  { name = "inst_1"
  ; term = app (ML.let_ ("id", ML.abs ("x", x), id)) one
  ; typ  = Some TyInt
  }

(*
   term : (let x = auto ~id in x) 1
   type : Int
*)
let fml_inst_2 =
  { name = "inst_2"
  ; term = (fml_id << fml_auto)
           (app (ML.let_ ("x", app auto (frozen "id"), x)) one)
  ; typ  = Some TyInt
  }

(*
   term : λ(x : (∀ a. a → a) → (∀ a. a → a)). (x ~id)@ 1
   type : ((∀ a. a → a) → (∀ a. a → a)) → Int
*)
let fml_nested_forall_inst =
  { name = "nested_forall_inst"
  ; term = fml_id (ML.Abs ("x",
      Some ([], F.TyArrow ( F.TyForall (1, F.TyArrow (F.TyVar 1, F.TyVar 1))
                          , F.TyForall (1, F.TyArrow (F.TyVar 1, F.TyVar 1)))),
      app (ML.inst (app x (frozen "id"))) one))
  ; typ  = Some
      (TyArrow
        (TyArrow ( F.TyForall ((), F.TyArrow (F.TyVar 0, F.TyVar 0))
                 , F.TyForall ((), F.TyArrow (F.TyVar 0, F.TyVar 0))), TyInt))
  }

(* Correctness of type annotations on let binders *)
(*
   term : let (id : ∀ a. a → a) = λx.x in id
   type : ∀ a. a → a
*)
let fml_id_annot_1 =
  { name = "id_annot_1"
  ; term = ML.Let ("id", Some ([1], TyArrow (TyVar 1, TyVar 1)), ML.abs ("x", x), id)
  ; typ  = Some (F.TyForall ((), F.TyArrow (F.TyVar 0, F.TyVar 0)))
  }

(*
   term : let (id : ∀ a b. a → b) = λx.x in id
   type : X
*)
let fml_id_annot_2 =
  { name = "id_annot_2"
  ; term = ML.Let ("id", Some ([1;2], TyArrow (TyVar 1, TyVar 2)), ML.abs ("x", x), id)
  ; typ  = None
  }

(*
   term : let (id : ∀ a. a → a) = λ(x : Int).x in id
   type : X
*)
let fml_id_annot_3 =
  { name = "id_annot_3"
  ; term = ML.Let ("id", Some ([1], TyArrow (TyVar 1, TyVar 1)),
                   ML.Abs ("x", Some ([], TyInt) , x), id)
  ; typ  = None
  }

(*
   term : let id = λx.x in let (y : ∀ a. a → a) = ~id in y
   type : ∀ a. a → a
*)
let fml_id_annot_4 =
  { name = "id_annot_4"
  ; term = ML.let_ ("id", ML.abs ("x", x),
      ML.Let ("y", Some ([1], TyArrow (TyVar 1, TyVar 1)),
                   frozen "id", y))
  ; typ  = Some (F.TyForall ((), F.TyArrow (F.TyVar 0, F.TyVar 0)))
  }

(*
   term : let id = λx.x in let (choose : ∀a b. a → b → b) = λx.λy.x in choose id
   type : X
*)
let fml_id_annot_5 =
  { name = "id_annot_5"
  ; term = ML.let_ ("id", ML.abs ("x", x),
      ML.Let ("choose", Some ([1;2], TyArrow (TyVar 1, TyArrow (TyVar 2, TyVar 2))),
                   ML.abs ("x", ML.abs ("y", x)), app choose id))
  ; typ  = None
  }


let () =
  (* PLDI paper examples *)
  test a1;
  test a1_dot;
  test a2;
  test a2_dot;
  test a4;
  test a4_dot;
  test a5;
  test a6;
  test a6_dot;
  test a7;
  test a8;
  test a10_star;
  test a11_star;
  test a12_star;

  (* Other examples *)
  test fml_id_to_int;
  test fml_id_to_bool;
  test fml_const_false;
  test fml_inst_1;
  test fml_inst_2;
  test fml_nested_forall_inst;
  test fml_id_annot_1;
  test fml_id_annot_2;
  test fml_id_annot_3;
  test fml_id_annot_4;
  test fml_id_annot_5
