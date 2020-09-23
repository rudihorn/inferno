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
    output_string stdout msg; flush stdout
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
    Printf.printf "%s\n" (Printexc.to_string e);
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

let translate t =
  try
    Some (Client.translate t)
  with
  | Client.Cycle ty ->
      if verbose then begin
        Printf.fprintf stdout "Type error: a cyclic type arose.\n";
        print_type ty
      end;
      None
  | Client.Unify (ty1, ty2) ->
      if verbose then begin
        Printf.fprintf stdout "Type error: type mismatch.\n";
        Printf.fprintf stdout "Type error: mismatch between the type:\n";
        print_type ty1;
        Printf.fprintf stdout "and the type:\n";
        print_type ty2;
        Printf.fprintf stdout "when translating the term:\n";
        print_ml_term t;
      end;
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
      translate term
  in
  match outcome, typ with
  | None, None ->
      (* Term is ill typed and is expected to be as such *)
     log_action log (fun () ->
         Printf.printf "Example %s is ill-typed." name;
       );
     if verbose then
       print_log log;
     Printf.printf "\027[32mExample %s works as expected\027[0m\n" name
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
         Printf.printf "but was determined ill-typed.";
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

let forall_a_a_to_a = Some ([1], F.TyArrow (F.TyVar 1, F.TyVar 1))

(* FreezeML examples from PLDI paper*)

let (<<) f g x = f(g(x))

(* Environment with some functions from Figure 2 *)
let env k =
  (* id : forall a. a -> a *)
  let fml_id k = ML.let_ ("id", ML.abs ("x", x), k) in
  (* choose : forall a. a -> a -> a *)
  let fml_choose k = ML.let_ ("choose", ML.abs ("x", (ML.abs ("y", x))), k) in
  (* auto : (forall a. a -> a) -> (forall a. a -> a) *)
  let fml_auto k = ML.let_ ("auto", ML.Abs ("x", forall_a_a_to_a, app x (frozen "x")), k) in
  (* auto' : forall b. (forall a. a -> a) -> b -> b *)
  let fml_autoprim k = ML.let_ ("auto'", ML.Abs ("x", forall_a_a_to_a, app x x), k) in
  (* app : forall a b. (a -> b) -> a -> b *)
  let fml_app k = ML.let_ ("app", ML.abs ("f", ML.abs ("x", app f x)), k) in
  (* revapp : forall a b. b -> (a -> b) -> b *)
  let fml_revapp k = ML.let_ ("revapp", ML.abs ("x", ML.abs ("f", app f x)), k) in
  (* zero : Int -> Int.  Turns every Int into 0.  This function replaces `inc`
     from FreezeML paper for all intents and purposes, since we only care about
     typing *)
  let fml_zero k = ML.let_ ("zero", ML.Abs ("x", Some ([], F.TyInt), ML.Int 0), k) in
  (* poly : (forall a. a -> a) -> (Int × Bool) *)
  let fml_poly k = ML.let_ ("poly", ML.Abs ("f", forall_a_a_to_a,
     ML.Pair (app f (ML.Int 1), app f (ML.Bool true))), k) in
  (* JSTOLAREK: implementing pair and pair' requires annotations on let *)
  (fml_id << fml_choose << fml_auto << fml_autoprim << fml_app << fml_revapp <<
   fml_zero << fml_poly) k

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
   inferred type      : INCORRECT ∀b. ∀a. a → b → b
   type in PLDI paper : (a → a) → (a → a)
 *)
let a2 =
  { name = "A2"
  ; term = env (app choose id)
  ; typ  = Some (TyForall ((),
             TyArrow (TyArrow (TyVar 0, TyVar 0), TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A2∘
   term               : choose ~id
   inferred type      : INCORRECT ∀a. a → ∀b. b → b
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a2_dot =
  { name = "A2∘"
  ; term = env (app choose (frozen "id"))
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
  ; term = env (app id auto)
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
  ; term = env (app id auto')
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
  ; term = env (app id (frozen "auto'"))
  ; typ  = Some (TyForall ((), TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                                        TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A7
   term               : choose id auto
   inferred type      : INCORRECT ∀ a. a → a
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a7 =
  { name = "A7"
  ; term = env (app (app choose id) auto)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  }

(* example            : A8
   term               : choose id auto'
   inferred type      : INCORRECT ∀ b. ∀ a. a → a
   type in PLDI paper : X
 *)
let a8 =
  { name = "A8"
  ; term = env (app (app choose id) auto')
  ; typ  = None
  }

(* MISSING : A9⋆: f (choose ~id) ids *)

(* example            : A10⋆
   term               : poly ~id
   inferred type      : FAILED ASSERTION
   type in PLDI paper : Int × Bool
 *)
let a10_star =
  { name = "A10⋆"
  ; term = env (app poly (frozen "id"))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* example            : A11⋆
   term               : poly $(λx. x)
   inferred type      : FAILED ASSERTION
   type in PLDI paper : Int × Bool
 *)
let a11_star =
  { name = "A11⋆"
  ; term = env (app poly (ML.gen (ML.abs ("x", x))))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* example            : A12⋆
   term               : id poly $(λx. x)
   inferred type      : FAILED ASSERTION
   type in PLDI paper : Int × Bool
 *)
let a12_star =
  { name = "A12⋆"
  ; term = env (app (app id poly) (ML.gen (ML.abs ("x", x))))
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
  ; term = ML.Abs ("x", forall_a_a_to_a, app x (ML.Int 1))
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

let () =
  (* FreezeML examples *)
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

  test fml_id_to_int;
  test fml_id_to_bool;
  test fml_const_false
