open Client
open F
open Result

let verbose =
  false

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
    begin
    match e with
    | FTypeChecker.NotAnArrow ty ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           PPrint.ToChannel.pretty 0.9 80 stdout PPrint.(
               string "Exception: not an arrow type:" ^^ hardline ^^
               string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline)
         )
    | FTypeChecker.NotAProduct ty ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           PPrint.ToChannel.pretty 0.9 80 stdout PPrint.(
             string "Exception: not a product type:" ^^ hardline ^^
             string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline)
         )
    | FTypeChecker.NotAForall ty ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           PPrint.ToChannel.pretty 0.9 80 stdout PPrint.(
             string "Exception: not a forall type:" ^^ hardline ^^
             string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline)
         )
    | exn ->
       log_action log (fun () ->
           Printf.fprintf stdout "Implementation bug.\n";
           Printf.fprintf stdout "%s\n" (Printexc.to_string exn);
           Printf.fprintf stdout "%s" (Printexc.get_backtrace ());
         )
    end;
    (* Any exception at this point is an implementation bug since it means we
       generated an ill-typed System F program *)
    Result.ImplementationBug

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
    Result.WellTyped (Client.translate t)
  with
  | Client.Cycle ty ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: a cyclic type arose.\n";
        print_type ty
       );
     IllTyped
  | Client.NotMono (x, ty) ->
     log_action log (fun () ->
        Printf.fprintf stdout "Type error: unannotated lambda binder %s inferred with polymorphic type:\n" x;
        print_type ty
       );
     IllTyped
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
     IllTyped
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
     IllTyped
  (* JSTOLAREK: other exceptions are thrown due to bugs in the implementation.
     I'm catching them here to simplify testing by not having to comment out
     failing test cases.  No exceptions should ever happen in a correct
     implementation other than Client exceptions, which are used to communicate
     typechecking errors. *)
  | exn ->
     log_action log (fun () ->
        Printf.fprintf stdout "Implementation bug.\n";
        Printf.fprintf stdout "%s\n" (Printexc.to_string exn);
        Printf.fprintf stdout "%s" (Printexc.get_backtrace ());
       );
     ImplementationBug

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
  | IllTyped, None ->
      (* Term is ill typed and is expected to be as such *)
     log_action log (fun () ->
         Printf.printf "Example %s was rejected by the typechecker as expected.\n" name;
       );
     if verbose then
       print_log log;
     Printf.printf "\027[32mExample %s works as expected\027[0m\n" name;
     flush stdout

  | WellTyped (t : F.nominal_term), Some exp_ty ->
      let works = ref false in
      log_action log (fun () ->
        Printf.printf "Formatting the System F term...\n%!";
        let doc = PPrint.(string "  " ^^ nest 2 (FPrinter.print_term t) ^^ hardline) in
        Printf.printf "Pretty-printing the System F term...\n%!";
        PPrint.ToChannel.pretty 0.9 80 stdout doc
      );
      begin
      match attempt log
              "Converting the System F term to de Bruijn style...\n"
              F.translate t with
      | IllTyped -> assert false
      | ImplementationBug ->
         (* Typechecking caused an exception *)
         log_action log (fun () ->
             Printf.printf "Example %s triggered an implementation bug!\n" name;
           );
      | WellTyped t ->
         begin
         match attempt log
                 "Type-checking the System F term...\n"
                 FTypeChecker.typeof t with
         | IllTyped -> assert false
         | ImplementationBug ->
            (* Typechecking caused an exception *)
            log_action log (fun () ->
                Printf.printf "Example %s triggered an implementation bug!\n" name;
              );
         | WellTyped ty ->
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
            works := true
         end;
      end;
      if verbose then
        print_log log;
      if ( !works ) then
        Printf.printf "\027[32mExample %s works as expected\027[0m\n" name
      else
        Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name;
     flush stdout
  | IllTyped, Some exp_ty ->
     log_action log (fun () ->
         Printf.printf "Example %s expected to have a type:\n" name;
         let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type exp_ty ^^ hardline) in
         PPrint.ToChannel.pretty 0.9 80 stdout doc;
         Printf.printf "but was determined ill-typed.\n";
       );
     if verbose then
       print_log log;
     Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name;
     flush stdout

  | WellTyped t, None ->
      log_action log (fun () ->
        Printf.printf "Formatting the System F term...\n%!";
        let doc = PPrint.(string "  " ^^ nest 2 (FPrinter.print_term t) ^^ hardline) in
        Printf.printf "Pretty-printing the System F term...\n%!";
        PPrint.ToChannel.pretty 0.9 80 stdout doc
      );
      begin
      match attempt log
              "Converting the System F term to de Bruijn style...\n"
              F.translate t with
      | IllTyped -> assert false
      | ImplementationBug ->
         (* Typechecking caused an exception *)
         log_action log (fun () ->
             Printf.printf "Example %s triggered an implementation bug!\n" name;
           );
      | WellTyped t ->
         begin
         match attempt log
                 "Type-checking the System F term...\n"
                 FTypeChecker.typeof t with
         | IllTyped -> assert false
         | ImplementationBug ->
            (* Typechecking caused an exception *)
            log_action log (fun () ->
                Printf.printf "Example %s triggered an implementation bug!\n" name;
              );
         | WellTyped ty ->
            log_action log (fun () ->
                Printf.printf "Pretty-printing the System F de Bruijn type...\n%!";
                let doc = PPrint.(string "  " ^^ FPrinter.print_debruijn_type ty ^^ hardline) in
                PPrint.ToChannel.pretty 0.9 80 stdout doc;
                Printf.printf "Example %s epected to be ill-typed but typechecks.\n" name;
              );
         end;
      end;
      if verbose then
        print_log log;
      Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name;
     flush stdout

  | ImplementationBug, _ ->
     (* Typechecking caused an exception *)
     log_action log (fun () ->
         Printf.printf "Example %s triggered an implementation bug!\n" name;
       );
     if verbose then
       print_log log;
     Printf.printf "\027[31mExample %s does not work as expected\027[0m\n" name;
     flush stdout

(* -------------------------------------------------------------------------- *)

let var x =
  ML.Var x

let frozen x =
  ML.FrozenVar x

let app x y =
  ML.App (x, y)

let abs x y =
  ML.abs (x, y)

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

let tru =
  ML.Bool true

let fals =
  ML.Bool false

let forall_a_a_to_a = Some (TyForall (1, TyArrow (TyVar 1, TyVar 1)))

(* FreezeML examples from PLDI paper*)

let (<<) f g x = f(g(x))

(* Environment with some functions from Figure 2 *)

(* id : ∀ a. a → a *)
let fml_id k = ML.let_ ("id", abs "x" x, k)

(* choose : ∀ a. a → a → a *)
let fml_choose k = ML.Let ("choose",
  Some (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1)))),
  abs "x" (abs "y" x), k)

(* auto : (∀ a. a → a) → (∀ a. a → a) *)
let fml_auto k = ML.let_ ("auto", ML.Abs ("x", forall_a_a_to_a,
                                               app x (frozen "x")), k)

(* auto' : (∀ a. a → a) → b → b *)
let fml_autoprim k = ML.let_ ("auto'", ML.Abs ("x", forall_a_a_to_a, app x x), k)

(* app : ∀ a b. (a → b) → a → b *)
let fml_app k = ML.let_ ("app", abs "f" (abs "x" (app f x)), k)

(* revapp : ∀ a b. b → (a → b) → b *)
let fml_revapp k = ML.let_ ("revapp", abs "x" (abs "f" (app f x)), k)

(* zero : Int → Int.  Turns every Int into 0.  This function replaces `inc`
   from FreezeML paper for all intents and purposes, since we only care about
   typing *)
let fml_zero k = ML.let_ ("zero", ML.Abs ("x", Some TyInt, ML.Int 0), k)

(* poly : (∀ a. a → a) → (Int × Bool) *)
let fml_poly k = ML.let_ ("poly", ML.Abs ("f", forall_a_a_to_a,
   ML.Pair (app f one, app f tru)), k)

(* pair : ∀ a b. a → b → (a × b) *)
let fml_pair k = ML.Let ("pair",
  Some (TyForall (1, TyForall (2, TyArrow (TyVar 1, TyArrow (TyVar 2,
                                  TyProduct (TyVar 1, TyVar 2)))))),
  abs "x" (abs "y" (ML.Pair (x, y))), k)

(* pair' : ∀ b a. a → b → (a × b) *)
let fml_pairprim k = ML.Let ("pair'",
  Some (TyForall (2, TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 2,
                                  TyProduct (TyVar 1, TyVar 2)))))),
  abs "x" (abs "y" (ML.Pair (x, y))), k)

let env k = (
    fml_id       <<
    fml_choose   <<
    fml_auto     <<
    fml_autoprim <<
    fml_app      <<
    fml_revapp   <<
    fml_zero     <<
    fml_poly     <<
    fml_pair     <<
    fml_pairprim
  ) k

(* Test basic well-formedness of functions in the environment *)
let env_test =
  { name = "env_test"
  ; term = env (ML.Int 1)
  ; typ  = Some TyInt
  }

(* PLDI paper examples (Figure 2) *)

(* Note: inferno does not permit unbound type variables.  Therefore in the
   inferred types all free type variables are bound at the program's top level.
   In the examples below type variables bound at program top level are placed in
   braces to explicitly mark they are not per se part of the type inferred for
   the term.  Concretely, if the inferred type is:

     [∀ b. ∀ a.] a → b → b

   it means that the inferred type is `a → b → b` and the quantifiers `∀ b. ∀
   a.` are added at the program top level.  *)

(* Section A: Polymorphic instantiation *)

(* example            : A1
   term               : λx.λy.y
   inferred type      : [∀ b. ∀ a.] a → b → b
   type in PLDI paper : a → b → b
*)
let a1 =
  { name = "A1"
  ; term = abs "x" (abs "y" y)
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 0, TyArrow (TyVar 1, TyVar 1)))))
  }

(* example            : A1∘
   term               : $(λx.λy.y)
   inferred type      : ∀ b. ∀ a. a → b → b
   type in PLDI paper : ∀ a b. a → b → b
 *)
let a1_dot =
  { name = "A1̣∘"
  ; term = ML.gen (abs "x" (abs "y" y))
  ; typ  = Some (TyForall ((), TyForall ((),
             TyArrow (TyVar 0, TyArrow (TyVar 1, TyVar 1)))))
  }

(* example            : A2
   term               : choose id
   inferred type      : [∀ a.] (a → a) → (a → a)
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
   inferred type      : [∀ b.] (∀ a. a → a) → b → b
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
   inferred type      : [∀ b.] (∀a. a → a) → b → b
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
   related bugs       : #3
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
           (app poly (ML.gen (abs "x" x)))
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
           (app (app id poly) (ML.gen (abs "x" x)))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* Section B : Inference with Polymorphic arguments *)

(* example            : B1⋆
   term               : λ(f : ∀ a. a → a). (f 1, f True)
   inferred type      : (∀ a. a → a) → Int × Bool
   type in PLDI paper : (∀ a. a → a) → Int × Bool
 *)
let b1_star =
  { name = "B1⋆"
  ; term = ML.Abs ("f", forall_a_a_to_a, ML.Pair (app f one,
                                                  app f tru))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyProduct (TyInt, TyBool)))
  }

(* MISSING : B2⋆: λ(xs : List (∀ a. a → a)). poly (head xs) *)


(* Section C : Functions on Polymorphic Lists *)

(* MISSING: whole section, because lists are not supported *)


(* Section D : Application Functions *)

(* example            : D1⋆
   term               : app poly ~id
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let d1_star =
  { name = "D1⋆"
  ; term = (fml_app << fml_poly << fml_id)
           (app (app (var "app") poly) (frozen "id"))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* example            : D2⋆
   term               : revapp ~id poly
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let d2_star =
  { name = "D2⋆"
  ; term = (fml_revapp << fml_poly << fml_id)
           (app (app (var "revapp") (frozen "id")) poly)
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* MISSING : D3⋆: runST ~argST *)

(* MISSING : D4⋆: app runST ~argST *)

(* MISSING : D5⋆: revapp ~argST runST *)


(* Section E : η-expansion *)

(* MISSING: E1: k h l *)

(* MISSING: E2⋆: k $(λx.(h x)@) l
     where: k : ∀ a. a → List a → a
            h : Int → ∀ a. a → a
            l : List (∀ a. Int → a → a)
 *)

(* example            : E3
   term               : let r : (∀ a. a → (∀ b. b → b)) → Int = λx.1 in r (λx.λy.y)
   inferred type      : X
   type in PLDI paper : X
 *)
let e3 =
  { name = "E3"
  ; term = ML.Let ("r", Some (TyArrow (TyForall (1, TyArrow (TyVar 1,
                          TyForall (2, TyArrow (TyVar 2, TyVar 2)))), TyInt)),
                        abs "x" one,
                   app (var "r") (abs "x" (abs "y" y)))
  ; typ  = None
  }

(* example            : E3∘
   term               : let r : (∀ a. a → (∀ b. b → b)) → Int = λx.1 in r $(λx.$(λy.y))
   inferred type      : Int
   type in PLDI paper : Int
   note               : differs from FreezeML specification, assigns polymorphic
                        type to unannotated binder
 *)
let e3_dot =
  { name = "E3∘"
  ; term = ML.Let ("r", Some (TyArrow (TyForall (1, TyArrow (TyVar 1,
                          TyForall (2, TyArrow (TyVar 2, TyVar 2)))), TyInt)),
                        abs "x" one,
                   app (var "r") (ML.gen (abs "x" (ML.gen (abs "y" y)))))
  ; typ  = Some TyInt
  }

(* Section F : FreezeML Programs *)

(* MISSING: F1-F8.  Either already implemented in previous examples or not
   possible to implement due to lack of support for lists *)

(* example            : F9
   term               : let f = revapp ~id in f poly
   inferred type      : Int × Bool
   type in PLDI paper : Int × Bool
 *)
let f9 =
  { name = "F9"
  ; term = (fml_revapp << fml_id << fml_poly)
           (ML.let_ ("f", app (var "revapp") (frozen "id"), app (var "f") poly))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(* example            : F10†
   term               : choose id (λ(x : ∀ a. a → a). $(auto' ~x))
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
   note               : example in the paper is incorrect since usage of x is
                        not frozen.
 *)
let f10_dagger =
  { name = "F10†"
  ; term = (fml_choose << fml_id << fml_autoprim)
           (app (app choose id) (ML.Abs ("x", forall_a_a_to_a,
                                         ML.gen (app auto' (frozen "x")))))
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)),
                          TyForall ((), TyArrow (TyVar 0, TyVar 0))))
  }

(* Bad examples *)

(* example            : bad1
   term               : λf.(poly ~f, f 1)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad1 =
  { name = "bad1"
  ; term = (fml_poly)
           (abs "f" (ML.Pair (app poly (frozen "f"), app (var "f") one)))
  ; typ  = None
  }

(* example            : bad2
   term               : λf.(f 1, poly ~f)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad2 =
  { name = "bad2"
  ; term = (fml_poly)
           (abs "f" (ML.Pair (app (var "f") one, app poly (frozen "f"))))
  ; typ  = None
  }

(* example            : bad3
   term               : λ(bot : ∀ a. a). let f = bot bot in (poly ~f, f 1)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad3 =
  { name = "bad3"
  ; term = (fml_poly)
           (ML.Abs ("bot", Some (TyForall (1, TyVar 1)),
                    ML.let_ ("f", app (var "bot") (var "bot"),
                             (ML.Pair (app (var "f") one, app poly (frozen "f"))))))
  ; typ  = None
  }

(* example            : bad4
   term               : λ(bot : ∀ a. a). let f = bot bot in (f 1, poly ~f)
   inferred type      : X
   type in PLDI paper : X
 *)
let bad4 =
  { name = "bad4"
  ; term = (fml_poly)
           (ML.Abs ("bot", Some (TyForall (1, TyVar 1)),
                    ML.let_ ("f", app (var "bot") (var "bot"),
                             (ML.Pair (app poly (frozen "f"), app (var "f") one)))))
  ; typ  = None
  }

(* example            : bad5
   term               : let f = λx.x in ~f 1
   inferred type      : X
   type in PLDI paper : X
 *)
let bad5 =
  { name = "bad5"
  ; term = ML.let_ ("f", abs "x" x, app (frozen "f") one)
  ; typ  = None
  }

(* example            : bad6
   term               : let f = λx.x in id ~f 1
   inferred type      : X
   type in PLDI paper : X
 *)
let bad6 =
  { name = "bad6"
  ; term = (fml_id)
           (ML.let_ ("f", abs "x" x, app (app id (frozen "f")) one))
  ; typ  = None
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
  ; term = ML.Abs ("x", forall_a_a_to_a, app x fals)
  ; typ  = Some (TyArrow (TyForall ((), TyArrow (TyVar 0, TyVar 0)), TyBool))
  }

(*
   term : λ(x : bool). false
   type : Bool → Bool
*)
let fml_const_false =
  { name = "const_false"
  ; term = ML.Abs ("x", Some TyBool, fals)
  ; typ  = Some (TyArrow (TyBool, TyBool))
  }

(* Some examples to test correct instantiation of quantified types *)
(*
   term : (let id = λx.x in id) 1
   type : Int
*)
let fml_inst_1 =
  { name = "inst_1"
  ; term = app (ML.let_ ("id", abs "x" x, id)) one
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
   term : let id_int : Int → Int = λx.x in id_int 1
   type : Int
*)
let fml_inst_sig_1 =
  { name = "inst_sig_1"
  ; term = ML.Let ("id_int",
                   Some (TyArrow (TyInt, TyInt)),
                   abs "x" x,
                   app (var "id_int") one)
  ; typ  = Some TyInt
  }

(*
   term : let id_int : Int → Int = λx.x in id_int true
   type : X
*)
let fml_inst_sig_2 =
  { name = "inst_sig_2"
  ; term = ML.Let ("id_int",
                   Some (TyArrow (TyInt, TyInt)),
                   abs "x" x,
                   app (var "id_int") tru)
  ; typ  = None
  }

(*
   term : λ(x : (∀ a. a → a) → (∀ a. a → a)). (x ~id)@ 1
   type : ((∀ a. a → a) → (∀ a. a → a)) → Int
*)
let fml_nested_forall_inst_1 =
  { name = "nested_forall_inst_1"
  ; term = (fml_id)
           (ML.Abs ("x",
                    Some (TyArrow ( TyForall (1, TyArrow (TyVar 1, TyVar 1))
                                  , TyForall (1, TyArrow (TyVar 1, TyVar 1)))),
                    app (ML.inst (app x (frozen "id"))) one))
  ; typ  = Some
      (TyArrow
        (TyArrow ( TyForall ((), TyArrow (TyVar 0, TyVar 0))
                 , TyForall ((), TyArrow (TyVar 0, TyVar 0))), TyInt))
  }

(*
   term : let (f : (∀ a. (∀ b. b → b) → a → a) → (∀ a. (∀ b. b → b) → a → a)) = id in
          let g = f $auto' in
          g ~id
   type : ∀ a. a → a
*)
let fml_nested_forall_inst_2 =
  { name = "nested_forall_inst_2"
  ; term = (fml_id << fml_autoprim)
          ( ML.Let  ( "f"
                    , Some (TyArrow
                            ((TyForall (1, TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1)))),
                             (TyForall (1, TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1))))))
          , id
          , ML.let_ ( "g", app (var "f") (ML.gen auto')
                    , app (var "g") (frozen "id"))))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  }

(*
   term : let (f : ∀ a. ((∀ b. b → b) → a → a) → ((∀ b. b → b) → a → a)) = id in
          let g = f (id auto') in
          g ~id
   type : ∀ a. a → a
*)
let fml_nested_forall_inst_3 =
  { name = "nested_forall_inst_3"
  ; term = (fml_id << fml_autoprim)
           (ML.Let  ( "f"
                    , Some (TyForall (1, (TyArrow
                            (TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1)),
                             TyArrow ((TyForall (2, TyArrow (TyVar 2, TyVar 2))), TyArrow (TyVar 1, TyVar 1))))))
          , id
          , ML.let_ ( "g", app (var "f") (app id auto')
                    , app (var "g") (frozen "id"))))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  }


(* Correctness of type annotations on let binders *)
(*
   term : let (id : ∀ a. a → a) = λx.x in id
   type : ∀ a. a → a
*)
let fml_id_annot_1 =
  { name = "id_annot_1"
  ; term = ML.Let ("id", Some (TyForall (1, TyArrow (TyVar 1, TyVar 1)))
                       , abs "x" x, id)
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  }

(*
   term : let (id : ∀ a b. a → b) = λx.x in id
   type : X
*)
let fml_id_annot_2 =
  { name = "id_annot_2"
  ; term = ML.Let ("id", Some (TyForall (1, TyForall (2,
                                TyArrow (TyVar 1, TyVar 2))))
                       , abs "x" x, id)
  ; typ  = None
  }

(*
   term : let (id : ∀ a. a → a) = λ(x : Int).x in id
   type : X
*)
let fml_id_annot_3 =
  { name = "id_annot_3"
  ; term = ML.Let ("id", Some (TyForall( 1, TyArrow (TyVar 1, TyVar 1))),
                   ML.Abs ("x", Some TyInt , x), id)
  ; typ  = None
  }

(*
   term : let id = λx.x in let (y : ∀ a. a → a) = ~id in y
   type : ∀ a. a → a
*)
let fml_id_annot_4 =
  { name = "id_annot_4"
  ; term = ML.let_ ("id", abs "x" x,
      ML.Let ("y", Some (TyForall (1, TyArrow (TyVar 1, TyVar 1))),
                   frozen "id", y))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  }

(*
   term : let id = λx.x in let (choose : ∀a b. a → b → b) = λx.λy.x in choose id
   type : X
*)
let fml_id_annot_5 =
  { name = "id_annot_5"
  ; term = ML.let_ ("id", abs "x" x,
      ML.Let ("choose", Some (TyForall (1, TyForall (2, TyArrow (TyVar 1,
                                             TyArrow (TyVar 2, TyVar 2))))),
                   abs "x" (abs "y" x), app choose id))
  ; typ  = None
  }

(*
   term : λx. choose ~id x
   type : X
*)
let fml_mono_binder_constraint_1 =
  { name = "mono_binder_constraint_1"
  ; term = (fml_choose << fml_id)
           (abs "x" (app (app choose (frozen "id")) x))
  ; typ  = None
  }

(*
   term : let f = λx.x 1 in f
   type : ∀ a. (Int → a) → a
*)
let fml_mono_binder_constraint_2 =
  { name = "mono_binder_constraint_2"
  ; term = ML.let_ ("f", abs "x" (app (var "x") one), var "f")
  ; typ  = Some (TyForall ((), TyArrow (TyArrow (TyInt, (TyVar 0)), TyVar 0)))
  }

(*
   term : (λ(f : ∀ a b. a → b → (a × b)). f 1 true) ~pair
   type : Int × Bool
*)
let fml_quantifier_ordering_1 =
  { name = "quantifier_ordering_1"
  ; term = (fml_pair)
           (app (ML.Abs ("f", Some (TyForall (1, TyForall (2,
                                      TyArrow (TyVar 1, TyArrow (TyVar 2,
                                      TyProduct (TyVar 1, TyVar 2))))))
                            , app (app (var "f") one) tru))
                (frozen "pair"))
  ; typ  = Some (TyProduct (TyInt, TyBool))
  }

(*
   term : (λ(f : ∀ a b. a → b → (a × b)). f 1 true) ~pair'
   type : X
   bugs : #3
*)
let fml_quantifier_ordering_2 =
  { name = "quantifier_ordering_2"
  ; term = (fml_pairprim)
           (app (ML.Abs ("f", Some (TyForall (1, TyForall (2,
                                      TyArrow (TyVar 1, TyArrow (TyVar 2,
                                      TyProduct (TyVar 1, TyVar 2))))))
                            , app (app (var "f") one) tru))
                (frozen "pair'"))
  ; typ  = None
  }

(*
   term : let (x : (∀ a. a → a) → Int) = λ(f : ∀ a. a → a). f 1 in 1
   type : Int
   bugs : #2
*)
let fml_type_annotations_1 =
  { name = "type_annotations_1"
  ; term = ML.Let ("x",
                   Some (TyArrow (TyForall (1, TyArrow (TyVar 1, TyVar 1)),
                                  TyInt)),
                   ML.Abs ("f", forall_a_a_to_a, app (var "f") one), one)
  ; typ  = Some TyInt
  }

(*
   term : let id = λx.x in ~id 1
   type : ∀ a. a → a
*)
let fml_id_appl =
  { name = "id_annot_1"
  ; term = ML.let_ ("id", abs "x" x, app (frozen "id") one)
  ; typ  = None
  }

(*
   term : choose ~choose
   type : (∀ a. a → a → a) → (∀ a. a → a → a)
*)
let fml_choose_choose =
  { name = "choose_choose"
  ; term = (fml_choose)
           (app choose (frozen "choose"))
  ; typ  = Some (TyArrow
               ((TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0)))),
                (TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))))
  }

(*
   term : let (f : (∀ a. a → a → a) → (∀ a. a → a → a)) = choose ~choose
          in f ~choose
   type : ∀ a. a → a → a
*)
let fml_choose_choose_let =
  { name = "choose_choose_let"
  ; term = (fml_choose)
  (ML.Let ( "f"
          , Some (TyArrow
                ((TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1)))),
                 (TyForall (1, TyArrow (TyVar 1, TyArrow (TyVar 1, TyVar 1))))))
          , app choose (frozen "choose")
          , app (var "f") (frozen "choose")))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
  }


(*
   term : (λx.x) ~auto
   type : ∀ a. a → a
   note : differs from FreezeML specification, assigns polymorphic type to
          unannotated binder
*)
let fml_id_auto_1 =
  { name = "id_auto_1"
  ; term = (fml_auto)
           (app (abs "x" x) (frozen "auto"))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  }


(*
   term : (id (λx.x)) ~auto
   type : ∀ a. a → a
   note : differs from FreezeML specification, assigns polymorphic type to
          unannotated binder
*)
let fml_id_auto_2 =
  { name = "id_auto_2"
  ; term = (fml_auto << fml_id)
           (app (app id (abs "x" x)) (frozen "auto"))
  ; typ  = Some (TyForall ((), TyArrow (TyVar 0, TyVar 0)))
  }


let () =
  test env_test;
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

  test b1_star;

  test d1_star;
  test d2_star;

  test e3;
  test e3_dot;

  test f9;
  test f10_dagger;

  test bad1;
  test bad2;
  test bad3;
  test bad4;
  test bad5;
  test bad6;

  (* Other examples *)
  test fml_id_to_int;
  test fml_id_to_bool;
  test fml_const_false;
  test fml_inst_1;
  test fml_inst_2;
  test fml_inst_sig_1;
  test fml_inst_sig_2;
  test fml_nested_forall_inst_1;
  test fml_nested_forall_inst_2;
  test fml_nested_forall_inst_3;
  test fml_id_annot_1;
  test fml_id_annot_2;
  test fml_id_annot_3;
  test fml_id_annot_4;
  test fml_id_annot_5;
  test fml_mono_binder_constraint_1;
  test fml_mono_binder_constraint_2;
  test fml_quantifier_ordering_1;
  test fml_quantifier_ordering_2;
  test fml_type_annotations_1;
  test fml_id_appl;
  test fml_choose_choose;
  test fml_choose_choose_let;
  test fml_id_auto_1;
  test fml_id_auto_2
