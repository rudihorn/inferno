open Client

let verbose =
  true

(* -------------------------------------------------------------------------- *)

(* A random generator of pure lambda-terms. *)

let int2var k =
  "x" ^ string_of_int k

(* [split n] produces two numbers [n1] and [n2] comprised between [0] and [n]
   (inclusive) whose sum is [n]. *)

let split n =
  let n1 = Random.int (n + 1) in
  let n2 = n - n1 in
  n1, n2

(* The parameter [k] is the number of free variables; the parameter [n] is the
   size (i.e., the number of internal nodes). *)

let rec random_ml_term k n =
  if n = 0 then begin
    assert (k > 0);
    ML.Var (int2var (Random.int k))
  end
  else
    let c = Random.int 5 (* Abs, App, Pair, Proj, Let *) in
    if k = 0 || c = 0 then
      (* The next available variable is [k]. *)
      let x, k = int2var k, k + 1 in
      ML.Abs (x, None, random_ml_term k (n - 1))
    else if c = 1 then
      let n1, n2 = split (n - 1) in
      ML.App (random_ml_term k n1, random_ml_term k n2)
    else if c = 2 then
      let n1, n2 = split (n - 1) in
      ML.Pair (random_ml_term k n1, random_ml_term k n2)
    else if c = 3 then
      ML.Proj (1 + Random.int 2, random_ml_term k (n - 1))
    else if c = 4 then
      let n1, n2 = split (n - 1) in
      ML.Let (int2var k, None, random_ml_term k n1, random_ml_term (k + 1) n2)
    else
      assert false

let rec size accu = function
  | ML.Var _ ->
      accu
  | ML.FrozenVar _ ->
      accu
  | ML.Abs (_, _, t)
  | ML.Proj (_, t)
    -> size (accu + 1) t
  | ML.App (t1, t2)
  | ML.Let (_, _, t1, t2)
  | ML.Pair (t1, t2)
    -> size (size (accu + 1) t1) t2
  | ML.Int _ -> accu
  | ML.Bool _ -> accu

let size =
  size 0

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

let test (t : ML.term) : bool =
  let log = create_log() in
  Printf.printf "\n===========================================\n\n%!";
  let outcome =
    attempt log
      "Type inference and translation to System F...\n"
      translate t
  in
  match outcome with
  | None ->
      (* This term is ill-typed. This is considered a normal outcome, since
         our terms can be randomly generated. *)
      false
  | Some (t : F.nominal_term) ->
      log_action log (fun () ->
        Printf.printf "Formatting the System F term...\n%!";
        let doc = PPrint.(FPrinter.print_term t ^^ hardline) in
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
        let doc = PPrint.(FPrinter.print_debruijn_type ty ^^ hardline) in
        PPrint.ToChannel.pretty 0.9 80 stdout doc
      );
      (* Everything seems to be OK. *)
      if verbose then
        print_log log;
      true

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
let a1 = ML.abs ("x", ML.abs ("y", y))

(* example            : A1∘
   term               : $(λx y.y)
   inferred type      : ∀ b. ∀ a. a → b → b
   type in PLDI paper : ∀ a b. a → b → b
 *)
let a1_dot = ML.gen (ML.abs ("x", ML.abs ("y", y)))

(* example            : A2
   term               : choose id
   inferred type      : INCORRECT ∀b. ∀a. a → b → b
   type in PLDI paper : (a → a) → (a → a)
 *)
let a2 = env (app choose id)

(* example            : A2∘
   term               : choose ~id
   inferred type      : INCORRECT ∀a. a → ∀b. b → b
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a2_dot = env (app choose (frozen "id"))

(* MISSING: A3: choose [] ids *)

(* example            : A4
   term               : λ(x : ∀ a. a → a). x x
   inferred type      : ∀b. (∀a. a → a) → b → b
   type in PLDI paper : (∀ a. a → a) → (b → b)
 *)
let a4 = ML.Abs ("x", forall_a_a_to_a, app x x)

(* example            : A4̣∘
   term               : λ(x : ∀ a. a → a). x ~x
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a4_dot = ML.Abs ("x", forall_a_a_to_a, app x (frozen "x"))

(* example            : A5
   term               : id auto
   inferred type      : (∀ a. a → a) → (∀ a. a → a)
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a5 = env (app id auto)

(* example            : A6
   term               : id auto'
   inferred type      : ∀b. (∀a. a → a) → b → b
   type in PLDI paper : (∀ a. a → a) → (b → b)
 *)
let a6 = env (app id auto')

(* example            : A6∘
   term               : id ~auto'
   inferred type      : ∀ b. (∀ a. a → a) → (b → b)
   type in PLDI paper : ∀ b. (∀ a. a → a) → (b → b)
 *)
let a6_dot = env (app id (frozen "auto'"))

(* example            : A7
   term               : choose id auto
   inferred type      : INCORRECT ∀ a. a → a
   type in PLDI paper : (∀ a. a → a) → (∀ a. a → a)
 *)
let a7 = env (app (app choose id) auto)

(* example            : A8
   term               : choose id auto'
   inferred type      : INCORRECT ∀ b. ∀ a. a → a
   type in PLDI paper : X
 *)
let a8 = env (app (app choose id) auto')

(* MISSING : A9⋆: f (choose ~id) ids *)

(* example            : A10⋆
   term               : poly ~id
   inferred type      : FAILED ASSERTION
   type in PLDI paper : Int × Bool
 *)
let a10_star = env (app poly (frozen "id"))

(* example            : A11⋆
   term               : poly $(λx. x)
   inferred type      : FAILED ASSERTION
   type in PLDI paper : Int × Bool
 *)
let a11_star = env (app poly (ML.gen (ML.abs ("x", x))))

(* example            : A12⋆
   term               : id poly $(λx. x)
   inferred type      : FAILED ASSERTION
   type in PLDI paper : Int × Bool
 *)
let a12_star = env (app (app id poly) (ML.gen (ML.abs ("x", x))))

(* Examples that were not in the PLDI paper *)

(* This was causing an exception in FTypeChecker because I didn't extend type
   equality checker with TyInt *)
let fml_id1   = ML.Abs ("x", forall_a_a_to_a, app x (ML.Int 1))
(* Two simple functions to test correctness of Bool implementation *)
let fml_false = ML.Abs ("x", Some ([], F.TyBool), ML.Bool false)
let fml_id2   = ML.Abs ("x", forall_a_a_to_a, app x (ML.Bool false))


let () =
  (* FreezeML examples *)
  assert (test a1);
  assert (test a1_dot);
  assert (test a2);
  assert (test a2_dot);
  assert (test a4);
  assert (test a4_dot);
  assert (test a5);
  assert (test a6);
  assert (test a6_dot);
  assert (test a7);
  assert (test a8)
(*
  assert (test a10_star)
  assert (test a11_star)
  assert (test a12_star)
*)

(*
  assert (test fml_id1);
  assert (test (env a1));
  assert (test fml_id2);
  assert (test fml_false)
*)

(* -------------------------------------------------------------------------- *)

(* Random testing. *)

(* A list of pairs [m, n], where [m] is the number of tests and [n] is the
   size of the randomly generated terms. *)

(*
let pairs = [
    0, 5;
  100000, 5;
  100000, 10;
  100000, 15;
  100000, 20;
  100000, 25; (* at this size, about 1% of the terms are well-typed *)
  100000, 30;
  (* At the following sizes, no terms are well-typed! *)
   10000, 100;
   10000, 500;
    1000, 1000;
     100, 10000;
      10, 100000;
       1, 1000000;
]

let () =
  Printf.printf "Preparing to type-check a bunch of randomly-generated terms...\n%!";
  Random.init 0;
  let c = ref 0 in
  let d = ref 0 in
  List.iter (fun (m, n) ->
    for i = 1 to m do
      if verbose then
        Printf.printf "Test number %d...\n%!" i;
      let t = random_ml_term 0 n in
      assert (size t = n);
      let success = test t in
      if success then incr c;
      incr d
    done
  ) pairs;
  Printf.printf "In total, %d out of %d terms were considered well-typed.\n%!" !c !d;
  Printf.printf "No problem detected.\n%!"
*)
