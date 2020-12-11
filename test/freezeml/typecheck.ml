open Client.Syntax

module Lang = Client.Lang
module FPrinter = Client.FPrinter

let print_ml_term m =
  PPrint.(ToChannel.pretty 0.9 80 stdout (Client.MLPrinter.print_term m ^^ hardline))

let typecheck term =
   let term = Lang.translate term in
   FPrinter.print_term term
   |> PPrint.ToChannel.pretty 0.9 80 stdout;
   reset ()

let%expect_test "id" =
  abs (fun x -> x)
  |> typecheck;
  [%expect {| Λ1. λ(v0 : 1). v0 |}]


let%expect_test "poly_id" =
  let term =
    let@ id = abs (fun x -> x) in
    app (app id id) id in
  typecheck term;
  [%expect {|
    Λ18. let v1 = Λ11. λ(v0 : 11). v0 in
    v1 [(18 → 18) → 18 → 18] (v1 [18 → 18]) (v1 [18]) |}]

let%expect_test "id" =
  let term =
    let@ id = abs (fun x -> x) in
    app (app id id) (i 5) in
  typecheck term;
  [%expect {|
    let v1 = Λ28. λ(v0 : 28). v0 in
    v1 [Int → Int] (v1 [Int]) 5 |}]

let%expect_test "frozen_id" =
  let term =
    let@ id = abs (fun x -> x) in
    let@ fid = ~% id in
    app (app fid fid) (i 5) in
  typecheck term;
  [%expect {|
    let v1 = Λ45. λ(v0 : 45). v0 in
    let v2 = v1 in
    v2 [Int → Int] (v2 [Int]) 5 |}]

let%expect_test "choose" =
  let term =
    let@ pick1 = abs2 (fun x _ -> x) in
    let@ _pick2 = abs2 (fun _ y -> y) in
    let@ choose = ~% pick1 in
    app2 choose (i 5) (ctrue) in
  typecheck term;
  [%expect {|
    let v2 = Λ74. Λ76. λ(v0 : 74). λ(v1 : 76). v0 in
    let v5 = Λ68. Λ66. λ(v3 : 66). λ(v4 : 68). v4 in
    let v6 = v2 in
    v6 [Int] [Bool] 5 true |}]

let%expect_test "poly" =
  let term =
    let@ poly = abs ~typ:(forall (fun a -> a --> a))
        (fun f -> app (app f f) (i 5)) in
    let@ id = abs (fun x -> x) in
    app poly (~% id) in
   typecheck term;
   [%expect {|
     let v1 = λ(v0 : ∀ [113]. 113 → 113). v0 [Int → Int] (v0 [Int]) 5 in
     let v3 = Λ94. λ(v2 : 94). v2 in
     v1 v3 |}]

