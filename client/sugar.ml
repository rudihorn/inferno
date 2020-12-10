module ML = Lang.ML

let nextFresh = ref 0

let reset () = nextFresh := 0

let fresh () =
  let v = !nextFresh in
  nextFresh := v + 1;
  "v" ^ (string_of_int v)

let var x = ML.Var x

let frozen x = ML.FrozenVar x

let abs e =
  let v = fresh () in
  ML.abs (v, e (var v))

let abs2 e =
  let v1 = fresh() in
  let v2 = fresh() in
  ML.abs (v1, ML.abs (v2, e (var v1) (var v2)))

let abs3 e =
  let v1 = fresh() in
  let v2 = fresh() in
  let v3 = fresh() in
  ML.abs (v1, ML.abs (v2, ML.abs (v3, e (var v1) (var v2) (var v3))))

let app x y = ML.App (x, y)

let app2 x y z = ML.App (ML.App (x, y), z)

let app3 f x y z = ML.App (ML.App (ML.App (f, x), y), z)

let (let@) x y =
  let v = fresh () in
  ML.let_ (v, x, y (var v))

let (let@@) (v, x) y =
  ML.let_ (v, x, y (var v))

let i v = ML.Int v

let ctrue = ML.Bool true

let cfalse = ML.Bool false

let (~%) v = match v with | ML.Var v -> ML.FrozenVar v  | _ -> failwith "Cannot freeze v."
