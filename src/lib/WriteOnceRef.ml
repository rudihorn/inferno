type 'a t =
  'a option ref

let create () =
  ref None

let set r x =
  match !r with
  | None ->
      r := Some x
  | Some _ ->
      (* error: double write! *)
      assert false

let get r =
  match !r with
  | None ->
      (* error: read before write! *)
      assert false
  | Some x ->
      x

