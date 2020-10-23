let enabled     = false
let hard        = false
let print_ranks = true
let fuel        = 5

let print message =
  if enabled then prerr_endline message;
  flush stderr

let print_doc doc =
  if enabled then
    PPrint.(ToChannel.pretty 0.9 80 stderr (doc ^^ hardline));
  flush stderr

(* Only enabled detailed debuf if debug enabled *)
let hard = enabled && hard
