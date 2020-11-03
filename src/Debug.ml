let enabled     = false
let hard        = true
let print_ranks = true
let fuel        = 8

(* JSTOLAREK: swap print_doc and print names since print_doc is used frequently
   and should be shorter *)
let print message =
  if enabled then prerr_endline message;
  flush stderr

let print_doc doc =
  if enabled then
    PPrint.(ToChannel.pretty 0.9 80 stderr (doc ^^ hardline));
  flush stderr

(* Only enabled detailed debuf if debug enabled *)
let hard = enabled && hard
