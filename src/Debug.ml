let enabled = true

let print_ranks = false

let print message =
  if enabled then prerr_endline message; flush stderr

let print_doc doc =
  if enabled then
    PPrint.(ToChannel.pretty 0.9 80 stderr (doc ^^ hardline)); flush stderr

let fuel = 4
