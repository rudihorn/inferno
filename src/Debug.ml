let enable_debug = true

let print message =
  if enable_debug then prerr_endline message; flush stderr

let print_doc doc =
  if enable_debug then
    PPrint.(ToChannel.pretty 0.9 80 stderr (doc ^^ hardline)); flush stderr
