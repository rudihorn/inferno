let enable_debug = true

let print message =
  (if enable_debug then prerr_endline message; flush stderr)
