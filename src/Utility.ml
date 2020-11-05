let rec unduplicate equal = function
  | [] -> []
  | elem :: elems -> (let _, others = List.partition (equal elem) elems in
                      elem :: unduplicate equal others)
