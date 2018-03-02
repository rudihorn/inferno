val iter: ('a -> unit) -> 'a option -> unit

val fold: ('a -> 'b -> 'b) -> 'a option -> 'b -> 'b

val map: ('a -> 'b) -> 'a option -> 'b option

val multiply: ('a -> 'a -> 'a) -> 'a option -> 'a option -> 'a option

