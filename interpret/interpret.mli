class ['a] channel :
  object
    val mutable input : (bool * ('a -> unit)) list
    val mutable output : ('a * (unit -> unit)) list
    method dequeue_input : unit -> (bool * ('a -> unit)) option
    method dequeue_output : unit -> ('a * (unit -> unit)) option
    method enqueue_input : bool -> ('a -> unit) -> unit
    method enqueue_output : 'a -> (unit -> unit) -> unit
  end
val zeroP : unit
val nuP : ('a channel -> 'b) -> 'b
val nuPl : ('a channel -> 'b) -> 'b
val parP : 'a * 'b -> unit
val outP :
  'a *
  < dequeue_input : unit -> (bool * ('b -> 'c)) option;
    enqueue_input : bool -> ('b -> 'c) -> unit;
    enqueue_output : 'b -> (unit -> 'd) -> unit; .. > *
  'b * (unit -> 'd) -> unit
val inP :
  'a *
  < dequeue_output : unit -> ('b * (unit -> 'c)) option;
    enqueue_input : bool -> ('b -> 'd) -> unit; .. > *
  ('b -> 'd) -> unit
val rinP :
  'a *
  < dequeue_output : unit -> ('b * (unit -> 'c)) option;
    enqueue_input : bool -> ('b -> 'd) -> 'e; .. > *
  ('b -> 'd) -> unit
