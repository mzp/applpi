class ['a] channel =
    object(self)
      val mutable input : (bool * ('a -> unit)) list = []
      val mutable output : ('a * (unit -> unit)) list = [] 

      method enqueue_output v k =
	output <- output @ [(v, k)]
      method dequeue_output () =
	match output with 
	    h::t -> output <- t; Some (h) 
	  | [] -> None

      (* false for a replicated input, true otherwise *)
      method enqueue_input flag r =
	input <- input @ [(flag, r)]
      method dequeue_input () =
	match input with 
	    (flag,r)::tl -> input <- tl; Some (flag, r) 
	  | [] -> None
    end

let zeroP = ()

let nuP cont = let c = new channel in cont c

let nuPl cont = let c = new channel in cont c

let parP (p, q) = ()
	
let outP (b, c, v, cont) =
    match c#dequeue_input () with
	Some (flag, r) -> if flag then 
	  parP (r v, (cont ())) 
	else 
	  (c#enqueue_input false r; parP (r v, (cont ())))
      | None -> c#enqueue_output v cont

let inP (b, c, r) = 
  match c#dequeue_output () with
      Some (v, cont) -> parP (r v, (cont ()))
    | None -> c#enqueue_input true r

let rinP (b, c, r) =
  c#enqueue_input false r;
  match c#dequeue_output () with
      Some (v, cont) -> parP (r v, (cont ()))
    | None -> ()
