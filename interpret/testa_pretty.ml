open Interpret

(* Definition P := (nuP [x:?](outP x (0) zeroP)).

Recursive Extraction P. *)

(******************************** code generated by Coq **********************)

type bool =
    True
  | False

(*type proc =
  | ZeroP
  | InP of bool * Obj.t * (Obj.t -> proc)
  | RinP of bool * Obj.t * (Obj.t -> proc)
  | OutP of bool * Obj.t * Obj.t * proc
  | ParP of proc * proc
  | NuP of (Obj.t -> proc)
  | NuPl of (Obj.t -> proc)*)

type nat =
    O
  | S of nat

let p = nuP (fun x -> outP (false, x, O, (fun _ -> print_string "coucou\n"; zeroP)))

(********************************* entry point ***********************************)

let main () = p

let _ = main ()

