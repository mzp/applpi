open Interpret

let rec ack n p r = 
  if n = 0 then 
    (outP (false, r, p+1, fun _ -> zeroP))
  else
    if p = 0 then 
      (ack (n-1) 1 r)
    else
      (nuP (fun r1 ->
	      (parP ((ack n (p-1) r1),
		     (inP (false, r1, (fun pp -> (ack (n-1) pp r))))))))

let main () =
  let res = new channel in 
    (parP ((ack 4 1 res), (inP (false, res, (fun v -> print_int v; (outP (false, res, v, fun _ -> zeroP)))))))
;;

main ();;
  

