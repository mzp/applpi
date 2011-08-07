open Interpret

let rec fib n res = 
  if n=1 then 
    (outP (false, res, 1, fun _ -> zeroP)) 
  else 
    if n=2 then 
      (outP (false, res, 1, fun _ -> zeroP))
    else 
      (nuP (fun r1 -> 
	      (nuP (fun r2 -> 
		      (parP ((fib (n-2) r1),
			 (parP ((fib (n-1) r2),
			    (inP (false, r1, (fun v1 -> 
						(inP (false, r2, (fun v2 -> 
								    (outP (false, res, v1+v2, fun _ -> zeroP))))))))))))))))


let main () =
  let r = new channel in
  let p = new channel in
    (parP ((fib 20 r), 
	   (inP (false, r, (fun v -> print_int v; zeroP)))))
;;

main ();;
  

