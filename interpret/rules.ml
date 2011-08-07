open Pcaml
  
  EXTEND
  
  expr: LEVEL "apply"
    [
      [ "ZeroP" -> <:expr< zeroP >> ]

    | [ "NuP"; e=expr -> <:expr< nuP $e$ >> ]
	
    | [ "NuPl"; e=expr -> <:expr< nuPl $e$ >> ]
  
    | [ "ParP"; "("; e=expr; ")" -> <:expr< parP $e$ >> ]

    | [ "InP"; "("; e=expr; ")" -> 
		<:expr< inP $e$ >> ]

    | [ "RinP"; "("; e=expr; ")" -> <:expr< rinP $e$ >> ]

    | [ "OutP"; "("; e=expr LEVEL "apply"; ","; f=expr LEVEL "apply"; 
	","; g=expr LEVEL "apply"; ","; h=expr LEVEL "apply"; ")" ->  
		 <:expr< outP ($e$, $f$, $g$, fun _ -> $h$) >> ]

    | [ UIDENT "True" -> <:expr< True >> ] 
    
    | [ UIDENT "False" -> <:expr< False >> ]

]
  ;

  END
