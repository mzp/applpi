# usage: 
# "make PRG=program_name direct"
# "make PRG=program_name pretty"

CC = ocamlc

interpret.cmi:
	$(CC) -c interpret.mli

interpret.cmo: interpret.cmi
	$(CC) -c interpret.ml

rules.cmo: 
	ocamlc -pp "camlp4o pa_extend.cmo q_MLast.cmo" \
	-I `camlp4 -where` -I . -c rules.ml

direct.cmo: rules.cmo
	ocamlc -pp "camlp4o ./rules.cmo" -c $(PRG).ml

direct: interpret.cmo direct.cmo
	ocamlc -o $(PRG) interpret.cmo $(PRG).cmo

pretty.ml: rules.cmo
	camlp4o ./rules.cmo pr_o.cmo $(PRG).ml -o $(PRG)_pretty.ml

pretty.cmo: pretty.ml
	$(CC) -c $(PRG)_pretty.ml

pretty: interpret.cmo pretty.cmo
	$(CC) -o $(PRG)_pretty interpret.cmo $(PRG)_pretty.ml

clean:
	rm -fr *.cm[iox] *.o




