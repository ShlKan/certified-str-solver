
ori2cava: ori.mly orilex.mll main.ml trans.mli 
	ocamlc -c trans.mli
	ocamllex orilex.mll
	ocamlyacc ori.mly
	ocamlc -c ori.mli
	ocamlc -c ori.ml
	ocamlc -c orilex.ml
	ocamlc -c main.ml
	ocamlc -o ori2cava str.cma orilex.cmo ori.cmo main.cmo


clean:
	rm -f *~ tests/*~

