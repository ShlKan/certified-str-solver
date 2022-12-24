
ori2cava: ori.mly orilex.mll main.ml trans.mli 
	ocamlc -c trans.mli
	ocamllex orilex.mll
	ocamlyacc ori.mly
	ocamlc -c ori.mli
	ocamlc -c ori.ml
	ocamlc -c orilex.ml
	ocamlc -I zarith -c Automata_lib.ml
	ocamlc -I zarith -c Forward.ml
	ocamlc -I zarith -c main.ml
	ocamlc -I zarith -o forward_analysis zarith/zarith.cmxa str.cmxa orilex.cmx ori.cmx Automata_lib.cmx Forward.cmx main.cmx


clean:
	rm -f *~ *.cmo *.cmi *.o *.cmx

