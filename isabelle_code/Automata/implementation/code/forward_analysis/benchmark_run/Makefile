
ori2cava: ori.mly orilex.mll main.ml trans.mli 
	ocamlopt -c trans.mli
	ocamllex orilex.mll
	ocamlyacc ori.mly
	ocamlopt -c ori.mli
	ocamlopt -c ori.ml
	ocamlopt -c orilex.ml
	ocamlopt -I zarith -c Automata_lib.ml
	ocamlopt -I zarith -c Forward.ml
	ocamlopt -I zarith -c main.ml
	ocamlopt -I zarith -o forward_analysis zarith/zarith.cmxa str.cmxa orilex.cmx ori.cmx Automata_lib.cmx Forward.cmx main.cmx


clean:
	rm -f *~ *.cmo *.cmi *.o *.cmx

