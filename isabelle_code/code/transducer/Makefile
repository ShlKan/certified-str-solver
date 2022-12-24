
ori2cava: ori.mly orilex.mll main.ml trans.mli
	ocamlopt -I zarith -c Automata_lib.ml
	ocamlopt -I zarith -c Automata.ml
	ocamlopt -I zarith -c main.ml
	ocamlopt -I zarith -o transducer zarith/zarith.cmxa str.cmxa Automata_lib.cmx Automata.cmx main.cmx

#	ocamlopt -I zarith -o forward_analysis -verbose -ccopt -static -ccopt -Wl,--no-export-dynamic -ccopt -static-libgcc zarith/zarith.cmxa str.cmxa orilex.cmx ori.cmx Automata_lib.cmx Forward.cmx main.cmx



clean:
	rm -f *~ *.cmo *.cmi *.o *.cmx forward_analysis

