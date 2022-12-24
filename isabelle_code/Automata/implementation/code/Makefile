
auto: Automata_lib.ml Automata.ml test.ml
	ocamlc -I zarith -c Automata_lib.ml
	ocamlc -I zarith -c Automata.ml
	ocamlc -c test.ml
	ocamlc -o auto zarith/zarith.cma Automata_lib.cmo Automata.cmo test.cmo

clean:
	rm -f *~
	rm -f result
	rm -f tests/*.ml
