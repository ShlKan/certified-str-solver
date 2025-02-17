# A Certified String Solver

CertiStr is a certified string solver developed by [Isabelle proof assistant](https://isabelle.in.tum.de/) and [OCaml](https://ocaml.org/).

## Isabelle Code

All the formalizations and proofs can be found in [isabelle_code](isabelle_code).
The proofs related to Symbolic Finite Transducers (SFT) have been upgraded to [Isabelle 2024](https://isabelle.in.tum.de/)
There are still some other proofs that have not been upgraded.

To run the proofs of SFTs, open the theory `isabelle_code/Automata/implementation/RBT_CodeExport.thy`


## Compile CertiStr

CertiStr's front-end (not certified) is developed based on (1) [dolmen](https://github.com/Gbury/dolmen) and (2)
[ocaml-re-nfa](https://github.com/ShlKan/ocaml-re-nfa).
Note that The original [ocaml-re-nfa](https://github.com/yallop/ocaml-re-nfa) does not support symbolic finite automata.
You must install the branch in my repo.

We use `dune` to manage the project. To build, jump into the [CertiStr]{CertiStr} folder and run `dune build`. 
To test (cram test), run `dune runtest`.

The automatically generated OCaml code for SFTs from Isabelle can be found in [Generated Code](CertiStr/lib/automata
/Automata_lib.ml)



## Papers
1. [Shuanglong Kan, Anthony Widjaja Lin, Philipp Rümmer, Micha Schrader:
CertiStr: a certified string solver. CPP 2022: 210-224](https://arxiv.org/abs/2112.06039) [Distinguished Paper Award]
