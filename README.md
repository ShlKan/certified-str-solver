# A Certified String Solver

CertiStr is a certified string solver developed by [Isabelle proof assistant](https://isabelle.in.tum.de/) and [OCaml](https://ocaml.org/).

## Isabelle Code

All the formalizations and proofs can be found in [isabelle_code](isabelle_code).
The proofs related to Symbolic Finite Transducers (SFT) have been upgraded to [Isabelle 2024](https://isabelle.in.tum.de/)
There are still some other proofs that have not been upgraded.

To run the proofs of SFTs, open the theory `isabelle_code/Automata/implementation/RBT_CodeExport.thy`

1. The abstract-level transducer is defined in [Transducer_new.thy](isabelle_code/Automata/Transducer_new.thy).
2. The implementation-level transducer is defined in [Transducer_Impl_new.thy](isabelle_code/Automata/implementation/Transducer_Impl_new.thy).
3. The abstract-level epsilon-SFA is defined in [NFA_epsilon.thy](isabelle_code/Automata/NFA_epsilon.thy).
4. The implementation-level epsilon-SFA is defined in [Epsilon_Elim_Imp.thy](isabelle_code/Automata/implementation/Epsilon_Elim_Imp.thy).
5. Interval is defined in [Interval.thy](isabelle_code/Automata/implementation/Interval.thy).


## Compile CertiStr

CertiStr's front-end (not certified) is developed based on (1) [dolmen](https://github.com/Gbury/dolmen) and (2)
[ocaml-re-nfa (my branch)](https://github.com/ShlKan/ocaml-re-nfa).
Note that, the original [ocaml-re-nfa](https://github.com/yallop/ocaml-re-nfa) does not support symbolic finite automata.
You must install the branch in my repo (`opam install [path to ocaml-re-nfa]`).

We use `dune` to manage the project. To build, jump into the [CertiStr](CertiStr) folder and run `dune build`. 
To test (cram test), run `dune runtest`.

The automatically generated OCaml code for SFTs from Isabelle can be found in [Generated Code](CertiStr/lib/automata/Automata_lib.ml)


**Note that:**

The semantics of the replacement operation of our certified string solver is different from standard SMT-LIB semantics.
Therefore, the results of running the tests and benchmarks in the repo may differ from other string solvers, such as CVC5 and Z3.

Given the following string replacement operation:
`str.replace_re a (re.+ (re.range "0" "9")) "NUM"` 
1. The standard SMT-LIB semantics will replace the **first** occurrence of the pattern `(re.+ (re.range "0" "9"))` in `a`.
2. The semantics in CertiStr are not limited to the first occurrence. 

## Papers
1. [Shuanglong Kan, Anthony Widjaja Lin, Philipp Rümmer, Micha Schrader:
CertiStr: a certified string solver. CPP 2022: 210-224](https://arxiv.org/abs/2112.06039) [Distinguished Paper Award]
2. [Shuanglong Kan: Certified Symbolic Transducer with Applications in String Solving](https://arxiv.org/abs/2504.07203)
