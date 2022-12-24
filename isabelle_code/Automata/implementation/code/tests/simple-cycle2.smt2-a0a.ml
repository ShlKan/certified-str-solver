open Automata;; 
let a0=nfa_construct ([], [], [0], [0] );;
let a1=nfa_construct ([], [(1000,(0,65310),1001);(1001,(0,65310),1001)], [1000], [1001] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
