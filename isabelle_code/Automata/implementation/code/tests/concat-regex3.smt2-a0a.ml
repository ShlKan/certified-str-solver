open Automata;; 
let a0=nfa_construct ([], [], [0], [0] );;
let a1=nfa_construct ([], [(1000,(120,120),1001);(1001,(120,120),1001)], [1000], [1001] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
