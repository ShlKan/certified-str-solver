open Automata;; 
let a0=nfa_construct ([], [(0,(121,121),0);(1,(121,121),0)], [0], [0] );;
let a1=nfa_construct ([], [(1000,(120,120),1000);(1001,(120,120),1000)], [1000], [1000] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
