open Automata;; 
let a0=nfa_construct ([], [(0,(40,40),0);(0,(41,41),1);(1,(41,41),1)], [0], [1] );;
let a1=nfa_construct ([], [(1000,(40,40),1001);(1001,(40,40),1001)], [1000], [1001] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
