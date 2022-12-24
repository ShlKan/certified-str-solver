open Automata;; 
let a0=nfa_construct ([], [(0,(0,65310),0);(1,(123,65310),0);(1,(0,119),0);(1,(120,122),1)], [0], [0] );;
let a1=nfa_construct ([], [(1000,(120,122),1000);(1001,(120,122),1000)], [1000], [1000] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
