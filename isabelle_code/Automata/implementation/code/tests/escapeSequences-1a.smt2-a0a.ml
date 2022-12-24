open Automata;; 
let a0=nfa_construct ([], [(1,(72,72),3);(2,(108,108),0);(3,(101,101),4);(4,(108,108),2)], [0], [0] );;
let a1=nfa_construct ([], [(1000,(97,117),1000)], [1000], [1000] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
