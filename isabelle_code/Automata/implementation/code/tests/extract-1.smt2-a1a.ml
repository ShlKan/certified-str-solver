open Automata;; 
let a0=nfa_construct ([], [(0,(123,65310),1);(0,(0,119),1);(0,(120,122),0);(1,(0,65310),1)], [0], [1] );;
let a1=nfa_construct ([], [(1000,(121,121),1002);(1001,(120,120),1000);(1002,(122,122),1003)], [1000], [1003] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
