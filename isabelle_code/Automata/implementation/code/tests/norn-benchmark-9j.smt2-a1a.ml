open Automata;; 
let a0=nfa_construct ([], [(0,(99,99),2);(1,(97,97),3);(3,(98,98),0)], [0], [2] );;
let a1=nfa_construct ([], [(1001,(98,98),1000);(1002,(97,97),1001)], [1000], [1000] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
