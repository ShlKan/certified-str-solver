open Automata;; 
let a0=nfa_construct ([], [(0,(98,98),2);(1,(97,97),0);(2,(99,99),3)], [0], [3] );;
let a1=nfa_construct ([], [(1000,(100,100),1002);(1001,(99,99),1000);(1003,(98,98),1001);(1004,(97,97),1003)], [1000], [1002] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
