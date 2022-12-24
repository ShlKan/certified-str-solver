open Automata;; 
let a0=nfa_construct ([], [(0,(97,97),1);(1,(98,98),3);(3,(99,99),2)], [0], [2] );;
let a1=nfa_construct ([], [(1000,(100,100),1001);(1002,(97,97),1003);(1003,(98,98),1000)], [1000], [1001] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;
