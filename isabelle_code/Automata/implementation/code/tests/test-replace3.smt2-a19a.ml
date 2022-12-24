open Automata;; 
let a0=nfa_construct ([], [(0,(49,49),5);(0,(97,99),5);(1,(49,49),2);(1,(97,99),2);(3,(49,49),4);(3,(97,99),4);(4,(48,48),0);(5,(49,49),1);(5,(97,99),1)], [0], [2] );;
let a1=nfa_construct ([], [(1000,(97,97),1002);(1001,(99,99),1003);(1002,(98,98),1001)], [1000], [1003] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;