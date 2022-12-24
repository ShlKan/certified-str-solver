open Automata;; 
let a0=nfa_construct ([], [(0,(48,48),2);(0,(97,97),2);(1,(48,48),0);(1,(97,97),0)], [0], [2] );;
let a1=nfa_construct ([], [(1000,(48,48),1016);(1001,(49,49),1017);(1001,(97,97),1017);(1002,(48,48),1012);(1003,(49,49),1018);(1003,(97,97),1018);(1004,(49,49),1008);(1004,(97,97),1008);(1005,(48,48),1022);(1006,(49,49),1011);(1006,(97,97),1011);(1007,(48,48),1013);(1008,(49,49),1010);(1008,(97,97),1010);(1009,(48,48),1003);(1010,(49,49),1014);(1010,(97,97),1014);(1011,(49,49),1000);(1011,(97,97),1000);(1012,(49,49),1006);(1012,(97,97),1006);(1013,(48,48),1021);(1014,(48,48),1005);(1015,(48,48),1007);(1016,(49,49),1001);(1016,(97,97),1001);(1017,(49,49),1020);(1017,(97,97),1020);(1018,(48,48),1019);(1019,(48,48),1004);(1021,(49,49),1009);(1021,(97,97),1009);(1022,(49,49),1002);(1022,(97,97),1002)], [1000], [1020] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;