open Automata;; 
let a0=nfa_construct ([], [(1,(48,48),2);(1,(97,97),2);(2,(48,48),0);(2,(97,97),0);(3,(48,48),1);(3,(97,97),1)], [0], [0] );;
let a1=nfa_construct ([], [(1000,(48,48),1006);(1001,(49,49),1014);(1001,(97,97),1014);(1002,(49,49),1000);(1002,(97,97),1000);(1003,(49,49),1016);(1003,(97,97),1016);(1004,(48,48),1007);(1005,(48,48),1001);(1006,(48,48),1018);(1007,(49,49),1017);(1007,(97,97),1017);(1008,(48,48),1012);(1009,(49,49),1008);(1009,(97,97),1008);(1010,(48,48),1004);(1011,(49,49),1009);(1011,(97,97),1009);(1012,(49,49),1003);(1012,(97,97),1003);(1013,(49,49),1020);(1013,(97,97),1020);(1014,(49,49),1002);(1014,(97,97),1002);(1015,(49,49),1011);(1015,(97,97),1011);(1016,(48,48),1021);(1017,(48,48),1013);(1018,(49,49),1019);(1018,(97,97),1019);(1019,(48,48),1015);(1020,(48,48),1005)], [1000], [1021] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;