open Automata;; 
let a0=nfa_construct ([], [(0,(0,91),0);(0,(93,65310),0);(0,(17,17),2);(1,(0,65310),1);(2,(0,59),0);(2,(93,65310),0);(2,(61,91),0);(2,(17,17),2);(2,(60,60),3);(3,(93,65310),0);(3,(0,82),0);(3,(84,91),0);(3,(17,17),2);(3,(83,83),6);(4,(0,81),0);(4,(93,65310),0);(4,(83,91),0);(4,(82,82),5);(4,(17,17),2);(5,(93,65310),0);(5,(74,91),0);(5,(0,72),0);(5,(17,17),2);(5,(73,73),7);(6,(93,65310),0);(6,(0,66),0);(6,(68,91),0);(6,(17,17),2);(6,(67,67),4);(7,(80,80),8);(7,(81,91),0);(7,(93,65310),0);(7,(17,17),2);(7,(0,79),0);(8,(93,65310),0);(8,(84,84),1);(8,(0,83),0);(8,(85,91),0);(8,(17,17),2)], [0], [1] );;
let a1=nfa_construct ([], [(1000,(60,60),1002);(1001,(62,62),1005);(1002,(47,47),1003);(1003,(116,116),1004);(1004,(100,100),1001)], [1000], [1005] );;
let product = nfa_concate a1 a0;;
print_auto (nfa_destruct product) ;;