open Automata;;
open Automata_lib;;
open Forward;;
let a0=nfa_construct ([], [(0,(48,48),1)], [0], [1] );;
let a1=nfa_construct ([], [(2,(1,48),3)], [2], [3] );;
let a3=nfa_construct ([], [(2,(1,48),3)], [2], [3] );;  

let S = gen_S_from_list [1;2];;
let rc = gen_rc_from_list [(3, (2,1))] ;;
let rm = gen_rm_from_list [(1,a0);(2,a1);(3,a2)];;


let re = forward_analysis S rc rm ;;
