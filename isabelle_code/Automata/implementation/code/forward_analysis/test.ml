
open Automata;;
open Automata_lib;;
open Forward;;
let a0=nfa_construct ([], [(0,(48,48),1)], [0], [1] );;
let a1=nfa_construct ([], [(2,(1,48),3)], [2], [3] );;
let a2=nfa_construct ([], [(2,(1,48),3); (3,(1,48),3)], [2], [3] );;  


let v1 = (z_to_int 1);;
let v2 = (z_to_int 2);;
let v3 = (z_to_int 3);;
let s = gen_S_from_list [v1;v2;v3];;

let r = gen_S_from_list [];;

let rc = gen_rc_from_list [(v3, [(v2,v1)])] ;;
let rm = gen_rm_from_list [(v1,a0);(v2,a1);(v3,a2)];;

let re = compute_ready_set s rc r;;
let re = s_to_list re;;
print_list re ;;

let (s,(rm,r)) = forward_analysis v1 v2 s rc rm ;; 

check_unsat_rm (rm_to_list rm);;



