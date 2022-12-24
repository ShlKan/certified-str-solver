
open Automata_lib 

let less_eq_nat z1 z2 = Z.leq (Automata_lib.integer_of_nat z1) (Automata_lib.integer_of_nat z2) ;;

let less_nat z1 z2 = Z.lt (Automata_lib.integer_of_nat z1) (Automata_lib.integer_of_nat z2) ;;


let ord_Z =
  ({less_eq = Z.leq; less = Z.lt} :                                                                    
  Z.t Automata_lib.ord);;  



let preorder_Z = ({ord_preorder = ord_Z} : Z.t Automata_lib.preorder);;
let order_Z = ({preorder_order = preorder_Z} : Z.t Automata_lib.order);;

let linorder_Z = ({order_linorder = order_Z} : Z.t Automata_lib.linorder);;

let nat_eq n1 n2 = match (n1, n2) with (Automata_lib.Nat a, Automata_lib.Nat b) -> Z.equal a b ;; 

let equal_Z = ({equal = Z.equal}: Z.t Automata_lib.equal) ;;
let equal_nat = ({equal = nat_eq}: Automata_lib.nat Automata_lib.equal) ;;

let ord_nat =
  ({less_eq = less_eq_nat; less = less_nat} :                                                                    
  Automata_lib.nat Automata_lib.ord);;  

let preorder_nat = ({ord_preorder = ord_nat} :  Automata_lib.nat Automata_lib.preorder);;
let order_nat = ({preorder_order = preorder_nat} : Automata_lib.nat Automata_lib.order);;

let linorder_nat = ({order_linorder = order_nat} : Automata_lib.nat Automata_lib.linorder);;

let nFA_states_nat = ({states_enumerate = (fun i -> i)}:
    (Automata_lib.nat Automata_lib.nFA_states)) ;;

let z_to_int z = Automata_lib.nat_of_integer (Z.of_int  z);;

let rec zlist l = match  l with [] -> []
                | (b1, b2) :: rl -> (Z.of_int b1, Z.of_int b2) :: zlist rl ;;

let nfa_construct (q, s, d, i, f) =
     Automata_lib.rs_nfa_construct_interval (nFA_states_nat, linorder_nat) (equal_Z, linorder_Z) 
         (List.map z_to_int q, 
           (zlist s, 
           ((List.map (fun (a, lb, c) -> (z_to_int a, (zlist lb, z_to_int c))) d),
           (List.map z_to_int i, 
            List.map z_to_int f))));;


let nfa_union nfa1 nfa2 = Automata_lib.rs_nfa_union (nFA_states_nat, linorder_nat) (equal_Z, linorder_Z)
                          nfa1 nfa2;;


let nfa_states_size nfa = Automata_lib.rs_nfa_qsize (nFA_states_nat, linorder_nat) linorder_Z nfa;;


let nfa_product nfa1 nfa2 = Automata_lib.rs_nfa_bool_comb (nFA_states_nat, linorder_nat) (equal_Z, linorder_Z)
                            (fun b1 b2 -> (b1 && b2)) 
                            nfa1 nfa2;;
let nstate n a = match (n, a) with (Automata_lib.Nat k1, Automata_lib.Nat k2) -> Automata_lib.Nat (Z.add k1 k2) ;;

let nfa_rename nfa n = Automata_lib.rs_nfa_rename linorder_nat (equal_Z, linorder_Z) linorder_nat nfa (nstate n);;

let nfa_determinise nfa = Automata_lib.rs_nfa_determinise (nFA_states_nat, linorder_nat) (equal_Z, linorder_Z)
                           nfa;;

let nfa_complement nfa = Automata_lib.rs_nfa_complement (nFA_states_nat, linorder_nat) 
                           nfa;;

let f1 x = Z.add x (Z.of_int 1) ;;
let f2 x = Z.sub x (Z.of_int 1) ;;

let nfa_uniq nfa = Automata_lib.rs_nfa_uniq (equal_Z, linorder_Z) (nFA_states_nat, linorder_nat) f1 f2 nfa;;

let nfa_tran_complement nfa q = Automata_lib.rs_nfa_tran_complement (equal_Z, linorder_Z) (equal_nat, nFA_states_nat, linorder_nat) f1 f2 nfa q;;

let nfa_destruct nfa = Automata_lib.rs_nfa_destruct 
(nFA_states_nat, linorder_nat) 
(equal_Z, linorder_Z) nfa ;;

let nfa_concate nfa1 nfa2 = Automata_lib.rs_nfa_concate (nFA_states_nat, linorder_nat) 
 (equal_Z, linorder_Z) nfa1 nfa2;;

let f1 q = (Automata_lib.Nat (Z.of_int 1), q);;                           
let f2 q = (Automata_lib.Nat (Z.of_int 2), q);;

let nfa_concate_rename nfa1 nfa2 = Automata_lib.rs_nfa_concate_rename (nFA_states_nat, linorder_nat) 
(equal_Z, linorder_Z) f1 f2 nfa1 nfa2;;

 let rec print_list l = match l with [] -> print_string "\n"
                               | a :: rl -> print_int (Z.to_int (Automata_lib.integer_of_nat a)) ; 
                                            print_string "; " ; print_list rl ;;

let rec print_labels l = match l with [] -> print_string ""
                                    | (x,y) :: rl -> (print_string "("; print_int (Z.to_int (x)); 
                                        print_string ", "; print_int (Z.to_int (y));print_string "); "; print_labels rl) ;;

let rec print_tran l = match l with [] -> print_string "\n" 
                               | (a,(lb,c)) :: rl -> print_string "("; 
                                              print_int (Z.to_int (Automata_lib.integer_of_nat a));
                                              print_string ", [";
                                              print_labels lb;
                                              print_string "], " ;
                                              print_int (Z.to_int (Automata_lib.integer_of_nat c)); 
                                              print_string ")"; print_tran rl;;

 let print_auto a = 
     match a with (s, (e, (d , (i, f)))) -> 
     print_string "States:"; print_list s ;
     print_string "Sigma:"; print_labels e ; print_string "\n"; 
     print_string "Initial states:"; print_list i;
     print_string "Transitions:" ; print_tran d;
     print_string "Accepting states:"; print_list f ;;


 


















