open Transducer
open Automata_lib

let less_eq_nat z1 z2 =
  Z.leq (Automata_lib.integer_of_nat z1) (Automata_lib.integer_of_nat z2)

let less_nat z1 z2 =
  Z.lt (Automata_lib.integer_of_nat z1) (Automata_lib.integer_of_nat z2)

let eq_nat n1 n2 =
  Automata_lib.integer_of_nat n1 = Automata_lib.integer_of_nat n2

let eq_Z n1 n2 = n1 = n2

let equal_nat = {Automata_lib.equal= eq_nat}

let equal_Z = {Automata_lib.equal= eq_Z}

let ord_Z = ({less_eq= Z.leq; less= Z.lt} : Z.t Automata_lib.ord)

let preorder_Z = ({ord_preorder= ord_Z} : Z.t Automata_lib.preorder)

let order_Z = ({preorder_order= preorder_Z} : Z.t Automata_lib.order)

let linorder_Z = ({order_linorder= order_Z} : Z.t Automata_lib.linorder)

let ord_nat =
  ({less_eq= less_eq_nat; less= less_nat} : Automata_lib.nat Automata_lib.ord)

let preorder_nat =
  ({ord_preorder= ord_nat} : Automata_lib.nat Automata_lib.preorder)

let order_nat =
  ({preorder_order= preorder_nat} : Automata_lib.nat Automata_lib.order)

let linorder_nat =
  ({order_linorder= order_nat} : Automata_lib.nat Automata_lib.linorder)

let nFA_states_nat =
  ( {states_enumerate= (fun i -> i)}
    : Automata_lib.nat Automata_lib.nFA_states )

let z_to_int z = Automata_lib.nat_of_integer (Z.of_int z)

let nFA_states_natnat =
  ( {states_enumerate= (fun i -> (i, i))}
    : (Automata_lib.nat * Automata_lib.nat) Automata_lib.nFA_states )

let linorder_natnat = Automata_lib.linorder_prod linorder_nat linorder_nat

let less_eq_str (s1 : string) (s2 : string) = String.compare s1 s2 <= 0

let less_str (s1 : string) (s2 : string) = String.compare s1 s2 < 0

let ord_str =
  ({less_eq= less_eq_str; less= less_str} : string Automata_lib.ord)

let preorder_str = ({ord_preorder= ord_str} : string Automata_lib.preorder)

let order_str = ({preorder_order= preorder_str} : string Automata_lib.order)

let eq_str n1 n2 = String.compare n1 n2 == 0

let equal_str = {Automata_lib.equal= eq_str}

let order_string =
  ({preorder_order= preorder_str} : string Automata_lib.order)

let linorder_str =
  ({order_linorder= order_str} : string Automata_lib.linorder)

let nfa_elim nfa =
  Automata_lib.rs_nfa_elim
    ( Automata_lib.equal_prod equal_nat equal_nat
    , nFA_states_natnat
    , linorder_natnat )
    (equal_Z, linorder_Z) nfa

let nfa_normal nfa =
  Automata_lib.rs_nfa_normal
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) nfa

let nfa_construct (q, d, i, f) =
  Automata_lib.rs_nfa_construct_interval
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z)
    ( List.map z_to_int q
    , ( List.map
          (fun (a, l, c) ->
            ( z_to_int a
            , ( List.map (fun (l, r) -> (Z.of_int l, Z.of_int r)) l
              , z_to_int c ) ) )
          d
      , (List.map z_to_int i, List.map z_to_int f) ) )

let nfa_product nfa1 nfa2 =
  Automata_lib.rs_nfa_bool_comb
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z)
    (fun b1 b2 -> b1 && b2)
    nfa1 nfa2

let nfa_destruct nfa =
  Automata_lib.rs_nfa_destruct
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) nfa

let nfa_destruct_str nfa =
  Automata_lib.rs_nfa_destruct
    (nFA_states_nat, linorder_nat)
    (equal_str, linorder_str) nfa

let nfa_concate nfa1 nfa2 =
  Automata_lib.rs_nfa_concate
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) nfa1 nfa2

let nfa_construct_reachable nfa =
  Automata_lib.rs_nfa_construct_reachable
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) nfa

let f1 q = (Automata_lib.Nat (Z.of_int 1), q)

let f2 q = (Automata_lib.Nat (Z.of_int 2), q)

let nfa_concate_rename nfa1 nfa2 =
  Automata_lib.rs_nfa_concate_rename
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) f1 f2 nfa1 nfa2

let rec print_list l =
  match l with
  | [] -> Format.printf "\n"
  | a :: rl ->
      Format.printf "%d" (Z.to_int (Automata_lib.integer_of_nat a)) ;
      Format.printf "; " ;
      print_list rl

let rec print_pair l =
  match l with
  | [] -> print_string "\n"
  | (a1, a2) :: rl ->
      print_string "(" ;
      print_int (Z.to_int (Automata_lib.integer_of_nat a1)) ;
      print_string ", " ;
      print_int (Z.to_int (Automata_lib.integer_of_nat a2)) ;
      print_string "); " ;
      print_pair rl

let rec print_rc l =
  match l with
  | [] -> print_string ""
  | (a, l) :: rl ->
      print_int (Z.to_int (Automata_lib.integer_of_nat a)) ;
      print_pair l ;
      print_string "; " ;
      print_rc rl

let rec print_tran l =
  match l with
  | [] -> Format.printf "\n"
  | (a, (l, c)) :: rl ->
      Format.printf "(" ;
      Format.printf "%d" (Z.to_int (Automata_lib.integer_of_nat a)) ;
      Format.printf ", " ;
      List.iter
        (fun (l, r) -> Format.printf "[%d, %d]" (Z.to_int l) (Z.to_int r))
        l ;
      Format.printf ", " ;
      Format.printf "%d" (Z.to_int (Automata_lib.integer_of_nat c)) ;
      Format.printf ")" ;
      print_tran rl

let rec print_tran_str l =
  match l with
  | [] -> Format.printf "\n"
  | (a, (l, c)) :: rl ->
      Format.printf "(" ;
      Format.printf "%d" (Z.to_int (Automata_lib.integer_of_nat a)) ;
      Format.printf ", " ;
      List.iter (fun (l, r) -> Format.printf "[%s, %s]" l r) l ;
      Format.printf ", " ;
      Format.printf "%d" (Z.to_int (Automata_lib.integer_of_nat c)) ;
      Format.printf ")" ;
      print_tran_str rl

let print_auto a =
  match a with
  | s, (d, (i, f)) ->
      Format.printf "States:" ;
      print_list s ;
      Format.printf "Initial states:" ;
      print_list i ;
      Format.printf "Transitions:" ;
      print_tran d ;
      Format.printf "Accepting states:" ;
      print_list f

let print_auto_str a =
  match a with
  | s, (d, (i, f)) ->
      Format.printf "States:" ;
      print_list s ;
      Format.printf "Initial states:" ;
      print_list i ;
      Format.printf "Transitions:" ;
      print_tran_str d ;
      Format.printf "Accepting states:" ;
      print_list f

let gen_S_from_list l = Automata_lib.rs_gen_S_from_list linorder_nat l

let gen_rm_from_list l =
  Automata_lib.rs_gen_rm_from_list linorder_nat
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) l

let gen_rc_from_list l = Automata_lib.rs_gen_rc_from_list linorder_nat l

let s_to_list l = Automata_lib.rs_S_to_list linorder_nat l

(* let forward_analysis a b s rc rm = Automata_lib.rs_forward_analysis
   (nFA_states_nat, linorder_nat) linorder_nat linorder_Z a b s rc rm *)

let rm_to_list rm =
  Automata_lib.rs_rm_to_list linorder_nat
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) rm

let indegree s rc = Automata_lib.rs_indegree (equal_nat, linorder_nat) s rc

let rec print_rm rm =
  match rm with
  | [] -> print_string "end"
  | (v, a) :: rml ->
      print_int (Z.to_int (Automata_lib.integer_of_nat v)) ;
      print_string "\n" ;
      print_auto (nfa_destruct a) ;
      print_string "\n---\n" ;
      print_rm rml

let rec check_unsat_rm s rc rm =
  match rm with
  | [] -> if indegree s rc = true then "sat" else "unknown"
  | (v, a) :: rml ->
      let _, (l, (_, ac)) = nfa_destruct a in
      if ac = [] then "unsat" else check_unsat_rm s rc rml

let print_trans_num a =
  let q, (l, (_, ac)) = nfa_destruct a in
  print_int (List.length q) ;
  print_string ", " ;
  print_int (List.length l) ;
  print_newline ()

let rec print_size rm =
  match rm with
  | [] -> ()
  | (v, a) :: rml -> print_trans_num a ; print_size rml

let sub_list lsmall llarge =
  List.for_all
    (fun (e1, e2) ->
      List.exists (fun e' -> e1 = e') llarge
      && List.exists (fun e' -> e2 = e') llarge )
    lsmall

let rec forward_analysis rest refined rc rm =
  if List.is_empty rest then []
  else
    let ready =
      List.fold_left
        (fun vars (l, deps) ->
          if List.exists (fun e' -> e' = l) rest && sub_list deps refined
          then l :: vars
          else vars )
        [] rc
    in
    let new_rest =
      List.filter (fun e -> not (List.exists (fun e' -> e = e') ready)) rest
    in
    let new_refined = refined @ ready in
    forward_analysis new_rest new_refined rc rm
