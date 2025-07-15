open Automata_lib
open Rel

let f1 x = Z.add x (Z.of_int 1)

let f2 x = Z.sub x (Z.of_int 1)

(* [ nfa_uniq ] is used to make sure that the transitions in the nfa are
   unique, that is, for any two transitions from a state q1 to q2 with the
   same label, it will only keep one of them. *)
let nfa_uniq nfa =
  Automata_lib.rs_nfa_uniq (equal_Z, linorder_Z)
    (nFA_states_nat, linorder_nat)
    f1 f2 nfa

(* [ nfa_tran_complement ] adds new transitions from a state q1. if for the
   labels of all transitions from the state q1, all the labels added up
   (L_added_up) does not equal to the alphabelt (L), then it will add a new
   transition from q1 to the state q (q1, L - L_added_up, q). This will make
   the transtions from q1 are complete.

   The parameter [ q ] is a new state that is added to the nfa. *)
let nfa_tran_complement nfa q =
  Automata_lib.rs_nfa_tran_complement (equal_Z, linorder_Z)
    (equal_nat, nFA_states_nat, linorder_nat)
    f1 f2 nfa q

(* [ nfa_determinise ] translate a non-deterministic finite automaton (nfa)
   to a deterministic finite automaton (dfa). *)
let nfa_determinise nfa =
  Automata_lib.rs_nfa_determinise
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) nfa

(* [ nfa_complement ] complements an NFA. *)
let nfa_complement_aux nfa =
  Automata_lib.rs_nfa_complement (nFA_states_nat, linorder_nat) nfa

(* To compute the complement of an NFA, use the following composition: [
   nfa_complement (nfa_determinise (nfa_uniq (nfa_tran_complement a0
   (Automata_lib.Nat q_dead)))) ]

   q_dead is a new staet that is not in the original nfa. It is used to
   represent the dead state of the nfa. It is used to make sure that the
   transitions are complete. *)

let nfa_complement nfa q_dead =
  let enfa =
    match nfa with
    | s, (d, (i, f)) -> (s, ([(Z.of_int 0, Z.of_int 0x10FFFF)], (d, (i, f))))
  in
  nfa_complement_aux
    (nfa_determinise (nfa_uniq (nfa_tran_complement enfa q_dead)))
