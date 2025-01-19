open Transducer
open Nfa
open Automata_lib
open Automata_lib
module SS = Set.Make (String)
module ConcatC = Map.Make (String)
module ConcatR = Map.Make (String)

(* Currently, only in_re, concat allowed. *)
let check_constraints (cons : Parser.strConstrain list) =
  List.for_all
    (fun (c : Parser.strConstrain) ->
      match c with
      | Parser.IN_RE _ -> true
      | Parser.StrEq (_, rhs) -> (
        match rhs with Parser.Concat _ -> true | _ -> false )
      | _ -> false )
    cons

let convertRE2NFA (cons : Parser.strConstrain) =
  match cons with
  | Parser.IN_RE (lhs, rhs) ->
      let nfa_from_reg = Regex.compile (Regex.parse (Parser.reg2Str rhs)) in
      Parser.IN_NFA (lhs, nfa_from_reg)
  | _ -> cons

let normalStrConstraints (cons : Parser.strConstrain list) =
  List.map convertRE2NFA cons

exception UnsupportError of string

let rec genStrConstraints (constraints : Parser.strConstrain list) =
  match constraints with
  | [] -> (SS.empty, ConcatC.empty, ConcatR.empty)
  | cons :: constraints' -> (
      let reS, reC, reR = genStrConstraints constraints' in
      match cons with
      | Parser.StrEq (Name lhs, Concat (Name c1, Name c2)) ->
          ( SS.add lhs ((SS.add c1) (SS.add c2 reS))
          , ConcatC.update lhs
              (fun x ->
                match x with
                | None -> Some [(c1, c2)]
                | Some l -> Some ((c1, c2) :: l) )
              reC
          , reR )
      | Parser.IN_NFA (Name lhs, nfa) ->
          ( SS.add lhs reS
          , reC
          , ConcatR.update lhs
              (fun x ->
                match x with None -> Some [nfa] | Some l -> Some (nfa :: l) )
              reR )
      | _ -> raise (UnsupportError "Currently only StrEq and In_Re supported")
      )

let print_vars s =
  Format.printf "The following are variables:" ;
  SS.iter (fun v -> Format.printf "%s, " v) s ;
  Format.printf "\n"

let print_conC c =
  Format.printf "The following are concatenations:\n" ;
  ConcatC.iter
    (fun s l ->
      Format.printf "%s = " s ;
      List.iter (fun (c1, c2) -> Format.printf "(%s, %s); " c1 c2) l )
    c ;
  Format.printf "\n"

let print_conR r =
  Format.printf "The following are Regex constraints:\n" ;
  ConcatR.iter
    (fun s l ->
      Format.printf "%s = \n" s ;
      List.iter (fun a -> SNFA.printNfa a) l )
    r ;
  Format.printf "\n"

let z_to_int z = nat_of_integer (Z.of_int z)

let rec gen_intl b e = if b = e then [e] else b :: gen_intl (b + 1) e

let rec get_index_aux e l i =
  match l with
  | [] -> -1
  | a :: rl -> if a = e then i else get_index_aux e rl (i + 1)

let get_index e l = get_index_aux e l 0

let rec genPair ls l =
  match ls with
  | [] -> []
  | (s1, s2) :: rs ->
      (z_to_int (get_index s1 l), z_to_int (get_index s2 l)) :: genPair rs l

let rec out_mapc s l =
  match s with
  | [] -> []
  | (s1, s2) :: rs ->
      (z_to_int (get_index s1 l), genPair s2 l) :: out_mapc rs l

let rec gen_mapc s l = out_mapc (ConcatC.bindings s) l

exception Automata_less

let nFA_states_nat =
  ( {states_enumerate= (fun i -> i)}
    : Automata_lib.nat Automata_lib.nFA_states )

let less_eq_nat z1 z2 =
  Z.leq (Automata_lib.integer_of_nat z1) (Automata_lib.integer_of_nat z2)

let less_nat z1 z2 =
  Z.lt (Automata_lib.integer_of_nat z1) (Automata_lib.integer_of_nat z2)

let ord_nat =
  ({less_eq= less_eq_nat; less= less_nat} : Automata_lib.nat Automata_lib.ord)

let preorder_nat =
  ({ord_preorder= ord_nat} : Automata_lib.nat Automata_lib.preorder)

let order_nat =
  ({preorder_order= preorder_nat} : Automata_lib.nat Automata_lib.order)

let linorder_nat =
  ({order_linorder= order_nat} : Automata_lib.nat Automata_lib.linorder)

let ord_Z = ({less_eq= Z.leq; less= Z.lt} : Z.t Automata_lib.ord)

let preorder_Z = ({ord_preorder= ord_Z} : Z.t Automata_lib.preorder)

let order_Z = ({preorder_order= preorder_Z} : Z.t Automata_lib.order)

let linorder_Z = ({order_linorder= order_Z} : Z.t Automata_lib.linorder)

let nfa_construct (q, d, i, f) =
  Automata_lib.rs_nfa_construct_interval
    (nFA_states_nat, linorder_nat)
    linorder_Z
    ( List.map z_to_int q
    , ( List.map
          (fun (a, (b1, b2), c) ->
            (z_to_int a, ((Z.of_int b1, Z.of_int b2), z_to_int c)) )
          d
      , (List.map z_to_int i, List.map z_to_int f) ) )

let nfa_construct_reachable nfa =
  rs_nfa_construct_reachable (nFA_states_nat, linorder_nat) linorder_Z nfa

let get_interval s =
  let l = String.split_on_char '-' s in
  if List.length l == 2 then
    ( Char.code (String.get (List.nth l 0) 0)
    , Char.code (String.get (List.nth l 1) 0) )
  else
    ( Char.code (String.get (List.nth l 0) 0)
    , Char.code (String.get (List.nth l 0) 0) )

let transitions_single next left pre_trans =
  CharMap.fold
    (fun l rights trans ->
      StateSet.fold
        (fun right ss ->
          (Int32.to_int left, get_interval l, Int32.to_int right) :: ss )
        rights trans )
    (next left) pre_trans

let transitions all_states next =
  StateSet.fold (transitions_single next) all_states []

let gen_nfa_construct_input (n : Nfa.nfa) =
  let all_states = SNFA.gather_states n in
  match n with
  | {start; finals; next} ->
      ( []
      , transitions all_states next
      , List.map Int32.to_int (StateSet.to_list start)
      , List.map Int32.to_int (StateSet.to_list finals) )

let gen_aut at =
  nfa_construct_reachable (nfa_construct (gen_nfa_construct_input at))

let nfa_product nfa1 nfa2 =
  Automata_lib.rs_nfa_bool_comb
    (nFA_states_nat, linorder_nat)
    linorder_Z
    (fun b1 b2 -> b1 && b2)
    nfa1 nfa2

let nfa_destruct nfa =
  Automata_lib.rs_nfa_destruct (nFA_states_nat, linorder_nat) linorder_Z nfa

let rec gen_concater l =
  match l with
  | [] -> raise Automata_less
  | [a] -> gen_aut a
  | a :: rl -> nfa_product (gen_aut a) (gen_concater rl)

let rec gen_maprs s l =
  match s with
  | [] -> []
  | (s1, s2) :: rs ->
      (z_to_int (get_index s1 l), gen_concater s2) :: gen_maprs rs l

let gen_mapr s l = gen_maprs (ConcatR.bindings s) l

let rec full_rm sl rm =
  match sl with
  | [] -> rm
  | a :: rl ->
      if ConcatR.mem a rm then full_rm rl rm
      else full_rm rl (ConcatR.add a [SNFA.universalAuto] rm)

let eq_nat n1 n2 =
  Automata_lib.integer_of_nat n1 = Automata_lib.integer_of_nat n2

let equal_nat = {Automata_lib.equal= eq_nat}

let indegree s rc = Automata_lib.rs_indegree (equal_nat, linorder_nat) s rc

let rec check_unsat_rm s rc rm =
  match rm with
  | [] -> if indegree s rc = true then "sat" else "unknown"
  | (v, a) :: rml ->
      let _, (l, (_, ac)) = nfa_destruct a in
      if ac = [] then "unsat" else check_unsat_rm s rc rml

let rm_to_list rm =
  Automata_lib.rs_rm_to_list linorder_nat
    (nFA_states_nat, linorder_nat)
    linorder_Z rm

let solve (constraints : Parser.strConstrain list) =
  let ss, cc, cr = genStrConstraints constraints in
  let sl = SS.elements ss in
  let s =
    Forward.gen_S_from_list
      (List.map z_to_int (gen_intl 0 (List.length sl - 1)))
  in
  let rc = Forward.gen_rc_from_list (gen_mapc cc sl) in
  let rr = full_rm sl cr in
  let rm = Forward.gen_rm_from_list (gen_mapr rr sl) in
  let s, (rm, r) =
    Forward.forward_analysis (z_to_int 1) (z_to_int 2) s rc rm
  in
  print_string (check_unsat_rm r rc (rm_to_list rm))
