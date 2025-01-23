open Transducer
open Nfa
open Automata_lib
open Automata_lib
open Rel
open Transducer.SFT
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

let nfa_construct_reachable nfa =
  rs_nfa_construct_reachable
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) nfa

let nft_construct nft =
  rs_nft_construct_interval
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) linorder_Z linorder_Z nft

let f (x : Z.t option) = Some [(Z.of_int 1, Z.of_int 100)]

let rec maxState states i =
  match states with
  | [] -> i
  | state :: states' ->
      if state > i then maxState states' state else maxState states' state

let rename_states states max =
  List.map
    (fun state -> Automata_lib.nat_of_integer (Z.of_int (state + max)))
    states

let rename_transtions trans max =
  List.map
    (fun (q, (l, q')) ->
      ( Automata_lib.nat_of_integer (Z.of_int (q + max))
      , (l, Automata_lib.nat_of_integer (Z.of_int (q' + max))) ) )
    trans

let nft_example =
  nft_construct
    ( List.map (fun x -> Automata_lib.nat_of_integer (Z.of_int x)) [1; 2]
    , ( [ ( Automata_lib.nat_of_integer (Z.of_int 1)
          , ( (Some [(Z.of_int 1, Z.of_int 10000)], Z.of_int 1)
            , Automata_lib.nat_of_integer (Z.of_int 2) ) ) ]
      , ( [Automata_lib.nat_of_integer (Z.of_int 1)]
        , ([Automata_lib.nat_of_integer (Z.of_int 2)], fun x -> f) ) ) )

let gen_nfa_construct_input (n : Nfa.nfa) =
  let all_states = SNFA.gather_states n in
  match n with
  | {start; finals; next} ->
      ( []
      , transitions all_states next
      , List.map Int32.to_int (StateSet.to_list start)
      , List.map Int32.to_int (StateSet.to_list finals) )

let connectTrans ends starts =
  List.fold_left
    (fun trans a ->
      List.fold_left
        (fun trans_s b -> (a, ((None, -1), b)) :: trans_s)
        trans starts )
    [] ends

let nft_from_replace pattern replacement =
  let pAuto = Regex.compile (Regex.parse pattern) in
  SNFA.printNfa pAuto ;
  let rAuto = Regex.compile (Regex.parse replacement) in
  SNFA.printNfa rAuto ;
  let pStates = SNFA.gather_states pAuto in
  let max =
    1 + maxState (List.map Int32.to_int (StateSet.to_list pStates)) 0
  in
  let _, pTrans, pInit, pAccept = gen_nfa_construct_input pAuto in
  let _, rTrans, rInit, rAccepts = gen_nfa_construct_input rAuto in
  let rTrans, output = trans_NFA2NFT rTrans in
  let outputZ =
    List.map
      (fun l -> List.map (fun (l1, l2) -> (Z.of_int l1, Z.of_int l2)) l)
      output
  in
  let nftInit =
    List.map (fun s -> Automata_lib.nat_of_integer (Z.of_int s)) pInit
  in
  let rAccepts = rename_states rAccepts max in
  let nftAccepts = rAccepts in
  let rTrans = rename_transtions rTrans max in
  let pTrans = trans_NFA2NFT_None pTrans in
  let pTrans = rename_transtions pTrans max in
  let pAccept =
    List.map (fun s -> Automata_lib.nat_of_integer (Z.of_int s)) pAccept
  in
  let rInit = rename_states rInit max in
  let nftTrans = rTrans @ pTrans @ connectTrans pAccept rInit in
  let nftTrans =
    List.map (fun (p, ((l, i), q)) -> (p, ((l, Z.of_int i), q))) nftTrans
  in
  let outputFun = outputFunc outputZ in
  nft_construct ([], (nftTrans, (nftInit, (nftAccepts, outputFun))))

(* let () = nft_from_replace "[a-b]|c" "abcd" *)

let nft_product nft =
  rs_product_transducer
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) linorder_Z (equal_Z, linorder_Z) nft

let gen_aut at =
  nfa_construct_reachable (nfa_construct (gen_nfa_construct_input at))

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
    (equal_Z, linorder_Z) rm

let fmap ff e =
  match e with
  | [] -> None
  | (a, b) :: l ->
      Some [(Z.of_int (Z.to_int a + 1), Z.of_int (Z.to_int b + 1))]

let fe f e = false

let output_nfa = nft_product nft_example (gen_aut SNFA.universalAuto) fmap fe

let solve (constraints : Parser.strConstrain list) =
  let ss, cc, cr = genStrConstraints constraints in
  let sl = SS.elements ss in
  let new_rc = gen_mapc cc sl in
  let rest = List.map (fun (l, _) -> l) new_rc in
  let new_sl =
    List.filter
      (fun e -> not (List.exists (fun e' -> e = e') rest))
      (List.map z_to_int (gen_intl 0 (List.length sl - 1)))
  in
  let _tmp = Forward.forward_analysis rest new_sl new_rc cr in
  let s =
    Forward.gen_S_from_list
      (List.map z_to_int (gen_intl 0 (List.length sl - 1)))
  in
  let rc = Forward.gen_rc_from_list (gen_mapc cc sl) in
  let rr = full_rm sl cr in
  let rm = Forward.gen_rm_from_list (gen_mapr rr sl) in
  List.iter
    (fun (v, a) -> ()) (* Forward.print_auto (nfa_destruct a)) *)
    (rm_to_list rm) ;
  Forward.print_auto
    (nfa_destruct
       (nfa_construct (gen_nfa_construct_input SNFA.universalAuto)) ) ;
  Format.printf "--------\n" ;
  Forward.print_auto
    (Forward.nfa_destruct
       (Forward.nfa_normal (Forward.nfa_elim output_nfa)) )
(* let s, (rm, r) = Forward.forward_analysis (z_to_int 1) (z_to_int 2) s rc
   rm in print_string (check_unsat_rm r rc (rm_to_list rm)) *)
