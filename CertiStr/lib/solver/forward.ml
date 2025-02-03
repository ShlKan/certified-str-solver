open Transducer
open Automata_lib
open Rel
open Nfa
open SFT
module SS = Set.Make (String)
module ConcatC = Map.Make (String)
module ConcatR = Map.Make (String)
module ConcatCI = Map.Make (Int)
module ConcatRI = Map.Make (Int)
module InDegree = Map.Make (Int)

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

let nft_product nft =
  Automata_lib.rs_product_transducer
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) linorder_Z (equal_Z, linorder_Z) nft

let update_rm rm var add_auto =
  List.map
    (fun (v, old_auto) ->
      if v = var then (v, nfa_product old_auto add_auto) else (v, old_auto) )
    rm

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

let rec maxState states i =
  match states with
  | [] -> i
  | state :: states' ->
      if state > i then maxState states' state else maxState states' state

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

let selfTrans states =
  List.fold_left
    (fun trans_s a ->
      (a, ((Some [(Z.of_int 0, Z.of_int 255)], -2), a)) :: trans_s )
    [] states

let nft_construct nft =
  Automata_lib.rs_nft_construct_interval
    (nFA_states_nat, linorder_nat)
    (equal_Z, linorder_Z) linorder_Z linorder_Z nft

let nft_from_replace pattern replacement =
  let pAuto =
    Regex.compile
      (Regex.parse (String.sub pattern 1 (String.length pattern - 2)))
  in
  let rAuto =
    Regex.compile
      (Regex.parse
         (String.sub replacement 1 (String.length replacement - 2)) )
  in
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
  let nftAccepts = rename_states rAccepts max in
  let rTrans = rename_transtions rTrans max in
  let pTrans = trans_NFA2NFT_None pTrans in
  let pTrans = rename_transtions pTrans 0 in
  let pAccept =
    List.map (fun s -> Automata_lib.nat_of_integer (Z.of_int s)) pAccept
  in
  let rInit = rename_states rInit max in
  let nftTrans =
    rTrans @ pTrans
    @ connectTrans pAccept rInit
    @ selfTrans (nftInit @ nftAccepts)
  in
  let nftTrans =
    List.map (fun (p, ((l, i), q)) -> (p, ((l, Z.of_int i), q))) nftTrans
  in
  List.iter
    (fun (p, ((l, i), q)) ->
      Format.printf "(%d, %d)\n"
        (Z.to_int (Automata_lib.integer_of_nat p))
        (Z.to_int (Automata_lib.integer_of_nat q)) )
    nftTrans ;
  let outputFun = outputFunc outputZ in
  nft_construct ([], (nftTrans, (nftInit, (nftAccepts, outputFun))))

type str_op =
  | Concat of string * string
  | ConcatI of int * int
  | Replace of string * string * string
  | ReplaceI of int * string * string

exception Unreachable of string

let sub_list lsmall llarge =
  List.for_all
    (fun e ->
      match e with
      | ConcatI (e1, e2) ->
          List.exists (fun e' -> e1 = e') llarge
          && List.exists (fun e' -> e2 = e') llarge
      | Concat _ -> raise (Unreachable "sub_list")
      | Replace _ -> raise (Unreachable "sub_list")
      | ReplaceI (i, _, _) -> List.exists (fun e' -> i = e') llarge )
    lsmall

let fmap ff e =
  match e with
  | [] -> None
  | (a, b) :: l ->
      let l = ff (Some a) in
      let r = ff (Some b) in
      if l = None then None else l

let fe f l =
  match l with
  | [] -> false
  | e :: l' -> if f (Some (fst e)) = None then true else false

let rec update_once l rm auto =
  List.fold_left
    (fun acc_auto op ->
      match op with
      | ConcatI (i, j) ->
          nfa_product acc_auto
            (nfa_concate (ConcatRI.find i rm) (ConcatRI.find j rm))
      | Concat (_, _) -> raise (Unreachable "update_once")
      | Replace _ -> raise (Unreachable "update_once")
      | ReplaceI (i, a, c) ->
          let nft = nft_from_replace a c in
          let nfa =
            nfa_product acc_auto
              (nfa_normal
                 (nfa_elim (nft_product nft (ConcatRI.find i rm) fmap fe)) )
          in
          let _, (_, (_, f)) = nfa_destruct nfa in
          if f = [] then ConcatRI.find i rm else nfa )
    auto l

let rec update_auto var rc rm =
  update_once (ConcatCI.find var rc) rm (ConcatRI.find var rm)

let indegree_count rc vars =
  let indegree_map =
    List.fold_left (fun acc k -> InDegree.add k 0 acc) InDegree.empty vars
  in
  ConcatCI.fold
    (fun _ l acc ->
      List.fold_left
        (fun acc cons ->
          match cons with
          | ConcatI (i, j) ->
              let acc1 = InDegree.add i (InDegree.find i acc + 1) acc in
              InDegree.add j (InDegree.find j acc1 + 1) acc1
          | ReplaceI (i, _, _) ->
              InDegree.add i (InDegree.find i acc + 1) acc
          | _ -> acc )
        acc l )
    rc indegree_map

let check_sat vars rc rm =
  let ind = indegree_count rc vars in
  let res =
    ConcatRI.for_all
      (fun i a ->
        let dAuto = nfa_destruct a in
        if snd (snd (snd dAuto)) == [] then false else true )
      rm
  in
  let indegree_cons =
    InDegree.for_all (fun _ c -> if c <= 1 then true else false) ind
  in
  if res then
    if indegree_cons = false then Format.printf "inconclusive"
    else Format.printf "SAT"
  else Format.printf "UNSAT"

let test_input rest refined rc rm =
  Format.printf "Rest: " ;
  List.iter (fun e -> Format.printf "%d, " e) rest ;
  Format.printf "\nRefined: " ;
  List.iter (fun e -> Format.printf "%d, " e) refined ;
  Format.printf "\nConstraints: " ;
  ConcatCI.iter
    (fun id s ->
      Format.printf "%d = " id ;
      match s with
      | [] -> Format.printf "Empty Error"
      | e :: s' ->
          ( match e with
          | ConcatI (i, j) -> Format.printf "(%d, %d)" i j
          | ReplaceI (i, p, s) -> Format.printf "(replace %d %s %s)" i p s
          | _ -> Format.printf "Unreachable" ) ;
          Format.printf "\n" )
    rc ;
  Format.printf "\nInitDomain:\n" ;
  ConcatRI.iter
    (fun id s ->
      Format.printf "%d = " id ;
      print_auto (nfa_destruct s) ;
      Format.printf "\n--------------------\n" )
    rm

let rec forward_analysis rest refined rc rm =
  test_input rest refined rc rm ;
  if List.is_empty rest then rm
  else
    let ready =
      ConcatCI.fold
        (fun l deps vars ->
          if List.exists (fun e' -> e' = l) rest && sub_list deps refined
          then l :: vars
          else vars )
        rc []
    in
    let new_rest =
      List.filter (fun e -> not (List.exists (fun e' -> e = e') ready)) rest
    in
    let new_refined = refined @ ready in
    let new_rm =
      List.fold_left
        (fun acc_rm v ->
          ConcatRI.update v
            (Option.map (fun _ -> update_auto v rc rm))
            acc_rm )
        rm ready
    in
    forward_analysis new_rest new_refined rc new_rm
