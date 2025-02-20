open Transducer
open Nfa
open Automata_lib
open Automata_lib
open Rel
open Transducer.SFT
open Forward

(* Currently, only in_re, concat allowed. *)
let check_constraints (cons : Parser.strConstrain list) =
  List.for_all
    (fun (c : Parser.strConstrain) ->
      match c with
      | Parser.IN_RE _ -> true
      | Parser.StrEq (_, rhs) -> (
        match rhs with
        | Parser.Concat _ -> true
        | Parser.REPLACE (_, _, _) -> true
        | Parser.Str _ -> true
        | Parser.Name _ -> true
        | _ -> Parser.print_str_cons c ; false )
      | _ -> false )
    cons

let count = ref 0

exception Unreachable of string

let add_additional s =
  match s with
  | Parser.Str s ->
      let nfa_from_reg =
        Regex.compile (Parser.str2Reg (String.sub s 1 (String.length s - 2)))
      in
      let new_var = Parser.Name ("tmp_" ^ string_of_int !count) in
      count := !count + 1 ;
      (new_var, Parser.IN_NFA (new_var, nfa_from_reg))
  | _ -> raise (Unreachable "Unreachable")

let convertRE2NFA (cons : Parser.strConstrain) =
  match cons with
  | IN_RE (lhs, rhs) ->
      let nfa_from_reg = Regex.compile (Parser.reg2reg rhs) in
      [Parser.IN_NFA (lhs, nfa_from_reg)]
  | StrEq (lhs, REPLACE (s, p, r)) -> (
    match s with
    | Parser.Str _ ->
        let v1, cons1 = add_additional s in
        [cons1; StrEq (lhs, Parser.REPLACE (v1, p, r))]
    | _ -> [StrEq (lhs, Parser.REPLACE (s, p, r))] )
  | _ -> [cons]

let normalStrConstraints (cons : Parser.strConstrain list) =
  let res = List.map convertRE2NFA cons in
  List.flatten res

exception UnsupportError of string

let rec genStrConstraints (constraints : Parser.strConstrain list) =
  match constraints with
  | [] -> (Forward.SS.empty, Forward.ConcatC.empty, Forward.ConcatR.empty)
  | cons :: constraints' -> (
      let reS, reC, reR = genStrConstraints constraints' in
      match cons with
      | Parser.StrEq (Name lhs, Concat (Name c1, Name c2)) ->
          ( Forward.SS.add lhs ((Forward.SS.add c1) (Forward.SS.add c2 reS))
          , Forward.ConcatC.update lhs
              (fun x ->
                match x with
                | None -> Some [Concat (c1, c2)]
                | Some l -> Some (Concat (c1, c2) :: l) )
              reC
          , reR )
      | Parser.StrEq (Name lhs, REPLACE (Name s, Str p, r)) ->
          ( Forward.SS.add lhs (Forward.SS.add s reS)
          , Forward.ConcatC.update lhs
              (fun x ->
                match x with
                | None -> Some [Replace (s, Str p, r)]
                | Some l -> Some (Replace (s, Str p, r) :: l) )
              reC
          , reR )
      | Parser.StrEq (Name lhs, REPLACE (Name s, RegEx p, r)) ->
          ( Forward.SS.add lhs (Forward.SS.add s reS)
          , Forward.ConcatC.update lhs
              (fun x ->
                match x with
                | None -> Some [Replace (s, RegEx p, r)]
                | Some l -> Some (Replace (s, RegEx p, r) :: l) )
              reC
          , reR )
      | Parser.StrEq (Name lhs, REPLACE (Name s, reg, r)) ->
          ( Forward.SS.add lhs (Forward.SS.add s reS)
          , Forward.ConcatC.update lhs
              (fun x ->
                match x with
                | None -> Some [Replace (s, reg, r)]
                | Some l -> Some (Replace (s, reg, r) :: l) )
              reC
          , reR )
      | Parser.IN_NFA (Name lhs, nfa) ->
          ( Forward.SS.add lhs reS
          , reC
          , Forward.ConcatR.update lhs
              (fun x ->
                match x with None -> Some [nfa] | Some l -> Some (nfa :: l) )
              reR )
      | Parser.StrEq (Name lhs, Str s) ->
          let s' = String.sub s 1 (String.length s - 2) in
          let reg =
            if String.compare s' "" = 0 then Regex.eps else Parser.str2Reg s'
          in
          ( Forward.SS.add lhs reS
          , reC
          , Forward.ConcatR.update lhs
              (fun x ->
                match x with
                | None -> Some [Regex.compile reg]
                | Some l -> Some (Regex.compile reg :: l) )
              reR )
      | Parser.StrEq (Name lhs, Name rhs) ->
          ( Forward.SS.add lhs (Forward.SS.add rhs reS)
          , Forward.ConcatC.update lhs
              (fun x ->
                match x with
                | None -> Some [Tran rhs]
                | Some l -> Some (Tran rhs :: l) )
              reC
          , reR )
      | _ -> raise (UnsupportError "Currently only StrEq and In_Re supported")
      )

let print_vars s =
  Format.printf "The following are variables:" ;
  Forward.SS.iter (fun v -> Format.printf "%s, " v) s ;
  Format.printf "\n"

let print_conC c =
  Format.printf "The following are concatenations:\n" ;
  Forward.ConcatC.iter
    (fun s l ->
      Format.printf "%s = " s ;
      List.iter (fun (c1, c2) -> Format.printf "(%s, %s); " c1 c2) l )
    c ;
  Format.printf "\n"

let print_conR r =
  Format.printf "The following are Regex constraints:\n" ;
  Forward.ConcatR.iter
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
  | Concat (s1, s2) :: rs ->
      ConcatI (get_index s1 l, get_index s2 l) :: genPair rs l
  | Replace (a, p, r) :: rs -> ReplaceI (get_index a l, p, r) :: genPair rs l
  | ConcatI (a, b) :: rs -> ConcatI (a, b) :: genPair rs l
  | ReplaceI (a, p, r) :: rs -> ReplaceI (a, p, r) :: genPair rs l
  | Tran s :: rs -> TranI (get_index s l) :: genPair rs l
  | TranI i :: rs -> TranI i :: genPair rs l

let rec out_mapc s l =
  match s with
  | [] -> ConcatCI.empty
  | (s1, s2) :: rs ->
      ConcatCI.add (get_index s1 l) (genPair s2 l) (out_mapc rs l)

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

let f (x : Z.t option) = Some [(Z.of_int 1, Z.of_int 100)]

let nft_example =
  nft_construct
    ( List.map (fun x -> Automata_lib.nat_of_integer (Z.of_int x)) [1; 2]
    , ( [ ( Automata_lib.nat_of_integer (Z.of_int 1)
          , ( (Some [(Z.of_int 1, Z.of_int 10000)], Z.of_int 1)
            , Automata_lib.nat_of_integer (Z.of_int 2) ) ) ]
      , ( [Automata_lib.nat_of_integer (Z.of_int 1)]
        , ([Automata_lib.nat_of_integer (Z.of_int 2)], fun x -> f) ) ) )

(* let () = nft_from_replace "[a-b]|c" "abcd" *)

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
  | [] -> ConcatRI.empty
  | (s1, s2) :: rs ->
      ConcatRI.add (get_index s1 l) (gen_concater s2) (gen_maprs rs l)

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

let output_nfa = nft_product nft_example (gen_aut SNFA.universalAuto) fmap fe

let solve (constraints : Parser.strConstrain list) =
  let ss, cc, cr = genStrConstraints constraints in
  let sl = SS.elements ss in
  let new_rc = gen_mapc cc sl in
  let rest = List.map (fun (l, _) -> l) (ConcatRI.to_list new_rc) in
  let new_sl =
    List.filter
      (fun e -> not (List.exists (fun e' -> e = e') rest))
      (gen_intl 0 (List.length sl - 1))
  in
  let rr = full_rm sl cr in
  let rm = gen_mapr rr sl in
  (* test_input rest new_sl new_rc rm *)
  let final_rm = forward_analysis rest new_sl new_rc rm in
  check_sat (rest @ new_sl) new_rc final_rm
