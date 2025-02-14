open Nfa

let to_code s =
  if String.length s = 1 then Char.code (String.get s 0)
  else int_of_string ("0x" ^ String.sub s 2 (String.length s - 2))

let get_interval s =
  let l = if String.length s = 1 then [s] else String.split_on_char '-' s in
  if List.length l == 2 then (to_code (List.nth l 0), to_code (List.nth l 1))
  else (to_code (List.nth l 0), to_code (List.nth l 0))

let transitions_single next left pre_trans =
  CharMap.fold
    (fun l rights trans ->
      StateSet.fold
        (fun right ss ->
          (Int32.to_int left, [get_interval l], Int32.to_int right) :: ss )
        rights trans )
    (next left) pre_trans

let transitions all_states next =
  StateSet.fold (transitions_single next) all_states []

let outputFunc l index i =
  if Z.to_int index = -1 then None
  else if Z.to_int index = -2 then
    match i with None -> None | Some b -> Some [(b, b)]
  else
    match i with
    | None -> Some (List.nth l (Z.to_int index))
    | Some _ -> None

let rec trans_NFA2NFT trans =
  match trans with
  | [] -> ([], [])
  | (q1, l, q2) :: l' ->
      let t, ll = trans_NFA2NFT l' in
      ((q1, ((None, List.length ll), q2)) :: t, ll @ [l])

let rec trans_NFA2NFT_None trans =
  match trans with
  | [] -> []
  | (q1, l, q2) :: l' ->
      let t = trans_NFA2NFT_None l' in
      ( q1
      , ( (Some (List.map (fun (l1, l2) -> (Z.of_int l1, Z.of_int l2)) l), -1)
        , q2 ) )
      :: t

(* Test *)
(*
let test_trans = [(1, [(3, 4)], 2); (1, [(13, 14)], 3); (2, [(3, 34)], 3)]

let test_none_trans = trans_NFA2NFT test_trans ;;

Format.printf "-----------***----------\n" ;;

List.iter
  (fun l -> List.iter (fun (l1, l2) -> Format.printf "(%d, %d); " l1 l2) l)
  (snd test_none_trans)
;;

Format.printf "\n" ;
List.iter
  (fun (q1, (l, q2)) ->
    let ll =
      match l with
      | None, index -> "None, " ^ string_of_int index
      | Some _, _ -> "label"
    in
    Format.printf "(%d, %s ,%d)\n" q1 ll q2 )
  (fst test_none_trans)
;;

Format.printf "-----------***----------\n"
*)
(* SFA to SFT *)
let nfa2FT (nfa : Nfa.nfa) n =
  let states = SNFA.gather_states nfa in
  match nfa with
  | {start; finals= _; next= _} ->
      List.map Int32.to_int (StateSet.to_list start)
