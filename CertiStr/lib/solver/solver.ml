open Transducer
open Nfa
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

let solve (constraints : Parser.strConstrain list) =
  let ss, cc, cr = genStrConstraints constraints in
  SS.elements ss
