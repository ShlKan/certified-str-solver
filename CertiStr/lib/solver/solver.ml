open Transducer
open Nfa

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
