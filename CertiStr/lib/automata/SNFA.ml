open Nfa

let printStateSet states =
  StateSet.iter
    (fun state -> Format.printf "%d " (Int32.to_int state))
    states

let printTransSet ori trans =
  Format.printf "%s:\n" (Int32.to_string ori) ;
  CharMap.iter
    (fun l ss ->
      StateSet.iter
        (fun s -> Format.printf "\t-[%s]-> %s\n" l (Int32.to_string s))
        ss )
    trans

let rec reachableStates (reached : StateSet.t) (state : state)
    (next : state -> transitions) =
  let reached = StateSet.add state reached in
  let trans = next state in
  CharMap.fold
    (fun l ss reached_1 ->
      StateSet.fold
        (fun s reached_2 ->
          if StateSet.mem s reached_2 then reached_2
          else reachableStates reached_2 s next )
        ss reached_1 )
    trans reached

let rec gather_states nfa =
  match nfa with
  | {start; finals= _; next} ->
      StateSet.fold
        (fun s reached -> reachableStates reached s next)
        start StateSet.empty

let printNfa nfa =
  match nfa with
  | {start; finals; next} ->
      Format.printf "---------- NFA -----------\n" ;
      Format.printf "States:\n" ;
      let all_states = gather_states nfa in
      printStateSet all_states ;
      Format.printf "\n---------------\nInitial States:\n" ;
      printStateSet start ;
      Format.printf "\n---------------\nTransitions:\n" ;
      StateSet.iter (fun s -> printTransSet s (next s)) all_states ;
      Format.printf "\n---------------\nAccepting States:\n" ;
      printStateSet finals ;
      Format.printf "\n"
