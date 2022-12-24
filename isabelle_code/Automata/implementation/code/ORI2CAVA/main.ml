
open Trans;;
open String;;
open Char;;
open Str ;;

exception Automata_less


module SS = Set.Make(String);;
module ConcatC = Map.Make(String);;
module ConcatR = Map.Make(String);;

let rec get_index_aux e l i = match l with [] -> -1 |  a :: rl -> (if a = e then i else (get_index_aux e rl (i + 1))) ;;
let get_index e l = get_index_aux e l 0;; 


let rec statesintrans t = 
            match t with
                [] -> []
             |  {origin=i;kind=_;toL=_} ::rs -> i :: statesintrans rs;;
        
let states at = match at with {init=_;trans=ts} -> statesintrans ts ;;

let rec acceptintrans t = 
            match t with
                [] -> []
             |  {origin=i;kind=0;toL=_} ::rs -> i :: acceptintrans rs
             |  {origin=i;kind=1;toL=_} ::rs -> acceptintrans rs
             |  {origin=i;kind=_;toL=_} ::rs -> acceptintrans rs;;

let rec acceptstates at =
            match at with {init=_;trans=ts} -> acceptintrans ts ;;

let initialstates at =
            match at with {init=s;trans=ts} -> s ;;


let rec output_intl oc l = match l with
            [] -> ()
         | x :: [] -> output_string oc (string_of_int (x ))
         | x :: rs -> output_string oc ((string_of_int(x))^"; ") ; output_intl oc rs ;;

let rec output_transitions oc ls = 
      match ls with
        [] -> ()
      | (s,l,t) :: [] -> output_string oc "(";
                 output_string oc (string_of_int (s));
                 output_string oc ",(";
                 output_string oc l;
                 output_string oc "),";
                 output_string oc (string_of_int (t));
                 output_string oc ")" ;
      | (s,l,t)::rs -> output_string oc "(";
                 output_string oc (string_of_int (s));
                 output_string oc ",(";
                 output_string oc l;
                 output_string oc "),";
                 output_string oc (string_of_int (t));
                 output_string oc ");" ;
                 output_transitions oc rs
                ;;



let rec init_states at = match at with {init = initstates; trans=_} -> initstates ;;

(************For HEX symbol and range*************)

let from = [| '0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'; 'A'; 'B'; 'C'; 'D'; 'E'; 'F' |] ;;
(*let To = [ 0 ;  1 ;  2 ;  3 ;  4 ;  5 ;  6 ;  7 ;  8;   9 ; 10; 11; 12; 13; 14; 15] ;; *)

let hexA c = 
    if c = from.(0) then 0
    else if c = from.(1) then 1
    else if c = from.(2) then 2
    else if c = from.(3) then 3
    else if c = from.(4) then 4
    else if c = from.(5) then 5
    else if c = from.(6) then 6
    else if c = from.(7) then 7
    else if c = from.(8) then 8
    else if c = from.(9) then 9
    else if c = 'a' then 10
    else if c = 'b' then 11
    else if c = 'c' then 12
    else if c = 'd' then 13
    else if c = 'e' then 14
    else if c = 'f' then 15
    else 0
    ;;

let l2int s = 
      (if length s == 1 then code (get s 0)
		else ((hexA (get s 2)) * 16 * 16 * 16 + (hexA (get s 3)) * 16 * 16 + (hexA (get s 4)) * 16 + (hexA (get s 5))))
     ;;


(*let _ = print_char (get "\\u0000" 5); print_newline() ;;
let _ = print_int (l2int "\\u0A0B") ; print_newline() ;;
*)

let rec gen_range bg ed = if bg == ed then concat "," [ string_of_int (ed); string_of_int (ed)]
                          else if bg < ed then concat "," [string_of_int bg; string_of_int ed ]
                          else "" ;;

let gen_label s = let ss = String.split_on_char '-' s in
if List.length ss == 1 then concat "," [ string_of_int(l2int (List.nth ss 0)); string_of_int(l2int (List.nth ss 0))]
else gen_range (l2int (List.nth ss 0)) (l2int (List.nth ss 1)) ;;


let rec trans1 s tos = match tos with [] -> [] |
                     {label=l;target=t} :: rs -> (s,gen_label l,t) :: trans1 s rs 

let rec trans2 t = 
            match t with
                [] -> []
             |  {origin=i;kind=_;toL=tos} ::rs -> (trans1 i tos) @ trans2 rs

let rec transitions at = match at with {init = initstates; trans=ts} -> trans2 ts ;;


       


let write_out oc at i = output_string oc ("let a" ^ string_of_int i ^ " = nfa_construct_reachable (nfa_construct ([], [") ;
(* output_intl oc (states at) ; *)
 print_string "number of transitions:" ; print_int (List.length (transitions at)) ; print_newline();
  output_transitions oc (transitions at);
			output_string oc ("], [") ;

   output_string oc (string_of_int (i * 1000) ^ "], [") ;
			output_intl oc (acceptstates at) ; output_string oc "] ));;" ;;
			
let rec write_out_automata al oc i =
      match al with [] -> ()
    | at :: res -> write_out oc at i; output_string oc "\n"; write_out_automata res oc (i+1) ;;
			


let header = "open Forward;; \n";;

let rec construct_product oc i = match i with
        1 -> output_string oc "a0"
      | i when i > 1 -> output_string oc "nfa_concate ";
                        output_string oc "a";
                        output_string oc (string_of_int (i-1));
                        output_string oc " " ;
                        construct_product oc (i-1) 
      | _ -> raise Automata_less ;; 

(*
let convert_one s =
  let oc = open_out (s ^ ".ml") in
  let ic = open_in (s) in
         
        output_string oc header;
        let lexbuf = Lexing.from_channel ic in
        let result = Ori.automataEnd Orilex.lexer lexbuf in
        write_out_automata result oc 0; 
        output_string oc "let product = "; 
        construct_product oc (List.length result);
        output_string oc ";;\n";
        output_string oc "print_auto (nfa_destruct product) ;;\n"; 
        close_out oc ; close_in ic;;
*)

let convert_one s = ();;

let f e ol = match ol with None -> Some [e] | Some l -> Some (e :: l) ;;

let rec genStrCon cons = match cons with
                  [] -> (SS.empty, ConcatC.empty, ConcatR.empty)
                | a :: rcons ->
		  let (reSS, reC, reR) = genStrCon rcons in 
		    (match a with
			   Strconcat (v1,v2,v3) ->
			     (SS.add v3 (SS.add v2 (SS.add v1 reSS)),
			      ConcatC.update v1 (f (v2, v3)) reC,
			      reR
			      ) |
                            Regexcon (v, aut) -> 
                             (SS.add v reSS,
                              reC,
                              ConcatR.update v (f aut) reR)
			      
                     ) ;;

let print_set s = List.iter (fun s -> print_string s; print_string "; ") (SS.elements s) ;;
let print_mapc s = List.iter (fun (s1,s2) -> print_string s1; print_string "-->";
				  (List.iter (fun (s1,s2) -> print_string s1; print_string " . ";
						  print_string s2; print_string "\n") s2);
						 print_string "; \n") (ConcatC.bindings s) ;;

let genv s l = "v" ^ (string_of_int (get_index s l)) ;;
						 
let out_mapc oc s l = output_string oc "["; (List.iter (fun (s1,s2) -> output_string oc (("(" ^ (genv s1 l)) ^ ", [") ;
				     (List.iter (fun (s11,s12) -> output_string oc ("(" ^ (genv s11 l));
						     output_string oc ", ";
						     output_string oc ((genv s12 l) ^ "); ")) s2);
				     output_string oc "]); ") (ConcatC.bindings s));
                      output_string oc "]";;

						 
let print_auto at = print_string ("nfa_construct ([], [") ;

			print_string ("], [") ;
   print_string (string_of_int (0) ^ "], [") ;
   output_intl stdout (acceptstates at) ; print_string "] );;" ;;

let rec transitions_string ls = 
      match ls with
        [] -> ""
      | (s,l,t) :: [] -> "(" ^ (string_of_int (s)) ^  ",(" ^ l ^ ")," ^ (string_of_int (t)) ^ ")" ;
      | (s,l,t)::rs -> "(" ^ (string_of_int (s)) ^ ",(" ^ l ^ ")," ^ (string_of_int (t)) ^ ");" ^ transitions_string rs
                ;;

let rec intl_string  l = match l with
            [] -> ""
         | x :: [] -> (string_of_int (x))
         | x :: rs -> ((string_of_int(x)) ^ "; ") ^ (intl_string rs) ;;
   

	 
let auto_string at =  "(nfa_construct_reachable (nfa_construct ([], [" ^
   (transitions_string (transitions at)) ^
		        "], [" ^ (intl_string (initialstates at)) ^ "], [" ^
   intl_string (acceptstates at) ^ "])))" ;;


let search_index r s = try search_forward r s 0 with Not_found -> -1 ;;

let splitAT s = let ic = open_in s in 
    let cnt = ref 0 in 
    try
    let reg1 = regexp "The following 2 automata have empty intersection:" in
    while true do
        let line = input_line ic in let bi = search_index reg1 line in 
            if bi <> -1 then (
                let oc = open_out (s^(string_of_int (!cnt))^"a") in 
                let reg2 = regexp "========\\|sat" in 
                let line1 = ref (input_line ic) in let bi1 = ref (search_index reg2 !line1) in 
                cnt := !cnt + 1;
                while !bi1 = -1 do
                   output_string oc (!line1^"\n");
                   line1 := input_line ic ;
                   bi1 := (search_index reg2 !line1)
                done;
                close_out oc;
            ) else ()
     done
     with End_of_file -> ( close_in ic;
        let i = ref 0 in
        while !i < !cnt do 
             convert_one (s^(string_of_int (!i))^"a");
             i := !i + 1
        done 
     );;

let rec gen_concate l = match l with
      [] -> raise Automata_less
    | [a] -> auto_string a 
    |  a :: rl -> "(nfa_product "^ " " ^ auto_string a ^ " " ^ gen_concate rl ^ ")";;

let rec out_S oc l sl = match l with
      [] -> ()
    | a :: rl -> (output_string oc ("let " ^ (genv a sl) ^ " = (" ^ "z_to_int " ^ (string_of_int (get_index a sl)) ^ ");;\n");
                  out_S oc rl sl);;
    
let out_mapr oc s l = output_string oc "[" ; (List.iter (fun (s1,s2) -> output_string oc "("; output_string oc (genv s1 l);
					                                  output_string oc ",";
				                output_string oc (gen_concate s2);
					        output_string oc "); \n") (ConcatR.bindings s)) ; output_string oc "]" ;;

let rec full_rm sl rm = match sl with
[] -> rm
| a :: rl -> (if ConcatR.mem a rm then (full_rm rl rm) else (full_rm rl (ConcatR.add a [{init=[0];trans=[{origin=0;kind=0;
                  toL = [{label = "\\u0000-\\uffff"; target = 0}]}]}] rm)));;


let rec gen_intl b e = (if b = e then ("v"^(string_of_int e)) else
		       (("v"^(string_of_int b)) ^ "; " ^ (gen_intl (b+1) e))) ;;

let convert_one_cons s =
  let oc = open_out (s ^ ".ml") in
  let ic = open_in (s) in
  output_string oc header;
  let lexbuf = Lexing.from_channel ic in
  let result = Ori.strCons Orilex.lexer lexbuf in
  let (s,c,r) = genStrCon (fst result) in
  let sl = SS.elements s in
  out_S oc sl sl;
  output_string oc ("let s = gen_S_from_list [" ^ (gen_intl 0 (List.length sl - 1)) ^ "];;\n") ;
  output_string oc "let rc = gen_rc_from_list "; out_mapc oc c sl; output_string oc ";;";
  output_string oc "\n";
  let r = full_rm sl r in 
  output_string oc "let rm = gen_rm_from_list ";
  out_mapr oc r sl;
  output_string oc ";;\n";
  output_string oc "let (s,(rm,r)) = forward_analysis (z_to_int 1) (z_to_int 2) s rc rm ;; \n" ;
  output_string oc ("print_string (check_unsat_rm (rm_to_list rm));;") ;
  close_out oc ; close_in ic;;

convert_one_cons Sys.argv.(1)  ;;
  
              
        






































