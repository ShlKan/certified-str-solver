open Dolmen
open Parser
open Nfa

(* Instantiate a module for parsing logic languages *)
module Logic =
  Class.Logic.Make (Std.Loc) (Std.Id) (Std.Term) (Std.Statement)
    (Std.Extensions)

(* instantiate the modules for typechecking *)

exception FormatError of string

let test file =
  (* Parse the file, and we get a tuple: - format: the guessed format
     (according to the file extension) - loc: some meta-data used for source
     file locations - statements: a lazy list of top-level directives found
     in the file *)
  let format, loc, parsed_statements_lazy = Logic.parse_all (`File file) in
  (* Any lexing/parsing error will be raised when forcing the lazy list of
     statements *)
  let parsed_statements = Lazy.force parsed_statements_lazy in
  (* You can match on the detected format of the input *)
  let () =
    match format with
    | Logic.Smtlib2 _ -> ()
    | Logic.Dimacs | Logic.ICNF | Logic.Alt_ergo | Logic.Tptp _ | Logic.Zf ->
        raise (FormatError "Only SMT file accepted")
  in
  (* Typing errors have a retcode associated to them, so that any typing
     error results in *)
  (* create the logic file corresponding to our input *)
  let lang : Dolmen_loop.Logic.language = Smtlib2 `Latest in
  let logic_file = State.mk_file ~lang ~loc "./" (`File file) in
  let response_file = State.mk_file "" (`File "this is unused") in
  (* let's create the initial state *)
  let state =
    State.empty
    |> State.init ~debug:false ~report_style:Contextual ~max_warn:max_int
         ~reports:(Dolmen_loop.Report.Conf.mk ~default:Enabled)
         ~response_file
           (* these limits are ignored in this example; to actually enforce
              the limits, one has to use the `run` function from
              `Dolmen_loop.Pipeline` *)
         ~time_limit:0. ~size_limit:0.
    |> State.set State.logic_file logic_file
    |> Typer_aux.init
    |> Typer.init ~type_check:true
  in
  (* We can loop over the parsed statements to generated the typed
     statements *)
  let _final_state, rev_typed_stmts =
    List.fold_left
      (fun (state, acc) parsed_stmt ->
        let state, typed_stmts = Typer.check state parsed_stmt in
        (state, List.rev_append typed_stmts acc) )
      (state, []) parsed_statements
  in
  let res = List.filter_map Parser.stmt_content (List.rev rev_typed_stmts) in
  List.iter Parser.print_str_cons res ;
  let nfa = Regex.compile (Regex.parse "[.]*[^a-zA-Z]") in
  match nfa with
  | {start; finals; next} ->
      Format.printf "Initial state: " ;
      StateSet.iter (fun s -> print_int (Int32.to_int s)) start ;
      Format.printf "\nAccepting state: " ;
      StateSet.iter (fun s -> print_int (Int32.to_int s)) finals ;
      let trans = next (Int32.of_int 0) in
      CharMap.iter
        (fun s i ->
          Format.printf " - %s -> " s ;
          StateSet.iter (fun s -> print_int (Int32.to_int s)) i )
        trans
(*; let typed_stmts = List.rev rev_typed_stmts in List.iter (fun typed_stmt
  -> Format.printf "%a@\n@." Typer.print typed_stmt) typed_stmts*)
;;

test Sys.argv.(1)
