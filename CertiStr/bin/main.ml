open Dolmen

(* Instantiate a module for parsing logic languages *)
module Logic = Class.Logic.Make(Std.Loc)(Std.Id)(Std.Term)(Std.Statement)(Std.Extensions)

(* instantiate the modules for typechecking *)
module State = Dolmen_loop.State
module Typer_aux = Dolmen_loop.Typer.Typer(State)
module Typer = Dolmen_loop.Typer.Make(Std.Expr)(Std.Expr.Print)(State)(Typer_aux)

let test file =

  (* *** Parsing ********************************************************** *)


  (* Parse the file, and we get a tuple:
    - format: the guessed format (according to the file extension)
    - loc: some meta-data used for source file locations
    - statements: a lazy list of top-level directives found in the file *)
  let format, loc, parsed_statements_lazy = Logic.parse_all (`File file) in

  (* Any lexing/parsing error will be raised when forcing the lazy list
     of statements *)
  let parsed_statements = Lazy.force parsed_statements_lazy in

  (* You can match on the detected format of the input *)
  let () =
    match format with
    | Logic.Dimacs | Logic.ICNF -> ()
    | Logic.Alt_ergo | Logic.Smtlib2 _ | Logic.Tptp _ | Logic.Zf -> ()
  in

  (* *** Typing *********************************************************** *)

  (* Typing errors have a retcode associated to them, so that any typing
     error results in *)

  (* create the logic file corresponding to our input *)
  let lang : Dolmen_loop.Logic.language = Smtlib2 `Latest in
  let logic_file = State.mk_file ~lang ~loc "./" (`File file) in
  let response_file = State.mk_file "" (`File "this is unused") in

  (* let's create the initial state *)
  let state =
    State.empty
    |> State.init
       ~debug:false ~report_style:Contextual ~max_warn:max_int
       ~reports:(Dolmen_loop.Report.Conf.mk ~default:Enabled)
       ~response_file
       (* these limits are ignored in this example; to actually enforce
          the limits, one has to use the `run` function from `Dolmen_loop.Pipeline` *)
       ~time_limit:0. ~size_limit:0.
    |> State.set State.logic_file logic_file
    |> Typer_aux.init
    |> Typer.init ~type_check:true
  in

  (* We can loop over the parsed statements to generated the typed statements *)
  let _final_state, rev_typed_stmts =
    List.fold_left (fun (state, acc) parsed_stmt ->
      let state, typed_stmts = Typer.check state parsed_stmt in
      (state, List.rev_append typed_stmts acc)
    ) (state, []) parsed_statements
  in
  let typed_stmts = List.rev rev_typed_stmts in

  print_endline "test--";
  (* let's print the typed statements *)
  List.iter (fun typed_stmt ->
    Format.printf "%a@\n@." Typer.print typed_stmt
  ) typed_stmts ;;

test Sys.argv.(1)
