open Dolmen

(* Instantiate a module for parsing logic languages *)
module Logic =
  Class.Logic.Make (Std.Loc) (Std.Id) (Std.Term) (Std.Statement)
    (Std.Extensions)

(* instantiate the modules for typechecking *)
module State = Dolmen_loop.State
module Typer_aux = Dolmen_loop.Typer.Typer (State)
module Typer =
  Dolmen_loop.Typer.Make (Std.Expr) (Std.Expr.Print) (State) (Typer_aux)

exception FormatError of string

let path_to_name (path : Std.Path.t) =
  let b = Buffer.create 16 in
  let formatter = Format.formatter_of_buffer b in
  Std.Path.print formatter path ;
  Format.pp_print_flush formatter () ;
  Buffer.contents b

type strConstrain =
  | Name of string
  | IN_RE of strConstrain * strConstrain
  | RegEx of string
  | OTHER

let rec print_str_constraint sc =
  match sc with
  | Name name -> Format.printf "%s" name
  | IN_RE (lhs, rhs) ->
      Format.printf "in_re " ;
      print_str_constraint lhs ;
      Format.printf ", " ;
      print_str_constraint rhs ;
      Format.printf "\n"
  | RegEx reg -> Format.printf "%s" reg
  | OTHER -> Format.printf "OTHER\n"

(* | {operator; args} -> ( match operator with | IN_RE -> Format.printf
   "in_re" | OTHER -> Format.printf "other" ) ; Format.printf " " ;
   Format.pp_print_list ~pp_sep:(return ", ") str_print Format.std_formatter
   args ; Format.printf "\n" *)

let var_name (var : Std.Expr.term_var) =
  match var with {path; _} -> path_to_name path

let cst_name (var : Std.Expr.term_cst) =
  match var with {path; _} -> path_to_name path

let rec term_str_constraint (tm : Std.Expr.term) =
  match tm with
  | {term_descr; _} -> (
    match term_descr with
    | Var var -> Some (Name (var_name var))
    | Cst cst -> Some (Name (cst_name cst))
    | App (op, _, args) -> (
      match term_str_constraint op with
      | Some (Name "in_re") ->
          let b = Buffer.create 16 in
          let fmt = Format.formatter_of_buffer b in
          Std.Expr.Print.term fmt (List.nth args 1) ;
          Format.pp_print_flush fmt () ;
          Some
            (IN_RE
               ( Option.get (term_str_constraint (List.nth args 0))
               , RegEx (Buffer.contents b) ) )
      | _ -> Some OTHER )
    | _ -> None )

let stmt_content (stmt : Typer.typechecked Typer.stmt) =
  match stmt with
  | {id= _; loc= _; contents; attrs= _; implicit= _} -> (
    match contents with `Hyp f -> term_str_constraint f | _ -> None )

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
  let res = List.filter_map stmt_content rev_typed_stmts in
  List.iter print_str_constraint res
(* let typed_stmts = List.rev rev_typed_stmts in

   List.iter (fun typed_stmt -> Format.printf "%a@\n@." Typer.print
   typed_stmt) typed_stmts *)
;;

test Sys.argv.(1)
