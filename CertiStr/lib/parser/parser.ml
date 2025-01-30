(**
 * Copyright 2025 kanshl
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)
open Dolmen

let path_to_name (path : Std.Path.t) =
  let b = Buffer.create 16 in
  let formatter = Format.formatter_of_buffer b in
  Std.Path.print formatter path ;
  Format.pp_print_flush formatter () ;
  Buffer.contents b

type strConstrain =
  | Name of string
  | IN_RE of strConstrain * strConstrain
  | IN_NFA of strConstrain * Nfa.nfa
  | RegEx of string
  | REPLACE of strConstrain * strConstrain * string
  | StrEq of strConstrain * strConstrain
  | Concat of strConstrain * strConstrain
  | Range of string * string
  | Union of strConstrain * strConstrain
  | Star of strConstrain
  | Plus of strConstrain
  | Str of string
  | OTHER

let rec reg2Str (c : strConstrain) =
  match c with
  | Name s -> s
  | Concat (sl, sr) -> reg2Str sl ^ reg2Str sr
  | Union (sl, sr) -> reg2Str sl ^ "|" ^ reg2Str sr
  | RegEx s -> String.sub s 1 (String.length s - 2)
  | Star s -> "(" ^ reg2Str s ^ ")*"
  | Plus s -> "(" ^ reg2Str s ^ ")+"
  | Range (s1, s2) -> "[" ^ s1 ^ "-" ^ s2 ^ "]"
  | OTHER -> "Other"
  | _ -> "Error"

let rec print_str_constraint fmt sc =
  match sc with
  | Name name -> Format.fprintf fmt "%s" name
  | IN_RE (lhs, rhs) ->
      Format.fprintf fmt "str.in_re %a, %s\n" print_str_constraint lhs
        (reg2Str rhs)
  | IN_NFA (lhs, rhs) ->
      Format.fprintf fmt "str.in_re %a, \n" print_str_constraint lhs ;
      Transducer.SNFA.printNfa rhs
  | RegEx reg -> Format.fprintf fmt "%s" reg
  | REPLACE (s, p, r) ->
      Format.fprintf fmt "str.replace %a %a %s" print_str_constraint s
        print_str_constraint p r
  | StrEq (lhs, rhs) ->
      Format.fprintf fmt "%a = %a\n" print_str_constraint lhs
        print_str_constraint rhs
  | Concat (lhs, rhs) ->
      Format.fprintf fmt "str.++ %a %a" print_str_constraint lhs
        print_str_constraint rhs
  | Union (lhs, rhs) ->
      Format.fprintf fmt "str.union %a %a" print_str_constraint lhs
        print_str_constraint rhs
  | Star cons -> Format.fprintf fmt "str.+ %a" print_str_constraint cons
  | Plus cons -> Format.fprintf fmt "str.* %a" print_str_constraint cons
  | Range (s1, s2) -> Format.fprintf fmt "str.range %s %s" s1 s2
  | Str s -> Format.fprintf fmt "%s" s
  | OTHER -> Format.fprintf fmt "OTHER\n"

let print_str_cons sc =
  print_str_constraint Format.std_formatter sc ;
  Format.fprintf Format.std_formatter "\n"

let var_name (var : Std.Expr.term_var) =
  match var with {path; _} -> path_to_name path

let cst_name (var : Std.Expr.term_cst) =
  let s = match var with {path; _} -> path_to_name path in
  if String.get s 0 = '\"' then Str s else Name s

(* term_name returns name (string) of a term. *)
let term_str (tm : Std.Expr.term) =
  let b = Buffer.create 16 in
  let fmt = Format.formatter_of_buffer b in
  Std.Expr.Print.term fmt tm ;
  Format.pp_print_flush fmt () ;
  Buffer.contents b

let rec term_str_constraint (tm : Std.Expr.term) =
  match tm with
  | {term_descr; _} -> (
    match term_descr with
    | Var var -> Some (Name (var_name var))
    | Cst cst -> Some (cst_name cst)
    | App (op, _, args) -> (
      match term_str op with
      | "in_re" ->
          Option.some
            (IN_RE
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1)) ) )
      | "replace" ->
          Option.some
            (REPLACE
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1))
               , term_str (List.nth args 2) ) )
      | "++" ->
          Option.some
            (Concat
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1)) ) )
      | "∪" ->
          Option.some
            (Union
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1)) ) )
      | "of_string" -> Option.some (RegEx (term_str (List.nth args 0)))
      | "=" ->
          Option.some
            (StrEq
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1)) ) )
      | "+" ->
          Option.some
            (Plus (Option.get (term_str_constraint (List.nth args 0))))
      | "*" ->
          Option.some
            (Star (Option.get (term_str_constraint (List.nth args 0))))
      | "range" ->
          Option.some
            (Range
               ( String.sub (term_str (List.nth args 0)) 1 1
               , String.sub (term_str (List.nth args 1)) 1 1 ) )
      | _ ->
          Format.fprintf Format.std_formatter "[%s] %d\n" (term_str op)
            (List.length args) ;
          Some OTHER )
    | _ -> None )

module State = Dolmen_loop.State
module Typer_aux = Dolmen_loop.Typer.Typer (State)
module Typer =
  Dolmen_loop.Typer.Make (Std.Expr) (Std.Expr.Print) (State) (Typer_aux)

let stmt_content (stmt : Typer.typechecked Typer.stmt) =
  match stmt with
  | {id= _; loc= _; contents; attrs= _; implicit= _} -> (
    match contents with `Hyp f -> term_str_constraint f | _ -> None )

(* Instantiate a module for parsing logic languages *)
module Logic =
  Class.Logic.Make (Std.Loc) (Std.Id) (Std.Term) (Std.Statement)
    (Std.Extensions)

(* instantiate the modules for typechecking *)

exception FormatError of string

(* Parse a file and return the statements of the file. *)
let parseSMT file =
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
  List.rev rev_typed_stmts
