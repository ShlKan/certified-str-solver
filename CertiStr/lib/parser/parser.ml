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
  | RegEx of string
  | REPLACE of string * string * string
  | StrEq of strConstrain * strConstrain
  | Concat of strConstrain * strConstrain
  | OTHER

let rec print_str_constraint fmt sc =
  match sc with
  | Name name -> Format.fprintf fmt "%s" name
  | IN_RE (lhs, rhs) ->
      Format.fprintf fmt "str.in_re %a, %a" print_str_constraint lhs
        print_str_constraint rhs
  | RegEx reg -> Format.fprintf fmt "%s" reg
  | REPLACE (s, p, r) -> Format.fprintf fmt "str.replace %s %s %s" s p r
  | StrEq (lhs, rhs) ->
      Format.fprintf fmt "%a = %a" print_str_constraint lhs
        print_str_constraint rhs
  | Concat (lhs, rhs) ->
      Format.fprintf fmt "str.++ %a %a" print_str_constraint lhs
        print_str_constraint rhs
  | OTHER -> Format.fprintf fmt "OTHER\n"

let print_str_cons sc =
  print_str_constraint Format.std_formatter sc ;
  Format.fprintf Format.std_formatter "\n"

let var_name (var : Std.Expr.term_var) =
  match var with {path; _} -> path_to_name path

let cst_name (var : Std.Expr.term_cst) =
  match var with {path; _} -> path_to_name path

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
    | Cst cst -> Some (Name (cst_name cst))
    | App (op, _, args) -> (
      match term_str op with
      | "in_re" ->
          Option.some
            (IN_RE
               ( Option.get (term_str_constraint (List.nth args 0))
               , RegEx (term_str (List.nth args 1)) ) )
      | "replace" ->
          Option.some
            (REPLACE
               ( term_str (List.nth args 0)
               , term_str (List.nth args 1)
               , term_str (List.nth args 2) ) )
      | "++" ->
          Option.some
            (Concat
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1)) ) )
      | "=" ->
          Option.some
            (StrEq
               ( Option.get (term_str_constraint (List.nth args 0))
               , Option.get (term_str_constraint (List.nth args 1)) ) )
      | _ -> Some OTHER )
    | _ -> None )

module State = Dolmen_loop.State
module Typer_aux = Dolmen_loop.Typer.Typer (State)
module Typer =
  Dolmen_loop.Typer.Make (Std.Expr) (Std.Expr.Print) (State) (Typer_aux)

let stmt_content (stmt : Typer.typechecked Typer.stmt) =
  match stmt with
  | {id= _; loc= _; contents; attrs= _; implicit= _} -> (
    match contents with `Hyp f -> term_str_constraint f | _ -> None )
