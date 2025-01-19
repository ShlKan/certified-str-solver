open Solve

let main file =
  let stmts = Parser.parseSMT file in
  let strCons = List.filter_map Parser.stmt_content stmts in
  if Solver.check_constraints strCons = false then
    Format.fprintf Format.err_formatter "Unsupported string constraints." ;
  let normalStrCons = Solver.normalStrConstraints strCons in
  Solver.solve normalStrCons
;;

main Sys.argv.(1)
