open Solve

let main file =
  let stmts = Parser.parseSMT file in
  let strCons = List.filter_map Parser.stmt_content stmts in
  if Solver.check_constraints strCons = false then
    Format.fprintf Format.err_formatter
      "Unsupported\n   string constraints: Check." ;
  let normalStrCons = Solver.normalStrConstraints strCons in
  (*List.iter (Parser.print_str_constraint Format.std_formatter)
    normalStrCons*)
  Solver.solve normalStrCons
;;

main Sys.argv.(1)
