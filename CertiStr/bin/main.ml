open Solve
open Cmdliner

let leftmost =
  let doc = "Use left-most solving strategy." in
  Arg.(value & flag & info ["left-most"] ~doc)

let file =
  let doc = "Input SMT file." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE" ~doc)

let main file leftmost =
  let stmts = Parser.parseSMT file in
  let strCons = List.filter_map Parser.stmt_content stmts in
  if Solver.check_constraints strCons = false then
    Format.fprintf Format.err_formatter
      "Unsupported\n   string constraints: Check." ;
  let normalStrCons = Solver.normalStrConstraints strCons in
  (*List.iter (Parser.print_str_constraint Format.std_formatter)
    normalStrCons*)
  let _ = Solver.solve normalStrCons leftmost in
  ()

let main_cmd =
  let doc = "Certified string solver" in
  Cmd.v (Cmd.info "certistr" ~doc) Term.(const main $ file $ leftmost)

let () =
  let exit_code = Cmd.eval main_cmd in
  Stdlib.exit exit_code
