type token =
  | Lrange
  | Label of (string)
  | Lint of (int)
  | Leol
  | LAutomaton
  | Lsingle of (string)
  | LState
  | LInitial
  | Lconcat
  | Lin
  | Lleft
  | LLleft
  | Lright
  | LRright
  | LReject
  | LEOF
  | Lcomm
  | LBleft
  | LBright
  | LAccept
  | LArrow
  | Lsep
  | Lsepa
  | Lassign
  | Leq
  | Lstr of (int list)
  | Lvar of (string)
  | Lresult of (string)

open Parsing;;
let _ = parse_error;;
# 3 "ori.mly"

open Trans ;;
open String;;
open Char ;;

let rec dtox s = Printf.sprintf "\\u%04x" s ;;

let rec str_code_l1 i s = if i >= ((String.length s) ) then []
       		      	else ( (((code (get s i))) ::
			      (str_code_l1 (i+1) s))) ;;


let label2kind l = match l with 
       "accept"  -> 0
     | "reject"  -> 1
     |   _       -> 2 ;;

let rec consTrans i l = match l with
    [] -> [{origin = i; kind = 0; toL = []}]
   | a :: rl -> ({origin = i; kind = 1; toL = [{label =  dtox a; target = (i + 1)}]} :: (consTrans (i+1) rl));;
   
let consAuto l = if l = [] then {init = [0]; trans = [{origin = 0; kind = 1; toL = [{label = "\\u0020"; target = 1}]};
    	       	      	                              {origin = 1; kind = 0; toL = []}
						      ]}
    	       	 else {init = [0]; trans = (consTrans 0 l)} ;;

# 61 "ori.ml"
let yytransl_const = [|
  257 (* Lrange *);
  260 (* Leol *);
  261 (* LAutomaton *);
  263 (* LState *);
  264 (* LInitial *);
  265 (* Lconcat *);
  266 (* Lin *);
  267 (* Lleft *);
  268 (* LLleft *);
  269 (* Lright *);
  270 (* LRright *);
  271 (* LReject *);
  272 (* LEOF *);
  273 (* Lcomm *);
  274 (* LBleft *);
  275 (* LBright *);
  276 (* LAccept *);
  277 (* LArrow *);
  278 (* Lsep *);
  279 (* Lsepa *);
  280 (* Lassign *);
  281 (* Leq *);
    0|]

let yytransl_block = [|
  258 (* Label *);
  259 (* Lint *);
  262 (* Lsingle *);
  282 (* Lstr *);
  283 (* Lvar *);
  284 (* Lresult *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\003\000\003\000\003\000\005\000\
\006\000\006\000\004\000\004\000\007\000\009\000\009\000\008\000\
\008\000\010\000\011\000\012\000\012\000\013\000\014\000\014\000\
\014\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\015\000\016\000\000\000"

let yylen = "\002\000\
\003\000\002\000\001\000\002\000\009\000\004\000\004\000\002\000\
\001\000\002\000\004\000\003\000\004\000\001\000\001\000\001\000\
\002\000\000\000\007\000\001\000\002\000\000\000\003\000\003\000\
\004\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\038\000\000\000\000\000\000\000\000\000\
\000\000\002\000\000\000\004\000\000\000\000\000\000\000\000\000\
\001\000\000\000\000\000\000\000\007\000\000\000\006\000\012\000\
\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\
\011\000\017\000\000\000\013\000\000\000\000\000\015\000\014\000\
\000\000\000\000\000\000\005\000\000\000\026\000\035\000\036\000\
\028\000\029\000\027\000\030\000\031\000\032\000\033\000\034\000\
\019\000\020\000\000\000\000\000\000\000\021\000\000\000\000\000\
\000\000\037\000\023\000\000\000\024\000\025\000"

let yydgoto = "\002\000\
\004\000\005\000\006\000\014\000\000\000\000\000\020\000\027\000\
\041\000\028\000\029\000\057\000\058\000\059\000\060\000\061\000"

let yysindex = "\004\000\
\004\255\000\000\250\254\000\000\248\254\004\255\011\255\019\255\
\006\255\000\000\017\255\000\000\001\255\012\255\022\255\013\255\
\000\000\018\255\031\255\032\255\000\000\014\255\000\000\000\000\
\020\255\037\255\024\255\000\000\032\255\027\255\042\255\035\255\
\000\000\000\000\021\255\000\000\010\255\033\255\000\000\000\000\
\036\255\028\255\030\255\000\000\255\254\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\255\254\002\255\029\255\000\000\255\254\003\255\
\050\255\000\000\000\000\051\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\254\254\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\038\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\008\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\008\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\049\000\000\000\000\000\000\000\000\000\000\000\027\000\
\000\000\000\000\000\000\255\255\000\000\000\000\252\255\000\000"

let yytablesize = 59
let yytable = "\046\000\
\047\000\048\000\063\000\007\000\001\000\067\000\018\000\010\000\
\019\000\049\000\050\000\051\000\052\000\003\000\022\000\053\000\
\054\000\008\000\009\000\011\000\055\000\056\000\064\000\068\000\
\039\000\003\000\022\000\015\000\013\000\040\000\003\000\016\000\
\017\000\022\000\021\000\023\000\024\000\025\000\026\000\032\000\
\030\000\031\000\033\000\035\000\036\000\037\000\042\000\038\000\
\043\000\065\000\044\000\045\000\069\000\070\000\012\000\034\000\
\018\000\062\000\066\000"

let yycheck = "\001\001\
\002\001\003\001\001\001\010\001\001\000\003\001\006\001\016\001\
\008\001\011\001\012\001\013\001\014\001\016\001\007\001\017\001\
\018\001\024\001\025\001\028\001\022\001\023\001\021\001\021\001\
\015\001\028\001\019\001\009\001\018\001\020\001\027\001\026\001\
\016\001\012\001\023\001\023\001\019\001\007\001\007\001\003\001\
\027\001\022\001\019\001\017\001\003\001\011\001\014\001\027\001\
\013\001\021\001\023\001\022\001\003\001\003\001\006\000\029\000\
\019\001\059\000\063\000"

let yynames_const = "\
  Lrange\000\
  Leol\000\
  LAutomaton\000\
  LState\000\
  LInitial\000\
  Lconcat\000\
  Lin\000\
  Lleft\000\
  LLleft\000\
  Lright\000\
  LRright\000\
  LReject\000\
  LEOF\000\
  Lcomm\000\
  LBleft\000\
  LBright\000\
  LAccept\000\
  LArrow\000\
  Lsep\000\
  Lsepa\000\
  Lassign\000\
  Leq\000\
  "

let yynames_block = "\
  Label\000\
  Lint\000\
  Lsingle\000\
  Lstr\000\
  Lvar\000\
  Lresult\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'strConss) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 49 "ori.mly"
                                  ((_1,_2))
# 214 "ori.ml"
               : (Trans.str_cons list) * string))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'strConss) in
    Obj.repr(
# 50 "ori.mly"
                           ((_1,"non"))
# 221 "ori.ml"
               : (Trans.str_cons list) * string))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'strCon) in
    Obj.repr(
# 52 "ori.mly"
            ([_1])
# 228 "ori.ml"
               : 'strConss))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'strCon) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'strConss) in
    Obj.repr(
# 53 "ori.mly"
                                      (_1 :: _2)
# 236 "ori.ml"
               : 'strConss))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 56 "ori.mly"
                                                             (Strconcat (_1, _5, _7))
# 245 "ori.ml"
               : 'strCon))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int list) in
    Obj.repr(
# 57 "ori.mly"
                            (Regexcon (_1, consAuto _3))
# 253 "ori.ml"
               : 'strCon))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'automaton) in
    Obj.repr(
# 58 "ori.mly"
                                 (Regexcon (_1, _3))
# 261 "ori.ml"
               : 'strCon))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'automata) in
    Obj.repr(
# 62 "ori.mly"
                  (_1)
# 268 "ori.ml"
               : 'automataEnd))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'automaton) in
    Obj.repr(
# 65 "ori.mly"
                    ([_1])
# 275 "ori.ml"
               : 'automata))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'automaton) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'automata) in
    Obj.repr(
# 66 "ori.mly"
                           ( _1 :: _2 )
# 283 "ori.ml"
               : 'automata))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'initstate) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'transitions) in
    Obj.repr(
# 70 "ori.mly"
                                              ({init=_2; trans=_3})
# 291 "ori.ml"
               : 'automaton))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 71 "ori.mly"
                                (consAuto (str_code_l1 0 _2))
# 298 "ori.ml"
               : 'automaton))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 77 "ori.mly"
                                ([_4])
# 305 "ori.ml"
               : 'initstate))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "ori.mly"
                       ("accept")
# 311 "ori.ml"
               : 'tlabel))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "ori.mly"
                       ("reject")
# 317 "ori.ml"
               : 'tlabel))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'epsilon) in
    Obj.repr(
# 84 "ori.mly"
                       ( _1 )
# 324 "ori.ml"
               : 'transitions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'transition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'transitions) in
    Obj.repr(
# 85 "ori.mly"
                                    (_1 :: _2)
# 332 "ori.ml"
               : 'transitions))
; (fun __caml_parser_env ->
    Obj.repr(
# 88 "ori.mly"
                                               (  [] )
# 338 "ori.ml"
               : 'epsilon))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : int) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'tlabel) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'ttos) in
    Obj.repr(
# 92 "ori.mly"
                                                ({origin=_2; kind=(label2kind _4); toL=_7})
# 347 "ori.ml"
               : 'transition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'emptyto) in
    Obj.repr(
# 95 "ori.mly"
                         ( _1     )
# 354 "ori.ml"
               : 'ttos))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'tto) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ttos) in
    Obj.repr(
# 96 "ori.mly"
                  ( _1 :: _2 )
# 362 "ori.ml"
               : 'ttos))
; (fun __caml_parser_env ->
    Obj.repr(
# 99 "ori.mly"
                                         ([])
# 368 "ori.ml"
               : 'emptyto))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'sspec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 102 "ori.mly"
                           ({label=_1; target=(_3)})
# 376 "ori.ml"
               : 'tto))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'range) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 103 "ori.mly"
                                        ({label=_1; target=(_3)})
# 384 "ori.ml"
               : 'tto))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'sspec) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 104 "ori.mly"
                               ({label=(String.concat "-" [_1;">"]); target=(_4)})
# 392 "ori.ml"
               : 'tto))
; (fun __caml_parser_env ->
    Obj.repr(
# 107 "ori.mly"
               ("\\u002d")
# 398 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "ori.mly"
                                        ("[")
# 404 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 109 "ori.mly"
              ("]")
# 410 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 110 "ori.mly"
               ("(")
# 416 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 111 "ori.mly"
                (")")
# 422 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 112 "ori.mly"
              (",")
# 428 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 113 "ori.mly"
               ("{")
# 434 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 114 "ori.mly"
             (":")
# 440 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    Obj.repr(
# 115 "ori.mly"
              (";")
# 446 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 116 "ori.mly"
              (_1)
# 453 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 117 "ori.mly"
             (string_of_int _1)
# 460 "ori.ml"
               : 'sspec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'sspec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'sspec) in
    Obj.repr(
# 120 "ori.mly"
                          (String.concat "-" [_1;_3])
# 468 "ori.ml"
               : 'range))
(* Entry strCons *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let strCons (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : (Trans.str_cons list) * string)
