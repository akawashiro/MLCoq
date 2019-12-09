type token =
  | CODE of (Coqpp_ast.code)
  | COMMENT of (string)
  | IDENT of (string)
  | QUALID of (string)
  | STRING of (string)
  | INT of (int)
  | VERNAC
  | TACTIC
  | GRAMMAR
  | EXTEND
  | END
  | DECLARE
  | PLUGIN
  | DEPRECATED
  | LBRACKET
  | RBRACKET
  | PIPE
  | ARROW
  | COMMA
  | EQUAL
  | LPAREN
  | RPAREN
  | COLON
  | SEMICOLON
  | GLOBAL
  | FIRST
  | LAST
  | BEFORE
  | AFTER
  | LEVEL
  | LEFTA
  | RIGHTA
  | NONA
  | EOF

open Parsing;;
let _ = parse_error;;
# 10 "coqpp/coqpp_parse.mly"

open Coqpp_ast

let starts s pat =
  let len = String.length s in
  let patlen = String.length pat in
  if patlen <= len && String.sub s 0 patlen = pat then
    Some (String.sub s patlen (len - patlen))
  else None

let ends s pat =
  let len = String.length s in
  let patlen = String.length pat in
  if patlen <= len && String.sub s (len - patlen) patlen = pat then
    Some (String.sub s 0 (len - patlen))
  else None

let between s pat1 pat2 = match starts s pat1 with
| None -> None
| Some s -> ends s pat2  

let without_sep k sep r =
  if sep <> "" then raise Parsing.Parse_error else k r

let parse_user_entry s sep =
  let table = [
    "ne_", "_list", without_sep (fun r -> Ulist1 r);
    "ne_", "_list_sep", (fun sep r -> Ulist1sep (r, sep));
    "", "_list", without_sep (fun r -> Ulist0 r);
    "", "_list_sep", (fun sep r -> Ulist0sep (r, sep));
    "", "_opt", without_sep (fun r -> Uopt r);
  ] in
  let rec parse s sep = function
  | [] ->
    let () = without_sep ignore sep () in
    begin match starts s "tactic" with
    | Some ("0"|"1"|"2"|"3"|"4"|"5") -> Uentryl ("tactic", int_of_string s)
    | Some _ | None -> Uentry s
    end
  | (pat1, pat2, k) :: rem ->
    match between s pat1 pat2 with
    | None -> parse s sep rem
    | Some s ->
      let r = parse s "" table in
      k sep r      
  in
  parse s sep table

# 89 "coqpp/coqpp_parse.ml"
let yytransl_const = [|
  263 (* VERNAC *);
  264 (* TACTIC *);
  265 (* GRAMMAR *);
  266 (* EXTEND *);
  267 (* END *);
  268 (* DECLARE *);
  269 (* PLUGIN *);
  270 (* DEPRECATED *);
  271 (* LBRACKET *);
  272 (* RBRACKET *);
  273 (* PIPE *);
  274 (* ARROW *);
  275 (* COMMA *);
  276 (* EQUAL *);
  277 (* LPAREN *);
  278 (* RPAREN *);
  279 (* COLON *);
  280 (* SEMICOLON *);
  281 (* GLOBAL *);
  282 (* FIRST *);
  283 (* LAST *);
  284 (* BEFORE *);
  285 (* AFTER *);
  286 (* LEVEL *);
  287 (* LEFTA *);
  288 (* RIGHTA *);
  289 (* NONA *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* CODE *);
  258 (* COMMENT *);
  259 (* IDENT *);
  260 (* QUALID *);
  261 (* STRING *);
  262 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\003\000\003\000\003\000\
\003\000\004\000\005\000\006\000\007\000\011\000\011\000\012\000\
\012\000\013\000\013\000\014\000\015\000\015\000\016\000\016\000\
\016\000\016\000\008\000\008\000\009\000\009\000\017\000\017\000\
\010\000\010\000\018\000\019\000\019\000\021\000\021\000\021\000\
\021\000\021\000\022\000\022\000\023\000\023\000\024\000\024\000\
\024\000\020\000\020\000\025\000\026\000\026\000\027\000\027\000\
\028\000\029\000\029\000\030\000\030\000\031\000\031\000\033\000\
\033\000\033\000\033\000\033\000\032\000\032\000\000\000"

let yylen = "\002\000\
\002\000\000\000\002\000\001\000\001\000\001\000\001\000\001\000\
\001\000\003\000\006\000\004\000\007\000\000\000\002\000\000\000\
\002\000\001\000\002\000\006\000\000\000\002\000\001\000\001\000\
\004\000\006\000\001\000\001\000\000\000\004\000\000\000\002\000\
\000\000\002\000\007\000\000\000\001\000\001\000\001\000\002\000\
\002\000\002\000\000\000\001\000\000\000\001\000\001\000\001\000\
\001\000\001\000\003\000\005\000\000\000\001\000\001\000\003\000\
\003\000\000\000\001\000\001\000\003\000\003\000\001\000\001\000\
\003\000\003\000\003\000\001\000\001\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\004\000\005\000\000\000\000\000\000\000\000\000\
\071\000\000\000\000\000\006\000\007\000\008\000\009\000\000\000\
\000\000\000\000\000\000\001\000\003\000\000\000\000\000\028\000\
\027\000\000\000\010\000\012\000\000\000\000\000\000\000\000\000\
\015\000\000\000\000\000\000\000\000\000\000\000\000\000\017\000\
\000\000\000\000\000\000\000\000\000\000\000\000\011\000\034\000\
\000\000\013\000\019\000\032\000\030\000\038\000\039\000\000\000\
\000\000\000\000\000\000\037\000\000\000\023\000\000\000\000\000\
\040\000\041\000\042\000\000\000\000\000\000\000\022\000\044\000\
\000\000\000\000\000\000\000\000\000\000\000\000\047\000\048\000\
\049\000\000\000\046\000\000\000\000\000\025\000\020\000\035\000\
\000\000\051\000\000\000\000\000\068\000\000\000\000\000\000\000\
\000\000\054\000\000\000\000\000\059\000\000\000\063\000\000\000\
\026\000\000\000\000\000\000\000\000\000\052\000\000\000\000\000\
\000\000\070\000\062\000\067\000\066\000\065\000\056\000\057\000\
\061\000"

let yydgoto = "\002\000\
\009\000\010\000\011\000\012\000\013\000\014\000\015\000\096\000\
\032\000\038\000\030\000\035\000\042\000\043\000\063\000\064\000\
\045\000\039\000\059\000\073\000\060\000\074\000\082\000\083\000\
\075\000\097\000\098\000\099\000\100\000\101\000\102\000\103\000\
\104\000"

let yysindex = "\038\000\
\054\255\000\000\000\000\000\000\031\255\049\255\050\255\044\255\
\000\000\068\000\054\255\000\000\000\000\000\000\000\000\067\255\
\068\255\021\255\073\255\000\000\000\000\071\255\069\255\000\000\
\000\000\059\255\000\000\000\000\084\255\056\255\064\255\021\255\
\000\000\082\255\072\255\021\255\070\255\079\255\021\255\000\000\
\076\255\081\255\072\255\021\255\074\255\047\255\000\000\000\000\
\005\255\000\000\000\000\000\000\000\000\000\000\000\000\089\255\
\090\255\091\255\085\255\000\000\078\255\000\000\086\255\005\255\
\000\000\000\000\000\000\092\255\098\255\087\255\000\000\000\000\
\088\255\048\255\093\255\023\255\102\255\083\255\000\000\000\000\
\000\000\094\255\000\000\092\255\101\255\000\000\000\000\000\000\
\029\255\000\000\095\255\096\255\000\000\029\255\033\255\097\255\
\099\255\000\000\103\255\100\255\000\000\104\255\000\000\033\255\
\000\000\033\255\105\255\107\255\106\255\000\000\029\255\111\255\
\029\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yyrindex = "\000\000\
\108\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\108\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\248\254\000\000\
\000\000\061\255\000\000\000\000\000\000\108\255\000\000\112\255\
\000\000\000\000\000\000\109\255\000\000\000\000\112\255\000\000\
\000\000\000\000\113\255\109\255\000\000\115\255\000\000\000\000\
\110\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\001\255\000\000\000\000\110\255\
\000\000\000\000\000\000\020\255\000\000\000\000\000\000\000\000\
\000\000\116\255\118\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\020\255\000\000\000\000\000\000\000\000\
\254\254\000\000\000\000\253\254\000\000\114\255\000\000\025\255\
\000\000\000\000\119\255\000\000\000\000\120\255\000\000\245\254\
\000\000\000\000\000\000\000\000\000\000\000\000\114\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\102\000\000\000\000\000\000\000\000\000\000\000\243\255\
\000\000\075\000\000\000\000\000\076\000\000\000\058\000\000\000\
\092\000\000\000\000\000\053\000\000\000\000\000\000\000\000\000\
\000\000\000\000\165\255\000\000\000\000\026\000\000\000\219\255\
\000\000"

let yytablesize = 139
let yytable = "\028\000\
\028\000\028\000\107\000\024\000\026\000\024\000\069\000\061\000\
\014\000\062\000\069\000\028\000\069\000\053\000\028\000\058\000\
\024\000\028\000\037\000\119\000\028\000\014\000\044\000\024\000\
\025\000\037\000\028\000\064\000\064\000\064\000\044\000\092\000\
\025\000\093\000\043\000\024\000\025\000\093\000\001\000\064\000\
\016\000\085\000\064\000\094\000\086\000\064\000\064\000\094\000\
\064\000\095\000\043\000\043\000\043\000\095\000\003\000\004\000\
\019\000\108\000\017\000\018\000\005\000\006\000\007\000\029\000\
\029\000\008\000\114\000\020\000\115\000\022\000\023\000\029\000\
\054\000\055\000\056\000\057\000\058\000\027\000\079\000\080\000\
\081\000\028\000\029\000\031\000\033\000\034\000\036\000\040\000\
\041\000\047\000\049\000\050\000\046\000\065\000\066\000\067\000\
\072\000\053\000\069\000\068\000\076\000\070\000\087\000\078\000\
\077\000\091\000\088\000\002\000\089\000\084\000\118\000\120\000\
\021\000\048\000\110\000\106\000\105\000\112\000\051\000\111\000\
\116\000\071\000\033\000\018\000\016\000\021\000\109\000\113\000\
\117\000\036\000\045\000\058\000\031\000\050\000\055\000\052\000\
\090\000\060\000\121\000"

let yycheck = "\003\001\
\004\001\005\001\094\000\003\001\018\000\005\001\018\001\003\001\
\017\001\005\001\022\001\015\001\024\001\016\001\018\001\018\001\
\016\001\021\001\032\000\111\000\024\001\030\001\036\000\003\001\
\004\001\039\000\030\001\003\001\004\001\005\001\044\000\003\001\
\004\001\005\001\015\001\003\001\004\001\005\001\001\000\015\001\
\010\001\019\001\018\001\015\001\022\001\021\001\022\001\015\001\
\024\001\021\001\031\001\032\001\033\001\021\001\001\001\002\001\
\013\001\095\000\010\001\010\001\007\001\008\001\009\001\003\001\
\004\001\012\001\104\000\000\000\106\000\003\001\003\001\011\001\
\026\001\027\001\028\001\029\001\030\001\005\001\031\001\032\001\
\033\001\011\001\014\001\025\001\001\001\030\001\023\001\006\001\
\017\001\011\001\015\001\011\001\023\001\005\001\005\001\005\001\
\005\001\024\001\021\001\015\001\003\001\016\001\001\001\016\001\
\018\001\005\001\024\001\000\000\015\001\017\001\005\001\001\001\
\011\000\039\000\016\001\020\001\022\001\018\001\043\000\017\001\
\016\001\064\000\011\001\011\001\017\001\016\001\030\001\024\001\
\022\001\015\001\015\001\018\001\024\001\016\001\016\001\044\000\
\084\000\018\001\113\000"

let yynames_const = "\
  VERNAC\000\
  TACTIC\000\
  GRAMMAR\000\
  EXTEND\000\
  END\000\
  DECLARE\000\
  PLUGIN\000\
  DEPRECATED\000\
  LBRACKET\000\
  RBRACKET\000\
  PIPE\000\
  ARROW\000\
  COMMA\000\
  EQUAL\000\
  LPAREN\000\
  RPAREN\000\
  COLON\000\
  SEMICOLON\000\
  GLOBAL\000\
  FIRST\000\
  LAST\000\
  BEFORE\000\
  AFTER\000\
  LEVEL\000\
  LEFTA\000\
  RIGHTA\000\
  NONA\000\
  EOF\000\
  "

let yynames_block = "\
  CODE\000\
  COMMENT\000\
  IDENT\000\
  QUALID\000\
  STRING\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'nodes) in
    Obj.repr(
# 78 "coqpp/coqpp_parse.mly"
  ( _1 )
# 308 "coqpp/coqpp_parse.ml"
               : Coqpp_ast.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 83 "coqpp/coqpp_parse.mly"
  ( [] )
# 314 "coqpp/coqpp_parse.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'node) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'nodes) in
    Obj.repr(
# 85 "coqpp/coqpp_parse.mly"
  ( _1 :: _2 )
# 322 "coqpp/coqpp_parse.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Coqpp_ast.code) in
    Obj.repr(
# 89 "coqpp/coqpp_parse.mly"
       ( Code _1 )
# 329 "coqpp/coqpp_parse.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "coqpp/coqpp_parse.mly"
          ( Comment _1 )
# 336 "coqpp/coqpp_parse.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'declare_plugin) in
    Obj.repr(
# 91 "coqpp/coqpp_parse.mly"
                 ( _1 )
# 343 "coqpp/coqpp_parse.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'grammar_extend) in
    Obj.repr(
# 92 "coqpp/coqpp_parse.mly"
                 ( _1 )
# 350 "coqpp/coqpp_parse.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'vernac_extend) in
    Obj.repr(
# 93 "coqpp/coqpp_parse.mly"
                ( _1 )
# 357 "coqpp/coqpp_parse.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tactic_extend) in
    Obj.repr(
# 94 "coqpp/coqpp_parse.mly"
                ( _1 )
# 364 "coqpp/coqpp_parse.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 98 "coqpp/coqpp_parse.mly"
                        ( DeclarePlugin _3 )
# 371 "coqpp/coqpp_parse.ml"
               : 'declare_plugin))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'qualid_or_ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'globals) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'gram_entries) in
    Obj.repr(
# 103 "coqpp/coqpp_parse.mly"
  ( GramExt { gramext_name = _3; gramext_globals = _4; gramext_entries = _5 } )
# 380 "coqpp/coqpp_parse.ml"
               : 'grammar_extend))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 107 "coqpp/coqpp_parse.mly"
                          ( VernacExt )
# 387 "coqpp/coqpp_parse.ml"
               : 'vernac_extend))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'tactic_deprecated) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'tactic_level) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'tactic_rules) in
    Obj.repr(
# 112 "coqpp/coqpp_parse.mly"
  ( TacticExt { tacext_name = _3; tacext_deprecated = _4; tacext_level = _5; tacext_rules = _6 } )
# 397 "coqpp/coqpp_parse.ml"
               : 'tactic_extend))
; (fun __caml_parser_env ->
    Obj.repr(
# 116 "coqpp/coqpp_parse.mly"
  ( None )
# 403 "coqpp/coqpp_parse.ml"
               : 'tactic_deprecated))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Coqpp_ast.code) in
    Obj.repr(
# 117 "coqpp/coqpp_parse.mly"
                  ( Some _2 )
# 410 "coqpp/coqpp_parse.ml"
               : 'tactic_deprecated))
; (fun __caml_parser_env ->
    Obj.repr(
# 121 "coqpp/coqpp_parse.mly"
  ( None )
# 416 "coqpp/coqpp_parse.ml"
               : 'tactic_level))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 122 "coqpp/coqpp_parse.mly"
            ( Some _2 )
# 423 "coqpp/coqpp_parse.ml"
               : 'tactic_level))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tactic_rule) in
    Obj.repr(
# 126 "coqpp/coqpp_parse.mly"
              ( [_1] )
# 430 "coqpp/coqpp_parse.ml"
               : 'tactic_rules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'tactic_rule) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'tactic_rules) in
    Obj.repr(
# 127 "coqpp/coqpp_parse.mly"
                           ( _1 :: _2 )
# 438 "coqpp/coqpp_parse.ml"
               : 'tactic_rules))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'ext_tokens) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Coqpp_ast.code) in
    Obj.repr(
# 132 "coqpp/coqpp_parse.mly"
  ( { tac_toks = _3; tac_body = _6 } )
# 446 "coqpp/coqpp_parse.ml"
               : 'tactic_rule))
; (fun __caml_parser_env ->
    Obj.repr(
# 136 "coqpp/coqpp_parse.mly"
  ( [] )
# 452 "coqpp/coqpp_parse.ml"
               : 'ext_tokens))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ext_token) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ext_tokens) in
    Obj.repr(
# 137 "coqpp/coqpp_parse.mly"
                       ( _1 :: _2 )
# 460 "coqpp/coqpp_parse.ml"
               : 'ext_tokens))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 141 "coqpp/coqpp_parse.mly"
         ( ExtTerminal _1 )
# 467 "coqpp/coqpp_parse.ml"
               : 'ext_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 142 "coqpp/coqpp_parse.mly"
        (
  let e = parse_user_entry _1 "" in
  ExtNonTerminal (e, TokNone) 
  )
# 477 "coqpp/coqpp_parse.ml"
               : 'ext_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 146 "coqpp/coqpp_parse.mly"
                            (
  let e = parse_user_entry _1 "" in
  ExtNonTerminal (e, TokName _3)
  )
# 488 "coqpp/coqpp_parse.ml"
               : 'ext_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 150 "coqpp/coqpp_parse.mly"
                                         (
  let e = parse_user_entry _1 _5 in
  ExtNonTerminal (e, TokName _3)
)
# 500 "coqpp/coqpp_parse.ml"
               : 'ext_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 157 "coqpp/coqpp_parse.mly"
         ( _1 )
# 507 "coqpp/coqpp_parse.ml"
               : 'qualid_or_ident))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 158 "coqpp/coqpp_parse.mly"
        ( _1 )
# 514 "coqpp/coqpp_parse.ml"
               : 'qualid_or_ident))
; (fun __caml_parser_env ->
    Obj.repr(
# 162 "coqpp/coqpp_parse.mly"
  ( [] )
# 520 "coqpp/coqpp_parse.ml"
               : 'globals))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'idents) in
    Obj.repr(
# 163 "coqpp/coqpp_parse.mly"
                                ( _3 )
# 527 "coqpp/coqpp_parse.ml"
               : 'globals))
; (fun __caml_parser_env ->
    Obj.repr(
# 167 "coqpp/coqpp_parse.mly"
  ( [] )
# 533 "coqpp/coqpp_parse.ml"
               : 'idents))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'qualid_or_ident) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'idents) in
    Obj.repr(
# 168 "coqpp/coqpp_parse.mly"
                         ( _1 :: _2 )
# 541 "coqpp/coqpp_parse.ml"
               : 'idents))
; (fun __caml_parser_env ->
    Obj.repr(
# 172 "coqpp/coqpp_parse.mly"
  ( [] )
# 547 "coqpp/coqpp_parse.ml"
               : 'gram_entries))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'gram_entry) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'gram_entries) in
    Obj.repr(
# 173 "coqpp/coqpp_parse.mly"
                          ( _1 :: _2 )
# 555 "coqpp/coqpp_parse.ml"
               : 'gram_entries))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'qualid_or_ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'position_opt) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'levels) in
    Obj.repr(
# 178 "coqpp/coqpp_parse.mly"
  ( { gentry_name = _1; gentry_pos = _3; gentry_rules = _5; } )
# 564 "coqpp/coqpp_parse.ml"
               : 'gram_entry))
; (fun __caml_parser_env ->
    Obj.repr(
# 182 "coqpp/coqpp_parse.mly"
  ( None )
# 570 "coqpp/coqpp_parse.ml"
               : 'position_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'position) in
    Obj.repr(
# 183 "coqpp/coqpp_parse.mly"
           ( Some _1 )
# 577 "coqpp/coqpp_parse.ml"
               : 'position_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 187 "coqpp/coqpp_parse.mly"
        ( First )
# 583 "coqpp/coqpp_parse.ml"
               : 'position))
; (fun __caml_parser_env ->
    Obj.repr(
# 188 "coqpp/coqpp_parse.mly"
       ( Last )
# 589 "coqpp/coqpp_parse.ml"
               : 'position))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 189 "coqpp/coqpp_parse.mly"
                ( Before _2 )
# 596 "coqpp/coqpp_parse.ml"
               : 'position))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 190 "coqpp/coqpp_parse.mly"
               ( After _2 )
# 603 "coqpp/coqpp_parse.ml"
               : 'position))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 191 "coqpp/coqpp_parse.mly"
               ( Level _2 )
# 610 "coqpp/coqpp_parse.ml"
               : 'position))
; (fun __caml_parser_env ->
    Obj.repr(
# 195 "coqpp/coqpp_parse.mly"
  ( None )
# 616 "coqpp/coqpp_parse.ml"
               : 'string_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 196 "coqpp/coqpp_parse.mly"
         ( Some _1 )
# 623 "coqpp/coqpp_parse.ml"
               : 'string_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 200 "coqpp/coqpp_parse.mly"
  ( None )
# 629 "coqpp/coqpp_parse.ml"
               : 'assoc_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'assoc) in
    Obj.repr(
# 201 "coqpp/coqpp_parse.mly"
        ( Some _1 )
# 636 "coqpp/coqpp_parse.ml"
               : 'assoc_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 205 "coqpp/coqpp_parse.mly"
        ( LeftA )
# 642 "coqpp/coqpp_parse.ml"
               : 'assoc))
; (fun __caml_parser_env ->
    Obj.repr(
# 206 "coqpp/coqpp_parse.mly"
         ( RightA )
# 648 "coqpp/coqpp_parse.ml"
               : 'assoc))
; (fun __caml_parser_env ->
    Obj.repr(
# 207 "coqpp/coqpp_parse.mly"
       ( NonA )
# 654 "coqpp/coqpp_parse.ml"
               : 'assoc))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'level) in
    Obj.repr(
# 211 "coqpp/coqpp_parse.mly"
        ( [_1] )
# 661 "coqpp/coqpp_parse.ml"
               : 'levels))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'level) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'levels) in
    Obj.repr(
# 212 "coqpp/coqpp_parse.mly"
                    ( _1 :: _3 )
# 669 "coqpp/coqpp_parse.ml"
               : 'levels))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'string_opt) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'assoc_opt) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'rules_opt) in
    Obj.repr(
# 217 "coqpp/coqpp_parse.mly"
  ( { grule_label = _1; grule_assoc = _2; grule_prods = _4; } )
# 678 "coqpp/coqpp_parse.ml"
               : 'level))
; (fun __caml_parser_env ->
    Obj.repr(
# 221 "coqpp/coqpp_parse.mly"
  ( [] )
# 684 "coqpp/coqpp_parse.ml"
               : 'rules_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rules) in
    Obj.repr(
# 222 "coqpp/coqpp_parse.mly"
        ( _1 )
# 691 "coqpp/coqpp_parse.ml"
               : 'rules_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rule) in
    Obj.repr(
# 226 "coqpp/coqpp_parse.mly"
       ( [_1] )
# 698 "coqpp/coqpp_parse.ml"
               : 'rules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rule) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'rules) in
    Obj.repr(
# 227 "coqpp/coqpp_parse.mly"
                  ( _1 :: _3 )
# 706 "coqpp/coqpp_parse.ml"
               : 'rules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'symbols_opt) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Coqpp_ast.code) in
    Obj.repr(
# 232 "coqpp/coqpp_parse.mly"
  ( { gprod_symbs = _1; gprod_body = _3; } )
# 714 "coqpp/coqpp_parse.ml"
               : 'rule))
; (fun __caml_parser_env ->
    Obj.repr(
# 236 "coqpp/coqpp_parse.mly"
  ( [] )
# 720 "coqpp/coqpp_parse.ml"
               : 'symbols_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'symbols) in
    Obj.repr(
# 237 "coqpp/coqpp_parse.mly"
          ( _1 )
# 727 "coqpp/coqpp_parse.ml"
               : 'symbols_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'symbol) in
    Obj.repr(
# 241 "coqpp/coqpp_parse.mly"
         ( [_1] )
# 734 "coqpp/coqpp_parse.ml"
               : 'symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'symbol) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'symbols) in
    Obj.repr(
# 242 "coqpp/coqpp_parse.mly"
                           ( _1 :: _3 )
# 742 "coqpp/coqpp_parse.ml"
               : 'symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'gram_tokens) in
    Obj.repr(
# 246 "coqpp/coqpp_parse.mly"
                          ( (Some _1, _3) )
# 750 "coqpp/coqpp_parse.ml"
               : 'symbol))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'gram_tokens) in
    Obj.repr(
# 247 "coqpp/coqpp_parse.mly"
              ( (None, _1) )
# 757 "coqpp/coqpp_parse.ml"
               : 'symbol))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'qualid_or_ident) in
    Obj.repr(
# 251 "coqpp/coqpp_parse.mly"
                  ( GSymbQualid (_1, None) )
# 764 "coqpp/coqpp_parse.ml"
               : 'gram_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'qualid_or_ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 252 "coqpp/coqpp_parse.mly"
                               ( GSymbQualid (_1, Some _3) )
# 772 "coqpp/coqpp_parse.ml"
               : 'gram_token))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'gram_tokens) in
    Obj.repr(
# 253 "coqpp/coqpp_parse.mly"
                            ( GSymbParen _2 )
# 779 "coqpp/coqpp_parse.ml"
               : 'gram_token))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'rules) in
    Obj.repr(
# 254 "coqpp/coqpp_parse.mly"
                          ( GSymbProd _2 )
# 786 "coqpp/coqpp_parse.ml"
               : 'gram_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 255 "coqpp/coqpp_parse.mly"
         ( GSymbString _1 )
# 793 "coqpp/coqpp_parse.ml"
               : 'gram_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'gram_token) in
    Obj.repr(
# 259 "coqpp/coqpp_parse.mly"
             ( [_1] )
# 800 "coqpp/coqpp_parse.ml"
               : 'gram_tokens))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'gram_token) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'gram_tokens) in
    Obj.repr(
# 260 "coqpp/coqpp_parse.mly"
                         ( _1 :: _2 )
# 808 "coqpp/coqpp_parse.ml"
               : 'gram_tokens))
(* Entry file *)
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
let file (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Coqpp_ast.t)
