type token =
  | NUM of (int)
  | STR of (string)
  | ID of (string)
  | INT
  | IF
  | WHILE
  | SPRINT
  | IPRINT
  | SCAN
  | EQ
  | NEQ
  | GT
  | LT
  | GE
  | LE
  | ELSE
  | RETURN
  | NEW
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | MOD
  | LB
  | RB
  | LS
  | RS
  | LP
  | RP
  | ASSIGN
  | SEMI
  | COMMA
  | TYPE
  | VOID

open Parsing;;
let _ = parse_error;;
# 3 "parser.mly"
  open Printf
  open Ast
# 43 "parser.ml"
let yytransl_const = [|
  260 (* INT *);
  261 (* IF *);
  262 (* WHILE *);
  263 (* SPRINT *);
  264 (* IPRINT *);
  265 (* SCAN *);
  266 (* EQ *);
  267 (* NEQ *);
  268 (* GT *);
  269 (* LT *);
  270 (* GE *);
  271 (* LE *);
  272 (* ELSE *);
  273 (* RETURN *);
  274 (* NEW *);
  275 (* PLUS *);
  276 (* MINUS *);
  277 (* TIMES *);
  278 (* DIV *);
  279 (* MOD *);
  280 (* LB *);
  281 (* RB *);
  282 (* LS *);
  283 (* RS *);
  284 (* LP *);
  285 (* RP *);
  286 (* ASSIGN *);
  287 (* SEMI *);
  288 (* COMMA *);
  289 (* TYPE *);
  290 (* VOID *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* STR *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\003\000\003\000\003\000\004\000\004\000\005\000\005\000\
\005\000\005\000\006\000\006\000\007\000\007\000\009\000\009\000\
\010\000\010\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\013\000\013\000\014\000\014\000\008\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\012\000\012\000\012\000\012\000\012\000\012\000\000\000"

let yylen = "\002\000\
\001\000\001\000\004\000\001\000\002\000\000\000\003\000\005\000\
\006\000\006\000\003\000\001\000\000\000\001\000\004\000\002\000\
\002\000\001\000\004\000\007\000\005\000\007\000\005\000\005\000\
\005\000\005\000\005\000\005\000\003\000\001\000\001\000\002\000\
\000\000\001\000\003\000\001\000\004\000\001\000\001\000\004\000\
\004\000\003\000\003\000\003\000\003\000\003\000\002\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\006\000\031\000\055\000\001\000\030\000\
\032\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\038\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\029\000\000\000\000\000\000\000\
\000\000\000\000\018\000\000\000\005\000\000\000\000\000\000\000\
\000\000\019\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\048\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\037\000\017\000\000\000\028\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\023\000\
\024\000\025\000\026\000\041\000\040\000\027\000\000\000\000\000\
\000\000\000\000\007\000\000\000\000\000\000\000\003\000\004\000\
\000\000\000\000\000\000\000\000\000\000\011\000\020\000\022\000\
\008\000\016\000\000\000\000\000\000\000\010\000\000\000\009\000\
\015\000"

let yydgoto = "\002\000\
\014\000\015\000\122\000\032\000\061\000\091\000\123\000\016\000\
\124\000\062\000\034\000\039\000\035\000\036\000"

let yysindex = "\015\000\
\105\255\000\000\245\254\033\255\006\255\014\255\045\255\051\255\
\054\255\032\255\069\255\000\000\000\000\000\000\000\000\000\000\
\000\000\032\255\032\255\032\255\032\255\032\255\097\255\032\255\
\068\255\000\000\234\254\032\255\032\255\096\255\095\255\005\255\
\035\000\053\000\072\255\074\255\214\255\025\000\075\255\091\255\
\092\255\232\255\099\255\032\255\032\255\084\255\030\000\032\255\
\032\255\032\255\032\255\032\255\000\000\108\255\033\255\098\255\
\122\255\123\255\000\000\135\255\000\000\078\255\114\255\115\255\
\032\255\000\000\032\255\032\255\032\255\032\255\032\255\032\255\
\105\255\105\255\117\255\119\255\128\255\044\000\116\255\000\000\
\071\255\071\255\084\255\084\255\053\000\129\255\160\255\136\255\
\139\255\140\255\019\255\000\000\000\000\032\255\000\000\053\000\
\053\000\053\000\053\000\053\000\053\000\053\000\155\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\142\255\073\255\
\073\255\073\255\000\000\170\255\227\255\105\255\000\000\000\000\
\151\255\180\255\161\255\152\255\162\255\000\000\000\000\000\000\
\000\000\000\000\165\255\073\255\165\255\000\000\191\255\000\000\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\163\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\120\255\000\000\000\000\000\000\000\000\000\000\
\000\000\251\254\000\000\167\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\163\255\143\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\202\255\000\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\212\255\002\000\166\255\189\255\043\255\000\000\000\000\000\000\
\000\000\058\255\000\000\000\000\000\000\000\000\000\000\008\255\
\177\255\178\255\183\255\184\255\185\255\186\255\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\188\255\188\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\190\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\226\255\224\255\000\000\000\000\000\000\114\000\153\255\
\000\000\000\000\253\255\207\000\185\000\000\000"

let yytablesize = 332
let yytable = "\060\000\
\021\000\059\000\002\000\044\000\003\000\045\000\030\000\055\000\
\056\000\005\000\006\000\007\000\008\000\009\000\033\000\001\000\
\037\000\038\000\038\000\017\000\042\000\010\000\011\000\036\000\
\046\000\047\000\036\000\134\000\012\000\136\000\002\000\093\000\
\026\000\021\000\027\000\013\000\035\000\057\000\058\000\035\000\
\078\000\022\000\103\000\104\000\081\000\082\000\083\000\084\000\
\085\000\115\000\116\000\028\000\046\000\046\000\046\000\046\000\
\046\000\046\000\018\000\029\000\019\000\096\000\020\000\097\000\
\098\000\099\000\100\000\101\000\102\000\046\000\043\000\046\000\
\023\000\046\000\046\000\120\000\056\000\003\000\024\000\121\000\
\004\000\025\000\005\000\006\000\007\000\008\000\009\000\128\000\
\012\000\012\000\117\000\050\000\051\000\052\000\010\000\011\000\
\031\000\054\000\041\000\135\000\064\000\012\000\092\000\073\000\
\003\000\065\000\052\000\004\000\013\000\005\000\006\000\007\000\
\008\000\009\000\048\000\049\000\050\000\051\000\052\000\074\000\
\075\000\010\000\011\000\087\000\088\000\089\000\053\000\077\000\
\012\000\039\000\039\000\039\000\039\000\039\000\039\000\013\000\
\086\000\090\000\039\000\039\000\039\000\039\000\039\000\094\000\
\109\000\095\000\039\000\105\000\039\000\106\000\039\000\039\000\
\047\000\047\000\047\000\047\000\047\000\047\000\107\000\110\000\
\111\000\047\000\047\000\047\000\047\000\112\000\113\000\114\000\
\119\000\047\000\118\000\047\000\126\000\047\000\047\000\044\000\
\044\000\044\000\044\000\044\000\044\000\129\000\130\000\132\000\
\044\000\044\000\044\000\044\000\012\000\131\000\133\000\033\000\
\044\000\137\000\044\000\034\000\044\000\044\000\045\000\045\000\
\045\000\045\000\045\000\045\000\004\000\049\000\050\000\045\000\
\045\000\045\000\045\000\051\000\052\000\053\000\054\000\045\000\
\013\000\045\000\014\000\045\000\045\000\042\000\042\000\042\000\
\042\000\042\000\042\000\125\000\040\000\079\000\042\000\042\000\
\048\000\049\000\050\000\051\000\052\000\000\000\042\000\000\000\
\042\000\000\000\042\000\042\000\066\000\048\000\049\000\050\000\
\051\000\052\000\048\000\049\000\050\000\051\000\052\000\000\000\
\021\000\127\000\000\000\021\000\076\000\021\000\021\000\021\000\
\021\000\021\000\000\000\043\000\043\000\043\000\043\000\043\000\
\043\000\021\000\021\000\000\000\043\000\043\000\000\000\000\000\
\021\000\021\000\000\000\000\000\043\000\000\000\043\000\021\000\
\043\000\043\000\067\000\068\000\069\000\070\000\071\000\072\000\
\000\000\000\000\000\000\048\000\049\000\050\000\051\000\052\000\
\048\000\049\000\050\000\051\000\052\000\048\000\049\000\050\000\
\051\000\052\000\080\000\000\000\000\000\063\000\048\000\049\000\
\050\000\051\000\052\000\000\000\000\000\000\000\108\000\048\000\
\049\000\050\000\051\000\052\000"

let yycheck = "\032\000\
\000\000\032\000\003\001\026\001\000\001\028\001\010\000\003\001\
\004\001\005\001\006\001\007\001\008\001\009\001\018\000\001\000\
\020\000\021\000\022\000\031\001\024\000\017\001\018\001\029\001\
\028\000\029\000\032\001\131\000\024\001\133\000\031\001\062\000\
\001\001\028\001\003\001\031\001\029\001\033\001\034\001\032\001\
\044\000\028\001\073\000\074\000\048\000\049\000\050\000\051\000\
\052\000\031\001\032\001\020\001\010\001\011\001\012\001\013\001\
\014\001\015\001\026\001\028\001\028\001\065\000\030\001\067\000\
\068\000\069\000\070\000\071\000\072\000\027\001\003\001\029\001\
\028\001\031\001\032\001\003\001\004\001\000\001\028\001\112\000\
\003\001\028\001\005\001\006\001\007\001\008\001\009\001\118\000\
\031\001\032\001\094\000\021\001\022\001\023\001\017\001\018\001\
\028\001\003\001\002\001\132\000\029\001\024\001\025\001\029\001\
\000\001\032\001\023\001\003\001\031\001\005\001\006\001\007\001\
\008\001\009\001\019\001\020\001\021\001\022\001\023\001\029\001\
\029\001\017\001\018\001\026\001\003\001\003\001\031\001\029\001\
\024\001\010\001\011\001\012\001\013\001\014\001\015\001\031\001\
\029\001\003\001\019\001\020\001\021\001\022\001\023\001\030\001\
\029\001\031\001\027\001\031\001\029\001\031\001\031\001\032\001\
\010\001\011\001\012\001\013\001\014\001\015\001\031\001\031\001\
\001\001\019\001\020\001\021\001\022\001\030\001\028\001\028\001\
\027\001\027\001\016\001\029\001\003\001\031\001\032\001\010\001\
\011\001\012\001\013\001\014\001\015\001\031\001\003\001\032\001\
\019\001\020\001\021\001\022\001\024\001\029\001\029\001\029\001\
\027\001\003\001\029\001\029\001\031\001\032\001\010\001\011\001\
\012\001\013\001\014\001\015\001\003\001\029\001\029\001\019\001\
\020\001\021\001\022\001\029\001\029\001\029\001\029\001\027\001\
\029\001\029\001\029\001\031\001\032\001\010\001\011\001\012\001\
\013\001\014\001\015\001\114\000\022\000\045\000\019\001\020\001\
\019\001\020\001\021\001\022\001\023\001\255\255\027\001\255\255\
\029\001\255\255\031\001\032\001\031\001\019\001\020\001\021\001\
\022\001\023\001\019\001\020\001\021\001\022\001\023\001\255\255\
\000\001\031\001\255\255\003\001\029\001\005\001\006\001\007\001\
\008\001\009\001\255\255\010\001\011\001\012\001\013\001\014\001\
\015\001\017\001\018\001\255\255\019\001\020\001\255\255\255\255\
\024\001\025\001\255\255\255\255\027\001\255\255\029\001\031\001\
\031\001\032\001\010\001\011\001\012\001\013\001\014\001\015\001\
\255\255\255\255\255\255\019\001\020\001\021\001\022\001\023\001\
\019\001\020\001\021\001\022\001\023\001\019\001\020\001\021\001\
\022\001\023\001\029\001\255\255\255\255\027\001\019\001\020\001\
\021\001\022\001\023\001\255\255\255\255\255\255\027\001\019\001\
\020\001\021\001\022\001\023\001"

let yynames_const = "\
  INT\000\
  IF\000\
  WHILE\000\
  SPRINT\000\
  IPRINT\000\
  SCAN\000\
  EQ\000\
  NEQ\000\
  GT\000\
  LT\000\
  GE\000\
  LE\000\
  ELSE\000\
  RETURN\000\
  NEW\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  MOD\000\
  LB\000\
  RB\000\
  LS\000\
  RS\000\
  LP\000\
  RP\000\
  ASSIGN\000\
  SEMI\000\
  COMMA\000\
  TYPE\000\
  VOID\000\
  "

let yynames_block = "\
  NUM\000\
  STR\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 27 "parser.mly"
       ( _1 )
# 306 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 31 "parser.mly"
                     ( IntTyp )
# 312 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 32 "parser.mly"
                     ( ArrayTyp (_3, IntTyp) )
# 319 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 33 "parser.mly"
                     ( NameTyp _1 )
# 326 "parser.ml"
               : 'ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'dec) in
    Obj.repr(
# 37 "parser.mly"
                     ( _1 @ _2 )
# 334 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    Obj.repr(
# 38 "parser.mly"
                     ( [] )
# 340 "parser.ml"
               : 'decs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'ids) in
    Obj.repr(
# 42 "parser.mly"
                     ( List.map (fun x -> VarDec (_1, x)) _2 )
# 348 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    Obj.repr(
# 44 "parser.mly"
                     ( [TypeDec (_2, _4)] )
# 356 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 46 "parser.mly"
                     ( [FuncDec(_2, _4, _1, _6)] )
# 366 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fargs_opt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 48 "parser.mly"
                     ( [FuncDec(_2, _4, VoidTyp, _6)] )
# 375 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 52 "parser.mly"
                     ( _1 @ [_3] )
# 383 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 53 "parser.mly"
                     ( [_1] )
# 390 "parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    Obj.repr(
# 57 "parser.mly"
                     ( [] )
# 396 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'fargs) in
    Obj.repr(
# 58 "parser.mly"
                     ( _1 )
# 403 "parser.ml"
               : 'fargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'fargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 62 "parser.mly"
                     ( _1 @ [(_3, _4)] )
# 412 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 63 "parser.mly"
                     ( [(_1, _2)] )
# 420 "parser.ml"
               : 'fargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 67 "parser.mly"
                     ( _1 @ [_2] )
# 428 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 68 "parser.mly"
                     ( [_1] )
# 435 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 73 "parser.mly"
                     ( Assign (Var _1, _3) )
# 443 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 75 "parser.mly"
                     ( Assign (IndexedVar (Var _1, _3), _6) )
# 452 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 77 "parser.mly"
                     ( If (_3, _5, None) )
# 460 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 79 "parser.mly"
                     ( If (_3, _5, Some _7) )
# 469 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'cond) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 81 "parser.mly"
                     ( While (_3, _5) )
# 477 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 83 "parser.mly"
                     ( CallProc ("sprint", [StrExp _3]) )
# 484 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
                     ( CallProc ("iprint", [_3]) )
# 491 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 87 "parser.mly"
                     ( CallProc ("scan", [VarExp (Var _3)]) )
# 498 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 89 "parser.mly"
                     ( CallProc ("new", [VarExp (Var _3)]) )
# 505 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aargs_opt) in
    Obj.repr(
# 91 "parser.mly"
                     ( CallProc (_1, _3) )
# 513 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                     ( CallProc ("return", [_2]) )
# 520 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 94 "parser.mly"
                     ( _1 )
# 527 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 95 "parser.mly"
                     ( NilStmt )
# 533 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 96 "parser.mly"
                     (printf "Error detected, skipping to next statement.\n"; NilStmt)
# 539 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 100 "parser.mly"
                     ( [] )
# 545 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aargs) in
    Obj.repr(
# 101 "parser.mly"
                     ( _1 )
# 552 "parser.ml"
               : 'aargs_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aargs) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                     ( _1 @ [_3] )
# 560 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( [_1] )
# 567 "parser.ml"
               : 'aargs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'decs) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 110 "parser.mly"
                     ( Block (_2, _3) )
# 575 "parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 114 "parser.mly"
                     ( IntExp _1 )
# 582 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 115 "parser.mly"
                     ( VarExp (Var _1) )
# 589 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'aargs_opt) in
    Obj.repr(
# 116 "parser.mly"
                     ( CallFunc (_1, _3) )
# 597 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 117 "parser.mly"
                     ( VarExp (IndexedVar (Var _1, _3)) )
# 605 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                     ( CallFunc ("+", [_1; _3]) )
# 613 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 119 "parser.mly"
                     ( CallFunc ("-", [_1; _3]) )
# 621 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 120 "parser.mly"
                     ( CallFunc ("*", [_1; _3]) )
# 629 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 121 "parser.mly"
                     ( CallFunc ("/", [_1; _3]) )
# 637 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 122 "parser.mly"
                     ( CallFunc ("%", [_1; _3]) )
# 645 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 124 "parser.mly"
                     ( CallFunc("!", [_2]) )
# 652 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 125 "parser.mly"
                     ( _2 )
# 659 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 129 "parser.mly"
                     ( CallFunc ("==", [_1; _3]) )
# 667 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 130 "parser.mly"
                     ( CallFunc ("!=", [_1; _3]) )
# 675 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 131 "parser.mly"
                     ( CallFunc (">", [_1; _3]) )
# 683 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 132 "parser.mly"
                     ( CallFunc ("<", [_1; _3]) )
# 691 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 133 "parser.mly"
                     ( CallFunc (">=", [_1; _3]) )
# 699 "parser.ml"
               : 'cond))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 134 "parser.mly"
                     ( CallFunc ("<=", [_1; _3]) )
# 707 "parser.ml"
               : 'cond))
(* Entry prog *)
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
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.stmt)
