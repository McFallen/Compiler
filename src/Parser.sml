local
in
datatype token =
    AND
  | DOT
  | EOF
  | EXIST
  | FALSE
  | FORALL
  | IMP
  | LPAR
  | NOT
  | OR
  | RPAR
  | TRUE
  | VAR of string
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";


open FEIEF;

(* Line 9, file Parser.sml *)
val yytransl = #[
  257 (* AND *),
  258 (* DOT *),
  259 (* EOF *),
  260 (* EXIST *),
  261 (* FALSE *),
  262 (* FORALL *),
  263 (* IMP *),
  264 (* LPAR *),
  265 (* NOT *),
  266 (* OR *),
  267 (* RPAR *),
  268 (* TRUE *),
  269 (* VAR *),
    0];

val yylhs = "\255\255\
\\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\\002\000\002\000\002\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\003\000\003\000\002\000\004\000\004\000\003\000\
\\001\000\001\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\010\000\000\000\000\000\000\000\011\000\
\\009\000\012\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\001\000\000\000\000\000\000\000\000\000\008\000\000\000\000\000\
\\000\000\000\000\000\000";

val yydgoto = "\002\000\
\\010\000\011\000";

val yysindex = "\002\000\
\\044\255\000\000\248\254\000\000\249\254\044\255\044\255\000\000\
\\000\000\000\000\001\255\005\255\022\255\036\255\000\000\044\255\
\\000\000\044\255\044\255\044\255\044\255\000\000\000\000\053\255\
\\000\000\053\255\053\255";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\015\255\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\020\255\006\255\
\\031\255\017\255\033\255";

val yygindex = "\000\000\
\\000\000\250\255";

val YYTABLESIZE = 63;
val yytable = "\014\000\
\\015\000\016\000\001\000\017\000\012\000\013\000\020\000\018\000\
\\004\000\023\000\019\000\024\000\025\000\026\000\027\000\005\000\
\\004\000\005\000\000\000\007\000\003\000\005\000\003\000\021\000\
\\005\000\005\000\003\000\007\000\000\000\003\000\003\000\002\000\
\\000\000\002\000\000\000\006\000\016\000\002\000\000\000\000\000\
\\002\000\002\000\018\000\006\000\000\000\019\000\022\000\003\000\
\\004\000\005\000\000\000\006\000\007\000\016\000\000\000\008\000\
\\009\000\000\000\000\000\018\000\000\000\000\000\019\000";

val yycheck = "\006\000\
\\007\000\001\001\001\000\003\001\013\001\013\001\002\001\007\001\
\\003\001\016\000\010\001\018\000\019\000\020\000\021\000\001\001\
\\011\001\003\001\255\255\003\001\001\001\007\001\003\001\002\001\
\\010\001\011\001\007\001\011\001\255\255\010\001\011\001\001\001\
\\255\255\003\001\255\255\003\001\001\001\007\001\255\255\255\255\
\\010\001\011\001\007\001\011\001\255\255\010\001\011\001\004\001\
\\005\001\006\001\255\255\008\001\009\001\001\001\255\255\012\001\
\\013\001\255\255\255\255\007\001\255\255\255\255\010\001";

val yyact = vector_ 13 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 23 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : FEIEF.Expr
in
( (d__1__) ) end : FEIEF.Expr))
;
(* Rule 2, file Parser.grm, line 26 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : FEIEF.Expr
val d__3__ = peekVal 0 : FEIEF.Expr
in
( Or( (d__1__), (d__3__) ) ) end : FEIEF.Expr))
;
(* Rule 3, file Parser.grm, line 27 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 2 : FEIEF.Expr
val d__3__ = peekVal 0 : FEIEF.Expr
in
( And( (d__1__), (d__3__) ) ) end : FEIEF.Expr))
;
(* Rule 4, file Parser.grm, line 28 *)
val _ = update_ yyact 4
(fn () => repr(let
val d__1__ = peekVal 2 : FEIEF.Expr
val d__3__ = peekVal 0 : FEIEF.Expr
in
( Implies( (d__1__), (d__3__) ) ) end : FEIEF.Expr))
;
(* Rule 5, file Parser.grm, line 29 *)
val _ = update_ yyact 5
(fn () => repr(let
val d__2__ = peekVal 0 : FEIEF.Expr
in
( Not( (d__2__) ) ) end : FEIEF.Expr))
;
(* Rule 6, file Parser.grm, line 30 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__2__ = peekVal 2 : string
val d__4__ = peekVal 0 : FEIEF.Expr
in
( Forall( (d__2__), (d__4__) ) ) end : FEIEF.Expr))
;
(* Rule 7, file Parser.grm, line 31 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__2__ = peekVal 2 : string
val d__4__ = peekVal 0 : FEIEF.Expr
in
( Exists( (d__2__), (d__4__) ) ) end : FEIEF.Expr))
;
(* Rule 8, file Parser.grm, line 32 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__2__ = peekVal 1 : FEIEF.Expr
in
( (d__2__) ) end : FEIEF.Expr))
;
(* Rule 9, file Parser.grm, line 33 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 0 : string
in
( Var( (d__1__) ) ) end : FEIEF.Expr))
;
(* Rule 10, file Parser.grm, line 34 *)
val _ = update_ yyact 10
(fn () => repr(let
in
( False ) end : FEIEF.Expr))
;
(* Rule 11, file Parser.grm, line 35 *)
val _ = update_ yyact 11
(fn () => repr(let
in
( True ) end : FEIEF.Expr))
;
(* Entry Prog *)
val _ = update_ yyact 12 (fn () => raise yyexit (peekVal 0));
val yytables : parseTables =
  ( yyact,
    yytransl,
    yylhs,
    yylen,
    yydefred,
    yydgoto,
    yysindex,
    yyrindex,
    yygindex,
    YYTABLESIZE,
    yytable,
    yycheck );
fun Prog lexer lexbuf = yyparse yytables 1 lexer lexbuf;
