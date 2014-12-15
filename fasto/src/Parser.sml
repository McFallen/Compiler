local
type t__1__ = (int*int)
type t__2__ = (int*int)
type t__3__ = (int*int)
type t__4__ = (int*int)
type t__5__ = char*(int*int)
type t__6__ = (int*int)
type t__7__ = (int*int)
type t__8__ = (int*int)
type t__9__ = (int*int)
type t__10__ = (int*int)
type t__11__ = (int*int)
type t__12__ = bool*(int*int)
type t__13__ = (int*int)
type t__14__ = (int*int)
type t__15__ = (int*int)
type t__16__ = string*(int*int)
type t__17__ = (int*int)
type t__18__ = (int*int)
type t__19__ = (int*int)
type t__20__ = (int*int)
type t__21__ = (int*int)
type t__22__ = (int*int)
type t__23__ = (int*int)
type t__24__ = (int*int)
type t__25__ = (int*int)
type t__26__ = (int*int)
type t__27__ = (int*int)
type t__28__ = (int*int)
type t__29__ = (int*int)
type t__30__ = (int*int)
type t__31__ = int*(int*int)
type t__32__ = (int*int)
type t__33__ = (int*int)
type t__34__ = (int*int)
type t__35__ = (int*int)
type t__36__ = (int*int)
type t__37__ = (int*int)
type t__38__ = (int*int)
type t__39__ = (int*int)
type t__40__ = (int*int)
type t__41__ = (int*int)
type t__42__ = string*(int*int)
type t__43__ = (int*int)
type t__44__ = (int*int)
type t__45__ = bool*(int*int)
type t__46__ = (int*int)
in
datatype token =
    AND of t__1__
  | ARROW of t__2__
  | BOOL of t__3__
  | CHAR of t__4__
  | CHARLIT of t__5__
  | COMMA of t__6__
  | DEQ of t__7__
  | DIV of t__8__
  | ELSE of t__9__
  | EOF of t__10__
  | EQ of t__11__
  | FALSE of t__12__
  | FILTER of t__13__
  | FN of t__14__
  | FUN of t__15__
  | ID of t__16__
  | IF of t__17__
  | IN of t__18__
  | INT of t__19__
  | IOTA of t__20__
  | LAMBDA of t__21__
  | LBRACKET of t__22__
  | LCURLY of t__23__
  | LET of t__24__
  | LPAR of t__25__
  | LTH of t__26__
  | MAP of t__27__
  | MINUS of t__28__
  | NEG of t__29__
  | NOT of t__30__
  | NUM of t__31__
  | OP of t__32__
  | OR of t__33__
  | PLUS of t__34__
  | RBRACKET of t__35__
  | RCURLY of t__36__
  | READ of t__37__
  | REDUCE of t__38__
  | REPLICATE of t__39__
  | RPAR of t__40__
  | SCAN of t__41__
  | STRINGLIT of t__42__
  | THEN of t__43__
  | TIMES of t__44__
  | TRUE of t__45__
  | WRITE of t__46__
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";



(* A parser definition for Fasto, for use with mosmlyac. *)

open Fasto
open Fasto.UnknownTypes

(* Line 13, file Parser.sml *)
val yytransl = #[
  257 (* AND *),
  258 (* ARROW *),
  259 (* BOOL *),
  260 (* CHAR *),
  261 (* CHARLIT *),
  262 (* COMMA *),
  263 (* DEQ *),
  264 (* DIV *),
  265 (* ELSE *),
  266 (* EOF *),
  267 (* EQ *),
  268 (* FALSE *),
  269 (* FILTER *),
  270 (* FN *),
  271 (* FUN *),
  272 (* ID *),
  273 (* IF *),
  274 (* IN *),
  275 (* INT *),
  276 (* IOTA *),
  277 (* LAMBDA *),
  278 (* LBRACKET *),
  279 (* LCURLY *),
  280 (* LET *),
  281 (* LPAR *),
  282 (* LTH *),
  283 (* MAP *),
  284 (* MINUS *),
  285 (* NEG *),
  286 (* NOT *),
  287 (* NUM *),
  288 (* OP *),
  289 (* OR *),
  290 (* PLUS *),
  291 (* RBRACKET *),
  292 (* RCURLY *),
  293 (* READ *),
  294 (* REDUCE *),
  295 (* REPLICATE *),
  296 (* RPAR *),
  297 (* SCAN *),
  298 (* STRINGLIT *),
  299 (* THEN *),
  300 (* TIMES *),
  301 (* TRUE *),
  302 (* WRITE *),
    0];

val yylhs = "\255\255\
\\001\000\002\000\002\000\003\000\003\000\004\000\004\000\004\000\
\\004\000\005\000\005\000\009\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\007\000\007\000\008\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\002\000\007\000\006\000\001\000\001\000\001\000\
\\003\000\004\000\002\000\001\000\001\000\001\000\001\000\001\000\
\\003\000\003\000\003\000\003\000\003\000\002\000\003\000\003\000\
\\003\000\003\000\006\000\004\000\003\000\004\000\004\000\004\000\
\\006\000\008\000\006\000\009\000\008\000\003\000\006\000\004\000\
\\001\000\001\000\002\000\003\000\001\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\047\000\000\000\007\000\008\000\006\000\
\\000\000\000\000\000\000\001\000\000\000\002\000\000\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\
\\042\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\013\000\000\000\000\000\000\000\000\000\016\000\
\\041\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\010\000\000\000\000\000\
\\029\000\000\000\000\000\000\000\000\000\017\000\000\000\038\000\
\\046\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\040\000\028\000\000\000\032\000\044\000\000\000\000\000\030\000\
\\012\000\000\000\000\000\000\000\000\000\031\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\035\000\
\\000\000\000\000\033\000\000\000\000\000\000\000\000\000\000\000\
\\034\000\037\000\036\000";

val yydgoto = "\002\000\
\\004\000\005\000\010\000\019\000\020\000\050\000\051\000\082\000\
\\106\000";

val yysindex = "\008\000\
\\249\254\000\000\001\255\000\000\007\255\000\000\000\000\000\000\
\\001\255\249\254\017\255\000\000\000\255\000\000\012\255\000\000\
\\119\255\038\255\035\255\023\255\175\001\061\255\064\255\000\000\
\\000\000\037\255\175\001\047\255\175\001\054\255\175\001\051\255\
\\175\001\175\001\000\000\055\255\056\255\058\255\071\255\000\000\
\\000\000\072\255\217\000\001\255\175\001\175\001\144\001\223\255\
\\175\001\007\000\048\255\087\255\016\000\094\255\000\000\230\000\
\\001\255\243\254\175\001\094\255\175\001\175\001\175\001\175\001\
\\175\001\175\001\175\001\175\001\175\001\000\000\217\000\019\000\
\\000\000\073\255\175\001\031\000\175\001\000\000\175\001\000\000\
\\000\000\105\255\075\255\078\255\110\255\060\000\112\255\069\000\
\\045\255\116\255\000\000\116\255\006\255\230\000\006\255\000\000\
\\000\000\000\000\072\000\000\000\000\000\100\000\175\001\000\000\
\\000\000\113\255\175\001\175\001\175\001\000\000\175\001\175\001\
\\113\000\175\001\130\000\142\000\159\000\217\000\217\000\000\000\
\\171\000\175\001\000\000\175\001\175\001\183\000\200\000\213\000\
\\000\000\000\000\000\000";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\111\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\080\255\000\000\000\000\
\\000\000\099\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\011\255\000\000\000\000\000\000\000\000\000\000\
\\000\000\231\254\000\000\000\000\000\000\000\000\139\255\086\001\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\019\255\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\021\255\059\255\179\255\073\001\253\000\122\001\035\001\219\255\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\011\001\075\001\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000";

val yygindex = "\000\000\
\\000\000\116\000\000\000\254\255\084\000\235\255\211\255\214\255\
\\000\000";

val YYTABLESIZE = 733;
val yytable = "\043\000\
\\011\000\074\000\081\000\006\000\007\000\048\000\013\000\003\000\
\\001\000\053\000\045\000\055\000\056\000\064\000\045\000\085\000\
\\012\000\087\000\084\000\008\000\005\000\023\000\009\000\071\000\
\\072\000\005\000\023\000\076\000\004\000\023\000\023\000\101\000\
\\015\000\004\000\016\000\023\000\017\000\086\000\023\000\088\000\
\\089\000\090\000\091\000\092\000\093\000\094\000\095\000\096\000\
\\021\000\069\000\022\000\063\000\064\000\099\000\083\000\023\000\
\\023\000\102\000\046\000\025\000\023\000\047\000\023\000\023\000\
\\025\000\025\000\044\000\025\000\025\000\052\000\065\000\049\000\
\\066\000\025\000\045\000\054\000\025\000\067\000\068\000\057\000\
\\058\000\113\000\059\000\078\000\025\000\115\000\116\000\117\000\
\\069\000\118\000\119\000\025\000\121\000\025\000\025\000\060\000\
\\061\000\079\000\025\000\015\000\126\000\025\000\127\000\128\000\
\\015\000\015\000\015\000\015\000\015\000\081\000\103\000\105\000\
\\098\000\015\000\104\000\107\000\015\000\109\000\114\000\011\000\
\\003\000\006\000\007\000\064\000\015\000\014\000\015\000\070\000\
\\000\000\000\000\000\000\015\000\015\000\015\000\015\000\000\000\
\\000\000\008\000\015\000\022\000\009\000\015\000\015\000\066\000\
\\022\000\022\000\022\000\022\000\022\000\068\000\000\000\000\000\
\\000\000\022\000\000\000\000\000\022\000\000\000\018\000\069\000\
\\000\000\000\000\000\000\000\000\022\000\000\000\022\000\000\000\
\\000\000\000\000\000\000\022\000\022\000\022\000\022\000\000\000\
\\000\000\000\000\022\000\021\000\000\000\022\000\022\000\000\000\
\\021\000\021\000\021\000\021\000\021\000\000\000\000\000\000\000\
\\000\000\021\000\000\000\000\000\021\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\021\000\000\000\021\000\000\000\
\\000\000\000\000\000\000\021\000\021\000\021\000\021\000\000\000\
\\000\000\000\000\021\000\020\000\000\000\021\000\021\000\062\000\
\\020\000\020\000\020\000\020\000\020\000\063\000\064\000\000\000\
\\000\000\020\000\000\000\000\000\020\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\020\000\000\000\020\000\000\000\
\\065\000\000\000\066\000\020\000\020\000\020\000\020\000\067\000\
\\068\000\000\000\020\000\000\000\000\000\020\000\020\000\062\000\
\\000\000\075\000\069\000\000\000\077\000\063\000\064\000\000\000\
\\062\000\000\000\000\000\062\000\000\000\000\000\063\000\064\000\
\\000\000\063\000\064\000\000\000\000\000\000\000\000\000\062\000\
\\065\000\000\000\066\000\000\000\000\000\063\000\064\000\067\000\
\\068\000\065\000\000\000\066\000\065\000\000\000\066\000\000\000\
\\067\000\068\000\069\000\067\000\068\000\097\000\000\000\080\000\
\\065\000\000\000\066\000\069\000\062\000\000\000\069\000\067\000\
\\068\000\108\000\063\000\064\000\000\000\062\000\100\000\000\000\
\\062\000\000\000\069\000\063\000\064\000\000\000\063\000\064\000\
\\111\000\000\000\000\000\000\000\000\000\065\000\000\000\066\000\
\\000\000\000\000\000\000\000\000\067\000\068\000\065\000\000\000\
\\066\000\065\000\000\000\066\000\062\000\067\000\068\000\069\000\
\\067\000\068\000\063\000\064\000\110\000\000\000\000\000\000\000\
\\069\000\062\000\000\000\069\000\000\000\112\000\000\000\063\000\
\\064\000\000\000\000\000\000\000\000\000\065\000\000\000\066\000\
\\000\000\000\000\062\000\000\000\067\000\068\000\000\000\122\000\
\\063\000\064\000\065\000\000\000\066\000\000\000\062\000\069\000\
\\000\000\067\000\068\000\000\000\063\000\064\000\000\000\000\000\
\\120\000\000\000\000\000\065\000\069\000\066\000\000\000\062\000\
\\000\000\000\000\067\000\068\000\124\000\063\000\064\000\065\000\
\\000\000\066\000\000\000\062\000\000\000\069\000\067\000\068\000\
\\125\000\063\000\064\000\000\000\000\000\123\000\000\000\062\000\
\\065\000\069\000\066\000\000\000\000\000\063\000\064\000\067\000\
\\068\000\000\000\000\000\000\000\065\000\000\000\066\000\000\000\
\\062\000\000\000\069\000\067\000\068\000\000\000\063\000\064\000\
\\065\000\000\000\066\000\000\000\000\000\062\000\069\000\067\000\
\\068\000\062\000\000\000\063\000\064\000\000\000\129\000\063\000\
\\064\000\065\000\069\000\066\000\000\000\000\000\000\000\000\000\
\\067\000\068\000\000\000\000\000\063\000\064\000\065\000\130\000\
\\066\000\000\000\065\000\069\000\066\000\067\000\068\000\000\000\
\\000\000\067\000\068\000\000\000\131\000\019\000\000\000\065\000\
\\069\000\066\000\019\000\019\000\069\000\019\000\019\000\068\000\
\\000\000\000\000\000\000\019\000\000\000\000\000\019\000\000\000\
\\027\000\069\000\000\000\027\000\027\000\000\000\019\000\000\000\
\\019\000\027\000\000\000\000\000\027\000\019\000\019\000\019\000\
\\019\000\000\000\000\000\018\000\019\000\000\000\000\000\019\000\
\\018\000\018\000\000\000\018\000\018\000\027\000\027\000\000\000\
\\000\000\018\000\027\000\000\000\018\000\027\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\018\000\000\000\018\000\000\000\
\\000\000\000\000\000\000\018\000\018\000\018\000\018\000\000\000\
\\000\000\026\000\018\000\000\000\000\000\018\000\026\000\026\000\
\\039\000\026\000\026\000\039\000\039\000\000\000\043\000\026\000\
\\000\000\039\000\026\000\043\000\039\000\000\000\043\000\043\000\
\\000\000\000\000\026\000\000\000\043\000\000\000\000\000\043\000\
\\000\000\026\000\000\000\026\000\026\000\039\000\039\000\000\000\
\\026\000\000\000\039\000\026\000\000\000\039\000\043\000\000\000\
\\043\000\043\000\024\000\000\000\000\000\043\000\000\000\024\000\
\\043\000\000\000\024\000\024\000\000\000\000\000\000\000\000\000\
\\024\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\024\000\000\000\000\000\000\000\
\\000\000\000\000\024\000\025\000\024\000\024\000\000\000\026\000\
\\027\000\024\000\000\000\028\000\024\000\000\000\029\000\030\000\
\\031\000\000\000\032\000\000\000\033\000\034\000\035\000\000\000\
\\000\000\000\000\000\000\024\000\036\000\037\000\038\000\073\000\
\\039\000\040\000\025\000\000\000\041\000\042\000\026\000\027\000\
\\000\000\000\000\028\000\000\000\000\000\029\000\030\000\031\000\
\\000\000\032\000\000\000\033\000\034\000\035\000\000\000\000\000\
\\000\000\000\000\000\000\036\000\037\000\038\000\000\000\039\000\
\\040\000\000\000\000\000\041\000\042\000";

val yycheck = "\021\000\
\\003\000\047\000\016\001\003\001\004\001\027\000\009\000\015\001\
\\001\000\031\000\036\001\033\000\034\000\008\001\040\001\058\000\
\\010\001\060\000\032\001\019\001\010\001\001\001\022\001\045\000\
\\046\000\015\001\006\001\049\000\010\001\009\001\010\001\077\000\
\\016\001\015\001\035\001\015\001\025\001\059\000\018\001\061\000\
\\062\000\063\000\064\000\065\000\066\000\067\000\068\000\069\000\
\\011\001\044\001\016\001\007\001\008\001\075\000\057\000\035\001\
\\036\001\079\000\022\001\001\001\040\001\025\001\040\001\043\001\
\\006\001\007\001\006\001\009\001\010\001\016\001\026\001\025\001\
\\028\001\015\001\011\001\025\001\018\001\033\001\034\001\025\001\
\\025\001\103\000\025\001\036\001\026\001\107\000\108\000\109\000\
\\044\001\111\000\112\000\033\001\114\000\035\001\036\001\025\001\
\\025\001\011\001\040\001\001\001\122\000\043\001\124\000\125\000\
\\006\001\007\001\008\001\009\001\010\001\016\001\006\001\034\001\
\\040\001\015\001\040\001\006\001\018\001\006\001\006\001\040\001\
\\010\001\003\001\004\001\008\001\026\001\010\000\028\001\044\000\
\\255\255\255\255\255\255\033\001\034\001\035\001\036\001\255\255\
\\255\255\019\001\040\001\001\001\022\001\043\001\044\001\028\001\
\\006\001\007\001\008\001\009\001\010\001\034\001\255\255\255\255\
\\255\255\015\001\255\255\255\255\018\001\255\255\040\001\044\001\
\\255\255\255\255\255\255\255\255\026\001\255\255\028\001\255\255\
\\255\255\255\255\255\255\033\001\034\001\035\001\036\001\255\255\
\\255\255\255\255\040\001\001\001\255\255\043\001\044\001\255\255\
\\006\001\007\001\008\001\009\001\010\001\255\255\255\255\255\255\
\\255\255\015\001\255\255\255\255\018\001\255\255\255\255\255\255\
\\255\255\255\255\255\255\255\255\026\001\255\255\028\001\255\255\
\\255\255\255\255\255\255\033\001\034\001\035\001\036\001\255\255\
\\255\255\255\255\040\001\001\001\255\255\043\001\044\001\001\001\
\\006\001\007\001\008\001\009\001\010\001\007\001\008\001\255\255\
\\255\255\015\001\255\255\255\255\018\001\255\255\255\255\255\255\
\\255\255\255\255\255\255\255\255\026\001\255\255\028\001\255\255\
\\026\001\255\255\028\001\033\001\034\001\035\001\036\001\033\001\
\\034\001\255\255\040\001\255\255\255\255\043\001\044\001\001\001\
\\255\255\043\001\044\001\255\255\006\001\007\001\008\001\255\255\
\\001\001\255\255\255\255\001\001\255\255\255\255\007\001\008\001\
\\255\255\007\001\008\001\255\255\255\255\255\255\255\255\001\001\
\\026\001\255\255\028\001\255\255\255\255\007\001\008\001\033\001\
\\034\001\026\001\255\255\028\001\026\001\255\255\028\001\255\255\
\\033\001\034\001\044\001\033\001\034\001\035\001\255\255\040\001\
\\026\001\255\255\028\001\044\001\001\001\255\255\044\001\033\001\
\\034\001\006\001\007\001\008\001\255\255\001\001\040\001\255\255\
\\001\001\255\255\044\001\007\001\008\001\255\255\007\001\008\001\
\\009\001\255\255\255\255\255\255\255\255\026\001\255\255\028\001\
\\255\255\255\255\255\255\255\255\033\001\034\001\026\001\255\255\
\\028\001\026\001\255\255\028\001\001\001\033\001\034\001\044\001\
\\033\001\034\001\007\001\008\001\040\001\255\255\255\255\255\255\
\\044\001\001\001\255\255\044\001\255\255\018\001\255\255\007\001\
\\008\001\255\255\255\255\255\255\255\255\026\001\255\255\028\001\
\\255\255\255\255\001\001\255\255\033\001\034\001\255\255\006\001\
\\007\001\008\001\026\001\255\255\028\001\255\255\001\001\044\001\
\\255\255\033\001\034\001\255\255\007\001\008\001\255\255\255\255\
\\040\001\255\255\255\255\026\001\044\001\028\001\255\255\001\001\
\\255\255\255\255\033\001\034\001\006\001\007\001\008\001\026\001\
\\255\255\028\001\255\255\001\001\255\255\044\001\033\001\034\001\
\\006\001\007\001\008\001\255\255\255\255\040\001\255\255\001\001\
\\026\001\044\001\028\001\255\255\255\255\007\001\008\001\033\001\
\\034\001\255\255\255\255\255\255\026\001\255\255\028\001\255\255\
\\001\001\255\255\044\001\033\001\034\001\255\255\007\001\008\001\
\\026\001\255\255\028\001\255\255\255\255\001\001\044\001\033\001\
\\034\001\001\001\255\255\007\001\008\001\255\255\040\001\007\001\
\\008\001\026\001\044\001\028\001\255\255\255\255\255\255\255\255\
\\033\001\034\001\255\255\255\255\007\001\008\001\026\001\040\001\
\\028\001\255\255\026\001\044\001\028\001\033\001\034\001\255\255\
\\255\255\033\001\034\001\255\255\040\001\001\001\255\255\026\001\
\\044\001\028\001\006\001\007\001\044\001\009\001\010\001\034\001\
\\255\255\255\255\255\255\015\001\255\255\255\255\018\001\255\255\
\\006\001\044\001\255\255\009\001\010\001\255\255\026\001\255\255\
\\028\001\015\001\255\255\255\255\018\001\033\001\034\001\035\001\
\\036\001\255\255\255\255\001\001\040\001\255\255\255\255\043\001\
\\006\001\007\001\255\255\009\001\010\001\035\001\036\001\255\255\
\\255\255\015\001\040\001\255\255\018\001\043\001\255\255\255\255\
\\255\255\255\255\255\255\255\255\026\001\255\255\028\001\255\255\
\\255\255\255\255\255\255\033\001\034\001\035\001\036\001\255\255\
\\255\255\001\001\040\001\255\255\255\255\043\001\006\001\007\001\
\\006\001\009\001\010\001\009\001\010\001\255\255\001\001\015\001\
\\255\255\015\001\018\001\006\001\018\001\255\255\009\001\010\001\
\\255\255\255\255\026\001\255\255\015\001\255\255\255\255\018\001\
\\255\255\033\001\255\255\035\001\036\001\035\001\036\001\255\255\
\\040\001\255\255\040\001\043\001\255\255\043\001\033\001\255\255\
\\035\001\036\001\001\001\255\255\255\255\040\001\255\255\006\001\
\\043\001\255\255\009\001\010\001\255\255\255\255\255\255\255\255\
\\015\001\255\255\255\255\018\001\255\255\255\255\255\255\255\255\
\\255\255\255\255\255\255\255\255\005\001\255\255\255\255\255\255\
\\255\255\255\255\033\001\012\001\035\001\036\001\255\255\016\001\
\\017\001\040\001\255\255\020\001\043\001\255\255\023\001\024\001\
\\025\001\255\255\027\001\255\255\029\001\030\001\031\001\255\255\
\\255\255\255\255\255\255\005\001\037\001\038\001\039\001\040\001\
\\041\001\042\001\012\001\255\255\045\001\046\001\016\001\017\001\
\\255\255\255\255\020\001\255\255\255\255\023\001\024\001\025\001\
\\255\255\027\001\255\255\029\001\030\001\031\001\255\255\255\255\
\\255\255\255\255\255\255\037\001\038\001\039\001\255\255\041\001\
\\042\001\255\255\255\255\045\001\046\001";

val yyact = vector_ 48 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 43 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.UnknownTypes.FunDec list
val d__2__ = peekVal 0 : (int*int)
in
( (d__1__) ) end : Fasto.UnknownTypes.Prog))
;
(* Rule 2, file Parser.grm, line 46 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.FunDec
val d__3__ = peekVal 0 : Fasto.UnknownTypes.FunDec list
in
( (d__2__) :: (d__3__) ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 3, file Parser.grm, line 47 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.FunDec
in
( (d__2__) :: [] ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 4, file Parser.grm, line 51 *)
val _ = update_ yyact 4
(fn () => repr(let
val d__1__ = peekVal 6 : Fasto.Type
val d__2__ = peekVal 5 : string*(int*int)
val d__3__ = peekVal 4 : (int*int)
val d__4__ = peekVal 3 : Fasto.Param list
val d__5__ = peekVal 2 : (int*int)
val d__6__ = peekVal 1 : (int*int)
val d__7__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( FunDec (#1 (d__2__), (d__1__), (d__4__), (d__7__), #2 (d__2__)) ) end : Fasto.UnknownTypes.FunDec))
;
(* Rule 5, file Parser.grm, line 53 *)
val _ = update_ yyact 5
(fn () => repr(let
val d__1__ = peekVal 5 : Fasto.Type
val d__2__ = peekVal 4 : string*(int*int)
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( FunDec (#1 (d__2__), (d__1__), [], (d__6__), #2 (d__2__)) ) end : Fasto.UnknownTypes.FunDec))
;
(* Rule 6, file Parser.grm, line 56 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Int ) end : Fasto.Type))
;
(* Rule 7, file Parser.grm, line 57 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Bool ) end : Fasto.Type))
;
(* Rule 8, file Parser.grm, line 58 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Char ) end : Fasto.Type))
;
(* Rule 9, file Parser.grm, line 59 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.Type
val d__3__ = peekVal 0 : (int*int)
in
( Array (d__2__) ) end : Fasto.Type))
;
(* Rule 10, file Parser.grm, line 62 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 3 : Fasto.Type
val d__2__ = peekVal 2 : string*(int*int)
val d__3__ = peekVal 1 : (int*int)
val d__4__ = peekVal 0 : Fasto.Param list
in
( Param (#1 (d__2__), (d__1__)) :: (d__4__) ) end : Fasto.Param list))
;
(* Rule 11, file Parser.grm, line 63 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.Type
val d__2__ = peekVal 0 : string*(int*int)
in
( Param (#1 (d__2__), (d__1__)) :: [] ) end : Fasto.Param list))
;
(* Rule 12, file Parser.grm, line 66 *)
val _ = update_ yyact 12
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( (Lambda
                           (Int, [Param ("x", Int),
                                        Param ("y", Int)],
                            Plus (Var ("x", (d__1__)),
                                        Var ("y", (d__1__)),
                                        (d__1__)) ,(d__1__)))
                        ) end : Fasto.UnknownTypes.FunArg))
;
(* Rule 13, file Parser.grm, line 75 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Constant (IntVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 14, file Parser.grm, line 76 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : char*(int*int)
in
( Constant (CharVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 15, file Parser.grm, line 77 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Var (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 16, file Parser.grm, line 78 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( StringLit (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 17, file Parser.grm, line 80 *)
val _ = update_ yyact 17
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__3__ = peekVal 0 : (int*int)
in
( ArrayLit ((d__2__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 18, file Parser.grm, line 81 *)
val _ = update_ yyact 18
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Plus ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 19, file Parser.grm, line 82 *)
val _ = update_ yyact 19
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Minus((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 20, file Parser.grm, line 84 *)
val _ = update_ yyact 20
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Times((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 21, file Parser.grm, line 86 *)
val _ = update_ yyact 21
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Divide((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 22, file Parser.grm, line 88 *)
val _ = update_ yyact 22
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Negate((d__2__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 23, file Parser.grm, line 89 *)
val _ = update_ yyact 23
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( And((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 24, file Parser.grm, line 91 *)
val _ = update_ yyact 24
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Or((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 25, file Parser.grm, line 93 *)
val _ = update_ yyact 25
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Equal((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 26, file Parser.grm, line 94 *)
val _ = update_ yyact 26
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Less ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 27, file Parser.grm, line 96 *)
val _ = update_ yyact 27
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( If ((d__2__), (d__4__), (d__6__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 28, file Parser.grm, line 98 *)
val _ = update_ yyact 28
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__4__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), (d__3__), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 29, file Parser.grm, line 100 *)
val _ = update_ yyact 29
(fn () => repr(let
val d__1__ = peekVal 2 : string*(int*int)
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), [], #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 30, file Parser.grm, line 103 *)
val _ = update_ yyact 30
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.Type
val d__4__ = peekVal 0 : (int*int)
in
( Read ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 31, file Parser.grm, line 105 *)
val _ = update_ yyact 31
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Write ((d__3__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 32, file Parser.grm, line 107 *)
val _ = update_ yyact 32
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Iota ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 33, file Parser.grm, line 109 *)
val _ = update_ yyact 33
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : (int*int)
val d__3__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 0 : (int*int)
in
( Replicate ((d__3__), (d__5__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 34, file Parser.grm, line 111 *)
val _ = update_ yyact 34
(fn () => repr(let
val d__1__ = peekVal 7 : (int*int)
val d__2__ = peekVal 6 : (int*int)
val d__3__ = peekVal 5 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 4 : (int*int)
val d__5__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 2 : (int*int)
val d__7__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__8__ = peekVal 0 : (int*int)
in
( Reduce ((d__3__), (d__5__), (d__7__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 35, file Parser.grm, line 113 *)
val _ = update_ yyact 35
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : (int*int)
val d__3__ = peekVal 3 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 0 : (int*int)
in
( Map ((d__3__), (d__5__), (), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 36, file Parser.grm, line 115 *)
val _ = update_ yyact 36
(fn () => repr(let
val d__1__ = peekVal 8 : (int*int)
val d__2__ = peekVal 7 : (int*int)
val d__3__ = peekVal 6 : (int*int)
val d__4__ = peekVal 5 : Fasto.UnknownTypes.FunArg
val d__5__ = peekVal 4 : (int*int)
val d__6__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__7__ = peekVal 2 : (int*int)
val d__8__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__9__ = peekVal 0 : (int*int)
in
( Reduce ((d__4__), (d__6__), (d__8__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 37, file Parser.grm, line 117 *)
val _ = update_ yyact 37
(fn () => repr(let
val d__1__ = peekVal 7 : (int*int)
val d__2__ = peekVal 6 : (int*int)
val d__3__ = peekVal 5 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 4 : (int*int)
val d__5__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 2 : (int*int)
val d__7__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__8__ = peekVal 0 : (int*int)
in
( Scan ((d__3__), (d__5__), (d__7__), (), (d__1__))) end : Fasto.UnknownTypes.Exp))
;
(* Rule 38, file Parser.grm, line 118 *)
val _ = update_ yyact 38
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 39, file Parser.grm, line 120 *)
val _ = update_ yyact 39
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : string*(int*int)
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Let (Dec (#1 (d__2__), (d__4__), (d__3__)), (d__6__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 40, file Parser.grm, line 122 *)
val _ = update_ yyact 40
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Index (#1 (d__1__), (d__3__), (), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 41, file Parser.grm, line 123 *)
val _ = update_ yyact 41
(fn () => repr(let
val d__1__ = peekVal 0 : bool*(int*int)
in
( Constant ( BoolVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 42, file Parser.grm, line 124 *)
val _ = update_ yyact 42
(fn () => repr(let
val d__1__ = peekVal 0 : bool*(int*int)
in
( Constant ( BoolVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 43, file Parser.grm, line 125 *)
val _ = update_ yyact 43
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Not ( (d__2__), (d__1__) ) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 44, file Parser.grm, line 128 *)
val _ = update_ yyact 44
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp list
in
( (d__1__) :: (d__3__) ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 45, file Parser.grm, line 129 *)
val _ = update_ yyact 45
(fn () => repr(let
val d__1__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( (d__1__) :: [] ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 46, file Parser.grm, line 132 *)
val _ = update_ yyact 46
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( FunName (#1 (d__1__)) ) end : Fasto.UnknownTypes.FunArg))
;
(* Entry Prog *)
val _ = update_ yyact 47 (fn () => raise yyexit (peekVal 0));
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
