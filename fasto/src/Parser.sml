local
type t__1__ = (int*int)
type t__2__ = (int*int)
type t__3__ = char*(int*int)
type t__4__ = (int*int)
type t__5__ = (int*int)
type t__6__ = (int*int)
type t__7__ = (int*int)
type t__8__ = (int*int)
type t__9__ = (int*int)
type t__10__ = (int*int)
type t__11__ = bool*(int*int)
type t__12__ = (int*int)
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
type t__44__ = bool*(int*int)
type t__45__ = (int*int)
in
datatype token =
    BOOL of t__1__
  | CHAR of t__2__
  | CHARLIT of t__3__
  | COMMA of t__4__
  | DEQ of t__5__
  | DIVERGENT of t__6__
  | DOLAN of t__7__
  | ELSE of t__8__
  | EOF of t__9__
  | EQ of t__10__
  | FALSE of t__11__
  | FILTER of t__12__
  | FN of t__13__
  | FUN of t__14__
  | HANSNOTTO of t__15__
  | ID of t__16__
  | IF of t__17__
  | IN of t__18__
  | INT of t__19__
  | IOTA of t__20__
  | LBRACKET of t__21__
  | LCURLY of t__22__
  | LET of t__23__
  | LPAR of t__24__
  | LTH of t__25__
  | MAP of t__26__
  | MINUS of t__27__
  | MULIFICENT of t__28__
  | NEGROMANCER of t__29__
  | NOT of t__30__
  | NUM of t__31__
  | OP of t__32__
  | ORBITER of t__33__
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
  | TRUE of t__44__
  | WRITE of t__45__
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";



(* A parser definition for Fasto, for use with mosmlyac. *)

open Fasto
open Fasto.UnknownTypes

(* Line 13, file Parser.sml *)
val yytransl = #[
  257 (* BOOL *),
  258 (* CHAR *),
  259 (* CHARLIT *),
  260 (* COMMA *),
  261 (* DEQ *),
  262 (* DIVERGENT *),
  263 (* DOLAN *),
  264 (* ELSE *),
  265 (* EOF *),
  266 (* EQ *),
  267 (* FALSE *),
  268 (* FILTER *),
  269 (* FN *),
  270 (* FUN *),
  271 (* HANSNOTTO *),
  272 (* ID *),
  273 (* IF *),
  274 (* IN *),
  275 (* INT *),
  276 (* IOTA *),
  277 (* LBRACKET *),
  278 (* LCURLY *),
  279 (* LET *),
  280 (* LPAR *),
  281 (* LTH *),
  282 (* MAP *),
  283 (* MINUS *),
  284 (* MULIFICENT *),
  285 (* NEGROMANCER *),
  286 (* NOT *),
  287 (* NUM *),
  288 (* OP *),
  289 (* ORBITER *),
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
  300 (* TRUE *),
  301 (* WRITE *),
    0];

val yylhs = "\255\255\
\\001\000\002\000\002\000\003\000\003\000\004\000\004\000\004\000\
\\004\000\005\000\005\000\009\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\007\000\007\000\008\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\002\000\007\000\006\000\001\000\001\000\001\000\
\\003\000\004\000\002\000\001\000\001\000\001\000\001\000\001\000\
\\003\000\003\000\003\000\003\000\003\000\002\000\003\000\003\000\
\\003\000\003\000\006\000\004\000\003\000\004\000\004\000\004\000\
\\006\000\008\000\006\000\009\000\003\000\006\000\004\000\001\000\
\\001\000\002\000\003\000\001\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\046\000\000\000\007\000\008\000\006\000\
\\000\000\000\000\000\000\001\000\000\000\002\000\000\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\
\\041\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\013\000\000\000\000\000\000\000\016\000\040\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\010\000\000\000\000\000\029\000\000\000\
\\000\000\000\000\000\000\017\000\000\000\037\000\045\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\039\000\028\000\000\000\
\\032\000\043\000\000\000\000\000\030\000\012\000\000\000\000\000\
\\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\035\000\000\000\000\000\033\000\000\000\000\000\
\\000\000\034\000\036\000";

val yydgoto = "\002\000\
\\004\000\005\000\010\000\019\000\020\000\050\000\051\000\080\000\
\\103\000";

val yysindex = "\003\000\
\\248\254\000\000\142\255\000\000\011\255\000\000\000\000\000\000\
\\142\255\248\254\008\255\000\000\254\254\000\000\010\255\000\000\
\\028\255\038\255\041\255\019\255\109\255\056\255\052\255\000\000\
\\000\000\109\255\253\254\109\255\042\255\109\255\049\255\109\255\
\\043\255\109\255\000\000\045\255\046\255\050\255\000\000\000\000\
\\051\255\057\001\142\255\109\255\057\001\109\255\077\255\107\000\
\\109\255\227\000\037\255\066\255\118\000\065\255\002\255\142\255\
\\241\254\109\255\109\255\109\255\109\255\109\255\109\255\109\255\
\\109\255\109\255\109\255\000\000\057\001\210\000\000\000\055\255\
\\109\255\132\000\109\255\000\000\109\255\000\000\000\000\078\255\
\\062\255\070\255\087\255\242\000\142\000\044\255\002\255\057\001\
\\044\255\057\255\002\255\057\001\057\255\000\000\000\000\026\001\
\\000\000\000\000\043\001\109\255\000\000\000\000\101\255\109\255\
\\109\255\000\000\109\255\109\255\156\000\109\255\252\000\172\000\
\\057\001\057\001\000\000\011\001\109\255\000\000\109\255\186\000\
\\196\000\000\000\000\000";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\098\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\069\255\000\000\000\000\
\\000\000\000\000\151\255\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\001\255\000\000\000\000\018\255\000\000\000\000\000\000\
\\000\000\232\254\000\000\000\000\000\000\000\000\163\255\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\005\255\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\009\000\196\255\051\000\
\\021\000\208\255\220\255\062\000\253\255\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\064\000\075\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000";

val yygindex = "\000\000\
\\000\000\100\000\000\000\255\255\068\000\235\255\212\255\056\000\
\\000\000";

val YYTABLESIZE = 603;
val yytable = "\042\000\
\\079\000\011\000\072\000\001\000\045\000\003\000\048\000\013\000\
\\062\000\005\000\053\000\044\000\055\000\004\000\005\000\044\000\
\\082\000\046\000\004\000\012\000\047\000\042\000\069\000\015\000\
\\070\000\042\000\042\000\074\000\006\000\007\000\098\000\042\000\
\\016\000\017\000\066\000\042\000\084\000\085\000\086\000\087\000\
\\088\000\089\000\090\000\091\000\092\000\093\000\008\000\021\000\
\\009\000\061\000\062\000\096\000\042\000\042\000\081\000\099\000\
\\022\000\042\000\023\000\043\000\042\000\044\000\061\000\062\000\
\\052\000\049\000\054\000\018\000\056\000\057\000\064\000\065\000\
\\076\000\058\000\059\000\077\000\066\000\067\000\109\000\024\000\
\\079\000\100\000\111\000\112\000\065\000\113\000\114\000\025\000\
\\116\000\066\000\104\000\026\000\027\000\028\000\095\000\120\000\
\\029\000\121\000\030\000\031\000\032\000\101\000\033\000\102\000\
\\110\000\034\000\003\000\035\000\011\000\014\000\068\000\024\000\
\\083\000\036\000\037\000\038\000\071\000\000\000\039\000\025\000\
\\040\000\041\000\000\000\026\000\027\000\028\000\000\000\000\000\
\\029\000\000\000\030\000\031\000\032\000\000\000\033\000\000\000\
\\000\000\034\000\000\000\035\000\000\000\000\000\006\000\007\000\
\\000\000\036\000\037\000\038\000\000\000\000\000\039\000\000\000\
\\040\000\041\000\015\000\015\000\015\000\015\000\015\000\015\000\
\\008\000\000\000\009\000\000\000\015\000\000\000\022\000\022\000\
\\015\000\000\000\022\000\022\000\000\000\000\000\000\000\015\000\
\\022\000\015\000\015\000\000\000\022\000\000\000\000\000\015\000\
\\015\000\015\000\015\000\022\000\000\000\022\000\015\000\000\000\
\\000\000\015\000\000\000\000\000\022\000\022\000\022\000\021\000\
\\021\000\000\000\022\000\021\000\021\000\022\000\000\000\000\000\
\\000\000\021\000\000\000\019\000\019\000\021\000\000\000\019\000\
\\019\000\000\000\000\000\000\000\021\000\019\000\021\000\020\000\
\\020\000\019\000\000\000\020\000\020\000\021\000\021\000\021\000\
\\019\000\020\000\019\000\021\000\000\000\020\000\021\000\000\000\
\\000\000\019\000\019\000\019\000\020\000\000\000\020\000\019\000\
\\000\000\000\000\019\000\000\000\000\000\020\000\020\000\020\000\
\\018\000\018\000\000\000\020\000\018\000\018\000\020\000\000\000\
\\000\000\000\000\018\000\000\000\025\000\025\000\018\000\000\000\
\\025\000\025\000\000\000\000\000\000\000\018\000\025\000\018\000\
\\026\000\026\000\025\000\000\000\026\000\026\000\018\000\018\000\
\\018\000\025\000\026\000\000\000\018\000\000\000\026\000\018\000\
\\000\000\000\000\000\000\025\000\025\000\026\000\000\000\000\000\
\\025\000\000\000\000\000\025\000\000\000\000\000\023\000\026\000\
\\026\000\000\000\023\000\023\000\026\000\000\000\000\000\026\000\
\\023\000\024\000\000\000\027\000\023\000\024\000\024\000\027\000\
\\027\000\000\000\000\000\024\000\000\000\027\000\038\000\024\000\
\\000\000\027\000\038\000\038\000\000\000\023\000\023\000\000\000\
\\038\000\000\000\023\000\000\000\038\000\023\000\000\000\000\000\
\\024\000\024\000\027\000\027\000\000\000\024\000\000\000\027\000\
\\024\000\000\000\027\000\000\000\000\000\038\000\038\000\060\000\
\\061\000\062\000\038\000\000\000\000\000\038\000\000\000\000\000\
\\000\000\000\000\060\000\061\000\062\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\063\000\000\000\064\000\065\000\000\000\
\\060\000\061\000\062\000\066\000\067\000\000\000\063\000\000\000\
\\064\000\065\000\060\000\061\000\062\000\073\000\066\000\067\000\
\\000\000\000\000\000\000\000\000\063\000\078\000\064\000\065\000\
\\060\000\061\000\062\000\000\000\066\000\067\000\063\000\000\000\
\\064\000\065\000\000\000\097\000\000\000\000\000\066\000\067\000\
\\060\000\061\000\062\000\000\000\063\000\106\000\064\000\065\000\
\\000\000\000\000\000\000\000\000\066\000\067\000\060\000\061\000\
\\062\000\000\000\000\000\115\000\063\000\000\000\064\000\065\000\
\\060\000\061\000\062\000\000\000\066\000\067\000\000\000\000\000\
\\000\000\000\000\063\000\118\000\064\000\065\000\060\000\061\000\
\\062\000\000\000\066\000\067\000\063\000\000\000\064\000\065\000\
\\000\000\122\000\000\000\000\000\066\000\067\000\075\000\060\000\
\\061\000\062\000\063\000\123\000\064\000\065\000\000\000\000\000\
\\000\000\000\000\066\000\067\000\094\000\105\000\060\000\061\000\
\\062\000\000\000\000\000\063\000\000\000\064\000\065\000\117\000\
\\060\000\061\000\062\000\066\000\067\000\000\000\000\000\000\000\
\\000\000\000\000\063\000\000\000\064\000\065\000\119\000\060\000\
\\061\000\062\000\066\000\067\000\063\000\000\000\064\000\065\000\
\\000\000\000\000\000\000\000\000\066\000\067\000\060\000\061\000\
\\062\000\107\000\000\000\063\000\000\000\064\000\065\000\000\000\
\\000\000\000\000\000\000\066\000\067\000\000\000\000\000\060\000\
\\061\000\062\000\063\000\000\000\064\000\065\000\000\000\000\000\
\\000\000\000\000\066\000\067\000\108\000\060\000\061\000\062\000\
\\000\000\000\000\000\000\063\000\000\000\064\000\065\000\000\000\
\\000\000\000\000\000\000\066\000\067\000\000\000\000\000\000\000\
\\000\000\063\000\000\000\064\000\065\000\000\000\000\000\000\000\
\\000\000\066\000\067\000";

val yycheck = "\021\000\
\\016\001\003\000\047\000\001\000\026\000\014\001\028\000\009\000\
\\007\001\009\001\032\000\036\001\034\000\009\001\014\001\040\001\
\\032\001\021\001\014\001\009\001\024\001\004\001\044\000\016\001\
\\046\000\008\001\009\001\049\000\001\001\002\001\075\000\014\001\
\\035\001\024\001\033\001\018\001\058\000\059\000\060\000\061\000\
\\062\000\063\000\064\000\065\000\066\000\067\000\019\001\010\001\
\\021\001\006\001\007\001\073\000\035\001\036\001\056\000\077\000\
\\016\001\040\001\040\001\004\001\043\001\010\001\006\001\007\001\
\\016\001\024\001\024\001\040\001\024\001\024\001\027\001\028\001\
\\036\001\024\001\024\001\010\001\033\001\034\001\100\000\003\001\
\\016\001\004\001\104\000\105\000\028\001\107\000\108\000\011\001\
\\110\000\033\001\004\001\015\001\016\001\017\001\040\001\117\000\
\\020\001\119\000\022\001\023\001\024\001\040\001\026\001\034\001\
\\004\001\029\001\009\001\031\001\040\001\010\000\043\000\003\001\
\\057\000\037\001\038\001\039\001\040\001\255\255\042\001\011\001\
\\044\001\045\001\255\255\015\001\016\001\017\001\255\255\255\255\
\\020\001\255\255\022\001\023\001\024\001\255\255\026\001\255\255\
\\255\255\029\001\255\255\031\001\255\255\255\255\001\001\002\001\
\\255\255\037\001\038\001\039\001\255\255\255\255\042\001\255\255\
\\044\001\045\001\004\001\005\001\006\001\007\001\008\001\009\001\
\\019\001\255\255\021\001\255\255\014\001\255\255\004\001\005\001\
\\018\001\255\255\008\001\009\001\255\255\255\255\255\255\025\001\
\\014\001\027\001\028\001\255\255\018\001\255\255\255\255\033\001\
\\034\001\035\001\036\001\025\001\255\255\027\001\040\001\255\255\
\\255\255\043\001\255\255\255\255\034\001\035\001\036\001\004\001\
\\005\001\255\255\040\001\008\001\009\001\043\001\255\255\255\255\
\\255\255\014\001\255\255\004\001\005\001\018\001\255\255\008\001\
\\009\001\255\255\255\255\255\255\025\001\014\001\027\001\004\001\
\\005\001\018\001\255\255\008\001\009\001\034\001\035\001\036\001\
\\025\001\014\001\027\001\040\001\255\255\018\001\043\001\255\255\
\\255\255\034\001\035\001\036\001\025\001\255\255\027\001\040\001\
\\255\255\255\255\043\001\255\255\255\255\034\001\035\001\036\001\
\\004\001\005\001\255\255\040\001\008\001\009\001\043\001\255\255\
\\255\255\255\255\014\001\255\255\004\001\005\001\018\001\255\255\
\\008\001\009\001\255\255\255\255\255\255\025\001\014\001\027\001\
\\004\001\005\001\018\001\255\255\008\001\009\001\034\001\035\001\
\\036\001\025\001\014\001\255\255\040\001\255\255\018\001\043\001\
\\255\255\255\255\255\255\035\001\036\001\025\001\255\255\255\255\
\\040\001\255\255\255\255\043\001\255\255\255\255\004\001\035\001\
\\036\001\255\255\008\001\009\001\040\001\255\255\255\255\043\001\
\\014\001\004\001\255\255\004\001\018\001\008\001\009\001\008\001\
\\009\001\255\255\255\255\014\001\255\255\014\001\004\001\018\001\
\\255\255\018\001\008\001\009\001\255\255\035\001\036\001\255\255\
\\014\001\255\255\040\001\255\255\018\001\043\001\255\255\255\255\
\\035\001\036\001\035\001\036\001\255\255\040\001\255\255\040\001\
\\043\001\255\255\043\001\255\255\255\255\035\001\036\001\005\001\
\\006\001\007\001\040\001\255\255\255\255\043\001\255\255\255\255\
\\255\255\255\255\005\001\006\001\007\001\255\255\255\255\255\255\
\\255\255\255\255\255\255\025\001\255\255\027\001\028\001\255\255\
\\005\001\006\001\007\001\033\001\034\001\255\255\025\001\255\255\
\\027\001\028\001\005\001\006\001\007\001\043\001\033\001\034\001\
\\255\255\255\255\255\255\255\255\025\001\040\001\027\001\028\001\
\\005\001\006\001\007\001\255\255\033\001\034\001\025\001\255\255\
\\027\001\028\001\255\255\040\001\255\255\255\255\033\001\034\001\
\\005\001\006\001\007\001\255\255\025\001\040\001\027\001\028\001\
\\255\255\255\255\255\255\255\255\033\001\034\001\005\001\006\001\
\\007\001\255\255\255\255\040\001\025\001\255\255\027\001\028\001\
\\005\001\006\001\007\001\255\255\033\001\034\001\255\255\255\255\
\\255\255\255\255\025\001\040\001\027\001\028\001\005\001\006\001\
\\007\001\255\255\033\001\034\001\025\001\255\255\027\001\028\001\
\\255\255\040\001\255\255\255\255\033\001\034\001\004\001\005\001\
\\006\001\007\001\025\001\040\001\027\001\028\001\255\255\255\255\
\\255\255\255\255\033\001\034\001\035\001\004\001\005\001\006\001\
\\007\001\255\255\255\255\025\001\255\255\027\001\028\001\004\001\
\\005\001\006\001\007\001\033\001\034\001\255\255\255\255\255\255\
\\255\255\255\255\025\001\255\255\027\001\028\001\004\001\005\001\
\\006\001\007\001\033\001\034\001\025\001\255\255\027\001\028\001\
\\255\255\255\255\255\255\255\255\033\001\034\001\005\001\006\001\
\\007\001\008\001\255\255\025\001\255\255\027\001\028\001\255\255\
\\255\255\255\255\255\255\033\001\034\001\255\255\255\255\005\001\
\\006\001\007\001\025\001\255\255\027\001\028\001\255\255\255\255\
\\255\255\255\255\033\001\034\001\018\001\005\001\006\001\007\001\
\\255\255\255\255\255\255\025\001\255\255\027\001\028\001\255\255\
\\255\255\255\255\255\255\033\001\034\001\255\255\255\255\255\255\
\\255\255\025\001\255\255\027\001\028\001\255\255\255\255\255\255\
\\255\255\033\001\034\001";

val yyact = vector_ 47 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 40 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.UnknownTypes.FunDec list
val d__2__ = peekVal 0 : (int*int)
in
( (d__1__) ) end : Fasto.UnknownTypes.Prog))
;
(* Rule 2, file Parser.grm, line 43 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.FunDec
val d__3__ = peekVal 0 : Fasto.UnknownTypes.FunDec list
in
( (d__2__) :: (d__3__) ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 3, file Parser.grm, line 44 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.FunDec
in
( (d__2__) :: [] ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 4, file Parser.grm, line 48 *)
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
(* Rule 5, file Parser.grm, line 50 *)
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
(* Rule 6, file Parser.grm, line 53 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Int ) end : Fasto.Type))
;
(* Rule 7, file Parser.grm, line 54 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Bool ) end : Fasto.Type))
;
(* Rule 8, file Parser.grm, line 55 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Char ) end : Fasto.Type))
;
(* Rule 9, file Parser.grm, line 56 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.Type
val d__3__ = peekVal 0 : (int*int)
in
( Array (d__2__) ) end : Fasto.Type))
;
(* Rule 10, file Parser.grm, line 59 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 3 : Fasto.Type
val d__2__ = peekVal 2 : string*(int*int)
val d__3__ = peekVal 1 : (int*int)
val d__4__ = peekVal 0 : Fasto.Param list
in
( Param (#1 (d__2__), (d__1__)) :: (d__4__) ) end : Fasto.Param list))
;
(* Rule 11, file Parser.grm, line 60 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.Type
val d__2__ = peekVal 0 : string*(int*int)
in
( Param (#1 (d__2__), (d__1__)) :: [] ) end : Fasto.Param list))
;
(* Rule 12, file Parser.grm, line 63 *)
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
(* Rule 13, file Parser.grm, line 72 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Constant (IntVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 14, file Parser.grm, line 73 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : char*(int*int)
in
( Constant (CharVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 15, file Parser.grm, line 74 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Var (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 16, file Parser.grm, line 75 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( StringLit (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 17, file Parser.grm, line 77 *)
val _ = update_ yyact 17
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__3__ = peekVal 0 : (int*int)
in
( ArrayLit ((d__2__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 18, file Parser.grm, line 78 *)
val _ = update_ yyact 18
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Plus ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 19, file Parser.grm, line 79 *)
val _ = update_ yyact 19
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Minus((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 20, file Parser.grm, line 81 *)
val _ = update_ yyact 20
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Times((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 21, file Parser.grm, line 83 *)
val _ = update_ yyact 21
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Divide((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 22, file Parser.grm, line 85 *)
val _ = update_ yyact 22
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Negate((d__2__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 23, file Parser.grm, line 86 *)
val _ = update_ yyact 23
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( And((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 24, file Parser.grm, line 88 *)
val _ = update_ yyact 24
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Or((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 25, file Parser.grm, line 90 *)
val _ = update_ yyact 25
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Equal((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 26, file Parser.grm, line 91 *)
val _ = update_ yyact 26
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Less ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 27, file Parser.grm, line 93 *)
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
(* Rule 28, file Parser.grm, line 95 *)
val _ = update_ yyact 28
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__4__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), (d__3__), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 29, file Parser.grm, line 97 *)
val _ = update_ yyact 29
(fn () => repr(let
val d__1__ = peekVal 2 : string*(int*int)
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), [], #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 30, file Parser.grm, line 100 *)
val _ = update_ yyact 30
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.Type
val d__4__ = peekVal 0 : (int*int)
in
( Read ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 31, file Parser.grm, line 102 *)
val _ = update_ yyact 31
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Write ((d__3__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 32, file Parser.grm, line 104 *)
val _ = update_ yyact 32
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Iota ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 33, file Parser.grm, line 106 *)
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
(* Rule 34, file Parser.grm, line 108 *)
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
(* Rule 35, file Parser.grm, line 110 *)
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
(* Rule 36, file Parser.grm, line 112 *)
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
(* Rule 37, file Parser.grm, line 113 *)
val _ = update_ yyact 37
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 38, file Parser.grm, line 115 *)
val _ = update_ yyact 38
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
(* Rule 39, file Parser.grm, line 117 *)
val _ = update_ yyact 39
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Index (#1 (d__1__), (d__3__), (), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 40, file Parser.grm, line 118 *)
val _ = update_ yyact 40
(fn () => repr(let
val d__1__ = peekVal 0 : bool*(int*int)
in
( Constant ( BoolVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 41, file Parser.grm, line 119 *)
val _ = update_ yyact 41
(fn () => repr(let
val d__1__ = peekVal 0 : bool*(int*int)
in
( Constant ( BoolVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 42, file Parser.grm, line 120 *)
val _ = update_ yyact 42
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Not ( (d__2__), (d__1__) ) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 43, file Parser.grm, line 123 *)
val _ = update_ yyact 43
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp list
in
( (d__1__) :: (d__3__) ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 44, file Parser.grm, line 124 *)
val _ = update_ yyact 44
(fn () => repr(let
val d__1__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( (d__1__) :: [] ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 45, file Parser.grm, line 127 *)
val _ = update_ yyact 45
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( FunName (#1 (d__1__)) ) end : Fasto.UnknownTypes.FunArg))
;
(* Entry Prog *)
val _ = update_ yyact 46 (fn () => raise yyexit (peekVal 0));
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
