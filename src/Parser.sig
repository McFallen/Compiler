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

val Prog :
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> FEIEF.Expr;
