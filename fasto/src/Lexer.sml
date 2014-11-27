local open Obj Lexing in


  (* A lexer definition for Fasto, for use with mosmllex. *)

  (* boilerplate code for all lexer files... *)

 open Lexing;

 exception Error of string * (int * int) (* (message, (line, column)) *)

 val currentLine = ref 1
 val lineStartPos = ref [0]

 fun resetPos () = (currentLine :=1; lineStartPos := [0])

 fun getPos lexbuf = getLineCol (getLexemeStart lexbuf)
        (!currentLine)
        (!lineStartPos)

 and getLineCol pos line (p1::ps) =
       if pos>=p1 then (line, pos-p1)
       else getLineCol pos (line-1) ps
   | getLineCol pos line [] = raise Error ("",(0,0))

 fun lexerError lexbuf s =
     raise Error (s, getPos lexbuf)

(* This one is language specific, yet very common. Alternative would
   be to encode every keyword as a regexp. This one is much easier. *)
 fun keyword (s, pos) =
     case s of
         "if"           => Parser.IF pos
       | "then"         => Parser.THEN pos
       | "else"         => Parser.ELSE pos
       | "let"          => Parser.LET pos
       | "in"           => Parser.IN pos
       | "int"          => Parser.INT pos
       | "bool"         => Parser.BOOL pos
       | "char"         => Parser.CHAR pos
       | "fun"          => Parser.FUN pos

(* specials: *)
       | "not"          => Parser.HANSNOTTO pos
       | "iota"         => Parser.IOTA pos
       | "replicate"    => Parser.REPLICATE pos
       | "map"          => Parser.MAP pos
       | "reduce"       => Parser.REDUCE pos
       | "filter"       => Parser.FILTER pos
       | "scan"         => Parser.SCAN pos
       | "read"         => Parser.READ pos
       | "write"        => Parser.WRITE pos
       | "op"           => Parser.OP pos
       | _              => Parser.ID (s, pos)

 
fun action_26 lexbuf = (
 lexerError lexbuf "Illegal symbol in input" )
and action_25 lexbuf = (
 Parser.EOF (getPos lexbuf) )
and action_24 lexbuf = (
 Parser.COMMA (getPos lexbuf) )
and action_23 lexbuf = (
 Parser.RCURLY (getPos lexbuf) )
and action_22 lexbuf = (
 Parser.LCURLY (getPos lexbuf) )
and action_21 lexbuf = (
 Parser.RBRACKET (getPos lexbuf) )
and action_20 lexbuf = (
 Parser.LBRACKET (getPos lexbuf) )
and action_19 lexbuf = (
 Parser.RPAR   (getPos lexbuf) )
and action_18 lexbuf = (
 Parser.LPAR   (getPos lexbuf) )
and action_17 lexbuf = (
 Parser.ORBITER (getPos lexbuf) )
and action_16 lexbuf = (
 Parser.LTH    (getPos lexbuf) )
and action_15 lexbuf = (
 Parser.EQ     (getPos lexbuf) )
and action_14 lexbuf = (
 Parser.DEQ    (getPos lexbuf) )
and action_13 lexbuf = (
 Parser.NEGROMANCER (getPos lexbuf) )
and action_12 lexbuf = (
 Parser.DIVERGENT (getPos lexbuf) )
and action_11 lexbuf = (
 Parser.MULIFICENT (getPos lexbuf) )
and action_10 lexbuf = (
 Parser.MINUS  (getPos lexbuf) )
and action_9 lexbuf = (
 Parser.PLUS   (getPos lexbuf) )
and action_8 lexbuf = (
 Parser.STRINGLIT
			    ((case String.fromCString (getLexeme lexbuf) of
			       NONE => lexerError lexbuf "Bad string constant"
			     | SOME s => String.substring(s,1,
							  String.size s - 2)),
			     getPos lexbuf) )
and action_7 lexbuf = (
 Parser.CHARLIT
        ((case String.fromCString (getLexeme lexbuf) of
             NONE => lexerError lexbuf "Bad char constant"
           | SOME s => String.sub(s,1)),
           getPos lexbuf) )
and action_6 lexbuf = (
 keyword (getLexeme lexbuf,getPos lexbuf) )
and action_5 lexbuf = (
 case Bool.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "Bad bool"
                             | SOME b => Parser.FALSE (b, getPos lexbuf) )
and action_4 lexbuf = (
 case Bool.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "Bad bool"
                             | SOME b => Parser.TRUE (b, getPos lexbuf) )
and action_3 lexbuf = (
 case Int.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "Bad integer"
                             | SOME i => Parser.NUM (i, getPos lexbuf) )
and action_2 lexbuf = (
 currentLine := !currentLine+1;
                          lineStartPos :=  getLexemeStart lexbuf
                           :: !lineStartPos;
                          Token lexbuf )
and action_1 lexbuf = (
 Token lexbuf )
and action_0 lexbuf = (
 Token lexbuf )
and state_0 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"G" andalso currChar <= #"S" then  state_18 lexbuf
 else if currChar >= #"U" andalso currChar <= #"Z" then  state_18 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_18 lexbuf
 else if currChar >= #"0" andalso currChar <= #"9" then  state_15 lexbuf
 else case currChar of
    #"E" => state_18 lexbuf
 |  #"D" => state_18 lexbuf
 |  #"C" => state_18 lexbuf
 |  #"B" => state_18 lexbuf
 |  #"A" => state_18 lexbuf
 |  #"\t" => state_3 lexbuf
 |  #"\r" => state_3 lexbuf
 |  #" " => state_3 lexbuf
 |  #"\n" => action_2 lexbuf
 |  #"\f" => action_2 lexbuf
 |  #"~" => action_13 lexbuf
 |  #"}" => action_23 lexbuf
 |  #"{" => action_22 lexbuf
 |  #"]" => action_21 lexbuf
 |  #"[" => action_20 lexbuf
 |  #"T" => state_20 lexbuf
 |  #"F" => state_19 lexbuf
 |  #"=" => state_17 lexbuf
 |  #"<" => action_16 lexbuf
 |  #"/" => state_14 lexbuf
 |  #"-" => action_10 lexbuf
 |  #"," => action_24 lexbuf
 |  #"+" => action_9 lexbuf
 |  #"*" => action_11 lexbuf
 |  #")" => action_19 lexbuf
 |  #"(" => action_18 lexbuf
 |  #"'" => state_7 lexbuf
 |  #"&" => state_6 lexbuf
 |  #"\"" => state_5 lexbuf
 |  #"\^@" => action_25 lexbuf
 |  _ => action_26 lexbuf
 end)
and state_3 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_0);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\t" => state_44 lexbuf
 |  #"\r" => state_44 lexbuf
 |  #" " => state_44 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_5 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_26);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_41 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_41 lexbuf
 else case currChar of
    #"!" => state_41 lexbuf
 |  #" " => state_41 lexbuf
 |  #"&" => state_41 lexbuf
 |  #"%" => state_41 lexbuf
 |  #"$" => state_41 lexbuf
 |  #"#" => state_41 lexbuf
 |  #"\\" => state_43 lexbuf
 |  #"\"" => action_8 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_6 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_26);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"&" => action_17 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_7 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_26);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_37 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_37 lexbuf
 else case currChar of
    #"!" => state_37 lexbuf
 |  #" " => state_37 lexbuf
 |  #"&" => state_37 lexbuf
 |  #"%" => state_37 lexbuf
 |  #"$" => state_37 lexbuf
 |  #"#" => state_37 lexbuf
 |  #"\\" => state_38 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_14 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_12);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"/" => state_36 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_15 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_3);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_35 lexbuf
 else backtrack lexbuf
 end)
and state_17 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_15);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_14 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_18 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_19 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"b" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"a" => state_30 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_20 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"q" then  state_26 lexbuf
 else if currChar >= #"s" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"r" => state_27 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_26 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_27 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"t" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"z" => state_26 lexbuf
 |  #"y" => state_26 lexbuf
 |  #"x" => state_26 lexbuf
 |  #"w" => state_26 lexbuf
 |  #"v" => state_26 lexbuf
 |  #"u" => state_28 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_28 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"f" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"d" => state_26 lexbuf
 |  #"c" => state_26 lexbuf
 |  #"b" => state_26 lexbuf
 |  #"a" => state_26 lexbuf
 |  #"e" => state_29 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_29 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_30 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"k" then  state_26 lexbuf
 else if currChar >= #"m" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"l" => state_31 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_31 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"r" then  state_26 lexbuf
 else if currChar >= #"t" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"s" => state_32 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_32 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"f" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  #"d" => state_26 lexbuf
 |  #"c" => state_26 lexbuf
 |  #"b" => state_26 lexbuf
 |  #"a" => state_26 lexbuf
 |  #"e" => state_33 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_33 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_5);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_26 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_26 lexbuf
 else case currChar of
    #"_" => state_26 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_35 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_3);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_35 lexbuf
 else backtrack lexbuf
 end)
and state_36 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_1);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\^@" => backtrack lexbuf
 |  #"\n" => backtrack lexbuf
 |  _ => state_36 lexbuf
 end)
and state_37 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"'" => action_7 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_38 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #" " andalso currChar <= #"~" then  state_37 lexbuf
 else backtrack lexbuf
 end)
and state_41 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_41 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_41 lexbuf
 else case currChar of
    #"!" => state_41 lexbuf
 |  #" " => state_41 lexbuf
 |  #"&" => state_41 lexbuf
 |  #"%" => state_41 lexbuf
 |  #"$" => state_41 lexbuf
 |  #"#" => state_41 lexbuf
 |  #"\\" => state_43 lexbuf
 |  #"\"" => action_8 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_43 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #" " andalso currChar <= #"~" then  state_41 lexbuf
 else backtrack lexbuf
 end)
and state_44 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_0);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\t" => state_44 lexbuf
 |  #"\r" => state_44 lexbuf
 |  #" " => state_44 lexbuf
 |  _ => backtrack lexbuf
 end)
and Token lexbuf =
  (setLexLastAction lexbuf (magic dummyAction);
   setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_0 lexbuf)

(* The following checks type consistency of actions *)
val _ = fn _ => [action_26, action_25, action_24, action_23, action_22, action_21, action_20, action_19, action_18, action_17, action_16, action_15, action_14, action_13, action_12, action_11, action_10, action_9, action_8, action_7, action_6, action_5, action_4, action_3, action_2, action_1, action_0];

end
