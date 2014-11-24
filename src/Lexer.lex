{
open Lexing;

exception Error of string;

}

rule Token = parse
  	[`A`-`Z` `a`-`z`]+ | `_` [`A`-`Z` `a`-`z` `0`-`9` `_`]*  { Parser.VAR(getLexeme lexbuf) } (* Matches for variable names with no underscores and number, or with underscores and numbers, as long as the variable begins with one *)
	|	[`\n` ` ` `\t` `\r`]+ { Token lexbuf } (* ignores whitespace *)
	| "//" [^`\n`]* { Token lexbuf } (* ignores comments *)
	| `+`		{Parser.OR}
	| `*`		{Parser.AND}
	| "=>"	{Parser.IMP}
	| `~`		{Parser.NOT}
	| `@`		{Parser.FORALL}
	| `#`		{Parser.EXIST}
	| `(`		{Parser.LPAR}
	| `)`		{Parser.RPAR}
	| `.`		{Parser.DOT}
  | `1`		{Parser.TRUE}
  | `0`   { Parser.FALSE }
  | eof   { Parser.EOF }
  | _     { raise Error "Unexpected symbol on input." }
;
