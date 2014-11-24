(* The FEIEF compiler main. *)

structure FEIEFC = struct

(*

This is the main program for FEIEF that will be turned into an executable. It
ties together all the compiler modules.

You probably want to build the entire compiler by typing 'make' on *nix, or by
running 'make.bat' on Windows. This produces and executable feief (or
feief.exe) in the sibling bin directory.

If you execute feief, you will be prompted to enter a FEIEF program.  Signal
the end of input by typing Ctrl-D, indicating an end of file. The program will
then attempt to parse the program and pretty print the resulting abstract
syntax tree. For instance,

$ ../bin/feief
0 *0 
*0
(Ctrl-D)
( ( 0 * 0 ) * 0 )

*)

fun parseString s =
  Parser.Prog Lexer.Token (Lexing.createLexerString s)

val _ =
  let
    val s = TextIO.inputAll TextIO.stdIn
  in
    ( TextIO.output (TextIO.stdOut, FEIEF.ppProg (parseString s) ^ "\n")
    ; TextIO.flushOut (TextIO.stdOut)
    )
  end

end
