(* Types and utilities for the abstract syntax of FEIEF. *)

(* FEIEF Er Ikke En Forkortelse, men til gengæld et palindrom *)

structure FEIEF = struct

(*

The abstract syntax of a (FEIEF) program is a representation of the (FEIEF)
program in terms of a data type in another programming language (SML).

This module also provides pretty printing functionality, printing a valid FEIEF
program given its abstract syntax. "pp" is used in this module as a shorthand
for "prettyPrint".

Before use, this module has to be compiled with mosmlc. It is instructive to
subsequently try out the following in your Moscow ML interpreter:

- load "FEIEF";
...
- open FEIEF;
...
- ppProg (Forall ("x", (Exists ("y", (Or (Var "x", Var "y"))))));
> val it = "@x.#y.( x + y )" : string

*)

type Var = string

datatype Expr
  = Or of Expr * Expr
  | And of Expr * Expr
  | Implies of Expr * Expr
  | Not of Expr
  | Forall of Var * Expr
  | Exists of Var * Expr
  | Var of Var
  | False
  | True

type Prog = Expr

fun ppExpr (Or (e0, e1)) = "( " ^ ppExpr e0 ^ " + " ^ ppExpr e1 ^ " )"
  | ppExpr (And (e0, e1)) = "( " ^ ppExpr e0 ^ " * " ^ ppExpr e1 ^ " )"
  | ppExpr (Implies (e0, e1)) = "( " ^ ppExpr e0 ^ " => " ^ ppExpr e1 ^ " )"
  | ppExpr (Not e) = "~" ^ ppExpr e
  | ppExpr (Forall (v,e)) = "@" ^ v ^ "." ^ ppExpr e
  | ppExpr (Exists (v,e)) = "#" ^ v ^ "." ^ ppExpr e
  | ppExpr (Var v) = v
  | ppExpr False = "0"
  | ppExpr True = "1"

fun ppProg (p : Prog) = ppExpr p

end
