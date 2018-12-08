
(* The type of tokens. *)

type token = 
  | STRING of (string)
  | SEMI
  | RPAREN
  | NEWLINE
  | LPAREN
  | EOF
  | COMMA
  | CAND of (char)

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> ((char * char * (string * string)) list list)
