type token =
  | VAR of (string)
  | IMPL
  | AND
  | OR
  | NOT
  | OPEN
  | CLOSE
  | EOF
  | COMMA
  | INTO
  | PROOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree
