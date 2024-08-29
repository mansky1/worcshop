type binary_operator =
  | ADD
  | SUB
  | MUL
  | DIV
  | MOD
  | CONS
  | APPEND
  | SEPIMP
  | AND

type unary_operator = MINUS | NOT

type relation_operator = EQ | NE | GE | LE | GT | LT

type expression =
  | UNARY of unary_operator * expression
  | BINARY of binary_operator * expression * expression
  | FUNCAPP of string * expression list
  | CONSTANT of int
  | VARIABLE of string
  | FORALL of string list * expression
  | EXISTS of string list * expression
  | RELATION of relation_operator * expression * expression
  | TUPLE of expression list
