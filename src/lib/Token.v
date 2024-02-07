Require Import Object.
Require Import String.
Require Import ZArith.

Variant token_type :=
  (* Single-character tokens *)
  | LEFT_PAREN
  | RIGHT_PAREN
  | LEFT_BRACE
  | RIGHT_BRACE
  | COMMA
  | DOT
  | MINUS
  | PLUS
  | SEMICOLON
  | SLASH
  | STAR
  (* One or two character tokens *)
  | BANG
  | BANG_EQUAL
  | EQUAL
  | EQUAL_EQUAL
  | GREATER
  | GREATER_EQUAL
  | LESS
  | LESS_EQUAL
  (* Literals *)
  | IDENTIFIER
  | STRING
  | NUMBER
  (* Keywords *)
  | AND
  | CLASS
  | ELSE
  | FALSE
  | FUN
  | FOR
  | IF
  | NIL
  | OR
  | PRINT
  | RET
  | SUPER
  | THIS
  | TRUE
  | VAR
  | WHILE
  | EOF
  | WS
.

Record token : Type := mktoken {
  t_type: token_type;
  t_lexeme: string;
  t_literal: option object;
  t_line: nat;
  t_id: nat
}.
