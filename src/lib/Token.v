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

Definition tt_eq_dec:
  forall (x y: token_type), { x = y } + { x <> y }.
Proof.
  decide equality.
Defined.

Definition teq (x y: token_type) :=
  if (tt_eq_dec x y) then true else false.

Record token : Type := mktoken {
  t_type: token_type;
  t_lexeme: string;
  t_literal: option object;
  t_line: nat;
  t_id: nat
}.
