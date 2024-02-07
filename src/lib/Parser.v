Require Import String.

Require Import Extlib.Data.Monads.StateMonad.

Require Import Object.
Require Import Token.
Require Import Expr.
Require Import Stmt.

Definition parse_error: Type := token * string.

Record parser_state: Type := mkps {
  tokens: list token;
  current: nat;
  errors: list parse_error
}.

Definition parser: Type :=
