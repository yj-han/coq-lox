Require Import ZArith.
Require Import Floats.

Require Import String.
Require Import BinaryString.
Require Import DecimalString.

Require Import Ascii.
Require Import List.

Require Import Token.
Require Import Expr.

Definition concat (exprs: list expr) :=
  fold_left (fun e => " " ++ (to_string e)) exprs.

Definition parenthesize (name: string) (exprs: list expr) :=
  "(" ++ name ++ (concat exprs) ++ ")".

Fixpoint to_string (e: expr) :=
  match e with
  | assign name value =>
  | binop (lhs : expr) (op : token) (rhs : expr)
  | function_call (callee : expr) (args : list expr)
  | get (obj : expr) (name : token)
  | grouping (expr : expr)
  | literal (val : token)
  | logical (lhs : expr) (op : token) (right : expr)
  | set (obj : expr) (name : token) (val : expr)
  | super (method : token)
  | this => "this"
  | unop (op : token) (rhs : expr) =>
  | variable (name : token) =>


Definition print_ast (visitor: Visitor T)
