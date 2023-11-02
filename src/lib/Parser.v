Require Import ZArith.
Require Import Floats.

Require Import String.
Require Import BinaryString.
Require Import DecimalString.

Require Import Ascii.
Require Import List.

Require Import Token.
Require Import Expr.

Definition peek (tokens : list token) (current : nat) : token.
Proof. Admitted.

Definition prev (tokens : list token) (current : nat) : token.
Proof. Admitted.

Definition advance (tokens : list token) (current : nat) : (token * nat).
Proof. Admitted.

Definition check (tokens : list token) (current : nat) (ttype : token_type) :=
  let token := peek tokens current in
  Token.eqb token.(type) ttype.


Definition match_token_types (tk_types : list token_type) (tk_type : token_type) :=
  existsb (Token.eqb tk_type) tk_types.


Module ParseError.
  
End ParseError.

Definition parse_expr_assign (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_binop (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_call (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_get (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_grouping (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_literal (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_logical (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_set (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_super (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_unop (tokens : list token) : expr.
Proof. Admitted.
Definition parse_expr_var (tokens : list token) : expr.
Proof. Admitted.


Definition parse_stmt_for (tokens : list token) : stmt.
Proof. Admitted.
Definition parse_stmt_ite (tokens : list token) : stmt.
Proof. Admitted.
Definition parse_stmt_print (token : list token) : stmt.
Proof. Admitted.
Definition parse_stmt_ret (tokens : list token) : stmt.
Proof. Admitted.
Definition parse_stmt_while (tokens : list token) : stmt.
Proof. Admitted.
Definition parse_stmt_block (tokens : list token) : stmt.
Proof. Admitted.
Definition parse_stmt_expr (tokens : list token) : stmt.
Proof. Admitted.

Fixpoint parse_stmt (tokens : list token) : stmt.
Proof. Admitted.

Definition parse_function (tokens : list token) : stmt.
Proof. Admitted.

Definition parse_class (tokens : list token) : stmt.
Proof. Admitted.

Definition parse_declaration (tokens : list token) : stmt.
Proof. Admitted.

Definition parse (tokens : list token) : list stmt.
Proof. Admitted.

