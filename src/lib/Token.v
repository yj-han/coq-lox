Require Import Floats.
Require Import String.
Require Import ZArith.

Variant token_type :=
  (* Single-character tokens *)
  | tk_left_paren
  | tk_right_paren
  | tk_left_brace
  | tk_right_brace
  | tk_comma
  | tk_dot
  | tk_minus
  | tk_plus
  | tk_semi_colon
  | tk_slash
  | tk_star
  (* One or two character tokens *)
  | tk_bang
  | tk_bang_eq
  | tk_eq
  | tk_eq_eq
  | tk_gt
  | tk_ge
  | tk_lt
  | tk_le
  (* Literals *)
  | tk_identifier (id: string)
  | tk_string (s: string)
  | tk_int (z: Z)
  | tk_float (f: float)
  (* Keywords *)
  | tk_and
  | tk_class
  | tk_else
  | tk_false
  | tk_fun
  | tk_for
  | tk_if
  | tk_nil
  | tk_or
  | tk_print
  | tk_ret
  | tk_super
  | tk_this
  | tk_true
  | tk_var
  | tk_while
  | tk_eof
  | tk_undef
.


Definition eqb (t1 t2 : token_type) : bool :=
  match t1, t2 with
  | tk_left_paren, tk_left_paren
  | tk_right_paren, tk_right_paren
  | tk_left_brace, tk_left_brace
  | tk_right_brace, tk_right_brace
  | tk_comma, tk_comma
  | tk_dot, tk_dot
  | tk_minus, tk_minus
  | tk_plus, tk_plus
  | tk_semi_colon, tk_semi_colon
  | tk_slash, tk_slash
  | tk_star, tk_star
  (* One or two character tokens *)
  | tk_bang, tk_bang
  | tk_bang_eq, tk_bang_eq
  | tk_eq, tk_eq
  | tk_eq_eq, tk_eq_eq
  | tk_gt, tk_gt
  | tk_ge, tk_ge
  | tk_lt, tk_lt
  | tk_le, tk_le => true
  (* Literals *)
  | tk_identifier id1, tk_identifier id2 => String.eqb id1 id2
  | tk_string s1, tk_string s2 => String.eqb s1 s2
  | tk_int z1, tk_int z2 => Z.eqb z1 z2
  | tk_float f1, tk_float f2 => PrimFloat.eqb f1 f2
  (* Keywords *)
  | tk_and, tk_and
  | tk_class, tk_class
  | tk_else, tk_else
  | tk_false, tk_false
  | tk_fun, tk_fun
  | tk_for, tk_for
  | tk_if, tk_if
  | tk_nil, tk_nil
  | tk_or, tk_or
  | tk_print, tk_print
  | tk_ret, tk_ret
  | tk_super, tk_super
  | tk_this, tk_this
  | tk_true, tk_true
  | tk_var, tk_var
  | tk_while, tk_while
  | tk_eof, tk_eof
  | tk_undef, tk_undef => true
  | _, _ => false
  end.   

Record token :=
  mkToken {
      type: token_type;
      line: nat;
    }.

Definition make_token (type: token_type) (line: nat): token :=
  {| type := type; line := line; |}.
