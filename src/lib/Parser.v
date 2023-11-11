Require Import ZArith.
Require Import Floats.

Require Import String.
Require Import BinaryString.
Require Import DecimalString.

Require Import Ascii.
Require Import List.

Require Import Token.
Require Import Expr.

Variant err_type :=
  | invalid_params
  | unexpected
  | left_brace_expected
.

Inductive parse_result :=
| syntax_err (e : err_type)
| expr_terminated (expr : expr) (rest : list token)
| param_terminated (params : list token) (rest : list token)
| stmt_terminated (stmts : list stmt) (rest : list token)
| terminated
.

Definition bind_stmt (val : stmt) (onto : parse_result) :=
  match onto with
  | syntax_err e => syntax_err e
  | expr_terminated _ _ => syntax_err unexpected
  | param_terminated _ _ => syntax_err unexpected
  | stmt_terminated stmts rest => stmt_terminated (cons val stmts) rest
  | terminated => stmt_terminated (cons val nil) nil
  end.

Definition bind_param (val : token) (onto : parse_result) :=
  match onto with
  | syntax_err e => syntax_err e
  | expr_terminated _ _ => syntax_err unexpected
  | param_terminated params rest => param_terminated (cons val params) rest
  | stmt_terminated _ _ => syntax_err unexpected
  | terminated => param_terminated (cons val nil) nil
  end.

Fixpoint parse_params_rec
  (tokens : list token)
  : parse_result :=
  match tokens with
  | tk_right_brace :: tl => param_terminated nil tl
  | (tk_identifier _ as param) :: tl => bind_param param (parse_params_rec tl)
  | _ => syntax_err invalid_params
  end.

Fixpoint parse_expression_rec
  (steps : nat)
  (tokens : list token)
  : parse_result :=
  match steps with
  | O => terminated
  | S n =>
      match tokens with
      | nil => syntax_err unexpected
      | (tk_false as val) :: tl
      | (tk_true as val) :: tl
      | (tk_nil as val) :: tl
      | (tk_identifier _ as val) :: tl
      | (tk_string _ as val) :: tl
      | (tk_int _ as val) :: tl
      | (tk_float _ as val) :: tl => expr_terminated (literal val) tl
      | tk_super :: tk_dot :: (tk_identifier _ as method) :: tl =>
          expr_terminated ( super method) tl
      | tk_this :: tl => expr_terminated this tl
      | (tk_identifier _ as name) :: tl => expr_terminated (variable name) tl
      | tk_left_paren :: tl =>
          match parse_expression_rec n tl with
          | syntax_err e => syntax_err e
          | expr_terminated group (tk_right_paren :: rest) =>
              expr_terminated (grouping group) rest
          | _  => syntax_err unexpected
          end
      | _ => syntax_err unexpected
      end
  end.
    
    
    
(* steps variable is a decreasing argument of this fixpoint definition *)
Fixpoint parse_rec
  (steps : nat)
  (tokens : list token)
  : parse_result :=
  match steps with
  | 0 => stmt_terminated nil tokens
  | S n =>
      match tokens with
      | nil => stmt_terminated nil nil
      (* Class Statement *)
      | tk_class :: tl =>
          match tl with
          | (tk_identifier _ as name)
              :: tk_lt
              :: (tk_identifier _ as superclass)
              :: tk_left_brace :: tl =>
              match parse_rec n tl with
              | syntax_err e => syntax_err e
              | param_terminated _ _ => syntax_err unexpected
              | stmt_terminated stmts rest =>
                  let class_stmt := class name (Some (variable superclass)) stmts in
                  bind_stmt class_stmt (parse_rec n rest)
              end
          | (tk_identifier _ as name)
              :: tk_left_paren :: tl =>
              match parse_params_rec tl with
              | syntax_err e => syntax_err e
              | param_terminated _ _ => syntax_err unexpected
              | stmt_terminated stmts rest =>
                  let class_stmt := class name None stmts in
                  bind_stmt class_stmt (parse_rec n rest)
              end
          | _ => syntax_err unexpected
          end
      (* Function Statement *)
      | tk_fun :: (tk_identifier id as name) :: tk_left_brace :: tl =>
          match parse_params_rec tl with
          | syntax_err e => syntax_err e
          | expr_terminated _ _ => syntax_err unexpected
          | param_terminated params tl =>
              match tl with
              | tk_left_brace :: tl =>
                  match parse_rec n tl with
                  | syntax_err e => syntax_err e
                  | expr_terminated _ _ => syntax_err unexpected
                  | param_terminated _ _ => syntax_err unexpected
                  | stmt_terminated stmts rest =>
                      let function_stmt := function name params stmts in
                      bind_stmt function_stmt (parse_rec n rest)
                  end
              | _ => syntax_err left_brace_expected
              end
          | stmt_terminated stmts rest => syntax_err unexpected
          end
      | tk_var :: (tk_identifier id as name) :: tk_eq :: tl =>
          match parse_expression_rec n tl with
          | syntax_err e => syntax_err e
          | expr_terminated initializer rest =>
              bind_stmt (var name initializer) (parse_rec n rest)
          | param_terminated _ _ => syntax_err unexpected
          | stmt_terminated _ _ => syntax_err unexpected
          end            
      | _ => syntax_err unexpected
      end
  end.

    (* | tk_for :: tl => Err syntax_err  *)
    (* | tk_if :: tl => Err syntax_err *)
    (* | tk_print :: tl => Err syntax_err *)
    (* | tk_ret :: tl => Err syntax_err *)
    (* | tk_while :: tl => Err syntax_err  *)
    (* | tk_left_brace :: tl => parse_rec tl in_stmt *)
    (* | _ => Err syntax_err *)
    (* end. *)


Definition parse (tokens : list token) : result (list stmt).
Proof. Admitted.
