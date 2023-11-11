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
| syntax_err (msg : string)
| expr_terminated (expr : expr) (tl : list token)
| exprs_terminated (args : list expr) (tl : list token)
| params_terminated (params : list token) (tl : list token)
| stmt_terminated (stmts : list stmt) (tl : list token)
| terminated
.

Definition bind_error
  (prev : parse_result)
  (cur_error : parse_result) :=
  match prev with
  | syntax_err msg => prev
  | _ => cur_error
  end.

Definition propagate_error (result : parse_result) :=
  bind_error result (syntax_err "Unexpected Error").

Definition bind_param (val : token) (onto : parse_result) :=
  match onto with
  | params_terminated params tl => params_terminated (cons val params) tl
  | terminated => params_terminated (cons val nil) nil
  | _ => propagate_error onto
  end.

Definition bind_expr (val : expr) (onto : parse_result) :=
  match onto with
  | exprs_terminated exprs tl => exprs_terminated (cons val exprs) tl
  | terminated => exprs_terminated (cons val nil) nil
  | _ => propagate_error onto
  end.

Definition bind_stmt (val : stmt) (onto : parse_result) :=
  match onto with
  | stmt_terminated stmts tl => stmt_terminated (cons val stmts) tl
  | terminated => stmt_terminated (cons val nil) nil
  | _ => propagate_error onto
  end.

Fixpoint parse_params_rec
  (tokens : list token)
  : parse_result :=
  match tokens with
  | tk_right_brace :: tl => params_terminated nil tl
  | (tk_identifier _ as param) :: tl => bind_param param (parse_params_rec tl)
  | _ => syntax_err "Expected a parameter"
  end.

Definition left_bind (expr1 : expr) (op : token) (result : parse_result) :=
  match result with
  | expr_terminated expr tl => expr_terminated (binop expr1 op expr) tl
  | other => bind_error other (syntax_err "Expected an expression")
  end.

Fixpoint parse_expr (steps : nat) (tokens : list token) : parse_result :=
  match steps with
  | O => terminated
  | S n =>
      match tokens with
      | nil => terminated
      | _ => match or n tokens with
            | expr_terminated expr (tk_eq :: tl) =>
                match parse_expr n tl with
                | expr_terminated value tl =>
                    match expr with
                    | variable name => expr_terminated (assign name value) tl
                    | get obj name => expr_terminated (set obj name value) tl
                    | _ => syntax_err "Invalid assignment target"
                    end
                | other => bind_error other (syntax_err "Invalid assignment target")
                end
            | expr_terminated expr tl => expr_terminated expr tl
            | other => bind_error other (syntax_err "Expected an expression")
            end
      end
  end
with primary (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n =>
           match tokens with
           | nil => terminated
           | (tk_false as val) :: tl
           | (tk_true as val) :: tl
           | (tk_nil as val) :: tl
           | (tk_string _ as val) :: tl
           | (tk_int _ as val) :: tl
           | (tk_float _ as val) :: tl => expr_terminated (literal val) tl
           | tk_super :: tk_dot :: (tk_identifier _ as method) :: tl
             => expr_terminated (super method) tl
           | tk_this :: tl => expr_terminated this tl
           | (tk_identifier _ as name) :: tl => expr_terminated (variable name) tl
           | tk_left_paren :: tl =>
               match parse_expr n tl with
               | expr_terminated group (tk_right_paren :: tl) => expr_terminated (grouping group) tl
               | other => bind_error other (syntax_err "Expected an expression")
               end
           | _ => syntax_err "Unexpected Error"
           end
       end
with call (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => syntax_err "Reached the maximum step"
       | S n =>
           match primary n tokens with
           | expr_terminated obj (tk_left_paren :: tl) =>
               match finish_call n tl with
               | exprs_terminated args tl => expr_terminated (function_call obj args) tl
               | other => bind_error other (syntax_err "Expected arguments")
               end

           | expr_terminated obj (tk_dot :: (tk_identifier _ as name) :: tl) =>
               expr_terminated (get obj name) tl
           | expr_terminated obj tl => expr_terminated obj tl
           | other => bind_error other (syntax_err "Expected an expression")
           end
       end
with finish_call (steps : nat) (tokens : list token) : parse_result :=
  match steps with
  | O => syntax_err "Reached the maximum step"
  | S n =>
      match tokens with
      | tk_right_paren :: tl => exprs_terminated nil tl
      | _ =>
          match parse_expr n tokens with
          | expr_terminated arg tl =>
              match tl with
              | tk_comma :: tl => bind_expr arg (finish_call n tl)
              | tk_right_paren :: tl => exprs_terminated (arg :: nil) tl
              | _ => syntax_err "Expected ')' after arguments"
              end
          | other => bind_error other (syntax_err "Expected an argument")
          end
      end
  end
with unary (steps : nat) (tokens : list token) : parse_result :=
  match steps with
  | O => syntax_err "Reached the maximum step"
  | S n =>
      match tokens with
      | (tk_bang as op) :: tl
      | (tk_minus as op) :: tl =>
          match unary n tl with
          | expr_terminated rhs tl => expr_terminated (unop op rhs) tl
          | other => bind_error other (syntax_err "Expected an expression")
          end
      | _ => call n tokens
      end
  end
with factor (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n => let ops := tk_star :: tk_slash :: nil in
               match unary n tokens with
               | expr_terminated lhs tl =>
                   match tl with
                   | nil => expr_terminated lhs tl
                   | op :: tl =>
                       if existsb (eqb op) ops then
                         match unary n tl with
                         | expr_terminated rhs (cons op tl) =>
                             if existsb (eqb op) tl then
                               left_bind (binop lhs op rhs) op (factor n tl)
                             else
                               expr_terminated (binop lhs op rhs) tl
                         | other => bind_error other (syntax_err "Expected an expression")
                         end
                       else expr_terminated lhs tl
                   end
               | other => bind_error other (syntax_err "Expected an expression")
               end
       end
with term (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n => let ops := tk_plus :: tk_minus :: nil in
               match factor n tokens with
               | expr_terminated lhs tl =>
                   match tl with
                   | nil => expr_terminated lhs tl
                   | op :: tl =>
                       if existsb (eqb op) ops then
                         match factor n tl with
                         | expr_terminated rhs (cons op tl) =>
                             if existsb (eqb op) tl then
                               left_bind (binop lhs op rhs) op (term n tl)
                             else
                               expr_terminated (binop lhs op rhs) tl
                         | other => bind_error other (syntax_err "Expected an expression")
                         end
                       else expr_terminated lhs tl
                   end
               | other => bind_error other (syntax_err "Expected an expression")
               end
       end
with comparison (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n => let ops := tk_gt :: tk_ge :: tk_lt :: tk_le :: nil in
           match term n tokens with
           | expr_terminated lhs tl =>
               match tl with
               | nil => expr_terminated lhs tl
               | op :: tl =>
                   if existsb (eqb op) ops then
                     match term n tl with
                     | expr_terminated rhs (cons op tl) =>
                         if existsb (eqb op) tl then
                           left_bind (binop lhs op rhs) op (comparison n tl)
                         else
                           expr_terminated (binop lhs op rhs) tl
                     | other => bind_error other (syntax_err "Expected an expression")
                     end
                   else expr_terminated lhs tl
               end
           | other => bind_error other (syntax_err "Expected an expression")
           end
       end
with equality (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n =>
           let ops := tk_bang_eq :: tk_eq_eq :: nil in
           match comparison n tokens with
           | expr_terminated lhs tl =>
               match tl with
               | nil => expr_terminated lhs tl
               | op :: tl =>
                   if existsb (eqb op) ops then
                     match comparison n tl with
                     | expr_terminated rhs (cons op tl) =>
                         if existsb (eqb op) tl then
                           left_bind (binop lhs op rhs) op (equality n tl)
                         else
                           expr_terminated (binop lhs op rhs) tl
                     | other => bind_error other (syntax_err "Expected an expression")
                     end
                   else expr_terminated lhs tl
               end
           | other => bind_error other (syntax_err "Expected an expression")
           end
       end
with and (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n =>
           let ops := tk_and :: nil in
           match equality n tokens with
           | expr_terminated lhs tl =>
               match tl with
               | nil => expr_terminated lhs tl
               | op :: tl =>
                   if existsb (eqb op) ops then
                     match equality n tl with
                     | expr_terminated rhs (cons op tl) =>
                         if existsb (eqb op) tl then
                           left_bind (binop lhs op rhs) op (and n tl)
                         else
                           expr_terminated (binop lhs op rhs) tl
                     | other => bind_error other (syntax_err "Expected an expression")
                     end
                   else expr_terminated lhs tl
               end
           | other => bind_error other (syntax_err "Expected an expression")
           end
       end
with or (steps : nat) (tokens : list token) : parse_result :=
       match steps with
       | O => terminated
       | S n =>
           let ops := tk_or :: nil in
           match and n tokens with
           | expr_terminated lhs tl =>
               match tl with
               | nil => expr_terminated lhs tl
               | op :: tl =>
                   if existsb (eqb op) ops then
                     match and n tl with
                     | expr_terminated rhs (cons op tl) =>
                         if existsb (eqb op) tl then
                           left_bind (binop lhs op rhs) op (or n tl)
                         else
                           expr_terminated (binop lhs op rhs) tl
                     | other => bind_error other (syntax_err "Expected an expression")
                     end
                   else expr_terminated lhs tl
               end
           | other => bind_error other (syntax_err "Expected an expression")
           end
       end.


(* steps variable is a decreasing argument of this fixpoint definition *)
Fixpoint parse_stmt (steps : nat) (tokens : list token) : parse_result :=
  match steps with
  | 0 => terminated
  | S n =>
      match tokens with
      | nil => terminated
      (* Class Statement *)
      | tk_class :: tl =>
          match tl with
          | (tk_identifier _ as name)
              :: tk_lt
              :: (tk_identifier _ as superclass)
              :: tk_left_brace :: tl =>
              match parse_stmt n tl with
              | stmt_terminated stmts tl =>
                  let class_stmt := class name (Some (variable superclass)) stmts in
                  bind_stmt class_stmt (parse_stmt n tl)
              | other => bind_error other (syntax_err "Expected statements")
              end
          | (tk_identifier _ as name)
              :: tk_left_paren :: tl =>
              match parse_params_rec tl with
              | stmt_terminated stmts tl =>
                  let class_stmt := class name None stmts in
                  bind_stmt class_stmt (parse_stmt n tl)
              | other => bind_error other (syntax_err "Expected statements")
              end
          | _ => syntax_err "Invalid class definition"
          end
      (* Function Statement *)
      | tk_fun :: (tk_identifier id as name) :: tk_left_paren :: tl =>
          match parse_params_rec tl with
          | params_terminated params tl =>
              match tl with
              | tk_left_brace :: tl =>
                  match parse_stmt n tl with
                  | stmt_terminated stmts tl =>
                      let function_stmt := function name params stmts in
                      bind_stmt function_stmt (parse_stmt n tl)
                  | other => bind_error other (syntax_err "Expected statements")
                  end
              | _ => syntax_err "Expected parameters"
              end
          | other => bind_error other (syntax_err "Invalid function definition")
          end
      (* Var Statement *)
      | tk_var :: (tk_identifier id as name) :: tk_eq :: tl =>
          match parse_expr n tl with
          | expr_terminated initializer tl =>
              bind_stmt (var name initializer) (parse_stmt n tl)
          | other => bind_error other (syntax_err "Expected an expression")
          end
      | _ => syntax_err "Unexpected token"
      end
  end.


Definition parse (tokens : list token) : parse_result :=
  let steps := (length tokens) * 2 in
  parse_stmt steps tokens.
