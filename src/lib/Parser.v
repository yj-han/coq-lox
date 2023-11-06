Require Import ZArith.
Require Import Floats.

Require Import String.
Require Import BinaryString.
Require Import DecimalString.

Require Import Ascii.
Require Import List.

Require Import Token.
Require Import Expr.


Section ERROR_HANDLING.
  (* Possible errors from scanning *)
  Variant err_type :=
    | syntax_err.

  (* Result: Ok or Err *)
  Inductive result (X: Type): Type :=
  | Ok (x: X)
  | Err (e: err_type).

  Definition error_msg (e: err_type): string :=
    match e with
    | syntax_err => "Syntax error"
    end.

End ERROR_HANDLING.

Arguments Ok {X}.
Arguments Err {X}.


Variant state :=
  | glob
  | in_class (name: token) (super: option expr) (body: list stmt)
  | in_function (name: token) (params: list token) (body: list stmt) (is_param: bool)
  | in_var_declaration
  | in_for_stmt
  | in_if_stmt
  | in_print
  | in_ret
  | in_while    
  | in_expr_stmt 
.

Definition concat_with_casting (X : Type) (tk : X) (tks : result (list X)) :=
  match tks with
  | Ok tks => Ok (tk :: tks)
  | _ => tks
  end.

(* TODO: remove redundancy *)
Arguments concat_with_casting {X}.


(*
Fixpoint parse_rec
  (tokens : list token)
  (state : state)
  (scope : nat)
  : result (list stmt) :=
  match state with
  | base =>
      match tokens with
      | nil => Ok nil
      | tk_class :: tl =>
          match tl with
          | tk_identifier id1 :: tk_lt :: tk_identifier id2 :: tk_left_brace :: tl =>
              let next_state := in_class id1 (Some var id2) nil in
              parse_rec tl next_state
          | tk_identifier id :: tk_left_brace :: tl =>
              let next_state := in_class id None nil in
              parse_rec tl next_state
          | _  => Err syntax_err
          end
      | tk_fun :: tl =>
          match tl with
          | tk_identifier :: tk_left_brace :: tl =>
              let next_state := in_function id nil nil in
              parse_rec tl next_state
          | _ => Err syntax_err
          end
      | tk_var :: tl =>
          match tl with
          | tk_identifier id :: tk_eq :: tl =>
              parse_rec tl in_var_declaration
          | _ => Err syntax_err
          end
      | tk_for :: tl => Err syntax_err 
      | tk_if :: tl => Err syntax_err
      | tk_print :: tl => Err syntax_err
      | tk_ret :: tl => Err syntax_err
      | tk_while :: tl => Err syntax_err 
      | tk_left_brace :: tl => parse_rec tl in_stmt
      | _ => Err syntax_err
      end
  | in_class name super body =>
      match tokens with
      | tk_right_brace :: tl =>
          let stmt := class name super body in
          let result := parse_rec tl glob in
          concat_with_casting stmt result            
      | tk_fun :: tl =>
          match tl with
          | tk_identifier :: tk_left_brace :: tl =>
              let next_state := in_function id nil nil false in
              parse_rec tl next_state
          | _ => Err syntax_err
          end
      | _ => Err syntax_err
      end
  | in_function name params body =>
      match tokens with
      | tk_right_brace :: tl =>
          let stmt := function name params body in
          let result := parse_rec tl glob in
          concat_with_casting stmt result
*)        
      
Definition parse (tokens : list token) : result (list stmt).
Proof. Admitted.
