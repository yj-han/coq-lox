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
  | in_class
  | in_function_param (name : token) (params : list token)
  | in_function_body (name : token) (params : list token) (body : list stmt)
  | in_var (name : token) (initializer : option expr)
  | in_for (initializer : option expr) (cond : option expr) (incr : option expr) (body : option stmt)  
  | in_if (cond : option expr) (bthen : option stmt) (belse : option stmt)
  | in_print
  | in_ret
  | in_while (cond : option expr) (body : list stmt)
  | in_block (stmts : list stmt)
  | in_assign (name : token) (value : option expr)
  | in_binop
  | in_call
  | in_get
  | in_grouping
  | in_literal
  | in_logical
  | in_set
  | in_super
  | in_this
  | in_unop
  | in_variable (name : token)      
.

Definition concat_with_casting {X : Type} (x : X) (xs : result (list X)) :=
  match xs with
  | Ok xs => Ok (x :: xs)
  | _ => xs
  end.

(* Assume that an opening brace exists *)
Fixpoint closing_brace_rec
  (nested : nat)
  (count : nat)
  (tokens : list token)
  : result nat :=
  match nested, tokens with
  | _, nil => Err syntax_err 
  | O, tk_right_brace :: _ => Ok count
  | _, tk_right_brace :: tl => closing_brace_rec (nested-1) (count+1) tl
  | _, tk_left_brace :: tl => closing_brace_rec (nested+1) (count+1) tl
  | _, _ :: tl => closing_brace_rec nested (count+1) tl
  end.

Definition closing_brace (tokens : list token) :=
  closing_brace_rec 0 1 tokens.


(* n is always equivalent to the length of the tokens.
   It is a decreasing argument of this fixpoint definition *)
Fixpoint parse_rec
  (n : nat)  
  (tokens : list token)
  {struct n}
  : result (list stmt) :=
  match n with
  | O => Ok nil
  | _ =>
    match tokens with
    | nil => Ok nil
    | tk_class :: tl =>
        match tl with
        | tk_identifier id1 :: tk_lt :: tk_identifier id2 :: tk_left_brace :: tl =>
            let closing_at := closing_brace tl in
            match closing_at with
              | Ok closing_at =>
                  let fst := firstn closing_at tl in
                  let body := parse_rec closing_at fst in
                  let snd := skipn closing_at tl in
                  parse_rec (n - closing_at) snd
            | Err e => Err e
            end              
        (* | tk_identifier id :: tk_left_brace :: tl *)
        | _ => Err syntax_err
        end
    (* | tk_fun :: tk_identifier id :: tk_left_brace :: tl *)
    (* | tk_var :: tk_identifier id :: tk_eq :: tl *)
    | _ => Err syntax_err
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
