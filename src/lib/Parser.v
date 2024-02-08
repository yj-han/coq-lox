Require Import String.
Require Import List.

Require Import Object.
Require Import Token.
Require Import Expr.
Require Import Stmt.

From ExtLib Require Import
  Structures.Monads
  Data.Monads.EitherMonad
  Data.Monads.StateMonad.

Section Parser.

Import MonadNotation.
Local Open Scope monad_scope.

Definition parser_error: Type := token * string.

Definition parser_state: Type := (list token) * nat * (list parser_error).

Definition init_state (ts: list token): parser_state := (ts, 0, nil).

Variable m: Type -> Type.
Context {monad_m: Monad m}.
Context {state_m: MonadState parser_state m}.
Context {monadexc_m: MonadExc parser_error m}.

(** Statement parsing *)

(** Expression parsing *)

(** Error recovery *)

(** Parsing utils *)
Definition p_error (tk: token) (message: string): m stmt := raise (tk, message).

Definition inc_current :=
  s <- get ;;
  let '(tokens, current, errors) := s in
  put (tokens, current + 1, errors).

Definition previous :=
  s <- get ;;
  let '(tokens, current, _) := s in
  ret (nth_error tokens (current - 1)).

Definition peek :=
  s <- get ;;
  let '(tokens, current, _) := s in
  ret (nth_error tokens current).

Definition is_at_end :=
  t <- peek ;;
  match t_type t with
  | EOF => ret True
  | _ => ret False
  end.

Definition advance :=
  if is_at_end then (previous) (inc_current >> previous).

Definition consume (tt: token_type) (message: string) :=
  ifM (check tt) (advance) (peek >>= t -> p_error t message).

Definition match_token_type (ts: list token_type) :=
  ifM (anyM check ts) (advance >> return True) (return False).


End Parser.
