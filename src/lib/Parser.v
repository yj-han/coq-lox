Require Import List.
Require Import String.

From ExtLib Require Import
  Data.String
  Data.Monads.EitherMonad
  Data.Monads.StateMonad
  Structures.Monads.

Require Import Object.
Require Import Token.
Require Import Expr.
Require Import Stmt.

Set Implicit Arguments.

Section Parser.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition parser_error: Type := (option token) * string.
  Definition parser_state: Type := (list token) * nat * (list parser_error).
  Definition init_state (ts: list token): parser_state := (ts, 0, nil).

  Definition parser := eitherT parser_error (state parser_state).

  (** Parsing utils *)
  Definition inc_current: parser unit :=
    s <- get ;;
    let '(tokens, current, errors) := s in
    put (tokens, current + 1, errors).

  Definition previous: parser (option token) :=
    s <- get ;;
    let '(tokens, current, _) := s in
    ret (nth_error tokens (current - 1)).

  Definition peek: parser (option token) :=
    s <- get ;;
    let '(tokens, current, _) := s in
    ret (nth_error tokens current).

  Definition is_at_end: parser (option bool) :=
    t <- peek ;;
    match t with
    | Some t => ret (Some (teq (t_type t) EOF))
    | None => ret None
    end.

  Definition advance: parser (option token) :=
    e <- is_at_end ;;
    match e with
    | Some e => if e then previous else (inc_current ;; previous)
    | None => ret None
    end.

  Definition check (tt: token_type): parser bool :=
    e <- is_at_end ;;
    match e with
    | Some e => if e then (ret false)
               else (t <- peek ;;
                      match t with
                      | Some t => ret (teq (t_type t) tt)
                      | None => ret false
                      end)
    | None => ret false
    end.

  Definition consume (tt: token_type) (message: string) :=
    c <- check tt ;;
    if c then advance else (t <- peek ;; raise (t, message)).

  Fixpoint match_token_type_inner (tts: list token_type): parser bool :=
    match tts with
    | nil => ret false
    | tty :: tts' => 
      c <- check tty ;;
      if c then advance ;; ret true else match_token_type_inner tts'
    end.

  Definition match_token_type (tts: list token_type): parser bool :=
    match_token_type_inner tts.

  (** Statement parsing *)

  (** Expression parsing *)

  (** Error recovery *)

End Parser.
