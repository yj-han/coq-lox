From sflib Require Import sflib.

Require Import ZArith.
Require Import Floats.

Require Import DecimalString.
Require Import String.
Require Import Ascii.
Require Import List.


(* ASCII codes of important characters *)
Definition LEFT_PAREN := 40.
Definition RIGHT_PAREN := 41.
Definition LEFT_BRACE := 123.
Definition RIGHT_BRACE := 125.
Definition COMMA := 44.
Definition DOT := 46.
Definition MINUS := 45.
Definition PLUS := 43.
Definition SEMI_COLON := 59.
Definition SLASH := 47.
Definition STAR := 42.
Definition BANG := 33.
Definition LT := 60.
Definition EQ := 61.
Definition GT := 62.
Definition QUEST := 63.
Definition DOUBLE_QUOTE := 34.

Definition SPACE := 32.
Definition TAB := 9.
Definition LINE_FEED := 10.
Definition CARRIAGE_RET := 13.

Definition ZERO := 48.
Definition NINE := 57.
Definition UPPER_A := 65.
Definition UPPER_Z := 90.
Definition LOWER_A := 97.
Definition LOWER_Z := 122.

(* Reserved Keywords *)
Definition AND := "and".
Definition OR := "or".
Definition FUN := "fun".
Definition CLASS := "class".
Definition PRINT := "print".
Definition RET := "return".
Definition FOR := "for".
Definition WHILE := "while".
Definition IF := "if".
Definition ELSE := "else".
Definition TRUE := "true".
Definition FALSE := "false".
Definition NIL := "nil".
Definition THIS := "this".
Definition SUPER := "super".
Definition VAR := "var".


Module Character.
  Variant t :=
    | whitespace
    | linespace
    | alpha (c: ascii)
    | digit (c: ascii)
    | double_quoute
    | left_paren
    | right_paren
    | left_brace
    | right_brace
    | comma
    | dot
    | minus
    | plus
    | semi_colon
    | slash
    | star
    | bang
    | eq
    | gt
    | lt
    | other (c: ascii)
  .


  Definition is_digit (c: ascii): bool :=
    let n:= nat_of_ascii c in
    andb (Nat.leb ZERO n) (Nat.leb n NINE).

  Definition is_alpha (c: ascii): bool :=
    let n:= nat_of_ascii c in
    orb (andb (Nat.leb UPPER_A n) (Nat.leb n UPPER_Z))
        (andb (Nat.leb LOWER_A n) (Nat.leb n LOWER_Z)).

  Definition t_of_ascii (c: ascii): t :=
    if is_digit c then digit c
    else if is_alpha c then alpha c
    else if Nat.eqb (nat_of_ascii c) LEFT_PAREN then left_paren
    else if Nat.eqb (nat_of_ascii c) RIGHT_PAREN then right_paren
    else if Nat.eqb (nat_of_ascii c) LEFT_BRACE then left_brace
    else if Nat.eqb (nat_of_ascii c) RIGHT_BRACE then right_brace
    else if Nat.eqb (nat_of_ascii c) COMMA then comma
    else if Nat.eqb (nat_of_ascii c) DOT then dot
    else if Nat.eqb (nat_of_ascii c) MINUS then minus
    else if Nat.eqb (nat_of_ascii c) PLUS then plus
    else if Nat.eqb (nat_of_ascii c) SEMI_COLON then semi_colon
    else if Nat.eqb (nat_of_ascii c) STAR then star
    else if Nat.eqb (nat_of_ascii c) BANG then bang
    else if Nat.eqb (nat_of_ascii c) EQ then eq
    else if Nat.eqb (nat_of_ascii c) LT then lt
    else if Nat.eqb (nat_of_ascii c) GT then gt
    else if Nat.eqb (nat_of_ascii c) SLASH then slash
    else if orb (Nat.eqb (nat_of_ascii c) SPACE)
                (Nat.eqb (nat_of_ascii c) TAB) then whitespace
    else if Nat.eqb (nat_of_ascii c) LINE_FEED then linespace
    else if Nat.eqb (nat_of_ascii c) CARRIAGE_RET then linespace
    else if Nat.eqb (nat_of_ascii c) DOUBLE_QUOTE then double_quoute
    else other c.

  Definition ascii_of_t (ch: t): ascii :=
    match ch with
    | whitespace => ascii_of_nat SPACE
    | linespace => ascii_of_nat LINE_FEED
    | alpha c => c
    | digit c => c
    | double_quoute => ascii_of_nat DOUBLE_QUOTE
    | left_paren => ascii_of_nat LEFT_PAREN 
    | right_paren => ascii_of_nat RIGHT_PAREN
    | left_brace => ascii_of_nat LEFT_BRACE 
    | right_brace => ascii_of_nat RIGHT_BRACE 
    | comma => ascii_of_nat COMMA
    | dot => ascii_of_nat DOT
    | minus => ascii_of_nat MINUS
    | plus => ascii_of_nat PLUS
    | semi_colon => ascii_of_nat SEMI_COLON
    | slash => ascii_of_nat SLASH
    | star => ascii_of_nat STAR
    | bang => ascii_of_nat BANG
    | eq => ascii_of_nat EQ
    | gt => ascii_of_nat GT
    | lt => ascii_of_nat LT
    | other c => c
    end.
  
  Fixpoint list_t_of_string (s : string): list t :=
    match s with
    | EmptyString => []
    | String c s => (t_of_ascii c) :: list_t_of_string s
    end.

End Character.

Section TOKEN.

   Variant ttype :=
    (* Single-character tokens *)
    | left_paren
    | right_paren
    | left_brace
    | right_brace
    | comma
    | dot
    | minus
    | plus
    | semi_colon
    | slash
    | star
    (* One or two character tokens *)
    | bang
    | bang_eq
    | eq
    | eq_eq
    | gt
    | ge
    | lt
    | le
    (* Literals *)
    | identifier (id: string)
    | str (s: string)
    | int_number (z: Z)
    | float_number (f: float)
    (* Keywords *)
    | and
    | class
    | els (* else is already reserved *)
    | false
    | func
    | forloop
    | ite
    | nil
    | or
    | print
    | ret
    | super
    | this
    | true
    | var
    | while
    | eof
    | undef
  .
  
  Record token :=
    mk_token {
        type: ttype;
        line: nat;
      }.
  
End TOKEN.

Section ERROR_HANDLING.
  (* Possible errors from scanning *)
  Variant errtype :=
    | unexpected_char (c: ascii) (line: nat).

  Definition error_message (e: errtype): string :=
    match e with
    | unexpected_char c line =>
        "Unexpected chracter '"
          ++ (String c EmptyString)
          ++ "' at line "
          ++ NilEmpty.string_of_int (Nat.to_int line)
    end.

  (* Compute error_message (unexpected_char (ascii_of_nat LOWER_A) 13). *)

  (* Result: Ok or Err *)
  Inductive result (X: Type): Type :=
  | Ok (x: X)
  | Err (e: errtype).

  Arguments Ok {X}.
  Arguments Err {X}.

  Notation "' p <- e1 ;; e2"
    := (match e1 with
        | Ok p => e2
        | Err err => Err err
        end)
         (right associativity, p pattern, at level 60, e1 at next level).

  Notation "'TRY' e1 'OR' e2"
    := (
      let result := e1 in
      match result with
      | Ok _ => result
      | Err _ => e2
      end)
         (right associativity, at level 60, e1 at next level, e2 at next level).

End ERROR_HANDLING.

Section TOKENIZER.

  (* Tokenize a string literal. This should return a list of ascii
     starting with a character right after the ending '"'. *)
  Definition tokenize_str (xs: list ascii): result ttype * list ascii. Proof. Admitted.
  (* TODO: Tokenize a number. *)
  Definition tokenize_number (xs: list ascii): result ttype * list ascii. Proof. Admitted.
  (* TODO: Tokenize an identifier *)
  Definition tokenize_identifier (xs: list ascii): result ttype * list ascii. Proof. Admitted.

  (* Tokenize an input source string. Index starts from 0. *)
  Fixpoint tokenize_rec
    (src: list Character.t)
    (line: nat)
    : result (list token) :=
    match src with
    | [] => Ok (list token) []
    | (Character.left_paren as p) :: tl => Ok (list token) []
    | (Character.right_paren as p) :: tl =>  Ok (list token) []
    | _ => Ok (list token) []
    end.

  (*
    else if Nat.eqb (nat_of_ascii c) LEFT_PAREN) :: tl => (Ok ttype left_paren, tl)
    else if Nat.eqb (nat_of_ascii c) RIGHT_PAREN) :: tl => (Ok ttype right_paren, tl)
    else if Nat.eqb (nat_of_ascii c) LEFT_BRACE) :: tl => (Ok ttype left_brace, tl)
    else if Nat.eqb (nat_of_ascii c) RIGHT_BRACE) :: tl => (Ok ttype right_brace, tl)
    else if Nat.eqb (nat_of_ascii c) COMMA) :: tl => (Ok ttype comma, tl)
    else if Nat.eqb (nat_of_ascii c) DOT) :: tl => (Ok ttype dot, tl)
    else if Nat.eqb (nat_of_ascii c) MINUS) :: tl => (Ok ttype minus, tl)
    else if Nat.eqb (nat_of_ascii c) PLUS) :: tl => (Ok ttype plus, tl)
    else if Nat.eqb (nat_of_ascii c) SEMI_COLON) :: tl => (Ok ttype semi_colon, tl)
    else if Nat.eqb (nat_of_ascii c) STAR) :: tl => (Ok ttype star, tl)
    else if Nat.eqb (nat_of_ascii c) BANG) :: (nat_of_ascii EQ) :: tl => (Ok ttype bang_eq, tl)
    else if Nat.eqb (nat_of_ascii c) BANG) :: _ :: tl => (Ok ttype bang, tl)
    else if Nat.eqb (nat_of_ascii c) EQ) :: (nat_of_ascii EQ) :: tl => (Ok ttype eq_eq, tl)
    else if Nat.eqb (nat_of_ascii c) EQ) :: _ :: tl => (Ok ttype eq, tl)
    else if Nat.eqb (nat_of_ascii c) LT) :: (nat_of_ascii EQ) :: tl => (Ok ttype le, tl)
    else if Nat.eqb (nat_of_ascii c) LT) :: _ :: tl => (Ok ttype tl, tl)
    else if Nat.eqb (nat_of_ascii c) GT) :: (nat_of_ascii EQ) :: tl => (Ok ttype ge, tl)
    else if Nat.eqb (nat_of_ascii c) GT) :: _ :: tl => (Ok ttype gt, tl)
    else if Nat.eqb (nat_of_ascii c) WHITESPACE) :: tl
    else if Nat.eqb (nat_of_ascii c) TAB) :: tl => (Ok ttype empty, tl)
    else if Nat.eqb (nat_of_ascii c) LINE_FEED) :: tl
    else if Nat.eqb (nat_of_ascii c) CARRIAGE_RET) :: tl => (Ok ttype nline (line + 1), tl)
    else if Nat.eqb (nat_of_ascii c) DOUBLE_QUOTE) :: tl => tokenize_str tl
      | c :: tl =>
          if is_digit c then tokenize_number tl
         else if is_alpha c then tokenize_identifier src
               else (Err (unexpected_char c line), [])
      end in
    match result with
    | Ok tk, tl =>
        let new_line := match tk with | nline => line + 1 | _ => line end in
        let tks := tokenize_rec tl new_line in
        match tks with
        | Ok tks => tk :: tks
        | Err e => Err e
        end
    | Err e, other => Err e
    end.
   *)
  Definition tokenize (src: string): result (list token) :=
    tokenize_rec (Character.list_t_of_string src) 1%nat.

End TOKENIZER.
