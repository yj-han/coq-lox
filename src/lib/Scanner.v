Require Import ZArith.
Require Import Floats.

Require Import String.
Require Import BinaryString.
Require Import DecimalString.

Require Import Ascii.
Require Import List.

Require Import Token.

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
Definition AND: string := "and".
Definition OR: string := "or".
Definition FUN: string := "fun".
Definition CLASS: string := "class".
Definition PRINT: string := "print".
Definition RET: string := "return".
Definition FOR: string := "for".
Definition WHILE: string := "while".
Definition IF: string := "if".
Definition ELSE: string := "else".
Definition TRUE: string := "true".
Definition FALSE: string := "false".
Definition NIL: string := "nil".
Definition THIS: string := "this".
Definition SUPER: string := "super".
Definition VAR: string := "var".

(* TODO: remove redundancy *)
Definition BASE := 10.

Module Character.
  Variant t :=
    | alpha (c: ascii)
    | digit (c: ascii)
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
    | space
    | tab
    | line_feed
    | carriage_ret
    | double_quoute
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
    else if Nat.eqb (nat_of_ascii c) SPACE then space
    else if Nat.eqb (nat_of_ascii c) TAB then tab
    else if Nat.eqb (nat_of_ascii c) LINE_FEED then line_feed
    else if Nat.eqb (nat_of_ascii c) CARRIAGE_RET then carriage_ret
    else if Nat.eqb (nat_of_ascii c) DOUBLE_QUOTE then double_quoute
    else other c.

  Definition ascii_of_t (ch: t): ascii :=
    match ch with
    | alpha c => c
    | digit c => c
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
    | space => ascii_of_nat SPACE
    | tab => ascii_of_nat TAB
    | line_feed => ascii_of_nat LINE_FEED
    | carriage_ret => ascii_of_nat CARRIAGE_RET
    | double_quoute => ascii_of_nat DOUBLE_QUOTE
    | other c => c
    end.

  Fixpoint list_t_of_string (s : string): list t :=
    match s with
    | EmptyString => nil
    | String c s => (t_of_ascii c) :: list_t_of_string s
    end.

  Definition string_of_list_t (xs: list t): string :=
    fold_right String EmptyString (map ascii_of_t xs).

End Character.

Section ERROR_HANDLING.
  (* Possible errors from scanning *)
  Variant err_type :=
    | unexpected_char (c: Character.t)
    | unterminated_string_literal.

  (* Result: Ok or Err *)
  Inductive result (X: Type): Type :=
  | Ok (x: X)
  | Err (e: err_type) (line: nat).

  Definition error_msg (e: err_type) (line: nat): string :=
    match e with
    | unexpected_char c =>
        "Unexpected chracter '"
          ++ (String (Character.ascii_of_t c)  EmptyString)
          ++ "' at line "
          ++ NilEmpty.string_of_int (Nat.to_int line)
    | unterminated_string_literal =>
        "Unterminated string literal "
          ++ "' at line "
          ++ NilEmpty.string_of_int (Nat.to_int line)
    end.

End ERROR_HANDLING.

Section DFA.
  Variant state :=
    | normal
    | commenting
    | quoting (acc: list Character.t)
    | wording (acc: list Character.t)
    | numbering (whole: list ascii) (fraction: list ascii) (is_float: bool)
  .

  Record DFA :=
    mk_DFA {
        mode: state;
        loc: nat
      }.

  (* State transitions *)
  Definition init_dfa (mode: state) (loc: nat) := {| mode := mode; loc := loc |}.
  Definition initial_dfa (loc : nat) := init_dfa normal loc.
  Definition start_quoting (loc: nat) := init_dfa (quoting nil) loc.
  Definition next_quoting
    (acc: list Character.t)
    (ch: Character.t)
    (loc: nat)
    := init_dfa (quoting (acc ++ ch :: nil)) loc.
  Definition start_wording
    (ch: Character.t)
    (loc: nat)
    := init_dfa (wording (ch :: nil)) loc.
  Definition next_wording
    (acc: list Character.t)
    (ch: Character.t)
    (loc: nat)
    := init_dfa (wording (acc ++ ch :: nil)) loc.
  Definition start_numbering
    (n: ascii)
    (loc: nat)
    := init_dfa (numbering (n :: nil) nil false) loc.
  Definition next_numbering
    (whole fraction: list ascii)
    (is_float: bool)
    (n: ascii)
    (loc: nat)
    :=
    if is_float then init_dfa (numbering whole (fraction ++ n :: nil) is_float) loc
    else init_dfa (numbering (whole ++ n :: nil) fraction is_float) loc.

End DFA.


Section TOKENIZER.
  Arguments Ok {X}.
  Arguments Err {X}.

 Definition z_to_primf (z: Z) :=
    match z with
    | Zneg p => opp (PrimFloat.of_uint63 (Uint63.of_Z (Zpos p)))
    | _ => PrimFloat.of_uint63 (Uint63.of_Z z)
    end.

  Definition z_of_list_ascii (xs: list ascii): Z :=
    to_Z (string_of_list_ascii xs).

  Definition tk_number_of_list_ascii
    (whole fraction: list ascii)
    : token_type :=
    let whole_num := z_of_list_ascii whole in
    if Nat.eqb (length fraction) 0 then
      tk_int whole_num
    else
      let sz := Z.of_nat (length fraction) in
      let decimal := z_to_primf (Z.pow 10%Z sz) in
      let fraction_num := div (z_to_primf (z_of_list_ascii fraction)) decimal in
      tk_float (z_to_primf whole_num + fraction_num).

  (* Get the token type of input word. The return type should be either
     related to reserved_keyword or identifier *)
  Definition token_type_of_word (word : string) : token_type :=
    if String.eqb word AND then tk_and
    else if String.eqb word OR then tk_or
    else if String.eqb word FUN then tk_fun
    else if String.eqb word CLASS then tk_class
    else if String.eqb word PRINT then tk_print
    else if String.eqb word RET then tk_ret
    else if String.eqb word FOR then tk_for
    else if String.eqb word WHILE then tk_while
    else if String.eqb word IF then tk_if
    else if String.eqb word ELSE then tk_else
    else if String.eqb word TRUE then tk_true
    else if String.eqb word FALSE then tk_false
    else if String.eqb word NIL then tk_nil
    else if String.eqb word THIS then tk_this
    else if String.eqb word SUPER then tk_super
    else if String.eqb word VAR then tk_var
    else tk_identifier word.

  Definition concat_with_casting (tk : token) (tks : result (list token)) :=
    match tks with
    | Ok tks => Ok (tk :: tks)
    | _ => tks
    end.

  (* Tokenize input source code. DFA helps the recursive function to use
   src as a decreasing variable to the base case *)
  Fixpoint tokenize_rec
    (src: list Character.t)
    (dfa: DFA)
    : result (list token) :=
    match dfa.(mode) with
    | normal =>
        match src with
        | nil => Ok nil
        | Character.left_paren :: tl =>
            let token := make_token tk_left_paren dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.right_paren :: tl =>
            let token := make_token tk_right_paren dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.left_brace :: tl =>
            let token := make_token tk_left_brace dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.right_brace :: tl =>
            let token := make_token tk_right_brace dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.comma :: tl =>
            let token := make_token tk_comma dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.dot :: tl =>
            let token := make_token tk_dot dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.minus :: tl =>
            let token := make_token tk_minus dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.plus :: tl =>
            let token := make_token tk_plus dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.semi_colon :: tl =>
            let token := make_token tk_semi_colon dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.star :: tl =>
            let token := make_token tk_star dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.space :: tl
        | Character.tab :: tl => tokenize_rec tl dfa
        | Character.line_feed :: tl
        | Character.carriage_ret :: tl =>
            let next_dfa := init_dfa normal (dfa.(loc) + 1) in
            tokenize_rec tl next_dfa
        | Character.bang :: Character.eq :: tl =>
            let token := make_token tk_bang_eq dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.bang :: tl =>
            let token := make_token tk_bang dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.eq :: Character.eq :: tl =>
            let token := make_token tk_eq_eq dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.eq :: tl =>
            let token := make_token tk_eq dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.lt :: Character.eq :: tl =>
            let token := make_token tk_le dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.lt :: tl =>
            let token := make_token tk_lt dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.gt :: Character.eq :: tl =>
            let token := make_token tk_ge dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.gt :: tl =>
            let token := make_token tk_gt dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.slash :: Character.slash :: tl =>
            let next_dfa := init_dfa commenting dfa.(loc) in
            tokenize_rec tl next_dfa
        | Character.slash :: tl =>
            let token := make_token tk_slash dfa.(loc) in
            let result := tokenize_rec tl dfa in
            concat_with_casting token result
        | Character.double_quoute :: tl =>
            let next_dfa := start_quoting dfa.(loc) in
            tokenize_rec tl next_dfa
        | Character.digit d :: tl =>
            let next_dfa := start_numbering d dfa.(loc) in
            tokenize_rec tl next_dfa
        | (Character.alpha a as c) :: tl =>
            let next_dfa := start_wording c dfa.(loc) in
            tokenize_rec tl next_dfa
        | c :: _ => Err (unexpected_char c) dfa.(loc)
        end
    | commenting =>
        match src with
        | nil => Ok nil
        | Character.line_feed :: tl
        | Character.carriage_ret :: tl =>
            let next_dfa := init_dfa normal dfa.(loc) in
            tokenize_rec tl next_dfa
        | _ :: tl => tokenize_rec tl dfa
        end
    | quoting acc =>
        match src with
        | nil => Err unterminated_string_literal dfa.(loc)
        | (Character.line_feed as ch) :: _
        | (Character.carriage_ret as ch) :: _ => Err (unexpected_char ch) dfa.(loc)
        | Character.double_quoute :: tl =>
            let token := make_token (tk_string (Character.string_of_list_t acc)) dfa.(loc) in
            let next_dfa := init_dfa normal dfa.(loc) in
            let result := tokenize_rec tl next_dfa in
            concat_with_casting token result
        | c :: tl =>
            let next_dfa := next_quoting acc c dfa.(loc) in
            tokenize_rec tl next_dfa
        end
    | numbering whole fraction is_float =>
        match src with
        | nil =>
            let token := make_token (tk_number_of_list_ascii whole fraction) dfa.(loc) in
            Ok (token :: nil)
        | Character.digit d :: tl =>
            let next_dfa := next_numbering whole fraction is_float d dfa.(loc) in
            tokenize_rec tl next_dfa
        | Character.space :: tl
        | Character.tab :: tl =>
            let token := make_token (tk_number_of_list_ascii whole fraction) dfa.(loc) in
            let next_dfa := init_dfa normal dfa.(loc) in
            let result := tokenize_rec tl next_dfa in
            concat_with_casting token result
        | ch :: tl => Err (unexpected_char ch) dfa.(loc)
        end
    | wording acc =>
        match src with
        | nil =>
            let token := make_token (token_type_of_word (Character.string_of_list_t acc)) dfa.(loc) in
            Ok (token :: nil)
        | (Character.alpha a as ch) :: tl =>
            let next_dfa := next_wording acc ch dfa.(loc) in
            tokenize_rec tl next_dfa
        | (Character.digit d as ch) :: tl =>
            let next_dfa := next_wording acc ch dfa.(loc) in
            tokenize_rec tl next_dfa
        | _ :: tl =>
            let token := make_token (token_type_of_word (Character.string_of_list_t acc)) dfa.(loc) in
            let next_dfa := init_dfa normal dfa.(loc) in
            let result := tokenize_rec tl next_dfa in
            concat_with_casting token result
        end
    end.


  Definition tokenize (src: string): result (list token) :=
    let dfa := init_dfa normal 1 in
    tokenize_rec (Character.list_t_of_string src) dfa.

End TOKENIZER.
