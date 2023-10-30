Require Import ZArith.
Require Import String.
Require Import Floats.
Require Import List.

Definition BASE := 10.


Module Val.
  (** Data types *)
  Variant t :=
    | boolean (b: bool)
    | int (n: Z)
    | float (f: float)
    | str (s: string)
    | func (name: string)
    | nil
  .

  Definition z_to_primf (z: Z) :=
    match z with
    | Zneg p => opp (PrimFloat.of_uint63 (Uint63.of_Z (Zpos p)))
    | _ => PrimFloat.of_uint63 (Uint63.of_Z z)                   
    end.

  (** Arithmetic *)
  Definition add (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => int (a + b)
    | float a, float b => float (a + b)
    | int a, float b => float (z_to_primf a + b)
    | float a, int b => float (a + z_to_primf b)
    | _, _ => nil
    end.

  Definition sub (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => int (a - b)
    | float a, float b => float (a - b)
    | int a, float b => float (z_to_primf a - b)
    | float a, int b => float (a - z_to_primf b)
    | _, _ => nil
    end.

  Definition mul (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => int (a * b)
    | float a, float b => float (a * b)
    | int a, float b => float (z_to_primf a * b)
    | float a, int b => float (a * z_to_primf b)
    | _, _ => nil
    end.

  Definition div (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => int (a / b)
    | float a, float b => float (a / b)
    | int a, float b => float (z_to_primf a / b)
    | float a, int b => float (a / z_to_primf b)
    | _, _ => nil
    end.

  Definition negate (v: t): t :=
    match v with
    | int z => int (-z)
    | float f => float (-f)
    | _ => nil
    end.

  (** Comparison and equality *)
  Definition lt (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => boolean (Zlt_bool a b)
    | float a, float b => boolean (ltb a b)
    | int a, float b => boolean (ltb (z_to_primf a) b)
    | float a, int b => boolean (ltb a (z_to_primf b))
    | _, _ => nil
    end.

  Definition le (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => boolean (Zle_bool a b)
    | float a, float b => boolean (leb a b)
    | int a, float b => boolean (leb (z_to_primf a) b)
    | float a, int b => boolean (leb a (z_to_primf b))
    | nil, nil => boolean true
    | _, _ => nil
    end.

  Definition gt (lhs rhs: t): t :=
    match (le lhs rhs) with
    | boolean b => boolean (negb b)
    | _ => nil
    end.

  Definition ge (lhs rhs: t): t :=
    match (lt lhs rhs) with
    | boolean b => boolean (negb b)
    | _ => nil
    end.

  Definition eq (lhs rhs: t): t :=
    match lhs, rhs with
    | int a, int b => boolean (Zeq_bool a b)
    | float a, float b => boolean (eqb a b)
    | int a, float b => boolean (eqb (z_to_primf a) b)
    | float a, int b => boolean (eqb a (z_to_primf b))
    | str a, str b => boolean (String.eqb a b)
    | func a, func b => boolean (String.eqb a b)
    | nil, nil => boolean true
    | _, nil => boolean false
    | nil, _ => boolean false
    | _, _ => nil
    end.

  (** Logical operators *)
  Definition not (v: t): t :=
    match v with
    | boolean b => boolean (negb b)
    | _ => nil
    end.

  Definition and (a b: t): t :=
    match a, b with
    | boolean a, boolean b => boolean (andb a b)
    | _, _ => nil
    end.

  Definition or (a b: t): t :=
    match a, b with
    | boolean a, boolean b => boolean (orb a b)
    | _, _ => nil
    end.

End Val.

Module BinOp.
  Variant t :=
    | add
    | sub
    | mul
    | div
    | le
    | lt
    | ge
    | gt
    | and
    | or
  .

  Definition eval (op: t): forall (lhs rhs: Val.t), Val.t :=
    match op with
    | add => Val.add
    | sub => Val.sub
    | mul => Val.mul
    | div => Val.div
    | le => Val.le
    | lt => Val.lt
    | ge => Val.ge
    | gt => Val.gt
    | and => Val.and
    | or => Val.or
    end.

End BinOp.

Module UnaryOp.
  Variant t :=
    | negate
    | not
  .

  Definition eval (op: t): forall (v: Val.t), Val.t :=
    match op with
    | negate => Val.negate
    | not => Val.not
    end.

End UnaryOp.

Module Inst.
  Inductive expr :=
  | val (v: Val.t)
  | bin_op (op: BinOp.t) (lhs: expr) (rhs: expr)
  | unary_op (op: UnaryOp.t) (v: Val.t)
  .

  Variant t :=
    | skip
    | assign (lhs: string) (rhs: Val.t)
    | print (expr: Val.t)
    | ret (expr: Val.t)
  .
End Inst.


Section STMT.
  Inductive stmt :=
  | inst (i: Inst.t)
  | ite (cond: Inst.expr) (b1 b2: block)
  | forloop (init: Inst.t) (cond: Inst.expr) (update: Inst.t) (b: block)
  | while (cond: Inst.expr) (b: block)
  | func (name: string) (params: list string) (b: block)
  with block :=
  | nil
  | cons (hd: stmt) (tl: block)
  .

  (* TODO: polymorphism? *)
  Record function: Type :=
    mk_function {
        fn_params: list string;
        fn_body: block;
      }.

  Record class: Type :=
    mk_class {
        fields: list string;
        sup: string; (* Inheritance *)
        cl_funcs: string -> option function;
      }.

End STMT.

Section ENV.
  Definition lenv := string -> Val.t.
  Definition init_le: lenv := fun _ => Val.nil.

  Definition update (k: string) (v: Val.t) (le: lenv): lenv :=
    fun i => if (String.eqb k i) then v else (le i).

End ENV.

Section PROGRAM.
  Record program: Type :=
    mk_program {
        classes: string -> option class;
        funcs: string -> option function;
      }.

End PROGRAM.
