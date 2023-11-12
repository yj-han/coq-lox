Require Import ZArith.
Require Import Floats.
Require Import String.
Require Import List.

Require Import Token.

Inductive expr :=
| assign (name : token) (value : expr)
| binop (lhs : expr) (op : token) (rhs : expr)
| function_call (callee : expr) (args : list expr)
| get (obj : expr) (name : token)
| grouping (expr : expr)
| literal (val : token)
| logical (lhs : expr) (op : token) (right : expr)
| set (obj : expr) (name : token) (val : expr)
| super (method : token)
| this
| unop (op : token) (rhs : expr)
| variable (name : token)
.

(* for superclass, only expr.variable is allowed,
   and for methods, only stmt.function is allowed *)
Inductive stmt :=
| block (stmts : list stmt)
| expression (expr : expr)
| function (name : token) (params : list token) (body : list stmt)
| class (name : token) (superclass : option expr) (methods : list stmt)
| ite (cond : expr) (bthen : list stmt) (belse : list stmt)
| print (expr : expr)
| ret (val : option expr)
| var (name : token) (initializer : expr)
| while (cond : expr) (body : list stmt)
.
