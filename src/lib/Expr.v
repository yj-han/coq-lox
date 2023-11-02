Require Import ZArith.
Require Import Floats.
Require Import String.
Require Import List.

Require Import Token.


Inductive expr :=                      
| assign (name : token) (value : expr)         
| binop (lhs : expr) (op : token) (rhs : expr)
| call (callee : expr) (paren : token) (args : list expr)
| get (obj : expr) (name : token)
| grouping (expr : expr)
| literal (val : token)
| logical (lhs : expr) (op : token) (right : expr)
| set (obj : expr) (name : token) (val : expr)
| super (keyword : token) (method : token)
| this  (keyword : token)
| unop (op : token) (rhs : expr)
| variable (name : token)
.

(* for superclass, only expr.variable is allowed,
   and for methods, only stmt.function is allowed *)
Inductive stmt :=
| block_stmt (stmts : list stmt)
| expression (expr : expr)
| function (name : token) (params : list token) (body : list stmt)
| class (name : token) (superclass : expr) (methods : stmt)
| ite (cond : expr) (bthen : stmt) (belse : stmt)
| print (expr : expr)
| ret (keyword : token) (val : expr)
| var (name : token) (initializer : expr)
| while (cond : expr) (body : stmt)
.

