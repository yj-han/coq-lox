Require Import List.

Require Import Object.
Require Import Token.
Require Import Expr.

Inductive stmt :=
| Sblock (stmts : list stmt)
| Sexpression (expr : expr)
| Sfunction (name : token) (params : list token) (body : list stmt)
| Sclass (name : token) (superclass : option expr) (methods : list stmt)
| Sif (cond : expr) (bthen : stmt) (belse : option stmt)
| Sprint (expr : expr)
| Sreturn (keyword: token) (val : option expr)
| Svar (name : token) (initializer : option expr)
| Swhile (cond : expr) (body : stmt)
.
