Require Import Token.
Require Import Object.

Inductive expr :=
| Eassign (name : token) (value : expr)
| Ebinary (lhs : expr) (op : token) (rhs : expr)
| Ecall (callee : expr) (args : list expr)
| Eget (obj : expr) (name : token)
| Egrouping (expr : expr)
| Eliteral (obj : object)
| Elogical (lhs : expr) (op : token) (right : expr)
| Eset (obj : expr) (name : token) (val : expr)
| Esuper (keyword: token) (method : token)
| Ethis (keyword: token)
| Eunary (op : token) (rhs : expr)
| Evariable (name : token)
.
