Require Import Floats.
Require Import String.
Require Import ZArith.

Inductive object: Type :=
| Number (n: float)
| String (s: string)
| Bool (b: bool)
| Undefined
| LoxFunction (name: string) (arity: nat) (tokenId: nat) (binding_id: nat) (is_initializer: bool)
| LoxClass (name: string) (superclass: option object) (methods: string -> option object)
.
