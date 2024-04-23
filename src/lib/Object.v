Require Import Floats.
Require Import String.
Require Import ZArith.

Inductive object: Type :=
| Onumber (n: float)
| Ostring (s: string)
| Obool (b: bool)
| Oundefined
| Ofunction (name: string) (arity: nat) (tokenId: nat) (binding_id: nat) (is_initializer: bool)
| Oclass (name: string) (superclass: option object) (methods: string -> option object)
.
