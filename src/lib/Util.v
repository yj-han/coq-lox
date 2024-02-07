Require Import List.

Variable A: Type.

Definition slice (s e: nat) (l : list A) : list A :=
    firstn (e - s) (skipn s l).
