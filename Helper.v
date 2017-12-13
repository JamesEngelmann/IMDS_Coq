(* Rule Evaluator Helper Functions *)

Require Import Nat.
Require Import QArith.

(* Q type less than -> bool *)

Definition Qlt (a b : Q) : bool := (Qle_bool a b) &&  negb (Qeq_bool a b).

(* Q type greater than -> bool *) 

Definition Qgt (a b : Q) : bool := negb (Qle_bool a b) &&  negb (Qeq_bool a b).

(* nat type greater than -> bool *) 

Definition gtr_nat (a b : nat) : bool := negb (Nat.leb a b) && negb (beq_nat a b). 