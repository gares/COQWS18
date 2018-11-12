From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - Declare exists2
    - Prove a lemma ex1 -> ex2 T
*)

Inductive ex2 T (P Q : pred T) : Prop :=
  ex2_intro (x : T) (p : P x) (q : Q x).

Lemma ex2T T (P : pred T) : (exists x, P x) -> (ex2 T P xpredT).
Proof. by case=> x px; exists x. Qed.


