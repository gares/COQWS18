From mathcomp Require Import all_ssreflect. 


(** *** Exercise 1:
    - Let's define the subtype of odd and even natural numbers
    - Intrument Coq to recognize odd/even number built out
      of product and successor
    - Inherit on [odd_nat] the [eqType] structure 
*)

Structure odd_nat := Odd {
  oval :> nat;
  oprop : odd oval
}.
Lemma oddP (n : odd_nat) : odd n.
Proof. by case: n. Qed.

Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.
Lemma evenP (n : even_nat) : ~~ (odd n).
Proof. by case: n. Qed.

Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

Canonical even_0 := Even 0 isT.

Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof.
(*D*)by rewrite /=; case: (odd n).
Qed.

Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
(*D*)by rewrite /=; case: (odd n).
Qed.

Canonical odd_even (m : even_nat) :=
  Odd m.+1 (oddS m (eprop m)).
Canonical even_odd (m : odd_nat) :=
(*D*)Even m.+1 (evenS m (oprop m)).

Lemma odd_mulP (n m : odd_nat) : odd (n * m).
Proof.
(*D*)by rewrite odd_mul !oddP.
Qed.
Canonical odd_mul (n m : odd_nat) :=
(*D*)Odd (n * m) (odd_mulP n m).

Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.

Fail Check forall n m : odd_nat, n == m.

Canonical odd_subType :=
(*D*)Eval hnf in [subType for oval].
Definition odd_eqMixin :=
(*D*)Eval hnf in [eqMixin of odd_nat by <:].
Canonical odd_eqType :=
(*D*)Eval hnf in EqType odd_nat odd_eqMixin.

Check forall n m : odd_nat, n == m.

