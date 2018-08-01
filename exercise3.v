From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - look for lemmas supporting contrapositive reasoning
    - use the eqP view to finish the proof.
*)
Lemma bool_gimmics1 a : a != a.-1 -> a != 0.
(*D*)Proof. by apply: contra; move => /eqP E; rewrite E. Qed.

(** *** Exercise 2:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
(*D*)Proof. by move=> -> /eqP->; exact: doubleK. Qed.

(** *** Exercise 3:
  - Prove this view by unfolding maxn and then using [leqP]
*)
Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
Proof. apply: (iffP idP).
(*D*)by rewrite /maxn; case: leqP.
(*D*)by move=> <-; rewrite /maxn; case: leqP.
Qed.

(** *** Exercise 4:
  - there is no need to prove [reflect] with [iffP]: here just use [rewrite] and [apply]
  - check out the definitions and theory of [leq] and [maxn]
  - proof sketch:
<<
   n <= m = n - m == 0
          = m + n - m == m + 0
          = maxn m n == m
>> *)
Lemma maxn_idPl_bis m n : reflect (maxn m n = m) (m >= n).
(*D*)Proof. by rewrite -subn_eq0 -(eqn_add2l m) addn0 -maxnE; apply: eqP. Qed.

