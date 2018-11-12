(** Cheat sheet available at
      #<a href='https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf'>https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf</a>#
*)

From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - prove this satement by induction
*)
Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
(*D*)Proof. by elim: n => // n IH; rewrite /= -IH. Qed.

(** *** Exercise 2:
    - look up the definition of [iter] (note there is an accumulator varying
      during recursion)
    - prove the following statement by induction
*)
Lemma iter_predn m n : iter n predn m = m - n.
Proof.
(*D*)elim: n m => [|n IHn] m.
(*D*)  by rewrite subn0.
(*D*)by rewrite /= IHn subnS.
Qed.
