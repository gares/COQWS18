From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - use no lemma to prove the following statement
*)
Lemma orbC p q : p || q = q || p.
(*D*)Proof. by case: p; case: q. Qed.

(** *** Exercise 2:
   - look up what [==>] is and prove that as you like
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*)Proof. by case: p; case: q. Qed. 

(** *** Exercise 3:
    - what is [(+)] ?
    - prove this using move and rewrite
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
(*D*)Locate "(+)".
(*D*)Search _ addb negb.
(*D*)Proof. by move=> np_q; rewrite -np_q addbN negb_add. Qed.

(** *** Exercise 4:
    - prove this satement by induction
*)
Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
(*D*)Proof. by elim: n => // n IH; rewrite /= -IH. Qed.

(** *** Exercise 5:
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
