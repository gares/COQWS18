(** Cheat sheet available at
      #<a href='https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf'>https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf</a>#
*)

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
