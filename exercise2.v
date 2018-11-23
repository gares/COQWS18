(** Cheat sheet available at
      #<a href='https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf'>https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf</a>#
*)

From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** 
    Try to prove the following theorems using no
    lemma and minimizing the number of applications of
    the tactic case
*)

(** *** Exercise 1:
*)

Lemma andTb p : true && p = p.
(*D*)Proof. by []. Qed.

(** *** Exercise 2:
*)

Lemma andbT p : p && true = p.
(*D*)Proof. by case: p. Qed.

(** *** Exercise 3:
*)

Lemma orbC p q : p || q = q || p.
(*D*)Proof. by case: p; case: q. Qed.

(** *** Exercise 4:
*)
Goal forall p q,    (p && q) || (   p && ~~ q) || 
                 (~~ p && q) || (~~ p && ~~ q). 
(*D*)Proof. by move=> p q; case: p; case: q. Qed.

(** *** Exercise 5 :
*)
Goal forall p q r, (p || q) && r = r && (p || q).
(*D*)Proof. by move=> p q r; case: (p || q); case: r. Qed.

Goal forall n, n < n.+1.
by [].

(** *** Exercise 6  :
   - look up what [==>] 
*)
(*D*)Locate "==>".
(*D*)Print implb.
Lemma implybE p q : p ==> q = ~~ p || q.
(*D*) Proof. by case: p. Qed.


(** *** 
    Try to prove using the case tactic and alternatively
    without using the case tactic
*)


(** *** Exercise 7  :
*)

Lemma negb_imply p q : ~~ (p ==> q) = p && ~~ q.
(*D*) (* Proof. by case: p. Qed. *)
(*D*) Proof. by rewrite implybE negb_or negbK. Qed.


(** *** Exercise 8  :
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*) (* Proof. by case: p; case: q. Qed. *)
(*D*) Proof. by rewrite implybE negb_imply implybE orbK orNb. Qed.


(** *** Exercise 9 :
    - what is [(+)] ?
    - prove this using move and rewrite
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
(*D*)Locate "(+)".
(*D*)Search _ addb negb.
(*D*)Proof. by move=> np_q; rewrite -np_q addbN negb_add. Qed.

