(** Cheat sheet available at
      #<a href='https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf'>https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf</a>#
*)

From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(**
-----------------------------------------------------------------
*** Exercise 1:
    - prove this satement by induction
*)
Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
(*A*)Proof. by elim: n => //= n <-. Qed.

(**
-----------------------------------------------------------------
*** Exercise 2:
    - look up the definition of [iter] (note there is an accumulator varying
      during recursion)
    - prove the following statement by induction
*)
Lemma iter_predn m n : iter n predn m = m - n.
Proof.
(*D*)by elim: n m => [|n IHn] m; rewrite ?subn0//= IHn subnS.
(*A*)Qed.
(**
-----------------------------------------------------------------
*** Exercise 3:

Prove the sum of the lists [odds n] of exercise 1 is [n ^ 2].

You can prove the following lemmas in any order, some are way easier
than others.

- Recall from exercise 1.
*)
Definition add2list s := map (fun x => x.+2) s.
Definition odds n := iter n (fun s => 1 :: add2list s) [::].
(**
- We define a sum operation [suml].
*)
Definition suml := foldl addn 0.
(**
- Any [foldl addn] can be rexpressed as a sum.
*)
Lemma foldl_addE n s : foldl addn n s = n + suml s.
Proof.
(*D*)elim: s n => //= x s IHs n.
(*D*)by rewrite /suml/= !IHs add0n addnA.
(*A*)Qed.
(**
- Not to break abstraction, prove [suml_cons].
*)
Lemma suml_cons n s : suml (n :: s) = n + suml s.
(*A*)Proof. by rewrite /suml/= foldl_addE. Qed.
(**
- Show how to sum a [add2list].
*)
Lemma suml_add2list s : suml (add2list s) = suml s + 2 * size s.
Proof.
(*D*)elim: s => [|x s IHs] //=; rewrite !suml_cons IHs.
(*D*)by rewrite !mulnS !addnS addnA.
(*A*)Qed.
(**
- Show the size of a [add2list].
*)
Lemma size_add2list s : size (add2list s) = size s.
(*A*)Proof. by apply: size_map. Qed.
(**
- Show how many elments [odds] have.
*)
Lemma size_odds n : size (odds n) = n.
(*A*)Proof. by elim: n => //= n; rewrite size_add2list => ->. Qed.
(**
- Show the final statment.
*)
Lemma eq_suml_odds n : suml (odds n) = n ^ 2.
Proof.
(*D*)elim: n => //= n IHn; rewrite suml_cons.
(*D*)rewrite suml_add2list IHn addnCA addnA.
(*D*)by rewrite -(addn1 n) sqrnD size_odds muln1.
(*A*)Qed.
(**
-----------------------------------------------------------------
*** Exercise 4:

Prove the sum of the lists [odds n] is what you think.

You may want to have at least one itermediate lemma to prove [oddsE]
*)
Lemma oddsE n : odds n = [seq 2 * i + 1 | i <- iota 0 n].
Proof.
(*D*)rewrite /odds; set k := (0 as X in iota X _).
(*D*)rewrite -[1 in LHS]/(2 * k + 1).
(*D*)elim: n k => //= n IHn k; rewrite IHn; congr (_ :: _).
(*D*)by elim: n {IHn} k => // n IHn k /=; rewrite IHn !mulnS.
(*A*)Qed.

Lemma nth_odds n i : i < n -> nth 0 (odds n) i = 2 * i + 1.
Proof.
(*D*)by move=> i_ltn; rewrite oddsE (nth_map 0) ?size_iota ?nth_iota.
(*A*)Qed.
(**
-----------------------------------------------------------------
*** Exercise 5:

Let us prove directly formula
#$$ \sum_{i=0}^{n-1} (2 i + 1) = n ^ 2 $$#
from lesson 1, slightly modified.

Let us first define a custom sum operator:
*)
Definition mysum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

Notation "\mysum_ ( m <= i < n ) F" := (mysum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \mysum_ ( m  <=  i  <  n ) '/  '  F ']'").
(**
- First prove a very useful lemma about summation
*)
Lemma mysum_recl m n F : m <= n ->
  \mysum_(m <= i < n.+1) F i = \mysum_(m <= i < n) F i + F n.
Proof.
(*D*)move=> leq_mn; rewrite /mysum subSn// -addn1 iota_add subnKC//= foldr_cat/=.
(*D*)by elim: (iota _ _) (F n) => [|x s IHs] k //=; rewrite IHs addnA.
(*A*)Qed.
(**
- Now prove the main result

Do NOT use [eq_suml_odds] above, it would take much more time

*)
Lemma sum_odds n : \mysum_(0 <= i < n) (2 * i + 1) = n ^ 2.
Proof.
(*D*)elim: n => //= n IHn; rewrite mysum_recl// IHn.
(*D*)by rewrite -[n.+1]addn1 sqrnD muln1 addnAC addnA.
(*A*)Qed.
