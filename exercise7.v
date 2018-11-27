From mathcomp Require Import all_ssreflect.


(** *** Exercise 1:
    - Prove this statement by induction.
      Relevant lemmas are
         doubleS odd_double addn0 addnn mulnn
         big_mkcond big_nat_recr big_geq
*)

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n^2.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite big_geq.
(*D*)rewrite doubleS big_mkcond 2?big_nat_recr // -big_mkcond /=.
(*D*)rewrite {}IHn odd_double /= addn0 -addnn -!mulnn.
(*D*)by rewrite mulSn mulnC mulSn addnA addSn addnC.
Qed.


(** *** Exercise 2:
    - Prove this statement by induction.
      Relevant lemmas are
         doubleD muln2 addn2 big_nat_recr big_geq
*)

Lemma sum_gauss n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
(*D*)elim: n => [|n IH]; first by rewrite big_geq.
(*D*)rewrite big_nat_recr //= doubleD {}IH.
(*D*)case: n => [|n /=]; first by rewrite muln0.
(*D*)by rewrite -muln2 -mulnDr addn2 mulnC.
(*A*)Qed.

Lemma sum_gauss_rev n : \sum_(0 <= i < n) (n.-1 - i)  = \sum_(0 <= i < n) i.
Proof.
(*D*)rewrite [RHS]big_nat_rev /=.
(*D*)by case: n => //.
(*A*)Qed.

Lemma sum_gauss_double n : (\sum_(0 <= i < n) i).*2  = 
       \sum_(0 <= i < n) i + \sum_(0 <= i < n) (n.-1 - i).
Proof.
(*D*)by rewrite sum_gauss_rev addnn.
(*A*)Qed.

Lemma sum_gaussD n :
       \sum_(0 <= i < n) i + \sum_(0 <= i < n) (n.-1 - i) =
           \sum_(0 <= i < n) n.-1.
Proof.
(*D*)rewrite -big_split /=.
(*D*)apply: eq_big_nat => i Hi.
(*D*)rewrite addnC subnK //.
(*D*)by case: n Hi.
(*A*)Qed.

Lemma sum_gauss_const n k : \sum_(0 <= i < n) k = n * k.
Proof.
(*D*)by rewrite sum_nat_const_nat subn0.
(*A*)Qed.

Lemma sum_gauss_alt n : (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
by rewrite sum_gauss_double sum_gaussD sum_gauss_const.
Qed.
