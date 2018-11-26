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

Lemma sum_gauss : forall n, (\sum_(0 <= i < n) i).*2 = n * n.-1.
Proof.
(*D*)elim=> [|n IH]; first by rewrite big_geq.
(*D*)rewrite big_nat_recr //= doubleD {}IH.
(*D*)case: n => [|n /=]; first by rewrite muln0.
(*D*)by rewrite -muln2 -mulnDr addn2 mulnC.
(*A*)Qed.



