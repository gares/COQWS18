From mathcomp Require Import all_ssreflect. 


(** *** Exercise 1:
    - Prove this statement by induction.
      Relevant lemmas are
         doubleS odd_double addn0 addnn mulnn
         big_mkcond big_nat_recr
*)

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n^2.
Proof.
(*D*)elim: n => [|n IHn]; first by rewrite unlock.
(*D*)rewrite doubleS big_mkcond 2?big_nat_recr // -big_mkcond /=.
(*D*)rewrite {}IHn odd_double /= addn0 -addnn -!mulnn.
(*D*)by rewrite mulSn mulnC mulSn addnA addSn addnC.
Qed.



