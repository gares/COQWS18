From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
*)
Lemma ex1 x y : 8 * y != 6 * x + 1.
Proof.
(*D*)apply/negP => /eqP /(congr1 (modn^~ 2)).
(*D*)by rewrite -modnMml mul0n -modnDml -modnMml.
(*A*)Qed.

(** *** Exercise 2:
*)
Lemma mod4Dsqr_even a b : (a ^ 2 + b ^ 2) %% 4 = 0 -> (~~ odd a) && (~~ odd b).
Proof.
(*D*)have sqr_x2Dy_mod4 x y : (x * 2 + y) ^ 2 = y ^ 2 %[mod 4].
(*D*)  rewrite sqrnD addnAC mulnAC [2 * _]mulnC -mulnA -[2 * 2]/4.
(*D*)  by rewrite expnMn -[2 ^ 2]/4 -mulnDl -modnDml modnMl.
(*D*)rewrite {1}(divn_eq a 2) {1}(divn_eq b 2) -modnDm.
(*D*)by rewrite !sqr_x2Dy_mod4 modnDm !modn2; do 2!case: odd.
(*A*)Qed.

Definition sol n a b := [&& a > 0, b > 0 & 2 ^ n == a ^ 2 + b ^ 2].

Lemma sol0 a b : ~~ sol 0 a b.
Proof.
(*D*)rewrite /sol; have [a_gt0/=|//] := ltnP; have [b_gt0/=|//] := ltnP.
(*D*)by rewrite ltn_eqF// (@leq_add 1 1) ?expn_gt0 ?a_gt0 ?b_gt0.
(*A*)Qed.

Lemma sol1 a b : sol 1 a b = (a == 1) && (b == 1).
Proof.
(*D*)by case : a b => [|[|a]] [|[|b]]//; rewrite /sol ltn_eqF// (@leq_add 2 1).
(*A*)Qed.

Lemma sol_are_even n a b : n > 1 -> sol n a b -> (~~ odd a) && (~~ odd b).
Proof.
(*D*)case: n => [|[|n]]// _; rewrite /sol => /and3P[_ _ /eqP eq_a2Db].
(*D*)by rewrite mod4Dsqr_even// -eq_a2Db !expnS mulnA modnMr.
(*A*)Qed.

Lemma solS n a b : sol n.+2 a b -> sol n a./2 b./2.
Proof.
(*D*)move=> soln2ab; have [//|a_even b_even] := andP (sol_are_even _ soln2ab).
(*D*)rewrite /sol -[a]odd_double_half -[b]odd_double_half in soln2ab.
(*D*)rewrite (negPf a_even) (negPf b_even) ?add0n ?double_gt0 in soln2ab.
(*D*)rewrite /sol; move: soln2ab => /and3P[-> -> /=].
(*D*)by rewrite -(addn2 n) expnD -!muln2 !expnMn -mulnDl eqn_mul2r.
(*A*)Qed.

Lemma sol_even a b n : ~~ sol (2 * n) a b.
Proof.
(*D*)elim: n => [|n IHn] in a b *; first exact: sol0.
(*D*)by apply/negP; rewrite mulnS => /solS; apply/negP.
(*A*)Qed.

Lemma sol_odd a b n : sol (2 * n + 1) a b = (a == 2 ^ n) && (b == 2 ^ n).
Proof.
(*D*)apply/idP/idP=> [|/andP[/eqP-> /eqP->]]; last first.
(*D*)  by rewrite /sol !expn_gt0/= expnD muln2 addnn -expnM mulnC.
(*D*)elim: n => [|n IHn] in a b *; first by rewrite sol1.
(*D*)rewrite mulnS !add2n !addSn => solab.
(*D*)have [//|/negPf aNodd /negPf bNodd] := andP (sol_are_even _ solab).
(*D*)rewrite /sol -[a]odd_double_half -[b]odd_double_half aNodd bNodd.
(*D*)by rewrite -!muln2 !expnSr !eqn_mul2r IHn// solS.
(*A*)Qed.

(** *** Exercise 3:
*)
Lemma ex3 n : (n + 4 %| 3 * n + 32) = (n \in [:: 0; 1; 6; 16]).
Proof.
(*D*)apply/idP/idP => [Hn|]; rewrite !inE; last first.
(*D*)  by move=> /or4P[] /eqP->.
(*D*)have : n + 4 %| 3 * n + 32 - 3 * (n + 4) by rewrite dvdn_sub// dvdn_mull.
(*D*)by rewrite mulnDr subnDl /= {Hn}; do 21?[case: n => // n].
(*A*)Qed.

(** *** Exercise 4:
*)
Lemma ex4 a b n : a > 0 -> b > 0 -> n > 0 ->
   edivn (a * b ^ n - 1) (b ^ n.+1) =
   ((a - 1) %/ b, ((a - 1) %% b) * b ^ n + b ^ n - 1).
Proof.
(*D*)move=> a_gt0 b_gt0 n_gt0; rewrite /divn modn_def.
(*D*)have [q r aB1_eq r_lt] /= := edivnP (a - 1).
(*D*)rewrite b_gt0 /= in r_lt.
(*D*)have /(congr1 (muln^~ (b ^ n))) := aB1_eq.
(*D*)rewrite mulnBl mulnDl mul1n.
(*D*)move=> /(congr1 (addn^~ (b ^ n - 1))).
(*D*)rewrite addnBA ?expn_gt0 ?b_gt0// subnK; last first.
(*D*)  by rewrite -[X in X <= _]mul1n leq_mul2r a_gt0 orbT.
(*D*)rewrite -mulnA -expnS -addnA => ->.
(*D*)rewrite edivn_eq addnBA ?expn_gt0 ?b_gt0//.
(*D*)rewrite subnS subn0 prednK ?addn_gt0 ?expn_gt0 ?b_gt0 ?orbT//.
(*D*)rewrite -[X in _ + X]mul1n -mulnDl addn1 expnS.
(*D*)by rewrite leq_mul2r r_lt orbT.
(*A*)Qed.
