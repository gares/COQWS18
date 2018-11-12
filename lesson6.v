
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Infinitude of primes

#<div>#
*)
Lemma prime_above (m : nat) : exists p, (prime p) && (m < p).
Proof.
have: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
move=> /pdivP[q pr_q q_dv_m1].
exists q; rewrite pr_q /= ltnNge.
apply: contraL q_dv_m1 => q_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.

(**
#</div>#

#<p><br/><p>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Order and max, a matter of symmetry

#<div>#
*)
Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
case/orP: (leq_total n2 n1) => [le_n21|le_n12].
  rewrite (maxn_idPl le_n21) orb_idr // => le_mn2.
  by apply: leq_trans le_mn2 le_n21.
rewrite maxnC orbC.
rewrite (maxn_idPl le_n12) orb_idr // => le_mn1.
by apply: leq_trans le_mn1 le_n12.
Abort.
(**
#</div>#

Note the repetition, and the step dealing with symmetry.

#<div>#
*)
Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
wlog le_n21: n1 n2 / n2 <= n1 => [th_sym|].
by case/orP: (leq_total n2 n1) => /th_sym; last rewrite maxnC orbC.
rewrite (maxn_idPl le_n21) orb_idr // => le_mn2.
by apply: leq_trans le_mn2 le_n21.
Qed.
(**
#</div>#


#<p><br/><p>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Euclidean division, simple and correct

#<div>#
*)
Print edivn.
Print edivn_rec.

Lemma edivn_recE d m q :
edivn_rec d m q = if m - d is m'.+1 then edivn_rec d m' q.+1 else (q,m).
Proof. by case: m. Qed.

Lemma edivnP m d (ed := edivn m d) :
  ((d > 0) ==> (ed.2 < d)) && (m == ed.1 * d + ed.2).
Proof.
case: d => [//=|d /=] in ed *.
rewrite -[edivn m d.+1]/(edivn_rec d m 0) in ed *.
rewrite -[m]/(0 * d.+1 + m).
elim: m {-2}m 0 (leqnn m) @ed => [[]//=|n IHn [//=|m]] q le_mn.
rewrite edivn_recE subn_if_gt; case: ifP => [le_dm|lt_md]; last first.
  by rewrite /= ltnS ltnNge lt_md eqxx.
have /(IHn _ q.+1) : m - d <= n by rewrite (leq_trans (leq_subr d m)).
by rewrite /= mulSnr -addnA -subSS subnKC.
Qed.
(**
#</div>#




#<p><br/><p>#

#</div>#

*)
