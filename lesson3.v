
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Lesson 3: summary

- proofs by backchaining
- proofs by induction
- TODO: stack model => :

#<p><br/><p>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by backward chaining

We learn two tactics.
[move=> names] to introduce hypotheses in the context.
[apply: term] to backchain.

#<div>#
*)
About dvdn_addr.
Lemma example m p : prime p ->
  p %| m `! + 1 -> m < p.
Proof.
move=> prime_p.
(* Search "contra". *)
apply: contraLR.
rewrite -leqNgt.
move=> leq_p_m.
rewrite dvdn_addr.
  by rewrite gtnNdvd // prime_gt1.
(* Search _ dvdn factorial.*)
apply: dvdn_fact.
by rewrite leq_p_m prime_gt0.
Qed.
(**
#</div>#

Remark [dvdn_addr] is an [iff] used inside a context.

Remark [//] in [rewrite] to solve simple goals.

Remark [rewrite] acepts many rewrite rules.

Remark [n <= m <= p] is [n <= m && m <= p].

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 2.3.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by induction

The [elim:] tactic is like [case:] but gives you
an induction hypothesis.

#<div>#
*)
Lemma addn0 m : m + 0 = m.
Proof.
elim: m => [ // |m IHm].
by rewrite addSn IHm.
Qed.
(**
#</div>#

The first pitfall when proving programs by
induction is not generalizing enough the property
being proved before starting the induction.

#<div>#
*)
Lemma foldl_cat T R f (z0 : R) (s1 s2 : seq T) :
  foldl f z0 (s1 ++ s2) = foldl f (foldl f z0 s1) s2.
Proof.
elim: s1 z0  => [ // | x xs IH].
move=> acc /=.
by rewrite IH.
Qed.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 2.3.4 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 3: sum up

- [apply: t] backchain
- [elim: n] induction
- [move=> n] naming

#</div>#


*)
