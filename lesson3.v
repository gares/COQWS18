
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** 

Roadmap:
- recall CH 3.x
- reflect 4.1.1 + iffP 4.1.2
- view application 4.1.3 4.1.4
- speck (leqP, ifP) 4.2

#<div>#

----------------------------------------------------------
#<div class="slide">#
** Curry Howard, propositions and booleans

#<div>#
*)
Print andb.
Print and.

Print orb.
Print or.

Check [forall x : 'I_4, 0 <= x].
Check forall x : nat, 0 <= x.

Check true ==> false.
Check True -> False.

Lemma test_and (P Q: bool) :
  P /\ Q -> P.
Proof.
move=> pAq.
case: pAq => p q.
apply: p.
Qed.

Lemma test_or (P Q R: bool) :
  P || Q -> R.
Proof.
move=> pOq.
Abort.

(**
#</div>#

Propositions:
- structure to your proof (a tree)
- more expressive logic (forall, exists)

# $$ \frac{P \vdash R \quad Q \vdash R}{P \lor Q \vdash R} $$ #

Booleans:
- computation & Excluded Middle
- Uniqueness of Identity Proofs

A taste of UIP (more in lesson 4):

#<div>#
*)
About bool_irrelevance.
Lemma odd3 : odd 3. Proof. by []. Qed.
Lemma odd21 : odd (2+1). Proof. by []. Qed.
Lemma uip_test : (3, odd3) = (2+1, odd21).
Proof. rewrite (bool_irrelevance odd3 odd21). by []. Qed.
(**
#</div>#

Side note: bool_irrelevance is a lemma, by CH also a
program, and I'm passing two arguments to it.


We want the best of the two worlds, and a way to
link them: views.

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 3.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Stating and proving a view

#<div>#
*)


About iffP.

Lemma eqnP {n m : nat} :
  reflect (n = m) (eqn n m).
Proof.
apply: (iffP idP).
  by elim: n m => [|n IH] m; case: m => // m Hm; rewrite (IH m).
by move=> def_n; rewrite {}def_n; elim: m.
Qed.

(**
#</div>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 4.1.1 and 4.1.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#


----------------------------------------------------------
#<div class="slide">#
** Using views

#<div>#
*)
About andP.

Lemma example n m k : k <= n ->
  (n <= m) && (m <= k) -> n = k.
Proof.
move=> lekn /andP H; case: H => lenm lemk.
Undo.
move=> lekn /andP[lenm lemk].
Abort.

Lemma leq_total m n : (m <= n) || (m >= n).
Proof. by rewrite -implyNb -ltnNge; apply/implyP; apply: ltnW. Qed.


Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
case/orP: (leq_total n2 n1) => [le_n21 | le_n12].
Abort.

(**
#</div>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 4.1.3 and 4.1.4 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#


----------------------------------------------------------
#<div class="slide">#
** The reflect predicate and other specs

#<div>#
*)
Print Bool.reflect.
About andP.

Lemma example a b : a && b ==> (a == b).
Proof. by case: andP => // [[-> ->]].  Qed.

About ifP.

(**
#</div>#





#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 4.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#


*)
