
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
- stack model => :

#<p><br/><p>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by backward chaining

We learn two tactics.
- [move=> names] to introduce hypotheses in the context.
- [apply: term] to do backward reasoning.

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
elim: s1 z0 => [ // | x xs IH].
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
** Goal managament

- naming everything can become bothersome
- but, we should not let the system give random names
- we adopt some sort of "stack & heap" model

*** The stack model of a goal
#<div>#
#<pre>#
ci : Ti
…
dj := ej : Tj
…
Fk : Pk ci
…
=================
forall (xl : Tl) …,
let ym := bm in … in
Pn xl -> … ->
Conclusion
#</pre>#
#</div>#

#<div>#
*)
Axiom (Ti Tj Tl : Type) (ej bm : Tj).
Axiom (Pk : Ti -> Type) (Pn : Tl -> Type) (Conclusion : Type).

Lemma goal_model_example (ci : Ti) (dj : Tj := ej) (Fk : Pk ci) :
  forall (xl : Tl), let ym := bm in Pn xl -> Conclusion.
(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to section
#<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html##bookkeeping">Bookkeeping</a># of the online docmentation of the ssreflect proof language.
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
*** Managing the stack

- [tactic=> names] executes tactics, pops and names
- [tactic: names] pushes the named objects, then execute tactic
- [move] is the tactic that does nothing (no-op, [idtac])

#<div>#
*)
move=> xl ym pnxl.
move: ci Fk.
Abort.
(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** elim and case work on the top of the stack

#<div>#
[elim: x y z => [t u v | w] is the same as
- [move: x y z.]
- [elim.]
- [move=> t u v.] in one branch, [move=> w] in another.
#</div>#

#<div>#
*)
Lemma foldl_cat' T R f (z0 : R) (s1 s2 : seq T) :
  foldl f z0 (s1 ++ s2) = foldl f (foldl f z0 s1) s2.
Proof.
move: s1 z0.
elim.
  done.
move=> x xs IH.
move=> acc /=.
by rewrite IH.
Qed.
(**
#</div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** intro-pattern and discharge partterns

You can write
- [tactic=> i_item+] where i_item could be a name, [?], [_], [//], [/=], [//=], [->], ...
  - [?] name chosen by the system, no user access,
  - [_] remove the top of the stack (if possible),
  - [//] close trivial subgoals,
  - [/=] perform simplifications,
  - [//=] do both the previous,
  - [->] rewrite using the top of the stack, left to right,
  - [<-] same but right to left,
  - [{x}] clear name [x] from the context.

  cf #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html##introduction-in-the-context">ssreflect documentation on introduction to the context</a>#

- [tactic: d_item+] where d_item could be a name or a term with holes (pattern), ...
  - tactic must be [move], [case], [elim], [apply], [exact] or [congr],
  - [move: name] clears the name from the context,
  - [move: pattern] generalize a subterm of the goal that match the pattern,
  - [move: (name)] forces [name] to be a pattern, hence not clearing it.

  cf #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html##discharge">ssreflect documentation on discharge</a>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 3: sum up

- [apply: t] backward reasonning
- [=>] is pop and [:] is push
- [elim] induction on the top of the stack

#</div>#


*)
