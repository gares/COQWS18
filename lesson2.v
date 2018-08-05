
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Proofs (in a library)

Today we learn how to state and prove theorems.
We don't do that in void, nor without a methodology.

We work on top of the Mathematical Components library
and we follow the Small Scale reflection approach.

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Formal statements

Most of the statements that we consider in Mathematical
Components are equalities.

It is not surprising one can equate two numbers.

#<div>#
*)
Lemma addnA (m n k : nat) : m + (n + k) = m + n + k.
Abort.
(**
#</div>#

In lesson 1 we have defined many boolean tests that can
play the role of (decidable) predicates.

#<div>#
*)
Check 3 <= 4. (* not a statement *)
Check (3 <= 4) = true. (* a statement we can prove *)
(**
#</div>#

Motto: whenever possible predicates are expressed as a programs.

This choice has a deep impact on the proofs we make in lesson 2 and 3 and
the way we can form new types in lesson 3.

More statements using equality and predicates in bool 

#<div>#
*)
Lemma eqn_leq m n : (m == n) = (m <= n) && (n <= m).
Abort.

Lemma leq0n (n : nat) : 0 <= n.
Abort.
(**
#</div>#

Notice that in the first statement [=] really means
"if and only if".

The last statement is valid thanks to the [is_true]
"coercion" automatically inserted by Coq.

#<div>#
*)
Check is_true.
(**
#</div>#

#$$~$$#

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#
----------------------------------------------------------
#<div class="slide">#
** Proofs by computation

Our statements are programs. Hence they compute!

The [by[]] tactic solves trivial goal (mostly) by
computation.

#<div>#
*)
Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof. by []. Qed.

Lemma leq0n n : 0 <= n.
Proof. by []. Qed.

Lemma ltn0 n : n.+1 <= 0 = false.
Proof. by []. Qed.

Lemma ltnS m n : (m.+1 <= n.+1) = (m <= n).
Proof. by []. Qed.
(**
#</div>#

Notice [_ < _] is just a notation for [_.+1 <= _].

Notice the naming convention.

#<div>#
*)

Print negb.
Locate "~~".

Lemma negbK (b : bool) : ~~ (~~ b) = b.
Proof. Fail by []. Abort.
(**
#</div>#

It is not always the case the computation solves all our
problems. In particular here there are no constructors to
consume, hence computation is stuck.

To prove [negbK] we need a case split.

#$$~$$#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.2.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#


----------------------------------------------------------
#<div class="slide">#
** Proofs by case analysis 

The proof of [negbK] requires a case analysis: given that
[b] is of type bool, it can only be [true] or [false].

The [case: term] command performs this proof step.

#<div>#
*)
Lemma negbK b : ~~ (~~ b) = b.
Proof.
case: b.
  by [].
by [].
Qed.

Lemma andbC (b1 b2 : bool) : b1 && b2 = b2 && b1.
Proof.
by case: b1; case: b2.
Qed.

Lemma orbN b : b || ~~ b.
Proof.
by case: b.
Qed.
(**
#</div>#

The constructors of [bool] have no arguments, but for
example the second constructor of [nat] has one.

In this case one has to complement the command by supplying
names for these arguments.

#<div>#
*)
Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
case: n => [| p].
  by [].
by [].
Qed.
(**
#</div>#

Sometimes case analysis is not enough.

[[
Fixpoint muln (m n : nat) : nat :=
  if m is p.+1 then n + muln p n else 0.
]]

#<div>#
*)
Print Nat.mul.
Lemma muln_eq0 m n :
(m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [|p].
  by [].
case: n => [|k]; last first. (* rotates the goals *)
  by [].
Abort.
(**
#</div>#

We don't know how to prove this yet.
But maybe someone proved it already...

#<div>#
*)
Search _ (_ * 0) in ssrnat. (*   :-(   *)
Search _ muln 0 in ssrnat.
Print right_zero.
Search right_zero.
(**
#</div>#

The [Search] command is quite primitive but also
your best friend. 

It takes a head pattern, the whildcard [_]
in the examples above, followed by term or patterns,
and finally a location, in this case the [ssrnat] library.

Our first attempt was unsuccessful because
standard properies (associativity, communtativity, ...)
are expressed in Mathematical Components using
higher order predicates.
In this way these lemmas are very consistent, but also
harder to find if one does not know that.

The second hit is what we need to complete the proof.

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 2.2.2 and 2.5 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by rewriting

The [rewrite] tactic uses an equation. If offers many
more flags than the ones we will see (hint: check the
Coq user manual, SSReflect chapter).

#<div>#
*)
Lemma muln_eq0 m n :
  (m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [ // |p].
case: n => [ |k //].
rewrite muln0.
by [].
Qed.
(**
#</div>#

Let's now look at another example to learn more
about [rewrite].

#<div>#
*)
Lemma leq_mul2l m n1 n2 :
  (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
rewrite /leq.
(* Search _ muln subn in ssrnat. *)
rewrite -mulnBr.
rewrite muln_eq0.
by [].
Qed.
(**
#</div>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.2.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

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

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 2: sum up

- [by []] trivial proofs (including computation)
- [case: m] case split
- [apply: t] backchain
- [rewrite t1 t2 //] rewrite
- [elim: n] induction
- [move=> n] naming

#</div>#


*)
