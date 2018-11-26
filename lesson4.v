
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Lesson 4: summary

- Curry Howard: the big picture
  + dependent function space
- Predicates and connectives
  + introduction
  + elimination
- Induction
- Consistency
- Dependent elimination

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Curry Howard

We link typed programs to statements with a proof.

Let's play a game in which we use inductive types
as our satements.

#<div>#
*)

Check nat : Type.

Definition zero : nat := 0.

Lemma zero_bis : nat.
Proof.
apply: 0.
Qed.


(**
#</div>#

We learn that 0 is a term of type nat, but Coq
also accepts it as a proof of nat.

In type theory: [p] is proof of [T] 
means that [p] inhabits the type [T].

Now let's look at the function space.

#<div>#
*)

Check nat -> nat  :  Type.

Definition silly : nat -> nat := fun x => x.

Lemma sillier : nat -> nat.
Proof. move=> x. apply: x. Show Proof. Qed.

(**
#</div>#

The function space [->] can represent implication.
An inhabitant of [A -> B] is a function turning
a proof of [A] into a proof of [B] (a program
taking in input a term of type [A] and returning
a term of type [B]).

The function space of type theory is *dependent*.

#<div>#
*)

Axiom P : nat -> Type.
Axiom p1 : P 1.


Check forall x, P x.
Check forall x : nat, P 1.

Check fun x : nat => p1.
     

(**
#</div>#

We could build (introduce) an arrow/forall using [fun].
Let's see how we can use (eliminate) an arrow/forall.

#<div>#
*)

Check factorial.
Check factorial 2.

Axiom px1 : forall x, P x.+1.

Check px1.
Check px1 3.

(**
#</div>#

Following the Curry Howard correspondence *application*
lets one call a function [f : A -> B] on [a : A] to
obtain a term of type [B]. If the type of [f] is
a dependent arrow (forall) [f : forall x : A, B x]
then the argument [a] appears in the type of
term we obtain, that is [f a] has type [B a].

In other words application instantiates universally
quantified lemmas.

Note: Any type can be put on the left of the arrow.

#<div>#
*)

Check seq.
Check (fun A : Type => seq A).

Check (fun A : Type => @nil A).


(**
#</div>#

So far we used [nat] (and [P]) as a predicate and [->] for implication.
Q: Can use inductive types to model other predicates or connectives?

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Predicates and connectives

Let's start with #$$ \top $$# and #$$ \bottom $$#

Here the label [Prop] could be a synonym of [Type].

#<div>#
*)

Print True.

Definition trivial1 : True := I.

Definition trivial2 : True -> nat :=
  fun t =>
    match t with I => 3 end.

Lemma trivial3 : True -> nat.
Proof.
move=> t. case: t. apply: 3.
Qed.

Print False.

Fail Definition hard1 : False := what.

Definition ex_falso A : False -> A :=
  fun abs => match abs with end.

Lemma ex_falso2 A : False -> A.
Proof.
move=> abs. case: abs.
Qed.

(**
#</div>#

Connectives

#<div>#
*)

Print and.

Definition and_intro (A B : Prop) : A -> B -> and A B :=
  fun a b => conj a b.

Lemma and_intro2 (A B : Prop) : A -> B -> and A B.
Proof.
move=> a b.
apply: conj a b.
Qed.

Definition and_elim_left (A B : Prop) : and A B -> A :=
  fun ab => match ab with conj a b => a end.


Lemma and_elim_left2 (A B : Prop) : and A B -> A.
Proof. case=> a b. apply: a. Qed.

Print or.

Definition or_elim (A B C : Prop) :
  A \/ B -> (A -> C) -> (B -> C) -> C :=
 fun aob a2c b2c =>
   match aob with
   | or_introl a => a2c a
   | or_intror b => b2c b
   end.

Print ex.

Lemma ex_elim A P : (exists x : A, P x) -> True.
Proof.
case => x px.
Abort.


(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#
----------------------------------------------------------
#<div class="slide">#
** Induction



#<div>#
*)

About nat_ind.

Definition ind :
  forall P : nat -> Prop,
    P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n :=
  fun P p0 pS =>
    fix IH n : P n :=
      match n with
      | O => p0
      | S p => pS p (IH p)
      end.

(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 4.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

----------------------------------------------------------
#<div class="slide">#
** Consistency

We give here the intuition why some terms that are in principle
well typed are rejected by Coq and why Coq is consistent.

#<div>#
*)
Print False.
Print True.
(**
#</div>#

What does it mean that [t : T] and [T] is not [False]?

#<div>#
*)
Check (match 3 with O => I | S _ => I end) : True.
(**
#</div>#

Constructors are not the only terms that can inhabit a type.
Hence we cannot simply look at terms, but we could look at
their normal form.

Subject reduction: [t : T] and [t ~> t1] then [t1 : T].
We claim there is not such [t1] (normal form) that
inhabits [False].

We have to reject [t] that don't have a normal form.

Exaustiveness of pattern matching:

#<div>#
*)
Lemma helper x : S x = 0 -> False. Proof. by []. Qed.
Fail Definition partial n : n = 0 -> False :=
  match n with
  | S x => fun p : S x = 0 => helper x p
(*  | 0 => fun _ => I*)
  end.
Fail Check partial 0 (erefl 0). (* : False *)
Fail Compute partial 0 (erefl 0). (* = ??? : False *)
(**
#</div>#

According to Curry Howard this means that in a case
split we did not forget to consider a branch!

Termination of recursion:

#<div>#
*)
Fail Fixpoint oops (n : nat) : False := oops n.+1.
Fail Check oops 3. (* : False *)
Fail Compute oops 3. (* = ??? : False *)
(**
#</div>#

According to Curry Howard this means that we did not
do any circular argument.

Non termination is subtle since a recursive call could
be hidden in a box.

#<div>#
*)
Fail Inductive hidden := Hide (f : hidden -> False).
Fail Definition oops (hf : hidden) : False := let: Hide f := hf in f hf.
Fail Check oops (Hide oops). (* : False *)
Fail Compute oops (Hide oops). (* = ??? : False *)
(**
#</div>#

This condition of inductive types is called positivity:
The type of [Hide] would be [(hidden -> False) -> hidden],
where the first occurrence of [hidden] is on the left (negative)
of the arrow.

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 3.2.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Lesson 4: sum up

- In Coq terms/types play a double role:
  + programs and their types
  + statements and their proofs
- Inductives can be used to model predicates and
  connectives
- Pattern machind and recursion can model induction
- The empty type is, well, empty, hence Coq is consistent
- TODO: dependent elim

#</div>#

*)
