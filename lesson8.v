
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** Lesson 8: summary

- interfaces and hierarchies
- subtypes

Let's remember the truth:

#<div style='color: red; font-size: 150%;'>#
Coq is an object oriented
programming language.
#</div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Sub types

A sub type extends another type by adding a property.
The new type has a richer theory.
The new type inherits the original theory.

Let's define the type of homogeneous tuples

#<div>#
*)

Module Tup.

Structure tuple_of n T := Tuple {
  tval  :> seq T;
  tsize :  size tval == n
}.
Notation "n .-tuple" := (tuple_of n) : type_scope.

Lemma size_tuple T n (t : n .-tuple T) : size t = n.
Proof. by case: t => s /= /eqP. Qed.

Example seq_on_tuple n (t : n .-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. 
by rewrite map_rev revK size_map.
Undo.
rewrite size_tuple.
Fail rewrite size_tuple.
Abort.


(**
#</div>#

We instrument Coq to automatically promote
sequences to tuples.

#<div>#
*)

Lemma rev_tupleP n A (t : n .-tuple A) : size (rev t) == n.
Proof. by rewrite size_rev size_tuple. Qed.
Canonical rev_tuple n A (t : n .-tuple A) := Tuple (rev_tupleP t).

Lemma map_tupleP n A B (f: A -> B) (t: n .-tuple A) : size (map f t) == n.
Proof. by rewrite size_map size_tuple. Qed.
Canonical map_tuple n A B (f: A -> B) (t: n .-tuple A) := Tuple (map_tupleP f t).

Example seq_on_tuple2 n (t : n .-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof. rewrite size_tuple. rewrite size_tuple. by []. Qed.

(**
#</div>#

Now we the tuple type to form an eqType,
exactly as seq does.

Which is the expected comparison for tuples?

#<div>#
*)

Lemma p1 : size [:: 1;2] == 2. Proof. by []. Qed.
Lemma p2 : size ([:: 1] ++ [::2]) == 2. Proof. by rewrite cat_cons cat0s. Qed.

Definition t1 := {| tval := [::1;2];        tsize := p1 |}.
Definition t2 := {| tval := [::1] ++ [::2]; tsize := p2 |}.

Lemma tuple_uip : t1 = t2.
Proof.
rewrite /t1 /t2. rewrite /=.
Fail by [].
congr (Tuple _).
Fail by [].
(*About bool_irrelevance.*)
apply: bool_irrelevance.
Qed.

(**
#</div>#

Given that propositions are expressed (whenever possible)
as booleans we can systematically prove that proofs
of these properties are irrelevant.

As a consequence we can form subtypes and systematically
prove that the projection to the supertype is injective,
that means we can craft an eqType.

#<div>#
*)


Canonical tuple_subType n T := Eval hnf in [subType for (@tval n T)].
Definition tuple_eqMixin n (T : eqType) := Eval hnf in [eqMixin of n .-tuple T by <:].
Canonical tuple_eqType n (T : eqType) := Eval hnf in EqType (n .-tuple T) (tuple_eqMixin n T).

Check [eqType of 3.-tuple nat].

Example test_eqtype (x y : 3.-tuple nat) : x == y -> True.
Proof.
move=> /eqP H.
Abort.

(**
#<div/>#

Tuples is not the only subtype part of the library.
Another one is ['I_n], the finite type of natural
numbers smaller than n.

#<div>#
*)
Print ordinal.

About tnth. (* like the safe nth function for vectors *)

End Tup.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 6.1 and 6.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Sum up

- subtypes add properties and inherit the theory of the supertype
  thanks to boolean predicates (UIP).
  In some cases the property can be inferred by Coq, letting one apply
  a lemma about the subtype on terms of the supertype.


#</div>#

*)
