From mathcomp Require Import all_ssreflect.

Implicit Type P Q R : Prop.

(** *** Exercise 0:
    - Define not. In type theory negation is defined in terms
      of [False].
*)

Definition not P := 
(*D*) P -> False
.

(** *** Exercise 1:
    - Prove the negation of the excluded middle.
*)
Lemma ex0 P : not (P /\ not P).
Proof.
(*D*)by move=> [p np]; apply: np; apply p.
Qed.

(** *** Exercise 2:
    - Declare iff (the constructor being called [iff_intro]).
*)
Inductive iff P Q :=
(*D*)  iff_intro (p2q : P -> Q) (q2p : Q -> P)
.


Definition iff1 P Q : iff P Q -> P -> Q :=
  fun x => match x with iff_intro f _ => f end.

Inductive xor P Q : Prop :=
(*D*) | xorL (p : P) (np : not Q)
(*D*) | xorR (no : not P) (q : Q)
.

Lemma xorC P Q : iff (xor P Q) (xor Q P).
Proof.
(*D*)apply: iff_intro; case=> [p nq|np q]; by [ apply: xorL | apply: xorR ].
Qed.

(** *** Exercise 4:
    - Declare exists2
    - Prove a lemma ex1 -> ex2 T
*)

Inductive ex2 T (P Q : pred T) : Prop :=
(*D*)  ex2_intro (x : T) (p : P x) (q : Q x)
.

Lemma ex2T T (P : pred T) : (exists x, P x) -> (ex2 T P P).
Proof. by case=> x px; apply: (ex2_intro _ _ _ x). Qed.


