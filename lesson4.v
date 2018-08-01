
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----------------------------------------------------------
#<div class="slide">#
** title


overloading

#<div>#
*)
Check 3 == 4.
Check true == false.
Check [::] == [:: 2; 3; 4].

Eval lazy in 3 == 4.
Eval lazy in true == false.
Eval lazy in [::] == [:: 2; 3; 4].

Check (3, true) == (4, false).
Fail Check (fun x => x) == (fun y => y).
(**
#</div>#

# <img style="width: 100%" src="demo-support-master.svg"/>#

theory reuse, hyps

#<div>#
*)
About eqxx.
About eq_refl.
Lemma test_eq (* T x *) :
  (3 == 3) && (true == true) (* && x == x *).
Proof.
rewrite eqxx.
rewrite eqxx.
by [].
Qed.
(**
#</div>#

bigop

<div>#
*)

Lemma sum_odd_3 :
  \sum_(0 <= i < 3.*2 | odd i) i = 3^2.
Proof.
rewrite unlock /=.
by [].
Qed.

About big_mkcond.
About big_nat_recr.
Lemma sum_odd_3_bis :
  \sum_(0 <= i < 3.*2 | odd i) i = 3^2.
Proof.
rewrite big_mkcond big_nat_recr //= -big_mkcond /=.
Abort.

Lemma prod_odd_3_bis :
  \big[muln/1]_(0 <= i < 3.*2 | odd i) i = 3^2.
Proof.
rewrite big_mkcond big_nat_recr //= -big_mkcond /=.
Abort.

(**
#</div>#

- sub types








body

- item [verbatim code]
- item # $$ \frac{1}{2} $$ #

#<div>#
*)
Check nat.
(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
footnote
#<a href="https://example">a link</a>#
end footnote
#</div></div>#

#</div>#
*)
