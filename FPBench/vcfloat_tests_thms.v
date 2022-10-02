From vcfloat Require Import Automate FPLang FPLangOpt RAux Rounding Reify Float_notations Prune.
Require Import vcfloat_tests.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Section WITHNANS.
Context {NANS:Nans}.

Open Scope R_scope.

Lemma ex0_bound :
  forall a  b  c  d  e  f  g  h  i,
  prove_roundoff_bound ex0_bmap (ex0_vmap a  b  c  d  e  f  g  h  i) ex0_expr 3.10862446895056e-12.
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
-
prove_roundoff_bound2.
time (
prune_terms (cutoff 30);
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end;
eapply Rle_trans; [ apply H99 | clear  ];
compute; lra).
(* COMPARE TO
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 interval. *)
Qed.

Close Scope R_scope.

End WITHNANS.

