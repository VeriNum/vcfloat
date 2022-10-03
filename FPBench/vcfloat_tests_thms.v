From vcfloat Require Import Automate FPLang FPLangOpt RAux Rounding Reify Float_notations Prune.
Require Import vcfloat_tests.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Section WITHNANS.
Context {NANS:Nans}.

Open Scope R_scope.

Lemma ex0_bound :
  forall vmap,
  prove_roundoff_bound ex0_bmap vmap ex0_expr 3.10862446895056e-12.
Proof.
intros.
time "prove_roundoff_bound" prove_roundoff_bound.
-
 time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.

(* How fast it runs on Andrew's machine with Intel core i7 processor:
Tactic call prove_roundoff_bound ran for 0. secs (0.u,0.s) (success)
Tactic call prove_rndval ran for 4.302 secs (4.312u,0.s) (success)
Tactic call interval ran for 3.243 secs (3.234u,0.s) (success)
Tactic call prove_roundoff_bound2 ran for 0.798 secs (0.765u,0.015s) (success)
Tactic call prune_terms ran for 0.182 secs (0.187u,0.s) (success)
Tactic call do_interval ran for 0.077 secs (0.078u,0.s) (success)
*)

(* Before improving the tactics on October 2, 2022, it was like,
Tactic call prove_roundoff_bound ran for 0.001 secs (0.u,0.s) (success)
Tactic call prove_rndval ran for 113.491 secs (111.484u,0.234s) (success)
Tactic call interval ran for 13.708 secs (13.531u,0.046s) (success) (total time for all 17 subgoals)
Tactic call prove_roundoff_bound2 ran for 6.464 secs (6.281u,0.046s) (success)
Tactic call prune_terms ran for 5.158 secs (5.031u,0.031s) (success)
Tactic call interval_intro ran for 0.498 secs (0.484u,0.s) (success)
Tactic call compute; lra ran for 0.131 secs (0.14u,0.s) (success)
*)

(* COMPARE TO
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 interval. *)
Qed.

Close Scope R_scope.

End WITHNANS.

