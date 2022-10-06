From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition turbine1_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine1 in exact e').
From Gappa Require Import Gappa_tactic.
From Coquelicot Require Import Coquelicot. 


Lemma turbine1_bound:
	find_and_prove_roundoff_bound turbine1_bmap turbine1_expr.
Proof.
idtac "Starting turbine1".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_bisect v, i_bisect v0, i_depth 20) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.


Definition turbine1_bound_val := Eval simpl in turbine1_bound.
Compute ltac:(ShowBound' turbine1_bound_val).

Definition turbine2_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine2_bmap_list) in exact z).

Definition turbine2 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((6)%F64 * v)%F64 - ((((5e-1)%F64 * v)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (25e-1)%F64)%F64).

Definition turbine2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine2 in exact e').

Lemma turbine2_bound:
	find_and_prove_roundoff_bound turbine2_bmap turbine2_expr.
Proof.
idtac "Starting turbine2".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_bisect v, i_bisect v0, i_depth 20) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Definition turbine2_bound_val := Eval simpl in turbine2_bound.
Compute ltac:(ShowBound' turbine2_bound_val).

Definition turbine3_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine3_bmap_list) in exact z).

Definition turbine3 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((3)%F64 - ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((1)%F64 + ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (5e-1)%F64)%F64).

Definition turbine3_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine3 in exact e').

Lemma turbine3_bound:
	find_and_prove_roundoff_bound turbine3_bmap turbine3_expr.
Proof.
idtac "Starting turbine3".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_bisect v, i_bisect v0, i_depth 20) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Definition turbine3_bound_val := Eval simpl in turbine3_bound.
Compute ltac:(ShowBound' turbine3_bound_val).

End WITHNANS.
Close Scope R_scope.