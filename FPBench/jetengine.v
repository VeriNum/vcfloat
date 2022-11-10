Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition jetengine_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-20) (5)].

Definition jetengine_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list jetengine_bmap_list) in exact z).

Definition jetengine (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble (let t := (((((3)%F64 * x1)%F64 * x1)%F64 + ((2)%F64 * x2)%F64)%F64 - x1)%F64 in
  let t_42_ := (((((3)%F64 * x1)%F64 * x1)%F64 - ((2)%F64 * x2)%F64)%F64 - x1)%F64 in
  let d := ((x1 * x1)%F64 + (1)%F64)%F64 in
  let s := (t / d)%F64 in
  let s_42_ := (t_42_ / d)%F64 in
  (x1 + ((((((((((2)%F64 * x1)%F64 * s)%F64 * (s - (3)%F64)%F64)%F64 + ((x1 * x1)%F64 * (((4)%F64 * s)%F64 - (6)%F64)%F64)%F64)%F64 * d)%F64 + ((((3)%F64 * x1)%F64 * x1)%F64 * s)%F64)%F64 + ((x1 * x1)%F64 * x1)%F64)%F64 + x1)%F64 + ((3)%F64 * s_42_)%F64)%F64)%F64).

Definition jetengine_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) jetengine in exact e').

Lemma jetengine_bound:
	find_and_prove_roundoff_bound jetengine_bmap jetengine_expr.
Proof.
idtac "Starting jetengine".
time "jetengine" (
try (eexists; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2);
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_bisect v, i_depth 17) as H
end;
try (
eapply Rle_trans;
try apply H;
try apply Rle_refl)).
Defined.

Lemma check_jetengine_bound: ltac:(CheckBound jetengine_bound 2.89e02%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.