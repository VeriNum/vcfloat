Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition _x1: ident := 1%positive.
Definition _x2: ident := 2%positive.

Definition jetengine_bmap_list := [Build_varinfo Tdouble _x1 (-5) (5);
    Build_varinfo Tdouble _x2 (-20) (5)].

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
 ltac:(let e' :=  HO_reify_float_expr constr:([_x1;_x2]) jetengine in exact e').

Derive jetengine_b
SuchThat (forall vmap, prove_roundoff_bound jetengine_bmap vmap jetengine_expr jetengine_b)
As jetengine_bound.
Proof.
idtac "Starting jetengine".
time "jetengine" (
try (subst jetengine_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2);
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v_x1, i_bisect v_x2, i_depth 12) as H
end;
(*match type of H with _ <= _ <= ?A => pose (b := ltac:(ShowBound A)) end.
 unify (Binary.Bcompare _ _ b 2.13e3%F64) (Some Lt).*)
try (
eapply Rle_trans;
try apply H;
try apply Rle_refl)).
Time Qed.

Lemma check_jetengine_bound: ltac:(CheckBound jetengine_b 2.13e3%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.