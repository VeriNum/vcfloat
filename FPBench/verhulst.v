Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition verhulst_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition verhulst_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list verhulst_bmap_list) in exact z).

Definition verhulst (x : ftype Tdouble) := 
  cast Tdouble (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  ((r * x)%F64 / ((1)%F64 + (x / k)%F64)%F64)%F64).

Definition verhulst_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) verhulst in exact e').

Derive verhulst_b 
SuchThat (forall vmap, prove_roundoff_bound verhulst_bmap vmap verhulst_expr verhulst_b)
As verhulst_bound.
Proof.
idtac "Starting verhulst".
time "verhulst" (
try (subst verhulst_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; field_simplify_Rabs);
try (eexists; intro; prove_roundoff_bound);
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_depth 15) as H
end;
try (
eapply Rle_trans;
try apply H;
try apply Rle_refl)).
Time Qed.

Lemma check_verhulst_bound: ltac:(CheckBound verhulst_b 2.33e-16%F64).
Proof. reflexivity. Qed.


End WITHNANS.
Close Scope R_scope.
