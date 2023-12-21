Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition carbongas_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (5e-1)].

Definition carbongas_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list carbongas_bmap_list) in exact z).

Definition carbongas (v : ftype Tdouble) := 
  cast Tdouble (let p := (35e6)%F64 in
  let a := (401e-3)%F64 in
  let b := (427e-7)%F64 in
  let t := (300)%F64 in
  let n := (1000)%F64 in
  let k := (13806503e-30)%F64 in
  (((p + ((a * (n / v)%F64)%F64 * (n / v)%F64)%F64)%F64 * (v - (n * b)%F64)%F64)%F64 - ((k * n)%F64 * t)%F64)%F64).

Definition carbongas_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) carbongas in exact e').


Derive carbongas_b 
SuchThat (forall vmap, prove_roundoff_bound carbongas_bmap vmap carbongas_expr carbongas_b)
As carbongas_bound.
Proof.
idtac "Starting carbongas".
time "carbongas" (
try (subst carbongas_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; error_rewrites);
try (
(prune_terms (cutoff 60);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end));
(try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      try (interval_intro (Rabs e) as G; 
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]) end);
try (
try field_simplify_Rabs ;
try match goal with |-Rabs ?a <= _ =>
  try (interval_intro (Rabs a) upper with 
  (i_taylor vxH, i_bisect vxH, i_depth 15) as H' ; apply H');
  try (interval_intro (Rabs a) upper as H' ; apply H') end;
  apply Rle_refl)).
Time Qed.

Lemma check_carbongas_bound: ltac:(CheckBound carbongas_b 2.5e-08%F64).
Proof. reflexivity. Qed.


End WITHNANS.
Close Scope R_scope.
