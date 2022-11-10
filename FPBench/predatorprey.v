Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition predatorprey_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition predatorprey_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list predatorprey_bmap_list) in exact z).

Definition predatorprey (x : ftype Tdouble) := 
  cast Tdouble (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  (((r * x)%F64 * x)%F64 / ((1)%F64 + ((x / k)%F64 * (x / k)%F64)%F64)%F64)%F64).

Definition predatorprey_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) predatorprey in exact e').

Lemma predatorprey_bound:
	find_and_prove_roundoff_bound predatorprey_bmap predatorprey_expr.
Proof.
idtac "Starting predatorprey".
time "predatorprey" (
eexists; intro; prove_roundoff_bound;
try (prove_rndval; interval); try interval;
try ( prove_roundoff_bound2); try error_rewrites;
try (
(prune_terms (cutoff 70);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      try (interval_intro (Rabs e) with 
                      (i_taylor vxH, i_bisect vxH, i_depth 20) as G;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]);
                      try (interval_intro (Rabs e) as G;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]) end));
try (
try rewrite Rsqr_pow2;
try field_simplify_Rabs;
try match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) upper with 
(i_bisect vxH, i_depth 17) as H'
end; apply H')).
Defined.

Lemma check_predatorprey_bound: ltac:(CheckBound predatorprey_bound 3.1e-16%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.