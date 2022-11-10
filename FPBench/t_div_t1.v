Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition t_div_t1_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition t_div_t1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list t_div_t1_bmap_list) in exact z).

Definition t_div_t1 (z : ftype Tdouble) := 
  cast Tdouble ((z / (z + (1)%F64)%F64)%F64).

Definition t_div_t1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) t_div_t1 in exact e').

Lemma t_div_t1_bound:
	find_and_prove_roundoff_bound t_div_t1_bmap t_div_t1_expr.
Proof.
idtac "Starting t_div_t1".
time "t_div_t1_bound" (
try (eexists; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2);
try match goal with |-Rabs ?a <= _ =>
field_simplify a; try split; try field; try nra; try interval
end;
try match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_taylor vxH, i_degree 10, i_bisect vxH,
i_depth 10)
end;
try (
eapply Rle_trans;
try apply H;
try apply Rle_refl)).
Defined.

Lemma check_t_div_t1_bound: ltac:(CheckBound t_div_t1_bound 4.4e-16%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.
