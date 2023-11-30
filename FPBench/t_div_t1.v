Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
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

Derive t_div_t1_b 
SuchThat (forall vmap, prove_roundoff_bound t_div_t1_bmap vmap t_div_t1_expr t_div_t1_b)
As t_div_t1_bound.
idtac "Starting t_div_t1".
time "t_div_t1_bound" (
try (subst t_div_t1_b; intro; prove_roundoff_bound);
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
Time Qed.

Lemma check_t_div_t1_bound: ltac:(CheckBound t_div_t1_b 4.4e-16%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.
