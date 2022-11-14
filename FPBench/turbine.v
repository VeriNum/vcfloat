Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.


Definition turbine1_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine1 in exact e').

Derive turbine1_b 
SuchThat (forall vmap, prove_roundoff_bound turbine1_bmap vmap turbine1_expr turbine1_b)
As turbine1_bound.
Proof.
idtac "Starting turbine1".
time "turbine1" (
try (subst turbine1_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; error_rewrites);
try (prune_terms (cutoff 70);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end);
try rewrite Rsqr_pow2;
try field_simplify_Rabs;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( i_bisect vxH,
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect vxH, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'; apply H'; apply Rle_refl
end).
Qed.

Lemma check_turbine1_bound: ltac:(CheckBound turbine1_b 7.9e-14%F64).
Proof. reflexivity. Qed.

Definition turbine2_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine2_bmap_list) in exact z).

Definition turbine2 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble (((((6)%F64 * v)%F64 - ((((5e-1)%F64 * v)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (25e-1)%F64)%F64).

Definition turbine2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine2 in exact e').

Derive turbine2_b 
SuchThat (forall vmap, prove_roundoff_bound turbine2_bmap vmap turbine2_expr turbine2_b)
As turbine2_bound.
Proof.
idtac "Starting turbine2".
time "turbine2" (
try (subst turbine2_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try prove_roundoff_bound2;
try error_rewrites;
try ((prune_terms (cutoff 70);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end));
try rewrite Rsqr_pow2;
try field_simplify_Rabs;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( i_bisect vxH,
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect vxH, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'; apply H'; apply Rle_refl
end).
Qed.

Lemma check_turbine2_bound: ltac:(CheckBound turbine2_b 1.2e-13%F64).
Proof. reflexivity. Qed.

Definition turbine3_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine3_bmap_list) in exact z).

Definition turbine3 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) : ftype Tdouble := 
  ((( (3 -  (2 / (r * r))) - (( (125e-3 * (1 + (2 * v))) *  (((w * w) * r) * r)) / (1 - v))) - (5e-1))%F64).

Definition turbine3_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine3 in exact e').

Derive turbine3_b 
SuchThat (forall vmap, prove_roundoff_bound turbine3_bmap vmap turbine3_expr turbine3_b)
As turbine3_bound.
Proof.
idtac "Starting turbine3".
time "turbine3" (
try (subst turbine3_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try prove_roundoff_bound2;
try error_rewrites;
try ((prune_terms (cutoff 70);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end));
(try rewrite Rsqr_pow2;
try field_simplify_Rabs;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( i_bisect vxH,
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect vxH, i_depth 20) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'; apply H'; apply Rle_refl
end)).
Qed.

Lemma check_turbine3_bound: ltac:(CheckBound turbine3_b 6.1e-14%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.