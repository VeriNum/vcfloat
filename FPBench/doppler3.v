Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.


Definition _u : ident := 1%positive.
Definition _v : ident := 2%positive.
Definition _t : ident := 3%positive.

Definition doppler3_bmap_list := [Build_varinfo Tdouble _u (-30) (120);Build_varinfo Tdouble _v (320) (20300);Build_varinfo Tdouble _t (-50) (30)].

Definition doppler3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler3_bmap_list) in exact z).

Definition doppler3 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler3_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([_u;_v;_t]) doppler3 in exact e').

Derive doppler3_b 
SuchThat (forall vmap, prove_roundoff_bound doppler3_bmap vmap doppler3_expr doppler3_b)
As doppler3_bound.
Proof.
idtac "Starting doppler3".
time "doppler3" (
(subst doppler3_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; error_rewrites;
((prune_terms (cutoff 30);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end)));
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v_v, 
 i_depth 14) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v_t, 
i_bisect v_u, i_depth 14) as H'; apply H'; apply Rle_refl
end).
Time Qed.

Lemma check_doppler3_bound: ltac:(CheckBound doppler3_b 2.0e-13%F64).
Proof. reflexivity. Qed.


End WITHNANS.
Close Scope R_scope.