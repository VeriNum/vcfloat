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

Definition doppler1_bmap_list := [
     Build_varinfo Tdouble _u (-100) (100);
     Build_varinfo Tdouble _v (20) (2e4);
     Build_varinfo Tdouble _t (-30) (50)].

Definition doppler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler1_bmap_list) in exact z).

Definition doppler1 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
  let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64.

Definition doppler1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([_u;_v;_t]) doppler1 in exact e').

Derive doppler1_b 
SuchThat (forall vmap, prove_roundoff_bound doppler1_bmap vmap doppler1_expr doppler1_b)
As doppler1_bound.
Proof.
idtac "Starting doppler1".
time "doppler1" (
(subst doppler1_b; intro; prove_roundoff_bound);
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
 i_depth 17) as H'; apply H'; apply Rle_refl
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v_u, 
i_bisect v_t, i_depth 17) as H'; apply H'; apply Rle_refl
end).
Qed.

Lemma check_doppler1_bound: ltac:(CheckBound doppler1_b 4.5e-13%F64).
Proof. reflexivity. Qed.


End WITHNANS.
Close Scope R_scope.