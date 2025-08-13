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

Definition doppler2_bmap_list := [
   Build_varinfo Tdouble _u (-125) (125);
   Build_varinfo Tdouble _v (15) (25000);
   Build_varinfo Tdouble _t (-40) (60)].

Definition doppler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler2_bmap_list) in exact z).

Definition doppler2 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
  cast Tdouble (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([_u;_v;_t]) doppler2 in exact e').

Derive doppler2_b
SuchThat (forall vmap, prove_roundoff_bound doppler2_bmap vmap doppler2_expr doppler2_b)
As doppler2_bound.
Proof.
idtac "Starting doppler2".
time "doppler2" (
(subst doppler2_b; intro; prove_roundoff_bound);
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
Time Qed.

Lemma check_doppler2_bound: ltac:(CheckBound doppler2_b 1.2e-12%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.