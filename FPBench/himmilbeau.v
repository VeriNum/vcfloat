Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition himmilbeau_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-5) (5)].

Definition himmilbeau_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list himmilbeau_bmap_list) in exact z).

Definition himmilbeau (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
  cast Tdouble (let a := (((x1 * x1)%F64 + x2)%F64 - (11)%F64)%F64 in
  let b := ((x1 + (x2 * x2)%F64)%F64 - (7)%F64)%F64 in
  ((a * a)%F64 + (b * b)%F64)%F64).

Definition himmilbeau_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) himmilbeau in exact e').

Derive himmilbeau_b
SuchThat (forall vmap, prove_roundoff_bound himmilbeau_bmap vmap himmilbeau_expr himmilbeau_b)
As jetengine_bound.
Proof.
idtac "Starting himmilbeau".
time "himmilbeau" (
try (subst himmilbeau_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; prune_terms (cutoff 30); do_interval)).
Time Qed.

Lemma check_himmilbeau_bound: ltac:(CheckBound himmilbeau_b 2.31e-12%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.