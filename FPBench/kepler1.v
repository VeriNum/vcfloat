Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition kepler1_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2)].

Definition kepler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler1_bmap_list) in exact z).

Definition kepler1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) := 
  cast Tdouble (((((((((x1 * x4)%F64 * ((((-x1) + x2)%F64 + x3)%F64 - x4)%F64)%F64 + (x2 * (((x1 - x2)%F64 + x3)%F64 + x4)%F64)%F64)%F64 + (x3 * (((x1 + x2)%F64 - x3)%F64 + x4)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - (x1 * x3)%F64)%F64 - (x1 * x2)%F64)%F64 - x4)%F64).

Definition kepler1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive]) kepler1 in exact e').

Derive kepler1_b 
SuchThat (forall vmap, prove_roundoff_bound kepler1_bmap vmap kepler1_expr kepler1_b)
As kepler1_bound.
Proof.
idtac "Starting kepler1".
time "kepler1" (
try (subst kepler1_b; intro; prove_roundoff_bound);
try (prove_rndval; interval));
try (prove_roundoff_bound2; error_rewrites;
try (field_simplify_Rabs);
try ((prune_terms (cutoff 30));
 do_interval)).
Qed.

Lemma check_kepler1_bound: ltac:(CheckBound kepler1_b 1.6e-12%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.