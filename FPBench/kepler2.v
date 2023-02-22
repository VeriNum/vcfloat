Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition kepler2_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler2_bmap_list) in exact z).

Definition kepler2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - ((x1 * x3)%F64 * x5)%F64)%F64 - ((x1 * x2)%F64 * x6)%F64)%F64 - ((x4 * x5)%F64 * x6)%F64)%F64).

Definition kepler2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler2 in exact e').

Derive kepler2_b 
SuchThat (forall vmap, prove_roundoff_bound kepler2_bmap vmap kepler2_expr kepler2_b)
As kepler2_bound.
Proof.
idtac "Starting kepler2".
time "kepler2" (
try (subst kepler2_b; intro; prove_roundoff_bound);
try (prove_rndval; interval));
try (prove_roundoff_bound2; error_rewrites;
try (field_simplify_Rabs);
try ((prune_terms (cutoff 60));
 do_interval)).
Qed.

Lemma check_kepler2_bound: ltac:(CheckBound kepler2_b 6.2e-12%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.