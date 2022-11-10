Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition rigidbody1_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody1_bmap_list) in exact z).

Definition rigidbody1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble (((((-(x1 * x2)%F64) - (((2)%F64 * x2)%F64 * x3)%F64)%F64 - x1)%F64 - x3)%F64).

Definition rigidbody1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody1 in exact e').

Lemma rigidbody1_bound:
	find_and_prove_roundoff_bound rigidbody1_bmap rigidbody1_expr.
Proof.
idtac "Starting rigidbody1".
time "rigidbody1" (
try (eexists; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; prune_terms (cutoff 30); do_interval)).
Defined.

Lemma check_rigidbody1_bound: ltac:(CheckBound rigidbody1_bound 3.1e-13%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.