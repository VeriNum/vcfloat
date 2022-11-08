Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition kepler0_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler0_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler0_bmap_list) in exact z).

Definition kepler0 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble ((((((x2 * x5)%F64 + (x3 * x6)%F64)%F64 - (x2 * x3)%F64)%F64 - (x5 * x6)%F64)%F64 + (x1 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64)%F64).

Definition kepler0_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler0 in exact e').

Lemma kepler0_bound:
	find_and_prove_roundoff_bound kepler0_bmap kepler0_expr.
Proof.
idtac "Starting kepler0".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition kepler0_bound_val := Eval simpl in kepler0_bound.
Check ltac:(ShowBound kepler0_bound_val).

Definition kepler1_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2)].

Definition kepler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler1_bmap_list) in exact z).

Definition kepler1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) := 
  cast Tdouble (((((((((x1 * x4)%F64 * ((((-x1) + x2)%F64 + x3)%F64 - x4)%F64)%F64 + (x2 * (((x1 - x2)%F64 + x3)%F64 + x4)%F64)%F64)%F64 + (x3 * (((x1 + x2)%F64 - x3)%F64 + x4)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - (x1 * x3)%F64)%F64 - (x1 * x2)%F64)%F64 - x4)%F64).

Definition kepler1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive]) kepler1 in exact e').

Lemma kepler1_bound:
	find_and_prove_roundoff_bound kepler1_bmap kepler1_expr.
Proof.
idtac "Starting kepler1".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition kepler1_bound_val := Eval simpl in kepler1_bound.
Check ltac:(ShowBound kepler1_bound_val).

Definition kepler2_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler2_bmap_list) in exact z).

Definition kepler2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - ((x1 * x3)%F64 * x5)%F64)%F64 - ((x1 * x2)%F64 * x6)%F64)%F64 - ((x4 * x5)%F64 * x6)%F64)%F64).

Definition kepler2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler2 in exact e').

Lemma kepler2_bound:
	find_and_prove_roundoff_bound kepler2_bmap kepler2_expr.
Proof.
idtac "Starting kepler2".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "prune_terms" (prune_terms (cutoff 60)).
time "do_interval" do_interval.
Defined.

Definition kepler2_bound_val := Eval simpl in kepler2_bound.
Check ltac:(ShowBound kepler2_bound_val).

End WITHNANS.
Close Scope R_scope.