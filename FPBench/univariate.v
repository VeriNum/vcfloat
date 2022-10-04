From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition intro_45_example_45_mixed_bmap_list := [Build_varinfo Tsingle 1%positive (1) (999)].

Definition intro_45_example_45_mixed_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list intro_45_example_45_mixed_bmap_list) in exact z).

Definition intro_45_example_45_mixed (t : ftype Tsingle) := 
  cast Tsingle _ (let t_1 := let t1_2 := (t + (1)%F32)%F32 in
      (cast Tdouble _ (t) / cast Tdouble _ (t1_2))%F64 in
  cast Tsingle _ (t_1)).

Definition intro_45_example_45_mixed_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) intro_45_example_45_mixed in exact e').

Lemma intro_45_example_45_mixed_bound:
	find_and_prove_roundoff_bound intro_45_example_45_mixed_bmap intro_45_example_45_mixed_expr.
Proof.
idtac "Starting intro_45_example_45_mixed".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition intro_45_example_45_mixed_bound_val := Eval simpl in intro_45_example_45_mixed_bound.
Compute ltac:(ShowBound' intro_45_example_45_mixed_bound_val).

Definition carbongas_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (5e-1)].

Definition carbongas_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list carbongas_bmap_list) in exact z).

Definition carbongas (v : ftype Tdouble) := 
  cast Tdouble _ (let p := (35e6)%F64 in
  let a := (401e-3)%F64 in
  let b := (427e-7)%F64 in
  let t := (300)%F64 in
  let n := (1000)%F64 in
  let k := (13806503e-30)%F64 in
  (((p + ((a * (n / v)%F64)%F64 * (n / v)%F64)%F64)%F64 * (v - (n * b)%F64)%F64)%F64 - ((k * n)%F64 * t)%F64)%F64).

Definition carbongas_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) carbongas in exact e').

Lemma carbongas_bound:
	find_and_prove_roundoff_bound carbongas_bmap carbongas_expr.
Proof.
idtac "Starting carbongas".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition carbongas_bound_val := Eval simpl in carbongas_bound.
Compute ltac:(ShowBound' carbongas_bound_val).

Definition nonlin1_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition nonlin1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list nonlin1_bmap_list) in exact z).

Definition nonlin1 (z : ftype Tdouble) := 
  cast Tdouble _ ((z / (z + (1)%F64)%F64)%F64).

Definition nonlin1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) nonlin1 in exact e').

Lemma nonlin1_bound:
	find_and_prove_roundoff_bound nonlin1_bmap nonlin1_expr.
Proof.
idtac "Starting nonlin1".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition nonlin1_bound_val := Eval simpl in nonlin1_bound.
Compute ltac:(ShowBound' nonlin1_bound_val).

Definition predatorprey_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition predatorprey_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list predatorprey_bmap_list) in exact z).

Definition predatorprey (x : ftype Tdouble) := 
  cast Tdouble _ (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  (((r * x)%F64 * x)%F64 / ((1)%F64 + ((x / k)%F64 * (x / k)%F64)%F64)%F64)%F64).

Definition predatorprey_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) predatorprey in exact e').

Lemma predatorprey_bound:
	find_and_prove_roundoff_bound predatorprey_bmap predatorprey_expr.
Proof.
idtac "Starting predatorprey".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition predatorprey_bound_val := Eval simpl in predatorprey_bound.
Compute ltac:(ShowBound' predatorprey_bound_val).

End WITHNANS.
Close R_scope.