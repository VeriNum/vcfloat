From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition nonlin2_bmap_list := [Build_varinfo Tdouble 1%positive (1001e-3) (2);Build_varinfo Tdouble 2%positive (1001e-3) (2)].

Definition nonlin2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list nonlin2_bmap_list) in exact z).

Definition nonlin2 (x : ftype Tdouble) (y : ftype Tdouble) := 
  cast Tdouble _ (let t := (x * y)%F64 in
  ((t - (1)%F64)%F64 / ((t * t)%F64 - (1)%F64)%F64)%F64).

Definition nonlin2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) nonlin2 in exact e').

Lemma nonlin2_bound:
	find_and_prove_roundoff_bound nonlin2_bmap nonlin2_expr.
Proof.
idtac "Starting nonlin2".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition nonlin2_bound_val := Eval simpl in nonlin2_bound.
Compute ltac:(ShowBound' nonlin2_bound_val).

Definition himmilbeau_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-5) (5)].

Definition himmilbeau_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list himmilbeau_bmap_list) in exact z).

Definition himmilbeau (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble _ (let a := (((x1 * x1)%F64 + x2)%F64 - (11)%F64)%F64 in
  let b := ((x1 + (x2 * x2)%F64)%F64 - (7)%F64)%F64 in
  ((a * a)%F64 + (b * b)%F64)%F64).

Definition himmilbeau_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) himmilbeau in exact e').

Lemma himmilbeau_bound:
	find_and_prove_roundoff_bound himmilbeau_bmap himmilbeau_expr.
Proof.
idtac "Starting himmilbeau".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition himmilbeau_bound_val := Eval simpl in himmilbeau_bound.
Compute ltac:(ShowBound' himmilbeau_bound_val).

Definition jetengine_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-20) (5)].

Definition jetengine_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list jetengine_bmap_list) in exact z).

Definition jetengine (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble _ (let t := (((((3)%F64 * x1)%F64 * x1)%F64 + ((2)%F64 * x2)%F64)%F64 - x1)%F64 in
  let t_42_ := (((((3)%F64 * x1)%F64 * x1)%F64 - ((2)%F64 * x2)%F64)%F64 - x1)%F64 in
  let d := ((x1 * x1)%F64 + (1)%F64)%F64 in
  let s := (t / d)%F64 in
  let s_42_ := (t_42_ / d)%F64 in
  (x1 + ((((((((((2)%F64 * x1)%F64 * s)%F64 * (s - (3)%F64)%F64)%F64 + ((x1 * x1)%F64 * (((4)%F64 * s)%F64 - (6)%F64)%F64)%F64)%F64 * d)%F64 + ((((3)%F64 * x1)%F64 * x1)%F64 * s)%F64)%F64 + ((x1 * x1)%F64 * x1)%F64)%F64 + x1)%F64 + ((3)%F64 * s_42_)%F64)%F64)%F64).

Definition jetengine_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) jetengine in exact e').

Lemma jetengine_bound:
	find_and_prove_roundoff_bound jetengine_bmap jetengine_expr.
Proof.
idtac "Starting jetengine".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition jetengine_bound_val := Eval simpl in jetengine_bound.
Compute ltac:(ShowBound' jetengine_bound_val).

End WITHNANS.
Close R_scope.