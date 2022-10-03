From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition matrixdeterminant_bmap_list := [Build_varinfo Tdouble 1%positive (-10) (10);Build_varinfo Tdouble 2%positive (-10) (10);Build_varinfo Tdouble 3%positive (-10) (10);Build_varinfo Tdouble 4%positive (-10) (10);Build_varinfo Tdouble 5%positive (-10) (10);Build_varinfo Tdouble 6%positive (-10) (10);Build_varinfo Tdouble 7%positive (-10) (10);Build_varinfo Tdouble 8%positive (-10) (10);Build_varinfo Tdouble 9%positive (-10) (10)].

Definition matrixdeterminant_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list matrixdeterminant_bmap_list) in exact z).

Definition matrixdeterminant (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := 
  cast Tdouble _ ((((((a * e)%F64 * i)%F64 + ((b * f)%F64 * g)%F64)%F64 + ((c * d)%F64 * h)%F64)%F64 - ((((c * e)%F64 * g)%F64 + ((b * d)%F64 * i)%F64)%F64 + ((a * f)%F64 * h)%F64)%F64)%F64).

Definition matrixdeterminant_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive]) matrixdeterminant in exact e').

Lemma matrixdeterminant_bound:
	find_and_prove_roundoff_bound matrixdeterminant_bmap matrixdeterminant_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition matrixdeterminant_bound_val := Eval simpl in (proj1_sig matrixdeterminant_bound).
Print matrixdeterminant_bound_val.

Definition matrixdeterminant2_bmap_list := [Build_varinfo Tdouble 1%positive (-10) (10);Build_varinfo Tdouble 2%positive (-10) (10);Build_varinfo Tdouble 3%positive (-10) (10);Build_varinfo Tdouble 4%positive (-10) (10);Build_varinfo Tdouble 5%positive (-10) (10);Build_varinfo Tdouble 6%positive (-10) (10);Build_varinfo Tdouble 7%positive (-10) (10);Build_varinfo Tdouble 8%positive (-10) (10);Build_varinfo Tdouble 9%positive (-10) (10)].

Definition matrixdeterminant2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list matrixdeterminant2_bmap_list) in exact z).

Definition matrixdeterminant2 (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := 
  cast Tdouble _ ((((a * (e * i)%F64)%F64 + ((g * (b * f)%F64)%F64 + (c * (d * h)%F64)%F64)%F64)%F64 - ((e * (c * g)%F64)%F64 + ((i * (b * d)%F64)%F64 + (a * (f * h)%F64)%F64)%F64)%F64)%F64).

Definition matrixdeterminant2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive]) matrixdeterminant2 in exact e').

Lemma matrixdeterminant2_bound:
	find_and_prove_roundoff_bound matrixdeterminant2_bmap matrixdeterminant2_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition matrixdeterminant2_bound_val := Eval simpl in (proj1_sig matrixdeterminant2_bound).
Print matrixdeterminant2_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
(*
time "prove_rndval" prove_rndval; time "interval" interval.*)
admit.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Admitted.

Definition intro_45_example_45_mixed_bound_val := Eval simpl in (proj1_sig intro_45_example_45_mixed_bound).
Print intro_45_example_45_mixed_bound_val.

Definition delta4_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta4_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta4_bmap_list) in exact z).

Definition delta4 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ ((((((((-x2) * x3)%F64 - (x1 * x4)%F64)%F64 + (x2 * x5)%F64)%F64 + (x3 * x6)%F64)%F64 - (x5 * x6)%F64)%F64 + (x1 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64)%F64).

Definition delta4_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta4 in exact e').

Lemma delta4_bound:
	find_and_prove_roundoff_bound delta4_bmap delta4_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition delta4_bound_val := Eval simpl in (proj1_sig delta4_bound).
Print delta4_bound_val.

Definition delta_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta_bmap_list) in exact z).

Definition delta (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 + (((-x2) * x3)%F64 * x4)%F64)%F64 + (((-x1) * x3)%F64 * x5)%F64)%F64 + (((-x1) * x2)%F64 * x6)%F64)%F64 + (((-x4) * x5)%F64 * x6)%F64)%F64).

Definition delta_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta in exact e').

Lemma delta_bound:
	find_and_prove_roundoff_bound delta_bmap delta_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
(*
time "prove_rndval" prove_rndval; time "interval" interval.*)
admit.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Admitted.

Definition delta_bound_val := Eval simpl in (proj1_sig delta_bound).
Print delta_bound_val.

Definition x_by_xy_bmap_list := [Build_varinfo Tsingle 1%positive (1) (4);Build_varinfo Tsingle 2%positive (1) (4)].

Definition x_by_xy_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list x_by_xy_bmap_list) in exact z).

Definition x_by_xy (x : ftype Tsingle) (y : ftype Tsingle) := 
  cast Tsingle _ ((x / (x + y)%F32)%F32).

Definition x_by_xy_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) x_by_xy in exact e').

Lemma x_by_xy_bound:
	find_and_prove_roundoff_bound x_by_xy_bmap x_by_xy_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
(*
time "prove_rndval" prove_rndval; time "interval" interval.*)
admit.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Admitted.

Definition x_by_xy_bound_val := Eval simpl in (proj1_sig x_by_xy_bound).
Print x_by_xy_bound_val.

Definition sum_bmap_list := [Build_varinfo Tdouble 1%positive (1) (2);Build_varinfo Tdouble 2%positive (1) (2);Build_varinfo Tdouble 3%positive (1) (2)].

Definition sum_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list sum_bmap_list) in exact z).

Definition sum (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble _ (let p0 := ((x0 + x1)%F64 - x2)%F64 in
  let p1 := ((x1 + x2)%F64 - x0)%F64 in
  let p2 := ((x2 + x0)%F64 - x1)%F64 in
  ((p0 + p1)%F64 + p2)%F64).

Definition sum_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) sum in exact e').

Lemma sum_bound:
	find_and_prove_roundoff_bound sum_bmap sum_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition sum_bound_val := Eval simpl in (proj1_sig sum_bound).
Print sum_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
(*
time "prove_rndval" prove_rndval; time "interval" interval.*)
admit.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Admitted.

Definition nonlin1_bound_val := Eval simpl in (proj1_sig nonlin1_bound).
Print nonlin1_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
(*
time "prove_rndval" prove_rndval; time "interval" interval.*)
admit.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Admitted.

Definition nonlin2_bound_val := Eval simpl in (proj1_sig nonlin2_bound).
Print nonlin2_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition himmilbeau_bound_val := Eval simpl in (proj1_sig himmilbeau_bound).
Print himmilbeau_bound_val.

Definition kepler0_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler0_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler0_bmap_list) in exact z).

Definition kepler0 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ ((((((x2 * x5)%F64 + (x3 * x6)%F64)%F64 - (x2 * x3)%F64)%F64 - (x5 * x6)%F64)%F64 + (x1 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64)%F64).

Definition kepler0_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler0 in exact e').

Lemma kepler0_bound:
	find_and_prove_roundoff_bound kepler0_bmap kepler0_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition kepler0_bound_val := Eval simpl in (proj1_sig kepler0_bound).
Print kepler0_bound_val.

Definition kepler1_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2)].

Definition kepler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler1_bmap_list) in exact z).

Definition kepler1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) := 
  cast Tdouble _ (((((((((x1 * x4)%F64 * ((((-x1) + x2)%F64 + x3)%F64 - x4)%F64)%F64 + (x2 * (((x1 - x2)%F64 + x3)%F64 + x4)%F64)%F64)%F64 + (x3 * (((x1 + x2)%F64 - x3)%F64 + x4)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - (x1 * x3)%F64)%F64 - (x1 * x2)%F64)%F64 - x4)%F64).

Definition kepler1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive]) kepler1 in exact e').

Lemma kepler1_bound:
	find_and_prove_roundoff_bound kepler1_bmap kepler1_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition kepler1_bound_val := Eval simpl in (proj1_sig kepler1_bound).
Print kepler1_bound_val.

Definition kepler2_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler2_bmap_list) in exact z).

Definition kepler2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - ((x1 * x3)%F64 * x5)%F64)%F64 - ((x1 * x2)%F64 * x6)%F64)%F64 - ((x4 * x5)%F64 * x6)%F64)%F64).

Definition kepler2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler2 in exact e').

Lemma kepler2_bound:
	find_and_prove_roundoff_bound kepler2_bmap kepler2_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition kepler2_bound_val := Eval simpl in (proj1_sig kepler2_bound).
Print kepler2_bound_val.

Definition intro_45_example_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition intro_45_example_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list intro_45_example_bmap_list) in exact z).

Definition intro_45_example (t : ftype Tdouble) := 
  cast Tdouble _ ((t / (t + (1)%F64)%F64)%F64).

Definition intro_45_example_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) intro_45_example in exact e').

Lemma intro_45_example_bound:
	find_and_prove_roundoff_bound intro_45_example_bmap intro_45_example_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition intro_45_example_bound_val := Eval simpl in (proj1_sig intro_45_example_bound).
Print intro_45_example_bound_val.

Definition sec4_45_example_bmap_list := [Build_varinfo Tdouble 1%positive (1001e-3) (2);Build_varinfo Tdouble 2%positive (1001e-3) (2)].

Definition sec4_45_example_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list sec4_45_example_bmap_list) in exact z).

Definition sec4_45_example (x : ftype Tdouble) (y : ftype Tdouble) := 
  cast Tdouble _ (let t := (x * y)%F64 in
  ((t - (1)%F64)%F64 / ((t * t)%F64 - (1)%F64)%F64)%F64).

Definition sec4_45_example_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) sec4_45_example in exact e').

Lemma sec4_45_example_bound:
	find_and_prove_roundoff_bound sec4_45_example_bmap sec4_45_example_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition sec4_45_example_bound_val := Eval simpl in (proj1_sig sec4_45_example_bound).
Print sec4_45_example_bound_val.

Definition rump_39_s_32_example_44__32_from_32_c_32_program_bmap_list := [Build_varinfo Tdouble 1%positive (0) (77617);Build_varinfo Tdouble 2%positive (0) (33096)].

Definition rump_39_s_32_example_44__32_from_32_c_32_program_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rump_39_s_32_example_44__32_from_32_c_32_program_bmap_list) in exact z).

Definition rump_39_s_32_example_44__32_from_32_c_32_program (a : ftype Tdouble) (b : ftype Tdouble) := 
  cast Tdouble _ (let b2 := (b * b)%F64 in
  let b4 := (b2 * b2)%F64 in
  let b6 := (b4 * b2)%F64 in
  let b8 := (b4 * b4)%F64 in
  let a2 := (a * a)%F64 in
  let firstexpr := ((((((11)%F64 * a2)%F64 * b2)%F64 - b6)%F64 - ((121)%F64 * b4)%F64)%F64 - (2)%F64)%F64 in
  (((((33375e-2)%F64 * b6)%F64 + (a2 * firstexpr)%F64)%F64 + ((55e-1)%F64 * b8)%F64)%F64 + (a / ((2)%F64 * b)%F64)%F64)%F64).

Definition rump_39_s_32_example_44__32_from_32_c_32_program_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) rump_39_s_32_example_44__32_from_32_c_32_program in exact e').

Lemma rump_39_s_32_example_44__32_from_32_c_32_program_bound:
	find_and_prove_roundoff_bound rump_39_s_32_example_44__32_from_32_c_32_program_bmap rump_39_s_32_example_44__32_from_32_c_32_program_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition rump_39_s_32_example_44__32_from_32_c_32_program_bound_val := Eval simpl in (proj1_sig rump_39_s_32_example_44__32_from_32_c_32_program_bound).
Print rump_39_s_32_example_44__32_from_32_c_32_program_bound_val.

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap_list := [Build_varinfo Tdouble 1%positive (0) (77617);Build_varinfo Tdouble 2%positive (0) (33096)].

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap_list) in exact z).

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point (a : ftype Tdouble) (b : ftype Tdouble) := 
  cast Tdouble _ (let b2 := (b * b)%F64 in
  let b4 := (b2 * b2)%F64 in
  let b6 := (b4 * b2)%F64 in
  let b8 := (b4 * b4)%F64 in
  let a2 := (a * a)%F64 in
  let firstexpr := (((((11)%F64 * a2)%F64 * b2)%F64 - ((121)%F64 * b4)%F64)%F64 - (2)%F64)%F64 in
  ((((((33375e-2)%F64 - a2)%F64 * b6)%F64 + (a2 * firstexpr)%F64)%F64 + ((55e-1)%F64 * b8)%F64)%F64 + (a / ((2)%F64 * b)%F64)%F64)%F64).

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) rump_39_s_32_example_32_revisited_32_for_32_floating_32_point in exact e').

Lemma rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bound:
	find_and_prove_roundoff_bound rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bound_val := Eval simpl in (proj1_sig rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bound).
Print rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bound_val.

Definition doppler1_bmap_list := [Build_varinfo Tdouble 1%positive (-100) (100);Build_varinfo Tdouble 2%positive (20) (2e4);Build_varinfo Tdouble 3%positive (-30) (50)].

Definition doppler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler1_bmap_list) in exact z).

Definition doppler1 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble _ (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler1 in exact e').

Lemma doppler1_bound:
	find_and_prove_roundoff_bound doppler1_bmap doppler1_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition doppler1_bound_val := Eval simpl in (proj1_sig doppler1_bound).
Print doppler1_bound_val.

Definition doppler2_bmap_list := [Build_varinfo Tdouble 1%positive (-125) (125);Build_varinfo Tdouble 2%positive (15) (25000);Build_varinfo Tdouble 3%positive (-40) (60)].

Definition doppler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler2_bmap_list) in exact z).

Definition doppler2 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble _ (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler2 in exact e').

Lemma doppler2_bound:
	find_and_prove_roundoff_bound doppler2_bmap doppler2_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition doppler2_bound_val := Eval simpl in (proj1_sig doppler2_bound).
Print doppler2_bound_val.

Definition doppler3_bmap_list := [Build_varinfo Tdouble 1%positive (-30) (120);Build_varinfo Tdouble 2%positive (320) (20300);Build_varinfo Tdouble 3%positive (-50) (30)].

Definition doppler3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler3_bmap_list) in exact z).

Definition doppler3 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble _ (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler3_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler3 in exact e').

Lemma doppler3_bound:
	find_and_prove_roundoff_bound doppler3_bmap doppler3_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition doppler3_bound_val := Eval simpl in (proj1_sig doppler3_bound).
Print doppler3_bound_val.

Definition rigidbody1_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody1_bmap_list) in exact z).

Definition rigidbody1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble _ (((((-(x1 * x2)%F64) - (((2)%F64 * x2)%F64 * x3)%F64)%F64 - x1)%F64 - x3)%F64).

Definition rigidbody1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody1 in exact e').

Lemma rigidbody1_bound:
	find_and_prove_roundoff_bound rigidbody1_bmap rigidbody1_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition rigidbody1_bound_val := Eval simpl in (proj1_sig rigidbody1_bound).
Print rigidbody1_bound_val.

Definition rigidbody2_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody2_bmap_list) in exact z).

Definition rigidbody2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble _ (((((((((2)%F64 * x1)%F64 * x2)%F64 * x3)%F64 + (((3)%F64 * x3)%F64 * x3)%F64)%F64 - (((x2 * x1)%F64 * x2)%F64 * x3)%F64)%F64 + (((3)%F64 * x3)%F64 * x3)%F64)%F64 - x2)%F64).

Definition rigidbody2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody2 in exact e').

Lemma rigidbody2_bound:
	find_and_prove_roundoff_bound rigidbody2_bmap rigidbody2_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition rigidbody2_bound_val := Eval simpl in (proj1_sig rigidbody2_bound).
Print rigidbody2_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition jetengine_bound_val := Eval simpl in (proj1_sig jetengine_bound).
Print jetengine_bound_val.

Definition turbine1_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine1 in exact e').

Lemma turbine1_bound:
	find_and_prove_roundoff_bound turbine1_bmap turbine1_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition turbine1_bound_val := Eval simpl in (proj1_sig turbine1_bound).
Print turbine1_bound_val.

Definition turbine2_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine2_bmap_list) in exact z).

Definition turbine2 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((6)%F64 * v)%F64 - ((((5e-1)%F64 * v)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (25e-1)%F64)%F64).

Definition turbine2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine2 in exact e').

Lemma turbine2_bound:
	find_and_prove_roundoff_bound turbine2_bmap turbine2_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition turbine2_bound_val := Eval simpl in (proj1_sig turbine2_bound).
Print turbine2_bound_val.

Definition turbine3_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine3_bmap_list) in exact z).

Definition turbine3 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((3)%F64 - ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((1)%F64 + ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (5e-1)%F64)%F64).

Definition turbine3_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine3 in exact e').

Lemma turbine3_bound:
	find_and_prove_roundoff_bound turbine3_bmap turbine3_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition turbine3_bound_val := Eval simpl in (proj1_sig turbine3_bound).
Print turbine3_bound_val.

Definition verhulst_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition verhulst_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list verhulst_bmap_list) in exact z).

Definition verhulst (x : ftype Tdouble) := 
  cast Tdouble _ (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  ((r * x)%F64 / ((1)%F64 + (x / k)%F64)%F64)%F64).

Definition verhulst_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) verhulst in exact e').

Lemma verhulst_bound:
	find_and_prove_roundoff_bound verhulst_bmap verhulst_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition verhulst_bound_val := Eval simpl in (proj1_sig verhulst_bound).
Print verhulst_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition predatorprey_bound_val := Eval simpl in (proj1_sig predatorprey_bound).
Print predatorprey_bound_val.

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
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition carbongas_bound_val := Eval simpl in (proj1_sig carbongas_bound).
Print carbongas_bound_val.

Definition sqroot_bmap_list := [Build_varinfo Tdouble 1%positive (0) (1)].

Definition sqroot_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list sqroot_bmap_list) in exact z).

Definition sqroot (x : ftype Tdouble) := 
  cast Tdouble _ ((((((1)%F64 + ((5e-1)%F64 * x)%F64)%F64 - (((125e-3)%F64 * x)%F64 * x)%F64)%F64 + ((((625e-4)%F64 * x)%F64 * x)%F64 * x)%F64)%F64 - (((((390625e-7)%F64 * x)%F64 * x)%F64 * x)%F64 * x)%F64)%F64).

Definition sqroot_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) sqroot in exact e').

Lemma sqroot_bound:
	find_and_prove_roundoff_bound sqroot_bmap sqroot_expr.
Proof.
eexists. intro. prove_roundoff_bound.
 -
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition sqroot_bound_val := Eval simpl in (proj1_sig sqroot_bound).
Print sqroot_bound_val.

End WITHNANS.
Close R_scope.