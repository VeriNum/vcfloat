Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition predatorprey_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition predatorprey_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list predatorprey_bmap_list) in exact z).

Definition predatorprey (x : ftype Tdouble) := 
  cast Tdouble (let r := (4)%F64 in
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
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "error rewrites" error_rewrites. 
all : (time "prune"
(prune_terms (cutoff 70);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      try (interval_intro (Rabs e) with 
                      (i_taylor vxH, i_bisect vxH, i_depth 20) as G;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]);
                      try (interval_intro (Rabs e) as G;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]) end)).
{
time "goal 1" (
try rewrite Rsqr_pow2;
try field_simplify_Rabs;
try match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) upper with 
(i_bisect vxH, i_depth 17) as H'
end; apply H').
}
all : time "remaining" (
try rewrite Rsqr_pow2;
try match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) upper with 
(i_bisect vxH, i_depth 17) as H'
end; apply H').
Defined.

Check ltac:(ShowBound (proj1_sig predatorprey_bound)).

Goal proj1_sig predatorprey_bound <= 3.1e-16.
simpl; interval. Qed.

Definition verhulst_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition verhulst_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list verhulst_bmap_list) in exact z).

Definition verhulst (x : ftype Tdouble) := 
  cast Tdouble (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  ((r * x)%F64 / ((1)%F64 + (x / k)%F64)%F64)%F64).

Definition verhulst_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) verhulst in exact e').

Lemma verhulst_bound:
	find_and_prove_roundoff_bound verhulst_bmap verhulst_expr.
Proof.
idtac "Starting verhulst".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "field_simplify" match goal with |-Rabs ?a <= _ =>
field_simplify a ; try split; try unfold id; try field; try nra; try interval
end. 
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_depth 15) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Check ltac:(ShowBound (proj1_sig verhulst_bound)p).

Definition intro_45_example_45_mixed_bmap_list := [Build_varinfo Tsingle 1%positive (1) (999)].

Definition intro_45_example_45_mixed_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list intro_45_example_45_mixed_bmap_list) in exact z).

Definition intro_45_example_45_mixed (t : ftype Tsingle) := 
  cast Tsingle (let t_1 := let t1_2 := (t + (1)%F32)%F32 in
      (cast Tdouble (t) / cast Tdouble (t1_2))%F64 in
  cast Tsingle (t_1)).

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
time "prove_roundoff_bound2" prove_roundoff_bound2.
unfold id.
time "field_simplify" match goal with |-Rabs ?a <= _ =>
field_simplify a ; try split; try unfold id; try field; try nra; try interval
end. 
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_depth 15) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Check ltac:(ShowBound (proj1_sig intro_45_example_45_mixed_bound)).

Definition carbongas_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (5e-1)].

Definition carbongas_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list carbongas_bmap_list) in exact z).

Definition carbongas (v : ftype Tdouble) := 
  cast Tdouble (let p := (35e6)%F64 in
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
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "error rewrites" error_rewrites.
all : (time "prune"
(prune_terms (cutoff 60);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end)).
all: (try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      try (interval_intro (Rabs e) as G; 
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]) end).
all: (
try field_simplify_Rabs ;
try match goal with |-Rabs ?a <= _ =>
  try (interval_intro (Rabs a) upper with 
  (i_taylor vxH, i_bisect vxH, i_depth 15) as H' ; apply H');
  try (interval_intro (Rabs a) upper as H' ; apply H') end;
  apply Rle_refl).
Defined.


Check ltac:(ShowBound (proj1_sig carbongas_bound)).

Lemma check_doppler3_bound :
proj1_sig carbongas_bound <= 2.5e-8.
Proof.
simpl.
interval.
Qed.


Definition nonlin1_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition nonlin1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list nonlin1_bmap_list) in exact z).

Definition nonlin1 (z : ftype Tdouble) := 
  cast Tdouble ((z / (z + (1)%F64)%F64)%F64).

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
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "field_simplify" match goal with |-Rabs ?a <= _ =>
field_simplify a; try split; try field; try nra; try interval
end.
time "interval_intro" match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_taylor vxH, i_degree 10, i_bisect vxH,
i_depth 10)
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Check ltac:(ShowBound (proj1_sig nonlin1_bound)).


End WITHNANS.
Close Scope R_scope.