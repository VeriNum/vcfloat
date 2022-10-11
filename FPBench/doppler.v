From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.


Definition doppler1_bmap_list := [Build_varinfo Tdouble 1%positive (-100) (100);Build_varinfo Tdouble 2%positive (20) (2e4);Build_varinfo Tdouble 3%positive (-30) (50)].

Definition doppler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler1_bmap_list) in exact z).

Definition doppler1 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
  let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64.

Definition doppler1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler1 in exact e').

Lemma doppler1_bound:
	find_and_prove_roundoff_bound doppler1_bmap doppler1_expr.
Proof.
idtac "Starting doppler1".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.  
time "error rewrites" error_rewrites_div_r.
all : (time "prune"
(prune_terms (cutoff 30);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end)).
+
time "goal 1" (
field_simplify_Rabs;
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 2" (
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH,  
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 3" (
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 4" (
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
Defined.

Definition doppler1_bound_val := Eval simpl in doppler1_bound.
Compute ltac:(ShowBound doppler1_bound_val).

Lemma check_doppler_bound :
proj1_sig doppler1_bound_val <= 1.21e-12.
Proof.
simpl.
interval.
Qed.


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
idtac "Starting doppler2".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "error rewrites" error_rewrites_div_r. 
all : (time "prune"
(prune_terms (cutoff 30);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end)).
+ 
time "goal 1"(
field_simplify_Rabs;
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 2"(
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect vxH, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 3"(
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 4"(
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
Defined.

Definition doppler2_bound_val := Eval simpl in doppler2_bound.
Compute ltac:(ShowBound doppler2_bound_val).

Lemma check_doppler2_bound :
proj1_sig doppler2_bound_val <= 1.3e-12.
Proof.
simpl.
interval.
Qed.

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
idtac "Starting doppler3".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "error rewrites" error_rewrites_div_r.
all : (time "prune"
(prune_terms (cutoff 30);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end;
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end)).
+ 
time "goal 1" (
field_simplify_Rabs;
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with ( 
i_bisect v, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 2" (
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect vxH, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 3" (
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect vxH, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
+
time "goal 4" (
match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, 
i_bisect vxH, 
i_bisect v0, i_depth 20) as H'; apply H'; apply Rle_refl
end).
Defined.


Definition doppler3_bound_val := Eval simpl in doppler3_bound.
Compute ltac:(ShowBound doppler3_bound_val).

Lemma check_doppler3_bound :
proj1_sig doppler3_bound_val <= 1.75e-13.
Proof.
simpl.
interval.
Qed.


End WITHNANS.
Close Scope R_scope.