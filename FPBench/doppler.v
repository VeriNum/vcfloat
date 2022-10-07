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

Lemma Rabs_triang_l :
forall a b c, Rabs (a + b - c) <= Rabs a + Rabs (b - c). 
Proof. intros. eapply Rle_trans. 2: apply Rabs_triang. apply Req_le. f_equal; nra. Qed.

Lemma doppler1_bound:
	find_and_prove_roundoff_bound doppler1_bmap doppler1_expr.
Proof.
idtac "Starting doppler1".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.

match goal with |- Rabs (?u/?v * (1+?d') +?e' - - ?u1' * ?u2' * / ?v2') <= _ => 
let u1:= fresh "u" in set (u1:= u);
let v1:= fresh "v" in set (v1:= v);
replace (u1/v1 * (1 + d')) with ((u1 * (1 + d')) / v1); try nra;
let u2:= fresh "u" in set (u2:= (u1 * (1 + d')));
let u3:= fresh "u" in set (u3:=- u1' * u2');
let v3:= fresh "v" in set (v3:= v2');
replace (u3 * / v3) with (u3/v3); try nra;
replace (u2/v1 + e' - u3/v3) with (u2/v1 - u3/v3 + e'); try nra
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
eapply Rle_trans.
apply Rdiv_rel_error_add; 
repeat match goal with |- ?g <> 0 =>
try subst g; try interval
end.
eapply Rle_trans.
apply Rmult_le_compat;
try apply Rabs_pos.
apply Rmult_le_pos.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos; try apply Rabs_pos.
apply Rmult_le_pos; try apply Rabs_pos.
try apply Rabs_pos.
apply Rmult_le_compat;
try apply Rabs_pos.
try apply Rmult_le_pos.
try apply Rplus_le_le_0_compat.
apply Rmult_le_pos; try apply Rabs_pos.
apply Rmult_le_pos; try apply Rabs_pos.
apply Rplus_le_compat.
apply Rmult_le_compat;
try apply Rabs_pos.
subst u0 u1 u.
match goal with |- Rabs ?a <= _ =>
field_simplify a
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'
end.
apply H'.
subst u1.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'
end.
apply H'.
apply Rmult_le_compat;
try apply Rabs_pos.
subst v1 v2.
time "prune_terms" (prune_terms (cutoff 30)).
match goal with |- (Rabs ?e <= ?a - ?b)%R =>
    let G := fresh "G" in
    interval_intro (Rabs e) as G
end.
eapply Rle_trans.
apply G.
             apply Rminus_plus_le_minus;
             apply Rle_refl.
subst v2.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'
end.
apply H'.
subst v1 v2.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'
end.
apply H'.
             apply Rle_refl.
apply Rmult_le_compat.
try interval.
apply Rabs_pos.
apply Rle_refl.
subst u1 v2.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, i_depth 20) as H'
end.
apply H'.
apply E8.
Defined.

Definition doppler1_bound_val := Eval simpl in doppler1_bound.
Compute ltac:(ShowBound doppler1_bound_val).

(*
Lemma check :
proj1_sig doppler1_bound_val <= 1.21e-12.
set (y:= proj1_sig doppler1_bound_val).
simpl in y.
subst y.
interval.
Qed.
*)

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
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, 
i_depth 20) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Definition doppler2_bound_val := Eval simpl in doppler2_bound.
Compute ltac:(ShowBound' doppler2_bound_val).

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
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, 
i_bisect v, 
i_bisect v0, 
i_depth 20) as H
end.
time "apply bound" (
eapply Rle_trans;
try apply H;
try apply Rle_refl).
Defined.

Definition doppler3_bound_val := Eval simpl in doppler3_bound.
Compute ltac:(ShowBound' doppler3_bound_val).

End WITHNANS.
Close Scope R_scope.