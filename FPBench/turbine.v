From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition turbine1_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine1 in exact e').
From Gappa Require Import Gappa_tactic.
From Coquelicot Require Import Coquelicot. 

Lemma Rplus_opp : forall a b,
a + - b = a - b. Proof. intros. nra. Qed.

Ltac rewrite_Rops :=
  try  rewrite Rplus_opp.

Ltac mult_le_compat_tac :=
try apply Rmult_le_compat; try apply Rabs_pos;
try apply Rmult_le_pos; try apply Rabs_pos;
try apply Rplus_le_le_0_compat; try apply Rabs_pos;
try apply  Rmult_le_pos; try apply Rabs_pos;
try apply  Rmult_le_pos; try apply Rabs_pos;
try apply  Rmult_le_compat; try apply Rabs_pos;

try apply  Rplus_le_le_0_compat; try apply Rabs_pos;
try apply  Rmult_le_pos; try apply Rabs_pos;
try apply  Rmult_le_pos; try apply Rabs_pos;

try apply Rplus_le_compat;
try apply Rmult_le_compat; try apply Rabs_pos.

Ltac error_rewrites :=
try rewrite Rplus_opp;
repeat match goal with 
 | |- Rabs((?u1 - ?v1) * ?D + ?E - ?U) <= _ => 
    (replace ((u1 - v1) * D + E - U) with 
      ((u1 * D - v1 * D) - U + E)  by nra) ; 
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [rewrite Rminus_rel_error; eapply Rle_trans; [apply Rabs_triang| apply Rplus_le_compat];
          [try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc| try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)]
          | try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)]
 | |- Rabs((?u1 + ?v1) * ?D + ?E - ?U) <= _ => 
    (replace ((u1 + v1) * D + E - U) with 
      ((u1 * D + v1 * D) - U + E)  by nra) ; 
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [rewrite Rplus_rel_error ; eapply Rle_trans ;[apply Rabs_triang| idtac] ; apply Rplus_le_compat;
          [try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc| try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)]
          | try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)]
 | |- Rabs((?u1 * ?v1) * ?D + ?E - ?U) <= _ => 
    (replace ((u1 * v1) * D + E - U ) with 
      ((u1 * D * v1) - U + E)  by nra);
        eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat; 
        [rewrite Rmult_rel_error; eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat ;
              [eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat; 
                  [rewrite Rabs_mult; apply Rmult_le_compat; mult_le_compat_tac| 
                    rewrite Rabs_mult; apply Rmult_le_compat; mult_le_compat_tac]] 
              | rewrite Rabs_mult; apply Rmult_le_compat; mult_le_compat_tac]  ] 
        | idtac ] ]
 | |- Rabs((?u1 / ?v1) * ?D + ?E - (?u2 /?v2)) <= _ => 
    (replace ((u1 / v1) * D + E - (u2 /v2) ) with 
      ((u1 * D)/v1 -  (u2 /v2) + E)  by nra);
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [eapply Rle_trans; 
          [apply Rdiv_rel_error_add_reduced_l; interval (* will sometimes fail *)
          | apply Rmult_le_compat; mult_le_compat_tac; try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc) ]
        | try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)] 
 | |- Rabs((?u1 / ?v1)  + ?E - ?U) <= _ => 
    (replace ((u1 / v1)  + E - U ) with 
      (u1/v1 - U + E)  by nra);
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [eapply Rle_trans; 
          [apply Rdiv_rel_error_add_reduced_l; interval (* will sometimes fail *)
          | apply Rmult_le_compat; mult_le_compat_tac; try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc) ]
        | try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)] 
 | |- Rabs((?u1 / ?v1)  * ?D - ?U) <= _ => 
    (replace ((u1 / v1) * D - U ) with 
      ((u1 * D)/v1 - U )  by nra);
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [eapply Rle_trans; 
          [apply Rdiv_rel_error_add_reduced_l; interval (* will sometimes fail *)
          | apply Rmult_le_compat; mult_le_compat_tac; try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc) ]
        | try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)] 
 | |- Rabs(- _) <= _ => rewrite Rabs_Ropp 
 | |- Rabs(?a/?b) <= _ => replace (Rabs (a/b)) with (Rabs a * Rabs (1/b)) by
        (rewrite <- Rabs_mult; f_equal; nra) ; eapply Rle_trans; 
  [ try (rewrite Rmult_plus_distr_r; rewrite Rmult_assoc)| idtac]
end.

Ltac interval_intro_mult:=
let H1 := fresh "H" in
let H2 := fresh "H" in
match goal with |-Rabs ?a * Rabs ?b <= _ =>
try apply Rmult_le_compat;
try apply Rabs_pos;
try interval_intro (Rabs a)  as H1;
try interval_intro (Rabs b)  as H2
end; try apply H1; try apply H2.



Lemma turbine1_bound:
	find_and_prove_roundoff_bound turbine1_bmap turbine1_expr.
Proof.
idtac "Starting turbine1".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2. 
time "error rewrites" error_rewrites.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
rewrite <- Rabs_mult.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor v0, i_degree 10) as H'
end; apply H'.
apply Rle_refl.
rewrite <- Rabs_mult.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor v0, i_degree 10) as H'
end; apply H'.
time "extra" (
try split; try interval; try 
match goal with |-?z <> 0 =>
field_simplify z
end; try interval).
apply Rle_refl.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_taylor vxH, i_degree 20)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 15) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_taylor vxH, i_degree 20)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
rewrite <- Rabs_mult.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_taylor vxH, i_degree 20)  as H'
end; apply H'.
time "extra" (
try split; try interval; try 
match goal with |-?z <> 0 =>
field_simplify z
end; try interval).
apply Rle_refl.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) as H'
end; apply H'.
Defined.


Definition turbine1_bound_val := Eval simpl in turbine1_bound.
Compute ltac:(ShowBound turbine1_bound_val).

Goal proj1_sig turbine1_bound_val <= 5e-12.
simpl.
interval.
Qed.


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
idtac "Starting turbine2".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2. 
time "error rewrites" error_rewrites.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor vxH, i_degree 10) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor vxH, i_degree 10) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
rewrite <- Rabs_mult.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_bisect vxH, i_depth 20) as H'
end; apply H'.
apply Rle_refl.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
rewrite <- Rabs_mult.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor vxH, i_degree 10) as H'
end; apply H'.
time "extra" (
try split; try interval; try 
match goal with |-?z <> 0 =>
field_simplify z
end; try interval).
apply Rle_refl.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
Defined.

Definition turbine2_bound_val := Eval simpl in turbine2_bound.
Compute ltac:(ShowBound turbine2_bound_val).

Goal proj1_sig turbine2_bound_val <= 3e-11.
simpl; interval.
Qed.

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
idtac "Starting turbine3".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "error rewrites" error_rewrites.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
rewrite <- Rabs_mult.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor v0, i_degree 10) as H'
end; apply H'.
apply Rle_refl.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.

rewrite Rmult_assoc.
match goal with |-context[(?A1 * ?A2 + ?G)/?B * ?D + ?E - (?X1 * ?X2)/?B' ] =>
replace ((A1 * A2 + G)/B * D + E - (X1 * X2)/B') with ( ((A1/B) * A2) * D + (E + (G*D)/B) - ((X1/B') * X2) ) by nra
end.
repeat match goal with |-context[(?A1 * ?A2 + ?E )/?B ] =>
replace ((A1 * A2 + E)/B ) with ( ((A1/B) * A2 + E/B) ) by nra
end.
time "error rewrites" error_rewrites.



time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor vxH, i_degree 20) as H'
end; apply H'.
time "extra" (
try split; try interval; try 
match goal with |-?z <> 0 =>
field_simplify z
end; try interval).
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_bisect vxH, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_bisect vxH, i_depth 20) as H'
end; apply H'.
time "interval_intro" interval_intro_mult.
apply Rle_refl.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor vxH, i_degree 20) as H'
end; apply H'.
time "extra" (
try split; try interval; try 
match goal with |-?z <> 0 =>
field_simplify z
end; try interval).
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect v0, i_bisect v, i_bisect vxH, i_depth 20) as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  with (i_taylor vxH, i_degree 20) as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "field_simplify" match goal with |- context[Rabs ?a]  =>
field_simplify a; try interval
end;
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
time "interval_intro" match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a)  as H'
end; apply H'.
Defined.

Definition turbine3_bound_val := Eval simpl in turbine3_bound.
Compute ltac:(ShowBound turbine3_bound_val).

Goal proj1_sig turbine3_bound_val <= 2.7e-10.
simpl.
interval.
Qed.

End WITHNANS.
Close Scope R_scope.