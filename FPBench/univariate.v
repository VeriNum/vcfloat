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

Derive predatorprey_b 
SuchThat (forall vmap, prove_roundoff_bound predatorprey_bmap vmap predatorprey_expr predatorprey_b)
As predatorprey_bound.
Proof.
idtac "Starting predatorprey".
time "predatorprey" (
subst predatorprey_b; intro; prove_roundoff_bound;
try (prove_rndval; interval); try interval;
try ( prove_roundoff_bound2); try error_rewrites;
try (
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
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]) end));
try (
try rewrite Rsqr_pow2;
try field_simplify_Rabs;
try match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) upper with 
(i_bisect vxH, i_depth 17) as H'
end; apply H')).
Qed.

Lemma check_predatorprey_bound: ltac:(CheckBound predatorprey_b 3.1e-16%F64).
Proof. reflexivity. Qed.

Definition verhulst_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition verhulst_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list verhulst_bmap_list) in exact z).

Definition verhulst (x : ftype Tdouble) := 
  cast Tdouble (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  ((r * x)%F64 / ((1)%F64 + (x / k)%F64)%F64)%F64).

Definition verhulst_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) verhulst in exact e').

Derive verhulst_b 
SuchThat (forall vmap, prove_roundoff_bound verhulst_bmap vmap verhulst_expr verhulst_b)
As verhulst_bound.
Proof.
idtac "Starting verhulst".
time "verhulst" (
try (subst verhulst_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try prove_roundoff_bound2;
try match goal with |-Rabs ?a <= _ =>
field_simplify a ; try split; try unfold id; try field; try nra; try interval
end;
try match goal with |- Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_bisect vxH, i_depth 15) as H
end;
try (
eapply Rle_trans;
try apply H;
try apply Rle_refl)).
Qed.

Lemma check_verhulst_bound: ltac:(CheckBound verhulst_b 2.33e-16%F64).
Proof. reflexivity. Qed.

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

Derive carbongas_b 
SuchThat (forall vmap, prove_roundoff_bound carbongas_bmap vmap carbongas_expr carbongas_b)
As carbongas_bound.
Proof.
idtac "Starting carbongas".
time "carbongas" (
try (subst carbongas_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2; error_rewrites);
try (
(prune_terms (cutoff 60);
try match goal with |- (Rabs ?e <= ?a - 0)%R =>
  rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
end));
(try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      try (interval_intro (Rabs e) as G; 
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl]) end);
try (
try field_simplify_Rabs ;
try match goal with |-Rabs ?a <= _ =>
  try (interval_intro (Rabs a) upper with 
  (i_taylor vxH, i_bisect vxH, i_depth 15) as H' ; apply H');
  try (interval_intro (Rabs a) upper as H' ; apply H') end;
  apply Rle_refl)).
Qed.

Lemma check_carbongas_bound: ltac:(CheckBound carbongas_b 2.5e-08%F64).
Proof. reflexivity. Qed.

Definition t_div_t1_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition t_div_t1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list t_div_t1_bmap_list) in exact z).

Definition t_div_t1 (z : ftype Tdouble) := 
  cast Tdouble ((z / (z + (1)%F64)%F64)%F64).

Definition t_div_t1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) t_div_t1 in exact e').

Derive t_div_t1_b 
SuchThat (forall vmap, prove_roundoff_bound t_div_t1_bmap vmap t_div_t1_expr t_div_t1_b)
As t_div_t1_bound.
Proof.
idtac "Starting t_div_t1".
time "t_div_t1_bound" (
try (subst t_div_t1_b; intro; prove_roundoff_bound);
try (prove_rndval; interval);
try (prove_roundoff_bound2);
try match goal with |-Rabs ?a <= _ =>
field_simplify a; try split; try field; try nra; try interval
end;
try match goal with |-Rabs ?a <= _ =>
interval_intro (Rabs a) with (i_taylor vxH, i_degree 10, i_bisect vxH,
i_depth 10)
end;
try (
eapply Rle_trans;
try apply H;
try apply Rle_refl)).
Qed.

Lemma check_t_div_t1_bound: ltac:(CheckBound t_div_t1_b 4.4e-16%F64).
Proof. reflexivity. Qed.


End WITHNANS.
Close Scope R_scope.