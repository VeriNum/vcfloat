Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition _v : ident := 1%positive.
Definition _w : ident := 2%positive.
Definition _r : ident := 3%positive.

Definition turbine1_bmap_list := [Build_varinfo Tdouble _v (-45e-1) (-3e-1);Build_varinfo Tdouble _w (4e-1) (9e-1);Build_varinfo Tdouble _r (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([_v;_w;_r]) turbine1 in exact e').

Derive turbine1_b 
SuchThat (forall vmap, prove_roundoff_bound turbine1_bmap vmap turbine1_expr turbine1_b)
As turbine1_bound.
Proof.
idtac "Starting turbine1".
time "turbine1" (
  subst turbine1_b; intro; prove_roundoff_bound;
 [ prove_rndval; interval 
 | prove_roundoff_bound2; error_rewrites; 
   try (prune_terms (cutoff 18);
   try match goal with |- (Rabs ?e <= ?a - 0)%R =>
     rewrite Rminus_0_r (* case prune terms will fail to produce reasonable bound on goal*)
   end;
   try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] end);
   try rewrite Rsqr_pow2;
   field_simplify_Rabs;
   [ interval_intro (Rabs (1 / v_r ^ 2)) with (i_bisect v_r, i_depth 13) as H'; apply H' 
   | interval_intro (Rabs (Tree.bpow' 2 1)) as H'; apply H'
   | interval_intro (Rabs (v_r ^ 2 / (v_r ^ 2 * e12 + v_r ^ 2 + e6))) with (i_bisect v_r, i_depth 13) as H'; apply H' 
   | interval_intro (Rabs (1 / v_r ^ 2)) with (i_bisect v_r, i_depth 13) as H'; apply H' 
   | interval_intro (Rabs (v_r ^ 2 * v_w ^ 2)) as H'; apply H'
   | interval_intro (Rabs (1 / (- v_v + 1))) with (i_bisect v_v, i_depth 13) as H'; apply H'
   | interval_intro (Rabs ((- v_v + 1) / (- v_v * e7 - v_v + e7 + e20 + 1))) with (i_bisect v_v, i_depth 13)  as H'; apply H'
   | interval_intro (Rabs (1 / (- v_v + 1))) with (i_bisect v_v, i_depth 13) as H'; apply H'
   ]]).
Time Qed.

Lemma check_turbine1_bound: ltac:(CheckBound turbine1_b 7.9e-14%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.