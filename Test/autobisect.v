Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition turbine1_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine1 in exact e').

Derive a
SuchThat 
(forall (v0 e2 d7 : R)
 (H : 38 / 10 <= v0 <= 78 / 10)
 (H0 : Rabs d7 <= / 9007199254740992)
 (H1 : Rabs e2 <=
     /
     404804506614621236704990693437834614099113299528284236713802716054860679135990693783920767402874248990374155728633623822779617474771586953734026799881477019843034848553132722728933815484186432682479535356945490137124014966849385397236206711298319112681620113024717539104666829230461005064372655017292012526615415482186989568),
 Rabs (v0 ^ 2 / (v0 ^ 2 * d7 + v0 ^ 2 + e2)) <= a - 0)
As a_proof.
Proof.
intros.
subst a.
match goal with |- Rabs ?a <= _ =>
   let G := fresh "G" in 
   bisect_all_vars constr:(Rabs a) (@nil interval_tac_parameters); intro G;
   eapply Rle_trans;
   [apply G | apply Rminus_plus_le_minus; apply Rle_refl] 
end.
Qed.


Derive turbine1_b 
SuchThat (forall vmap, prove_roundoff_bound turbine1_bmap vmap turbine1_expr turbine1_b)
As turbine1_bound.
Proof.
idtac "Starting turbine1".
intro.
prove_roundoff_bound.
-
clear.
time  abstract (prove_rndval; interval).
-
time "prove_roundoff_bound2" prove_roundoff_bound2.
time "error_rewrites" error_rewrites.
all: time "prune_terms" prune_terms (cutoff 70); unfold Rsqr.
all: time "interval1" 
try match goal with |- (Rabs ?e <= ?a - ?b)%R =>
                      let G := fresh "G" in
                      interval_intro (Rabs e) as G ;
                      eapply Rle_trans;
                      [apply G | apply Rminus_plus_le_minus; apply Rle_refl] 
        end.
all: time "field_simplify" field_simplify_Rabs.
all: time "interval2" 
match goal with |- Rabs ?a <= _ =>
   let G := fresh "G" in 
   bisect_all_vars constr:(Rabs a) [i_depth 15]; intro G;
   eapply Rle_trans;
   [apply G | apply Rminus_plus_le_minus; apply Rle_refl] 
end.
Time Qed.


Lemma check_turbine1_bound: ltac:(CheckBound turbine1_b 7.9e-14%F64).
Proof. reflexivity. Qed.

End WITHNANS.
Close Scope R_scope.