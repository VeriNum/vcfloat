From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Set Bullet Behavior "Strict Subproofs". 


Section WITHNANS.
Context {NANS: Nans}. 

Definition sum {A: Type} (sum_op : A -> A -> A) (a b : A) : A := sum_op a b.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum sum_op a s).

Definition sum_rel_F := @sum_rel (ftype Tsingle) 0%F32 (BPLUS Tsingle).
Definition sum_rel_R := @sum_rel R 0%R Rplus.


Definition _a := 1%positive. (* current element *)
Definition _b := 2%positive. (* accumulator *)

Definition vmap_list ty (a b : ftype ty) := 
   [(_a, existT ftype _ a); (_b, existT ftype _ b)].

Definition vmap {ty} (a b : ftype ty) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap_list ty a b)) in exact z).


Definition bmap_list {ty} : list varinfo := 
  let ov := powerRZ 2 (femax ty) in 
  [ Build_varinfo Tsingle _a (-ov) ov;
    Build_varinfo Tsingle _b (-ov) ov ].

Definition bmap {ty} : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (@bmap_list ty ) ) in exact z).

Definition sum_expr {ty} (a b : ftype ty) := ltac :( let e' :=
  HO_reify_float_expr constr:([_a; _b]) (BPLUS ty) in exact e').


Require Import Interval.Tactic.

Lemma real_lt_1 :
forall a b c,
a <= b -> b < c -> a < c.
Proof. intros; apply Rle_lt_trans with b; auto. Qed.

Lemma bnd_lt_overflow n :
  (2 <= n )%nat ->
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let ov := powerRZ 2 (femax Tsingle) in 
  let bnd := (ov - (INR n - 1) * 2 * e * (1 + d) ^ (n - 2)) /
       ((INR n - 1) * d * (1 + d) ^ (n - 2) + 1)  in
bnd * (1 + d) + e < 0x1p128%xR.
Proof.
intros.
subst bnd.
rewrite <- Rcomplements.Rlt_minus_r.
replace (0x1p128%xR) with ov by (subst ov; simpl; nra).
match goal with |- context [?a / ?b * ?c] =>
replace (a/b  *c) with ((a  *c) / b)
end.
assert (Hn: 1 <= INR n - 1).
assert (Hn2: INR 2 <= INR n); try apply le_INR; auto.
eapply Rle_trans; [  | apply  Rplus_le_compat; [ apply Hn2| apply Rle_refl]]; try simpl; nra.
assert (Hd: 1 <= (1 + d) ^ (n - 2)).
assert (H1: 1 = (1 + d) ^ 0) by nra. 
eapply Rle_trans; [ rewrite H1  | apply Rle_refl]; apply Rle_pow; 
  subst d; simpl; try nra; try lia.
apply Rdiv_lt_left.
eapply Rlt_le_trans; [ idtac | apply  Rplus_le_compat; 
    [apply  Rmult_le_compat ; [| | apply Rmult_le_compat |]| apply Rle_refl]]; 
   try apply Hn; try apply Hd; try nra; try rewrite Rmult_1_l; try rewrite Rmult_0_l;
   try apply Rle_refl; try subst d; try simpl; nra.
set (A:= (INR n - 1) * (1 + d) ^ (n - 2)).
assert (HA: 1 <= A).
subst A.
eapply Rle_trans; [ idtac | apply  Rmult_le_compat];
   try apply Hn; try apply Hd; try nra.
replace ((INR n - 1) * d * (1 + d) ^ (n - 2)) with (A * d) by (subst A; nra).
replace ((INR n - 1) * 2 * e * (1 + d) ^ (n - 2)) with (A * 2 * e) by (subst A; nra).
replace ((ov - A * 2 * e) * (1 + d)) with (ov + (- 2 * A * e * d + ov * d - 2 * A * e )) by nra.
replace ((ov - e) * (A * d + 1)) with (ov + (- A * e * d + ov * A * d - e )) by nra.
apply Rplus_lt_compat_l.
apply Rplus_lt_compat.
apply Rplus_lt_le_compat.
assert (lem: forall a b c, 
  0 < c -> a < b -> a * c < b * c) by (intros;nra).
repeat apply lem; try subst d; try simpl; try nra;
  try subst e; try simpl; try nra;
  try subst A; try simpl;  
  try apply Hneg.
rewrite Rmult_assoc.
eapply Rle_trans; [ | apply Rmult_le_compat_l; [ subst ov; simpl; nra| 
  apply Rmult_le_compat_r; [ subst d; simpl; nra | apply HA ]]]; nra.
apply Ropp_lt_contravar.
rewrite Rmult_comm.
eapply Rle_lt_trans with (e * 1); try nra.
apply Rmult_lt_compat_l; try subst e; simpl; try nra.
nra.
Qed.


Lemma prove_rndoff' :
  forall (a b : ftype Tsingle) n,
  (2 <= n )%nat ->
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let ov := powerRZ 2 (femax Tsingle) in 
  let bnd := (ov - (INR n - 1) * 2 * e * (1 + d) ^ (n - 2)) /
       ((INR n - 1) * d * (1 + d) ^ (n - 2) + 1)  in
  - (bnd * (INR n - 1) / INR n) <= FT2R b <= bnd * (INR n - 1) / INR n -> 
  - (bnd * / INR n) <= FT2R a <= bnd * / INR n -> 
  prove_roundoff_bound (@bmap Tsingle) (vmap a b) (@sum_expr Tsingle a b) 
     (Rabs ( FT2R a + FT2R b) * d + e).
Proof.
intros ?  ?  ? ? ? ? ? ? ?bnd1 ?bnd2.
prove_roundoff_bound.
- 
prove_rndval.
clear BOUND BOUND0.
(* prove_rndval SHOULD SUBST V_A  & V_B ABOVE THE LINE *)
simpl in e; simpl in d.
assert (Rabs (1 + u0) <= 1 + d) as Hu2. 
{ subst e; eapply Rle_trans;
 [apply Rabs_triang | eapply Rplus_le_compat;
                                      [ rewrite Rabs_R1; apply Rle_refl | apply H1 ]]. }
apply Rlt_Rminus.
rewrite Rmult_1_l. 
try apply Rabs_le in bnd1, bnd2.
eapply real_lt_1; [eapply Rabs_triang | 
    rewrite Rabs_mult; eapply real_lt_1; [ eapply Rplus_le_compat; 
          [eapply Rmult_le_compat; try apply Rabs_pos; 
                      [eapply Rle_trans; [apply Rabs_triang | eapply Rplus_le_compat; 
                                      [apply bnd2| apply bnd1]] 
                          | eapply Rle_trans; [ apply Hu2 | apply Rle_refl] ] | apply H0 ] | ]].
replace (bnd * / INR n + bnd * (INR n - 1) / INR n) with bnd.
apply Rle_lt_trans with (bnd * (1+d) + e). 
  apply Rplus_le_compat; [apply Rle_refl| subst e; simpl; nra].
apply bnd_lt_overflow; auto.
field.
apply not_0_INR; try lia.
-
prove_roundoff_bound2.
clear BOUND BOUND0.
try apply Rabs_le in bnd1, bnd2.
match goal with |- context[Rabs ?a <= _] =>
field_simplify a
end.
assert (He0: Rabs e1 <= e).
{ eapply Rle_trans. apply E. subst e; simpl; nra. }
assert (Hd: Rabs d0 <= d).
{ eapply Rle_trans. apply E0. subst d; simpl; nra. }
replace (a * d0 + b * d0 + e1) with ((a + b) * d0 + e1) by nra.
eapply Rle_trans; [
apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat; [rewrite Rabs_mult; eapply Rle_trans;
  [apply Rmult_le_compat; 
      [ apply Rabs_pos | apply Rabs_pos |   apply Rle_refl | apply Hd ] | 
  apply Rle_refl ]  | apply He0 ] | ]  ].
nra.
Qed.

End WITHNANS.