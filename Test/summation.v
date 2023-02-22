From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

From vcfloat Require Import IEEE754_extra.
Import Coq.Lists.List ListNotations.

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Set Bullet Behavior "Strict Subproofs". 


Section WITHNANS.
Context {NANS: Nans}. 


Definition sum {A: Type} (sum_op : A -> A -> A) (a b : A) : A := sum_op a b.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum sum_op a s).

Definition sum_rel_F := @sum_rel (ftype Tsingle) (-0)%F32 (@BPLUS _ Tsingle).
Definition sum_rel_R := @sum_rel R 0%R Rplus.


Lemma sum_rel_R_abs :
forall l s1 s2,
sum_rel_R l s1 -> sum_rel_R (map Rabs l) s2 -> s1 <= s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold sum.
eapply Rplus_le_compat.
apply Rle_abs.
fold sum_rel_R in H4.
fold sum_rel_R in H3.
apply IHl;
auto.
Qed.

Lemma sum_rel_R_Rabs_eq :
forall l s,
sum_rel_R (map Rabs l) s -> Rabs s = s.
Proof.
induction  l.
-
intros.
inversion H.
rewrite Rabs_R0.
nra.
-
intros.
inversion H; subst; clear H.
unfold sum.
replace (Rabs(Rabs a + s0)) with 
  (Rabs a  + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s0).
apply Rabs_pos.
eapply Req_le.
apply IHl.
fold sum_rel_R in H3.
auto.
Qed.



Lemma sum_rel_R_Rabs :
forall l s1 s2,
sum_rel_R l s1 -> sum_rel_R (map Rabs l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
fold sum_rel_R in H4.
fold sum_rel_R in H3.
unfold sum.
eapply Rle_trans.
apply Rabs_triang.
replace (Rabs(Rabs a + s0)) with 
  (Rabs a  + s0).
eapply Rplus_le_compat; try nra.
eapply Rle_trans with (Rabs s0).
fold sum_rel_R in H4.
fold sum_rel_R in H3.
apply IHl; auto.
apply Req_le.
eapply sum_rel_R_Rabs_eq; apply H3.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s0).
apply Rabs_pos.
apply Req_le.
eapply sum_rel_R_Rabs_eq; apply H3.
Qed.

Lemma plus_zero a:
is_finite _ _ a = true -> 
(a + -0)%F32 = a.
Proof.
destruct a; simpl; auto;
intros; try discriminate; auto;
destruct s;
cbv; auto.
Qed.

Lemma sum_rel_F_single :
forall (a : ftype Tsingle) (fs : ftype Tsingle)
  (HFIN: is_finite _ _ a = true),
  sum_rel_F [a] fs -> fs = a.
Proof.
intros.
inversion H; auto.
inversion H3. subst.
unfold sum.
apply plus_zero; auto.
Qed.

Lemma sum_rel_R_single :
forall (a : R) (fs : R), sum_rel_R [a] fs -> fs = a.
Proof.
intros.
inversion H; auto.
inversion H3. subst.
unfold sum; nra.
Qed.


Definition _a := 1%positive. (* current element *)
Definition _b := 2%positive. (* accumulator *)

Definition vmap_list ty (a b : ftype ty) := 
   [(_a, existT ftype _ a); (_b, existT ftype _ b)].

Definition vmap {ty} (a b : ftype ty) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap_list ty a b)) in exact z).

Definition bmap_list : list varinfo := 
  [ trivbound_varinfo Tsingle _a;
    trivbound_varinfo Tsingle _b ].

Definition bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list bmap_list) in exact z).

Definition sum_expr {ty} (a b : ftype ty) := ltac :( let e' :=
  HO_reify_float_expr constr:([_a; _b]) (@BPLUS _ ty) in exact e').

Lemma real_lt_1 :
forall a b c,
a <= b -> b < c -> a < c.
Proof. intros; apply Rle_lt_trans with b; auto. Qed.


Lemma prove_rndoff' :
  forall (a b : ftype Tsingle) ,
  let e := / IZR (2 ^ 150) in 
  let d := / IZR (2 ^ 24) in 
      let ov := powerRZ 2 (femax Tsingle) in
  Rabs (FT2R a + FT2R b) <= (ov - 2 * e) / (1 + d) -> 
  prove_roundoff_bound bmap (vmap a b) (@sum_expr Tsingle a b) 
     (Rabs ( FT2R a + FT2R b) * d + e).
Proof.
intros ? ? ? ?  ? bnd.
prove_roundoff_bound.
- 
prove_rndval.
clear BOUND BOUND0.
assert (Rabs (1 + u0) <= 1 + d) as Hu2. 
{ subst e; eapply Rle_trans;
 [apply Rabs_triang | eapply Rplus_le_compat;
                                      [ rewrite Rabs_R1; apply Rle_refl | apply H0 ]]. }
assert (Rabs u <= e) as Hu1.
{ subst e; eapply Rle_trans;
 [ apply Rle_refl | apply H ] 
.
}
apply Rlt_Rminus.
rewrite Rmult_1_l.
eapply Rle_lt_trans.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
eapply Rplus_le_compat.
rewrite Rabs_mult.
eapply Rmult_le_compat; try apply Rabs_pos.
apply bnd.
apply Hu2.
apply Hu1.
eapply Rle_refl.
replace ((ov - 2 * e) / (1 + d) * (1 + d))
  with (ov - 2 * e).
replace ov with 0x1p128%xR.
apply Rminus_lt.
field_simplify.
subst e.
interval.
subst ov; simpl; nra.
field.
subst d.
interval.
-
prove_roundoff_bound2.
clear BOUND BOUND0.
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

Lemma reflect_reify_sumF : 
  forall a b,
  fval (env_ (vmap a b)) (@sum_expr Tsingle a b) = sum (@BPLUS _ Tsingle)  a b .
Proof. reflexivity. Qed.

Lemma reflect_reify_sumR : 
  forall a b,
  rval (env_ (vmap a b)) (@sum_expr Tsingle a b) = FT2R a + FT2R b .
Proof. reflexivity. Qed.

Lemma prove_rndoff:
  forall (a b : ftype Tsingle),
  boundsmap_denote bmap (vmap a b) ->
  let e  := / IZR (2 ^ 150) in 
  let d := / IZR (2 ^ 24) in
      let ov := powerRZ 2 (femax Tsingle) in
  Rabs (FT2R a + FT2R b) <= (ov - 2 * e) / (1 + d) -> 
      Rabs ( FT2R a + FT2R b - FT2R (BPLUS a b)) <=
     (Rabs ( FT2R a + FT2R b) * d + e).
Proof.
intros  ? ?   BMD  ? ? H1 H2.
pose proof prove_rndoff' a b H2.
pose proof reflect_reify_sumF a b as HF.
pose proof reflect_reify_sumR a b as HR.
unfold prove_roundoff_bound, roundoff_error_bound in H.
specialize (H BMD).
destruct H as ( _ & H).
rewrite HF in H.
rewrite HR in H.
fold d e in H.
unfold sum in H.
rewrite Rabs_minus_sym.
auto.
Qed.


Lemma rewrite_Rabs_triang a b (a' b': ftype Tsingle): 
Rabs((a + b) - FT2R (BPLUS a' b')) <= 
  Rabs((a + b) - (FT2R a' + FT2R b')) + 
  Rabs((FT2R a' + FT2R b') - FT2R (BPLUS a' b')).
Proof.
eapply Rle_trans; [ | apply Rabs_triang].
eapply Req_le.
f_equal.
nra.
Qed.


Lemma le_div a b c:
  0 < c -> a <= b -> a / c <= b / c .
Proof.
intros.
apply Generic_proof.Rdiv_le_mult_pos; try nra.
field_simplify; nra.
Qed.

Lemma le_div3 c1 c2:
   0 < c1 -> c2 <= c1 -> c2/c1 <= 1.
Proof.
intros.
apply Rdiv_le_left; try nra.
Qed.

Lemma le_div2 a b c1 c2:
  0 <= a -> 
  0 < c1 -> 0 < c2 -> c2 <= c1 -> a <= b -> a / c1 <= b / c2 .
Proof.
intros A. intros.
apply Generic_proof.Rdiv_le_mult_pos; try nra. 
apply le_div3 in H1; auto.
field_simplify; try nra.
Qed.

Lemma length_not_empty {A} l :
l <> [] -> 
(1 <= @length A l)%nat.
Proof.
intros.
destruct l; simpl; 
 try simpl (length (a :: l)); try lia.
destruct H; auto.
Qed.

Lemma length_not_empty' {A} l :
l <> [] -> 
1 <= INR (@length A l).
Proof.
intros.
replace 1 with (INR 1) by (simpl; auto).
eapply le_INR.
apply length_not_empty; auto.
Qed.

Lemma length_not_empty_nat {A} l :
l <> [] -> 
(1 <= (@length A l))%nat.
Proof.
intros.
apply INR_le.
apply length_not_empty';auto.
Qed.



Lemma length_not_empty_lt {A} l :
l <> [] -> 
0 < INR (@length A l).
Proof.
intros.
destruct l.
destruct H; auto.
simpl (length (a:: l)).
rewrite <- Nat.add_1_r.
rewrite plus_INR.
apply Rcomplements.Rlt_minus_l.
field_simplify.
simpl.
eapply Rlt_le_trans with 0;  try nra.
apply pos_INR.
Qed.

Lemma length_not_empty_nat' {A} l :
l <> [] -> 
(0 <= (@length A l))%nat.
Proof.
intros.
apply INR_le.
apply Rlt_le.
apply length_not_empty_lt;auto.
Qed.

Definition error_rel (n : nat) (r : R) : R :=
  let e  := / IZR (2 ^ 150) in
  let d := / IZR (2 ^ 24) in
  if (1 <=? Z.of_nat n) then 
    ((1 + d)^(n-1) - 1) * (Rabs r + e/d)
  else 0%R.

Ltac write_tsingle:=
set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle));
simpl in ea; subst ea;
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1));
simpl in ea; subst ea.


Lemma prove_rndoff_n :
  forall (l : list (ftype Tsingle)) fs rs rs_abs,
  sum_rel_F l fs -> sum_rel_R (map FT2R l) rs -> sum_rel_R (map Rabs (map FT2R l)) rs_abs ->
  let e  := / IZR (2 ^ 150) in
  let d  := / IZR (2 ^ 24) in 
  let ov := powerRZ 2 (femax Tsingle) in
  let n := length l in 
  let A := (1 + d)^(n-1) - 1 in
  (forall a0, In a0 l -> 
  is_finite (fprec Tsingle) 128 a0 = true /\
  Rabs (FT2R a0) <= (ov - 2 * e - A * e/d * (1 + d)) / ((1 + (A + 1) * INR n) * (1 + d))) -> 
  is_finite (fprec Tsingle) (femax Tsingle) fs = true /\
  Rabs (rs - FT2R fs) <= error_rel (length l)  rs_abs.
Proof.
induction l.
-
intros.
inversion H; subst; clear H;
inversion H0; subst; clear H0; simpl.
cbv [error_rel]; simpl.
rewrite Rminus_0_r.
rewrite Rabs_R0.
nra.
-
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
+
subst; simpl.
assert (HFIN: is_finite (fprec Tsingle) 128 a = true).
{
apply H2; simpl; auto.
}
rewrite (sum_rel_F_single a fs HFIN H).
rewrite (sum_rel_R_single (FT2R a) rs H0).
cbv [error_rel]; simpl;
split; auto.
field_simplify_Rabs.
rewrite Rabs_R0.
field_simplify; nra.
+
(* start common *)
assert (Hifn : 1 <=? Z.of_nat n = true).
{
apply Z.leb_le.
replace 1%Z with (Z.of_nat 1) by lia.
apply inj_le.
subst n.
simpl (length (a::l)).
rewrite <- Nat.add_1_r.
lia.
}
assert (Hif1 : 1 <=? Z.of_nat (length l + 1) = true).
{
apply Z.leb_le.
rewrite Nat2Z.inj_add.
simpl.
apply Z.le_sub_le_add_r.
ring_simplify.
replace 0%Z with (Z.of_nat 0)%Z by lia.
apply inj_le.
apply length_not_empty_nat'; auto.
}
assert (Hif2: 1 <=? Z.of_nat (length l) = true).
{
apply Z.leb_le.
replace 1%Z with (Z.of_nat 1) by lia.
apply inj_le.
apply length_not_empty_nat; auto.
}
assert (Hlenl: (1 <= length l)%nat).
{
apply length_not_empty_nat; auto.
}
assert (Hnlt: 0 < INR n).
{ subst n.
simpl (length (a::l)).
rewrite <- Nat.add_1_r.
rewrite plus_INR.
apply Rcomplements.INRp1_pos.
}
assert (Hd : 0 < d).
{
subst d; interval.
}
assert (Hd2: 0 < 1 + d).
{
subst d; interval.
}
assert (HA2: 0 < A).
{
subst A.
apply Rlt_Rminus.
subst n.
simpl (length(a::l)).
rewrite <- Nat.add_1_r.
eapply Rlt_le_trans with ((1+d)^1). 
  try subst d; try interval.
apply Rle_pow.
  try subst d; try interval.
rewrite Nat.add_sub; auto.
}
assert (HAgt: 0 < (1 + (A + 1) * INR n) * (1 + d)).
{ 
apply Rmult_lt_0_compat; auto.
apply Rplus_lt_0_compat; try nra.
}
set (A':=(1 + d) ^ (length l - 1) - 1).
assert (Aposp: 0 <= A').
{
subst A'.
apply Rle_0_minus.
subst n.
apply pow_R1_Rle.
subst d; interval.
}
assert (HAgtp: 0 < (1 + (A' + 1) * INR (length l)) * (1 + d)).
{ 
apply Rmult_lt_0_compat; auto.
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; auto.
apply Rplus_le_lt_0_compat; try nra.
apply length_not_empty_lt; auto.
}
assert (Hov: 0 <= ov - 2 * e - A * e / d * (1 + d)).
{
eapply Stdlib.Rdiv_pos_compat_rev with ((1 + (A + 1) * INR n)* (1+d)); auto.
eapply Rle_trans with (Rabs (FT2R a));
  try apply Rabs_pos.
apply H2.
simpl; auto.
}
assert (Hln: INR (length l) <= INR n).
{
subst n.
simpl (length(a::l)).
rewrite <- Nat.add_1_r.
apply le_INR.
lia.
}
assert (HAd: 0 <= (1 + d) ^ (length l - 1)).
{
apply pow_le; nra.
}
assert (Hle: (1 + d) ^ (length l - 1) <= (1 + d) ^ (n - 1)).
{
apply Rle_pow; try nra.
subst n.
simpl (length(a::l)).
rewrite <- Nat.add_1_r.
lia.
}
assert (Hle2: (1 + d) ^ (length l - 1) <= (1 + d) ^ (length l + 1 - 1)).
{
apply Rle_pow; try nra.
subst n.
simpl (length(a::l)).
rewrite <- Nat.add_1_r.
lia.
}
assert (Aeq: ((1 + d) ^ (length l + 1 - 1) - 1) = A).
{
subst A.
f_equal.
f_equal.
subst n.
simpl (length(a::l)).
rewrite <- Nat.add_1_r.
lia.
}
assert (HAd2: d <= A).
{ subst A. apply Rcomplements.Rle_minus_r.
subst n.
simpl (length(a::l)).
rewrite <- Nat.add_1_r.
eapply Rle_trans with ((1+d)^1).
nra.
apply Rle_pow; try nra.
lia.
}
assert (
Her:  forall s, error_rel (length l) s <= error_rel (length l + 1) s).
{
intros.
unfold error_rel.
rewrite Hif2.
rewrite Hif1.
write_tsingle.
fold e d.
apply Rmult_le_compat_r; auto.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
subst e d; interval.
apply Rplus_le_compat_r; auto.
} 

(* end common *)

inversion H1; subst; clear H1.
inversion H0; subst; clear H0.
inversion H; subst; clear H.
fold sum_rel_F in H5.
fold sum_rel_R in H6.
fold sum_rel_R in H7.

assert (IHLp:
forall a0 : ftype Tsingle,
In a0 l ->
is_finite (fprec Tsingle) 128 a0 = true /\
Rabs (FT2R a0) <=
(ov - 2 * e - ((1 + d) ^ (length l - 1) - 1) * e / d * (1 + d)) /
((1 + ((1 + d) ^ (length l - 1) - 1 + 1) * INR (length l)) * (1 + d))).
{
intros.
split.
-
apply H2.
simpl; auto.
-
eapply Rle_trans.
apply H2.
simpl; auto.
apply le_div2; auto.
+
apply Rmult_le_compat_r; try nra.
+
apply Rplus_le_compat_l.
apply Ropp_le_contravar. 
apply Rmult_le_compat_r; try nra.
apply Rmult_le_compat_r; try nra.
subst d; try interval.
subst A.
apply Rmult_le_compat_r; try nra.
subst e; interval.
}

assert (Hs1: Rabs (FT2R s1) <= error_rel (length l + 1 ) s + Rabs (s0)).
{
apply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
eapply Rle_trans.
rewrite Rabs_minus_sym; auto.
apply IHl.
apply H5.
apply H6.
apply H7.
write_tsingle.
fold e d ov.
auto.
apply Her.
}

set (b:= 
    (ov - 2 * e - A * e / d * (1 + d)) / ((1 + (A + 1) * INR n) * (1 + d)) *
    INR n).
assert (Rabs s <= b /\ Rabs s0 <= b).
{
assert (
forall  l s b, 
(forall a0, In a0 l -> Rabs a0 <= b) ->
sum_rel_R l s -> Rabs s <= 
  b * INR (length l)).
{
induction l0.
simpl.
intros.
inversion H0; subst; clear H0.
rewrite Rabs_R0; nra.
intros.
inversion H0; subst; clear H0.
fold sum_rel_R in H9.
eapply Rle_trans.
unfold sum in *.
eapply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat.
apply H.
simpl; auto.
unfold sum in *.
apply IHl0.
intros.
apply H.
simpl in H0; simpl; auto.
auto.
replace (INR (length (a0 :: l0))) with 
(1 + INR (length l0)).
nra.
simpl (length (a0::l0)).
rewrite S_INR.
nra.
}
assert (
forall a0 : R,
     In a0 (map FT2R l) ->
     Rabs a0 <= 
  (ov - 2 * e - A * e/d * (1 + d)) / ((1 + (A + 1) * INR n)* (1 + d))).
{
intros.
apply in_map_iff in H0.
destruct H0 as (A1 & B & C).
subst.
eapply Rle_trans.
apply H2. 
simpl; auto.
nra.
}

assert (
forall a0 : R,
     In a0 (map Rabs (map FT2R l)) ->
     Rabs a0 <= 
  (ov - 2 * e - A * e/d * (1 + d)) / ((1 + (A + 1) * INR n)* (1 + d))).
{
intros.
apply in_map_iff in H1.
destruct H1 as (A1 & B & C).
subst.
eapply Rle_trans.
rewrite Rabs_Rabsolu.
apply H0. 
simpl; auto.
nra.
}

split.
-
(* Rabs s <= b *)
eapply Rle_trans.
eapply (H (map Rabs (map FT2R l)) s).
intros.
apply H1; auto.
auto.
apply Rmult_le_compat; auto.
apply Stdlib.Rdiv_pos_compat; auto.
rewrite map_length. 
apply pos_INR.
apply Req_le; nra.
replace (length (map FT2R l)) with (length l); auto.
rewrite map_length; auto.
rewrite map_length; auto.
rewrite map_length; auto.
-
(* Rabs s0 <= b *)
eapply Rle_trans.
eapply (H (map FT2R l) s0).
intros.
apply H0; auto.
auto.
apply Rmult_le_compat; auto.
apply Stdlib.Rdiv_pos_compat; auto.
rewrite map_length. 
apply pos_INR.
apply Req_le; nra.
replace (length (map FT2R l)) with (length l); auto.
rewrite map_length; auto.
}

assert (HBMD: boundsmap_denote bmap (vmap a s1)).
{
assert (is_finite (fprec Tsingle) (femax Tsingle) s1 = true). {
  eapply IHl.
  apply H5.
  apply H6.
  apply H7.
  write_tsingle.
  fold e d ov.
  auto.
}
apply boundsmap_denote_i.
repeat constructor;
(eexists; split; [reflexivity | split; [reflexivity | split;  [  | ]]]); auto.
-
apply trivbound_correct.
-
apply H2.
simpl; auto.
-
apply trivbound_correct.
-
repeat constructor.
}

assert (Hs2: Rabs (FT2R s1) <= error_rel (length l ) s + Rabs s).
{ 
assert (Rabs (s0 - FT2R s1) <= error_rel (length l ) s).
apply IHl; auto.
rewrite Rabs_minus_sym in H0.
eapply Rle_trans with (error_rel (length l) s + Rabs s0).
apply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv; auto.
auto.
apply Rplus_le_compat_l.
eapply sum_rel_R_Rabs.
apply H6.
apply H7.
}

assert (Hrndp:
Rabs (FT2R a + FT2R s1) <=
(ov - 2 * e) / (1 + d)).
{
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat.
apply H2.
simpl; auto.
eapply Rle_trans.
apply Hs1.
apply Rplus_le_compat.
cbv [error_rel].
rewrite Hif1.
write_tsingle.
fold e d ov A n.
rewrite Aeq.
assert (A * (Rabs s + e / d) <= 
  A * ( b + e / d)).
apply Rmult_le_compat_l; try nra.
apply H0.
apply H.

subst b.
set (h:=(ov - 2 * e - A * e / d * (1 + d)) / ((1 + (A + 1) * INR n) * (1 + d))).
rewrite <- Rplus_assoc.
replace (
h + A * (h * INR n + e / d) + h * INR n)
with
(h * (1  + (A + 1)* INR n) + A * e/d) by nra.
apply Generic_proof.Rdiv_le_mult_pos; try nra.
rewrite Rmult_plus_distr_r.
assert (h * (1 + (A + 1) * INR n) * (1 + d) =
(ov - 2 * e - A * e / d * (1 + d))).
subst h.
field.
repeat split; try nra.
rewrite H0.
apply Req_le.
field; nra.
}


match goal with |- (?A /\ ?B) =>
assert (HFIN : A)
end.
{
destruct (prove_rndoff' a s1 ); auto. 

}
split; auto.

eapply Rle_trans.
apply rewrite_Rabs_triang.
repeat match goal with |- context[Rabs ?a] =>
field_simplify a
end.


eapply Rle_trans.
apply Rplus_le_compat.
{
apply IHl; auto.
apply H7.
}
{
eapply prove_rndoff; auto.
}



write_tsingle.
fold e d.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; try nra.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat_l.
apply Hs2.


cbv [error_rel].
unfold sum.
fold n;
rewrite Hif2.
rewrite Hifn.
write_tsingle.
fold e d ov A A'.

replace (
A' * (Rabs s + e / d) +
((Rabs (FT2R a) + (A' * (Rabs s + e / d) + Rabs s)) * d + e))
with
(A' * (1 + d) * (Rabs s + e / d) + Rabs (FT2R a) * d + Rabs s * d + e) by nra.

assert (A' * (1 + d) = A - d).
{
subst A' A.
rewrite Rmult_minus_distr_r.
assert ((1 + d) ^ (length l - 1) * (1 + d) = (1 + d) ^ (n - 1)).
replace ((1 + d) ^ (length l - 1) * (1 + d)) with
  ((1 + d) ^ (length l - 1 + 1)).
f_equal.
subst n.
simpl (length (a::l)).
rewrite Nat.add_1_r; lia.
rewrite pow_add; nra.
rewrite H0.
nra.
}

rewrite H0; clear H0.
replace ((A - d) * (Rabs s + e / d)) with
(A *(Rabs s + e / d) - d * (Rabs s + e / d)) by nra.
assert (Hs: Rabs s = s). 
{ eapply sum_rel_R_Rabs_eq.
apply H7.
}
ring_simplify.
replace (
A * Rabs s + A * (e / d) - e / d * d + d * Rabs (FT2R a) + e)
with
(A * Rabs s + A * (e / d) + d * Rabs (FT2R a)).
replace (Rabs (Rabs (FT2R a) + s)) with (Rabs (FT2R a) + s).


eapply Rle_trans.
apply Rplus_le_compat_l.
assert (d * Rabs (FT2R a) <= A * Rabs (FT2R a)).
apply Rmult_le_compat_r; auto.
apply Rabs_pos.
apply H0.


rewrite Hs.
apply Req_le.
field_simplify; try nra.
symmetry.
rewrite Rabs_pos_eq; auto.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s).
apply Rabs_pos.
apply Req_le; auto.
rewrite Hs.
field_simplify; nra.
Qed.



End WITHNANS.