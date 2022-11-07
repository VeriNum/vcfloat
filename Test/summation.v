From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Binary.

Import List ListNotations.

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
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

Definition sum_rel_F := @sum_rel (ftype Tsingle) 0%F32 (BPLUS Tsingle).
Definition sum_rel_R := @sum_rel R 0%R Rplus.

Lemma plus_zero a:
(a + 0)%F32 = a.
Proof.
Admitted.

Lemma sum_rel_F_single :
forall (a : ftype Tsingle) (fs : ftype Tsingle), sum_rel_F [a] fs -> fs = a.
Proof.
intros.
inversion H; auto.
inversion H3. subst.
unfold sum.
apply plus_zero.
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


Definition bmap_list {ty} : list varinfo := 
  let ov := powerRZ 2 (femax ty) in 
  [ Build_varinfo Tsingle _a (-ov) ov;
    Build_varinfo Tsingle _b (-ov) ov ].

Definition bmap {ty} : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (@bmap_list ty ) ) in exact z).

Definition sum_expr {ty} (a b : ftype ty) := ltac :( let e' :=
  HO_reify_float_expr constr:([_a; _b]) (BPLUS ty) in exact e').


Lemma real_lt_1 :
forall a b c,
a <= b -> b < c -> a < c.
Proof. intros; apply Rle_lt_trans with b; auto. Qed.

Lemma bnd_lt_overflow n :
  (2 <= n )%nat ->
  let e  := / 2 * Raux.bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle) in
  let d  := / 2 * Raux.bpow Zaux.radix2 (- fprec Tsingle + 1) in
  let sov := (powerRZ 2 (femax Tsingle) - 2 * e) / (1 + d) in
  let A  := (INR n - 1) * (1 + d)^(n-2) in
  let bnd := (sov - A * e) * (1 / ((A * d + 1) * INR n + 1)) * (INR n + 1) in 
    (bnd / (INR n + 1) * ((A * d + 1) * INR n + 1) + A * e) * (1 + d) + e < 0x1p128%xR.
Proof.
intros. 
assert (lem: forall a b c, 
  0 < c -> a < b -> a * c < b * c) by (intros;nra).
subst bnd.
rewrite <- Rcomplements.Rlt_minus_r.
set (ov:= powerRZ 2 (femax Tsingle)).
subst sov. fold ov.
replace (0x1p128%xR) with ov by (subst ov; simpl; nra).

assert (
((INR n - 1) * (1 + / 2 * / IZR (Z.pow_pos 2 23)) ^ (n - 2) *
 (/ 2 * / IZR (Z.pow_pos 2 23)) + 1) * INR n + 1 <> 0).
{
apply tech_Rplus; try nra.
apply Rmult_le_pos; try interval.
apply Rplus_le_le_0_compat; try nra.
apply Rmult_le_pos; try interval.
apply Rmult_le_pos; try interval.
apply Rle_0_minus.
apply le_INR in H; interval.
apply pow_le;
try nra.
apply pos_INR.
}

match goal with |- context [?a / ?b * ?c] =>
replace (a/b  *c) with ((a  *c) / b)
end.
assert (Hn2: INR 2 <= INR n); try apply le_INR; auto.

assert (Hd: 1 <= (1 + d) ^ (n - 2)).
assert (H1: 1 = (1 + d) ^ 0) by nra. 
eapply Rle_trans; [ rewrite H1  | apply Rle_refl]; apply Rle_pow; 
  subst d; simpl; try nra; try lia.
apply Rcomplements.Rlt_div_r.
 try subst d; try nra.
  simpl; nra.

rewrite <- Rcomplements.Rlt_minus_r.

apply Rcomplements.Rlt_div_r.
apply Rlt_gt.
replace (/ (INR n + 1)) with (1/ (INR n + 1)) by nra.
apply Rdiv_lt_0_compat; try interval.
field_simplify.
apply Rdiv_lt_right.
subst d; try interval.

match goal with |- context[ ?a / ?g * ?g ] =>
replace (a / g  * g) with a
end.

rewrite Rplus_comm.
apply Rplus_lt_compat.
apply Rplus_le_lt_compat; try nra.

apply Ropp_lt_contravar. 
replace (e * INR n) with (1 * e * INR n) by nra; 
  apply lem; try lia; try interval.

apply Ropp_lt_contravar. 
try subst e; simpl; interval.


field_simplify;
try field; try subst d; simpl; try nra.

split; try field; try subst d; simpl; try nra.
try interval.

split; try field; try subst A; try subst d; simpl; try nra.

field.
split; try field; try subst A; try subst d; simpl; try nra; auto.
split; try field; try subst A; try subst d; simpl; try nra; auto.
apply tech_Rplus; try nra.
apply pos_INR.
Qed.

Lemma prove_rndoff' :
  forall (a b : ftype Tsingle) ,
  let e  := powerRZ 2 (3 - femax Tsingle - fprec Tsingle - 1) in
  let d := powerRZ 2 (- fprec Tsingle) in
      let ov := powerRZ 2 (femax Tsingle) in
  Rabs (FT2R a + FT2R b) <= (ov - 2 * e) / (1 + d) -> 
  prove_roundoff_bound (@bmap Tsingle) (vmap a b) (@sum_expr Tsingle a b) 
     (Rabs ( FT2R a + FT2R b) * d + e).
Proof.
intros ? ? ? ?  ? bnd.
prove_roundoff_bound.
- 
prove_rndval.
clear BOUND BOUND0.
simpl in e; simpl in d.
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
apply tech_Rplus; try nra.
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


Definition error_rel (n : nat) (r : R) : R :=
  let e  :=powerRZ 2 (3 - femax Tsingle - fprec Tsingle - 1)  in
  let d := powerRZ 2 (- fprec Tsingle)  in
  if (2 <=? Z.of_nat n) then 
    ((INR n-1) * (Rabs r * d + e) * (1 + d)^( n -2))
  else 0%R.

Lemma reflect_reify_sumF : 
  forall a b,
  fval (env_ (vmap a b)) (@sum_expr Tsingle a b) = sum (BPLUS Tsingle)  a b .
Proof. reflexivity. Qed.

Lemma reflect_reify_sumR : 
  forall a b,
  rval (env_ (vmap a b)) (@sum_expr Tsingle a b) = FT2R a + FT2R b .
Proof. reflexivity. Qed.

Lemma prove_rndoff:
  forall (a b : ftype Tsingle),
  boundsmap_denote (@bmap Tsingle) (vmap a b) ->
  let e  :=powerRZ 2 (3 - femax Tsingle - fprec Tsingle - 1)  in
  let d := powerRZ 2 (- fprec Tsingle)  in
      let ov := powerRZ 2 (femax Tsingle) in
  Rabs (FT2R a + FT2R b) <= (ov - 2 * e) / (1 + d) -> 
      Rabs ( FT2R a + FT2R b - FT2R (BPLUS Tsingle a b)) <=
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


Lemma rewrite_Rabs_triang a b a' b': 
Rabs((a + b) - FT2R ((BPLUS Tsingle) a' b')) <= 
  Rabs((a + b) - (FT2R a' + FT2R b')) + 
  Rabs((FT2R a' + FT2R b') - FT2R ((BPLUS Tsingle) a' b')).
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


Lemma prove_rndoff_n :
  forall (l : list (ftype Tsingle)) fs rs ,
  sum_rel_F l fs -> sum_rel_R (map FT2R l) rs ->
  let e  :=powerRZ 2 (3 - femax Tsingle - fprec Tsingle - 1)  in
  let d := powerRZ 2 (- fprec Tsingle)  in
  let ov := powerRZ 2 (femax Tsingle) in
  let n := length l in 
  let A := (INR n - 1)*(1+d)^(n-2) in
  (forall a0, In a0 l -> 
  Rabs (FT2R a0) <= (ov - 2 * e - A * e * (1 + d)) / (1 + (A * d + 1) * INR n) / (1 + d)) -> 
  Rabs (rs - FT2R fs) <= error_rel (length l + 1) rs.
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
rewrite (sum_rel_F_single a fs H).
rewrite (sum_rel_R_single (FT2R a) rs H0).
cbv [error_rel]; simpl.
simpl in e, d.
fold e d.
rewrite Rmult_1_r.
*
field_simplify_Rabs.
rewrite Rabs_R0.
field_simplify.
apply Rplus_le_le_0_compat;
try subst d e; try nra.
try subst d e; try nra.
apply Rmult_le_pos;
try subst d e; try nra.
apply Rabs_pos.
+
(* basic facts for common subgoals *)
assert (Hn0 : (2 <= n)%nat).
{
subst n.
simpl (length (a :: l)).
replace (S (length l)) with (length l +1)%nat.
repeat rewrite  <- Nat.add_1_r.
apply add_le_mono_r_proj_l2r.
apply length_not_empty_nat; auto.
lia.
}
assert (Hn : 0 <= INR n) by (apply pos_INR).
assert (Hnp: 0 < INR n - 1).
{ 
apply Rlt_Rminus.
subst n.
simpl (length (a::l)).
rewrite <- Nat.add_1_r.
rewrite plus_INR.
simpl.
apply Rcomplements.Rlt_minus_l.
field_simplify.
apply length_not_empty_lt; auto.
}
assert (Hlen: 0 <= INR (length l)). 
{
eapply Rle_trans; [| apply length_not_empty']; try nra; auto.
}
assert (HA1 : 0 <= (1 + d) ^ (length l - 2)).
{
apply pow_le.
subst d; interval.
}
assert (HA2: 0 < A).
{
subst A.
apply Rmult_lt_0_compat; auto.
apply pow_lt.
subst d; interval.
}
assert (Hov: 0 <= ov - 2 * e - A * e * (1 + d)).
{
  assert (forall a b, 
  0 < b -> 0 <= a / b -> 0 <= a).
{
intros.
eapply Stdlib.Rdiv_pos_compat_rev; auto.
apply H4. auto.
}
  assert (0 <= Rabs(FT2R a)) by (apply Rabs_pos; auto).
  assert ((ov - 2 * e - A * e * (1 + d)) / (1 + (A * d + 1) * INR n) / (1 + d) =
  (ov - 2 * e - A * e * (1 + d)) / ((1 + (A * d + 1) * INR n) * (1 + d))).
  field_simplify.
  field.
  apply tech_Rplus; try nra. 
  repeat apply Rplus_le_le_0_compat; 
    try nra; try apply pos_INR; try subst d; try interval;
    repeat try  apply Rmult_le_pos; try interval; auto;
   try nra;
    try apply pow_le; simpl; try interval.
repeat split.
subst d;  try apply tech_Rplus; try nra.
  simpl; try nra.
try apply tech_Rplus; try nra.
apply Rmult_lt_0_compat; try nra.
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; try nra.
subst d; interval.
repeat split.
try apply tech_Rplus; try nra.
apply Rmult_lt_0_compat; try nra.
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; try nra.
subst d; interval.
try apply tech_Rplus; try nra.
subst d; interval.
eapply H3 with (((1 + (A * d + 1) * INR n) * (1 + d)))
  ; [ | eapply Rle_trans; [apply H4|]].
apply Rmult_lt_0_compat; try nra.
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; try nra.
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; try nra.
subst d; interval.
apply Rplus_lt_0_compat; try nra.
subst d; interval.
rewrite H5 in H1.
apply H1.
simpl; auto.
}
set (A':=
   (INR (length l) - 1) * (1 + d) ^ (length l - 2)).
assert (HAp: 0 <= A').
{
subst A'.
apply Rmult_le_pos.
subst n;
simpl (length (a :: l));
try lia.
apply Rle_0_minus.
apply length_not_empty'; auto.
apply pow_le.
subst d; interval.
}
assert (HAA': A' <= A).
{
subst A A'.
apply Rmult_le_compat; auto.
apply Rle_0_minus;
apply length_not_empty'; auto.
subst n.
simpl (length (a :: l)).
apply Rplus_le_compat; try nra.
apply le_INR; lia.
apply Rle_pow.
subst d; interval.
subst n;
simpl (length (a :: l));
lia.
}
assert (Hd: 0 < d).
{ subst d; interval.
}
assert (HAlt: 0 < 1 + (A * d + 1) * INR n).
{
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; try nra.
}
assert (HA'lt: 0 < 1 + (A' * d + 1) * INR (length l)).
{
apply Rplus_lt_0_compat; try nra.
apply Rmult_lt_0_compat; try nra.
apply length_not_empty_lt; auto.
}
assert (Hnpp: INR (length l) <= INR n).
{
subst n;
simpl (length (a :: l)).
rewrite <- Nat.add_1_r;
apply le_INR;
lia.
}
assert (Hif1: 2 <=? Z.of_nat (length l + 1) = true). 
{
apply Z.leb_le.
rewrite Nat2Z.inj_add.
simpl.
apply Z.le_sub_le_add_r.
ring_simplify.
replace 1%Z with (Z.of_nat 1) by lia.
apply inj_le.
apply length_not_empty_nat; auto.
}
assert (Hif2: 2 <=? Z.of_nat (length (a :: l) + 1) = true).
{
apply Z.leb_le.
rewrite Nat2Z.inj_add.
simpl (length (a :: l)).
apply Z.le_sub_le_add_r.
ring_simplify.
rewrite <- Nat.add_1_r.
replace 1%Z with (Z.of_nat 1)%Z by lia.
apply inj_le.
apply Nat.le_sub_le_add_r.
replace (1 - 1)%nat with 0%nat by lia.
apply length_not_empty_nat'; auto.
}

(* end common *)

inversion H0; subst; clear H0.
inversion H; subst; clear H.
fold sum_rel_F in H5.
fold sum_rel_R in H6.
eapply Rle_trans.
apply rewrite_Rabs_triang.
repeat match goal with |- context[Rabs ?a] =>
field_simplify a
end.

eapply Rle_trans.
apply Rplus_le_compat.
apply IHl; auto.
{
set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)).
simpl in ea. subst ea.
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1)).
simpl in ea. subst ea.
(*simpl in e, d.*)
fold e d ov  A'.
intros.
eapply Rle_trans.
apply H1.
simpl; auto.
{ 
apply le_div.
try subst d; interval.
apply le_div2; auto.
+
apply Rplus_le_compat_l.
apply Rmult_le_compat; auto.
apply Rplus_le_le_0_compat; try nra.
nra.
+
fold d in A'. 
fold A'.
apply Rplus_le_compat_l.
apply Ropp_le_contravar. 
apply Rmult_le_compat; try nra.
apply Rmult_le_pos; auto; try subst e; try nra.
apply powerRZ_le. lra.
apply Rmult_le_compat; auto;
try subst e; try nra.
apply powerRZ_le. lra.
}
}

eapply prove_rndoff.
{
assert (is_finite (fprec Tsingle) (femax Tsingle) s0 = true) by admit.
assert (is_finite (fprec Tsingle) (femax Tsingle) a = true) by admit.
apply boundsmap_denote_i;  [ | repeat split]. 
repeat split;
 (eexists; split; [ reflexivity | ]; split; [reflexivity | ]; split; [ assumption | ]).
admit.
admit.
}
set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)).
simpl in ea. subst ea.
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1)).
simpl in ea. subst ea.
fold e d ov.
eapply Rle_trans.
apply Rabs_triang.
eapply Rle_trans.
apply Rplus_le_compat.
apply H1.
simpl; auto.

assert (
Rabs (s - FT2R s0) <= error_rel (length l + 1) s).
{
apply IHl; auto.
{
set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)).
simpl in ea. subst ea.
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1)).
simpl in ea. subst ea.
fold e d ov  A'.
intros.
eapply Rle_trans.
apply H1.
simpl; auto.
assert (0 <= d) by lra.
apply le_div.
subst d. interval.
apply le_div2; try lra.
apply Rplus_le_compat_l.
apply Rmult_le_compat; try nra.
assert (0 <= e) by (compute; lra).
assert (A'*e*(1+d) <= A*e*(1+d)); [ | lra].
apply Rmult_le_compat_r; try lra.
apply Rmult_le_compat_r; try lra.
}
}
assert (Rabs (FT2R s0) <= error_rel (length l + 1) s + Rabs (s)).
{
apply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
rewrite Rabs_minus_sym; auto.
}
apply H0.

(*
assert (lem : forall a b c,
  0 < c -> a <= b -> a / c <= b / c ).
intros.
admit.
apply lem.
subst d; interval.
assert (lem2 : forall a b c1 c2,
  0 < c1 -> 0 < c2 -> c2 <= c1 -> a <= b -> a / c1 <= b / c2 ).
intros.
admit.

apply lem2; auto.
fold A'.
apply Rplus_le_compat_l.
apply Rmult_le_compat; auto.
apply Rplus_le_le_0_compat; try nra.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; auto; try nra.

fold A'.
apply Rplus_le_compat_l.
apply Ropp_le_contravar. 
apply Rmult_le_compat.
apply Rmult_le_pos; try subst e; try nra.
subst d; nra.
apply Rmult_le_compat_r; auto;
subst e; nra.
nra.
}
assert (Rabs (FT2R s0) <= error_rel (length l + 1) s + Rabs (s)).
{
apply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv.
rewrite Rabs_minus_sym; auto.
}
apply H0.
*)
cbv [error_rel].
rewrite Hif1.
set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)).
simpl in ea. subst ea.
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1)).
simpl in ea. subst ea.
fold e d ov.
assert (Rabs s <=
(ov - 2 * e - A * e * (1 + d)) / (1 + (A * d  + 1) * INR n) / (1 + d) * INR n).
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
fold sum_rel_R in H8.
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
  (ov - 2 * e - A * e * (1 + d)) / (1 + (A * d + 1) * INR n) / (1 + d)).
{
intros.
apply in_map_iff in H0.
destruct H0 as (A1 & B & C).
subst.
eapply Rle_trans.
apply H1. 
simpl; auto.
nra.
}

eapply Rle_trans.
eapply (H (map FT2R l) s).
intros.
apply H0; auto.
auto.
apply Rmult_le_compat; auto.
apply Stdlib.Rdiv_pos_compat; auto.
apply Stdlib.Rdiv_pos_compat; auto.
subst d; interval.
replace (length (map FT2R l)) with (length l); auto.
rewrite map_length; auto.
apply Req_le; nra.
replace (length (map FT2R l)) with (length l); auto.
rewrite map_length; auto.
}


replace (length l + 1 - 2)%nat with (n - 2)%nat.
replace ((INR (length l + 1) - 1)) with (INR n -1).
match goal with |-context [?a * ?b *?c ^ ?d] =>
replace (a * b * c ^ d) with
  (a * c ^ d * b) by nra;
fold A
end.

replace (
A * (Rabs s * d + e) + Rabs s)
with
(Rabs s * (A *d + 1) +A * e) by nra.

set (B:= (ov - 2 * e - A * e * (1 + d)) / (1 + (A * d + 1)* INR n)) in *.

eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; try nra.
apply H.


replace (
B / (1 + d) * (1 + INR n * (A * d + 1)) * (1 + d))
with
(B  * (1 + INR n * (A * d + 1))).
apply Generic_proof.Rdiv_le_mult_pos; try nra.

rewrite Rmult_plus_distr_r.
replace (
(B / (1 + d) * INR n * (A * d + 1) + A * e) * (1 + d))
with
((B  * INR n * (A * d + 1) + A * e * (1 + d)) ).

replace (B / (1 + d) * (1 + d)) with B.
rewrite <- Rplus_assoc.
replace (
B + B * INR n * (A * d + 1))
with
(B * (1 +INR n * (A * d + 1))) by nra.

replace (B * (1 + INR n * (A * d + 1)))
with (ov - 2 * e - A * e * (1 + d)).

field_simplify; nra.
subst B; field; nra.
field; nra.
field; nra.
field; nra.


subst n.
simpl (length (a :: l)).
replace (S (length l)) with (length l +1)%nat by lia; auto.

subst n.
simpl (length (a :: l)).
replace (S (length l)) with (length l +1)%nat by lia; auto.

unfold sum.
cbv [error_rel].
rewrite Hif1.
rewrite Hif2.

eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
simpl; nra.

eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat_l.

assert (Rabs (FT2R s0) <= error_rel (length l + 1) s + Rabs (s)).
{ assert (Rabs (s - FT2R s0) <= error_rel (length l + 1) s).
  apply IHl; auto.

set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)).
simpl in ea. subst ea.
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1)).
simpl in ea. subst ea.
fold e d ov  A'.
intros.
eapply Rle_trans.
apply H1.
simpl; auto.
{ 
apply le_div.
try subst d; interval.
apply le_div2; auto.
+
apply Rplus_le_compat_l.
apply Rmult_le_compat; auto.
apply Rplus_le_le_0_compat; try nra.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r; try subst d; try nra.
+
fold d in A'. 
fold A'.
apply Rplus_le_compat_l.
apply Ropp_le_contravar. 
apply Rmult_le_compat; try nra.
apply Rmult_le_pos; auto; try subst e; try nra.
try subst d; try nra.
apply powerRZ_le. lra.
apply Rmult_le_compat; auto; try lra.
apply powerRZ_le. lra.
}
rewrite Rabs_minus_sym in H.
apply Rcomplements.Rle_minus_l.
eapply Rle_trans.
apply Rabs_triang_inv. auto.
}
apply H.

cbv [error_rel].
rewrite Hif1.
fold n.
set (ea:= bpow Zaux.radix2 (3 - femax Tsingle - fprec Tsingle)).
simpl in ea. subst ea.
set (ea:= bpow Zaux.radix2 (- fprec Tsingle + 1)).
simpl in ea. subst ea.
fold e d ov.
 

replace (INR (length l + 1)) with (INR n).
replace (length l + 1 - 2)%nat with (n-2)%nat.
replace ((n + 1 - 2)%nat) with (n-1)%nat. 
replace ((INR (n + 1) - 1)) with (INR n).

match goal with |-context [?a * ?b *?c ^ ?d] =>
replace (a * b * c ^ d) with
  (a * c ^ d * b) by nra;
fold A
end.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
replace (A * (Rabs s * d) + A * e + Rabs (FT2R a) * d + A * (Rabs s * d) * d + A * e * d +
Rabs s * d + e)
with (
A * (Rabs s * d + e) *(1 + d) + Rabs s * d  + Rabs (FT2R a) * d  + e) by nra.
assert (0 <= FT2R a) by admit.
assert (0 <= s) by admit.
assert (
1 <= (1 + d) ^ (n - 1)).
{apply pow_R1_Rle.
try subst d; try nra.
}
repeat rewrite Rabs_pos_eq; try nra.
rewrite <- Rmult_plus_distr_r.
rewrite <- Rmult_plus_distr_l.
eapply Rle_trans.
apply Rplus_le_compat.
apply Rplus_le_compat.
apply Rplus_le_compat_l.
assert(
 s * d <=  s * d * (1 + d) ^ (n - 1)).
match goal with |- context[?a <= ?b] =>
replace a with (1 *a) at 1
end.
rewrite Rmult_comm.
apply Rmult_le_compat; try nra.
nra.
apply H4.
assert (
FT2R a * d * 1 <= (FT2R a * d) * INR n * (1 + d) ^ (n - 1) ). {
apply Rmult_le_compat; try nra.
replace (FT2R a * d) with (FT2R a * d * 1) at 1.
apply Rmult_le_compat; try nra. nra.
}
subst n; simpl (length (a :: l)).
replace 1 with (INR 1) by (simpl; nra).
rewrite Rmult_1_r in H4.
apply H4.
apply Rle_refl.
assert (e * 1 <= e * (1 + d) ^ (n - 1)).
{
apply Rmult_le_compat; try nra.
apply powerRZ_le. lra.
}
rewrite Rmult_1_r in H4.
fold e d A n.
replace (A * (s * d + e) * (1 + d)) with
((INR n - 1) * (1 + d) ^ (n - 1) * (s * d + e)).
apply Req_le.
(*nra.*)
replace (A * (s * d + e) * (1 + d)) with
(A * (1 + d) *(s * d + e)).
f_equal; subst A.
replace (1 + d) with ((1+d)^ 1) at 3.
rewrite Rmult_assoc.
f_equal; try nra.
f_equal.
Admitted.



End WITHNANS.