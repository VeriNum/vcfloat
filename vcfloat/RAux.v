(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)
(** More properties about real numbers. *)

From Coq Require Export Reals Psatz.
From Coq Require Export Lia.
Open Scope R_scope.

Lemma increasing_weaken f x y:
  (x < y -> f x < f y) ->
  x <= y -> f x <= f y.
Proof.
  intros.
  destruct (Req_dec x y); subst; lra.
Qed.

Lemma Rle_Rpower_strong:
  forall e n m : R, 1 < e -> n <= m -> Rpower e n <= Rpower e m.
Proof.
  unfold Rpower. intros.
  apply (increasing_weaken (fun t => exp (t * ln e))); auto.
  intros.
  apply exp_increasing.
  apply Rmult_lt_compat_r; auto.
  rewrite <- ln_1.
  apply ln_increasing; auto; lra.
Qed.


Lemma Rle_powerRZ_2:
  forall a b : R,
  forall n: nat,
  0 <= a ->
  a <= b -> powerRZ a (Z.of_nat n) <= powerRZ b (Z.of_nat n).
Proof.
  intros.
  induction n.
  + simpl. nra.
  + replace (Z.of_nat (S n)) with ( (Z.of_nat n + 1%Z)%Z) by lia.
    destruct H.
    - rewrite ?powerRZ_add; try nra.
      eapply Rmult_le_compat; try simpl; try nra.
      apply powerRZ_le; auto.
    - subst; destruct H0; subst; try simpl; try nra.
      assert ((0 < n + 1)%nat) by lia.
      pose proof pow_i (n+1) H0.
      replace (powerRZ 0 (Z.of_nat n + 1)) with
       (0^( n + 1)).
      pose proof pow_i (n+1) H0. rewrite H1. apply powerRZ_le; nra.
      rewrite ?pow_powerRZ; apply f_equal; lia.
Qed.

Lemma power_RZ_inv: forall x y, x <> 0 -> Rinv (powerRZ x y) = powerRZ x (-y).
Proof.
intros.
destruct y; simpl; auto.
apply Rinv_1.
apply Rinv_inv.
Qed.

Lemma lesseq_less_or_eq:
 forall x y : R,  x <= y -> x < y \/ x = y.
Proof. intros. lra. Qed.

Lemma Int_part_unique x z:
  IZR z <= x ->
  IZR z - x > -1 ->
  z = Int_part x.
Proof.
  intros.
  destruct (base_Int_part x).
  assert (K: -1 < IZR z - IZR (Int_part x) < 1) by lra.
  replace (-1) with (IZR (-1)) in K by reflexivity.
  replace (1) with (IZR (1)) in K by reflexivity.
  rewrite <- minus_IZR in K.
  destruct K as [KL KR].
  apply lt_IZR in KL.
  apply lt_IZR in KR.
  lia.
Qed.

Lemma IZR_Int_part x y:
  IZR x <= y ->
  (x <= Int_part y)%Z.
Proof.
  intros.
  destruct (base_Int_part y).
  assert (K: -1 < IZR (Int_part y) - IZR x) by lra.
  rewrite <- minus_IZR in K.
  replace (-1) with (IZR (-1)) in K by reflexivity.
  apply lt_IZR in K.
  lia.
Qed.

Lemma powerRZ_Rpower a b:
  0 < a ->
  powerRZ a b = Rpower a (IZR b).
Proof.
  intros.
  destruct b; simpl.
  {
    rewrite Rpower_O; auto.
  }
  {
   unfold IZR. rewrite <- INR_IPR.
    rewrite Rpower_pow; auto.
  }
  rewrite IZR_NEG. unfold IZR.  rewrite <- INR_IPR.
  rewrite Rpower_Ropp.
  rewrite Rpower_pow; auto.
Qed.

Lemma frac_part_sterbenz w:
  1 <= w ->
  IZR (Int_part w) / 2 <= w <= 2 * IZR (Int_part w).
Proof.
  intro K.
  generalize K.
  intro L.
  replace 1 with (IZR 1) in L by reflexivity.
  apply IZR_Int_part in L.
  apply IZR_le in L.
  simpl in L.
  destruct (base_Int_part w).
  lra.
Qed.


Lemma Rdiv_le_left d a b:
  0 < d ->
  a <= b * d ->
  a / d <= b.
Proof.
  intros.
  apply (Rmult_le_compat_r ( / d)) in H0.
  * rewrite Rmult_assoc in H0.
    rewrite <- Rinv_r_sym in H0; [ | lra].
    rewrite Rmult_1_r in H0.
    assumption.
  * cut (0 < / d); [ lra | ].
    apply Rinv_0_lt_compat.
    assumption.
Qed.

Lemma Rdiv_le_right_elim d a b:
  0 < d ->
  a <= b / d ->
  a * d <= b.
Proof.
  intros.
  apply Rdiv_le_left in H0.
  {
    unfold Rdiv in H0.
    rewrite Rinv_inv in H0; lra.
  }
  apply Rinv_0_lt_compat.
  assumption.
Qed.

Lemma Rdiv_lt_right d a b:
  0 < d ->
  a * d < b -> a < b / d.
Proof.
  intros.
  apply (Rmult_lt_compat_r ( / d)) in H0.
  * rewrite Rmult_assoc in H0.
    rewrite <- Rinv_r_sym in H0; [ | lra].
    rewrite Rmult_1_r in H0.
    assumption.
  * apply Rinv_0_lt_compat.
    assumption.
Qed.

Lemma Rdiv_lt_left d a b:
  0 < d ->
  a < b * d ->
  a / d < b.
Proof.
  intros.
  apply (Rmult_lt_compat_r ( / d)) in H0.
  * rewrite Rmult_assoc in H0.
    rewrite <- Rinv_r_sym in H0; [ | lra].
    rewrite Rmult_1_r in H0.
    assumption.
  * apply Rinv_0_lt_compat.
    assumption.
Qed.

Lemma Rdiv_lt_left_elim d a b:
  0 < d ->
  a / d < b -> a < b * d.
Proof.
  intros.
  apply Rdiv_lt_right in H0.
  {
    unfold Rdiv in H0.
    rewrite Rinv_inv in H0; lra.
  }
  apply Rinv_0_lt_compat.
  assumption.
Qed.

Lemma Rminus_diag x:
  x - x = 0.
Proof.
  ring.
Qed.

Lemma Rminus_le x y:
x - y <= 0 -> x<=y.
Proof.
  nra.
Qed.

Lemma Rminus_plus_le_minus x y z:
x + y <= z -> x <= z - y.
Proof.
intros.
nra.
Qed.

Lemma Rabs_le_minus x y z:
Rabs (x-y) <= z ->
Rabs x <= z + Rabs y.
Proof.
intros.
pose proof Rle_trans (Rabs x - Rabs y) (Rabs (x - y)) z
  (Rabs_triang_inv x y) H.
nra.
Qed.

Lemma Rabs_triang1 a b u v:
  Rabs a <= u ->
  Rabs b <= v ->
  Rabs (a + b) <= u + v.
Proof.
  intros.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  lra.
Qed.

Lemma Rabs_triang2 a b c u v:
  Rabs (a - b) <= u ->
  Rabs (b - c) <= v ->
  Rabs (a - c) <= u + v.
Proof.
  intros.
  replace (a - c) with (a - b + (b - c)) by ring.
  apply Rabs_triang1; auto.
Qed.

Lemma neg_powerRZ (x:R) (n:Z) :
  x <> R0 ->
  1 / (powerRZ x%R n%Z) = (powerRZ x%R (-n)%Z) .
Proof.
intros; pose proof power_RZ_inv x n H; symmetry; rewrite <- H0; nra.
Qed.



Lemma mul_hlf_powerRZ (n:Z) :
 / 2 * / powerRZ 2 n = powerRZ 2 (-n-1).
Proof.
assert (2 <> R0) by nra.
replace (/ 2) with (1/2) by nra.
replace (1 / 2 * / powerRZ 2 n) with
(1 / 2 * powerRZ 2 (- n)).
match goal with |- ?s = powerRZ ?a ?b' =>
replace b' with (-1 + - n)%Z by ring
end.
pose proof powerRZ_add 2 (-1) (-n) H. rewrite H0.
replace (1 / 2) with (powerRZ 2 (-1)). reflexivity.
simpl; nra.
replace (powerRZ 2 (- n)) with
(1 / powerRZ 2 n).
nra.
(apply neg_powerRZ); nra.
Qed.


From Coq Require Import ZArith.
From Coq Require Import Lists.List.

Ltac R_to_pos p :=
  match p with
  | 1%R => constr:(1%positive)
  | 2%R => constr:(2%positive)
  | 3%R => constr:(3%positive)
  | 1 + 2 * ?q =>
    let r := R_to_pos q in
    constr:(xI r)
  | 2 * ?q =>
    let r := R_to_pos q in
    constr:(xO r)
  end.

Ltac R_to_Z p :=
  match p with
  | - ?q =>
    let r := R_to_pos q in
    constr:(Z.neg r)
  | 0%R => constr:(0%Z)
  | ?q =>
    let r := R_to_pos q in
    constr:(Z.pos r)
  end.

(* Limits of derivatives and variations. *)

Theorem derivable_nonpos_decr :
  forall (f f':R -> R) (a b:R),
    a < b ->
    (forall c:R, a < c < b -> derivable_pt_lim f c (f' c)) ->
    (forall c:R, a < c < b -> f' c <= 0) ->
    forall x1 x2,
      a < x1 ->
      x1 <= x2 ->
      x2 < b ->
      f x2 <= f x1.
Proof.
  intros.
  destruct (Req_dec x1 x2).
  {
    apply Req_le.
    congruence.
  }
  assert (K: x1 < x2) by lra.
  destruct (MVT_cor2 f f' _ _ K) as (c & ? & ?).
  {
    intros.
    apply H0.
    lra.
  }
  cut (f' c * (x2 - x1) <= 0); [ lra | ].
  rewrite <- Ropp_0.
  rewrite <- (Ropp_involutive (f' c)).
  rewrite Ropp_mult_distr_l_reverse.
  apply Ropp_le_contravar.
  apply Rmult_le_pos.
  {
   assert (f' c  <= 0) by (apply H1; lra).
   lra.
  }
  lra.
Qed.

Theorem derivable_nonneg_incr :
  forall (f f':R -> R) (a b:R),
    a < b ->
    (forall c:R, a < c < b -> derivable_pt_lim f c (f' c)) ->
    (forall c:R, a < c < b -> 0 <= f' c) ->
    forall x1 x2,
      a < x1 ->
      x1 <= x2 ->
      x2 < b ->
      f x1 <= f x2.
Proof.
  intros.
  cut (opp_fct f x2 <= opp_fct f x1).
  {
    unfold opp_fct.
    lra.
  }
  eapply derivable_nonpos_decr with (a := a) (b := b) (f' := opp_fct f'); eauto.
  {
    intros.
    apply derivable_pt_lim_opp.
    auto.
  }
  unfold opp_fct.
  intros.
  replace 0 with (- 0) by ring.
  apply Ropp_le_contravar.
  auto.
Qed.

Theorem derivable_nonneg_incr' :
  forall (f f':R -> R) (a b:R),
    (forall c:R, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
    (forall c:R, a <= c <= b -> 0 <= f' c) ->
      a <= b ->
      f a <= f b.
Proof.
  intros.
  destruct (Req_dec a b).
  {
    subst. lra.
  }
  assert (K: a < b) by lra.
  destruct (MVT_cor2 f f' _ _ K H) as (c & ? & ?).
  cut (0 <= f' c * (b - a)); [ lra | ].
  apply Rmult_le_pos.
  {
    apply H0.
    lra.
  }
  lra.
Qed.

Theorem derivable_nonpos_decr' :
  forall (f f':R -> R) (a b:R),
    (forall c:R, a <= c <= b -> derivable_pt_lim f c (f' c)) ->
    (forall c:R, a <= c <= b -> f' c <= 0) ->
      a <= b ->
      f b <= f a.
Proof.
  intros.
  cut (opp_fct f a <= opp_fct f b).
  {
    unfold opp_fct.
    lra.
  }
  apply derivable_nonneg_incr' with (opp_fct f').
  {
    intros.
    apply derivable_pt_lim_opp.
    auto.
  }
  {
    intros.
    generalize (H0 _ H2).
    unfold opp_fct.
    lra.
  }
  assumption.
Qed.

(* Absolute error for sine/cosine *)

Lemma sin_ub x: 0 <= x -> sin x <= x.
Proof.
  intros.
  pose (f t := sin t - t).
  cut (f x <= f 0).
  {
    unfold f.
    rewrite sin_0.
    lra.
  }
  apply derivable_nonpos_decr' with (f' := fun t => cos t - 1); auto; intros.
  {
    apply derivable_pt_lim_minus.
    {
      apply derivable_pt_lim_sin.
    }
    apply derivable_pt_lim_id.
  }
  generalize (COS_bound c).
  lra.
Qed.

Corollary sin_ub_abs_pos x:
  0 <= x ->
  Rabs x <= PI / 2 ->
  Rabs (sin x) <= Rabs x.
Proof.
  intro.
  rewrite (Rabs_right x) by lra.
  intro.
  rewrite Rabs_right.
  {
    apply sin_ub; auto.
  }
  apply Rle_ge.
  rewrite <- sin_0.
  generalize PI2_3_2; intro.
  apply sin_incr_1; try lra.
Qed.

Corollary sin_ub_abs x:
  Rabs x <= PI / 2 ->
  Rabs (sin x) <= Rabs x.
Proof.
  intros.
  destruct (Rle_dec 0 x).
  {
    apply sin_ub_abs_pos; auto.
  }
  rewrite <- Rabs_Ropp.
  rewrite <- sin_neg.
  revert H.
  rewrite <- (Rabs_Ropp x).
  apply sin_ub_abs_pos.
  lra.
Qed.

Lemma sin_absolute_error_term x d:
  sin (x + d) - sin x = 2 * cos (x + d / 2) * sin (d / 2).
Proof.
  replace (x + d) with (x + d / 2 + d / 2) by field.
  replace x with (x + d / 2 - d / 2) at 2 by field.
  rewrite sin_plus.
  rewrite sin_minus.
  ring.
Qed.

Lemma sin_absolute_error_bound' x d:
  Rabs d <= PI ->
  Rabs (sin (x + d) - sin x) <= Rabs d.
Proof.
  intros.
  rewrite sin_absolute_error_term.
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  rewrite Rabs_right by lra.
  replace (Rabs d) with (2 * 1 * Rabs (d / 2))
    by (unfold Rdiv; rewrite Rabs_mult;
        rewrite (Rabs_right ( / 2)) by lra;
        field).
  repeat rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  {
    lra.
  }
  apply Rmult_le_compat; auto using Rabs_pos.
  {
    apply Rabs_le.
    apply COS_bound.
  }
  apply sin_ub_abs.
  unfold Rdiv. rewrite Rabs_mult.
  rewrite (Rabs_right (/ 2)) by lra.
  lra.
Qed.

Lemma sin_absolute_error_bound x d:
  Rabs (sin (x + d) - sin x) <= Rmin (Rabs d) 2.
Proof.
  unfold Rmin.
  destruct (Rle_dec (Rabs d) 2).
  {
    apply sin_absolute_error_bound'.
    generalize (PI2_3_2). lra.
  }
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  rewrite Rabs_Ropp.
  apply Rplus_le_compat;
    apply Rabs_le;
    apply SIN_bound.
Qed.

Lemma cos_absolute_error_bound x d:
  Rabs (cos (x + d) - cos x) <= Rmin (Rabs d) 2.
Proof.
  repeat rewrite cos_sin.
  rewrite <- Rplus_assoc.
  apply sin_absolute_error_bound.
Qed.

Lemma sin_abs_error a b d:
  Rabs (a - b) <= d ->
  Rabs (sin a - sin b) <= d.
Proof.
  intros.
  replace a with (b + (a - b)) by ring.
  eapply Rle_trans.
  {
    eapply sin_absolute_error_bound.
  }
  eapply Rle_trans.
  {
    apply Rmin_l.
  }
  assumption.
Qed.

Lemma cos_abs_error a b d:
  Rabs (a - b) <= d ->
  Rabs (cos a - cos b) <= d.
Proof.
  intros.
  replace a with (b + (a - b)) by ring.
  eapply Rle_trans.
  {
    eapply cos_absolute_error_bound.
  }
  eapply Rle_trans.
  {
    apply Rmin_l.
  }
  assumption.
Qed.

Lemma sin_abs x:
  Rabs x <= PI ->
  sin (Rabs x) = Rabs (sin x).
Proof.
  intros H.
  destruct (Rle_dec 0 x).
  {
    rewrite Rabs_right in * |- * by lra.
    rewrite Rabs_right; auto.
    generalize (sin_ge_0 x).
    lra.
  }
  destruct (Req_dec x (-PI)).
  {
    subst.
    rewrite sin_neg.
    repeat rewrite Rabs_Ropp.
    rewrite Rabs_right by lra.
    rewrite sin_PI.
    rewrite Rabs_R0.
    reflexivity.
  }
  rewrite Rabs_left in * |- * by lra.
  rewrite sin_neg.
  rewrite Rabs_left; auto.
  apply sin_lt_0_var; lra.
Qed.

Lemma cos_abs_eq u:
  cos (Rabs u) = cos u.
Proof.
  destruct (Rle_dec 0 u).
  {
    rewrite Rabs_right by lra.
    reflexivity.
  }
  rewrite Rabs_left by lra.
  apply cos_neg.
Qed.

Lemma abs_sign (b: bool):
  Rabs (if b then -1 else 1) = 1.
Proof.
  destruct b.
  {
    rewrite IZR_NEG.
    rewrite Rabs_Ropp.
    apply Rabs_R1.
  }
  apply Rabs_R1.
Qed.

(* Square root *)
Lemma sqrt_pos_strict x:
  0 < x ->
  0 < sqrt x.
Proof.
  intros.
  assert (sqrt x <> 0).
  {
    intro ABSURD.
    apply sqrt_eq_0 in ABSURD; lra.
  }
  generalize (sqrt_pos x).
  lra.
Qed.

Lemma cos_sin_plus_bound a:
  Rabs (cos a + sin a) <= sqrt 2.
Proof.
  rewrite <- cos_shift.
  rewrite form1.
  match goal with
  |- Rabs (2 * cos ?u * cos ?v) <= _ =>
      replace v with (PI / 4) by field;
      rewrite cos_PI4
  end.
  assert (0 < sqrt 2) as HSQRT.
  {
    apply sqrt_pos_strict.
    lra.
  }
  rewrite Rabs_mult.
  eapply Rle_trans.
  {
    apply Rmult_le_compat; auto using Rabs_pos.
    {
      rewrite Rabs_mult.
      apply Rmult_le_compat; auto using Rabs_pos.
      {
        rewrite Rabs_right by lra.
        apply Rle_refl.
      }
      apply Rabs_le.
      apply COS_bound.
    }
    rewrite Rabs_right.
    {
      apply Rle_refl.
    }
    apply Rinv_0_lt_compat in HSQRT.
    lra.
  }
  eapply (eq_rect_r (fun t => t <= _)).
  {
    apply Rle_refl.
  }
  rewrite <- (sqrt_sqrt 2) at 1 by lra.
  unfold IPR.
  field.
  lra.
Qed.

Lemma cos_sin_minus_bound a:
  Rabs (cos a - sin a) <= sqrt 2.
Proof.
  rewrite <- cos_neg.
  unfold Rminus.
  rewrite <- sin_neg.
  apply cos_sin_plus_bound.
Qed.

Lemma abs_cos_sin_plus_1 a:
  0 <= a <= PI / 2 ->
  Rabs (cos a) + Rabs (sin a) = cos a + sin a.
Proof.
  intros.
  generalize (cos_ge_0 a ltac:( lra ) ltac:( lra ) ).
  generalize (sin_ge_0 a ltac:( lra ) ltac:( lra ) ).
  intros.
  repeat rewrite Rabs_right by lra.
  reflexivity.
Qed.

Lemma abs_cos_sin_plus_aux_2 a:
  0 <= a <= PI ->
  exists b,
    Rabs (cos a) + Rabs (sin a) = cos b + sin b.
Proof.
  intros.
  destruct (Rle_dec a (PI / 2)).
  {
    exists a.
    apply abs_cos_sin_plus_1.
    lra.
  }
  exists (PI - a).
  replace a with ((- (PI - a)) + PI) at 1 by ring.
  rewrite neg_cos.
  rewrite cos_neg.
  rewrite Rabs_Ropp.
  replace a with (PI - (PI - a)) at 2 by ring.
  rewrite sin_PI_x.
  apply abs_cos_sin_plus_1.
  lra.
Qed.

Lemma abs_cos_sin_plus_aux_3 a:
  - PI <= a <= PI ->
  exists b,
    Rabs (cos a) + Rabs (sin a) = cos b + sin b.
Proof.
  intros.
  destruct (Rle_dec 0 a).
  {
    apply abs_cos_sin_plus_aux_2.
    lra.
  }
  replace a with (- (- a)) by ring.
  rewrite cos_neg.
  rewrite sin_neg.
  rewrite Rabs_Ropp.
  apply abs_cos_sin_plus_aux_2.
  lra.
Qed.

Lemma cos_period_1 x k:
  (0 <= k)%Z ->
  cos (x + 2 * IZR k * PI) = cos x.
Proof.
  intro LE.
  apply IZN in LE.
  destruct LE.
  subst.
  rewrite <- INR_IZR_INZ.
  apply cos_period.
Qed.

Lemma cos_period' k x:
  cos (x + 2 * IZR k * PI) = cos x.
Proof.
  destruct (Z_le_dec 0 k) as [ LE | ].
  {
    apply cos_period_1.
    lia.
  }
  match goal with
  |- cos ?a = _ =>
     rewrite <- (Ropp_involutive a);
     rewrite cos_neg;
     replace (- a) with ((- x) + 2 * (- IZR k) * PI) by ring
  end.
  rewrite <- opp_IZR.
  rewrite cos_period_1 by lia.
  apply cos_neg.
Qed.

Lemma sin_period' k x:
  sin (x + 2 * IZR k * PI) = sin x.
Proof.
  repeat rewrite <- cos_shift.
  match goal with
  |- cos ?a = _ =>
    replace a with (PI / 2 - x + 2 * (- IZR k) * PI) by ring
  end.
  rewrite <- opp_IZR.
  apply cos_period'.
Qed.

Lemma frac_part_ex x:
{ i |
  IZR (Int_part x) = x - i /\ 0 <= i < 1
}.
Proof.
  exists (x - IZR (Int_part x)).
  split.
  {
    ring.
  }
  generalize (base_Int_part x).
  lra.
Qed.

Lemma sin_period_minus x z:
  sin (x - IZR z * (2 * PI)) = sin x.
Proof.
  unfold Rminus.
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- opp_IZR.
  generalize (- z)%Z.
  clear z.
  intro z.
  replace (IZR z * (2 * PI)) with (2 * IZR z * PI) by ring.
  destruct z; simpl.
  {
    f_equal.
    ring.
  }
  {
    unfold IZR. rewrite <- !INR_IPR.
    apply sin_period.
  }
    unfold IZR. rewrite <- !INR_IPR.
  generalize (Pos.to_nat p).
  clear p. simpl.
  intro n.
  rewrite <- (sin_period _ n).
  f_equal.
  ring.
Qed.

Lemma cos_period_minus x z:
  cos (x - IZR z * (2 * PI)) = cos x.
Proof.
  repeat rewrite <- sin_shift.
  replace (PI / 2 - (x - IZR z * (2 * PI))) with (PI / 2 - x - IZR (- z) * (2 * PI)).
  {
    apply sin_period_minus.
  }
  rewrite opp_IZR.
  ring.
Qed.

Lemma cos_PI_x x:
  cos (PI - x) = - cos x.
Proof.
  replace (PI - x) with ((-x) + PI) by ring.
  rewrite neg_cos.
  rewrite cos_neg.
  reflexivity.
Qed.

Lemma abs_cos_sin_plus a:
  exists b,
    Rabs (cos a) + Rabs (sin a) = cos b + sin b.
Proof.
  remember (a / (2 * PI) + / 2) as u.
  remember (- Int_part u)%Z as k.
  rewrite <- (cos_period' k).
  rewrite <- (sin_period' k).
  apply abs_cos_sin_plus_aux_3.
  subst k.
  rewrite opp_IZR.
  destruct (base_Int_part u).
  remember (IZR (Int_part u)) as k.
  clear Heqk.
  subst.
  assert (k - / 2 <= a / (2 * PI)) as LE by lra.
  assert (a / (2 * PI) < k + 1 - / 2) as LT by lra.
  generalize (PI_RGT_0).
  intros.
  apply Rdiv_le_right_elim in LE; [ | lra ] .
  match type of LE with ?v <= _ =>
  replace v with (- (2 * - k * PI) - PI) in LE by field
  end.
  apply Rdiv_lt_left_elim in LT; [ | lra ] .
  match type of LT with _ < ?v =>
  replace v with (- (2 * - k * PI) + PI) in LT by field
  end.
  lra.
Qed.

Corollary abs_cos_sin_plus_le a:
  Rabs (cos a) + Rabs (sin a) <= sqrt 2.
Proof.
  match goal with
  |- ?u <= _ => rewrite <- (Rabs_right u)
  end.
  {
    destruct (abs_cos_sin_plus a) as (? & K).
    rewrite K.
    apply cos_sin_plus_bound.
  }
  generalize (Rabs_pos (cos a)).
  generalize (Rabs_pos (sin a)).
  lra.
Qed.

Lemma sqrt_abs_error x d:
  0 <= x ->
  0 <= x + d ->
  sqrt (x + d) - sqrt x = d / (sqrt (x + d) + sqrt x).
Proof.
  intros.
  destruct (Req_dec d 0).
  {
    subst.
    unfold Rdiv.
    rewrite Rplus_0_r.
    ring.
  }
  assert (0 < x \/ 0 < x + d) as OR by lra.
  assert (0 + 0 < sqrt (x + d) + sqrt x).
  {
    destruct OR.
    {
      apply Rplus_le_lt_compat.
      {
        apply sqrt_pos.
      }
      apply sqrt_pos_strict.
      assumption.
    }
    apply Rplus_lt_le_compat.
    {
      apply sqrt_pos_strict.
      assumption.
    }
    apply sqrt_pos.
  }
  replace d with (x + d - x) at 2 by ring.
  rewrite <- (sqrt_sqrt (x + d)) at 2 by assumption.
  rewrite <- (sqrt_sqrt x) at 5 by assumption.
  field.
  lra.
Qed.

Lemma sqrt_abs_error' x y:
  0 <= x ->
  0 <= y ->
  Rabs (sqrt y - sqrt x) = Rabs (y - x) / (sqrt y + sqrt x).
Proof.
  intros.
  replace y with (x + (y - x)) at 1 by ring.
  rewrite sqrt_abs_error by lra.
  unfold Rdiv.
  rewrite Rabs_mult.
  replace (x + (y - x)) with y by ring.
  destruct (Req_dec y x).
  {
    subst.
    rewrite Rminus_diag.
    rewrite Rabs_R0.
    ring.
  }
  f_equal.
  assert (0 < x \/ 0 < y) as OR by lra.
  generalize match OR with
  | or_introl K => or_introl (sqrt_pos_strict _ K)
  | or_intror K => or_intror (sqrt_pos_strict _ K)
  end.
  intros.
  generalize (sqrt_pos x). generalize (sqrt_pos y). intros.
  rewrite Rabs_inv by lra.
  f_equal.
  rewrite Rabs_right by lra.
  reflexivity.
Qed.

Corollary sqrt_abs_error_bound x y d:
  Rabs (y - x) <= d ->
  0 < x (* one of the two must be positive, we arbitrarily choose x *) ->
  0 <= y ->
  Rabs (sqrt y - sqrt x) <= d / (sqrt y + sqrt x).
Proof.
  intros Hxy Hx Hy.
  generalize (sqrt_pos y). intro.
  generalize (sqrt_pos_strict _ Hx). intro.
  rewrite sqrt_abs_error' by lra.
  apply Rmult_le_compat_r.
  {
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.
  }
  assumption.
Qed.

Lemma sqrt_succ_le :
forall n: R,
0 <= n ->
sqrt(n) < sqrt(n+1).
Proof.
intros.
assert (0 <= n+1) by nra.
assert (n < n+1) by nra.
pose proof sqrt_lt_1 n (n+1) H H0 H1; apply H2.
Qed.


Lemma eq_le_le x y:
  x = y ->
  y <= x <= y.
Proof.
  lra.
Qed.

Lemma Rdiv_le_0_compat_Raux : forall r1 r2 : R, 0 <= r1 -> 0 < r2 -> 0 <= r1 / r2.
Proof.
 intros.
 apply Rmult_le_pos; auto.
 apply Rinv_0_lt_compat in H0. lra.
Qed.

Lemma  Rabs_div_Raux : forall a b : R, b <> 0 -> Rabs (a/b) = (Rabs a) / (Rabs b).
Proof.
intros.
unfold Rdiv.
rewrite Rabs_mult. rewrite Rabs_inv. auto.
Qed.

Lemma Rabs_div_eq : forall a b , b <> 0 -> 0 <= b -> Rabs (a /b) = Rabs a / b.
Proof. intros. rewrite Rabs_div_Raux; try nra; replace (Rabs b) with b; try nra; symmetry; apply Rabs_pos_eq; auto. Qed.

Lemma Rminus_rel_error :
forall u1 u2 v1 v2, ((u1 - v1) ) - (u2 - v2) = (u1 - u2) - (v1 - v2).
Proof. intros. nra. Qed.

Lemma Rplus_rel_error:
forall u1 u2 v1 v2, (u1 + v1) - (u2 + v2) = (u1 - u2) + (v1 - v2).
Proof. intros. nra. Qed.

Lemma Rmult_rel_error:
forall u1 v1 u v, (u1 * v1) - (u  * v) = (u1 - u)*v + (v1 - v)*u + (u1-u) * (v1-v).
Proof. intros.  nra. Qed.


Lemma Rdiv_rel_error : forall u v u' v', v' <>0 -> v <> 0 -> u <> 0 ->
u'/v' - u/v = ((u'-u)/u - (v'-v)/v ) * (1 / (1 + ((v'-v)/v))) * (u/v).
Proof. intros. field_simplify; repeat try split; try nra; auto. Qed.

Lemma Rdiv_rel_error_add : forall u v u' v', v' <>0 -> v <> 0 -> u <> 0 ->
Rabs (u'/v' - u/v) <=
(Rabs((u'-u) / u) + Rabs((v'-v) /v)) * Rabs (1 / (1 + ((v'-v)/v))) * Rabs (u/v).
Proof.
intros.
rewrite Rdiv_rel_error; auto.
rewrite Rabs_mult.
rewrite Rabs_mult.
eapply Rle_trans.
rewrite Rmult_assoc.
apply Rmult_le_compat. apply Rabs_pos.
rewrite <- Rabs_mult.
apply Rabs_pos.
match goal with |- Rabs (?a/u - ?b /v) <= _=>
replace (a/u - b /v) with (a/u + (v - v') /v) by nra
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
apply Rle_refl. apply Rle_refl.
apply Rle_refl.
rewrite Rmult_assoc.
replace ((v - v')/v) with (-((v' - v)/v)) by nra.
rewrite Rabs_Ropp.
apply Rle_refl.
Qed.

Lemma Rdiv_rel_error_add_reduced_r : forall u v u' v', v' <>0 -> v <> 0 -> u <> 0 ->
Rabs (u'/v' - u/v) <=
(Rabs((u'-u)/u)  + Rabs (v'-v) * Rabs(1/v)) * Rabs (1 / (1 + ((v'-v)/v))) * Rabs (u/v).
Proof.
intros.
rewrite Rdiv_rel_error; auto.
eapply Rle_trans.
rewrite Rmult_assoc.
rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
match goal with |- Rabs (?a/u - ?b /v) <= _=>
replace (a/u - b /v) with (a/u + (v - v') /v) by nra
end.
match goal with |- Rabs (?a/u + ?b /v) <= _=>
replace (a/u + b /v) with (a/u + b * (1 /v))
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
apply Rle_refl.
rewrite Rabs_mult. rewrite Rabs_minus_sym. apply Rle_refl.
field_simplify. f_equal. split; auto. split; auto.
rewrite Rabs_mult; apply Rle_refl.
rewrite Rmult_assoc.
apply Rle_refl.
Qed.

Lemma Rdiv_rel_error_add_reduced_l : forall u v u' v', v' <>0 -> v <> 0 -> u <> 0 ->
Rabs (u'/v' - u/v) <=
(Rabs(u'-u) * Rabs(1/u)  + Rabs((v'-v)/v)) * Rabs (1 / (1 + ((v'-v)/v))) * Rabs (u/v).
Proof.
intros.
rewrite Rdiv_rel_error; auto.
eapply Rle_trans.
rewrite Rmult_assoc.
rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
match goal with |- Rabs (?a/u - ?b /v) <= _=>
replace (a/u - b /v) with (a/u + (v - v') /v) by nra
end.
match goal with |- Rabs (?a/u + ?b /v) <= _=>
replace (a/u + b /v) with (a * (1/u) + b /v)
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
rewrite Rabs_mult. apply Rle_refl.
rewrite <- Rabs_Ropp. apply Rle_refl.
field_simplify. f_equal. split; auto. split; auto.
rewrite Rabs_mult; apply Rle_refl.
rewrite Rmult_assoc.
apply Req_le.
f_equal. f_equal. f_equal.
nra.
Qed.

Lemma Rdiv_rel_error_add_reduced : forall u v u' v', v' <>0 -> v <> 0 -> u <> 0 ->
Rabs (u'/v' - u/v) <=
(Rabs(u'-u) * Rabs (1/u) + Rabs (v'-v) * Rabs(1/v)) * Rabs (1 / (1 + ((v'-v)/v))) * Rabs (u/v).
Proof.
intros.
rewrite Rdiv_rel_error; auto.
eapply Rle_trans.
rewrite Rmult_assoc.
rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
match goal with |- Rabs (?a/u - ?b /v) <= _=>
replace (a/u - b /v) with (a/u + (v - v') /v) by nra
end.
match goal with |- Rabs (?a/u + ?b /v) <= _=>
replace (a/u + b /v) with (a * (1/u) + b * (1 /v))
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
rewrite Rabs_mult; apply Rle_refl.
rewrite Rabs_mult. rewrite Rabs_minus_sym. apply Rle_refl.
field_simplify. f_equal. split; auto. split; auto.
rewrite Rabs_mult; apply Rle_refl.
rewrite Rmult_assoc.
apply Rle_refl.
Qed.

Lemma Rdiv_rel_error_no_u_div' : forall u v u' v', v' <>0 -> v <> 0 ->
u'/v' - u/v = ((u'-u) - (v'-v) * 1/v * u)  * (1 / (1 + ((v'-v)/v))) * (1/v).
Proof. intros. field_simplify; repeat try split; try nra; auto. Qed.

Lemma Rdiv_rel_error_no_u_div2 : forall u v u' v', v' <>0 -> v <> 0 ->
u'/v' - u/v = ((u'-u) - (v'-v)/v  * u)  * (1 / (1 + ((v'-v)/v))) * (1/v).
Proof. intros. field_simplify; repeat try split; try nra; auto. Qed.

Lemma Rdiv_rel_error_no_u_div_reduced :
forall u v u' v', v' <>0 -> v <> 0 ->
Rabs (u'/v' - u/v) <= (Rabs (u'-u)  +  Rabs ((v'-v)) * Rabs (1/v) * Rabs u)  * Rabs (1 / (1 + ((v'-v)/v))) * Rabs (1/v).
Proof.
intros.
rewrite Rdiv_rel_error_no_u_div'; auto.
eapply Rle_trans.
rewrite Rmult_assoc.
rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
match goal with |- Rabs (?a - (v' - v) *1/v * u) <= _=>
replace (a - (v' - v) * 1/v * u) with (a + (v - v') * (1/v) * u) by nra
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
apply Rle_refl.
rewrite Rabs_mult.
apply Rmult_le_compat;
try apply Rabs_pos.
rewrite Rabs_mult.
apply Rmult_le_compat;
try apply Rabs_pos.
rewrite <- Rabs_Ropp;  apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
rewrite Rabs_mult.
apply Rmult_le_compat;
try apply Rabs_pos.
apply Rle_refl.
apply Rle_refl.
repeat rewrite Rmult_assoc.
apply Req_le.
f_equal. f_equal. f_equal.
f_equal.
nra.
Qed.

Lemma Rdiv_rel_error_no_u_div_reduced2 :
forall u v u' v', v' <>0 -> v <> 0 ->
Rabs (u'/v' - u/v) <= (Rabs (u'-u)  +  Rabs ((v'-v)/v)* Rabs u)  * Rabs (1 / (1 + ((v'-v)/v))) * Rabs (1/v).
Proof.
intros.
rewrite Rdiv_rel_error_no_u_div2; auto.
eapply Rle_trans.
rewrite Rmult_assoc.
rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
match goal with |- Rabs (?a - (v' - v)/v * u) <= _=>
replace (a - (v' - v)/v * u) with (a + (v - v')/v * u) by nra
end.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat.
apply Rle_refl.
rewrite Rabs_mult.
apply Rmult_le_compat;
try apply Rabs_pos.
rewrite <- Rabs_Ropp;  apply Rle_refl.
apply Rle_refl.
apply Rle_refl.

repeat rewrite Rmult_assoc.
apply Req_le.
f_equal. f_equal. f_equal.
f_equal.
nra.
rewrite Rabs_mult.
nra.
Qed.

Lemma Rplus_opp : forall a b,
a + - b = a - b. Proof. intros. nra. Qed.

Lemma Rabs_Ropp2 :
forall A D U,  Rabs(-A * D - - U) = Rabs(A * D - U).
Proof.
intros.
rewrite <- Rabs_Ropp.
rewrite Ropp_minus_distr.
f_equal. nra. Qed.

Require Flocq.Core.Raux.

Lemma center_R_correct a b x:
 0 <= b - a - Rabs (2 * x - (a + b)) ->
 a <= x <= b.
Proof.
  intros.
  assert (Rabs (2 * x - (a + b)) <= (b - a) )%R by lra.
  apply Raux.Rabs_le_inv in H0.
  lra.
Qed.

Lemma center_R_complete a b x:
 a <= x <= b ->
 0 <= b - a - Rabs (2 * x - (a + b)).
Proof.
  intros.
  cut (Rabs (2 * x - (a + b)) <= (b - a)); [ lra | ].
  apply Rabs_le.
  lra.
Qed.

Definition center_Z a x b :=
  (b - a - Z.abs (2 * x - (a + b)))%Z
.

Lemma center_Z_correct a b x:
  (0 <= center_Z a x b)%Z ->
  (a <= x <= b)%Z.
Proof.
  unfold center_Z.
  intros.
  apply IZR_le in H.
  replace (IZR 0) with 0 in H by reflexivity.
  repeat rewrite minus_IZR in H.
  rewrite abs_IZR in H.
  rewrite minus_IZR in H.
  rewrite mult_IZR in H.
  rewrite plus_IZR in H.
  replace (IZR 2) with 2 in H by reflexivity.
  apply center_R_correct in H.
  intuition eauto using le_IZR.
Qed.

Lemma center_Z_complete a b x:
  (a <= x <= b)%Z ->
  (0 <= center_Z a x b)%Z.
Proof.
  unfold center_Z.
  intros.
  apply le_IZR.
  replace (IZR 0) with 0 by reflexivity.
  repeat rewrite minus_IZR.
  rewrite abs_IZR.
  rewrite minus_IZR.
  rewrite mult_IZR.
  rewrite plus_IZR.
  replace (IZR 2) with 2 by reflexivity.
  apply center_R_complete.
  intuition eauto using IZR_le.
Qed.


