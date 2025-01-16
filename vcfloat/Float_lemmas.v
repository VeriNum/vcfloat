From vcfloat Require Import RAux.
From Flocq Require Import Binary Bits Core Zaux.
From vcfloat Require Import IEEE754_extra.
Require vcfloat.Fprop_absolute.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Import Bool.

Local Open Scope R_scope.

(*
Lemma binary_float_eqb_eq_rect_r:
 forall ty1 ty2 (STD: is_standard ty1) (a b: binary_float (fprec ty1) (femax ty1))
  (H: ty2=ty1),
@binary_float_eqb (fprec ty1) (femax ty1) (fprec ty2) (femax ty2) 
  a (@eq_rect_r type ty1 ftype b ty2 H) = 
  binary_float_eqb a b.
Proof.
intros. subst ty2.
reflexivity.
Qed.
*)

Require Import vcfloat.FPCore.

Global Existing Instance fprec_gt_0. (* to override the Opaque one in Interval package *)


Section WITHNANS.

Context {NANS: Nans}.

Definition Bsqrt ty {STD: is_standard ty}:= Bsqrt _ _ (fprec_gt_0 ty) (fprec_lt_femax ty) (sqrt_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE.

Definition F2 prec emax e  :=
if Z_lt_le_dec (e+1) (3 - emax)
 then F754_zero false
 else let p := Pos.pred prec in
  F754_finite false (2 ^ p) (e - Z.pos p).

Lemma F2R_F2 prec emax e:
   (3 - emax <= e + 1)%Z ->
  FF2R Zaux.radix2 (F2 prec emax e) = Raux.bpow Zaux.radix2 e.
Proof.
  unfold F2.
 destruct (Z_lt_le_dec _ _); [lia | ].
 intros _.
  simpl.
  unfold Defs.F2R.
  simpl Defs.Fnum.
  simpl Defs.Fexp.
  generalize (Pos.pred prec).
  intros.
  rewrite Pos2Z.inj_pow.
  replace 2%Z with (Zaux.radix_val Zaux.radix2) by reflexivity.
  rewrite Raux.IZR_Zpower by (vm_compute; congruence).
  rewrite <- Raux.bpow_plus.
  f_equal.
  ring.
Qed.

Lemma F2_valid_binary_gen prec emax e:
  (Z.pos prec < emax)%Z ->
  (e + 1 <= emax)%Z ->
  prec <> 1%positive ->
  valid_binary (Z.pos prec) emax (F2 prec emax e) = true.
Proof.
  intros.
  unfold valid_binary.
  unfold F2.
  destruct (Z_lt_le_dec _ _); auto.
  rename H0 into H0'.
  assert (H0 := conj l H0'). clear l H0'.
  apply bounded_canonical_lt_emax.
  { constructor. }
  { assumption.  }
  {
   red.
   rewrite cexp_fexp with (ex := (e + 1)%Z). 
    {
      simpl Defs.Fexp.
      unfold FLT_exp.
      symmetry. unfold SpecFloat.fexp.
      rewrite  Z.max_l.
      {
        rewrite Pos2Z.inj_pred by assumption.
        lia.
      }
      unfold SpecFloat.emin; lia.
    }
    unfold Defs.F2R. simpl Defs.Fnum. simpl Defs.Fexp.
    rewrite Pos2Z.inj_pow.
    replace 2%Z with (Zaux.radix_val Zaux.radix2) by reflexivity.
    rewrite Raux.IZR_Zpower by (vm_compute; congruence).
    rewrite <- Raux.bpow_plus.
    rewrite Rabs_right.
    {
      split.
      {
        apply Raux.bpow_le.
        lia.
      }
      apply Raux.bpow_lt.
      lia.
    }
    apply Rle_ge.
    apply Raux.bpow_ge_0.
  }
  unfold Defs.F2R. simpl Defs.Fnum. simpl Defs.Fexp.
  rewrite Pos2Z.inj_pow.
  replace 2%Z with (Zaux.radix_val Zaux.radix2) by reflexivity.
  rewrite Raux.IZR_Zpower by (vm_compute; congruence).
  rewrite <- Raux.bpow_plus.
  apply Raux.bpow_lt.
  lia.
Qed.

Lemma F2_valid_binary ty e:
  (e + 1 <= femax ty)%Z ->
  valid_binary (fprec ty) (femax ty) (F2 (fprecp ty) (femax ty) e) = true.
Proof.
  intros.
  destruct (Z_lt_le_dec (e+1) (3 - (femax ty))).
-
  unfold F2. 
  destruct (Z_lt_le_dec (e+1) (3 - (femax ty))); try lia.
  reflexivity.
-
  apply F2_valid_binary_gen.
  { apply fprec_lt_femax. }
  { assumption. }
  apply fprecp_not_one.
Qed.

Definition B2 ty e := FF2B_gen (fprec ty) (femax ty) (F2 (fprecp ty) (femax ty) e).
Definition B2_opp ty (STD: is_standard ty) e := BOPP (ftype_of_float (B2 ty e)).

Lemma B2_finite ty e:
  (e + 1 <= femax ty)%Z ->
  Binary.is_finite _ _ (B2 ty e) = true.
Proof.
  unfold B2.
  intros.
  rewrite (FF2B_gen_correct _ _ _ (F2_valid_binary _ _ H)).
  set (j := F2_valid_binary _ _ _). clearbody j. revert j.
  destruct (F2 _ _ _) eqn:?H; intros; auto;
  exfalso; clear - H0; unfold F2 in H0;
  destruct (Z_lt_le_dec _ _) in H0; inversion H0.
Qed.

Lemma B2_correct ty e:
  (3 - femax ty <= e + 1 <= femax ty)%Z ->
  B2R _ _ (B2 ty e) = Raux.bpow Zaux.radix2 e.
Proof.
  intros.
  unfold B2.
  rewrite (FF2B_gen_correct _ _ _ (F2_valid_binary _ _ (proj2 H))).
  rewrite B2R_FF2B.
  apply F2R_F2.
  destruct H; auto.
Qed.

Definition fone: Defs.float Zaux.radix2 :=
  {|
    Defs.Fnum := 1;
    Defs.Fexp := 0
  |}.

Local Open Scope R_scope.

Lemma F2R_fone: F2R _ fone = 1.
Proof.
  simpl. ring.
Qed.

Definition ftwo: Defs.float Zaux.radix2 :=
  {|
    Defs.Fnum := 1;
    Defs.Fexp := 1
  |}.

Lemma F2R_ftwo: F2R _ ftwo = 2.
Proof.
 unfold F2R, ftwo. ring_simplify. reflexivity.
Qed.

Lemma Rabs_lt_pos: forall x : R, 0 < Rabs x -> x <> 0.
Proof.
  intros.
  unfold Rabs in H.
  destruct (Rcase_abs x); lra.
Qed.

Lemma FLT_format_mult_beta_n_aux beta emin prec n
      x:
  FLX.Prec_gt_0 prec ->
  (Generic_fmt.generic_format
     beta (FLT.FLT_exp emin prec) x) ->  
  Generic_fmt.generic_format
    beta
    (FLT.FLT_exp emin prec)
    (x * Raux.bpow beta (Z.of_N n)).
Proof.
  intros.
  revert x H0.
  rewrite <- N_nat_Z.
  induction (N.to_nat n).
  {
    simpl.
    intros.
    rewrite Rmult_1_r.
    auto.
  }
  intros.
  rewrite Nat2Z.inj_succ.
  unfold Z.succ.
  rewrite bpow_plus_1.
  rewrite (Rmult_comm (IZR _)).
  rewrite <- Rmult_assoc.
  apply FLT.generic_format_FLT.
  rewrite <- (Rmult_comm (IZR _)).
  apply Fprop_absolute.FLT_format_mult_beta.
  apply FLT.FLT_format_generic; auto.
Qed.

Lemma FLT_format_mult_beta_n ty (STD: is_standard ty) (x: ftype ty) n rnd
      {H: Generic_fmt.Valid_rnd rnd}:
  Generic_fmt.round
      Zaux.radix2
      (FLT.FLT_exp (3 - femax ty - fprec ty) (fprec ty))
      rnd (B2R _ _ (float_of_ftype x) * Raux.bpow Zaux.radix2 (Z.of_N n)) = 
         B2R _ _ (float_of_ftype x) * Raux.bpow Zaux.radix2 (Z.of_N n).
Proof.
  intros.
  apply Generic_fmt.round_generic; auto.
  apply FLT_format_mult_beta_n_aux; try typeclasses eauto.
  apply generic_format_B2R.
Qed.

Lemma bpow_minus1
     : forall (r : Zaux.radix) (e : Z),
       Raux.bpow r (e - 1) =
       Raux.bpow r e / IZR (Zaux.radix_val r)
.
Proof.
  intros.
  replace (e - 1)%Z with (e + - (1))%Z by ring.
  rewrite Raux.bpow_plus.
  rewrite Raux.bpow_opp.
  unfold Rdiv.
  f_equal.
  f_equal.
  simpl.
  f_equal.
  apply Zpow_facts.Zpower_pos_1_r.
Qed.

Lemma FLT_format_div_beta_1_aux beta emin prec n
      x:
  FLX.Prec_gt_0 prec ->
  (Generic_fmt.generic_format
     beta (FLT.FLT_exp emin prec) x) ->
  Raux.bpow beta (emin + prec + Z.pos n - 1) <= Rabs x ->
  Generic_fmt.generic_format
    beta
    (FLT.FLT_exp emin prec)
    (x / Raux.bpow beta (Z.pos n)).
Proof.
  intros until 1.
  unfold Rdiv.
  rewrite <- Raux.bpow_opp.
  rewrite <- positive_nat_Z.
  revert x.
  induction (Pos.to_nat n).
  {
    simpl.
    intros.
    rewrite Rmult_1_r.
    auto.
  }
  intro.
  rewrite Nat2Z.inj_succ.
  unfold Z.succ.
  intros.
  replace (- (Z.of_nat n0 + 1))%Z with (- Z.of_nat n0 - 1)%Z by ring.
  rewrite bpow_minus1.
  unfold Rdiv.
  rewrite <- Rmult_assoc.
  apply FLT.generic_format_FLT.
  apply Fprop_absolute.FLT_format_div_beta.
  {
    unfold FLX.Prec_gt_0 in H. lia.
  }
  {
    apply FLT.FLT_format_generic; auto.
    apply IHn0; auto.
    eapply Rle_trans; [ | eassumption ].
    apply Raux.bpow_le.
    lia.
  }
  rewrite Rabs_mult.
  rewrite (Rabs_right (Raux.bpow _ _)) by (apply Rle_ge; apply Raux.bpow_ge_0).
  eapply Rle_trans; [ | apply Rmult_le_compat_r ; try eassumption ].
  {
    rewrite <- Raux.bpow_plus.
    apply Raux.bpow_le.
    lia.
  }
  apply Raux.bpow_ge_0.
Qed.

Lemma FLT_format_div_beta_1 ty (x: binary_float (fprec ty) (femax ty)) n rnd
      {H: Generic_fmt.Valid_rnd rnd}:
  Raux.bpow Zaux.radix2 (3 - femax ty + Z.pos n - 1) <= Rabs (B2R _ _ x) ->
  Generic_fmt.round
      Zaux.radix2
      (FLT.FLT_exp (3 - femax ty - fprec ty) (fprec ty))
      rnd (B2R _ _ x * / Raux.bpow Zaux.radix2 (Z.pos n)) = 
          B2R _ _ x / Raux.bpow Zaux.radix2 (Z.pos n).
Proof.
  intros.
  apply Generic_fmt.round_generic; auto.
  apply FLT_format_div_beta_1_aux; try typeclasses eauto.
  {
    apply generic_format_B2R.
  }
  eapply Rle_trans; [ | eassumption ].
  apply Raux.bpow_le.
  lia.
Qed.

Lemma Bdiv_beta_no_overflow' ty (STD: is_standard ty) (x: ftype ty) n:
  Binary.is_finite _ _ (float_of_ftype x) = true ->
  (n >= 0)%Z ->
  Rabs (B2R _ _ (float_of_ftype x) / Raux.bpow Zaux.radix2 n) < Raux.bpow Zaux.radix2 (femax ty).
Proof.
  intros.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite <- Raux.bpow_opp.
  rewrite (Rabs_right (Raux.bpow _ _)) by (apply Rle_ge; apply Raux.bpow_ge_0).
  eapply Rlt_le_trans.
  {
    apply Rmult_lt_compat_r.
    {
      apply Raux.bpow_gt_0.
    }
    apply abs_B2R_lt_emax.
  }
  rewrite <- Raux.bpow_plus.
  apply Raux.bpow_le.
  lia.
Qed.

Lemma Bdiv_beta_no_overflow ty (STD: is_standard ty) (x: ftype ty) n:
  Binary.is_finite _ _ (float_of_ftype x) = true ->
  Rabs (B2R _ _ (float_of_ftype x) / Raux.bpow Zaux.radix2 (Z.pos n)) < Raux.bpow Zaux.radix2 (femax ty).
Proof.
  intros.
  apply Bdiv_beta_no_overflow'; auto.
 lia.
Qed.

Theorem Bdiv_mult_inverse_finite ty {STD: is_standard ty} :
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  Binary.is_finite _ _ x = true ->
  Binary.is_finite _ _ y = true ->
  Binary.is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  Bdiv _ _ _ (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y =
  Bmult _ _ _ (fprec_lt_femax ty) (mult_nan  (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z .
Proof.
  intros.
  destruct (Bexact_inverse_correct _ _ _ _ _ _ H2) as (A & B & C & D & E).
  assert (HMUL :=Binary.Bmult_correct (fprec ty)  (femax ty) 
                     (fprec_gt_0 ty) (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z).
  assert (HDIV := Binary.Bdiv_correct  (fprec ty)  (femax ty)  
                    (fprec_gt_0 ty) (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y D).
 unfold Rdiv in HDIV.
 rewrite <- C in HDIV.
 destruct Rlt_bool.
 -
  destruct HMUL as (P & Q & R). 
  destruct HDIV as (S & T & U).
  assert (Binary.is_finite  (fprec ty) (femax ty)
               (Binary.Bmult (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (mult_nan  (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z) = true) 
   by  (rewrite Q; auto;  rewrite ?andb_true_iff; auto).
  assert (Binary.is_finite (fprec ty) (femax ty)
              (Binary.Bdiv (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (div_nan  (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y) = true)
    by (rewrite T; auto).
  apply Binary.B2R_Bsign_inj; auto;
  rewrite ?S, ?R, ?U, ?E; auto; apply is_finite_not_is_nan; auto.
- 
  pose proof Binary.B2FF_inj _ _
       (Binary.Bdiv (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y)
      (Binary.Bmult (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z).
  rewrite E in HMUL.
  rewrite HMUL, HDIV in *; auto.
Qed.

Theorem Bdiv_mult_inverse_nan ty {STD: is_standard ty}:
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  Binary.is_nan _ _ x = false ->
  Binary.is_finite _ _ y = true ->
  Binary.is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  Bdiv _ _ _ (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y =
  Bmult _ _ _ (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z .
Proof.
  intros.
  destruct (Bexact_inverse_correct _ _ _ _ _ _ H2) as (A & B & C & D & E).
  assert (HMUL :=Binary.Bmult_correct (fprec ty)  (femax ty) 
                     (fprec_gt_0 ty) (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z).
  assert (HDIV := Binary.Bdiv_correct  (fprec ty)  (femax ty)  
                    (fprec_gt_0 ty) (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y D).
 unfold Rdiv in HDIV.
 rewrite <- C in HDIV.
 destruct Rlt_bool.
 -
  destruct HMUL as (P & Q & R). 
  destruct HDIV as (S & T & U).
  destruct x; simpl in H; try discriminate.
 +
 set (x:= (B754_zero (fprec ty) (femax ty) s)) in *.
 assert (Binary.is_finite  (fprec ty) (femax ty)
               (Binary.Bmult (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z) = true) 
   by  (rewrite Q; auto;  rewrite ?andb_true_iff; auto).
  assert (Binary.is_finite (fprec ty) (femax ty)
              (Binary.Bdiv (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y) = true)
    by (rewrite T; auto).
  apply Binary.B2R_Bsign_inj; auto;
  rewrite ?S, ?R, ?U, ?E; auto; apply is_finite_not_is_nan; auto.
 +
   destruct y; simpl in A; try discriminate. 
   destruct z; simpl in B; try discriminate. 
   cbv [Bdiv]; simpl; simpl in E; subst; auto.
 + apply Bdiv_mult_inverse_finite; auto.
- 
  pose proof Binary.B2FF_inj _ _
       (Binary.Bdiv (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y)
      (Binary.Bmult (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z).
  rewrite E in HMUL.
  rewrite HMUL, HDIV in *; auto.
Qed.

Theorem Bdiv_mult_inverse_equiv ty {STD: is_standard ty}:
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  Binary.is_finite _ _ y = true ->
  Binary.is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  binary_float_equiv
  (Bdiv _ _ _ (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x y) 
  (Bmult _ _ _ (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x z) .
Proof.
intros.
destruct x.
- apply binary_float_eq_equiv.
   apply Bdiv_mult_inverse_finite; auto.
- apply binary_float_eq_equiv.
   apply Bdiv_mult_inverse_nan; auto.
- destruct y; try simpl in H; try discriminate.
   destruct z; try simpl in H0; try discriminate.
 + cbv [Bdiv Bmult Binary.build_nan binary_float_equiv]. reflexivity.
 + cbv [Bdiv Bmult Binary.build_nan binary_float_equiv]. reflexivity.
- apply binary_float_eq_equiv.
   apply Bdiv_mult_inverse_finite; auto.
Qed.  

Theorem Bdiv_mult_inverse_equiv2 ty {STD: is_standard ty}:
  forall x1 x2 y z: (Binary.binary_float (fprec ty) (femax ty)),
  binary_float_equiv x1 x2 ->
  Binary.is_finite _ _ y = true ->
  Binary.is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  binary_float_equiv
  (Bdiv _ _ _ (fprec_lt_femax ty) (div_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x1 y) 
  (Bmult _ _ _ (fprec_lt_femax ty) (mult_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE x2 z) .
Proof.
intros.
assert (binary_float_equiv x1 x2) by apply H.
destruct x1; destruct x2; simpl in H; try contradiction.
-  subst; apply Bdiv_mult_inverse_equiv; auto.
-  subst; apply Bdiv_mult_inverse_equiv; auto.
-  destruct y; simpl in H0; try discriminate.
    destruct z; simpl in H1; try discriminate;
    cbv [Bdiv Bmult build_nan binary_float_equiv]; reflexivity.
- apply binary_float_finite_equiv_eqb in H3; auto.
   apply binary_float_eqb_eq in H3.
   rewrite H3. 
   apply Bdiv_mult_inverse_equiv; auto.
Qed.

Lemma is_nan_normalize:
  forall prec emax (H0: FLX.Prec_gt_0 prec) (H1 : (prec < emax)%Z)
                   mode m e s, 
  Binary.is_nan _ _ (binary_normalize prec emax H0 H1 mode m e s) = false.
Proof.
intros.
apply is_nan_BSN2B'.
Qed.

Lemma Bmult_correct_comm:
forall (prec emax : Z) (prec_gt_0_ : FLX.Prec_gt_0 prec)
         (Hmax : (prec < emax)%Z)
         (mult_nan : binary_float prec emax ->
                     binary_float prec emax -> nan_payload prec emax) 
         (m : BinarySingleNaN.mode) (x y : binary_float prec emax),
       if
        Raux.Rlt_bool
          (Rabs
             (Generic_fmt.round Zaux.radix2
                (FLT.FLT_exp (3 - emax - prec) prec) 
                (BinarySingleNaN.round_mode m)
                (B2R prec emax x * B2R prec emax y)))
          (Raux.bpow Zaux.radix2 emax)
       then
        B2R prec emax
          (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
        Generic_fmt.round Zaux.radix2
          (FLT.FLT_exp (3 - emax - prec) prec) 
          (BinarySingleNaN.round_mode m)
          (B2R prec emax x * B2R prec emax y) /\
        Binary.is_finite prec emax (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
        Binary.is_finite prec emax x && Binary.is_finite prec emax y /\
        (Binary.is_nan prec emax (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
         false ->
         Bsign prec emax (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
         xorb (Bsign prec emax x) (Bsign prec emax y))
       else
        B2FF prec emax (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
        binary_overflow prec emax m
          (xorb (Bsign prec emax x) (Bsign prec emax y))
.
Proof.
  intros.
  rewrite Rmult_comm.
  rewrite andb_comm.
  rewrite xorb_comm.
  apply Bmult_correct.
Qed.

Lemma Rabs_zero_iff x:
  Rabs x = 0 <-> x = 0.
Proof.
  split; intros; subst; auto using Rabs_R0.
  destruct (Req_dec x 0); auto.
  apply Rabs_no_R0 in H0.
  contradiction.
Qed.


Lemma B2_zero: 
  forall (ty : type) (e : Z),
  (e+1 < 3 - (femax ty))%Z -> (B2 ty e) = B754_zero (fprec ty) (femax ty) false.
Proof.
intros.
destruct (B2 ty e) eqn:?H; auto.
unfold B2, F2 in H0; 
destruct (Z_lt_le_dec (e + 1) (3 - femax ty)); [ | lia];
inversion H0; auto.
all:
exfalso;
unfold B2, F2 in H0;
destruct (Z_lt_le_dec (e + 1) (3 - femax ty)); [ | lia];
inversion H0.
Qed.

Lemma F2R_B2F:
 forall ty x, 
    Binary.is_finite (fprec ty) (femax ty) x = true ->
    F2R radix2 (B2F x) = B2R (fprec ty) (femax ty) x.
Proof.
intros.
unfold F2R, B2R.
unfold B2F.
destruct x; auto; lra.
Qed.

Lemma InvShift_finite_aux:
 forall (pow : positive) (ty : type) (x: binary_float (fprec ty) (femax ty)),
   Binary.is_finite (fprec ty) (femax ty) x = true ->
  Rabs (round radix2 (FLT_exp (3 - femax ty - fprec ty) (fprec ty)) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
     (B2R (fprec ty) (femax ty) x * / bpow radix2 (Z.pos pow))) < bpow radix2 (femax ty).
Proof.
intros.
unfold BinarySingleNaN.round_mode.
pose proof (bpow_gt_0 radix2 (Z.pos pow)).
rewrite <- round_NE_abs by (apply FLT_exp_valid; apply fprec_gt_0).
rewrite Rabs_mult, Rabs_inv by lra.
rewrite (Rabs_right (bpow _ _)) by lra.
assert (bpow radix2 (femax ty - 1) < bpow radix2 (femax ty - 1 + 1)).
rewrite bpow_plus.
simpl bpow.
pose proof (bpow_gt_0 radix2 (femax ty - 1)).
lra.
replace (femax ty - 1 + 1)%Z with (femax ty) in H1 by lia.
match goal with |- ?A < _ => assert (A <= bpow radix2 (femax ty - 1)) end;
 [ | lra].
clear H1.
apply round_le_generic.
apply FLT_exp_valid; apply fprec_gt_0.
apply valid_rnd_N.
apply generic_format_FLT_bpow.
apply fprec_gt_0.
  pose proof (fprec_lt_femax ty).
  pose proof (fprec_gt_0 ty).
  red in H2.
  lia.
assert (Rabs (B2R (fprec ty) (femax ty) x) <= bpow radix2 (femax ty)). {
  pose proof (abs_B2R_lt_emax _ _ x). lra.
}
replace (Z.pos pow) with (1 + (Z.pos pow - 1))%Z by lia.
rewrite bpow_plus.
assert (bpow radix2 0 <= bpow radix2 (Z.pos pow - 1)).
apply bpow_le. lia.
unfold bpow at 1 in H2.
change (bpow radix2 1) with 2.
set (j := bpow radix2 (Z.pos pow - 1)) in *. clearbody j.
rewrite Rinv_mult by lra.
replace (femax ty - 1)%Z with (femax ty + -(1))%Z by lia.
rewrite bpow_plus, bpow_opp.
rewrite bpow_1.
change (IZR radix2) with 2.
rewrite (Rmult_comm _ (/ j)).
rewrite <- Rmult_assoc.
set (y := Rabs _) in *.
assert (0 <= y) by apply Rabs_pos.
apply Rmult_le_compat_r.
lra.
assert (y * /j <= y * 1); [ | lra].
apply Rmult_le_compat_l; try lra.
apply Rle_Rinv in H2; lra.
Qed.

Lemma InvShift_accuracy_aux:
  forall ty x pow, 
    Binary.is_finite (fprec ty) (femax ty) x = true ->
  Rabs (round radix2 (FLT_exp (3 - femax ty - fprec ty) (fprec ty)) (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
        (B2R (fprec ty) (femax ty) x * bpow radix2 (- Z.pos pow)) -
            bpow radix2 (- Z.pos pow) * B2R (fprec ty) (femax ty) x) <=
           /2 * bpow radix2 (3 - femax ty - fprec ty).
Proof.
intros.
 destruct (Rle_lt_dec
    (bpow radix2 (3 - femax ty + Z.pos pow))
    (Rabs (B2R (fprec ty) (femax ty) x))).
-
rewrite bpow_opp.
rewrite FLT_format_div_beta_1; auto.
2: apply valid_rnd_N.
rewrite Rmult_comm.
unfold Rdiv.
rewrite Rminus_eq_0, Rabs_R0.
pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)). lra.
eapply Rle_trans. 2: apply r. apply bpow_le. lia.
-
unfold BinarySingleNaN.round_mode.
rewrite (Rmult_comm (bpow _ _)).
eapply Rle_trans.
apply (error_le_half_ulp radix2 
  (FLT_exp (3 - femax ty - fprec ty) (fprec ty)) (fun x => negb (Z.even x))
  (B2R (fprec ty) (femax ty) x * bpow radix2 (- Z.pos pow))).
unfold ulp.
set (emin := (3 - _ - _)%Z).
match goal with |- context  [Req_bool ?A ?B] =>
  set (a := A)
end.
pose proof (Req_bool_spec a 0).
destruct H0. 
+
subst a.
destruct (negligible_exp_FLT emin (fprec ty)) as [z [? ?]].
rewrite H1.
unfold FLT_exp.
pose proof (fprec_gt_0 ty). red in H3.
rewrite Z.max_r by lia.
lra.
+
rewrite <- ulp_neq_0 by auto.
rewrite ulp_FLT_small.
lra.
apply fprec_gt_0.
subst a.
unfold emin.
rewrite bpow_opp.
replace (bpow radix2 (3 - femax ty + Z.pos pow)) with
(bpow radix2 (3 - femax ty - fprec ty + fprec ty) * bpow radix2 (Z.pos pow) ) in r.

assert (HltA: Rlt (IZR Z0) (bpow radix2 (Zpos pow))).
{pose proof bpow_gt_0 radix2  (( Zpos pow)); auto.
}
assert (HnotA: not (@eq R (bpow radix2 (Zpos pow)) (IZR Z0))).
{
apply Rabs_lt_pos; auto.
repeat rewrite Rabs_pos_eq; try apply bpow_ge_0; try nra.
}
match goal with |- context [Rabs ?A ] => 
field_simplify A; try nra
end.
apply Rdiv_lt_left in r; try nra.
rewrite <- Rabs_div_eq in r; try nra.
rewrite <- bpow_plus.
match goal with |-context [ bpow _ ?b = bpow _ ?a] =>
ring_simplify a; ring_simplify b; nra
end; symmetry;
match goal with |-context [_ = bpow _ ?a] =>
ring_simplify a
end.
Qed.

End WITHNANS.
