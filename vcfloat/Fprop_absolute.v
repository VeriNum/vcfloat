(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(** More properties of floating-point numbers: absolute error, multiply/divide by radix. *)

From Coq Require Import ZArith.
Require Import Flocq.Core.Raux. 
From Coq Require Import Reals Lia Lra.

Require Import Flocq.Prop.Relative.
(*Require Import Flocq.Appli.Fappli_IEEE. *)

Open Scope R_scope.

Section I3E.
Variables prec emin : Z.
Context (prec_gt_0_ : Core.FLX.Prec_gt_0 prec).

Let fexp := Core.FLT.FLT_exp emin prec.

Import Core.FLT Generic_fmt Core.Ulp.

Lemma absolute_error_N_FLT_aux beta choice :
  forall x,
  (0 < x)%R ->
  x < bpow beta (emin + prec) ->
 exists eta,
  (Rabs eta <= /2 * Raux.bpow beta (emin))%R /\
  Generic_fmt.round beta fexp (Generic_fmt.Znearest choice) x = (x + eta)%R.
Proof.
(* from error_N_FLT_aux *)
intros x Hx2 Hx.
exists (round beta (FLT_exp emin prec) (Znearest choice) x - x)%R.
split.
apply Rle_trans with (/2*ulp beta (FLT_exp emin prec) x)%R.
apply error_le_half_ulp.
now apply FLT_exp_valid.
apply Rmult_le_compat_l; auto with real.
rewrite ulp_neq_0 by lra.
apply bpow_le.
unfold FLT_exp, cexp.
rewrite Zmax_right.
lia.
destruct (mag beta x) as (e,He); simpl.
assert (e-1 < emin+prec)%Z.
apply (lt_bpow beta).
apply Rle_lt_trans with (2:=Hx).
rewrite <- (Rabs_right x).
apply He; auto with real.
apply Rle_ge; now left.
lia.
unfold fexp. ring.
Qed.

Import Morphisms.

Global Instance Znearest_proper: Proper ((eq ==> eq) ==> eq ==> eq) Znearest.
Proof.
  do 3 red.
  intros a b Hab u v Huv.
  subst.
  unfold Znearest.
  destruct (Rcompare (v - IZR (Raux.Zfloor v)) (/ 2)); auto.
  replace (b (Raux.Zfloor v)) with (a (Raux.Zfloor v)) by auto.
  reflexivity.
Qed.

Corollary absolute_error_N_FLT beta choice:
 forall x,
  Rabs x < bpow beta (emin + prec) ->
 exists eta,
  (Rabs eta <= /2 * Raux.bpow beta (emin))%R /\
  Generic_fmt.round beta fexp (Generic_fmt.Znearest choice) x = (x + eta)%R.
Proof.
  intros.
  destruct (Req_dec x 0).
  {
    subst.
    rewrite round_0; try typeclasses eauto.
    exists 0.
    split; try ring.
    rewrite Rabs_R0.
    generalize (bpow_ge_0 beta emin); lra.
  }
  destruct (Rle_dec x 0).
  {
    rewrite Rabs_left in H by lra.
    assert (0 < - x) by lra.
    destruct (absolute_error_N_FLT_aux _ (fun t => negb (choice (- (t + 1))%Z)) _ H1 H) as (eta & Heta & EQ).
    rewrite round_N_opp in EQ.
    apply (f_equal Ropp) in EQ.
    rewrite Ropp_involutive in EQ.
    exists (- eta).
    split.
    {
      rewrite Rabs_Ropp.
      assumption.
    }
    refine (eq_trans _ (eq_trans EQ _)).
    {
      apply round_ext.
      intros.
      apply Znearest_proper; auto.
      red. intros; subst.
      rewrite Bool.negb_involutive.
      f_equal.
      ring.
    }
    ring.
  }
  rewrite Rabs_right in H by lra.
  eapply absolute_error_N_FLT_aux; eauto.
  lra.
Qed.

End I3E.

Lemma FLT_format_mult_beta beta emin prec x:
  FLT.FLT_format beta emin prec x ->
  FLT.FLT_format beta emin prec (IZR (Zaux.radix_val beta) * x)
.
Proof.
  intros [f Hx mantissa exponent].
  subst.
  exists (Defs.Float _ (Defs.Fnum f) (Defs.Fexp f + 1)).
  simpl.
  unfold Defs.F2R.
  simpl.
  rewrite Core.Raux.bpow_plus_1.
  ring. auto. simpl. lia.
Qed.

Lemma FLT_format_div_beta beta emin prec
      (Hprec: (0 <= prec)%Z) x:
  FLT.FLT_format beta emin prec x ->
  Core.Raux.bpow beta (emin + prec) <= Rabs x ->
  FLT.FLT_format beta emin prec (x / IZR (Zaux.radix_val beta))
.
Proof.
  intros [f Hx mantissa exponent].
  subst.
  exists (Defs.Float _ (Defs.Fnum f) (Defs.Fexp f - 1)); auto.
 -
  unfold Defs.F2R.
  simpl.
  replace (Defs.Fexp f) with (Defs.Fexp f - 1 + 1)%Z at 1 by ring.
  rewrite bpow_plus_1.
  field.
  apply eq_IZR_contrapositive.
  generalize (Zaux.radix_gt_0 beta). lia.
 -
  simpl.
  destruct (Z.eq_dec emin (Defs.Fexp f)); try lia.
  exfalso.
  clear exponent.
  subst.
  revert H.
  unfold Defs.F2R.
  rewrite Rabs_mult.
  rewrite bpow_plus.
  rewrite (Rmult_comm (Raux.bpow _ _)).
  generalize (Raux.bpow_gt_0 beta (Defs.Fexp f)).
  intro.
  rewrite (Rabs_right (Raux.bpow _ _)) by lra.
  intro K.
  apply Rmult_le_reg_r in K; auto.
  rewrite <- Raux.IZR_Zpower in K by assumption.
  repeat rewrite IZR_IZR in K.
  rewrite Rabs_Zabs in K.
  apply le_IZR in K.
  lia.
Qed.
