(** VCFloat: A Unified Coq Framework for Verifying C Programs with
 Floating-Point Computations. Application to SAR Backprojection.
 
 Version 1.0 (2015-12-04)
 
 Copyright (C) 2015 Reservoir Labs Inc.
 All rights reserved.
 
 This file, which is part of VCFloat, is free software. You can
 redistribute it and/or modify it under the terms of the GNU General
 Public License as published by the Free Software Foundation, either
 version 3 of the License (GNU GPL v3), or (at your option) any later
 version. A verbatim copy of the GNU GPL v3 is included in gpl-3.0.txt.
 
 This file is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE for
 more details about the use and redistribution of this file and the
 whole VCFloat library.
 
 This work is sponsored in part by DARPA MTO as part of the Power
 Efficiency Revolution for Embedded Computing Technologies (PERFECT)
 program (issued by DARPA/CMO under Contract No: HR0011-12-C-0123). The
 views and conclusions contained in this work are those of the authors
 and should not be interpreted as representing the official policies,
 either expressly or implied, of the DARPA or the
 U.S. Government. Distribution Statement "A" (Approved for Public
 Release, Distribution Unlimited.)
 
 
 If you are using or modifying VCFloat in your work, please consider
 citing the following paper:
 
 Tahina Ramananandro, Paul Mountcastle, Benoit Meister and Richard
 Lethin.
 A Unified Coq Framework for Verifying C Programs with Floating-Point
 Computations.
 In CPP (5th ACM/SIGPLAN conference on Certified Programs and Proofs)
 2016.
 
 
 VCFloat requires third-party libraries listed in ACKS along with their
 copyright information.
 
 VCFloat depends on third-party libraries listed in ACKS along with
 their copyright and licensing information.
*)
(**
Author: Tahina Ramananandro <ramananandro@reservoir.com>

Accumulation of rounding errors for naive summation.

For more technical information, you can read Section 5.4 of our paper
published at ACM/SIGPLAN Certified Programs and Proofs (CPP) 2016:

Tahina Ramananandro, Paul Mountcastle, Benoit Meister and Richard
Lethin.
A Unified Coq Framework for Verifying C Programs with Floating-Point
Computations

*)

Require Import Arith ZArith Reals Psatz Morphisms.
Open Scope R_scope.

Class Sum (Sf: (nat -> R) -> nat -> R): Prop :=
  {
    SfO: forall f, Sf f O = 0;
    SfS: forall f n, Sf f (S n) = Sf f n + f n
  }.

Section S.

Context `{SUM: Sum}.

Lemma Sf_ext: forall n f1 f2,
  (forall i, (i < n)%nat -> f1 i = f2 i) ->
  Sf f1 n = Sf f2 n.
Proof.
  induction n; intros; simpl.
  {
    repeat rewrite SfO. reflexivity.
  }
  repeat rewrite SfS.
  f_equal; auto.
Qed.

Lemma Sf_left n:
  forall f,
    Sf f (S n) = f O + Sf (fun i => f (S i)) n.
Proof.
  induction n; intros.
  {
    rewrite SfS.
    repeat rewrite SfO.
    ring.
  }
  rewrite SfS.
  rewrite IHn.
  rewrite Rplus_assoc.
  f_equal.
  rewrite SfS.
  reflexivity.
Qed.

Lemma Sf_inv n:
  forall f,
    Sf f n = Sf (fun i => f (n - S i)%nat) n.
Proof.
  induction n; intros.
  {
    repeat rewrite SfO.
    reflexivity.
  }
  rewrite Sf_left.
  rewrite SfS.
  rewrite Rplus_comm.
  f_equal.
  {
    rewrite IHn.
    apply Sf_ext.
    intros.
    f_equal.
    lia.
  }
  f_equal.
  lia.
Qed.

Lemma Sf_scal x f n:
  Sf f n * x = Sf (fun i => x * f i) n.
Proof.
  induction n.
  {
    repeat rewrite SfO.
    ring.
  }
  repeat rewrite SfS.
  rewrite Rmult_plus_distr_r.
  rewrite IHn.
  ring.
Qed.

Definition sumOfPowers x := Sf (pow x).
Definition sumOfPowersO x: sumOfPowers x O = 0 := SfO _.
Definition sumOfPowersS x n: sumOfPowers x (S n) = sumOfPowers x n + x ^ n := SfS _ _.

Section U.

Variable x: R.
Local Notation u := (sumOfPowers x).
Let uO: u O = 0 := sumOfPowersO _.
Let uS n: u (S n) = u n + x ^ n := sumOfPowersS _ _.

Hypothesis x_ne_1: x <> 1.

Lemma u_eq n: u n = (1 - x ^ n) / (1 - x).
Proof.
  induction n.
  {
    rewrite uO.
    simpl.
    unfold Rdiv.
    ring.
  }
  rewrite uS.
  rewrite IHn.
  simpl.
  field.
  lra.
Qed.

Lemma u_x n:
  u n * x = u (S n) - 1.
Proof.
  unfold u. rewrite Sf_left. simpl.
  match goal with
  |- _ = ?z => match z with
    1 + ?y - 1 => replace z with y by ring
  end end.
  apply Sf_scal.
Qed.

End U.

Definition sumOfIPowers x := Sf (fun i => INR (S i) * pow x i).
Definition sumOfIPowersO x: sumOfIPowers x O = 0 := SfO _.
Definition sumOfIPowersS x n: sumOfIPowers x (S n) = sumOfIPowers x n + INR (S n) * x ^ n := SfS _ _.

Section SUMDERIV.

Variable x: R.
Local Notation v := (sumOfIPowers x).
Let v0: v O = 0 := sumOfIPowersO _.
Let vS n: v (S n) = v n + INR (S n) * pow x n := sumOfIPowersS _ _.

Hypothesis x_ne_1: x <> 1.

Lemma v_eq n:
  v n = (INR n * x ^ (S n) - INR (S n) * x ^ n + 1) / (1 - x) ^ 2.
Proof.
  induction n.
  {
    rewrite v0.
    simpl.
    field.
    lra.
  }
  rewrite vS.
  rewrite IHn.
  repeat rewrite S_INR.
  simpl.
  field.
  lra.
Qed.

End SUMDERIV.

Class prop (K L M: R) (D: nat -> R): Prop :=
  {
    DO: D O = 0;
    DS: forall n, D (S n) = D n * M + INR n * L + K
  }.

Context {D_} {PROP: forall K L M, prop K L M (D_ K L M)}.

Section S.

Context (K L M: R).

Local Notation D := (D_ K L M).

Section WITH_M_hyp.

Hypothesis M_neq_0: M <> 0.

Lemma D_eq_aux' n:
  D (S (S n)) = K * sumOfPowers M (S (S n)) + L * M ^ n * sumOfIPowers (/ M) (S n).
Proof.
  induction n.
  {
    repeat rewrite DS.
    rewrite DO.
    repeat rewrite sumOfPowersS.
    rewrite sumOfPowersO.
    repeat rewrite sumOfIPowersS.
    rewrite sumOfIPowersO.
    simpl.
    ring.
  }
  rewrite DS.
  rewrite IHn; clear IHn.
  repeat rewrite sumOfPowersS.
  repeat rewrite sumOfIPowersS.
  repeat rewrite S_INR.
  simpl.
  rewrite <- Rinv_pow by assumption.
  ring_simplify.
  rewrite Rmult_assoc.
  rewrite u_x.
  rewrite sumOfPowersS.
  field.
  split; auto.
  apply pow_nonzero.
  assumption.
Qed.

Hypothesis M_neq_1: M <> 1.

Let InvM_neq_1: / M <> 1.
Proof.
  intro ABS.
  generalize (f_equal Rinv ABS).
  rewrite Rinv_involutive by assumption.
  rewrite Rinv_1.
  assumption.
Qed.

Lemma tech_invert_square u:
  u / (1 - / M) ^ 2 = u * M ^ 2 / (1 - M) ^ 2.
Proof.
  field.
  lra.
Qed.

Lemma tech1 n: D (S (S n)) = K * ((1 - M ^ S (S n)) / (1 - M)) + L * (INR (S n) - INR (S (S n)) * M + M ^ S (S n)) / (1 - M) ^ 2.
rewrite D_eq_aux'.
rewrite u_eq by assumption.
rewrite v_eq by assumption.
f_equal.
rewrite tech_invert_square.
unfold Rdiv.
rewrite Rmult_assoc.
symmetry.
rewrite Rmult_assoc.
f_equal.
rewrite <- Rmult_assoc.
f_equal.
symmetry.
replace (S (S n)) with (n + 2)%nat at 1 4 by lia.
repeat rewrite pow_add.
rewrite <- (tech_pow_Rmult (/ M) n).
repeat rewrite <- Rinv_pow by assumption.
field.
split; auto.
apply pow_nonzero.
assumption.
Qed.

Lemma tech2 n:
  D (S (S n)) = K * ((1 - M ^ S (S n)) / (1 - M)) + L * (INR (S (S n)) - 1 - INR (S (S n)) * M + M ^ S (S n)) / (1 - M) ^ 2.
Proof.
  rewrite tech1.
  repeat rewrite S_INR.
  field.
  lra.
Qed.

Lemma tech3 n:
 D n = K * ((1 - M ^ n) / (1 - M)) + L * (INR n * (1 - M) - 1 + M ^ n) / (1 - M) ^ 2.
Proof.
  destruct n.
  {
    rewrite DO.
    simpl.
    unfold Rdiv.
    ring.
  }
  destruct n.
  {
    rewrite DS.
    rewrite DO.
    simpl.
    field.
    lra.
  }
  rewrite tech2.
  field.
  lra.
Qed.

Definition E n := (1 - M ^ n) / (1 - M) * (K - L / (1 - M)) + L * INR n / (1 - M).

Theorem D_eq_aux n:
 D n = E n.
Proof.
  unfold E.
  rewrite tech3.
  field.
  lra.
Qed.

End WITH_M_hyp.

Theorem D_eq:
  M <> 1 ->
  forall n,
    D n = E n.
Proof.
  intros HM n.
  destruct (Req_dec M 0) as [EQ | ].
  {
    unfold E.
    rewrite EQ.
    destruct n.
    {
      simpl.
      rewrite DO.
      field.
    }
    rewrite DS.
    rewrite S_INR.
    simpl.
    field.
  }
  apply D_eq_aux; auto.
Qed.

End S.

Lemma ub f M:
  (forall n, f n <= M) ->
  forall n, Sf f n <= INR n * M.
Proof.
  induction n.
  {
    rewrite SfO. simpl. apply Req_le. ring.
  }
  rewrite SfS. rewrite S_INR.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  apply Rplus_le_compat; auto.
Qed.

Lemma ub_abs f M:
  (forall n, Rabs (f n) <= M) ->
  forall n, Rabs (Sf f n) <= INR n * M.
Proof.
  induction n.
  {
    rewrite SfO. simpl. rewrite Rabs_R0.
    apply Req_le. lra.
  }
  rewrite SfS. rewrite S_INR.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  eapply Rle_trans.
  {
    apply Rabs_triang.
  }
  apply Rplus_le_compat; auto.
Qed.

(* Total error of a rounded sum of approximate terms *)

Theorem error_rounded_sum_with_approx Q q Q_ q_ d e Mq Mdq Md Me n:
  Rabs q <= Mq ->
  Rabs d <= Md ->
  Rabs e <= Me ->
  Rabs (q_ - q) <= Mdq ->
  Rabs Q <= INR n * Mq ->
  let M := 1 + Md in
  let L := (Mq * Md) in
  let K := (Mq * Md + Mdq * (1 + Md) + Me) in
  Rabs (Q_ - Q) <= D_ K L M n ->
  Rabs ((Q_ + q_) * (1 + d) + e - (Q + q)) <= D_ K L M (S n). 
Proof.
  intros H H0 H1 H2 H3 M L K H4.
  pose (dq := q_ - q).
  assert 
    ((Q_ + q_) * (1 + d) + e - (Q + q)
     = (Q_ - Q) * (1 + d) + Q * d + (q * d + dq * (1 + d) + e))
    as V_m_U.
  {
    unfold dq.
    ring.
  }
  assert 
  (Rabs ((Q_ + q_) * (1 + d) + e - (Q + q)) <= Rabs (Q_ - Q) * M + INR n * L + K)
  as V_m_U_le.
  {
    unfold K, L, M.
    rewrite V_m_U.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    apply Rplus_le_compat.
    {
      eapply Rle_trans.
      {
        apply Rabs_triang.
      }
      apply Rplus_le_compat.
      {
        rewrite Rabs_mult.
        apply Rmult_le_compat_l; auto using Rabs_pos.
        eapply Rle_trans.
        {
          apply Rabs_triang.
        }
        rewrite Rabs_R1.
        apply Rplus_le_compat_l; auto.
      }
      rewrite Rabs_mult.
      rewrite <- Rmult_assoc.
      apply Rmult_le_compat; auto using Rabs_pos.
    }
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    apply Rplus_le_compat; auto.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    apply Rplus_le_compat.
    {
      rewrite Rabs_mult.
      apply Rmult_le_compat; auto using Rabs_pos.
    }
    rewrite Rabs_mult.
    apply Rmult_le_compat; auto using Rabs_pos.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    rewrite Rabs_R1.
    apply Rplus_le_compat_l; auto.
  }
  eapply Rle_trans.
  {
    apply V_m_U_le.
  }
  rewrite DS.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_r; auto.
  unfold M.
  generalize (Rabs_pos (d)).
  lra.
Qed.

(* Range of a sum with rounding errors. (We assume that we already know the range of each computed term of the sum.) *)

Lemma next_rounded_sum_range Q n q d e Mq Md Me:
  Rabs q <= Mq ->
  Rabs d <= Md ->
  Rabs e <= Me ->
  let M := 1 + Md in
  let K' := (Mq * (1 + Md) + Me) in
  Rabs Q <=  D_ K' 0 M (n) ->
  Rabs ((Q + q) * (1 + d) + e) <= D_ K' 0 (M) (S n).
Proof.
  intros H H0 H1 M K' H2.
  assert (Rabs ((Q + q) * (1 + d) + e) <= Rabs Q * M + INR n * 0 + K') as H3.
  {
    replace ((Q + q) * (1 + d) + e) with
    (Q * (1 + d) + INR n * 0 + (q * (1 + d) + e))
      by ring.
    unfold K', M.
    rewrite Rmult_0_r.
    repeat rewrite Rplus_0_r.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    apply Rplus_le_compat.
    {
      rewrite Rabs_mult.
      apply Rmult_le_compat_l; auto using Rabs_pos.
      eapply Rle_trans.
      {
        apply Rabs_triang.
      }
      rewrite Rabs_R1.
      apply Rplus_le_compat_l; auto.
    }
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    apply Rplus_le_compat; auto.
    rewrite Rabs_mult.
    apply Rmult_le_compat; auto using Rabs_pos.
    eapply Rle_trans.
    {
      apply Rabs_triang.
    }
    rewrite Rabs_R1.
    apply Rplus_le_compat_l; auto.
  }
  eapply Rle_trans.
  {
    apply H3.
  }
  rewrite DS.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_r; auto.   
  unfold M.
  generalize (Rabs_pos d).
  lra.
Qed.

End S.

(* Implementations *)
 
Fixpoint Sf (f: nat -> R) (n: nat): R :=
  match n with
  | O => 0
  | S n' => Sf f n' + f n'
  end.

Global Instance: Sum Sf.
Proof.
  split; reflexivity.
Qed.

Fixpoint D (K L M: R) (n: nat): R :=
  match n with
  | O => 0
  | S n' => D K L M n' * M + INR n' * L + K
  end.

Global Instance: forall K L M, prop K L M (D K L M).
Proof.
  split; reflexivity.
Qed.
