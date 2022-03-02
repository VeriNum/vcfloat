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

VCFloat: core and annotated languages for floating-point operations.
*)

Require Import Interval.Tactic.
From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
From compcert Require Import lib.IEEE754_extra lib.Floats.
Require compcert.lib.Maps.  
Require Coq.MSets.MSetAVL.
Require vcfloat.Fprop_absolute.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Require Export vcfloat.FPCore.
Import Bool.

Global Existing Instance fprec_gt_0. (* to override the Opaque one in Interval package *)

Module MSET := MSetAVL.Make(Nat).

Inductive rounded_binop: Type :=
| PLUS
| MINUS
| MULT
| DIV
.

Inductive rounding_knowledge: Type :=
| Normal
| Denormal
.

Inductive binop: Type :=
| Rounded2 (op: rounded_binop) (knowl: option rounding_knowledge)
| SterbenzMinus
| PlusZero (minus: bool) (zero_left: bool) (* use only if one of the two arguments can be shown to be zero *)
.

Inductive rounded_unop: Type :=
| SQRT
.

Inductive exact_unop: Type :=
| Abs
| Opp
| Shift (pow: N) (ltr: bool) (* multiply by power of two never introduces rounding *)
| InvShift (pow: positive) (ltr: bool) (* divide by power of two may introduce gradual underflow *)
.

Inductive unop: Type :=
| Rounded1 (op: rounded_unop) (knowl:  option rounding_knowledge)
| Exact1 (o: exact_unop)
| CastTo (ty: type) (knowl: option rounding_knowledge)
| uInvShift (pow: positive) (ltr: bool) (* divide by power of two that may introduce underflow *)
.

Class VarType (V: Type): Type := 
  {
    var_eqb: V -> V -> bool;
    var_eqb_eq: forall v1 v2, var_eqb v1 v2 = true <-> v1 = v2
  }.


Inductive rounding_knowledge': Type :=
| Unknown'
| Normal'
| Denormal'
| Denormal2' (* specially for uInvShift *)
.

Definition round_knowl_denote (r: option rounding_knowledge) :=
 match r with
 | None => Unknown'
 | Some Normal => Normal'
 | Some Denormal => Denormal'
 end.

Section WITHVAR.

Context `{VAR: VarType}.

Inductive expr: Type :=
| Const (ty: type) (f: ftype ty)
| Var (ty: type) (i: V)
| Binop (b: binop) (e1 e2: expr)
| Unop (u: unop) (e1: expr)
.

Definition Rop_of_rounded_binop (r: rounded_binop): R -> R -> R :=
  match r with
    | PLUS => Rplus
    | MINUS => Rminus
    | MULT => Rmult
    | DIV => Rdiv
  end.

Definition Rop_of_binop (r: binop): R -> R -> R :=
  match r with
    | Rounded2 op _ => Rop_of_rounded_binop op
    | SterbenzMinus => Rminus
    | PlusZero minus zero_left =>
      if zero_left then
        fun _ => if minus then Ropp else (fun x => x)
      else
        fun x _ => x
  end.

Definition Rop_of_rounded_unop (r: rounded_unop): R -> R :=
  match r with
    | SQRT => R_sqrt.sqrt
  end.

Definition Rop_of_exact_unop (r: exact_unop): R -> R :=
  match r with
    | Abs => Rabs
    | Opp => Ropp
    | Shift pow b =>
      Rmult (Raux.bpow Zaux.radix2 (Z.of_N pow))
    | InvShift pow _ => Rmult (Raux.bpow Zaux.radix2 (- Z.pos pow))
  end.

Definition Rop_of_unop (r: unop): R -> R :=
  match r with
    | Rounded1 op _ => Rop_of_rounded_unop op
    | Exact1 op => Rop_of_exact_unop op
    | CastTo _ _ => id
    | uInvShift pow _ => Rmult (Raux.bpow Zaux.radix2 (- Z.pos pow))
  end.

Fixpoint rval (env: forall ty, V -> ftype ty) (e: expr) {struct e}: R :=
  match e with
    | Const ty f => B2R (fprec ty) (femax ty) f
    | Var ty i => B2R (fprec ty) (femax ty) (env ty i)
    | Binop b e1 e2 =>
      Rop_of_binop b (rval env e1) (rval env e2)
    | Unop b e =>
      Rop_of_unop b (rval env e)
  end.

Context {NANS: Nans}.

Definition type_of_unop (u: unop): type -> type :=
  match u with
    | CastTo ty _ => fun _ => ty
    | _ => Datatypes.id
  end.

Fixpoint type_of_expr (e: expr) {struct e}: type :=
  match e with
    | Const ty _ => ty
    | Var ty _ => ty
    | Binop b e1 e2 => type_lub (type_of_expr e1) (type_of_expr e2)
    | Unop b e => type_of_unop b (type_of_expr e)
  end.

Local Open Scope R_scope.

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

Definition unop_valid ty (u: unop): bool :=
  match u with
    | Exact1 (Shift p _) => 
      Z.leb 0 (center_Z (3 - femax ty) (Z.of_N p + 1) (femax ty))
    | Exact1 (InvShift p _) =>
      Z.leb 0 (center_Z (3 - (femax ty)) (- Z.pos p + 1) (femax ty))
    | _ => true
  end.

Fixpoint expr_valid (e: expr): bool :=
  match e with
    | Const _ f => is_finite _ _ f
    | Binop _ e1 e2 => andb (expr_valid e1) (expr_valid e2)
    | Unop u e => unop_valid (type_of_expr e) u && expr_valid e
    | _ => true
  end.

Definition rounded_binop_precond (r: rounded_binop):
  R -> R -> Prop :=
  match r with
    | DIV => fun _ y => y <> 0
    | _ => fun _ _ => True
  end.

Definition fop_of_rounded_binop (r: rounded_binop): 
  forall ty,
    binary_float (fprec ty) (femax ty) ->
    binary_float (fprec ty) (femax ty) ->
    binary_float (fprec ty) (femax ty)
  :=
    match r with
      | PLUS => BPLUS
      | MINUS => BMINUS
      | MULT => BMULT
      | DIV => BDIV
    end.

Definition fop_of_binop (r: binop):
  forall ty,
    binary_float (fprec ty) (femax ty) ->
    binary_float (fprec ty) (femax ty) ->
    binary_float (fprec ty) (femax ty)
  :=
    match r with
      | Rounded2 r _ => fop_of_rounded_binop r
      | SterbenzMinus => BMINUS
      | PlusZero minus zero_left => if minus then BMINUS else BPLUS
    end.

Definition Bsqrt ty := Bsqrt _ _ (fprec_gt_0 ty) (fprec_lt_femax ty) (sqrt_nan ty) mode_NE.

Definition rounded_unop_precond (r: rounded_unop):
  R -> Prop :=
  match r with
    | SQRT => Rle 0
  end.

Definition fop_of_rounded_unop (r: rounded_unop):
  forall ty,
    binary_float (fprec ty) (femax ty) ->
    binary_float (fprec ty) (femax ty)
  :=
    match r with
      | SQRT => Bsqrt
    end.

Inductive FF2B_gen_spec (prec emax: Z) (x: full_float): binary_float prec emax -> Prop :=
  | FF2B_gen_spec_invalid (Hx: valid_binary prec emax x = false):
      FF2B_gen_spec prec emax x (B754_infinity _ _ (sign_FF x))
  | FF2B_gen_spec_valid (Hx: valid_binary prec emax x = true)
                        y (Hy: y = FF2B _ _ _ Hx):
      FF2B_gen_spec _ _ x y
.

Lemma FF2B_gen_spec_unique prec emax x y1:
  FF2B_gen_spec prec emax x y1 ->
  forall y2,
    FF2B_gen_spec prec emax x y2 ->
    y1 = y2.
Proof.
  inversion 1; subst;
  inversion 1; subst; try congruence.
  f_equal.
  apply Eqdep_dec.eq_proofs_unicity.
  generalize bool_dec. clear. firstorder.
Qed.

Definition FF2B_gen prec emax x :=
  match valid_binary prec emax x as y return valid_binary prec emax x = y -> _ with
    | true => fun Hx => FF2B _ _ _ Hx
    | false => fun _ => B754_infinity _ _ (sign_FF x)
  end eq_refl.

Lemma bool_true_elim {T} a  (f: _ -> T) g H:
  match a as a' return a = a' -> _ with
    | true => f
    | false => g
  end eq_refl = f H.
Proof.
  destruct a; try congruence.
  f_equal.
  apply Eqdep_dec.eq_proofs_unicity.
  decide equality.
Qed.

Lemma FF2B_gen_correct prec emax x (Hx: valid_binary prec emax x = true):
  FF2B_gen _ _ x = FF2B _ _ _ Hx.
Proof.  
  apply bool_true_elim.
Qed.

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
      symmetry.
      rewrite  Z.max_l.
      {
        rewrite Pos2Z.inj_pred by assumption.
        lia.
      }
      lia.
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
Definition B2_opp ty e := BOPP ty (B2 ty e).

Lemma B2_finite ty e:
  (e + 1 <= femax ty)%Z ->
  is_finite _ _ (B2 ty e) = true.
Proof.
  unfold B2.
  intros.
  rewrite (FF2B_gen_correct _ _ _ (F2_valid_binary _ _ H)).
  set (j := F2_valid_binary _ _ _). clearbody j. revert j.
  destruct (F2 _ _ _) eqn:?H; intros; auto;
  elimtype False; clear - H0; unfold F2 in H0;
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

Definition fop_of_exact_unop (r: exact_unop)
  := 
    match r with
      | Abs => BABS
      | Opp => BOPP
      | Shift n b =>
        if b
        then
          (fun ty x => BMULT ty x (B2 ty (Z.of_N n)))
        else
          (fun ty => BMULT ty (B2 ty (Z.of_N n)))
      | InvShift n b => 
        if b
        then
          (fun ty x => BMULT ty x (B2 ty (- Z.pos n)))
        else
          (fun ty => BMULT ty (B2 ty (- Z.pos n)))
    end.

Definition fop_of_unop (r: unop):
  forall ty,
    binary_float (fprec ty) (femax ty) ->
    let ty' := type_of_unop r ty in
    binary_float (fprec ty') (femax ty')
  :=
    match r as r' return 
  forall ty,
    binary_float (fprec ty) (femax ty) ->
    let ty' := type_of_unop r' ty in
    binary_float (fprec ty') (femax ty')
    with
      | Rounded1 o _ => fop_of_rounded_unop o
      | Exact1 o => fop_of_exact_unop o
      | CastTo tto _ => cast tto
      | uInvShift n b => 
        if b
        then
          (fun ty x => BMULT ty x (B2 ty (- Z.pos n)))
        else
          (fun ty => BMULT ty (B2 ty (- Z.pos n)))

    end.

Fixpoint fval (env: forall ty, V -> ftype ty) (e: expr) {struct e}:
  ftype (type_of_expr e) :=

           match e as e' return
                 ftype (type_of_expr e') with
             | Const ty f => f
             | Var ty i => env ty i
             | Binop b e1 e2 =>
               fop_of_binop b _ (cast_lub_l _ _ (fval env e1)) (cast_lub_r _ _ (fval env e2))
             | Unop b e =>
               fop_of_unop b _ (fval env e)
           end.

Class Map (T U M: Type): Type :=
  {
    mget: M -> T -> U;
    mset: M -> T -> U -> M;
    mempty: U -> M;
    mget_set: forall m_T_eq_dec: forall t1 t2: T, {t1 = t2} + {t1 <> t2}, forall
                     m t t' u,
                mget (mset m t u) t' = if m_T_eq_dec t' t then u else mget m t';
    mget_empty: forall t u, mget (mempty u) t = u
  }.

Lemma finite_errors_ex {T M} {MAP: Map nat T M}  (t: T) n:
  forall errors,
  exists m,
    forall i,
      mget m i = if Nat.ltb i n then errors i else t.
Proof.
  induction n; intros.
  {
    exists (mempty t).
    intros.
    rewrite mget_empty.
    reflexivity.
  }
  specialize (IHn errors).
  destruct IHn.
  exists (mset x n (errors n)).
  intros.
  rewrite (mget_set Nat.eq_dec).
  destruct (Nat.eq_dec i n).
  {
    subst.
    rewrite (fun n m => let (_, J) := Nat.ltb_lt n m in J); auto with arith.
  }
  rewrite H.
  replace (Nat.ltb i n) with (Nat.ltb i (S n)); auto.
  rewrite Bool.eq_iff_eq_true.
  repeat rewrite Nat.ltb_lt.
  intuition lia.
Qed.  

Section COMPCERTMAPS.

Class MapIndex (T: Type): Type :=
  {
    index_of_tr: T -> positive;
    index_of_tr_correct:
      forall tr1 tr2,
        (tr1 = tr2) <-> (index_of_tr tr1 = index_of_tr tr2)
  }.

Local Program Instance compcert_map:
  forall T U, MapIndex T -> Map T U (Maps.PMap.t U) :=
  {
    mget m t := Maps.PMap.get (index_of_tr t) m;
    mset m t u := Maps.PMap.set (index_of_tr t) u m;
    mempty := @Maps.PMap.init _
  }.
Solve Obligations with (intros; try apply Maps.PMap.gi). 
   (* Need this line for compatibility with CompCert 3.9 and before and/or Coq 8.13 and before *)
Next Obligation.
    rewrite Maps.PMap.gsspec.
    destruct (Coqlib.peq (index_of_tr t') (index_of_tr t)).
    {
      rewrite <- index_of_tr_correct in e.
      destruct (m_T_eq_dec t' t); congruence.
    }
    rewrite <- index_of_tr_correct in n.
    destruct (m_T_eq_dec t' t); congruence.
Defined.

End COMPCERTMAPS.

Section I_OF_TR.

Lemma some_eq {U} (u1 u2: U):
  (u1 = u2 <-> Some u1 = Some u2).
Proof.
  intuition congruence.
Qed.

Local Program Instance index_of_option T:
  MapIndex T ->
  MapIndex (option T) :=
  {
    index_of_tr := fun o =>
      match o with
        | None => xH
        | Some t => xI (index_of_tr t)
      end
  }.
Next Obligation.
  destruct tr1; destruct tr2; try intuition congruence.
  generalize (index_of_tr_correct t t0).
  rewrite <- some_eq.
  intro K.
  rewrite K.
  intuition congruence.
Defined.

Fixpoint inj_pair_aux (a: positive) (b: positive) {struct a}: positive :=
  match a with
    | xH => b
    | xI a' => inj_pair_aux a' (xO (xI b))
    | xO a' => inj_pair_aux a' (xO (xO b))
  end.

Fixpoint inj_pair_rev_r (b: positive): option positive :=
  match b with
    | xI b' => Some b'
    | xO (xI b') => inj_pair_rev_r b'
    | xO (xO b') => inj_pair_rev_r b'
    | _ => None
  end.

Lemma inj_pair_aux_right_correct a1:
  forall a2 b1 b2,
    inj_pair_aux a1 b1 = inj_pair_aux a2 b2 ->
    forall c1 c2,
    inj_pair_rev_r b1 = Some c1 ->
    inj_pair_rev_r b2 = Some c2 ->
    c1 = c2.
Proof.
  induction a1; simpl; intros; eauto.
  subst b1.
  revert b2 c1 c2 H0 H1.
  induction a2; simpl; intros; eauto.
  congruence.
Qed.

Fixpoint inj_pair_rev_l (a b: positive) {struct b}: positive :=
  match b with
    | xO (xI b') => inj_pair_rev_l (xI a) b'
    | xO (xO b') => inj_pair_rev_l (xO a) b'
    | _ => a
  end.

Lemma inj_pair_aux_left_correct a1:
  forall a2 b1 b2,
    inj_pair_aux a1 b1 = inj_pair_aux a2 b2 ->
    forall c,
      inj_pair_rev_r b1 = Some c ->
      inj_pair_rev_r b2 = Some c ->
      inj_pair_rev_l a1 b1 = inj_pair_rev_l a2 b2
.
Proof.
  induction a1; simpl; intros.
  {
    specialize (IHa1 _ _ _ H).
    simpl in IHa1.
    eauto.
  }
  {
    specialize (IHa1 _ _ _ H).
    simpl in IHa1.
    eauto.
  }
  subst b1.
  revert b2 c H0 H1.
  induction a2; simpl; intros.
  {
    specialize (IHa2 _ _ H0).
    simpl in IHa2.
    eauto.
  }
  {
    specialize (IHa2 _ _ H0).
    simpl in IHa2.
    eauto.
  }
  auto.
Qed.

Definition inj_pair a b := inj_pair_aux a (xI b).

Lemma inj_pair_correct a1 a2 b1 b2:
  (a1, b1) = (a2, b2) <-> inj_pair a1 b1 = inj_pair a2 b2.
Proof.
  split.
  {
    congruence.
  }
  intros.
  specialize (inj_pair_aux_right_correct _ _ _ _ H _ _ (eq_refl _) (eq_refl _)).
  intros; subst.
  specialize (inj_pair_aux_left_correct _ _ _ _ H _ (eq_refl _) (eq_refl _)).
  simpl.
  congruence.
Qed.

Lemma inject_pair {A B} (a1 a2: A) (b1 b2: B):
  a1 = a2 ->
  b1 = b2 ->
  (a1, b1) = (a2, b2)
.
Proof.
  congruence.
Qed.

Lemma inject_pair_iff {A B} (a1 a2: A) (b1 b2: B):
  (a1 = a2 /\ b1 = b2) <-> (a1, b1) = (a2, b2)
.
Proof.
  intuition congruence.
Qed.

Local Program Instance index_of_pair U V:
  MapIndex U ->
  MapIndex V ->
  MapIndex (U * V) :=
  {
    index_of_tr := fun uv =>
                     let '(u, v) := uv in
                     inj_pair (index_of_tr u) (index_of_tr v)
  }.
Next Obligation.
  rewrite <- inj_pair_correct.
  repeat rewrite <- inject_pair_iff.
  repeat rewrite <- index_of_tr_correct.
  tauto.
Defined.

End I_OF_TR.

Inductive ratom: Type :=
| RConst (_: Defs.float Zaux.radix2)
| RVar (ty: type) (_: V)
| RError (_: nat)
.

Inductive rexpr: Type :=
  | RAtom (_: ratom)
  | RUnop (o: Tree.unary_op) (e: rexpr)
  | RBinop (o: Tree.binary_op) (e1 e2: rexpr)
. 

Fixpoint reval (e: rexpr) (env: forall ty, V -> ftype ty) (eenv: nat -> R): R :=
  match e with
    | RAtom (RConst q) => F2R _ q
    | RAtom (RVar ty n) => B2R _ _ (env ty n)
    | RAtom (RError n) => eenv n
    | RUnop o e => Prog.unary Prog.real_operations o (reval e env eenv)
    | RBinop o e1 e2 => Prog.binary Prog.real_operations o (reval e1 env eenv) (reval e2 env eenv)
  end.

Fixpoint max_error_var (e: rexpr): nat :=
  match e with
    | RAtom (RError n) =>
      S n
    | RUnop _ e => max_error_var e
    | RBinop _ e1 e2 => Nat.max (max_error_var e1) (max_error_var e2)
    | _ => O
  end.

Lemma reval_error_ext eenv1 env eenv2 e:
  (forall i, (i < max_error_var e)%nat ->
                 eenv1 i = eenv2 i) ->
  reval e env eenv1 = reval e env eenv2.
Proof.
  induction e; simpl.
  {
    destruct r; auto.
  }
  {
    intros.
    f_equal.
    auto.
  }
  intros.
  f_equal.
  {
    eapply IHe1; eauto with arith.
  }
  eapply IHe2; eauto with arith.
Qed.

Definition fone: Defs.float Zaux.radix2 :=
  {|
    Defs.Fnum := 1;
    Defs.Fexp := 0
  |}.


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

Section WITHMAP.

Context {MSHIFT} {MAP: Map nat (type * rounding_knowledge') MSHIFT}.

Definition make_rounding
           (si: nat)
           (shift: MSHIFT)
           (kn:  rounding_knowledge') (ty: type) (x: rexpr):
  (rexpr * (nat * MSHIFT))
  :=
    match kn with
      | Unknown' =>
        let d := si in
        let es1 := mset shift d (ty, Normal') in
        let e := S d in
        let es2 := mset es1 e (ty, Denormal') in
        (
          RBinop Tree.Add
                 (RBinop Tree.Mul x
                         (RBinop Tree.Add (RAtom (RConst fone))
                                 (RAtom (RError d)))
                 )
                 (RAtom (RError e))
          , (S e, es2)
        )

      | Normal' =>
        let d := si in
        let es1 := mset shift d (ty, Normal') in
        (
          RBinop Tree.Mul x
                 (RBinop Tree.Add (RAtom (RConst fone))
                         (RAtom (RError d))
                 )
          , (S d, es1)
        )
      | Denormal' => 
        let e := si in
        let es1 := mset shift e (ty, Denormal') in
        (
          RBinop Tree.Add x
                 (RAtom (RError e))
          , (S e, es1)
        )
      | Denormal2' => 
        let e := si in
        let es1 := mset shift e (ty, Denormal2') in
        (
          RBinop Tree.Add x
                 (RAtom (RError e))
          , (S e, es1)
        )
    end.

Lemma make_rounding_shift_incr
      si
      shift
      kn ty x
      y si' shift':
  make_rounding si shift kn ty x = (y, (si', shift')) ->
  (si <= si')%nat
.
Proof.
  unfold make_rounding.
  destruct kn;
  inversion 1; subst; auto with arith.
Qed.

Lemma make_rounding_shift_unchanged
      si
      shift
      kn ty x
      y si' shift':
  make_rounding si shift kn ty x = (y, (si', shift')) ->
  forall i, (i < si)%nat ->
            mget shift' i = mget shift i.
Proof.
  unfold make_rounding.
  destruct kn.
  inversion 1; subst; intros.
  repeat rewrite (mget_set eq_nat_dec).
  destruct (Nat.eq_dec i (S si)); auto;
  destruct (Nat.eq_dec i si); auto;
  exfalso; lia.
all: try (    inversion 1; subst; intros;
    rewrite (mget_set eq_nat_dec);
    destruct (Nat.eq_dec i si); auto;
    exfalso; lia).
Qed.

Lemma make_rounding_shift_le
      si
      shift
      kn ty x
      y si' shift':
  make_rounding si shift kn ty x = (y, (si', shift')) ->
    (max_error_var x <= si)%nat ->
    (max_error_var y <= si')%nat.
Proof.
  unfold make_rounding.
  destruct kn;
  inversion 1; subst; simpl; intros;
  repeat (apply Max.max_lub; auto with arith).
Qed.

Definition error_bound ty k :=
  / 2 * Raux.bpow Zaux.radix2
  match k with
    | Unknown' => 0
    | Normal' => (- fprec ty + 1)
    | Denormal' =>  (3 - femax ty - fprec ty)
    | Denormal2' =>  (1 + (3 - femax ty - fprec ty))
  end.

Lemma error_bound_nonneg ty k:
  0 <= error_bound ty k.
Proof.
    unfold error_bound.
    apply Rmult_le_pos; try lra.
    apply Raux.bpow_ge_0.
Qed.

Definition error_bound' ty k :=
  match k with
    | Unknown' => /2
    | Normal' => / 2 * Raux.bpow Zaux.radix2 (- fprec ty + 1)
    | Denormal' => / 2 * Raux.bpow Zaux.radix2 (3 - femax ty - fprec ty) 
    | Denormal2' => Raux.bpow Zaux.radix2 (3 - femax ty - fprec ty) 
  end.

Lemma error_bound'_correct ty k:
  error_bound' ty k = error_bound ty k.
Proof.
  destruct k; try reflexivity;
  unfold error_bound', error_bound.
  simpl. lra.
  rewrite bpow_plus.
 rewrite <- Rmult_assoc.
 rewrite Rinv_l. lra.
 simpl. lra.
Qed.

Definition rounding_cond ty k x :=
  match k with
    | Unknown' => True
    | Normal' =>
      Raux.bpow Zaux.radix2 (3 - femax ty - 1) <= Rabs x
    | Denormal' =>
      Rabs x < Raux.bpow Zaux.radix2 (3 - femax ty)
    | Denormal2' => True
  end.

Lemma make_rounding_correct
      si shift kn ty x y si' shift':
  make_rounding si shift (round_knowl_denote kn) ty x = (y, (si', shift')) ->
  (max_error_var x <= si)%nat ->
  forall errors1,
    (forall i ty k,
       mget shift i = (ty, k) ->
       Rabs (errors1 i) <= error_bound ty k) ->
  forall env,
    rounding_cond ty (round_knowl_denote kn) (reval x env errors1) ->
  forall choice,
  exists errors2,
    (forall i,
       (i < si)%nat ->
       errors2 i = errors1 i)
    /\
    reval y env errors2 =
    Generic_fmt.round
      Zaux.radix2
      (FLT_exp (3 - femax ty - fprec ty) (fprec ty))
      (Generic_fmt.Znearest choice)
      (reval x env errors1)
    /\
    (forall i ty' k,
       mget shift' i = (ty', k) ->
       Rabs (errors2 i) <= error_bound ty' k)
.  

Proof. 
unfold make_rounding, rounding_cond.
intros.
destruct kn as [ [ | ] | ]; unfold round_knowl_denote in H2.
- (* Normal *)
  replace (3 - femax ty - 1)%Z with (3 - femax ty - fprec ty + fprec ty - 1)%Z in H2 by ring.
  generalize (Relative.relative_error_N_FLT_ex _ _ _ (fprec_gt_0 _) choice _ H2).
  destruct 1 as (eps & Heps & Hround).
  pose (errors2 i := if Nat.eq_dec i si  then eps else errors1 i).
  exists errors2.
  split; [ | split].
  * unfold errors2; intros; destruct (Nat.eq_dec i si); auto; lia.
  * inversion H; clear H; subst.
    simpl reval.
    rewrite Rmult_1_l.
    rewrite <- (reval_error_ext errors1).
   --
     unfold errors2.
     destruct (Nat.eq_dec si si); congruence.
   --  intros; unfold errors2; destruct (Nat.eq_dec i si); auto; exfalso; lia.
  * inversion H; clear H; subst.
    simpl reval.
    intros until i.
    rewrite (mget_set Nat.eq_dec).
    intros.
    unfold errors2.
    destruct (Nat.eq_dec i si); auto.
    inversion H; subst.
    assumption.
 - (* Denormal *)
  replace (3 - femax ty)%Z with (3 - femax ty - fprec ty + fprec ty)%Z in H2 by ring.
  generalize (Fprop_absolute.absolute_error_N_FLT _ _ (fprec_gt_0 _) _ choice _ H2).
  destruct 1 as (eps & Heps & Hround).
  pose (errors2 i := if Nat.eq_dec i si then eps else errors1 i).
  exists errors2.    
  split; [ | split].
  * unfold errors2; intros; destruct (Nat.eq_dec i si); auto; lia.
  * inversion H; clear H; subst. simpl reval.
    rewrite <- (reval_error_ext errors1).
   -- unfold errors2; destruct (Nat.eq_dec si si); congruence.
   -- intros; unfold errors2; destruct (Nat.eq_dec i si); auto; lia.
  * inversion H; clear H; subst. simpl reval.
     intros until i.
     rewrite (mget_set Nat.eq_dec).
     intros.
     unfold errors2.
     destruct (Nat.eq_dec i si); auto.
     inversion H; subst.
     auto.
-  (* None *)
 generalize (Relative.error_N_FLT Zaux.radix2 (3 - femax ty - fprec ty) (fprec ty) (fprec_gt_0 _)  choice (reval x env errors1)).
 destruct 1 as (eps & eta & Heps & Heta & _ & Hround).
 pose (errors2 i := if Nat.eq_dec i (S (si)) then eta
                          else if Nat.eq_dec i si then eps else  errors1 i).
 exists errors2.
 split; [ | split].
 + 
   unfold errors2.
   intros; destruct (Nat.eq_dec i (S si)); try lia; destruct (Nat.eq_dec i si); try lia; auto.
 + inversion H; clear H; subst.
    simpl reval.
    rewrite Rmult_1_l.     
  rewrite <- (reval_error_ext errors1).
  *
    unfold errors2.
    destruct (Nat.eq_dec si (S si)); try (exfalso; lia).
    destruct (Nat.eq_dec si si); try congruence.
    destruct (Nat.eq_dec (S si) (S si)); congruence.
  *
   intros.
   unfold errors2.
   destruct (Nat.eq_dec i (S si)); try lia.
   destruct (Nat.eq_dec i si); try lia.
   auto.
 +
   inversion H; clear H; subst.
    simpl reval.
  intros until i.
  repeat rewrite (mget_set Nat.eq_dec).
  intros.
  unfold errors2.
  destruct (Nat.eq_dec i (S si)).
  * inversion H; subst; assumption.
  * destruct (Nat.eq_dec i si); auto.
     inversion H; subst.
    assumption.
Qed.

Definition Rbinop_of_rounded_binop o :=
  match o with
    | PLUS => Tree.Add
    | MULT => Tree.Mul
    | MINUS => Tree.Sub
    | DIV => Tree.Div
  end.

Definition rnd_of_binop
           si
           (shift: MSHIFT)
           (ty: type)
           (o: binop) (r1 r2: rexpr)
  :=
    match o with
      | SterbenzMinus => (RBinop Tree.Sub r1 r2, (si, shift))
      | PlusZero minus zero_left =>
        ((
            if zero_left
            then
              if minus
              then RUnop Tree.Neg r2
              else r2
            else
              r1
          ), (si, shift))       
      | Rounded2 o' k => 
        make_rounding si shift (round_knowl_denote k) ty                      
                      (RBinop (Rbinop_of_rounded_binop o') r1 r2)
    end.

Definition rnd_of_cast
           si
           (shift: MSHIFT)
           (tyfrom tyto: type)
           (k: rounding_knowledge')
           (r: rexpr) :=
  if type_leb tyfrom tyto
  then
    (r, (si, shift))
  else
    make_rounding si shift k tyto r
.

Definition Runop_of_rounded_unop o :=
  match o with
    | SQRT => Tree.Sqrt
  end.

Definition Runop_of_exact_unop ty o :=
  match o with
    | Abs => RUnop Tree.Abs
    | Opp => RUnop Tree.Neg
    | Shift n _ => RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (Z.of_N n)))))
    | InvShift n _ => RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (- Z.pos n)))))
  end.

Definition rnd_of_unop
           si
           (shift: MSHIFT)
           (ty: type)
           (o: unop) (r: rexpr)
  :=
    match o with
      | Rounded1 o k =>
        make_rounding si shift (round_knowl_denote k) ty
                      (RUnop (Runop_of_rounded_unop o) r)
      | Exact1 o => (Runop_of_exact_unop ty o r, (si, shift))
      | CastTo ty' k => rnd_of_cast si shift ty ty' (round_knowl_denote k) r
      | uInvShift n _ => 
           make_rounding si shift Denormal2' ty
              ((RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (- Z.pos n)))))) r)
    end.

Fixpoint rndval 
         si
         (shift: MSHIFT)
         (e: expr) {struct e}
 :=
  match e with
    | Const ty f => (RAtom (RConst (B2F f)), (si, shift))
    | Var ty i => (RAtom (RVar ty i), (si, shift))
    | Binop b e1 e2 =>
      let '(r1, (si1, s1)) := rndval si shift e1 in
      let '(r2, (si2, s2)) := rndval si1 s1 e2 in
      rnd_of_binop si2 s2 (type_of_expr e) b r1 r2
    | Unop b e1 =>
      let '(r1, (si1, s1)) := rndval si shift e1 in
      rnd_of_unop si1 s1 (type_of_expr e1) b r1
  end.

Lemma rnd_of_binop_shift_incr si shift ty b r1 r2 r si' shift':
  rnd_of_binop si shift ty b r1 r2 = (r, (si', shift')) ->
  (si <= si')%nat.
Proof.
  destruct b; simpl; intros.
  {
    eapply make_rounding_shift_incr; eauto.
  }
  {
    inversion H; clear H; subst.
    auto with arith.
  }
  {
    inversion H; clear H; subst.
    auto with arith.
  }
Qed.

Lemma rnd_of_binop_shift_le si shift ty b r1 r2 r si' shift':
  rnd_of_binop si shift ty b r1 r2 = (r, (si', shift')) ->
    (max_error_var r1 <= si)%nat ->
    (max_error_var r2 <= si)%nat ->
    (max_error_var r <=  si')%nat.
Proof.
  destruct b; simpl; intros.
  {
    eapply make_rounding_shift_le; eauto.
    simpl.
    apply Nat.max_lub; auto.
  }
  {
    inversion H; clear H; subst.
    simpl.
    apply Nat.max_lub; auto.
  }
  {
    inversion H; clear H; subst.
    destruct zero_left; auto.
    destruct minus; auto.
  }
Qed.

Lemma rnd_of_binop_shift_unchanged  si shift ty b r1 r2 r si' shift':
  rnd_of_binop si shift ty b r1 r2 = (r, (si', shift')) ->
  forall i, (i < si)%nat ->
            mget shift' i = mget shift i.
Proof.
  destruct b; simpl; intros.
  {
    eapply make_rounding_shift_unchanged; eauto.
  }
  {
    congruence.
  }
  {
    congruence.
  }
Qed.

Lemma rnd_of_cast_shift_incr si shift ty ty0 knowl r1 y si' shift':
  rnd_of_cast si shift ty ty0 knowl r1 = (y, (si', shift')) ->
  (si <= si')%nat.
Proof.
  unfold rnd_of_cast.
  destruct (
      type_leb ty ty0
    ).
  {
    inversion_clear 1; auto with arith.
  }
  intros.
  eapply make_rounding_shift_incr; eauto.
Qed.

Lemma rnd_of_cast_shift_le si shift ty ty0 knowl r1 y si' shift':
  rnd_of_cast si shift ty ty0 knowl r1 = (y, (si', shift')) ->
  (max_error_var r1 <= si)%nat ->
    (max_error_var y <= si')%nat.
Proof.
  unfold rnd_of_cast.
  destruct (
      type_leb ty ty0
    ).
  {
    congruence.
  }
  intros; eapply make_rounding_shift_le; eauto.
Qed.

Lemma rnd_of_cast_shift_unchanged si shift ty ty0 knowl r1 y si' shift':
  rnd_of_cast si shift ty ty0 knowl r1 = (y, (si', shift')) ->
  forall i, (i < si)%nat ->
            mget shift' i = mget shift i.
Proof.
  unfold rnd_of_cast.
  destruct (type_leb ty ty0).
  {
    congruence.
  }
  apply make_rounding_shift_unchanged.
Qed.
    
Lemma rnd_of_unop_shift_incr si shift ty u r1 y si' shift':
  rnd_of_unop si shift ty u r1 = (y, (si', shift')) ->
  (si <= si')%nat.
Proof.
  destruct u; simpl.
- (* Rounded1 *)
     apply make_rounding_shift_incr.
- (* Exact1 *)
   inversion_clear 1; auto with arith.
- (* CastTo *)
  apply rnd_of_cast_shift_incr.
- (* uInvShift *)
  apply (make_rounding_shift_incr _ _ Denormal2').
Qed.

Lemma rnd_of_unop_shift_le si  shift ty u r1 y si' shift':
  rnd_of_unop si shift ty u r1 = (y, (si', shift')) ->
  (max_error_var r1 <= si)%nat ->
  (max_error_var y  <=  si')%nat.
Proof.
  destruct u; simpl; intros.
- (* Rounded1 *)
    eapply make_rounding_shift_le; eauto.
- (* Exact1 *)
    inversion H; clear H; subst; simpl.
    destruct o; simpl; auto.
- (* CastTo *)
  eapply rnd_of_cast_shift_le; eauto.
- (* uInvShift *)
    eapply (make_rounding_shift_le _ _ Denormal2'); eauto.
Qed.

Lemma rnd_of_unop_shift_unchanged si  shift ty u r1 y si' shift':
  rnd_of_unop si shift ty u r1 = (y, (si', shift')) ->
  forall i, (i < si)%nat ->
            mget shift' i = mget shift i.
Proof.
  destruct u; simpl.
- (* Rounded1 *)
    apply make_rounding_shift_unchanged.
- (* Exact1 *)
    inversion_clear 1; auto with arith.
- (* CastTo *)
  apply rnd_of_cast_shift_unchanged.
- (* uInvShift *)
    apply (make_rounding_shift_unchanged _ _ Denormal2').
Qed.

Lemma rndval_shift_incr x:
  forall si shift y si' shift',
    rndval si shift x = (y, (si', shift')) ->
    (si <= si')%nat.
Proof.
  induction x; simpl.
- (* Const *)
    inversion_clear 1; intros; auto with arith.
- (* Var *)
    inversion_clear 1; intros; auto with arith.
- (* Binop *)
    intros.
    destruct (rndval si shift x1) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval si1 s1 x2) as (r2 & si2 & s2) eqn:EQ2.
    eapply le_trans.
    {
      eapply IHx1; eauto.
    }
    eapply le_trans.
    {
      eapply IHx2; eauto.
    }
    eapply rnd_of_binop_shift_incr; eauto.
- (* Unop *)
  intros.
  destruct (rndval si shift x) as (r1 & si1 & s1) eqn:EQ1.
  eapply le_trans.
  {
    eapply IHx; eauto.
  }
  eapply rnd_of_unop_shift_incr; eauto.
Qed.

Lemma rndval_shift_le x:
  forall si shift y si' shift',
    rndval si shift x = (y, (si', shift')) ->
    (max_error_var y <=  si')%nat.
Proof.
  induction x; simpl.
- (* Const *)
    inversion_clear 1; simpl; auto with arith.
- (* Var *)
    inversion_clear 1; simpl; auto with arith.
- (* Binop *)
    intros.
    destruct (rndval si shift x1) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval si1 s1 x2) as (r2 & si2 & s2) eqn:EQ2.
    eapply rnd_of_binop_shift_le; eauto.
    eapply le_trans.
    {
      eapply IHx1; eauto.
    }
    eapply rndval_shift_incr; eauto.
- (* Unop *)
  intros.
  destruct (rndval si shift x) as (r1 & si1 & s1) eqn:EQ1.
  eapply rnd_of_unop_shift_le; eauto.
Qed.

Lemma rndval_shift_unchanged x:
  forall si shift y si' shift',
    rndval si shift x = (y, (si', shift')) ->
  forall i, (i < si)%nat ->
            mget shift' i = mget shift i.
Proof.
  induction x; simpl.
- (* Const *)
    inversion_clear 1; intros; auto with arith.
- (* Var *)
    inversion_clear 1; intros; auto with arith.
- (* Binop *)
    intros.
    destruct (rndval si shift x1) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval si1 s1 x2) as (r2 & si2 & s2) eqn:EQ2.
    etransitivity.
    {
      eapply rnd_of_binop_shift_unchanged; eauto.
      eapply lt_le_trans; [ eassumption | ].
      etransitivity.
      {
        eapply rndval_shift_incr; eauto.
      }
      eapply rndval_shift_incr; eauto.
    }
    etransitivity.
    {
      eapply IHx2; eauto.
      eapply lt_le_trans; [ eassumption | ].
      eapply rndval_shift_incr; eauto.
    }
    eapply IHx1; eauto.
- (* Unop *)
  intros.
  destruct (rndval si shift x) as (r1 & si1 & s1) eqn:EQ1.
  etransitivity.
  {
    eapply rnd_of_unop_shift_unchanged; eauto.
    eapply lt_le_trans; [ eassumption | ].
    eapply rndval_shift_incr; eauto.
  }
  eapply IHx; eauto.
Qed.

(*  "(a, b) holds" iff 0 (if b then < else <=) a *)
Definition cond: Type := (rexpr * bool).

Definition False_cond : cond  := 
   (* a condition that is impossible to satisfy *)
 (RAtom (RConst (Float radix2 0 0)), true).

Definition eval_cond1 env m (c: cond) :=
  let '(e, b) := c in
  forall errors,
    (forall i ty' k,
       mget m i = (ty', k) ->
       Rabs (errors i) <= error_bound ty' k) ->
    (if b then Rlt else Rle) 0 (reval e env errors)
.

Lemma evalcond1_False: forall env m, eval_cond1 env m False_cond -> False.
Proof.
intros.
hnf in H.
specialize (H (fun _ => 0)).
match type of H with ?A -> _ => assert A end;
  [ |  apply H in H0; simpl in H0; lra].
intros. unfold error_bound. destruct k.
- 
simpl.
rewrite Rabs_R0.
lra.
-
pose proof (bpow_gt_0 radix2 (Z.pos_sub 1 (fprecp ty'))).
set (j := bpow _ _) in *. clearbody j.
rewrite Rabs_pos_eq by lra.
lra.
-
pose proof (bpow_gt_0 radix2 (3 - femax ty' - fprec ty')).
set (j := bpow _ _) in *. clearbody j.
rewrite Rabs_pos_eq by lra.
lra.
-
rewrite Rabs_R0.
apply Rmult_le_pos.
lra.
apply Rlt_le. apply bpow_gt_0.
Qed.

Lemma eval_cond1_preserved m1 m2 env c:
  ( forall e b,
      c = (e, b) ->
      forall i,
        (i < max_error_var e)%nat ->
        mget m2 i = mget m1 i
  ) ->
  eval_cond1 env m1 c ->
  eval_cond1 env m2 c.
Proof.
  unfold eval_cond1.
  intros.
  destruct c.
  intros.
  rewrite <- (reval_error_ext (fun i =>
                              if Nat.ltb i (max_error_var r)
                              then errors i
                              else 0)).
  {
    apply H0.
    intros.
    destruct (Nat.ltb i (max_error_var r)) eqn:LTB.
    {
      apply H1.
      erewrite H; eauto.
      apply Nat.ltb_lt.
      assumption.
    }
    rewrite Rabs_R0.
    apply error_bound_nonneg.
  }
  intros.
  rewrite <- Nat.ltb_lt in H2.
  rewrite H2.
  reflexivity.
Qed.

Fixpoint revars (r: rexpr): MSET.t :=
  match r with
    | RAtom (RError n) => MSET.singleton n
    | RUnop _ e => revars e
    | RBinop _ e1 e2 => MSET.union (revars e1) (revars e2)
    | _ => MSET.empty
  end.

Lemma reval_error_ext_strong errors1 env errors2 e:
  (forall i, MSET.In i (revars e) -> errors2 i = errors1 i) ->
  reval e env errors2 = reval e env errors1.
Proof.
  induction e; simpl.
  {
    destruct r; auto.
    intros.
    apply H.
    apply MSET.singleton_spec.
    reflexivity.
  }
  {
    intros.
    intuition congruence.
  }
  intros.
  rewrite IHe1.
  {
    rewrite IHe2.
    {
      reflexivity.
    }
    intros.
    apply H.
    rewrite MSET.union_spec.
    tauto.
  }
  intros.
  apply H.
  rewrite MSET.union_spec.
  tauto.
Qed.

Lemma revars_max_error_var e:
  forall i, MSET.In i (revars e) -> 
            (i < max_error_var e)%nat.
Proof.
  induction e; simpl; auto; intro.
  {
    destruct r; generalize (@MSET.empty_spec i); try contradiction.
    intros _.
    rewrite MSET.singleton_spec.
    intro; subst; auto with arith.
  }
  rewrite MSET.union_spec.
  destruct 1.
  {
    eapply lt_le_trans.
    { eapply IHe1; eauto. }
    apply Nat.le_max_l.
  }
  eapply lt_le_trans.
  { eapply IHe2; eauto. }
  apply Nat.le_max_r.
Qed.

Context {MSHIFT'} {MAP': Map nat R MSHIFT'}.

Export List.

Fixpoint enum_forall' t_ (Q: nat -> _ -> Prop) (l: list nat) (P: MSHIFT' -> Prop): Prop :=
  match l with
    | nil => P (mempty t_)
    | a :: q =>
      enum_forall' t_ Q q (fun errors =>
                            forall u,
                              Q a u ->
                              P (mset errors a u))
  end.

Lemma enum_forall_correct'  t_ (Q: _ -> _ -> Prop) (Ht_: forall i, Q i t_) l:
  forall (P: _ -> Prop),
    (forall errors1 errors2,
       (forall i, In i l -> mget errors2 i = mget errors1 i) ->
       P errors1 -> P errors2) ->
    (forall errors,
       (forall i, Q i (mget errors i)) ->
       P errors) <->
    enum_forall' t_ Q l P.
Proof.
  induction l; simpl; intros.
  {
    split.
    {
      intros.
      eapply H0.
      intros.
      rewrite mget_empty.
      auto.
    }
    intros.
    eapply H; [ | eassumption ].
    contradiction.
  }
  specialize (IHl (fun errors => forall u, Q a u -> P (mset errors a u))).
  destruct IHl.
  {
    simpl.
    intros.
    eapply H.
    2: eapply H1; eauto.
    intros.
    repeat rewrite (mget_set Nat.eq_dec).
    destruct (Nat.eq_dec i a); auto.
    destruct H3; try congruence.
    auto.
  }
  split; intros.
  {
    apply H0; intros.
    apply H2.
    intros.
    repeat rewrite (mget_set Nat.eq_dec).
    destruct (Nat.eq_dec i a); auto.
    congruence.
  }
  eapply H.
  2: eapply H1 with (u := mget errors a); eauto.
  intros.
  repeat rewrite (mget_set Nat.eq_dec).
  destruct (Nat.eq_dec i a); auto.
Qed.

Definition enum_forall t_ Q l P :=
    enum_forall' t_ Q l (fun m => P (mget m)).  

Theorem enum_forall_correct  t_ (Q: _ -> _ -> Prop) (Ht_: forall i, Q i t_) l:
  forall (P: _ -> Prop),
    (forall errors1 errors2,
       (forall i, In i l -> errors2 i = errors1 i) ->
       P errors1 -> P errors2) ->
    (forall errors,
       (forall i, Q i (mget errors i)) ->
       P (mget errors)) <->
    enum_forall t_ Q l P.
Proof.
  unfold enum_forall.
  intros.
  rewrite <- (enum_forall_correct' t_ Q Ht_ l (fun m => P (mget m))); try tauto.
  intros.
  eapply H; eauto.
Qed.

Section EVAL_COND2.

Let P env e (b: bool) errors :=
  (if b then Rlt else Rle) 0 (reval e env errors).

Let Q m i err := 
  let '(ty', k) := mget m i in
  Rabs err <= error_bound ty' k
.

Definition eval_cond2 env m (c: cond) :=
  let '(e, b) := c in
  enum_forall 0 (Q m) (MSET.elements (revars e)) (P env e b)
.

Lemma eval_cond2_correct env m c:
  eval_cond2 env m c <-> eval_cond1 env m c.
Proof.
  unfold eval_cond2, eval_cond1.
  destruct c.
  rewrite <- enum_forall_correct.
  {
    unfold Q, P.
    split; intros.
    {
      destruct (finite_errors_ex 0 (max_error_var r) errors).
      rewrite <- (reval_error_ext (mget x)).
      {
        eapply H; eauto.
        intros.
        destruct (mget m i) eqn:?.
        rewrite H1.
        destruct (Nat.ltb i (max_error_var r)); auto.
        rewrite Rabs_R0.
        apply error_bound_nonneg.
      }
      intros.
      rewrite H1.
      rewrite <- Nat.ltb_lt in H2.
      rewrite H2.
      reflexivity.
    }
    apply H.
    intros.
    specialize (H0 i).
    rewrite H1 in H0.
    assumption.
  }
  {
    unfold Q.
    intros.
    destruct (mget m i).
    rewrite Rabs_R0.
    apply error_bound_nonneg.
  }
  unfold P.
  intros.
  rewrite (reval_error_ext_strong errors1); auto.
  intros.
  apply H.
  rewrite <- MSET.elements_spec1 in H1.
  rewrite SetoidList.InA_alt in H1.
  destruct H1.
  intuition congruence.
Qed.

End EVAL_COND2.

Definition is_div o :=
  match o with
    | DIV => true
    | _ => false
  end.

Definition rounding_cond_ast ty k x: list cond :=
  match k with
    | Normal' =>
      (RBinop Tree.Sub (RUnop Tree.Abs x) (RAtom (RConst (Defs.Float _ 1 (3 - femax ty - 1)))), false) :: nil
    | Denormal' =>
      (RBinop Tree.Sub (RAtom (RConst (Defs.Float _ 1 (3 - femax ty)))) (RUnop Tree.Abs x), true) :: nil
    | Denormal2' => nil
    | Unknown' => nil 
  end.

Lemma rounding_cond_ast_shift ty k x e b:
  In (e, b) (rounding_cond_ast ty k x) ->
  (max_error_var e <= max_error_var x)%nat.
Proof.
  Opaque Zminus.
  destruct k; simpl; try tauto;
    intro K;
    inversion K; try contradiction;
    clear K;
    subst;
    inversion H; clear H; subst;
    simpl;
    try rewrite Max.max_0_r;
    auto with arith.
  Transparent Zminus.
Qed.

Lemma rounding_cond_ast_correct m env ty knowl r errors:
  (forall i ty k,
     mget m i = (ty, k) ->
     Rabs (errors i) <= error_bound ty k) ->
  (forall i, In i (rounding_cond_ast ty knowl r) -> eval_cond1 env m i) ->
  rounding_cond ty knowl (reval r env errors)
.
Proof.
  intros.
  unfold rounding_cond.
  destruct knowl; auto.
 -
  cbn -[Zminus] in * |- *  .
    specialize (H0 _ (or_introl _ (refl_equal _))).
    cbn -[Zminus] in *.
    specialize (H0 _ H).
    lra.
 -
  specialize (H0 _ (or_introl _ (refl_equal _))).
  cbn -[Zminus] in *.
  specialize (H0 _ H).
  lra.
Qed.

Definition no_overflow ty x: cond := 
  (RBinop Tree.Sub (RAtom (RConst (Defs.Float _ 1 (femax ty)))) (RUnop Tree.Abs x), true).

Definition rnd_of_plus_zero_cond (zero_left: bool) r1 r2 :=
  (RUnop Tree.Neg (RUnop Tree.Abs (if zero_left then r1 else r2)), false) :: nil.  

Definition rnd_of_binop_with_cond
           si
           (shift: MSHIFT)
           (ty: type)
           (o: binop) (r1 r2: rexpr):
  ((rexpr * (nat * MSHIFT)) * list cond)
  :=
    match o with
      | SterbenzMinus =>
        ((RBinop Tree.Sub r1 r2, (si, shift)),
         (RBinop Tree.Sub r1 (RBinop Tree.Mul r2 (RAtom (RConst (Defs.Float _ 1 (-1))))), false)
           ::
           (RBinop Tree.Sub (RBinop Tree.Mul r2 (RAtom (RConst (Defs.Float _ 1 1)))) r1, false)
           :: nil)
      | PlusZero minus zero_left =>
        (
          ((
              if zero_left
              then
                if minus
                then RUnop Tree.Neg r2
                else r2
              else
                r1
            ), (si, shift))
          ,
          rnd_of_plus_zero_cond zero_left r1 r2
        )
      | Rounded2 o' k =>
        let ru := RBinop (Rbinop_of_rounded_binop o') r1 r2 in
        let rs := make_rounding si shift (round_knowl_denote k) ty ru in
        let '(r, _) := rs in
        (rs,
         (if is_div o' then (RUnop Tree.Abs r2, true) :: nil else nil)
           ++ no_overflow ty r :: rounding_cond_ast ty (round_knowl_denote k) ru)
    end.

Lemma rounding_cond_ast_shift_cond ty k r e b:
  In (e, b) (rounding_cond_ast ty k r) ->
     (max_error_var e = max_error_var r)%nat.
Proof.
  unfold rounding_cond_ast.
  destruct k; try contradiction.
-
    destruct 1; try contradiction.
    Opaque Zminus. inversion H; clear H; subst. Transparent Zminus.
    simpl.
    apply Max.max_0_r.
-
  destruct 1; try contradiction.
  Opaque Zminus. inversion H; clear H; subst. Transparent Zminus.
  reflexivity.
Qed.

Lemma rnd_of_binop_with_cond_shift_cond si shift ty o r1 r2 r' si' shift' cond:
  rnd_of_binop_with_cond si shift ty o r1 r2 = ((r', (si', shift')), cond) ->
  (max_error_var r1 <= si)%nat ->
  (max_error_var r2 <= si)%nat ->
  forall e b,
    In (e, b) cond ->
    (max_error_var e <= si')%nat.
Proof.
  destruct o; simpl.
  {
    destruct (
        make_rounding si shift (round_knowl_denote knowl) ty
                      (RBinop (Rbinop_of_rounded_binop op) r1 r2)
    ) eqn:EQ.
    intro K.
    inversion K; clear K; subst.
    intros.
    apply in_app_or in H1.
    destruct H1.
    {
      destruct (is_div op); try contradiction.
      destruct H1; try contradiction.
      inversion H1; clear H1; subst.
      simpl.
      apply make_rounding_shift_incr in EQ.
      lia.
    }
    destruct H1.
    {
      inversion H1; clear H1; subst.
      simpl.
      eapply make_rounding_shift_le; eauto.
      simpl.
      apply Max.max_lub; auto.
    }
    apply rounding_cond_ast_shift_cond in H1.
    rewrite H1.
    simpl.
    apply make_rounding_shift_incr in EQ.
    apply Max.max_lub; lia.
  }
  {
    intro K.
    inversion K; clear K; subst.
    simpl.
    destruct 3.
    {
      inversion H1; clear H1; subst.
      simpl.
      rewrite Max.max_0_r.
      apply Max.max_lub; lia.
    }
    destruct H1; try contradiction.
    inversion H1; clear H1; subst.
    simpl.
    rewrite Max.max_0_r.
    apply Max.max_lub; lia.
  }
  {
    intro K.
    inversion K; clear K; subst.
    simpl.
    destruct 3; try contradiction.
    inversion H1; clear H1; subst.
    simpl.
    destruct zero_left; auto.
  }
Qed.

Definition rnd_of_cast_with_cond
           si
           (shift: MSHIFT)
           (tyfrom tyto: type)
           (k: rounding_knowledge')
           (r: rexpr) :=
  if type_leb tyfrom tyto
  then
    ((r, (si, shift)), nil)
  else
    let rs := make_rounding si shift k tyto r in
    let '(r', _) := rs in
    (rs, no_overflow tyto r' :: rounding_cond_ast tyto k r)
.

Lemma rnd_of_cast_with_cond_shift_cond
      si shift tyfrom tyto k r r' si' shift' cond:
  rnd_of_cast_with_cond si shift tyfrom tyto k r = ((r', (si', shift')), cond) ->
  (max_error_var r <= si)%nat ->
  forall e b,
    In (e, b) cond ->
    (max_error_var e <= si')%nat.
Proof.
  unfold rnd_of_cast_with_cond.
  destruct (type_leb tyfrom tyto).
  {
    intros.
    inversion H; clear H; subst.
    contradiction.
  }
  destruct (make_rounding si shift k tyto r) eqn:EQ.
  destruct p.
  intro K.
  inversion K; clear K; subst.
  destruct 2.
  {
    inversion H0; clear H0; subst.
    simpl.
    eapply make_rounding_shift_le; eauto.
  }
  apply rounding_cond_ast_shift_cond in H0.
  rewrite H0.
  apply make_rounding_shift_incr in EQ.
  lia.
Qed.

Definition is_sqrt o :=
  match o with
    | SQRT => true
  end.

Definition rnd_of_unop_with_cond
           si
           (shift: MSHIFT)
           (ty: type)
           (o: unop) (r1: rexpr)
  :=
    match o with
      | Rounded1 o k =>
        let ru := RUnop (Runop_of_rounded_unop o) r1 in
        let rs := make_rounding si shift (round_knowl_denote k) ty ru in
        let '(r, _) := rs in
        (rs, (if is_sqrt o
              then
                (r1, false) :: nil
              else nil) ++ rounding_cond_ast ty (round_knowl_denote k) ru)
      | Exact1 o => 
        let ru := Runop_of_exact_unop ty o r1 in
        ((ru, (si, shift)), 
         match o with
           | Shift _ _ => no_overflow ty ru :: nil
           | InvShift n _ => (RBinop Tree.Sub (RUnop Tree.Abs r1) (RAtom (RConst (Defs.Float _ 1 (3 - femax ty + Z.pos n - 1)))), false) :: nil
           | _ => nil
         end)
      | CastTo ty' k => rnd_of_cast_with_cond si shift ty ty' (round_knowl_denote k) r1
     | uInvShift n _ =>
        let ru := RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (- Z.pos n))))) r1 in
        let rs := make_rounding si shift Denormal2' ty ru in
        let '(r, _) := rs in
        (rs, nil)
    end.

Lemma rnd_of_unop_with_cond_shift_cond si shift ty o r1 r' si' shift' cond:
  rnd_of_unop_with_cond si shift ty o r1 = ((r', (si', shift')), cond) ->
  (max_error_var r1 <= si)%nat ->
  forall e b,
    In (e, b) cond ->
    (max_error_var e <= si')%nat.
Proof.
  destruct o; cbn -[Zminus].
- (* Rounded1 *)
    destruct (
        make_rounding si shift (round_knowl_denote knowl) ty (RUnop (Runop_of_rounded_unop op) r1)
      ) as [r'1 [si'1 shift'1]] eqn:EQ.
    intro K.
    inversion K; clear K; subst.
    intros.
    apply in_app_or in H0.
    destruct H0.
    {
      destruct (is_sqrt op); try contradiction.
      destruct H0; try contradiction.
      inversion H0; clear H0; subst.
      eapply make_rounding_shift_incr in EQ.
      lia.
    }
    apply rounding_cond_ast_shift_cond in H0.
    rewrite H0.
    simpl.
    apply make_rounding_shift_incr in EQ.
    lia.
- (* Exact1 *)
    intro K.
    inversion K; clear K; subst.
    intros.
    destruct o; try contradiction.
   + (* Shift *)
      destruct H0; try contradiction.
      inversion H0; clear H0; subst.
      simpl.
      assumption.
   + (* InvShift *)
    destruct H0; try contradiction.
    inversion H0; clear H0; subst.
    simpl.
    rewrite Max.max_0_r.
    assumption.
- (* CastTo *)
  apply rnd_of_cast_with_cond_shift_cond.
- (* uInvShift *)
  intros.
  inversion H; clear H; subst. inversion H1.
Qed.

Fixpoint rndval_with_cond
         si
         (shift: MSHIFT)
         (e: expr) {struct e}
  :=
  match e with
    | Const ty f => ((RAtom (RConst (B2F f)), (si, shift)), nil)
    | Var ty i => ((RAtom (RVar ty i), (si, shift)), nil)
    | Binop b e1 e2 =>
      let '((r1, (si1, s1)), p1) := rndval_with_cond si shift e1 in
      let '((r2, (si2, s2)), p2) := rndval_with_cond si1 s1 e2 in
      let ty := type_of_expr e in
      let '(rs, p) := rnd_of_binop_with_cond si2 s2 ty b r1 r2 in
      (rs, p ++ (p1 ++ p2))
    | Unop b e1 =>
      let '((r1, (si1, s1)), p1) := rndval_with_cond si shift e1 in
      let '(rs, p) := rnd_of_unop_with_cond si1 s1 (type_of_expr e1) b r1 in
      (rs, p ++ p1)
  end. 

Lemma rnd_of_binop_with_cond_left si shift ty o r1 r2:
  fst (rnd_of_binop_with_cond si shift ty o r1 r2) =
  rnd_of_binop si shift ty o r1 r2.
Proof.
  unfold rnd_of_binop_with_cond, rnd_of_binop.
  destruct o; simpl; auto.
  destruct (
make_rounding si shift (round_knowl_denote knowl) ty
         (RBinop (Rbinop_of_rounded_binop op) r1 r2)
    ); simpl; auto.
Qed.

Lemma rnd_of_cast_with_cond_left si shift ty ty0 knowl r1:
   fst (rnd_of_cast_with_cond si shift ty ty0 knowl r1) =
   rnd_of_cast si shift ty ty0 knowl r1.
Proof.
  unfold rnd_of_cast_with_cond, rnd_of_cast.
  destruct (
      type_leb ty ty0
    ); auto.
  destruct (make_rounding si shift knowl ty0 r1).
  auto.
Qed.

Lemma rnd_of_unop_with_cond_left si shift ty o r1:
  fst (rnd_of_unop_with_cond si shift ty o r1) =
  rnd_of_unop si shift ty o r1.
Proof.
  unfold rnd_of_unop_with_cond, rnd_of_unop.
  destruct o; simpl; auto.
- (* Rounded1 *)
    destruct (
        make_rounding si shift (round_knowl_denote knowl) ty
                      (RUnop (Runop_of_rounded_unop op) r1)
      ); simpl; auto.
- (* CastTo *)
  apply rnd_of_cast_with_cond_left.
Qed.

Lemma rndval_with_cond_left e:
  forall si shift,
    fst (rndval_with_cond si shift e) = rndval si shift e.
Proof.
  induction e; simpl; auto.
- (* Binop *)
    intros.
    specialize (IHe1 si shift).
    destruct (rndval_with_cond si shift e1).
    simpl in IHe1.
    subst.
    destruct (rndval si shift e1).
    destruct p.
    specialize (IHe2 n m).
    destruct (rndval_with_cond n m e2).
    simpl in IHe2.
    subst.
    destruct (rndval n m e2).
    destruct p.
    specialize (rnd_of_binop_with_cond_left n0 m0 (type_lub (type_of_expr e1) (type_of_expr e2)) b r r0).
    destruct (rnd_of_binop_with_cond n0 m0 (type_lub (type_of_expr e1) (type_of_expr e2)) b r r0);
      simpl; auto.
- (* Unop *)
   intros.
  specialize (IHe si shift).
  destruct (rndval_with_cond si shift e); simpl in *; subst.
  destruct (rndval si shift e).
  destruct p.
  specialize (rnd_of_unop_with_cond_left n m (type_of_expr e) u r).
  destruct (
      rnd_of_unop_with_cond n m (type_of_expr e) u r
    ); simpl; auto. 
Qed.

Lemma rndval_with_cond_shift_cond e:
  forall si shift r' si' shift' cond,
  rndval_with_cond si shift e = ((r', (si', shift')), cond) ->
  forall e' b',
    In (e', b') cond ->
    (max_error_var e' <= si')%nat.
Proof.
  induction e; simpl; intros.
  {
    inversion H; clear H; subst; contradiction.
  }
  {
    inversion H; clear H; subst; contradiction.
  }
  {
    destruct (rndval_with_cond si shift e1) as [[r1 [si1 s1]] p1] eqn:EQ1.
    destruct (rndval_with_cond si1 s1 e2) as [[r2 [si2 s2]] p2] eqn:EQ2.
    destruct (rnd_of_binop_with_cond si2 s2 (type_lub (type_of_expr e1) (type_of_expr e2)) b r1 r2)
             as [rs' p']
             eqn:EQ.
    inversion H; clear H; subst.
    generalize (rndval_with_cond_left e1 si shift).
    rewrite EQ1.
    simpl.
    intros.
    symmetry in H.   
    generalize (rndval_with_cond_left e2 si1 s1).
    rewrite EQ2.
    simpl.
    intros.
    symmetry in H1.
    generalize (rnd_of_binop_with_cond_left si2 s2 (type_lub (type_of_expr e1) (type_of_expr e2)) b r1 r2).
    rewrite EQ.
    intros.
    symmetry in H2.
    simpl in H2.
    generalize H.
    intro.
    apply rndval_shift_incr in H.
    apply rndval_shift_le in H3.
    generalize H1.
    intro.
    apply rndval_shift_incr in H1.
    apply rndval_shift_le in H4.
    generalize H2.
    intro.
    apply rnd_of_binop_shift_incr in H2.
    apply rnd_of_binop_shift_le in H5; try lia.
    apply in_app_or in H0.
    destruct H0.
    {
      eapply rnd_of_binop_with_cond_shift_cond; eauto.
      lia.
    }
    apply in_app_or in H0.
    destruct H0.
    {
      eapply IHe1 in H0; [ | eassumption ] .
      lia.
    }
    eapply IHe2 in H0; [ | eassumption ].
    lia.
  }
  destruct (rndval_with_cond si shift e) as [[r1 [si1 s1]] p1] eqn:EQ1.
  destruct (rnd_of_unop_with_cond si1 s1 (type_of_expr e) u r1) eqn:EQ.
  inversion H; clear H; subst.
  generalize (rndval_with_cond_left e si shift).
  rewrite EQ1.
  simpl.
  intros.
  symmetry in H.   
  generalize (rnd_of_unop_with_cond_left si1 s1 (type_of_expr e) u r1).
  rewrite EQ.
  intros.
  symmetry in H1.
  simpl in H1.
  generalize H.
  intro.
  apply rndval_shift_incr in H.
  apply rndval_shift_le in H2.
  generalize H1.
  intro.
  apply rnd_of_unop_shift_incr in H1.
  apply rnd_of_unop_shift_le in H3; try lia.
  apply in_app_or in H0.
  destruct H0.
  {
    eapply rnd_of_unop_with_cond_shift_cond; eauto.
  }
  eapply IHe in H0; [ | eassumption ] .
  lia.
Qed.

Lemma sterbenz_no_overflow A x y:
  - A < x < A ->
  - A < y < A ->
  0 <= y * 2 - x ->
  0 <= x - y * / 2 ->
  - A < x - y < A
.
Proof.
  lra.
Qed.

Lemma Rabs_lt_pos: forall x : R, 0 < Rabs x -> x <> 0.
Proof.
  intros.
  unfold Rabs in H.
  destruct (Rcase_abs x); lra.
Qed.

Theorem fop_of_rounded_binop_correct op shift errors
        (Herr: forall i (ty' : type) (k : rounding_knowledge'),
                 mget shift i = (ty', k) ->
                 Rabs (errors i) <= error_bound ty' k)
        ty e1
        (F1: is_finite _ _ e1 = true)
        env r1
        (V1: reval r1 env errors =
             B2R _ _ e1)
        e2
        (F2: is_finite _ _ e2 = true)
        r2
        (V2: reval r2 env errors = B2R _ _ e2)
        r
        (V_: reval r env errors =
            Generic_fmt.round Zaux.radix2
                                    (FLT.FLT_exp
                                       (3 - femax ty - fprec ty)
                                       (fprec ty)
                                    )
                                    (Generic_fmt.Znearest (fun x : Z => negb (Z.even x)))
                                    (reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors))
        (COND:
           (forall i,
              In i ((if is_div op
                     then (RUnop Tree.Abs r2, true) :: nil
                     else nil)) ->
              eval_cond1 env shift i))
        (NO_OVERFLOW:
           eval_cond1 env shift (no_overflow ty r))
:
  is_finite _ _ (fop_of_rounded_binop op ty e1 e2) = true /\
  B2R _ _ (fop_of_rounded_binop op ty e1 e2) =
  reval r env errors.
Proof.
  intros.
  specialize (NO_OVERFLOW _ Herr).
  simpl in NO_OVERFLOW.
  rewrite Rmult_1_l in NO_OVERFLOW.
  rewrite V_ in * |- *.
  clear r V_.
  repeat rewrite B2R_correct in *.
  destruct op;
    cbn -[Zminus] in * |- * ;
    rewrite V1 in * |- *;
    rewrite V2 in * |- *.

  {
    (* plus *)
    generalize (Bplus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
    rewrite Raux.Rlt_bool_true by (unfold round_mode; lra).
    destruct 1 as (? & ? & _).
    auto.
  }
  {
    (* minus *)
    generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
    rewrite Raux.Rlt_bool_true by (unfold round_mode; lra).
    destruct 1 as (? & ? & _).
    auto.
  }
  {
    (* mult *)
    generalize (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE e1 e2).
    rewrite Raux.Rlt_bool_true by (unfold round_mode; lra).
    rewrite F1. rewrite F2.
    simpl andb.
    destruct 1 as (? & ? & _).
    auto.
  }
  (* div *)
  generalize (fun K => Bdiv_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (div_nan _) mode_NE e1 e2 K).
  rewrite Raux.Rlt_bool_true by (unfold round_mode; lra).
  rewrite F1.
  destruct 1 as (? & ? & _).
  {
    specialize (COND _ (or_introl _ (refl_equal _))).
    simpl in COND.
    specialize (COND _ Herr).
    apply Rabs_lt_pos in COND.
    congruence.
  }
  auto.
Qed.

Theorem fop_of_rounded_unop_correct op shift errors
        (Herr: forall (i : nat) (ty' : type) (k : rounding_knowledge'),
                 mget shift i = (ty', k) ->
                 Rabs (errors i) <= error_bound ty' k)
        ty e1
        (F1: is_finite _ _ e1 = true)
        env r1
        (V1: reval r1 env errors =
             B2R _ _ e1)
        r
        (V_: reval r env errors =
            Generic_fmt.round Zaux.radix2
                                    (FLT.FLT_exp
                                       (3 - femax ty - fprec ty)
                                       (fprec ty)
                                    )
                                    (Generic_fmt.Znearest (fun x : Z => negb (Z.even x)))
                                    (reval (RUnop (Runop_of_rounded_unop op) r1) env errors))
        (COND:
           (forall i,
              In i ((if is_sqrt op
                     then (r1, false) :: nil
                     else nil)) ->
              eval_cond1 env shift i))
:
  is_finite _ _ (fop_of_rounded_unop op ty e1) = true /\
  B2R _ _ (fop_of_rounded_unop op ty e1) =
  reval r env errors.
Proof.
  intros.
  rewrite V_ in * |- *.
  clear r V_.
  repeat rewrite B2R_correct in *.
  destruct op;
    cbn -[Zminus] in * |- * ;
    rewrite V1 in * |- *.
    (* sqrt *)
    generalize (Bsqrt_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (sqrt_nan _) mode_NE e1).
    destruct 1 as (? & ? & _).
    split; auto.
    specialize (COND _ (or_introl _ (refl_equal _))).
    simpl in COND.
    specialize (COND _ Herr).
    rewrite V1 in COND.
    clear r1 V1.
    destruct e1; auto.
    destruct s; auto.
    exfalso.
    revert COND.
    clear.
    simpl.
    clear e0.
    unfold Defs.F2R.
    simpl.
    assert (0 < INR (Pos.to_nat m) * Raux.bpow Zaux.radix2 e).
    {
      apply Rmult_lt_0_compat.
      {
        apply pos_INR_nat_of_P.
      }
      apply Raux.bpow_gt_0.
    }
   rewrite INR_IZR_INZ in H.
   intro.
   replace (IZR (Z.neg m)) with (- IZR (Z.of_nat (Pos.to_nat m))) in COND.
   lra.
   rewrite <- opp_IZR.
   f_equal.
   rewrite <- Pos2Z.opp_pos.
   f_equal.
   apply positive_nat_Z.
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

Lemma FLT_format_mult_beta_n ty (x: ftype ty) n rnd
      {H: Generic_fmt.Valid_rnd rnd}:
  Generic_fmt.round
      Zaux.radix2
      (FLT.FLT_exp (3 - femax ty - fprec ty) (fprec ty))
      rnd (B2R _ _ x * Raux.bpow Zaux.radix2 (Z.of_N n)) = B2R _ _ x * Raux.bpow Zaux.radix2 (Z.of_N n).
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

Lemma FLT_format_div_beta_1 ty (x: ftype ty) n rnd
      {H: Generic_fmt.Valid_rnd rnd}:
  Raux.bpow Zaux.radix2 (3 - femax ty + Z.pos n - 1) <= Rabs (B2R _ _ x) ->
  Generic_fmt.round
      Zaux.radix2
      (FLT.FLT_exp (3 - femax ty - fprec ty) (fprec ty))
      rnd (B2R _ _ x * / Raux.bpow Zaux.radix2 (Z.pos n)) = B2R _ _ x / Raux.bpow Zaux.radix2 (Z.pos n).
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

Lemma Bdiv_beta_no_overflow' ty (x: ftype ty) n:
  is_finite _ _ x = true ->
  (n >= 0)%Z ->
  Rabs (B2R _ _ x / Raux.bpow Zaux.radix2 n) < Raux.bpow Zaux.radix2 (femax ty).
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

Lemma Bdiv_beta_no_overflow ty (x: ftype ty) n:
  is_finite _ _ x = true ->
  Rabs (B2R _ _ x / Raux.bpow Zaux.radix2 (Z.pos n)) < Raux.bpow Zaux.radix2 (femax ty).
Proof.
  intros.
  apply Bdiv_beta_no_overflow'; auto.
 lia.
Qed.

Theorem Bdiv_mult_inverse_finite ty:
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  is_finite _ _ x = true ->
  is_finite _ _ y = true ->
  is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  Bdiv _ _ _ (fprec_lt_femax ty) (div_nan ty) mode_NE x y =
  Bmult _ _ _ (fprec_lt_femax ty) (mult_nan ty) mode_NE x z .
Proof.
  intros.
  destruct (Bexact_inverse_correct _ _ _ _ _ _ H2) as (A & B & C & D & E).
  assert (HMUL :=Binary.Bmult_correct (fprec ty)  (femax ty) 
                     (fprec_gt_0 ty) (fprec_lt_femax ty) (mult_nan ty) mode_NE x z).
  assert (HDIV := Binary.Bdiv_correct  (fprec ty)  (femax ty)  
                    (fprec_gt_0 ty) (fprec_lt_femax ty) (div_nan ty) mode_NE x y D).
 unfold Rdiv in HDIV.
 rewrite <- C in HDIV.
 destruct Rlt_bool.
 -
  destruct HMUL as (P & Q & R). 
  destruct HDIV as (S & T & U).
  assert (Binary.is_finite  (fprec ty) (femax ty)
               (Binary.Bmult (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (mult_nan ty) mode_NE x z) = true) 
   by  (rewrite Q; auto;  rewrite ?andb_true_iff; auto).
  assert (Binary.is_finite (fprec ty) (femax ty)
              (Binary.Bdiv (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (div_nan ty) mode_NE x y) = true)
    by (rewrite T; auto).
  apply Binary.B2R_Bsign_inj; auto;
  rewrite ?S, ?R, ?U, ?E; auto; apply is_finite_not_is_nan; auto.
- 
  pose proof Binary.B2FF_inj _ _
       (Binary.Bdiv (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (div_nan ty) mode_NE x y)
      (Binary.Bmult (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (mult_nan ty) mode_NE x z).
  rewrite E in HMUL.
  rewrite HMUL, HDIV in *; auto.
Qed.

Theorem Bdiv_mult_inverse_nan ty:
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  is_nan _ _ x = false ->
  is_finite _ _ y = true ->
  is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  Bdiv _ _ _ (fprec_lt_femax ty) (div_nan ty) mode_NE x y =
  Bmult _ _ _ (fprec_lt_femax ty) (mult_nan ty) mode_NE x z .
Proof.
  intros.
  destruct (Bexact_inverse_correct _ _ _ _ _ _ H2) as (A & B & C & D & E).
  assert (HMUL :=Binary.Bmult_correct (fprec ty)  (femax ty) 
                     (fprec_gt_0 ty) (fprec_lt_femax ty) (mult_nan ty) mode_NE x z).
  assert (HDIV := Binary.Bdiv_correct  (fprec ty)  (femax ty)  
                    (fprec_gt_0 ty) (fprec_lt_femax ty) (div_nan ty) mode_NE x y D).
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
                   (mult_nan ty) mode_NE x z) = true) 
   by  (rewrite Q; auto;  rewrite ?andb_true_iff; auto).
  assert (Binary.is_finite (fprec ty) (femax ty)
              (Binary.Bdiv (fprec ty) (femax ty)  (fprec_gt_0 ty) (fprec_lt_femax ty) 
                   (div_nan ty) mode_NE x y) = true)
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
            (fprec_lt_femax ty) (div_nan ty) mode_NE x y)
      (Binary.Bmult (fprec ty) (femax ty) (fprec_gt_0 ty) 
            (fprec_lt_femax ty) (mult_nan ty) mode_NE x z).
  rewrite E in HMUL.
  rewrite HMUL, HDIV in *; auto.
Qed.

Theorem Bdiv_mult_inverse_equiv ty:
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  is_finite _ _ y = true ->
  is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  binary_float_equiv
  (Bdiv _ _ _ (fprec_lt_femax ty) (div_nan ty) mode_NE x y) 
  (Bmult _ _ _ (fprec_lt_femax ty) (mult_nan ty) mode_NE x z) .
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

Theorem Bdiv_mult_inverse_equiv2 ty:
  forall x1 x2 y z: (Binary.binary_float (fprec ty) (femax ty)),
  binary_float_equiv x1 x2 ->
  is_finite _ _ y = true ->
  is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  binary_float_equiv
  (Bdiv _ _ _ (fprec_lt_femax ty) (div_nan ty) mode_NE x1 y) 
  (Bmult _ _ _ (fprec_lt_femax ty) (mult_nan ty) mode_NE x2 z) .
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
  Binary.is_nan _ _ (Binary.binary_normalize prec emax H0 H1 mode m e s) = false.
Proof.
intros.
unfold Binary.binary_normalize.
destruct m; try reflexivity.
-
set (H2 := Binary.binary_round_correct _ _ _ _ _ _ _ _); clearbody H2.
set (z := Binary.binary_round prec emax mode false p e) in *.
destruct H2.
cbv zeta in y.
set (b := Rlt_bool _ _) in y.
clearbody b.
set (H2 := proj1 _).
clearbody H2.
destruct b.
+
destruct y as [? [? ?]].
destruct z; try discriminate; reflexivity.
+
unfold Binary.binary_overflow in y.
destruct (Binary.overflow_to_inf mode false);
clearbody z; subst z; reflexivity.
-
set (H2 := Binary.binary_round_correct _ _ _ _ _ _ _ _); clearbody H2.
set (z := Binary.binary_round prec emax mode true p e) in *.
destruct H2.
cbv zeta in y.
set (b := Rlt_bool _ _) in y.
clearbody b.
set (H2 := proj1 _).
clearbody H2.
destruct b.
+
destruct y as [? [? ?]].
destruct z; try discriminate; reflexivity.
+
unfold Binary.binary_overflow in y.
destruct (Binary.overflow_to_inf mode true);
clearbody z; subst z; reflexivity.
Qed.

Lemma is_nan_cast:
  forall  t1 t2 x1,
   is_nan _ _ x1 = false ->
   is_nan _ _ (cast t2 t1 x1) = false.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _).
subst t2.
apply H.
unfold Bconv.
destruct x1; try discriminate; auto.
apply is_nan_normalize.
Qed.

Lemma cast_is_nan :
  forall t1 t2 x1,
  is_nan _ _ x1 = true ->
  is_nan _ _ (cast t1 t2 x1) = true.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _).
subst t2.
apply H.
unfold Bconv.
destruct x1; try discriminate; auto.
Qed.

Lemma cast_inf tfrom tto:
  forall f,
  is_finite _ _ f = false ->
  is_finite _ _ (cast tto tfrom f) = false.
Proof.
  unfold cast.
  intros.
destruct (type_eq_dec _ _).
subst tto.
apply H.
unfold Bconv.
destruct f; try discriminate; auto.
Qed.

Lemma cast_inf_strict tfrom tto:
  forall f,
  is_finite_strict _ _ f = false ->
  is_finite_strict _ _ (cast tto tfrom f) = false.
Proof.
  unfold cast.
  intros.
destruct (type_eq_dec _ _).
subst tto.
apply H.
unfold Bconv.
destruct f; try discriminate; auto.
Qed.

Lemma cast_preserves_bf_equiv tfrom tto (b1 b2: Binary.binary_float (fprec tfrom) (femax tfrom)) :
  binary_float_equiv b1 b2 -> 
  binary_float_equiv (cast tto tfrom b1) (cast tto tfrom b2).
Proof.
intros.
destruct b1, b2; simpl; inversion H; clear H; subst; auto;
try solve [apply binary_float_eq_equiv; auto].
-
unfold cast; simpl.
destruct (type_eq_dec tfrom tto); auto.
unfold eq_rect.
destruct e1.
reflexivity.
reflexivity.
-
destruct H1; subst m0 e1.
unfold cast; simpl.
destruct (type_eq_dec tfrom tto); subst; auto.
unfold eq_rect.
simpl. split; auto.
apply binary_float_eq_equiv.
f_equal.
Qed.

Lemma binary_float_equiv_BDIV ty (b1 b2 b3 b4: binary_float (fprec ty) (femax ty)):
binary_float_equiv b1 b2 ->
binary_float_equiv b3 b4 ->
binary_float_equiv (BDIV ty b1 b3) (BDIV ty b2 b4).
Proof.
intros.
destruct b1.
all : (destruct b3; destruct b4; try contradiction; try discriminate).
all :
match goal with 
  |- context [
binary_float_equiv (BDIV ?ty ?a ?b)
 _] =>
match a with 
| B754_nan _ _ _ _ _ => destruct b2; try contradiction; try discriminate;
    cbv [BDIV BINOP Bdiv build_nan binary_float_equiv]; try reflexivity
  | _ => apply binary_float_equiv_eq in H; try rewrite <- H;
  match b with 
  | B754_nan _ _ _ _ _ => 
      cbv [BDIV BINOP Bdiv build_nan binary_float_equiv]; try reflexivity
  | _ => apply binary_float_equiv_eq in H0; try rewrite <- H0;
          try apply binary_float_eq_equiv; try reflexivity
end
end
end.
Qed.

Lemma binary_float_equiv_BOP ty (b1 b2 b3 b4: binary_float (fprec ty) (femax ty)):
forall b: binop ,
binary_float_equiv b1 b2 ->
binary_float_equiv b3 b4 ->
binary_float_equiv (fop_of_binop b ty b1 b3) (fop_of_binop b ty b2 b4).
Proof.
intros.
destruct b1.
all :
match goal with 
  |- context [
binary_float_equiv (fop_of_binop ?bo ?ty ?a ?b)
 _] =>
match a with 
| B754_zero _ _ _ => 
apply binary_float_equiv_eq in H; try simpl; try reflexivity
| B754_infinity _ _ _ => 
apply binary_float_equiv_eq in H; try simpl; try reflexivity
| B754_finite _ _ _ _ _ _ => 
apply binary_float_equiv_eq in H; try simpl; try reflexivity
| _ => try simpl
end
end.
all :(
destruct b2; simpl in H; try contradiction; try discriminate;
destruct b3; destruct b4; try contradiction; try discriminate;
match goal with 
  |- context [ binary_float_equiv (fop_of_binop ?bo ?ty ?a ?b)  _] =>
match a with 
| B754_nan _ _ _ _ _  => try simpl
| _ => try (rewrite H); 
      match b with 
      | B754_nan _ _ _ _ _ => try simpl
      | _ => try (apply binary_float_equiv_eq in H);
             try (rewrite H);
             try (apply binary_float_equiv_eq in H0);
             try (rewrite H0);
             try (apply binary_float_eq_equiv); try reflexivity
      end
end
end
).

all: (
try (destruct b);
try( cbv [fop_of_binop]);
try destruct op;
try (cbv [fop_of_rounded_binop]);
try (cbv [fop_of_rounded_binop]);
try(
match goal with 
|- context [ binary_float_equiv ((if ?m then ?op1 else ?op2)  ?ty ?a ?b) _] =>
destruct m
end;
cbv [BPLUS BMINUS BDIV BMULT BINOP 
Bplus Bminus Bdiv Bmult build_nan binary_float_equiv]);
try (reflexivity)
).
Qed.

Lemma binary_float_equiv_UOP ty (b1 b2: binary_float (fprec ty) (femax ty)):
forall u: unop ,
binary_float_equiv b1 b2 ->
binary_float_equiv (fop_of_unop u ty b1) (fop_of_unop u ty b2).
Proof.
intros.
destruct b1.
all: (
match goal with |- context [binary_float_equiv 
(fop_of_unop ?u ?ty ?a) _]  =>
match a with 
| Binary.B754_nan _ _ _ _ _  => simpl 
| _ => try apply binary_float_equiv_eq in H; try rewrite  <-H; 
  try apply binary_float_eq_equiv; try reflexivity
end
end).
destruct b2; try discriminate; try contradiction.
try (destruct u).
all: (
try( cbv [fop_of_unop fop_of_exact_unop]);
try destruct op;
try destruct o;
try destruct ltr;
try (cbv [fop_of_rounded_unop]);
try (cbv [Bsqrt Binary.Bsqrt build_nan]);
try reflexivity
).
+ destruct (B2 ty (Z.of_N pow)).
all: try (
 (cbv [ BMULT BINOP Bmult build_nan]);
 reflexivity).
+ destruct (B2 ty (- Z.pos pow)) .
all: try (
 (cbv [ BMULT BINOP Bmult build_nan]);
 reflexivity).
+ apply cast_preserves_bf_equiv; auto.
+ destruct (B2 ty (- Z.pos pow)) .
all: try (
 (cbv [ BMULT BINOP Bmult build_nan]);
 reflexivity).
Qed.

Lemma Bmult_correct_comm:
forall (prec emax : Z) (prec_gt_0_ : FLX.Prec_gt_0 prec)
         (Hmax : (prec < emax)%Z)
         (mult_nan : binary_float prec emax ->
                     binary_float prec emax -> nan_payload prec emax) 
         (m : mode) (x y : binary_float prec emax),
       if
        Raux.Rlt_bool
          (Rabs
             (Generic_fmt.round Zaux.radix2
                (FLT.FLT_exp (3 - emax - prec) prec) 
                (round_mode m)
                (B2R prec emax x * B2R prec emax y)))
          (Raux.bpow Zaux.radix2 emax)
       then
        B2R prec emax
          (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
        Generic_fmt.round Zaux.radix2
          (FLT.FLT_exp (3 - emax - prec) prec) 
          (round_mode m)
          (B2R prec emax x * B2R prec emax y) /\
        is_finite prec emax (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
        is_finite prec emax x && is_finite prec emax y /\
        (is_nan prec emax (Bmult prec emax prec_gt_0_ Hmax mult_nan m y x) =
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
elimtype False;
unfold B2, F2 in H0;
destruct (Z_lt_le_dec (e + 1) (3 - femax ty)); [ | lia];
inversion H0.
Qed.

Lemma F2R_B2F:
 forall ty x, 
    is_finite (fprec ty) (femax ty) x = true ->
    F2R radix2 (B2F x) = B2R (fprec ty) (femax ty) x.
Proof.
intros.
unfold F2R, B2R.
unfold B2F.
destruct x; auto; lra.
Qed.

Ltac spec H := match type of H with ?A -> _ => 
  let H1 := fresh in assert (H1:A); [ | specialize (H H1); clear H1]
end.

Lemma uInvShift_finite_aux:
 forall (pow : positive) (ty : type) (x : ftype ty),
   is_finite (fprec ty) (femax ty) x = true ->
  Rabs (round radix2 (FLT_exp (3 - femax ty - fprec ty) (fprec ty)) (round_mode mode_NE)
     (B2R (fprec ty) (femax ty) x * / bpow radix2 (Z.pos pow))) < bpow radix2 (femax ty).
Proof.
intros.
unfold round_mode.
pose proof (bpow_gt_0 radix2 (Z.pos pow)).
rewrite <- round_NE_abs by (apply FLT_exp_valid; apply fprec_gt_0).
rewrite Rabs_mult, Rabs_Rinv by lra.
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
rewrite Rinv_mult_distr by lra.
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

Lemma uInvShift_accuracy_aux:
  forall ty x pow, 
    is_finite (fprec ty) (femax ty) x = true ->
  Rabs (round radix2 (FLT_exp (3 - femax ty - fprec ty) (fprec ty)) (round_mode mode_NE)
        (B2R (fprec ty) (femax ty) x * bpow radix2 (- Z.pos pow)) -
            bpow radix2 (- Z.pos pow) * B2R (fprec ty) (femax ty) x) <=
           bpow radix2 (3 - femax ty - fprec ty).
Proof.
intros.
 destruct (Rle_lt_dec
    (bpow radix2 (3 - femax ty + Z.pos pow - 1))
    (Rabs (B2R (fprec ty) (femax ty) x))).
-
rewrite bpow_opp.
rewrite FLT_format_div_beta_1; auto.
2: apply valid_rnd_N.
rewrite Rmult_comm.
unfold Rdiv.
rewrite Rminus_eq_0, Rabs_R0.
pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)). lra.
-
rewrite (Rmult_comm (bpow _ _)).
unfold round_mode.
eapply Rle_trans.
apply error_le_ulp_round.
apply FLT_exp_valid; apply fprec_gt_0.
apply fexp_monotone.
apply valid_rnd_N.
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
rewrite <- round_NE_abs by (apply FLT_exp_valid; apply fprec_gt_0).
rewrite Rabs_mult.
rewrite (Rabs_right (bpow _ _)) by (apply Rgt_ge; apply bpow_gt_0).
apply Rle_lt_trans with (round  radix2 (FLT_exp emin (fprec ty)) ZnearestE (bpow radix2 (emin + fprec ty - 1))).
 *
 apply round_le.
 apply FLT_exp_valid; apply fprec_gt_0.
 apply valid_rnd_N.
 replace (emin + fprec ty - 1)%Z
  with ((3 - femax ty + Z.pos pow - 1) + (- Z.pos pow))%Z by lia.
 rewrite bpow_plus.
 apply Rmult_le_compat_r.
 apply Rlt_le. apply bpow_gt_0.
 lra.
 *
  apply Rle_lt_trans with (bpow radix2 (emin + fprec ty - 1)).
  apply round_le_generic.
 apply FLT_exp_valid; apply fprec_gt_0.
 apply valid_rnd_N.
 apply generic_format_bpow.
 unfold FLT_exp. 
 rewrite Z.max_l by lia.
 ring_simplify.
 pose proof (fprec_gt_0 ty). red in H1; lia.
 apply bpow_le. lia.
 replace (bpow radix2 (emin + fprec ty))%Z
   with (bpow radix2 (emin + fprec ty - 1 + 1))%Z by (f_equal; lia).
 rewrite bpow_plus.
 change (bpow radix2 1) with 2.
 pose proof (bpow_gt_0 radix2 (emin + fprec ty - 1) ). lra.
Qed.

Lemma uInvShift_accuracy: 
 forall (pow : positive) (ltr : bool) (ty : type) (x : ftype ty) 
  (F1 : is_finite (fprec ty) (femax ty) x = true),
 Rabs (B2R (fprec ty) (femax ty) (fop_of_unop (uInvShift pow ltr) ty x) -
      F2R radix2 (B2F (B2 ty (Z.neg pow))) * B2R (fprec ty) (femax ty) x) <=
   bpow radix2 (3 - femax ty - fprec ty).
Proof.
intros.
assert (is_finite (fprec ty) (femax ty) (B2 ty (Z.neg pow)) = true). {
  apply B2_finite.
  pose proof (fprec_lt_femax ty).
  pose proof (fprec_gt_0 ty).
  red in H0.
  lia.
} 
simpl fop_of_unop.
destruct ltr.
-
   destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty)).
  + rewrite (B2_zero ty (Z.neg pow)) in * by auto.
     simpl B2R. clear H l.
    unfold BMULT, BINOP.
    pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)).
    set (j := bpow radix2 _) in *. clearbody j.
    destruct x; try discriminate; simpl; rewrite ?Rmult_0_l, Rminus_0_r, Rabs_R0; lra.     
  +
    assert (H2 := Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    unfold BMULT, BINOP.
    rewrite F2R_B2F by auto.
    rewrite (B2_correct ty (Z.neg pow) ltac:(lia)) in *.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; clear H4]. 
  * apply Rlt_bool_true.
   apply  uInvShift_finite_aux; auto.
  * destruct H2 as [H2 _].
    rewrite H2. clear H2.
    apply uInvShift_accuracy_aux; auto.
- 
   destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty)).
  + rewrite (B2_zero ty (Z.neg pow)) in * by auto.
     simpl B2R. clear H l.
    unfold BMULT, BINOP.
    pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)).
    set (j := bpow radix2 _) in *. clearbody j.
    destruct x; try discriminate; simpl; rewrite ?Rmult_0_l, Rminus_0_r, Rabs_R0; lra.     
  +
    assert (H2 := Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    unfold BMULT, BINOP.
    rewrite F2R_B2F by auto.
    rewrite (B2_correct ty (Z.neg pow) ltac:(lia)) in *.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; clear H4]. 
  * apply Rlt_bool_true.
   apply  uInvShift_finite_aux; auto.
  * destruct H2 as [H2 _].
    rewrite H2. clear H2.
    apply uInvShift_accuracy_aux; auto.
Qed.

Lemma uInvShift_finite: 
 forall (pow : positive) (ltr : bool) (ty : type) (x : ftype ty) 
  (F1 : is_finite (fprec ty) (femax ty) x = true),
 is_finite (fprec (type_of_unop (uInvShift pow ltr) ty)) (femax (type_of_unop (uInvShift pow ltr) ty))
  (fop_of_unop (uInvShift pow ltr) ty x) = true.
Proof.
intros.
simpl.
pose proof (fprec_lt_femax ty).
pose proof (fprec_gt_0 ty).
red in H0.
pose proof (B2_finite ty (Z.neg pow) ltac:(lia)).
unfold BMULT, BINOP.
destruct ltr; destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty));
  unfold Datatypes.id.
- rewrite (B2_zero _ _ l); unfold Bmult. destruct x; auto.
- 
    pose proof (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    pose proof (B2_correct ty (Z.neg pow) ltac:(lia)).
   rewrite H3 in H2.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite F1, H1, Raux.bpow_opp in H2. simpl andb in H2.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; apply H2].
     apply Rlt_bool_true.
   apply  uInvShift_finite_aux; auto.
- rewrite (B2_zero _ _ l); unfold Bmult. destruct x; auto.
- 
    pose proof (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    pose proof (B2_correct ty (Z.neg pow) ltac:(lia)).
   rewrite H3 in H2.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite F1, H1, Raux.bpow_opp in H2. simpl andb in H2.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; apply H2].
     apply Rlt_bool_true.
   apply  uInvShift_finite_aux; auto.
Qed.

Lemma rndval_with_cond_correct_uInvShift:
forall (env : forall x : type, V -> binary_float (fprec x) (femax x))
 (Henv : forall (ty : type) (i : V),  is_finite (fprec ty) (femax ty) (env ty i) = true)
(pow : positive)
 (ltr : bool) (e : expr) (si : nat) (r1 : rexpr) (s1 : MSHIFT)
 (errors1 errors1_1 : nat -> R)
 (E1 : forall i : nat, (i < si)%nat -> errors1_1 i = errors1 i)
 (EB1 : forall (i : nat) (ty' : type) (k : rounding_knowledge'),
      mget s1 i = (ty', k) -> Rabs (errors1_1 i) <= error_bound ty' k)
 (F1 : is_finite (fprec (type_of_expr e)) (femax (type_of_expr e)) (fval env e) = true)
 (V1 : reval r1 env errors1_1 =
         B2R (fprec (type_of_expr e)) (femax (type_of_expr e)) (fval env e))
 (H0 : expr_valid e = true)
 (shift : MSHIFT) (r : rexpr) (si2 : nat) (s : MSHIFT) (si1 : nat) (p1 : list cond) 
 (EQ1 : rndval_with_cond si shift e = (r1, (si1, s1), p1))
 (p_ : list (rexpr * bool))
  (EQ : rnd_of_unop_with_cond si1 s1 (type_of_expr e) (uInvShift pow ltr) r1 =
     (r, (si2, s), p_))
 (H1 : forall i : cond, In i (p_ ++ p1) -> eval_cond1 env s i) 
 (H2 : forall (i : nat) (ty : type) (k : rounding_knowledge'),
     mget shift i = (ty, k) -> Rabs (errors1 i) <= error_bound ty k)
 (K_ : rnd_of_unop si1 s1 (type_of_expr e) (uInvShift pow ltr) r1 = (r, (si2, s))),
exists errors2 : nat -> R,
  (forall i : nat, (i < si)%nat -> errors2 i = errors1 i) /\
  (forall (i : nat) (ty' : type) (k : rounding_knowledge'),
   mget s i = (ty', k) -> Rabs (errors2 i) <= error_bound ty' k) /\
  is_finite (fprec (type_of_unop (uInvShift pow ltr) (type_of_expr e)))
    (femax (type_of_unop (uInvShift pow ltr) (type_of_expr e)))
    (fop_of_unop (uInvShift pow ltr) (type_of_expr e) (fval env e)) = true /\
  reval r env errors2 =
  B2R (fprec (type_of_unop (uInvShift pow ltr) (type_of_expr e)))
    (femax (type_of_unop (uInvShift pow ltr) (type_of_expr e)))
    (fop_of_unop (uInvShift pow ltr) (type_of_expr e) (fval env e)).
Proof.
intros.
assert (K1 := rndval_with_cond_left e si shift); rewrite EQ1 in K1; simpl in K1; symmetry in K1.
inversion EQ; clear EQ; subst.
set (op := RBinop Tree.Mul _) in *.
set (s := mset s1 si1 (type_of_expr e, Denormal')) in *.
pose (eps :=
  B2R (fprec (type_of_expr e)) (femax (type_of_expr e))
    (fop_of_unop (uInvShift pow ltr) (type_of_expr e) (fval env e)) -
  F2R radix2 (B2F (B2 (type_of_expr e) (Z.neg pow))) * reval r1 env errors1_1).
pose (errors2 i := if Nat.eq_dec i si1  then eps else errors1_1 i).
exists errors2.
split; [ | split; [ | split]].
-
intros. unfold errors2.
destruct (Nat.eq_dec i si1); auto.
pose proof (rndval_shift_incr _ _ _ _ _ _ K1). lia.
-
subst errors2.
simpl.
intros.
subst s; simpl in H.
rewrite (mget_set Nat.eq_dec) in H.
destruct (Nat.eq_dec i si1). inversion H; clear H; subst.
 +
  unfold error_bound.
  subst eps.
  rewrite V1.
 rewrite bpow_plus.
 rewrite <- Rmult_assoc.
 change (bpow radix2 1) with 2.
 rewrite Rinv_l, Rmult_1_l by lra.
 apply uInvShift_accuracy; auto.
 +
  clear eps.
  destruct (le_lt_dec si i).
 *
  apply EB1; auto.
 *  rewrite E1 by auto. apply H2.
   rewrite <- H.
   symmetry; eapply rndval_shift_unchanged; eauto.
- apply uInvShift_finite; auto.
-
 subst op. unfold reval; fold reval.
 replace (reval r1 env errors2) with (reval r1 env errors1_1).
2:{
   apply reval_error_ext; intros.
   unfold errors2.
 destruct (Nat.eq_dec i si1); auto.
  subst i.
  pose proof (rndval_shift_le _ _ _ _ _ _ K1). lia.
}
  subst errors2.
  subst eps.
  rewrite V1.
  simpl.
  destruct (Nat.eq_dec si1 si1) as [ _ |]; [ | congruence].
  set (a := F2R _ _).
  set (b := B2R _ _ _).
  set (c := B2R _ _ _).
  ring.
Qed.

Theorem rndval_with_cond_correct env (Henv: forall ty i, is_finite _ _ (env ty i) = true) e:
  expr_valid e = true ->
  forall si shift r si2 s p,
    rndval_with_cond si shift e = ((r, (si2, s)), p) ->
    (forall i, In i p -> eval_cond1 env s i) ->
    forall errors1,
      (forall i ty k,
         mget shift i = (ty, k) ->
         Rabs (errors1 i) <= error_bound ty k) ->
      exists errors2,
        (forall i,
           (i < si)%nat ->
           errors2 i = errors1 i)
        /\
        (forall i ty' k,
           mget s i = (ty', k) ->
           Rabs (errors2 i) <= error_bound ty' k)
        /\
        let fv := fval env e in
        is_finite _ _ fv = true
        /\
        reval r env errors2 = B2R _ _ fv
.
Proof.
  induction e; intros.
-  (* const *)
    simpl in *.
    inversion H0; clear H0; subst.
    simpl.
    exists errors1.
    split; auto.
    split; auto.
    split; auto.
    symmetry.
    rewrite F2R_eq.
    apply B2F_F2R_B2R.
- (* var *)
    simpl in *.
    inversion H0; clear H0; subst.
    eauto.
-  (* binop *)
    simpl in *.
    destruct (rndval_with_cond si shift e1) as [[r1 [si1 s1]] p1] eqn:EQ1.
    destruct (rndval_with_cond si1 s1 e2) as [[r2 [si2_ s2]] p2] eqn:EQ2.
    destruct (rnd_of_binop_with_cond si2_ s2 (type_lub (type_of_expr e1) (type_of_expr e2)) b r1 r2) as [rs p_] eqn:EQ.
    inversion H0; clear H0; subst.
    rewrite andb_true_iff in H.
    destruct H.

    assert (K1 := rndval_with_cond_left e1 si shift).
    rewrite EQ1 in K1.
    symmetry in K1.
    simpl in K1.
    generalize (rndval_with_cond_left e2 si1 s1).
    rewrite EQ2.
    intro K2.
    symmetry in K2.
    simpl in K2.
    generalize (rnd_of_binop_with_cond_left si2_ s2 (type_lub (type_of_expr e1) (type_of_expr e2)) b r1 r2).
    intro K_.
    rewrite EQ in K_.
    simpl in K_.
    symmetry in K_.

   assert (N : forall i : cond, In i p1 -> eval_cond1 env s1 i).
    {
      intros. 
      apply (eval_cond1_preserved s).
      {
        intros.
        subst.
        symmetry.
        etransitivity.
        {
          eapply rnd_of_binop_shift_unchanged; eauto.
          eapply lt_le_trans; [ eassumption | ].
          etransitivity.
          eapply rndval_with_cond_shift_cond; [ | eassumption ] ; eauto.
          eapply rndval_shift_incr; eauto.
        }
        eapply rndval_shift_unchanged; eauto.
        eapply lt_le_trans; [ eassumption | ].
        eapply rndval_with_cond_shift_cond; eauto.
      }
      apply H1. apply in_or_app. right. apply in_or_app. auto.
    }
    specialize (IHe1 H _ _ _ _ _ _ EQ1 N _ H2).
    clear N.
    destruct IHe1 as (errors1_1 & E1 & EB1 & F1 & V1).
    assert (N : forall i : cond, In i p2 -> eval_cond1 env s2 i).
    {
      intros.
      apply (eval_cond1_preserved s).
      {
        intros.
        subst.
        symmetry.
        eapply rnd_of_binop_shift_unchanged; eauto.
        eapply lt_le_trans; [ eassumption | ].
        eapply rndval_with_cond_shift_cond; [ | eassumption ] ; eauto.
      }
      apply H1. apply in_or_app. right. apply in_or_app. auto.
    }
    specialize (IHe2 H0 _ _ _ _ _ _ EQ2 N _ EB1).
    clear N.
    destruct IHe2 as (errors1_2 & E2 & EB2 & F2 & V2).

    generalize (cast_finite _ _ (type_lub_left _ (type_of_expr e2)) _ F1).
    generalize (cast_eq _ _ (type_lub_left _ (type_of_expr e2)) _ F1).
    clear F1.
    rewrite <- V1.
    clear V1.
    intros V1 F1.
    generalize (cast_finite _ _ (type_lub_right (type_of_expr e1) _) _ F2).
    generalize (cast_eq _ _ (type_lub_right (type_of_expr e1) _) _ F2).
    clear F2.
    rewrite <- V2.
    clear V2.
    intros V2 F2.
    symmetry in V1.
    symmetry in V2.

    rewrite <- (reval_error_ext errors1_2) in V1
     by (intros; apply E2; eapply lt_le_trans; [ eassumption | eapply rndval_shift_le; eauto]).
    destruct b.
   + (* rounded binary operator *)
        simpl.
        simpl in EQ.
        destruct (
            make_rounding si2_ s2 (round_knowl_denote knowl)
                          (type_lub (type_of_expr e1) (type_of_expr e2))
                          (RBinop (Rbinop_of_rounded_binop op) r1 r2)
          ) eqn:ROUND.
        inversion EQ; clear EQ; subst.
        simpl.

        generalize (make_rounding_correct _ _ _ _ _ _ _ _ ROUND).
        intro K.
        simpl max_error_var in K.
        assert (L: (Nat.max (max_error_var r1) (max_error_var r2) <= si2_)%nat).
        {
          intros.
          apply Nat.max_lub.
          {
            eapply le_trans; [ eapply rndval_shift_le; eauto | ].
            eapply rndval_shift_incr; eauto.
          }
          eapply rndval_shift_le; eauto.
        }
        specialize (K L _ EB2).
        clear L.
        assert (L: rounding_cond (type_lub (type_of_expr e1) (type_of_expr e2)) (round_knowl_denote knowl)
                            (reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors1_2)).
        {
          eapply rounding_cond_ast_correct; [ eassumption | ].
          intros.
          eapply (eval_cond1_preserved s).
          {
            intros.
            subst.
            symmetry.
            apply rounding_cond_ast_shift in H3.
            simpl in H3.
            
            eapply make_rounding_shift_unchanged; eauto.
            eapply lt_le_trans; eauto.
            etransitivity; try eassumption.
            apply Max.max_lub; eauto using rndval_shift_le.
            etransitivity; [ eapply rndval_shift_le; eauto | ].
            eapply rndval_shift_incr; eauto.
          }
          eapply H1. apply in_or_app. left. apply in_or_app. right. right. assumption.
        }
        specialize (K _ L (fun x : Z => negb (Z.even x))).
        clear L.
        destruct K as (errors2 & E & R & EB).
        assert (W1: reval r1 env errors2 = reval r1 env errors1_2). {
          apply reval_error_ext.
          intros.
          apply E.
          eapply lt_le_trans; [ eassumption | ].
          etransitivity; [ eapply rndval_shift_le; eauto | ].
          eapply rndval_shift_incr; eauto.
        }

        assert (W2: reval r2 env errors2 = reval r2 env errors1_2). {
          apply reval_error_ext.
          intros.
          apply E.
          eapply lt_le_trans; [ eassumption | ].
          eapply rndval_shift_le; eauto.
        }
        rewrite <- W1, <- W2 in *.
        assert (
            reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors1_2
            =
            reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors2
        ) as W.
        {
          simpl.
          congruence.
        }
        rewrite W in * |- *. clear W.

        assert (L : forall i : rexpr * bool,
             In i (if is_div op then (RUnop Tree.Abs r2, true) :: nil else nil) ->
             eval_cond1 env s i).
        {
          intros.
          apply H1.
          apply in_or_app.
          left.
          apply in_or_app.
          auto.
        }
       assert (L': eval_cond1 env s
            (no_overflow (type_lub (type_of_expr e1) (type_of_expr e2)) r)).
        {
          apply H1.
          apply in_or_app.
          left.
          apply in_or_app.
          right.
          left.
          auto.
        }

        assert (K := fop_of_rounded_binop_correct _ _ _ EB 
                                                 _ _ F1
                                                 _ _ V1
                                                 _ F2
                                                 _ V2
                                                 _ R L L').
        clear L L'.

        destruct K.
        exists errors2.
        split; auto.
        intros.
        etransitivity.
        {
          eapply E.
          eapply lt_le_trans; [ eassumption | ].
          etransitivity; [ eapply rndval_shift_incr; eauto | ].
          eapply rndval_shift_incr; eauto.
        }
        etransitivity.
        {
          eapply E2.
          eapply lt_le_trans; [ eassumption | ].
          eapply rndval_shift_incr; eauto.
        }
        eauto.
    + (* Sterbenz *)      
        simpl.
        simpl in EQ.
        inversion EQ; clear EQ; subst.
        simpl.
        generalize (H1 _ (or_introl _ (refl_equal _))).
        specialize (fun j K => H1 j (or_intror _ K)).
        specialize (H1 _ (or_introl _ (refl_equal _))).
        simpl in H1 |- * .
        intro H1'.
        rewrite Rmult_1_l in *.
        specialize (H1 _ EB2).
        specialize (H1' _ EB2).

        generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
        intro K.
        change ( Z.pos
                   (fprecp (type_lub (type_of_expr e1) (type_of_expr e2))))
        with (
          fprec (type_lub (type_of_expr e1) (type_of_expr e2))
        ) in K.
        rewrite <- V1 in K.
        rewrite <- V2 in K.
        rewrite Generic_fmt.round_generic in K; try typeclasses eauto.
        {
          destruct (Rlt_dec
                      (Rabs (reval r1 env errors1_2 - reval r2 env errors1_2))
                      (Raux.bpow Zaux.radix2
                                       (femax (type_lub (type_of_expr e1) (type_of_expr e2))))
                   ).
          {
            apply Raux.Rlt_bool_true in r.
            rewrite r in K.
            destruct K as (KR & KF & _).
            exists errors1_2.
            split; auto.
            intros.
            etransitivity.
            {
              eapply E2.
              eapply lt_le_trans; [ eassumption | ].
              eapply rndval_shift_incr; eauto.
            }
            auto.
          }
          exfalso.
          pose proof 
          (abs_B2R_lt_emax _ _
            (cast (type_lub (type_of_expr e1) (type_of_expr e2)) 
                  (type_of_expr e1) (fval env e1))).
          pose proof 
          (abs_B2R_lt_emax _ _
            (cast (type_lub (type_of_expr e1) (type_of_expr e2)) 
                  (type_of_expr e2) (fval env e2))).
          rewrite <- V1 in H3.
          rewrite <- V2 in H4.
          apply Raux.Rabs_lt_inv in H3.
          apply Raux.Rabs_lt_inv in H4.
          generalize (sterbenz_no_overflow _ _ _ H3 H4 H1 H1').
          clear K.
          intro K.
          apply Raux.Rabs_lt in K.
          contradiction.
        }
        apply Sterbenz.sterbenz; try typeclasses eauto.
        * rewrite V1. apply generic_format_B2R.
        * rewrite V2. apply generic_format_B2R.
        * lra.

    + (* plus zero *)
        simpl.
        simpl in EQ.
        inversion EQ; clear EQ; subst.
        simpl.
        specialize (H1 _ (or_introl _ (refl_equal _))).
        simpl in H1 |- * .
        specialize (H1 _ EB2).        
        exists errors1_2.
        split.
        *
          intros.
          etransitivity.
          {
            eapply E2.
            eapply lt_le_trans; [ eassumption | ].
            eapply rndval_shift_incr; eauto.
          }
          eauto.
        * split; auto.
         assert (reval (if zero_left then r1 else r2) env errors1_2 = 0) as ZERO.
         {
          rewrite <- Rabs_zero_iff.
          apply Rle_antisym; [lra | ].
          apply Rabs_pos.
         }
         destruct zero_left.
         {
          rewrite V1 in ZERO.
          pose proof (abs_B2R_lt_emax _ _
          (cast (type_lub (type_of_expr e1) (type_of_expr e2)) 
            (type_of_expr e2) (fval env e2))).
          destruct minus.
          {
            generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
            rewrite ZERO.
            rewrite Rminus_0_l.
            rewrite Generic_fmt.round_opp.
            rewrite Generic_fmt.round_generic; try typeclasses eauto.
            {
              rewrite Rabs_Ropp.
              rewrite Raux.Rlt_bool_true by assumption.
              unfold BMINUS.
              unfold BINOP.
              simpl reval.
              destruct 1 as (BV & BF & _).
              simpl femax in BV, BF |- * .
              unfold cast_lub_l.
              unfold cast_lub_r.
              rewrite BV.
              intuition.
            }
            apply generic_format_B2R.
          }
          generalize (Bplus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
          rewrite ZERO.
          rewrite Rplus_0_l.
          rewrite Generic_fmt.round_generic; try typeclasses eauto.
          {
            rewrite Raux.Rlt_bool_true by assumption.
            unfold BPLUS.
            unfold BINOP.
            simpl reval.
            destruct 1 as (BV & BF & _).
            simpl femax in BV, BF |- * .
            unfold cast_lub_l.
            unfold cast_lub_r.
            rewrite BV.
            intuition.
          }
          apply generic_format_B2R.          
        }
        rewrite V2 in ZERO.
        pose proof (abs_B2R_lt_emax _ _
        (cast (type_lub (type_of_expr e1) (type_of_expr e2)) 
          (type_of_expr e1) (fval env e1))).
        destruct minus.
        {
          generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
          rewrite ZERO.
          rewrite Rminus_0_r.
          rewrite Generic_fmt.round_generic; try typeclasses eauto.
          {
            rewrite Raux.Rlt_bool_true by assumption.
            unfold BMINUS.
            unfold BINOP.
            simpl reval.
            destruct 1 as (BV & BF & _).
            simpl femax in BV, BF |- * .
            unfold cast_lub_l.
            unfold cast_lub_r.
            rewrite BV.
            intuition.
          }
          apply generic_format_B2R.
        }
        generalize (Bplus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) mode_NE _ _ F1 F2).
        rewrite ZERO.
        rewrite Rplus_0_r.
        rewrite Generic_fmt.round_generic; try typeclasses eauto.
        {
          rewrite Raux.Rlt_bool_true by assumption.
          unfold BPLUS.
          unfold BINOP.
          simpl reval.
          destruct 1 as (BV & BF & _).
          simpl femax in BV, BF |- * .
          unfold cast_lub_l.
          unfold cast_lub_r.
          rewrite BV.
          intuition.
        }
        apply generic_format_B2R.          

- (* unop *)
  simpl in *.
  destruct (rndval_with_cond si shift e) as [[r1 [si1 s1]] p1] eqn:EQ1.
  destruct (rnd_of_unop_with_cond si1 s1 (type_of_expr e) u r1) as [rs p_] eqn:EQ.
  inversion H0; clear H0; subst.
  rewrite andb_true_iff in H.
  destruct H.

  generalize (rndval_with_cond_left e si shift).
  rewrite EQ1.
  intro K1.
  symmetry in K1.
  simpl in K1.
  generalize (rnd_of_unop_with_cond_left si1 s1 (type_of_expr e) u r1).
  rewrite EQ.
  simpl.
  intro K_.
  symmetry in K_.

  assert (N: forall i : cond, In i p1 -> eval_cond1 env s1 i).
  {
    intros.
    apply (eval_cond1_preserved s).
    {
      intros; subst.
      symmetry.
      eapply rnd_of_unop_shift_unchanged; eauto.
      eapply lt_le_trans; eauto.
      eapply rndval_with_cond_shift_cond; eauto.
    }
    apply H1. apply in_or_app. auto.
  }
  specialize (IHe H0 _ _ _ _ _ _ EQ1 N _ H2).
  clear N.
  destruct IHe as (errors1_1 & E1 & EB1 & F1 & V1).

  destruct u.
 + (* rounded unary operator *)
    simpl.
    simpl in EQ.
    unfold Datatypes.id in *.
    destruct (
        make_rounding si1 s1 (round_knowl_denote knowl)
                      (type_of_expr e)
                      (RUnop (Runop_of_rounded_unop op) r1)
      ) eqn:ROUND.
    inversion EQ; clear EQ; subst.

    assert (K := make_rounding_correct _ _ _ _ _ _ _ _ ROUND).
    simpl max_error_var in K.
    assert (L:  (max_error_var r1 <= si1)%nat).
    {
      intros.
      eapply rndval_shift_le; eauto.
    }
    assert (L': rounding_cond (type_of_expr e) (round_knowl_denote knowl)
      (reval (RUnop (Runop_of_rounded_unop op) r1) env errors1_1)).
    {
      eapply rounding_cond_ast_correct; [ eassumption | ].
      intros.
      eapply (eval_cond1_preserved s).
      {
        intros; subst.
        symmetry.
        apply rounding_cond_ast_shift in H3.
        simpl in H3.
        eapply rnd_of_unop_shift_unchanged; eauto.
        eapply lt_le_trans; eauto.
        etransitivity; try eassumption.
      }
      eapply H1.
      apply in_or_app.
      left.
      apply in_or_app.
      right.
      assumption.
    }
    specialize (K L _ EB1 _ L' (fun x : Z => negb (Z.even x))).
    clear L L'.
    destruct K as (errors2 & E & R & EB).

    assert (W1: reval r1 env errors2 = reval r1 env errors1_1).
    {
      apply reval_error_ext.
      intros.
      apply E.
      eapply lt_le_trans; [ eassumption | ].
      eapply rndval_shift_le; eauto.
    }
    rewrite <- W1 in V1.

    assert (
        reval (RUnop (Runop_of_rounded_unop op) r1) env errors1_1
        =
        reval (RUnop (Runop_of_rounded_unop op) r1) env errors2
      ) as W.
    {
      simpl.
      congruence.
    }
    rewrite W in * |- *. clear W.

   assert (L : forall i : rexpr * bool,
     In i (if is_sqrt op then (r1, false) :: nil else nil) ->
     eval_cond1 env s i).
    {
      intros.
      apply H1.
      apply in_or_app.
      left.
      apply in_or_app.
      auto.
    }
    assert (K := fop_of_rounded_unop_correct _ _ _ EB 
                                             _ _ F1
                                             _ _ V1
                                             _ R L).
    clear L.

    destruct K.
    exists errors2.
    split; auto.
    intros.
    etransitivity.
    {
      eapply E.
      eapply lt_le_trans; [eassumption | ].
      eapply rndval_shift_incr; eauto.
    }
    eauto.

 + (* exact unary operator *)

    simpl.
    cbn -[Zminus] in EQ.
    unfold Datatypes.id in *.
    Opaque Zminus.
    inversion EQ; clear EQ; subst.
    Transparent Zminus.

    exists errors1_1.
    split; auto.
    split; auto.

    destruct o.

   * (* abs *)
      simpl in * |- *.
      unfold BABS.
      rewrite is_finite_Babs.
      split; auto.
      rewrite B2R_Babs.
      congruence.

   * (* opp *)
      simpl in * |- * .
      unfold BOPP.
      rewrite is_finite_Bopp.
      split; auto.
      rewrite B2R_Bopp.
      congruence.

   * (* shift *)
      cbn -[Zminus] in * |- *.
      rewrite F2R_eq.
      rewrite <- B2F_F2R_B2R.
      rewrite Z.leb_le in H.
      apply center_Z_correct in H.
      generalize (B2_finite (type_of_expr e) (Z.of_N pow) (proj2 H)).
      intro B2_FIN.
      generalize
          (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 (type_of_expr e) (Z.of_N pow)) (fval env e)).
      generalize
         (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 (type_of_expr e) (Z.of_N pow)) (fval env e)).
      rewrite Rmult_comm.
      replace (Z.of_N (pow + 1)) with (Z.of_N pow + 1)%Z in H by (rewrite N2Z.inj_add; simpl; ring).
      assert (K := B2_correct _ _ H).
      rewrite K.
      rewrite FLT_format_mult_beta_n; try typeclasses eauto.
      rewrite F1.
      rewrite B2_FIN.
      simpl andb.
      rewrite Raux.Rlt_bool_true.
      {
        unfold BMULT, BINOP.
        destruct 1 as (LC & ? & ?).
        destruct 1 as (L & ? & ?).        
        destruct ltr; split; auto; rewrite V1.
        {
          rewrite LC.
          ring.
        }
        rewrite L.
        ring.
      }
      specialize (H1 _ (or_introl _ (refl_equal _))).
      specialize (H1 _ EB1).
      simpl in H1.
      rewrite F2R_eq in H1.
      rewrite <- B2F_F2R_B2R in H1.
      rewrite V1 in H1.
      rewrite K in H1.
      rewrite Rmult_comm.
      lra.

  * (* invshift *)
    cbn -[Zminus] in * |- *.
    rewrite F2R_eq.
    rewrite <- B2F_F2R_B2R.
    rewrite Z.leb_le in H.
    apply center_Z_correct in H.
    assert (B2_FIN := B2_finite (type_of_expr e) (Z.neg pow) (proj2 H)).
    generalize (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 (type_of_expr e) (Z.neg pow)) (fval env e)).
    generalize (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) mode_NE (B2 (type_of_expr e) (Z.neg pow)) (fval env e)).
    rewrite Rmult_comm.
    generalize (B2_correct _ (Z.neg pow) H).
    repeat rewrite B2R_correct.
    intro K.
    rewrite K.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite Raux.bpow_opp.
    rewrite FLT_format_div_beta_1; try typeclasses eauto.
    {
      unfold Rdiv.
      rewrite <- Raux.bpow_opp.
      rewrite F1.
      rewrite B2_FIN.
      simpl andb.
      rewrite Raux.Rlt_bool_true.
      {
        unfold BMULT, BINOP.
        destruct 1 as (LC & ? & ?).
        destruct 1 as (L & ? & ?).
        destruct ltr; split; auto; rewrite V1.
        {
          rewrite LC.
          ring.
        }
        rewrite L.
        ring.
      }
      rewrite Raux.bpow_opp.
      apply Bdiv_beta_no_overflow.
      assumption.
    }
    specialize (H1 _ (or_introl _ (refl_equal _))).
    specialize (H1 _ EB1).
    cbn -[Zminus] in H1.
    rewrite <- V1.
    lra.

 + (* cast *)
  simpl.
  simpl in *.
  unfold cast.
  unfold rnd_of_cast_with_cond in EQ.
  destruct (type_eq_dec (type_of_expr e) ty).
  {
    subst ty.
    simpl.
    rewrite (fun t1 t2 => let (_, K) := type_leb_le t1 t2 in K) in EQ.
    {
      inversion EQ; clear EQ; subst.
      eauto.
    }
    apply type_le_refl.
  }
  destruct (type_leb (type_of_expr e) ty) eqn:LEB.
  {
    inversion EQ; clear EQ; subst.
    rewrite type_leb_le in LEB.
    inversion LEB.
    generalize ((fun J1 =>
                  Bconv_widen_exact _ _ _ _ J1 (fprec_gt_0 _) (fprec_lt_femax _) (Z.le_ge _ _ H3) (Z.le_ge _ _ H4) (conv_nan _ _) mode_NE _ F1) ltac:( typeclasses eauto ) ).
    destruct 1 as (K & L & _).
    symmetry in K.
    rewrite <- V1 in K.
    eauto.
  }
  destruct (make_rounding si1 s1 (round_knowl_denote knowl) ty r1) eqn:ROUND.
  inversion EQ; clear EQ; subst.
  generalize (make_rounding_correct _ _ _ _ _ _ _ _ ROUND).
  intro K.
  assert (L: (max_error_var r1 <= si1)%nat).
  {
    eapply rndval_shift_le; eauto.
  }
  assert (L': rounding_cond ty (round_knowl_denote knowl) (reval r1 env errors1_1)).
  {
    eapply rounding_cond_ast_correct.
    {
      eassumption.
    }
    intros.
    eapply (eval_cond1_preserved s).
    {
      intros; subst.
      symmetry.
      apply rounding_cond_ast_shift in H3.
      simpl in H3.
      eapply make_rounding_shift_unchanged; eauto.
      eapply lt_le_trans; eauto.
      etransitivity; try eassumption.
    }
    eapply H1.
    apply in_or_app.
    left.
    right.
    assumption.
  } 
  specialize (K L _ EB1 _ L'  (fun x : Z => negb (Z.even x))); clear L L'.
  destruct K as (errors2 & E & R & EB).
  rewrite V1 in R.
  generalize (Bconv_correct _ _ _ _ (fprec_gt_0 _) (fprec_lt_femax ty) (conv_nan _ _) mode_NE _ F1).
  unfold round_mode.
  rewrite <- R.
  rewrite Raux.Rlt_bool_true.
  {
    destruct 1 as (J & K & _).
    symmetry in J.
    exists errors2.
    split; auto.
    intros.
    etransitivity.
    {
      eapply E.
      eapply lt_le_trans; eauto.
      eapply rndval_shift_incr; eauto.
    }
    auto.
  }
  specialize (H1 _ (or_introl _ (refl_equal _))).
  specialize (H1 _ EB).
  simpl in H1.
  lra.
 + (* uInvShift *)
 eapply rndval_with_cond_correct_uInvShift; eassumption.
Qed.

End WITHMAP.

End WITHVAR.

Section TEST.

Local Program Instance map_nat: MapIndex nat :=
  {
    index_of_tr := Pos.of_succ_nat
  }.
Next Obligation.
  generalize SuccNat2Pos.inj_iff.
  clear.
  firstorder.
Defined.

Local Existing Instances compcert_map.

Definition Tsingle := TYPE 24 128 I I.
Definition Tdouble := TYPE 53 1024 I I.


(* OK
Definition sqrt_of_two : @expr ident := Unop (Rounded1 SQRT None) (Const Tsingle (B2 _ 0)).
Eval simpl in rndval 0 (Maps.PMap.init 0) sqrt_of_two.
Eval simpl in rndval_with_cond 0 (Maps.PMap.init 0) sqrt_of_two.
*)


End TEST.
