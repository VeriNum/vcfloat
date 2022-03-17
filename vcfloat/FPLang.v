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
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Require Export vcfloat.FPCore.
Import Bool.

Global Existing Instance fprec_gt_0. (* to override the Opaque one in Interval package *)

Local Open Scope R_scope.

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
| InvShift (pow: positive) (ltr: bool) (* divide by power of two *)
.

Inductive exact_unop: Type :=
| Abs
| Opp
| Shift (pow: N) (ltr: bool) (* multiply by power of two never introduces rounding *)
.

Inductive unop: Type :=
| Rounded1 (op: rounded_unop) (knowl:  option rounding_knowledge)
| Exact1 (o: exact_unop)
| CastTo (ty: type) (knowl: option rounding_knowledge)
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
    | InvShift pow _ => Rmult (Raux.bpow Zaux.radix2 (- Z.pos pow))
  end.

Definition Rop_of_exact_unop (r: exact_unop): R -> R :=
  match r with
    | Abs => Rabs
    | Opp => Ropp
    | Shift pow b =>
      Rmult (Raux.bpow Zaux.radix2 (Z.of_N pow))
  end.

Definition Rop_of_unop (r: unop): R -> R :=
  match r with
    | Rounded1 op _ => Rop_of_rounded_unop op
    | Exact1 op => Rop_of_exact_unop op
    | CastTo _ _ => id
  end.

Fixpoint rval (env: forall ty, V -> ftype ty) (e: expr) {struct e}: R :=
  match e with
    | Const ty f => B2R (fprec ty) (femax ty) f
    | Var ty i => B2R (fprec ty) (femax ty) (env ty i)
    | Binop b e1 e2 =>  Rop_of_binop b (rval env e1) (rval env e2)
    | Unop b e => Rop_of_unop b (rval env e)
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

Definition unop_valid ty (u: unop): bool :=
  match u with
    | Exact1 (Shift p _) => 
      Z.leb 0 (center_Z (3 - femax ty) (Z.of_N p + 1) (femax ty))
    | Rounded1 (InvShift p _) _ =>
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

Definition fop_of_rounded_unop (r: rounded_unop):
  forall ty,
    binary_float (fprec ty) (femax ty) ->
    binary_float (fprec ty) (femax ty)
  :=
    match r with
      | SQRT => Bsqrt
      | InvShift n b => 
        if b
        then (fun ty x => BMULT ty x (B2 ty (- Z.pos n)))
        else (fun ty => BMULT ty (B2 ty (- Z.pos n)))
    end.

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

Lemma InvShift_accuracy: 
 forall (pow : positive) (ltr : bool) (ty : type) (x : ftype ty) 
  (F1 : is_finite (fprec ty) (femax ty) x = true),
 Rabs (B2R (fprec ty) (femax ty) (fop_of_rounded_unop (InvShift pow ltr) ty x) -
      F2R radix2 (B2F (B2 ty (Z.neg pow))) * B2R (fprec ty) (femax ty) x) <=
   bpow radix2 (3 - femax ty - fprec ty).
Proof.
intros.
unfold fop_of_unop.
assert (is_finite (fprec ty) (femax ty) (B2 ty (Z.neg pow)) = true). {
  apply B2_finite.
  pose proof (fprec_lt_femax ty).
  pose proof (fprec_gt_0 ty).
  red in H0.
  lia.
} 
simpl fop_of_rounded_unop.
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
   apply  InvShift_finite_aux; auto.
  * destruct H2 as [H2 _].
    rewrite H2. clear H2.
    apply InvShift_accuracy_aux; auto.
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
   apply  InvShift_finite_aux; auto.
  * destruct H2 as [H2 _].
    rewrite H2. clear H2.
    apply InvShift_accuracy_aux; auto.
Qed.

Lemma InvShift_finite: 
 forall (pow : positive) (ltr : bool) (ty : type) (x : ftype ty) 
  (F1 : is_finite (fprec ty) (femax ty) x = true),
 is_finite (fprec ty) (femax ty) (fop_of_rounded_unop (InvShift pow ltr) ty x) = true.
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
   apply  InvShift_finite_aux; auto.
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
   apply  InvShift_finite_aux; auto.
Qed.

End WITHVAR.
