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
From vcfloat Require Import IEEE754_extra. (*  lib.Floats. *)
Require compcert.lib.Maps.  
Require Coq.MSets.MSetAVL.
Require vcfloat.Fprop_absolute.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Require Export vcfloat.FPCore.
Require Import vcfloat.klist.
Import Bool.
Import Coq.Lists.List ListNotations.

Global Existing Instance fprec_gt_0. (* to override the Opaque one in Interval package *)

Local Open Scope R_scope.

Local Definition V := positive.
Definition     var_eqb: V -> V -> bool := Pos.eqb.
Lemma var_eqb_eq: forall v1 v2, var_eqb v1 v2 = true <-> v1 = v2.
Proof.  apply Pos.eqb_eq. Qed.

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

Inductive unop : Type :=
| Rounded1 (op: rounded_unop) (knowl:  option rounding_knowledge)
| Exact1 (o: exact_unop)
.

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

Unset Elimination Schemes.

(* See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Coq.20can't.20recognize.20a.20strictly.20positive.20occurrence
   for a discussion of Func1,Func2, etc. *)   
Inductive expr (ty: type): Type :=
| Const (f: ftype ty)
| Var (i: V)
| Binop (STD: is_standard ty) (b: binop) (e1 e2: expr ty)
| Unop (STD: is_standard ty) (u: unop) (e1: expr ty)
| Cast (fromty: type) (STDto: is_standard ty) (STDfrom: is_standard fromty) (knowl: option rounding_knowledge) (e1: expr fromty)
| Func (f: floatfunc_package ty) (args: klist expr (ff_args f))
.

Arguments Binop [ty STD] b e1 e2.
Arguments Unop [ty STD] u e1.

Set Elimination Schemes.
Lemma expr_ind:
  forall P : forall ty : type, expr ty -> Prop,
  (forall (ty : type) (f : ftype ty), P ty (Const ty f)) ->
  (forall (ty : type) (i : FPLang.V), P ty (Var ty i)) ->
  (forall (ty : type) (STD: is_standard ty) (b : binop) (e1 : expr ty),
   P ty e1 -> forall e2 : expr ty, P ty e2 -> P ty (Binop b e1 e2)) ->
  (forall (ty : type) (STD: is_standard ty) (u : unop) (e1 : expr ty), P ty e1 -> P ty (Unop u e1)) ->
  (forall (ty fromty : type) STDto STDfrom (knowl : option rounding_knowledge)
     (e1 : expr fromty), P fromty e1 -> P ty (Cast ty fromty STDto STDfrom knowl e1)) ->
  (forall (ty : type) (f4 : floatfunc_package ty)
    (args : klist expr (ff_args f4))
      (IH: Kforall P args),
      P ty (Func ty f4 args)) ->
  forall (ty : type) (e : expr ty), P ty e.
Proof.
intros.
refine (
(fix F (ty : type) (e : expr ty) {struct e} : P ty e :=
  match e as e0 return (P ty e0) with
  | Const _ f5 => H ty f5
  | Var _ i => H0 ty i
  | @Binop _ STD b e1 e2 => H1 ty STD b e1 (F ty e1) e2 (F ty e2)
  | @Unop _ STD u e1 => H2 ty STD u e1 (F ty e1)
  | Cast _ fromty STDto STDfrom knowl e1 => H3 ty fromty STDto STDfrom knowl e1 (F fromty e1)
  | Func _ f5 args => _ 
    end) ty e).
apply H4.
clear - F f5.
set (tys := ff_args f5) in *. clearbody tys.
induction args.
constructor.
constructor.
apply F.
apply IHargs.
Qed.

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
  end.

Fixpoint expr_height {ty} (e: expr ty) {struct e} : nat := 
 match e with
 | Const _ _ => O
 | Var _ _ => O
 | Binop _ e1 e2 => S (Nat.max (expr_height e1) (expr_height e2))
 | Unop _ e => S (expr_height e)
 | Cast _ _ _ _ _ e => S (expr_height e)
 | Func _ _ en => 
    let fix expr_klist_height {tys: list type} (l': klist expr tys) : list nat :=
        match l' with
        | Knil => nil
        | Kcons h tl => (expr_height h) :: expr_klist_height tl
        end in
    S (fold_right Nat.max O (expr_klist_height en))
 end.

Definition RR' (x: R) : Type := R.

Fixpoint apply_list (l: list R) (f: function_type (map RR' l) R) {struct l} : R.
 destruct l.
 apply f.
 simpl in f.
 apply (apply_list l). apply f. hnf. apply r.
Defined.

Fixpoint rval (env: forall ty, V -> ftype ty) {ty: type} (e: expr ty): R :=
  match e with
    | Const _ f => FT2R f
    | Var _ i => FT2R (env ty i)
    | Binop b e1 e2 =>  Rop_of_binop b (rval env e1) (rval env e2)
    | Unop b e => Rop_of_unop b (rval env e)
    | Cast _ _  _ _ _ e => rval env e
    | Func _ ff en => 
    let fix rval_klist {tys: list type} (l': klist expr tys) (f: function_type (map RR tys) R) {struct l'}: R :=
          match l' in (klist _ l)  return (function_type (map RR l) R -> R)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => rval_klist tl (f0 (rval env h))
          end f 
          in rval_klist en (ff_realfunc ff)
  end.

Definition rval_klist (env: forall ty, V -> ftype ty) {ty: type}  :=
 fix rval_klist {tys: list type} (l': klist expr tys) (f: function_type (map RR tys) R) {struct l'}: R :=
          match l' in (klist _ l)  return (function_type (map RR l) R -> R)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => rval_klist tl (f0 (rval env h))
          end f.

Section WITHNAN.
Context {NANS: Nans}.

Definition unop_valid ty (u: unop): bool :=
  match u with
    | Exact1 (Shift p _) => 
      Z.leb 0 (center_Z (3 - femax ty) (Z.of_N p + 1) (femax ty))
    | Rounded1 (InvShift p _) _ =>
      Z.leb 0 (center_Z (3 - (femax ty)) (- Z.pos p + 1) (femax ty))
    | _ => true
  end.

Fixpoint expr_valid {ty} (e: expr ty): bool :=
  match e with
    | Const _ f => is_finite f
    | Var _ _ => true
    | Binop _ e1 e2 => andb (expr_valid e1) (expr_valid e2)
    | Unop u e => unop_valid ty u && expr_valid e
    | Cast _ _  _ _ _ e => expr_valid e
    | Func _ ff en => 
       let fix expr_klist_valid {tys: list type} (es: klist expr tys) : bool :=
        match es with
        | Knil => true 
        | Kcons h tl => expr_valid h && expr_klist_valid tl 
       end
       in expr_klist_valid en
  end.

Fixpoint expr_klist_valid {tys: list type} (es: klist expr tys) : bool :=
        match es with
        | Knil => true 
        | Kcons h tl => expr_valid h && expr_klist_valid tl 
       end.

Definition fop_of_rounded_binop (r: rounded_binop): 
  forall ty (STD: is_standard ty),
    ftype ty -> ftype ty -> ftype ty
  :=
    match r with
      | PLUS => @BPLUS _
      | MINUS => @BMINUS _
      | MULT => @BMULT _
      | DIV => @BDIV _
    end.

Definition fop_of_binop (r: binop):
  forall ty (STD: is_standard ty),
    ftype ty -> ftype ty -> ftype ty
  :=
    match r with
      | Rounded2 r _ => fop_of_rounded_binop r
      | SterbenzMinus => @BMINUS _
      | PlusZero minus zero_left => if minus then @BMINUS _ else @BPLUS _
    end.

Definition fop_of_rounded_unop (r: rounded_unop): 
  forall ty (STD: is_standard ty),
    ftype ty -> ftype ty
  :=
    match r with
      | SQRT => @BSQRT _
      | InvShift n b => 
        if b
        then (fun ty STD x => @BMULT _ ty _ x (ftype_of_float (B2 ty (- Z.pos n))))
        else (fun ty STD => @BMULT _ ty _ (ftype_of_float (B2 ty (- Z.pos n))))
    end.

Definition fop_of_exact_unop (r: exact_unop)
  := 
    match r with
      | Abs => @BABS _
      | Opp => @BOPP _
      | Shift n b =>
        if b
        then
          (fun ty STD x => @BMULT _ ty _ x (ftype_of_float (B2 ty (Z.of_N n))))
        else
          (fun ty STD => @BMULT _ ty _ (ftype_of_float (B2 ty (Z.of_N n))))
    end.

Definition fop_of_unop (r: unop) :=
 match r with
 | Rounded1 u o => fop_of_rounded_unop u
 | Exact1 u => fop_of_exact_unop u
 end.

Fixpoint fval (env: forall ty, V -> ftype ty) {ty} (e: expr ty) {struct e}: ftype ty :=
      match e with
      | Const _ f => f
      | Var _ i => env ty i
      | Binop b e1 e2 => fop_of_binop b _ _ (fval env e1) (fval env e2)
      | Unop u e1 => fop_of_unop u _ _ (fval env e1)
      | Cast _ tfrom STDto STDfrom o e1 => @cast _ ty tfrom STDto STDfrom (fval env e1)
      | Func _ ff en =>
       let fix fval_klist {l1: list type} (l': klist expr l1) (f: function_type (map ftype' l1) (ftype' ty)) {struct l'}: ftype' ty :=
          match  l' in (klist _ l) return (function_type (map ftype' l) (ftype' ty) -> ftype' ty)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => fval_klist tl (f0 (fval env h))
          end f 
          in fval_klist en (ff_func (ff_ff ff))
      end.

Definition fval_klist (env: forall ty, V -> ftype ty) {T: Type} :=
  fix fval_klist {l1: list type} (l': klist expr l1) (f: function_type (map ftype' l1) T) {struct l'}: T :=
          match  l' in (klist _ l) return (function_type (map ftype' l) T -> T)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => fval_klist tl (f0 (fval env h))
          end f.

Lemma is_nan_cast:
  forall  t1 t2 STD1 STD2 x1,
   is_nan _ _ (float_of_ftype x1) = false ->
   is_nan _ _ (float_of_ftype (@cast _ t2 t1 STD2 STD1 x1)) = false.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _ _ _).
subst t2.
simpl.
rewrite <- H.
f_equal.
apply float_of_ftype_irr.
destruct t2 as [? ? ? ? ? [|]]; try contradiction.
destruct t1 as [? ? ? ? ? [|]]; try contradiction.
simpl.
unfold Bconv.
destruct x1; try discriminate; auto.
apply is_nan_BSN2B'.
Qed.

Lemma cast_is_nan :
  forall t1 t2 STD1 STD2 x1,
  is_nan _ _ (float_of_ftype x1) = true ->
  is_nan _ _ (float_of_ftype (@cast _ t1 t2 STD2 STD1 x1)) = true.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _ _ _ ).
-
subst t2. simpl.
rewrite <- H.
f_equal.
apply float_of_ftype_irr.
-
destruct t2 as [? ? ? ? ? [|]]; try contradiction.
destruct t1 as [? ? ? ? ? [|]]; try contradiction.
simpl.
unfold Bconv.
destruct x1; try discriminate; auto.
Qed.

Lemma is_finite_Binary: forall {ty} `{STD: is_standard ty} (x: ftype ty),
  is_finite x = Binary.is_finite (fprec ty) (femax ty) (float_of_ftype x).
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; try contradiction.
reflexivity.
Qed.

Lemma FT2R_ftype_of_float:
  forall {ty} `{STD: is_standard ty} x,
   FT2R (ftype_of_float x) = B2R _ _ x.
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; try contradiction.
reflexivity.
Qed.

Lemma InvShift_accuracy: 
 forall (pow : positive) (ltr : bool) (ty : type) (STD: is_standard ty) x 
  (F1 : is_finite x = true),
 Rabs (FT2R (fop_of_rounded_unop (InvShift pow ltr) ty STD x) -
      F2R radix2 (B2F (B2 ty (Z.neg pow))) * FT2R x) <=
   /2 * bpow radix2 (3 - femax ty - fprec ty).
Proof.
intros.
unfold fop_of_unop.
assert (Binary.is_finite (fprec ty) (femax ty) (B2 ty (Z.neg pow)) = true). {
  apply B2_finite.
  pose proof (fprec_lt_femax ty).
  pose proof (fprec_gt_0 ty).
  red in H0.
  lia.
}
rewrite is_finite_Binary in F1.
simpl fop_of_rounded_unop.
rewrite <- (ftype_of_float_of_ftype STD STD x).
set (x' := float_of_ftype x) in *.
clearbody x'. clear x. rename x' into x.
destruct ltr.
-
   destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty)).
  + rewrite (B2_zero ty (Z.neg pow)) in * by auto.
     simpl B2R. clear H l.
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
    pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)).
    set (j := bpow radix2 _) in *. clearbody j.
    destruct x; try discriminate; simpl;
     rewrite ?Rmult_0_l, Rminus_0_r, Rabs_R0; lra.     
  +
    assert (H2 := Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
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
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
    pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)).
    set (j := bpow radix2 _) in *. clearbody j.
    destruct x; try discriminate; simpl; rewrite ?Rmult_0_l, Rminus_0_r, Rabs_R0; lra.     
  +
    assert (H2 := Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
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
 forall (pow : positive) (ltr : bool) (ty : type) (STD: is_standard ty) (x : ftype ty) 
  (F1 : is_finite x = true),
 is_finite (fop_of_rounded_unop (InvShift pow ltr) ty STD x) = true.
Proof.
intros.
simpl.
rewrite is_finite_Binary in F1.
pose proof (fprec_lt_femax ty).
pose proof (fprec_gt_0 ty).
red in H0.
pose proof (B2_finite ty (Z.neg pow) ltac:(lia)).
unfold BMULT, BINOP.
destruct ltr; destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty));
  unfold Datatypes.id;
  rewrite is_finite_Binary, !float_of_ftype_of_float.
- rewrite (B2_zero _ _ l); unfold Bmult. destruct (float_of_ftype x); auto.
- 
    pose proof (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) (float_of_ftype x)).
    rewrite Rmult_comm in H2. 
    pose proof (B2_correct ty (Z.neg pow) ltac:(lia)).
   rewrite H3 in H2.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite F1, H1, Raux.bpow_opp in H2. simpl andb in H2.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; apply H2].
     apply Rlt_bool_true.
   apply  InvShift_finite_aux; auto.
- rewrite (B2_zero _ _ l); unfold Bmult. destruct (float_of_ftype x); auto.
- 
    pose proof (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) (float_of_ftype x)).
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

End WITHNAN.
