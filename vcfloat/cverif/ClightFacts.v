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

More properties about the operational semantics of CompCert Clight.
*)

From compcert.cfrontend Require Export Clight.
Require Import MSets.
Require Import ZArith.
Require Import vcfloat.LibTac.
Require Export vcfloat.cverif.ClightBigstep2.

Module VSET := MSetAVL.Make(Pos).

Fixpoint cvars (e: Clight.expr): VSET.t :=
  match e with
    | Etempvar i _ => VSET.singleton i
    | Ederef e _ => cvars e
    | Eaddrof e _ => cvars e
    | Eunop _ e _ => cvars e
    | Ebinop _ e1 e2 _ => VSET.union (cvars e1) (cvars e2)
    | Ecast e _ => cvars e
    | Efield e _ _ => cvars e
    | _ => VSET.empty
  end.


Lemma gempty {T} (P: _ -> T -> Prop):
  True <->
  (forall i v,
     Maps.PTree.get i (Maps.PTree.empty _) = Some v -> P i v).
Proof.
  split; auto.
  intros.
  rewrite Maps.PTree.gempty in H0.
  discriminate.
Qed.

Lemma gsspec {T} (P: _ -> T -> Prop) m i_ v_:
(
  (P i_ v_ /\ (forall i v, Maps.PTree.get i m = Some v -> i <> i_ -> P i v))
) <->
(forall i v,
  Maps.PTree.get i (Maps.PTree.set i_ v_ m) = Some v -> P i v)
.
Proof.
  split.
  {
    destruct 1.
    intros.
    rewrite Maps.PTree.gsspec in H1.
    destruct (Coqlib.peq i i_); eauto.
    congruence.
  }
  intros.
  split.
  {
    apply (H _ _ (Maps.PTree.gss _ _ _ )).
  }
  intros.
  specialize (H i v).
  rewrite Maps.PTree.gso in H; auto.
Qed.

Lemma eval_expr_lvalue_impl ge env m tenv1 tenv2
      (Htenv: forall i v, Maps.PTree.get i tenv1 = Some v ->
                          Maps.PTree.get i tenv2 = Some v)
:
  (forall e v,
     eval_expr ge env tenv1 m e v ->
     eval_expr ge env tenv2 m e v)
  /\
  (forall e b o,
     eval_lvalue ge env tenv1 m e b o ->
     eval_lvalue ge env tenv2 m e b o).
Proof.
  apply eval_expr_lvalue_ind; try (intros; econstructor; eauto; fail).
Qed.

Lemma eval_expr_impl ge env m tenv1 tenv2
      (Htenv: forall i v, Maps.PTree.get i tenv1 = Some v ->
                          Maps.PTree.get i tenv2 = Some v)
:
  (forall e v,
     eval_expr ge env tenv1 m e v ->
     eval_expr ge env tenv2 m e v)
.
Proof.
  apply eval_expr_lvalue_impl.
  assumption.
Qed.


Definition intsize_eqb (s1 s2: Ctypes.intsize): bool :=
  match s1, s2 with
    | Ctypes.I8, Ctypes.I8 => true
    | Ctypes.I16, Ctypes.I16 => true
    | Ctypes.I32, Ctypes.I32 => true
    | Ctypes.IBool, Ctypes.IBool => true
    | _, _ => false
  end.

Lemma intsize_eqb_eq s1 s2:
  intsize_eqb s1 s2 = true <-> s1 = s2.
Proof.
  destruct s1; destruct s2; simpl; intuition congruence.
Qed.

Definition signedness_eqb (s1 s2: Ctypes.signedness): bool :=
  match s1, s2 with
    | Ctypes.Signed, Ctypes.Signed => true
    | Ctypes.Unsigned, Ctypes.Unsigned => true
    | _, _ => false
  end.

Lemma signedness_eqb_eq s1 s2:
  signedness_eqb s1 s2 = true <-> s1 = s2.
Proof.
  destruct s1; destruct s2; simpl; intuition congruence.
Qed.

Definition attr_eqb (s1 s2: Ctypes.attr): bool :=
  andb (Bool.eqb (Ctypes.attr_volatile s1) (Ctypes.attr_volatile s2))
       (option_eqb N.eqb (Ctypes.attr_alignas s1) (Ctypes.attr_alignas s2))
.

Lemma attr_eqb_eq s1 s2:
  attr_eqb s1 s2 = true <-> s1 = s2.
Proof.
  unfold attr_eqb.
  destruct s1; destruct s2; simpl.
  rewrite Bool.andb_true_iff.
  rewrite Bool.eqb_true_iff.
  rewrite option_eqb_eq; auto using N.eqb_eq.
  intuition congruence.
Qed.

Definition floatsize_eqb (s1 s2: Ctypes.floatsize): bool :=
  match s1, s2 with
    | Ctypes.F32, Ctypes.F32 => true
    | Ctypes.F64, Ctypes.F64 => true
    | _, _ => false
  end.

Lemma floatsize_eqb_eq s1 s2:
  floatsize_eqb s1 s2 = true <-> s1 = s2.
Proof.
  destruct s1; destruct s2; simpl; intuition congruence.
Qed.

Definition calling_convention_eqb s1 s2 :=
  andb (option_eqb Z.eqb (AST.cc_vararg s1) (AST.cc_vararg s2))
       (andb (Bool.eqb (AST.cc_unproto s1) (AST.cc_unproto s2))
            (Bool.eqb (AST.cc_structret s1) (AST.cc_structret s2))).

Lemma calling_convention_eqb_eq s1 s2:
  calling_convention_eqb s1 s2 = true <-> s1 = s2.
Proof.
  unfold calling_convention_eqb.
  destruct s1; destruct s2; simpl.
  repeat rewrite Bool.andb_true_iff.
  rewrite (option_eqb_eq (Z.eqb_eq)).
  repeat rewrite Bool.eqb_true_iff.
  intuition congruence.
Qed.

Fixpoint Ctype_eqb (t1 t2: Ctypes.type) {struct t1}: bool :=
  match t1, t2 with
    | Ctypes.Tvoid, Ctypes.Tvoid => true
    | Ctypes.Tint i1 s1 a1, Ctypes.Tint i2 s2 a2 =>
      andb (intsize_eqb i1 i2)
           (andb (signedness_eqb s1 s2)
                 (attr_eqb a1 a2))
    | Ctypes.Tlong s1 a1, Ctypes.Tlong s2 a2 =>
      andb (signedness_eqb s1 s2)
           (attr_eqb a1 a2)
    | Ctypes.Tfloat f1 a1, Ctypes.Tfloat f2 a2 =>
      andb (floatsize_eqb f1 f2)
           (attr_eqb a1 a2)
    | Ctypes.Tpointer u1 a1, Ctypes.Tpointer u2 a2 =>
      andb (Ctype_eqb u1 u2)
           (attr_eqb a1 a2)
    | Ctypes.Tarray u1 n1 a1, Ctypes.Tarray u2 n2 a2 =>
      andb (Ctype_eqb u1 u2)
           (andb (Z.eqb n1 n2)
                 (attr_eqb a1 a2))
    | Ctypes.Tfunction l1 u1 c1, Ctypes.Tfunction l2 u2 c2 =>
      andb (Ctypelist_eqb l1 l2)
           (andb (Ctype_eqb u1 u2)
                 (calling_convention_eqb c1 c2))
    | Ctypes.Tstruct i1 a1, Ctypes.Tstruct i2 a2 =>
      andb (Pos.eqb i1 i2)
          (attr_eqb a1 a2)
    | Ctypes.Tunion i1 a1, Ctypes.Tunion i2 a2 =>
      andb (Pos.eqb i1 i2)
          (attr_eqb a1 a2)
    | _, _ => false
  end
with Ctypelist_eqb (l1 l2: Ctypes.typelist) {struct l1}: bool :=
       match l1, l2 with
         | Ctypes.Tnil, Ctypes.Tnil => true
         | Ctypes.Tcons t1 u1, Ctypes.Tcons t2 u2 =>
           andb (Ctype_eqb t1 t2)
                (Ctypelist_eqb u1 u2)
         | _, _ => false
       end.

Scheme Ctype_ind2 := Induction for Ctypes.type Sort Prop
with Ctypelist_ind2 := Induction for Ctypes.typelist Sort Prop.
Combined Scheme Ctype_Ctypelist_ind2 from Ctype_ind2, Ctypelist_ind2.

Lemma Ctype_Ctypelist_eqb_eq:
  (forall t1 t2,
     Ctype_eqb t1 t2 = true <-> t1 = t2)
  /\
  (forall t1 t2,
     Ctypelist_eqb t1 t2 = true <-> t1 = t2).
Proof.
  apply Ctype_Ctypelist_ind2;
  intros;
  destruct t2;
  simpl;
  repeat rewrite Bool.andb_true_iff;
  repeat rewrite intsize_eqb_eq;
  repeat rewrite signedness_eqb_eq;
  repeat rewrite attr_eqb_eq;
  repeat rewrite calling_convention_eqb_eq;
  repeat rewrite floatsize_eqb_eq;
  repeat rewrite Z.eqb_eq;
  repeat rewrite Pos.eqb_eq;
  (try rewrite H);
  (try rewrite H0);
  intuition congruence.
Qed.

Lemma Ctype_eqb_eq t1 t2:
     Ctype_eqb t1 t2 = true <-> t1 = t2.
Proof.
  apply Ctype_Ctypelist_eqb_eq.
Qed. 

Fixpoint subst_expr (i: AST.ident) (e': Clight.expr) (e: Clight.expr) {struct e}: option Clight.expr :=
  match e with
    | Etempvar i_ ty =>
      if Pos.eqb i_ i
      then
        if Ctype_eqb ty (Clight.typeof e')
        then Some e'
        else None
      else
        Some e
    | Ederef e1 ty =>
      match subst_expr i e' e1 with
        | Some e2 => Some (Ederef e2 ty)
        | _ => None
      end
    | Eaddrof e1 ty =>
      match subst_expr i e' e1 with
        | Some e2 => Some (Eaddrof e2 ty)
        | None => None
      end
    | Eunop u e1 ty =>
      match subst_expr i e' e1 with
        | Some e2 => Some (Eunop u e2 ty)
        | None => None
      end
    | Ebinop b e1 e2 ty =>
      match subst_expr i e' e1 with
        | Some e3 =>
          match subst_expr i e' e2 with
            | Some e4 => Some (Ebinop b e3 e4 ty)
            | None => None
          end
        | None => None
      end
    | Ecast e1 ty =>
      match subst_expr i e' e1 with
        | Some e2 => Some (Ecast e2 ty)
        | None => None
      end
    | Efield e1 i_ ty =>
      match subst_expr i e' e1 with
        | Some e2 => Some (Efield e2 i_ ty)
        | None => None
      end
    | _ => Some e
  end.

Lemma subst_expr_type i e' e1:
  forall e2,
    subst_expr i e' e1 = Some e2 ->
    Clight.typeof e2 = Clight.typeof e1.
Proof.
  induction e1; simpl.
  {
    inversion 1; subst; simpl; auto.
  }
  {
    inversion 1; subst; simpl; auto.
  }
  {
    inversion 1; subst; simpl; auto.
  }
  {
    inversion 1; subst; simpl; auto.
  }
  {
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (Pos.eqb i0 i).
    {
      destruct (Ctype_eqb t (typeof e')) eqn:EQB; try discriminate.
      rewrite Ctype_eqb_eq in EQB.
      congruence.
    }
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (subst_expr i e' e1); try discriminate.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (subst_expr i e' e1); try discriminate.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (subst_expr i e' e1); try discriminate.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (subst_expr i e' e1_1); try discriminate.
    destruct (subst_expr i e' e1_2); try discriminate.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (subst_expr i e' e1); try discriminate.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    destruct (subst_expr i e' e1); try discriminate.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    inversion 1; subst; simpl; auto.
  }
  {
    intro.
    inversion 1; subst; simpl; auto.
  }
Qed.

Lemma peq_eqb_elim {T: Type} (c d: T) a b:
  (if Coqlib.peq a b then c else d) = (if Pos.eqb a b then c else d).
Proof.
  destruct (Coqlib.peq a b) as [ EQ | EQ ]; destruct (Pos.eqb a b) eqn:EQB;
  rewrite <- Pos.eqb_eq in EQ;
  congruence.
Qed.

Lemma subst_expr_correct tenv i:
  Maps.PTree.get i tenv = None ->
  forall ge lenv m e' v',
    eval_expr ge lenv tenv m e' v' ->
    (
        forall e1 v,
          eval_expr ge lenv (Maps.PTree.set i v' tenv) m e1 v ->
          forall e2,
            subst_expr i e' e1 = Some e2 ->
            eval_expr ge lenv tenv m e2 v
      ) /\ (
        forall e1 l o,
          eval_lvalue ge lenv (Maps.PTree.set i v' tenv) m e1 l o ->
          forall e2,
            subst_expr i e' e1 = Some e2 ->
            eval_lvalue ge lenv tenv m e2 l o
      ).
Proof.
  intros.
  apply eval_expr_lvalue_ind; simpl.
  {
    inversion 1; subst; constructor.
  }
  {
    inversion 1; subst; constructor.
  }
  {
    inversion 1; subst; constructor.
  }
  {
    inversion 1; subst; constructor.
  }
  {
    intros until v.
    rewrite Maps.PTree.gsspec.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq id i).
    {
      subst.
      inversion 1; subst.
      intro.
      destruct (Ctype_eqb ty (typeof e')) eqn:?; congruence.
    }
    inversion 2; subst.
    constructor.
    assumption.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a); try congruence.
    inversion 1; subst.
    constructor; auto.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a) eqn:SUBST; try congruence.
    inversion 1; subst.
    apply subst_expr_type in SUBST.
    econstructor; eauto.
    congruence.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a1) eqn:SUBST1; try congruence.
    destruct (subst_expr i e' a2) eqn:SUBST2; try congruence.
    inversion 1; subst.
    apply subst_expr_type in SUBST1.
    apply subst_expr_type in SUBST2.
    econstructor; eauto.
    congruence.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a) eqn:SUBST; try congruence.
    inversion 1; subst.
    apply subst_expr_type in SUBST.
    econstructor; eauto.
    congruence.
  }
  {
    inversion 1; subst.
    constructor.
  }
  {
    inversion 1; subst.
    constructor.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a) eqn:SUBST; try congruence.
    inversion 1; subst.
    apply subst_expr_type in SUBST.
    econstructor; eauto.
    congruence.
  }
  {
    inversion 2; subst.
    constructor; auto.
  }
  {
    inversion 3; subst.
    apply eval_Evar_global; auto.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a); try congruence.
    inversion 1; subst.
    econstructor; eauto.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a) eqn:SUBST; try congruence.
    inversion 1; subst.
    apply subst_expr_type in SUBST.
    econstructor; eauto.
    rewrite SUBST.
    eassumption.
  }
  {
    intros until e2.
    destruct (subst_expr i e' a) eqn:SUBST; try congruence.
    inversion 1; subst.
    apply subst_expr_type in SUBST.
    econstructor; eauto.
    rewrite SUBST.
    eassumption.
  }
Qed.

Fixpoint next_index {A} (accu: positive) (l: list (positive * A)): positive :=
  match l with
    | nil => accu
    | (i, _) :: l' =>
      next_index (Pos.max accu (Pos.succ i)) l'
  end.

Lemma next_index_le {A} l:
  forall accu,
    Pos.le accu (next_index (A := A) accu l).
Proof.
  induction l; simpl; intros.
  {
    reflexivity.
  }
  destruct a.
  etransitivity; [ | eapply IHl ].
  apply Pos.le_max_l.
Qed.

Lemma next_index_correct' {A} (a: A) l:
  forall accu,
    In (next_index accu l, a) l ->
    False.
Proof.
  induction l; simpl; auto.
  destruct a0.
  destruct 1; eauto.
  inversion H.
  apply (Pos.lt_irrefl p).
  eapply Pos.lt_le_trans.
  {
    apply Pos.lt_succ_diag_r.
  }
  rewrite H1 at 2.
  etransitivity; [ | eapply next_index_le ].
  apply Pos.le_max_r.
Qed.

Corollary next_index_correct accu {A} (m: Maps.PTree.t A):
  Maps.PTree.get (next_index accu (Maps.PTree.elements m)) m = None.
Proof.
  destruct (Maps.PTree.get (next_index accu (Maps.PTree.elements m))) eqn:EQ; auto.
  apply Maps.PTree.elements_correct in EQ.
  apply next_index_correct' in EQ.
  contradiction.
Qed.

Definition is_trivial_expr (e: Clight.expr): bool :=
  match e with
    | Econst_int _ _ => true
    | Econst_float _ _ => true
    | Econst_single _ _ => true
    | Econst_long _ _ => true
    | Etempvar _ _ => true
    | _ => false
  end.

(* Extract the deepest nontrivial Clight expression (strict node) *)

Fixpoint deepest_expr (i_: AST.ident) (e: Clight.expr): Clight.expr * Clight.expr :=
  match e with
    | Ederef e1 ty =>
      if is_trivial_expr e1
      then
        (e, Etempvar i_ ty)
      else 
        let '(deep, e1_) := deepest_expr i_ e1 in
        (deep, Ederef e1_ ty)
    | Eaddrof e1 ty =>
      if is_trivial_expr e1
      then
        (e, Etempvar i_ ty)
      else
        let '(deep, e1_) := deepest_expr i_ e1 in
        (deep, Eaddrof e1_ ty)
    | Eunop u e1 ty =>
      if is_trivial_expr e1
      then
        (e, Etempvar i_ ty)
      else
        let '(deep, e1_) := deepest_expr i_ e1 in
        (deep, Eunop u e1_ ty)
    | Ebinop b e1 e2 ty =>
      if is_trivial_expr e1
      then
        if is_trivial_expr e2
        then
          (e, Etempvar i_ ty)
        else
          let '(deep, e2_) := deepest_expr i_ e2 in
          (deep, Ebinop b e1 e2_ ty)
      else
        let '(deep, e1_) := deepest_expr i_ e1 in
        (deep, Ebinop b e1_ e2 ty)
    | Ecast e1 ty =>
      if is_trivial_expr e1
      then
        (e, Etempvar i_ ty)
      else
        let '(deep, e1_) := deepest_expr i_ e1 in
        (deep, Ecast e1_ ty)
    | Efield e1 f ty =>
      if is_trivial_expr e1
      then
        (e, Etempvar i_ ty)
      else
        let '(deep, e1_) := deepest_expr i_ e1 in
        (deep, Efield e1_ f ty)
    | _ => (e, Etempvar i_ (Clight.typeof e))
  end.

Lemma eq_sym_iff {A} (x y: A): x = y <-> y = x.
Proof.
  intuition congruence.
Qed.

Lemma subst_expr_not_in i_ deep e:
    ~ VSET.In i_ (cvars e) ->
    subst_expr i_ deep e = Some e.
Proof.
  induction e; simpl; auto.
  {
    rewrite VSET.singleton_spec.
    rewrite eq_sym_iff.
    rewrite <- Pos.eqb_eq.
    destruct (Pos.eqb i i_); congruence.
  }
  {
    intros.
    rewrite IHe; auto.
  }
  {
    intros.
    rewrite IHe; auto.
  }
  {
    intros.
    rewrite IHe; auto.
  }
  {
    rewrite VSET.union_spec.
    intros.
    rewrite IHe1 by tauto.
    rewrite IHe2 by tauto.
    reflexivity.
  }
  {
    intros.
    rewrite IHe; auto.
  }
  {
    intros.
    rewrite IHe; auto.
  }
Qed.

Lemma deepest_expr_correct i_ e:
  forall deep e_,
    deepest_expr i_ e = (deep, e_) ->
    ~ VSET.In i_ (cvars e) ->
    subst_expr i_ deep e_ = Some e.
Proof.
  induction e; simpl.
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    destruct (is_trivial_expr e).
    {
      inversion 1; subst; simpl.
      rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
      rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
      auto.
    }
    destruct (deepest_expr i_ e).
    inversion 1; subst; simpl.
    intros.
    rewrite IHe; auto.
  }
  {
    destruct (is_trivial_expr e).
    {
      inversion 1; subst; simpl.
      rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
      rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
      auto.
    }
    destruct (deepest_expr i_ e).
    inversion 1; subst; simpl.
    intros.
    rewrite IHe; auto.
  }
  {
    destruct (is_trivial_expr e).
    {
      inversion 1; subst; simpl.
      rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
      rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
      auto.
    }
    destruct (deepest_expr i_ e).
    inversion 1; subst; simpl.
    intros.
    rewrite IHe; auto.
  }
  {
    intros until e_.
    rewrite VSET.union_spec.
    destruct (is_trivial_expr e1).
    {
      destruct (is_trivial_expr e2).
      {
        inversion 1; subst; simpl.
        rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
        rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
        auto.
      }
      destruct (deepest_expr i_ e2).
      inversion 1; subst; simpl.
      intros.
      rewrite subst_expr_not_in by tauto. 
      rewrite IHe2; tauto.
    }
    destruct (deepest_expr i_ e1).
    inversion 1; subst; simpl.
    intros.
    rewrite IHe1; try tauto.
    rewrite subst_expr_not_in; tauto.
  }
  {
    destruct (is_trivial_expr e).
    {
      inversion 1; subst; simpl.
      rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
      rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
      auto.
    }
    destruct (deepest_expr i_ e).
    inversion 1; subst; simpl.
    intros.
    rewrite IHe; auto.
  }
  {
    destruct (is_trivial_expr e).
    {
      inversion 1; subst; simpl.
      rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
      rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
      auto.
    }
    destruct (deepest_expr i_ e).
    inversion 1; subst; simpl.
    intros.
    rewrite IHe; auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite (fun u1 u2 => let (_, K) := Pos.eqb_eq u1 u2 in K) by auto.
    rewrite (fun u1 u2 => let (_, K) := Ctype_eqb_eq u1 u2 in K) by auto.
    auto.
  }
Qed.

Definition is_var_expr e :=
  match e with
    | Etempvar _ _ => true
    | _ => false
  end.

Definition shallowest_expr (i_: AST.ident) (e: Clight.expr): Clight.expr * Clight.expr :=
  match e with
    | Ederef e1 ty =>
      (Ederef (Etempvar i_ (Clight.typeof e1)) ty, e1)

    | Eaddrof e1 ty =>
      (Eaddrof (Etempvar i_ (Clight.typeof e1)) ty, e1)

    | Eunop u e1 ty =>
      (Eunop u (Etempvar i_ (Clight.typeof e1)) ty, e1)

    | Ebinop b e1 e2 ty =>
      if is_var_expr e1
      then
        (Ebinop b e1 (Etempvar i_ (Clight.typeof e2)) ty, e2)
      else
        (Ebinop b (Etempvar i_ (Clight.typeof e1)) e2 ty, e1)

    | Ecast e1 ty =>
      (Ecast (Etempvar i_ (Clight.typeof e1)) ty, e1)

    | Efield e1 f ty =>
      (Efield (Etempvar i_ (Clight.typeof e1)) f ty, e1)

    | _ =>
      (Etempvar i_ (Clight.typeof e), e)
  end.

Lemma ctype_eq_elim {T: Type} (c d: T) a b:
  (if Ctypes.type_eq a b then c else d) = (if Ctype_eqb a b then c else d).
Proof.
  destruct (Ctypes.type_eq a b) as [ EQ | EQ ]; destruct (Ctype_eqb a b) eqn:EQB;
  rewrite <- Ctype_eqb_eq in EQ;
  congruence.
Qed.

Lemma shallowest_expr_correct i_ e:
  forall shallow e_,
    shallowest_expr i_ e = (shallow, e_) ->
    ~ VSET.In i_ (cvars e) ->
    subst_expr i_ e_ shallow = Some e.
Proof.
  destruct e; simpl.
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t t); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t t); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t t); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t t); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t t); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t t); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq (typeof e_) (typeof e_)); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq (typeof e_) (typeof e_)); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq (typeof e_) (typeof e_)); congruence.
  }
  {
    intros until e_.
    rewrite VSET.union_spec.    
    destruct (is_var_expr e1) eqn:ISVAR.
    {
      destruct e1; try discriminate.
      inversion 1; subst; simpl.      
      rewrite VSET.singleton_spec.
      rewrite eq_sym_iff.
      rewrite <- peq_eqb_elim.
      destruct (Coqlib.peq i i_); try tauto.
      rewrite <- peq_eqb_elim.
      destruct (Coqlib.peq i_ i_); try congruence.      
      rewrite <- ctype_eq_elim.
      destruct (Ctypes.type_eq (typeof e_) (typeof e_)); congruence.
    }
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq (typeof e_) (typeof e_)); try congruence.
    intro.
    rewrite subst_expr_not_in; auto.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq (typeof e_) (typeof e_)); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq (typeof e_) (typeof e_)); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t0 t0); congruence.
  }
  {
    inversion 1; subst; simpl.
    rewrite <- peq_eqb_elim.
    destruct (Coqlib.peq i_ i_); try congruence.
    rewrite <- ctype_eq_elim.
    destruct (Ctypes.type_eq t0 t0); congruence.
  }
Qed.

Fixpoint PTree_filter2 {A : Type} (pred : AST.ident -> A -> bool) (m : Maps.PTree.t A) {struct m} :
  Maps.PTree.t A :=
  match m with
  | Maps.PTree.Leaf => Maps.PTree.Leaf
  | Maps.PTree.Node l o r =>
      let o' :=
        match o with
        | Some x => if pred xH x then o else None
        | None => None
        end in
      Maps.PTree.Node' (PTree_filter2 (fun i => pred (xO i)) l) o' (PTree_filter2 (fun i => pred (xI i)) r)
  end.

Lemma PTree_gfilter2 {A} (m: _ A):
  forall pred i,
    Maps.PTree.get i (PTree_filter2 pred m) =
    match Maps.PTree.get i m with
      | Some x => if pred i x then Some x else None
      | None => None
    end.
Proof.
  induction m; simpl.
  {
    replace (Maps.PTree.Leaf) with (Maps.PTree.empty A) by reflexivity.
    intros.
    rewrite Maps.PTree.gempty.
    reflexivity.
  }
  intros.
  rewrite Maps.PTree.gnode'.
  destruct i; simpl; auto.
  {
    rewrite IHm2.
    auto.
  }
  {
    rewrite IHm1.
    auto.
  }
  destruct o; auto.
Qed.

Lemma PTree_elements_correct {T: Type} (P: _ -> T -> Prop) m:
  list_forall (fun iv => let '(i, v) := iv in P i v)
              (Maps.PTree.elements m) ->
  (forall i v,
     Maps.PTree.get i m = Some v ->
     P i v).
Proof.
  intros.
  apply Maps.PTree.elements_correct in H0.
  rewrite list_forall_spec in H.
  apply H in H0.
  assumption.
Qed.
