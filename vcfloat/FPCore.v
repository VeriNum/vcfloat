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

(** FPCore module.
   [note by Andrew W. Appel]
  These definitions, which were previously part of FPLang.v, are 
  separated out to support a modularity principle:  some clients
  may want the definitions of [type], [BPLUS] etc.  but not the
  deep-embedded syntax of [binop], [PLUS] etc.  Such clients
  can import FPCore without importing FPLang.
     Why might such clients exist?  We envision a multilayer
   correctness proof of a C program:  prove in VST that a C program
   implements a functional model (a Gallina function over Flocq
   floating point);  then prove that the functional model satisfies
   a high-level specification (approximates real-valued function F
   to some accuracy bound).   It is in that second proof that VCFloat
   might be used.   The first proof (VST refinement) should not need
   to import VCFloat.   But the functional model would still like to make
   use of some convenient definitions for Flocq functions on floating-point
   numbers; those definitions are defined here in FPCore.
   Thus, the refinement proof in VST will need to import FPCore but
    not the rest of VCFloat. *)

Require Import ZArith Lia Reals.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra. (* lib.Floats. *)
Global Unset Asymmetric Patterns. (* because "Require compcert..." sets it *)
Require Export vcfloat.Float_notations.

Definition BOOL (a: bool): Prop := if a then True else False.

Lemma BOOL_proof_eq a (h1 h2: BOOL a):
  h1 = h2.
Proof.
  destruct a; try contradiction.
  unfold BOOL in h1, h2.
  destruct h1. destruct h2. reflexivity.
Defined. (* required for the semantics of cast *)

Lemma BOOL_intro a:
  a = true ->
  BOOL a.
Proof.
  unfold BOOL.
  intros.
  rewrite H.
  exact I.
Qed.

Lemma BOOL_elim a:
  BOOL a -> a = true.
Proof.
  unfold BOOL.
  destruct a; auto.
Qed.

Definition ZLT a b: Prop := BOOL (Z.ltb a b).

Lemma ZLT_intro a b:
  (a < b)%Z ->
  ZLT a b.
Proof.
  intros.
  apply BOOL_intro.
  apply Z.ltb_lt.
  assumption.
Qed.

Lemma ZLT_elim a b:
  ZLT a b ->
  (a < b)%Z.
Proof.
  intros.
  apply Z.ltb_lt.
  apply BOOL_elim.
  assumption.
Qed.

Record type: Type := TYPE
  {
    fprecp: positive;
    femax: Z;
    fprec := Z.pos fprecp;
    fprec_lt_femax_bool: ZLT fprec femax;
    fprecp_not_one_bool: BOOL (negb (Pos.eqb fprecp xH))
  }.

Lemma type_ext t1 t2:
  fprecp t1 = fprecp t2 -> femax t1 = femax t2 -> t1 = t2.
Proof.
  destruct t1. destruct t2. simpl. intros. subst.
  f_equal; apply BOOL_proof_eq.
Defined. (* required for the semantics of cast *)

Lemma type_ext' t1 t2:
  fprec t1 = fprec t2 -> femax t1 = femax t2 -> t1 = t2.
Proof.
  intros.
  apply type_ext; auto.
  apply Zpos_eq_iff.
  assumption.
Qed.

Lemma type_eq_iff t1 t2:
  ((fprecp t1 = fprecp t2 /\ femax t1 = femax t2) <-> t1 = t2).
Proof.
  split.
  {
    destruct 1; auto using type_ext.
  }
  intuition congruence.
Qed.

Import Bool.

Definition type_eqb t1 t2 :=
  Pos.eqb (fprecp t1) (fprecp t2) && Z.eqb (femax t1) (femax t2).

Lemma type_eqb_eq t1 t2:
  (type_eqb t1 t2 = true <-> t1 = t2).
Proof.
  unfold type_eqb.
  rewrite andb_true_iff.
  rewrite Pos.eqb_eq.
  rewrite Z.eqb_eq.
  apply type_eq_iff.
Qed.

Lemma type_eq_dec (t1 t2: type): 
  {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1. destruct t2.
  destruct (Pos.eq_dec fprecp0 fprecp1); [ |   right; intro K; injection K; congruence ].
  subst.
  destruct (Z.eq_dec femax0 femax1); [ |   right; intro K; injection K; congruence ].
  subst.
  left.
  apply type_ext; auto. 
Defined.

Lemma fprec_lt_femax' ty: (fprec ty < femax ty)%Z.
Proof.
  apply ZLT_elim.
  apply fprec_lt_femax_bool.
Qed.

(* For transparency purposes *)
Lemma fprec_lt_femax ty: (fprec ty < femax ty)%Z.
Proof.
  unfold Z.lt.
  destruct (Z.compare (fprec ty) (femax ty)) eqn:EQ; auto;
  generalize (fprec_lt_femax' ty);
    intro K;
    unfold Z.lt in K;
    congruence.
Defined.

Lemma fprecp_not_one ty:
    fprecp ty <> 1%positive
.
Proof.
  apply Pos.eqb_neq.
  apply negb_true_iff.
  apply BOOL_elim.
  apply fprecp_not_one_bool.
Qed.

Lemma fprec_eq ty: fprec ty = Z.pos (fprecp ty).
Proof. reflexivity. Qed.

Global Instance fprec_gt_0: forall ty, Prec_gt_0 (fprec ty).
Proof.
  intros.
  reflexivity.
Defined.

Definition ftype ty := binary_float (fprec ty) (femax ty).

Definition FT2R {t: type} : ftype t -> R := B2R (fprec t) (femax t).

Definition nan_payload prec emax : Type := {x : binary_float prec emax
                                                          | is_nan prec emax x = true}.

Class Nans: Type :=
  {
    conv_nan: forall ty1 ty2, 
                binary_float (fprec ty1) (femax ty1) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
                nan_payload (fprec ty2) (femax ty2)
    ;
    plus_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        nan_payload (fprec ty) (femax ty)
    ;
    mult_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        nan_payload (fprec ty) (femax ty)
    ;
    div_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        nan_payload (fprec ty) (femax ty)
    ;
    abs_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
        nan_payload (fprec ty) (femax ty)
    ;
    opp_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
        nan_payload (fprec ty) (femax ty)
    ;
    sqrt_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) ->
        nan_payload (fprec ty) (femax ty)
    ;
    fma_nan:
      forall ty,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        nan_payload (fprec ty) (femax ty)
  }.

Definition nan_pl_eqb {prec1 emax1 prec2 emax2} 
         (n1: nan_payload prec1 emax1) (n2: nan_payload prec2 emax2) :=
 match proj1_sig n1, proj1_sig n2 with
 | B754_nan _ _ b1 pl1 _, B754_nan _ _ b2 pl2 _ => Bool.eqb b1 b2 && Pos.eqb pl1 pl2
 | _, _ => true
 end.

Definition nan_pl_eqb' {prec1 emax1 prec2 emax2}
         (n1: nan_payload prec1 emax1) (n2: nan_payload prec2 emax2) : bool.
destruct n1 as [x1 e1].
destruct n2 as [x2 e2].
unfold is_nan in *.
destruct x1; try discriminate.
destruct x2; try discriminate.
apply (Bool.eqb s s0 && Pos.eqb pl pl0).
Defined.

Lemma nan_pl_sanity_check:
   forall prec1 emax1 prec2 emax2 n1 n2, 
   @nan_pl_eqb' prec1 emax1 prec2 emax2 n1 n2 = @nan_pl_eqb prec1 emax1 prec2 emax2 n1 n2.
Proof.
intros.
destruct n1 as [x1 e1], n2 as [x2 e2].
simpl.
unfold is_nan in *.
destruct x1; try discriminate.
destruct x2; try discriminate.
unfold nan_pl_eqb. simpl.
auto.
Qed.

Lemma nan_payload_eqb_eq prec emax (n1 n2: nan_payload prec emax):
  (nan_pl_eqb n1 n2 = true <-> n1 = n2).
Proof.
  unfold nan_pl_eqb.
  destruct n1; destruct n2; simpl.
  destruct x; try discriminate.
  destruct x0; try discriminate.
  split; intros.
 -
  rewrite andb_true_iff in H. destruct H.
  rewrite eqb_true_iff in H.
  rewrite Pos.eqb_eq in H0.
  assert (e=e0) by 
     (apply Eqdep_dec.eq_proofs_unicity; destruct x; destruct y; intuition congruence).
   subst s0 pl0 e0.
 assert (e1=e2) by 
     (apply Eqdep_dec.eq_proofs_unicity; destruct x; destruct y; intuition congruence).
   subst e2.
  reflexivity.
 - inversion H; clear H; subst.
    rewrite eqb_reflx. rewrite Pos.eqb_refl. reflexivity.
Qed.

Definition binary_float_eqb {prec1 emax1 prec2 emax2} (b1: binary_float prec1 emax1) (b2: binary_float prec2 emax2): bool :=
  match b1, b2 with
    | B754_zero _ _ b1, B754_zero _ _ b2 => Bool.eqb b1 b2
    | B754_infinity _ _ b1, B754_infinity _ _ b2 => Bool.eqb b1 b2
    | B754_nan _ _ b1 n1 _, B754_nan _ _ b2 n2 _ => Bool.eqb b1 b2 && Pos.eqb n1 n2
    | B754_finite _ _ b1 m1 e1 _, B754_finite _ _ b2 m2 e2 _ =>
      Bool.eqb b1 b2 && Pos.eqb m1 m2 && Z.eqb e1 e2
    | _, _ => false
  end.

Lemma binary_float_eqb_eq prec emax (b1 b2: binary_float prec emax):
  binary_float_eqb b1 b2 = true <-> b1 = b2.
Proof.
  destruct b1; destruct b2; simpl;
  
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
- split; intro.
   + destruct H; subst; f_equal.
      apply Eqdep_dec.eq_proofs_unicity.
      destruct x; destruct y; intuition congruence.
   + inversion H; clear H; subst; auto.
- split; intro.
   + destruct H as [[? ?] ?]. 
      apply Z.eqb_eq in H1. subst.
      f_equal.       
      apply Eqdep_dec.eq_proofs_unicity.
      destruct x; destruct y; intuition congruence.
   + inversion H; clear H; subst; split; auto.
       apply Z.eqb_eq. auto.
Qed.

Definition binary_float_equiv {prec emax} 
(b1 b2: binary_float prec emax): Prop :=
  match b1, b2 with
    | B754_zero _ _ b1, B754_zero _ _ b2 => b1 = b2
    | B754_infinity _ _ b1, B754_infinity _ _ b2 =>  b1 = b2
    | B754_nan _ _ _ _ _, B754_nan _ _ _ _ _ => True
    | B754_finite _ _ b1 m1 e1 _, B754_finite _ _ b2 m2 e2 _ =>
      b1 = b2 /\  m1 = m2 /\ e1 = e2
    | _, _ => False
  end.

Lemma binary_float_equiv_refl prec emax (b1: binary_float prec emax):
     binary_float_equiv b1 b1.
Proof.
destruct b1; simpl; auto. Qed.

Lemma binary_float_equiv_sym prec emax (b1 b2: binary_float prec emax):
     binary_float_equiv b1 b2 -> binary_float_equiv b2 b1.
Proof.
intros.
destruct b1; destruct b2; simpl; auto. 
destruct H as (A & B & C); subst; auto. Qed.

Lemma binary_float_equiv_trans prec emax (b1 b2 b3: binary_float prec emax):
  binary_float_equiv b1 b2 -> 
  binary_float_equiv b2 b3 -> binary_float_equiv b1 b3.
Proof. 
intros.
destruct b1; destruct b2; destruct b3; simpl; auto.
all: try (destruct H; destruct H0; reflexivity).    
destruct H; destruct H0. subst. destruct H2; destruct H1; subst; auto. 
Qed.

Lemma binary_float_eqb_equiv prec emax (b1 b2: binary_float prec emax):
   binary_float_eqb b1 b2 = true -> binary_float_equiv b1 b2 .
Proof.
  destruct b1; destruct b2; simpl;
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
      rewrite ?Z.eqb_eq; 
      rewrite ?and_assoc; auto.  
Qed.

Lemma binary_float_finite_equiv_eqb prec emax (b1 b2: binary_float prec emax):
is_finite prec emax b1  = true -> 
binary_float_equiv b1 b2 -> binary_float_eqb b1 b2 = true .
Proof.
  destruct b1; destruct b2; simpl;
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
      rewrite ?Z.eqb_eq; 
      rewrite ?and_assoc; auto.  
Qed.

Lemma binary_float_eq_equiv prec emax (b1 b2: binary_float prec emax):
   b1 = b2 -> binary_float_equiv b1 b2.
Proof.
intros.
apply binary_float_eqb_eq in H. 
apply binary_float_eqb_equiv in H; apply H.
Qed.

Lemma binary_float_equiv_eq prec emax (b1 b2: binary_float prec emax):
   binary_float_equiv b1 b2 -> is_nan _ _ b1 =  false -> b1 = b2.
Proof.
intros. 
assert (binary_float_eqb b1 b2 = true). 
- destruct b1; destruct b2; simpl in H; subst; simpl; auto;
  try discriminate;
  try apply eqb_reflx.
rewrite ?andb_true_iff. 
destruct H; rewrite H.
destruct H1; rewrite H1; rewrite H2; split. split; auto. 
apply eqb_reflx. 
apply Pos.eqb_eq; reflexivity.
apply Z.eqb_eq; reflexivity.
- apply binary_float_eqb_eq; apply H1. 
Qed.

Lemma binary_float_inf_equiv_eqb prec emax (b1 b2: binary_float prec emax):
is_finite prec emax b1  = false -> 
is_nan prec emax b1  = false -> 
binary_float_equiv b1 b2 -> binary_float_eqb b1 b2 = true .
Proof.
  destruct b1; destruct b2; simpl;
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
Qed.


Lemma binary_float_equiv_nan prec emax (b1 b2: binary_float prec emax):
binary_float_equiv b1 b2 -> is_nan _ _ b1 = true -> is_nan _ _ b2 = true.
Proof. 
intros.
destruct b1; simpl in H0; try discriminate.
destruct b2; simpl in H; try contradiction.
simpl; reflexivity.
Qed.

Lemma exact_inverse (prec emax : Z) 
(prec_gt_0_ : FLX.Prec_gt_0 prec)
(Hmax : (prec < emax)%Z) :
forall (b1 b2: binary_float prec emax),
is_finite_strict prec emax b1 = false -> 
Bexact_inverse prec emax prec_gt_0_ Hmax b1 = Some b2 -> False.
Proof. 
intros. 
apply Bexact_inverse_correct in H0; destruct H0; rewrite H0 in H; discriminate.
Qed.

Definition B2F {prec emax} (f : binary_float prec emax):
  Defs.float Zaux.radix2 :=
match f with
| @B754_finite _ _ s m e _ =>
      {|
      Defs.Fnum := Zaux.cond_Zopp s (Z.pos m);
      Defs.Fexp := e |}
| _ =>
  {|
    Defs.Fnum := 0;
    Defs.Fexp := 0
  |}
end.

Lemma B2F_F2R_B2R {prec emax} f:
  B2R prec emax f = Defs.F2R (B2F f).
Proof.
  destruct f; simpl; unfold Defs.F2R; simpl; ring.
Qed.

Definition F2R beta (f: Defs.float beta): R :=
  match f with
    | Defs.Float _ Fnum Fexp =>
      IZR Fnum * Raux.bpow beta Fexp
  end.

Lemma F2R_eq beta f:
  F2R beta f = Defs.F2R f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma type_lub_lt a1 a2 b1 b2:
  (ZLT (Z.pos a1) b1) ->
  (ZLT (Z.pos a2) b2) ->
  ZLT (Z.pos (Pos.max a1 a2)) (Z.max b1 b2).
Proof.
  intros.  
  unfold ZLT, BOOL.
  (* this is necessary for transparent proof reduction *)
  destruct (Z.ltb (Z.pos (Pos.max a1 a2)) (Z.max b1 b2)) eqn:LT.
  {
    exact I.
  }
  cut (Z.ltb (Z.pos (Pos.max a1 a2)) (Z.max b1 b2) = true); [ congruence | ].
  apply Z.ltb_lt.
  apply ZLT_elim in H.
  apply ZLT_elim in H0. 
  rewrite Pos2Z.inj_max.
  rewrite Z.max_lt_iff.
  repeat rewrite Z.max_lub_lt_iff.
  lia.
Defined.

Lemma  type_lub_neq_one a1 a2:
  BOOL (negb (Pos.eqb a1 xH)) ->
  BOOL (negb (Pos.eqb a2 xH)) ->
  BOOL (negb (Pos.eqb (Pos.max a1 a2) xH))
.
Proof.
  intros.
  (* this is necessary for transparent proof reduction *)
  destruct (negb (Pos.eqb (Pos.max a1 a2) 1)) eqn:EQB.
  {
    exact I.
  }
  generalize (Pos.max_spec_le a1 a2); intuition congruence.
Defined.

Definition type_le t1 t2 : Prop := (fprec t1 <= fprec t2)%Z /\ (femax t1 <= femax t2)%Z.

Definition type_leb t1 t2 : bool :=
  Z.leb (fprec t1) (fprec t2) && Z.leb (femax t1) (femax t2)
.

Lemma type_leb_le t1 t2:
  type_leb t1 t2 = true <-> type_le t1 t2.
Proof.
  unfold type_le, type_leb.
  rewrite andb_true_iff.
  repeat rewrite Z.leb_le.
  tauto.
Qed.

Lemma type_le_refl t: type_le t t.
Proof.
  unfold type_le; auto with zarith.
Qed.

Definition type_lub' t1 t2 := TYPE _ _ (type_lub_lt _ _ _ _ (fprec_lt_femax_bool t1) (fprec_lt_femax_bool t2)) (type_lub_neq_one _ _ (fprecp_not_one_bool t1) (fprecp_not_one_bool t2)).

Definition type_lub t1 t2 :=
  (* we need this version so that it can compute more efficiently in the
   common cases, otherwise proofs blow up. *)
 if type_leb t1 t2 then t2 else if type_leb t2 t1 then t1 else type_lub' t1 t2.

Lemma type_lub'_eq:
 forall t1 t2, type_lub' t1 t2 = type_lub t1 t2.
Proof.
intros.
unfold type_lub.
pose proof (type_leb_le t1 t2).
destruct (type_leb t1 t2).
destruct (proj1 H (eq_refl _)).
unfold fprec in *.
apply type_ext'.
unfold fprec, type_lub'; simpl; lia.
simpl; lia. 
clear H.
pose proof (type_leb_le t2 t1).
destruct (type_leb t2 t1).
destruct (proj1 H (eq_refl _)).
unfold fprec in *.
apply type_ext'.
unfold fprec, type_lub'; simpl; lia.
simpl; lia.
auto.
Qed. 


Lemma type_lub_left t1 t2: type_le t1 (type_lub t1 t2).
Proof.
  rewrite <- type_lub'_eq.
  unfold type_lub'.
  unfold type_le.
  simpl.
  unfold fprec.
  simpl.
  split.
  {
    rewrite Pos2Z.inj_max.
    apply Z.le_max_l.
  }
  apply Z.le_max_l.
Qed.

Lemma type_lub_right t1 t2: type_le t2 (type_lub t1 t2).
Proof.
  rewrite <- type_lub'_eq.
  unfold type_lub'.
  unfold type_le.
  simpl.
  unfold fprec.
  simpl.
  split.
  {
    rewrite Pos2Z.inj_max.
    apply Z.le_max_r.
  }
  apply Z.le_max_r.
Qed.

Lemma fprec_gt_one ty:
  (1 < fprec ty)%Z.
Proof.
  generalize (fprec_gt_0 ty).
  unfold FLX.Prec_gt_0.
  unfold fprec.
  intros.
  generalize (fprecp_not_one ty).
  intros.
  assert (Z.pos (fprecp ty) <> 1%Z) by congruence.
  lia.
Qed.

Corollary any_nan ty: nan_payload (fprec ty) (femax ty).
Proof.
 red.
  set (a:=1%positive).
  assert (H: Binary.nan_pl (fprec ty) a = true).
  unfold Binary.nan_pl.
  subst a. 
   pose proof (fprec_gt_one ty). simpl. lia.
  exists (Binary.B754_nan (fprec ty) (femax ty) false 1 H).
  reflexivity.
Defined.

(* Perhaps VarType shouldn't go in FPCore, since it has something
 to do with reification; but it's needed in FPCompCert, which doesn't
 want to import FPLang, so we make do this way. *)
Class VarType (V: Type): Type := 
  {
    var_eqb: V -> V -> bool;
    var_eqb_eq: forall v1 v2, var_eqb v1 v2 = true <-> v1 = v2
  }.

Section WITHNANS.
Context {NANS: Nans}.

Definition cast (tto: type) {tfrom: type} (f: ftype tfrom): ftype tto :=
  match type_eq_dec tfrom tto with
    | left r => eq_rect _ _ f _ r
    | _ => Bconv (fprec tfrom) (femax tfrom) (fprec tto) (femax tto)
                        (fprec_gt_0 _) (fprec_lt_femax _) (conv_nan _ _) BinarySingleNaN.mode_NE f
  end.

Definition cast_lub_l t1 t2 := @cast (type_lub t1 t2) t1.
Definition cast_lub_r t1 t2 := @cast (type_lub t1 t2) t2.

Lemma cast_finite tfrom tto:
  type_le tfrom tto ->
  forall f,
  is_finite _ _ f = true ->
  is_finite _ _ (@cast tto tfrom f) = true.
Proof.
  unfold cast.
  intros.
  destruct (type_eq_dec tfrom tto).
  {
    subst. assumption.
  }
  destruct H.
  apply Bconv_widen_exact; auto with zarith.
  typeclasses eauto.
Qed.

Lemma cast_eq tfrom tto:
  type_le tfrom tto ->
  forall f,
    is_finite _ _ f = true ->
    B2R _ _ (@cast tto tfrom f) = B2R _ _ f.
Proof.
  unfold cast.
  intros.
  destruct (type_eq_dec tfrom tto).
  {
    subst.
    reflexivity.
  }
  destruct H.
  apply Bconv_widen_exact; auto with zarith.
  typeclasses eauto.
Qed.

Lemma cast_id ty f:
    @cast ty ty f = f.
Proof.
  unfold cast.
  destruct (type_eq_dec ty ty); try congruence.
  assert (e = eq_refl) as K.
  {
    apply Eqdep_dec.eq_proofs_unicity.
    intros.
    unfold not.
    rewrite <- type_eqb_eq.
    destruct (type_eqb x y); intuition congruence.
  }
  rewrite K.
  reflexivity.
Qed.

Lemma type_lub_comm a b:
  type_lub a b = type_lub b a.
Proof.
  rewrite <- !type_lub'_eq.
  apply type_ext; simpl; eauto using Pos.max_comm, Z.max_comm.
Qed.

Lemma type_lub_r a b:
  type_le a b ->
  type_lub a b = b.
Proof.
  rewrite <- !type_lub'_eq.
  inversion 1.
  apply type_ext; simpl; eauto using Pos.max_r, Z.max_r.
Qed.

Lemma type_lub_id a:
  type_lub a a = a.
Proof.
  rewrite <- !type_lub'_eq.
  apply type_ext; simpl; eauto using Pos.max_id, Z.max_id.
Qed.

Definition BINOP (op: ltac:( let t := type of Bplus in exact t ) ) op_nan ty 
    : ftype ty -> ftype ty -> ftype ty 
    := op _ _ (fprec_gt_0 ty) (fprec_lt_femax ty) (op_nan ty) BinarySingleNaN.mode_NE.

Definition BPLUS := BINOP Bplus plus_nan.
Definition BMINUS := BINOP Bminus plus_nan. (* NOTE: must be same as the one used for plus *)
Definition BMULT := BINOP Bmult mult_nan.
Definition BDIV := BINOP Bdiv div_nan.
Definition BABS ty := Babs _ (femax ty) (abs_nan ty).
Definition BOPP ty := Bopp _ (femax ty) (opp_nan ty).


Definition UNOP (op: ltac:( let t := type of Bsqrt in exact t ) ) op_nan ty 
    : ftype ty -> ftype ty
    := op _ _ (fprec_gt_0 ty) (fprec_lt_femax ty) (op_nan ty) BinarySingleNaN.mode_NE.

Definition BSQRT :=  UNOP Bsqrt sqrt_nan.

End WITHNANS.

Definition Norm {T} (x: T) := x.
Definition Denorm {T} (x: T) := x.
Definition Sterbenz {T} (x: T) := x.

Definition Tsingle := TYPE 24 128 I I.
Definition Tdouble := TYPE 53 1024 I I.

Lemma single_le_double:
  type_le Tsingle Tdouble.
Proof.
  constructor; compute; congruence.
Qed.

Definition extend_comp (c: comparison) (b: bool) (d: option comparison) :=
 match d with
 | None => false
 | Some c' =>
 match c, b, c' with
 | Gt, true, Gt => true
 | Gt, false, Lt => true
 | Gt, false, Eq => true
 | Eq, true, Eq => true
 | Eq, false, Gt => true
 | Eq, false, Lt => true
 | Lt, true, Lt => true
 | Lt, false, Gt => true
 | Lt, false, Eq => true
 | _, _, _ => false
 end
 end.

Definition BCMP (ty: type) (c: comparison) (b: bool) (x y: ftype ty) :=
  extend_comp c b (Binary.Bcompare (fprec ty) (femax ty) x y).

Notation "x + y" := (BPLUS Tsingle x y) (at level 50, left associativity) : float32_scope.
Notation "x - y"  := (BMINUS Tsingle x y) (at level 50, left associativity) : float32_scope.
Notation "x * y"  := (BMULT Tsingle x y) (at level 40, left associativity) : float32_scope.
Notation "x / y"  := (BDIV Tsingle x y) (at level 40, left associativity) : float32_scope.
Notation "- x" := (BOPP Tsingle x) (at level 35, right associativity) : float32_scope.
Notation "x <= y" := (BCMP Tsingle Gt false x y) (at level 70, no associativity) : float32_scope. 
Notation "x < y" := (BCMP Tsingle Gt true y x) (at level 70, no associativity) : float32_scope. 
Notation "x >= y" := (BCMP Tsingle Lt false x y) (at level 70, no associativity) : float32_scope. 
Notation "x > y" := (BCMP Tsingle Gt true x y) (at level 70, no associativity) : float32_scope. 
Notation "x <= y <= z" := (x <= y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y < z" := (x < y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.

Notation "x + y" := (BPLUS Tdouble x y) (at level 50, left associativity) : float64_scope.
Notation "x - y"  := (BMINUS Tdouble x y) (at level 50, left associativity) : float64_scope.
Notation "x * y"  := (BMULT Tdouble x y) (at level 40, left associativity) : float64_scope.
Notation "x / y"  := (BDIV Tdouble x y) (at level 40, left associativity) : float64_scope.
Notation "- x" := (BOPP Tdouble x) (at level 35, right associativity) : float64_scope.
Notation "x <= y" := (BCMP Tdouble Gt false x y) (at level 70, no associativity) : float64_scope. 
Notation "x < y" := (BCMP Tdouble Gt true y x) (at level 70, no associativity) : float64_scope. 
Notation "x >= y" := (BCMP Tdouble Lt false x y) (at level 70, no associativity) : float64_scope. 
Notation "x > y" := (BCMP Tdouble Gt true x y) (at level 70, no associativity) : float64_scope. 
Notation "x <= y <= z" := (x <= y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y < z" := (x < y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.


Definition build_nan_full {prec emax} (pl: nan_payload prec emax) :=
  let n := proj1_sig pl in F754_nan (Bsign _ _ n) (get_nan_pl _ _ n).

Ltac const_pos p :=
  lazymatch p with xH => idtac | xI ?p => const_pos p | xO ?p => const_pos p end.

Ltac const_Z i := 
  lazymatch i with
  | Zpos ?p => const_pos p 
  | Zneg ?p => const_pos p
  | Z0 => idtac 
 end.

Ltac const_bool b := lazymatch b with true => idtac | false => idtac end.

Ltac const_float f :=
 lazymatch f with
 | Float_notations.b32_B754_zero ?s => const_bool s
 | Float_notations.b32_B754_finite ?s ?m ?e _  => const_bool s; const_pos m; const_Z e
 | Float_notations.b32_B754_infinity ?s  => const_bool s
 | Float_notations.b64_B754_zero ?s => const_bool s
 | Float_notations.b64_B754_finite ?s ?m ?e  _ => const_bool s; const_pos m; const_Z e
 | Float_notations.b64_B754_infinity ?s  => const_bool s
 | B754_zero ?prec ?emax ?s => const_Z prec; const_Z emax; const_bool s
 | B754_finite ?prec ?emax ?s ?m ?e _ => const_Z prec; const_Z emax; const_bool s; const_pos m; const_Z e
 | B754_infinity ?prec ?emax ?s => const_Z prec; const_Z emax; const_bool s
 | B754_nan ?prec ?emax ?s ?p _ => const_Z prec; const_Z emax; const_bool s; const_pos p
 end.

Lemma B754_finite_replace_proof:
  forall prec emax s m e H1 H2,
  B754_finite prec emax s m e H1 = B754_finite prec emax s m e H2.
Proof.
intros.
f_equal.
apply  Classical_Prop.proof_irrelevance.
Qed .

Ltac compute_float_operation E :=
  (* E should be a float expression in the goal below the line,
     that is known to compute to B754_finite;
     for example, a binary operator (Bdiv, Bplus, etc.) applied
     to constant prec,emax and two constant arguments.
     This tactic replaces E with its computed value, and in particular
     where the proof  of SpecFloat.bounded is simply (eq_refl true).  *)
           let z := eval hnf in E in
           lazymatch z with
           | B754_finite ?prec ?emax ?s ?m ?e ?H =>
             let w := constr:(B754_finite prec emax s m e) in
             let w := eval compute in w in
             let w := constr:(w (eq_refl true)) in
             replace E with w by apply B754_finite_replace_proof
           | B754_zero ?prec ?emax ?s => 
                  let w := constr:(B754_zero prec emax s) in 
                  let w := eval compute in w in
                   change E with w
           end.

Ltac compute_binary_floats :=
repeat (match goal with
| |- context [@BDIV ?NANS ?t ?x1 ?x2] =>
           const_float x1; const_float x2;
           let c := constr:(@BDIV NANS t) in 
           let d := eval  cbv [BINOP BDIV BMULT BPLUS BMINUS BOPP] in c in 
           change c with d
| |- context [@BMULT ?NANS ?t ?x1 ?x2] =>
           const_float x1; const_float x2;
           let c := constr:(@BMULT NANS t) in 
           let d := eval  cbv [BINOP BDIV BMULT BPLUS BMINUS BOPP] in c in 
           change c with d
| |- context [@BPLUS ?NANS ?t ?x1 ?x2] =>
           const_float x1; const_float x2;
           let c := constr:(@BPLUS NANS t) in 
           let d := eval  cbv [BINOP BDIV BMULT BPLUS BMINUS BOPP] in c in 
           change c with d
| |- context [@BMINUS ?NANS ?t ?x1 ?x2] =>
           const_float x1; const_float x2;
           let c := constr:(@BMINUS NANS t) in 
           let d := eval  cbv [BINOP BDIV BMULT BPLUS BMINUS BOPP] in c in 
           change c with d
| |- context [Bdiv ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bdiv prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
| |- context [Bmult ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bmult prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
| |- context [Bplus ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bplus prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
| |- context [Bminus ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bminus prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
end; simpl FF2B);
 fold Float_notations.b32_B754_zero;
 fold Float_notations.b32_B754_finite;
 fold Float_notations.b32_B754_infinity;
 fold Float_notations.b64_B754_zero;
 fold Float_notations.b64_B754_finite;
 fold Float_notations.b64_B754_infinity.

Import Float_notations.

Local Lemma test_compute_binary_floats {NANS: Nans}:
  (BPLUS Tsingle 1.5 3.5 = BDIV Tsingle 10.0 2)%F32.
Proof. compute_binary_floats. auto. Qed.

Definition Zconst (t: type) : Z -> ftype t :=
  BofZ (fprec t) (femax t) (Pos2Z.is_pos (fprecp t)) (fprec_lt_femax t).

Lemma BPLUS_commut {NANS: Nans}: forall t a b, 
    plus_nan t a b = plus_nan t b a -> BPLUS t a b = BPLUS t b a.
Proof.
intros. apply Bplus_commut; auto.
Qed.

Lemma BMULT_commut {NANS: Nans}: forall t a b, 
    mult_nan t a b = mult_nan t b a -> BMULT t a b = BMULT t b a.
Proof.
intros. apply Bmult_commut; auto.
Qed.
