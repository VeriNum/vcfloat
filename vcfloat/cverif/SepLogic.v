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

A simple separation logic for the CompCert memory model.
*)

Require Import Arith.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import Relations.
Require Import Morphisms.
Require Import Lia.

Lemma NoDup_app_elim {A: Type} (l1 l2: list A):
  NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2 /\ (forall a: A, In a l1 -> In a l2 -> False).
Proof.
  induction l1; simpl.
  {
    intuition auto using NoDup_nil.
  }
  inversion 1; subst.
  specialize (IHl1 ltac:( assumption ) ).
  destruct IHl1 as (? & ? & ? ).
  rewrite in_app in *.  
  split.
  {
    constructor; auto.
  }
  firstorder.
  congruence.
Qed.

Lemma NoDup_app_intro {A: Type}: forall l1: list A,
  NoDup l1 ->
  forall l2, NoDup l2 ->
             (forall a: A, In a l1 -> In a l2 -> False) ->
             NoDup (l1 ++ l2).
Proof.
  induction l1; simpl; auto.
  inversion 1; subst.
  intros.
  constructor; eauto.
  rewrite in_app.
  firstorder.
Qed.

Lemma NoDup_app_iff {A: Type}:
  forall l1 l2,
    NoDup (l1 ++ l2) <-> 
    (NoDup l1 /\ NoDup l2 /\ (forall a: A, In a l1 -> In a l2 -> False)).
Proof.
  intros.
  generalize (NoDup_app_intro (A := A)).
  generalize (NoDup_app_elim (A := A)).
  firstorder.
Qed.

Lemma NoDup_comm {A: Type}:
  forall (l1 l2: list A),
    NoDup (l1 ++ l2) ->
    NoDup (l2 ++ l1).
Proof.
  intros l1 l2 H.
  apply NoDup_app_elim in H.
  destruct H as (? & ? & ?).
  apply NoDup_app_intro; auto.
  firstorder.
Qed.

Inductive list_comm {A: Type}: list A -> list A -> Prop :=
| list_comm_intro l1 l2:
    list_comm (l1 ++ l2) (l2 ++ l1)
| list_comm_refl:
    Reflexive list_comm
| list_comm_trans:
    Transitive list_comm
| list_comm_compat:
    Proper (list_comm ==> list_comm ==> list_comm) (@app A)
.

Global Existing Instances list_comm_refl list_comm_trans list_comm_compat.

Global Instance: forall (A: Type), Symmetric (list_comm (A := A)).
Proof.
  red.
  induction 1.
  {
    constructor.
  }
  {
    reflexivity.
  }
  {
    etransitivity; eauto.
  }
  {
    eapply list_comm_compat; eauto.
  }
Qed.

Lemma list_comm_in_aux {A} (a: A) l1 l2:
  list_comm l1 l2 ->
  In a l1 -> In a l2.
Proof.
  induction 1; auto.
  {
    repeat rewrite in_app.
    tauto.
  }
  {
    repeat rewrite in_app.
    tauto.
  }    
Qed.

Global Instance list_comm_in {A: Type}:
    Proper (eq ==> list_comm ==> iff)
           (In (A := A)).
Proof.
  do 2 red.
  intros until 1. subst.
  red.
  intros x y0 H.
  split.
  {
    apply list_comm_in_aux.
    assumption.
  }
  apply list_comm_in_aux.
  symmetry.
  assumption.
Qed.

Lemma NoDup_list_comm_aux {A: Type} l1 l2:
  list_comm l1 l2 ->
  NoDup l1 -> NoDup (A := A) l2.
Proof.
  induction 1; auto.
  {
    apply NoDup_comm.
  }
  repeat rewrite NoDup_app_iff.
  generalize (fun a => list_comm_in a a (eq_refl _) _ _ H).
  generalize (fun a => list_comm_in a a (eq_refl _) _ _ H0).
  firstorder.
Qed.    

Global Instance NoDup_list_comm {A: Type}:
  Proper (list_comm ==> iff) (NoDup (A := A)).
Proof.
  do 2 red.
  split.
  {
    apply NoDup_list_comm_aux.
    assumption.
  }
  apply NoDup_list_comm_aux.
  symmetry.
  assumption.
Qed.

Local Instance map_ext {A B: Type}:
  Proper ((eq ==> eq) ==> eq ==> eq) (map (A := A) (B := B)).
Proof.
  do 3 red.
  intros x y H.
  red in H.
  intros x0 y0 H0.
  subst y0.
  induction x0; simpl; auto.
  f_equal; auto.
Qed.

Global Instance list_comm_map {A B: Type}:
  Proper ((eq ==> eq) ==> list_comm ==> list_comm) (map (A := A) (B := B)).
Proof.
  do 3 red.
  intros x y H x0 y0 H0.
  rewrite H.
  induction H0.
  {
    repeat rewrite map_app.
    apply list_comm_intro.
  }
  {
    reflexivity.
  }
  {
    etransitivity; eauto.
  }
  {
    repeat rewrite map_app.
    eapply list_comm_compat; eauto.
  }
Qed.

Definition pred := list ((Values.block * Z) * (permission * option memval)).

Definition holds (P: pred) (m: mem) :=
  (
    forall b o p v, In ((b, o), (p, v)) P ->
                    (
                      Mem.perm m b o Cur p /\
                      match v with
                        | None => True
                        | Some v' =>
                          Mem.loadbytes m b o 1 = Some (v' :: nil)
                      end
                    )
  ) /\
  NoDup (map fst P)
.

Lemma holds_nil m: holds nil m.
Proof.
  split; simpl; intuition.
  apply NoDup_nil.
Qed.

Lemma holds_cons_nil a m:
  holds (a :: nil) m <->
  let '((b, o), (p, v)) := a in
  Mem.perm m b o Cur p /\
  match v with
    | None => True
    | Some v' =>
      Mem.loadbytes m b o 1 = Some (v' :: nil)
  end.
Proof.
  split.
  {
    destruct 1 as (H & N).
    destruct a as [[b o] [p v]].
    apply H.
    simpl; auto.
  }
  intros H.
  split.
  {
    inversion 1; subst; try contradiction.
    assumption.
  }
  constructor; simpl; auto.
  constructor.
Qed.

Lemma holds_weak_left m P1 P2:
  holds (P1 ++ P2) m ->
  holds P1 m.
Proof.
  destruct 1 as (H & N).
  split.
  {
    intros.
    apply H.
    apply in_or_app.
    auto.
  }
  rewrite map_app in N.
  apply NoDup_app_elim in N.
  tauto.
Qed.

Lemma holds_list_comm_aux m P1 P2:
  list_comm P1 P2 ->
  holds P1 m ->
  holds P2 m.
Proof.
  unfold holds.
  intros H H0.
  setoid_rewrite <- H.
  assumption.
Qed.

Global Instance holds_list_comm:
  Proper (list_comm ==> eq ==> iff) holds.
Proof.
  split; subst; apply holds_list_comm_aux; auto.
  symmetry; auto.
Qed.

Lemma holds_weak_right m P1 P2:
  holds (P1 ++ P2) m ->
  holds P2 m.
Proof.
  rewrite list_comm_intro.
  apply holds_weak_left.
Qed.

Lemma holds_disjoint P1 P2 m:
  holds (P1 ++ P2) m ->
  (forall bo, In bo (map fst P1) -> In bo (map fst P2) -> False).
Proof.
  destruct 1 as (H & N).
  rewrite map_app in N.
  apply NoDup_app_elim in N.
  tauto.
Qed.

Lemma holds_star P1 P2 m:
  holds P1 m ->
  holds P2 m ->
  (forall bo, In bo (map fst P1) -> In bo (map fst P2) -> False) ->
  holds (P1 ++ P2) m.
Proof.
  destruct 1 as (H1 & N1).
  destruct 1 as (H2 & N2).
  split.
  {
    intros b o p v H0.
    rewrite in_app in H0.
    destruct H0; eauto.
  }
  rewrite map_app.
  apply NoDup_app_intro; auto.
Qed.

Lemma holds_star_iff P1 P2 m:
  holds (P1 ++ P2) m <->
  (
    holds P1 m /\
    holds P2 m /\
    (forall bo, In bo (map fst P1) -> In bo (map fst P2) -> False)
  ).
Proof.
  generalize (holds_star P1 P2 m).
  generalize (holds_weak_left m P1 P2).
  generalize (holds_weak_right m P1 P2).
  generalize (holds_disjoint P1 P2 m).
  tauto.
Qed.

Lemma app_cons_nil {A: Type} (a: A) (l: list A):
  (a :: nil) ++ l = a :: l.
Proof.
  reflexivity.
Qed.

Lemma holds_ext m1 m2
  (PERM: forall b o p,
     Mem.perm m1 b o Cur p -> Mem.perm m2 b o Cur p)
  (LOAD: forall b o v,
           Mem.loadbytes m1 b o 1 = Some v ->
           Mem.loadbytes m2 b o 1 = Some v)
  P
:
  holds P m1 ->
  holds P m2.
Proof.
  induction P; simpl; auto using holds_nil.
  rewrite <- app_cons_nil.
  repeat rewrite holds_star_iff.
  simpl.
  destruct 1 as (A & ? & ?).
  split; auto.
  inversion A; subst.
  rewrite holds_cons_nil in A |- * .
  destruct a as [[b o] [p v]].
  simpl in *.
  destruct A.
  split; auto.
  destruct v; auto.
Qed.

(* This is the key transport lemma. It actually shows that there is no need to reprove
   disjointness of locations. *)
Theorem holds_ext_strong m1 m2 P:
  forall
    (PERM: forall b o p v,
             In ((b, o), (p, v)) P ->
             Mem.perm m1 b o Cur p -> Mem.perm m2 b o Cur p)
    (LOAD: forall b o p v,
             In ((b, o), (p, Some v)) P ->
             Mem.loadbytes m1 b o 1 = Some (v :: nil) ->
             Mem.loadbytes m2 b o 1 = Some (v :: nil))
  ,
    holds P m1 ->
    holds P m2.
Proof.
  induction P; simpl; auto using holds_nil.
  intros PERM LOAD H.
  rewrite <- app_cons_nil in H |- * by reflexivity.
  rewrite holds_star_iff in H |- * .
  destruct H as (A & ? & ?).
  split.
  {
    rewrite holds_cons_nil in A |- * .
    destruct a as [[b o] [p v]].
    simpl in *.
    destruct A.
    split; eauto.
    destruct v; eauto.
  }
  split; eauto.
  eapply IHP; eauto.
Qed.

(* A simplified setting: we assume that we are not
   writing values across locations with different
   permissions. *)

Fixpoint Prange (b: block) (o: Z) (p: permission) (l: list (option memval)) {struct l}: pred :=
  match l with
    | nil => nil
    | (v :: q) => ((b, o), (p, v)) :: Prange b (o + 1) p q
  end.

Theorem holds_storebytes p (Hperm: perm_order p Writable) b l1:
  forall P o m,
     holds (P ++ Prange b o p l1) m ->
     forall l2,
       length l1 = length l2 ->
       exists m',
         Mem.storebytes m b o l2 = Some m' /\
         holds (P ++ Prange b o p (map Some l2)) m'.
Proof.
  induction l1.
  {
    simpl.
    intros P o m H l2 H0.
    rewrite <- app_nil_end in H .
    destruct l2; try discriminate.
    simpl.
    generalize (Mem.range_perm_storebytes m b o nil).
    simpl.
    unfold Mem.range_perm.
    intros X.
    specialize (X ltac:( intros ; lia ) ).
    destruct X as (m' & SB).
    rewrite <- app_nil_end.
    esplit.
    split; eauto.
    eapply holds_ext; try eassumption.
    {
      intros b0 o0 p0.
      eapply Mem.perm_storebytes_1; eauto.
    }
    intros b0 o0 v.
    erewrite <- Mem.loadbytes_storebytes_other; (try eassumption); auto; try lia.
  }
  simpl.
  intros P o m H l2 H0.
  rewrite holds_star_iff in H.
  destruct H as (HP & HS & DISJ).
  rewrite <- app_cons_nil in HS.
  rewrite holds_star_iff in HS.
  destruct HS as (HSO & HSS & DISJS).
  destruct l2 as [ | v l2 ] ; try discriminate.
  simpl in H0.
  injection H0; clear H0.
  intro H0.
  generalize (Mem.range_perm_storebytes m b o (v :: nil)).
  intro K.  
  rewrite holds_cons_nil in HSO.
  destruct HSO as (HSO & _).
  destruct K as (m1 & Hm1).
  {
    simpl.
    red.
    intros ofs H.
    assert (ofs = o) by lia.
    subst.
    eapply Mem.perm_implies; eauto.
  }
  assert (holds P m1) as HP1.
  {
    eapply holds_ext_strong; try eassumption.
    {
      intros until 1.
      eapply Mem.perm_storebytes_1; eauto.
    }
    intros b0 o0 p0 v0 H.
    erewrite <- Mem.loadbytes_storebytes_other; eauto; try lia.
    simpl.
    destruct (peq b0 b); auto.
    subst.
    right.
    destruct (Z.eq_dec o0 o); try lia.
    subst.
    apply (in_map fst) in H.
    simpl in H.
    edestruct DISJ; simpl; eauto.
  }
  assert (holds (Prange b o p (Some v :: nil)) m1) as HV1.
  {
    simpl.
    rewrite holds_cons_nil.
    split.
    {
      eapply Mem.perm_storebytes_1; eauto.
    }
    replace 1%Z with (Z.of_nat (length (v :: nil))) by reflexivity.
    eapply Mem.loadbytes_storebytes_same; eauto.
  }
  pose (Q := P ++ Prange b o p (Some v :: nil)).
  assert (holds Q m1) as HQ.
  {
    unfold Q.
    rewrite holds_star_iff.
    split; auto.
    split; auto.
    intros bo H H1.
    eapply DISJ; eauto.
    simpl in H1 |- * .
    tauto.
  }
  specialize (fun K => IHl1 Q (o + 1) m1 K _ H0).
  destruct IHl1 as (m_ & S_ & H_).
  {
    rewrite holds_star_iff.
    split; auto.
    split.
    {
      eapply holds_ext_strong; try eassumption.
      {
        intros until 1.
        eapply Mem.perm_storebytes_1; eauto.
      }
      intros b0 o0 p0 v0 H.
      apply (in_map fst) in H.
      simpl in H.
      erewrite <- Mem.loadbytes_storebytes_other; eauto; try lia.
      destruct (peq b0 b); auto.
      subst.
      simpl.
      right.
      destruct (Z.eq_dec o0 o); try lia.
      subst.
      edestruct DISJS; simpl; eauto.
    }
    unfold Q.
    rewrite map_app.
    intros bo.
    rewrite in_app_iff.
    simpl in DISJ.
    simpl.
    destruct 1 as [ | K ] ; eauto.
    destruct K; eauto.
    intros.
    eapply DISJS; simpl; eauto.
  }
  esplit.
  split.
  {
    rewrite <- app_cons_nil.
    eapply Mem.storebytes_concat; eauto.
  }
  unfold Q in H_.
  rewrite app_ass in H_.
  eexact H_.
Qed.    

Theorem holds_loadbytes p b m l:
  forall o,
    holds (Prange b o p (map Some l)) m ->
    Mem.loadbytes m b o (Z.of_nat (length l)) = Some l.
Proof.
  induction l; simpl.
  {
    intros o H.
    generalize (Mem.range_perm_loadbytes m b o 0).
    unfold Mem.range_perm.
    intros K.
    specialize (K ltac:( intros; lia ) ).
    destruct K as (bytes & Hbytes).
    generalize (Mem.loadbytes_length _ _ _ _ _ Hbytes).
    destruct bytes; auto; discriminate.
  }
  intros o H.
  rewrite <- app_cons_nil in H.
  rewrite holds_star_iff in H.
  destruct H as (HL & HR & _).
  rewrite holds_cons_nil in HL.
  destruct HL.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  rewrite <- Zplus_comm.
  rewrite <- app_cons_nil.
  eapply Mem.loadbytes_concat; eauto; lia.
Qed.

Lemma Prange_fst_eq b p1 p2 l1:
  forall o l2,
    length l1 = length l2 ->
    map fst (Prange b o p1 l1) = map fst (Prange b o p2 l2).
Proof.
  induction l1; destruct l2; simpl; auto; try discriminate.
  inversion 1; subst.
  f_equal; eauto.
Qed.

Lemma Prange_weaken_weak p1 p2 (PERM: perm_order p1 p2) m b l:
  forall o,
    holds (Prange b o p1 l) m ->
    holds (Prange b o p2 l) m.
Proof.
  induction l; simpl; auto.
  intros o.
  rewrite <- app_cons_nil.
  intros H.
  rewrite <- app_cons_nil.
  rewrite holds_star_iff in H |- * .
  destruct H as (H & K1 & K2).
  simpl in K2 |- * .
  split.
  {
    rewrite holds_cons_nil in H |- * .
    destruct H.
    split; auto.
    eapply Mem.perm_implies; eauto.
  }
  split; auto.
  rewrite (Prange_fst_eq _ _ p1 l _ l (eq_refl _)).
  assumption.
Qed.

Lemma Prange_weaken p1 p2 (PERM: perm_order p1 p2) m b l P:
  forall o,
    holds (P ++ Prange b o p1 l) m ->
    holds (P ++ Prange b o p2 l) m.
Proof.
  intros o H.
  rewrite holds_star_iff in * |- * .
  destruct H as (K & L & M).
  split; auto.
  split; eauto using Prange_weaken_weak.
  erewrite Prange_fst_eq; eauto.
Qed.

Definition Pval chunk b o p v :=
  Prange b o p (map Some (encode_val chunk v)).

Lemma Pval_eq chunk b o p v:
  Pval chunk b o p v = Prange b o p (map Some (encode_val chunk v)).
Proof.
  reflexivity.
Qed.
  
Lemma Pval_weaken p1 p2 (PERM: perm_order p1 p2) m chunk b v o P:
    holds (P ++ Pval chunk b o p1 v) m ->
    holds (P ++ Pval chunk b o p2 v) m.
Proof.
  apply Prange_weaken.
  assumption.
Qed.

Lemma holds_load_gen chunk2 o
        (Halign: (align_chunk chunk2 | o))
        chunk1
        (Heq: size_chunk chunk1 = size_chunk chunk2)
        p b m v:
  holds (Pval chunk1 b o p v) m ->
  Mem.load chunk2 m b o = Some (decode_val chunk2 (encode_val chunk1 v)).
Proof.
  intro.
  apply Mem.loadbytes_load; auto.
  rewrite <- Heq.
  rewrite size_chunk_conv.
  rewrite <- (encode_val_length _ v).
  eapply holds_loadbytes; eauto.
Qed.

Theorem holds_load chunk o
        (Halign: (align_chunk chunk | o))
        p b m v:
  holds (Pval chunk b o p v) m ->
  Mem.load chunk m b o = Some (Val.load_result chunk v).
Proof.
  intros.
  erewrite holds_load_gen; eauto.
  f_equal.
  eapply decode_encode_val_similar; eauto.
  apply decode_encode_val_general.
Qed.
 
Theorem holds_store chunk o
        (Halign: (align_chunk chunk | o))
        p (Hperm: perm_order p Writable) b l1:
  forall P m,
     holds (P ++ Prange b o p l1) m ->
     length l1 = size_chunk_nat chunk ->
     forall v,
     exists m',
       Mem.store chunk m b o v = Some m' /\
       holds (P ++ Pval chunk b o p v) m'.
Proof.
  intros P m H H0 v.
  generalize (holds_storebytes p Hperm b l1 P o m H (encode_val chunk v)).
  rewrite encode_val_length.
  intro K.
  specialize (K ltac:( assumption ) ).
  destruct K as (m' & STORE & HOLDS).
  esplit.
  split; eauto.
  eapply Mem.storebytes_store; eauto.
Qed.

Definition Pperm b o p n := Prange b o p (repeat None n).

Lemma Pperm_eq b o p n: Pperm b o p n = Prange b o p (repeat None n).
Proof.
  reflexivity.
Qed.

Theorem holds_store_perm chunk o
        (Halign: (align_chunk chunk | o))
        p (Hperm: perm_order p Writable) b:
  forall P m,
     holds (P ++ Pperm b o p (size_chunk_nat chunk)) m ->
     forall v,
     exists m',
       Mem.store chunk m b o v = Some m' /\
       holds (P ++ Pval chunk b o p v) m'.
Proof.
  intros P m H v.
  eapply holds_store; eauto.
  rewrite repeat_length.
  reflexivity.
Qed.

Lemma Prange_perm m b p l:
  forall o,
    holds (Prange b o p l) m ->
    forall i, o <= i < o + Z.of_nat (length l) ->
              Mem.perm m b i Cur p.
Proof.
  induction l; simpl.
  {
    intros; lia.
  }
  intros o H i H0.
  rewrite <- app_cons_nil in H.
  rewrite holds_star_iff in H.
  destruct H as (HH & HT & _).
  rewrite holds_cons_nil in HH.
  destruct HH.
  destruct (Z.eq_dec o i); try congruence.
  eapply IHl; eauto.
  rewrite Zpos_P_of_succ_nat in H0.
  lia.
Qed.

Lemma Prange_fst_in b p l:
  forall o b' o',
    In (b', o') (map fst (Prange b o p l)) ->
    o <= o' < o + Z.of_nat (length l) /\
    b' = b.
Proof.
  induction l; simpl; try tauto.
  rewrite Zpos_P_of_succ_nat.
  destruct 1 as [ K | K ].
  {
    inversion K; subst.
    split; auto.
    lia.
  }
  apply IHl in K.
  destruct K.
  split; auto.
  lia.
Qed.

Lemma holds_Pperm_intro m b p n:
  forall o,
    (forall i, o <= i < o + Z.of_nat n ->
               Mem.perm m b i Cur p) ->
    holds (Pperm b o p n) m.
Proof.
  unfold Pperm.
  induction n; simpl.
  {
    intros. apply holds_nil.
  }
  rewrite Zpos_P_of_succ_nat.
  intros o H.
  rewrite <- app_cons_nil.
  rewrite holds_star_iff.
  rewrite holds_cons_nil.
  split.
  {
    split; auto.
    apply H.
    lia.
  }
  split.
  {
    apply IHn.
    intros.
    apply H.
    lia.
  }
  simpl.
  destruct 1; try contradiction.
  subst.
  intros H0.
  apply Prange_fst_in in H0.
  destruct H0.
  lia.
Qed.

Lemma Prange_Pperm_weak m b p l o:
    holds (Prange b o p l) m ->
    holds (Pperm b o p (length l)) m.
Proof.
  intros.
  apply holds_Pperm_intro.
  apply Prange_perm.
  assumption.
Qed.

Lemma Prange_Pperm m b p l o P:
    holds (P ++ Prange b o p l) m ->
    holds (P ++ Pperm b o p (length l)) m.
Proof.
  intros H.
  rewrite holds_star_iff in * |- * .
  destruct H as (K & L & M).
  split; auto.
  split; eauto using Prange_Pperm_weak.
  unfold Pperm.
  erewrite Prange_fst_eq; eauto.
  rewrite repeat_length.
  reflexivity.
Qed.

Lemma refl_from_eq {A: Type} (R: relation A) {refl: Reflexive R} a b:
  a = b ->
  R a b.
Proof.
  intros; subst; auto.
Qed.

Lemma Pval_Pperm chunk m b p v o P:
  holds (P ++ Pval chunk b o p v) m ->
  holds (P ++ Pperm b o p (size_chunk_nat chunk)) m.
Proof.
  intros H.
  apply Prange_Pperm in H.
  revert H.
  apply holds_list_comm_aux.
  apply refl_from_eq; try typeclasses eauto.
  f_equal.
  f_equal.
  rewrite map_length.
  apply encode_val_length.
Qed.  

Lemma holds_Pperm_iff m b p n o:
  holds (Pperm b o p n) m <->
  (forall i, o <= i < o + Z.of_nat n ->
             Mem.perm m b i Cur p).
Proof.
  split.
  {
    intros; eapply Prange_perm; eauto.
    rewrite repeat_length.
    assumption.
  }
  apply holds_Pperm_intro.
Qed.

Lemma in_decomp {A: Type} (a: A) l:
  In a l ->
  exists l1 l2, l = l1 ++ a :: l2.
Proof.
  induction l; simpl; try contradiction.
  destruct 1 as [? | H].
  {
    subst.
    exists nil; simpl; eauto.
  }
  specialize (IHl H).
  destruct IHl as (? & ? & ?).
  subst.
  eexists (_ :: _); simpl; eauto.
Qed.

Lemma holds_valid_block P m:
  holds P m ->
  forall b o,
    In (b, o) (map fst P) ->
    Mem.valid_block m b.
Proof.
  intros H b o H0.
  apply list_in_map_inv in H0.
  destruct H0 as [[? [? ?]] [EQ IN]].
  simpl in EQ. subst.
  apply in_decomp in IN.
  destruct IN as (? & ? & ?).
  subst.
  setoid_rewrite list_comm_intro in H.
  rewrite <- app_cons_nil in H.
  rewrite app_ass in H.
  rewrite holds_star_iff in H.
  destruct H as (H0 & _ & _).
  rewrite holds_cons_nil in H0.
  destruct H0 as (H0 & _).
  eapply Mem.perm_valid_block; eauto.
Qed.  
  
Lemma Z_to_nat_negative a:
  (a < 0)%Z ->
  Z.to_nat a = O.
Proof.
  intros.
  destruct a; try discriminate.
  apply Z2Nat.inj_neg.
Qed.

Theorem holds_alloc m lo hi m' b':
  Mem.alloc m lo hi = (m', b') ->
  forall P,
  holds P m ->
  holds (P ++ Pperm b' lo Freeable (Z.to_nat (hi - lo))) m'.
Proof.
  intros H P H0.
  apply holds_star_iff.
  split.
  {
    generalize H0.
    apply holds_ext_strong.
    {
      intros until 1.
      eapply Mem.perm_alloc_1; eauto.
    }
    intros b o p v H1.
    erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
    apply (in_map fst) in H1.
    eapply holds_valid_block; eauto.
  }
  split.
  {
    apply holds_Pperm_intro.
    destruct (Z_le_dec lo hi).
    {
      rewrite Z2Nat.id by lia.
      intros.
      eapply Mem.perm_alloc_2; eauto.
      lia.
    }
    rewrite Z_to_nat_negative by lia.
    simpl.
    intros.
    lia.
  }
  intros bo H1 H2.
  destruct bo as [b o].
  generalize (holds_valid_block _ _ H0 _ _ H1).
  apply Prange_fst_in in H2.
  destruct H2; subst.
  eapply Mem.fresh_block_alloc; eauto.
Qed.

Theorem holds_alloc_exists m P:
  holds P m ->
  forall lo hi,
  exists  m' b',
    Mem.alloc m lo hi = (m', b') /\
    holds (P ++ Pperm b' lo Freeable (Z.to_nat (hi - lo))) m'.
Proof.
  intros H lo hi.
  destruct (Mem.alloc m lo hi) eqn:EQ.
  do 2 esplit.
  split; eauto.
  eapply holds_alloc; eauto.
Qed.

Lemma Prange_fst_in_intro_aux b p l:
  forall i,
    (i < length l)%nat ->
    forall o,
      In (b, o + Z.of_nat i) (map fst (Prange b o p l)).
Proof.
  induction l; simpl; try (intros; lia).
  destruct i as [ | i ].
  {
    intros _.
    left.
    f_equal.
    simpl.
    lia.
  }
  intros H o.
  assert (i < length l)%nat as LT by lia.
  specialize (IHl _ LT (o + 1)).
  simpl.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  right.
  replace (o + (Z.of_nat i + 1))%Z with (o + 1 + Z.of_nat i)%Z by lia.
  assumption.
Qed.

Lemma Prange_fst_in_intro b p l:
  forall o o',
    o <= o' < o + Z.of_nat (length l) ->
    In (b, o') (map fst (Prange b o p l)).
Proof.
  intros o o' H.
  assert (exists i, o' = o + Z.of_nat i /\ (i < length l)%nat) as EX.
  {
    exists (Z.to_nat (o' - o)).
    split.
    {
      rewrite Z2Nat.id by lia.
      lia.
    }
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    lia.
  }
  destruct EX as (i & Hi & LT).
  subst.
  eapply Prange_fst_in_intro_aux; eauto.
Qed.

Theorem holds_free m b lo hi P:
  holds (P ++ Pperm b lo Freeable (Z.to_nat (hi - lo))) m ->
  exists m',
    Mem.free m b lo hi = Some m' /\
    holds P m'.
Proof.
  intros H.
  rewrite holds_star_iff in H.
  destruct H as (HP & HF & DISJ).
  rewrite holds_Pperm_iff in HF.
  assert 
    (
      forall i : Z,
        lo <= i < hi ->
        Mem.perm m b i Cur Freeable
    )
    as HF'.
  {
    intros.
    apply HF.
    rewrite Z2Nat.id by lia.
    lia.
  }
  clear HF.
  apply Mem.range_perm_free in HF'.
  destruct HF' as (m' & Hm').
  esplit.
  split; eauto.
  generalize HP.
  apply holds_ext_strong.
  {
    intros b0 o p v H.
    eapply Mem.perm_free_1; eauto.
    apply (in_map fst) in H.
    simpl in H.
    destruct (peq b0 b); auto.
    subst.
    right.
    destruct (Z_lt_dec o lo); auto.
    right.
    destruct (Z_le_dec hi o); auto.
    exfalso.
    eapply DISJ; eauto.
    apply Prange_fst_in_intro.
    rewrite repeat_length.
    rewrite Z2Nat.id by lia.
    lia.
  }
  intros b0 o p v H.
  erewrite <- Mem.loadbytes_free; eauto.
  destruct (peq b0 b); auto.
  subst.
  right.
  destruct (Z_ge_dec lo hi); auto.
  right.
  destruct (Z_le_dec (o + 1) lo); auto.
  right.
  destruct (Z_le_dec hi o); auto.
  exfalso.
  apply (in_map fst) in H.
  simpl in H.
  eapply DISJ; eauto.
  apply Prange_fst_in_intro.
  rewrite repeat_length.
  rewrite Z2Nat.id by lia.
  lia.
Qed.  

Fixpoint type_of_chunk (c: AST.memory_chunk): Type :=
  match c with
    | Mint8signed => Integers.Int.int
    | Mint8unsigned => Integers.Int.int
    | Mint16signed => Integers.Int.int
    | Mint16unsigned => Integers.Int.int
    | Mint32 => Integers.int
    | Mint64 => Integers.int64
    | Mfloat32 => Floats.float32
    | Mfloat64 => Floats.float
    | Many32 => False
    | Many64 => False
  end.

Fixpoint value_of_chunk (c: memory_chunk): forall (t: type_of_chunk c), val :=
  match c as c' return type_of_chunk c' -> val with
    | Mint8signed => Vint
    | Mint8unsigned => Vint
    | Mint16signed => Vint
    | Mint16unsigned => Vint
    | Mint32 => Vint
    | Mint64 => Vlong
    | Mfloat32 => Vsingle
    | Mfloat64 => Vfloat
    | Many32 => False_rect _
    | Many64 => False_rect _
  end.

(* Unidimensional arrays *)

Lemma Pperm_decomp b p i:
  forall j,
    (j <= i)%nat ->
    forall o,
      Pperm b o p i =
      Pperm b o p j ++
      Pperm b (o + Z.of_nat j) p (i - j).
Proof.
  induction i; simpl.
  {
    intros j H o.
    assert (j = O) by lia.
    subst.
    simpl.
    f_equal.
    ring.
  }
  intros j H o.
  rewrite Pperm_eq.
  simpl.
  rewrite <- Pperm_eq.
  destruct j as [ | j ] ; simpl.
  {
    symmetry.
    rewrite Pperm_eq.
    simpl.
    rewrite <- Pperm_eq.
    repeat ((try lia); f_equal).
  }
  rewrite Zpos_P_of_succ_nat.
  rewrite <- Pperm_eq.
  rewrite (IHi j ltac:( lia ) ).
  repeat ((try (lia || ring)); f_equal).
Qed.

Corollary Pperm_plus b o p u v:
  Pperm b o p (u + v) =
  Pperm b o p u ++ Pperm b (o + Z.of_nat u) p v.
Proof.
  rewrite Pperm_decomp with (j := u) by lia.
  f_equal.
  f_equal.
  lia.
Qed.

Fixpoint Parray_opt (chunk: memory_chunk) (lo: Z) (data: Z -> option (type_of_chunk chunk)) (bd: block) (od: Z) (p: permission) (i: nat) {struct i}: pred :=
  match i with
    | O => nil
    | S i' =>
      match data lo with
        | Some v =>
          Pval chunk bd od p (value_of_chunk chunk v)
        | _ =>
          Pperm bd od p (Memdata.size_chunk_nat chunk)
      end
        ++ Parray_opt chunk (lo + 1) data bd (od + Memdata.size_chunk chunk) p i'
  end.

Lemma Parray_opt_none chunk (data: Z -> option (type_of_chunk chunk)) bd p i:
  forall lo,
    (forall j, (j < i)%nat -> data (lo + Z.of_nat j) = None) ->
    forall od,
      Parray_opt chunk lo data bd od p i =
      Pperm bd od p (Memdata.size_chunk_nat chunk * i).
Proof.
  induction i; simpl.
  {
    intros lo H od.
    rewrite Nat.mul_0_r.
    reflexivity.
  }
  intros lo H od.
  replace lo with (lo + Z.of_nat O) at 1 by (simpl; ring).
  rewrite H by lia.
  rewrite IHi.
  {
    rewrite <- mult_n_Sm.
    rewrite (Nat.add_comm (_ * _)).
    rewrite Pperm_plus.
    rewrite size_chunk_conv.
    reflexivity.
  }
  intros j H0.
  replace (lo + 1 + Z.of_nat j) with (lo + Z.of_nat (S j)).
  {
    apply H; lia.
  }
  simpl.
  rewrite Zpos_P_of_succ_nat.
  lia.
Qed.

Theorem holds_Parray_opt chunk data bd p m i:
  forall od,
    (align_chunk chunk | od) ->
    forall lo,
      holds (Parray_opt chunk lo data bd od p i) m ->
      forall j,
        (j < i)%nat ->
        forall v,
          data (lo + Z.of_nat j) = Some v ->
          Memory.Mem.load chunk m bd
                          (od + Memdata.size_chunk chunk * Z.of_nat j) =
          Some (Val.load_result chunk (value_of_chunk chunk v)).
Proof.
  induction i.
  {
    intros; lia.
  }
  intros od H lo H0 j H1 v H2.
  simpl in H0.
  rewrite holds_star_iff in H0.
  destruct H0 as (V & A & _).
  destruct j as [ | j ] ; simpl.
  {
    rewrite Z.mul_0_r.
    repeat rewrite Z.add_0_r.
    simpl in H2.
    rewrite Z.add_0_r in H2.
    rewrite H2 in V.
    eapply holds_load; eauto.
  }
  revert H2.
  simpl.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  rewrite Z.mul_add_distr_l.
  rewrite Z.mul_1_r.
  rewrite (Z.add_comm _ (size_chunk _)).
  rewrite Z.add_assoc.
  rewrite (Z.add_comm _ 1).
  repeat rewrite Z.add_assoc.
  apply IHi; auto; try lia.
  {
    apply Z.divide_add_r; auto.
    apply align_size_chunk_divides.
  }
  rewrite Z.add_comm.
  assumption.
Qed.

Lemma Parray_opt_ext (chunk: memory_chunk) (data1 data2: Z -> option (type_of_chunk chunk))
      (bd: block)
      (p: permission) (i: nat):
  forall 
    (lo: Z),
    (forall j, (j < i)%nat -> data1 (lo + Z.of_nat j) = data2 (lo + Z.of_nat j)) ->
    forall (od: Z),
      Parray_opt chunk lo data1 bd od p i =
      Parray_opt chunk lo data2 bd od p i.
Proof.
  induction i; simpl; auto.
  intros lo H od.
  f_equal.
  {
    replace lo with (lo + Z.of_nat O) by (simpl; lia).
    rewrite H by lia.
    reflexivity.
  }
  apply IHi.
  intros j H0.
  replace (lo + 1 + Z.of_nat j) with (lo + Z.of_nat (S j)).
  {
    apply H.
    lia.
  }
  simpl.
  rewrite Zpos_P_of_succ_nat.
  lia.
Qed.

Lemma Parray_opt_decomp chunk data bd p i:
  forall j,
    (j < i)%nat ->
  forall lo od,
    Parray_opt chunk lo data bd od p i =
    Parray_opt chunk lo data bd od p j
    ++
    match data (lo + Z.of_nat j) with
      | Some v => Pval chunk bd (od + size_chunk chunk * Z.of_nat j) p (value_of_chunk chunk v)
      | None => Pperm bd (od + size_chunk chunk * Z.of_nat j) p (Memdata.size_chunk_nat chunk)
    end
    ++ Parray_opt chunk (lo + (1 + Z.of_nat j)) data bd (od + Memdata.size_chunk chunk * (1 + Z.of_nat j)) p (i - S j).
Proof.
  induction i.
  {
    intros; lia.
  }
  intros j H lo od.
  cbn -[Z.add].
  destruct j as [ | j].
  {
    cbn -[Z.add].
    repeat rewrite Z.mul_0_r.
    repeat rewrite Z.add_0_r.
    rewrite Nat.sub_0_r.
    rewrite Z.mul_1_r.
    reflexivity.
  }
  cbn -[Z.add].
  rewrite app_ass.
  f_equal.
  rewrite (IHi j ltac:( lia ) ).
  f_equal.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  f_equal.
  {
    replace (lo + (Z.of_nat j + 1))%Z with (lo + 1 + Z.of_nat j)%Z by ring.
    destruct (data (lo + 1 + Z.of_nat j));
      repeat ((try first [lia | ring] );
              f_equal).
  }
  repeat ((try first [lia | ring] );
          f_equal).
Qed.

Theorem holds_Parray_opt_modify chunk o
        (Halign: (align_chunk chunk | o))
        p
        (Hperm: perm_order p Writable)
        P data b i m:
  holds (P ++ Parray_opt chunk 0 data b o p i) m ->
  forall j,
    (j < i)%nat ->
    forall v,
    exists m',
      Mem.store chunk m b (o + Memdata.size_chunk chunk * Z.of_nat j) (value_of_chunk chunk v) = Some m' /\
      holds (P ++ Parray_opt chunk 0 (fun k => if Z.eq_dec k (Z.of_nat j) then Some v else data k) b o p i) m'.
Proof.
  intros H j H0 v.
  rewrite (Parray_opt_decomp _ _ _ _ _ _ H0) in H.
  repeat rewrite Z.add_0_l in H.
  repeat rewrite <- app_ass in H.
  setoid_rewrite list_comm_intro in H.
  repeat rewrite <- app_ass in H.
  match type of H with
      holds (?P ++ _) _ =>
      assert (holds (P ++ Pperm b (o + size_chunk chunk * Z.of_nat j) p (size_chunk_nat chunk)) m) as H'
  end.
  {
    destruct (data (Z.of_nat j)); auto.
    apply Pval_Pperm in H.
    assumption.
  }
  clear H.
  generalize (fun v K1 K2 => holds_store chunk _ K1 _ Hperm _ _ _ _ H' K2 v).
  clear H'. intro H.
  specialize (H (value_of_chunk chunk v)).
  destruct H as (m' & STORE & HOLDS).
  {
    apply Z.divide_add_r; auto.
    apply Z.divide_mul_l.
    apply align_size_chunk_divides.
  }
  {
    apply repeat_length.
  }
  esplit.
  split; eauto.
  rewrite (Parray_opt_decomp _ _ _ _ _ _ H0).
  repeat rewrite Z.add_0_l.
  destruct (Z.eq_dec (Z.of_nat j) (Z.of_nat j)) as [_ | ] ; try congruence.
  repeat rewrite <- app_ass.  
  setoid_rewrite list_comm_intro.
  repeat rewrite <- app_ass.
  revert HOLDS.
  apply holds_list_comm_aux.
  apply refl_from_eq; try typeclasses eauto.
  f_equal.
  f_equal.
  {
    f_equal.
    apply Parray_opt_ext.
    intros j0 H.
    destruct (Z.eq_dec (1 + Z.of_nat j + Z.of_nat j0) (Z.of_nat j)); try congruence.
    lia.
  }
  apply Parray_opt_ext.
  intros j0 H.
  rewrite Z.add_0_l.
  destruct (Z.eq_dec (Z.of_nat j0) (Z.of_nat j)) as [ e | ] ; auto.
  apply Nat2Z.inj in e.
  lia.
Qed.

Global Instance:
  Reflexive Ptrofs.eqm.
Proof.
  exact Ptrofs.eqm_refl.
Qed.

Global Instance:
  Symmetric Ptrofs.eqm.
Proof.
  exact Ptrofs.eqm_sym.
Qed.

Global Instance:
  Transitive Ptrofs.eqm.
Proof.
  exact Ptrofs.eqm_trans.
Qed.

Global Instance:
  Proper (Ptrofs.eqm ==> Ptrofs.eqm ==> Ptrofs.eqm) Zplus.
Proof.
  do 3 red.
  intros; eauto using Ptrofs.eqm_add.
Qed.

Global Instance:
  Proper (Ptrofs.eqm ==> Ptrofs.eqm ==> Ptrofs.eqm) Zminus.
Proof.
  do 3 red.
  intros; eauto using Ptrofs.eqm_sub.
Qed.

Global Instance:
  Proper (Ptrofs.eqm ==> Ptrofs.eqm) Z.opp.
Proof.
  exact Ptrofs.eqm_neg.
Qed.

Global Instance:
  Proper (Ptrofs.eqm ==> Ptrofs.eqm ==> Ptrofs.eqm) Zmult.
Proof.
  do 3 red.
  intros; eauto using Ptrofs.eqm_mult.
Qed.

Global Instance:
  Proper (Ptrofs.eqm ==> Logic.eq) Ptrofs.repr.
Proof.
  exact Ptrofs.eqm_samerepr.
Qed.

Lemma eqm_signed_repr b:
   Ptrofs.eqm (Ptrofs.signed (Ptrofs.repr b)) b.
Proof.
  rewrite Ptrofs.eqm_signed_unsigned.
  rewrite <- Ptrofs.eqm_unsigned_repr.
  reflexivity.
Qed.

Lemma mul_repr a b:
  Ptrofs.mul (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a * b).
Proof.
  rewrite Ptrofs.mul_signed.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_mult; auto using eqm_signed_repr.
Qed.

Lemma add_repr a b:
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  rewrite Ptrofs.add_signed.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; auto using eqm_signed_repr.
Qed.

Lemma unsigned_eqm u v:
    Ptrofs.eqm (Ptrofs.unsigned u) v ->
    (0 <= v <= Ptrofs.max_unsigned)%Z ->
    Ptrofs.unsigned u = v.
Proof.
  intros.
  apply Ptrofs.unsigned_repr in H0.
  rewrite <- H0.
  f_equal.
  rewrite <- (Ptrofs.repr_unsigned u).
  apply Ptrofs.eqm_samerepr.
  assumption.
Qed.

Lemma unsigned_add_repr u v:
  (0 <= Ptrofs.unsigned u + v <= Ptrofs.max_unsigned)%Z ->
  Ptrofs.unsigned (Ptrofs.add u (Ptrofs.repr v)) = (Ptrofs.unsigned u + v)%Z.
Proof.
  intros.
  apply unsigned_eqm; auto.
  rewrite Ptrofs.add_unsigned.
  rewrite <- Ptrofs.eqm_unsigned_repr.
  rewrite <- Ptrofs.eqm_unsigned_repr.
  reflexivity.
Qed.

Lemma signed_add a b:
  Int.eqm (Int.signed (Int.add a b)) (Int.signed a + Int.signed b).
Proof.
  rewrite Int.add_signed.
  etransitivity.
  {
    eapply Int.eqm_signed_unsigned.
  }
  symmetry.
  apply Int.eqm_unsigned_repr.
Qed.

Lemma signed_sub a b:
  Int.eqm (Int.signed (Int.sub a b)) (Int.signed a - Int.signed b).
Proof.
  rewrite Int.sub_signed.
  etransitivity.
  {
    eapply Int.eqm_signed_unsigned.
  }
  symmetry.
  apply Int.eqm_unsigned_repr.
Qed.

Lemma signed_mul a b:
  Int.eqm (Int.signed (Int.mul a b)) (Int.signed a * Int.signed b).
Proof.
  rewrite Int.mul_signed.
  etransitivity.
  {
    eapply Int.eqm_signed_unsigned.
  }
  symmetry.
  apply Int.eqm_unsigned_repr.
Qed.

Lemma signed_neg a:
  Int.eqm (Int.signed (Int.neg a)) (- Int.signed a).
Proof.
  rewrite <- Int.sub_zero_r.
  rewrite signed_sub.
  reflexivity.
Qed.

Lemma unsigned_add a b:
  Int.eqm (Int.unsigned (Int.add a b)) (Int.unsigned a + Int.unsigned b).
Proof.
  rewrite Int.add_unsigned.
  symmetry.
  apply Int.eqm_unsigned_repr.  
Qed.

Lemma unsigned_sub a b:
  Int.eqm (Int.unsigned (Int.sub a b)) (Int.unsigned a - Int.unsigned b).
Proof.
  repeat setoid_rewrite <- Int.eqm_signed_unsigned.
  apply signed_sub.
Qed.

Lemma unsigned_mul a b:
  Int.eqm (Int.unsigned (Int.mul a b)) (Int.unsigned a * Int.unsigned b).
Proof.
  repeat setoid_rewrite <- Int.eqm_signed_unsigned.
  apply signed_mul.
Qed.

Lemma unsigned_neg a:
  Int.eqm (Int.unsigned (Int.neg a)) (- Int.unsigned a).
Proof.
  repeat setoid_rewrite <- Int.eqm_signed_unsigned.
  apply signed_neg.
Qed.

Definition Parray_opt_int chunk data bd od p sz :=
  Parray_opt chunk 0 data bd (Ptrofs.unsigned od) p (Z.to_nat (Int.signed sz)).

Corollary holds_Parray_opt_int chunk:
  forall od,
    (align_chunk chunk | Ptrofs.unsigned od) ->
    forall sz,
      (Ptrofs.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z ->
      forall i,
        0 <= Ptrofs.signed i < Int.signed sz ->
        forall data v,
          data (Ptrofs.signed i) = Some v ->
          forall bd p m,
            holds (Parray_opt_int chunk data bd od p sz) m ->
            Memory.Mem.loadv chunk m (Vptr bd (Ptrofs.add od (Ptrofs.mul (Ptrofs.repr (Memdata.size_chunk chunk)) i))) =
            Some (Val.load_result chunk (value_of_chunk chunk v)).
Proof.
  intros od H sz H0 i H1 data v H2 bd p m H3.
  simpl.
  rewrite <- (Ptrofs.repr_signed i).
  rewrite mul_repr.
  rewrite <- (Ptrofs.repr_unsigned od).
  rewrite add_repr.
  rewrite Ptrofs.unsigned_repr.
  {
    rewrite <- (Z2Nat.id (Int.signed i)) by lia.
    eapply holds_Parray_opt; eauto.
    {
      apply Nat2Z.inj_lt.
      repeat rewrite Z2Nat.id by lia.
      lia.
    }
    rewrite <- H2.
    f_equal.
    rewrite Z2Nat.id by lia.
    lia.
  }
  split.
  {
    apply Z.le_trans with (Int.unsigned od + 0).
    {
      generalize (Int.unsigned_range od); lia.
    }
    apply Zplus_le_compat_l.
    apply Z.mul_nonneg_nonneg.
    {
      generalize (size_chunk_pos chunk); lia.
    }
    lia.
  }
  eapply Z.le_trans; [ | eassumption].
  apply Zplus_le_compat_l.
  apply Zmult_le_compat_l.
  {
    lia.
  }
  generalize (size_chunk_pos chunk); lia.
Qed.

Corollary holds_Parray_opt_int_repr chunk:
  forall od,
    (align_chunk chunk | Int.unsigned od) ->
    forall sz,
      (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z ->
      forall i,
        0 <= i < Int.signed sz ->
        forall data v,
          data i = Some v ->
          forall bd p m,
            holds (Parray_opt_int chunk data bd od p sz) m ->
            Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) (Int.repr i)))) = Some (Val.load_result chunk (value_of_chunk chunk v)).
Proof.
  intros od H sz H0 i H1 data v H2 bd p m H3.
  assert (Int.signed (Int.repr i) = i) as Hi.
  {
    apply Int.signed_repr.
    generalize (Int.signed_range sz).
    assert (Int.min_signed <= 0) by (vm_compute; congruence).
    lia.
  }
  rewrite <- Hi in H2.  
  eapply holds_Parray_opt_int; eauto.
  congruence.
Qed.

(* How to manage a `for' loop counter *)

Definition counter sz i :=
  (0 <= Int.signed i <= Int.signed sz)%Z.

Lemma init_counter sz:
  (0 <= Int.signed sz)%Z -> counter sz (Int.repr 0).
Proof.
  intros H.
  unfold counter.
  rewrite Int.signed_repr by (vm_compute; intuition congruence).
  lia.
Qed.

Lemma incr_counter sz i:
  counter sz i ->
  Int.cmp Clt i sz = true ->
  counter sz (Int.add i (Int.repr 1)).
Proof.
  unfold counter.
  intros H H0.
  simpl in H0.
  unfold Int.lt in H0.
  destruct (zlt (Int.signed i) (Int.signed sz)); try discriminate.
  rewrite <- (Int.repr_signed i).
  rewrite add_repr.
  rewrite Int.signed_repr.
  {
    lia.
  }
  generalize (Int.signed_range sz).
  generalize (Int.signed_range i).
  lia.
Qed.

Lemma fin_counter sz i:
    counter sz i ->
    Int.cmp Clt i sz = false ->
    i = sz.
Proof.
  unfold counter.
  simpl.
  unfold Int.lt.
  intros H H0.
  destruct (zlt (Int.signed i) (Int.signed sz)); try discriminate.
  assert (Int.signed i = Int.signed sz) as EQ by lia.
  apply (f_equal Int.repr) in EQ.
  repeat rewrite Int.repr_signed in EQ.
  assumption.
Qed.

Corollary holds_Parray_opt_int_counter chunk:
  forall od,
    (align_chunk chunk | Int.unsigned od) ->
    forall sz,
      (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z ->
      forall i,
        counter i sz ->
        Int.cmp Clt i sz = true ->
        forall data v,
          data (Int.signed i) = Some v ->
          forall bd p m,
            holds (Parray_opt_int chunk data bd od p sz) m ->
            Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) i))) =
            Some (Val.load_result chunk (value_of_chunk chunk v)).
Proof.
  intros od H sz H0 i H1 H2 data v H3 bd p m H4.
  unfold counter in H1.
  simpl in H2.
  unfold Int.lt in H2.
  destruct (zlt (Int.signed i) (Int.signed sz)); try discriminate.
  eapply holds_Parray_opt_int; eauto.
  lia.
Qed.

Definition Parray chunk data := Parray_opt chunk 0 (fun x => Some (data x)).

Lemma Parray_opt_some chunk (data1: Z -> option (type_of_chunk chunk)) (data2: Z -> type_of_chunk chunk) bd p i:
  (forall j, (j < i)%nat -> data1 (Z.of_nat j) = Some (data2 (Z.of_nat j))) ->
  forall od,
    Parray_opt chunk 0 data1 bd od p i =
    Parray chunk data2 bd od p i.
Proof.
  intros H od.
  apply Parray_opt_ext.
  intros j H0.
  repeat rewrite Z.add_0_l.
  auto.
Qed.

Lemma Parray_ext (chunk: memory_chunk) (data1 data2: Z -> type_of_chunk chunk)
      (bd: block)
      (p: permission) (i: nat):
  (forall j, (j < i)%nat -> data1 (Z.of_nat j) = data2 (Z.of_nat j)) ->
  forall (od: Z),
    Parray chunk data1 bd od p i =
    Parray chunk data2 bd od p i.
Proof.
  intros H od.
  apply Parray_opt_ext.
  intros j H0.
  f_equal.
  rewrite Z.add_0_l.
  auto.
Qed.

Theorem holds_Parray chunk data bd p m i:
  forall od,
    (align_chunk chunk | od) ->
    holds (Parray chunk data bd od p i) m ->
    forall j,
      (j < i)%nat ->
      Memory.Mem.load chunk m bd
                      (od + Memdata.size_chunk chunk * Z.of_nat j) =
      Some (Val.load_result chunk (value_of_chunk chunk (data (Z.of_nat j)))).
Proof.
  intros od H H0 j H1.
  eapply holds_Parray_opt; eauto.
Qed.

Theorem holds_Parray_modify chunk o
        (Halign: (align_chunk chunk | o))
        p
        (Hperm: perm_order p Writable)
        P data b i m:
  holds (P ++ Parray chunk data b o p i) m ->
  forall j,
    (j < i)%nat ->
    forall v,
    exists m',
      Mem.store chunk m b (o + Memdata.size_chunk chunk * Z.of_nat j) (value_of_chunk chunk v) = Some m' /\
      holds (P ++ Parray chunk (fun k => if Z.eq_dec k (Z.of_nat j) then v else data k) b o p i) m'.
Proof.
  intros H j H0 v.
  destruct (holds_Parray_opt_modify _ _ Halign _ Hperm _ _ _ _ _ H _ H0 v)
           as (m' & STORE & HOLDS).
  esplit.
  split; eauto.
  eapply eq_rect with (P := fun t => holds t m'); eauto.
  f_equal.
  apply Parray_opt_ext.
  intros j0 H1.
  destruct (Z.eq_dec (0 + Z.of_nat j0) (Z.of_nat j)); auto.
Qed.

Definition Parray_int chunk data bd od p sz :=
  Parray_opt_int chunk (fun t => Some (data t)) bd od p sz.

Lemma Parray_int_eq chunk data bd od p sz:
  Parray_int chunk data bd od p sz =
  Parray chunk data bd (Int.unsigned od) p (Z.to_nat (Int.signed sz)).
Proof.
  reflexivity.
Qed.

Corollary holds_Parray_int chunk:
  forall od,
    (align_chunk chunk | Int.unsigned od) ->
    forall sz,
      (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z ->
      forall i,
        0 <= Int.signed i < Int.signed sz ->
        forall data bd p m,
          holds (Parray_int chunk data bd od p sz) m ->
          Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) i))) =
          Some (Val.load_result chunk (value_of_chunk chunk (data (Int.signed i)))).
Proof.
  intros od H sz H0 i H1 data bd p m H2.
  eapply holds_Parray_opt_int; eauto.
  reflexivity.
Qed.

Corollary holds_Parray_int_repr chunk:
  forall od,
    (align_chunk chunk | Int.unsigned od) ->
    forall sz,
      (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z ->
      forall i,
        0 <= i < Int.signed sz ->
        forall data bd p m,
          holds (Parray_int chunk data bd od p sz) m ->
          Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) (Int.repr i)))) =
          Some (Val.load_result chunk (value_of_chunk chunk (data i))).
Proof.
  intros od H sz H0 i H1 data bd p m H2.
  eapply holds_Parray_opt_int_repr; eauto.
  reflexivity.
Qed.

Corollary holds_Parray_int_counter chunk:
  forall od,
    (align_chunk chunk | Int.unsigned od) ->
    forall sz,
      (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z ->
      forall i,
        counter i sz ->
        Int.cmp Clt i sz = true ->
        forall data bd p m,
          holds (Parray_int chunk data bd od p sz) m ->
          Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) i))) =
          Some (Val.load_result chunk (value_of_chunk chunk (data (Int.signed i)))).
Proof.
  intros od H sz H0 i H1 H2 data bd p m H3.
  eapply holds_Parray_opt_int_counter; eauto.
  reflexivity.
Qed.

Lemma refl_eq {A: Type} (R: relation A)
      {refl: Reflexive R}
  a b:
    (forall c,
       R a c -> R c b) ->
    R a b.
Proof.
  intros.
  auto.
Qed.

Ltac search_for_in K t :=
  match type of K with
    | holds (_ ++ _) _ =>
      let L := constr:(holds_weak_left _ _ _ K) in
      search_for_in L t
    | holds (_ ++ _) _ =>
      let R := constr:(holds_weak_right _ _ _ K) in
      search_for_in R t
    | _ => t K
  end.

Ltac search_for_exact_in P K :=
  let t H :=
      match type of H with
        | holds P _ => exact H
      end
  in search_for_in K t.

Theorem holds_loadv chunk o
        (Halign: (align_chunk chunk | Int.unsigned o)%Z)
        p b m v:
  holds (Pval chunk b (Int.unsigned o) p v) m ->
  Mem.loadv chunk m (Vptr b o) = Some (Val.load_result chunk v).
Proof.
  apply holds_load; trivial.
Qed.

Theorem holds_loadv_exists chunk o p b m v (P: _ -> Prop):
  (forall v',
     v' = Val.load_result chunk v ->
     P v') ->
  forall
    (Halign: (align_chunk chunk | Int.unsigned o)%Z)
  ,
  holds (Pval chunk b (Int.unsigned o) p v) m ->
  exists v',
    Mem.loadv chunk m (Vptr b o) = Some v' /\
    P v'.
Proof.
  eauto using holds_loadv.
Qed.

Ltac search_for_Pval_int_in chunk b o K :=
  let t H :=
      match type of H with
        | holds (Pval chunk b (Int.unsigned o) _ _) _ =>
          exact H
      end
  in
  search_for_in K t.

Ltac search_for_gen m t :=
  match goal with
    K1:
      (forall m_,
         holds ?P m_ ->
         holds ?Q m_),
    K2: holds ?R m |- _ =>
    let HP := constr: ( search_for_exact_in P K2 ) in
    let K3 := constr: (K1 _ HP) in
    let TU := type of K3 in
    t K3
    | K_ : holds _ m |- _ => t K_
  end.

Ltac search_for_Pval_int chunk b o m :=
  let t := search_for_Pval_int_in chunk b o in
  search_for_gen m t.

Ltac holds_loadv_exists :=
  match goal with
      ALIGN: (align_chunk ?chunk | Int.unsigned ?o)%Z |-
      holds (Pval ?chunk ?b (Int.unsigned ?o) _ ?v) ?m ->
      exists v_,
        Mem.loadv ?chunk ?m (Vptr ?b ?o) = Some v_ /\ _ =>
      generalize ALIGN;
      apply holds_loadv_exists;
      let v := fresh "v" in
      let vEQ := fresh "vEQ" in
      intros v vEQ;
        simpl in vEQ;
        subst v
  end.

Ltac Pval_solve :=
  match goal with
      |- exists v,
           Mem.loadv ?chunk ?m (Vptr ?b ?o) = Some v /\ _ =>
      let z := constr: ( search_for_Pval_int chunk b o m ) in
      generalize z;
        holds_loadv_exists
  end.

Ltac search_for_Parray_int_in chunk b o K :=
  let t H :=
      match type of H with
        | holds (Parray_int chunk _ b o _ _) _ =>
          exact H
      end
  in
  search_for_in K t.

Ltac search_for_Parray_int chunk b o m :=
  let t := search_for_Parray_int_in chunk b o in
  search_for_gen m t.


Ltac break K :=
  match type of K with
      exists x, _ =>
      let x := fresh "x" in
      destruct K as [x K];
        break K
    | _ /\ _ =>
      let K_ := fresh "K_" in
      destruct K as (K_ & K);
        break K_;
        break K
    | _ => idtac
  end.

Corollary holds_Parray_int_exists chunk od sz i data (P: _ -> Prop):
  (
    (align_chunk chunk | Int.unsigned od)%Z /\
    (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z /\
    (0 <= Int.signed i < Int.signed sz)%Z /\
    (
      forall v,
        v = Val.load_result chunk (value_of_chunk chunk (data (Int.signed i))) ->
        P v
    )
  ) ->
  forall bd p m,
    holds (Parray_int chunk data bd od p sz) m ->
    exists v' ,
      Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) i))) =
      Some v' /\
      P v'.
Proof.
  intros H bd p m H0.
  break H.
  esplit.
  split.
  {
    eapply holds_Parray_int; eauto.
  }
  auto.
Qed.

Corollary holds_Parray_int_repr_exists chunk od sz i data (P: _ -> Prop):
  (
    (align_chunk chunk | Int.unsigned od)%Z /\
    (Int.unsigned od + Memdata.size_chunk chunk * Int.signed sz <= Int.max_unsigned)%Z /\
    (0 <= i < Int.signed sz)%Z /\
    (
      forall v',
        v' = Val.load_result chunk (value_of_chunk chunk (data i)) ->
        P v'
    )
  ) ->
  forall bd p m,
    holds (Parray_int chunk data bd od p sz) m ->
    exists v',
      Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) (Int.repr i)))) =
      Some v' /\
      P v'.
Proof.
  intros H bd p m H0.
  break H.
  esplit.
  split.
  {
    eapply holds_Parray_int_repr; eauto.
  }
  auto.
Qed.

Corollary holds_Parray_int_repr_exists_const_bound chunk od sz i data (P: _ -> Prop):
  (
    (Int.signed (Int.repr sz) = sz) /\
    (align_chunk chunk | Int.unsigned od)%Z /\
    (Int.unsigned od + Memdata.size_chunk chunk * sz <= Int.max_unsigned)%Z /\
    (0 <= i < sz)%Z /\
    (
      forall v,
        v = Val.load_result chunk (value_of_chunk chunk (data i)) ->
        P v
    )
  ) ->
  forall bd p m,
    holds (Parray_int chunk data bd od p (Int.repr sz)) m ->
    exists v' ,
      Memory.Mem.loadv chunk m (Vptr bd (Int.add od (Int.mul (Int.repr (Memdata.size_chunk chunk)) (Int.repr i)))) =
      Some v' /\
      P v'.
Proof.
  intros H bd p m H0.
  destruct H as (K & H).
  break H.
  eapply holds_Parray_int_exists; eauto.
  rewrite K.
  rewrite Int.signed_repr; auto.
  generalize (Int.signed_range (Int.repr sz)).
  rewrite K.
  assert (Int.min_signed <= 0)%Z by (vm_compute; congruence).
  lia.
Qed.

Ltac Parray_solve :=
  match goal with
      |- exists v,
           Mem.loadv ?chunk ?m (Vptr ?b (Int.add ?o _)) = Some v /\ _ =>
      let z := constr: $( search_for_Parray_int chunk b o m )$ in
      generalize z
  end.

Ltac solve_trivial :=
  match goal with
      |- _ /\ _ => split; [ exact I | ]; try solve_trivial
    | |- _ /\ _ => split; [ reflexivity | ]; try solve_trivial
    | |- _ /\ _ => split; [ eassumption | ]; try solve_trivial
    | |- exists _, _ => esplit; solve_trivial
  end.

Ltac holds_Parray_int_repr_exists_const_bound :=
    apply holds_Parray_int_repr_exists_const_bound;
    solve_trivial;
    split; [ lia | ];
    let v := fresh "v" in
    let Hv := fresh "Hv" in
    intros v Hv;
    simpl in Hv;
    subst v.

Ltac revolve_aux H_ P H t :=
  match type of H with
      holds (_ ++ ?Q) _ => clear H_; rename H into H_; t Q
    | _ =>
      setoid_rewrite list_comm_intro in H;
      (repeat rewrite <- app_ass in H);
      match type of H with
        | holds P _ =>
          fail 2
        | _ => idtac
      end;
      revolve_aux H_ P H t
  end.

Ltac revolve H_ t :=
  generalize H_;
  let H := fresh in
  intro H;
    (repeat rewrite <- app_ass in H);
    match type of H with
        holds ?P _ =>
        revolve_aux H_ P H t
    end.

Theorem holds_storev chunk o
        (Halign: (align_chunk chunk | Int.unsigned o)%Z)
        p (Hperm: perm_order p Writable) b:
  forall P m,
     holds (P ++ Pperm b (Int.unsigned o) p (size_chunk_nat chunk)) m ->
     forall v,
     exists m',
       Mem.storev chunk m (Vptr b o) v = Some m' /\
       holds (P ++ Pval chunk b (Int.unsigned o) p v) m'.
Proof.
  apply holds_store_perm; auto.
Qed.

Lemma holds_storev_exists P bsr osr psr chunk v (Q: _ -> Prop):
  (
    (align_chunk chunk | Int.unsigned osr)%Z /\
    perm_order psr Writable /\
    (
      forall m',
        holds (P ++
                 Pval chunk bsr (Int.unsigned osr) psr v)
              m' ->
        Q m'
    )
  ) ->
  forall m,
    holds
      (P ++
         Pperm bsr (Int.unsigned osr) psr (size_chunk_nat chunk)) m ->
    exists m' : mem,
      Mem.storev chunk m (Vptr bsr osr) v = Some m' /\
      Q m'.
Proof.
  intros H m H0.
  destruct H as (AL & PE & K).
  generalize (holds_storev  _ _ AL _ PE _ _ _ H0 v).
  intros H.
  break H.
  eauto.
Qed.

Ltac holds_storev_solve :=
  match goal with
      K: holds _ ?m
      |- exists m',
           Mem.storev ?chunk ?m_ (Vptr ?b ?o) _ = Some m' /\ _ =>
      (
        let t Q :=
            match Q with
                Pperm b (Int.unsigned o) ?p (size_chunk_nat chunk) =>
                idtac
              | Pval chunk b (Int.unsigned o) ?p _ =>
                apply Pval_Pperm in K
        end
        in
          revolve K t;
        revert m K;
        apply holds_storev_exists;
        solve_trivial
      )
  end.

Lemma list_comm_right_compat {A: Type} P Q:
  (forall x, list_comm P x -> list_comm x Q) ->
  forall u x,
    list_comm (P ++ u) x -> list_comm (A := A) x (Q ++ u).
Proof.
  intros H u x H0.
  setoid_rewrite <- H0.
  apply list_comm_compat.
  {
    eapply H; eauto.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma holds_list_comm_impl P Q:
  (forall x,
     list_comm P x -> list_comm x Q) ->
  forall m,
    holds P m ->
    holds Q m.
Proof.
  intros H m.
  apply holds_list_comm_aux.
  apply H; auto.
  reflexivity.
Qed.

Class DecideEq (T: Type): Type :=
  decide_eq_intro: forall t1 t2: T, {t1 = t2} + {t1 <> t2}.

Section WithDecideEq.

  Context `{DEC: DecideEq}.

  Definition count_occ := List.count_occ DEC.

  Lemma count_occ_app l1:
    forall l2 i,
      count_occ (l1 ++ l2) i = (count_occ l1 i + count_occ l2 i)%nat.
  Proof.
    induction l1; simpl; auto.
    intros l2 i.
    rewrite IHl1.
    destruct (DEC _ i); lia.
  Qed.

  Lemma count_occ_in i j l:
    count_occ l i = S j ->
    In i l.
  Proof.
    induction l; simpl; try discriminate.
    destruct (DEC a i); tauto.
  Qed.

  Lemma count_occ_list_comm l1:
    forall l2,
      (forall i, count_occ l1 i = count_occ l2 i) ->
      list_comm l1 l2.
  Proof.
    induction l1.
    {
      intros l2 H.
      destruct l2 as [ | t ].
      {
        reflexivity.
      }
      specialize (H t).
      simpl in H.
      destruct (DEC t t); congruence.
    }
    intros l2 H.
    assert (In a l2) as IN.
    {
      eapply count_occ_in.
      rewrite <- H.
      eapply count_occ_cons_eq.
      auto.
    }
    apply in_decomp in IN.
    destruct IN as (l3 & l4 & ? ).
    subst l2.
    setoid_rewrite list_comm_intro.
    simpl.
    rewrite <- app_cons_nil.
    symmetry.
    rewrite <- app_cons_nil.
    apply list_comm_compat.
    {
      reflexivity.
    }
    symmetry.
    apply IHl1.
    intros i.
    specialize (H i).
    rewrite count_occ_app in H |- * .
    simpl in H.
    destruct (DEC a i); lia.
  Qed.

End WithDecideEq.

(** NOTE: we could follow Leroy's Gagallium blog note <URL: http://gallium.inria.fr/blog/coq-eval/ >, but we are lazy *)

Global Instance: DecideEq Z := Z.eq_dec.

Global Instance: DecideEq permission.
Proof.
  red; intros. decide equality.
Defined.

Global Instance: DecideEq Values.block.
Proof.
  red; intros. decide equality.
Defined.

Global Instance: DecideEq val := Val.eq.

Global Instance: DecideEq memval.
Proof.
  red; intros. decide equality.
  {
   apply Byte.eq_dec.
  }
  {
    apply Nat.eq_dec.
  }
  {
    apply quantity_eq.
  }
  apply decide_eq_intro.
Defined.

Global Instance:
  forall U,
    DecideEq U ->
    DecideEq (option U).
Proof.
  red; intros.
  decide equality.
Defined.

Global Instance:
  forall U V,
    DecideEq U ->
    DecideEq V ->
    DecideEq (U * V).
Proof.
  red; intros.
  decide equality.
Defined.

Ltac eqm_signed u Hu :=
  let rec to_Z_signed x :=
      match x with
        | Int.add ?a ?b => 
          let u := to_Z_signed a in
          let v := to_Z_signed b in
          constr:(u + v)%Z
        | Int.sub ?a ?b => 
          let u := to_Z_signed a in
          let v := to_Z_signed b in
          constr:(u - v)%Z
        | Int.mul ?a ?b =>
          let u := to_Z_signed a in
          let v := to_Z_signed b in
          constr:(u * v)%Z
        | Int.neg ?a => 
          let u := to_Z_signed a in
          constr:(- u)%Z
        | Int.repr ?z => z
        | _ => constr:(Int.signed x)
      end
  in
  let w := to_Z_signed u in
  assert (Int.eqm (Int.signed u) w)
    as Hu
      by (repeat
           match goal with
             | _ => setoid_rewrite signed_add
             | _ => setoid_rewrite signed_sub
             | _ => setoid_rewrite signed_mul
             | _ => setoid_rewrite signed_neg
             | _ => setoid_rewrite eqm_signed_repr
           end;
          reflexivity)
.

Ltac erase_Pval H b o :=
  let t Q :=
      match Q with
          Pval _ b (Int.unsigned o) _ _ =>
          (apply Pval_Pperm in H)
      end
        in
  revolve H t.
