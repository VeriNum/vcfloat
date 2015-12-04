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

A simple separation logic for CompCert Clight temporary variables.
*)

Require Import Maps.
Require Import Clight.
Require Import ClightBigstep2.
Require Import Relations.
Require Import Morphisms.

Definition env_le {T: Type} (t1 t2: PTree.t T) :=
  forall i v,
    PTree.get i t1 = Some v ->
    PTree.get i t2 = Some v.

Global Instance env_le_refl: forall {T: Type}, Reflexive (env_le (T := T)).
Proof.
  do 2 red. tauto.
Qed.

Global Instance env_le_trans: forall {T: Type}, Transitive (env_le (T := T)).
Proof.
  intros T.
  do 2 red.
  intros x y z H H0 i v H1.
  red in H.
  red in H0.
  eauto.
Qed.

Require Import ClightTac.

Lemma exec_stmt_exists_lift ge le te1 m st (P: _ -> _ -> _ -> Prop):
  (
    forall te2,
      env_le te1 te2 ->
      exists te2_ m_ out,
        exec_stmt ge le te2 m st E0 te2_ m_ out /\
        forall te3_,
          env_le te2_ te3_ ->
          P te3_ m_ out
  ) ->
  exists te1_ m_ out,
    exec_stmt ge le te1 m st E0 te1_ m_ out /\
    P te1_ m_ out.
Proof.
  intros H.
  specialize (H _ $( reflexivity )$ ).
  destruct H as (te1_ & m_ & out & EXEC & H).
  specialize (H _ $( reflexivity )$ ).
  eauto.
Qed.

Lemma exec_Sskip_exists_lifted ge le te1 m (P: _ -> _ -> _ -> Prop):
  (
    forall te2,
      env_le te1 te2 ->
      P te2 m Out_normal
  )
  ->
  forall te2,
    env_le te1 te2 ->
    exists te2_ m_ out,
      exec_stmt ge le te2 m Sskip E0 te2_ m_ out /\
      forall te3_,
        env_le te2_ te3_ ->
        P te3_ m_ out.
Proof.
  intros H te2 H0.
  do 3 esplit.
  split.
  {
    econstructor.
  }
  intros te3_ H1.
  eapply H; etransitivity; eauto.
Qed.

Lemma loop_exists_lifted (I: _ -> _ -> Prop) W te m ge le st1 st2 (P_: _ -> _ -> _ -> Prop):
  (
    (
      I te m
    )
    /\
    (
      forall te0_ m0,
        I te0_ m0 ->
        forall te0,
          env_le te0_ te0 ->
          exists te1_ m1 out1,
            exec_stmt ge le te0 m0 st1 E0 te1_ m1 out1 /\
            forall te1,
              env_le te1_ te1 ->
              if orb (out_normal_b out1) (out_continue_b out1)
              then
                exists te2_ m2 out2,
                  exec_stmt ge le te1 m1 st2 E0 te2_ m2 out2 /\
                  forall te2,
                    env_le te2_ te2 ->
                    if orb (out_normal_b out2) (out_continue_b out2)
                    then
                      out2 = Out_normal /\
                      I te2 m2 /\ (W te2 m2 < W te0_ m0)%nat
                    else
                      (
                        P_ te2 m2 (out_break_or_return_f out2)
                      )
              else
                (
                  P_
                    te1
                    m1
                    (out_break_or_return_f out1)
                )
    )
  ) ->
  forall te1,
    env_le te te1 ->
    exists te2 m_ out_,
      exec_stmt ge le te1 m (Sloop st1 st2) E0 te2 m_ out_ /\
      forall te_,
        env_le te2 te_ ->
        P_ te_ m_ out_.
Proof.
  intros H.
  destruct H as (H0 & H).
  destruct (rememb (W te m)) as (n & Hn).
  revert te m Hn H0.
  induction n using (well_founded_induction lt_wf).
  intros te m Hn H1.
  subst.
  specialize (H _ _ H1). clear H1.
  intros te1 H1.
  specialize (H _ H1). clear H1.
  destruct H as (te1_ & m1 & out1 & Hst1 & H1).
  destruct (orb (out_normal_b out1) (out_continue_b out1)) eqn:NORMAL_OR_CONTINUE1.
  {
    specialize (H1 _ $( reflexivity )$ ).
    rewrite out_normal_or_continue_iff in NORMAL_OR_CONTINUE1.
    destruct H1 as (te2_ & m2 & out2 & Hst2 & H1).
    destruct (orb (out_normal_b out2) (out_continue_b out2)) eqn:NORMAL_OR_CONTINUE2.
    {
      specialize (H1 _ $( reflexivity )$ ).
      destruct H1 as (? & HI & HW).
      subst.
      specialize (H0 _ HW _ _ (eq_refl _) HI).
      specialize (H0 _ $( reflexivity )$ ).
      break H0.
      do 3 esplit.
      split; eauto.
      replace E0 with (E0 ** E0 ** E0) by traceEq.
      eapply exec_Sloop_loop; eauto.
    }
    clear H0.
    apply out_break_or_return_intro in NORMAL_OR_CONTINUE2.
    replace E0 with (E0 ** E0) by traceEq.
    do 3 esplit.
    split; eauto.
    eapply exec_Sloop_stop2; eauto.
  }
  clear H0.
  apply out_break_or_return_intro in NORMAL_OR_CONTINUE1.
  do 3 esplit.
  split; eauto.
  eapply exec_Sloop_stop1; eauto.
Qed.

Global Instance PTree_set_le:
  forall {A: Type},
    Proper (eq ==> eq ==> env_le ==> env_le) (PTree.set (A := A)).
Proof.
  do 4 red.
  unfold env_le.
  intros A x y H x0 y0 H0 x1 y1 H1 i v.
  subst.
  repeat rewrite PTree.gsspec.
  destruct (peq i y); auto.
Qed.

Lemma exec_Sset_exists_lifted ge e le m id a (P: _ -> _ -> _ -> Prop):
  (
    exists v,
      eval_expr ge e le m a v /\
      forall le_,
        env_le (Maps.PTree.set id v le) le_ ->
        P le_ m Out_normal
  ) ->
  forall le1,
    env_le le le1 ->
    exists le2 m2 out,
      exec_stmt ge e le1 m (Sset id a) E0 le2 m2 out /\
      forall le2_,
        env_le le2 le2_ ->
        P le2_ m2 out.
Proof.
  intros H le1 H0.
  destruct H as (v & Hv & Q).
  do 3 esplit.
  split.
  {
    econstructor.
    eapply eval_expr_impl; eauto.
  }
  setoid_rewrite H0 in Q.
  assumption.
Qed.

Lemma exec_Sseq_exists_lifted ge e le m st1 st2 (P: _ -> _ -> _ -> Prop):
  (
    forall le0,
      env_le le le0 ->
      exists le1 m1 out1,
        exec_stmt ge e le0 m st1 E0 le1 m1 out1 /\
        forall le1_,
          env_le le1 le1_ ->
          if out_normal_b out1
          then
            exists le2 m2 out2,
              exec_stmt ge e le1_ m1 st2 E0 le2 m2 out2 /\
              forall le2_,
                env_le le2 le2_ ->
                P le2_ m2 out2
          else
            P le1_ m1 out1
  ) ->
  forall le0,
    env_le le le0 ->
    exists le2 m2 out,
      exec_stmt ge e le0 m (Ssequence st1 st2) E0 le2 m2 out /\
      forall le2_,
        env_le le2 le2_ ->
        P le2_ m2 out.
Proof.
  intros H le0 H0.
  specialize (H _ H0).
  destruct H as (le1 & m1 & out1 & Hexec1 & TEST).
  destruct (out_normal_b out1) eqn:NORMAL.
  {
    rewrite out_normal_b_iff in NORMAL.
    subst.
    specialize (TEST _ $( reflexivity )$ ).
    destruct TEST as (le2 & m2 & out2 & Hexec2 & HP).
    do 3 esplit.
    split; eauto.
    replace E0 with (E0 ** E0) by traceEq.
    econstructor; eauto.
  }
  do 3 esplit.
  split; eauto.
  econstructor; eauto.
  rewrite <- out_normal_b_iff.
  congruence.
Qed.

Lemma exec_Sifthenelse_exists_lifted ge e le m a st1 st2 (P: _ -> _ -> _ -> Prop):
  (
    exists v,
      eval_expr ge e le m a v /\
      exists b,
        bool_val v (typeof a) m = Some b /\
        forall le1,
          env_le le le1 ->
          exists le2 m2 out,
            exec_stmt ge e le1 m (if b then st1 else st2) E0 le2 m2 out /\
            forall le2_,
              env_le le2 le2_ ->
              P le2_ m2 out
  ) ->
  forall le1,
    env_le le le1 ->
    exists le2 m2 out,
      exec_stmt ge e le1 m (Sifthenelse a st1 st2) E0 le2 m2 out /\
      forall le2_,
        env_le le2 le2_ ->
        P le2_ m2 out.
Proof.
  intros H le1 H0.
  destruct H as (v & Hv & b & Hb & H). 
  specialize (H _ H0).
  destruct H as (le2 & m2 & out & Hexec & HP).
  do 3 esplit.
  split; eauto.
  econstructor; eauto.
  eapply eval_expr_impl; eauto.
Qed.

Lemma exec_Sreturn_none_exists_lifted ge e le m (P: _ -> _ -> _ -> Prop):
  (forall le_,
     env_le le le_ ->
     P le_ m (Out_return None)) ->
  forall le_,
    env_le le le_ ->  
    exists le2 m2 out2,
      exec_stmt ge e le_ m (Sreturn None) E0 le2 m2 out2 /\
      forall le2_,
        env_le le2 le2_ ->
        P le2_ m2 out2.
Proof.
  intros H le_ H0.
  do 3 esplit.
  split.
  {
    constructor.
  }
  intros le2_ H1.
  eapply H; etransitivity; eauto.
Qed.

Lemma exec_Sreturn_some_exists_lifted ge e le m a (P: _ -> _ -> _ -> Prop):
  (
    exists v,
      eval_expr ge e le m a v /\
      forall le_,
        env_le le le_ ->
        P le_ m (Out_return (Some (v, typeof a)))
  ) ->
  forall le_,
    env_le le le_ ->  
  exists le2 m2 out2,
    exec_stmt ge e le_ m (Sreturn (Some a)) E0 le2 m2 out2 /\
    forall le2_,
      env_le le2 le2_ ->
      P le2_ m2 out2.
Proof.
  intros H le_ H0.
  destruct H as (v & Hv & HP).
  do 3 esplit.
  split.
  {
    econstructor; eauto.
    eapply eval_expr_impl; eauto.
  }
  intros le2_ H.
  eapply HP; etransitivity; eauto.
Qed.

Lemma exec_Sbreak_exists_lifted ge e le m (P: _ -> _ -> _ -> Prop):
  (forall le_,
     env_le le le_ ->
     P le_ m Out_break) ->
forall le_,
  env_le le le_ ->
  exists le2 m2 out2,
    exec_stmt ge e le_ m Sbreak E0 le2 m2 out2 /\
    forall le2_,
      env_le le2 le2_ ->
      P le2_ m2 out2.
Proof.
  intros H le_ H0.
  do 3 esplit.
  split.
  {
    constructor.
  }
  intros le2_ H1.
  eapply H; etransitivity; eauto.
Qed.

Lemma exec_Scontinue_exists_lifted ge e le m (P: _ -> _ -> _ -> Prop):
  (forall le_,
     env_le le le_ ->
     P le_ m Out_continue) ->
  forall le_,
    env_le le le_ ->
    exists le2 m2 out2,
      exec_stmt ge e le_ m Scontinue E0 le2 m2 out2 /\
      forall le2_,
        env_le le2 le2_ ->
        P le2_ m2 out2.
Proof.
  intros H le_ H0.
  do 3 esplit.
  split.
  {
    constructor.
  }
  intros le2_ H1.
  eapply H; etransitivity; eauto.
Qed.

Lemma exec_Sassign_exists_lifted
     : forall (ge : genv) (e : env) (le : temp_env) 
              (m : Memory.Mem.mem) (a1 a2 : expr)
              (P: _ -> _ -> _ -> Prop),
         (exists 
             (loc : block) (ofs : int),
             eval_lvalue ge e le m a1 loc ofs /\
             exists v2,
               eval_expr ge e le m a2 v2 /\
               exists (v : val),
                 Cop.sem_cast v2 (typeof a2) (typeof a1) = Some v /\
                 exists (m' : Memory.Mem.mem),
                   assign_loc ge (typeof a1) m loc ofs v m' /\
                   forall le1,
                     env_le le le1 ->
                     P le1 m' Out_normal
         ) ->
         forall le1,
           env_le le le1 ->
           exists le2 m2 out2,
             exec_stmt ge e le1 m (Sassign a1 a2) E0 le2 m2 out2 /\
             forall le3, env_le le2 le3 ->
             P le3 m2 out2.
Proof.
  intros ge e le m a1 a2 P H le1 H0.
  break H.
  do 3 esplit.
  split.
  {
    econstructor; eauto.
    {
      eapply eval_lvalue_impl; eauto.
    }
    eapply eval_expr_impl; eauto.
  }
  intros le3 H1.
  eapply H; etransitivity; eauto.
Qed.

Global Instance set_opttemp_le:
  Proper (eq ==> eq ==> env_le ==> env_le) set_opttemp.
Proof.
  do 4 red.
  unfold env_le.
  intros x y H x0 y0 H0 x1 y1 H1 i v.
  subst.
  unfold set_opttemp.
  destruct y; auto.
  apply PTree_set_le; auto.
Qed.

Lemma exec_Scall_exists_lifted (ge : genv) (e : env) (le : temp_env) 
         (m : Memory.Mem.mem) (optid : option ident) 
         (a : expr) (al : list expr)  
         (P: _ -> _ -> _ -> Prop)
:
  (
    exists (tyargs : typelist) 
           (tyres : type) (cconv : calling_convention),
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv /\
      exists (vf : val),
        eval_expr ge e le m a vf /\
        exists (vargs : list val),
          eval_exprlist ge e le m al tyargs vargs /\
          exists (f : Clight.fundef),
            Globalenvs.Genv.find_funct ge vf = Some f /\
            type_of_fundef f = Tfunction tyargs tyres cconv /\
            exists (m' : Memory.Mem.mem) (vres : val),
              eval_funcall ge m f vargs E0 m' vres /\
              forall le_,
                env_le (set_opttemp optid vres le) le_ ->
                P le_  m' Out_normal
  ) ->
  forall le1,
    env_le le le1 ->
    exists le2 m' out,
    exec_stmt ge e le1 m (Scall optid a al) E0 le2 m' out /\
    forall le',
      env_le le2 le' ->
      P le' m' out.
Proof.
  intros H le1 H0.
  break H.
  do 3 esplit.
  split.
  {
    econstructor; eauto.
    {
      eapply eval_expr_impl; eauto.
    }
    eapply eval_exprlist_impl; eauto.
  }
  setoid_rewrite H0 in H.
  assumption.
Qed.


  Lemma env_le_elements {A} l2 l1:
    Maps.PTree.elements l1 = Maps.PTree.elements l2 ->
    forall t: Maps.PTree.t A,
      env_le l1 t ->
      env_le l2 t.
  Proof.
    clear.
    unfold env_le.
    intros H t H0 i v H1.
    apply H0.
    apply Maps.PTree.elements_complete.
    rewrite H.
    apply Maps.PTree.elements_correct.
    assumption.
  Qed.

    Lemma env_le_set_l {A} i te (v: A):
      Maps.PTree.get i te = Some v ->
      forall te',
        env_le te te' ->
        env_le (Maps.PTree.set i v te) te'.
    Proof.
      clear.
      unfold env_le.
      intros H te' H0 i0 v0.
      rewrite Maps.PTree.gsspec.
      destruct (peq i0 i); auto.
      subst.
      inversion 1; subst.
      auto.
    Qed.

    Lemma env_le_empty {A} (te: _ A):
      env_le (Maps.PTree.empty _) te.
    Proof.
      unfold env_le.
      intros i v.
      rewrite Maps.PTree.gempty.
      discriminate.
    Qed.

    Import List.
  Fixpoint create_map {A} (l: list (ident * A)) (u: Maps.PTree.t A): Maps.PTree.t A :=
    match l with
      | nil => u
      | (v, a) :: q =>
        Maps.PTree.set v a (create_map q u)
    end.

  Lemma set_create_map {A} v (a: A) u:
    Maps.PTree.set v a u = create_map ((v, a) :: nil) u.
  Proof.
    reflexivity.
  Qed.

  Lemma create_map_app {A: Type} l1 l2 (u: _ A):
    create_map l1 (create_map l2 u) = create_map (l1 ++ l2) u.
  Proof.
    induction l1; simpl; auto.
    destruct a.
    congruence.
  Qed.

    Global Instance create_map_le {A}:
      Proper (eq ==> env_le ==> env_le) (create_map (A := A)).
    Proof.
      clear.
      do 3 red.
      intros x y H x0 y0 H0.
      subst.
      induction y; simpl; auto.
      destruct a.
      apply PTree_set_le; auto.
    Qed.

