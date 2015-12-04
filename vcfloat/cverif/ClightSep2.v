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

A tactic for CompCert Clight structured control.
*)

Require Import Memory.
Require Export ClightTac.
Require Export SepLogic.

Lemma assign_loc_exists_value ge ty m b ofs v (P: _ -> Prop):
(
  exists chunk,
    Ctypes.access_mode ty = Ctypes.By_value chunk /\
    exists m',
      Mem.storev chunk m (Vptr b ofs) v = Some m' /\
      P m'
) ->
  exists m',
    assign_loc ge ty m b ofs v m' /\
    P m'
.
Proof.
  intros H.
  break H.
  esplit.
  split; eauto.
  eapply assign_loc_value; eauto.
Qed.

Ltac run :=
  match goal with
      |- exists s2,
           Smallstep.star
             step2 _
             (State _ (Ssequence _ _) _ _ _ _)
             Events.E0 _ /\ _ =>
      apply star_exists_step;
        apply step_exists_seq
    | |- exists s2,
           Smallstep.star
             step2 _
             (State _ (Scall _ _ _) _ _ _ _)
             Events.E0 _ /\ _ =>
      apply star_exists_step;
        apply step_exists_call;
        solve_trivial
    | |- exists vf,
           eval_expr _ ?le _ _ (Evar ?v _) _ /\ _ =>
      let v := (eval cbn in (Maps.PTree.get v le)) in
      match v with
        | None =>
          apply eval_exists_Evar_global;
            solve_trivial
      (* HERE provide the case Evar_local *)
      end
    | |- exists vargs,
           eval_exprlist _ _ _ _ _ _ _ /\ _ =>
      apply eval_exprlist_exists_correct;
        unfold eval_exprlist_exists
    | |- exists v,
           eval_expr _ _ _ _ (Etempvar _ _) _ /\ _ =>
      apply eval_exists_Etempvar;
        solve_trivial
    | |- exists s2,
           Smallstep.star _ _ (Returnstate _ (Kcall _ _ _ _ _) _) Events.E0 _ /\ _
      =>
      apply star_exists_step;
        apply step_exists_returnstate
    | |- exists s2,
           Smallstep.star _ _ (State _ Sskip (Kseq _ _) _ _ _) Events.E0 _ /\ _
      =>
      apply star_exists_step;
        apply step_exists_skip_seq
    | |- exists s2,
           Smallstep.star _ _ (State _ (Sset _ _) _ _ _ _) Events.E0 _ /\ _
      =>
      apply star_exists_step;
        apply step_exists_set
    | |- exists s2,
           Smallstep.star step2 _
                          (State _ (Sassign _ _) _ _ _ _)
                          Events.E0 _ /\ _
      =>
      apply star_exists_step;
        apply step_exists_assign
    | |- exists loc ofs,
           eval_lvalue _ _ _ _ (Ederef _ _) _ _ /\ _
      =>
      apply eval_lvalue_exists_Ederef
    | |- exists m,
           assign_loc _ ?ty _ _ _ _ _ /\ _ =>
      let am := (eval cbn in (Ctypes.access_mode ty)) in
      match am with
        | Ctypes.By_value _ =>
          apply assign_loc_exists_value;
            solve_trivial
      (* HERE add the Ctypes.By_reference case *)
      end
    | |- exists s2,
           Smallstep.star _ _ (State _ Sskip Kstop _ _ _) Events.E0 _ /\ _
      =>
      apply star_exists_step;
        apply step_exists_skip_call;
        solve_trivial      
    | |- exists v,
           eval_expr _ _ _ _ (Ederef _ _) _ /\ _
      =>
      apply eval_exists_Ederef;
        solve_trivial
    | |- exists s,
           Smallstep.star _ _ (State _ (Sreturn None) _ _ _ _) Events.E0 _ /\ _
      =>
      apply star_exists_step;
        apply step_exists_return_none_2;
        let k' := fresh in
        let K' := fresh in
        intros k' K';
          cbn in K';
          subst k';
          solve_trivial

  end.
