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

VCFloat: automatic translation of a CompCert Clight floating-point
expression into a real-number expression with all rounding error terms
and their correctness proofs.
**)

Require Export RAux.
Require Export Clight2FP.
Require Export LibTac.
Require Export FPLangOpt.
      
Local Existing Instance nans.

Definition static_float m e :=
  match static_float m e with
    | None => None
    | Some t => Some (fshift (fcval t))
  end.

Export FPLang.

Lemma static_float_correct
     : forall (m : Maps.PTree.t type) (me : Maps.PTree.t Values.val)
         (env : forall x : type, AST.ident -> ftype x) 
         (ge : Clight.genv) (ce : Clight.env) (mm : Memory.Mem.mem)
         (e : Clight.expr),
       (forall i : AST.ident,
          List.In i (VSET.elements (cvars e)) ->          
        forall ty : type,
        Maps.PTree.get i m = Some ty -> ty = Tsingle \/ ty = Tdouble) ->
       (forall i : AST.ident,
          List.In i (VSET.elements (cvars e)) ->
          forall ty : type,
            Maps.PTree.get i m = Some ty ->
            exists v : Values.val,
              Maps.PTree.get i me = Some v /\ val_inject v ty (env ty i)) ->
       forall t : expr,
         static_float m e = Some t ->
         exists v : Values.val,
           Clight.eval_expr ge ce me mm e v /\
           val_inject v (type_of_expr t) (fval env t)
.
Proof.
  intros.
  unfold static_float in H1.
  destruct (Clight2FP.static_float m e) eqn:E; try discriminate.
  inversion H1; clear H1; subst; simpl.
  specialize (static_float_correct m me env ge ce mm e H H0 _ E).
  destruct 1 as (v & EVAL & FVAL).
  esplit.
  split; eauto.
  rewrite fshift_correct.
  apply val_inject_eq_rect_r.
  rewrite fcval_correct.
  apply val_inject_eq_rect_r.
  assumption.
Qed.


(* Tactic for automatic annotations *)

Require Import Flocq.Appli.Fappli_IEEE.
Require Import Reals.
Open Scope R_scope.

Local Existing Instances
      map_nat compcert_map
.


Require Import compcert.Values.


Require Import Clight.

Require Import Interval.Interval_tactic.
Require Import Psatz.


Require Import List.


Lemma Sreturn_inj a1 a2:
  Sreturn a1 = Sreturn a2 ->
  a1 = a2.
Proof.
  congruence.
Qed.


(* transform the C expression into a floating-point expression *)

Ltac C_to_float_aux k ge lenv tenv m e :=
      generalize (eqpivot (static_float (ttenv tenv) e));
        let o := fresh in
        let K := fresh in
        let K_ := fresh in
        destruct 1 as (o & K & K_);
          vm_compute in K_;
          rewrite K_ in K; clear o K_;
          generalize (fun H =>
                        static_float_correct
                          (ttenv tenv) tenv ((env_ tenv)) ge lenv m _ (fun i _ => ttenv_float _ i)
                          H
                          _ K
                     );
      clear K; intro K;
      specialize
        (K
           $(
             rewrite <- list_forall_spec;
             simpl;
             repeat
               match goal with
                   |- _ /\ _ => split
                 | |- True => exact I
                 | |- _ => inversion 1; subst;
                   now (eauto using Clight2FP.val_inject_single, Clight2FP.val_inject_double)
               end
           )$
        );
      let v := fresh in
      let Hv := fresh in
      let INJ := fresh in
      destruct K as (v & Hv & INJ);
        match type of INJ with
            Clight2FP.val_inject _ _ ?z =>
            generalize (eqpivot z)
        end;
        let o := fresh in
        let OL := fresh in
        destruct 1 as (o & OL & _);
          rewrite OL in INJ;
          vm_compute in INJ, o;
          match type of INJ with
              Clight2FP.val_inject _ ?ty _ =>
              let b := (eval cbn in (type_eqb ty Tsingle)) in
              match b with
                | true => apply val_inject_single_left_inv in INJ
                | _ =>
                  let b := (eval cbn in (type_eqb ty Tdouble)) in
                  match b with
                    | true => apply val_inject_double_left_inv in INJ
                  end
              end
          end;
          subst v;
          esplit;
          split; [ eassumption | ];
          clear Hv;
          k o OL
.

Ltac C_to_float k :=
  match goal with
      |- exists y: Floats.float32, eval_expr ?ge ?lenv ?tenv ?m ?e (Vsingle y) /\ _
      =>
      C_to_float_aux k ge lenv tenv m e
    | |- exists y: Floats.float, eval_expr ?ge ?lenv ?tenv ?m ?e (Vfloat y) /\ _
      =>
      C_to_float_aux k ge lenv tenv m e
  end.


Ltac C_to_float_as o OL :=
  (assert True as o by exact I);
  (assert True as OL by exact I);
  let k o_ OL_ :=
      clear o; rename o_ into o;
      clear OL; rename OL_ into OL
  in
  C_to_float k
.


Require Import Floats.
Require Import Integers.
Open Scope R_scope.

