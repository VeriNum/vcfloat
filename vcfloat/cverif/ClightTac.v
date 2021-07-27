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

Helpers for CompCert Clight structured control and temporary
variables.
*)

From compcert.lib Require Export Coqlib Integers.
From compcert.common Require Export Values Events Smallstep.
From compcert.cfrontend Require Export Ctypes Cop Clight.
From compcert.exportclight Require Export Clightdefs.
Require Export cverif.ClightBigstep2.
Require Export LibTac.
Require Export cverif.ClightFacts.
Require Export Reals Psatz.
Require Export ZArith.
Require Export Morphisms.

Lemma deepest_expr_exists e tenv ge lenv m (P: _ -> Prop):
(
  forall i,
    i = next_index xH (Maps.PTree.elements tenv) (* to compute *)
    ->
    (
      VSET.mem i (cvars e) = false /\
      exists e' e1,
        deepest_expr i e = (e', e1) /\
        exists v',
          eval_expr ge lenv tenv m e' v' /\
          exists v,
            eval_expr ge lenv (Maps.PTree.set i v' tenv) m e1 v /\
            P v
    )
) ->
exists v,
  eval_expr ge lenv tenv m e v /\
  P v
.
Proof.
  intros.
  specialize (H _ (eq_refl _)).
  break H.
  esplit.
  split; eauto.
  eapply subst_expr_correct; eauto.
  {
    apply next_index_correct.
  }
  eapply deepest_expr_correct; eauto.
  rewrite <- VSET.mem_spec.
  congruence.
Qed.

Lemma shallowest_expr_exists e tenv ge lenv m (P: _ -> Prop):
(
  forall i,
    i = next_index xH (Maps.PTree.elements tenv) (* to compute *)
    ->
    (
      VSET.mem i (cvars e) = false /\
      exists e' e1,
        shallowest_expr i e = (e', e1) /\
        exists v1,
          eval_expr ge lenv tenv m e1 v1 /\
          exists v,
            eval_expr ge lenv (Maps.PTree.set i v1 tenv) m e' v /\
            P v
    )
) ->
exists v,
  eval_expr ge lenv tenv m e v /\
  P v
.
Proof.
  intros.
  specialize (H _ (Logic.eq_refl _)).
  break H.
  esplit.
  split; eauto.
  eapply subst_expr_correct; eauto.
  {
    apply next_index_correct.
  }
  eapply shallowest_expr_correct; eauto.
  rewrite <- VSET.mem_spec.
  congruence.
Qed.

(* Clight existential constructs *)

Lemma star_return_single (P: Floats.float32 -> Prop) m ge st0:
(
exists s,
 Smallstep.star step2 ge st0 Events.E0 s /\
 exists y,
   s = Returnstate (Vsingle y) Kstop m /\
   P y
)
->
(
exists y,
 Smallstep.star step2 ge st0 Events.E0 (Returnstate (Vsingle y) Kstop m) /\
 P y
). 
Proof.
  destruct 1.
  destruct H.
  destruct H0.
  destruct H0.
  subst.
  eauto.
Qed.

Lemma star_exists_step (P: _ -> Prop) ge st0:
  (
    exists s1,
      step2 ge st0 Events.E0 s1 /\
      exists s2,
        Smallstep.star step2 ge s1 Events.E0 s2 /\
        P s2
  ) ->
  exists s2,
    Smallstep.star step2 ge st0 Events.E0 s2 /\
    P s2
.
Proof.
  destruct 1.
  destruct H.
  destruct H0.
  destruct H0.
  esplit.
  split; eauto.
  eapply Smallstep.star_step; eauto.
Qed.

Require Import List.

Fixpoint alloc_variables_compute (ge: genv) (e: env) (m: Memory.Mem.mem) (l: list (AST.ident * Ctypes.type)) {struct l}: (env * Memory.Mem.mem) :=
  match l with
    | nil => (e, m)
    | ((id, ty) :: vars) =>
      let '(m1, b1) := Memory.Mem.alloc m 0 (Ctypes.sizeof ge ty) in
      alloc_variables_compute ge (Maps.PTree.set id (b1, ty) e) m1 vars
  end.

Lemma alloc_variables_compute_correct ge l:
  forall e m e' m',
    alloc_variables_compute ge e m l = (e', m') ->
    alloc_variables ge e m l e' m'.
Proof.
  induction l; simpl.
  {
    inversion 1; subst; constructor.
  }
  destruct a.
  intros until m'.
  destruct (Memory.Mem.alloc m 0 (Ctypes.sizeof ge t)) eqn:ALLOC.
  intros.
  econstructor; eauto.
Qed.

Definition function_entry2_compute 
           (ge : genv) (f : function) (vargs : list val)
           (m : Memory.Mem.mem):
  option ((env) * (temp_env) * (Memory.Mem.mem))
  :=
    if
      andb
      (
        Coqlib.proj_sumbool
          (Coqlib.list_norepet_dec AST.ident_eq (var_names (fn_vars f)))
      ) 
      (
        andb
          (
            Coqlib.proj_sumbool (Coqlib.list_norepet_dec AST.ident_eq (var_names (fn_params f)))
          )
          (
            Coqlib.proj_sumbool (Coqlib.list_disjoint_dec AST.ident_eq (var_names (fn_params f)) (var_names (fn_temps f)))
          )
      )
    then
      let (e, m') := alloc_variables_compute ge empty_env m (fn_vars f) in
      match bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)) with
        | Some le => Some (e, le, m')
        | None => None
      end
    else None
.

Lemma function_entry2_compute_correct ge f vargs m e le m':
  function_entry2_compute ge f vargs m = Some (e, le, m') ->
  function_entry2 ge f vargs m e le m'.
Proof.
  unfold function_entry2_compute.
  destruct
    (
(Coqlib.proj_sumbool
        (Coqlib.list_norepet_dec AST.ident_eq (var_names (fn_vars f))) &&
      (Coqlib.proj_sumbool
         (Coqlib.list_norepet_dec AST.ident_eq (var_names (fn_params f))) &&
       Coqlib.proj_sumbool
         (Coqlib.list_disjoint_dec AST.ident_eq (var_names (fn_params f))
            (var_names (fn_temps f)))))%bool
    ) eqn:BOOL; try discriminate.
  repeat rewrite Bool.andb_true_iff in BOOL.
  destruct BOOL.
  destruct H0.
  repeat
    match goal with
        K: Coqlib.proj_sumbool _ = true |- _ =>
        apply Coqlib.proj_sumbool_true in K
    end.
  destruct (alloc_variables_compute ge empty_env m (fn_vars f)) eqn:ALLOC.
  destruct (bind_parameter_temps (fn_params f)  vargs (create_undef_temps (fn_temps f))) eqn:BIND; try discriminate.
  inversion 1; subst.
  econstructor; eauto using alloc_variables_compute_correct.
Qed.

Ltac call_fn :=
  match goal with
      |- exists s,
           step2 ?ge (Callstate (Ctypes.Internal ?f) ?l _ ?m) _ _ /\ _ =>
      let j := fresh in
      let JL := fresh in
      let JR := fresh in
      destruct (eqpivot (function_entry2_compute ge f l m))
        as (j & JL & JR);
        cbn -[Maps.PTree.set] in JR;
        subst j;
        apply function_entry2_compute_correct in JR;
        esplit;
        split; [ econstructor; eassumption | ];
        clear JR
  end.

Lemma star_exists_return_single e f m1 ge lenv m2 k tenv (P: _ -> Prop):
Cop.classify_cast (typeof e) (fn_return f) = Cop.cast_case_s2s ->
Memory.Mem.free_list m1 (blocks_of_env ge lenv) = Some m2 ->
call_cont k = Kstop ->
(
  exists v,
    eval_expr ge lenv tenv m1 e (Vsingle v) /\
    P v
) -> (
  exists s2,
    Smallstep.star step2 ge
                 (State f (Sreturn (Some e)) k lenv tenv m1) Events.E0 s2
  /\
  exists y, s2 = Returnstate (Vsingle y) Kstop m2
            /\
            P y
).
Proof.
  destruct 4.
  destruct H2.
  esplit.
  split; eauto.
  eapply Smallstep.star_step.
  {
    eapply step_return_1; eauto.
    unfold Cop.sem_cast.
    rewrite H.
    reflexivity.
  }
  {
    rewrite H1.
    eapply Smallstep.star_refl.
  }
  reflexivity.
Qed.

(* Some "program logic"-like proof rules *)

Require Import compcert.common.Globalenvs.

Lemma step_exists_seq (P: _ -> Prop) f u1 u2 k lenv tenv m ge:
  P (State f u1 (Kseq u2 k) lenv tenv m)
  ->
  (exists s1, step2 ge (State f (Ssequence u1 u2) k lenv tenv m) Events.E0 s1
             /\ P s1)
.
Proof.
  intros.
  esplit.
  split; eauto.
  constructor.
Qed.

Lemma step_exists_call ge le m a al f optid k e (P: _ -> Prop):
  (
    exists tyargs tyres cconv,
      Cop.classify_fun (typeof a) = Cop.fun_case_f tyargs tyres cconv /\
      exists vf,
        eval_expr ge e le m a vf /\
        exists fd,
          Genv.find_funct ge vf = Some fd /\
          type_of_fundef fd = Ctypes.Tfunction tyargs tyres cconv /\
          exists vargs,
            eval_exprlist ge e le m al tyargs vargs /\
            P (Callstate fd vargs (Kcall optid f e le k) m)
  ) ->
  exists s,
    step2 ge (State f (Scall optid a al) k e le m) Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma eval_exists_Evar_global v (P: _ -> Prop) (ge: genv) tenv m ty:
  (
    Ctypes.access_mode ty = Ctypes.By_reference /\
    exists l,
      Genv.find_symbol ge v = Some l /\
      P (Vptr l Integers.Ptrofs.zero)
  ) ->
  exists vf,
    eval_expr ge empty_env tenv m (Evar v ty) vf /\ P vf.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  econstructor.
  {
    eapply eval_Evar_global; eauto.
    apply Maps.PTree.gempty.
  }
  constructor.
  auto.
Qed.

Require Import List.

Fixpoint eval_exprlist_exists ge lenv tenv m (l: list Clight.expr) (lt: Ctypes.typelist) (P: list val -> Prop) {struct l} :=
  match l with
    | nil => 
      match lt with
        | Ctypes.Tnil => P nil
        | _ => False
      end
    | e1 :: l' =>
      match lt with
        | Ctypes.Tcons ty1 lt' =>
          exists v1,
            eval_expr ge lenv tenv m e1 v1 /\
            exists v2,
              Cop.sem_cast v1 (typeof e1) ty1 m = Some v2 /\
              eval_exprlist_exists ge lenv tenv m l' lt' (fun l_ => P (v2 :: l_))
        | _ => False
      end
  end.

Lemma eval_exprlist_exists_correct ge lenv tenv m l:
  forall lt (P: _ -> Prop),
    eval_exprlist_exists ge lenv tenv m l lt P ->
    exists lv, eval_exprlist ge lenv tenv m l lt lv /\ P lv.
Proof.
  induction l; simpl.
  {
    destruct lt; try tauto.
    intros.
    esplit.
    split; eauto.
    constructor.
  }
  destruct lt; try tauto.
  intros.
  break H.
  apply IHl in H.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma eval_exists_Etempvar i te ge le ty m (P: _ -> Prop):
  (
    exists v_,
      Maps.PTree.get i te = Some v_ /\
      P v_
  ) ->
  exists v,
  eval_expr ge le te m (Etempvar i ty) v /\ P v
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  econstructor.
  assumption.
Qed.

Lemma exec_call_exists k ge f vargs m (P: _ -> Prop):
  (
    is_call_cont k /\
    exists s1,
      Smallstep.star step2 ge
                     (Callstate f vargs Kstop m) Events.E0 s1
      /\
      exists v1 m1,
        s1 = Returnstate v1 Kstop m1
    /\
    exists s2,
      Smallstep.star step2 ge
                     (Returnstate v1 k m1) Events.E0 s2
      /\
    P s2
  ) -> (
      exists s2,
        Smallstep.star step2 ge
                       (Callstate f vargs k m)
                       Events.E0
                       s2
        /\ P s2
    ).
Proof.
  intros.
  break H.
  subst.
  esplit.
  split; eauto.
  apply (star2_concat_cont k) in K_0; auto.
  eapply Smallstep.star_trans; eauto.
Qed.

Lemma exists_single_elim (P: _ -> Prop) (Q: _ -> Prop) m:
  (exists v,
    P (Returnstate (Vsingle v) Kstop m) /\
    Q v) ->
  (exists s,
     P s /\
     exists v,
       s = Returnstate (Vsingle v) Kstop m /\
       Q v)
.
Proof.
  intros.
  break H.
  eauto.
Qed.

Lemma step_exists_returnstate ge (v : val) (optid : option AST.ident)
                         (f : function) (e : env) (le : temp_env) 
                         (k : cont) (m : Memory.Mem.mem)
                         (P: _ -> Prop):
  P (State f Sskip k e (set_opttemp optid v le) m) ->
  exists s,
    step2 ge
          (Returnstate v (Kcall optid f e le k) m) Events.E0
          s /\
    P s.
Proof.
  intros.
  esplit.
  split; eauto.
  constructor.
Qed.

Lemma step_exists_skip_seq ge (f : function) (s : statement) 
      (k : cont) (e : env) (le : temp_env)
      (m : Memory.Mem.mem)
      (P: _ -> Prop)
:
  P (State f s k e le m) ->
  exists s',
    step2 ge (State f Sskip (Kseq s k) e le m)
         Events.E0 s' /\
    P s' 
.
Proof.
  intros.
  esplit.
  split; eauto.
  constructor.
Qed.

Lemma step_exists_set ge (f : function) (id : AST.ident) 
      (a : Clight.expr) (k : cont) (e : env) 
      (le : temp_env) (m : Memory.Mem.mem)
      (P: _ -> Prop)
:
  (exists (v : val),
     eval_expr ge e le m a v /\
     P (State f Sskip k e (Maps.PTree.set id v le) m)) ->
  exists s,
    step2 ge (State f (Sset id a) k e le m)
         Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma Vsingle_exists (P: _ -> Prop):
  (exists i, P (Vsingle i)) ->
  exists v, P v.
Proof.
  destruct 1; eauto.
Qed.

Lemma Vfloat_exists (P: _ -> Prop):
  (exists i, P (Vfloat i)) ->
  exists v, P v.
Proof.
  destruct 1; eauto.
Qed.

Lemma eval_expr_exists_filter_float ge le te m e (P: _ -> Prop):
  (exists v, eval_expr ge le (Maps.PTree.filter1 (fun v =>
                                                   match v with
                                                     | Vsingle _ => true
                                                     | Vfloat _ => true
                                                     | _ => false
                                                   end) te) m e v /\ P v) ->
  exists v, eval_expr ge le te m e v /\ P v.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  eapply eval_expr_impl; try eassumption.
  intros.
  rewrite Maps.PTree.gfilter1 in H0.
  destruct (Maps.PTree.get i te); try discriminate.
  destruct v0; auto; discriminate.
Qed.


Lemma step_exists_assign ge f a1 a2 k e le m (P: _ -> Prop):
  (
    exists loc ofs,
      eval_lvalue ge e le m a1 loc ofs /\
      exists v2,
        eval_expr ge e le m a2 v2 /\
        exists v,
          Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v /\
          exists m',
            assign_loc ge (typeof a1) m loc ofs v m' /\
            P (State f Sskip k e le m')
  ) ->
  exists s,
    step2 ge (State f (Sassign a1 a2) k e le m)
          Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma eval_lvalue_exists_Ederef (ge: genv) le te m e ty (P: _ -> _ -> Prop):
  (
    exists v,
      eval_expr ge le te m e v /\
      exists l o,
        v = Vptr l o /\
        P l o
  ) ->
  exists l o,
    eval_lvalue ge le te m (Ederef e ty) l o /\
    P l o
.
Proof.
  intros.
  break H.
  subst.
  esplit.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma step_exists_skip_call (ge : genv)
      (f : function) (k : cont) (e : env) (le : temp_env)
      (m : Memory.Mem.mem) (P: _ -> Prop):
  (
    is_call_cont k /\
    exists m',
      Memory.Mem.free_list m (blocks_of_env ge e) = Some m' /\
      P (Returnstate Vundef k m')
  ) ->
  exists s,
    step2 ge (State f Sskip k e le m) Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  eapply step_skip_call; eauto.
Qed.

Lemma star_exists_refl ge s (P: _ -> Prop):
  P s ->
  exists s',
    Smallstep.star step2 ge s Events.E0 s' /\
    P s'
.
Proof.
  intros.
  eauto using Smallstep.star_refl.
Qed.

Lemma eval_exists_Ederef (ge: genv) le te m e ty (P: _ -> Prop):
  (
    exists chunk,
      Ctypes.access_mode ty = Ctypes.By_value chunk /\      
      exists l o,
        eval_lvalue ge le te m (Ederef e ty) l o /\
        exists v,
          Memory.Mem.loadv chunk m (Vptr l o) = Some v /\
          P v
  ) ->
  exists v,
    eval_expr ge le te m (Ederef e ty) v /\
    P v
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma step_exists_return_none (ge : genv)
      (f : function) (k : cont) (e : env) (le : temp_env)
      (m : Memory.Mem.mem) (P: _ -> Prop):
  (
    exists m',
      Memory.Mem.free_list m (blocks_of_env ge e) = Some m' /\
      P (Returnstate Vundef (call_cont k) m')
  ) ->
  exists s,
    step2 ge (State f (Sreturn None) k e le m) Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  eapply step_return_0; eauto.
Qed.

Lemma step_exists_return_none_2 (ge : genv)
      (f : function) (k : cont) (e : env) (le : temp_env)
      (m : Memory.Mem.mem) (P: _ -> Prop):
  (
    forall k',
      k' = call_cont k ->
    exists m',
      Memory.Mem.free_list m (blocks_of_env ge e) = Some m' /\
      P (Returnstate Vundef k' m')
  ) ->
  exists s,
    step2 ge (State f (Sreturn None) k e le m) Events.E0 s /\
    P s
.
Proof.
  intros.
  eapply step_exists_return_none; eauto.
Qed.

Lemma exists_double_elim
     : forall (P : state -> Prop) (Q : Floats.float -> Prop)
         (m : Memory.Mem.mem),
       (exists v : Floats.float, P (Returnstate (Vfloat v) Kstop m) /\ Q v) ->
       exists s : state,
         P s /\
         (exists v : Floats.float,
            s = Returnstate (Vfloat v) Kstop m /\ Q v)
.
Proof.
  intros.
  break H.
  eauto.
Qed.

Lemma exists_void_elim
     : forall (P : state -> Prop) (Q : _ -> Prop),
       (exists m_, P (Returnstate Vundef Kstop m_) /\ Q m_) ->
       exists s : state,
         P s /\
         (exists m_,
            s = Returnstate Vundef Kstop m_ /\ Q m_)
.
Proof.
  intros.
  break H.
  eauto.
Qed.

Require compcert.exportclight.Clightdefs.

Lemma eval_exists_Ole_double ge le te m u1 u2 (P: _ -> Prop):
  (exists f1,
     Maps.PTree.get u1 te = Some (Vfloat f1) /\
     exists f2,
       Maps.PTree.get u2 te = Some (Vfloat f2) /\
       P (Floats.Float.cmp Integers.Cle f1 f2)
  ) ->
  exists v : val,
    eval_expr ge le te m
              (Ebinop Cop.Ole
                      (Etempvar u1 Clightdefs.tdouble)
                      (Etempvar u2 Clightdefs.tdouble)
                      Clightdefs.tint) v /\
    exists b1 : bool,
      Cop.bool_val v Clightdefs.tint m = Some b1 /\
      P b1
.
Proof.
  intros.
  break H.
  esplit.
  split.
  {
    econstructor.
    {
      econstructor.
      eassumption.
    }
    {
      econstructor.
      eassumption.
    }
    reflexivity.
  }
  destruct (Floats.Float.cmp Integers.Cle x x0); simpl;
  unfold Cop.bool_val;
  simpl;
  vm_compute;
  eauto.
Qed. 

Lemma step_ifthenelse ge f a s1 s2 k e le m (P: _ -> Prop):
  (exists v1,
    eval_expr ge e le m a v1 /\
    exists b,
      Cop.bool_val v1 (typeof a) m = Some b /\
      P (State f (if b then s1 else s2) k e le m)) ->
  exists s,
    step2 ge (State f (Sifthenelse a s1 s2) k e le m)
          Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  exact (step_ifthenelse _ _ _ _ _ _ _ _ _ _ _ _ K_ K_0).
Qed.

Lemma step_ifthenelse2 ge f e1 e2 s1 s2 k e le m (P: _ -> Prop):
  (exists v1,
     eval_expr ge e le m e1 v1 /\
     exists b1,
       Cop.bool_val v1 (typeof e1) m = Some b1 /\
       exists v2,
         eval_expr ge e le m e2 v2 /\
         exists b2,
           Cop.bool_val v2 (typeof e2) m = Some b2 /\
           exists s,
             Smallstep.star step2 ge
                  (State f (if andb b1 b2 then s1 else s2) k e le m)
                  Events.E0 s
             /\
             P s
  ) ->
  exists s,
    Smallstep.star step2 ge (State f (Sifthenelse e1 (Sifthenelse e2 s1 s2) s2) k e le m) Events.E0 s /\
    P s
.
Proof.
  intros.
  break H.
  apply star_exists_step.
  apply step_ifthenelse.
  solve_trivial.
  destruct x0; eauto.
  simpl in K_3.
  apply star_exists_step.
  apply step_ifthenelse.
  solve_trivial.
  assumption.
Qed.


Lemma eval_expr_exists_filter_domain ge le te m e (P: _ -> Prop):
  (exists v, eval_expr ge le (PTree_filter2 (fun i _ =>
                                                    VSET.mem i (cvars e))
                                                 te) m e v /\ P v) ->
  exists v, eval_expr ge le te m e v /\ P v.
Proof.
  intros.
  break H.
  esplit.
  split; eauto.
  eapply eval_expr_impl; try eassumption.
  intros.
  rewrite PTree_gfilter2 in H0.
  destruct (Maps.PTree.get i te); try discriminate.
  destruct (VSET.mem i (cvars e)); congruence.
Qed.

Lemma sem_cast_double_int_exists bin (P: _ -> Prop):
  (
    exists v,
      Floats.Float.to_int bin = Some v /\
      P (Vint v)
  ) ->
  exists v, forall m,
    Cop.sem_cast (Vfloat bin) tdouble tint m = Some v /\ P v.
Proof.
  intros (v & Hv & HP).
  cbn.
  rewrite Hv.
  eauto.
Qed.

Lemma Rle_dec_to_bool a b:
  sumbool_to_bool (Rle_dec a b) = Raux.Rle_bool a b.
Proof.
  symmetry.
  destruct (Rle_dec a b); simpl; auto using Raux.Rle_bool_true.
  apply Raux.Rle_bool_false.
  lra.
Qed.

Lemma Rlt_dec_to_bool a b:
  sumbool_to_bool (Rlt_dec a b) = Raux.Rlt_bool a b.
Proof.
  symmetry.
  destruct (Rlt_dec a b); simpl; auto using Raux.Rlt_bool_true.
  apply Raux.Rlt_bool_false.
  lra.
Qed.

Lemma eval_exists_Econst_int c ge le te m ty (P: _ -> Prop):
  P (Vint c) ->
  exists v,
    eval_expr ge le te m (Econst_int c ty) v /\ P v.
Proof.
  intros.
  esplit.
  split; eauto.
  constructor.
Qed.

Lemma  eval_exists_Ebinop ge le te m b e1 e2 ty (P: _ -> Prop):
    (exists v1,
       eval_expr ge le te m e1 v1 /\
       exists v2,
         eval_expr ge le te m e2 v2 /\
         exists v,
           sem_binary_operation ge b v1 (typeof e1) v2 (typeof e2) m = Some v /\
           P v) ->
    (exists v,
       eval_expr ge le te m
                 (Ebinop b e1 e2 ty) v /\
       P v).
Proof.
  intros K.
  break K.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma bool_val_int_of_bool b m:
  bool_val (Val.of_bool b) tint m = Some b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma eval_exists_Ecast ge e le m (a : expr) (ty : type) (P: _ -> Prop):
  (exists v1,
     eval_expr ge e le m a v1 /\
     exists v,
       Cop.sem_cast v1 (typeof a) ty m = Some v /\
       P v) ->
  exists v,
    eval_expr ge e le m (Ecast a ty) v /\
    P v.
Proof.
  intro K.
  break K.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma subst_expr_exists e1 e2 i e ge le te m (P: _ -> Prop):
  (Maps.PTree.get i te = None /\
   subst_expr i e1 e2 = Some e /\
   exists v1,
     eval_expr ge le te m e1 v1 /\
     exists v,
       eval_expr ge le (Maps.PTree.set i v1 te) m e2 v /\
       P v) ->
  exists v,
    eval_expr ge le te m e v /\
    P v.
Proof.
  intro K.
  break K.
  destruct (subst_expr_correct _ _ K_ _ _ _ _ _ K_1).
  specialize (H _ _ K_2 _ K_0).
  eauto.
Qed.

Ltac pattern_expr i ep e :=
  match e with
    | ep => constr:(Etempvar i (typeof ep))
    | Ederef ?e1 ?ty =>
      let e2 := pattern_expr i ep e1 in
      constr:(Ederef e2 ty)
    | Eaddrof ?e1 ?ty =>
      let e2 := pattern_expr i ep e1 in
      constr:(Eaddrof e2 ty)
    | Eunop ?o ?e1 ?ty =>
      let e2 := pattern_expr i ep e1 in
      constr:(Eunop o e2 ty)
    | Ebinop ?o ?e1 ?e2 ?ty =>
      let e3 := pattern_expr i ep e1 in
      let e4 := pattern_expr i ep e2 in
      constr:(Ebinop o e3 e4 ty)
    | Ecast ?e1 ?ty =>
      let e2 := pattern_expr i ep e1 in
      constr:(Ecast e2 ty)
    | Efield ?e1 ?f ?ty =>
      let e2 := pattern_expr i ep e1 in
      constr:(Efield e2 f ty)
    | _ => constr:(e)
  end. 

Fixpoint typelist_of_list_type (l: list Ctypes.type): typelist :=
  match l with
    | nil => Ctypes.Tnil
    | cons a q => Ctypes.Tcons a (typelist_of_list_type q)
  end.

Import AST.

Fixpoint alloc_variables_prop (l: list (ident * type)) (Q: env -> Memory.Mem.mem -> Prop) (ge: genv) (le: env) (m: Memory.Mem.mem) {struct l}: Prop :=
  match l with
    | nil => Q le m
    | (id, ty) :: vars =>
      forall b1 m1,
        Memory.Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
        alloc_variables_prop vars Q ge (Maps.PTree.set id (b1, ty) le) m1
  end.      

Lemma alloc_variables_prop_correct l ge le m (Q: _ -> _ -> Prop):
  alloc_variables_prop l Q ge le m
  ->
  (exists le' m',
     alloc_variables ge le m l le' m' /\
     Q le' m')
.
Proof.
  revert le m.
  induction l; simpl; intros.
  {
    do 2 esplit.
    split; eauto.
    constructor.
  }
  destruct a.
  destruct (Memory.Mem.alloc m 0 (sizeof ge t)) eqn:ALLOC.
  specialize (H _ _ Logic.eq_refl).
  specialize (IHl _ _ H).
  break IHl.
  do 2 esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Definition outcome_result_value_exists (out: outcome) (t: type) m (P: _ -> Prop) :=
  match out, t with
    | Out_normal, Ctypes.Tvoid => P Vundef
    | Out_return None, Ctypes.Tvoid => P Vundef
    | Out_return (Some (v', t')), ty => ty <> Ctypes.Tvoid /\
                                        exists v,
                                          Cop.sem_cast v' t' t m = Some v /\
                                          P v
    | _, _ => False
  end.

Lemma outcome_result_value_exists_correct out t m (P: _ -> Prop):
  outcome_result_value_exists out t m P ->
  exists v,
    outcome_result_value out t m v /\ P v.
Proof.
  destruct out; simpl; try tauto.
  {
    destruct t; try tauto.
    eauto.
  }
  destruct o.
  {
    destruct p.
    destruct 1 as (? & (? & (? & ?))).
    eauto.
  }
  destruct t; try tauto.
  eauto.
Qed.

Lemma eval_funcall_exists_internal ge m f vargs (P: _ -> _ -> Prop):
  (
    Coqlib.proj_sumbool
      (Coqlib.list_norepet_dec ident_eq (var_names (fn_vars f))) &&
      (Coqlib.proj_sumbool
         (Coqlib.list_norepet_dec ident_eq (var_names (fn_params f))) &&
         Coqlib.proj_sumbool
         (Coqlib.list_disjoint_dec ident_eq (var_names (fn_params f))
                                   (var_names (fn_temps f)))) = true /\
    alloc_variables_prop
      (fn_vars f) 
      (
        fun le1 m1 =>
          exists te,
            bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)) = Some te /\
            exists te2 m2 out,
              exec_stmt ge le1 te m1 (fn_body f) E0 te2 m2 out
              /\
              exists m3,
                Memory.Mem.free_list m2 (blocks_of_env ge le1) = Some m3 /\
                outcome_result_value_exists out (fn_return f) m2 (P m3)
      ) ge empty_env m
  ) ->
  exists m_ vres,
    eval_funcall ge m (Ctypes.Internal f) vargs E0 m_ vres /\
    P m_ vres
.  
Proof.
  destruct 1 as (H & H0).
  apply Bool.andb_true_iff in H.
  destruct H as (H & H1).
  apply Bool.andb_true_iff in H1.
  destruct H1 as (H1 & H2).
  destruct (Coqlib.list_norepet_dec ident_eq (var_names (fn_vars f))); try discriminate.
  clear H.
  destruct (Coqlib.list_norepet_dec ident_eq (var_names (fn_params f))); try discriminate.
  clear H1.
  destruct (Coqlib.list_disjoint_dec ident_eq (var_names (fn_params f))
            (var_names (fn_temps f))); try discriminate.
  clear H2.
  apply alloc_variables_prop_correct in H0.
  break H0.
  apply outcome_result_value_exists_correct in H0.
  destruct H0 as (? & ? & ?).
  esplit.
  esplit.
  split.
  eapply eval_funcall_internal; eauto.
  auto.
Qed.


Definition out_normal_b (o: outcome): bool :=
  match o with
    | Out_normal => true
    | _ => false
  end.

Definition out_continue_b (o: outcome): bool :=
  match o with
    | Out_continue => true
    | _ => false
  end.

Definition out_return_o (o: outcome): option (option (val * type)) :=
  match o with
    | Out_return o_ => Some o_
    | _ => None
  end.

Lemma out_normal_or_continue_iff out:
  orb (out_normal_b out) (out_continue_b out) = true <-> out_normal_or_continue out.
Proof.
  destruct out; simpl; split; try inversion 1; constructor.
Qed.

Definition out_break_or_return_f out :=
  match out_return_o out with
    | Some _ => out
    | _ => Out_normal
  end.

Lemma out_break_or_return_intro out:
  orb (out_normal_b out) (out_continue_b out) = false ->
  out_break_or_return out (out_break_or_return_f out).
Proof.
  destruct out; simpl; try inversion 1; constructor.
Qed.

Lemma eval_exprlist_impl tenv1 tenv2
      (Htenv: forall i v, Maps.PTree.get i tenv1 = Some v ->
                          Maps.PTree.get i tenv2 = Some v)
      ge env m l lt lv :
  eval_exprlist ge env tenv1 m l lt lv ->
  eval_exprlist ge env tenv2 m l lt lv.
Proof.
  induction 1.
  {
    constructor.
  }
  econstructor; eauto.
  eapply eval_expr_lvalue_impl; eauto.
Qed.

Lemma eval_lvalue_impl ge env m tenv1 tenv2
      (Htenv: forall i v, Maps.PTree.get i tenv1 = Some v ->
                          Maps.PTree.get i tenv2 = Some v)
:
  (forall e b o,
     eval_lvalue ge env tenv1 m e b o ->
     eval_lvalue ge env tenv2 m e b o).
Proof.
  apply eval_expr_lvalue_impl.
  assumption.
Qed.

Lemma out_normal_b_iff out:
  (out_normal_b out = true) <-> (out = Out_normal).
Proof.
  destruct out; simpl; intuition congruence.
Qed.

Lemma exec_Sseq_exists ge e le m st1 st2 (P: _ -> _ -> _ -> Prop):
  (
    exists le1 m1 out1,
      exec_stmt ge e le m st1 E0 le1 m1 out1 /\
      if out_normal_b out1
      then
        exists le2 m2 out2,
          exec_stmt ge e le1 m1 st2 E0 le2 m2 out2 /\
          P le2 m2 out2
      else
        P le1 m1 out1
  ) ->
  exists le2 m2 out,
    exec_stmt ge e le m (Ssequence st1 st2) E0 le2 m2 out /\
    P le2 m2 out.
Proof.
  intros (le1 & m1 & out1 & Hexec1 & TEST).
  destruct (out_normal_b out1) eqn:NORMAL.
  {
    rewrite out_normal_b_iff in NORMAL.
    subst.
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

Lemma exec_Sset_exists ge e le m id a (P: _ -> _ -> _ -> Prop):
  (
    exists v,
      eval_expr ge e le m a v /\
      P (Maps.PTree.set id v le) m Out_normal
  ) ->
  exists le2 m2 out,
    exec_stmt ge e le m (Sset id a) E0 le2 m2 out /\
    P le2 m2 out.
Proof.
  destruct 1 as (? & ? & ?).
  do 3 esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma exec_Sassign_exists
     : forall (ge : genv) (e : env) (le : temp_env) 
              (m : Memory.Mem.mem) (a1 a2 : expr)
              (P: _ -> _ -> _ -> Prop),
         (exists 
             (loc : block) (ofs : ptrofs),
             eval_lvalue ge e le m a1 loc ofs /\
             exists v2,
               eval_expr ge e le m a2 v2 /\
               exists (v : val),
                 Cop.sem_cast v2 (typeof a2) (typeof a1) m = Some v /\
                 exists (m' : Memory.Mem.mem),
                   assign_loc ge (typeof a1) m loc ofs v m' /\
                   P le m' Out_normal
         ) ->
              exists le2 m2 out2,
                exec_stmt ge e le m (Sassign a1 a2) E0 le2 m2 out2 /\
                P le2 m2 out2.
Proof.
  intros ge e le m a1 a2 P H.
  break H.
  do 3 esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma eval_exists_Eunop
     : forall (ge : genv) (le : env) (te : temp_env) 
         (m : Memory.Mem.mem) (u : Cop.unary_operation) 
         (e1 : expr) (ty : type) (P : val -> Prop),
       (exists v1 : val,
          eval_expr ge le te m e1 v1 /\
          (exists v : val,
             sem_unary_operation u v1 (typeof e1) m =
                Some v /\ P v)) ->
       exists v : val, eval_expr ge le te m (Eunop u e1 ty) v /\ P v
.
Proof.
  intros ge le te m u e1 ty P H.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma star_call_eval_funcall_exists ge m f args (P: _ -> Prop):
  (
    exists m2 res,
      eval_funcall ge m f args E0 m2 res
      /\
      P (Returnstate res Kstop m2)
  ) ->
  exists s2,
    star step2
         ge
         (Callstate f args Kstop m)
         E0
         s2 /\
    P s2.
Proof.
  intros (m2 & res & HF & HP).
  rewrite eval_funcall_steps_equiv in HF.
  eauto.
Qed.

Lemma eval_funcall_exists_star_call ge m f args (P: _ -> _ -> Prop):
  (exists s2,
    star step2
         ge
         (Callstate f args Kstop m)
         E0
         s2 /\
    exists res m2,
      s2 = Returnstate res Kstop m2 /\
      P res m2) ->
  exists m2 res,
    eval_funcall ge m f args E0 m2 res
    /\
    P res m2.
Proof.
  intros H.
  break H.
  do 2 esplit.
  split; eauto.
  rewrite eval_funcall_steps_equiv.
  congruence.
Qed.

Lemma eval_lvalue_exists_Evar (ge: genv) le te m id ty (P: _ -> _ -> Prop):
  (
    forall u,
      u = Maps.PTree.get id le ->
      match u with
        | Some (l, ty_) =>
          ty_ = ty /\
          P l Integers.Ptrofs.zero
        | None =>
          exists l,
            Globalenvs.Genv.find_symbol ge id = Some l /\
            P l Integers.Ptrofs.zero
      end
  ) ->
  exists l o,
    eval_lvalue ge le te m (Evar id ty) l o /\
    P l o
.
Proof.
  intros H.
  specialize (H _ (eq_refl _)).
  destruct (Maps.PTree.get id le) as [ [ ? ? ] | ] eqn:LOC.
  {
    destruct H.
    subst.
    do 2 esplit.
    split; eauto.
    econstructor.
    assumption.
  }
  break H.
  do 2 esplit.
  split; eauto.
  eapply eval_Evar_global; eauto.
Qed.

Ltac eval_lvalue_exists_Evar :=
  match goal with
      |- exists l o,
           eval_lvalue _ ?le _ _ (Evar ?id _) l o /\ _
      =>
      apply eval_lvalue_exists_Evar;
      let u := fresh "u" in
      let Hu := fresh "Hu" in
      intros u Hu;
        cbn in Hu;
        rewrite Hu;
        clear u Hu;
        solve_trivial
  end.

Lemma eval_exists_Econst_float:
  forall c (ge : genv) (le : env) (te : temp_env)
         (m : Memory.Mem.mem) (ty : type) (P : val -> Prop),
    (forall d, d = c ->
               P (Vfloat d)) ->
    exists v : val, eval_expr ge le te m (Econst_float c ty) v /\ P v.
Proof.
  intros c ge le te m ty P H.
  specialize (H _ (eq_refl _)).
  esplit.
  split; eauto.
  constructor.
Qed.

Ltac eval_exists_Econst_float :=
  apply eval_exists_Econst_float;
  let d := fresh "d" in
  let Hd := fresh "Hd" in
  intros d Hd;
    vm_compute in Hd;
    subst d.

Lemma exec_Sseq_assoc_l2r s1 s2 s3 ge le te m t te_ m_ out:
  exec_stmt ge le te m (Ssequence (Ssequence s1 s2) s3) t te_ m_ out ->
  exec_stmt ge le te m (Ssequence s1 (Ssequence s2 s3)) t te_ m_ out.
Proof.
  inversion_clear 1; subst.
  {
    match goal with
        K: exec_stmt _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
        inversion_clear K; try congruence
    end.
    match goal with
        |- exec_stmt _ _ _ _ _ ?u _ _ _ =>
        match u with
            ((?u1 ** ?u2) ** ?u3) =>
            replace u with (u1 ** (u2 ** u3)) by traceEq
        end
    end.
    econstructor; eauto.
    econstructor; eauto.
  }
  match goal with
      K: exec_stmt _ _ _ _ _ _ _ _ _ |- _ =>
      inversion_clear K
  end.
  {
    econstructor; eauto.
    constructor; auto.
  }
  constructor; auto.
Qed.

Lemma exec_Sseq_assoc_r2l s1 s2 s3 ge le te m t te_ m_ out:
  exec_stmt ge le te m (Ssequence s1 (Ssequence s2 s3)) t te_ m_ out ->
  exec_stmt ge le te m (Ssequence (Ssequence s1 s2) s3) t te_ m_ out.
Proof.
  inversion_clear 1; subst.
  {
    match goal with
        K: exec_stmt _ _ _ _ (Ssequence _ _) _ _ _ _ |- _ =>
        inversion_clear K
    end.
    {      
      match goal with
          |- exec_stmt _ _ _ _ _ ?u _ _ _ =>
          match u with
              (?u1 ** ?u2 ** ?u3) =>
               replace u with ((u1 ** u2) ** u3) by traceEq
          end
      end.
      econstructor; eauto.
      econstructor; eauto.
    }
    constructor; auto.
    econstructor; eauto.
  }
  constructor; auto.
  constructor; auto.
Qed.

Lemma exec_Sseq_context sl1 sl2 sr1 sr2 ge le:
  (forall te m t te_ m_ out,
     exec_stmt ge le te m sl1 t te_ m_ out ->
     exec_stmt ge le te m sl2 t te_ m_ out) ->
  (forall te m t te_ m_ out,
     exec_stmt ge le te m sr1 t te_ m_ out ->
     exec_stmt ge le te m sr2 t te_ m_ out) ->
  forall te m t te_ m_ out,
     exec_stmt ge le te m (Ssequence sl1 sr1) t te_ m_ out ->
     exec_stmt ge le te m (Ssequence sl2 sr2) t te_ m_ out.
Proof.
  intros H H0 te m t te_ m_ out H1.
  inversion H1; subst.
  {
    econstructor; eauto.
  }
  constructor; auto.
Qed.

Inductive stmt_assoc: statement -> statement -> Prop :=
| stmt_assoc_l2r s1 s2 s3:
    stmt_assoc
      (Ssequence (Ssequence s1 s2) s3)
      (Ssequence s1 (Ssequence s2 s3))
| stmt_assoc_r2l s1 s2 s3:
    stmt_assoc
      (Ssequence s1 (Ssequence s2 s3))
      (Ssequence (Ssequence s1 s2) s3)
| stmt_assoc_refl:
    Reflexive stmt_assoc
| stmt_assoc_trans:
    Transitive stmt_assoc
| stmt_assoc_compat:
    Proper (stmt_assoc ==> stmt_assoc ==> stmt_assoc) Ssequence
.
Global Existing Instances stmt_assoc_refl stmt_assoc_trans stmt_assoc_compat.

Global Instance stmt_assoc_sym: Symmetric stmt_assoc.
Proof.
  red.
  induction 1.
  {
    constructor.
  }
  {
    constructor.
  }
  {
    reflexivity.
  }
  {
    eapply stmt_assoc_trans; eauto.
  }
  {
    eapply stmt_assoc_compat; eauto.
  }
Qed.

Lemma exec_stmt_assoc s1 s2:
  stmt_assoc s1 s2 ->
  forall ge le te m t te_ m_ out,
    exec_stmt ge le te m s1 t te_ m_ out ->
    exec_stmt ge le te m s2 t te_ m_ out.
Proof.
  induction 1.
  {
    apply exec_Sseq_assoc_l2r.
  }
  {
    apply exec_Sseq_assoc_r2l.
  }
  {
    tauto.
  }
  {
    firstorder.
  }
  {
    intros ? ? .
    apply exec_Sseq_context; auto.
  }
Qed.

Global Instance exec_stmt_assoc_morph:
  Proper (eq ==> eq ==> eq ==> eq ==> stmt_assoc ==> eq ==> eq ==> eq ==> eq ==> iff) exec_stmt.
Proof.
  do 10 red.
  intros; subst.
  split.
  {
    apply exec_stmt_assoc; auto.
  }
  apply exec_stmt_assoc.
  symmetry.
  assumption.
Qed.

Ltac first_loop s := 
  match s with
    | Sloop _ _ => s
    | Ssequence ?s1 _ =>
      first_loop s1
    | Ssequence _ ?s2 =>
      first_loop s2
    | Sifthenelse _ ?s1 _ =>
      first_loop s1
    | Sifthenelse _ _ ?s2 =>
      first_loop s2
    | Slabel _ ?s =>
      first_loop s
    | Sswitch _ ?ls =>
      first_loop ls
    | LScons _ ?s _ =>
      first_loop s
    | LScons _ _ ?ls =>
      first_loop ls
  end.

Lemma exec_Scall_exists (ge : genv) (e : env) (le : temp_env) 
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
              P (set_opttemp optid vres le) m' Out_normal
  ) ->
  exists le' m' out,
    exec_stmt ge e le m (Scall optid a al) E0 le' m' out /\
    P le' m' out.
Proof.
  intros H.
  break H.
  do 3 esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Definition deref_loc_exists (mo: mode) (m: Memory.Mem.mem) (b: block) (ofs: ptrofs) (P: val -> Prop) :=
  match mo with
    | By_value chunk =>
      exists v,
        Memory.Mem.loadv chunk m (Vptr b ofs) = Some v /\
        P v
    | By_nothing => False
    | _ => P (Vptr b ofs)
  end.

Lemma deref_loc_exists_correct ty m b ofs P:
  deref_loc_exists (access_mode ty) m b ofs P ->
  exists v,
    deref_loc ty m b ofs v /\
    P v.
Proof.
  unfold deref_loc_exists.
  intros H.
  destruct (access_mode ty) eqn:ACCESS;
    break H;
    (try contradiction);
    esplit;
    split;
    eauto.
  {
    eapply deref_loc_value; eauto.
  }
  {
    apply deref_loc_reference; auto.
  }
  {
    apply deref_loc_copy; auto.
  }
Qed.

Lemma eval_Elvalue_exists ge e le m (a : expr) (P: _ -> Prop):
  (
    forall am,
      am = access_mode (typeof a) ->
      exists loc ofs,
        eval_lvalue ge e le m a loc ofs /\
        deref_loc_exists am m loc ofs P
  ) ->
  exists v,
    eval_expr ge e le m a v /\
    P v
.
Proof.
  intros H.
  specialize (H _ (eq_refl _)).
  break H.
  apply deref_loc_exists_correct in H.
  break H.
  esplit.
  split; eauto.
  eapply eval_Elvalue; eauto.
Qed.

Ltac eval_Elvalue_exists :=
  apply eval_Elvalue_exists;
  unfold deref_loc_exists at 1;
  let am := fresh "am" in
  let Ham := fresh "Ham" in
  intros am Ham;
    vm_compute in Ham;
    subst am
.    

Lemma eval_exists_Eaddrof (ge : genv) (e : env) (le : temp_env) (m : Memory.Mem.mem)
     (a : expr) (ty : type) (P: _ -> Prop):
  (exists (loc : block) (ofs : ptrofs),
     eval_lvalue ge e le m a loc ofs /\
     P (Vptr loc ofs)) ->
  exists v,
    eval_expr ge e le m (Eaddrof a ty) v /\
    P v.
Proof.
  intros H.
  break H.
  esplit.
  split; eauto.
  econstructor; eauto.
Qed.

Lemma exec_stmt_assoc_exists s1 s2 (P: _ -> _ -> _ -> Prop):
  forall ge le te m t,
    (
      exists  te_ m_ out,
        exec_stmt ge le te m s1 t te_ m_ out /\
        P  te_ m_ out) ->
    stmt_assoc s2 s1 ->
    exists te_ m_ out,
      exec_stmt ge le te m s2 t te_ m_ out /\
      P te_ m_ out.
Proof.
  intros ge le te m t H H0.
  break H.
  symmetry in H0.
  eauto 6 using exec_stmt_assoc.
Qed.
