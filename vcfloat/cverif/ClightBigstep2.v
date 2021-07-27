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

 A big-step semantics for the Clight language, based on Clight.step2
 (non-addressed function arguments passed in temporary variables)
 and with "escape to small-step" at internal function calls.

 This file is a modified version of ClightBigstep.v in CompCert, which
 is Copyright (C) 2004-2015 INRIA. All rights reserved.

 Original Author: Xavier Leroy <xavier.leroy@inria.fr>

 The original ClightBigstep.v is dual-licensed under GNU
 General Public License version 2 or (at your option) any
 later version, or (at your option) INRIA non-commercial
 license. See ACKS for more information.
*)

From compcert.lib Require Import Coqlib Maps Integers Floats.
From compcert.common Require Import Values AST Memory Events Globalenvs Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight.

Section BIGSTEP.

Variable ge: genv.

(** ** Big-step semantics for terminating statements and functions *)

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

Inductive outcome: Type :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_continue: outcome              (**r terminated by [continue] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

Inductive out_normal_or_continue : outcome -> Prop :=
  | Out_normal_or_continue_N: out_normal_or_continue Out_normal
  | Out_normal_or_continue_C: out_normal_or_continue Out_continue.

Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

Definition outcome_switch (out: outcome) : outcome :=
  match out with
  | Out_break => Out_normal
  | o => o
  end.

Definition outcome_result_value (out: outcome) (t: type) m (v: val) : Prop :=
  match out, t with
  | Out_normal, Tvoid => v = Vundef
  | Out_return None, Tvoid => v = Vundef
  | Out_return (Some (v',t')), ty => ty <> Tvoid /\ sem_cast v' t' t m = Some v
  | _, _ => False
  end. 

(** [exec_stmt ge e m1 s t m2 out] describes the execution of 
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

Inductive exec_stmt: env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e le m,
      exec_stmt e le m Sskip
               E0 le m Out_normal
  | exec_Sassign:   forall e le m a1 a2 loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      exec_stmt e le m (Sassign a1 a2)
               E0 le m' Out_normal
  | exec_Sset:     forall e le m id a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sset id a)
               E0 (PTree.set id v le) m Out_normal 
  | exec_Scall:   forall e le m optid a al tyargs tyres cconv vf vargs f t m' vres,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      eval_funcall m f vargs t m' vres ->
      exec_stmt e le m (Scall optid a al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sbuiltin:   forall e le m optid ef al tyargs vargs t m' vres,
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      exec_stmt e le m (Sbuiltin optid ef tyargs al)
                t (set_opttemp optid vres le) m' Out_normal
  | exec_Sseq_1:   forall e le m s1 s2 t1 le1 m1 t2 le2 m2 out,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out ->
      exec_stmt e le m (Ssequence s1 s2)
                (t1 ** t2) le2 m2 out
  | exec_Sseq_2:   forall e le m s1 s2 t1 le1 m1 out,
      exec_stmt e le m s1 t1 le1 m1 out ->
      out <> Out_normal ->
      exec_stmt e le m (Ssequence s1 s2)
                t1 le1 m1 out
  | exec_Sifthenelse: forall e le m a s1 s2 v1 b t le' m' out,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      exec_stmt e le m (if b then s1 else s2) t le' m' out ->
      exec_stmt e le m (Sifthenelse a s1 s2)
                t le' m' out
  | exec_Sreturn_none:   forall e le m,
      exec_stmt e le m (Sreturn None)
               E0 le m (Out_return None)
  | exec_Sreturn_some: forall e le m a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sreturn (Some a))
                E0 le m (Out_return (Some (v, typeof a)))
  | exec_Sbreak:   forall e le m,
      exec_stmt e le m Sbreak
               E0 le m Out_break
  | exec_Scontinue:   forall e le m,
      exec_stmt e le m Scontinue
               E0 le m Out_continue
  | exec_Sloop_stop1: forall e le m s1 s2 t le' m' out' out,
      exec_stmt e le m s1 t le' m' out' ->
      out_break_or_return out' out ->
      exec_stmt e le m (Sloop s1 s2)
                t le' m' out
  | exec_Sloop_stop2: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt e le m (Sloop s1 s2)
                (t1**t2) le2 m2 out
  | exec_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 Out_normal ->
      exec_stmt e le2 m2 (Sloop s1 s2) t3 le3 m3 out ->
      exec_stmt e le m (Sloop s1 s2)
                (t1**t2**t3) le3 m3 out
  | exec_Sswitch:   forall e le m a t v n sl le1 m1 out,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      exec_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t le1 m1 out ->
      exec_stmt e le m (Sswitch a sl)
                t le1 m1 (outcome_switch out)
  (** Tahina 2015-09-21: missing trivial label case *)
  | exec_Slabel:
      forall lbl e le m st t le1 m1 out,
        exec_stmt e le m st t le1 m1 out ->
        exec_stmt e le m (Slabel lbl st) t le1 m1 out

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall le m f vargs t e m2 le3 m3 out vres m4,
      (** Tahina 2015-09-21: changed to step2 *)
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variables ge empty_env m f.(fn_vars) e m2 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      exec_stmt e le m2 f.(fn_body) t le3 m3 out ->
      outcome_result_value out f.(fn_return) m3 vres ->
      Mem.free_list m3 (blocks_of_env ge e) = Some m4 ->
      eval_funcall m (Internal f) vargs t m4 vres
  | eval_funcall_external: forall m ef targs tres cconv vargs t vres m',
      external_call ef ge vargs m t vres m' ->
      eval_funcall m (External ef targs tres cconv) vargs t m' vres
(** Tahina 2015-09-21: Function invocation does not need to necessarily
    follow the big-step rules. (In particular, functions may contain gotos) *)
  | eval_funcall_default:
      forall m fd args t m' res,
        star step2 ge (Callstate fd args Kstop m) t (Returnstate res Kstop m') ->
        eval_funcall m fd args t m' res
.

Scheme exec_stmt_ind2 := Minimality for exec_stmt Sort Prop
  with eval_funcall_ind2 := Minimality for eval_funcall Sort Prop.
Combined Scheme exec_stmt_funcall_ind from exec_stmt_ind2, eval_funcall_ind2.

(** ** Big-step semantics for diverging statements and functions *)

(** Coinductive semantics for divergence.
  [execinf_stmt ge e m s t] holds if the execution of statement [s]
  diverges, i.e. loops infinitely.  [t] is the possibly infinite
  trace of observable events performed during the execution. *)

CoInductive execinf_stmt: env -> temp_env -> mem -> statement -> traceinf -> Prop :=
  | execinf_Scall:   forall e le m optid a al vf tyargs tyres cconv vargs f t,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      evalinf_funcall m f vargs t ->
      execinf_stmt e le m (Scall optid a al) t
  | execinf_Sseq_1:   forall e le m s1 s2 t,
      execinf_stmt e le m s1 t ->
      execinf_stmt e le m (Ssequence s1 s2) t
  | execinf_Sseq_2:   forall e le m s1 s2 t1 le1 m1 t2,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      execinf_stmt e le1 m1 s2 t2 ->
      execinf_stmt e le m (Ssequence s1 s2) (t1 *** t2)
  | execinf_Sifthenelse: forall e le m a s1 s2 v1 b t,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      execinf_stmt e le m (if b then s1 else s2) t ->
      execinf_stmt e le m (Sifthenelse a s1 s2) t
  | execinf_Sloop_body1: forall e le m s1 s2 t,
      execinf_stmt e le m s1 t ->
      execinf_stmt e le m (Sloop s1 s2) t
  | execinf_Sloop_body2: forall e le m s1 s2 t1 le1 m1 out1 t2,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e le1 m1 s2 t2 ->
      execinf_stmt e le m (Sloop s1 s2) (t1***t2)
  | execinf_Sloop_loop: forall e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3,
      exec_stmt e le m s1 t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 t2 le2 m2 Out_normal ->
      execinf_stmt e le2 m2 (Sloop s1 s2) t3 ->
      execinf_stmt e le m (Sloop s1 s2) (t1***t2***t3)
  | execinf_Sswitch:   forall e le m a t v n sl,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      execinf_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t ->
      execinf_stmt e le m (Sswitch a sl) t
  (** Tahina 2015-09-21: missing trivial label case *)
  | execinf_Slabel:
      forall lbl e le m st t,
        execinf_stmt e le m st t ->
        execinf_stmt e le m (Slabel lbl st) t

(** [evalinf_funcall ge m fd args t] holds if the invocation of function
    [fd] on arguments [args] diverges, with observable trace [t]. *)

with evalinf_funcall: mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal: forall le m f vargs t e m2,
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names f.(fn_params)) ->
      list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
      alloc_variables ge empty_env m f.(fn_vars) e m2 ->
      bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      execinf_stmt e le m2 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t.

End BIGSTEP.

(** Big-step execution of a whole program.  *)

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro: forall b f m0 m1 t r,
      let ge := globalenv p in 
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      eval_funcall ge m0 f nil t m1 (Vint r) ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
  | bigstep_program_diverges_intro: forall b f m0 t,
      let ge := globalenv p in 
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      evalinf_funcall ge m0 f nil t ->
      bigstep_program_diverges p t.

Definition bigstep_semantics (p: program) :=
  Bigstep_semantics (bigstep_program_terminates p) (bigstep_program_diverges p).

(** * Implication from big-step semantics to transition semantics *)

Section BIGSTEP_TO_TRANSITIONS.

Section WITHGE.

Variable ge: Clight.genv.

Inductive outcome_state_match
       (e: env) (le: temp_env) (m: mem) (f: function) (k: cont): outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match e le m f k Out_normal (State f Sskip k e le m)
  | osm_break:
      outcome_state_match e le m f k Out_break (State f Sbreak k e le m)
  | osm_continue:
      outcome_state_match e le m f k Out_continue (State f Scontinue k e le m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match e le m f k 
        (Out_return None) (State f (Sreturn None) k' e le m)
  | osm_return_some: forall a v k',
      call_cont k' = call_cont k ->
      eval_expr ge e le m a v ->
      outcome_state_match e le m f k
        (Out_return (Some (v,typeof a))) (State f (Sreturn (Some a)) k' e le m).

Lemma is_call_cont_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; contradiction || auto.
Qed.


Fixpoint concat_cont (k1 k2: cont): cont :=
  match k1 with
    | Kstop => k2
    | Kseq s k => Kseq s (concat_cont k k2)
    | Kloop1 s1 s2 k => Kloop1 s1 s2 (concat_cont k k2)
    | Kloop2 s1 s2 k => Kloop2 s1 s2 (concat_cont k k2)
    | Kswitch k => Kswitch (concat_cont k k2)
    | Kcall oi f e te k => Kcall oi f e te (concat_cont k k2)
  end.

Lemma call_cont_is_call_cont k:
  is_call_cont k ->
  call_cont k = k.
Proof.
  induction k; try contradiction; auto.
Qed.

Lemma concat_call_cont k1 k2:
  is_call_cont k2 ->
  call_cont (concat_cont k1 k2) = concat_cont (call_cont k1) k2.
Proof.
  induction k1; simpl; auto using call_cont_is_call_cont.
Qed.

Lemma is_call_cont_concat k1 k2:
  is_call_cont k1 ->
  is_call_cont k2 ->
  is_call_cont (concat_cont k1 k2).
Proof.
  induction k1; simpl; auto.
Qed.

Definition concat_state s k2 :=
  match s with
    | State f st k e le m =>
      State f st (concat_cont k k2) e le m
    | Callstate fd args k m =>
      Callstate fd args (concat_cont k k2) m
    | Returnstate res k m =>
      Returnstate res (concat_cont k k2) m
  end.

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_labeled_statements_ind from statement_ind2, labeled_statements_ind2.

Lemma find_label_find_label_ls_concat k2 lbl:
(forall bo k,
   find_label lbl bo (concat_cont k k2) =
   match find_label lbl bo k with
     | Some (s', k') => Some (s', concat_cont k' k2)
     | None => None
   end) /\
(forall bol k,
   find_label_ls lbl bol (concat_cont k k2) =
   match find_label_ls lbl bol k with
     | Some (s', k') => Some (s', concat_cont k' k2)
     | None => None
   end).
Proof.
  apply statement_labeled_statements_ind; simpl; try congruence.
  * intros.
    specialize (H (Kseq s0 k)).
    simpl in H.
    rewrite H.
    destruct (find_label lbl s (Kseq s0 k)); auto.
    destruct p; auto.
  * intros.
    rewrite H.
    destruct (find_label lbl s k); auto.
    destruct p; auto.
  * intros.
    specialize (H (Kloop1 s s0 k)).
    simpl in H.
    rewrite H.
    destruct (find_label lbl s (Kloop1 s s0 k)).
    + destruct p; auto.
    + specialize (H0 (Kloop2 s s0 k)).
      auto.
  * intros.
    specialize (H (Kswitch k)).
    auto.
  * intros.
    rewrite H.
    destruct (ident_eq lbl l); auto.
  * intros.
    specialize (H (Kseq (seq_of_labeled_statement l) k)).
    simpl in H.
    rewrite H.
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) k)); auto.
    destruct p; auto.
Qed.

Lemma find_label_concat k2 lbl:
(forall bo k,
   find_label lbl bo (concat_cont k k2) =
   match find_label lbl bo k with
     | Some (s', k') => Some (s', concat_cont k' k2)
     | None => None
   end)
.
Proof.
  apply find_label_find_label_ls_concat.
Qed.

Theorem step2_concat_cont:
  forall ge s t s1 k2,
    Clight.step2 ge s t s1 ->
    is_call_cont k2 ->
    Clight.step2 ge (concat_state s k2) t (concat_state s1 k2)
.
Proof.
  inversion 1; subst; simpl; try (econstructor; eauto; fail).
  * intros.
    rewrite <- concat_call_cont by assumption.
    constructor; auto.
  * intros.
    rewrite <- concat_call_cont by assumption.
    econstructor; eauto.
  * intros.
    econstructor; eauto.
    apply is_call_cont_concat; auto.
  * intros.
    econstructor; eauto.
    rewrite concat_call_cont by assumption.
    rewrite find_label_concat.
    rewrite H0.
    reflexivity.
Qed.

Corollary star2_concat_cont k2:
  is_call_cont k2 ->
  forall ge s t s',
    star Clight.step2 ge s t s' ->
    star Clight.step2 ge (concat_state s k2) t (concat_state s' k2)
.
Proof.
  induction 2.
  * constructor.
  * eapply step2_concat_cont in H0; eauto.
    econstructor; eauto.
Qed.

Lemma exec_stmt_eval_funcall_steps:
  (forall e le m s t le' m' out,
   exec_stmt ge e le m s t le' m' out ->
   forall f k, exists S,
   star step2 ge (State f s k e le m) t S
   /\ outcome_state_match e le' m' f k out S)
/\
  (forall m fd args t m' res,
   eval_funcall ge m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step2 ge (Callstate fd args k m) t (Returnstate res k m')).
Proof.
  apply exec_stmt_funcall_ind; intros.

(* skip *)
  econstructor; split. apply star_refl. constructor.

(* assign *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* set *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* call *)
  econstructor; split.
  eapply star_left. econstructor; eauto. 
  eapply star_right. apply H5. simpl; auto. econstructor. reflexivity. traceEq.
  constructor.

(* builtin *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* sequence 2 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]]. 
  econstructor; split.
  eapply star_left. econstructor.
  eapply star_trans. eexact A1. 
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* sequence 1 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_break => State f Sbreak k e le1 m1
    | Out_continue => State f Scontinue k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. econstructor.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    congruence.
    apply star_one. apply step_break_seq.
    apply star_one. apply step_continue_seq.
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || econstructor; eauto.

(* ifthenelse *)
  destruct (H2 f k) as [S1 [A1 B1]].
  exists S1; split.
  eapply star_left. 2: eexact A1. eapply step_ifthenelse; eauto. traceEq.
  auto.

(* return none *)
  econstructor; split. apply star_refl. constructor. auto.

(* return some *)
  econstructor; split. apply star_refl. econstructor; eauto.

(* break *)
  econstructor; split. apply star_refl. constructor.

(* continue *)
  econstructor; split. apply star_refl. constructor.

(* loop stop 1 *)
  destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out' with
    | Out_break => State f Sskip k e le' m'
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_loop. 
  eapply star_trans. eexact A1.
  unfold S2. inversion H1; subst.
  inv B1. apply star_one. constructor.    
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H1; subst. constructor. inv B1; econstructor; eauto.

(* loop stop 2 *)
  destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  destruct (H3 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
  set (S3 :=
    match out2 with
    | Out_break => State f Sskip k e le2 m2
    | _ => S2
    end).
  exists S3; split.
  eapply star_left. eapply step_loop. 
  eapply star_trans. eexact A1.
  eapply star_left with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
  inv H1; inv B1; constructor; auto.
  eapply star_trans. eexact A2.
  unfold S3. inversion H4; subst.
  inv B2. apply star_one. constructor. apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq. 
  unfold S3. inversion H4; subst. constructor. inv B2; econstructor; eauto.

(* loop loop *)
  destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  destruct (H3 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
  destruct (H5 f k) as [S3 [A3 B3]].
  exists S3; split.
  eapply star_left. eapply step_loop. 
  eapply star_trans. eexact A1.
  eapply star_left with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
  inv H1; inv B1; constructor; auto.
  eapply star_trans. eexact A2.
  eapply star_left with (s2 := State f (Sloop s1 s2) k e le2 m2).
  inversion H4; subst; inv B2; constructor; auto. 
  eexact A3.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq. 
  auto.

(* switch *)
  destruct (H2 f (Kswitch k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k e le1 m1
    | Out_break => State f Sskip k e le1 m1
    | Out_continue => State f Scontinue k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_switch; eauto. 
  eapply star_trans. eexact A1. 
  unfold S2; inv B1. 
    apply star_one. constructor. auto. 
    apply star_one. constructor. auto. 
    apply star_one. constructor. 
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2. inv B1; simpl; econstructor; eauto.
  (** Tahina 2015-09-21: missing trivial label case *)
(* label *)
  specialize (H0 f k).
  destruct H0 as (? & ? & ?).
  esplit.
  split; eauto.
  eright.
  econstructor; eauto.
  eassumption.
  traceEq.

(* call internal *)
  destruct (H5 f k) as [S1 [A1 B1]].
  eapply star_left. eapply step_internal_function; eauto. econstructor; eauto.
  eapply star_right. eexact A1. 
   inv B1; simpl in H6; try contradiction.
  (* Out_normal *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H9. subst vres. apply step_skip_call; auto.
  (* Out_return None *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H10. subst vres.
  rewrite <- (is_call_cont_call_cont k H8). rewrite <- H9.
  apply step_return_0; auto.
  (* Out_return Some *)
  destruct H6.
  rewrite <- (is_call_cont_call_cont k H8). rewrite <- H9.
  eapply step_return_1; eauto.
  reflexivity. traceEq.

(* call external *)
  apply star_one. apply step_external_function; auto. 

(* call default *)
  exact (star2_concat_cont _ H0 _ _ _ _ H).
Qed.

Lemma exec_stmt_steps:
   forall e le m s t le' m' out,
   exec_stmt ge e le m s t le' m' out ->
   forall f k, exists S,
   star step2 ge (State f s k e le m) t S
   /\ outcome_state_match e le' m' f k out S.
Proof (proj1 exec_stmt_eval_funcall_steps).

Lemma eval_funcall_steps:
   forall m fd args t m' res,
   eval_funcall ge m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step2 ge (Callstate fd args k m) t (Returnstate res k m').
Proof (proj2 exec_stmt_eval_funcall_steps).

Lemma eval_funcall_steps_equiv:
   forall m fd args t m' res,
   eval_funcall ge m fd args t m' res <->
   star step2 ge (Callstate fd args Kstop m) t (Returnstate res Kstop m').
Proof.
  split.
  {
    intro.
    apply eval_funcall_steps; simpl; auto.
  }
  constructor.
  assumption.
Qed.

Definition order (x y: unit) := False.

Lemma evalinf_funcall_forever:
  forall m fd args T k,
  evalinf_funcall ge m fd args T ->
  forever_N step2 order ge tt (Callstate fd args k m) T.
Proof.
  cofix CIH_FUN.
  assert (forall e le m s T f k,
          execinf_stmt ge e le m s T ->
          forever_N step2 order ge tt (State f s k e le m) T).
  cofix CIH_STMT.
  intros. inv H.

(* call  *)
  eapply forever_N_plus.
  apply plus_one. eapply step_call; eauto. 
  eapply CIH_FUN. eauto. traceEq.

(* seq 1 *)
  eapply forever_N_plus.
  apply plus_one. econstructor.
  apply CIH_STMT; eauto. traceEq.
(* seq 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kseq s2 k)) as [S1 [A1 B1]].
  inv B1.
  eapply forever_N_plus.
  eapply plus_left. constructor. eapply star_trans. eexact A1. 
  apply star_one. constructor. reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.

(* ifthenelse *)
  eapply forever_N_plus.
  apply plus_one. eapply step_ifthenelse with (b := b); eauto. 
  apply CIH_STMT; eauto. traceEq.

(* loop body 1 *)
  eapply forever_N_plus.
  eapply plus_one. constructor. 
  apply CIH_STMT; eauto. traceEq.
(* loop body 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  eapply forever_N_plus with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
  eapply plus_left. constructor.
  eapply star_right. eexact A1.
  inv H1; inv B1; constructor; auto. 
  reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.
(* loop loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H2 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
  eapply forever_N_plus with (s2 := State f (Sloop s1 s2) k e le2 m2).
  eapply plus_left. constructor.
  eapply star_trans. eexact A1.
  eapply star_left. inv H1; inv B1; constructor; auto.
  eapply star_right. eexact A2.
  inv B2. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.

(* switch *)
  eapply forever_N_plus.
  eapply plus_one. eapply step_switch; eauto.
  apply CIH_STMT; eauto.
  traceEq.

  (** Tahina 2015-09-21: missing trivial label case *)
(* label *)
  eapply forever_N_plus.
  apply plus_one. constructor.
  eapply CIH_STMT; eauto.
  traceEq. 

(* call internal *)
  intros. inv H0.
  eapply forever_N_plus.
  eapply plus_one. econstructor; eauto. econstructor; eauto.
  apply H; eauto.
  traceEq.
Qed.

End WITHGE.

Variable prog: program.
Let ge : genv := globalenv prog.

Theorem bigstep_semantics_sound:
  bigstep_sound (bigstep_semantics prog) (semantics2 prog).
Proof.
  constructor; simpl; intros.
(* termination *)
  inv H. econstructor; econstructor.
  split. econstructor; eauto.
  split. eapply eval_funcall_steps. eauto. red; auto. 
  econstructor.
(* divergence *)
  inv H. econstructor.
  split. econstructor; eauto.
  eapply forever_N_forever with (order := order).
  red; intros. constructor; intros. red in H. elim H.
  eapply evalinf_funcall_forever; eauto. 
Qed.

End BIGSTEP_TO_TRANSITIONS.
