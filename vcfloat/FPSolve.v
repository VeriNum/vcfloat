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

Require Import Lia.
From vcfloat Require Export FPLang FPLangOpt.
Require compcert.common.AST compcert.common.Values.
Require Import compcert.lib.Floats.
Import Binary.

Section WITHNANS.
Context {NANS: Nans}.

Lemma cast_id ty f:
    cast ty ty f = f.
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

Lemma single_le_double:
  type_le Tsingle Tdouble.
Proof.
  constructor; compute; congruence.
Qed.

Global Instance ident_vartype: VarType AST.ident :=
  {
    var_eqb_eq := Pos.eqb_eq
  }.


Inductive val_inject: Values.val -> forall ty, ftype ty -> Prop :=
| val_inject_single f:
    val_inject (Values.Vsingle f) Tsingle f
| val_inject_double f:
    val_inject (Values.Vfloat f) Tdouble f
.

Lemma val_inject_single_inv f1 f2:
  val_inject (Values.Vsingle f1) Tsingle f2 ->
  f1 = f2.
Proof.
  inversion 1; subst.
  revert H2.
  apply Eqdep_dec.inj_pair2_eq_dec; auto.
  apply type_eq_dec.
Qed.

Lemma val_inject_double_inv f1 f2:
  val_inject (Values.Vfloat f1) Tdouble f2 ->
  f1 = f2.
Proof.
  inversion 1; subst.
  revert H2.
  apply Eqdep_dec.inj_pair2_eq_dec; auto.
  apply type_eq_dec.
Qed.

Definition val_injectb v ty (f: ftype ty): bool :=
  match v with
    | Values.Vsingle f' =>
      type_eqb Tsingle ty && binary_float_eqb f' f
    | Values.Vfloat f' =>
      type_eqb Tdouble ty && binary_float_eqb f' f
    | _ => false
  end.

Lemma val_injectb_inject v ty f:
  val_injectb v ty f = true <-> val_inject v ty f.
Proof.
  unfold val_injectb.
  destruct v;
  (try (split; (try congruence); inversion 1; fail));
  rewrite Bool.andb_true_iff.
  {
    destruct (type_eqb Tdouble ty) eqn:EQ.
    {
      rewrite type_eqb_eq in EQ.
      subst.
      rewrite binary_float_eqb_eq.
      split.
      {
        destruct 1; subst.
        constructor.
      }
      intros; eauto using val_inject_double_inv.
    }
    split; try intuition congruence.
    inversion 1; subst.
    apply type_eqb_eq in H3.
    congruence.
  }
  destruct (type_eqb Tsingle ty) eqn:EQ.
  {
    rewrite type_eqb_eq in EQ.
    subst.
    rewrite binary_float_eqb_eq.
    split.
    {
      destruct 1; subst.
      constructor.
    }
    intros; eauto using val_inject_single_inv.
  }
  split; try intuition congruence.
  inversion 1; subst.
  apply type_eqb_eq in H3.
  congruence.  
Qed.

End WITHNANS.

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

Lemma conv_nan_ex:
  { conv_nan: forall ty1 ty2,
                binary_float (fprec ty1) (femax ty1) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
                nan_payload (fprec ty2) (femax ty2)
  |
  conv_nan Tsingle Tdouble = Floats.Float.of_single_nan
  /\
  conv_nan Tdouble Tsingle = Floats.Float.to_single_nan
  }.
Proof.
  eapply exist.
  Unshelve.
  {
    shelve.
  }
  intros ty1 ty2.
  destruct (type_eq_dec ty1 Tsingle).
  {
    subst.
    destruct (type_eq_dec ty2 Tdouble).
    {
      subst.
      exact Floats.Float.of_single_nan.
    }
    auto using any_nan.
  }
  destruct (type_eq_dec ty1 Tdouble).
  {
    subst.
    destruct (type_eq_dec ty2 Tsingle).
    {
      subst.
      exact Floats.Float.to_single_nan.
    }
    intros.
    auto using any_nan.
  }
  intros.
  auto using any_nan.
  Unshelve.
  split; reflexivity.
Defined.

Definition conv_nan := let (c, _) := conv_nan_ex in c.

Lemma single_double_ex (U: _ -> Type):
  (forall ty, U ty) ->
  forall s: U Tsingle,
  forall d: U Tdouble,
    {
      f: forall ty, U ty |
      f Tsingle = s /\
      f Tdouble = d
    }.
Proof.
  intro ref.
  intros.
  esplit.
  Unshelve.
  shelve.
  intro ty.
  destruct (type_eq_dec ty Tsingle).
  {
    subst.
    exact s.
  }
  destruct (type_eq_dec ty Tdouble).
  {
    subst.
    exact d.
  }
  apply ref.
  Unshelve.
  split; reflexivity.
Defined.

Definition single_double (U: _ -> Type)
           (f_: forall ty, U ty)
           (s: U Tsingle)
           (d: U Tdouble)
:
  forall ty, U ty :=
  let (f, _) := single_double_ex U f_ s d in f.

Definition binop_nan :  forall ty, binary_float (fprec ty) (femax ty) ->
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty) :=
  single_double
    (fun ty =>
       binary_float (fprec ty) (femax ty) ->
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty)) 
     (fun ty  _ _ => any_nan ty)
     Floats.Float32.binop_nan
     Floats.Float.binop_nan.

Definition abs_nan :=
  single_double
    (fun ty =>
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty)) 
     (fun ty  _ => any_nan ty)
     Floats.Float32.abs_nan
     Floats.Float.abs_nan.

Definition opp_nan :=
  single_double
    (fun ty =>
       binary_float (fprec ty) (femax ty) ->
       nan_payload (fprec ty) (femax ty)) 
     (fun ty  _ => any_nan ty)
     Floats.Float32.neg_nan
     Floats.Float.neg_nan.

Local Instance nans: Nans :=
  {
    conv_nan := conv_nan;
    plus_nan := binop_nan;
    mult_nan := binop_nan;
    div_nan := binop_nan;
    abs_nan := abs_nan;
    opp_nan := opp_nan;
    sqrt_nan := (fun ty _ => any_nan ty)
  }.

Lemma val_inject_eq_rect_r v ty1 e:
  val_inject v ty1 e ->
  forall ty2 (EQ: ty2 = ty1),
    val_inject v ty2 (eq_rect_r _ e EQ).
Proof.
  intros.
  subst.
  assumption.
Qed.
      
Local Existing Instance nans.

Lemma val_inject_single_inv_r v f:
  val_inject v Tsingle f ->
  v = Values.Vsingle f.
Proof.
  inversion 1; subst.
  apply val_inject_single_inv in H.
  congruence.
Qed.

Lemma val_inject_double_inv_r v f:
  val_inject v Tdouble f ->
  v = Values.Vfloat f.
Proof.
  inversion 1; subst.
  apply val_inject_double_inv in H.
  congruence.
Qed.

(* Tactic for automatic annotations *)

Require Import Reals.
Open Scope R_scope.

Local Existing Instances
      map_nat compcert_map
.

Lemma rndval_with_cond_correct_1:
  forall env : forall x : type, AST.ident -> binary_float (fprec x) (femax x),
       (forall (ty : type) (i : AST.ident),
        is_finite (fprec ty) (femax ty) (env ty i) = true) ->
       forall e : expr,
       expr_valid e = true ->
       forall (si : nat) (shift : Maps.PMap.t (type * rounding_knowledge))
         (r : rexpr) (si2 : nat)
         (s : Maps.PMap.t (type * rounding_knowledge)) 
         (p : list cond),
       rndval_with_cond si shift e = (r, (si2, s), p) ->
       (forall i : cond, List.In i p -> eval_cond1 env s i) ->
       forall errors1 : nat -> R,
       (forall (i : nat) (ty : type) (k : rounding_knowledge),
        mget shift i = (ty, k) -> Rabs (errors1 i) <= error_bound ty k) ->
       forall fv, fval env e = fv ->
       exists errors2 : nat -> R,
         (forall i : nat, (i < si)%nat -> errors2 i = errors1 i) /\
         (forall (i : nat) (ty' : type) (k : rounding_knowledge),
          mget s i = (ty', k) -> Rabs (errors2 i) <= error_bound ty' k) /\
          is_finite (fprec (type_of_expr e)) (femax (type_of_expr e)) fv =
          true /\
          reval r env errors2 =
          B2R (fprec (type_of_expr e)) (femax (type_of_expr e)) fv
.
Proof.
  intros.
  subst.
  eapply rndval_with_cond_correct; eauto.
Qed.

Fixpoint enum_exists' {T: Type} t (P: nat -> T -> Prop) (Q: _ -> Prop) (m n: nat) {struct n}: Prop :=
  match n with
    | O => Q (mempty t)
    | S n' =>
      enum_exists' t P
                   (fun g => exists x, P m x /\  Q (mset g m x))
                   (S m)
                   n'
  end.

Lemma enum_exists'_O {T: Type} (t: T) (P: _ -> _ -> Prop) (Q: _ -> Prop) m:
  enum_exists' t P Q m O = Q (mempty t).
Proof.
  reflexivity.
Qed.

Lemma enum_exists'_S {T: Type} (t: T) (P: _ -> _ -> Prop) (Q: _ -> Prop) m n':
  enum_exists' t P Q m (S n') =
  enum_exists' t P
               (fun g => exists x, P m x /\  Q (mset g m x))
               (S m)
               n'.  
Proof.
  reflexivity.
Qed.

Lemma enum_exists'_correct {T} t (P: nat -> T -> Prop) (Ht: forall i, P i t) N n:
  forall m,
    (m + n = N)%nat ->
    forall  (Q: _ -> Prop),
      (forall g1 g2, 
         (forall i, (m <= i < N)%nat -> mget g2 i = mget g1 i) ->
         (Q g1 -> Q g2)) ->
      (exists g,
         (forall i, P i (mget g i)) /\
         Q g) <-> enum_exists' t P Q m n.
Proof.
  induction n.
  {
    intros; subst.
    rewrite enum_exists'_O.
    split; intros.
    {      
      destruct H.
      destruct H.
      apply (H0 x); auto.
      intros; lia.
    }
    exists (mempty t).
    split; auto.
    all:  intros; rewrite mget_empty;  auto.  (* This line for compatibility with Coq 8.13 and before *)
  }
  intros.
  rewrite enum_exists'_S.
  rewrite <- IHn; clear IHn.
  {
    split.
    {
      destruct 1.
      destruct H1.
      exists x.
      split; auto.
      exists (mget x m).
      split.
      { apply H1. }
      apply (H0 x); auto.
      intros.
      rewrite (mget_set Nat.eq_dec).
      destruct (Nat.eq_dec i m); congruence.
    }
    destruct 1.
    destruct H1.
    destruct H2.
    destruct H2.
    exists (mset x m x0).
    split; auto.
    intros.
    rewrite (mget_set Nat.eq_dec).
    destruct (Nat.eq_dec i m); try congruence.
    auto.
  }
  {
    subst; lia.
  }
  intros.
  destruct H2.
  destruct H2.
  exists x.
  split; auto.
  apply (H0 (mset g1 m x)); auto.
  intros.
  repeat rewrite (mget_set Nat.eq_dec).
  destruct (Nat.eq_dec i m); auto.
  apply H1.
  lia.
Qed.

Definition enum_exists {T} (t: T) (P: nat -> T -> Prop) (N: nat) (Q: (nat -> T) -> Prop) :=
  enum_exists' t P (fun g => Q (mget g)) O N.

Lemma enum_exists_correct {T} t (P: nat -> T -> Prop) (N: nat) (Q: (nat -> T) -> Prop)
      (Ht: forall i, P i t):
  (forall g1 g2, 
     (forall i, (i < N)%nat -> g2 i = g1 i) ->
     (Q g1 -> Q g2)) ->
  (exists g,
     (forall i, P i (g i)) /\
     Q g) <-> enum_exists t P N Q.
Proof.
  unfold enum_exists.
  intros.
  rewrite <- enum_exists'_correct; auto.
  {
    split.
    {
      destruct 1.
      destruct H0.
      generalize (finite_errors_ex t N x).
      destruct 1.
      exists x0.
      split.
      {
        intros.
        rewrite H2.
        destruct (Nat.ltb i N); auto.
      }
      apply (H x); auto.
      intros.
      rewrite H2.
      apply Nat.ltb_lt in H3.
      rewrite H3.
      reflexivity.
    }
    destruct 1.
    destruct H0.
    eauto.
  }
  intros until 1.
  apply H.
  intros.
  apply H0.
  lia.
Qed.

Ltac spec H :=
  lazymatch type of H with ?a -> _ =>
    lazymatch type of a with
    | Prop =>  let H1 := fresh in (assert (H1: a); 
                                        [|specialize (H H1); clear H1]) 
    | _ => fail "The parameter of" H "is not a Prop"
    end
 end.

Definition environ := forall x : type, AST.ident -> binary_float (fprec x) (femax x).

Definition rndval_with_cond_result (env: environ) (e: expr) (r: rexpr) (si2: nat) (s: Maps.PMap.t (type * rounding_knowledge)) :=
       forall fv,
         fval env e = fv ->
         is_finite (fprec (type_of_expr e)) (femax (type_of_expr e)) fv =
         true /\
         enum_exists 0 (fun i r =>
                          let '(ty', k) := mget s i in
                          Rabs r <= error_bound ty' k)
                     si2
                     (fun errors2 =>
                        reval r env errors2 =
                        B2R (fprec (type_of_expr e)) (femax (type_of_expr e)) fv).

Lemma rndval_with_cond_correct:
  forall env : forall x : type, AST.ident -> binary_float (fprec x) (femax x),
       (forall (ty : type) (i : AST.ident),
        is_finite (fprec ty) (femax ty) (env ty i) = true) ->
       forall (e : expr),
       expr_valid e = true ->
       forall
         (r : rexpr) (si2 : nat)
         (s : Maps.PMap.t (type * rounding_knowledge)) 
         (p : list cond),
       rndval_with_cond O (mempty (Tsingle, Normal))  e = (r, (si2, s), p) ->
       list_forall (eval_cond2 env s) p ->
       rndval_with_cond_result env e r si2 s.
Proof.
  intros. hnf. intros.
  specialize (rndval_with_cond_correct_1 env H e H0 _ _ r si2 s p H1).
  intro K.
 spec K.
  {
    apply list_forall_spec.
    apply (list_forall_ext (eval_cond2 env s)); auto.
    apply eval_cond2_correct.
  }
  specialize (K (fun _ => 0)).
  spec K.
  {
    intros.
    rewrite Rabs_R0.
    apply error_bound_nonneg.
  }
  specialize (K _ H3).
  destruct K.
  destruct H4.
  destruct H5.
  destruct H6.
  split; auto.
  rewrite <- enum_exists_correct.
  {
    exists x.
    split; auto.
    intros.
    destruct (mget s i) eqn:EQ.
    eauto.
  }
  {
    intros.
    destruct (mget s i).
    rewrite Rabs_R0.
    apply error_bound_nonneg.
  }
  intros.
  rewrite <- H9.
  apply reval_error_ext.
  intros.
  apply H8.
  eapply lt_le_trans; eauto.
  generalize (rndval_with_cond_left e O (mempty (Tsingle, Normal))).
  rewrite H1.
  simpl.
  intro L.
  symmetry in L.
  eapply rndval_shift_le; eauto.
Qed.

Lemma val_inject_single_left_inv v l:
  val_inject v Tsingle l ->
  v = Values.Vsingle l.
Proof.
  inversion 1; subst.
  apply val_inject_single_inv in H.
  congruence.
Qed.

Lemma val_inject_double_left_inv v l:
  val_inject v Tdouble l ->
  v = Values.Vfloat l.
Proof.
  inversion 1; subst.
  apply val_inject_double_inv in H.
  congruence.
Qed.

Ltac mimetism J :=
  match goal with
      |- _ => let K := fresh in (intro K; specialize (J K))
    | |- _ => intro
  end.

Require Import Interval.Tactic.
Require Import Psatz.

Ltac interval_ :=
  match goal with
    |- ?a <= ?b =>
    interval_intro (a - b);
      lra
    | |- ?a < ?b =>
    let K := fresh in
    interval_intro (a - b);
      lra
  end.

Ltac list_forall_eval_cond2_solve_aux t :=
  match goal with
      |- ?A /\ ?B =>
      (
        tryif
          (
            let K := fresh in
            (assert A as K by (list_forall_eval_cond2_solve_aux t));
            split; [ exact K | clear K; now list_forall_eval_cond2_solve_aux t ]
          )
        then
          idtac
        else
          fail 1
      )
    | |- True => exact I
    | |- ?P => idtac P; intros; t Datatypes.tt; idtac "success"
    | |- _ => idtac "fail"; fail 1
  end. 

Ltac list_forall_eval_cond2_solve t :=
  cbn;
  unfold fprec, type_lub, error_bound;
  cbn;
  now list_forall_eval_cond2_solve_aux t.

Ltac adjust_list_forall_eval_cond2 shift' j :=
  let k := fresh in
  rename j into k;
    match type of k with
      list_forall (eval_cond2 ?env _) ?l =>
      assert (list_forall (eval_cond2 env shift') l) as j by exact k
    end;
    clear k
.

Require Import List.

Ltac rnd_of_binop_with_cond_solve
     t
     env
     si
     shift
     ty
     o
     r1 r2
     cont
  :=
    match o with
    | Rounded2 ?o' _ =>
      let ru := (eval cbn in (RBinop (Rbinop_of_rounded_binop o') r1 r2)) in
      let j := fresh in

      (* Sterbenz *)
      
      let K_sterbenz K0 K1 K2 := 
          match (eval vm_compute in (rounded_binop_eqb o' MINUS)) with
            | true => (
                tryif
                  (assert (list_forall (eval_cond2 env shift)
                                       (
                                         (RBinop Tree.Sub r1 (RBinop Tree.Mul r2 (RAtom (V := AST.ident) (RConst (Defs.Float _ 1 (-1))))), false)
                                           :: (RBinop Tree.Sub (RBinop Tree.Mul r2 (RAtom (V := AST.ident) (RConst (Defs.Float _ 1 1)))) r1, false)
                                           :: nil
                          ))
                    as j
                      by (list_forall_eval_cond2_solve t)
                  )
                then
                  (
                    tryif
                      cont
                      SterbenzMinus
                      ru
                      si
                      shift
                      j
                    then
                      idtac
                    else
                      fail 1
                  )
                else
                  (
                    tryif
                      K0 K1 K2
                    then
                      idtac
                    else
                      fail 1
                  )
              )
            | _ =>
              K0 K1 K2
          end
      in

      (* Plus Zero *)

      let K0 K1 K2 :=
          let test_minus k :=
              match (eval vm_compute in (rounded_binop_eqb o' MINUS)) with
                | true =>
                  (
                    tryif
                      k true
                    then
                      idtac
                    else
                      fail 1
                  )
                | _ =>
                  match (eval vm_compute in (rounded_binop_eqb o' PLUS)) with
                    | true =>
                      (
                        tryif
                          k false
                        then
                          idtac
                        else
                          fail 2
                      )
                    | _ => 
                      (
                        tryif
                          K1 K2
                        then
                          idtac
                        else
                          fail 2
                      )
                  end
              end
          in
          let f minus :=
              let test_zero zero_left zsuccess zfail :=
                  (
                    tryif
                      (assert (list_forall (eval_cond2 env shift)
                                           (rnd_of_plus_zero_cond zero_left r1 r2))                              
                        as j
                          by (list_forall_eval_cond2_solve t)
                      )
                    then
                      zsuccess zero_left
                    else
                      zfail zero_left
                  )
              in
              let zsuccess zero_left :=
                  let ru_ := eval simpl in
                      (
                        if zero_left
                        then
                          if minus then RUnop Tree.Neg r2 else r2
                        else
                          r1
                      )
                  in
                  cont
                    (PlusZero minus zero_left)
                    ru_
                    si
                    shift
                    j
              in
              let zfail_false _ := K1 K2
              in
              let zfail_true _ := test_zero false zsuccess zfail_false
              in
              test_zero true zsuccess zfail_true
          in
          test_minus f

      in

      (* Rounded case *)

      let K1 K2 := (
            tryif
              (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast ty (Some Normal) ru)) as j by (list_forall_eval_cond2_solve t))
            then
              (
                K2 (Some Normal)
              )
            else
              tryif (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast ty (Some Denormal) ru)) as j by (list_forall_eval_cond2_solve t))
            then
              (
                K2 (Some Denormal)
              )
            else
              (
                (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast ty None ru)) as j by exact I);
                K2 (@None rounding_knowledge)
              )
          )
      in

      let K2 k :=
          let rs := (eval cbn in (make_rounding si shift k ty ru)) in
          match rs with
            | (?r, (?si_, ?s)) =>
              adjust_list_forall_eval_cond2 s j;
              let j1 := fresh in
              (assert (
                   list_forall (eval_cond2 env s)
                               (
                                 (if is_div o' then (RUnop Tree.Abs r2, true) :: nil else nil)
                                   ++ no_overflow ty r :: nil
                               )
                 )
                as j1
                  by (list_forall_eval_cond2_solve t));
              let j2 := fresh in
              generalize (list_forall_app _ _ _ j1 j);
                clear j1 j;
                intro j2;
                cont
                  (Rounded2 o' k)
                  r
                  si_
                  s
                  j2
          end
      in

      K_sterbenz K0 K1 K2
    end.

Ltac rnd_of_cast_with_cond_solve
     t
     env
     si
     shift
     tyfrom
     tyto
     ru
     cont
  :=
    match eval vm_compute in (type_leb tyfrom tyto) with
      | true =>
        (
          tryif
            let j := fresh in
            (assert (list_forall (eval_cond2 env shift) nil) as j by exact I);
          cont
            (CastTo tyto None)
            ru
            si
            shift
            j
          then
            idtac
          else
            fail 1
        )

      | _ =>
        let j := fresh in

        let K1 K2 := (

              tryif
                (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast tyto (Some Normal) ru)) as j by (list_forall_eval_cond2_solve t))
              then
                (
                  K2 (Some Normal)
                )
              else
                tryif (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast tyto (Some Denormal) ru)) as j by (list_forall_eval_cond2_solve t))
              then
                (
                  K2 (Some Denormal)
                )
              else
                (
                  (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast tyto None ru)) as j by exact I);
                  K2 (@None rounding_knowledge)
                )
            )
        in

        let K2 k :=
            let rs := (eval cbn in (make_rounding si shift k tyto ru)) in
            match rs with
              | (?r, (?si_, ?s)) =>
                adjust_list_forall_eval_cond2 s j;
                  let j1 := fresh in
                  (assert (
                       list_forall (eval_cond2 env s)
                                   (no_overflow tyto r :: nil)
                     )
                    as j1
                      by (list_forall_eval_cond2_solve t));
                    let j2 := fresh in
                    generalize (list_forall_app _ _ _ j1 j);
                      clear j1 j;
                      intro j2;
                      cont
                        (CastTo tyto k)
                        r
                        si_
                        s
                        j2
            end
        in

        K1 K2
    end.

Ltac rnd_of_unop_with_cond_solve
     t
     env
     si
     shift
     ty
     o
     r1
     cont :=
  match o with

    | Rounded1 ?o' _ =>
      let ru := (eval cbn in (RUnop (Runop_of_rounded_unop o') r1)) in
      let j := fresh in

      let K1 K2 := (
            tryif
              (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast ty (Some Normal) ru)) as j by (list_forall_eval_cond2_solve t))
            then
              (
                K2 (Some Normal)
              )
            else
              (
                tryif (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast ty (Some Denormal) ru)) as j by (list_forall_eval_cond2_solve t))
                then
                  (
                    K2 (Some Denormal)
                  )
                else
                  (
                    (assert (list_forall (eval_cond2 env shift) (rounding_cond_ast ty None ru)) as j by exact I);
                    K2 (@None rounding_knowledge)
                  )
              )
          )
      in

      let K2 k :=
          let rs := (eval cbn in (make_rounding si shift k ty ru)) in
          match rs with
            | (?r, (?si_, ?s)) =>
              adjust_list_forall_eval_cond2 s j;
              let j1 := fresh in
              (assert (
                   list_forall (eval_cond2 env s)
                               (if is_sqrt o' then (r1, false) :: nil else nil)
                 )
                as j1
                  by (list_forall_eval_cond2_solve t));
              let j2 := fresh in
              generalize (list_forall_app _ _ _ j1 j);
                clear j1 j;
                intro j2;
                cont
                  (Rounded1 o' k)
                  r
                  si_
                  s
                  j2
          end
      in

      K1 K2

    | Exact1 ?o' =>
      let ru := (eval cbn in (Runop_of_exact_unop ty o' r1)) in
      let j := fresh in
      (assert (
           list_forall (eval_cond2 env shift)
                       match o' with
                           | Shift _ _ => no_overflow ty ru :: nil
                           | InvShift n _ => (RBinop Tree.Sub (RUnop Tree.Abs r1) (RAtom (V := AST.ident) (RConst (Defs.Float _ 1 (3 - femax ty + Z.pos n - 1)))), false) :: nil
                           | _ => nil
                       end
         )
        as j
             by (list_forall_eval_cond2_solve t)
      );
        cont
          (Exact1 o')
          ru
          si
          shift
          j

    | CastTo ?ty' _ =>
      rnd_of_cast_with_cond_solve 
        t
        env
        si
        shift
        ty
        ty'
        r1
        cont

  end.

Ltac rndval_with_cond_solve
     t
     env
     si
     shift
     e
     k :=
  match e with
    | Const ?ty ?f =>
      let j := fresh in
      generalize (list_forall_nil (eval_cond2 env shift));
        intro j;
        k (Const (V := AST.ident) ty f)
          (RAtom (V := AST.ident) (RConst (B2F f)))
          si
          shift
          j

    | Var ?ty ?i =>
      let j := fresh in
      generalize (list_forall_nil (eval_cond2 env shift));
        intro j;
        k (Var ty i)
          (RAtom (RVar ty i))
          si
          shift
          j

    | Binop ?b ?e1 ?e2 =>

      let ty := (eval vm_compute in (type_lub (type_of_expr e1) (type_of_expr e2)))
      in

      let k1 k2 cont e1_ r1 si1 s1 j1 :=
          let tk := 
              k2 cont e1_ r1 j1 in
          rndval_with_cond_solve t env si1 s1 e2 tk
      in

      let k2 cont e1_ r1 j1 e2_ r2 si2 s2 j2 :=
          let tk := 
              cont e1_ e2_ j1 j2 in
          rnd_of_binop_with_cond_solve t env si2 s2 ty b r1 r2 tk
      in

      let cont e1_ e2_ j1 j2 b' r si_ shift_ j :=
          adjust_list_forall_eval_cond2 shift_ j1;
            adjust_list_forall_eval_cond2 shift_ j2;
            let j_ := fresh in
            generalize (list_forall_app _ _ _ j (list_forall_app _ _ _ j1 j2));
              clear j1 j2 j;
              intro j_;
              k
                (Binop b' e1_ e2_)
                r
                si_
                shift_
                j_

      in
      let tk :=
            k1 k2 cont in
      rndval_with_cond_solve t env si shift e1 tk

    | Unop ?u ?e1 =>

      let ty := (eval vm_compute in (type_of_expr e1))
      in

      let k1 cont e1_ r1 si1 s1 j1 :=
          let tk := 
              cont e1_ j1 in
          rnd_of_unop_with_cond_solve t env si1 s1 ty u r1 tk
      in

      let cont e1_ j1 b' r si_ shift_ j :=
          adjust_list_forall_eval_cond2 shift_ j1;
            let j_ := fresh in
            generalize (list_forall_app _ _ _ j j1);
              clear j1 j;
              intro j_;
              k
                (Unop b' e1_)
                r
                si_
                shift_
                j_

      in
      let tk :=
          k1 cont in
      rndval_with_cond_solve t env si shift e1 tk


  end.

Definition env_ tenv ty v: ftype ty :=
  match Maps.PTree.get v tenv with
    | Some (Values.Vfloat f) =>
      match type_eq_dec ty Tdouble with
        | left K => eq_rect_r _ f K
        | _ => B754_zero _ _ true
      end
    | Some (Values.Vsingle f) =>
      match type_eq_dec ty Tsingle with
        | left K => eq_rect_r _ f K
        | _ => B754_zero _ _ true
      end
    | _ => B754_zero _ _ true
  end.

Lemma env_finite tenv:
  (forall i v, Maps.PTree.get i tenv = Some v ->
               match v with
                 | Values.Vfloat f => is_finite _ _ f = true
                 | Values.Vsingle f => is_finite _ _ f = true
                 | _ => True
               end) ->
  forall ty i, is_finite _ _ (env_ tenv ty i) = true.
Proof.
  intros.
  unfold env_.
  destruct (Maps.PTree.get i tenv) eqn:EQ; auto.
  destruct v; auto.
  {
    destruct (type_eq_dec ty Tdouble); auto.
    subst.
    unfold eq_rect_r.
    simpl eq_rect.
    apply H in EQ.
    assumption.
  }
  destruct (type_eq_dec ty Tsingle); auto.
  subst.
  unfold eq_rect_r.
  simpl eq_rect.
  apply H in EQ.
  assumption.
Qed.

Lemma eq_rect_r_sym
{U: Type}
{P: U -> Type}
(u1 u2: U)
(Heq: u1 = u2)
(Heq': u2 = u1)
(K: forall (u: U) (v: u = u), v = eq_refl u)
(p: P u1):
p = eq_rect_r P (eq_rect_r P p Heq') Heq.
Proof.
  intros.
  subst u1.
  specialize (K _ Heq').
  subst Heq'.
  reflexivity.
Qed.

Lemma fval_erase_correct {V} env e o e':
  fval (V := V) env e = o ->
  FPLangOpt.erase e' = e ->
  forall EQ,
  { p | fval env e' = p /\ p = eq_rect_r _ o EQ }.
Proof.
  intros.
  generalize (FPLangOpt.erase_correct env e').
  subst.
  generalize (FPLangOpt.erase_type e').
  intros.
  rewrite H.
  esplit.
  split.
  {
    reflexivity.
  }
  apply eq_rect_r_sym.
  intros.
  apply Eqdep_dec.eq_proofs_unicity.
  intros.
  generalize (type_eq_dec x y).
  tauto.
Defined.

Definition annotated_float_expr {V: Type} nv z :=
   (fun z' r si shift t =>
      expr_valid z' = true /\
      FPLangOpt.erase z' = z /\
      rndval_with_cond O (mempty (Tsingle, Normal)) z' = ((r, (si, shift)), t) /\
      list_forall (eval_cond2 (V := V) nv shift) t)
.

(* The following tactic takes an environment nv and a floating-point
   expression z and produces a proof of type:

   (annotated_float_expr nv z _ _ _ _ _)
 
 *)

Ltac annotate_float_expr t nv z k_ :=
      let k z' r si shift j :=
          match type of j with
              list_forall _ ?t =>
              let EVALID := fresh in
              let ERASE := fresh in
              let RNDVAL := fresh in
              (assert (expr_valid z' = true) as EVALID by reflexivity);
                (assert (erase z' = z) as ERASE by reflexivity);
                (
                  tryif
                    (assert (rndval_with_cond O (mempty (Tsingle, Normal)) z' = ((r, (si, shift)), t)) as RNDVAL by (simpl; reflexivity))
                  then
                    k_  EVALID ERASE RNDVAL j
                  else
                    (
                      let t1 := (eval simpl in ((r, (si, shift)), t)) in
                      idtac "Type: " t1;
                      let t_ :=
                          (
                            eval simpl in
                              (rndval_with_cond O (mempty (Tsingle, Normal)) z')
                          )
                      in
                      idtac "Expected: " t_ ;
                      fail 1 "Type mismatch in conditions, please check"
                    )
                )
          end
      in
      rndval_with_cond_solve t nv O (mempty (Tsingle, Normal)) z k
.

Lemma some_inj {A} (a1 a2: A):
  Some a1 = Some a2 ->
  a1 = a2.
Proof.
  congruence.
Qed.

(* In the following, we assume that the environment only contains floating-point numbers.
   Anyway, it is always possible to use Maps.PTree.filter beforehand.
 *)

Definition ttenv :=
  Maps.PTree.map (fun _ v => match v with
                             | Values.Vsingle _ => Tsingle
                             | _ => Tdouble
                           end).

Lemma ttenv_float tenv:
  (forall i : AST.ident,
   forall ty : type,
     Maps.PTree.get i (ttenv tenv) = Some ty -> ty = Tsingle \/ ty = Tdouble).
Proof.
  intros ? ? .
  unfold ttenv.
  rewrite Maps.PTree.gmap.
  unfold Coqlib.option_map.
  destruct (Maps.PTree.get i tenv); try discriminate.
  destruct v; intuition congruence.
Qed.

Ltac compute_type_lub K :=
  repeat
    match type of K with
        context [ type_lub ?a ?b ] =>
        let c := (eval vm_compute in (type_lub a b)) in
        replace (type_lub a b) with c in K by (vm_compute; reflexivity)
    end.

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

Ltac compute_fval t OL cont :=
  match type of OL with
      fval ?nv ?z = ?o =>
      let EFIN := fresh in
      ( (* alternative to pattern-matching *)
        assert (forall ty i, is_finite (fprec ty) (femax ty) (nv ty i) = true)
        as EFIN
          by
            (apply env_finite;
             apply PTree_elements_correct;
             simpl;
             tauto)
      );
        let k EVALID ERASE RNDVAL J := 
            generalize (fval_erase_correct nv z o);
            let K := fresh in
            intro K;
            generalize (fun e' => K e' OL);
            clear OL K; intro K;
            specialize (K _ ERASE);
            clear ERASE;
            specialize (K Logic.eq_refl);
              let j := fresh in
              let FERASE := fresh in
              let FEQ := fresh in
              destruct K as (j & FERASE & FEQ);
              cbn in FEQ;
                subst j;
                let FFIN := fresh in
                let FVAL := fresh in
              destruct (rndval_with_cond_correct
                          _ EFIN _ EVALID _ _ _ _ RNDVAL J _ FEQ)
                as (FFIN & FVAL);
                clear EFIN EVALID RNDVAL J FEQ;
              cbn in FFIN, FVAL;
              compute_type_lub FFIN;
              compute_type_lub FVAL;
              unfold error_bound, ftype, fprec in FFIN, FVAL;
              cbn in FFIN, FVAL;
              break FVAL;
              idtac "Annotations successful";
              cont o FFIN FVAL
          in
          annotate_float_expr t nv z k
      end.

Ltac compute_fval_as' t OL FFIN FVAL :=
  match type of OL with
    | _ = ?o =>
      (assert True as FFIN by exact I);
        (assert True as FVAL by exact I);
        let k o_ FFIN_ FVAL_ :=
            rename o_ into o;
              clear FFIN; rename FFIN_ into FFIN;
              clear FVAL; rename FVAL_ into FVAL
        in
        compute_fval t OL k
  end.

Ltac compute_fval_as := 
  let t _ := interval_ in
  compute_fval_as' t.


Lemma int_part_sterbenz prec emax x k:
is_finite prec emax x = true ->
is_finite prec emax k = true ->
B2R _ _ k = IZR (Int_part (B2R _ _ x)) ->
0 <= B2R _ _ x ->
forall K1 K2 K3 M z,
Bminus prec emax K1 K2 K3 M x k = z ->
is_finite _ _ z = true /\
B2R _ _ z = B2R _ _ x - IZR (Int_part (B2R _ _ x))
.
Proof.
  intros.
  generalize (Bminus_correct _ _ K1 K2 K3 M x k H H0).
  rewrite Generic_fmt.round_generic; try typeclasses eauto.
  {
    rewrite Raux.Rlt_bool_true.
    {
      intuition congruence.
    }
    rewrite H1.
    destruct (base_Int_part (B2R _ _ x)).
    apply Rlt_le_trans with (powerRZ 2 0).
    {
      simpl.
      apply Raux.Rabs_lt.
      Psatz.lra.
    }
    rewrite Raux.bpow_powerRZ.
    simpl IZR.
    repeat rewrite RAux.powerRZ_Rpower by Psatz.lra.
    apply RAux.Rle_Rpower_strong; try Psatz.lra.
    apply IZR_le.
    unfold FLX.Prec_gt_0 in K1.
    eauto with zarith.
  }
  destruct (Rle_dec 1 (B2R _ _ x)).
  {
    apply frac_part_sterbenz in r.
    apply Sterbenz.sterbenz; eauto using generic_format_B2R with typeclass_instances.
    congruence.
  }
  assert (0%Z = Int_part (B2R _ _ x)) as ZERO.
  {
    apply RAux.Int_part_unique; simpl; Psatz.lra.
  }
  rewrite <- ZERO in * |- *.
  simpl IZR in *.
  rewrite H1.
  rewrite Rminus_0_r.
  apply generic_format_B2R.
Qed.

Lemma IZR_Int_part_correct a b:
  a = IZR (Int_part b) ->
  { c |
    a = b - c /\
    0 <= c < 1
  }.
Proof.
  intros.
  subst.
  exists (b - IZR (Int_part b)).
  split.
  {
    ring.
  }
  destruct (base_Int_part b).
  Psatz.lra.
Qed.

Import Integers.

Lemma Rcompare_true u v:
  Floats.cmp_of_comparison Cle (Some (Raux.Rcompare u v)) = true ->
  u <= v
.
Proof.
  generalize (Raux.Rcompare_spec u v).
  inversion 1; subst; simpl; try congruence; intros; lra.
Qed.

(* Require Import Floats.*)
Open Scope R_scope.

Lemma Float_cmp_lt_le_weak f1 f2:
      Float.cmp Integers.Clt f1 f2 = true ->
      Float.cmp Integers.Cle f1 f2 = true.
Proof.
  intros.
  rewrite Float.cmp_le_lt_eq.
  rewrite H.
  reflexivity.
Qed.

Lemma Bcompare_bound_finite prec emax a b c:
  cmp_of_comparison Integers.Cle (Bcompare prec emax a b) = true ->
  cmp_of_comparison Integers.Cle (Bcompare prec emax b c) = true ->
  Binary.is_finite _ _ a = true ->
  Binary.is_finite _ _ c = true ->
  Binary.is_finite _ _ b = true.
Proof.
  destruct a; destruct b; destruct c; simpl; try congruence;
  destruct s0; congruence.
Qed.

Lemma Zfloor_int_part x:
  Raux.Zfloor x = Int_part x.
Proof.
  generalize (Raux.Zfloor_lb x).
  generalize (Raux.Zfloor_ub x).
  intros.
  apply RAux.Int_part_unique; lra.
Qed.

Lemma Rle_bool_iff u v:
  Raux.Rle_bool u v = true <-> u <= v.
Proof.
  split.
  {
    intros.
    generalize (Raux.Rle_bool_spec u v).
    rewrite H.
    inversion 1.
    assumption.
  }
  apply Raux.Rle_bool_true.
Qed.

Lemma Rlt_bool_iff u v:
  Raux.Rlt_bool u v = true <-> u < v.
Proof.
  split.
  {
    intros.
    generalize (Raux.Rlt_bool_spec u v).
    rewrite H.
    inversion 1.
    assumption.
  }
  apply Raux.Rlt_bool_true.
Qed.

Lemma Z_leb_Rle_bool u v:
  Z.leb u (Int_part v) = Raux.Rle_bool (IZR u) v.
Proof.
  rewrite Bool.eq_iff_eq_true.
  rewrite Z.leb_le.
  rewrite Rle_bool_iff.
  destruct (base_Int_part v).
  split.
  {
    intros.
    apply IZR_le in H1.
    lra.
  }
  apply RAux.IZR_Int_part.
Qed.

Lemma Z_leb_Rlt_bool u v:
Z.leb (Int_part u) v = Raux.Rlt_bool u (IZR (v + 1)).
Proof.
  rewrite Bool.eq_iff_eq_true.
  rewrite Z.leb_le.
  rewrite Rlt_bool_iff.
  destruct (base_Int_part u).
  split.
  {
    rewrite plus_IZR.
    replace (IZR 1) with 1 by reflexivity.
    intros.
    apply IZR_le in H1.
    lra.
  }
  intros.
  cut (Int_part u < v + 1)%Z; [ lia | ].
  apply lt_IZR.
  lra.
Qed.

Lemma Float_of_int_exists' x:
      (- 2 ^ 53 <= Integers.Int.signed x <= 2 ^ 53)%Z ->
      { u | Float.of_int x = u /\
                    Binary.is_finite _ _ u = true /\
                    B2R _ _ u = IZR (Integers.Int.signed x) } .
Proof.
  intros.
  generalize (IEEE754_extra.BofZ_exact 53 1024 Logic.eq_refl Logic.eq_refl _ H).
  intro K.
  break K.
  eauto.
Defined.

Lemma Float_of_int_exists x:
      { u | Float.of_int x = u /\
                    is_finite _ _ u = true /\
                    B2R _ _ u = IZR (Int.signed x) } .
Proof.
  apply Float_of_int_exists'.
  generalize (Int.signed_range x).
  simpl.
  unfold Int.min_signed, Int.max_signed.
  simpl.
  cbn.
  lia.
Defined.

Lemma Float_of_int_forall x (P: _ -> Prop):
  (
    (
      forall u,
        is_finite _ _ u = true ->
        B2R _ _ u = IZR (Int.signed x) ->
        P u
    )
  ) ->
  P (Float.of_int x)
.
Proof.
  intros K.
  destruct (Float_of_int_exists x) as (? & a).
  break a.
  rewrite K_ ; clear K_ .
  eauto.
Qed.

Lemma signed_repr_forall z (P: _ -> Prop):
  (
    (Int.min_signed <= z <= Int.max_signed)%Z /\
    P z
  ) -> P (Int.signed (Int.repr z)).
Proof.
  destruct 1.
  rewrite Int.signed_repr; assumption.
Qed.

Lemma Float_of_int_exists_strong' x y:
  Int.eqm (Int.signed x) y ->
  (Int.min_signed <= y <= Int.max_signed)%Z ->
  { u | Float.of_int x = u /\
        is_finite _ _ u = true /\
        B2R _ _ u = IZR y } .
Proof.
  intros H H0.
  apply Int.eqm_samerepr in H.
  rewrite Int.repr_signed in H.
  apply (f_equal Int.signed) in H.
  rewrite Int.signed_repr in H by assumption.
  subst y.
  apply Float_of_int_exists.
Defined.

Lemma Float_of_int_exists_strong x u y:
  u = Float.of_int x ->
  Int.eqm (Int.signed x) y ->
  (Int.min_signed <= y <= Int.max_signed)%Z ->
  is_finite _ _ u = true /\
  B2R _ _ u = IZR y .
Proof.
  intros H H0 H1.
  generalize (Float_of_int_exists_strong' _ _ H0 H1).
  destruct 1 as (z & Hz).
  break Hz.
  intuition congruence.
Qed.

Lemma Int_part_nonneg x:
  0 <= x ->
  (0 <= Int_part x)%Z.
Proof.
  intros.
  apply RAux.IZR_Int_part.
  assumption.
Qed.

Lemma Rcompare_Rlt_true_iff: forall u v : R,
       cmp_of_comparison Clt (Some (Raux.Rcompare u v)) = true <-> u < v.
Proof.
  intros u v.
  generalize (Raux.Rcompare_spec u v).
  inversion 1; simpl; intuition (lra || congruence).
Qed.

Lemma Rcompare_Rle_true_iff: forall u v : R,
       cmp_of_comparison Cle (Some (Raux.Rcompare u v)) = true <-> u <= v.
Proof.
  intros u v.
  generalize (Raux.Rcompare_spec u v).
  inversion 1; simpl; intuition (lra || congruence).
Qed.

Ltac specialize_interval H prec :=
  match type of H with
      _ <= ?u <= _ -> _ =>
      let t k :=
          match goal with
              K: u = ?a |- _ => k K
            | K: ?a = u |- _ =>
              let K_ := fresh "K_" in
              (assert (u = a) as K_ by (symmetry; exact K));
                k K_;
                clear K_
          end
      in
      let k K :=
          match type of K with
            | _ = ?a =>
              let range := fresh "range" in
              idtac a;
              (interval_intro a with (i_prec prec) as range);
                (rewrite <- K in range);
                specialize (H ltac:( lra ) );
                clear range;
                idtac "success"
            | _ =>
              idtac "failure";
                fail
          end
      in
      t k
  end.

Global Existing Instances
      nans map_nat compcert_map
.
