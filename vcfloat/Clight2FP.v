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

VCFloat: helpers for the translation of a CompCert Clight
floating-point expression into a real-number expression with all
rounding error terms and their correctness proofs.
**)

Require Export Lia.
Require Export FPLang FPSolve.
Require Export compcert.cfrontend.Clight.
Require Export cverif.ClightFacts.

Section WITHNANS.
Context {NANS: Nans}.

Fixpoint static_float_type (c: Ctypes.type): option FPLang.type :=
  match c with
    | Ctypes.Tfloat Ctypes.F32 _ => Some Tsingle
    | Ctypes.Tfloat Ctypes.F64 _ => Some Tdouble
    | _ => None
  end.

Definition static_unop (c: Cop.unary_operation) : option (forall  (e: FPLang.expr (V := AST.ident)), FPLang.expr) :=
  match c with
    | Cop.Oneg => 

(* The semantics of Clight assumes that casts have been inserted explicitly beforehand
   for Opp, so that all type annotations are assumed to be correct. *)

      Some (fun e => FPLang.Unop (Exact1 Opp) e)
    | Cop.Oabsfloat => Some (fun e => FPLang.Unop (Exact1 Abs) (FPLang.Unop (FPLang.CastTo Tdouble None) e))
    | _ => None
  end.

Definition static_binop (c: Cop.binary_operation): option FPLang.binop :=
  match c with
    | Cop.Oadd => Some (Rounded2 PLUS None)
    | Cop.Osub => Some (Rounded2 MINUS None)
    | Cop.Omul => Some (Rounded2 MULT None)
    | Cop.Odiv => Some (Rounded2 DIV None)
    | _ => None
  end.

Fixpoint static_float (m: Maps.PTree.t FPLang.type) (e: Clight.expr): option FPLang.expr :=
  match e with
    | Clight.Econst_float f _ => Some (Const Tdouble f)
    | Clight.Econst_single f _ => Some (Const Tsingle f)
    | Clight.Etempvar v _ =>
      match Maps.PTree.get v m with
        | Some ty' => Some (Var ty' v)
        | _ => None
      end
    | Clight.Eunop u e1 _ =>
      match static_float m e1 with
        | Some e1' =>
          match static_float_type (Clight.typeof e1) with
            | Some ty =>
              if type_eqb ty (type_of_expr e1')
              then 
                match static_unop u with
                  | Some f => Some (f e1')
                  | _ => None
                end
              else None
            | _ => None
          end
        | _ => None
      end
    | Clight.Ebinop b e1 e2 _ =>
      match static_float m e1 with
        | Some e1' =>
          match static_float m e2 with
            | Some e2' =>
              match static_binop b with
                | Some b' =>
                  match static_float_type (Clight.typeof e1) with
                    | Some ty1 =>
                      match static_float_type (Clight.typeof e2) with
                        | Some ty2 =>
                          if 
                            andb (type_eqb ty1 (type_of_expr e1'))
                                 (type_eqb ty2 (type_of_expr e2'))
                          then
                            let ty := type_lub ty1 ty2 in
                            Some (FPLang.Binop b'
                                               e1'
                                               e2')
                          else
                            None
                        | None => None
                      end
                    | None => None
                  end
                | None => None
              end
            | None => None
          end      
        | _ => None
      end
    | Clight.Ecast e1 cty =>
      match static_float m e1 with
        | Some e1' =>
          match static_float_type cty with
            | Some ty' =>
              match static_float_type (Clight.typeof e1) with
                | Some ty1 =>
                  if type_eqb ty1 (type_of_expr e1')
                  then
                    Some (FPLang.Unop (FPLang.CastTo ty' None) e1')
                  else
                    None
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end
    | _ => None
  end.

Lemma float_type_swap f:
    match f with
      | Ctypes.F32 => Some Tsingle
      | Ctypes.F64 => Some Tdouble
    end = Some match f with
                 | Ctypes.F32 => Tsingle
                 | Ctypes.F64 => Tdouble
               end.
Proof.
  destruct f; auto.
Qed.

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

Lemma typeof_static_float
      m
      e:
  forall
    (Hm: forall i,
           VSET.In i (cvars e) ->
           forall ty,
             Maps.PTree.get i m = Some ty ->
             ty = Tsingle \/ ty = Tdouble)      
  ,
  forall e',
    static_float m e = Some e' ->
    type_of_expr e' = Tsingle \/ type_of_expr e' = Tdouble
.
Proof.
  induction e; simpl; try discriminate.
  {
    inversion 2; subst; auto.
  }
  {
    inversion 2; subst; auto.
  }
  {
    destruct (Maps.PTree.get i m) eqn:EQ; try discriminate.
    inversion 2; subst.
    simpl.
    specialize (Hm i).
    rewrite VSET.singleton_spec in Hm.
    eauto using Pos.eqb_refl.
  }
  {
    destruct (static_float m e) eqn:E; try discriminate.
    destruct (Clight.typeof e); try discriminate.
    simpl.
    rewrite float_type_swap.
    intro.
    intro.
    destruct (
        type_eqb
          match f with
            | Ctypes.F32 => Tsingle
            | Ctypes.F64 => Tdouble
          end (type_of_expr e0)
      ) eqn:EQ; try discriminate.
    unfold static_unop.
    destruct u; simpl; try discriminate.
    {
      (* opp *)
      inversion 1; subst.
      rewrite type_eqb_eq in EQ.
      simpl.
      unfold id.
      rewrite <- EQ.
      destruct f; auto.
    }
    (* abs *)
    inversion 1; subst.
    simpl.
    auto.
  }
  {
    (* binop *)
    intro.
    generalize (fun i Hi => Hm i (let (_, K) := VSET.union_spec _ _ _ in K Hi)).
    clear Hm.
    intro Hm.
    generalize (fun i Hi => Hm i (or_introl _ Hi)).
    generalize (fun i Hi => Hm i (or_intror _ Hi)).
    clear Hm.
    intros Hm2 Hm1.
    destruct (static_float m e1) eqn:E1; try discriminate.
    destruct (static_float m e2) eqn:E2; try discriminate.
    destruct (static_binop b) eqn:B; try discriminate.
    destruct (Clight.typeof e1); try discriminate.
    destruct (Clight.typeof e2); try (destruct f; discriminate).
    simpl.
    intro.
    rewrite float_type_swap.
    rewrite float_type_swap.
    destruct (
(type_eqb
        match f with
        | Ctypes.F32 => Tsingle
        | Ctypes.F64 => Tdouble
        end (type_of_expr e) &&
      type_eqb
        match f0 with
        | Ctypes.F32 => Tsingle
        | Ctypes.F64 => Tdouble
        end (type_of_expr e0))%bool
      ) ; try discriminate.
    inversion 1; subst.
    simpl.
    specialize (IHe1 Hm1 _ (eq_refl _)).
    specialize (IHe2 Hm2 _ (eq_refl _)).
    destruct IHe1 as [IHe1 | IHe1] ; destruct IHe2 as [IHe2 | IHe2]; rewrite IHe1; rewrite IHe2; simpl; auto.
  }
  (* cast *)
  intro.
  intro.
  destruct (static_float m e) eqn:E; try discriminate.
  destruct (static_float_type t) eqn:T; try discriminate.
  destruct (static_float_type (typeof e)); try discriminate.
  destruct (type_eqb t1 (type_of_expr e0)); try discriminate.
  inversion 1; subst.
  simpl.
  destruct t; try discriminate.
  simpl in T.
  destruct f; simpl; intuition congruence.
Qed.

Import FPLang.

Theorem static_float_correct'
      (conv_nan_single_double:
         conv_nan Tsingle Tdouble = Floats.Float.of_single_nan)
      (conv_nan_double_single:
         conv_nan Tdouble Tsingle = Floats.Float.to_single_nan)

      (plus_nan_single: plus_nan Tsingle = Floats.Float32.binop_nan)
      (plus_nan_double: plus_nan Tdouble = Floats.Float.binop_nan)

      (mult_nan_single: mult_nan Tsingle = Floats.Float32.binop_nan)
      (mult_nan_double: mult_nan Tdouble = Floats.Float.binop_nan)

      (div_nan_single: div_nan Tsingle = Floats.Float32.binop_nan)
      (div_nan_double: div_nan Tdouble = Floats.Float.binop_nan)

      (abs_nan_double: abs_nan Tdouble = Floats.Float.abs_nan)

      (opp_nan_single: opp_nan Tsingle = Floats.Float32.neg_nan)
      (opp_nan_double: opp_nan Tdouble = Floats.Float.neg_nan)

      m me env
      ge ce mm
      
      e:
  forall
    (Hm_ty: forall i,
              VSET.In i (cvars e) ->
              forall ty,
                Maps.PTree.get i m = Some ty ->
                ty = Tsingle \/ ty = Tdouble)
    (Hm_val: forall i,
               VSET.In i (cvars e) ->
               forall ty,
                 Maps.PTree.get i m = Some ty ->
                 exists v,
                   Maps.PTree.get i me = Some v /\
                   val_inject v ty (env ty i))
    t,
      static_float m e = Some t ->
      exists v,
        Clight.eval_expr ge ce me mm e v /\
        val_inject v _ (FPLang.fval env t)
.
Proof.
  induction e; simpl; intros until 2; try congruence.
  {
    (* const *)
    inversion 1; subst.
    repeat econstructor.
  }
  {
    (* const single *)
    inversion 1; subst.
    repeat econstructor.
  }
  {
    (* var *)
    destruct (Maps.PTree.get i m) eqn:VAR; try discriminate.
    inversion 1; subst.
    specialize (Hm_val i).
    rewrite VSET.singleton_spec in Hm_val.
    specialize (Hm_val (eq_refl _) _ VAR).
    destruct Hm_val as (v & Hv & INJ).
    simpl.
    esplit.
    split; try eassumption.
    econstructor.
    assumption.
  }
  {
    (* unop *)
    destruct (static_float m e) eqn:E; try discriminate.
    destruct (static_float_type (Clight.typeof e)) eqn:T; try discriminate.
    unfold static_unop.
    specialize (IHe Hm_ty Hm_val _ (eq_refl _)).
    destruct IHe as (v & Hv & INJ).
    destruct (type_eqb t0 (type_of_expr e0)) eqn:EQ; try discriminate.
    rewrite type_eqb_eq in EQ.
    subst.
    destruct u; try discriminate.
    {
      (* neg *)
      inversion 1; subst.
      destruct (Clight.typeof e) eqn:TY; try discriminate.
      simpl in T.
      rewrite float_type_swap in T.
      inversion T; clear T; subst.
      simpl.
      revert INJ.
      generalize (fval env e0).
      unfold VSET.elt, AST.ident in * |- *.
      rewrite <- H1; clear H1.
      unfold id.
      destruct f; inversion 1; subst.
      {
        (* single *)
        apply val_inject_single_inv in INJ.
        subst.
        esplit.
        split.
        {
          econstructor.
          {
            eassumption.
          }
          simpl.
          rewrite TY.
          unfold Cop.sem_neg.
          simpl.
          reflexivity.
        }
        Transparent Floats.Float32.neg.
        unfold Floats.Float32.neg.
        unfold BOPP.
        rewrite opp_nan_single.
        constructor.
      }
      (* double *)
      apply val_inject_double_inv in INJ.
      subst.
      esplit.
      split.
      {
        econstructor.
        {
          eassumption.
        }
        simpl.
        rewrite TY.
        unfold Cop.sem_neg.
        simpl.
        reflexivity.
      }
      Transparent Floats.Float.neg.
      unfold Floats.Float.neg.
      unfold BOPP.
      rewrite opp_nan_double.
      simpl.
      constructor.
    }
    (* abs *)
    inversion 1; subst.
    simpl.
    unfold id.
    destruct (Clight.typeof e) eqn:TY; try discriminate.
    simpl in T.
    rewrite float_type_swap in T.
    inversion T; clear T; subst.
    simpl.
    revert INJ.
    generalize (fval env e0).
    unfold VSET.elt, AST.ident in * |- *.
    rewrite <- H1; clear H1.
    destruct f.
    {
      unfold cast.
      simpl.
      inversion 1; subst.
      apply val_inject_single_inv in INJ.
      subst.
      esplit.
      split.
      {
        econstructor.
        {
          eassumption.
        }
        simpl.
        unfold Cop.sem_absfloat.
        simpl.
        rewrite TY.
        simpl.
        reflexivity.
      }
      Transparent Floats.Float.of_single.
      unfold Floats.Float.of_single.
      simpl.
      unfold fprec.
      simpl.
      rewrite conv_nan_single_double.
      assert (fprec_gt_0 Tdouble = eq_refl) as K.
      {
        clear.
        apply Eqdep_dec.eq_proofs_unicity.
        decide equality.
      }
      rewrite K; clear K.
      assert (fprec_lt_femax Tdouble = eq_refl) as K.
      {
        clear.
        apply Eqdep_dec.eq_proofs_unicity.
        decide equality.
      }
      rewrite K; clear K.
      Transparent Floats.Float.abs.
      unfold Floats.Float.abs.
      unfold BABS.
      rewrite abs_nan_double.
      constructor.
    }
    inversion 1; subst.
    apply val_inject_double_inv in INJ.
    subst.
    unfold cast.
    simpl.
    esplit.
    split.
    {
      econstructor.
      {
        eassumption.
      }
      simpl.
      unfold Cop.sem_absfloat.
      simpl.
      rewrite TY.
      simpl.
      reflexivity.
    }
    unfold BABS.
    rewrite abs_nan_double.
    constructor.
  }
  {
    (* binop *)
    destruct (static_float m e1) eqn:E1; try discriminate.
    destruct (static_float m e2) eqn:E2; try discriminate.
    destruct (static_binop b) eqn:B; try discriminate.
    destruct (static_float_type (typeof e1)) eqn:T1; try discriminate.
    destruct (static_float_type (typeof e2)) eqn:T2; try discriminate.
    destruct (
        (type_eqb t0 (type_of_expr e) && type_eqb t1 (type_of_expr e0))%bool
      ) eqn:TEQ; try discriminate.
    inversion 1; subst.
    clear H.
    rewrite Bool.andb_true_iff in TEQ.
    destruct TEQ as (TEQ1 & TEQ2).
    rewrite type_eqb_eq in TEQ1.
    rewrite type_eqb_eq in TEQ2.
    subst.
    simpl.
    unfold cast_lub_l, cast_lub_r.
    generalize (fun i Hi => Hm_ty i (let (_, K) := VSET.union_spec _ _ _ in K Hi)).
    generalize (fun i Hi => Hm_val i (let (_, K) := VSET.union_spec _ _ _ in K Hi)).
    clear Hm_ty Hm_val.
    intros Hm_val Hm_ty.
    generalize (fun i Hi => Hm_ty i (or_introl _ Hi)).
    generalize (fun i Hi => Hm_ty i (or_intror _ Hi)).
    generalize (fun i Hi => Hm_val i (or_introl _ Hi)).
    generalize (fun i Hi => Hm_val i (or_intror _ Hi)).
    clear Hm_ty Hm_val.
    intros Hm2_val Hm1_val Hm2_ty Hm1_ty.
    specialize (IHe1 Hm1_ty Hm1_val). clear Hm1_ty Hm1_val.
    specialize (IHe2 Hm2_ty Hm2_val). clear Hm2_ty Hm2_val.
    specialize (IHe1 _ (eq_refl _)).
    destruct IHe1 as (v1 & Hv1 & INJ1).
    specialize (IHe2 _ (eq_refl _)).
    destruct IHe2 as (v2 & Hv2 & INJ2).
    destruct (typeof e1) eqn:CT1; try discriminate.
    simpl in T1.
    rewrite float_type_swap in T1.
    inversion T1; clear T1; subst.
    destruct (typeof e2) eqn:CT2; try discriminate.
    simpl in T2.
    rewrite float_type_swap in T2.
    inversion T2; clear T2; subst.
    revert INJ1 INJ2.
    generalize (fval env e0).
    generalize (fval env e).
    intros f1 f2 Hf1 Hf2.
    unfold VSET.elt, AST.ident in * |- *.
    pose (cty := match f, f0 with
                   | Ctypes.F32, Ctypes.F32 => Ctypes.F32
                   | _, _ => Ctypes.F64
                 end).
    pose (ty' := match cty with
                   | Ctypes.F32 => Tsingle
                   | Ctypes.F64 => Tdouble
                 end).
    assert (type_lub (type_of_expr e) (type_of_expr e0) = ty') as EQTY.
    {
      rewrite <- H0.
      rewrite <- H1.
      unfold ty', cty.
      apply type_eqb_eq.
      destruct f; destruct f0; auto.
    }
    rewrite EQTY.
    clear EQTY.
    pose (f_cast := fun (f_single: Floats.float32 -> Floats.float32 -> Floats.float32)
                         (f_double: Floats.float -> Floats.float -> Floats.float) =>
                      match cty as cty' return
                            ftype match cty' with
                                    | Ctypes.F32 => Tsingle
                                    | Ctypes.F64 => Tdouble
                                  end -> 
                            ftype match cty' with
                                    | Ctypes.F32 => Tsingle
                                    | Ctypes.F64 => Tdouble
                                  end ->
                            ftype match cty' with
                                    | Ctypes.F32 => Tsingle
                                    | Ctypes.F64 => Tdouble
                                  end
                      with
                        | Ctypes.F32 => f_single 
                        | Ctypes.F64 => f_double
                      end).
    fold ty' in f_cast.
    assert (
      forall
        f_double f_single m
      ,
        exists v,
          (forall f_int f_long,
            Cop.sem_binarith f_int f_long
                             (fun n1 n2 => Some (Values.Vfloat (f_double n1 n2)))
                             (fun n1 n2 => Some (Values.Vsingle (f_single n1 n2)))
                             v1 (Ctypes.Tfloat f a)
                             v2 (Ctypes.Tfloat f0 a0) m = Some v) /\
            val_inject v ty'
                       (
                         f_cast f_single f_double
                                (cast ty' _ f1)
                                (cast ty' _ f2)
                       )
      ) as TH.
    {
      intros.
      unfold f_cast.
      unfold Cop.sem_binarith.
      revert f1 Hf1 f2 Hf2.
      rewrite <- H0.
      rewrite <- H1.
      unfold ty'.
      unfold cty.
      destruct f; destruct f0; simpl;
      inversion 1; inversion 1; subst;
      simpl;
      unfold cast;
      simpl.
      {
        apply val_inject_single_inv in Hf1.
        apply val_inject_single_inv in Hf2.
        subst.
        esplit.
        split.
        { reflexivity. }
        constructor.
      }
      {
        apply val_inject_single_inv in Hf1.
        apply val_inject_double_inv in Hf2.
        subst.
        esplit.
        split.
        {
          reflexivity.
        }
        unfold Floats.Float.of_single.
        unfold fprec. simpl.
        rewrite conv_nan_single_double.
        assert (fprec_gt_0 Tdouble = eq_refl) as K.
        {
          apply Eqdep_dec.eq_proofs_unicity.
          decide equality.
        }
        rewrite K; clear K.
        assert (fprec_lt_femax Tdouble = eq_refl) as K.
        {
          apply Eqdep_dec.eq_proofs_unicity.
          decide equality.
        }
        rewrite K; clear K.
        constructor.
      }
      {
        apply val_inject_double_inv in Hf1.
        apply val_inject_single_inv in Hf2.
        subst.
        esplit.
        split.
        {
          reflexivity.
        }
        unfold fprec. simpl.
        rewrite conv_nan_single_double.
        assert (fprec_gt_0 Tdouble = eq_refl) as K.
        {
          apply Eqdep_dec.eq_proofs_unicity.
          decide equality.
        }
        rewrite K; clear K.
        assert (fprec_lt_femax Tdouble = eq_refl) as K.
        {
          apply Eqdep_dec.eq_proofs_unicity.
          decide equality.
        }
        rewrite K; clear K.
        constructor.
      }
      apply val_inject_double_inv in Hf1.
      apply val_inject_double_inv in Hf2.
      subst.
      esplit.
      split.
      { reflexivity. }
      constructor.
    }
    destruct b; try discriminate;
    simpl in B; inversion B; clear B; subst; simpl.
    {
      (* plus *)
      specialize (TH
                    Floats.Float.add
                    Floats.Float32.add mm ).
      destruct TH as (v & Hv & INJ).
      esplit.
      split.
      {
        econstructor.
        {
          eassumption.
        }
        {
          eassumption.
        }
        rewrite CT1. rewrite CT2.
        eapply Hv.
      }
      cut (forall x y, f_cast Floats.Float32.add Floats.Float.add x y = BPLUS ty' x y).
      {
        intro K.
        rewrite <- K.
        assumption.
      }
      unfold ty'.
      unfold f_cast.
      generalize cty.
      revert plus_nan_single plus_nan_double.
      clear.
      intros.      
      destruct cty.
      {
        Transparent Floats.Float32.add.
        unfold Floats.Float32.add.
        unfold BPLUS, BINOP.
        f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
        congruence.
      }
      Transparent Floats.Float.add.
      unfold Floats.Float.add.
      unfold BPLUS, BINOP.
      f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
      congruence.
    }
    {
      (* minus *)
      specialize (TH
                    Floats.Float.sub
                    Floats.Float32.sub mm ).
      destruct TH as (v & Hv & INJ).
      esplit.
      split.
      {
        econstructor.
        {
          eassumption.
        }
        {
          eassumption.
        }
        rewrite CT1. rewrite CT2.
        eapply Hv.
      }
      cut (forall x y, f_cast Floats.Float32.sub Floats.Float.sub x y = BMINUS ty' x y).
      {
        intro K.
        rewrite <- K.
        assumption.
      }
      unfold ty'.
      unfold f_cast.
      generalize cty.
      revert plus_nan_single plus_nan_double.
      clear.
      intros.      
      destruct cty.
      {
        Transparent Floats.Float32.sub.
        unfold Floats.Float32.sub.
        unfold BMINUS, BINOP.
        f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
        congruence.
      }
      Transparent Floats.Float.sub.
      unfold Floats.Float.sub.
      unfold BMINUS, BINOP.
      f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
      congruence.
    }
    {
      (* mult *)
      specialize (TH
                    Floats.Float.mul
                    Floats.Float32.mul mm).
      destruct TH as (v & Hv & INJ).
      esplit.
      split.
      {
        econstructor.
        {
          eassumption.
        }
        {
          eassumption.
        }
        rewrite CT1. rewrite CT2.
        eapply Hv.
      }
      cut (forall x y, f_cast Floats.Float32.mul Floats.Float.mul x y = BMULT ty' x y).
      {
        intro K.
        rewrite <- K.
        assumption.
      }
      unfold ty'.
      unfold f_cast.
      generalize cty.
      revert mult_nan_single mult_nan_double.
      clear.
      intros.      
      destruct cty.
      {
        Transparent Floats.Float32.mul.
        unfold Floats.Float32.mul.
        unfold BMULT, BINOP.
        f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
        congruence.
      }
      Transparent Floats.Float.mul.
      unfold Floats.Float.mul.
      unfold BMULT, BINOP.
      f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
      congruence.
    }
      (* div *)
      specialize (TH
                    Floats.Float.div
                    Floats.Float32.div mm).
      destruct TH as (v & Hv & INJ).
      esplit.
      split.
      {
        econstructor.
        {
          eassumption.
        }
        {
          eassumption.
        }
        rewrite CT1. rewrite CT2.
        eapply Hv.
      }
      cut (forall x y, f_cast Floats.Float32.div Floats.Float.div x y = BDIV ty' x y).
      {
        intro K.
        rewrite <- K.
        assumption.
      }
      unfold ty'.
      unfold f_cast.
      generalize cty.
      revert div_nan_single div_nan_double.
      clear.
      intros.      
      destruct cty.
      {
        Transparent Floats.Float32.div.
        unfold Floats.Float32.div.
        unfold BDIV, BINOP.
        f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
        congruence.
      }
      Transparent Floats.Float.div.
      unfold Floats.Float.div.
      unfold BDIV, BINOP.
      f_equal; try (apply Eqdep_dec.eq_proofs_unicity; decide equality).
      congruence.
  }
  
  (* cast *)
  destruct (static_float m e) eqn:E; try discriminate.
  destruct (static_float_type t) eqn:T; try discriminate.
  destruct (static_float_type (typeof e)) eqn:TO; try discriminate.
  destruct (type_eqb t1 (type_of_expr e0)) eqn:TEQ; try discriminate.
  inversion 1; subst.
  clear H.
  rewrite type_eqb_eq in TEQ.
  subst.
  simpl.
  specialize (IHe Hm_ty Hm_val _ (eq_refl _)); clear Hm_ty Hm_val.
  destruct IHe as (v & Hv & INJ).
  destruct t; try discriminate.
  simpl in T.
  rewrite float_type_swap in T.
  inversion T; clear T; subst.
  destruct (typeof e) eqn:TY; try discriminate.
  simpl in TO.
  rewrite float_type_swap in TO.
  inversion TO; clear TO; subst.
  revert INJ.
  generalize (fval env e0).
  unfold VSET.elt, AST.ident in * |- *.
  rewrite <- H0; clear H0.
  destruct f; destruct f0; simpl; unfold cast; simpl; inversion 1; subst.
  {
    apply val_inject_single_inv in INJ.
    subst.
    esplit.
    split.
    {
      econstructor.
      {
        eassumption.
      }
      rewrite TY.
      unfold Cop.sem_cast.
      simpl.
      reflexivity.
    }
    constructor.
  }
  {
    apply val_inject_double_inv in INJ.
    subst.
    esplit.
    split.
    {
      econstructor.
      {
        eassumption.
      }
      rewrite TY.
      unfold Cop.sem_cast.
      simpl.
      reflexivity.
    }
    Transparent Floats.Float.to_single.
    unfold Floats.Float.to_single.
    unfold fprec; simpl.
    assert (fprec_gt_0 Tsingle = eq_refl) as K.
    {
      clear.
      apply Eqdep_dec.eq_proofs_unicity.
      decide equality.
    }
    rewrite K; clear K.
    assert (fprec_lt_femax Tsingle = eq_refl) as K.
    {
      clear.
      apply Eqdep_dec.eq_proofs_unicity.
      decide equality.
    }
    rewrite K; clear K.
    rewrite conv_nan_double_single.
    constructor.
  }
  {
    apply val_inject_single_inv in INJ.
    subst.
    esplit.
    split.
    {
      econstructor.
      {
        eassumption.
      }
      rewrite TY.
      unfold Cop.sem_cast.
      simpl.
      reflexivity.
    }
    unfold Floats.Float.of_single.
    assert (fprec_gt_0 Tdouble = eq_refl) as K.
    {
      clear.
      apply Eqdep_dec.eq_proofs_unicity.
      decide equality.
    }
    rewrite K; clear K.
    assert (fprec_lt_femax Tdouble = eq_refl) as K.
    {
      clear.
      apply Eqdep_dec.eq_proofs_unicity.
      decide equality.
    }
    rewrite K; clear K.
    unfold fprec; simpl.
    rewrite conv_nan_single_double.
    constructor.
  }
  apply val_inject_double_inv in INJ.
  subst.
  esplit.
  split.
  {
    econstructor.
    {
      eassumption.
    }
    rewrite TY.
    unfold Cop.sem_cast.
    simpl.
    reflexivity.
  }
  constructor.
Qed.

End WITHNANS.


Section NANS.

Definition static_float_correct_1 :=
  static_float_correct'
    eq_refl eq_refl
    eq_refl eq_refl
    eq_refl eq_refl
    eq_refl eq_refl
    eq_refl
    eq_refl eq_refl
.

Theorem static_float_correct:
forall (m : Maps.PTree.t type) (me : Maps.PTree.t Values.val)
         (env0 : forall x : type, VSET.elt -> ftype x) 
         (ge : genv) (ce : env) (mm : Memory.Mem.mem) 
         (e : expr),
       (forall i : VSET.elt,
        List.In i (VSET.elements (cvars e)) ->
        forall ty : type,
        Maps.PTree.get i m = Some ty -> ty = Tsingle \/ ty = Tdouble) ->
       (forall i : VSET.elt,
          List.In i (VSET.elements (cvars e)) ->
        forall ty : type,
        Maps.PTree.get i m = Some ty ->
        exists v : Values.val,
          Maps.PTree.get i me = Some v /\ val_inject v ty (env0 ty i)) ->
       forall t : FPLang.expr,
       static_float m e = Some t ->
       exists v : Values.val,
         eval_expr ge ce me mm e v /\
         val_inject v (type_of_expr t) (fval env0 t)
.
Proof.
  intros.
  eapply static_float_correct_1; eauto.
  {
    intro.
    rewrite <- VSET.elements_spec1.
    rewrite SetoidList.InA_alt.
    destruct 1 as (? & ? & ?); subst; eauto.
  }
  intro.
  rewrite <- VSET.elements_spec1.
  rewrite SetoidList.InA_alt.
  destruct 1 as (? & ? & ?); subst; eauto.
Qed.  

End NANS.
