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

VCFloat: helpers for correct optimization of rounding error terms in
the real-number semantics of floating-point computations.
**)

Require Export vcfloat.FPLang.
Import RAux.
Import compcert.lib.IEEE754_extra.
Import compcert.lib.Floats.
Require Export vcfloat.LibTac.
Require Export vcfloat.BigRAux.
Set Bullet Behavior "Strict Subproofs". (* because LibTac screws it up *)

Definition rounded_binop_eqb (r1 r2: rounded_binop): bool :=
  match r1, r2 with
    | PLUS, PLUS => true
    | MINUS, MINUS => true
    | MULT, MULT => true
    | DIV, DIV => true
    | _, _ => false
  end.

Lemma rounded_binop_eqb_eq r1 r2:
  (rounded_binop_eqb r1 r2 = true <-> r1 = r2).
Proof.
  destruct r1; destruct r2; simpl; intuition congruence.
Qed.

Definition rounding_knowledge_eqb (r1 r2: rounding_knowledge): bool :=
  match r1, r2 with
    | Normal, Normal => true
    | Denormal, Denormal => true
    | _, _ => false
  end.

Lemma rounding_knowledge_eqb_eq r1 r2:
  (rounding_knowledge_eqb r1 r2 = true <-> r1 = r2).
Proof.
  destruct r1; destruct r2; simpl; intuition congruence.
Qed.

Export Bool.

Definition binop_eqb b1 b2 :=
  match b1, b2 with
    | Rounded2 op1 k1, Rounded2 op2 k2 =>
      rounded_binop_eqb op1 op2 && option_eqb rounding_knowledge_eqb k1 k2
    | SterbenzMinus, SterbenzMinus => true
    | PlusZero minus1 zero_left1, PlusZero minus2 zero_left2 =>
      Bool.eqb minus1 minus2 && Bool.eqb zero_left1 zero_left2
    | _, _ => false
  end.

Lemma binop_eqb_eq b1 b2:
  (binop_eqb b1 b2 = true <-> b1 = b2).
Proof.
  destruct b1; destruct b2; simpl; (try intuition congruence);
  rewrite andb_true_iff;
    (try rewrite rounded_binop_eqb_eq);
    (try rewrite (option_eqb_eq rounding_knowledge_eqb_eq));
    (repeat rewrite Bool.eqb_true_iff);
  intuition congruence.
Qed.

Definition rounded_unop_eqb u1 u2 :=
  match u1, u2 with
    | SQRT, SQRT => true
  end.

Lemma rounded_unop_eqb_eq u1 u2:
  (rounded_unop_eqb u1 u2 = true <-> u1 = u2).
Proof.
  destruct u1; destruct u2; simpl; intuition congruence.
Qed.


Definition exact_unop_eqb u1 u2 :=
  match u1, u2 with
    | Abs, Abs => true
    | Opp, Opp => true
    | Shift p1 b1, Shift p2 b2  => N.eqb p1 p2 && Bool.eqb b1 b2
    | InvShift p1 b1, InvShift p2 b2 => Pos.eqb p1 p2 && Bool.eqb b1 b2
    | _, _ => false
  end.

Lemma exact_unop_eqb_eq u1 u2:
  (exact_unop_eqb u1 u2 = true <-> u1 = u2).
Proof.
  destruct u1; destruct u2; simpl; (try intuition congruence);
  rewrite Bool.andb_true_iff;
  (try rewrite Pos.eqb_eq);
  (try rewrite N.eqb_eq);
  rewrite Bool.eqb_true_iff;
  intuition congruence.
Qed.

Definition unop_eqb u1 u2 :=
  match u1, u2 with
    | Rounded1 op1 k1, Rounded1 op2 k2 =>
      rounded_unop_eqb op1 op2 && option_eqb rounding_knowledge_eqb k1 k2
    | Exact1 o1, Exact1 o2 => exact_unop_eqb o1 o2
    | CastTo ty1 k1, CastTo ty2 k2 =>
      type_eqb ty1 ty2 && option_eqb rounding_knowledge_eqb k1 k2
    | _, _ => false
  end.

Lemma unop_eqb_eq u1 u2:
  (unop_eqb u1 u2 = true <-> u1 = u2).
Proof.
  destruct u1; destruct u2; simpl; (try intuition congruence).
  {
    rewrite andb_true_iff.
    rewrite rounded_unop_eqb_eq.
    rewrite (option_eqb_eq rounding_knowledge_eqb_eq).
    intuition congruence.
  }
  {
    rewrite exact_unop_eqb_eq.
    intuition congruence.
  }
  rewrite andb_true_iff.
  rewrite type_eqb_eq.
  rewrite (option_eqb_eq rounding_knowledge_eqb_eq).
  intuition congruence.
Qed.

Section WITHVARS.
Context {V} `{VARS: VarType V}.

Context {NANS: Nans}.

Definition fcval_nonrec (e: expr): option (ftype (type_of_expr e)) :=
  match e as e' return option (ftype (type_of_expr (V := V) e')) with
    | Const ty f => Some f
    | _ => None
  end.

Lemma fcval_nonrec_correct e:
  forall v, fcval_nonrec e = Some v ->
            forall env, fval env e = v.
Proof.
  destruct e; simpl; try discriminate.
  intros; congruence.
Qed.

Definition option_pair_of_options {A B} (a: option A) (b: option B) :=
  match a, b with
    | Some a', Some b' => Some (a', b')
    | _, _ => None
  end.

Lemma option_pair_of_options_correct {A B} (a: option A) (b: option B) a' b':
  option_pair_of_options a b = Some (a', b') ->
  a = Some a' /\ b = Some b'.
Proof.
  unfold option_pair_of_options.
  destruct a; destruct b; intuition congruence.
Qed.

(* Partial evaluation of constants *)

Fixpoint fcval (e: expr) {struct e}: expr :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fcval e1 in
      let e'2 := fcval e2 in
      match option_pair_of_options (fcval_nonrec e'1) (fcval_nonrec e'2) with
        | Some (v1, v2) =>
          Const _ (fop_of_binop b _ (cast_lub_l _ _ v1) (cast_lub_r _ _ v2))
        | None => Binop b e'1 e'2
      end
    | Unop b e =>
      let e' := fcval e in
      match fcval_nonrec e' with
        | Some v => Const _ (fop_of_unop b _ v)
        | _ => Unop b e'
      end
    | _ => e
  end.

Lemma fcval_type e:
  type_of_expr (fcval e) = type_of_expr e.
Proof.
  induction e; simpl; auto.
  {
    destruct (fcval_nonrec (fcval e1)) eqn:EQ1; simpl; try congruence.
    destruct (fcval_nonrec (fcval e2)) eqn:EQ2; simpl; congruence.
  }
  destruct (fcval_nonrec (fcval e)) eqn:EQ; simpl; congruence.
Defined. (* required because of eq_rect_r *)

Lemma fcval_correct_bool env e:
  binary_float_eqb (fval env (fcval e)) (fval env e) = true.
Proof.
  induction e; simpl.
  {
    apply binary_float_eqb_eq. reflexivity.
  }
  {
    apply binary_float_eqb_eq. reflexivity.
  }
  {
    destruct (option_pair_of_options (fcval_nonrec (fcval e1)) (fcval_nonrec (fcval e2))) eqn:OPT.
    {
      destruct p.
      apply option_pair_of_options_correct in OPT.
      destruct OPT as (V1 & V2).
      apply fcval_nonrec_correct with (env := env) in V1.
      apply fcval_nonrec_correct with (env := env) in V2.
      simpl.
      unfold cast_lub_l, cast_lub_r.
      subst.
      revert IHe1 IHe2.
      generalize (fval env (fcval e1)).
      generalize (fval env e1).
      generalize (fval env (fcval e2)).
      generalize (fval env e2).
      rewrite fcval_type.
      rewrite fcval_type.
      intros ? ? ? ? .
      repeat rewrite binary_float_eqb_eq.
      congruence.
    }
    clear OPT.
    simpl.
    unfold cast_lub_l, cast_lub_r.
    subst.
    revert IHe1 IHe2.
    generalize (fval env (fcval e1)).
    generalize (fval env e1).
    generalize (fval env (fcval e2)).
    generalize (fval env e2).
    rewrite fcval_type.
    rewrite fcval_type.
    intros ? ? ? ? .
    repeat rewrite binary_float_eqb_eq.
    congruence.
  }    
  destruct (fcval_nonrec (fcval e)) eqn:V_.
  {
    apply fcval_nonrec_correct with (env := env) in V_.
    subst.
    revert IHe.
    generalize (fval env (fcval e)).
    generalize (fval env e).
    rewrite fcval_type.
    intros ? ? .
    simpl.
    repeat rewrite binary_float_eqb_eq.
    congruence.
  }
  simpl.
  revert IHe.
  generalize (fval env (fcval e)).
  generalize (fval env e).
  rewrite fcval_type.
  intros ? ? .
  simpl.
  repeat rewrite binary_float_eqb_eq.
  congruence.
Qed.  

Lemma binary_float_eqb_eq_strong ty1 ty2 (e1: ftype ty1) (e2: ftype ty2):
  binary_float_eqb e1 e2 = true ->
  forall EQ: ty1 = ty2,
    binary_float_eqb e1 (eq_rect_r _ e2 EQ) = true.
Proof.
  intros.
  subst.
  assumption.
Qed.
        
Lemma fcval_correct env e:
  fval env (fcval e) = eq_rect_r _ (fval env e) (fcval_type e).
Proof.
  apply binary_float_eqb_eq.
  apply binary_float_eqb_eq_strong.
  apply fcval_correct_bool.
Qed.

Lemma is_finite_eq_rect_r ty1 ty2 (f: ftype ty2)
      (EQ: ty1 = ty2):
  Binary.is_finite _ _ (eq_rect_r _ f EQ) = Binary.is_finite _ _ f.
Proof.
  subst.
  reflexivity.
Qed.

Lemma B2R_eq_rect_r ty1 ty2 (f: ftype ty2)
      (EQ: ty1 = ty2):
  Binary.B2R _ _ (eq_rect_r _ f EQ) = Binary.B2R _ _ f.
Proof.
  subst.
  reflexivity.
Qed.

Import Qreals.
Open Scope R_scope.

(* Identification of shifts *)
Definition F2BigQ (beta : Zaux.radix) (f : Defs.float beta) :=
  match f with
    | {| Defs.Fnum := Fnum; Defs.Fexp := Fexp |} =>
      BigQ.mul (BigQ.Qz (BigZ.of_Z Fnum)) (BigQ.power (BigQ.Qz (BigZ.of_Z (Zaux.radix_val beta))) Fexp)
  end.

Lemma Q2R_Qpower_positive p:
  forall q,
    Q2R (Qpower_positive q p) = Q2R q ^ Pos.to_nat p.
Proof.
  induction p.
  {
    intros.
    rewrite Pos2Nat.inj_xI.
    simpl.
    repeat rewrite pow_add.
    simpl.
    repeat rewrite Q2R_mult.
    repeat rewrite IHp.
    ring.
  }
  {
    intros.
    rewrite Pos2Nat.inj_xO.
    simpl.
    repeat rewrite pow_add.
    simpl.
    repeat rewrite Q2R_mult.
    repeat rewrite IHp.
    ring.
  }
  simpl.
  intros.
  ring.
Qed.

Lemma Q2R_pow q z:
  ~ q == 0%Q ->
  Q2R (q ^ z) = powerRZ (Q2R q) z.
Proof.
  intros.
  unfold powerRZ, Qpower.
  destruct z.
  {
    unfold Q2R. simpl. field.
  }
  {
    apply Q2R_Qpower_positive.
  }
  rewrite Q2R_inv.
  {
    f_equal.
    apply Q2R_Qpower_positive.
  }
  apply Qpower.Qpower_not_0_positive.
  assumption.
Qed.

Lemma F2BigQ2R beta f:
  BigQ2R (F2BigQ beta f) = F2R beta f.
Proof.
  destruct f; cbn -[BigQ.mul].
  unfold BigQ2R.
  rewrite BigQ.spec_mul.
  rewrite BigQ.spec_power.
  repeat rewrite to_Q_bigZ.
  repeat rewrite BigZ.spec_of_Z.
  rewrite Q2R_mult.
  rewrite Q2R_pow.
  {
    repeat rewrite Q2R_inject_Z.
    repeat rewrite <- Z2R_IZR.
    rewrite <- bpow_powerRZ.
    reflexivity.
  }
  replace 0%Q with (inject_Z 0) by reflexivity.
  rewrite inject_Z_injective.
  generalize (Zaux.radix_gt_0 beta).
  lia.
Qed.

Definition B2BigQ {prec emax} b := F2BigQ _ (@B2F prec emax b).

Lemma B2BigQ2R {prec emax} b:
  Binary.B2R prec emax b = BigQ2R (B2BigQ b).
Proof.
  unfold B2BigQ.
  rewrite F2BigQ2R.
  rewrite B2F_F2R_B2R.
  rewrite F2R_eq.
  reflexivity.
Qed.

Fixpoint blog (base: bigZ) (accu: nat) (z: bigZ) (fuel: nat) {struct fuel}: nat :=
  match fuel with
    | O => O
    | S fuel' =>
      if BigZ.eqb z BigZ.one
      then accu
      else
        let '(q, r) := BigZ.div_eucl z base in
        if BigZ.eqb r BigZ.zero
        then blog base (S accu) q fuel'
        else O
  end.

Definition to_power_2 {prec emax} (x: Binary.binary_float prec emax) :=
  let y := B2BigQ x in
  let '(q, r) := BigZ.div_eucl (Bnum y) (BigZ.Pos (Bden y)) in
  N.of_nat (blog (BigZ.of_Z 2) O q (Z.to_nat emax))
.

Definition to_inv_power_2 {prec emax} (x: Binary.binary_float prec emax) :=
  let y := BigQ.inv (B2BigQ x) in
  let '(q, r) := BigZ.div_eucl (Bnum y) (BigZ.Pos (Bden y)) in
  Pos.of_nat (blog (BigZ.of_Z 2) O q (Z.to_nat emax))
.

Fixpoint fshift (e: FPLang.expr) {struct e}: FPLang.expr :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fshift e1 in
      let e'2 := fshift e2 in
      if binop_eqb b (Rounded2 MULT None)
      then
        let ty := type_lub (type_of_expr e'1) (type_of_expr e'2) in
        match fcval_nonrec e'1 with
          | Some c1' =>
            let c1 := cast ty _ c1' in
            let n := to_power_2 c1 in
            if binary_float_eqb c1 (B2 ty (Z.of_N n))
            then Unop (Exact1 (Shift n false)) (Unop (CastTo ty None) e'2)
            else
              let n := to_inv_power_2 c1 in
              if binary_float_eqb c1 (B2 ty (- Z.pos n))
              then Unop (Exact1 (InvShift n false)) (Unop (CastTo ty None) e'2)
              else Binop b e'1 e'2
          | None =>
            match fcval_nonrec e'2 with
              | Some c2' =>
                let c2 := cast ty _ c2' in
                let n := to_power_2 c2 in
                if binary_float_eqb c2 (B2 ty (Z.of_N n))
                then Unop (Exact1 (Shift n true)) (Unop (CastTo ty None) e'1)
                else
                  let n := to_inv_power_2 c2 in
                  if binary_float_eqb c2 (B2 ty (- Z.pos n))
                  then Unop (Exact1 (InvShift n true)) (Unop (CastTo ty None) e'1)
                  else Binop b e'1 e'2
              | None => Binop b e'1 e'2
            end                  
        end
      else
        Binop b e'1 e'2
    | Unop b e => Unop b (fshift e)
    | _ => e
  end.

Lemma fshift_type e:
  type_of_expr (fshift e) = type_of_expr e.
Proof.
  induction e; simpl; auto.
  {
    destruct (binop_eqb b (Rounded2 MULT None)) eqn:EQ.
    {
      apply binop_eqb_eq in EQ.
      subst.
      simpl.
      destruct (fcval_nonrec (fshift e1)).
      {
        revert IHe1 f. 
        generalize (fshift e1).
        intros until 1.
        rewrite IHe1.
        intros.
        simpl.
        match goal with
            |- type_of_expr (if ?v then _ else _) = _ =>
            destruct v
        end;
          simpl.
        {
          unfold Datatypes.id.
          congruence.
        }
        match goal with
            |- type_of_expr (if ?v then _ else _) = _ =>
            destruct v
        end; simpl;
        unfold Datatypes.id;
        congruence.
}
      destruct (fcval_nonrec (fshift e2)).
 {
        match goal with
            |- type_of_expr (if ?v then _ else _) = _ =>
            destruct v
        end; simpl.
        {
          unfold Datatypes.id.
          congruence.
        }
        match goal with
            |- type_of_expr (if ?v then _ else _) = _ =>
            destruct v
        end; simpl.
        {
        unfold Datatypes.id;
        congruence.
      }
        congruence.
      }
        simpl.
        congruence.
}
    simpl.
    congruence.
    }
    simpl.
    congruence.
Defined. 

Lemma fshift_correct' env e:
 binary_float_eqb (fval env (fshift e)) (fval env e) = true.
Proof.
  induction e; simpl.
  {
    apply binary_float_eqb_eq. reflexivity.
  }
  {
    apply binary_float_eqb_eq. reflexivity.
  }
  {
    destruct (binop_eqb b (Rounded2 MULT None)) eqn:ISMULT.
    {
      apply binop_eqb_eq in ISMULT.
      subst.
      destruct (fcval_nonrec (fshift e1)) eqn:E1.
      {
        generalize (fshift_type e1).
        destruct (fshift e1); try discriminate.
        simpl in E1.
        simpl in f.
        inversion E1; clear E1; subst.
        simpl in IHe1.
        simpl.
        intros.
        subst.
        apply binary_float_eqb_eq in IHe1.
        subst.
        match goal with
            |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
            destruct b eqn:FEQ
        end;
          simpl.
        {
          unfold cast_lub_l.
          unfold cast_lub_r.
          revert IHe2.
          generalize (fval env (fshift e2)).
          revert FEQ.
          rewrite fshift_type.
          intros.
          apply binary_float_eqb_eq in IHe2.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
        }
        clear FEQ.
        match goal with
            |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
            destruct b eqn:FEQ
        end;
          simpl.
        {
          unfold Datatypes.id.
          unfold cast_lub_l.
          unfold cast_lub_r.
          revert IHe2.
          generalize (fval env (fshift e2)).
          revert FEQ.
          rewrite fshift_type.
          intros.
          apply binary_float_eqb_eq in IHe2.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
        }
        clear FEQ.
        revert IHe2.
        generalize (fval env (fshift e2)).
        rewrite fshift_type.
        intros.
        apply binary_float_eqb_eq in IHe2.
        subst.
        apply binary_float_eqb_eq.
        reflexivity.
      }
      destruct (fcval_nonrec (fshift e2)) eqn:E2.
      {
        generalize (fshift_type e2).
        destruct (fshift e2); try discriminate.
        simpl in E2.
        simpl in f.
        inversion E2; clear E2; subst.
        simpl in IHe2.
        simpl.
        intros.
        subst.
        apply binary_float_eqb_eq in IHe2.
        subst.
        match goal with
            |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
            destruct b eqn:FEQ
        end;
          simpl.
        {
          unfold cast_lub_l.
          unfold cast_lub_r.
          revert IHe1.
          generalize (fval env (fshift e1)).
          revert FEQ.
          rewrite fshift_type.
          intros.
          apply binary_float_eqb_eq in IHe1.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
        }
        clear FEQ.
        match goal with
            |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
            destruct b eqn:FEQ
        end;
          simpl.
        {
          unfold cast_lub_l.
          unfold cast_lub_r.
          revert IHe1.
          generalize (fval env (fshift e1)).
          revert FEQ.
          rewrite fshift_type.
          intros.
          apply binary_float_eqb_eq in IHe1.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
        }
        clear FEQ.
        revert IHe1.
        generalize (fval env (fshift e1)).
        rewrite fshift_type.
        intros.
        apply binary_float_eqb_eq in IHe1.
        subst.
        apply binary_float_eqb_eq.
        reflexivity.
      }
      clear E1 E2.
      revert IHe1 IHe2.
      simpl.
      generalize (fval env (fshift e1)).
      generalize (fval env (fshift e2)).
      repeat rewrite fshift_type.
      intros.
      apply binary_float_eqb_eq in IHe1. subst.
      apply binary_float_eqb_eq in IHe2. subst.
      apply binary_float_eqb_eq.
      reflexivity.
    }
    clear ISMULT.
    revert IHe1 IHe2.
    simpl.
    generalize (fval env (fshift e1)).
    generalize (fval env (fshift e2)).
    repeat rewrite fshift_type.
    intros.
    apply binary_float_eqb_eq in IHe1. subst.
    apply binary_float_eqb_eq in IHe2. subst.
    apply binary_float_eqb_eq.
    reflexivity.
  }
  revert IHe.
  generalize (fval env (fshift e)).
  rewrite fshift_type.
  intros.
  apply binary_float_eqb_eq in IHe.
  subst.
  apply binary_float_eqb_eq.
  reflexivity.
Qed.

Lemma fshift_correct env e:
  fval env (fshift e) = eq_rect_r _ (fval env e) (fshift_type e).
Proof.
  apply binary_float_eqb_eq.
  apply binary_float_eqb_eq_strong.
  apply fshift_correct'.
Qed.

Definition to_power_2_pos {prec emax} (x: Binary.binary_float prec emax) :=
  let y := B2BigQ x in
  let '(q, r) := BigZ.div_eucl (Bnum y) (BigZ.Pos (Bden y)) in
  Pos.of_nat (blog (BigZ.of_Z 2) O q (Z.to_nat emax))
.

Fixpoint fshift_div (e: FPLang.expr) {struct e}: FPLang.expr :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fshift_div e1 in
      let e'2 := fshift_div e2 in
      if binop_eqb b (Rounded2 DIV None) then
      let ty := type_lub (type_of_expr e'1) (type_of_expr e'2) in
      match (fcval_nonrec e'2) with
            | Some c2' =>
                let c2 := cast ty _ c2' in
                match (Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) c2) with
                  | Some z' => 
                    let n1 := to_power_2_pos c2 in
                    if binary_float_eqb z' (B2 ty (Z.neg n1))
                    then Unop (Exact1 (InvShift n1 true)) (Unop (CastTo ty None) e'1)
                    else
                    let n2 := to_inv_power_2 c2 in
                    if binary_float_eqb z' (B2 ty (Z.pos n2))
                    then Unop (Exact1 (Shift (N.of_nat (Pos.to_nat n2)) true)) (Unop (CastTo ty None) e'1)
                    else Binop b e'1 e'2
                  | None => Binop b e'1 e'2
                end
             | None => Binop b e'1 e'2
         end
      else
        Binop b e'1 e'2
    | Unop b e => Unop b (fshift_div e)
    | _ => e
  end.


Lemma fshift_type_div e:
  type_of_expr (fshift_div e) = type_of_expr e.
Proof.
   induction e; simpl; auto.
  {
    destruct (binop_eqb b (Rounded2 DIV None)) eqn:EQ.
    {
      apply binop_eqb_eq in EQ.
      subst.
      simpl.
      destruct (fcval_nonrec (fshift_div e2)).
      {
        revert IHe2 f. 
        generalize (fshift_div e2).
        intros until 1.
        rewrite IHe2.
        intros.
        simpl.
        destruct (Bexact_inverse _ ). 
        {
          match goal with
              |- type_of_expr (if ?v then _ else _) = _ =>
              destruct v
          end;
            simpl.
        {
          unfold Datatypes.id.
          congruence.
        }
        {
        match goal with
            |- type_of_expr (if ?v then _ else _) = _ =>
            destruct v
        end; simpl.
        {
          unfold Datatypes.id.
          congruence.
        }
          congruence.
}
}
        simpl.
        congruence.
}
        simpl.
        congruence.
}
        simpl.
        congruence.
}
        congruence.
Defined. 



Lemma fshift_div_correct' env e:
 binary_float_equiv (fval env (fshift_div e)) (fval env e).
Proof.
{ induction e; cbn [fshift_div].
- apply binary_float_eq_equiv. reflexivity.
- apply binary_float_eq_equiv. reflexivity.
- { destruct (binop_eqb b (Rounded2 DIV None)) eqn:ISDIV.
- apply binop_eqb_eq in ISDIV; subst.
{ destruct (fcval_nonrec (fshift_div e2)) eqn:E2.
- generalize (fshift_type_div e2).
destruct (fshift_div e2); try discriminate.
simpl in E2; simpl in f; inversion E2; clear E2; subst.
simpl in IHe2; cbn [type_of_expr]; intros; subst.
{ destruct (Bexact_inverse _ ) eqn:EINV. 
- { destruct f. 
- eapply exact_inverse in EINV. contradiction.     (* IHe2 zero *)
apply cast_inf_strict; simpl; auto.
- eapply exact_inverse in EINV. contradiction.     (* IHe2 inf *)
apply cast_inf_strict; simpl; auto.
- eapply exact_inverse in EINV. contradiction.     (* IHe2 nan *)
apply cast_inf_strict; simpl; auto.
- { eapply binary_float_equiv_eq in IHe2.          (* IHe2 finite *)
- { destruct (fcval_nonrec (fshift_div e1)) eqn:E1.
- generalize (fshift_type_div e1).
destruct (fshift_div e1); try discriminate.
simpl in E1; simpl in f; inversion E1; clear E1; subst.
simpl in IHe1; cbn [type_of_expr]; intros; subst.
{ destruct f.                                      (* IHe1 zero *)
- { eapply binary_float_equiv_eq in IHe1.
{ match goal with
|- binary_float_equiv (fval env (if ?b then _ else _)) _ =>
destruct b eqn:FEQ
end.
- rewrite ?andb_true_iff in FEQ; 
unfold cast_lub_l;
unfold cast_lub_r.
apply binary_float_eqb_eq in FEQ.
rewrite FEQ in EINV. 
apply binary_float_equiv_sym.
simpl; unfold cast_lub_l;
unfold cast_lub_r. rewrite <- IHe1; rewrite <- IHe2.
{ apply Bdiv_mult_inverse_equiv ; try apply EINV.
- apply cast_finite; simpl; auto;
eapply type_lub_right.
- apply Bexact_inverse_correct in EINV.
destruct EINV as (A & B & C & D & E). 
apply is_finite_strict_finite in B.  apply B.
}
- clear FEQ. { match goal with
|- binary_float_equiv (fval env (if ?b then _ else _)) _ =>
destruct b eqn:FEQ
end.
- rewrite ?andb_true_iff in FEQ; 
unfold cast_lub_l;
unfold cast_lub_r.
apply binary_float_eqb_eq in FEQ.
rewrite FEQ in EINV. 
apply binary_float_equiv_sym.
unfold BDIV, BMULT, BINOP. 
simpl; unfold cast_lub_l;
unfold cast_lub_r. rewrite <- IHe1; rewrite <- IHe2.
rewrite ?positive_nat_N.  
rewrite ?N2Z.inj_pos.
{ apply Bdiv_mult_inverse_equiv ; try apply EINV.
- apply cast_finite; simpl; auto;
eapply type_lub_right.
- apply Bexact_inverse_correct in EINV.
destruct EINV as (A & B & C & D & E). 
apply is_finite_strict_finite in B.  apply B.
}
- simpl; unfold cast_lub_l;
unfold cast_lub_r; clear FEQ. 
apply binary_float_eq_equiv.
rewrite <- IHe1; rewrite <- IHe2.
reflexivity. 
} } simpl; reflexivity. 
}
- { match goal with
|- binary_float_equiv (fval env (if ?b then _ else _)) _ =>
destruct b eqn:FEQ
end.
- rewrite ?andb_true_iff in FEQ; 
unfold cast_lub_l;
unfold cast_lub_r.
apply binary_float_eqb_eq in FEQ.
rewrite FEQ in EINV. 
clear FEQ. 
simpl in EINV.
{ apply binary_float_equiv_eq in IHe1.
- simpl. rewrite <- IHe1. rewrite <- IHe2. 
apply binary_float_equiv_sym.
{ apply Bdiv_mult_inverse_equiv; try apply EINV.
- apply cast_finite; simpl; auto.
apply type_lub_right.
- apply Bexact_inverse_correct in EINV.
destruct EINV as (A & B & C & D & E). 
apply is_finite_strict_finite in B; apply B.
}
- simpl; reflexivity.
}
- clear FEQ. { match goal with
|- binary_float_equiv (fval env (if ?b then _ else _)) _ =>
destruct b eqn:FEQ
end.
- rewrite ?andb_true_iff in FEQ; 
unfold cast_lub_l;
unfold cast_lub_r.
apply binary_float_eqb_eq in FEQ.
rewrite FEQ in EINV. 
clear FEQ. 
simpl in EINV.
{ apply binary_float_equiv_eq in IHe1.
- simpl. rewrite <- IHe1. rewrite <- IHe2. 
rewrite ?positive_nat_N.  
rewrite ?N2Z.inj_pos.
apply binary_float_equiv_sym.
{ apply Bdiv_mult_inverse_equiv; try apply EINV.
- apply cast_finite; simpl; auto.
apply type_lub_right.
- apply Bexact_inverse_correct in EINV.
destruct EINV as (A & B & C & D & E). 
apply is_finite_strict_finite in B; apply B.
}
- simpl; reflexivity. 
}
- { apply binary_float_equiv_eq in IHe1.
- simpl. rewrite <- IHe1. rewrite <- IHe2. 
apply binary_float_eq_equiv; reflexivity.
- simpl; reflexivity.
} } }
- { match goal with                              (* IHe1 nan *)
|- binary_float_equiv (fval env (if ?b then _ else _)) _ =>
destruct b eqn:FEQ
end.
- rewrite ?andb_true_iff in FEQ; 
unfold cast_lub_l;
unfold cast_lub_r.
apply binary_float_eqb_eq in FEQ.
rewrite FEQ in EINV. 
apply binary_float_equiv_sym.
simpl; unfold cast_lub_l;
unfold cast_lub_r. rewrite <- IHe2.
{ apply Bdiv_mult_inverse_equiv2.
(* prove lemma cast preserves equiv *)
Admitted.

Lemma fshift_div_correct env e:
  fval env (fshift_div env e) = eq_rect_r _ (fval env e) (fshift_type_div env e).
Proof.
  apply binary_float_eqb_eq.
  apply binary_float_eqb_eq_strong.
  apply fshift_div_correct'.
Qed.


Definition is_zero_expr (env: forall ty, V -> ftype ty) (e: FPLang.expr)
 : bool :=  
match (fval env e) with
| Binary.B754_zero _ _ b1 => true
| _ => false
end.

Fixpoint is_nan_expr (env: forall ty, V -> ftype ty) (e: expr)
{struct e}: bool := 
  match e with
    | Const ty f => Binary.is_nan _ _ f
    | Var ty i => Binary.is_nan _ _ (env ty i)
    | Binop b e1 e2 =>
        match b with (Rounded2 DIV None) => 
          let be1':= is_zero_expr env e1 in 
          let be2':= is_zero_expr env e2 in
          be1' || be2'
          | _ => 
            let be1':= is_nan_expr env e1 in 
            let be2':= is_nan_expr env e2 in
            be1' || be2' end
    | Unop b e1 => 
        match b with (Rounded1 SQRT None) => 
          Binary.Bsign _ _ (fval env e)
        |_ => is_nan_expr env e1 end
  end.

Lemma is_nan_plus (env: forall ty, V -> ftype ty) (e1 e2:FPLang.expr):
Binary.is_nan _ _ (fval env e1) = false -> 
Binary.is_nan _ _ (fval env e2) = false -> 
Binary.is_nan _ _ (fval env (Binop (Rounded2 PLUS None) e1 e2)) = false.
Proof.
intros.
simpl.
set (x1 := fval env e1) in *; clearbody x1.
set (x2 := fval env e2) in *; clearbody x2.
set (t1 := type_of_expr e1) in *; clearbody t1.
set (t2 := type_of_expr e2) in *; clearbody t2.
unfold cast_lub_l, cast_lub_r.
change (Z.max _ _) with (femax (type_lub t1 t2)).
set (t := type_lub t1 t2).
unfold BPLUS, BINOP.
assert (Binary.is_nan _ _ (cast t t1 x1) = false) by (apply is_nan_cast; auto).
assert (Binary.is_nan _ _ (cast t t2 x2) = false) by (apply is_nan_cast; auto).
set (y1 := cast t t1 x1) in *; clearbody y1.
set (y2 := cast t t2 x2) in *; clearbody y2.
clearbody t.
clear x1 H x2 H0 t1 t2.
destruct y1; try discriminate; destruct y2; try discriminate; try reflexivity.
unfold Binary.Bplus.
destruct (eqb _ _); reflexivity.
unfold Binary.Bplus.
destruct (eqb _ _); try reflexivity.
(*  OOPS!  Adding +infinity to -infinity is a nan *)
admit.
unfold Binary.Bplus.
apply is_nan_normalize.
Admitted.

Lemma is_nan_minus (env: forall ty, V -> ftype ty) (e1 e2:FPLang.expr):
Binary.is_nan _ _ (fval env e1) = false -> 
Binary.is_nan _ _ (fval env e2) = false -> 
Binary.is_nan _ _ (fval env (Binop (Rounded2 MINUS None) e1 e2)) = false.
Proof.
Admitted.

Lemma is_nan_mult (env: forall ty, V -> ftype ty) (e1 e2:FPLang.expr):
Binary.is_nan _ _ (fval env e1) = false -> 
Binary.is_nan _ _ (fval env e2) = false -> 
Binary.is_nan _ _ (fval env (Binop (Rounded2 MULT None) e1 e2)) = false.
Proof.
Admitted.


Lemma is_nan_expr_correct_binop (env: forall ty : type, V -> ftype ty) (e1 e2:FPLang.expr):
forall b : binop, 
 b <> Rounded2 DIV None ->
 Binary.is_nan (fprec (type_of_expr e1)) (femax (type_of_expr e1)) (fval env e1)
  || Binary.is_nan (fprec (type_of_expr e2)) (femax (type_of_expr e2))  (fval env e2) =
 Binary.is_nan (fprec (type_of_expr (Binop b e1 e2)))
  (femax (type_of_expr (Binop b e1 e2))) (fval env (Binop b e1 e2)).
Admitted.

Lemma is_nan_expr_correct_unop (env: forall ty : type, V -> ftype ty)  (e: expr):
forall u : unop, 
 u <> Rounded1 SQRT None ->
Binary.is_nan (fprec (type_of_expr e)) (femax (type_of_expr e)) (fval env e) =
Binary.is_nan (fprec (type_of_expr (Unop u e)))
  (femax (type_of_expr (Unop u e))) (fval env (Unop u e)).
Proof.
Admitted.

Lemma is_nan_correct_sqrt (env: forall ty : type, V -> ftype ty)  (e: expr):
Binary.Bsign (fprec (Datatypes.id (type_of_expr e)))
  (femax (Datatypes.id (type_of_expr e))) (Bsqrt (type_of_expr e) (fval env e)) =
Binary.is_nan (fprec (Datatypes.id (type_of_expr e)))
  (femax (Datatypes.id (type_of_expr e))) (Bsqrt (type_of_expr e) (fval env e)).
Admitted.

Lemma is_nan_div_correct env (e1 e2: expr):
is_zero_expr env e1 || is_zero_expr env e2 =
Binary.is_nan (fprec (type_of_expr (Binop (Rounded2 DIV None) e1 e2)))
  (femax (type_of_expr (Binop (Rounded2 DIV None) e1 e2)))
  (fval env (Binop (Rounded2 DIV None) e1 e2)).
Admitted.

Lemma is_nan_expr_correct env (e: expr):
is_nan_expr env e = 
Binary.is_nan _ _ (fval env e).
Proof. 
induction e.
- simpl; auto.
- simpl; auto.
-
 unfold is_nan_expr; fold is_nan_expr.
 rewrite IHe1, IHe2; clear IHe1 IHe2.
 pose proof (binop_eqb_eq b (Rounded2 DIV None)).
 destruct (binop_eqb b (Rounded2 DIV None)).
 +
   rewrite (proj1 H) by auto.
   apply is_nan_div_correct.
 +
    assert (b <> Rounded2 DIV None).
    intro. subst. destruct H; auto.
    rewrite <- is_nan_expr_correct_binop by auto.
    destruct b; try congruence. destruct op, knowl; try congruence; auto.
-
  unfold is_nan_expr; fold is_nan_expr.
  rewrite IHe; clear IHe.
 pose proof (unop_eqb_eq u (Rounded1 SQRT None)).
 destruct (unop_eqb u (Rounded1 SQRT None)).
 +
 rewrite (proj1 H) by auto.
  apply is_nan_correct_sqrt.
 +
  assert (u <> Rounded1 SQRT None).
  intro. subst. destruct H; auto.
  rewrite <-  is_nan_expr_correct_unop by auto.
  destruct u; try congruence. destruct op, knowl; try congruence; auto.
Qed. 

(* Erasure of rounding annotations *)

Fixpoint erase (e: FPLang.expr (V := V)) {struct e}: FPLang.expr :=
  match e with
    | Binop (Rounded2 u k) e1 e2 => Binop (Rounded2 u None) (erase e1) (erase e2)
    | Binop SterbenzMinus e1 e2 => Binop (Rounded2 MINUS None) (erase e1) (erase e2)
    | Binop (PlusZero minus_ _) e1 e2 => Binop (Rounded2 (if minus_ then MINUS else PLUS) None) (erase e1) (erase e2)
    | Unop (Rounded1 u k) e => Unop (Rounded1 u None) (erase e)
    | Unop (CastTo u _) e => Unop (CastTo u None) (erase e)
    | Unop u e => Unop u (erase e)
    | _ => e
  end.

Lemma erase_type e: type_of_expr (erase e) = type_of_expr e.
Proof.
  induction e; simpl; auto.
  {
    destruct b; simpl; intuition congruence.
  }
  destruct u; simpl; intuition congruence.
Defined. (* required because of eq_rect_r *)

Lemma erase_correct' env e:
 binary_float_eqb (fval env (erase e)) (fval env e) = true.
Proof.
  induction e; simpl.
  {
    apply binary_float_eqb_eq; reflexivity.
  }
  {
    apply binary_float_eqb_eq; reflexivity.
  }
  {
    unfold cast_lub_r.
    unfold cast_lub_l.
    revert IHe1.
    revert IHe2.
    generalize (fval env e1).
    generalize (fval env e2).
    destruct b; simpl; unfold cast_lub_r, cast_lub_l;
      generalize (fval env (erase e1));
      generalize (fval env (erase e2));
      repeat rewrite erase_type;
      intros until 2;
      apply binary_float_eqb_eq in IHe1; subst;
      apply binary_float_eqb_eq in IHe2; subst;
      apply binary_float_eqb_eq;
      try reflexivity.
    destruct minus; reflexivity.
  }
  revert IHe.
  generalize (fval env e).
  destruct u; simpl;
  generalize (fval env (erase e));
  repeat rewrite erase_type;
  intros until 1;
  apply binary_float_eqb_eq in IHe; subst;
  apply binary_float_eqb_eq;
  reflexivity.
Qed.

Lemma erase_correct env e:
  fval env (erase e) = eq_rect_r _ (fval env e) (erase_type e).
Proof.
  apply binary_float_eqb_eq.
  apply binary_float_eqb_eq_strong.
  apply erase_correct'.
Qed.

End WITHVARS.
