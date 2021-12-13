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
        end; simpl.
        {
          unfold Datatypes.id.
          congruence.
        }
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


(* BEGIN - AEK additions for converting expressions withe exact division
by powers of two. *)
Definition to_power_2_pos {prec emax} (x: Binary.binary_float prec emax) :=
  let y := B2BigQ x in
  let '(q, r) := BigZ.div_eucl (Bnum y) (BigZ.Pos (Bden y)) in
  Pos.of_nat (blog (BigZ.of_Z 2) O q (Z.to_nat emax))
.


Fixpoint fshift_div env (e: FPLang.expr) {struct e}: FPLang.expr :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fshift_div env e1 in
      let e'2 := fshift_div env e2 in
      if binop_eqb b (Rounded2 DIV None) then
      let ty := type_lub (type_of_expr e'1) (type_of_expr e'2) in
      match (fcval_nonrec e'2) with (* match 1 *)
            | Some c2' =>
                let c2 := cast ty _ c2' in
                match (Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) c2) with (* match 2 *)
                  | Some z' => 
                    let n1 := to_power_2_pos c2 in
                    if ((Z.eqb (fprec ty) 24 && Z.eqb (femax ty) 128) || (Z.eqb (fprec ty) 53 && Z.eqb (femax ty) 1024)) then
                      if binary_float_eqb z' (B2 ty (Z.neg n1)) then 
                        Unop (Exact1 (InvShift n1 true)) (Unop (CastTo ty None) e'1)
                      else
                        let n2 := to_inv_power_2 c2 in
                          if binary_float_eqb z' (B2 ty (Z.pos n2)) then 
                            Unop (Exact1 (Shift (N.of_nat (Pos.to_nat n2)) true)) (Unop (CastTo ty None) e'1)
                          else Binop b e'1 e'2
                    else
                      let fin := (eqb (Binary.is_finite _ _ (fval env e'1)) true) in 
                        if (binary_float_eqb z' (B2 ty (Z.neg n1))) && fin then 
                          Unop (Exact1 (InvShift n1 true)) (Unop (CastTo ty None) e'1)
                        else
                        let n2 := to_inv_power_2 c2 in
                          if (binary_float_eqb z' (B2 ty (Z.pos n2))) && fin then
                            Unop (Exact1 (Shift (N.of_nat (Pos.to_nat n2)) true)) (Unop (CastTo ty None) e'1)
                          else Binop b e'1 e'2
                  | None => Binop b e'1 e'2 (* match 2 *)
                end
             | None => Binop b e'1 e'2
         end (* match 1 *)
      else
        Binop b e'1 e'2
    | Unop b e => Unop b (fshift_div env e)
    | _ => e
  end.


Lemma fshift_type_div env e:
  type_of_expr (fshift_div env e) = type_of_expr e.
Proof.
   induction e; simpl; auto.
  {
    destruct (binop_eqb b (Rounded2 DIV None)) eqn:EQ.
    {
      apply binop_eqb_eq in EQ.
      subst.
      simpl.
      destruct (fcval_nonrec (fshift_div env e2)).
      {
        revert IHe2 f. 
        generalize (fshift_div env e2).
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
          end;
            simpl.
{
          unfold Datatypes.id.
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
}
        simpl.
        congruence.
}
congruence. 
Defined. 

Lemma fshift_div_correct' env e:
 binary_float_eqb (fval env (fshift_div env e)) (fval env e) = true.
Proof.
  induction e; cbn [fshift_div].
  {
    apply binary_float_eqb_eq. reflexivity.
  }
  {
    apply binary_float_eqb_eq. reflexivity.
  }
  {
    destruct (binop_eqb b (Rounded2 DIV None)) eqn:ISDIV.
    {
      apply binop_eqb_eq in ISDIV.
      subst.
      destruct (fcval_nonrec (fshift_div env e1)) eqn:E1.
          { (* case Some e1*)
              generalize (fshift_type_div env e1).
        destruct (fshift_div env e1); try discriminate.
        simpl in E1.
        simpl in f.
        inversion E1; clear E1; subst.
        simpl in IHe1.
        simpl.
        intros.
        subst.
        apply binary_float_eqb_eq in IHe1.
        subst.
   destruct (fcval_nonrec (fshift_div env e2)) eqn:E2.
      {
        generalize (fshift_type_div env e2).
        destruct (fshift_div env e2); try discriminate.
        simpl in E2.
        simpl in f.
        inversion E2; clear E2; subst.
        simpl in IHe2.
        simpl.
        intros.
        subst.
        apply binary_float_eqb_eq in IHe2.
        subst.
             destruct (Bexact_inverse _ ) eqn:EINV. 
              {
                match goal with
                  |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
                  destruct b eqn:FEQ
                end.
                {
                  simpl. 
                  rewrite ?orb_true_iff in FEQ. 
                  rewrite ?andb_true_iff in FEQ. destruct FEQ. 
destruct H. 
apply eqb_eq in H. 


destruct H. 
apply Z.eqb_eq in H. 
                  unfold cast_lub_l.
                  unfold cast_lub_r.
destruct H. 
apply eqb in H0. 
                  apply type_eqb_eq in H.

                  set (ty:=(type_lub (type_of_expr e1) (type_of_expr e2))) in *.
                  change (Z.max (femax (type_of_expr e1)) (femax (type_of_expr e2))) with (femax ty) in *.
                  set (x:=(cast ty (type_of_expr e1) (fval env e1))) in *.
                  set (y:=(cast ty (type_of_expr e2) (fval env e2))) in *.
                  match goal with
                    |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
                    destruct b eqn:FEQ
                  end. 
                  {
                    simpl. apply binary_float_eqb_eq in FEQ.
                    apply binary_float_eqb_eq. 
                    unfold BMULT, BDIV, BINOP. symmetry. 
                    rewrite FEQ in EINV. 
                    pose proof Float32.div_mul_inverse.
assert (type_eq_dec float32 Tsingle).
unfold float32, Bits.binary32 in H0.
cbv [type_of_expr].
Search "binary_float".
                    apply Float32.div_mul_inverse; auto.
                  {    
                    apply Bexact_inverse_correct in EINV.
                    destruct EINV as (A & B & C & D & E).
                    apply is_finite_strict_finite; auto.
                    } 
                    apply Bexact_inverse_correct in EINV.
                    destruct EINV as (A & B & C & D & E).
                    apply is_finite_strict_finite; auto.
                    }
clear FEQ.
              match goal with
                  |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
                  destruct b eqn:FEQ
                end.
                   {
                      simpl. rewrite ?andb_true_iff in FEQ; destruct FEQ as [FEQ FIN]. 
                      unfold cast_lub_l.
                      unfold cast_lub_r.
                      apply binary_float_eqb_eq in FEQ.
                      apply eqb_prop in FIN.
                      set (ty:=(type_lub (type_of_expr e1) (type_of_expr e2))) in *.
                      change (Z.max (femax (type_of_expr e1)) (femax (type_of_expr e2))) with (femax ty) in *.
                      pose proof type_lub_left (type_of_expr e1) (type_of_expr e2).
                      pose proof cast_finite (type_of_expr e1) ty H (fval env e1) FIN.
                      set (x:=(cast ty (type_of_expr e1) (fval env e1))) in *.
                      set (y:=(cast ty (type_of_expr e2) (fval env e2))) in *.
                      apply binary_float_eqb_eq. 
                      unfold BMULT, BDIV, BINOP. symmetry. 
                      replace (Z.of_N (N.of_nat (Pos.to_nat (to_inv_power_2 y)))) with  (Z.pos (to_inv_power_2 y)) in * by lia.
                      rewrite FEQ in EINV. 
                      apply Bdiv_mult_inverse_finite; auto.
                      {    
                        apply Bexact_inverse_correct in EINV.
                        destruct EINV as (A & B & C & D & E).
                        apply is_finite_strict_finite; auto.
                      } 
                        apply Bexact_inverse_correct in EINV.
                        destruct EINV as (A & B & C & D & E).
                        apply is_finite_strict_finite; auto.
                     }
                       apply binary_float_eqb_eq.
                       reflexivity.
}
                       apply binary_float_eqb_eq.
                       reflexivity.
} (*case None e2, Some e1*)

      revert IHe2.
      simpl.
      generalize (fval env (fshift_div env e2)).
      repeat rewrite fshift_type_div.
      intros.
      apply binary_float_eqb_eq in IHe2. subst.
      apply binary_float_eqb_eq.
      reflexivity.
} (*case None e1*)
   destruct (fcval_nonrec (fshift_div env e2)) eqn:E2.
      {
        generalize (fshift_type_div env e2).
        destruct (fshift_div env e2); try discriminate.
        simpl in E2.
        simpl in f.
        inversion E2; clear E2; subst.
        simpl in IHe2.
        simpl.
        intros.
        subst.
        apply binary_float_eqb_eq in IHe2.
        subst.
 destruct (Bexact_inverse _ ) eqn:EINV. 
              {
                match goal with
                  |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
                  destruct b eqn:FEQ
                end.
                {
                simpl. rewrite ?andb_true_iff in FEQ; destruct FEQ as [FEQ FIN]. 
                      unfold cast_lub_l.
                      unfold cast_lub_r.
                      revert IHe1. revert FIN. 
           apply binary_float_eqb_eq in FEQ. subst. revert EINV.
                      generalize (fval env (fshift_div env e1)).
                      rewrite fshift_type_div.
intros. 
apply binary_float_eqb_eq in IHe1. subst.
apply eqb_prop in FIN.
                   apply binary_float_eqb_eq.
                  set (ty:=(type_lub (type_of_expr e1) (type_of_expr e2))) in *.
                  change (Z.max (femax (type_of_expr e1)) (femax (type_of_expr e2))) with (femax ty) in *.
                  pose proof type_lub_left (type_of_expr e1) (type_of_expr e2).
                  pose proof cast_finite (type_of_expr e1) ty H (fval env e1) FIN.
                  set (x:=(cast ty (type_of_expr e1) (fval env e1))) in *.
                  set (y:=(cast ty (type_of_expr e2) (fval env e2))) in *.
                  unfold BMULT, BDIV, BINOP. symmetry. 
                  apply Bdiv_mult_inverse_finite; auto.
                  {    
                    apply Bexact_inverse_correct in EINV.
                    destruct EINV as (A & B & C & D & E).
                    apply is_finite_strict_finite; auto.
                    } 
                    apply Bexact_inverse_correct in EINV.
                    destruct EINV as (A & B & C & D & E).
                    apply is_finite_strict_finite; auto.
                    }
clear FEQ.
         match goal with
                  |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
                  destruct b eqn:FEQ
                end.
                   {
                simpl. rewrite ?andb_true_iff in FEQ; destruct FEQ as [FEQ FIN]. 
                      unfold cast_lub_l.
                      unfold cast_lub_r.
                      revert IHe1. revert FIN. 
           apply binary_float_eqb_eq in FEQ. subst. revert EINV.
                      generalize (fval env (fshift_div env e1)).
                      rewrite fshift_type_div.
intros. 
apply binary_float_eqb_eq in IHe1. subst.
apply eqb_prop in FIN.
                   apply binary_float_eqb_eq.
                  set (ty:=(type_lub (type_of_expr e1) (type_of_expr e2))) in *.
                  change (Z.max (femax (type_of_expr e1)) (femax (type_of_expr e2))) with (femax ty) in *.
                  pose proof type_lub_left (type_of_expr e1) (type_of_expr e2).
                  pose proof cast_finite (type_of_expr e1) ty H (fval env e1) FIN.
                  set (x:=(cast ty (type_of_expr e1) (fval env e1))) in *.
                  set (y:=(cast ty (type_of_expr e2) (fval env e2))) in *.
                  unfold BMULT, BDIV, BINOP. symmetry. 
                  apply Bdiv_mult_inverse_finite; auto.
                  {    
                    apply Bexact_inverse_correct in EINV.
                    destruct EINV as (A & B & C & D & E).
                    apply is_finite_strict_finite; auto.
                    } 
{
                    apply Bexact_inverse_correct in EINV.
                    destruct EINV as (A & B & C & D & E).
                      replace (Z.of_N (N.of_nat (Pos.to_nat (to_inv_power_2 y)))) with  (Z.pos (to_inv_power_2 y)) in * by lia.
                    apply is_finite_strict_finite; auto.
                    }
replace (Z.of_N (N.of_nat (Pos.to_nat (to_inv_power_2 y)))) with  (Z.pos (to_inv_power_2 y)) in * by lia.
auto.
}
clear FEQ.
                      simpl. 
                      unfold cast_lub_l.
                      unfold cast_lub_r.
                      revert IHe1. revert EINV. revert b.
                      generalize (fval env (fshift_div env e1)).
                      rewrite fshift_type_div.
intros. 
apply binary_float_eqb_eq in IHe1. subst.
                   apply binary_float_eqb_eq. reflexivity.
}
clear EINV.
 simpl. 
                      unfold cast_lub_l.
                      unfold cast_lub_r.
                      revert IHe1. 
                      generalize (fval env (fshift_div env e1)).
                      rewrite fshift_type_div.
intros. 
apply binary_float_eqb_eq in IHe1. subst.
                   apply binary_float_eqb_eq. reflexivity.
}
     clear E1 E2.
      revert IHe1 IHe2.
      simpl.
      generalize (fval env (fshift_div env e1)).
      generalize (fval env (fshift_div env e2)).
      repeat rewrite fshift_type_div.
      intros.
      apply binary_float_eqb_eq in IHe1. subst.
      apply binary_float_eqb_eq in IHe2. subst.
      apply binary_float_eqb_eq.
      reflexivity.
    }
    clear ISDIV.
    revert IHe1 IHe2.
    simpl.
      generalize (fval env (fshift_div env e1)).
      generalize (fval env (fshift_div env e2)).
      repeat rewrite fshift_type_div.
    intros.
    apply binary_float_eqb_eq in IHe1. subst.
    apply binary_float_eqb_eq in IHe2. subst.
    apply binary_float_eqb_eq.
    reflexivity.
  }
simpl.
  revert IHe.
      generalize (fval env (fshift_div env e)).
  rewrite fshift_type_div.
  intros.
  apply binary_float_eqb_eq in IHe.
  subst.
  apply binary_float_eqb_eq.
  reflexivity.
Qed.

Lemma fshift_div_correct env e:
  fval env (fshift_div env e) = eq_rect_r _ (fval env e) (fshift_type_div env e).
Proof.
  apply binary_float_eqb_eq.
  apply binary_float_eqb_eq_strong.
  apply fshift_div_correct'.
Qed.
(* END - A.E.K additions for converting expressions withe exact division
by powers of two. *)

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
