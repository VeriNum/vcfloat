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

Require Export vcfloat.Float_lemmas.
Require Export vcfloat.FPLang.
Require Import vcfloat.klist.
Import RAux.
Import vcfloat.IEEE754_extra.
(*Import compcert.lib.Floats. *)
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
  destruct r1; destruct r2; simpl; try intuition congruence.
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

Section WITHNAN.
Context {NANS: Nans}.

Definition fcval_nonrec {ty} (e: expr ty): option (ftype ty) :=
  match e with
    | Const _ f => Some f
    | _ => None
  end.

Lemma fcval_nonrec_correct ty e:
  forall (v: ftype ty), fcval_nonrec e = Some v ->
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

Fixpoint fcval {ty} (e: expr ty) {struct e}: expr ty :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fcval e1 in
      let e'2 := fcval e2 in
      match option_pair_of_options (fcval_nonrec e'1) (fcval_nonrec e'2) with
        | Some (v1, v2) =>
          Const _ (fop_of_binop b _ v1 v2)
        | None => Binop b e'1 e'2
      end
    | Unop b e =>
      let e' := fcval e in
      match fcval_nonrec e' with
        | Some v => Const _ (fop_of_unop b _ v)
        | _ => Unop b e'
      end
    | Func _ ff el =>
       let fix fcval_klist {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (fcval h) (fcval_klist tl)
          end 
          in Func _ ff (fcval_klist el)
    | _ => e
  end.

Fixpoint fcval_klist  {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (fcval h) (fcval_klist tl)
          end.

Lemma fcval_correct_bool env ty (e: expr ty):
  binary_float_eqb (fval env (fcval e)) (fval env e) = true.
Proof.
  induction e; simpl.
  - apply binary_float_eqb_eq. reflexivity.
  - apply binary_float_eqb_eq. reflexivity.
  - destruct (option_pair_of_options (fcval_nonrec (fcval e1)) (fcval_nonrec (fcval e2))) eqn:OPT.
    +
      destruct p.
      apply option_pair_of_options_correct in OPT.
      destruct OPT as (V1 & V2).
      apply fcval_nonrec_correct with (env := env) in V1.
      apply fcval_nonrec_correct with (env := env) in V2.
      simpl.
      subst.
      revert IHe1 IHe2.
      generalize (fval env (fcval e1)).
      generalize (fval env e1).
      generalize (fval env (fcval e2)).
      generalize (fval env e2).
      intros ? ? ? ? .
      repeat rewrite binary_float_eqb_eq.
      congruence.
    +
    clear OPT.
    simpl.
    revert IHe1 IHe2.
    generalize (fval env (fcval e1)).
    generalize (fval env e1).
    generalize (fval env (fcval e2)).
    generalize (fval env e2).
    intros ? ? ? ? .
    repeat rewrite binary_float_eqb_eq.
    congruence.
 -
  destruct (fcval_nonrec (fcval e)) eqn:V_.
  +
    apply fcval_nonrec_correct with (env := env) in V_.
    subst.
    revert IHe.
    generalize (fval env (fcval e)).
    generalize (fval env e).
    intros ? ? .
    simpl.
    repeat rewrite binary_float_eqb_eq.
    congruence.
  +
  simpl.
  revert IHe.
  generalize (fval env (fcval e)).
  generalize (fval env e).
  intros ? ? .
  simpl.
  repeat rewrite binary_float_eqb_eq.
  congruence.
-
    revert IHe.
    generalize (fval env (fcval e)).
    generalize (fval env e).
    intros ? ? .
    simpl.
    repeat rewrite binary_float_eqb_eq.
    congruence.  
- 
 match goal with |- binary_float_eqb _ (?G _ _ _) = _ =>  change G with (@fval_klist _ env (ftype ty)) end.

  set (func := ff_func _). clearbody func.
  set (tys := ff_args f4) in *. clearbody tys.
  fold (@fcval_klist tys args).
 rewrite binary_float_eqb_eq.
  induction args. simpl. reflexivity.
 simpl.
  apply Kforall_inv in IH. destruct IH.
  apply binary_float_eqb_eq in H. rewrite H.
  specialize (IHargs H0). apply IHargs.
Qed.

Lemma fcval_correct env ty (e: expr ty):
  fval env (fcval e) = (fval env e).
Proof.
  apply binary_float_eqb_eq.
  apply fcval_correct_bool.
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

Definition fshift_mult {ty} (e'1 e'2: expr ty ) :=
        match fcval_nonrec e'1 with
          | Some c1 =>
            if Binary.Bsign _ _ c1 then Binop (Rounded2 MULT None) e'1 e'2
            else
            let n := to_power_2 c1 in
            if binary_float_eqb c1 (B2 ty (Z.of_N n))
            then Unop (Exact1 (Shift n false)) e'2
            else
              let n := to_inv_power_2 c1 in
              if binary_float_eqb c1 (B2 ty (- Z.pos n))
              then Unop (Rounded1 (InvShift n false) None) e'2
              else Binop (Rounded2 MULT None) e'1 e'2
          | None =>
            match fcval_nonrec e'2 with
              | Some c2 =>
                if Binary.Bsign _ _ c2 then Binop (Rounded2 MULT None) e'1 e'2
                else
                let n := to_power_2 c2 in
                if binary_float_eqb c2 (B2 ty (Z.of_N n))
                then Unop (Exact1 (Shift n true)) e'1
                else
                  let n := to_inv_power_2 c2 in
                  if binary_float_eqb c2 (B2 ty (- Z.pos n))
                  then Unop (Rounded1 (InvShift n true) None) e'1
                  else Binop (Rounded2 MULT None) e'1 e'2
              | None => Binop (Rounded2 MULT None) e'1 e'2
            end                  
        end.

Fixpoint fshift {ty} (e: expr ty) {struct e}: expr ty :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fshift e1 in
      let e'2 := fshift e2 in
      if binop_eqb b (Rounded2 MULT None)
      then fshift_mult e'1 e'2
      else Binop b e'1 e'2
    | Unop b e => Unop b (fshift e)
    | Func _ ff el =>
       let fix fshift_klist {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (fshift h) (fshift_klist tl)
          end 
          in Func _ ff (fshift_klist el)
    | _ => e
  end.

Lemma fshift_correct' env ty (e: expr ty):
 binary_float_eqb (fval env (fshift e)) (fval env e) = true.
Proof.
  induction e; simpl; unfold fshift_mult.
- apply binary_float_eqb_eq. reflexivity.
- apply binary_float_eqb_eq. reflexivity.
- (* binop case *)
  assert (DEFAULT:    binary_float_eqb
         (fval env (Binop b (fshift e1) (fshift e2)))
         (fop_of_binop b _ (fval env e1) (fval env e2))
     = true). {
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
  destruct (binop_eqb b (Rounded2 MULT None)) eqn:ISMULT; [ | auto].
  apply binop_eqb_eq in ISMULT.
  subst.
  destruct (fcval_nonrec (fshift e1)) eqn:E1; [ |  destruct (fcval_nonrec (fshift e2)) eqn:E2].
  +  
     destruct (Binary.Bsign _ _ _); [ auto | ].
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
   *    revert IHe2.
          generalize (fval env (fshift e2)).
          revert FEQ.
          intros.
          apply binary_float_eqb_eq in IHe2.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
    *
        clear FEQ.
        match goal with
            |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
            destruct b eqn:FEQ
        end;
          simpl.
       --
          revert IHe2.
          generalize (fval env (fshift e2)).
          revert FEQ.
          intros.
          apply binary_float_eqb_eq in IHe2.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
       --
        clear FEQ.
        revert IHe2.
        generalize (fval env (fshift e2)).
        intros.
        apply binary_float_eqb_eq in IHe2.
        subst.
        apply binary_float_eqb_eq.
        reflexivity.
   +
     destruct (Binary.Bsign _ _ _); [ auto | ].
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
    *    revert IHe1.
          generalize (fval env (fshift e1)).
          revert FEQ.
          intros.
          apply binary_float_eqb_eq in IHe1.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
    *
        clear FEQ.
        match goal with
            |- binary_float_eqb (fval env (if ?b then _ else _)) _ = _ =>
            destruct b eqn:FEQ
        end;
          simpl.
       --
          revert IHe1.
          generalize (fval env (fshift e1)).
          revert FEQ.
          intros.
          apply binary_float_eqb_eq in IHe1.
          subst.
          apply binary_float_eqb_eq in FEQ.
          rewrite <- FEQ.
          apply binary_float_eqb_eq.
          reflexivity.
     --
        clear FEQ.
        revert IHe1.
        generalize (fval env (fshift e1)).
        intros.
        apply binary_float_eqb_eq in IHe1.
        subst.
        apply binary_float_eqb_eq.
        reflexivity.
  +
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
- (* unop case *)
  revert IHe.
  generalize (fval env (fshift e)).
  intros.
  apply binary_float_eqb_eq in IHe.
  subst.
  apply binary_float_eqb_eq.
  reflexivity.
- (* cast case *)
  revert IHe.
  generalize (fval env (fshift e)).
  intros.
  apply binary_float_eqb_eq in IHe.
  subst.
  apply binary_float_eqb_eq.
  reflexivity.
-
  set (func := ff_func _). clearbody func.
  set (tys := ff_args f4) in *. clearbody tys.
 rewrite binary_float_eqb_eq.
  induction args. simpl. reflexivity.
 simpl.
  apply Kforall_inv in IH. destruct IH.
  apply binary_float_eqb_eq in H. rewrite H.
  specialize (IHargs H0). apply IHargs.
Qed.

Lemma fshift_correct env ty (e: expr ty):
  fval env (fshift e) =  (fval env e).
Proof.
  apply binary_float_eqb_eq.
  apply fshift_correct'.
Qed.

Definition to_power_2_pos {prec emax} (x: Binary.binary_float prec emax) :=
  let y := B2BigQ x in
  let '(q, r) := BigZ.div_eucl (Bnum y) (BigZ.Pos (Bden y)) in
  Pos.of_nat (blog (BigZ.of_Z 2) O q (Z.to_nat emax))
.

Fixpoint fshift_div {ty} (e: expr ty) {struct e}: expr ty :=
  match e with
    | Binop b e1 e2 =>
      let e'1 := fshift_div e1 in
      let e'2 := fshift_div e2 in
      if binop_eqb b (Rounded2 DIV None) then
      match (fcval_nonrec e'2) with
            | Some c2 =>
                match (Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) c2) with
                  | Some z' => 
                    let n1 := to_power_2_pos c2 in
                    if binary_float_eqb z' (B2 ty (Z.neg n1))
                    then Unop (Rounded1 (InvShift n1 true) None) e'1
                    else
                    let n2 := to_inv_power_2 c2 in
                    if binary_float_eqb z' (B2 ty (Z.pos n2))
                    then Unop (Exact1 (Shift (N.of_nat (Pos.to_nat n2)) true)) e'1
                    else Binop b e'1 e'2
                  | None => Binop b e'1 e'2
                end
             | None => Binop b e'1 e'2
         end
      else
        Binop b e'1 e'2
    | Unop b e => Unop b (fshift_div e)
    | Func _ ff el =>
       let fix fshift_div_klist {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (fshift_div h) (fshift_div_klist tl)
          end 
          in Func _ ff (fshift_div_klist el)
    | _ => e
  end.

Fixpoint fshift_div_klist {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (fshift_div h) (fshift_div_klist tl)
          end.

Local Lemma binary_float_equiv_refl : forall prec emax x, 
   @binary_float_equiv prec emax x x.
Proof. intros. destruct x; hnf; try reflexivity. repeat split; reflexivity. Qed.
Local Hint Resolve binary_float_equiv_refl : vcfloat.

Local Hint Extern 2 (Binary.is_finite _ _ _ = true) => 
   match goal with EINV: Bexact_inverse _ _ _ _ _ = Some _ |- _ =>
             apply is_finite_strict_finite; 
         apply (Bexact_inverse_correct _ _ _ _ _ _ EINV)
   end : vcfloat.

Lemma cast_preserves_bf_equiv tfrom tto (b1 b2: Binary.binary_float (fprec tfrom) (femax tfrom)) :
  binary_float_equiv b1 b2 -> 
  binary_float_equiv (@cast _ tto tfrom b1) (@cast _ tto tfrom b2).
Proof.
intros.
destruct b1, b2; simpl; inversion H; clear H; subst; auto;
try solve [apply binary_float_eq_equiv; auto].
-
unfold cast; simpl.
destruct (type_eq_dec tfrom tto); auto.
unfold eq_rect.
destruct e1.
reflexivity.
reflexivity.
-
destruct H1; subst m0 e1.
unfold cast; simpl.
destruct (type_eq_dec tfrom tto); subst; auto.
unfold eq_rect.
simpl. split; auto.
apply binary_float_eq_equiv.
f_equal.
Qed.

Import Binary.

Lemma binary_float_equiv_BDIV ty (b1 b2 b3 b4: binary_float (fprec ty) (femax ty)):
binary_float_equiv b1 b2 ->
binary_float_equiv b3 b4 ->
binary_float_equiv (BDIV b1 b3) (BDIV b2 b4).
Proof.
intros.
destruct b1.
all : (destruct b3; destruct b4; try contradiction; try discriminate).
all :
match goal with 
  |- context [
binary_float_equiv (BDIV ?a ?b)
 _] =>
match a with 
| B754_nan _ _ _ _ _ => destruct b2; try contradiction; try discriminate;
    cbv [BDIV BINOP Bdiv build_nan binary_float_equiv]; try reflexivity
  | _ => apply binary_float_equiv_eq in H; try rewrite <- H;
  match b with 
  | B754_nan _ _ _ _ _ => 
      cbv [BDIV BINOP Bdiv build_nan binary_float_equiv]; try reflexivity
  | _ => apply binary_float_equiv_eq in H0; try rewrite <- H0;
          try apply binary_float_eq_equiv; try reflexivity
end
end
end.
Qed.

Lemma binary_float_equiv_BOP ty (b1 b2 b3 b4: binary_float (fprec ty) (femax ty)):
forall b: binop ,
binary_float_equiv b1 b2 ->
binary_float_equiv b3 b4 ->
binary_float_equiv (fop_of_binop b ty b1 b3) (fop_of_binop b ty b2 b4).
Proof.
intros.
destruct b1.
all :
match goal with 
  |- context [
binary_float_equiv (fop_of_binop ?bo ?ty ?a ?b)
 _] =>
match a with 
| B754_zero _ _ _ => 
apply binary_float_equiv_eq in H; try simpl; try reflexivity
| B754_infinity _ _ _ => 
apply binary_float_equiv_eq in H; try simpl; try reflexivity
| B754_finite _ _ _ _ _ _ => 
apply binary_float_equiv_eq in H; try simpl; try reflexivity
| _ => try simpl
end
end.
all :(
destruct b2; simpl in H; try contradiction; try discriminate;
destruct b3; destruct b4; try contradiction; try discriminate;
match goal with 
  |- context [ binary_float_equiv (fop_of_binop ?bo ?ty ?a ?b)  _] =>
match a with 
| B754_nan _ _ _ _ _  => try simpl
| _ => try (rewrite H); 
      match b with 
      | B754_nan _ _ _ _ _ => try simpl
      | _ => try (apply binary_float_equiv_eq in H);
             try (rewrite H);
             try (apply binary_float_equiv_eq in H0);
             try (rewrite H0);
             try (apply binary_float_eq_equiv); try reflexivity
      end
end
end
).

all: (
try (destruct b);
try( cbv [fop_of_binop]);
try destruct op;
try (cbv [fop_of_rounded_binop]);
try (cbv [fop_of_rounded_binop]);
try(
match goal with 
|- context [ binary_float_equiv ((if ?m then ?op1 else ?op2)  ?ty ?a ?b) _] =>
destruct m
end;
cbv [BPLUS BMINUS BDIV BMULT BINOP 
Bplus Bminus Bdiv Bmult build_nan binary_float_equiv]);
try (reflexivity)
).
Qed.

Lemma binary_float_equiv_UOP ty (b1 b2: binary_float (fprec ty) (femax ty)):
forall u: unop ,
binary_float_equiv b1 b2 ->
binary_float_equiv (fop_of_unop u ty b1) (fop_of_unop u ty b2).
Proof.
intros.
destruct b1.
all: (
match goal with |- context [binary_float_equiv 
(fop_of_unop ?u ?ty ?a) _]  =>
match a with 
| Binary.B754_nan _ _ _ _ _  => simpl 
| _ => try apply binary_float_equiv_eq in H; try rewrite  <-H; 
  try apply binary_float_eq_equiv; try reflexivity
end
end).
destruct b2; try discriminate; try contradiction.
try (destruct u).
all: (
try( cbv [fop_of_unop fop_of_exact_unop]);
try destruct op;
try destruct o;
try destruct ltr;
try (cbv [fop_of_rounded_unop]);
try (cbv [Bsqrt Binary.Bsqrt build_nan]);
try reflexivity
).
+ destruct (B2 ty (- Z.pos pow)) .
all: try (
 (cbv [ BMULT BINOP Bmult build_nan]);
 reflexivity).
+ destruct (B2 ty (Z.of_N pow)).
all: try (
 (cbv [ BMULT BINOP Bmult build_nan]);
 reflexivity).
Qed.


Local Hint Resolve cast_preserves_bf_equiv : vcfloat.
Local Hint Resolve binary_float_eq_equiv : vcfloat.
Local Ltac inv  H := inversion H; clear H; subst.

Lemma general_eqb_neq:
  forall {A} {f: A -> A -> bool} (H: forall x y, f x y = true <-> x=y),
    forall x y,  f x y = false <-> x<>y.
Proof.
intros.
rewrite <- H.
destruct (f x y); split; congruence.
Qed.

Local Ltac destruct_ifb H := 
    lazymatch type of H with
    | forall x y, ?f x y = true <-> x=y =>
         match goal with |- context [if f ?b ?c then _ else _] =>
                  let FEQ := fresh "FEQ" in 
                     destruct (f b c) eqn:FEQ; 
             [apply H in FEQ; rewrite FEQ in *
             | apply (general_eqb_neq H) in FEQ]
         end
    | _ => fail "argument of destruct_ifb must be a lemma of the form,  forall x y, ?f x y = true <-> x=y"
    end.

Local Lemma ifb_cases_lem: 
  forall {A} {f: A -> A -> bool} (H: forall x y, f x y = true <-> x=y),
  forall (x y: A) {B} (b c: B) (P: B -> Prop),
  (x=y -> P b) -> (x<>y -> P c) ->
  P (if f x y then b else c).
Proof.
intros.
destruct (f x y) eqn:?H.
apply H in H2; auto.
apply (general_eqb_neq H) in H2; auto.
Qed.

Local Lemma binary_float_eqb_lem1:
  forall prec emax b c {A} (y z: A) (P: A -> Prop) ,
    (b=c -> P y) -> P z ->
    P (if @binary_float_eqb prec emax prec emax b c then y else z).
Proof.
intros.
 destruct (binary_float_eqb b c) eqn:H1.
 apply H. apply binary_float_eqb_eq. auto. auto.
Qed.

Local Ltac binary_float_eqb_cases := 
  let H := fresh in 
  apply binary_float_eqb_lem1; [intro H; rewrite H in *; clear H | ].

Local Lemma Bmult_div_inverse_equiv ty:
  forall x y z: (Binary.binary_float (fprec ty) (femax ty)),
  Binary.is_finite _ _ y = true ->
  Binary.is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  binary_float_equiv
  (Binary.Bmult _ _ _ (fprec_lt_femax ty) (mult_nan ty) BinarySingleNaN.mode_NE x z) 
  (Binary.Bdiv _ _ _ (fprec_lt_femax ty) (div_nan ty) BinarySingleNaN.mode_NE x y) .
Proof. intros. apply binary_float_equiv_sym; apply Bdiv_mult_inverse_equiv; auto. Qed.

Theorem Bmult_div_inverse_equiv2 ty:
  forall x1 x2 y z: (Binary.binary_float (fprec ty) (femax ty)),
  binary_float_equiv x1 x2 ->
  Binary.is_finite _ _ y = true ->
  Binary.is_finite _ _ z = true ->
  Bexact_inverse (fprec ty) (femax ty) (fprec_gt_0 ty) (fprec_lt_femax ty) y = Some z -> 
  binary_float_equiv
  (Binary.Bmult _ _ _ (fprec_lt_femax ty) (mult_nan ty) BinarySingleNaN.mode_NE x2 z)
  (Binary.Bdiv _ _ _ (fprec_lt_femax ty) (div_nan ty) BinarySingleNaN.mode_NE x1 y) .
Proof. intros. apply binary_float_equiv_sym; apply Bdiv_mult_inverse_equiv2; auto. Qed.

Lemma uncast_finite_strict:
  forall t t2 f, Binary.is_finite_strict (fprec t) (femax t) (@cast _ t t2 f) = true ->
        Binary.is_finite_strict _ _ f = true.
Proof.
intros.
unfold cast in H.
destruct (type_eq_dec t2 t).
subst. 
destruct f; simpl in *; auto.
destruct f; simpl in *; auto.
Qed.

Lemma is_finite_strict_not_nan:
  forall prec emax f, Binary.is_finite_strict prec emax f = true -> Binary.is_nan prec emax f = false.
Proof.
intros.
destruct f; auto; discriminate.
Qed.

Lemma binary_float_equiv_nan:
  forall prec emax f1 f2,
  Binary.is_nan prec emax f1= true  ->
   Binary.is_nan prec emax f2 = true ->
    binary_float_equiv f1 f2.
Proof.
intros.
destruct f1; inv H.
destruct f2; inv H0.
apply I.
Qed.

Lemma binary_float_equiv_nan1:
  forall b prec emax f1 f2,
  Binary.is_nan prec emax f1= b  ->
    binary_float_equiv f1 f2 ->
   Binary.is_nan prec emax f2 = b.
Proof.
intros.
destruct b.
destruct f1; inv H.
destruct f2; inv H0.
reflexivity.
destruct f1; inv H;
destruct f2; inv H0;
reflexivity.
Qed.

Lemma binary_float_equiv_nan2:
  forall b prec emax f1 f2,
  Binary.is_nan prec emax f2= b  ->
    binary_float_equiv f1 f2 ->
   Binary.is_nan prec emax f1 = b.
Proof.
intros.
destruct b.
destruct f2; inv H.
destruct f1; inv H0.
reflexivity.
destruct f2; inv H;
destruct f1; inv H0;
reflexivity.
Qed.

Lemma Bmult_nan1:
  forall fprec emax H H0 H1 H2 f1 f2,
   Binary.is_nan fprec emax f1 = true -> Binary.is_nan _ _  (Binary.Bmult _ _ H H0 H1 H2 f1 f2) = true.
Proof.
intros.
destruct f1; try discriminate. reflexivity.
Qed.

Lemma Bmult_nan2:
  forall fprec emax H H0 H1 H2 f1 f2,
   Binary.is_nan fprec emax f2 = true -> Binary.is_nan _ _  (Binary.Bmult _ _ H H0 H1 H2 f1 f2) = true.
Proof.
intros. 
destruct f2; try discriminate.
destruct f1; reflexivity.
Qed.

Lemma Bdiv_nan1:
  forall fprec emax H H0 H1 H2 f1 f2,
   Binary.is_nan fprec emax f1 = true -> Binary.is_nan _ _  (Binary.Bdiv _ _ H H0 H1 H2 f1 f2) = true.
Proof.
intros.
destruct f1; try discriminate. reflexivity.
Qed.

Lemma Bdiv_nan2:
  forall fprec emax H H0 H1 H2 f1 f2,
   Binary.is_nan fprec emax f2 = true -> Binary.is_nan _ _  (Binary.Bdiv _ _ H H0 H1 H2 f1 f2) = true.
Proof.
intros. 
destruct f2; try discriminate.
destruct f1; reflexivity.
Qed.

Local Hint Resolve Bmult_nan1 Bmult_nan2 Bdiv_nan1 Bdiv_nan2 cast_is_nan : vcfloat.

Ltac unfold_fval := cbv [fop_of_unop fop_of_exact_unop fop_of_rounded_unop
                      fop_of_binop fop_of_rounded_binop 
                      BDIV BMULT BINOP BPLUS BMINUS].

Ltac binary_float_equiv_tac :=
      repeat (first [ apply Bmult_div_inverse_equiv
                          | apply Bmult_div_inverse_equiv2
                          | apply cast_preserves_bf_equiv;
                               (assumption || apply binary_float_equiv_sym; assumption)
                          | apply binary_float_equiv_BDIV
                          | apply binary_float_equiv_BOP];
                   auto with vcfloat).

Ltac binary_float_equiv_tac2 env e1 e2 :=
         simpl;
         repeat match goal with
                    | H: binary_float_equiv _ _ |- _ => revert H 
                    end;
         generalize (fval env (fshift_div  e1));
         generalize (fval env (fshift_div  e2));
         intros;
         binary_float_equiv_tac.

Lemma fshift_div_correct' env ty (e: expr ty) :
 binary_float_equiv (fval env (fshift_div e))  (fval env e).
Proof.
induction e; cbn [fshift_div]; auto with vcfloat; unfold fval; fold (@fval _ env ty);
try (set (x1 := fval env e1) in *; clearbody x1);
try (set (x2 := fval env e2) in *; clearbody x2).
- (* binop case *)
 apply (ifb_cases_lem binop_eqb_eq); intros ?OP; subst;
               [ | binary_float_equiv_tac2 env e1 e2].
 destruct (fcval_nonrec (fshift_div e2)) eqn:E2;
               [ | binary_float_equiv_tac2 env e1 e2].
 destruct (fshift_div e2); try discriminate.
 simpl in *|-. inv E2.
 simpl in IHe2; intros; subst.
 destruct (Bexact_inverse _ ) eqn:EINV; [ | clear EINV];
               [ | binary_float_equiv_tac2 env e1 e2]. 
 assert (H := proj1 (Bexact_inverse_correct _ _ _ _ _ _ EINV)).
 destruct f; inversion H; clear H.
 rewrite positive_nat_N.
 destruct (fcval_nonrec (fshift_div e1)) eqn:E1.
 + destruct (fshift_div e1); try discriminate.
     simpl in f, E1, IHe1; inv E1.
     intros.
     destruct (Binary.is_nan _ _ f) eqn:?NAN.
    * pose proof (binary_float_equiv_nan1 true _ _ _ _ NAN IHe1).
       apply binary_float_equiv_nan; repeat binary_float_eqb_cases;
       unfold fval; unfold_fval; auto with vcfloat.
    * apply binary_float_equiv_eq in IHe1; [ subst | assumption].
       apply binary_float_equiv_eq in IHe2; [ subst | reflexivity ].
       repeat binary_float_eqb_cases;
       binary_float_equiv_tac.
+ repeat binary_float_eqb_cases; [ .. | clear EINV];
    simpl;
    try (apply binary_float_equiv_eq in IHe2; [subst x2 | reflexivity]);
    try revert EINV;
    revert IHe1;
    generalize (fval env (fshift_div e1));
    intros;
    (destruct (Binary.is_nan _ _ f) eqn:?NAN;
       [pose proof (binary_float_equiv_nan1 true _ _ _ _ NAN IHe1);
        unfold fval; fold (@fval _ env ty); unfold_fval;
        apply binary_float_equiv_nan; auto with vcfloat
      | apply binary_float_equiv_eq in IHe1; [ subst | assumption ];
        binary_float_equiv_tac; pose (y:=True)
     ]).
- (* unop case *)
 simpl.
revert IHe.
generalize (fval env (fshift_div e)).
intros.
apply binary_float_equiv_UOP; apply IHe.
-
  set (func := ff_func _). clearbody func.
  set (tys := ff_args f4) in *. clearbody tys.
  fold @fshift_div_klist.
 match goal with |- binary_float_equiv (?G _ _ _) _ =>  change G with (@fval_klist _ env (ftype ty)) end.
  induction args. simpl. apply binary_float_equiv_refl.
 simpl.
  apply Kforall_inv in IH. destruct IH.
  specialize (IHargs H0).
  simpl in func.
  specialize (IHargs (func (fval env k))).
  eapply binary_float_equiv_trans; [ | apply IHargs].
  admit.  (* This looks OK but will take some work.  Perhaps use the Morphism congruence
                 system for binary_float_equiv; or (maybe) base this whole thing on binary_float_eqb
               instead of binary_float_equiv? *)
Admitted.

Lemma fshift_div_correct env ty (e: expr ty):
  Binary.is_nan _ _ (fval env (fshift_div e)) = false -> 
  fval env (fshift_div e) = fval env e.
Proof.
  intros.
  apply binary_float_equiv_eq. 
  - apply fshift_div_correct'.
  - apply H. 
Qed.

Definition is_zero_expr (env: forall ty, FPLang.V -> ftype ty) {ty} (e: expr ty)
 : bool :=  
match (fval env e) with
| Binary.B754_zero _ _ b1 => true
| _ => false
end.

(* Erasure of rounding annotations *)

Fixpoint erase {ty} (e: expr ty) {struct e}: expr ty :=
  match e with
    | Binop (Rounded2 u k) e1 e2 => Binop (Rounded2 u None) (erase e1) (erase e2)
    | Binop SterbenzMinus e1 e2 => Binop (Rounded2 MINUS None) (erase e1) (erase e2)
    | Binop (PlusZero minus_ _) e1 e2 => Binop (Rounded2 (if minus_ then MINUS else PLUS) None) (erase e1) (erase e2)
    | Unop (Rounded1 u k) e => Unop (Rounded1 u None) (erase e)
    | Cast _ u _ e => Cast _ u None (erase e)
    | Unop u e => Unop u (erase e)
    | Func _ ff args => 
       let fix erase_klist {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (erase h) (erase_klist tl)
          end 
       in Func _ ff (erase_klist args)
    | _ => e
  end.

Fixpoint erase_klist  {tys: list type} (l': klist expr tys) {struct l'}: klist expr tys :=
          match  l' in (klist _ l) return (klist expr l)
          with
          | Knil => Knil
          | Kcons h tl => Kcons (erase h) (erase_klist tl)
          end.

Lemma erase_correct' env ty (e: expr ty):
 binary_float_eqb (fval env (erase e)) (fval env e) = true.
Proof.
  induction e; simpl.
  - apply binary_float_eqb_eq; reflexivity.
  - apply binary_float_eqb_eq; reflexivity.
  - revert IHe1.
    revert IHe2.
    generalize (fval env e1).
    generalize (fval env e2).
    destruct b; simpl;
      generalize (fval env (erase e1));
      generalize (fval env (erase e2));
      repeat rewrite erase_type;
      intros until 2;
      apply binary_float_eqb_eq in IHe1; subst;
      apply binary_float_eqb_eq in IHe2; subst;
      apply binary_float_eqb_eq;
      try reflexivity.
    destruct minus; reflexivity.
  -
  revert IHe.
  generalize (fval env e).
  destruct u; simpl;
  generalize (fval env (erase e));
  intros until 1;
  apply binary_float_eqb_eq in IHe; subst;
  apply binary_float_eqb_eq;
  reflexivity.
- 
  revert IHe.
  generalize (fval env e).
  generalize (fval env (erase e));
  intros until 1;
  apply binary_float_eqb_eq in IHe; subst;
  apply binary_float_eqb_eq;
  reflexivity.
-
  set (func := ff_func _). clearbody func.
  set (tys := ff_args f4) in *. clearbody tys.
  fold @erase_klist.
 match goal with |- binary_float_eqb (?G _ _ _) _ = true =>  change G with (@fval_klist _ env (ftype ty)) end.
  induction args. simpl. apply binary_float_eqb_eq. reflexivity.
 simpl.
  apply Kforall_inv in IH. destruct IH.
  specialize (IHargs H0).
  specialize (IHargs (func (fval env k))).
  apply binary_float_eqb_eq in IHargs.  
  apply binary_float_eqb_eq.
  rewrite <- IHargs. f_equal.
  apply binary_float_eqb_eq in H. rewrite H. auto.
Qed.

Lemma erase_correct env ty (e: expr ty):
  fval env (erase e) = fval env e.
Proof.
  apply binary_float_eqb_eq.
  apply erase_correct'.
Qed.

End WITHNAN.
