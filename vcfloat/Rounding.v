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

VCFloat: core and annotated languages for floating-point operations.
*)

Require Import Interval.Tactic.
From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra. (* lib.Floats. *)
Require compcert.lib.Maps.  
Require Import JMeq.
Require Coq.MSets.MSetAVL.
Require vcfloat.Fprop_absolute.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Require Export vcfloat.FPCore vcfloat.FPLang.
Require Import vcfloat.klist.
Import Bool.

Import Coq.Lists.List ListNotations.

Local Open Scope R_scope.

Module MSET := MSetAVL.Make(Pos).

Definition mget {U} (m: Maps.PMap.t U) t := Maps.PMap.get t m.
Definition mset {U} m t (u: U) := Maps.PMap.set t u m.
Definition mempty {U} := @Maps.PMap.init U.
Lemma mget_set {U}: forall m t t' (u: U),
                mget (mset m t u) t' = if Pos.eq_dec t' t then u else mget m t'.
Proof. intros.
   unfold mget, mset.
    rewrite Maps.PMap.gsspec.
    destruct (Coqlib.peq t' t); destruct (Pos.eq_dec t' t); congruence.
Qed.

Lemma mget_empty {U}: forall t (u: U), mget (mempty u) t = u.
Proof. intros. apply Maps.PMap.gi. Qed.

Lemma finite_errors_ex {U}  (t: U) n:
  forall errors,
  exists m,
    forall i,
      mget m i = if Pos.ltb i n then errors i else t.
Proof.
  remember (Nat.pred (Pos.to_nat n)) as k.
 revert n Heqk.
 induction k; intros.
 - exists (mempty t).
    intros.
    rewrite mget_empty.
    assert (n=1%positive) by lia. subst.
    destruct (Pos.ltb_spec i 1); auto; lia.
 -
  specialize (IHk (Pos.pred n) ltac:(lia) errors).
  destruct IHk.
  exists (mset x (Pos.pred n) (errors (Pos.pred n))).
  intros.
  rewrite mget_set.
  rewrite H.
  destruct (Pos.eq_dec _ _). subst.
  destruct (Pos.ltb_spec (Pos.pred n) n); try lia. auto.
  destruct (Pos.ltb_spec i n);
  destruct (Pos.ltb_spec i (Pos.pred n)); auto; lia.
Qed.  

Section WITH_NAN.
Context {NANS: Nans}.

Inductive ratom `{coll: collection}: Type :=
| RConst (_: Defs.float Zaux.radix2)
| RVar (ty: type) (IN: incollection ty) (_: FPLang.V)
| RError (_: positive)
.

Unset Elimination Schemes.
Inductive rexpr `{coll: collection}: Type :=
  | RAtom (_: ratom)
  | RUnop (o: Tree.unary_op) (e: rexpr)
  | RBinop (o: Tree.binary_op) (e1 e2: rexpr)
  | RFunc ty (ff: floatfunc_package ty) (args: klist (fun _ => rexpr) (ff_args ff)) 
.

Set Elimination Schemes.
Lemma rexpr_ind `{coll: collection}:
  forall P : rexpr -> Prop,
  (forall (r : ratom), P (RAtom r)) ->
  (forall o e1, P e1 -> P (RUnop o e1)) ->
  (forall o e1 e2, P e1 -> P e2 -> P (RBinop o e1 e2)) ->
  (forall (ty : type) (ff : floatfunc_package ty)
    (args : klist (fun _ => rexpr) (ff_args ff))
      (IH: Kforall (fun ty => P) args),
      P  (RFunc ty ff args)) ->
  forall (e : rexpr), P e.
Proof.
intros.
refine (
(fix F (e : rexpr) {struct e} : P e :=
  match e as e0 return (P e0) with
  | RAtom a => H a
  | RUnop o e1 => H0 o e1 (F e1)
  | RBinop b e1 e2 => H1 b e1 e2 (F e1) (F e2)
  | RFunc ty ff args => _
    end) e).
apply H2.
clear - F ff.
set (tys := ff_args ff) in *. clearbody tys.
induction args.
constructor.
constructor.
apply F.
apply IHargs.
Qed.

Fixpoint reval `{coll: collection} (e: rexpr) (env: environ) (eenv: positive -> R): R :=
  match e with
    | RAtom (RConst q) => F2R _ q
    | RAtom (RVar ty IN n) => FT2R (env ty IN n)
    | RAtom (RError n) => eenv n
    | RUnop o e => Prog.unary Prog.real_operations o (reval e env eenv)
    | RBinop o e1 e2 => Prog.binary Prog.real_operations o (reval e1 env eenv) (reval e2 env eenv)
    | RFunc ty ff args => 
    let fix reval_klist {tys: list type} (l': klist (fun _ => rexpr) tys) (f: function_type (map RR tys) R) {struct l'}: R :=
          match l' in (klist _ l)  return (function_type (map RR l) R -> R)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => reval_klist tl (f0 (reval h env eenv))
          end f 
          in reval_klist args (ff_realfunc ff)
  end.

Definition reval_klist `{coll: collection} {T} (env: environ) (eenv: positive -> R) :=
 fix reval_klist {tys: list type} (l': klist (fun _ => rexpr) tys) (f: function_type (map RR tys) T) {struct l'}: T :=
          match l' in (klist _ l)  return (function_type (map RR l) T -> T)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => reval_klist tl (f0 (reval h env eenv))
          end f. 

Fixpoint max_error_var `{coll: collection} (e: rexpr): positive :=
  match e with
    | RAtom (RError n) =>Pos.succ n
    | RUnop _ e => max_error_var e
    | RBinop _ e1 e2 => Pos.max (max_error_var e1) (max_error_var e2)
    | RFunc ty ff args => 
       let fix max_error_var_klist (tys: list type) (es: klist (fun _ => rexpr) tys) : positive :=
        match es with
        | Knil => 1%positive
        | Kcons h tl => Pos.max (max_error_var h) (max_error_var_klist _ tl)
       end
       in max_error_var_klist (ff_args ff) args
    | _ => 1%positive
  end.

Definition max_error_var_klist `{coll: collection} :=
  fix max_error_var_klist (tys: list type) (es: klist (fun _ => rexpr) tys) : positive :=
        match es with
        | Knil => 1%positive
        | Kcons h tl => Pos.max (max_error_var h) (max_error_var_klist _ tl)
       end.

Lemma reval_error_ext `{coll: collection} eenv1 env eenv2 e:
  (forall i, (i < max_error_var e)%positive ->
                 eenv1 i = eenv2 i) ->
  reval e env eenv1 = reval e env eenv2.
Proof.
  induction e; simpl;
 try (intros; f_equal; 
     match goal with IH:_ -> ?a |- ?g => unify a g; eapply IH; eauto end;
     intros; apply H; lia).
  - destruct r; auto. intros. apply H. lia.
 - intros.
    change (reval_klist env eenv1  args (ff_realfunc ff) =
                   reval_klist env eenv2 args (ff_realfunc ff)).
    fold (max_error_var_klist) in H.
    destruct ff; simpl in *.
    rename ff_args into tys.
    rename ff_realfunc into f.
    clear - args H IH.
    revert f H IH.
    induction args; simpl; intros; auto.
    apply Kforall_inv in IH. destruct IH.
    rewrite <- H0.
    apply IHargs; auto.
    intros. apply H; lia.
    intros. apply H; lia.
Qed.

Lemma reval_error_klist_ext `{coll: collection}:
  forall (eenv1 eenv2  : positive -> R)
    (env : environ)
    (tys : list type)
   (args : klist (fun _ : type => rexpr) tys)
  (f : function_type (map RR tys) R),
(forall i : positive,
 (i < max_error_var_klist tys args)%positive -> eenv1 i = eenv2 i) ->
Kforall
  (fun (_ : type) (e : rexpr) =>
   (forall i : positive, (i < max_error_var e)%positive -> eenv1 i = eenv2 i) ->
   reval e env eenv1 = reval e env eenv2) args ->
  reval_klist env eenv1 args f = reval_klist env eenv2 args f.
Proof.
    induction args; simpl; intros; auto.
    apply Kforall_inv in H0. destruct H0.
    rewrite <- H0.
    apply IHargs; auto.
    intros. apply H; lia.
    intros. apply H; lia.
Qed.

Definition MSHIFT := Maps.PMap.t  (type * rounding_knowledge').

Definition error_bound ty_k :=
  / 2 * Raux.bpow Zaux.radix2
  match ty_k with
    | (ty, Unknown') => 0
    | (ty, Normal') => (- fprec ty + 1)
    | (ty, Denormal') =>  (3 - femax ty - fprec ty)
    | (ty, Denormal2') =>   (3 - femax ty - fprec ty)
  end.

Definition errors_bounded
    (shift: MSHIFT) (errors: positive -> R) := 
   forall i, (Rabs (errors i) <= error_bound (mget shift i))%R.

Lemma error_bound_nonneg ty_k:
  0 <= error_bound ty_k.
Proof.
    unfold error_bound. destruct ty_k.
    apply Rmult_le_pos; try lra.
    apply Raux.bpow_ge_0.
Qed.

Definition make_rounding `{coll: collection}
           (si: positive)
           (shift: MSHIFT)
           (kn:  rounding_knowledge') (ty: type) (x: rexpr):
  (rexpr * (positive * MSHIFT))
  :=
    match kn with
      | Unknown' =>
        let d := si in
        let es1 := mset shift d (ty, Normal') in
        let e := Pos.succ d in
        let es2 := mset es1 e (ty, Denormal') in
        (
          RBinop Tree.Add
                 (RBinop Tree.Mul x
                         (RBinop Tree.Add (RAtom (RConst fone))
                                 (RAtom (RError d)))
                 )
                 (RAtom (RError e))
          , (Pos.succ e, es2)
        )

      | Normal' =>
        let d := si in
        let es1 := mset shift d (ty, Normal') in
        (
          RBinop Tree.Mul x
                 (RBinop Tree.Add (RAtom (RConst fone))
                         (RAtom (RError d))
                 )
          , (Pos.succ d, es1)
        )
      | Denormal' => 
        let e := si in
        let es1 := mset shift e (ty, Denormal') in
        (
          RBinop Tree.Add x
                 (RAtom (RError e))
          , (Pos.succ e, es1)
        )
      | Denormal2' => 
        let e := si in
        let es1 := mset shift e (ty, Denormal2') in
        (
          RBinop Tree.Add x
                 (RAtom (RError e))
          , (Pos.succ e, es1)
        )
    end.

Lemma make_rounding_shift_incr
      `{coll: collection}
      si
      shift
      kn ty x
      y si' shift':
  make_rounding si shift kn ty x = (y, (si', shift')) ->
  (si <= si')%positive
.
Proof.
  unfold make_rounding.
  destruct kn;
  inversion 1; subst; auto; lia.
Qed.

Definition same_upto {T} (si: positive) (s1 s2: positive ->T) :=
  forall i, (i < si)%positive -> s2 i = s1 i.

Lemma make_rounding_shift_unchanged
      `{coll: collection}
      si
      shift
      kn ty x
      y si' shift':
  make_rounding si shift kn ty x = (y, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
  unfold make_rounding, same_upto.
  destruct kn.
  inversion 1; subst; intros.
  repeat rewrite mget_set.
  destruct (Pos.eq_dec i (Pos.succ si)); auto;
  destruct (Pos.eq_dec i si); auto;
  try (exfalso; lia).
all: try (    inversion 1; subst; intros;
    rewrite mget_set;
    destruct (Pos.eq_dec i si); auto;
    exfalso; lia).
Qed.

Lemma make_rounding_shift_le
      `{coll: collection}
      si
      shift
      kn ty x
      y si' shift':
  make_rounding si shift kn ty x = (y, (si', shift')) ->
    (max_error_var x <= si)%positive ->
    (max_error_var y <= si')%positive.
Proof.
  unfold make_rounding.
  destruct kn;
  inversion 1; subst; simpl; intros;
  repeat (apply Pos.max_lub; auto; lia).
Qed.

Definition rounding_cond ty k x :=
  match k with
    | Unknown' => True
    | Normal' =>
      Raux.bpow Zaux.radix2 (3 - femax ty - 1) <= Rabs x
    | Denormal' =>
      Rabs x < Raux.bpow Zaux.radix2 (3 - femax ty)
    | Denormal2' => True
  end.

Lemma make_rounding_correct `{coll: collection}
      si shift kn ty x y si' shift':
  make_rounding si shift (round_knowl_denote kn) ty x = (y, (si', shift')) ->
  (max_error_var x <= si)%positive ->
  forall errors1, errors_bounded shift errors1 ->
  forall env,
    rounding_cond ty (round_knowl_denote kn) (reval x env errors1) ->
  forall choice,
  exists errors2,
    same_upto si errors1 errors2
    /\
    reval y env errors2 =
    Generic_fmt.round
      Zaux.radix2
      (FLT_exp (3 - femax ty - fprec ty) (fprec ty))
      (Generic_fmt.Znearest choice)
      (reval x env errors1)
    /\
    errors_bounded shift' errors2
.  

Proof. 
unfold make_rounding, rounding_cond.
intros.
destruct kn as [ [ | ] | ]; unfold round_knowl_denote in H2.
- (* Normal *)
  replace (3 - femax ty - 1)%Z with (3 - femax ty - fprec ty + fprec ty - 1)%Z in H2 by ring.
  generalize (Relative.relative_error_N_FLT_ex _ _ _ (fprec_gt_0 _) choice _ H2).
  destruct 1 as (eps & Heps & Hround).
  pose (errors2 i := if Pos.eq_dec i si  then eps else errors1 i).
  exists errors2.
  split; [ | split].
  * intro; unfold errors2; intros; destruct (Pos.eq_dec i si); auto; lia.
  * inversion H; clear H; subst.
    simpl reval.
    rewrite Rmult_1_l.
    rewrite <- (reval_error_ext errors1).
   --
     unfold errors2.
     destruct (Pos.eq_dec si si); congruence.
   --  intros; unfold errors2; destruct (Pos.eq_dec i si); auto; exfalso; lia.
  * inversion H; clear H; subst.
    simpl reval.
    intros until i.
    rewrite mget_set.
    intros.
    unfold errors2.
    destruct (Pos.eq_dec i si); auto.
 - (* Denormal *)
  replace (3 - femax ty)%Z with (3 - femax ty - fprec ty + fprec ty)%Z in H2 by ring.
  generalize (Fprop_absolute.absolute_error_N_FLT _ _ (fprec_gt_0 _) _ choice _ H2).
  destruct 1 as (eps & Heps & Hround).
  pose (errors2 i := if Pos.eq_dec i si then eps else errors1 i).
  exists errors2.    
  split; [ | split].
  * intro; unfold errors2; intros; destruct (Pos.eq_dec i si); auto; lia.
  * inversion H; clear H; subst. simpl reval.
    rewrite <- (reval_error_ext errors1).
   -- unfold errors2; destruct (Pos.eq_dec si si); congruence.
   -- intros; unfold errors2; destruct (Pos.eq_dec i si); auto; lia.
  * inversion H; clear H; subst. simpl reval.
     intros until i.
     rewrite mget_set.
     intros.
     unfold errors2.
     destruct (Pos.eq_dec i si); auto.
-  (* None *)
 generalize (Relative.error_N_FLT Zaux.radix2 (3 - femax ty - fprec ty) (fprec ty) (fprec_gt_0 _)  choice (reval x env errors1)).
 destruct 1 as (eps & eta & Heps & Heta & _ & Hround).
 pose (errors2 i := if Pos.eq_dec i (Pos.succ (si)) then eta
                          else if Pos.eq_dec i si then eps else  errors1 i).
 exists errors2.
 split; [ | split].
 + intro.
   unfold errors2.
   intros; destruct (Pos.eq_dec i (Pos.succ si)); try lia; destruct (Pos.eq_dec i si); try lia; auto.
 + inversion H; clear H; subst.
    simpl reval.
    rewrite Rmult_1_l.     
  rewrite <- (reval_error_ext errors1).
  *
    unfold errors2.
    destruct (Pos.eq_dec si (Pos.succ si)); try (exfalso; lia).
    destruct (Pos.eq_dec si si); try congruence.
    destruct (Pos.eq_dec (Pos.succ si) (Pos.succ si)); congruence.
  *
   intros.
   unfold errors2.
   destruct (Pos.eq_dec i (Pos.succ si)); try lia.
   destruct (Pos.eq_dec i si); try lia.
   auto.
 +
   inversion H; clear H; subst.
    simpl reval.
  intros until i.
  repeat rewrite mget_set.
  intros.
  subst errors2.
 specialize (H1 i).
 repeat destruct (Pos.eq_dec _ _); subst; auto; lia.
Qed.

Definition Rbinop_of_rounded_binop o :=
  match o with
    | PLUS => Tree.Add
    | MULT => Tree.Mul
    | MINUS => Tree.Sub
    | DIV => Tree.Div
  end.

Definition rnd_of_binop `{coll: collection}
           si
           (shift: MSHIFT)
           (ty: type)
           (o: binop) (r1 r2: rexpr)
  :=
    match o with
      | SterbenzMinus => (RBinop Tree.Sub r1 r2, (si, shift))
      | PlusZero minus zero_left =>
        ((
            if zero_left
            then
              if minus
              then RUnop Tree.Neg r2
              else r2
            else
              r1
          ), (si, shift))       
      | Rounded2 o' k => 
        make_rounding si shift (round_knowl_denote k) ty                      
                      (RBinop (Rbinop_of_rounded_binop o') r1 r2)
    end.

Definition rnd_of_cast `{coll: collection}
           si
           (shift: MSHIFT)
           (tyfrom tyto: type)
           (k: rounding_knowledge')
           (r: rexpr) :=
  if type_leb tyfrom tyto
  then
    (r, (si, shift))
  else
    make_rounding si shift k tyto r
.

Definition Runop_of_rounded_unop `{coll: collection} ty o :=
  match o with
    | SQRT => RUnop Tree.Sqrt
    | InvShift n _ => RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (- Z.pos n)))))
  end.

Definition Runop_of_exact_unop `{coll: collection} ty o :=
  match o with
    | Abs => RUnop Tree.Abs
    | Opp => RUnop Tree.Neg
    | Shift n _ => RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (Z.of_N n)))))
  end.

Definition rnd_of_unop `{coll: collection} 
           si
           (shift: MSHIFT)
           (ty: type)
           (o: unop) (r: rexpr)
  :=
    match o with
      | Rounded1 (InvShift n ltr) (Some Normal) =>
                  (Runop_of_rounded_unop ty (InvShift n ltr) r, (si, shift))
      | Rounded1 (InvShift n _) _ =>
           make_rounding si shift Denormal2' ty
              ((RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (- Z.pos n)))))) r)
      | Rounded1 o k =>
        make_rounding si shift (round_knowl_denote k) ty
                      (Runop_of_rounded_unop ty o r)
      | Exact1 o => (Runop_of_exact_unop ty o r, (si, shift))
    end. 

Definition rel_error `{coll: collection} r n d :=
     RBinop Tree.Mul r 
        (RBinop Tree.Add  (RAtom (RConst fone))
           (RBinop Tree.Mul (RAtom (RConst (Float radix2 (Z.of_N n) 0))) (RAtom (RError d)))).

Definition abs_error `{coll: collection} r n e :=
     RBinop Tree.Add r (RBinop Tree.Mul (RAtom (RConst (Float radix2 (Z.of_N n) 0))) (RAtom (RError e))).

Definition rnd_of_func' `{coll: collection} (si: positive) (shift: MSHIFT) ty (rel abs: N) (r: rexpr) :
           rexpr * (positive * MSHIFT) :=
        let d := si in
        let es1 := mset shift d (ty, Normal') in
        let e := Pos.succ d in
        let es2 := mset es1 e (ty, Denormal') in
        (abs_error (rel_error r rel d) abs e, (Pos.succ e, es2)).

Definition rnd_of_func `{coll: collection} (si: positive) (shift: MSHIFT) (ty: type) 
                      ff (r: klist (fun _ => rexpr) (ff_args ff)) :
          rexpr * (positive * MSHIFT) :=
  rnd_of_func' si shift ty (ff_rel (ff_ff ff)) (ff_abs (ff_ff ff)) (RFunc ty ff r).

Lemma rnd_of_func'_shift_incr `{coll: collection} 
      si
      shift
      ty rel abs x
      y si' shift':
  rnd_of_func' si shift ty rel abs x = (y, (si', shift')) ->
  (si <= si')%positive
.
Proof.
  unfold rnd_of_func';
  inversion 1; subst; auto; lia.
Qed.

Lemma rnd_of_func'_shift_unchanged `{coll: collection} 
      si
      shift
      ty rel abs x
      y si' shift':
  rnd_of_func' si shift ty rel abs x = (y, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
  unfold rnd_of_func', same_upto.
  intros. inversion H; clear H; subst.
  repeat rewrite mget_set;
  repeat destruct (Pos.eq_dec _ _); subst; auto; lia.
Qed.

Lemma rnd_of_func'_shift_le `{coll: collection} 
      si
      shift
      ty rel abs x
      y si' shift':
  rnd_of_func' si shift ty rel abs x = (y, (si', shift')) ->
    (max_error_var x <= si)%positive ->
    (max_error_var y <= si')%positive.
Proof.
  unfold rnd_of_func'.
  inversion 1; subst; simpl; intros;
  repeat (apply Pos.max_lub; auto; lia).
Qed.

Fixpoint rndval `{coll: collection} 
         (si: positive)
         (shift: MSHIFT)
         (ty: type) (e: expr ty) {struct e} : rexpr * (positive * MSHIFT) :=
  match e with
    | Const _ _ f => (RAtom (RConst (B2F f)), (si, shift))
    | Var _ IN i => (RAtom (RVar ty IN i), (si, shift))
    | Binop b e1 e2 =>
      let '(r1, (si1, s1)) := rndval si shift _ e1 in
      let '(r2, (si2, s2)) := rndval si1 s1 _ e2 in
      rnd_of_binop si2 s2 ty b r1 r2
    | Unop b e1 =>
      let '(r1, (si1, s1)) := rndval si shift _ e1 in
      rnd_of_unop si1 s1 ty b r1
    | Cast _ fromty STDto STDfrom k e1 => 
      let '(r1, (si1, s1)) := rndval si shift fromty e1 in
      rnd_of_cast si1 s1 fromty ty (round_knowl_denote k) r1
    | Func _ ff args => 
       let fix rndval_klist (si: positive) (shift: MSHIFT) (tys: list type) (l': klist expr tys) {struct l'}: 
                                (klist (fun _ => rexpr) tys * (positive * MSHIFT))  :=
          match  l' 
          with
          | Knil => (Knil, (si,shift))
          | Kcons h tl => let '(r1, (si1,s1)) := rndval si shift _ h in 
                                    let '(r2, (si2,s2)) := rndval_klist si1 s1 _ tl in
                                      (Kcons r1 r2, (si2,s2))
          end 
          in let '(r1,(si1,s1)) := rndval_klist si shift _ args
               in rnd_of_func si1 s1 _ ff r1
   end.

Definition rndval_klist `{coll: collection} :=
  fix rndval_klist (si: positive) (shift: MSHIFT) {tys: list type} (l': klist expr tys) {struct l'}: 
                                (klist (fun _ => rexpr) tys * (positive * MSHIFT))  :=
          match  l' 
          with
          | Knil => (Knil, (si,shift))
          | Kcons h tl => let '(r1, (si1,s1)) := rndval si shift _ h in 
                                    let '(r2, (si2,s2)) := rndval_klist si1 s1 tl in
                                      (Kcons r1 r2, (si2,s2))
          end.

Lemma rnd_of_binop_shift_incr  `{coll: collection} si shift ty b r1 r2 r si' shift':
  rnd_of_binop si shift ty b r1 r2 = (r, (si', shift')) ->
  (si <= si')%positive.
Proof.
  destruct b; simpl; intros.
  -  eapply make_rounding_shift_incr; eauto.
  -  inversion H; clear H; subst. lia.
  - inversion H; clear H; subst. lia.
Qed.

Lemma rnd_of_binop_shift_le  `{coll: collection} si shift ty b r1 r2 r si' shift':
  rnd_of_binop si shift ty b r1 r2 = (r, (si', shift')) ->
    (max_error_var r1 <= si)%positive ->
    (max_error_var r2 <= si)%positive ->
    (max_error_var r <=  si')%positive.
Proof.
  destruct b; simpl; intros.
 - eapply make_rounding_shift_le; eauto.
    simpl.
    apply Pos.max_lub; auto.
 - inversion H; clear H; subst.
    simpl.
    apply Pos.max_lub; auto.
 - inversion H; clear H; subst.
    destruct zero_left; auto.
    destruct minus; auto.
Qed.

Lemma rnd_of_binop_shift_unchanged  `{coll: collection} si shift ty b r1 r2 r si' shift':
  rnd_of_binop si shift ty b r1 r2 = (r, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
  destruct b; simpl; intros.
  {
    eapply make_rounding_shift_unchanged; eauto.
  }
  {
    congruence.
  }
  {
    congruence.
  }
Qed.

Lemma rnd_of_cast_shift_incr  `{coll: collection} si shift ty ty0 knowl r1 y si' shift':
  rnd_of_cast si shift ty ty0 knowl r1 = (y, (si', shift')) ->
  (si <= si')%positive.
Proof.
  unfold rnd_of_cast.
  destruct (type_leb ty ty0).
  - inversion_clear 1; auto. lia.
  - intros. eapply make_rounding_shift_incr; eauto.
Qed.

Lemma rnd_of_cast_shift_le  `{coll: collection} si shift ty ty0 knowl r1 y si' shift':
  rnd_of_cast si shift ty ty0 knowl r1 = (y, (si', shift')) ->
  (max_error_var r1 <= si)%positive ->
    (max_error_var y <= si')%positive.
Proof.
  unfold rnd_of_cast.
  destruct (type_leb ty ty0).
  - congruence.
  - intros; eapply make_rounding_shift_le; eauto.
Qed.

Lemma rnd_of_cast_shift_unchanged  `{coll: collection} si shift ty ty0 knowl r1 y si' shift':
  rnd_of_cast si shift ty ty0 knowl r1 = (y, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
  unfold rnd_of_cast.
  destruct (type_leb ty ty0).
  - congruence.
  - apply make_rounding_shift_unchanged.
Qed.

Lemma rnd_of_unop_shift_incr `{coll: collection} si shift ty u r1 y si' shift':
  rnd_of_unop si shift ty u r1 = (y, (si', shift')) ->
  (si <= si')%positive.
Proof.
  destruct u; simpl.
- (* Rounded1 *)
  destruct op.
 +
     apply make_rounding_shift_incr.
 + destruct knowl as [ [ | ] | ].
  * (* Some Normal *)
   inversion_clear 1; auto; lia.
  *  apply (make_rounding_shift_incr _ _ Denormal2').
  *  apply (make_rounding_shift_incr _ _ Denormal2').
- (* Exact1 *)
   inversion_clear 1; auto; lia.
Qed.

Lemma rnd_of_unop_shift_le `{coll: collection} si shift ty u r1 y si' shift':
  rnd_of_unop si shift ty u r1 = (y, (si', shift')) ->
  (max_error_var r1 <= si)%positive ->
  (max_error_var y  <=  si')%positive.
Proof.
  destruct u; simpl; intros.
- (* Rounded1 *)
 destruct op.
 + eapply make_rounding_shift_le; eauto.
 + destruct knowl as [ [ | ] | ].
  * (* Some Normal *)
    inversion H; clear H; subst; simpl. lia.
  * eapply (make_rounding_shift_le _ _ Denormal2'); eauto. simpl. lia.
  * eapply (make_rounding_shift_le _ _ Denormal2'); eauto. simpl. lia.
- (* Exact1 *)
    inversion H; clear H; subst; simpl.
    destruct o; simpl; auto. lia.
Qed.

Lemma rnd_of_unop_shift_unchanged `{coll: collection} si shift ty u r1 y si' shift':
  rnd_of_unop si shift ty u r1 = (y, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
   unfold same_upto.
  destruct u; simpl.
- (* Rounded1 *)
  destruct op.
 + apply make_rounding_shift_unchanged.
 + destruct knowl as [ [ | ] | ].
  * (* Some Normal *)
        inversion_clear 1; auto with arith.
  * apply (make_rounding_shift_unchanged _ _ Denormal2').
  * apply (make_rounding_shift_unchanged _ _ Denormal2').
- (* Exact1 *)
    inversion_clear 1; auto with arith.
Qed.

Lemma rndval_shift_incr `{coll: collection} ty x:
  forall si shift y si' shift',
    rndval si shift ty x = (y, (si', shift')) ->
    (si <= si')%positive.
Proof.
  induction x; simpl.
- (* Const *)
    inversion_clear 1; intros; auto; lia.
- (* Var *)
    inversion_clear 1; intros; auto; lia.
- (* Binop *)
    intros.
    destruct (rndval si shift _ x1) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval si1 s1 _ x2) as (r2 & si2 & s2) eqn:EQ2.
    eapply Pos.le_trans; [ | eapply Pos.le_trans].
    + eapply IHx1; eauto.
    + eapply IHx2; eauto.
    + eapply rnd_of_binop_shift_incr; eauto.
- (* Unop *)
  intros.
  destruct (rndval si shift _ x) as (r1 & si1 & s1) eqn:EQ1.
  eapply Pos.le_trans.
  + eapply IHx; eauto.
  + eapply rnd_of_unop_shift_incr; eauto.
- (* Cast *)
  intros.
  destruct (rndval si shift _ x) as (r1 & si1 & s1) eqn:EQ1.
  eapply Pos.le_trans.
  + eapply IHx; eauto.
  + eapply rnd_of_cast_shift_incr; eauto.
- (* Func *)
   fold (@rndval_klist _).
   destruct f4; simpl in *.
   unfold rnd_of_func.
  clear - IH.
   intros.
   destruct (rndval_klist si shift args) eqn:?H.
   destruct p as [si2 s2].
   apply Pos.le_trans with si2.
   + clear H. revert k si shift si2 s2 H0.
       clear - IH.
       induction args; simpl; intros.
     * inversion H0; clear H0; subst. lia.
     * apply Kforall_inv in IH. destruct IH.
        destruct (rndval si shift _ k) as (r1 & si1 & s1) eqn:EQ1.
        destruct (rndval_klist si1 s1 args) as (r3 & si3 & s3) eqn:EQ2.
        inversion H0; clear H0; subst.
        eapply Pos.le_trans.
        apply (H _ _ _ _ _ EQ1).
        eapply IHargs in H1; eauto.
   + eapply rnd_of_func'_shift_incr; eassumption.
Qed.

Lemma rndval_klist_shift_incr `{coll: collection} tys (x: klist expr tys) :
  forall si shift y si' shift',
    rndval_klist si shift x = (y, (si', shift')) ->
    (si <= si')%positive.
Proof.
intros.
revert si shift y si' shift' H; induction x; intros.
simpl in H. inversion H; lia.
simpl in H.
destruct (rndval si shift ty k) as (r1 & si1 & s1) eqn:EQ1.
destruct (rndval_klist si1 s1  x) as (r2 & si2 & s2) eqn:EQ2.
inversion H; clear H; subst.
apply rndval_shift_incr in EQ1.
apply IHx in EQ2. lia.
Qed.

Lemma rndval_shift_le `{coll: collection} ty (x: expr ty):
  forall si shift y si' shift',
    rndval si shift _ x = (y, (si', shift')) ->
    (max_error_var y <=  si')%positive.
Proof.
  induction x; simpl.
- (* Const *)
    inversion_clear 1; simpl; auto; lia.
- (* Var *)
    inversion_clear 1; simpl; auto; lia.
- (* Binop *)
    intros.
    destruct (rndval si shift _ x1) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval si1 s1 _ x2) as (r2 & si2 & s2) eqn:EQ2.
    eapply rnd_of_binop_shift_le; eauto.
    eapply Pos.le_trans.
    + eapply IHx1; eauto.
    + eapply rndval_shift_incr; eauto.
- (* Unop *)
  intros.
  destruct (rndval si shift _ x) as (r1 & si1 & s1) eqn:EQ1.
  eapply rnd_of_unop_shift_le; eauto.
- (* Cast *)
  intros.
  destruct (rndval si shift _ x) as (r1 & si1 & s1) eqn:EQ1.
  eapply rnd_of_cast_shift_le; eauto.
- (* Func *) 
   fold (@rndval_klist _).
   destruct f4; simpl in *.
   unfold rnd_of_func.
   clear - IH.
   intros.
   destruct (rndval_klist si shift args) as [k [si2 s2]] eqn:?H.
   apply (rnd_of_func'_shift_le _ _ _ _ _ _ _ _ _ H); clear H.
   clear - IH H0. rename ff_args into tys.
   revert k si shift si2 s2 H0.
   simpl.
   clear - IH.
   induction args; simpl; intros.
 + inversion H0; clear H0; subst. simpl.  lia.
 + apply Kforall_inv in IH. destruct IH.
    destruct (rndval si shift _ k) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval_klist si1 s1 args) as (r3 & si3 & s3) eqn:EQ2.
    inversion H0; clear H0; subst.
    pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ EQ2).
    pose proof (rndval_shift_incr _ _ _ _ _ _ _ EQ1).
    eapply IHargs in H1; try eassumption. clear IHargs EQ2.
    simpl.
    apply H in EQ1; clear H.
   set (a := max_error_var_klist tys r3) in *.
   change (a <= si2)%positive in H1.
   change (_ tys r3) with a.
  set (b := max_error_var r1) in *. clearbody a. clearbody b.
  clear - EQ1 H1 H0 H2. lia.
Qed.

Lemma rndval_klist_shift_le `{coll: collection} tys (x: klist expr tys):
  forall si shift y si' shift',
    rndval_klist si shift x = (y, (si', shift')) ->
    (max_error_var_klist _ y <=  si')%positive.
Proof.
  induction x; simpl; intros.
  inversion H; clear H; subst.
  simpl. lia.
   destruct (rndval si shift _ k) as (r1 & si1 & s1) eqn:EQ1.
   destruct (rndval_klist si1 s1 x) as (r3 & si3 & s3) eqn:EQ2.
   inversion H; clear H; subst.
   pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ EQ2).
   apply IHx in EQ2.
   simpl.
   pose proof (rndval_shift_le _ _ _ _ _ _ _ EQ1).
   pose proof (rndval_shift_incr _ _ _ _ _ _ _ EQ1). lia.
Qed.

Lemma rndval_shift_unchanged `{coll: collection} ty (x: expr ty):
  forall si shift y si' shift',
    rndval si shift _ x = (y, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
   unfold same_upto.
  induction x; simpl.
- (* Const *)
    inversion_clear 1; intros; auto; lia.
- (* Var *)
    inversion_clear 1; intros; auto; lia.
- (* Binop *)
    intros.
    destruct (rndval si shift _ x1) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval si1 s1 _ x2) as (r2 & si2 & s2) eqn:EQ2.
    etransitivity; [ | etransitivity].
    +
      eapply rnd_of_binop_shift_unchanged; eauto.
      eapply Pos.lt_le_trans; [ eassumption | ].
      etransitivity; eapply rndval_shift_incr; eauto.
    +
      eapply IHx2; eauto.
      eapply Pos.lt_le_trans; [ eassumption | ].
      eapply rndval_shift_incr; eauto.
    + eapply IHx1; eauto.
- (* Unop *)
  intros.
  destruct (rndval si shift _ x) as (r1 & si1 & s1) eqn:EQ1.
  etransitivity.
  +
    eapply rnd_of_unop_shift_unchanged; eauto.
    eapply Pos.lt_le_trans; [ eassumption | ].
    eapply rndval_shift_incr; eauto.
  + eapply IHx; eauto.
- (* Cast *)
  intros.
  destruct (rndval si shift _ x) as (r1 & si1 & s1) eqn:EQ1.
  etransitivity.
  +
    eapply rnd_of_cast_shift_unchanged; eauto.
    eapply Pos.lt_le_trans; [ eassumption | ].
    eapply rndval_shift_incr; eauto.
  + eapply IHx; eauto.
- (* Func *) 
   fold (@rndval_klist _).
   unfold rnd_of_func.
   intros.
   destruct (rndval_klist si shift args) as [k [si2 s2]] eqn:?H.
   apply rnd_of_func'_shift_unchanged in H.
   rewrite H by (apply rndval_klist_shift_incr in H1; lia).
   clear shift' H.
   destruct f4; simpl in *.
   intros.
   clear - IH H0 H1. rename ff_args into tys.
   revert k si shift si2 s2 H1 i H0.
   induction args; simpl; intros; auto.
   inversion H1; clear H1; subst; auto.
   apply Kforall_inv in IH. destruct IH.
    destruct (rndval si shift _ k) as (r1 & si1 & s1) eqn:EQ1.
    destruct (rndval_klist si1 s1 args) as (r3 & si3 & s3) eqn:EQ2.
    pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ EQ2).
    pose proof (rndval_shift_incr _ _ _ _ _ _ _ EQ1).
    inversion H1; clear H1; subst.
    specialize (IHargs H2); clear H2.
    specialize (IHargs _ _ _ _ _ EQ2); clear EQ2.
    specialize (H _ _ _ _ _ EQ1); clear EQ1.
    transitivity (mget s1 i).
    apply IHargs; lia.
    apply H; lia.
Qed.

Lemma rndval_klist_shift_unchanged `{coll: collection} tys (x: klist expr tys):
  forall si shift y si' shift',
    rndval_klist si shift x = (y, (si', shift')) ->
  same_upto si (mget shift) (mget shift').
Proof.
  induction x; simpl; intros; intro; intros.
  inversion H; clear H; subst; auto.
  destruct (rndval si shift _ k) as (r1 & si1 & s1) eqn:EQ1.
  destruct (rndval_klist si1 s1 x) as (r3 & si3 & s3) eqn:EQ2.
  inversion H; clear H; subst.
  pose proof (rndval_shift_unchanged _ _ _ _ _ _ _ EQ1 _ H0).
  pose proof (IHx _ _ _ _ _ EQ2 i).
  pose proof (rndval_shift_incr _ _ _ _ _ _ _ EQ1).
  pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ EQ2).
   rewrite H1 by lia.
  apply H.
Qed.

(*  "(a, b) holds" iff 0 (if b then < else <=) a *)
Definition cond `{coll: collection} : Type := (rexpr * bool).

Definition False_cond `{coll: collection} : cond  := 
   (* a condition that is impossible to satisfy *)
 (RAtom (RConst (Float radix2 0 0)), true).

Definition eval_cond1 `{coll: collection} env m (c: cond) :=
  let '(e, b) := c in
  forall errors, errors_bounded m errors ->
    (if b then Rlt else Rle) 0 (reval e env errors)
.

Lemma evalcond1_False `{coll: collection} : forall env m, eval_cond1 env m False_cond -> False.
Proof.
intros.
hnf in H.
simpl in H.
assert (0 < 0 * 1); [ | lra].
apply (H (fun _ => 0)).
intros. intro.
rewrite Rabs_R0.
apply error_bound_nonneg.
Qed.

Lemma eval_cond1_preserved `{coll: collection} m1 m2 env c:
  ( forall e b,  c = (e, b) ->  same_upto (max_error_var e) (mget m1) (mget m2)) ->
  eval_cond1 env m1 c ->
  eval_cond1 env m2 c.
Proof.
  unfold eval_cond1.
  intros.
  destruct c.
  intros.
  rewrite <- (reval_error_ext (fun i =>
                              if Pos.ltb i (max_error_var r)
                              then errors i
                              else 0)).
  {
    apply H0.
    intros. intro.
    destruct (Pos.ltb i (max_error_var r)) eqn:LTB.
    { erewrite <- H; eauto.
      apply Pos.ltb_lt.
      assumption.
    }
    rewrite Rabs_R0. apply error_bound_nonneg.
  }
  intros.
  rewrite <- Pos.ltb_lt in H2.
  rewrite H2.
  reflexivity.
Qed.

Fixpoint revars `{coll: collection} (r: rexpr): MSET.t :=
  match r with
    | RAtom (RError n) => MSET.singleton n
    | RUnop _ e => revars e
    | RBinop _ e1 e2 => MSET.union (revars e1) (revars e2)
    | RFunc _ ff args => 
       let fix revars_klist (tys: list type) (es: klist (fun _ => rexpr) tys) : MSET.t :=
        match es with
        | Knil => MSET.empty
        | Kcons h tl => MSET.union (revars h) (revars_klist _ tl)
       end
       in revars_klist (ff_args ff) args
    | _ => MSET.empty
  end.

Definition revars_klist `{coll: collection} :=
 fix revars_klist {tys: list type} (es: klist (fun _ => rexpr) tys) : MSET.t :=
        match es with
        | Knil => MSET.empty
        | Kcons h tl => MSET.union (revars h) (revars_klist tl)
       end.

Lemma reval_error_ext_strong `{coll: collection} errors1 env errors2 e:
  (forall i, MSET.In i (revars e) -> errors2 i = errors1 i) ->
  reval e env errors2 = reval e env errors1.
Proof.
  induction e; simpl.
 - (* RAtom *)
    destruct r; auto.
    intros.
    apply H.
    apply MSET.singleton_spec.
    reflexivity.
- (* RUnop *)
    intuition congruence.
- (* RBinop *)
  intros.
  rewrite IHe1.
  +
    rewrite IHe2; [reflexivity | ].
    intros.
    apply H.
    rewrite MSET.union_spec.
    tauto.
  +
    intros.
    apply H.
    rewrite MSET.union_spec.
    tauto.
- (* RFunc *)
 destruct ff; simpl in *.
 clear - args IH. rename ff_args into tys.
 rename ff_realfunc into f.
 fold (revars_klist args).
 intro.
 change (reval_klist env errors2 args f = reval_klist env errors1 args f).
 revert IH H; induction args; intros.
 reflexivity.
 apply Kforall_inv in IH. destruct IH.
 simpl in f|-*.
 replace (reval k env errors2) with (reval k env errors1).
 apply (IHargs (f (reval k env errors1)) H1).
 intros; apply H; simpl.
 rewrite MSET.union_spec. auto.
 symmetry; apply H0; intros.
 apply H. simpl. 
 rewrite MSET.union_spec. auto.
Qed.

Lemma revars_max_error_var `{coll: collection} e:
  forall i, MSET.In i (revars e) -> 
            (i < max_error_var e)%positive.
Proof.
  induction e; simpl; auto; intro.
 - (* RAtom *)
    destruct r; generalize (@MSET.empty_spec i); try contradiction.
    intros _.
    rewrite MSET.singleton_spec.
    intro; subst; auto; lia.
 - (* RBinop *)
  rewrite MSET.union_spec.
  destruct 1.
  +
    eapply Pos.lt_le_trans; [eapply IHe1; eauto | ].
    apply Pos.le_max_l.
  +
    eapply Pos.lt_le_trans; [eapply IHe2; eauto | ].
    apply Pos.le_max_r.
- (* RFunc *)
 destruct ff; simpl in *.
 clear - args IH. rename ff_args into tys.
 fold (revars_klist args).
 intro.
 change (i < max_error_var_klist tys args)%positive.
 revert IH H; induction args; intros.
 simpl in *.
 contradiction (@MSET.empty_spec i).
 apply Kforall_inv in IH. destruct IH.
 simpl in H |-*.
 rewrite MSET.union_spec in H.
 destruct H.
 + apply H0 in H. lia.
 +  apply IHargs in H1; clear IHargs; auto.  lia.
Qed.

Export List.

Fixpoint enum_forall' t_ (Q: positive -> _ -> Prop) (l: list positive) 
   (P: Maps.PMap.t R -> Prop): Prop :=
  match l with
    | nil => P (mempty t_)
    | a :: q =>
      enum_forall' t_ Q q (fun errors =>
                            forall u,
                              Q a u ->
                              P (mset errors a u))
  end.

Lemma enum_forall_correct'  t_ (Q: _ -> _ -> Prop) (Ht_: forall i, Q i t_) l:
  forall (P: _ -> Prop),
    (forall errors1 errors2,
       (forall i: positive, In i l -> mget errors2 i = mget errors1 i) ->
       P errors1 -> P errors2) ->
    (forall errors,
       (forall i, Q i (mget errors i)) ->
       P errors) <->
    enum_forall' t_ Q l P.
Proof.
  induction l; simpl; intros.
  {
    split.
    {
      intros.
      eapply H0.
      intros.
      rewrite mget_empty.
      auto.
    }
    intros.
    eapply H; [ | eassumption ].
    contradiction.
  }
  specialize (IHl (fun errors => forall u, Q a u -> P (mset errors a u))).
  destruct IHl.
  {
    simpl.
    intros.
    eapply H.
    2: eapply H1; eauto.
    intros.
    repeat rewrite mget_set.
    destruct (Pos.eq_dec i a); auto.
    destruct H3; try congruence.
    auto.
  }
  split; intros.
  {
    apply H0; intros.
    apply H2.
    intros.
    repeat rewrite mget_set.
    destruct (Pos.eq_dec i a); auto.
    congruence.
  }
  eapply H.
  2: eapply H1 with (u := mget errors a); eauto.
  intros.
  repeat rewrite mget_set.
  destruct (Pos.eq_dec i a); subst; auto.
Qed.

Definition enum_forall t_ Q l P :=
    enum_forall' t_ Q l (fun m => P (mget m)).  

Theorem enum_forall_correct  t_ (Q: _ -> _ -> Prop) (Ht_: forall i, Q i t_) l:
  forall (P: _ -> Prop),
    (forall errors1 errors2,
       (forall i, In i l -> errors2 i = errors1 i) ->
       P errors1 -> P errors2) ->
    (forall errors,
       (forall i, Q i (mget errors i)) ->
       P (mget errors)) <->
    enum_forall t_ Q l P.
Proof.
  unfold enum_forall.
  intros.
  rewrite <- (enum_forall_correct' t_ Q Ht_ l (fun m => P (mget m))); try tauto.
  intros.
  eapply H; eauto.
Qed.

Let P `{coll: collection}  env e (b: bool) errors :=
  (if b then Rlt else Rle) 0 (reval e env errors).

Let Q m i err := 
  Rabs err <= error_bound (mget m i).

Definition eval_cond2 `{coll: collection} env m (c: cond) :=
  let '(e, b) := c in
  enum_forall 0 (Q m) (MSET.elements (revars e)) (P env e b)
.

Lemma eval_cond2_correct `{coll: collection} env (m: MSHIFT) c:
  eval_cond2 env m c <-> eval_cond1 env m c.
Proof.
  unfold eval_cond2, eval_cond1.
  destruct c.
  rewrite <- enum_forall_correct.
  {
    unfold Q, P.
    split; intros.
    {
      destruct (finite_errors_ex 0 (max_error_var r) errors).
      rewrite <- (reval_error_ext (mget x)).
      {
        eapply H; eauto.
        intros. rewrite H1.
        destruct (Pos.ltb i (max_error_var r)); auto.
        rewrite Rabs_R0. apply error_bound_nonneg.
      }
      intros.
      rewrite H1.
      rewrite <- Pos.ltb_lt in H2.
      rewrite H2.
      reflexivity.
    }
    apply H. auto.
  }
  {
    unfold Q.
    intros.
    rewrite Rabs_R0. apply error_bound_nonneg. 
  }
  unfold P.
  intros.
  rewrite (reval_error_ext_strong errors1); auto.
  intros.
  apply H.
  rewrite <- MSET.elements_spec1 in H1.
  rewrite SetoidList.InA_alt in H1.
  destruct H1.
  intuition congruence.
Qed.  

Definition is_div o :=
  match o with
    | DIV => true
    | _ => false
  end.

Definition rounding_cond_ast `{coll: collection} ty k x: list cond :=
  match k with
    | Normal' =>
      (RBinop Tree.Sub (RUnop Tree.Abs x) (RAtom (RConst (Defs.Float _ 1 (3 - femax ty - 1)))), false) :: nil
    | Denormal' =>
      (RBinop Tree.Sub (RAtom (RConst (Defs.Float _ 1 (3 - femax ty)))) (RUnop Tree.Abs x), true) :: nil
    | Denormal2' => nil
    | Unknown' => nil 
  end.

Lemma rounding_cond_ast_shift `{coll: collection} ty k x e b:
  In (e, b) (rounding_cond_ast ty k x) ->
  (max_error_var e <= max_error_var x)%positive.
Proof.
  Opaque Zminus.
  destruct k; simpl; try tauto;
    intro K;
    inversion K; try contradiction;
    clear K;
    subst;
    inversion H; clear H; subst;
    simpl; lia.
  Transparent Zminus.
Qed.

Lemma rounding_cond_ast_correct `{coll: collection} m env ty knowl r errors:
  errors_bounded m errors ->
  (forall i, In i (rounding_cond_ast ty knowl r) -> eval_cond1 env m i) ->
  rounding_cond ty knowl (reval r env errors)
.
Proof.
  intros.
  unfold rounding_cond.
  destruct knowl; auto.
 -
  cbn -[Zminus] in * |- *  .
    specialize (H0 _ (or_introl _ (refl_equal _))).
    cbn -[Zminus] in *.
    specialize (H0 _ H).
    lra.
 -
  specialize (H0 _ (or_introl _ (refl_equal _))).
  cbn -[Zminus] in *.
  specialize (H0 _ H).
  lra.
Qed.

Definition no_overflow `{coll: collection} ty x: cond := 
  (RBinop Tree.Sub (RAtom (RConst (Defs.Float _ 1 (femax ty)))) (RUnop Tree.Abs x), true).

Definition rnd_of_plus_zero_cond `{coll: collection} (zero_left: bool) r1 r2 :=
  (RUnop Tree.Neg (RUnop Tree.Abs (if zero_left then r1 else r2)), false) :: nil.  

Definition rnd_of_binop_with_cond`{coll: collection} 
           si
           (shift: MSHIFT)
           (ty: type)
           (o: binop) (r1 r2: rexpr):
  ((rexpr * (positive * MSHIFT)) * list cond)
  :=
    match o with
      | SterbenzMinus =>
        ((RBinop Tree.Sub r1 r2, (si, shift)),
         (RBinop Tree.Sub r1 (RBinop Tree.Mul r2 (RAtom (RConst (Defs.Float _ 1 (-1))))), false)
           ::
           (RBinop Tree.Sub (RBinop Tree.Mul r2 (RAtom (RConst (Defs.Float _ 1 1)))) r1, false)
           :: nil)
      | PlusZero minus zero_left =>
        (
          ((
              if zero_left
              then
                if minus
                then RUnop Tree.Neg r2
                else r2
              else
                r1
            ), (si, shift))
          ,
          rnd_of_plus_zero_cond zero_left r1 r2
        )
      | Rounded2 o' k =>
        let ru := RBinop (Rbinop_of_rounded_binop o') r1 r2 in
        let rs := make_rounding si shift (round_knowl_denote k) ty ru in
        let '(r, _) := rs in
        (rs,
         (if is_div o' then (RUnop Tree.Abs r2, true) :: nil else nil)
           ++ no_overflow ty r :: rounding_cond_ast ty (round_knowl_denote k) ru)
    end.

Lemma rounding_cond_ast_shift_cond `{coll: collection} ty k r e b:
  In (e, b) (rounding_cond_ast ty k r) ->
     (max_error_var e = max_error_var r)%positive.
Proof.
  unfold rounding_cond_ast.
  destruct k; try contradiction.
-
    destruct 1; try contradiction.
    Opaque Zminus. inversion H; clear H; subst. Transparent Zminus.
    simpl. lia.
-
  destruct 1; try contradiction.
  Opaque Zminus. inversion H; clear H; subst. Transparent Zminus.
  simpl. lia.
Qed.

Lemma rnd_of_binop_with_cond_shift_cond `{coll: collection} si shift ty o r1 r2 r' si' shift' cond:
  rnd_of_binop_with_cond si shift ty o r1 r2 = ((r', (si', shift')), cond) ->
  (max_error_var r1 <= si)%positive ->
  (max_error_var r2 <= si)%positive ->
  forall e b,
    In (e, b) cond ->
    (max_error_var e <= si')%positive.
Proof.
  destruct o; simpl.
  {
    destruct (
        make_rounding si shift (round_knowl_denote knowl) ty
                      (RBinop (Rbinop_of_rounded_binop op) r1 r2)
    ) eqn:EQ.
    intro K.
    inversion K; clear K; subst.
    intros.
    apply in_app_or in H1.
    destruct H1.
    {
      destruct (is_div op); try contradiction.
      destruct H1; try contradiction.
      inversion H1; clear H1; subst.
      simpl.
      apply make_rounding_shift_incr in EQ.
      lia.
    }
    destruct H1.
    {
      inversion H1; clear H1; subst.
      simpl. rewrite Pos.max_r by lia.
      eapply make_rounding_shift_le; eauto.
      simpl. lia.
    }
    apply rounding_cond_ast_shift_cond in H1.
    rewrite H1.
    simpl.
    apply make_rounding_shift_incr in EQ.
    lia.
  }
  {
    intro K.
    inversion K; clear K; subst.
    simpl.
    destruct 3.
    {
      inversion H1; clear H1; subst.
      simpl. lia.
    }
    destruct H1; try contradiction.
    inversion H1; clear H1; subst.
    simpl. lia.
  }
  {
    intro K.
    inversion K; clear K; subst.
    simpl.
    destruct 3; try contradiction.
    inversion H1; clear H1; subst.
    simpl.
    destruct zero_left; auto.
  }
Qed.

Definition rnd_of_cast_with_cond `{coll: collection} 
           si
           (shift: MSHIFT)
           (tyfrom tyto: type)
           (k: rounding_knowledge')
           (r: rexpr) :=
  if type_leb tyfrom tyto
  then
    ((r, (si, shift)), nil)
  else
    let rs := make_rounding si shift k tyto r in
    let '(r', _) := rs in
    (rs, no_overflow tyto r' :: rounding_cond_ast tyto k r)
.

Lemma rnd_of_cast_with_cond_shift_cond `{coll: collection} 
      si shift tyfrom tyto k r r' si' shift' cond:
  rnd_of_cast_with_cond si shift tyfrom tyto k r = ((r', (si', shift')), cond) ->
  (max_error_var r <= si)%positive ->
  forall e b,
    In (e, b) cond ->
    (max_error_var e <= si')%positive.
Proof.
  unfold rnd_of_cast_with_cond.
  destruct (type_leb tyfrom tyto).
  {
    intros.
    inversion H; clear H; subst.
    contradiction.
  }
  destruct (make_rounding si shift k tyto r) eqn:EQ.
  destruct p.
  intro K.
  inversion K; clear K; subst.
  destruct 2.
  {
    inversion H0; clear H0; subst.
    simpl. rewrite Pos.max_r by lia.
    eapply make_rounding_shift_le; eauto.
  }
  apply rounding_cond_ast_shift_cond in H0.
  rewrite H0.
  apply make_rounding_shift_incr in EQ.
  lia.
Qed.

Definition rnd_of_unop_with_cond `{coll: collection} 
           si
           (shift: MSHIFT)
           (ty: type)
           (o: unop) (r1: rexpr)
  :=
    match o with
      | Rounded1 (InvShift n ltr) (Some Normal) =>
        let ru := Runop_of_rounded_unop ty  (InvShift n ltr) r1 in
        ((ru, (si, shift)), 
            (RBinop Tree.Sub (RUnop Tree.Abs r1) (RAtom (RConst (Defs.Float _ 1 (3 - femax ty + Z.pos n - 1)))), false) :: nil)
      | Rounded1 (InvShift n _) _ =>
        let ru := RBinop Tree.Mul (RAtom (RConst (B2F (B2 ty (- Z.pos n))))) r1 in
        let rs := make_rounding si shift Denormal2' ty ru in
        let '(r, _) := rs in
        (rs, nil)
      | Rounded1 op k =>
        let ru := Runop_of_rounded_unop ty op r1 in
        let rs := make_rounding si shift (round_knowl_denote k) ty ru in
        let '(r, _) := rs in
        (rs, (r1, false) :: rounding_cond_ast ty (round_knowl_denote k) ru)
      | Exact1 o => 
        let ru := Runop_of_exact_unop ty o r1 in
        ((ru, (si, shift)), 
         match o with
           | Shift _ _ => no_overflow ty ru :: nil
           | _ => nil
         end)
    end.

Lemma rnd_of_unop_with_cond_shift_cond `{coll: collection} 
   si shift ty o r1 r' si' shift' cond:
  rnd_of_unop_with_cond si shift ty o r1 = ((r', (si', shift')), cond) ->
  (max_error_var r1 <= si)%positive ->
  forall e b,
    In (e, b) cond ->
    (max_error_var e <= si')%positive.
Proof.
  destruct o; cbn -[Zminus].
- (* Rounded1 *)
 destruct op.
 + (* SQRT *)
    destruct (
        make_rounding si shift (round_knowl_denote knowl) ty (Runop_of_rounded_unop ty SQRT r1)
      ) as [r'1 [si'1 shift'1]] eqn:EQ.
    intro K.
    inversion K; clear K; subst.
    intros.
    destruct H0.
    {
      inversion H0; clear H0; subst.
      eapply make_rounding_shift_incr in EQ.
      lia.
    }
    apply rounding_cond_ast_shift_cond in H0.
    rewrite H0.
    simpl.
    apply make_rounding_shift_incr in EQ.
    lia.
 + (* InvShift *)
    destruct knowl as [ [ | ] | ].
  * (* Some Normal *)
    intro K.
    inversion K; clear K; subst.
    intros.
    destruct H0; try contradiction.
    inversion H0; clear H0; subst.
    simpl. lia.
  * intros. inversion H; clear H; subst. inversion H1.
  * intros. inversion H; clear H; subst. inversion H1.
- (* Exact1 *)
    intro K.
    inversion K; clear K; subst.
    intros.
    destruct o; try contradiction.
   + (* Shift *)
      destruct H0; try contradiction.
      inversion H0; clear H0; subst.
      simpl. lia.
Qed.

Definition interp_all_bounds `{coll: collection} (env:  environ)
    {tys: list type} (bl: klist bounds tys) (args: klist expr tys) :=
 Kforall2 (fun ty (bd: bounds ty) (e: expr ty) => interp_bounds bd (fval env e) = true) bl args.

Definition vacuous_lo_bound {ty} (bnd: bounds ty) : bool.
destruct ty as [? ? ? ? ? [|]].
exact false.
exact
 match bnd with
 | ((lo, false), _) => 
     match float_of_ftype lo with
     | B754_infinity _ _ true => true 
     | _ => false
     end
 | _ => false 
 end.
Defined.

Definition vacuous_hi_bound {ty} (bnd: bounds ty) : bool.
destruct ty as [? ? ? ? ? [|]].
exact false.
exact
 match bnd with
 | (_, (hi, false)) => 
     match float_of_ftype hi with
     | B754_infinity _ _ false => true 
     | _ => false
     end
 | _ => false 
 end.
Defined.

Definition Defsfloat_of_ftype {ty} (x: ftype ty) : option (float radix2).
destruct ty as [? ? ? ? ? [|]].
exact (nonstd_to_F x).
apply (Some (B2F x)).
Defined.


Definition FT2F {ty} (x: ftype ty) : float radix2.
destruct ty as [? ? ? ? ? [|]].
exact
match nonstd_to_F x with
| Some f => f
| None => {| Fnum:=0; Fexp:=0 |}
end.
exact (B2F x).
Defined.


Definition bounds_to_cond `{coll: collection} {ty} (bnd: bounds ty) (r: rexpr) : list cond := 
 let '((lo,blo),(hi,bhi)) := bnd in
  (if vacuous_lo_bound bnd then [] 
   else if is_finite lo then [(RBinop Tree.Sub r (RAtom (RConst (FT2F lo))), blo)]
   else [False_cond])
   ++ 
  (if vacuous_hi_bound bnd then [] 
   else if is_finite hi then [(RBinop Tree.Sub (RAtom (RConst (FT2F hi))) r, bhi)]
   else [False_cond]).

Fixpoint bounds_to_conds `{coll: collection} {tys} (bnds: klist bounds tys) (args: klist (fun _ => rexpr) tys) : list cond.
inversion bnds as [ | ty tys' b1 bnds'].
exact nil.
subst tys.
inversion args as [ | ty1 tys1' e1 args'].
subst.
exact (bounds_to_cond b1 e1 ++ bounds_to_conds _ _ bnds' args').
Defined.

Definition type_hibound' (t: type) :=
(*   Float radix2 (Z.pow 2 (femax t) - Z.pow 2 (femax t - fprec t)) 1. *)
  Float radix2 (Z.pow 2 (fprec t) - 1) (femax t - fprec t).

Definition func_no_overflow `{coll: collection} si shift {ty: type}
     (ff:  floatfunc_package ty) 
     (args: klist (fun _ => rexpr) (ff_args ff)) : cond :=
  no_overflow ty (fst (rnd_of_func si shift _ ff args)).

Definition rnd_of_func_with_cond `{coll: collection} 
    (si: positive) (shift: MSHIFT) {ty: type} (ff:  floatfunc_package ty) 
     (args: klist (fun _ => rexpr) (ff_args ff)) :
     rexpr * (positive * MSHIFT) * list cond :=
  (rnd_of_func si shift ty ff args, 
     func_no_overflow si shift ff args :: bounds_to_conds (ff_precond ff) args).

Fixpoint rndval_with_cond' `{coll: collection} 
         (si: positive)
         (shift: MSHIFT)
         {ty} (e: expr ty) {struct e}
   : rexpr * (positive * MSHIFT) * list (rexpr * bool) :=
  match e with
    | Const _ _ f => ((RAtom (RConst (B2F f)), (si, shift)), nil)
    | Var _ IN i => ((RAtom (RVar ty IN i), (si, shift)), nil)
    | Binop b e1 e2 =>
      let '((r1, (si1, s1)), p1) := rndval_with_cond' si shift e1 in
      let '((r2, (si2, s2)), p2) := rndval_with_cond' si1 s1 e2 in
      let '(rs, p) := rnd_of_binop_with_cond si2 s2 ty b r1 r2 in
      (rs, p ++ (p1 ++ p2))
    | Unop b e1 =>
      let '((r1, (si1, s1)), p1) := rndval_with_cond' si shift e1 in
      let '(rs, p) := rnd_of_unop_with_cond si1 s1 ty b r1 in
      (rs, p ++ p1)
    | Cast _ fromty STDto STDfrom k e1 => 
      let '((r1, (si1, s1)), p1) := rndval_with_cond' si shift e1 in
      let '(rs, p) := rnd_of_cast_with_cond si1 s1 fromty ty (round_knowl_denote k) r1 in
      (rs, p ++ p1)
    | Func _ ff args => 
       let fix rndval_with_cond'_klist (si: positive) (shift: MSHIFT) {tys: list type} (l': klist expr tys)                     {struct l'}: 
                   klist (fun _ => rexpr) tys * (positive*MSHIFT) * list (rexpr * bool) :=
          match l' (* in (klist _ l)  return (function_type (map RR l) R -> R) *)
          with
          | Knil => (Knil, (si, shift), nil)
          | Kcons h tl => let  '((r1, (si1, s1)), p1) := rndval_with_cond' si shift h in
                                    let '((r2, (si2, s2)), p2) := rndval_with_cond'_klist
                                                      si1 s1 tl in
                                    (Kcons r1 r2, (si2,s2), p1++p2)
          end
          in let '((rn, (si', s')), pn) := rndval_with_cond'_klist si shift args in
              let '(rs,p) := rnd_of_func_with_cond si' s' ff rn
               in (rs, p++pn)
  end. 

Definition rndval_with_cond'_klist `{coll: collection} :=
 fix rndval_with_cond'_klist (si: positive) (shift: MSHIFT) {tys: list type} (l': klist expr tys) 
                       {struct l'}: 
                   klist (fun _ => rexpr) tys * (positive*MSHIFT) * list (rexpr * bool) :=
          match l'
          with
          | Knil => (Knil, (si, shift), nil)
          | Kcons h tl => let  '((r1, (si1, s1)), p1) := rndval_with_cond' si shift h in
                                    let '((r2, (si2, s2)), p2) := rndval_with_cond'_klist si1 s1 tl in
                                    (Kcons r1 r2, (si2,s2), p1++p2)
          end.

Lemma rnd_of_binop_with_cond_left `{coll: collection} {si shift ty o r1 r2 a c}:
  rnd_of_binop_with_cond si shift ty o r1 r2 = (a,c) ->
  rnd_of_binop si shift ty o r1 r2 = a.
Proof.
  unfold rnd_of_binop_with_cond, rnd_of_binop; intros.
  destruct o; try congruence.
  destruct (make_rounding _ _ _ _ _); congruence.
Qed.


Lemma rnd_of_cast_with_cond_left `{coll: collection} {si shift ty ty0 knowl r1 a c}:
   rnd_of_cast_with_cond si shift ty ty0 knowl r1 = (a,c) ->
   rnd_of_cast si shift ty ty0 knowl r1 = a.
Proof.
   unfold rnd_of_cast_with_cond, rnd_of_cast; intros.
  destruct (type_leb _ _); try congruence.
  destruct (make_rounding _ _ _ _ _); congruence.
Qed.

Lemma rnd_of_unop_with_cond_left `{coll: collection} {si shift ty o r1  a c}:
  rnd_of_unop_with_cond si shift ty o r1 = (a,c) ->
  rnd_of_unop si shift ty o r1 = a.
Proof.
  unfold rnd_of_unop_with_cond, rnd_of_unop; intros.
  destruct o; simpl; try congruence.
 destruct op; try congruence.
  destruct (make_rounding _ _ _ _ _); congruence.
  destruct knowl as [ [ | ] | ]; simpl in *; congruence.
Qed.

Lemma rnd_of_func_with_cond_left `{coll: collection} {si shift ty ff args  a c}:
  rnd_of_func_with_cond si shift ff args  = (a,c) ->
  rnd_of_func si shift ty ff args = a.
Proof.
 unfold rnd_of_func_with_cond; intros; congruence.
Qed.

Lemma rndval_with_cond_left `{coll: collection} {si shift ty} {e: expr ty} {a c}:
    rndval_with_cond' si shift e = (a,c) ->
   rndval si shift _ e = a.
Proof.
  revert si shift a c;
  induction e; simpl; intros; try congruence.
- (* Binop *)
    specialize (IHe1 si shift).
    destruct (rndval_with_cond' si shift e1) as [[r1 [si1 s1]] p1].
    rewrite (IHe1 _ _ (eq_refl _)).
    specialize (IHe2 si1 s1).
    destruct (rndval_with_cond' si1 s1 e2) as [[r2 [si2 s2]] p2].
    rewrite (IHe2 _ _ (eq_refl _)).
    destruct (rnd_of_binop_with_cond si2 s2 ty b r1 r2) as [[r3 [si3 s3]] p3] eqn:?H.
    apply @rnd_of_binop_with_cond_left in H0.
    congruence.
- (* Unop *)
   intros.
  specialize (IHe si shift).
  destruct (rndval_with_cond' si shift e) as [[r1 [si1 s1]] p1].
  rewrite (IHe _ _ (eq_refl _)).
  destruct (rnd_of_unop_with_cond si1 s1 ty u r1) as [[r2 [si2 s2]] p2] eqn:?H.
  apply rnd_of_unop_with_cond_left in H0. congruence.
- (* Cast *) 
  intros.
  specialize (IHe si shift).
  destruct (rndval_with_cond' si shift e) as [[r1 [si1 s1]] p1]. 
  rewrite (IHe _ _ (eq_refl _)).
  destruct (rnd_of_cast_with_cond si1 s1 fromty ty
                 (round_knowl_denote knowl) r1)
                   as [[r2 [si2 s2]] p2] eqn:?H.
  apply rnd_of_cast_with_cond_left in H0. 
  congruence.
- (* Func *)
 intros.
  fold (@rndval_with_cond'_klist _) in *.
  fold (@rndval_klist _ si shift (ff_args f4)) in *.
  destruct (rndval_with_cond'_klist si shift args) as [[r1 [si1 s1]] l1] eqn:?H.
  destruct (rndval_klist si shift args) as [r2 [si2 s2]] eqn:?H.
  unfold rnd_of_func_with_cond, rnd_of_func in *.
  assert ((si1,s1,r1) = (si2,s2,r2)); [ | simpl; congruence].
  clear P Q.
  clear a c H.
  revert si shift r1 si1 s1 l1 r2 si2 s2 H0 IH H1.
  induction args; simpl; intros.
  congruence.
  destruct (rndval si shift ty0 k)  as [r1' [si1' s1']] eqn:?H.
  destruct (rndval_klist si1' s1' args) as [r2' [si2' s2']] eqn:?H.
  destruct (rndval_with_cond' si shift k) as [[r3 [si3 s3]] c3] eqn:?H.
  destruct (rndval_with_cond'_klist si3 s3 args) as [[r4 [si4 s4]] c4] eqn:?H.
  apply Kforall_inv in IH; destruct IH.
  inversion H1; clear H1; inversion H0; clear H0; subst.
  apply H5 in H3.
  rewrite H3 in H; inversion H; clear H; subst.
  clear H5 H3.
  specialize (IHargs _ _ _ _ _ _ _ _ _ H4 H6 H2); clear H4 H6 H2.
  congruence.
Qed.

Lemma rndval_with_cond_klist_left `{coll: collection} {si shift tys} {e: klist expr tys} {a c}:
   rndval_with_cond'_klist si shift e = (a,c) ->
   rndval_klist si shift e = a.
Proof.
  revert si shift a c;  induction e; simpl; intros; auto.
  congruence.
  destruct (rndval_with_cond' si shift k) as [[r1 [si1 s1]] p1] eqn:?H.
  destruct (rndval_with_cond'_klist si1 s1 e) as [[r2 [si2 s2]] p2] eqn:?H.
  rewrite (rndval_with_cond_left H0).
  apply IHe in H1. rewrite H1. congruence.
Qed.

Lemma rndval_with_cond_shift_cond `{coll: collection} ty (e: expr ty):
  forall si shift r' si' shift' cond,
  rndval_with_cond' si shift e = ((r', (si', shift')), cond) ->
  forall e' b',
    In (e', b') cond ->
    (max_error_var e' <= si')%positive.
Proof.
  induction e; simpl; intros.
  -
    inversion H; clear H; subst; contradiction.
  -
    inversion H; clear H; subst; contradiction.
  -
    destruct (rndval_with_cond' si shift e1) as [[r1 [si1 s1]] p1] eqn:EQ1.
    destruct (rndval_with_cond' si1 s1 e2) as [[r2 [si2 s2]] p2] eqn:EQ2.
    destruct (rnd_of_binop_with_cond si2 s2 _ b r1 r2)
             as [rs' p']
             eqn:EQ.
    inversion H; clear H; subst.
    pose proof (rndval_with_cond_left EQ1).
    pose proof (rndval_with_cond_left EQ2).
    pose proof (rnd_of_binop_with_cond_left EQ).
    pose proof (rndval_shift_le _ _ _ _ _ _ _ H).
    apply rndval_shift_incr in H.
    pose proof (rndval_shift_le _ _ _ _ _ _ _ H1).
    apply rndval_shift_incr in H1.
    pose proof (rnd_of_binop_shift_incr _ _ _ _ _ _ _ _ _ H2).
    apply rnd_of_binop_shift_le in H2; try lia.
    rewrite !in_app_iff in H0.
    destruct H0 as [?|[?|?]].
      eapply rnd_of_binop_with_cond_shift_cond; eauto; lia.
      eapply IHe1 in H0; [ | eassumption ]; lia .
      eapply IHe2 in H0; [ | eassumption ]; lia .
  - (* Unop *)
    destruct (rndval_with_cond' si shift e) as [[r1 [si1 s1]] p1] eqn:EQ1.
    destruct (rnd_of_unop_with_cond si1 s1 ty u r1) eqn:EQ.
    inversion H; clear H; subst.
    pose proof (rndval_with_cond_left EQ1).
    pose proof (rnd_of_unop_with_cond_left EQ).
    pose proof (rndval_shift_le _ _ _ _ _ _ _ H).
    apply rndval_shift_incr in H.
    pose proof (rnd_of_unop_shift_incr _ _ _ _ _ _ _ _ H1).
    apply rnd_of_unop_shift_le in H1; try lia.
    rewrite !in_app_iff in H0.
    destruct H0.
      eapply rnd_of_unop_with_cond_shift_cond; eauto.
      eapply IHe in H0; [ | eassumption ]; lia.
 - (* Cast *)
  destruct (rndval_with_cond' si shift e) as [[r1 [si1 s1]] p1] eqn:EQ1.
  destruct (rnd_of_cast_with_cond si1 s1 fromty ty (round_knowl_denote knowl)  r1) eqn:EQ.
  inversion H; clear H; subst.
    pose proof (rndval_with_cond_left EQ1).
    pose proof (rnd_of_cast_with_cond_left EQ).
    pose proof (rndval_shift_le _ _ _ _ _ _ _ H).
    apply rndval_shift_incr in H.
    pose proof (rnd_of_cast_shift_incr _ _ _ _ _ _ _ _ _ H1).
    apply rnd_of_cast_shift_le in H1; try lia.
    rewrite !in_app_iff in H0.
  destruct H0.
       eapply rnd_of_cast_with_cond_shift_cond; eauto.
       eapply IHe in H0; [ | eassumption ]; lia.
- (* Func *)
 fold (@rndval_with_cond'_klist _) in H.
 destruct (rndval_with_cond'_klist si shift args) as [[r2 [si2 s2]] c2] eqn:?H.
 inversion H; clear H; subst.
 unfold func_no_overflow, rnd_of_func, rnd_of_func', fst in H0.
 change (?a :: ?b ++ ?c) with ((a::b)++c) in H0.
 apply in_app_iff in H0.
 destruct H0 as [[H0|H0]|H0].
 + unfold no_overflow in *. inversion H0; clear H0; subst.
     assert (H4 := rndval_with_cond_klist_left H1).
      pose proof (rndval_klist_shift_le _ _ _ _ _ _ _ H4).
     destruct (ff_rel (ff_ff f4)), (ff_abs (ff_ff f4)); simpl;
     change (_ (ff_args f4) r2) with  (max_error_var_klist (ff_args f4) r2); lia.
 + assert (H4 := rndval_with_cond_klist_left H1).
      pose proof (rndval_klist_shift_le _ _ _ _ _ _ _ H4).
      clear - H H0.
      destruct f4 as [tys pre rf ff]; simpl in *. clear - H0 H.
      revert pre r2 H0 H; induction tys; simpl; intros.
      rewrite (klist_nil pre) in H0. rewrite (klist_nil r2) in H0. destruct H0.
      destruct (klist_cons pre) as [p1 [pre' ?]]. destruct (klist_cons r2) as [r1 [r2' ?]].  subst.
     simpl in *. unfold eq_rect_r, eq_rect, eq_sym in H0.
     apply in_app_iff in H0. destruct H0.
     destruct p1 as [[lo blo] [hi bhi]]. unfold bounds_to_cond in H0.
         apply in_app_iff in H0. destruct H0.
         destruct (vacuous_lo_bound (lo, blo, (hi, bhi))) eqn:?H. contradiction.
         destruct (is_finite lo) eqn:?H; destruct H0; try contradiction; inversion H0; clear H0; subst; simpl; lia.
         destruct (vacuous_hi_bound (lo, blo, (hi, bhi))) eqn:?H. destruct H0.
         destruct (is_finite hi) eqn:?H; destruct H0; try contradiction; inversion H0; clear H0; subst; simpl; lia.
         eapply IHtys; try eassumption. lia.
  + clear - H1 H0 IH.
      revert si shift r2 si2 s2 c2 H1 H0; induction args; simpl; intros. 
      inversion H1; clear H1; subst. contradiction.
      apply Kforall_inv in IH; destruct IH as [IH' IH].
        destruct (rndval_with_cond' si shift k) as [[r1 [si1 s1]] p1] eqn:?H.
        destruct (rndval_with_cond'_klist si1 s1 args) as [[r3 [si3 s3]] p3] eqn:?H.
        inversion H1; clear H1; subst.
       apply in_app_iff in H0; destruct H0.
       specialize (IH' _ _ _ _ _ _ H _ _ H0). 
       assert (H4 := rndval_with_cond_klist_left H2).
       pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ H4). lia.
       apply IHargs in H2; eauto.
Qed.

Lemma rndval_with_cond_klist_shift_cond `{coll: collection} tys (e: klist expr tys):
  forall si shift r' si' shift' cond,
  rndval_with_cond'_klist si shift e = ((r', (si', shift')), cond) ->
  forall e' b',
    In (e', b') cond ->
    (max_error_var e' <= si')%positive.
Proof.
  induction e; simpl; intros.
  inversion H; clear H; subst; contradiction H0.
 destruct (rndval_with_cond' si shift k) as [[r1 [si1 s1]] p1] eqn:?H.
 destruct (rndval_with_cond'_klist si1 s1 e) as [[r3 [si3 s3]] p3] eqn:?H.
  inversion H; clear H; subst.
  pose proof (rndval_with_cond_left H1).
 pose proof (rndval_with_cond_klist_left H2).
 pose proof (rndval_shift_incr _ _ _ _ _ _ _ H).
 pose proof (rndval_shift_le _ _ _ _ _ _ _ H).
 pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ H3).
 pose proof (rndval_klist_shift_le _ _ _ _ _ _ _ H3).
 pose proof (rndval_with_cond_shift_cond _ _ _ _ _ _ _ _ H1).
 specialize (IHe _ _ _ _ _ _ H2).
 apply in_app_iff in H0.
 destruct H0.
 apply H8 in H0; lia.
  apply IHe in H0. lia.
Qed.

Lemma sterbenz_no_overflow A x y:
  - A < x < A ->
  - A < y < A ->
  0 <= y * 2 - x ->
  0 <= x - y * / 2 ->
  - A < x - y < A
.
Proof.
  lra.
Qed.

Theorem fop_of_rounded_binop_correct `{coll: collection} op shift errors
    (Herr: errors_bounded shift errors)
        ty (STD: is_standard ty) e1
        (F1: is_finite e1 = true)
        env r1
        (V1: reval r1 env errors =
             FT2R e1)
        e2
        (F2: is_finite e2 = true)
        r2
        (V2: reval r2 env errors = FT2R e2)
        r
        (V_: reval r env errors =
            Generic_fmt.round Zaux.radix2
                                    (FLT.FLT_exp
                                       (3 - femax ty - fprec ty)
                                       (fprec ty)
                                    )
                                    (Generic_fmt.Znearest (fun x : Z => negb (Z.even x)))
                                    (reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors))
        (COND:
           (forall i,
              In i ((if is_div op
                     then (RUnop Tree.Abs r2, true) :: nil
                     else nil)) ->
              eval_cond1 env shift i))
        (NO_OVERFLOW:
           eval_cond1 env shift (no_overflow ty r))
:
  is_finite (fop_of_rounded_binop op ty _ e1 e2) = true /\
  FT2R (fop_of_rounded_binop op ty _ e1 e2) =
  reval r env errors.
Proof.
  intros.
  specialize (NO_OVERFLOW _ Herr).
  simpl in NO_OVERFLOW.
  rewrite Rmult_1_l in NO_OVERFLOW.
  rewrite V_ in * |- *.
  clear r V_.
  rewrite is_finite_Binary in *.
(*  repeat rewrite B2R_correct in *. *)
  destruct op;
    cbn -[Zminus] in * |- * ;
    rewrite V1 in * |- *;
    rewrite V2 in * |- *.

  {
    (* plus *)
    generalize (Bplus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
    change (SpecFloat.fexp _ _) with (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
    change (BinarySingleNaN.round_mode _) with ZnearestE.
    rewrite <- !FT2R_ftype_of_float, !ftype_of_float_of_ftype.
    rewrite Raux.Rlt_bool_true by lra.
    destruct 1 as (? & ? & _).
    unfold BPLUS, BINOP; rewrite float_of_ftype_of_float; auto.
  }
  {
    (* minus *)
    generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
    change (SpecFloat.fexp _ _) with (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
    change (BinarySingleNaN.round_mode _) with ZnearestE.
    rewrite <- !FT2R_ftype_of_float, !ftype_of_float_of_ftype.
    rewrite Raux.Rlt_bool_true by lra.
    destruct 1 as (? & ? & _).
    unfold BMINUS, BINOP; rewrite float_of_ftype_of_float; auto.
  }
  {
    (* mult *)
    generalize (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (float_of_ftype e1) (float_of_ftype e2)).
    change (SpecFloat.fexp _ _) with (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
    change (BinarySingleNaN.round_mode _) with ZnearestE.
    rewrite <- !FT2R_ftype_of_float, !ftype_of_float_of_ftype.
    rewrite Raux.Rlt_bool_true by lra.
    rewrite F1. rewrite F2.
    simpl andb.
    destruct 1 as (? & ? & _).
    unfold BMULT, BINOP; rewrite float_of_ftype_of_float; auto.
  }
  (* div *)
  generalize (fun K => Bdiv_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (div_nan _) BinarySingleNaN.mode_NE (float_of_ftype e1) (float_of_ftype e2) K).
    change (SpecFloat.fexp _ _) with (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
    change (BinarySingleNaN.round_mode _) with ZnearestE.
    rewrite <- !FT2R_ftype_of_float, !ftype_of_float_of_ftype.
    rewrite Raux.Rlt_bool_true by lra.
  rewrite F1.
  destruct 1 as (? & ? & _).
  {
    specialize (COND _ (or_introl _ (refl_equal _))).
    simpl in COND.
    specialize (COND _ Herr).
    apply Rabs_lt_pos in COND.
    congruence.
  }
    unfold BDIV, BINOP; rewrite float_of_ftype_of_float; auto.
Qed.

Theorem fop_of_rounded_unop_correct `{coll: collection} shift errors
    (Herr: errors_bounded shift errors)
        ty (STD: is_standard ty) e1
        (F1: is_finite e1 = true)
        env r1
        (V1: reval r1 env errors = FT2R e1)
        r
        (V_: reval r env errors =
            Generic_fmt.round Zaux.radix2
                                    (FLT.FLT_exp
                                       (3 - femax ty - fprec ty)
                                       (fprec ty)
                                    )
                                    (Generic_fmt.Znearest (fun x : Z => negb (Z.even x)))
                                    (reval (Runop_of_rounded_unop ty SQRT r1) env errors))
        (COND:
           (forall i,
              In i ((r1, false) :: nil) ->
              eval_cond1 env shift i))
:
  is_finite (fop_of_rounded_unop SQRT ty _ e1) = true /\
  FT2R (fop_of_rounded_unop SQRT ty _ e1) =
  reval r env errors.
Proof.
  intros.
  rewrite V_ in * |- *.
  clear r V_.
  repeat rewrite B2R_correct in *.
    cbn -[Zminus] in * |- * ;
    rewrite V1 in * |- *.
    generalize (Bsqrt_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (sqrt_nan _) 
          BinarySingleNaN.mode_NE (float_of_ftype e1)).
    destruct 1 as (? & ? & _).
    unfold BSQRT, UNOP.
    rewrite FT2R_ftype_of_float.
    rewrite <- (FT2R_ftype_of_float (float_of_ftype e1)), ftype_of_float_of_ftype in H.
    rewrite is_finite_Binary in *. rewrite float_of_ftype_of_float in *.
    split; auto.
    specialize (COND _ (or_introl _ (refl_equal _))).
    simpl in COND.
    specialize (COND _ Herr).
    rewrite V1 in COND.
    clear r1 V1.
    rewrite <- (ftype_of_float_of_ftype _ _ e1), FT2R_ftype_of_float in COND.
    destruct (float_of_ftype e1); auto.
    destruct s; auto.
    exfalso.
    revert COND.
    clear.
    simpl.
    clear e0.
    unfold Defs.F2R.
    simpl.
    assert (0 < INR (Pos.to_nat m) * Raux.bpow Zaux.radix2 e).
    {
      apply Rmult_lt_0_compat.
      {
        apply pos_INR_nat_of_P.
      }
      apply Raux.bpow_gt_0.
    }
   rewrite INR_IZR_INZ in H.
   intro.
   replace (IZR (Z.neg m)) with (- IZR (Z.of_nat (Pos.to_nat m))) in COND.
   lra.
   rewrite <- opp_IZR.
   f_equal.
   rewrite <- Pos2Z.opp_pos.
   f_equal.
   apply positive_nat_Z.
Qed.

Lemma rndval_with_cond_correct_uInvShift:
forall `{coll: collection} (env : environ)
 (Henv : forall (ty : type) IN (i : FPLang.V), is_finite (env ty IN i) = true)
(pow : positive)
 (ltr : bool) ty (STDty: is_standard ty) 
 (e : expr ty) (si : positive) (r1 : rexpr) (s1 : MSHIFT)
 (errors1 errors1_1 : positive-> R)
 (E1 : same_upto si errors1 errors1_1)
 (EB1 : errors_bounded s1 errors1_1)
 (F1 : is_finite (fval env e) = true)
 (V1 : reval r1 env errors1_1 = FT2R (fval env e))
 (H0 : expr_valid e)
 (shift : MSHIFT) (r : rexpr) (si2 : positive) (s : MSHIFT) (si1 : positive) (p1 : list cond) 
 (EQ1 : rndval_with_cond' si shift e = (r1, (si1, s1), p1))
 (p_ : list (rexpr * bool))
  (EQ : rnd_of_unop_with_cond si1 s1 ty (Rounded1 (InvShift pow ltr) None) r1 =
     (r, (si2, s), p_))
 (H1 : forall i : cond, In i (p_ ++ p1) -> eval_cond1 env s i) 
 (H2 : errors_bounded shift errors1)
 (K_ : rnd_of_unop si1 s1 ty (Rounded1 (InvShift pow ltr) None) r1 = (r, (si2, s))),
exists errors2 : positive -> R,
   same_upto si errors1 errors2 /\
  (forall i, Rabs (errors2 i) <= error_bound (mget s i)) /\
  is_finite (fop_of_unop (Rounded1 (InvShift pow ltr) None) ty _ (fval env e)) = true /\
  reval r env errors2 =
  FT2R (fop_of_unop (Rounded1 (InvShift pow ltr) None) ty _ (fval env e)).
Proof.
intros.
assert (K1 := rndval_with_cond_left EQ1).
inversion EQ; clear EQ; subst.
set (op := RBinop Tree.Mul _) in *.
set (s := mset s1 si1 (ty, Denormal')) in *.
pose (eps :=
  FT2R (fop_of_unop (Rounded1 (InvShift pow ltr) None) ty _ (fval env e)) -
  F2R radix2 (B2F (B2 ty (Z.neg pow))) * reval r1 env errors1_1).
pose (errors2 i := if Pos.eq_dec i si1  then eps else errors1_1 i).
exists errors2.
split; [ | split; [ | split]].
-
intro; intros. unfold errors2.
destruct (Pos.eq_dec i si1); auto.
pose proof (rndval_shift_incr _ _ _ _ _ _ _ K1). lia.
-
subst errors2.
simpl.
intros.
subst s; simpl.
rewrite mget_set.
destruct (Pos.eq_dec i si1).
 + subst.
  unfold error_bound.
  subst eps.
  rewrite V1.
 change (bpow radix2 1) with 2.
 apply InvShift_accuracy; auto.
 +
  clear eps.
  destruct (Pos.lt_total i si).
 *rewrite E1 by auto. 
   erewrite rndval_shift_unchanged; eauto.
 * apply EB1; auto.
- apply InvShift_finite; auto.
-
 subst op. unfold reval; fold reval.
 replace (reval r1 env errors2) with (reval r1 env errors1_1).
2:{
   apply reval_error_ext; intros.
   unfold errors2.
 destruct (Pos.eq_dec i si1); auto.
  subst i.
  pose proof (rndval_shift_le _ _ _ _ _ _ _ K1). lia.
}
  subst errors2.
  subst eps.
  rewrite V1.
  simpl.
  destruct (Pos.eq_dec si1 si1) as [ _ |]; [ | congruence].
  destruct ltr; ring.
Qed.

Definition rwcc errors1 `{coll: collection} si (s: MSHIFT) env ty (e: expr ty) r := 
      exists errors2,
        same_upto si errors1 errors2
        /\
        errors_bounded s errors2
        /\
        let fv := fval env e in
        is_finite fv = true
        /\
        reval r env errors2 = FT2R fv.

Definition fvalr_klist `{coll: collection} (env: environ) {T: Type} :=
  fix fvalr_klist {l1: list type} (l': klist expr l1) (f: function_type (map RR l1) T) {struct l'}: T :=
          match  l' in (klist _ l) return (function_type (map RR l) T -> T)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => fvalr_klist tl (f0 (FT2R (fval env h)))
          end f.

Definition apply_errors (r: R) (si: positive) (errors: positive -> R) rel abs :=
  r * (1 + (IZR (Z.of_N rel)) * errors si) + (IZR (Z.of_N abs)) * errors (Pos.succ si).


Lemma IZR_N_mult_div:
  forall p x, IZR (Zpos p) * (x / IZR (Zpos p)) = x.
Proof.
intros.
unfold Rdiv.
rewrite Rmult_comm.
rewrite Rmult_assoc.
rewrite (Rmult_comm (/ _)).
rewrite Rinv_r. lra.
apply IZR_neq.
intro; discriminate.
Qed.

Lemma rnd_of_func'_e `{coll: collection}:
  forall si s ty rel abs ff r r2 x,
  rnd_of_func' si s ty rel abs (RFunc ty ff r) = (r2, x) ->
  forall env errors,
  reval r2 env errors =
  apply_errors (reval_klist env errors r (ff_realfunc ff)) si errors rel abs.
Proof.
clear.
intros.
unfold rnd_of_func' in H.
inversion H; clear H; subst.
unfold apply_errors.
simpl.
rewrite !Rmult_1_r. reflexivity.
Qed.

Definition rfval_klist `{coll: collection} (env: environ) :=
  fix fval_klist {l1: list type} (l': klist expr l1) (f: function_type (map RR l1) R) {struct l'}: R :=
          match  l' in (klist _ l) return (function_type (map RR l) R -> R)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => fval_klist tl (f0 (FT2R (fval env h)))
          end f.

Fixpoint list_real_args (xl: list R) (tys: list type): function_type (map RR tys) (list R) :=
  match tys as l return (function_type (map RR l) (list R)) with
  | [] => rev xl
  | _ :: tys' => (fun x : R => list_real_args (x :: xl) tys')
  end.

Definition rwcc_klist errors1 `{coll: collection} si (s: MSHIFT) env tys (args: klist expr tys) (r: klist (fun _ => rexpr) tys) := 
      exists errors2,
        same_upto si errors1 errors2
        /\
        errors_bounded s errors2
        /\
        let fv := mapk (fun ty => @fval _ _ env ty) args in
        Kforall (fun ty (f: ftype ty) => is_finite f = true) fv
        /\
        mapk (fun ty r => reval r env errors2) r = mapk (fun ty (x: ftype' ty) => FT2R x) fv.

Definition adjust_err (coeff: N) (delta: R) := match coeff with N0 => R0 | Npos x => delta / IZR (Zpos x) end.

Lemma Rabs_adjust_le:
  forall coeff delta bd, Rabs delta <= error_bound bd -> Rabs (adjust_err coeff delta) <= error_bound bd.
Proof.
 intros. destruct coeff; simpl. change R0 with 0. rewrite Rabs_R0. apply error_bound_nonneg.
 eapply Rle_trans; [ clear H | eassumption].
 unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv. rewrite Rabs_Zabs. simpl.
 apply Rle_trans with (Rabs delta * 1); [ | lra].
 apply Rmult_le_compat_l. apply Rabs_pos.
 replace 1 with (/ 1) by nra. apply Rinv_le. lra. apply IZR_le. lia.
Qed.

Lemma B2R_float_of_ftype: forall {ty} {STD: is_standard ty} (x: ftype ty),
    B2R _ _ (float_of_ftype x) = FT2R x.
Proof.
intros.
rewrite <- (ftype_of_float_of_ftype _ _ x).
rewrite FT2R_ftype_of_float.
rewrite ftype_of_float_of_ftype; auto.
Qed.

Lemma cast_standard: forall NAN tto tfrom STDto STDfrom f,
  @cast NAN tto tfrom STDto STDfrom (f: ftype tfrom) =
  match type_eq_dec tfrom tto STDfrom STDto with
    | left r => eq_rect _ _ f _ r
    | _ =>  ftype_of_float
           (Bconv (fprec tfrom) (femax tfrom) (fprec tto) (femax tto)
                        (fprec_gt_0 _) (fprec_lt_femax _) (conv_nan _ _) 
                 BinarySingleNaN.mode_NE (float_of_ftype f))
  end.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _ _ _).
- subst. reflexivity.
- destruct tto as [? ? ? ? ? [|]]; try contradiction.
  destruct tfrom as [? ? ? ? ? [|]]; try contradiction.
  reflexivity.
Qed.

Lemma F2R_FT2F: forall ty (x: ftype ty), F2R radix2 (FT2F x) = FT2R x.
Proof.
intros.
unfold FT2F, FT2R.
destruct ty as [? ? ? ? ? [|]]; simpl.
unfold nonstd_to_R.
unfold F2R, Defs.F2R.
destruct (@nonstd_to_F fprecp femax fprec_lt_femax_bool fprecp_not_one_bool n x).
destruct f; simpl. auto. lra.
unfold F2R, B2F, B2R.
destruct x; auto; lra.
Qed.

Lemma rndval_with_cond_correct_klist : 
   forall `{coll: collection} env (Henv: forall ty IN i, is_finite (env ty IN i) = true) 
        tys (args: klist expr tys)
  (IH : Kforall
       (fun (ty : type) (e : expr ty) =>
        expr_valid e ->
        forall si shift r si' s' p,
           rndval_with_cond' si shift e = (r, (si', s'), p) ->
        (forall i : rexpr * bool, In i p -> eval_cond1 env s' i) ->
        forall errors1 : positive -> R,
        errors_bounded shift errors1 -> rwcc errors1 si s' env ty e r)
       args),
  expr_klist_valid args ->
  forall si shift r si' s' p,
    rndval_with_cond'_klist si shift args = ((r, (si', s')), p) ->
    (forall i, In i p -> eval_cond1 env s' i) ->
    forall errors1, errors_bounded shift errors1 ->
    rwcc_klist errors1 si s' env tys args r.
Proof.
  induction args; intros.
-
 rewrite (klist_nil r).
 exists errors1; simpl.
 split; [ | split; [ | split]].
 intros ? ?; auto.
 simpl in H0. inversion H0; clear H0; subst; auto.
 constructor.
 auto.
-
 destruct H.
 apply Kforall_inv in IH; destruct IH as [IH1 IH].
 simpl in H0. 
 destruct (rndval_with_cond' si shift k) as [[r1 [si1 s1]] p1] eqn:?H.
 destruct (rndval_with_cond'_klist si1 s1 args) as [[r2 [si2 s2]] p2] eqn:?H.
 inversion H0; clear H0; subst.
 specialize (IHargs IH H3 _ _ _ _ _ _ H5); clear IH H3.
 apply (IH1 H _ _ _ _ _ _ H4) in H2; clear IH1.
2:{ intros. eapply eval_cond1_preserved; try apply H1.
     intros. subst i.
  pose proof (rndval_with_cond_klist_left H5).
  pose proof (rndval_with_cond_left H4).
  intros ? ?.
  rewrite (rndval_klist_shift_unchanged _ _ _ _ _ _ _ H3); auto.
  pose proof (rndval_with_cond_shift_cond _ _ _ _ _ _ _ _ H4 _ _ H0). lia.
  apply in_app_iff; auto.
}
 destruct H2 as [errors2 [? [? [? ?]]]].
 apply IHargs in H2; clear IHargs.
2:{ intros; apply H1. 
  apply in_app_iff; auto.
}
 destruct H2 as [errors3 [? [? [? ?]]]].
 pose proof (rndval_with_cond_left H4).
 pose proof (rndval_shift_incr _ _ _ _ _ _ _ H10).
 exists errors3; split; [ |split; [ | split]]; auto.
 intros ? ?.
 rewrite  H2. auto. lia.
 constructor; auto.
 rewrite mapk_mapk in H9|-*.
 simpl. f_equal; auto.
 rewrite <- H6.
 apply reval_error_ext; intros.
 apply H2.
 apply rndval_shift_le in H10; lia.
Qed.

Theorem rndval_with_cond_correct' 
   `{coll: collection} env (Henv: forall ty IN i, is_finite (env ty IN i) = true) ty (e: expr ty) :
  expr_valid e ->
  forall si shift r si' s' p,
    rndval_with_cond' si shift e = ((r, (si', s')), p) ->
    (forall i, In i p -> eval_cond1 env s' i) ->
    forall errors1, errors_bounded shift errors1 ->
    rwcc errors1 si s' env ty e r.
Proof.
  induction e; intros.
-  (* const *)
    unfold rwcc.
    simpl in *.
    rewrite <- (float_of_ftype_of_float _ _ f), <- is_finite_Binary in H.
    inversion H0; clear H0; subst.
    simpl.
    exists errors1.
    split. intro; auto.
    split; auto.
    split; auto.
    symmetry.
    rewrite FT2R_ftype_of_float, F2R_eq.
    apply B2F_F2R_B2R.
- (* var *)
    unfold rwcc.
    simpl in *.
    inversion H0; clear H0; subst. unfold same_upto.
    eauto.
-  (* binop *)
    simpl in *.
    destruct (rndval_with_cond' si shift e1) as [[r1 [si1 s1]] p1] eqn:EQ1.
    destruct (rndval_with_cond' si1 s1 e2) as [[r2 [si2_ s2]] p2] eqn:EQ2.
    destruct (rnd_of_binop_with_cond si2_ s2 ty b r1 r2) as [rs p_] eqn:EQ.
    inversion H0; clear H0; subst.
    destruct H.

    assert (K1 := rndval_with_cond_left EQ1).
    assert (K2 := rndval_with_cond_left EQ2).
    assert (K_ := rnd_of_binop_with_cond_left EQ).

   assert (N : forall i : cond, In i p1 -> eval_cond1 env s1 i).
    {
      intros. 
      apply (eval_cond1_preserved s').
      {
        intros. intro.
        subst.
        symmetry.
        etransitivity.
        {
          eapply rnd_of_binop_shift_unchanged; eauto.
          eapply Pos.lt_le_trans; [ eassumption | ].
          etransitivity.
          eapply rndval_with_cond_shift_cond; [ | eassumption ] ; eauto.
          eapply rndval_shift_incr; eauto.
        }
        eapply rndval_shift_unchanged; eauto.
        eapply Pos.lt_le_trans; [ eassumption | ].
        eapply rndval_with_cond_shift_cond; eauto.
      }
      apply H1. apply in_or_app. right. apply in_or_app. auto.
    }
    specialize (IHe1 H _ _ _ _ _ _ EQ1 N _ H2).
    clear N.
    destruct IHe1 as (errors1_1 & E1 & EB1 & F1 & V1).
    assert (N : forall i : cond, In i p2 -> eval_cond1 env s2 i).
    {
      intros.
      apply (eval_cond1_preserved s').
      {
        intros; intro.
        subst.
        symmetry.
        eapply rnd_of_binop_shift_unchanged; eauto.
        eapply Pos.lt_le_trans; [ eassumption | ].
        eapply rndval_with_cond_shift_cond; [ | eassumption ] ; eauto.
      }
      apply H1. apply in_or_app. right. apply in_or_app. auto.
    }
    specialize (IHe2 H0 _ _ _ _ _ _ EQ2 N _ EB1).
    clear N.
    destruct IHe2 as (errors1_2 & E2 & EB2 & F2 & V2).
    rewrite <- (reval_error_ext errors1_2) in V1
     by (intros; apply E2; eapply Pos.lt_le_trans; [ eassumption | eapply rndval_shift_le; eauto]).
    destruct b.
   + (* rounded binary operator *)
        simpl.
        simpl in EQ.
        destruct (
            make_rounding si2_ s2 (round_knowl_denote knowl) ty
                          (RBinop (Rbinop_of_rounded_binop op) r1 r2)
          ) eqn:ROUND.
        inversion EQ; clear EQ; subst.
        simpl.

        generalize (make_rounding_correct _ _ _ _ _ _ _ _ ROUND).
        intro K.
        simpl max_error_var in K.
        assert (L: (Pos.max (max_error_var r1) (max_error_var r2) <= si2_)%positive).
        {
          intros.
          apply Pos.max_lub.
          {
            eapply Pos.le_trans; [ eapply rndval_shift_le; eauto | ].
            eapply rndval_shift_incr; eauto.
          }
          eapply rndval_shift_le; eauto.
        }
        specialize (K L _ EB2).
        clear L.
        assert (L: rounding_cond ty (round_knowl_denote knowl)
                            (reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors1_2)).
        {
          eapply rounding_cond_ast_correct; [ eassumption | ].
          intros.
          eapply (eval_cond1_preserved s').
          {
            intros; intro.
            subst.
            symmetry.
            apply rounding_cond_ast_shift in H3.
            simpl in H3.
            
            eapply make_rounding_shift_unchanged; eauto.
            eapply Pos.lt_le_trans; eauto.
            etransitivity; try eassumption.
            apply Pos.max_lub; eauto using rndval_shift_le.
            etransitivity; [ eapply rndval_shift_le; eauto | ].
            eapply rndval_shift_incr; eauto.
          }
          eapply H1. apply in_or_app. left. apply in_or_app. right. right. assumption.
        }
        specialize (K _ L (fun x : Z => negb (Z.even x))).
        clear L.
        destruct K as (errors2 & E & R & EB).
        assert (W1: reval r1 env errors2 = reval r1 env errors1_2). {
          apply reval_error_ext.
          intros.
          apply E.
          eapply Pos.lt_le_trans; [ eassumption | ].
          etransitivity; [ eapply rndval_shift_le; eauto | ].
          eapply rndval_shift_incr; eauto.
        }

        assert (W2: reval r2 env errors2 = reval r2 env errors1_2). {
          apply reval_error_ext.
          intros.
          apply E.
          eapply Pos.lt_le_trans; [ eassumption | ].
          eapply rndval_shift_le; eauto.
        }
        rewrite <- W1, <- W2 in *.
        assert (
            reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors1_2
            =
            reval (RBinop (Rbinop_of_rounded_binop op) r1 r2) env errors2
        ) as W.
        {
          simpl.
          congruence.
        }
        rewrite W in * |- *. clear W.

        assert (L : forall i : rexpr * bool,
             In i (if is_div op then (RUnop Tree.Abs r2, true) :: nil else nil) ->
             eval_cond1 env s' i).
        {
          intros.
          apply H1.
          apply in_or_app.
          left.
          apply in_or_app.
          auto.
        }
       assert (L': eval_cond1 env s'
            (no_overflow ty r)).
        {
          apply H1.
          apply in_or_app.
          left.
          apply in_or_app.
          right.
          left.
          auto.
        }

        assert (K := fop_of_rounded_binop_correct _ _ _ EB 
                                                 _ _ _ F1
                                                 _ _ V1
                                                 _ F2
                                                 _ V2
                                                 _ R L L').
        clear L L'.

        destruct K.
        exists errors2.
        split; auto.
        intros ? ?.
        etransitivity.
        {
          eapply E.
          eapply Pos.lt_le_trans; [ eassumption | ].
          etransitivity; [ eapply rndval_shift_incr; eauto | ].
          eapply rndval_shift_incr; eauto.
        }
        etransitivity.
        {
          eapply E2.
          eapply Pos.lt_le_trans; [ eassumption | ].
          eapply rndval_shift_incr; eauto.
        }
        eauto.
    + (* Sterbenz *)      
        simpl.
        simpl in EQ.
        inversion EQ; clear EQ; subst.
        simpl.
        generalize (H1 _ (or_introl _ (refl_equal _))).
        specialize (fun j K => H1 j (or_intror _ K)).
        specialize (H1 _ (or_introl _ (refl_equal _))).
        simpl in H1 |- * .
        intro H1'.
        rewrite Rmult_1_l in *.
        specialize (H1 _ EB2).
        specialize (H1' _ EB2).
        rewrite is_finite_Binary in F1,F2.
        generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
        intro K.
        change ( Z.pos (fprecp ty)) with (fprec ty) in K.
        rewrite !B2R_float_of_ftype in *.
        rewrite <- V1 in K.
        rewrite <- V2 in K.
        rewrite Generic_fmt.round_generic in K; try typeclasses eauto.
        {
          destruct (Rlt_dec
                      (Rabs (reval r1 env errors1_2 - reval r2 env errors1_2))
                      (Raux.bpow Zaux.radix2
                                       (femax ty))
                   ).
          {
            apply Raux.Rlt_bool_true in r.
            rewrite r in K.
            destruct K as (KR & KF & _).
            exists errors1_2.
            simpl fval. unfold BMINUS, BINOP.
            rewrite is_finite_Binary, float_of_ftype_of_float.
            rewrite FT2R_ftype_of_float.
            split; auto.
            intros; intro.
            etransitivity.
            {
              eapply E2.
              eapply Pos.lt_le_trans; [ eassumption | ].
              eapply rndval_shift_incr; eauto.
            }
            auto.
          }
          exfalso.
          pose proof 
          (abs_B2R_lt_emax _ _ (float_of_ftype (fval env e1))).
          pose proof 
          (abs_B2R_lt_emax _ _ (float_of_ftype (fval env e2))).
          rewrite !B2R_float_of_ftype in *.
          rewrite <- V1 in H3.
          rewrite <- V2 in H4.
          apply Raux.Rabs_lt_inv in H3.
          apply Raux.Rabs_lt_inv in H4.
          generalize (sterbenz_no_overflow _ _ _ H3 H4 H1 H1').
          clear K.
          intro K.
          apply Raux.Rabs_lt in K.
          contradiction.
        }
        apply Sterbenz.sterbenz; try typeclasses eauto.
        * rewrite V1. rewrite <- B2R_float_of_ftype. apply generic_format_B2R.
        * rewrite V2. rewrite <- B2R_float_of_ftype. apply generic_format_B2R.
        * lra.

    + (* plus zero *)
        unfold rwcc.
        simpl.
        simpl in EQ.
        inversion EQ; clear EQ; subst.
        simpl.
        specialize (H1 _ (or_introl _ (refl_equal _))).
        simpl in H1 |- * .
        specialize (H1 _ EB2).        
        exists errors1_2.
        split.
        *
          intros; intro.
          etransitivity.
          {
            eapply E2.
            eapply Pos.lt_le_trans; [ eassumption | ].
            eapply rndval_shift_incr; eauto.
          }
          eauto.
        * split; auto.
         assert (reval (if zero_left then r1 else r2) env errors1_2 = 0) as ZERO.
         {
          rewrite <- Rabs_zero_iff.
          apply Rle_antisym; [lra | ].
          apply Rabs_pos.
         }
         destruct zero_left.
         --
          rewrite V1 in ZERO. rewrite <- B2R_float_of_ftype in ZERO.
          pose proof (abs_B2R_lt_emax _ _ (float_of_ftype (fval env e2))).
          rewrite is_finite_Binary in F1,F2.
          destruct minus.
          ++
            unfold BMINUS, BINOP.
            generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
            rewrite ZERO.
            rewrite Rminus_0_l.
            rewrite Generic_fmt.round_opp.
            rewrite Generic_fmt.round_generic
               by (try typeclasses eauto; apply generic_format_B2R).
            rewrite Rabs_Ropp.
            rewrite Raux.Rlt_bool_true by assumption.
            unfold BMINUS.
            unfold BINOP.
            simpl reval.
            destruct 1 as (BV & BF & _).
            simpl femax in BV, BF |- * .
            rewrite <- B2R_float_of_ftype in V2.
            rewrite FT2R_ftype_of_float,
                   is_finite_Binary, float_of_ftype_of_float, BV.
            intuition auto with *.
          ++
            generalize (Bplus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
            rewrite ZERO.
            rewrite Rplus_0_l.
            rewrite Generic_fmt.round_generic
               by (try typeclasses eauto; apply generic_format_B2R).
            rewrite Raux.Rlt_bool_true by assumption.
            unfold BPLUS.
            unfold BINOP.
            simpl reval.
            destruct 1 as (BV & BF & _).
            simpl femax in BV, BF |- * .
            rewrite <- B2R_float_of_ftype in V2.
            rewrite FT2R_ftype_of_float,
                   is_finite_Binary, float_of_ftype_of_float, BV.
            intuition.
                      
        --
          rewrite V2 in ZERO.  rewrite <- B2R_float_of_ftype in ZERO.
          pose proof (abs_B2R_lt_emax _ _ (float_of_ftype (fval env e1))).
          rewrite is_finite_Binary in F1,F2|-*.
          destruct minus.
          {
          generalize (Bminus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
          rewrite ZERO.
          rewrite Rminus_0_r.
          rewrite Generic_fmt.round_generic; try typeclasses eauto.
          {
            rewrite Raux.Rlt_bool_true by assumption.
            unfold BMINUS.
            unfold BINOP.
            simpl reval.
            destruct 1 as (BV & BF & _).
            simpl femax in BV, BF |- * .
              rewrite <- B2R_float_of_ftype in V1,V2.
              rewrite FT2R_ftype_of_float,
                     float_of_ftype_of_float, BV.
            intuition.
          }
          apply generic_format_B2R.
         }
         generalize (Bplus_correct _ _  (fprec_gt_0 _) (fprec_lt_femax _) (plus_nan _) BinarySingleNaN.mode_NE _ _ F1 F2).
         rewrite ZERO.
         rewrite Rplus_0_r.
         rewrite Generic_fmt.round_generic; try typeclasses eauto.
         {
          rewrite Raux.Rlt_bool_true by assumption.
          unfold BPLUS.
          unfold BINOP.
          simpl reval.
          destruct 1 as (BV & BF & _).
          simpl femax in BV, BF |- * .
              rewrite <- B2R_float_of_ftype in V1,V2.
              rewrite FT2R_ftype_of_float,
                     float_of_ftype_of_float, BV.
          intuition.
         }
         apply generic_format_B2R.          

- (* unop *)
  simpl in *.
  destruct (rndval_with_cond' si shift e) as [[r1 [si1 s1]] p1] eqn:EQ1.
  destruct (rnd_of_unop_with_cond si1 s1 ty u r1) as [rs p_] eqn:EQ.
  inversion H0; clear H0; subst.
  destruct H.

  assert (K1 := rndval_with_cond_left EQ1).
  assert (K_ := rnd_of_unop_with_cond_left EQ).

  assert (N: forall i : cond, In i p1 -> eval_cond1 env s1 i).
  {
    intros.
    apply (eval_cond1_preserved s').
    {
      intros; intro; subst.
      symmetry.
      eapply rnd_of_unop_shift_unchanged; eauto.
      eapply Pos.lt_le_trans; eauto.
      eapply rndval_with_cond_shift_cond; eauto.
    }
    apply H1. apply in_or_app. auto.
  }
  specialize (IHe H0 _ _ _ _ _ _ EQ1 N _ H2).
  clear N.
  destruct IHe as (errors1_1 & E1 & EB1 & F1 & V1).

  destruct u.
 + (* rounded unary operator *)
    simpl.
  destruct op.
  * (* SQRT *)
    simpl in EQ.
    unfold Datatypes.id in *.
    destruct (
        make_rounding si1 s1 (round_knowl_denote knowl)
                      ty (RUnop Tree.Sqrt r1)
      ) eqn:ROUND.
    inversion EQ; clear EQ; subst.

    assert (K := make_rounding_correct _ _ _ _ _ _ _ _ ROUND).
    simpl max_error_var in K.
    assert (L:  (max_error_var r1 <= si1)%positive).
    {
      intros.
      eapply rndval_shift_le; eauto.
    }
    assert (L': rounding_cond ty (round_knowl_denote knowl)
      (reval (RUnop Tree.Sqrt r1)env errors1_1)).
    {
      eapply rounding_cond_ast_correct; [ eassumption | ].
      intros.
      eapply (eval_cond1_preserved s').
      {
        intros; intro; subst.
        symmetry.
        apply rounding_cond_ast_shift in H3.
        simpl in H3.
        eapply rnd_of_unop_shift_unchanged; eauto.
        eapply Pos.lt_le_trans; eauto.
        etransitivity; try eassumption.
      }
      eapply H1.
      apply in_or_app.
      left.
      right.
      assumption.
    }
    specialize (K L _ EB1 _ L' (fun x : Z => negb (Z.even x))).
    clear L L'.
    destruct K as (errors2 & E & R & EB).

    assert (W1: reval r1 env errors2 = reval r1 env errors1_1).
    {
      apply reval_error_ext.
      intros.
      apply E.
      eapply Pos.lt_le_trans; [ eassumption | ].
      eapply rndval_shift_le; eauto.
    }
    rewrite <- W1 in V1.

    assert (
        reval (RUnop Tree.Sqrt r1) env errors1_1
        =
        reval (RUnop Tree.Sqrt r1) env errors2
      ) as W.
    {
      simpl.
      congruence.
    }
    rewrite W in * |- *. clear W.

   assert (L : forall i : rexpr * bool,
     In i ((r1, false) :: nil) ->
     eval_cond1 env s' i).
    {
      intros.
      apply H1.
      apply in_or_app.
      left.   destruct H3. left; auto. destruct H3.
    }
    assert (K := fop_of_rounded_unop_correct _ _ EB 
                                             _ _ _ F1
                                             _ _ V1
                                             _ R L).
    clear L.

    destruct K.
    exists errors2.
    split; auto.
    intros; intro.
    etransitivity.
    {
      eapply E.
      eapply Pos.lt_le_trans; [eassumption | ].
      eapply rndval_shift_incr; eauto.
    }
    eauto.
  * (* InvShift *)
   destruct knowl as [ [ | ] | ].
  -- (* Normal *)
    simpl.
    cbn -[Zminus] in EQ.
    unfold Datatypes.id in *.
    Opaque Zminus.
    inversion EQ; clear EQ; subst.
    Transparent Zminus.

    exists errors1_1.
    split; auto.
    split; auto.
    cbn -[Zminus] in * |- *.
    rewrite F2R_eq.
    rewrite <- B2F_F2R_B2R.
    rewrite Z.leb_le in H.
    apply center_Z_correct in H.
    assert (B2_FIN := B2_finite ty (Z.neg pow) (proj2 H)).
    generalize (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) (float_of_ftype (fval env e))).
    generalize (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) (float_of_ftype (fval env e))).
    rewrite Rmult_comm.
    change (SpecFloat.fexp (fprec ty) (femax ty))
     with  (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
    rewrite (B2_correct _ (Z.neg pow) H).
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite Raux.bpow_opp.
    rewrite FLT_format_div_beta_1; try typeclasses eauto.
    {
      unfold Rdiv.
      rewrite <- Raux.bpow_opp.
      rewrite <- is_finite_Binary, F1.
      rewrite B2_FIN.
      simpl andb.
      rewrite Raux.Rlt_bool_true.
      {
        unfold BMULT, BINOP.
        destruct 1 as (LC & ? & ?).
        destruct 1 as (L & ? & ?).
        rewrite <- B2R_float_of_ftype.
        rewrite is_finite_Binary.
        destruct ltr; rewrite !float_of_ftype_of_float; split; auto; 
          rewrite V1, <- B2R_float_of_ftype.
        {
          rewrite LC.
          ring.
        }
        rewrite L.
        ring.
      }
      rewrite Raux.bpow_opp.
      apply Bdiv_beta_no_overflow.
      rewrite <- is_finite_Binary.
      assumption.
    }
    specialize (H1 _ (or_introl _ (refl_equal _))).
    specialize (H1 _ EB1).
    cbn -[Zminus] in H1. rewrite B2R_float_of_ftype.
    rewrite <- V1.
    lra.
  -- eapply rndval_with_cond_correct_uInvShift; eassumption.
  -- eapply rndval_with_cond_correct_uInvShift; eassumption.

 + (* exact unary operator *)

    simpl.
    cbn -[Zminus] in EQ.
    unfold Datatypes.id in *.
    Opaque Zminus.
    inversion EQ; clear EQ; subst.
    Transparent Zminus.

    exists errors1_1.
    split; auto.
    split; auto.

    destruct o.

   * (* abs *)
      simpl in * |- *.
      unfold BABS.
      rewrite is_finite_Binary, float_of_ftype_of_float.
      rewrite is_finite_Babs, <- is_finite_Binary, FT2R_ftype_of_float.
      split; auto.
      rewrite B2R_Babs, B2R_float_of_ftype.
      congruence.

   * (* opp *)
      simpl in * |- * .
      unfold BOPP.
      rewrite is_finite_Binary, float_of_ftype_of_float.
      rewrite is_finite_Bopp, <- is_finite_Binary, FT2R_ftype_of_float.
      split; auto.
      rewrite B2R_Bopp, B2R_float_of_ftype.
      congruence.

   * (* shift *)
      cbn -[Zminus] in * |- *.
      rewrite F2R_eq.
      rewrite <- B2F_F2R_B2R.
      rewrite Z.leb_le in H.
      apply center_Z_correct in H.
      generalize (B2_finite ty (Z.of_N pow) (proj2 H)).
      intro B2_FIN.
      generalize
          (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.of_N pow)) (float_of_ftype (fval env e))).
      generalize
         (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _) BinarySingleNaN.mode_NE (B2 ty (Z.of_N pow)) (float_of_ftype (fval env e))).
      rewrite Rmult_comm.
      replace (Z.of_N (pow + 1)) with (Z.of_N pow + 1)%Z in H by (rewrite N2Z.inj_add; simpl; ring).
      specialize (H1 _ (or_introl _ (refl_equal _)) _ EB1).
      simpl in H1.
      rewrite F2R_eq, <- B2F_F2R_B2R, V1 in H1.
      rewrite (B2_correct _ _ H) in H1|-*.
    change (SpecFloat.fexp (fprec ty) (femax ty))
     with  (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
      rewrite FLT_format_mult_beta_n; try typeclasses eauto.
      rewrite is_finite_Binary in F1. 
      rewrite F1.
      rewrite B2_FIN.
      simpl andb.
      rewrite Raux.Rlt_bool_true.
      {
        unfold BMULT, BINOP.
        destruct 1 as (LC & ? & ?).
        destruct 1 as (L & ? & ?).
        rewrite is_finite_Binary.        
        destruct ltr; rewrite FT2R_ftype_of_float, !float_of_ftype_of_float;
        split; auto; rewrite V1, <- B2R_float_of_ftype.
        {
          rewrite LC.
          ring.
        }
        rewrite L.
        ring.
      }
      rewrite Rmult_comm, B2R_float_of_ftype.
      lra.

 - (* cast *)
  unfold rwcc.
  simpl in *.
  destruct (rndval_with_cond' si shift e) as [[r1 [si1 s1]] p1] eqn:EQ1.
  destruct (rnd_of_cast_with_cond si1 s1  fromty ty (round_knowl_denote knowl) r1) as [rs p_] eqn:EQ.
  inversion H0; clear H0; subst.

  assert (K1 := rndval_with_cond_left EQ1).
  assert (K2 := rnd_of_cast_with_cond_left EQ).

  assert (N: forall i : cond, In i p1 -> eval_cond1 env s1 i).
  {
    intros.
    apply (eval_cond1_preserved s').
    {
      intros; intro; subst.
      symmetry.
      eapply rnd_of_cast_shift_unchanged; eauto.
      eapply Pos.lt_le_trans; eauto.
      eapply rndval_with_cond_shift_cond; eauto.
    }
    apply H1. apply in_or_app. auto.
  }
  specialize (IHe H _ _ _ _ _ _ EQ1 N _ H2).
  clear N.
  destruct IHe as (errors1_1 & E1 & EB1 & F1 & V1).

  simpl.
  simpl in *.


  
  rewrite cast_standard.
  unfold rnd_of_cast_with_cond in EQ.
  destruct (type_eq_dec fromty ty).
  {
    subst ty.
    simpl.
    rewrite (fun t1 t2 => let (_, K) := type_leb_le t1 t2 in K) in EQ.
    {
      inversion EQ; clear EQ; subst.
      eauto.
    }
    apply type_le_refl.
  }
  
  destruct (type_leb fromty ty) eqn:LEB.
  {
    inversion EQ; clear EQ; subst.
    rewrite type_leb_le in LEB.
    inversion LEB.
    rewrite is_finite_Binary in F1.
    generalize ((fun J1 =>
                  Bconv_widen_exact _ _ _ _ J1 (fprec_gt_0 _) (fprec_lt_femax _) 
                        (Z.le_ge _ _ H0) (Z.le_ge _ _ H3) (conv_nan _ _) BinarySingleNaN.mode_NE _ F1) ltac:( typeclasses eauto ) ).
    destruct 1 as (K & L & _).
    symmetry in K.
    rewrite B2R_float_of_ftype, <- V1 in K.
    rewrite is_finite_Binary, float_of_ftype_of_float.
    rewrite FT2R_ftype_of_float.
    eauto.
  }
  destruct (make_rounding si1 s1 (round_knowl_denote knowl) ty r1) eqn:ROUND.
  inversion EQ; clear EQ; subst.
  generalize (make_rounding_correct _ _ _ _ _ _ _ _ ROUND).
  intro K.
  assert (L: (max_error_var r1 <= si1)%positive).
  {
    eapply rndval_shift_le; eauto.
  }
  assert (L': rounding_cond ty (round_knowl_denote knowl) (reval r1 env errors1_1)).
  {
    eapply rounding_cond_ast_correct.
    {
      eassumption.
    }
    intros.
    eapply (eval_cond1_preserved s').
    {
      intros; intro; subst.
      symmetry.
      apply rounding_cond_ast_shift in H0.
      simpl in H0.
      eapply make_rounding_shift_unchanged; eauto.
      eapply Pos.lt_le_trans; eauto.
      etransitivity; try eassumption.
    }
    eapply H1.
    apply in_or_app.
    left.
    right.
    assumption.
  } 
  specialize (K L _ EB1 _ L'  (fun x : Z => negb (Z.even x))); clear L L'.
  destruct K as (errors2 & E & R & EB).
  rewrite V1 in R.
  rewrite is_finite_Binary in F1.
  generalize (Bconv_correct _ _ _ _ (fprec_gt_0 _) (fprec_lt_femax ty) (conv_nan _ _) BinarySingleNaN.mode_NE _ F1).
  unfold BinarySingleNaN.round_mode.
  rewrite !B2R_float_of_ftype, <- R.
  rewrite Raux.Rlt_bool_true.
  {
    destruct 1 as (J & K & _).
    symmetry in J.
    exists errors2.
    rewrite is_finite_Binary, float_of_ftype_of_float.
    rewrite FT2R_ftype_of_float.
    split; auto.
    intros; intro.
    etransitivity.
    {
      eapply E.
      eapply Pos.lt_le_trans; eauto.
      eapply rndval_shift_incr; eauto.
    }
    auto.
  }
  specialize (H1 _ (or_introl _ (refl_equal _))).
  specialize (H1 _ EB).
  simpl in H1.

  lra.
- (* Func *)
 change (fval env (Func ty f4 args)) with (fval_klist env args (ff_func (ff_ff f4))).
 change (expr_klist_valid args) in H.
 simpl in H0.
 fold (@rndval_with_cond'_klist _) in H0.
 destruct ( rndval_with_cond'_klist si shift args) as [[r2 [si2 s2]] p2] eqn:?H.
 inversion H0; clear H0; subst.
 assert (EC2: forall i : rexpr * bool, In i p2 -> eval_cond1 env s2 i). {
    intros. eapply eval_cond1_preserved; try apply H1.
    intros; subst.
    intros ? ?. 
    apply  (rndval_with_cond_klist_shift_cond _ _ _ _ _ _ _ _ H3) in H0.
    rewrite !mget_set. repeat (destruct (Pos.eq_dec _ _)); try lia. auto.
    right. apply in_app_iff; auto.
 }
 eapply rndval_with_cond_correct_klist in IH; try eassumption; clear H EC2.
 assert (MEV := rndval_with_cond_klist_left H3).
 apply rndval_klist_shift_le in MEV.
 destruct IH as [errors2 [? [? [? ?]]]].
 rewrite mapk_mapk in H5.
 red.
 change (fval env (Func ty f4 args)) with (fval_klist env args (ff_func (ff_ff f4))).
 set (s' := mset (mset _ _ _) _ _).
 set (r := abs_error _ _ _).
 assert (exists errors0 : positive -> R,
     same_upto si errors2 errors0 /\
     errors_bounded s' errors0 /\
     is_finite (fval_klist env args (ff_func (ff_ff f4))) = true /\
     reval r env errors0 = FT2R (fval_klist env args (ff_func (ff_ff f4)))).
 2:{ destruct H6 as [err [? ?]]; exists err; split; auto. intros ? ?. rewrite <- H; auto. }
 assert (Hsi: (si <= si2 /\ max_error_var_klist (ff_args f4) r2 <= si2)%positive). {
    pose proof (rndval_with_cond_klist_left H3).
    pose proof (rndval_klist_shift_incr _ _ _ _ _ _ _ H6).
    pose proof (rndval_klist_shift_le _ _ _ _ _ _ _ H6).
    auto.
  } 
  destruct Hsi as [Hsi Hr2].
  clear errors1 H2 H shift H3.
  assert (forall i, In i (func_no_overflow si2 s2 f4 r2 :: bounds_to_conds (ff_precond f4) r2) -> eval_cond1 env s' i)
     by (intros; apply H1; clear - H; simpl in H|-*; rewrite in_app_iff; tauto). clear H1 p2.
  unfold func_no_overflow, rnd_of_func, rnd_of_func', fst in H. fold r in H.
  set (r4 := RFunc ty f4 r2) in *.
  assert (Hrf: reval_klist env errors2 r2 (ff_realfunc f4) = reval r4 env errors2) by reflexivity.
  change  (max_error_var r4 <= si2)%positive in Hr2.
  clearbody r4.
  destruct f4 as [tys pre rf [f rel abs ACC]]; simpl in *.
  move args before tys.
  clear ff_congr.
  generalize dependent tys.
  clear - Henv H0 Hsi Hr2.
  induction args; intros.
 + simpl in *. rewrite (klist_nil pre), (klist_nil r2) in *. clear pre r2 H4.  simpl in *.
     match type of H with (forall i, ?a = i \/ False -> _) => assert (eval_cond1 env s' a) by (apply H; left; reflexivity) end.
     clear H H5.
     unfold func_no_overflow, no_overflow, rnd_of_func in H1. simpl in H1.
     destruct (Relative.error_N_FLT Zaux.radix2 (3 - femax ty - fprec ty) (fprec ty) (fprec_gt_0 _)
                        (fun x : Z => negb (Z.even x)) rf)
          as [delta [epsilon [K0 [K1 [_ K3]]]]].
     pose (errors3 i := if Pos.eq_dec i (Pos.succ si2) then adjust_err abs epsilon
                          else if Pos.eq_dec i si2 then adjust_err rel delta else  errors2 i).
     assert (errors_bounded s' errors3). {
      intro. unfold errors3, s'.
      rewrite !mget_set.
      repeat destruct (Pos.eq_dec _ _); auto; clear - K0 K1.
       apply  Rabs_adjust_le; auto.
       apply  Rabs_adjust_le; auto.
    }
     assert (reval r4 env errors3 = reval r4 env errors2). {
        apply reval_error_ext. intros. unfold errors3.
        repeat destruct (Pos.eq_dec _ _); auto; lia.
    }
    destruct ACC as [RA [ER ACC]].
     assert (rounded_finite ty rf). {
       red. apply H1 in H. rewrite H2 in H.
       rewrite !Rmult_1_r in *. rewrite Rmult_1_l in *.
       change (SpecFloat.fexp (fprec ty) (femax ty)) with (FLT_exp (3 - femax ty - fprec ty) (fprec ty)).
       change  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)  with ZnearestE.
       subst errors3. simpl in H. 
       assert (rel=0 \/ rel <>0)%N by (clear; tauto).
       destruct H3.
       - assert (abs=0)%N by (rewrite <- RA; auto).  subst abs rel. specialize (ER (eq_refl _)). red in ER; rewrite ER.
          repeat destruct (Pos.eq_dec _ _) in H; try lia. simpl in H. rewrite <- Hrf in H.
          rewrite !Rmult_0_l in H. rewrite !Rplus_0_r in H. rewrite Rmult_1_r in H. lra.
      - assert (abs<>0)%N by (clear - H3 RA; tauto).
          repeat destruct (Pos.eq_dec _ _) in H; try lia. simpl in H. rewrite <- Hrf in H.
          unfold adjust_err in H. destruct rel; try contradiction. destruct abs; try contradiction.
          unfold Z.of_N in H.
         unfold Rdiv in H. rewrite !(Rmult_comm _ (/ _)) in H. rewrite <- !(Rmult_assoc _ (/ _)) in H. 
         rewrite K3.
        rewrite !Rinv_r in H. rewrite !Rmult_1_l in *. lra.
        apply Qreals.IZR_nz.
        apply Qreals.IZR_nz.
      }
     specialize (ACC H3). destruct ACC as [FIN [delta' [epsilon' [? [? ?]]]]].
     pose (errors4 i := if Pos.eq_dec i (Pos.succ si2) then adjust_err abs epsilon'
                          else if Pos.eq_dec i si2 then adjust_err rel delta' else  errors2 i).
     assert (EB4: errors_bounded s' errors4). {
      intro. unfold errors4, s'.
      rewrite !mget_set.
      repeat destruct (Pos.eq_dec _ _); auto; clear - H4 H5.
      destruct abs; simpl. change R0 with 0. rewrite Rabs_R0. apply error_bound_nonneg.
      change (error_bound _) with (default_abs ty). unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
      rewrite (Rabs_right (IZR _)) by (apply IZR_ge; lia). 
      apply Rdiv_le_left; [ apply IZR_lt; lia | rewrite Rmult_comm; auto].
      destruct rel; simpl. change R0 with 0. rewrite Rabs_R0. apply error_bound_nonneg.
      change (error_bound _) with (default_rel ty). unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
      rewrite (Rabs_right (IZR _)) by (apply IZR_ge; lia). 
      apply Rdiv_le_left; [ apply IZR_lt; lia | rewrite Rmult_comm; auto].
    }
      exists errors4; split; auto.
      clear - Hsi; intros ? ?; subst errors4; simpl; repeat destruct (Pos.eq_dec _ _); auto; lia.
      split; auto.
      split; auto.
     assert (reval r4 env errors4 = reval r4 env errors2). {
        apply reval_error_ext. intros. unfold errors4.
        repeat destruct (Pos.eq_dec _ _); auto; lia.
    }
      rewrite H7, <- Hrf. unfold errors4.
        repeat destruct (Pos.eq_dec _ _); try lia.
       rewrite !Rmult_1_r in *. 
        fold (FT2R f). rewrite H6. clear - H4 H5.
        repeat f_equal.
        destruct rel; simpl in *. rewrite Rmult_0_r. rewrite Rmult_0_l in H4.
        assert (Rabs delta' = 0) by (pose proof (Rabs_pos delta'); lra).
        apply Rabs_eq_R0 in H; auto.
        unfold Rdiv. rewrite !(Rmult_comm _ (/ _)). rewrite <- !(Rmult_assoc _ (/ _)). 
        rewrite !Rinv_r by (apply IZR_neq; lia). rewrite !Rmult_1_l. auto.
        destruct abs; simpl in *. rewrite Rmult_0_r. rewrite Rmult_0_l in H5.
        assert (Rabs epsilon' = 0) by (pose proof (Rabs_pos epsilon'); lra).
        apply Rabs_eq_R0 in H; auto.
        unfold Rdiv. rewrite !(Rmult_comm _ (/ _)). rewrite <- !(Rmult_assoc _ (/ _)). 
        rewrite !Rinv_r by (apply IZR_neq; lia). rewrite !Rmult_1_l. auto.

 + apply Kforall_inv in H4. destruct H4.
    change (Kforall
       (fun (ty : type) (f : ftype ty) => is_finite f = true)
       (mapk (fun ty : type => fval env) args)) in H2.
    destruct (klist_cons r2) as [r1 [r2' ?]]; subst r2; rename r2' into r2.
    destruct (klist_cons pre) as [p1 [pre' ?]]; subst pre; rename pre' into pre.
     simpl in ACC.  unfold eq_rect_r, eq_rect, eq_sym in ACC.
     simpl in H5. inversion H5; clear H5; subst.
     apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H6.
     simpl in H. unfold eq_rect_r, eq_rect, eq_sym in H.
      simpl in Hrf.
     pose (errors2' i := if Pos.eq_dec i (Pos.succ si2) then 0
                          else if Pos.eq_dec i si2 then 0 else  errors2 i).
     simpl in MEV.
     assert (MEV1: (max_error_var r1 <= si2)%positive) by (clear - MEV; lia).
     assert (MEV': (max_error_var_klist tys r2 <= si2)%positive) by (clear - MEV; lia). clear MEV.
     assert (EB4: errors_bounded s' errors2'). {
       intro. specialize (H0 i). unfold s', errors2'. clear - H0.
       rewrite !mget_set. 
       repeat destruct (Pos.eq_dec _ _); auto; subst; rewrite Rabs_R0; apply error_bound_nonneg.
     }
      assert (interp_bounds p1 (fval env k) = true). {
         clear - H4 H H1 Hsi Henv EB4 MEV1.
         assert (reval r1 env errors2 = reval r1 env errors2'). {
               apply reval_error_ext; intros; unfold errors2'.
                   repeat destruct (Pos.eq_dec _ _); try lia; auto.
         }
          unfold bounds_to_cond in H.
          destruct p1 as [[lo blo] [hi bhi]]; simpl; rewrite andb_true_iff; split.
          - destruct (vacuous_lo_bound (lo, blo, (hi, bhi))) eqn:H2.
           + clear - H2 H1.
             destruct ty0 as [? ? ? ? ? [|]]; [discriminate |].
             simpl in H2. destruct blo, lo; try destruct s; try discriminate.
             destruct (fval env k); try destruct s; try discriminate; reflexivity.
           + destruct (is_finite lo) eqn:?H.
             * apply (H (RBinop Tree.Sub r1 (RAtom (RConst (FT2F lo))), blo)) in EB4; simpl in EB4.

                rewrite F2R_FT2F in EB4.
                rewrite <- H0, H4 in EB4 by auto.
                destruct blo; unfold compare, extend_comp; simpl;
                rewrite compare'_correct; auto;
                destruct (Rcompare_spec (FT2R lo) (FT2R (fval env k))); auto; lra.
                rewrite in_app_iff; simpl; auto.
             * apply (H False_cond) in EB4; simpl in EB4. lra. rewrite in_app_iff; simpl; auto.
          - destruct (vacuous_hi_bound (lo, blo, (hi, bhi))) eqn:H2.
           + clear - H2 H1.
             destruct ty0 as [? ? ? ? ? [|]]; [discriminate |].
             simpl in H2. destruct bhi, hi; try destruct s; try discriminate; destruct (fval env k); try destruct s; try discriminate; reflexivity.
           + destruct (is_finite hi) eqn:?H.
             * apply (H (RBinop Tree.Sub (RAtom (RConst (FT2F hi))) r1, bhi)) in EB4; simpl in EB4.
                rewrite F2R_FT2F, <- H0, H4 in EB4 by auto.
                destruct bhi; unfold compare, extend_comp; simpl;
                 rewrite compare'_correct; auto;
                destruct (Rcompare_spec (FT2R (fval env k))  (FT2R hi)); auto; lra.
                rewrite !in_app_iff; simpl; auto.
             * apply (H False_cond) in EB4; simpl in EB4. lra. rewrite !in_app_iff; simpl; auto.
        }
     specialize (ACC _ H3).
     apply (IHargs _ _ _ ACC r2); clear IHargs ACC; auto.
     intros; apply H; simpl; rewrite in_app_iff. clear - H5; tauto.
     rewrite <- Hrf, H4; auto.
Qed.

Definition empty_shiftmap := mempty (Tdouble, Unknown').



Definition eval_cond `{coll: collection} (s: MSHIFT) (c: cond) (env: environ) : Prop :=
  eval_cond1 env s c.

Definition rndval_with_cond `{coll: collection} {ty} (e: expr ty) : rexpr * MSHIFT * list (environ -> Prop) :=
 let '((r,(si,s)),p) := rndval_with_cond' 1%positive empty_shiftmap e
  in (r, s, map (eval_cond s) p).

Theorem rndval_with_cond_correct 
    `{coll: collection} env (Henv: env_all_finite env) {ty} (e: expr ty):
  expr_valid e ->
  forall r s p,
    rndval_with_cond e = (r, s, p) ->
    Forall (fun c => c env) p ->
    exists errors,
        (errors_bounded s errors)
        /\
        let fv := fval env e in
        is_finite fv = true
        /\
        reval r env errors = FT2R fv
.
Proof.
intros.
unfold rndval_with_cond in H0.
destruct (rndval_with_cond' _ empty_shiftmap e) as [[r' [si s']] p'] eqn:?H.
inversion H0; clear H0; subst r' s' p.
assert (forall i : cond, In i p' -> eval_cond1 env s i). {
  intros.
  rewrite Forall_forall in H1.
  apply H1. 
  rewrite in_map_iff.
  exists i; auto.
}
destruct (rndval_with_cond_correct' env Henv ty e H 1 empty_shiftmap r _ _ _ H2 H0
 (fun _ => 0%R))
  as [errors2 [? [? [? ?]]]].
-
intros. intro.
rewrite Rabs_R0. apply error_bound_nonneg.
-
exists errors2; split; auto.
Qed.

End WITH_NAN.


