(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(* Core and annotated languages for floating-point operations. *)

Require Import Interval.Tactic.
From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra. (*  lib.Floats. *)
Require compcert.lib.Maps.  
Require Coq.MSets.MSetAVL.
Require vcfloat.Fprop_absolute.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.

Require Export vcfloat.FPCore.
Require Import vcfloat.klist.
Import Bool.
Import Coq.Lists.List ListNotations.

Global Existing Instance fprec_gt_0. (* to override the Opaque one in Interval package *)

Local Open Scope R_scope.

Local Definition V := positive.
Definition     var_eqb: V -> V -> bool := Pos.eqb.
Lemma var_eqb_eq: forall v1 v2, var_eqb v1 v2 = true <-> v1 = v2.
Proof.  apply Pos.eqb_eq. Qed.

Inductive rounded_binop: Type :=
| PLUS
| MINUS
| MULT
| DIV
.

Inductive rounding_knowledge: Type :=
| Normal
| Denormal
.

Inductive binop: Type :=
| Rounded2 (op: rounded_binop) (knowl: option rounding_knowledge)
| SterbenzMinus
| PlusZero (minus: bool) (zero_left: bool) (* use only if one of the two arguments can be shown to be zero *)
.

Inductive rounded_unop: Type :=
| SQRT
| InvShift (pow: positive) (ltr: bool) (* divide by power of two *)
.

Inductive exact_unop: Type :=
| Abs
| Opp
| Shift (pow: N) (ltr: bool) (* multiply by power of two never introduces rounding *)
.

Inductive unop : Type :=
| Rounded1 (op: rounded_unop) (knowl:  option rounding_knowledge)
| Exact1 (o: exact_unop)
.

Inductive rounding_knowledge': Type :=
| Unknown'
| Normal'
| Denormal'
| Denormal2' (* specially for uInvShift *)
.

Definition round_knowl_denote (r: option rounding_knowledge) :=
 match r with
 | None => Unknown'
 | Some Normal => Normal'
 | Some Denormal => Denormal'
 end.

Definition collection_ok (cl: list type) :=
 forall t1 t2, In t1 cl -> In t2 cl ->
        fprec t1 = fprec t2 -> femax t1 = femax t2 -> t1=t2.

Definition collection := sig collection_ok.
Existing Class collection.

Definition incollection {coll: collection} t : Prop :=
 match nonstd t with 
 | Some _ => In t (proj1_sig coll)
 | _ => True
 end.
Existing Class incollection.

Unset Elimination Schemes.

(* See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Coq.20can't.20recognize.20a.20strictly.20positive.20occurrence
   for a discussion of Func1,Func2, etc. *)   
Inductive expr `{coll: collection} (ty: type) : Type :=
| Const (STD: is_standard ty) (f: Binary.binary_float (fprec ty) (femax ty))
| Var (IN: incollection ty) (i: V)
| Binop (STD: is_standard ty) (b: binop) (e1 e2: expr ty)
| Unop (STD: is_standard ty) (u: unop) (e1: expr ty)
| Cast (fromty: type) (STDto: is_standard ty) (STDfrom: is_standard fromty) (knowl: option rounding_knowledge) (e1: expr fromty)
| Func (f: floatfunc_package ty) (args: klist expr (ff_args f))
.

Arguments Binop [coll ty STD] b e1 e2.
Arguments Unop [coll ty STD] u e1.

Set Elimination Schemes.
Lemma expr_ind `{coll: collection}:
  forall P : forall ty : type, expr ty -> Prop,
  (forall (ty : type) STD f, P ty (Const ty STD f)) ->
  (forall (ty : type) (IN: incollection ty) (i : FPLang.V), P ty (Var ty IN i)) ->
  (forall (ty : type) (STD: is_standard ty) (b : binop) (e1 : expr ty),
   P ty e1 -> forall e2 : expr ty, P ty e2 -> P ty (Binop b e1 e2)) ->
  (forall (ty : type) (STD: is_standard ty) (u : unop) (e1 : expr ty), P ty e1 -> P ty (Unop u e1)) ->
  (forall (ty fromty : type) STDto STDfrom (knowl : option rounding_knowledge)
     (e1 : expr fromty), P fromty e1 -> P ty (Cast ty fromty STDto STDfrom knowl e1)) ->
  (forall (ty : type) (f4 : floatfunc_package ty)
    (args : klist expr (ff_args f4))
      (IH: Kforall P args),
      P ty (Func ty f4 args)) ->
  forall (ty : type) (e : expr ty), P ty e.
Proof.
intros.
refine (
(fix F (ty : type) (e : expr ty) {struct e} : P ty e :=
  match e as e0 return (P ty e0) with
  | Const _ _ f5 => H ty _ f5
  | Var _ IN i => H0 ty IN i
  | @Binop _ _ STD b e1 e2 => H1 ty STD b e1 (F ty e1) e2 (F ty e2)
  | @Unop _ _ STD u e1 => H2 ty STD u e1 (F ty e1)
  | Cast _ fromty STDto STDfrom knowl e1 => H3 ty fromty STDto STDfrom knowl e1 (F fromty e1)
  | Func _ f5 args => _ 
    end) ty e).
apply H4.
clear - F f5.
set (tys := ff_args f5) in *. clearbody tys.
induction args.
constructor.
constructor.
apply F.
apply IHargs.
Qed.

Definition Rop_of_rounded_binop (r: rounded_binop): R -> R -> R :=
  match r with
    | PLUS => Rplus
    | MINUS => Rminus
    | MULT => Rmult
    | DIV => Rdiv
  end.

Definition Rop_of_binop (r: binop): R -> R -> R :=
  match r with
    | Rounded2 op _ => Rop_of_rounded_binop op
    | SterbenzMinus => Rminus
    | PlusZero minus zero_left =>
      if zero_left then
        fun _ => if minus then Ropp else (fun x => x)
      else
        fun x _ => x
  end.

Definition Rop_of_rounded_unop (r: rounded_unop): R -> R :=
  match r with
    | SQRT => R_sqrt.sqrt
    | InvShift pow _ => Rmult (Raux.bpow Zaux.radix2 (- Z.pos pow))
  end.

Definition Rop_of_exact_unop (r: exact_unop): R -> R :=
  match r with
    | Abs => Rabs
    | Opp => Ropp
    | Shift pow b =>
      Rmult (Raux.bpow Zaux.radix2 (Z.of_N pow))
  end.

Definition Rop_of_unop (r: unop): R -> R :=
  match r with
    | Rounded1 op _ => Rop_of_rounded_unop op
    | Exact1 op => Rop_of_exact_unop op
  end.

Definition RR' (x: R) : Type := R.

Fixpoint apply_list (l: list R) (f: function_type (map RR' l) R) {struct l} : R.
 destruct l.
 apply f.
 simpl in f.
 apply (apply_list l). apply f. hnf. apply r.
Defined.

Definition environ {coll: collection} := 
  forall (ty : type) (IN: incollection ty), FPLang.V -> ftype ty.

Definition env_all_finite `{coll: collection} (env: environ) :=
  forall (ty : type) (IN: incollection ty) (i : FPLang.V),
        is_finite (env ty IN i) = true.

Fixpoint rval `{coll: collection} (env: environ) {ty: type} (e: expr ty): R :=
  match e with
    | Const _ _ f => B2R _ _ f
    | Var _ IN i => FT2R (env ty IN i)
    | Binop b e1 e2 =>  Rop_of_binop b (rval env e1) (rval env e2)
    | Unop b e => Rop_of_unop b (rval env e)
    | Cast _ _  _ _ _ e => rval env e
    | Func _ ff en => 
    let fix rval_klist {tys: list type} (l': klist expr tys) (f: function_type (map RR tys) R) {struct l'}: R :=
          match l' in (klist _ l)  return (function_type (map RR l) R -> R)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => rval_klist tl (f0 (rval env h))
          end f 
          in rval_klist en (ff_realfunc ff)
  end.

Definition rval_klist `{coll: collection} (env: environ) {ty: type}  :=
 fix rval_klist {tys: list type} (l': klist expr tys) (f: function_type (map RR tys) R) {struct l'}: R :=
          match l' in (klist _ l)  return (function_type (map RR l) R -> R)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => rval_klist tl (f0 (rval env h))
          end f.

Section WITHNAN.
Context {NANS: Nans}.


Definition unop_valid ty (u: unop): bool :=
  match u with
    | Exact1 (Shift p _) => 
      Z.leb 0 (center_Z (3 - femax ty) (Z.of_N p + 1) (femax ty))
    | Rounded1 (InvShift p _) _ =>
      Z.leb 0 (center_Z (3 - (femax ty)) (- Z.pos p + 1) (femax ty))
    | _ => true
  end.

Fixpoint expr_valid `{coll: collection} {ty} (e: expr ty): Prop :=
  match e with
    | Const _ _ f => Binary.is_finite _ _ f = true
    | Var _ _ _ => True
    | Binop _ e1 e2 => expr_valid e1 /\ expr_valid e2
    | Unop u e => unop_valid ty u = true /\ expr_valid e
    | Cast _ _  _ _ _ e => expr_valid e
    | Func _ ff en => 
       let fix expr_klist_valid {tys: list type} (es: klist expr tys) : Prop :=
        match es with
        | Knil => True 
        | Kcons h tl => expr_valid h /\ expr_klist_valid tl 
       end
       in expr_klist_valid en
  end.

Definition expr_klist_valid `{coll: collection} : 
       forall {tys: list type} (es: klist expr tys), Prop :=
  fix expr_klist_valid {tys: list type} (es: klist expr tys) : Prop :=
     match es with
        | Knil => True 
        | Kcons h tl => expr_valid h /\ expr_klist_valid tl 
       end.

Definition fop_of_rounded_binop (r: rounded_binop): 
  forall ty (STD: is_standard ty),
    ftype ty -> ftype ty -> ftype ty
  :=
    match r with
      | PLUS => @BPLUS _
      | MINUS => @BMINUS _
      | MULT => @BMULT _
      | DIV => @BDIV _
    end.

Definition fop_of_binop (r: binop):
  forall ty (STD: is_standard ty),
    ftype ty -> ftype ty -> ftype ty
  :=
    match r with
      | Rounded2 r _ => fop_of_rounded_binop r
      | SterbenzMinus => @BMINUS _
      | PlusZero minus zero_left => if minus then @BMINUS _ else @BPLUS _
    end.

Definition fop_of_rounded_unop (r: rounded_unop): 
  forall ty (STD: is_standard ty),
    ftype ty -> ftype ty
  :=
    match r with
      | SQRT => @BSQRT _
      | InvShift n b => 
        if b
        then (fun ty STD x => @BMULT _ ty _ x (ftype_of_float (B2 ty (- Z.pos n))))
        else (fun ty STD => @BMULT _ ty _ (ftype_of_float (B2 ty (- Z.pos n))))
    end.

Definition fop_of_exact_unop (r: exact_unop)
  := 
    match r with
      | Abs => @BABS _
      | Opp => @BOPP _
      | Shift n b =>
        if b
        then
          (fun ty STD x => @BMULT _ ty _ x (ftype_of_float (B2 ty (Z.of_N n))))
        else
          (fun ty STD => @BMULT _ ty _ (ftype_of_float (B2 ty (Z.of_N n))))
    end.

Definition fop_of_unop (r: unop) :=
 match r with
 | Rounded1 u o => fop_of_rounded_unop u
 | Exact1 u => fop_of_exact_unop u
 end.

Fixpoint fval `{coll: collection} (env: environ) {ty} (e: expr ty) {struct e}: ftype ty :=
      match e with
      | Const _ STD f => ftype_of_float f
      | Var _ IN i => env ty IN i
      | Binop b e1 e2 => fop_of_binop b _ _ (fval env e1) (fval env e2)
      | Unop u e1 => fop_of_unop u _ _ (fval env e1)
      | Cast _ tfrom STDto STDfrom o e1 => @cast _ ty tfrom STDto STDfrom (fval env e1)
      | Func _ ff en =>
       let fix fval_klist {l1: list type} (l': klist expr l1) (f: function_type (map ftype' l1) (ftype' ty)) {struct l'}: ftype' ty :=
          match  l' in (klist _ l) return (function_type (map ftype' l) (ftype' ty) -> ftype' ty)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => fval_klist tl (f0 (fval env h))
          end f 
          in fval_klist en (ff_func (ff_ff ff))
      end.

Definition fval_klist `{coll: collection} (env: environ) {T: Type} :=
  fix fval_klist {l1: list type} (l': klist expr l1) (f: function_type (map ftype' l1) T) {struct l'}: T :=
          match  l' in (klist _ l) return (function_type (map ftype' l) T -> T)
          with
          | Knil => fun f0 => f0
          | Kcons h tl => fun f0 => fval_klist tl (f0 (fval env h))
          end f.

Lemma is_nan_cast:
  forall  t1 t2 STD1 STD2 x1,
   Binary.is_nan _ _ (float_of_ftype x1) = false ->
   Binary.is_nan _ _ (float_of_ftype (@cast _ t2 t1 STD2 STD1 x1)) = false.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _ _ _).
subst t2.
simpl.
rewrite <- H.
f_equal.
apply float_of_ftype_irr.
destruct t2 as [? ? ? ? ? [|]]; try contradiction.
destruct t1 as [? ? ? ? ? [|]]; try contradiction.
simpl.
unfold Bconv.
destruct x1; try discriminate; auto.
apply is_nan_BSN2B'.
Qed.

Lemma cast_is_nan :
  forall t1 t2 STD1 STD2 x1,
  Binary.is_nan _ _ (float_of_ftype x1) = true ->
  Binary.is_nan _ _ (float_of_ftype (@cast _ t1 t2 STD2 STD1 x1)) = true.
Proof.
intros.
unfold cast.
destruct (type_eq_dec _ _ _ _ ).
-
subst t2. simpl.
rewrite <- H.
f_equal.
apply float_of_ftype_irr.
-
destruct t2 as [? ? ? ? ? [|]]; try contradiction.
destruct t1 as [? ? ? ? ? [|]]; try contradiction.
simpl.
unfold Bconv.
destruct x1; try discriminate; auto.
Qed.

Lemma InvShift_accuracy: 
 forall (pow : positive) (ltr : bool) (ty : type) (STD: is_standard ty) x 
  (F1 : is_finite x = true),
 Rabs (FT2R (fop_of_rounded_unop (InvShift pow ltr) ty STD x) -
      F2R radix2 (B2F (B2 ty (Z.neg pow))) * FT2R x) <=
   /2 * bpow radix2 (3 - femax ty - fprec ty).
Proof.
intros.
unfold fop_of_unop.
assert (Binary.is_finite (fprec ty) (femax ty) (B2 ty (Z.neg pow)) = true). {
  apply B2_finite.
  pose proof (fprec_lt_femax ty).
  pose proof (fprec_gt_0 ty).
  red in H0.
  lia.
}
rewrite is_finite_Binary in F1.
simpl fop_of_rounded_unop.
rewrite <- (ftype_of_float_of_ftype STD STD x).
set (x' := float_of_ftype x) in *.
clearbody x'. clear x. rename x' into x.
destruct ltr.
-
   destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty)).
  + rewrite (B2_zero ty (Z.neg pow)) in * by auto.
     simpl B2R. clear H l.
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
    pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)).
    set (j := bpow radix2 _) in *. clearbody j.
    destruct x; try discriminate; simpl;
     rewrite ?Rmult_0_l, Rminus_0_r, Rabs_R0; lra.     
  +
    assert (H2 := Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _ _ (fprec_gt_one _)) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
    rewrite F2R_B2F by auto.
    rewrite (B2_correct ty (Z.neg pow) ltac:(lia)) in *.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; clear H4]. 
  * apply Rlt_bool_true.
   apply  InvShift_finite_aux; auto.
  * destruct H2 as [H2 _].
    rewrite H2. clear H2.
    apply InvShift_accuracy_aux; auto.
- 
   destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty)).
  + rewrite (B2_zero ty (Z.neg pow)) in * by auto.
     simpl B2R. clear H l.
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
    pose proof (bpow_gt_0 radix2 (3 - femax ty - fprec ty)).
    set (j := bpow radix2 _) in *. clearbody j.
    destruct x; try discriminate; simpl; rewrite ?Rmult_0_l, Rminus_0_r, Rabs_R0; lra.     
  +
    assert (H2 := Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _ _ (fprec_gt_one _)) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) x).
    rewrite Rmult_comm in H2. 
    unfold BMULT, BINOP.
     rewrite !float_of_ftype_of_float.
    rewrite !FT2R_ftype_of_float.
    rewrite F2R_B2F by auto.
    rewrite (B2_correct ty (Z.neg pow) ltac:(lia)) in *.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; clear H4]. 
  * apply Rlt_bool_true.
   apply  InvShift_finite_aux; auto.
  * destruct H2 as [H2 _].
    rewrite H2. clear H2.
    apply InvShift_accuracy_aux; auto.
Qed.

Lemma InvShift_finite: 
 forall (pow : positive) (ltr : bool) (ty : type) (STD: is_standard ty) (x : ftype ty) 
  (F1 : is_finite x = true),
 is_finite (fop_of_rounded_unop (InvShift pow ltr) ty STD x) = true.
Proof.
intros.
simpl.
rewrite is_finite_Binary in F1.
pose proof (fprec_lt_femax ty).
pose proof (fprec_gt_0 ty).
red in H0.
pose proof (B2_finite ty (Z.neg pow) ltac:(lia)).
unfold BMULT, BINOP.
destruct ltr; destruct  (Z_lt_le_dec ((Z.neg pow) + 1) (3 - femax ty));
  unfold Datatypes.id;
  rewrite is_finite_Binary, !float_of_ftype_of_float.
- rewrite (B2_zero _ _ l); unfold Bmult. destruct (float_of_ftype x); auto.
- 
    pose proof (Bmult_correct_comm _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _ _ (fprec_gt_one _)) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) (float_of_ftype x)).
    rewrite Rmult_comm in H2. 
    pose proof (B2_correct ty (Z.neg pow) ltac:(lia)).
   rewrite H3 in H2.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite F1, H1, Raux.bpow_opp in H2. simpl andb in H2.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; apply H2].
     apply Rlt_bool_true.
   apply  InvShift_finite_aux; auto.
- rewrite (B2_zero _ _ l); unfold Bmult. destruct (float_of_ftype x); auto.
- 
    pose proof (Bmult_correct _ _ (fprec_gt_0 _) (fprec_lt_femax _) (mult_nan _ _ (fprec_gt_one _)) BinarySingleNaN.mode_NE (B2 ty (Z.neg pow)) (float_of_ftype x)).
    rewrite Rmult_comm in H2. 
    pose proof (B2_correct ty (Z.neg pow) ltac:(lia)).
   rewrite H3 in H2.
    replace (Z.neg pow) with (- Z.pos pow)%Z in * |- * by reflexivity.   
    rewrite F1, H1, Raux.bpow_opp in H2. simpl andb in H2.
    match type of H2 with if ?A then _ else _ => assert (H4: A=true) end;
    [ clear H2 | rewrite H4 in H2; apply H2].
     apply Rlt_bool_true.
   apply  InvShift_finite_aux; auto.
Qed.

End WITHNAN.
