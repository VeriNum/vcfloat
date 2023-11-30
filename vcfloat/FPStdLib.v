Require Import ZArith Lia Reals Coq.Lists.List.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra klist.
Global Unset Asymmetric Patterns. (* because "Require compcert..." sets it *)
Require Export vcfloat.Float_notations.
Require vcfloat.FPCore.

From vcfloat Require Export RAux.
Set Bullet Behavior "Strict Subproofs".
Require Import Coq.Relations.Relations Coq.Classes.Morphisms Coq.Classes.RelationPairs Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.

Local Definition ZLT a b: Prop := Bool.Is_true (Z.ltb a b).

Local Lemma ZLT_intro a b:
  (a < b)%Z ->
  ZLT a b.
Proof.
  intros.
  apply Bool.Is_true_eq_left.
  apply Z.ltb_lt.
  assumption.
Qed.

Local Lemma ZLT_elim a b:
  ZLT a b ->
  (a < b)%Z.
Proof.
  intros.
  apply Z.ltb_lt. 
  apply Bool.Is_true_eq_true.
  assumption.
Qed.

Record type: Type := TYPE
  {
    fprecp: positive;
    femax: Z;
    fprec := Z.pos fprecp;
    fprec_lt_femax_bool: ZLT fprec femax;
    fprecp_not_one_bool: Bool.Is_true (negb (Pos.eqb fprecp xH))
  }.

Lemma Is_true_eq a (h1 h2: Bool.Is_true a):
  h1 = h2.
Proof.
  destruct a; try contradiction.
  unfold Bool.Is_true in h1, h2.
  destruct h1. destruct h2. reflexivity.
Defined. 

Lemma type_ext t1 t2:
  fprecp t1 = fprecp t2 -> femax t1 = femax t2 -> t1 = t2.
Proof.
  destruct t1. destruct t2. simpl. intros. subst.
  f_equal; apply Is_true_eq.
Defined. (* required for the semantics of cast *)

Lemma type_ext' t1 t2:
  fprec t1 = fprec t2 -> femax t1 = femax t2 -> t1 = t2.
Proof.
  intros.
  apply type_ext; auto.
  apply Zpos_eq_iff.
  assumption.
Qed.

Lemma type_eq_iff t1 t2:
  ((fprecp t1 = fprecp t2 /\ femax t1 = femax t2) <-> t1 = t2).
Proof.
  split.
  {
    destruct 1; auto using type_ext.
  }
  intuition congruence.
Qed.

Import Bool.

Definition type_eqb t1 t2 :=
  Pos.eqb (fprecp t1) (fprecp t2) && Z.eqb (femax t1) (femax t2).

Lemma type_eqb_eq t1 t2:
  (type_eqb t1 t2 = true <-> t1 = t2).
Proof.
  unfold type_eqb.
  rewrite andb_true_iff.
  rewrite Pos.eqb_eq.
  rewrite Z.eqb_eq.
  apply type_eq_iff.
Qed.

Lemma type_eq_dec (t1 t2: type): 
  {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1. destruct t2.
  destruct (Pos.eq_dec fprecp0 fprecp1); [ |   right; intro K; injection K; congruence ].
  subst.
  destruct (Z.eq_dec femax0 femax1); [ |   right; intro K; injection K; congruence ].
  subst.
  left.
  apply type_ext; auto. 
Defined.

Lemma fprec_lt_femax' ty: (fprec ty < femax ty)%Z.
Proof.
  apply ZLT_elim.
  apply fprec_lt_femax_bool.
Qed.

(* For transparency purposes *)
Lemma fprec_lt_femax ty: (fprec ty < femax ty)%Z.
Proof.
  unfold Z.lt.
  destruct (Z.compare (fprec ty) (femax ty)) eqn:EQ; auto;
  generalize (fprec_lt_femax' ty);
    intro K;
    unfold Z.lt in K;
    congruence.
Defined.

Lemma fprecp_not_one ty:
    fprecp ty <> 1%positive
.
Proof.
  apply Pos.eqb_neq.
  apply negb_true_iff.
  apply Bool.Is_true_eq_true.
  apply fprecp_not_one_bool.
Qed.

Lemma fprec_eq ty: fprec ty = Z.pos (fprecp ty).
Proof. reflexivity. Qed.

Global Instance fprec_gt_0: forall ty, Prec_gt_0 (fprec ty).
Proof.
  intros.
  reflexivity.
Defined.

Definition ftype ty := binary_float (fprec ty) (femax ty).

(* The term "fprecp_not_one t" has type "fprecp t <> 1%positive" while it is expected to have type
 "Is_true (negb (fprecp t =? 1)%positive)".
*)


Definition coretype_of_type (t: type) : FPCore.type :=
 FPCore.TYPE (fprecp t) (femax t) (FPCore.ZLT_intro _ _ (fprec_lt_femax t)) (fprecp_not_one_bool t).

#[export] Instance STDtype: forall (t: type), FPCore.is_standard (coretype_of_type t).
Proof.
intros. apply I.
Qed.


Definition Nans := FPCore.Nans.

Definition conv_nan {NAN: FPCore.Nans} : forall ty1 ty2 : type, 
                binary_float (fprec ty1) (femax ty1) ->
                FPCore.nan_payload (fprec ty2) (femax ty2) 
  := fun t1 t2 => FPCore.conv_nan (coretype_of_type t1) (coretype_of_type t2).

Definition plus_nan {NAN: FPCore.Nans}:
      forall ty: type,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        FPCore.nan_payload (fprec ty) (femax ty) 
 := fun t => FPCore.plus_nan (coretype_of_type t).

Definition  mult_nan {NAN: FPCore.Nans}:
      forall ty : type,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        FPCore.nan_payload (fprec ty) (femax ty)
 := fun t => FPCore.plus_nan (coretype_of_type t).


Definition    div_nan {NAN: FPCore.Nans}:
      forall ty : type,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        FPCore.nan_payload (fprec ty) (femax ty)
 := fun t => FPCore.div_nan (coretype_of_type t).

Definition    abs_nan {NAN: FPCore.Nans}:
      forall ty : type,
        binary_float (fprec ty) (femax ty) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
        FPCore.nan_payload (fprec ty) (femax ty)
 := fun t => FPCore.abs_nan (coretype_of_type t).

Definition    opp_nan {NAN: FPCore.Nans}:
      forall ty : type,
        binary_float (fprec ty) (femax ty) -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
        FPCore.nan_payload (fprec ty) (femax ty)
 := fun t => FPCore.opp_nan (coretype_of_type t).

Definition    sqrt_nan {NAN: FPCore.Nans}:
      forall ty : type,
        binary_float (fprec ty) (femax ty) ->
        FPCore.nan_payload (fprec ty) (femax ty)
 := fun t => FPCore.sqrt_nan (coretype_of_type t).

Definition    fma_nan {NAN: FPCore.Nans}:
      forall ty : type,
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        binary_float (fprec ty) (femax ty) ->
        FPCore.nan_payload (fprec ty) (femax ty)
 := fun t => FPCore.fma_nan (coretype_of_type t).


Definition FT2R {t: type} : ftype t -> R := B2R (fprec t) (femax t).

Definition BFMA {NAN: FPCore.Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.

(* see https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/RelationPairs.20rewriting.20really.20slow *)
Global Instance proper_pair1: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> Basics.flip Basics.impl) RA
    -> Proper (RB1 ==> RB2 ==> Basics.flip Basics.impl) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> Basics.flip Basics.impl) (RA * RB)%signature.
Proof. cbv; intuition eauto. Qed.

Global Instance proper_pair2: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> Basics.impl) RA
    -> Proper (RB1 ==> RB2 ==> Basics.impl) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> Basics.impl) (RA * RB)%signature.
Proof. cbv; intuition eauto. Qed.

Definition feq {t: type} : relation (ftype t) :=
 fun x y =>
  match x, y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_zero _ _ _, _ => False
    | _, Binary.B754_zero _ _ _ => False
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | Binary.B754_finite _ _ _ _ _ _, _ => False
    | _, Binary.B754_finite _ _ _ _ _ _ => False
    | _, _ => True
  end.

Lemma feq_refl {t}: reflexive (ftype t) feq.
Proof.
intro x; destruct x; simpl; auto.
Qed.

Lemma feq_refl' {t}: forall x: ftype t, feq x x. 
exact feq_refl.
Qed.

#[export] Hint Resolve feq_refl': core.

Lemma feq_sym {t}: symmetric (ftype t) feq.
Proof.
intros x y; destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma feq_trans {t: type}: transitive (ftype t) feq.
Proof.
intros x y z.
destruct x,y,z; simpl; intros; auto; try contradiction.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@feq t)
  reflexivity proved by feq_refl
  symmetry proved by feq_sym
  transitivity proved by feq_trans
   as feq_rel.

Lemma list_eqv_refl: forall {T} {rel: relation T} {EQrel: Equivalence rel},
   reflexive (list T) (Forall2 rel).
Proof.
intros.
red.
induction x; constructor; auto. reflexivity.
Qed.

Lemma list_eqv_sym: forall {T} {rel: relation T} {EQrel: Equivalence rel},
   symmetric (list T) (Forall2 rel).
Proof.
intros.
red.
induction x; destruct y; intros; inversion H; clear H; subst;  constructor; auto.
symmetry; auto.
Qed.

Lemma list_eqv_trans: forall {T} {rel: relation T} {EQrel: Equivalence rel},
   transitive (list T) (Forall2 rel).
Proof.
intros.
red.
induction x; destruct y,z; intros; inversion H; inversion H0; clear H H0; subst;  constructor; auto.
rewrite H4; auto.
eapply IHx; eauto.
Qed.

Add Parametric Relation {T: Type} (rel: relation T) {EQrel: Equivalence rel}: (list T) (Forall2 rel)
  reflexivity proved by list_eqv_refl
  symmetry proved by list_eqv_sym
  transitivity proved by list_eqv_trans
   as list_eqv_rel.

Lemma test_pair: forall t (a a': ftype t) (b b': list (ftype t)),
  feq a a' -> Forall2 feq b b' ->
  (feq * Forall2 feq)%signature (a,b) (a',b').
Proof.
intros.
rewrite H. 
rewrite H0. 
reflexivity.
Abort.  (* no need to save this *)

Add Parametric Morphism {T: Type} (rel: relation T): (@Some T)
  with signature rel ==> FPCore.option_rel rel
  as Some_mor.
Proof.
intros. constructor; auto.
Qed.

Add Parametric Morphism {t: Type} (rel: t -> t -> Prop) : (@cons t)
  with signature rel ==> Forall2 rel ==> Forall2 rel
  as cons_mor.
Proof.
intros.
constructor; auto.
Qed.

Definition strict_feq {t: type} : relation (ftype t) :=
 fun x y =>
  match x, y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | _, _ => False
  end.

Require vcfloat.FPLib.

Ltac proof_irr := FPLib.proof_irr.

Local Ltac inv H := inversion H; clear H; subst. 

#[export] Instance subrelation_strict_feq {t: type}: subrelation (@strict_feq t) (@feq t).
Proof.
red; intros.
destruct x,y; inv H; simpl; auto.
Qed.

Definition finite {t} (x: ftype t) := strict_feq x x.

Lemma strict_feq_refl {t: type}: forall (x: ftype t),
 Binary.is_finite _ _ x = true -> strict_feq x x.
Proof.
intros.
destruct x; try discriminate; hnf; auto.
Qed.

Lemma strict_feq_sym {t: type}: symmetric (ftype t) strict_feq.
Proof.
intros x y.
destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma strict_feq_trans {t: type}:  transitive (ftype t) strict_feq.
Proof.
intros x y z.
destruct x,y,z; simpl; intros; auto; try contradiction.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@strict_feq t)
  symmetry proved by strict_feq_sym
  transitivity proved by strict_feq_trans
   as strict_feq_rel.

#[export] Hint Extern 100 (Proper ?R ?x) => 
 (* See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/rewriting.20with.20PERs *)
    (lazymatch R with respectful _ _ => fail | _ => red; auto with nocore typeclass_instances end)    : typeclass_instances.

Add Parametric Morphism {NAN: FPCore.Nans}{t: type} : BFMA
 with signature (@feq t) ==> feq ==> feq ==> feq
  as BFMA_mor.
Proof.
intros.    
destruct x,y; inv H; try apply I;
destruct x0,y0; inv  H0; try apply I;
destruct x1,y1; inv H1; try apply I;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst; simpl; auto;
repeat proof_irr;
try reflexivity;
repeat match goal with s: bool |- _ => destruct s end;
try reflexivity;
unfold BFMA, Binary.Bfma, BinarySingleNaN.Bfma, Binary.BSN2B, Binary.B2BSN;
simpl;
set (K := _ (proj1 _)); clearbody K; destruct K; simpl; auto.
Qed.

Lemma Forall_map: forall  {A B} (P: B -> Prop) (f: A -> B) (al: list A),
  Forall (Basics.compose P f) al ->
  Forall P (map f al).
Proof.
induction 1; constructor; auto.
Qed.

Lemma Forall_seq: forall (P: nat -> Prop) (lo n: nat),
  (forall i, lo <= i < lo+n -> P i)%nat ->
  Forall P (seq lo n).
Proof.
intros.
revert lo H; induction n; simpl; intros; constructor.
apply H. lia.
apply IHn; intros.
apply H; lia.
Qed.

Definition adapt_op_nan
  (op_nan: forall ty : FPCore.type,
       FPCore.is_standard ty ->
       binary_float (FPCore.fprec ty) (FPCore.femax ty) ->
       binary_float (FPCore.fprec ty) (FPCore.femax ty) ->
       FPCore.nan_payload (FPCore.fprec ty) (FPCore.femax ty)) :
    forall ty: type, 
    binary_float (fprec ty) (femax ty) -> 
    binary_float (fprec ty) (femax ty) -> 
    FPCore.nan_payload (fprec ty) (femax ty) :=
 fun t x y =>
  op_nan (coretype_of_type t) I x y.

Definition adapt_unop_nan
  (op_nan: forall ty : FPCore.type,
       FPCore.is_standard ty ->
       binary_float (FPCore.fprec ty) (FPCore.femax ty) ->
       FPCore.nan_payload (FPCore.fprec ty) (FPCore.femax ty)) :
    forall ty: type, 
    binary_float (fprec ty) (femax ty) -> 
    FPCore.nan_payload (fprec ty) (femax ty) :=
 fun t x =>
  op_nan (coretype_of_type t) I x.

  
Definition BINOP (op: ltac:( let t := type of Bplus in exact t ) ) 
   (op_nan: forall ty : FPCore.type,
       FPCore.is_standard ty ->
       binary_float (FPCore.fprec ty) (FPCore.femax ty) ->
       binary_float (FPCore.fprec ty) (FPCore.femax ty) ->
       FPCore.nan_payload (FPCore.fprec ty) (FPCore.femax ty))
    ty 
    : ftype ty -> ftype ty -> ftype ty 
    := op _ _ (fprec_gt_0 ty) (fprec_lt_femax ty) (adapt_op_nan op_nan ty)
      BinarySingleNaN.mode_NE.

Section WITHNANS.
Context {NANS: FPCore.Nans}.

Definition BPLUS := BINOP Bplus FPCore.plus_nan.
Definition BMINUS := BINOP Bminus FPCore.plus_nan. (* NOTE: must be same as the one used for plus *)

Definition BMULT := BINOP Bmult FPCore.mult_nan.
Definition BDIV := BINOP Bdiv FPCore.div_nan.
Definition BABS {ty} := Babs _ (femax ty) (adapt_unop_nan FPCore.abs_nan ty).
Definition BOPP {ty} := Bopp _ (femax ty) (adapt_unop_nan FPCore.opp_nan ty).

Definition UNOP (op: ltac:( let t := type of Bsqrt in exact t ) ) op_nan ty 
    : ftype ty -> ftype ty
    := op _ _ (fprec_gt_0 ty) (fprec_lt_femax ty) (adapt_unop_nan op_nan ty) BinarySingleNaN.mode_NE.

Definition BSQRT :=  UNOP Bsqrt FPCore.sqrt_nan.
Arguments BSQRT {ty}.

End WITHNANS.

Definition cast {NANS: FPCore.Nans} (tto: type) {tfrom: type} (f: ftype tfrom): ftype tto :=
  match type_eq_dec tfrom tto with
    | left r => eq_rect _ _ f _ r
    | _ => Bconv (fprec tfrom) (femax tfrom) (fprec tto) (femax tto)
                        (fprec_gt_0 _) (fprec_lt_femax _) (conv_nan _ _) BinarySingleNaN.mode_NE f
  end.

Arguments BPLUS {NANS ty}.
Arguments BMINUS {NANS ty}.
Arguments BMULT {NANS ty}.
Arguments BDIV {NANS ty}.

Definition BCMP {ty: type} (c: comparison) (b: bool) (x y: ftype ty) :=
  FPCore.extend_comp c b (Binary.Bcompare (fprec ty) (femax ty) x y).

Definition type_of_coretype (t: FPCore.type) `{STD: FPCore.is_standard t} : type :=
 TYPE (FPCore.fprecp t) (FPCore.femax t) (FPCore.fprec_lt_femax_bool t) (FPCore.fprecp_not_one_bool t).

Definition Tsingle := @type_of_coretype FPCore.Tsingle I.
Definition Tdouble := @type_of_coretype FPCore.Tdouble I.


Notation "x + y" := (@BPLUS _ Tsingle x y) (at level 50, left associativity) : float32_scope.
Notation "x - y"  := (@BMINUS _ Tsingle x y) (at level 50, left associativity) : float32_scope.
Notation "x * y"  := (@BMULT _ Tsingle x y) (at level 40, left associativity) : float32_scope.
Notation "x / y"  := (@BDIV _ Tsingle x y) (at level 40, left associativity) : float32_scope.
Notation "- x" := (@BOPP _ Tsingle x) (at level 35, right associativity) : float32_scope.
Notation "x <= y" := (@BCMP Tsingle Gt false x y) (at level 70, no associativity) : float32_scope. 
Notation "x < y" := (@BCMP Tsingle Gt true y x) (at level 70, no associativity) : float32_scope. 
Notation "x >= y" := (@BCMP Tsingle Lt false x y) (at level 70, no associativity) : float32_scope. 
Notation "x > y" := (@BCMP Tsingle Gt true x y) (at level 70, no associativity) : float32_scope. 
Notation "x <= y <= z" := (x <= y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y < z" := (x < y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.

Notation "x + y" := (@BPLUS _ Tdouble x y) (at level 50, left associativity) : float64_scope.
Notation "x - y"  := (@BMINUS _ Tdouble x y) (at level 50, left associativity) : float64_scope.
Notation "x * y"  := (@BMULT _ Tdouble x y) (at level 40, left associativity) : float64_scope.
Notation "x / y"  := (@BDIV _ Tdouble x y) (at level 40, left associativity) : float64_scope.
Notation "- x" := (@BOPP _ Tdouble x) (at level 35, right associativity) : float64_scope.
Notation "x <= y" := (@BCMP Tdouble Gt false x y) (at level 70, no associativity) : float64_scope. 
Notation "x < y" := (@BCMP Tdouble Gt true y x) (at level 70, no associativity) : float64_scope. 
Notation "x >= y" := (@BCMP Tdouble Lt false x y) (at level 70, no associativity) : float64_scope. 
Notation "x > y" := (@BCMP Tdouble Gt true x y) (at level 70, no associativity) : float64_scope. 
Notation "x <= y <= z" := (x <= y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y < z" := (x < y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.

Definition Zconst (t: type) (i: Z) : ftype t :=
    BofZ (fprec t) (femax t) (Pos2Z.is_pos (fprecp t)) (fprec_lt_femax t) i.

Lemma BPLUS_BOPP_diag: 
  forall {NAN: FPCore.Nans} {t} (x: ftype t), finite x -> BPLUS x (BOPP x) = Zconst t 0.
Proof.
intros.
destruct x,s; inv H; try reflexivity;
unfold BPLUS, BOPP, BINOP, Binary.Bplus, Binary.Bopp, Binary.BSN2B,
   BinarySingleNaN.binary_normalize, BinarySingleNaN.binary_normalize,
   BinarySingleNaN.binary_normalize; simpl;
 unfold BinarySingleNaN.binary_normalize, BinarySingleNaN.Fplus_naive,
  SpecFloat.cond_Zopp;
replace (_ + _)%Z with 0%Z by lia; reflexivity.
Qed.

Lemma Forall_Forall2diag {A: Type}:
   forall (P: A -> A -> Prop) al,
    Forall (fun x => P x x) al <-> Forall2 P al al.
Proof.
split; try solve [induction 1; auto].
intro.
induction al; auto.
inv H.
constructor; auto.
Qed.

Lemma BFMA_zero1: forall {NAN: FPCore.Nans} {t} y s, 
  strict_feq y y ->
  feq (BFMA (Zconst t 0) y s) s.
Proof.
intros.
intros.
change (Zconst t 0) with 
  (Binary.B754_zero (fprec t)  (femax t) false).
unfold BFMA, BPLUS, BINOP in *.
destruct y, s; try discriminate; simpl; auto.
Qed.

Lemma BFMA_zero2: forall  {NAN: FPCore.Nans}{t} x s, 
  strict_feq x x ->
  feq (BFMA x (Zconst t 0) s) s.
Proof.
intros.
intros.
change (Zconst t 0) with 
  (Binary.B754_zero (fprec t)  (femax t) false).
unfold BFMA, BPLUS, BINOP in *.
destruct x, s; try discriminate; simpl; auto.
Qed.

Lemma BPLUS_0_l: forall  {NAN: FPCore.Nans} {t} x, finite x -> 
      feq (BPLUS (Zconst t 0) x) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma BPLUS_0_r: forall {NAN: FPCore.Nans} {t} x, finite x -> 
      feq (BPLUS x (Zconst t 0)) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma finite_0: forall t,  finite (Zconst t 0).
Proof.
intros; apply I.
Qed.

Lemma BMULT_congr:
 forall  {NAN: FPCore.Nans}{t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMULT x y) (BMULT x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor.
destruct H2,H1; subst. repeat proof_irr.
apply feq_refl.
Qed.

Lemma BMINUS_congr:
 forall  {NAN: FPCore.Nans}{t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMINUS x y) (BMINUS x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor;
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto;
 destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto.
Qed.

Lemma Forall2_rev:  forall {t} (rel: relation t) (x x': list t),
    Forall2 rel x x' -> Forall2 rel (rev x) (rev x').
Proof.
induction 1.
constructor.
simpl.
apply Forall2_app; auto.
Qed.

Lemma Forall2_rel_refl: forall {A: Type} (rel: relation A), 
   (forall x, rel x x) -> forall al, Forall2 rel al al.
Proof.
unfold reflexive; intros.
induction al; constructor; auto.
Qed.
#[export] Hint Resolve Forall2_rel_refl  : core.

Lemma Forall2_subrelation: forall {A: Type} (f g: A -> A -> Prop) (al bl: list A),
  subrelation f g -> Forall2 f al bl  -> Forall2 g al bl.
Proof.
induction 2; constructor; auto.
Qed.
#[export] Hint Resolve Forall2_subrelation: core.

Lemma BFMA_xx_mor:
 forall  {NAN: FPCore.Nans}{t} (x x' s s': ftype t), 
  feq x x' -> 
  feq s s' ->
  feq (BFMA x x s) (BFMA x' x' s').
Proof.
intros.
red.
unfold BFMA.
destruct x,x'; inv H; simpl; auto;
 destruct s,s'; inv H0; simpl; auto;
repeat proof_irr; 
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto;
try solve [destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto].
all:
unfold Binary.Bfma, Binary.BSN2B, BinarySingleNaN.Bfma, Binary.B2BSN; simpl;
set (K := _ (proj1 _)); clearbody K; destruct K; simpl; auto.
Qed.

Lemma strict_feq_i1:
  forall  {t} (x y: ftype t), 
    finite x -> feq x y ->
    strict_feq x y.
Proof.
 intros.
 red in H.
 destruct x; inv H;
 destruct y; inv H0. constructor. constructor; auto.
Qed.

Lemma FMA_one: forall {NAN: FPCore.Nans}{t} (x y: ftype t),
  feq (BFMA x y (Zconst t 0)) (BMULT x y).
Proof.
unfold BFMA, BMULT, BINOP.
intros.
(*unfold Binary.Bmult, Binary.Bfma, Binary.BSN2B, Binary.B2BSN, BinarySingleNaN.Bfma,
  BinarySingleNaN.Bfma_szero .
*)
destruct x,y; try destruct s; try destruct s0; try apply I.
-
Abort.  (* Not at all easy to prove, though probably true *)

Add Parametric Morphism {t: type} : (Binary.is_finite (fprec t) (femax t))
  with signature feq ==> eq
  as is_finite_mor.
Proof.
intros.
destruct x, y; inv H; reflexivity.
Qed.

Lemma strict_floatlist_eqv_i1: 
   forall {t} (a b: list (ftype t)),
    Forall finite a -> Forall2 feq a b -> Forall2 strict_feq a b.
Proof.
induction 2; inv H;constructor.
apply strict_feq_i1; auto.
apply IHForall2; auto.
Qed.

Lemma finite_is_finite: forall {t} (x: ftype t),
   finite x <-> Binary.is_finite _ _ x = true.
Proof.
split; intros;
destruct x; inv H; try reflexivity.
constructor; auto.
Qed.

Lemma feq_strict_feq:
 forall {t} (x y: ftype t),
   finite x -> feq x y -> strict_feq x y.
Proof.
 intros.
 destruct x; inv H; destruct y; inv H0; constructor; auto.
Qed.

Lemma strict_feq_finite1:
  forall {t} (x y: ftype t),
    strict_feq x y -> finite x.
Proof.
intros.
destruct x,y; inv H; constructor; auto.
Qed.

Lemma BFMA_finite_e {NAN: FPCore.Nans} {t: type}:
 forall x y z : ftype t,
 finite (BFMA x y z) ->
 finite x /\ finite y /\ finite z.
Proof.
intros.
destruct x,y, z; try contradiction H;
 try solve [split; [ | split]; simpl; auto; constructor; auto].
all: try solve [destruct s,s0,s1; contradiction].
Qed.

Add Parametric Morphism {T: Type} (rel: relation T): (@length T)
  with signature Forall2 rel ==> eq
  as length_mor.
Proof.
induction 1; auto.
simpl; f_equal; auto.
Qed.

Add Parametric Morphism {t: type}: (@finite t)
  with signature feq ==> iff
  as finite_rel.
Proof.
destruct x,y; split; intros; inv H0; inv H; constructor; auto.
Qed.

Add Parametric Morphism {A} (rel1: A->Prop)(rel2: relation A)
          (proper1: Proper (rel2 ==> iff) rel1)  : (Forall rel1)
 with signature  Forall2 rel2 ==> iff
 as Forall_Forall2_mor.
Proof.
intros.
induction H. split; auto.
split; intro H1; inversion H1; clear H1; subst; constructor.
rewrite <- H; auto. apply IHForall2; auto. rewrite H; auto.
apply IHForall2; auto.
Qed.

Add Parametric Morphism {NAN: FPCore.Nans}{t}: (@BPLUS NAN t)
 with signature feq ==> feq ==> feq
 as BPLUS_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto.
Qed.

Add Parametric Morphism {NAN: FPCore.Nans}{t}: (@BMINUS NAN t)
 with signature feq ==> feq ==> feq
 as BMINUS_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto.
Qed.

Add Parametric Morphism {NAN: FPCore.Nans}{t}: (@BMULT NAN t)
 with signature feq ==> feq ==> feq
 as BMULT_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto.
Qed.

Add Parametric Morphism {NAN: FPCore.Nans}{t}: (@BDIV NAN t)
 with signature feq ==> strict_feq ==> feq
 as BDIV_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor;
reflexivity.
Qed.

Add Parametric Morphism {t}: (@BCMP t) 
 with signature eq ==> eq ==> strict_feq ==> strict_feq ==> eq
 as BCMP_mor.
Proof.
intros.
destruct x,y1; inv H; destruct x0,y2; inv H0; simpl.
destruct y,s,s0,s1,s2;simpl; auto.
destruct H1; subst.
proof_irr.
destruct y0,s,s0,s2; simpl; auto.
destruct H2; subst.
proof_irr.
destruct y0,s,s0,s1; simpl; auto.
destruct H1,H2; subst.
repeat proof_irr.
destruct y0,s0,s1; simpl; auto.
Qed.

Definition relate_type t t' := coretype_of_type t = t'.

Definition relate_standard: forall [t t'], relate_type t t' -> FPCore.is_standard t'.
Proof.
intros.
red in H.
subst.
apply STDtype.
Qed.

Inductive type_coretype: forall [t: type], ftype t -> FPCore.ftype (coretype_of_type t) -> Prop :=
| TC_Zconst: forall t z,
      type_coretype (@Zconst t z) (@FPCore.Zconst (coretype_of_type t) (STDtype t) z)
| TC_BINOP: forall op NAN t 
        x x' (TCx: type_coretype x x') y y' (TCy: type_coretype y y'),
        type_coretype (@BINOP op NAN t x y) (@FPCore.BINOP op NAN (coretype_of_type t) (STDtype t) x' y')
| TC_UNOP: forall op NAN t x x',
        type_coretype x x' ->
        type_coretype (@UNOP op NAN t x) (@FPCore.UNOP op NAN (coretype_of_type t) (STDtype t) x')
| TC_cast: forall NAN t1 t2  x x',
      type_coretype  x x' ->
      type_coretype (@cast NAN t1 t2 x) 
       (@FPCore.cast NAN (coretype_of_type t1) (coretype_of_type t2) (STDtype t1) (STDtype t2) x').

Require Import JMeq.
Require vcfloat.Rounding.
Set Bullet Behavior "Strict Subproofs".

Lemma eq_JMeq: forall t (x y: t), x=y -> JMeq x y.
Proof.
intros.
subst.
apply JMeq_refl.
Qed.

Axiom extensionality: forall s t (f g: s -> t), (forall x, f x = g x) -> f = g.


Lemma type_coretype_sound: forall t (e: ftype t) (e': FPCore.ftype (coretype_of_type t)),
  type_coretype e e' ->
  JMeq e (@FPCore.float_of_ftype _ (STDtype t) e').
Proof.
intros.
induction H; simpl.
-
apply eq_JMeq.
unfold Zconst, FPCore.Zconst.
f_equal; auto; try apply FPLib.proof_irr.
-
apply eq_JMeq.
unfold BINOP, FPCore.BINOP.
(*
rewrite FPCore.float_of_ftype_of_float. *)
f_equal; auto; try apply FPLib.proof_irr.
unfold adapt_op_nan.
do 2 (apply extensionality; intro).
f_equal; apply FPLib.proof_irr.
apply JMeq_eq; auto.
apply JMeq_eq; auto.
-
apply eq_JMeq.
unfold UNOP, FPCore.UNOP.
f_equal; auto; try apply FPLib.proof_irr.
unfold adapt_unop_nan.
apply extensionality; intro.
f_equal; apply FPLib.proof_irr.
apply JMeq_eq; auto.
-
unfold cast, FPCore.cast.
destruct (type_eq_dec t2 t1).
+

destruct (FPCore.type_eq_dec _ _ _ _); try congruence.
subst t2.
apply eq_JMeq.
apply JMeq_eq in IHtype_coretype.
subst x.
unfold eq_rect.
unfold f_equal.
pose proof ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.UIP_refl _ _ e0.
subst e0.
auto.
+
apply eq_JMeq.
apply JMeq_eq in IHtype_coretype.
subst x.
destruct (FPCore.type_eq_dec _ _ _ _).
  * exfalso.
    apply n.
    clear - e.
    unfold coretype_of_type, FPCore.TYPE in *.
    inv e.
    destruct t1, t2; simpl in *; subst; repeat f_equal; apply FPLib.proof_irr.
  *
  destruct t1, t2.
  unfold coretype_of_type in *.
  simpl in *. clear H.
  f_equal. apply FPLib.proof_irr.
Qed. 

Module Test.

Definition foo {Nans: FPCore.Nans} (x: ftype Tsingle) :=
   BPLUS (cast Tdouble x) (Zconst Tdouble 8).

Definition foo' {Nans: FPCore.Nans} (x: FPCore.ftype FPCore.Tsingle) :=
   @FPCore.BPLUS Nans _ FPCore.is_standard_Tdouble 
      (@FPCore.cast Nans _ _ FPCore.is_standard_Tdouble FPCore.is_standard_Tsingle x)
      (@FPCore.Zconst FPCore.Tdouble FPCore.is_standard_Tdouble 8).

Lemma coretype_of_type_of_coretype: forall t (STD: FPCore.is_standard t),
    coretype_of_type (type_of_coretype t) = t.
Proof.
 intros.
 apply FPCore.type_ext; simpl; auto.
 apply STDtype.
Qed.


Definition corify {NAN: FPCore.Nans} (x: ftype Tsingle) (x': FPCore.ftype FPCore.Tsingle):
   type_coretype x x' ->
   {e' : FPCore.ftype FPCore.Tdouble | JMeq (foo x) e'}.
Proof.
intros.
eexists.
apply type_coretype_sound.
repeat econstructor; eauto.
Defined.
(*
Print corify.
*)

End Test.

