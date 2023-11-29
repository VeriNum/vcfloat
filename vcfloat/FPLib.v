From vcfloat Require Export FPCore RAux (*Rounding*) Float_notations.

Set Bullet Behavior "Strict Subproofs".
Require Import Coq.Relations.Relations Coq.Classes.Morphisms Coq.Classes.RelationPairs Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Definition BFMA {NAN: Nans} {t: type} {STD: is_standard t} (x y z: ftype t) : ftype t :=
  ftype_of_float
    (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE
     (float_of_ftype x) (float_of_ftype y) (float_of_ftype z)).

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
 fun x y => match is_finite x, is_finite y with
            | true, true => compare' x y = Some Eq
            | false, false => True
            | _, _ => False
            end.

Definition feq' {t: type} {STD: is_standard t} : relation (ftype t) :=
 fun x y =>
  match float_of_ftype x, float_of_ftype y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_zero _ _ _, _ => False
    | _, Binary.B754_zero _ _ _ => False
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | Binary.B754_finite _ _ _ _ _ _, _ => False
    | _, Binary.B754_finite _ _ _ _ _ _ => False
    | _, _ => True
  end.

Lemma feq'_iff {t: type} {STD: is_standard t}:
  forall x y, feq' x y <-> feq x y.
Proof.
intros.
unfold feq', feq.
destruct t; try contradiction.
rewrite !is_finite_Binary.
unfold float_of_ftype.
destruct nonstd; try contradiction.
hnf in x,y.
destruct x as [[|]| | |[|]], y as [[|]| | |[|]] ;
simpl in *;
unfold Binary.Bcompare; simpl; split; 
 try intros [? [? ?]]; intros; subst;
  auto; try contradiction; try congruence; try discriminate.
-
rewrite BinarySingleNaN.Bcompare_correct by auto.
simpl.
rewrite Raux.Rcompare_Eq by auto; auto.
-
split; auto.
clear - H.
unfold BinarySingleNaN.Bcompare in H.
simpl in H.
destruct (Z.compare_spec e e1); try discriminate.
pose proof (Pcompare_Eq_eq m m0).
destruct (Pos.compare_cont Eq m m0); try discriminate.
rewrite H0,H1 by auto; auto.
-
unfold BinarySingleNaN.Bcompare.
simpl.
rewrite Z.compare_refl.
rewrite Pos.compare_cont_refl.
auto.
-
split; auto.
clear - H.
unfold BinarySingleNaN.Bcompare in H.
simpl in H.
destruct (Z.compare_spec e e1); try discriminate.
pose proof (Pcompare_Eq_eq m m0).
destruct (Pos.compare_cont Eq m m0); try discriminate.
rewrite H0,H1 by auto; auto.
Qed.

Lemma feq_refl {t}: reflexive (ftype t) feq.
Proof.
intro x.
red.
destruct (is_finite x) eqn:?H; auto.
rewrite compare'_correct by auto.
f_equal.
apply Raux.Rcompare_Eq; auto.
Qed.

Lemma feq_refl' {t}: forall x: ftype t, feq x x. 
exact feq_refl.
Qed.

#[export] Hint Resolve feq_refl': core.

Lemma feq_sym {t}: symmetric (ftype t) feq.
Proof.
unfold feq.
intros x y.
destruct (is_finite x) eqn:?H;
destruct (is_finite y) eqn:?H;
auto.
intros.
rewrite compare'_correct in H1|-* by auto.
inversion H1; clear H1.
f_equal.
rewrite Raux.Rcompare_sym, H3.
reflexivity.
Qed.

Lemma feq_trans {t: type}: transitive (ftype t) feq.
Proof.
unfold feq.
intros x y z ? ?.
destruct (is_finite x) eqn:?H;
destruct (is_finite y) eqn:?H;
destruct (is_finite z) eqn:?H;
auto; try contradiction.
rewrite compare'_correct in H,H0|-* by auto.
inversion H; clear H; inversion H0; clear H0.
f_equal.
apply Raux.Rcompare_Eq_inv in H5, H4.
rewrite H5, H4. auto.
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
  with signature rel ==> option_rel rel
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
 fun x y => match is_finite x, is_finite y with
            | true, true => compare' x y = Some Eq
            | _, _ => False
            end.


Definition strict_feq' {t: type} {STD: is_standard t} : relation (ftype t) :=
 fun x y =>
  match float_of_ftype x, float_of_ftype y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | _, _ => False
  end.



Lemma strict_feq'_iff {t: type} {STD: is_standard t}:
  forall x y, strict_feq' x y <-> strict_feq x y.
Proof.
intros.
unfold strict_feq', strict_feq.
destruct t; try contradiction.
rewrite !is_finite_Binary.
unfold float_of_ftype.
destruct nonstd; try contradiction.
hnf in x,y.
destruct x as [[|]| | |[|]], y as [[|]| | |[|]] ;
simpl in *;
unfold Binary.Bcompare; simpl; split; 
 try intros [? [? ?]]; intros; subst;
  auto; try contradiction; try congruence; try discriminate.
-
rewrite BinarySingleNaN.Bcompare_correct by auto.
simpl.
rewrite Raux.Rcompare_Eq by auto; auto.
-
split; auto.
clear - H.
unfold BinarySingleNaN.Bcompare in H.
simpl in H.
destruct (Z.compare_spec e e1); try discriminate.
pose proof (Pcompare_Eq_eq m m0).
destruct (Pos.compare_cont Eq m m0); try discriminate.
rewrite H0,H1 by auto; auto.
-
unfold BinarySingleNaN.Bcompare.
simpl.
rewrite Z.compare_refl.
rewrite Pos.compare_cont_refl.
auto.
-
split; auto.
clear - H.
unfold BinarySingleNaN.Bcompare in H.
simpl in H.
destruct (Z.compare_spec e e1); try discriminate.
pose proof (Pcompare_Eq_eq m m0).
destruct (Pos.compare_cont Eq m m0); try discriminate.
rewrite H0,H1 by auto; auto.
Qed.

Local Ltac inv H := inversion H; clear H; subst. 

Axiom prop_ext: ClassicalFacts.prop_extensionality.

Lemma proof_irr      : ClassicalFacts.proof_irrelevance.
Proof. apply ClassicalFacts.ext_prop_dep_proof_irrel_cic. 
 apply prop_ext.
Qed.
Arguments proof_irr [A] a1 a2.

Ltac proof_irr :=
  match goal with
  | H:?A, H':?A
    |- _ => generalize (proof_irr H H'); intro; subst H'
  end.

#[export] Instance subrelation_strict_feq {t: type}: subrelation (@strict_feq t) (@feq t).
Proof.
unfold strict_feq, feq.
red; intros.
destruct (is_finite x), (is_finite y); try contradiction; auto.
Qed.

Definition finite {t} (x: ftype t) := strict_feq x x.

Lemma strict_feq_refl {t: type}: forall (x: ftype t),
 is_finite x = true -> strict_feq x x.
Proof.
intros.
unfold strict_feq.
rewrite H.
rewrite compare'_correct by auto.
f_equal.
apply Raux.Rcompare_Eq; auto.
Qed.

Lemma strict_feq_sym {t: type}: symmetric (ftype t) strict_feq.
Proof.
unfold strict_feq.
intros x y ?.
destruct (is_finite x) eqn:?H;
destruct (is_finite y) eqn:?H;
try contradiction.
rewrite compare'_correct in H|-* by auto.
inversion H; clear H.
f_equal.
apply Raux.Rcompare_Eq_inv in H3.
rewrite H3; reflexivity.
Qed.

Lemma strict_feq_trans {t: type}:  transitive (ftype t) strict_feq.
Proof.
unfold strict_feq.
intros x y z ? ?.
destruct (is_finite x) eqn:?H;
destruct (is_finite y) eqn:?H;
destruct (is_finite z) eqn:?H;
try contradiction.
rewrite compare'_correct in H,H0|-* by auto.
inversion H; clear H.
inversion H0; clear H0.
apply Raux.Rcompare_Eq_inv in H4,H5.
f_equal.
rewrite H4,H5. auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@strict_feq t)
  symmetry proved by strict_feq_sym
  transitivity proved by strict_feq_trans
   as strict_feq_rel.

#[export] Hint Extern 100 (Proper ?R ?x) => 
 (* See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/rewriting.20with.20PERs *)
    (lazymatch R with respectful _ _ => fail | _ => red; auto with nocore typeclass_instances end)    : typeclass_instances.

Add Parametric Morphism {NAN: Nans}{t: type} {STD: is_standard t} : BFMA
 with signature (@feq t) ==> feq ==> feq ==> feq
  as BFMA_mor.
Proof.
intros.
rewrite <- feq'_iff in *|-*.
red.
unfold BFMA.
rewrite !float_of_ftype_of_float.
red in H,H0,H1.
set (X := float_of_ftype x) in *; clearbody X.
set (Y := float_of_ftype y) in *; clearbody Y.
set (X0 := float_of_ftype x0) in *; clearbody X0.
set (Y0 := float_of_ftype y0) in *; clearbody Y0.
set (X1 := float_of_ftype x1) in *; clearbody X1.
set (Y1 := float_of_ftype y1) in *; clearbody Y1.
clear x y x0 y0 x1 y1.
destruct X,Y; inv H; try apply I;
destruct X0,Y0; inv  H0; try apply I;
destruct X1,Y1; inv H1; try apply I;
repeat match goal with H: _ /\ _ |- _ => destruct H end.
all: try solve [
subst; simpl; auto;
repeat proof_irr;
try reflexivity;
repeat match goal with s: bool |- _ => destruct s end;
try reflexivity;
unfold BFMA, Binary.Bfma, BinarySingleNaN.Bfma, Binary.BSN2B, Binary.B2BSN;
simpl;
set (K := _ (proj1 _)); clearbody K; destruct K; simpl; auto].

all:
subst; simpl; auto;
repeat proof_irr;
try reflexivity.
all:
unfold Binary.Bfma, Binary.BSN2B, BinarySingleNaN.Bfma, Binary.B2BSN,
Operations.Fmult, Operations.Fplus, Operations.Falign;
destruct (_ + _ <=? _);
destruct (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _); try apply I; 
 solve [auto].
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

Lemma BPLUS_BOPP_diag: 
  forall {NAN: Nans} {t} {STD: is_standard t} 
     (x: ftype t), finite x -> BPLUS x (BOPP x) = Zconst t 0.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
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

Lemma BFMA_zero1: forall {NAN: Nans} {t} {STD: is_standard t} y s, 
  strict_feq y y ->
  feq (BFMA (Zconst t 0) y s) s.
Proof.
intros.
rewrite <- strict_feq'_iff in H.
intros.
rewrite <- feq'_iff.
destruct t as [? ? ? ? ? [|]]; try contradiction.
change (Zconst _ 0) with 
  (Binary.B754_zero (Z.pos fprecp) femax false).
red.
simpl.
destruct y, s; try discriminate; simpl; auto.
Qed.

Lemma BFMA_zero2: forall  {NAN: Nans}{t} {STD: is_standard t} x s, 
  strict_feq x x ->
  feq (BFMA x (Zconst t 0) s) s.
Proof.
intros.
rewrite <- strict_feq'_iff in H.
intros.
rewrite <- feq'_iff.
destruct t as [? ? ? ? ? [|]]; try contradiction.
change (Zconst _ 0) with 
  (Binary.B754_zero (Z.pos fprecp) femax false).
red.
simpl.
destruct x, s; try discriminate; simpl; auto.
Qed.

Lemma BPLUS_0_l: forall  {NAN: Nans} {t} {STD: is_standard t} x, finite x -> 
      feq (BPLUS (Zconst t 0) x) x.
Proof.
  intros.
  destruct t as [? ? ? ? ? [|]]; try contradiction.
  destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma BPLUS_0_r: forall {NAN: Nans} {t} {STD: is_standard t} x, finite x -> 
      feq (BPLUS x (Zconst t 0)) x.
Proof.
  intros. 
  destruct t as [? ? ? ? ? [|]]; try contradiction.
  destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma finite_0: forall t {STD: is_standard t} ,  finite (Zconst t 0).
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
reflexivity.
Qed.

Lemma BMULT_congr:
 forall  {NAN: Nans}{t} {STD: is_standard t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMULT x y) (BMULT x' y').
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H,H0.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor.
destruct H2,H1; subst. repeat proof_irr.
apply feq_refl.
Qed.

Lemma BMINUS_congr:
 forall  {NAN: Nans}{t} {STD: is_standard t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMINUS x y) (BMINUS x' y').
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H,H0.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor;
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto; try reflexivity.
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
 forall  {NAN: Nans}{t} {STD: is_standard t} (x x' s s': ftype t), 
  feq x x' -> 
  feq s s' ->
  feq (BFMA x x s) (BFMA x' x' s').
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H,H0|-*.
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
 red in H,H0|-*.
 destruct (is_finite x), (is_finite y); try contradiction; auto.
Qed.

Lemma FMA_one: forall {NAN: Nans}{t} {STD: is_standard t} (x y: ftype t),
  feq (BFMA x y (Zconst t 0)) (BMULT x y).
Proof.
unfold BFMA, BMULT, BINOP.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff.
(*unfold Binary.Bmult, Binary.Bfma, Binary.BSN2B, Binary.B2BSN, BinarySingleNaN.Bfma,
  BinarySingleNaN.Bfma_szero .
*)
destruct x,y; try destruct s; try destruct s0; hnf; try apply I.
-
Abort.  (* Not at all easy to prove, though probably true *)

Add Parametric Morphism {t: type} : (@is_finite t)
  with signature feq ==> eq
  as is_finite_mor.
Proof.
intros.
red in H.
destruct (is_finite x), (is_finite y); auto; try contradiction.
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
   finite x <-> is_finite x = true.
Proof.
unfold finite, strict_feq.
split; intros.
destruct (is_finite x); auto; contradiction.
rewrite H.
rewrite compare'_correct by auto.
f_equal.
apply Raux.Rcompare_Eq; auto.
Qed.

Lemma feq_strict_feq:
 forall {t} (x y: ftype t),
   finite x -> feq x y -> strict_feq x y.
Proof.
 intros.
 rewrite finite_is_finite in H.
 red in H0|-*. rewrite H in *. auto.
Qed.

Lemma strict_feq_finite1:
  forall {t} (x y: ftype t),
    strict_feq x y -> finite x.
Proof.
intros.
red in H|-*.
red.
destruct (is_finite x) eqn:?H; try contradiction.
rewrite compare'_correct by auto.
f_equal.
apply Raux.Rcompare_Eq; auto.
Qed.

Lemma BFMA_finite_e {NAN: Nans} {t: type} {STD: is_standard t}:
 forall x y z : ftype t,
 finite (BFMA x y z) ->
 finite x /\ finite y /\ finite z.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
unfold finite in *.
rewrite <- !strict_feq'_iff in *. 
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
intros.
red in H.
destruct (is_finite x) eqn:?H, (is_finite y) eqn:?H; try contradiction;
rewrite !finite_is_finite.
tauto.
intuition congruence.
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

Add Parametric Morphism {NAN: Nans}{t} {STD: is_standard t}: (@BPLUS NAN t STD)
 with signature feq ==> feq ==> feq
 as BPLUS_mor.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H,H0|-.
simpl in *.
compute in x,y,x0,y0.
hnf in H,H0|-. simpl in *|-.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *|-;
repeat match goal with H: _ /\ _ |- _ => destruct H end; 
auto;
subst;
repeat proof_irr; reflexivity.
Qed.

Add Parametric Morphism {NAN: Nans}{t} STD : (@BMINUS NAN t STD)
 with signature feq ==> feq ==> feq
 as BMINUS_mor.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H,H0|-.
simpl in *.
compute in x,y,x0,y0.
hnf in H,H0|-. simpl in *|-.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *|-;
repeat match goal with H: _ /\ _ |- _ => destruct H end; 
auto;
subst;
repeat proof_irr; reflexivity.
Qed.

Add Parametric Morphism {NAN: Nans}{t} STD: (@BMULT NAN t STD)
 with signature feq ==> feq ==> feq
 as BMULT_mor.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H,H0|-.
simpl in *.
compute in x,y,x0,y0.
hnf in H,H0|-. simpl in *|-.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *|-;
repeat match goal with H: _ /\ _ |- _ => destruct H end; 
auto;
subst;
repeat proof_irr; reflexivity.
Qed.

Add Parametric Morphism {NAN: Nans}{t} STD:  (@BDIV NAN t STD)
 with signature feq ==> strict_feq ==> feq
 as BDIV_mor.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- feq'_iff in H; rewrite <- strict_feq'_iff in H0.
simpl in *.
compute in x,y,x0,y0.
hnf in H,H0|-. simpl in *|-.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *|-;
repeat match goal with H: _ /\ _ |- _ => destruct H end; 
auto;
subst;
repeat proof_irr; reflexivity.
Qed.


Add Parametric Morphism {t} STD: (@BCMP t STD) 
 with signature eq ==> eq ==> strict_feq ==> strict_feq ==> eq
 as BCMP_mor.
Proof.
intros.
destruct t as [? ? ? ? ? [|]]; try contradiction.
rewrite <- strict_feq'_iff in H,H0.
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

