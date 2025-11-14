(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(** FPCore module.
  These definitions, which were previously part of FPLang.v, are
  separated out to support a modularity principle:  some clients
  may want the definitions of [type], [BPLUS] etc.  but not the
  deep-embedded syntax of [binop], [PLUS] etc.  Such clients
  can import FPCore without importing FPLang.
     Why might such clients exist?  We envision a multilayer
   correctness proof of a C program:  prove in VST that a C program
   implements a functional model (a Gallina function over Flocq
   floating point);  then prove that the functional model satisfies
   a high-level specification (approximates real-valued function F
   to some accuracy bound).   It is in that second proof that VCFloat
   might be used.   The first proof (VST refinement) should not need
   to import VCFloat.   But the functional model would still like to make
   use of some convenient definitions for Flocq functions on floating-point
   numbers; those definitions are defined here in FPCore.
   Thus, the refinement proof in VST will need to import FPCore but
    not the rest of VCFloat. *)

From Coq Require Import ZArith Lia Reals Lists.List.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra klist.
Global Unset Asymmetric Patterns. (* because "Require compcert..." sets it *)
Require Export vcfloat.Float_notations.

Require Export vcfloat.Base.

Record nonstdtype
   (fprecp: positive)
   (femax: Z)
   (fprec := Z.pos fprecp)
   (fprec_lt_femax_bool: ZLT fprec femax)
   (fprecp_not_one_bool: Bool.Is_true (negb (Pos.eqb fprecp xH))) := NONSTD
  { nonstd_rep: Type;
    nonstd_nonempty: nonstd_rep;
    nonstd_to_F: nonstd_rep -> option (float radix2);
    nonstd_compare: nonstd_rep -> nonstd_rep -> option comparison;
    nonstd_finite_compare: forall x: nonstd_rep,
           if nonstd_to_F x then nonstd_compare x x = Some Eq else True;
    nonstd_compare_correct: forall (f1 f2 : nonstd_rep) g1 g2,
      nonstd_to_F f1 = Some g1 ->
      nonstd_to_F f2 = Some g2 ->
      nonstd_compare f1 f2 = Some (Rcompare (Defs.F2R g1) (Defs.F2R g2));
    nonstd_nonempty_finite: if nonstd_to_F nonstd_nonempty then True else False;
    nonstd_bounds: forall x: nonstd_rep,
       ( - (bpow radix2 femax - bpow radix2 (femax - Z.pos fprecp)) <=
        match nonstd_to_F x with Some f => Defs.F2R f | None => R0 end <=
        bpow radix2 femax - bpow radix2 (femax - Z.pos fprecp) )%R

}.


Arguments nonstd_rep [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool] n.
Arguments nonstd_nonempty [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool] n.

Arguments nonstd_to_F [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool n] n.
Arguments nonstd_compare [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool n]
    _ _.
Arguments nonstd_finite_compare [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool n]
    x.
Arguments nonstd_compare_correct [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool n]
    f1 f2 g1 g2.
Arguments nonstd_nonempty_finite [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool] n.

Arguments nonstd_bounds [fprecp femax fprec_lt_femax_bool fprecp_not_one_bool n] x.

Definition nonstd_to_R {fprecp femax fprec_lt_femax_bool fprecp_not_one_bool}
      {n: nonstdtype fprecp femax fprec_lt_femax_bool fprecp_not_one_bool}
      (x: nonstd_rep n) : R :=
  match nonstd_to_F x with Some f => Defs.F2R f | None => R0 end.

Definition nonstd_is_finite {fprecp: positive} {femax: Z}
        {fprec_lt_femax_bool: ZLT (Z.pos fprecp) femax}
        {fprecp_not_one_bool: Bool.Is_true (negb (Pos.eqb fprecp xH))}
        {n: nonstdtype fprecp femax fprec_lt_femax_bool fprecp_not_one_bool}
        (x: nonstd_rep n) :=
 match nonstd_to_F x with Some _ => true | _ => false end.

Definition nonstd_is_nan {fprecp: positive} {femax: Z}
        {fprec_lt_femax_bool: ZLT (Z.pos fprecp) femax}
        {fprecp_not_one_bool: Bool.Is_true (negb (Pos.eqb fprecp xH))}
        {n: nonstdtype fprecp femax fprec_lt_femax_bool fprecp_not_one_bool}
        (x: nonstd_rep n) :=
  match nonstd_compare x x with Some Eq => false | _ => true end.

Lemma nonstd_compare_correct':
  forall {fprecp femax fprec_lt_femax_bool fprecp_not_one_bool}
   {n: nonstdtype fprecp femax fprec_lt_femax_bool fprecp_not_one_bool}
    (f1 f2: nonstd_rep n),
   match nonstd_to_F f1 with Some _ => true | _ => false end = true ->
   match nonstd_to_F f2 with Some _ => true | _ => false end = true ->
   nonstd_compare f1 f2 = Some (Rcompare (nonstd_to_R f1) (nonstd_to_R f2)).
Proof.
intros.
pose proof (nonstd_compare_correct f1 f2).
unfold nonstd_to_R.
destruct (nonstd_to_F f1) as [g1|] eqn:?H; [ | discriminate].
destruct (nonstd_to_F f2) as [g2|] eqn:?H; [ | discriminate].
eauto.
Qed.

Record type: Type := GTYPE
  {
    fprecp: positive;
    femax: Z;
    fprec := Z.pos fprecp;
    fprec_lt_femax_bool: ZLT fprec femax;
    fprecp_not_one_bool: Bool.Is_true (negb (Pos.eqb fprecp xH));
    nonstd: option (nonstdtype fprecp femax fprec_lt_femax_bool fprecp_not_one_bool)
  }.

Definition TYPE fprecp femax fprec_lt_femax fprecp_not_one :=
  GTYPE  fprecp femax fprec_lt_femax fprecp_not_one None.


Definition ftype (ty: type) : Type :=
 match nonstd ty with
 | None => binary_float (fprec ty) (femax ty)
 | Some t => nonstd_rep t
 end.

Class is_standard (t: type) :=
   Is_standard: match nonstd t with None => True | _ => False end.


Definition ftype_of_float {t: type} {STD: is_standard t}
    (x: binary_float (fprec t) (femax t)) : ftype t.
unfold ftype.
destruct t; simpl.
destruct nonstd0; simpl; auto.
contradiction.
Defined.

Definition float_of_ftype {t: type} {STD: is_standard t}
      (x: ftype t) : binary_float (fprec t) (femax t).
unfold ftype.
destruct t; simpl.
destruct nonstd0; simpl; auto.
contradiction.
Defined.

Lemma float_of_ftype_of_float {t: type} (STD1 STD2: is_standard t):
  forall x, @float_of_ftype t STD1 (@ftype_of_float t STD2 x) = x.
Proof.
intros.
destruct t.
destruct nonstd0; try contradiction.
reflexivity.
Qed.

Lemma ftype_of_float_of_ftype {t: type} (STD1 STD2: is_standard t):
  forall x, @ftype_of_float t STD1 (@float_of_ftype t STD2 x) = x.
Proof.
intros.
destruct t.
destruct nonstd0; try contradiction.
reflexivity.
Qed.

Lemma float_of_ftype_irr:
  forall t (STD1 STD2: is_standard t) (x: ftype t),
  @float_of_ftype t STD1 x = @float_of_ftype t STD2 x.
Proof.
intros.
unfold float_of_ftype.
destruct t as [? ? ? ? ? [|]].
contradiction STD1.
auto.
Qed.

Definition is_finite {t: type} (x: ftype t): bool.
destruct t as [precp emax prec prec_lt precp_not [n|]].
apply (match nonstd_to_F x with Some _ => true | _ => false end).
apply (Binary.is_finite prec emax x).
Defined.

Definition is_nan {t: type} (x: ftype t) : bool.
destruct t as [precp emax prec prec_lt precp_not [n|]].
apply (nonstd_is_nan x).
apply (Binary.is_nan prec emax x).
Defined.

Definition compare' {t: type} (x y: ftype t) : option comparison.
destruct t as [precp emax prec prec_lt precp_not [n|]].
apply (nonstd_compare x y).
apply (Binary.Bcompare prec emax x y).
Defined.

Definition compare {t: type} (c: comparison) (b: bool) (x y: ftype t) : bool :=
 extend_comp c b (compare' x y).

Lemma type_ext (t1 t2: type) :
  fprecp t1 = fprecp t2 -> femax t1 = femax t2 -> is_standard t1 -> is_standard t2 -> t1 = t2.
Proof.
  unfold is_standard.
  destruct t1. destruct t2. simpl. subst fprec0 fprec1. intros. subst.
  destruct nonstd0; try contradiction. destruct nonstd1; try contradiction.
  assert (fprec_lt_femax_bool0 = fprec_lt_femax_bool1) by apply Is_true_eq.
  assert (fprecp_not_one_bool0 = fprecp_not_one_bool1) by apply Is_true_eq.
  subst. reflexivity.
Defined. (* required for the semantics of cast *)

Lemma type_eq_iff (t1 t2: type):
   is_standard t1 -> is_standard t2 ->
  (((fprecp t1 = fprecp t2 /\ femax t1 = femax t2) <-> t1 = t2)).
Proof.
  unfold is_standard. intros.
  destruct t1 as [? ? ? ? ? [|]]; try contradiction.
  destruct t2 as [? ? ? ? ? [|]]; try contradiction.
  simpl in *.
  split.
  {
    destruct 1; auto using type_ext.
  }
  intro. inversion H1; clear H1; subst. auto.
Qed.

Import Bool.

Definition type_eqb t1 t2 :=
  Pos.eqb (fprecp t1) (fprecp t2) && Z.eqb (femax t1) (femax t2).

Lemma type_eqb_eq t1 t2:
   is_standard t1 -> is_standard t2 ->
  (type_eqb t1 t2 = true <-> t1 = t2).
Proof.
  intros.
  unfold type_eqb.
  rewrite andb_true_iff.
  rewrite Pos.eqb_eq.
  rewrite Z.eqb_eq.
  apply type_eq_iff; auto.
Qed.

Lemma type_eq_dec (t1 t2: type):
   is_standard t1 -> is_standard t2 ->
  {t1 = t2} + {t1 <> t2}.
Proof.
  unfold is_standard. intros.
  destruct t1 as [? ? ? ? ? [|]]; try contradiction.
  destruct t2 as [? ? ? ? ? [|]]; try contradiction.
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

Definition FT2R {t: type} : ftype t -> R :=
 match
   nonstd t as o0
   return
     (nonstd t = o0 ->
      match o0 with
      | Some t0 => nonstd_rep t0
      | None => binary_float (fprec t) (femax t)
      end -> R)
 with
 | Some a => fun _ : nonstd t = Some a => @nonstd_to_R _ _ _ _ a
 | None => fun _ : nonstd t = None => B2R (fprec t) (femax t)
 end eq_refl.

Class Nans: Type :=
  {
    conv_nan: forall prec1 emax1 prec2 emax2,
                (1<prec2)%Z ->
                binary_float prec1 emax1 -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
                nan_payload prec2 emax2
    ;
    plus_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax ->
        binary_float prec emax ->
        nan_payload prec emax
    ;
    mult_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax ->
        binary_float prec emax ->
        nan_payload prec emax
    ;
    div_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax ->
        binary_float prec emax ->
        nan_payload prec emax
    ;
    abs_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
        nan_payload prec emax
    ;
    opp_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
        nan_payload prec emax
    ;
    sqrt_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax ->
        nan_payload prec emax
    ;
    fma_nan:
      forall prec emax,
        (1<prec)%Z ->
        binary_float prec emax ->
        binary_float prec emax ->
        binary_float prec emax ->
        nan_payload prec emax
  }.

Definition float_equiv {ty} (b1 b2: ftype ty) : Prop.
unfold ftype, nonstd;
destruct ty as [? ? ? ? ? [|]]; simpl in *.
exact
match (nonstd_is_nan b1), (nonstd_is_nan b2) with
 | false, false => b1=b2
 | true, true => True
 | _, _ => False
end.
exact (binary_float_equiv b1 b2).
Defined.

Definition float_equiv_alt {ty} (b1 b2: ftype ty) : Prop :=
 match is_nan b1, is_nan b2 with
 | false, false => b1=b2
 | true, true => True
 | _, _ => False
 end.


Lemma float_equiv_alt_eq: forall {ty} (b1 b2: ftype ty),
  float_equiv_alt b1 b2 <-> float_equiv b1 b2.
Proof.
intros.
unfold float_equiv_alt, float_equiv, binary_float_equiv.
destruct ty as [? ? ? ? ? [|]]; simpl.
-

tauto.
-
destruct b1, b2; split; simpl; intro; try contradiction; try congruence.
inversion H; auto.
destruct H as [? [? ?]]; subst; auto.
f_equal. apply Classical_Prop.proof_irrelevance.
Qed.


Lemma float_equiv_refl: forall ty (b: ftype ty), float_equiv b b.
Proof.
intros. destruct ty as [? ? ? ? ? [|]]; simpl in *.
destruct (@nonstd_is_nan fprecp0 femax0 fprec_lt_femax_bool0 fprecp_not_one_bool0 n b); auto.
apply binary_float_equiv_refl.
Qed.

Lemma float_equiv_sym: forall ty (b1 b2: ftype ty),
   float_equiv b1 b2 -> float_equiv b2 b1.
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; simpl in *.
destruct (@nonstd_is_nan fprecp0 femax0 fprec_lt_femax_bool0 fprecp_not_one_bool0 n b2),
    (@nonstd_is_nan fprecp0 femax0 fprec_lt_femax_bool0 fprecp_not_one_bool0 n b1); auto.
apply binary_float_equiv_sym; auto.
Qed.

Lemma float_equiv_trans: forall ty (b1 b2 b3: ftype ty),
   float_equiv b1 b2 -> float_equiv b2 b3 -> float_equiv b1 b3.
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; simpl in *.
destruct (@nonstd_is_nan fprecp0 femax0 fprec_lt_femax_bool0 fprecp_not_one_bool0 n b2),
(@nonstd_is_nan fprecp0 femax0 fprec_lt_femax_bool0 fprecp_not_one_bool0 n b1),
(@nonstd_is_nan fprecp0 femax0 fprec_lt_femax_bool0 fprecp_not_one_bool0 n b3);
subst; auto; contradiction.
eapply binary_float_equiv_trans; eassumption.
Qed.

Lemma float_equiv_binary_float_equiv:
 forall ty (STD: is_standard ty) (b1 b2: ftype ty),
  float_equiv b1 b2 <-> binary_float_equiv (float_of_ftype b1) (float_of_ftype b2).
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; simpl in *.
contradiction.
reflexivity.
Qed.

Definition type_le t1 t2 : Prop := (fprec t1 <= fprec t2)%Z /\ (femax t1 <= femax t2)%Z.

Definition type_leb t1 t2 : bool :=
  Z.leb (fprec t1) (fprec t2) && Z.leb (femax t1) (femax t2)
.

Lemma type_leb_le t1 t2:
  type_leb t1 t2 = true <-> type_le t1 t2.
Proof.
  unfold type_le, type_leb.
  rewrite andb_true_iff.
  repeat rewrite Z.leb_le.
  tauto.
Qed.

Lemma type_le_refl t: type_le t t.
Proof.
  unfold type_le; auto with zarith.
Qed.

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


Corollary any_nan prec emax: (1<prec)%Z -> nan_payload prec emax.
Proof.
 intro.
 red.
  assert (H0: Binary.nan_pl prec 1 = true).
   unfold nan_pl. simpl. lia.
  exists (Binary.B754_nan prec emax false 1 H0).
  reflexivity.
Defined.

(*

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
*)

Section WITHNANS.
Context {NANS: Nans}.

Definition cast (tto: type) {tfrom: type}
  {STDto: is_standard tto} {STDfrom: is_standard tfrom} (f: ftype tfrom):
   ftype tto.

refine

  match type_eq_dec tfrom tto STDfrom STDto with
    | left r => eq_rect _ _ f _ (f_equal _ r)
    | right _ => _ (*Bconv (fprec tfrom) (femax tfrom) (fprec tto) (femax tto)
                        (fprec_gt_0 _) (fprec_lt_femax _) (conv_nan _ _) BinarySingleNaN.mode_NE f *)
  end.
unfold ftype in *.
destruct (nonstd tto) eqn:?H.
destruct tto. destruct nonstd0; try contradiction. inversion H.
destruct (nonstd tfrom) eqn:?H.
destruct tfrom. destruct nonstd0; try contradiction. discriminate.
apply (Bconv (fprec tfrom) (femax tfrom) (fprec tto) (femax tto)
                        (fprec_gt_0 _) (fprec_lt_femax _) (conv_nan _ _ _ _ (fprec_gt_one _)) BinarySingleNaN.mode_NE f)
.
Defined.


Lemma cast_finite tfrom tto (STDfrom: is_standard tfrom) (STDto: is_standard tto):
  type_le tfrom tto ->
  forall f,
  Binary.is_finite _ _ f = true ->
  Binary.is_finite _ _ (float_of_ftype (@cast tto tfrom STDto STDfrom (ftype_of_float f))) = true.
Proof.
  unfold cast.
  intros.
  destruct (type_eq_dec tfrom tto STDfrom STDto).
  {
    subst. simpl. rewrite float_of_ftype_of_float.
    assumption.
  }
  destruct H.
  destruct tfrom as [? ? ? ? ? [|]]; try contradiction.
  destruct tto as [? ? ? ? ? [|]]; try contradiction.
  simpl in *.
  apply Bconv_widen_exact; auto with zarith.
  typeclasses eauto.
Qed.

Lemma cast_eq tfrom tto STDfrom STDto:
  type_le tfrom tto ->
  forall f,
    Binary.is_finite _ _ f = true ->
    B2R _ _ (float_of_ftype (@cast tto tfrom STDto STDfrom (ftype_of_float f))) =
           B2R _ _ f.
Proof.
  unfold cast.
  intros.
  destruct (type_eq_dec tfrom tto _ _).
  {
    subst.
    unfold eq_rect, f_equal.
    rewrite float_of_ftype_of_float.
    reflexivity.
  }
  destruct H.
  destruct tfrom as [? ? ? ? ? [|]]; try contradiction.
  destruct tto as [? ? ? ? ? [|]]; try contradiction.
  simpl in *.
  apply Bconv_widen_exact; auto with zarith.
  typeclasses eauto.
Qed.

Lemma cast_id ty STD1 STD2 f:
    @cast ty ty STD1 STD2 f = f.
Proof.
  unfold cast.
  destruct (type_eq_dec ty ty); try congruence.
  change ty with ((fun x => x) ty).
  change f with ((fun (a:type) (x:ftype a) => x) ty f).
  apply f_equal_dep2.
  symmetry; apply Eqdep.EqdepTheory.eq_rect_eq.
Qed.


Definition BINOP (op: ltac:( let t := type of Bplus in exact t ) )
      (op_nan: forall prec emax,
       (1<prec) ->
       binary_float prec emax ->
       binary_float prec emax ->
       nan_payload prec emax)
    ty `{STD: is_standard ty}
    (x y: ftype ty) : ftype ty :=
   ftype_of_float (op _ _ (fprec_gt_0 ty) (fprec_lt_femax ty)
                     (op_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE
            (float_of_ftype x) (float_of_ftype y)).

Definition BPLUS := BINOP Bplus plus_nan.
Definition BMINUS := BINOP Bminus plus_nan. (* NOTE: must be same as the one used for plus *)

Definition BMULT := BINOP Bmult mult_nan.
Definition BDIV := BINOP Bdiv div_nan.

Definition UNOP (op: ltac:( let t := type of Bsqrt in exact t ) )
   (op_nan: forall prec emax,
       (1<prec) ->
       binary_float prec emax ->
       nan_payload prec emax)
    ty `{STD: is_standard ty}
      (x: ftype ty) : ftype ty :=
      ftype_of_float (op _ _ (fprec_gt_0 ty) (fprec_lt_femax ty)
                     (op_nan (fprec ty) (femax ty) (fprec_gt_one ty)) BinarySingleNaN.mode_NE
            (float_of_ftype x)).

Definition BABS {ty} {STD: is_standard ty} (x: ftype ty) :=
   ftype_of_float (Babs _ (femax ty) (abs_nan (fprec ty) (femax ty) (fprec_gt_one _)) (float_of_ftype x)).
Definition BOPP {ty} {STD: is_standard ty} (x: ftype ty) :=
   ftype_of_float (Bopp _ (femax ty) (opp_nan (fprec ty) (femax ty) (fprec_gt_one _)) (float_of_ftype x)).

Definition BSQRT :=  UNOP Bsqrt sqrt_nan.
Arguments BSQRT {ty}.

End WITHNANS.

Arguments BPLUS {NANS ty STD}.
Arguments BMINUS {NANS ty STD}.
Arguments BMULT {NANS ty STD}.
Arguments BDIV {NANS ty STD}.

Definition Norm {T} (x: T) := x.
Definition Denorm {T} (x: T) := x.
Definition Sterbenz {T} (x: T) := x.

Definition Tsingle := TYPE 24 128 I I.
Definition Tdouble := TYPE 53 1024 I I.


#[export] Instance is_standard_Tsingle: is_standard Tsingle := I. (* move these to FPCore *)
#[export] Instance is_standard_Tdouble: is_standard Tdouble := I.

Lemma single_le_double:
  type_le Tsingle Tdouble.
Proof.
  constructor; compute; congruence.
Qed.

Definition BCMP {ty: type} `{STD: is_standard ty} (c: comparison) (b: bool) (x y: ftype ty) :=
  extend_comp c b (Binary.Bcompare (fprec ty) (femax ty) (float_of_ftype x) (float_of_ftype y)).

Notation "x + y" := (@BPLUS _ Tsingle _ x y) (at level 50, left associativity) : float32_scope.
Notation "x - y"  := (@BMINUS _ Tsingle _ x y) (at level 50, left associativity) : float32_scope.
Notation "x * y"  := (@BMULT _ Tsingle _ x y) (at level 40, left associativity) : float32_scope.
Notation "x / y"  := (@BDIV _ Tsingle _ x y) (at level 40, left associativity) : float32_scope.
Notation "- x" := (@BOPP _ Tsingle _ x) (at level 35, right associativity) : float32_scope.
Notation "x <= y" := (@BCMP Tsingle _ Gt false x y) (at level 70, no associativity) : float32_scope.
Notation "x < y" := (@BCMP Tsingle _ Gt true y x) (at level 70, no associativity) : float32_scope.
Notation "x >= y" := (@BCMP Tsingle _ Lt false x y) (at level 70, no associativity) : float32_scope.
Notation "x > y" := (@BCMP Tsingle _ Gt true x y) (at level 70, no associativity) : float32_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y < z" := (x < y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.

Notation "x + y" := (@BPLUS _ Tdouble _ x y) (at level 50, left associativity) : float64_scope.
Notation "x - y"  := (@BMINUS _ Tdouble _ x y) (at level 50, left associativity) : float64_scope.
Notation "x * y"  := (@BMULT _ Tdouble _ x y) (at level 40, left associativity) : float64_scope.
Notation "x / y"  := (@BDIV _ Tdouble _ x y) (at level 40, left associativity) : float64_scope.
Notation "- x" := (@BOPP _ Tdouble _ x) (at level 35, right associativity) : float64_scope.
Notation "x <= y" := (@BCMP Tdouble _ Gt false x y) (at level 70, no associativity) : float64_scope.
Notation "x < y" := (@BCMP Tdouble _ Gt true y x) (at level 70, no associativity) : float64_scope.
Notation "x >= y" := (@BCMP Tdouble _ Lt false x y) (at level 70, no associativity) : float64_scope.
Notation "x > y" := (@BCMP Tdouble _ Gt true x y) (at level 70, no associativity) : float64_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y < z" := (x < y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.


Ltac compute_binary_floats :=
repeat (match goal with
| |- context [@BDIV ?NANS ?t ?STD ?x1 ?x2] =>
           const_float x1; const_float x2;
           change (@BDIV NANS t STD x1 x2)
            with (Bdiv (fprec t) (femax t) (fprec_gt_0 t)
              (fprec_lt_femax t) (div_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x1 x2)
| |- context [@BMULT ?NANS ?t ?STD ?x1 ?x2] =>
           const_float x1; const_float x2;
           change (@BMULT NANS t STD x1 x2)
             with (Bmult (fprec t) (femax t) (fprec_gt_0 t)
                (fprec_lt_femax t) (mult_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x1 x2)
| |- context [@BPLUS ?NANS ?t ?STD ?x1 ?x2] =>
           const_float x1; const_float x2;
           change (@BPLUS NANS t STD x1 x2)
           with (Bplus (fprec t) (femax t) (fprec_gt_0 t)
                 (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x1 x2)
| |- context [@BMINUS ?NANS ?t ?STD ?x1 ?x2] =>
           const_float x1; const_float x2;
           change (@BMINUS NANS t STD x1 x2)
           with (Bminus (fprec t) (femax t) (fprec_gt_0 t)
                 (fprec_lt_femax t) (plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x1 x2)
| |- context [Bdiv ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bdiv prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
| |- context [Bmult ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bmult prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
| |- context [Bplus ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bplus prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
| |- context [Bminus ?prec ?emax ?a ?b ?c ?d ?x1 ?x2] =>
   const_float x1; const_float x2;
   tryif (const_Z prec; const_Z emax)
   then (compute_float_operation constr:(Bminus prec emax a b c d x1 x2))
    else (progress (let f := eval compute in prec in change prec with f;
                           let f := eval compute in emax in change emax with f))
end; simpl FF2B);
 fold Float_notations.b32_B754_zero;
 fold Float_notations.b32_B754_finite;
 fold Float_notations.b32_B754_infinity;
 fold Float_notations.b64_B754_zero;
 fold Float_notations.b64_B754_finite;
 fold Float_notations.b64_B754_infinity.

Import Float_notations.

#[export] Instance is_standard_None: forall ty: type,
  match nonstd ty with None => True | _ => False end -> is_standard ty.
Proof.
destruct ty as [? ? ? ? ? [ | ]]; simpl; auto.
Qed.


#[export] Hint Extern 1 (is_standard _) => (apply is_standard_None; apply I) : typeclass_instances.


Local Lemma test_compute_binary_floats {NANS: Nans}:
  (@BPLUS _ Tsingle _ 1.5 3.5 = @BDIV _ Tsingle _ 10.0 2)%F32.
Proof.
 compute_binary_floats.
 auto. Qed.

Definition Zconst (t: type) `{STD: is_standard t} (i: Z) : ftype t :=
    ftype_of_float
  (BofZ (fprec t) (femax t) (Pos2Z.is_pos (fprecp t)) (fprec_lt_femax t) i).

Lemma BPLUS_commut {NANS: Nans}: forall (t: type) `{STD: is_standard t}
     (a b: ftype t),
    plus_nan (fprec t) (femax t) (fprec_gt_one t) (float_of_ftype a) (float_of_ftype b) =
    plus_nan (fprec t) (femax t) (fprec_gt_one t) (float_of_ftype b) (float_of_ftype a) ->
    BPLUS a b = BPLUS b a.
Proof.
intros.
unfold BPLUS, BINOP.
f_equal.
apply Bplus_commut; auto.
Qed.

Lemma BMULT_commut {NANS: Nans}: forall t `{STD: is_standard t} a b,
    mult_nan (fprec t) (femax t) (fprec_gt_one t) (float_of_ftype a) (float_of_ftype b) =
    mult_nan (fprec t) (femax t) (fprec_gt_one t) (float_of_ftype b) (float_of_ftype a) ->
    BMULT a b = BMULT b a.
Proof.
intros.
unfold BMULT, BINOP.
f_equal.
apply Bmult_commut; auto.
Qed.

Definition RR (_: type) : Type := R.
Definition ftype'  (t: type) : Type := ftype t.

Definition default_rel (t: type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Definition bounds (t: type) : Type :=  (ftype t * bool) * (ftype t * bool).
Definition interp_bounds {t} (bnds: bounds t) (x: ftype t) : bool :=
 let '((lo,blo),(hi,bhi)) := bnds in
 (if blo then compare Lt true lo x  else compare Gt false lo x) &&
 (if bhi then compare Lt true x hi  else compare Gt false x hi).


Definition rounded_finite (t: type) (x: R) : Prop :=
  (Rabs (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
                         (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) x)
    < Raux.bpow Zaux.radix2 (femax t))%R.

Definition exact_round ty r :=
  round radix2 (FLT_exp (3 - femax ty - fprec ty) (fprec ty)) ZnearestE r = r.

Fixpoint acc_prop  (args: list type) (result: type)
             (rel abs : N)
             (precond: klist bounds args)
             (rf: function_type (map RR args) R)
             (f: function_type (map ftype' args) (ftype' result)) {struct args} : Prop.
destruct args as [ | a r].
exact (     (rel=0 <-> abs=0)%N
                 /\ ( rel=0 -> exact_round result rf)%N
                /\ (rounded_finite result rf ->
                   is_finite f = true /\
                   exists delta epsilon,
                  (Rabs delta <= IZR (Z.of_N rel) * default_rel result
                      /\ Rabs epsilon <= IZR (Z.of_N abs) * default_abs result /\
                   FT2R f = rf * (1+delta) + epsilon)%R)).
inversion precond as [| ? ? bnds pre]; clear precond; subst.
exact (forall z: ftype a, interp_bounds bnds z = true ->
             acc_prop r result rel abs pre (rf (FT2R z)) (f z)).
Defined.

Definition floatfunc_congr {args: list type} {result: type}
      (func: function_type (map ftype' args) (ftype' result)) : Prop :=
  forall (al bl: klist ftype args),
      Kforall2 (@float_equiv) al bl ->
      float_equiv
         (applyk ftype args result func (fun _ t => t) al)
         (applyk ftype args result func (fun _ t => t) bl).

Record floatfunc (args: list type) (result: type)
     (precond: klist bounds args)
     (realfunc: function_type (map RR args) R) :=
 {ff_func: function_type (map ftype' args) (ftype' result);
  ff_rel: N;
  ff_abs: N;
  ff_acc: acc_prop args result ff_rel ff_abs precond realfunc ff_func;
  ff_congr: floatfunc_congr ff_func
 }.

Record floatfunc_package ty:=
 {ff_args: list type;
  ff_precond: klist bounds ff_args;
  ff_realfunc: function_type (map RR ff_args) R;
  ff_ff: floatfunc ff_args ty ff_precond ff_realfunc}.

Arguments ff_func [args result precond realfunc].
Arguments ff_acc [args result precond realfunc].
Arguments ff_rel [args result precond realfunc].
Arguments ff_abs [args result precond realfunc].
Arguments ff_args [ty].
Arguments ff_precond [ty].
Arguments ff_realfunc [ty].
Arguments ff_ff [ty].

Lemma is_finite_Binary: forall {ty} `{STD: is_standard ty} (x: ftype ty),
  is_finite x = Binary.is_finite (fprec ty) (femax ty) (float_of_ftype x).
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; try contradiction.
reflexivity.
Qed.

Lemma FT2R_ftype_of_float:
  forall {ty} `{STD: is_standard ty} x,
   FT2R (ftype_of_float x) = B2R _ _ x.
Proof.
intros.
destruct ty as [? ? ? ? ? [|]]; try contradiction.
reflexivity.
Qed.


Lemma compare'_correct
     : forall ty (f1 f2 : ftype ty),
       is_finite f1 = true ->
       is_finite f2 = true ->
       compare' f1 f2 =
       Some (Rcompare (FT2R f1) (FT2R f2)).
Proof.
clear.
intros.
destruct ty as [? ? ? ? ? [|]].
simpl.
apply nonstd_compare_correct'; auto.
apply Bcompare_correct; auto.
Qed.


