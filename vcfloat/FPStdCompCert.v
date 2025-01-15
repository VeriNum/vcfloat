Require Import Lia.
From vcfloat Require Import FPStdLib. (* FPLang Rounding FPLangOpt.*)
Require compcert.common.AST compcert.common.Values.
Require Import compcert.lib.Floats.
Import Binary BinPos.

Inductive val_inject: Values.val -> forall ty, ftype ty -> Prop :=
| val_inject_single (f: ftype Tsingle):
    val_inject (Values.Vsingle f) Tsingle f
| val_inject_double f:
    val_inject (Values.Vfloat f) Tdouble f
.

Lemma val_inject_single_inv (f1: float32) (f2: ftype Tsingle):
  val_inject (Values.Vsingle f1) Tsingle f2 ->
  f1 = f2.
Proof.
  inversion 1; subst.
  apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H2; auto.
Qed.

Lemma val_inject_double_inv f1 f2:
  val_inject (Values.Vfloat f1) Tdouble f2 ->
  f1 = f2.
Proof.
  inversion 1; subst.
  apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H2; auto.
Qed.

Require vcfloat.FPCompCert.

#[export] Instance nans: FPCore.Nans := FPCompCert.nans.

Lemma val_inject_eq_rect_r v ty1 e:
  val_inject v ty1 e ->
  forall ty2 (EQ: ty2 = ty1),
    val_inject v ty2 (eq_rect_r _ e EQ).
Proof.
  intros.
  subst.
  assumption.
Qed.
      
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

(** Why do we need this rewrite hint database?
   You might think that all of this could be accomplished with "change"
   instead of "rewrite".  But if you do that, then Qed takes forever. *)
Lemma Float32_add_rewrite: Float32.add = @BPLUS _ Tsingle.
Proof. reflexivity. Qed.

#[export] Hint Rewrite Float32_add_rewrite : float_elim.
Lemma Float32_sub_rewrite: Float32.sub = @BMINUS _ Tsingle.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_sub_rewrite : float_elim.
Lemma Float32_mul_rewrite: Float32.mul = @BMULT _ Tsingle.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_mul_rewrite : float_elim.
Lemma Float32_div_rewrite: Float32.div = @BDIV _ Tsingle.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_div_rewrite : float_elim.
Lemma Float32_neg_rewrite: Float32.neg = @BOPP _ Tsingle.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_neg_rewrite : float_elim.
Lemma Float32_abs_rewrite: Float32.abs = @BABS _ Tsingle.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_abs_rewrite : float_elim.

Lemma Float_add_rewrite: Float.add = @BPLUS _ Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_add_rewrite : float_elim.
Lemma Float_sub_rewrite: Float.sub = @BMINUS _ Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_sub_rewrite : float_elim.
Lemma Float_mul_rewrite: Float.mul = @BMULT _ Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_mul_rewrite : float_elim.
Lemma Float_div_rewrite: Float.div = @BDIV _ Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_div_rewrite : float_elim.
Lemma Float_neg_rewrite: Float.neg = @BOPP _ Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_neg_rewrite : float_elim.
Lemma Float_abs_rewrite: Float.abs = @BABS _ Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_abs_rewrite : float_elim.

Lemma float_of_single_eq: Float.of_single = @cast _ Tdouble Tsingle.
Proof. reflexivity. Qed.

Lemma float32_to_double_eq: Float32.to_double = @cast _ Tdouble Tsingle.
Proof. reflexivity. Qed.
Lemma float32_of_float_eq: Float32.of_double = @cast _ Tsingle Tdouble.
Proof. reflexivity. Qed.
Lemma float_to_single_eq: Float.to_single = @cast _ Tsingle Tdouble.
Proof. reflexivity. Qed.
#[export] Hint Rewrite float_of_single_eq float32_to_double_eq
          float32_of_float_eq float_to_single_eq : float_elim.

Import Float_notations.

Lemma B754_finite_ext:
  forall prec emax s m e p1 p2,
    Binary.B754_finite prec emax s m e p1 = Binary.B754_finite prec emax s m e p2.
Proof.
intros.
f_equal.
apply Classical_Prop.proof_irrelevance.
Qed.

Import Integers.

Ltac canonicalize_float_constant x :=
match x with
| Float32.of_bits (Int.repr ?a) =>
  const_Z a;
  let x' := constr:(Bits.b32_of_bits a) in
  let y := eval compute in x' in
 match y with
   | Binary.B754_finite _ _ ?s ?m ?e _ =>
     let z := constr:(b32_B754_finite s m e (@eq_refl bool true))
      in change x with x'; 
        replace x' with z by (apply B754_finite_ext; reflexivity)
   | Binary.B754_zero _ _ ?s => 
       let z := constr:(b32_B754_zero s) in
       change x with z        
  end
| Float.of_bits (Int64.repr ?a) =>
  const_Z a;
  let x' := constr:(Bits.b64_of_bits a) in
  let y := eval compute in x' in
 match y with
   | Binary.B754_finite _ _ ?s ?m ?e _ =>
     let z := constr:(b64_B754_finite s m e (@eq_refl bool true))
      in change x with x'; 
        replace x' with z by (apply B754_finite_ext; reflexivity)
   | Binary.B754_zero _ _ ?s => 
       let z := constr:(b64_B754_zero s) in
       change x with z        
  end
end.

Ltac canonicalize_float_constants := 
  repeat
    match goal with
    | |- context [Binary.B754_finite 24 128 ?s ?m ?e ?p] =>
         let x := constr:(Binary.B754_finite 24 128 s m e p) in
         let e' := eval compute in e in
         let z := constr:(b32_B754_finite s m e' (@eq_refl bool true)) in
         replace x with z by (apply B754_finite_ext; reflexivity)
    | |- context [Binary.B754_finite 53 1024 ?s ?m ?e ?p] =>
         let x := constr:(Binary.B754_finite 53 1024 s m e p) in
         let e' := eval compute in e in
         let z := constr:(b64_B754_finite s m e' (@eq_refl bool true)) in
         replace x with z by (apply B754_finite_ext; reflexivity)
    | |- context [Float32.of_bits (Int.repr ?a)] =>
     canonicalize_float_constant constr:(Float32.of_bits (Int.repr a))
    | |- context [Float.of_bits (Int64.repr ?a)] =>
     canonicalize_float_constant constr:(Float.of_bits (Int64.repr a))
    end.

