(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

Require Import Lia.
From vcfloat Require Export FPCore. (* FPLang Rounding FPLangOpt.*)
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

Require Import Coq.Classes.EquivDec.
Require Import ZArith.

Lemma conv_nan_ex:
  { conv_nan: forall (prec1 emax1 prec2 emax2 : Z),
                (1< prec2)%Z ->
                binary_float prec1 emax1 -> (* guaranteed to be a nan, if this is not a nan then any result will do *)
                nan_payload prec2 emax2
  | 
  conv_nan (fprec Tsingle) (femax Tsingle) (fprec Tdouble) (femax Tdouble) (fprec_gt_one _) = Floats.Float.of_single_nan
  /\
  conv_nan (fprec Tdouble) (femax Tdouble) (fprec Tsingle) (femax Tsingle) (fprec_gt_one _) =  Floats.Float.to_single_nan
  }.
Proof.
  eapply exist.
  Unshelve.
  {
    shelve.
  }
  intros ? ? ? ? ?.
(*  destruct (eq_dec (prec1, fprec Tsingle) (emax1, femax Tsingle)). *)
  destruct (BinInt.Z.eq_dec prec1 (fprec Tsingle)). {
    destruct (BinInt.Z.eq_dec emax1 (femax Tsingle)); [ | intros; auto using any_nan].
    destruct (BinInt.Z.eq_dec prec2 (fprec Tdouble)); [ | intros; auto using any_nan].
    destruct (BinInt.Z.eq_dec emax2 (femax Tdouble)); [ | intros; auto using any_nan].
    subst; exact Floats.Float.of_single_nan.
  }
  destruct (BinInt.Z.eq_dec prec1 (fprec Tdouble)). {
    destruct (BinInt.Z.eq_dec emax1 (femax Tdouble)); [ | intros; auto using any_nan].
    destruct (BinInt.Z.eq_dec prec2 (fprec Tsingle)); [ | intros; auto using any_nan].
    destruct (BinInt.Z.eq_dec emax2 (femax Tsingle)); [ | intros; auto using any_nan].
    subst; exact Floats.Float.to_single_nan.
  }
  intros.
  auto using any_nan.
  Unshelve.
  split; reflexivity.
Defined.

Definition conv_nan := let (c, _) := conv_nan_ex in c.

Lemma single_double_ex (U: forall prec emax, (1<prec)%Z -> Type):
  (forall prec emax H, U prec emax H) ->
  forall (s: forall H, U (fprec Tsingle) (femax Tsingle) H)
         (d: forall H, U (fprec Tdouble) (femax Tdouble) H),
    {
      f: forall prec emax H, U prec emax H |
      f (fprec Tsingle) (femax Tsingle) = s /\
      f (fprec Tdouble) (femax Tdouble) = d
    }.
Proof.
  intro ref.
  intros.
  esplit.
  Unshelve.
  shelve.
  intros prec emax H.
  destruct (Z.eq_dec prec (fprec Tsingle)). {
     destruct (Z.eq_dec emax (femax Tsingle)); [ | apply ref].
     subst. apply s.
  }
  destruct (Z.eq_dec prec (fprec Tdouble)). {
     destruct (Z.eq_dec emax (femax Tdouble)); [ | apply ref].
     subst. apply d.
  }
  apply ref.
  Unshelve.
  split; reflexivity.
Defined.

Definition single_double (U: forall prec emax, (1<prec)%Z -> Type)
           (f_: forall prec emax H, U prec emax H)
           (s: forall H, U (fprec Tsingle) (femax Tsingle) H)
           (d: forall H, U (fprec Tdouble) (femax Tdouble) H)
:
  forall prec emax H, U prec emax H :=
  let (f, _) := single_double_ex U f_ s d in f.

Definition binop_nan :  forall prec emax,
       (1<prec)%Z ->
       binary_float prec emax ->
       binary_float prec emax ->
       nan_payload prec emax :=
  single_double
    (fun prec emax H =>
       binary_float prec emax ->
       binary_float prec emax ->
       nan_payload prec emax) 
     (fun prec emax H _ _ => any_nan prec emax H)
     (fun _ => Floats.Float32.binop_nan)
     (fun _ => Floats.Float.binop_nan).

Definition abs_nan :=
  single_double
    (fun prec emax H =>
       binary_float prec emax ->
       nan_payload prec emax) 
     (fun prec emax H  _ => any_nan prec emax H)
     (fun _ => Floats.Float32.abs_nan)
     (fun _ => Floats.Float.abs_nan).

Definition opp_nan :=
  single_double
    (fun prec emax H =>
       binary_float prec emax ->
       nan_payload prec emax) 
     (fun prec emax H  _ => any_nan prec emax H)
     (fun _ => Floats.Float32.neg_nan)
     (fun _ => Floats.Float.neg_nan).

Module FMA_NAN. 
(* some of these definitions adapted from [the open-source part of] CompCert  *)
Import ZArith. Import Coq.Lists.List.

(** Transform a Nan payload to a quiet Nan payload. *)

Definition quiet_nan_payload (prec: Z) (p: positive) :=
  Z.to_pos (Zbits.P_mod_two_p (Pos.lor p ((Zaux.iter_nat xO (Z.to_nat (prec - 2)) 1%positive))) (Z.to_nat (prec - 1))).

Lemma quiet_nan_proof (prec: Z): (1<prec)%Z -> 
   forall p, Binary.nan_pl prec (quiet_nan_payload prec p) = true.
Proof. 
intros.
 apply normalized_nan; auto; lia.
Qed.

Definition quiet_nan prec emax (H: (1<prec)%Z) (sp: bool * positive) :
         {x : binary_float prec emax | Binary.is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (Binary.B754_nan prec emax s (quiet_nan_payload prec p) 
              (quiet_nan_proof prec H p)) (eq_refl _).

Definition default_nan (prec: Z) := (fst Archi.default_nan_64, iter_nat (Z.to_nat (prec - 2)) _ xO xH).

Inductive NAN_SCHEME := NAN_SCHEME_ARM | NAN_SCHEME_X86 | NAN_SCHEME_RISCV.

Definition the_nan_scheme : NAN_SCHEME.
Transparent Archi.choose_nan_64.
try (unify Archi.choose_nan_64 Archi.default_nan_64; exact NAN_SCHEME_RISCV);
try (unify Archi.choose_nan_64 (fun l => match l with nil => Archi.default_nan_64 | n::_ => n end);
      exact NAN_SCHEME_X86);
try (let p := constr:(Archi.choose_nan_64) in
      let p := eval red in p in
      match p with _ (fun p => negb (Pos.testbit p 51)) _ => idtac end;
      exact NAN_SCHEME_ARM).
Opaque Archi.choose_nan_64.
Defined.

Definition ARMchoose_nan (is_signaling: positive -> bool) 
                      (default: bool * positive)
                      (l0: list (bool * positive)) : bool * positive :=
  let fix choose_snan (l1: list (bool * positive)) :=
    match l1 with
    | nil =>
        match l0 with nil => default | n :: _ => n end
    | ((s, p) as n) :: l1 =>
        if is_signaling p then n else choose_snan l1
    end
  in choose_snan l0.

Definition choose_nan (prec: Z) : list (bool * positive) -> bool * positive :=
 match the_nan_scheme with
 | NAN_SCHEME_RISCV => fun _ => default_nan prec
 | NAN_SCHEME_X86 => fun l => match l with nil => default_nan prec | n :: _ => n end
 | NAN_SCHEME_ARM => ARMchoose_nan (fun p => negb (Pos.testbit p (Z.to_N (prec - 2))))
                                          (default_nan prec)
 end.

Definition cons_pl {prec emax} (x : binary_float prec emax) (l : list (bool * positive)) :=
match x with
| Binary.B754_nan _ _ s p _ => (s, p) :: l
| _ => l
end.

Definition fma_nan_1 prec emax H
    (x y z: binary_float prec emax) : nan_payload prec emax :=
  let '(a, b, c) := Archi.fma_order x y z in
  quiet_nan prec emax H (choose_nan prec (cons_pl a (cons_pl b (cons_pl c nil)))).

Definition fma_nan_pl prec emax H (x y z: binary_float prec emax) : {x : binary_float prec emax | Binary.is_nan _ _ x = true} :=
  match x, y with
  | Binary.B754_infinity _ _ _, Binary.B754_zero _ _ _ | Binary.B754_zero _ _ _, Binary.B754_infinity _ _ _ =>
      if Archi.fma_invalid_mul_is_nan
      then quiet_nan prec emax H (choose_nan prec (default_nan prec :: cons_pl z nil))
      else fma_nan_1 prec emax H x y z
  | _, _ =>
      fma_nan_1 prec emax H x y z
  end.

End FMA_NAN.

#[export] Instance nans: Nans :=
  {
    conv_nan := conv_nan;
    plus_nan := binop_nan;
    mult_nan := binop_nan;
    div_nan := binop_nan;
    abs_nan := abs_nan;
    opp_nan := opp_nan;
    sqrt_nan := (fun prec emax H _ => any_nan prec emax H);
    fma_nan := FMA_NAN.fma_nan_pl
  }.

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
Lemma Float32_add_rewrite: Float32.add = @BPLUS _ Tsingle _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_add_rewrite : float_elim.
Lemma Float32_sub_rewrite: Float32.sub = @BMINUS _ Tsingle _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_sub_rewrite : float_elim.
Lemma Float32_mul_rewrite: Float32.mul = @BMULT _ Tsingle _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_mul_rewrite : float_elim.
Lemma Float32_div_rewrite: Float32.div = @BDIV _ Tsingle _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_div_rewrite : float_elim.
Lemma Float32_neg_rewrite: Float32.neg = @BOPP _ Tsingle _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_neg_rewrite : float_elim.
Lemma Float32_abs_rewrite: Float32.abs = @BABS _ Tsingle _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float32_abs_rewrite : float_elim.

Lemma Float_add_rewrite: Float.add = @BPLUS _ Tdouble _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_add_rewrite : float_elim.
Lemma Float_sub_rewrite: Float.sub = @BMINUS _ Tdouble _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_sub_rewrite : float_elim.
Lemma Float_mul_rewrite: Float.mul = @BMULT _ Tdouble _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_mul_rewrite : float_elim.
Lemma Float_div_rewrite: Float.div = @BDIV _ Tdouble _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_div_rewrite : float_elim.
Lemma Float_neg_rewrite: Float.neg = @BOPP _ Tdouble _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_neg_rewrite : float_elim.
Lemma Float_abs_rewrite: Float.abs = @BABS _ Tdouble _.
Proof. reflexivity. Qed.
#[export] Hint Rewrite Float_abs_rewrite : float_elim.

Lemma float_of_single_eq: Float.of_single = @cast _ Tdouble Tsingle _ _.
Proof. reflexivity. Qed.

Lemma float32_to_double_eq: Float32.to_double = @cast _ Tdouble Tsingle _ _.
Proof. reflexivity. Qed.
Lemma float32_of_float_eq: Float32.of_double = @cast _ Tsingle Tdouble _ _.
Proof. reflexivity. Qed.
Lemma float_to_single_eq: Float.to_single = @cast _ Tsingle Tdouble _ _.
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

