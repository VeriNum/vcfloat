Require Import ZArith Lia Reals Coq.Lists.List.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra klist Float_notations.


Definition ZLT a b: Prop := Bool.Is_true (Z.ltb a b).

Lemma ZLT_intro a b:
  (a < b)%Z ->
  ZLT a b.
Proof.
  intros.
  unfold ZLT, Bool.Is_true, Z.lt, Z.ltb in *.
  rewrite H.
  apply I.
Defined.

Lemma ZLT_elim a b:
  ZLT a b ->
  (a < b)%Z.
Proof.
  intros.
  unfold ZLT, Bool.Is_true, Z.lt, Z.ltb in *.
  destruct (Z.compare a b); auto; contradiction.
Defined.

Lemma Is_true_eq a (h1 h2: Bool.Is_true a):
  h1 = h2.
Proof.
  destruct a; try contradiction.
  unfold Bool.Is_true in h1, h2.
  destruct h1. destruct h2. reflexivity.
Defined.


Definition extend_comp (c: comparison) (b: bool) (d: option comparison) :=
 match d with
 | None => false
 | Some c' =>
 match c, b, c' with
 | Gt, true, Gt => true
 | Gt, false, Lt => true
 | Gt, false, Eq => true
 | Eq, true, Eq => true
 | Eq, false, Gt => true
 | Eq, false, Lt => true
 | Lt, true, Lt => true
 | Lt, false, Gt => true
 | Lt, false, Eq => true
 | _, _, _ => false
 end
 end.

Definition nan_payload prec emax : Type :=
   {x : binary_float prec emax | Binary.is_nan prec emax x = true}.

Import Bool.

Definition nan_pl_eqb {prec1 emax1 prec2 emax2}
         (n1: nan_payload prec1 emax1) (n2: nan_payload prec2 emax2) :=
 match proj1_sig n1, proj1_sig n2 with
 | B754_nan _ _ b1 pl1 _, B754_nan _ _ b2 pl2 _ => Bool.eqb b1 b2 && Pos.eqb pl1 pl2
 | _, _ => true
 end.

Definition nan_pl_eqb' {prec1 emax1 prec2 emax2}
         (n1: nan_payload prec1 emax1) (n2: nan_payload prec2 emax2) : bool.
destruct n1 as [x1 e1].
destruct n2 as [x2 e2].
unfold Binary.is_nan in *.
destruct x1; try discriminate.
destruct x2; try discriminate.
apply (Bool.eqb s s0 && Pos.eqb pl pl0).
Defined.

Lemma nan_pl_sanity_check:
   forall prec1 emax1 prec2 emax2 n1 n2,
   @nan_pl_eqb' prec1 emax1 prec2 emax2 n1 n2 = @nan_pl_eqb prec1 emax1 prec2 emax2 n1 n2.
Proof.
intros.
destruct n1 as [x1 e1], n2 as [x2 e2].
simpl.
unfold Binary.is_nan in *.
destruct x1; try discriminate.
destruct x2; try discriminate.
unfold nan_pl_eqb. simpl.
auto.
Qed.

Lemma nan_payload_eqb_eq prec emax (n1 n2: nan_payload prec emax):
  (nan_pl_eqb n1 n2 = true <-> n1 = n2).
Proof.
  unfold nan_pl_eqb.
  destruct n1; destruct n2; simpl.
  destruct x; try discriminate.
  destruct x0; try discriminate.
  split; intros.
 -
  rewrite andb_true_iff in H. destruct H.
  rewrite eqb_true_iff in H.
  rewrite Pos.eqb_eq in H0.
  assert (e=e0) by
     (apply Eqdep_dec.eq_proofs_unicity; destruct x; destruct y; intuition congruence).
   subst s0 pl0 e0.
 assert (e1=e2) by
     (apply Eqdep_dec.eq_proofs_unicity; destruct x; destruct y; intuition congruence).
   subst e2.
  reflexivity.
 - inversion H; clear H; subst.
    rewrite eqb_reflx. rewrite Pos.eqb_refl. reflexivity.
Qed.

Definition binary_float_eqb {prec1 emax1 prec2 emax2} (b1: binary_float prec1 emax1) (b2: binary_float prec2 emax2): bool :=
  match b1, b2 with
    | B754_zero _ _ b1, B754_zero _ _ b2 => Bool.eqb b1 b2
    | B754_infinity _ _ b1, B754_infinity _ _ b2 => Bool.eqb b1 b2
    | B754_nan _ _ b1 n1 _, B754_nan _ _ b2 n2 _ => Bool.eqb b1 b2 && Pos.eqb n1 n2
    | B754_finite _ _ b1 m1 e1 _, B754_finite _ _ b2 m2 e2 _ =>
      Bool.eqb b1 b2 && Pos.eqb m1 m2 && Z.eqb e1 e2
    | _, _ => false
  end.

Lemma binary_float_eqb_eq prec emax (b1 b2: binary_float prec emax):
  binary_float_eqb b1 b2 = true <-> b1 = b2.
Proof.
  destruct b1; destruct b2; simpl;

      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
- split; intro.
   + destruct H; subst; f_equal.
      apply Eqdep_dec.eq_proofs_unicity.
      destruct x; destruct y; intuition congruence.
   + inversion H; clear H; subst; auto.
- split; intro.
   + destruct H as [[? ?] ?].
      apply Z.eqb_eq in H1. subst.
      f_equal.
      apply Eqdep_dec.eq_proofs_unicity.
      destruct x; destruct y; intuition congruence.
   + inversion H; clear H; subst; split; auto.
       apply Z.eqb_eq. auto.
Qed.

Definition binary_float_equiv {prec emax}
(b1 b2: binary_float prec emax): Prop :=
  match b1, b2 with
    | B754_zero _ _ b1, B754_zero _ _ b2 => b1 = b2
    | B754_infinity _ _ b1, B754_infinity _ _ b2 =>  b1 = b2
    | B754_nan _ _ _ _ _, B754_nan _ _ _ _ _ => True
    | B754_finite _ _ b1 m1 e1 _, B754_finite _ _ b2 m2 e2 _ =>
      b1 = b2 /\  m1 = m2 /\ e1 = e2
    | _, _ => False
  end.

Lemma binary_float_equiv_refl prec emax (b1: binary_float prec emax):
     binary_float_equiv b1 b1.
Proof.
destruct b1; simpl; auto. Qed.

Lemma binary_float_equiv_sym prec emax (b1 b2: binary_float prec emax):
     binary_float_equiv b1 b2 -> binary_float_equiv b2 b1.
Proof.
intros.
destruct b1; destruct b2; simpl; auto.
destruct H as (A & B & C); subst; auto. Qed.

Lemma binary_float_equiv_trans prec emax (b1 b2 b3: binary_float prec emax):
  binary_float_equiv b1 b2 ->
  binary_float_equiv b2 b3 -> binary_float_equiv b1 b3.
Proof.
intros.
destruct b1; destruct b2; destruct b3; simpl; auto.
all: try (destruct H; destruct H0; reflexivity).
destruct H; destruct H0. subst. destruct H2; destruct H1; subst; auto.
Qed.

Lemma binary_float_eqb_equiv prec emax (b1 b2: binary_float prec emax):
   binary_float_eqb b1 b2 = true -> binary_float_equiv b1 b2 .
Proof.
  destruct b1; destruct b2; simpl;
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
      rewrite ?Z.eqb_eq;
      rewrite ?and_assoc; auto.
Qed.

Lemma binary_float_finite_equiv_eqb prec emax (b1 b2: binary_float prec emax):
Binary.is_finite prec emax b1  = true ->
binary_float_equiv b1 b2 -> binary_float_eqb b1 b2 = true .
Proof.
  destruct b1; destruct b2; simpl;
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
      rewrite ?Z.eqb_eq;
      rewrite ?and_assoc; auto.
Qed.

Lemma binary_float_eq_equiv prec emax (b1 b2: binary_float prec emax):
   b1 = b2 -> binary_float_equiv b1 b2.
Proof.
intros.
apply binary_float_eqb_eq in H.
apply binary_float_eqb_equiv in H; apply H.
Qed.

Lemma binary_float_equiv_eq prec emax (b1 b2: binary_float prec emax):
   binary_float_equiv b1 b2 -> Binary.is_nan _ _ b1 =  false -> b1 = b2.
Proof.
intros.
assert (binary_float_eqb b1 b2 = true).
- destruct b1; destruct b2; simpl in H; subst; simpl; auto;
  try discriminate;
  try apply eqb_reflx.
rewrite ?andb_true_iff.
destruct H; rewrite H.
destruct H1; rewrite H1; rewrite H2; split. split; auto.
apply eqb_reflx.
apply Pos.eqb_eq; reflexivity.
apply Z.eqb_eq; reflexivity.
- apply binary_float_eqb_eq; apply H1.
Qed.

Lemma binary_float_inf_equiv_eqb prec emax (b1 b2: binary_float prec emax):
Binary.is_finite prec emax b1  = false ->
Binary.is_nan prec emax b1  = false ->
binary_float_equiv b1 b2 -> binary_float_eqb b1 b2 = true .
Proof.
  destruct b1; destruct b2; simpl;
      (repeat rewrite andb_true_iff);
      (try rewrite Bool.eqb_true_iff);
      (try rewrite Pos.eqb_eq);
      (try intuition congruence).
Qed.


Lemma binary_float_equiv_nan prec emax (b1 b2: binary_float prec emax):
binary_float_equiv b1 b2 -> Binary.is_nan _ _ b1 = true -> Binary.is_nan _ _ b2 = true.
Proof.
intros.
destruct b1; simpl in H0; try discriminate.
destruct b2; simpl in H; try contradiction.
simpl; reflexivity.
Qed.

Lemma exact_inverse (prec emax : Z)
(prec_gt_0_ : FLX.Prec_gt_0 prec)
(Hmax : (prec < emax)%Z) :
forall (b1 b2: binary_float prec emax),
is_finite_strict prec emax b1 = false ->
Bexact_inverse prec emax prec_gt_0_ Hmax b1 = Some b2 -> False.
Proof.
intros.
apply Bexact_inverse_correct in H0; destruct H0; rewrite H0 in H; discriminate.
Qed.

Definition B2F {prec emax} (f : binary_float prec emax):
  Defs.float Zaux.radix2 :=
match f with
| @B754_finite _ _ s m e _ =>
      {|
      Defs.Fnum := Zaux.cond_Zopp s (Z.pos m);
      Defs.Fexp := e |}
| _ =>
  {|
    Defs.Fnum := 0;
    Defs.Fexp := 0
  |}
end.

Lemma B2F_F2R_B2R {prec emax} f:
  B2R prec emax f = Defs.F2R (B2F f).
Proof.
  destruct f; simpl; unfold Defs.F2R; simpl; ring.
Qed.

Definition F2R beta (f: Defs.float beta): R :=
  match f with
    | Defs.Float _ Fnum Fexp =>
      IZR Fnum * Raux.bpow beta Fexp
  end.

Lemma F2R_eq beta f:
  F2R beta f = Defs.F2R f.
Proof.
  destruct f; reflexivity.
Qed.

Definition build_nan_full {prec emax} (pl: nan_payload prec emax) :=
  let n := proj1_sig pl in F754_nan (Bsign _ _ n) (get_nan_pl _ _ n).

Ltac const_pos p :=
  lazymatch p with xH => idtac | xI ?p => const_pos p | xO ?p => const_pos p end.

Ltac const_Z i :=
  lazymatch i with
  | Zpos ?p => const_pos p
  | Zneg ?p => const_pos p
  | Z0 => idtac
 end.

Ltac const_bool b := lazymatch b with true => idtac | false => idtac end.

Ltac const_float f :=
 lazymatch f with
 | Float_notations.b32_B754_zero ?s => const_bool s
 | Float_notations.b32_B754_finite ?s ?m ?e _  => const_bool s; const_pos m; const_Z e
 | Float_notations.b32_B754_infinity ?s  => const_bool s
 | Float_notations.b64_B754_zero ?s => const_bool s
 | Float_notations.b64_B754_finite ?s ?m ?e  _ => const_bool s; const_pos m; const_Z e
 | Float_notations.b64_B754_infinity ?s  => const_bool s
 | B754_zero ?prec ?emax ?s => const_Z prec; const_Z emax; const_bool s
 | B754_finite ?prec ?emax ?s ?m ?e _ => const_Z prec; const_Z emax; const_bool s; const_pos m; const_Z e
 | B754_infinity ?prec ?emax ?s => const_Z prec; const_Z emax; const_bool s
 | B754_nan ?prec ?emax ?s ?p _ => const_Z prec; const_Z emax; const_bool s; const_pos p
 end.

Lemma B754_finite_replace_proof:
  forall prec emax s m e H1 H2,
  B754_finite prec emax s m e H1 = B754_finite prec emax s m e H2.
Proof.
intros.
f_equal.
apply  Classical_Prop.proof_irrelevance.
Qed .

Ltac compute_float_operation E :=
  (* E should be a float expression in the goal below the line,
     that is known to compute to B754_finite;
     for example, a binary operator (Bdiv, Bplus, etc.) applied
     to constant prec,emax and two constant arguments.
     This tactic replaces E with its computed value, and in particular
     where the proof  of SpecFloat.bounded is simply (eq_refl true).  *)
           let z := eval hnf in E in
           lazymatch z with
           | B754_finite ?prec ?emax ?s ?m ?e ?H =>
             let w := constr:(B754_finite prec emax s m e) in
             let w := eval compute in w in
             let w := constr:(w (eq_refl true)) in
             replace E with w by apply B754_finite_replace_proof
           | B754_zero ?prec ?emax ?s =>
                  let w := constr:(B754_zero prec emax s) in
                  let w := eval compute in w in
                   change E with w
           end.

Inductive option_rel [A B: Type] (R: A -> B -> Prop) : option A -> option B -> Prop :=
  | option_rel_none: option_rel R None None
  | option_rel_some: forall x y, R x y -> option_rel R (Some x) (Some y).

Inductive FF2B_gen_spec (prec emax: Z) (x: full_float): binary_float prec emax -> Prop :=
  | FF2B_gen_spec_invalid (Hx: valid_binary prec emax x = false):
      FF2B_gen_spec prec emax x (B754_infinity _ _ (sign_FF x))
  | FF2B_gen_spec_valid (Hx: valid_binary prec emax x = true)
                        y (Hy: y = FF2B _ _ _ Hx):
      FF2B_gen_spec _ _ x y
.

Lemma FF2B_gen_spec_unique prec emax x y1:
  FF2B_gen_spec prec emax x y1 ->
  forall y2,
    FF2B_gen_spec prec emax x y2 ->
    y1 = y2.
Proof.
  inversion 1; subst;
  inversion 1; subst; try congruence.
  f_equal.
  apply Eqdep_dec.eq_proofs_unicity.
  generalize bool_dec. clear. firstorder.
Qed.

Lemma bool_true_elim {T} a  (f: _ -> T) g H:
  match a as a' return a = a' -> _ with
    | true => f
    | false => g
  end eq_refl = f H.
Proof.
  destruct a; try congruence.
  f_equal.
  apply Eqdep_dec.eq_proofs_unicity.
  decide equality.
Qed.

Definition FF2B_gen prec emax x :=
  match valid_binary prec emax x as y return valid_binary prec emax x = y -> _ with
    | true => fun Hx => FF2B _ _ _ Hx
    | false => fun _ => B754_infinity _ _ (sign_FF x)
  end eq_refl.

Lemma FF2B_gen_correct prec emax x (Hx: valid_binary prec emax x = true):
  FF2B_gen _ _ x = FF2B _ _ _ Hx.
Proof.
  apply bool_true_elim.
Qed.

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

