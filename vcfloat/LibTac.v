(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(** R-CoqLib: general-purpose Coq libraries and tactics. *)
(** Basic tactics and logical properties. *)

Ltac break K :=
  match type of K with
      exists x, _ =>
      let x := fresh "x" in
      destruct K as [x K];
        break K
    | _ /\ _ =>
      let K_ := fresh "K_" in
      destruct K as (K_ & K);
        break K_;
        break K
    | _ => idtac
  end.

Lemma exists_and {T: Type} (P: T -> Prop) (Q: Prop):
  (exists x, (P x /\ Q)) ->
  (exists x, P x) /\ Q.
Proof.
  intro H.
  break H.
  eauto.
Qed.

Lemma exists_and_assoc {T: Type} (P Q R: T -> Prop):
  (exists x, P x /\ Q x /\ R x) ->
  exists x, (P x /\ Q x) /\ R x.
Proof.
  intro H.
  break H.
  eauto.
Qed.

Definition option_eqb {T} (eqb: T -> T -> bool) u1 u2 :=
  match u1, u2 with
    | Some t1, Some t2 => eqb t1 t2
    | None, None => true
    | _, _ => false
  end.

Require Setoid.

Lemma option_eqb_eq {T} {eqb: T -> T -> bool}:
  (forall t1 t2, eqb t1 t2 = true <-> t1 = t2) ->
  (forall u1 u2, option_eqb eqb u1 u2 = true <-> u1 = u2).
Proof.
  intros.
  destruct u1; destruct u2; simpl; try intuition congruence.
  rewrite H.
  intuition congruence.
Qed.

Ltac solve_trivial :=
  match goal with
      |- _ /\ _ => split; [ exact I | ]; try solve_trivial
    | |- _ /\ _ => split; [ reflexivity | ]; try solve_trivial
    | |- _ /\ _ => split; [ eassumption | ]; try solve_trivial
    | |- exists _, _ => esplit; solve_trivial
  end.

Definition eqpivot {A} (a: A):
  {o | a = o /\ o = a}.
Proof.
  exists a; auto.
Defined.


From Coq Require Import Lists.List.

Fixpoint list_forall {T} (P: T -> Prop) (l: list T): Prop :=
  match l with
    | nil => True
    | a :: nil => P a
    | a :: l => P a /\ list_forall P l
  end.


Lemma list_forall_spec {T} (P: T -> Prop) l:
  list_forall P l <-> (forall t, In t l -> P t).
Proof.
  induction l.
  {
    simpl.
    tauto.
  }
  destruct l.
  {
    simpl in *.
    firstorder.
    congruence.
  }
  change (list_forall P (a :: t :: l)) with (P a /\ list_forall P (t :: l)).
  revert IHl.
  generalize (t :: l).
  clear t l.
  simpl.
  firstorder.
  congruence.
Qed.

Lemma list_forall_impl {T} (P Q: T -> Prop):
  (forall t, (P t -> Q t)) ->
  (forall l, (list_forall P l -> list_forall Q l)).
Proof.
  intros.
  induction l.
  {
    simpl.
    tauto.
  }
  destruct l.
  {
    simpl.
    auto.
  }
  change (list_forall P (a :: t :: l)) with (P a /\ list_forall P (t :: l)) in H0.
  change (list_forall Q (a :: t :: l)) with (Q a /\ list_forall Q (t :: l)).
  revert IHl H0.
  generalize (t :: l).
  clear t l.
  firstorder.
Qed.

Lemma list_forall_ext {T} (P Q: T -> Prop):
  (forall t, (P t <-> Q t)) ->
  (forall l, (list_forall P l <-> list_forall Q l)).
Proof.
  intros.
  generalize (list_forall_impl P Q).
  generalize (list_forall_impl Q P).
  firstorder.
Qed.

Lemma list_forall_nil {T} (P: T -> Prop):
  list_forall P nil.
Proof.
  exact I.
Qed.

Lemma list_forall_cons {T} (P: T -> Prop) a l:
  P a ->
  list_forall P l ->
  list_forall P (a :: l).
Proof.
  intros.
  destruct l; simpl; auto.
Qed.

Lemma list_forall_cons_inv {T} (P: T -> Prop) a l:
  list_forall P (a :: l) -> P a /\ list_forall P l.
Proof.
  destruct l; simpl; auto.
Qed.

Lemma list_forall_app {T} (P: T -> Prop) l1 l2:
  list_forall P l1 ->
  list_forall P l2 ->
  list_forall P (l1 ++ l2).
Proof.
  induction l1; auto.
  intros.
  apply list_forall_cons_inv in H.
  apply list_forall_cons; intuition.
Qed.


Definition sumbool_to_bool {A B} (u: {A} + {B}): bool :=
  if u then true else false.

Coercion sumbool_to_bool: sumbool >-> bool.

From Coq Require Import ZArith Reals.
Require Import vcfloat.RAux.
Import Lists.List.

Lemma rememb {A} (a: A): {x | x = a}.
Proof.
  eauto.
Qed.
Require Export Morphisms.

Definition rememb_gen {A: Type} (R: A -> A -> Prop) {refl: Reflexive R} (a: A):
  {a_: A | R a a_ /\ R a_ a}.
Proof.
  exists a; eauto.
Defined.

Lemma exists_modus_ponens {T} (Q P R: _ -> Prop):
  (exists s1: T, P s1 /\ Q s1) ->
  (forall s1, Q s1 -> R s1) ->
  exists s1,
    P s1 /\ R s1.
Proof.
  firstorder.
Qed.

Lemma if_bool_eq_dec (b: bool):
  {b_: bool & {u : {b_ = true} + {~ (b_ = true)} |
              (b_ = true <-> b = true) /\
              (forall (A: Type) (a1 a2: A),
          (if b then a1 else a2) = if u then a1 else a2) } }.
Proof.
  exists b.
  destruct b; simpl.
  {
    exists (left Logic.eq_refl).
    tauto.
  }
  exists (@right _ (false <> true) ltac:( discriminate ) ).
  tauto.
Defined.

Lemma asplit (P Q: Prop):
  P -> (P -> Q) -> (P /\ Q).
Proof.
  tauto.
Qed.

  Ltac specialize_assert H :=
    match type of H with
        ?P -> _ =>
        let K := fresh in
        assert P as K; [ | specialize (H K); clear K ]
    end.

Ltac vm_compute_with_meta :=
  match goal with
      |- ?z = _ =>
      let b := fresh "b" in
      let Hb := fresh "Hb" in
      destruct (rememb z) as (b & Hb);
        rewrite <- Hb;
        vm_compute in Hb;
        eexact Hb
  end.
