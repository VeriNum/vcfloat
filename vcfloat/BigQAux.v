(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(** R-CoqLib: general-purpose Coq libraries and tactics. *)

(* Auxiliary theorems for big rational numbers *)

Require Export Morphisms.
Require Export QArith.
Require Export Bignums.BigQ.BigQ.

Global Instance to_Q_morph: Proper (BigQ.eq ==> Qeq) BigQ.to_Q.
Proof.
  do 2 red.
  intros.
  rewrite <- BigQ.eqb_eq in H.
  rewrite BigQ.spec_eq_bool in H.
  rewrite Qeq_bool_iff in H.
  assumption.
Qed.

Lemma to_Q_bigZ z:
  BigQ.to_Q (BigQ.Qz z) == inject_Z (BigZ.to_Z z).
Proof.
  reflexivity.
Qed.

Definition Bnum b :=
  match b with
  | BigQ.Qz t => t
  | BigQ.Qq n d =>
    if (d =? BigN.zero)%bigN then 0%bigZ else n
  end.

Definition Bden b :=
  match b with
  | BigQ.Qz _ => 1%bigN
  | BigQ.Qq _ d => if (d =? BigN.zero)%bigN then 1%bigN else d 
  end.
