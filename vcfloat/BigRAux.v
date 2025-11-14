(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(** Auxiliary theorems for the real-number semantics of big rational numbers. *)

From Coq Require Import Reals.
Require Export vcfloat.BigQAux.
Require Export vcfloat.Q2RAux.
Require Export Flocq.Core.Raux.
Open Scope R_scope.

Definition BigQ2R x := Q2R (BigQ.to_Q x).

Global Instance BigQ2R_proper:
  Proper (BigQ.eq ==> eq) BigQ2R.
Proof.
  do 2 red.
  intros.
  unfold BigQ2R.
  setoid_rewrite H.
  reflexivity.
Qed.
