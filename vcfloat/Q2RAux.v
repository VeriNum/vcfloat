(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)
(* Helpers for computing in rational numbers. *)

Require Export QArith Qreals Flocq.Core.Raux Reals.
Open Scope R_scope.

Global Instance Q2R_proper:
  Proper (Qeq ==> eq) Q2R.
Proof.
  do 2 red.
  intros.
  apply Qreals.Qeq_eqR.
  assumption.
Qed.

Lemma Q2R_inject_Z n:
  Q2R (inject_Z n) = IZR n.
Proof.
  unfold Q2R.
  simpl.
  field.
Qed.
