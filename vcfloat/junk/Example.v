(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)
(**
Author: Tahina Ramananandro <ramananandro@reservoir.com>

Examples from Section 4 of the CPP 2016 paper.
**)

Require Import Clight.
Require Import Clightdefs.

Require Import Reals.
Require Clight2FPOpt.
Import Flocq.Appli.Fappli_IEEE.
Require Import Maps.
Require Import Values.
Require ClightTac.

Open Scope R_scope.

(** The following ASTs have been obtained through the following process:
1. preprocess example.c
2. remove all unsupported "long double" definitions
3. use CompCert Clightgen
4. extract the expressions from the return statements of f and g.

Assume x is a double-precision floating-point variable.
*)

(**
2.0f * (float) x - 3.0
*)

Definition _x : ident := 47%positive.

Definition e1 :=
  Ebinop Osub
         (Ebinop Omul
                 (Econst_single (Float32.of_bits (Int.repr 1073741824)) tfloat)
                 (Ecast (Etempvar _x tdouble) tfloat) tfloat)
         (Econst_float (Float.of_bits (Int64.repr 4613937818241073152)) tdouble)
         tdouble.

Goal
  forall ge e x m,
    is_finite _ _ x = true ->
    1 <= B2R _ _ x <= 2 ->
    exists v,
      eval_expr ge e (PTree.set _x (Vfloat x) (PTree.empty _)) m e1 v
      /\ True.
Proof.
  intros ge e x m H H0.
  apply ClightTac.Vfloat_exists.

  (**
    The goal is of the form: exists y, eval_expr ? ? ? ? e1 (Vfloat y) /\ _.
    So, we are going to transform e2 into a non-annotated core computation ?z of VCfloat,
    and y will be its floating-point value, such that Hy: fval ?z = y
  *)
  Clight2FPOpt.C_to_float_as y Hy.
  (** Then, to annotate ?z , we are going to take Hy (where ?z appears in: fval ?z = y)
      and we will tentatively deduce that y is finite (to store in hypothesis Hy_finite)
      and the real-number value of y (to store in hypothesis Hy_val).

      The validity condition checks will appear during the automatic search for annotation.
  *)

  Clight2FPOpt.compute_fval_as Hy Hy_finite Hy_val.
  exact I.
Qed.

(**
#include <float.h>

DBL_MAX * (x + .5)
*)

Definition e2 :=
  Ebinop Omul
         (Econst_float (Float.of_bits (Int64.repr 9218868437227405311)) tdouble)
         (Ebinop Oadd (Etempvar _x tdouble)
                 (Econst_float (Float.of_bits (Int64.repr 4602678819172646912)) tdouble)
                 tdouble) tdouble.

Goal
  forall ge e x m,
    is_finite _ _ x = true ->
    1 <= B2R _ _ x <= 2 ->
    exists v,
      eval_expr ge e (PTree.set _x (Vfloat x) (PTree.empty _)) m e2 v
      /\ False.
Proof.
  intros ge e x m H H0.
  apply ClightTac.Vfloat_exists.

  (**
    The goal is of the form: exists y, eval_expr ? ? ? ? e2 (Vfloat y) /\ _.
    So, we are going to transform e2 into a non-annotated core computation ?z of VCfloat,
    and y will be its floating-point value, such that Hy: fval ?z = y
  *)
  Clight2FPOpt.C_to_float_as y Hy.
  (** Then, to annotate ?z , we are going to take Hy (where ?z appears in: fval ?z = y)
      and we will tentatively deduce that y is finite (to store in hypothesis Hy_finite)
      and the real-number value of y (to store in hypothesis Hy_val).

      The validity condition checks will appear during the automatic search for annotation.
  *)
  Fail Clight2FPOpt.compute_fval_as Hy Hy_finite Hy_val.
Abort.
