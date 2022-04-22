(** VCFloat: A Unified Coq Framework for Verifying C Programs with
 Floating-Point Computations. Application to SAR Backprojection.
 
 Version 1.0 (2015-12-04)
 
 Copyright (C) 2015 Reservoir Labs Inc.
 All rights reserved.
 
 This file, which is part of VCFloat, is free software. You can
 redistribute it and/or modify it under the terms of the GNU General
 Public License as published by the Free Software Foundation, either
 version 3 of the License (GNU GPL v3), or (at your option) any later
 version. A verbatim copy of the GNU GPL v3 is included in gpl-3.0.txt.
 
 This file is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE for
 more details about the use and redistribution of this file and the
 whole VCFloat library.
 
 This work is sponsored in part by DARPA MTO as part of the Power
 Efficiency Revolution for Embedded Computing Technologies (PERFECT)
 program (issued by DARPA/CMO under Contract No: HR0011-12-C-0123). The
 views and conclusions contained in this work are those of the authors
 and should not be interpreted as representing the official policies,
 either expressly or implied, of the DARPA or the
 U.S. Government. Distribution Statement "A" (Approved for Public
 Release, Distribution Unlimited.)
 
 
 If you are using or modifying VCFloat in your work, please consider
 citing the following paper:
 
 Tahina Ramananandro, Paul Mountcastle, Benoit Meister and Richard
 Lethin.
 A Unified Coq Framework for Verifying C Programs with Floating-Point
 Computations.
 In CPP (5th ACM/SIGPLAN conference on Certified Programs and Proofs)
 2016.
 
 
 VCFloat requires third-party libraries listed in ACKS along with their
 copyright information.
 
 VCFloat depends on third-party libraries listed in ACKS along with
 their copyright and licensing information.
*)
(**
Author: Tahina Ramananandro <ramananandro@reservoir.com>

Examples from Section 4 of the abovementioned CPP 2016 paper.
**)

Require Import Clight.
Require Import Clightdefs.

Require Import Reals.
Require Clight2FPOpt.
Import Flocq3.Appli.Fappli_IEEE.
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
