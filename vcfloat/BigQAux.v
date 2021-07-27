(** R-CoqLib: general-purpose Coq libraries and tactics.
 
 Version 1.0 (2015-12-04)
 
 Copyright (C) 2015 Reservoir Labs Inc.
 All rights reserved.
 
 This file, which is part of R-CoqLib, is free software. You can
 redistribute it and/or modify it under the terms of the GNU General
 Public License as published by the Free Software Foundation, either
 version 3 of the License (GNU GPL v3), or (at your option) any later
 version.
 
 This file is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE for
 more details about the use and redistribution of this file and the
 whole R-CoqLib library.
 
 This work is sponsored in part by DARPA MTO as part of the Power
 Efficiency Revolution for Embedded Computing Technologies (PERFECT)
 program (issued by DARPA/CMO under Contract No: HR0011-12-C-0123). The
 views and conclusions contained in this work are those of the authors
 and should not be interpreted as representing the official policies,
 either expressly or implied, of the DARPA or the
 U.S. Government. Distribution Statement "A" (Approved for Public
 Release, Distribution Unlimited.)
*)
(**
Author: Tahina Ramananandro <ramananandro@reservoir.com>

Auxiliary theorems for big rational numbers
*)

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
