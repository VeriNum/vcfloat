(** Test2.v:  application demo of "ftype" usage-style of VCfloat.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.

(* Example: Sterbenz subtraction *)
Definition Sterbenz_test32 a b := Sterbenz(a - b)%F32.
Definition Sterbenz_test64 a b := Sterbenz(a - b)%F64.

Definition _a : ident := 1%positive.
Definition _b : ident := 2%positive.

Definition Sterbenz_expr32 := ltac:(let e' :=
  HO_reify_float_expr constr:([_a; _b]) Sterbenz_test32 in exact e').
Definition Sterbenz_expr64:= ltac:(let e' :=
  HO_reify_float_expr constr:([_a; _b]) Sterbenz_test64 in exact e').

Definition vmap' {ty} (a b : ftype ty) :=
   [(_a, existT ftype _ a);(_b, existT ftype _ b)].
(*  this should be made to work more generally . . .
Definition vmap (ty: type) (a b : ftype ty) : valmap :=
 ltac:(make_valmap_of_list (vmap' a b)).
*)


Definition vmap (a b : ftype Tsingle) : valmap :=
 ltac:(make_valmap_of_list (vmap' a b)).

Definition bmap' (ty : type) : list varinfo :=
  [ Build_varinfo ty _a 1 2 ;  Build_varinfo ty _b 1  2 ].
Definition bmap (ty : type) : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (bmap' ty)) in exact z).

Lemma prove_roundoff_bound32:
  forall a b : ftype Tsingle,
  prove_roundoff_bound (bmap Tsingle) (vmap (*Tsingle*) a b) Sterbenz_expr32 0%R.
Proof.
intros.
prove_roundoff_bound.
-
(* the VCFloat tactic "prove_rndval" creates subgoals for each of
the automatically generated validity conditions. These subgoals
may or may not be satisfied by the user provided bounds in the
data structure bmap. The interval tactic is invoked in order to
try and solve each subgoal; this tactic might require, as in this
exmaple, computations done in higher-precision in order to solve
the subgoal. *)
prove_rndval.
+ (* Sterbenz goal 1 *) interval with (i_prec 128).
+ (* Sterbenz goal 2 *) interval with (i_prec 128).
-
prove_roundoff_bound2.
match goal with |- Rabs ?a <= _ => field_simplify a end.
interval.
Qed.

End WITHNANS.



