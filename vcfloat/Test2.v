(** Test.v:  application demo of "ftype" usage-style of VCfloat.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.

(* Example: Sterbenz subtraction *)
Definition Sterbenz_test32 a b := Sterbenz(a - b)%F32.
Definition Sterbenz_test64 a b := Sterbenz(a - b)%F64.

Definition _a : ident := 1%positive.  (* Variable name for position *)
Definition _b : ident := 2%positive.  (* Variable name for velocity *)

Definition Sterbenz_expr32 := ltac:(let e' := 
  HO_reify_float_expr constr:([_a; _b]) Sterbenz_test32 in exact e').
Definition Sterbenz_expr64:= ltac:(let e' := 
  HO_reify_float_expr constr:([_a; _b]) Sterbenz_test64 in exact e').

Definition vmap' {ty} (a b : ftype ty) := 
   [(_a, existT ftype _ a);(_b, existT ftype _ b)].
Definition vmap (ty: type) (a b : ftype ty) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap' a b)) in exact z).


Definition bmap' (ty : type) : list varinfo := 
  [ Build_varinfo ty _a 1 2 ;  Build_varinfo ty _b 1  2 ].
Definition bmap (ty : type) : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list (bmap' ty)) in exact z).

Lemma prove_roundoff_bound32:
  forall a b : ftype Tsingle,
  prove_roundoff_bound (bmap Tsingle) (vmap Tsingle a b) Sterbenz_expr32 0%R.
Proof.
intros.
prove_roundoff_bound.
- 
prove_rndval; interval with (i_prec 128).
- 
prove_roundoff_bound2.
match goal with |- Rabs ?a <= _ => field_simplify a end. 
interval.
Qed.

End WITHNANS.



