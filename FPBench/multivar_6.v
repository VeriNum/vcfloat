Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.
Open Scope R_scope.

Definition delta4_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta4_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta4_bmap_list) in exact z).

Definition delta4 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble ((((((((-x2) * x3)%F64 - (x1 * x4)%F64)%F64 + (x2 * x5)%F64)%F64 + (x3 * x6)%F64)%F64 - (x5 * x6)%F64)%F64 + (x1 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64)%F64).

Definition delta4_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta4 in exact e').

Derive delta4_b 
SuchThat (forall vmap, prove_roundoff_bound delta4_bmap vmap delta4_expr delta4_b)
As delta4_bound.
Proof.
idtac "Starting delta4".
subst delta4_b. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Qed.

Lemma check_delta4_bound: ltac:(CheckBound delta4_b 2.51e-13%F64).
Proof. reflexivity. Qed.

Definition delta_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta_bmap_list) in exact z).

Definition delta (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 + (((-x2) * x3)%F64 * x4)%F64)%F64 + (((-x1) * x3)%F64 * x5)%F64)%F64 + (((-x1) * x2)%F64 * x6)%F64)%F64 + (((-x4) * x5)%F64 * x6)%F64)%F64).

Definition delta_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta in exact e').

Derive delta_b 
SuchThat (forall vmap, prove_roundoff_bound delta_bmap vmap delta_expr delta_b)
As delta_bound.
Proof.
idtac "Starting delta".
subst delta_b. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Qed.

Lemma check_delta_bound: ltac:(CheckBound delta_b 6.2e-12%F64).
Proof. reflexivity. Qed.

End WITHNANS.
