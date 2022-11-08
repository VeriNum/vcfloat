Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary List ListNotations.
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

Lemma delta4_bound:
	find_and_prove_roundoff_bound delta4_bmap delta4_expr.
Proof.
idtac "Starting delta4".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition delta4_bound_val := Eval simpl in delta4_bound.
Check ltac:(ShowBound delta4_bound_val).

Definition delta_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta_bmap_list) in exact z).

Definition delta (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 + (((-x2) * x3)%F64 * x4)%F64)%F64 + (((-x1) * x3)%F64 * x5)%F64)%F64 + (((-x1) * x2)%F64 * x6)%F64)%F64 + (((-x4) * x5)%F64 * x6)%F64)%F64).

Definition delta_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta in exact e').

Lemma delta_bound:
	find_and_prove_roundoff_bound delta_bmap delta_expr.
Proof.
idtac "Starting delta".
eexists. intro. prove_roundoff_bound.
-
time "prove_rndval" prove_rndval; time "interval" interval.
-
time "prove_roundoff_bound2" prove_roundoff_bound2;
time "prune_terms" (prune_terms (cutoff 30)).
time "do_interval" do_interval.
Defined.

Definition delta_bound_val := Eval simpl in delta_bound.
Check ltac:(ShowBound delta_bound_val).

End WITHNANS.
