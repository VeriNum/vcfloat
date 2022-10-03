(** TestPaper.v:  examples taken from the paper,
  "VCFloat2: Floating-point error analysis in Coq"
 Copyright (C) 2022 Andrew W. Appel and Ariel Kellison.
*)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate Prune.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Section WITHNANS.

(** NANS:  Each different computer architecture supports the same IEEE-754
  floating-point standard, but with slightly different Not-a-number (NAN) behavior.
  That behavior is encapsulated in a Nans typeclass.  You can instantiate that
  appropriate for your own architecture; but all the demos in this file are
  independent of the Nans details, so we can leave it abstract, like this: *)
Context {NANS: Nans}.

(** We will demonstrate VCfloat on a symplectic ODE (ordinary differential 
  equation) integration for a simple harmonic oscillator. *)

Definition h := (1/32)%F32.
Definition F(x: ftype Tsingle) : ftype Tsingle := Sterbenz(3.0-x)%F32.  
Definition step (x v: ftype Tsingle) := (Norm(x + h*(v+(h/2)*F(x))))%F32.

(** In deep-embedded (syntactic) expressons, variables are represented
  by "ident"ifiers, which are actually small positive numbers. *)
Definition _x : ident := 1%positive.  (* Variable name for position *)
Definition _v : ident := 2%positive.  (* Variable name for velocity *)

(** These two lines compute a deep-embedded "expr"ession from
  a shallow-embedded Coq expression.  *)
Definition step' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) step in exact e').

Print step'.  (* Demonstrates what step' looks like *)

(** When interpreting deep-embedded expressions, "Var"iables will appear
  which are labeled by identifiers such as "_x" and "_v".  We want a
  "varmap" for looking up the values of those variables.  We'll compute
  that varmap in two stages.  Step one, given values "x" and "v", 
  make an association list mapping _x to x, and _v to v,  each labeled
  by its floating-point type.  *)

Definition step_vmap_list (x v : ftype Tsingle) := 
   [(_x, existT ftype _ x);(_v, existT ftype _ v)].

(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition step_vmap (x v : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (step_vmap_list x v)) in exact z).

(**  Demonstration of reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)

Lemma reflect_reify : forall x v, 
             fval (env_ (step_vmap x v)) step' = step x v.
Proof. reflexivity. Qed.

(** To create the boundsmap, first we make an association list.  This one says
   that    2.0 <= x <= 4.0   and   -2.0 <= v <= 2.0  *)
Definition step_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _x 2 4 ;  Build_varinfo Tsingle _v (-2)  2 ].

(** Then we calculate an efficient lookup table, the "boundsmap". *)
Definition step_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list step_bmap_list) in exact z).

(** Now we prove that the leapfrogx expression (deep-embedded as  x' )
   has a roundoff error less than 1.0e-5 *)
Lemma prove_roundoff_bound_step:
  forall vmap,
     prove_roundoff_bound step_bmap vmap step'  (/ 4000000).
Proof.
intros.
prove_roundoff_bound.
-
 prove_rndval.
 all: interval.
- 
 prove_roundoff_bound2.
 prune_terms (cutoff 30).
 do_interval.
Qed.

(* The next part demonstrates that you don't have to guess the
  upper bound in advance, to use the tool. *)
Definition find_and_prove_roundoff_bound (bmap: boundsmap) (e: expr) :=
  {bound: R | forall vmap, prove_roundoff_bound bmap vmap e bound}.

(* This proof returns a pair, 
   {bound | proof that it really is a bound for step }
 where "bound" is a simple real-valued expression with only constants. *)
Lemma find_and_prove_roundoff_bound_step :
  find_and_prove_roundoff_bound step_bmap step'.
Proof.
eexists.
intro.
 prove_roundoff_bound.
-
 prove_rndval; interval.
-
prove_roundoff_bound2.
prune_terms (cutoff 100).
do_interval.
Defined.

(* Let's check that the first component of that thing is actually
   simple expression containing a few constants,
   i.e. a concrete bound on the roundoff error of the step function. *)
Eval hnf in proj1_sig find_and_prove_roundoff_bound_step.

(* We claimed that the roundoff error is less than 1/4000000; let's check! *)
Lemma bound_less_than_one_over_four_million:
 proj1_sig find_and_prove_roundoff_bound_step <= 1 / 4000000.
Proof. compute; lra. Qed.

(* Let's make sure the second component really is a proof that
  this is a bound on the roundoff error of the step function *)
Check proj2_sig find_and_prove_roundoff_bound_step.

End WITHNANS.



