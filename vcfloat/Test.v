(** Test.v:  application demo of "ftype" usage-style of VCfloat.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations Automate.
Require Import Interval.Tactic.
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

Definition h := (1 / 32)%F32.   (* Time-step: 1/32 of a second *)

(* Force, as a function of position *)
Definition F (x : ftype Tsingle ) : ftype Tsingle := (-x)%F32.

(** Compute one time-step: given "ic" which is a pair of position and velocity,
  calculate the new position and velocity after time "h" has elapsed. *)
Definition leapfrog_step ( ic : ftype Tsingle * ftype Tsingle) : ftype Tsingle * ftype Tsingle :=
  let x  := fst ic in let v:= snd ic in 
  let x' := ((x + h * v) + ((1/2) * (h * h)) * F x)%F32 in
  let v' :=  (v +  (1/2 * h) * (F x + F x'))%F32 in 
  (x', v').

(** Calculate a new position, as a function of position x and velocity v *)
Definition leapfrog_stepx x v := fst (leapfrog_step (x,v)).

(** Calculate a new velocity, as a function of position x and velocity v *)
Definition leapfrog_stepv x v := snd (leapfrog_step (x,v)).

(** In deep-embedded (syntactic) expressons, variables are represented
  by "ident"ifiers, which are actually small positive numbers. *)
Definition _x : ident := 1%positive.  (* Variable name for position *)
Definition _v : ident := 2%positive.  (* Variable name for velocity *)

(** These two lines compute a deep-embedded "expr"ession from
  a shallow-embedded Coq expression.  *)
Definition x' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepx in exact e').
Definition v' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x; _v]) leapfrog_stepv in exact e').

Print x'.  (* Demonstrates what x' looks like *)

(** When interpreting deep-embedded expressions, "Var"iables will appear
  which are labeled by identifiers such as "_x" and "_v".  We want a
  "varmap" for looking up the values of those variables.  We'll compute
  that varmap in two stages.  Step one, given values "x" and "v", 
  make an association list mapping _x to x, and _v to v,  each labeled
  by its floating-point type.  *)

Definition leapfrog_vmap_list (x v : ftype Tsingle) := 
   [(_x, existT ftype _ x);(_v, existT ftype _ v)].

(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition leapfrog_vmap (x v : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list x v)) in exact z).

(**  Demonstration of reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)

Lemma reflect_reify_x : forall x v, 
             fval (env_ (leapfrog_vmap x v)) x' = leapfrog_stepx x v.
Proof.
intros.
destruct true.  (* artificial way to get two subgoals *)
-
   unfold x', leapfrog_stepx, leapfrog_step, F,  fst, snd.  (* This line makes things go faster *)
  Time reflexivity.  (* 0.01 sec *)
-
   (* Demonstration that unfold_reflect doesn't make things any faster (or much slower). *)
   unfold x', leapfrog_stepx, leapfrog_step, F,  fst, snd.  (* This line needed here  *)
   Time unfold_reflect. (* 0.02 secs *)
   Time reflexivity. (* 0.006 sec *)
   (* Therefore, use unfold_reflect if you wish to, for clarity, not for performance *)
Qed.

(**  Demonstration of reification and reflection, this time on  leapfrog_stepv *) 
Lemma reflect_reify_v : forall x v, fval (env_ (leapfrog_vmap x v)) v' = leapfrog_stepv x v.
Proof.
intros.
unfold v'.
(* without this line, things are much slower: *) unfold leapfrog_stepv, leapfrog_step, F,  fst, snd.
Time reflexivity.
Qed.

(** The main point of VCFloat is to prove bounds on the roundoff error of
  floating-point expressions.  Generally those bounds are provable only if
  the free variables of the expression (e.g., "x" and "v") are themselves 
  bounded in some way;  otherwise, the expression might overflow.
  A "boundsmap" is a mapping from identifier (such as "_x") to
  a "varinfo", which gives its (floating-point) and its lower and upper bound. *)

(** First we make an association list.  This one says that 
   -2.0 <= x <= 2.0   and   -2.0 <= v <= 2.0  *)
Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _x (-2)  2 ;  Build_varinfo Tsingle _v (-2)  2 ].

(** Then we calculate an efficient lookup table, the "boundsmap". *)
Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).

(** Now we prove that the leapfrogx expression (deep-embedded as  x' )
   has a roundoff error less than 1.0e-5 *)
Lemma prove_roundoff_bound_x:
  forall x v : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap x v) x' 
    (/ 4068166).
Proof.
intros.
prove_roundoff_bound.
 (* This divides into two proof goals.  
  Goal 1 is "prove_rndval", which generates a list of verification conditions 
        about subexpressions of x'; and if those can be proved, then
  x' evaluates equivalent to a perturbed expression.
  Goal 2 shows that the perturbed expression evaluates "close to"
  the exact real-number interpretation of expression x'.  *)
- 
  (* Solve Goal 1 by the prove_rndval tactic, which generates
    a list of interval subgoals, and hope to prove each one of those
     by the "interval" tactic *)
 abstract (prove_rndval; interval).
- 
    destruct false eqn:SILLY. {
     (** This proof goal is just to demonstrate unfold_prove_rndval *)
    intro.
    unfold_prove_rndval P.
    (** Now examine the proof goal above the line *)
    discriminate SILLY.
   } clear SILLY.

 prove_roundoff_bound2.

 match goal with |- Rabs ?a <= _ => field_simplify a end. (* improves the bound *)

 (* Right now, just "interval" would solve the goal.
  but to see how we guess the bound to use, try this instead: *)
  match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 eapply Rle_trans; [apply H | clear].
 eapply roundoff_bound_hack; [lia|lia|lia|compute; reflexivity|].
 lia.
Qed.

Lemma prove_roundoff_bound_v:
  forall x v : ftype Tsingle,
  prove_roundoff_bound leapfrog_bmap (leapfrog_vmap x v) v' 
    (/ 7662902).
Proof.
intros.
prove_roundoff_bound.
- abstract (prove_rndval; interval).
-
  prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
 interval.
Qed.

(** The following lemma demonstrates [val_bound],  that is, 
  compute the maximum absolute value of a floating-point expression *)
Lemma prove_val_bound_x:
  forall x v : ftype Tsingle,
  prove_val_bound leapfrog_bmap (leapfrog_vmap x v) x' 
    (4642138645987358 / 2251799813685248).
Proof.
intros.
prove_val_bound.
- 
 abstract (prove_rndval; interval).
- 
  prove_val_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
  match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
 eapply Rle_trans; [apply H | clear].
 lra.
Qed.

End WITHNANS.



