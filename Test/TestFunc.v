(** Test.v:  application demo of "ftype" usage-style of VCfloat.
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

Fixpoint always_true (args: list type) : function_type (map RR args) Prop :=
 match args with
 | nil => True
 | _ :: args' => fun _ => always_true args'
 end.

Definition default_rel (t: type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Parameter c_function: forall (args: list type) (res: type) (bnds: klist bounds args) (rel: N) (f: function_type (map RR args) R),
   {ff: function_type (map ftype' args) (ftype res) 
   | acc_prop args res rel 1 bnds f ff}.

Ltac floatfunc' args res bnds rel f :=
 let abs := constr:(1%N) in
 let cf := constr:(c_function args res bnds rel f) in
 let ff1 := constr:(Build_floatfunc args res _ f (proj1_sig cf) rel abs (proj2_sig cf)) in
 exact (Build_floatfunc_package _ _  _ _ ff1).

Definition vacuous_bnds ty : bounds ty := ((B754_infinity (fprec ty) (femax ty) true, false), 
                              (B754_infinity (fprec ty) (femax ty) false, false)).

Definition silly_bnds : bounds Tdouble :=
  ((-6, true), (99, false))%F64.

Definition cosff := ltac:(floatfunc' [Tdouble] Tdouble (Kcons (vacuous_bnds Tdouble) Knil) 3%N Rtrigo_def.cos).
Definition cos := ltac:(apply_func cosff).
Definition sinff := ltac:(floatfunc' [Tdouble] Tdouble (Kcons silly_bnds Knil) 5%N Rtrigo_def.sin).
Definition sin := ltac:(apply_func sinff).

Lemma test_reify1: False.
Proof.
pose (e := (1 +  cos 2)%F64).
let u := reify_float_expr e in 
 constr_eq u 
  (Binop (Rounded2 PLUS None) (Const Tdouble 1%F64)
       (Func Tdouble cosff
          (Kcons (Const Tdouble 2%F64) Knil))).
Abort.


(** We will demonstrate VCfloat on a symplectic ODE (ordinary differential 
  equation) integration for a simple harmonic oscillator. *)

(* Force, as a function of position *)
Definition F (x : ftype Tdouble ) : ftype Tdouble := 
  (cos x * cos x + sin x * sin x)%F64.


Definition _x : ident := 1%positive.  
(** These two lines compute a deep-embedded "expr"ession from
  a shallow-embedded Coq expression.  *)
Definition F' := ltac:(let e' := 
  HO_reify_float_expr constr:([_x]) F in exact e').

Print F'.  (* Demonstrates what x' looks like *)

(** When interpreting deep-embedded expressions, "Var"iables will appear
  which are labeled by identifiers such as "_x" and "_v".  We want a
  "varmap" for looking up the values of those variables.  We'll compute
  that varmap in two stages.  Step one, given values "x" and "v", 
  make an association list mapping _x to x, and _v to v,  each labeled
  by its floating-point type.  *)

Definition vmap_list (x : ftype Tdouble) := 
   [(_x, existT ftype _ x)].

(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition vmap (x : ftype Tdouble) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap_list x)) in exact z).

(**  Demonstration of reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)

Lemma reflect_reify_x : forall x, 
             fval (env_ (vmap x)) F' = F x.
Proof.
intros.
reflexivity.
Qed.

(** The main point of VCFloat is to prove bounds on the roundoff error of
  floating-point expressions.  Generally those bounds are provable only if
  the free variables of the expression (e.g., "x" and "v") are themselves 
  bounded in some way;  otherwise, the expression might overflow.
  A "boundsmap" is a mapping from identifier (such as "_x") to
  a "varinfo", which gives its (floating-point) and its lower and upper bound. *)

(** First we make an association list.  This one says that 
   -2.0 <= x <= 2.0   and   -2.0 <= v <= 2.0  *)
Definition bmap_list : list varinfo := 
  [ Build_varinfo Tdouble _x (-2)  2 ].

(** Then we calculate an efficient lookup table, the "boundsmap". *)
Definition bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list bmap_list) in exact z).

(** Now we prove that the leapfrogx expression (deep-embedded as  x' )
   has a roundoff error less than 1.0e-5 *)
Lemma prove_roundoff_bound_x:
  forall vmap,
  prove_roundoff_bound bmap vmap F'  2.3e-15.
Proof.
intros.
prove_roundoff_bound.
-
prove_rndval.
all: interval.
- 
prove_roundoff_bound2.
 match goal with |- Rabs ?a <= _ => field_simplify a end. (* improves the bound *)
 interval.
Qed.

Derive x_acc 
 SuchThat  (forall vmap,  prove_roundoff_bound bmap vmap F' x_acc)
 As prove_roundoff_bound_x_alt.
Proof.
intros.
 prove_roundoff_bound.
-
 prove_rndval; interval.
-
prove_roundoff_bound2.
match goal with |- Rabs ?a <= _ => field_simplify a end.
match goal with |- Rabs ?a <= _ => interval_intro (Rabs a) end.
subst x_acc; apply H.
Qed.

Print x_acc.
Check prove_roundoff_bound_x_alt.

End WITHNANS.



