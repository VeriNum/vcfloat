(** Test.v:  application demo of "ftype" usage-style of VCfloat.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.


Definition dubdub : nonstdtype 106 1024 I I. Admitted.
Definition Tdubdub : type := GTYPE _ _ _ _ (Some dubdub).

Instance coll : collection.
 exists [Tdubdub]. hnf; intros. destruct H; try contradiction. destruct H0; try contradiction.
 subst; auto.
Defined.

Section WITHNANS.
Context {NANS: Nans}.

Fixpoint always_true (args: list type) : function_type (map RR args) Prop :=
 match args with
 | nil => True
 | _ :: args' => fun _ => always_true args'
 end.

Parameter c_function: forall (args: list type) (res: type) (bnds: klist bounds args) (rel: N) (f: function_type (map RR args) R),
   {ff: function_type (map ftype' args) (ftype res) 
   | acc_prop args res rel 1 bnds f ff /\ floatfunc_congr ff}.

Ltac floatfunc' args res bnds rel f :=
 let abs := constr:(1%N) in
 let cf := constr:(c_function args res bnds rel f) in
 let ff1 := constr:(Build_floatfunc args res _ f (proj1_sig cf) rel abs (proj1 (proj2_sig cf)) (proj2 (proj2_sig cf))) in
 exact (Build_floatfunc_package _ _  _ _ ff1).

Axiom some_lo: ftype Tdubdub.
Axiom some_hi: ftype Tdubdub.
Axiom some_lo': Defs.float Zaux.radix2.
Axiom some_hi': Defs.float Zaux.radix2.
Axiom nonstd_to_F_lo: nonstd_to_F some_lo = Some some_lo'.
Axiom nonstd_to_F_hi: nonstd_to_F some_hi = Some some_hi'.


Definition some_bounds : bounds Tdubdub :=
  ((some_lo, true), (some_hi, false)).

Definition cosff := ltac:(floatfunc' [Tdubdub] Tdubdub (Kcons some_bounds Knil) 3%N Rtrigo_def.cos).
Definition cos := ltac:(apply_func cosff).
Definition sinff := ltac:(floatfunc' [Tdubdub] Tdubdub (Kcons some_bounds Knil) 5%N Rtrigo_def.sin).
Definition sin := ltac:(apply_func sinff).

Definition plusff := ltac:(floatfunc' [Tdubdub;Tdubdub] Tdubdub (Kcons some_bounds (Kcons some_bounds Knil)) 0%N Rplus).
Definition plus := ltac:(apply_func plusff).
Definition multff := ltac:(floatfunc' [Tdubdub;Tdubdub] Tdubdub (Kcons some_bounds (Kcons some_bounds Knil)) 0%N Rmult).
Definition mult := ltac:(apply_func multff).
(*

Definition F (x : ftype Tdubdub ) : ftype Tdubdub := 
  plus (mult (cos x) (cos x)) (mult (sin x) (sin x)).
*)

Definition F (x : ftype Tdubdub ) : ftype Tdubdub := 
  plus x x.

Instance incoll_dubdub: incollection Tdubdub.
hnf; auto.
Defined.


Definition _x : ident := 1%positive.
(*Arguments Var {coll} ty {IN} _.*)

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

Definition vmap_list (x : ftype Tdubdub) := 
   [(_x, existT ftype _ x)].

(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition vmap (x : ftype Tdubdub) : valmap :=
 ltac:(make_valmap_of_list (vmap_list x)).

(**  Demonstration of reification and reflection.   When you have a 
  deep-embedded "expr"ession, you can get back the shallow embedding
   by applying the "fval" function *)

Require Import vcfloat.FPLib.

Lemma env_x: forall x IN, env_ (vmap x) Tdubdub IN _x = x.
Proof.
intros.
unfold vmap, env_.
simpl.
unfold eq_rect, eq_ind_r, eq_ind.
simpl.
destruct IN; simpl; try contradiction.
destruct (compute_valmap_valid _ _); simpl; try contradiction.
simpl in e0.
proof_irr.
fold Tdubdub.
assert (e = eq_refl _).
apply proof_irr.
subst.
auto.
Qed.

Lemma reflect_reify_x : forall x, 
             fval (env_ (vmap x)) F' = F x.
Proof.
intros.
cbv [F plus mult cos sin plusff multff cosff sinff func].
simpl.
rewrite !env_x.
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
  [ Build_varinfo Tdubdub _x (-2)  2 ].

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
interval.
simpl.
admit.
- 
prove_roundoff_bound2.
 match goal with |- (Rabs ?a <= _)%R => field_simplify a end. (* improves the bound *)
 interval.
all:fail.
Admitted.

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



