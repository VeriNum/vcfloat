(** Test.v:  application demo of "ftype" usage-style of VCfloat.
 Copyright (C) 2021-2022 Andrew W. Appel and Ariel Kellison.
*)

Require Import vcfloat.VCFloat.
Require Import Interval.Tactic.
Import Binary.
Import Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.


Definition dub_to_F (x: ftype Tdouble) : option (Defs.float Zaux.radix2) :=
 if FPCore.is_finite x then Some (FT2F x) else None.


Definition dub_compare (x y : ftype Tdouble) : option comparison := compare' x y.

Lemma dub_finite_compare: forall x, if dub_to_F x then dub_compare x x = Some Eq else True.
Proof.
intros.
destruct x; simpl; auto.
unfold dub_compare, compare'.
simpl.
unfold Bcompare.
simpl.
unfold BinarySingleNaN.Bcompare.
simpl.
destruct s; rewrite Z.compare_refl, Pcompare_refl; auto.
Qed.

Lemma dub_compare_correct:
  forall (f1 f2 : ftype Tdouble) (g1 g2 : Defs.float Zaux.radix2),
  dub_to_F f1 = Some g1 ->
  dub_to_F f2 = Some g2 ->
  dub_compare f1 f2 = Some (Rcompare (Defs.F2R g1) (Defs.F2R g2)).
Proof.
intros.
unfold dub_to_F, dub_compare in *.
destruct (FPCore.is_finite f1) eqn:?H; inversion H; clear H; subst.
destruct (FPCore.is_finite f2) eqn:?H; inversion H0; clear H0; subst.
rewrite compare'_correct; auto.
f_equal.
rewrite <- !B2R_float_of_ftype.
simpl.
rewrite <- !F2R_B2F by auto.
rewrite !F2R_eq.
auto.
Qed.

Lemma dub_nonempty_finite: if dub_to_F (Zconst Tdouble 0) then True else False.
Proof.
intros.
reflexivity.
Qed.

Lemma dub_bounds: forall x : ftype Tdouble,
  - (bpow Zaux.radix2 1024 - bpow Zaux.radix2 (1024 - 53)) <=
  match dub_to_F x with
  | Some f => Defs.F2R f
  | None => R0
  end <= bpow Zaux.radix2 1024 - bpow Zaux.radix2 (1024 - 53).
Proof.
Admitted.


Definition dub : nonstdtype 53 1024 I I :=
  NONSTD _ _ _ _ (ftype Tdouble) (Zconst _ 0) dub_to_F dub_compare dub_finite_compare
  dub_compare_correct dub_nonempty_finite dub_bounds.

Definition Tdub : type := GTYPE _ _ _ _ (Some dub).

#[export] Instance coll : collection.
 exists [Tdub]. hnf; intros. destruct H; try contradiction. destruct H0; try contradiction.
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

Definition some_bounds : bounds Tdub :=
  ((Zconst Tdouble (-100), true), (Zconst Tdouble 100, false)).

Definition cosff := ltac:(floatfunc' [Tdub] Tdub (Kcons some_bounds Knil) 3%N Rtrigo_def.cos).
Definition cos := ltac:(apply_func cosff).
Definition sinff := ltac:(floatfunc' [Tdub] Tdub (Kcons some_bounds Knil) 5%N Rtrigo_def.sin).
Definition sin := ltac:(apply_func sinff).

Definition plusff := ltac:(floatfunc' [Tdub;Tdub] Tdub (Kcons some_bounds (Kcons some_bounds Knil)) 0%N Rplus).
Definition plus := ltac:(apply_func plusff).
Definition multff := ltac:(floatfunc' [Tdub;Tdub] Tdub (Kcons some_bounds (Kcons some_bounds Knil)) 0%N Rmult).
Definition mult := ltac:(apply_func multff).
(*

Definition F (x : ftype Tdub ) : ftype Tdub :=
  plus (mult (cos x) (cos x)) (mult (sin x) (sin x)).
*)

Definition F (x : ftype Tdub ) : ftype Tdub :=
  plus x x.

Instance incoll_dub: incollection Tdub.
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

Definition vmap_list (x : ftype Tdub) :=
   [(_x, existT ftype _ x)].


(** Step two, build that into "varmap" data structure, taking care to
  compute it into a lookup-tree ___here___, not later in each place
  where we look something up. *)
Definition vmap (x : ftype Tdub) : valmap :=
 ltac:(make_valmap_of_list (vmap_list x)).

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
  [ Build_varinfo Tdub _x (-2)  2 ].

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
 match goal with |- (Rabs ?a <= _)%R => field_simplify a end. (* improves the bound *)
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
match goal with |- (Rabs ?a <= _)%R => field_simplify a end.
match goal with |- (Rabs ?a <= _)%R => interval_intro (Rabs a) end.
subst x_acc; apply H.
Qed.

Print x_acc.
Check prove_roundoff_bound_x_alt.

End WITHNANS.



