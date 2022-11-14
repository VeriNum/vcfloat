(** TestPaper.v:  examples taken from the paper,
  "VCFloat2: Floating-point error analysis in Coq"
 Copyright (C) 2022 Andrew W. Appel and Ariel Kellison.
*)

Require Import vcfloat.VCFloat.
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
Derive acc 
 SuchThat  (forall vmap,  prove_roundoff_bound step_bmap vmap step' acc)
 As prove_roundoff_bound_x_alt.
Proof.
intros.
 prove_roundoff_bound.
-
 prove_rndval; interval.
-
subst acc.
prove_roundoff_bound2.
prune_terms (cutoff 100).
do_interval.
Qed.


(* Let's check that the first component of that thing is actually
   simple expression containing a few constants,
   i.e. a concrete bound on the roundoff error of the step function. *)
Print acc.

(* We claimed that the roundoff error is less than 1/4000000; let's check! *)
Lemma bound_less_than_one_over_four_million:  acc <= 1 / 4000000.
Proof. compute; lra. Qed.

(* Let's make sure the second component really is a proof that
  this is a bound on the roundoff error of the step function *)
Check prove_roundoff_bound_x_alt.

End WITHNANS.

(* Below are tests of the "prune_terms" tactic and various steps
  of the algorithm *)

Lemma test1:
 forall 
 (x v e0 d e1 e2 d0 e3 : R)
 (BOUND : -2 <= v <= 2)
 (BOUND0 : -2 <= x <= 2)
 (E : Rabs e0 <= / 713623846352979940529142984724747568191373312)
 (E0 : Rabs d <= / 16777216)
 (E1 : Rabs e1 <= / 1427247692705959881058285969449495136382746624)
 (E2 : Rabs e2 <= / 713623846352979940529142984724747568191373312)
 (E3 : Rabs d0 <= / 16777216)
 (E4 : Rabs e3 <= / 1427247692705959881058285969449495136382746624),
Rabs
  (((x + (1 / 32 * v + e2)) * (1 + d) + e3 + (1 / 2048 * - x + e0)) *
   (1 + d0) + e1 - (x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * - x)) <=
   2.46e-7.
Proof.
intros.
prune_terms (cutoff 30).
(*match goal with |- Rabs ?a <= _ => field_simplify a end.*)
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end.
eapply Rle_trans; [ apply H99 | clear  ].
compute; lra.
Qed.

Import Tree.

Lemma test1_double_precision:
 forall 
 (x v e0 d e1 e2 d0 e3 : R)
 (BOUND : -2 <= v <= 2)
 (BOUND0 : -2 <= x <= 2)
 (E : Rabs e0 <= / bpow' 2 298)
 (E0 : Rabs d <= / bpow' 2 48)
 (E1 : Rabs e1 <= / bpow' 2 300)
 (E2 : Rabs e2 <= / bpow' 2 298)
 (E3 : Rabs d0 <= / bpow' 2 48)
 (E4 : Rabs e3 <= / bpow' 2 298),
Rabs
  (((x + (1 / 32 * v + e2)) * (1 + d) + e3 + (1 / 2048 * - x + e0)) *
   (1 + d0) + e1 - (x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * - x)) <=
   2.46e-7.
Proof.
intros.
prune_terms (cutoff 60).
(*match goal with |- Rabs ?a <= _ => field_simplify a end.*)
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end.
eapply Rle_trans; [ apply H99 | clear  ].
compute; lra.
Qed.

Lemma test3: forall
 (x v d1 d2 e0 e1 e3 : R)
 (BOUND : -2 <= v <= 2)
 (BOUND0 : 2 <= x <= 4)
 (E : Rabs d1 <= / 16777216) 
 (E0 : Rabs d2 <= / 16777216)
 (E1 : Rabs e0 <= / 713623846352979940529142984724747568191373312)
 (E2 : Rabs e1 <= / 1427247692705959881058285969449495136382746624)
 (E3 : Rabs e3 <= / 713623846352979940529142984724747568191373312),
Rabs
  (((x + (1 / 32 * v + e0)) * (1 + d2) + (1 / 2048 * (3 - x) + e3)) *
   (1 + d1) + e1 -
   (x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * (3 - x))) <=
/ 2000000.
Proof.
intros.
prune_terms (cutoff 30).
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end.
eapply Rle_trans; [ apply H99 | clear  ].
simpl; compute; lra.
Qed.


Lemma test3_alt: forall
 (x v d1 d2 e0 e1 e3 : R)
 (BOUND : -2 <= v <= 2)
 (BOUND0 : 2 <= x <= 4)
 (E : Rabs e0 <= / 713623846352979940529142984724747568191373312)
 (E0 : Rabs d1 <= / 16777216) 
 (E1 : Rabs e1 <= / 713623846352979940529142984724747568191373312)
 (E2 : Rabs d2 <= / 16777216) 
 (E3 : Rabs e3 <= / 1427247692705959881058285969449495136382746624),
Rabs
  ((x + (1 / 32 * ((v + (1 / 64 * (3 - x) + e1)) * (1 + d1) + e3) + e0)) *
   (1 + d2) - (x + 1 / 32 * (v + 1 / 32 / 2 * (3 - x)))) <= 
  1/4000000.
Proof.
intros.
prune_terms (cutoff 30).
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end.
eapply Rle_trans; [ apply H99 | clear  ].
compute; simpl; lra.
Qed.

Lemma test2:
 forall 
 (d d0 d1 e0 d2 e1 e2 e3 e4 e5 d3 e6 e7 e8 e9 e10 e11 e12 e13 d4 e14
e15 e16 e17 e18 d5 d6 d7 d8 e19 e20 d9 d10 d11 d12 e21 d13 e22 e23 e24
x v : R)
 (BOUND : (-2) <= v <= 2)
 (BOUND0 : (-2) <= x <= 2)
 (E : (Rabs d) <= (/ 16777216))
 ( E0 : (Rabs d0) <= (/ 16777216))
 ( E1 : (Rabs d1) <= (/ 16777216)) 
( E2 : (Rabs e0) <= (/ 1427247692705959881058285969449495136382746624))
 (E3 : (Rabs d2) <= (/ 16777216)) 
 (E4 : (Rabs e1) <= (/ 713623846352979940529142984724747568191373312))
 ( E5 : (Rabs e2) <= (/ 1427247692705959881058285969449495136382746624))
 ( E6 : (Rabs e3) <= (/ 1427247692705959881058285969449495136382746624))
 ( E7 : (Rabs e4) <= (/ 1427247692705959881058285969449495136382746624))
 ( E8 : (Rabs e5) <= (/ 1427247692705959881058285969449495136382746624)) 
( E9 : (Rabs d3) <= (/ 16777216))
 ( E10 : (Rabs e6) <= (/ 713623846352979940529142984724747568191373312)) 
( E11 : (Rabs e7) <= (/ 713623846352979940529142984724747568191373312))
 ( E12 : (Rabs e8) <= (/ 713623846352979940529142984724747568191373312))
 ( E13 : (Rabs e9) <= (/ 713623846352979940529142984724747568191373312)) 
 ( E14 : (Rabs e10) <= (/ 1427247692705959881058285969449495136382746624))
 ( E15 : (Rabs e11) <= (/ 1427247692705959881058285969449495136382746624)) 
( E16 : (Rabs e12) <= (/ 1427247692705959881058285969449495136382746624))
 ( E17 : (Rabs e13) <= (/ 1427247692705959881058285969449495136382746624))
 ( E18 : (Rabs d4) <= (/ 16777216))
 ( E19 : (Rabs e14) <= (/ 713623846352979940529142984724747568191373312))
 ( E20 : (Rabs e15) <= (/ 1427247692705959881058285969449495136382746624))
 (E21 : (Rabs e16) <= (/ 1427247692705959881058285969449495136382746624) )
( E22 : (Rabs e17) <= (/ 1427247692705959881058285969449495136382746624))
 ( E23 : (Rabs e18) <= (/ 1427247692705959881058285969449495136382746624)) 
( E24 : (Rabs d5) <= (/ 16777216))
(E25 : (Rabs d6) <= (/ 16777216))
(E26 : (Rabs d7) <= (/ 16777216))
(E27 : (Rabs d8) <= (/ 16777216))
(E28 : (Rabs e19) <= (/ 713623846352979940529142984724747568191373312))
(E29 : (Rabs e20) <= (/ 1427247692705959881058285969449495136382746624))
(E30 : (Rabs d9) <= (/ 16777216))
(E31 : (Rabs d10) <= (/ 16777216))
(E32 : (Rabs d11) <= (/ 16777216))
(E33 : (Rabs d12) <= (/ 16777216))
(E34 : (Rabs e21) <= (/ 713623846352979940529142984724747568191373312))
(E35 : (Rabs d13) <= (/ 16777216))
(E36 : (Rabs e22) <= (/ 713623846352979940529142984724747568191373312))
(E37 : (Rabs e23) <= (/ 713623846352979940529142984724747568191373312))
(E38 : (Rabs e24) <= (/ 1427247692705959881058285969449495136382746624)),
  Rabs
    (((((x + (1 / 32 * v + e14)) * (1 + d3) + e20 + (1 / 2048 * - x + e1)) *
       (1 + d5) + e10) *
      (((x + (1 / 32 * v + e21)) * (1 + d1) + e17 + (1 / 2048 * - x + e8)) *
       (1 + d11) + e4) * (1 + d8) + e13 +
      (((v +
         (1 / 64 *
          ((- x +
            -
            (((x + (1 / 32 * v + e23)) * (1 + d0) + e16 +
              (1 / 2048 * - x + e7)) * (1 + d10) + e3)) * 
           (1 + d7) + e12) + e22)) * (1 + d2) + e18) *
       ((v +
         (1 / 64 *
          ((- x +
            -
            (((x + (1 / 32 * v + e9)) * (1 + d12) + e5 +
              (1 / 2048 * - x + e19)) * (1 + d4) + e24)) * 
           (1 + d) + e15) + e6)) * (1 + d9) + e2) * 
       (1 + d6) + e11)) * (1 + d13) + e0 -
     ((x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * - x) *
      (x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * - x) +
      (v +
       1 / 2 * (1 / 32) *
       (- x + - (x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * - x))) *
      (v +
       1 / 2 * (1 / 32) *
       (- x + - (x + 1 / 32 * v + 1 / 2 * (1 / 32 * (1 / 32)) * - x))))) <=
  3e-6.
Proof.
intros.
destruct true.
-
Time prune_terms (cutoff 30).  
(* before collapse_terms was added to the algorithm, this
   took about 1.8-2.0 sec.
  Now it takes 1.55-6.0 sec. *)

(*Time match goal with |- Rabs ?a <= _ => field_simplify a end.*)
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end;
eapply Rle_trans; [ apply H99 | clear  ].
simpl; compute; lra.
-
simple_reify.
pose (nodes_and_terms e := (count_nodes e, count_terms e)).

pose (counts0 := nodes_and_terms __expr);
vm_compute in counts0;
let e1 := constr:(ring_simp false 100 __expr) in 
let e1 := eval vm_compute in e1 in 
pose (counts1 := nodes_and_terms e1);
vm_compute in counts1;
let e2 := constr:(fst (prune (map b_hyps __hyps) e1 (cutoff 30))) in
let e2 := eval vm_compute in e2 in 
pose (counts2 := nodes_and_terms e2);
vm_compute in counts2;
let e3 := constr:(cancel_terms e2) in 
let e3 := eval vm_compute in e3 in 
pose (counts3 := nodes_and_terms e3);
vm_compute in counts3;
let e4 := constr:(ring_simp true 100 e3) in 
let e4 := eval vm_compute in e4 in 
pose (counts4 := nodes_and_terms e4);
vm_compute in counts4;
pose (t3 := eval e3 __vars); 
pose (t4 := eval e4 __vars); 
cbv [eval nth nullary_real unary_real binary_real bpow' __vars] in t3, t4;
elimtype False; clear - t3 t4 counts0 counts1 counts2 counts3 counts4.
Open Scope Z.

(*
counts0 := (242, 4) : Z * Z
counts1 := (612284, 31759) : Z * Z
counts2 := (1456, 244) : Z * Z
counts3 := (289, 25) : Z * Z ,  before collapse_terms was added 
counts3 := (219, 24) : Z * Z   with collapse_terms
counts4 := (395, 46) : Z * Z
*)
Abort.




