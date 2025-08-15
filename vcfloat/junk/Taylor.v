(* THIS FILE IS JUST THE BEGINNING OF AN EXPERIMENTAL SKETCH!
  We explore whether multivariate first-order Taylor expansions,
  in the style of FPTaylor, might be useful.
 *)

Require Import Reals ZArith Lra Lia IntervalFlocq3.Tactic.
Import Raux.
From Flocq3 Require Import IEEE754.Binary Zaux.
Require Import Setoid.

Import Coq.Lists.List ListNotations.
Import Tree. (* must import this _after_ List *)
Import Interval Private Interval_helper I2 IT2.IH I2.T Xreal Eval.Reify.

Import Basic.
Import Bool.
From vcfloat Require Import Prune.

Lemma doppler1_test:
  forall
  (v_v : R)
  (BOUND : 20 <= v_v <= 2e4)
  (v_u : R)
  (BOUND0 : -100 <= v_u <= 100)
  (v_t : R)
  (BOUND1 : -30 <= v_t <= 50)
  (e0 : R)
  (E : Rabs e0 <= powerRZ 2 (-1075))
  (e1 : R)
  (E0 : Rabs e1 <= powerRZ 2 (-1075))
  (e3 : R)
  (E2 : Rabs e3 <= powerRZ 2 (-1075))
  (e4 : R)
  (E3 : Rabs e4 <= powerRZ 2 (-1075))
  (e8 : R)
  (E7 : Rabs e8 <= powerRZ 2 (-1075))
  (e9 : R)
  (E8 : Rabs e9 <= powerRZ 2 (-1075))
  (d : R)
  (E10 : Rabs d <= powerRZ 2 (-53))
  (d0 : R)
  (E11 : Rabs d0 <= powerRZ 2 (-53))
  (d1 : R)
  (E12 : Rabs d1 <= powerRZ 2 (-53))
  (d2 : R)
  (E13 : Rabs d2 <= powerRZ 2 (-53))
  (d3 : R)
  (E14 : Rabs d3 <= powerRZ 2 (-53))
  (d6 : R)
  (E17 : Rabs d6 <= powerRZ 2 (-53))
  (a := 2915025227559731 / 8796093022208 : R)
  (b := 5404319552844595 / 9007199254740992 : R),
 {bound: R |
Rabs
  ((- ((a + (b * v_t * (1 + d) + e1)) * (1 + d1) + e0) * v_v *
    (1 + d2) + e8) /
   ((((a + (b * v_t * (1 + d) + e1)) * (1 + d1) + e0 + v_u) *
     (1 + d0) + e4) *
    (((a + (b * v_t * (1 + d) + e1)) * (1 + d1) + e0 + v_u) *
     (1 + d0) + e4) * (1 + d6) + e3) * (1 + d3) + e9 -
   - (a + b * v_t) * v_v *
   / ((a + b * v_t + v_u) * (a + b * v_t + v_u)))
   <= bound}.
Proof. intros.
evar (bound: R).
exists bound. (*eexists.*)
unfold a, b.

simple_reify.

Definition bind2 (f: expr -> expr -> expr) (x1: option expr) (x2: option expr) : option expr :=
 match x1, x2 with
 | Some y1, Some y2 => Some (f y1 y2)
 | _, _ => None
 end.

Definition Mul' (e1 e2: expr) :=
 match e1, e2 with
 | Econst (Int 0) , _ => zeroexpr
 | _, Econst (Int 0) => zeroexpr
 | Econst (Int 1) , _ => e2
 | _, Econst (Int 1) => e1
 | _, _ => Ebinary Mul e1 e2
 end.


Definition Div' (e1 e2: expr) :=
 match e1, e2 with
 | Econst (Int 0) , _ => zeroexpr
 | _, Econst (Int 1) => e1
 | _, _ => Ebinary Div e1 e2
 end.

Definition Neg' (e1: expr) :=
 match e1 with Econst (Int 0) => zeroexpr | _ => e1 end.

Definition Sqr' (e1: expr) :=
 match e1 with
 | Econst (Int 0) => zeroexpr
 | Econst (Int 1) => oneexpr
 | _ => e1
 end.


Print Add0.

Definition partial_deriv (x: nat) : expr -> option expr :=
 fix aux (e: expr) : option expr :=
 match e with
 | Evar y => Some (if Nat.eqb x y then oneexpr else zeroexpr)
 | Econst _ => Some zeroexpr
 | Eunary Neg e1 => option_map Neg' (aux e1)
 | Eunary Inv e1 => option_map (fun d => Neg' (Div' d (Sqr' e1))) (aux e1)
 | Eunary Sqr e => option_map (Mul' (Econst (Int 2))) (aux e)
 | Ebinary Add e1 e2 => bind2 Add0 (aux e1) (aux e2)
 | Ebinary Sub e1 e2 => bind2 Sub0 (aux e1) (aux e2)
 | Ebinary Mul e1 e2 => bind2 (fun d1 d2 => Add0 (Mul' e1 d2) (Mul' e2 d1)) (aux e1) (aux e2)
 | Ebinary Div e1 e2 => bind2 (fun d1 d2 => Div' (Sub0 (Mul' e2 d1) (Mul' e1 d2)) (Sqr' e2))
            (aux e1) (aux e2)
 | e => None
 end.

Fixpoint option_list {A} (al: list (option A)) : option (list A) :=
 match al with
 | nil => Some nil
 | Some x :: r => option_map (cons x) (option_list r)
 | None :: _ => None
 end.

Definition gradient (vars: list R) e  :=
 option_list (map (fun x => partial_deriv x e) (seq.iota 0 (length vars))).

assert (
 match partial_deriv 3%nat __expr with
  | Some d => eval d __vars = 0%R
 | _ => False
 end).
cbv -[IZR].
repeat change (?A * / ?B) with (A/B).
fold a. fold b.
clear __expr.






pose (vars := seq.iota 0 (length __vars)).

Search (list (option _) -> option (list _)).
assert (partial_deriv 3%nat __expr = None).
cbv.

cbv [partial_deriv __expr Nat.eqb ].




Check option_map.





