(* Copyright (c) 2022 Andrew W. Appel *)

From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
From compcert Require Import lib.IEEE754_extra (*lib.Floats*) .
Require compcert.lib.Maps.  
Require Coq.MSets.MSetAVL.
Require vcfloat.Fprop_absolute.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.


Require Import vcfloat.FPCore vcfloat.FPLang.
Require Import vcfloat.Float_notations.
Import List.

Definition ident := positive.

Definition SterbenzSub {NANS: Nans} := BMINUS. 

Definition placeholder32: ident -> ftype Tsingle. intro. apply 0%F32. Qed.

Definition extend_comp (c: comparison) (b: bool) (d: option comparison) :=
 match d with
 | None => false
 | Some c' =>
 match c, b, c' with
 | Gt, true, Gt => true
 | Gt, false, Lt => true
 | Gt, false, Eq => true
 | Eq, true, Eq => true
 | Eq, false, Gt => true
 | Eq, false, Lt => true
 | Lt, true, Lt => true
 | Lt, false, Gt => true
 | Lt, false, Eq => true
 | _, _, _ => false
 end
 end.

Definition BCMP (ty: type) (c: comparison) (b: bool) (x y: ftype ty) :=
  extend_comp c b (Binary.Bcompare (fprec ty) (femax ty) x y).

Notation "x + y" := (BPLUS Tsingle x y) (at level 50, left associativity) : float32_scope.
Notation "x - y"  := (BMINUS Tsingle x y) (at level 50, left associativity) : float32_scope.
Notation "x * y"  := (BMULT Tsingle x y) (at level 40, left associativity) : float32_scope.
Notation "x / y"  := (BDIV Tsingle x y) (at level 40, left associativity) : float32_scope.
Notation "- x" := (BOPP Tsingle x) (at level 35, right associativity) : float32_scope.
Notation "x <= y" := (BCMP Tsingle Gt false x y) (at level 70, no associativity) : float32_scope. 
Notation "x < y" := (BCMP Tsingle Gt true y x) (at level 70, no associativity) : float32_scope. 
Notation "x >= y" := (BCMP Tsingle Lt false x y) (at level 70, no associativity) : float32_scope. 
Notation "x > y" := (BCMP Tsingle Gt true x y) (at level 70, no associativity) : float32_scope. 
Notation "x <= y <= z" := (x <= y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y < z" := (x < y /\ y < z)%F32 (at level 70, y at next level) : float32_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F32 (at level 70, y at next level) : float32_scope.

Notation "x + y" := (BPLUS Tdouble x y) (at level 50, left associativity) : float64_scope.
Notation "x - y"  := (BMINUS Tdouble x y) (at level 50, left associativity) : float64_scope.
Notation "x * y"  := (BMULT Tdouble x y) (at level 40, left associativity) : float64_scope.
Notation "x / y"  := (BDIV Tdouble x y) (at level 40, left associativity) : float64_scope.
Notation "- x" := (BOPP Tdouble x) (at level 35, right associativity) : float64_scope.
Notation "x <= y" := (BCMP Tdouble Gt false x y) (at level 70, no associativity) : float64_scope. 
Notation "x < y" := (BCMP Tdouble Gt true y x) (at level 70, no associativity) : float64_scope. 
Notation "x >= y" := (BCMP Tdouble Lt false x y) (at level 70, no associativity) : float64_scope. 
Notation "x > y" := (BCMP Tdouble Gt true x y) (at level 70, no associativity) : float64_scope. 
Notation "x <= y <= z" := (x <= y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x <= y < z" := (x <= y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y < z" := (x < y /\ y < z)%F64 (at level 70, y at next level) : float64_scope.
Notation "x < y <= z" := (x < y /\ y <= z)%F64 (at level 70, y at next level) : float64_scope.

Ltac ground_pos p := 
 match p with
 | Z.pos ?p' => ground_pos p'
 | xH => constr:(tt) 
 | xI ?p' => ground_pos p' 
 | xO ?p' => ground_pos p' 
 end.

Ltac find_type prec emax :=
 match prec with
 | 24%Z => match emax with 128%Z => constr:(Tsingle) end
 | 53%Z => match emax with 1024%Z => constr:(Tdouble) end
 | Z.pos ?precp => 
     let g := ground_pos precp in let g := ground_pos emax in 
     constr:(TYPE precp emax (ZLT_intro prec emax (eq_refl _)) (BOOL_intro _ (eq_refl _)))
 end.

Definition Norm {T} (x: T) := x.
Definition Denorm {T} (x: T) := x.

Ltac reify_float_expr E :=
 match E with
 | placeholder32 ?i => constr:(@Var ident Tsingle i)
 | cast ?tto _ ?f => constr:(@Unop ident (CastTo tto None) f)
 | Zconst ?t ?z => constr:(@Const ident t (Zconst t z))
 | BPLUS _ ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 PLUS None) a' b')
 | Norm (BPLUS _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 PLUS (Some Normal)) a' b')
 | Denorm (BPLUS _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 PLUS (Some Denormal)) a' b')
 | BMINUS _ ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 MINUS None) a' b')
 | Norm (BMINUS _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 MINUS (Some Normal)) a' b')
 | Denorm (BMINUS _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 MINUS (Some Denormal)) a' b')
 | BMULT _ ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 MULT None) a' b')
 | Norm (BMULT _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 MULT (Some Normal)) a' b')
 | Denorm (BMULT _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 MULT (Some Denormal)) a' b')
 | BDIV _ ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 DIV None) a' b')
 | Norm (BDIV _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 DIV (Some Normal)) a' b')
 | Denorm (BDIV _ ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident (Rounded2 DIV (Some Denormal)) a' b')
 | BOPP _ ?a => let a' := reify_float_expr a in 
                                      constr:(@Unop ident (Exact1 Opp) a')
 | BABS _ ?a => let a' := reify_float_expr a in 
                                      constr:(@Unop ident (Exact1 Abs) a')
 | cast Tsingle Tdouble ?f => constr:(@Unop ident (CastTo Tdouble None) f)
 | cast Tdouble Tsingle ?f => constr:(@Unop ident (CastTo Tsingle None) f)
 | b32_B754_zero _ => constr:(@Const ident Tsingle E)
 | b64_B754_zero _ => constr:(@Const ident Tdouble E)
 | b64_B754_finite _ _ _ _ => constr:(@Const ident Tdouble E)
 | b32_B754_finite _ _ _ _ => constr:(@Const ident Tsingle E)
 | b64_B754_finite _ _ _ _ => constr:(@Const ident Tdouble E)
 | SterbenzSub _ ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(@Binop ident SterbenzMinus a' b')
                                  
 | _ => let E' := eval red in E in reify_float_expr E'
 | _ => fail 100 "could not reify" E
 end.

Ltac HO_reify_float_expr names E :=
 lazymatch names with
 | ?n :: ?names' =>
             let Ev := constr:(E (placeholder32 n)) in 
             HO_reify_float_expr names' Ev
 | nil =>reify_float_expr E
 end.

Ltac unfold_corresponding e :=
  (* This tactic is given a term (E1=E2), where E1 is an expression
     with internal nodes Bplus, Bminus, etc. and arbitrary leaves;
    and E2 is an expression which, if carefully unfolded in the right places,
    would have just the same tree structure.  And it carefully unfolds
    just in the right places, and returns (E1=E2') where E2' is the unfolding of E2.

    We want this tactic because, if we do not carefully unfold E2 before
   calling reflexivity, then reflexivity takes forever and then Qed takes
   two-to-the-forever.   In particular, some of the operators we may need
   to unfold are Float32.add, Float32.sub, et cetera. 

 TODO:  Maybe we need to fix this tactic to use BPLUS, BMINUS, etc. instead of Bplus, Bminus

*)
lazymatch e with eq ?E1 ?E2 =>
lazymatch E1 with
 | Bplus ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bplus _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bplus a1 b1 c1 d1 e1 f1 l2' r2')
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bminus ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bminus _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bminus a1 b1 c1 d1 e1 f1 l2' r2') 
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bmult ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bmult _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bmult a1 b1 c1 d1 e1 f1 l2' r2')
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bdiv ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?l1 ?r1 =>
    lazymatch E2 with
    | Bdiv _ _ _ _ _ _ ?l2 ?r2 => 
          let l2' := unfold_corresponding constr:(eq l1 l2) in
          let r2' := unfold_corresponding constr:(eq r1 r2) in
          constr:(Bdiv a1 b1 c1 d1 e1 f1 l2' r2') 
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | Bopp ?a1 ?b1 ?c1 ?x1 =>
    lazymatch E2 with
    | Bopp _ _ _ ?x2 => 
          let x2' := unfold_corresponding constr:(eq x1 x2) in
          constr:(Bopp a1 b1 c1 x2') 
   | _ => 
          let E2' := eval red  in E2 in unfold_corresponding constr:(eq E1 E2')
    end
 | _ => constr:(E2)
end end.


Ltac unfold_float_ops_for_equality :=
  (* see comment at Ltac unfold_corresponding. *)
  lazymatch goal with |- ?a = ?b => 
        let b' := unfold_corresponding constr:(a=b) in change (a=b')
  end.

Ltac unfold_reflect :=
 match goal with |- context [fval ?A ?B] =>
   pattern (fval A B);
   match goal with |- ?M _ =>
   let X := fresh "X" in set (X := M);
   cbv beta iota delta [
    fval fop_of_binop fop_of_rounded_binop type_of_expr cast_lub_l cast_lub_r
    fop_of_unop fop_of_rounded_unop fop_of_exact_unop
   ];
   change (type_lub _ _) with Tsingle;
   change (type_lub _ _) with Tdouble;
   change (type_lub ?x ?y) with x;
   change (type_lub ?x ?y) with y;
   repeat change (cast ?a _ ?x) with x;
   subst X; cbv beta
  end
 end.

