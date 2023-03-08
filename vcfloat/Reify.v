(* Copyright (c) 2022 Andrew W. Appel *)

From vcfloat Require Export RAux.
From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra klist.
Require compcert.lib.Maps.  
Require Coq.MSets.MSetAVL.
Require vcfloat.Fprop_absolute.
Require Import vcfloat.Float_lemmas.
Set Bullet Behavior "Strict Subproofs".
Global Unset Asymmetric Patterns.


Require Import vcfloat.FPCore vcfloat.FPLang.
Require Import vcfloat.Float_notations.
Import Coq.Lists.List.

Definition ident := positive.

Definition placeholder32: ident -> ftype Tsingle. intro. apply 0%F32. Qed.

Definition placeholder ty: ident -> ftype ty. intro. apply (B754_zero _ _ false). Qed.

Definition func {ty} (f: floatfunc_package ty) := ff_func (ff_ff f).
Ltac apply_func ff := 
 let f := constr:(func ff) in
 match type of f with ?t =>
   let t' := eval hnf in t in
   let t' := eval cbv [function_type map ftype'] in t' in 
  let f' := constr:(f : t') in
  exact f'
  end.
 

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
     constr:(TYPE precp emax Logic.I Logic.I)
 end.

Ltac reify_float_expr E :=
 match E with
 | placeholder32 ?i => constr:(Var Tsingle i)
 | placeholder ?ty ?i => constr:(Var ty i)
 | Zconst ?t ?z => constr:(Const t (Zconst t z))
 | BPLUS ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 PLUS None) a' b')
 | Norm (BPLUS ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 PLUS (Some Normal)) a' b')
 | Denorm (BPLUS ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 PLUS (Some Denormal)) a' b')
 | BMINUS ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 MINUS None) a' b')
 | Norm (BMINUS ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 MINUS (Some Normal)) a' b')
 | Denorm (BMINUS ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 MINUS (Some Denormal)) a' b')
 | BMULT ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 MULT None) a' b')
 | Norm (BMULT ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 MULT (Some Normal)) a' b')
 | Denorm (BMULT ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 MULT (Some Denormal)) a' b')
 | BDIV ?a ?b => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 DIV None) a' b')
 | Norm (BDIV ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 DIV (Some Normal)) a' b')
 | Denorm (BDIV ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop (Rounded2 DIV (Some Denormal)) a' b')
 | BOPP ?a => let a' := reify_float_expr a in 
                                      constr:(Unop (Exact1 Opp) a')
 | BABS ?a => let a' := reify_float_expr a in 
                                      constr:(Unop (Exact1 Abs) a')
 | BSQRT ?a => let a' := reify_float_expr a in 
                                      constr:(Unop (Rounded1 SQRT) a')
 | @cast _ Tsingle Tdouble ?f => let f':= reify_float_expr f in 
                                      constr:(Cast Tdouble Tsingle None f')
 | @cast _ Tdouble Tsingle ?f => let f':= reify_float_expr f in 
                                      constr:(Cast Tsingle Tdouble None f')
 | @cast _ Tsingle Tsingle ?f => let f':= reify_float_expr f in 
                                      constr:(f')
 | @cast _ Tdouble Tdouble ?f => let f':= reify_float_expr f in 
                                      constr:(f')
 | b32_B754_zero _ => constr:(Const Tsingle E)
 | b64_B754_zero _ => constr:(Const Tdouble E)
 | b64_B754_finite _ _ _ _ => constr:(Const Tdouble E)
 | b32_B754_finite _ _ _ _ => constr:(Const Tsingle E)
 | b64_B754_finite _ _ _ _ => constr:(Const Tdouble E)
 | Sterbenz (BMINUS ?a ?b) => let a' := reify_float_expr a in let b' := reify_float_expr b in 
                                      constr:(Binop SterbenzMinus a' b')
 | @func ?ty ?ff ?a1 => let a1' := reify_float_expr a1 in 
                                            constr:(Func ty ff (Kcons a1' Knil))
 | @func ?ty ?ff ?a1 ?a2 => let a1' := reify_float_expr a1 in 
                                            let a2' := reify_float_expr a2 in 
                                            constr:(Func ty ff (Kcons a1' (Kcons a2' Knil)))
 | @func ?ty ?ff ?a1 ?a2 ?a3 => let a1' := reify_float_expr a1 in 
                                            let a2' := reify_float_expr a2 in 
                                            let a3' := reify_float_expr a3 in 
                                            constr:(Func ty ff (Kcons a1' (Kcons a2' (Kcons a3' Knil))))
 | _ => let E' := eval red in E in reify_float_expr E'
 | _ => fail 100 "could not reify bot" E
 end.

Ltac HO_reify_float_expr names E :=
         lazymatch names with
         | ?n :: ?names' =>
              lazymatch (type of E) with
              | ftype ?ty -> _ =>
                     let Ev := constr:(E (placeholder ty n)) in 
                     HO_reify_float_expr names' Ev
              | _ => fail 100 "could not reify" E
              end
         | nil => reify_float_expr E
end.

Ltac unfold_reflect :=
 match goal with |- context [fval ?A ?B] =>
   pattern (fval A B);
   match goal with |- ?M _ =>
   let X := fresh "X" in set (X := M);
   cbv beta iota delta [
    fval fop_of_binop fop_of_rounded_binop
    fop_of_unop fop_of_rounded_unop fop_of_exact_unop
   ];
   repeat change (cast ?a _ ?x) with x;
   subst X; cbv beta
  end
 end.
