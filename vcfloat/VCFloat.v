From vcfloat Require Export klist FPLang FPLangOpt RAux Rounding Reify Float_notations Automate Prune.
Require Derive.
Set Bullet Behavior "Strict Subproofs".

(* The following RtoFloat tactics are a very crude way to convert a n
  expression of type R that uses only IZR, Rplus, Rmult, Rdiv, Rinv,
  to a primitive floating-point constant.  It's crude in part because
  it always uses rounding-UP, which is not really appropriate, and it'
 does not use interval arithmetic.   It could perhaps be improved to actually
 compute in interval arithmetic, etc.

  Usage:
  RtoFloat' x    returns a float-valued expression corresponding
                                  to the real-valued expression
  RtoFloat x    returns a float-valued constant from the real-valued expr
  ShowBound  prints it out with its name.
*)

Ltac RtoFloat' x :=
lazymatch x with
| IZR ?z => constr:(Tactic_float.Float.fromZ_UP 53%Z z)
| Rplus ?a ?b => let a' := RtoFloat' a in let b' := RtoFloat' b in constr:(PrimFloat.add a' b')
| Rmult ?a ?b => let a' := RtoFloat' a in let b' := RtoFloat' b in constr:(PrimFloat.mul a' b')
| Rdiv ?a ?b => let a' := RtoFloat' a in let b' := RtoFloat' b in constr:(PrimFloat.div a' b')
| Rinv ?a => let a' := RtoFloat' a in constr:(PrimFloat.div PrimFloat.one a')
| _ => let y := eval unfold x in x in RtoFloat' y
end.


Ltac RtoFloat x :=
   let y := eval simpl in x in
   let y := RtoFloat' y in
   let y := eval compute in y in
   exact y.

Import Binary.

Definition some_nan64:  {x : binary_float 53 1024 | is_nan _ _ x = true}.
exists (B754_nan 53 1024 false 1 (eq_refl _)). reflexivity.
Defined.

Require Import vcfloat.Float_notations.

Ltac ShowBound bound :=
  match type of bound with
  | ?t => first [unify t R | fail 1 "ShowBound expects an argument of type R but" bound "has type" t]
  end;
  let y := eval simpl in bound in
  let y := RtoFloat' y in
  let y := constr:(BSN2B _ _ some_nan64 (@BinarySingleNaN.SF2B 53 1024 (FloatOps.Prim2SF y) (eq_refl _))) in
  let y := eval compute in y in
  match y with  B754_finite 53 1024 ?s ?m ?e ?H =>
     let z := constr:(b64_B754_finite s m e H) in
     idtac "ShowBound" bound z; exact z
  end.

Ltac CheckBound x hi :=
     idtac "Checking that" x "is indeed less than" hi;
       exact (Binary.Bcompare _ _ ltac:(ShowBound x) hi = Some Lt).
