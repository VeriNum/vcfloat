(*  Number Notations for Flocq, by Andrew W. Appel, August 2021.

   The purpose of this file is to provide  Notation  (parsing/printing) for
   Flocq binary-format floating-point constants.
   That is, unlike Coq's built-in Number notation for floats, which goes
   into Coq's primitive floats, this file goes to any bitsize of Flocq IEEE (binary)
   floating point.

   Underflows, overflow-to-infinity, infinity, and Nan are not recognized in parsing.
   The user can still have such values, just not through this notation.

   Printing does not handle infinities or nans; they'll print using no Notation or other Notation.

   An alternate, and much simpler, method, would be to use Coq's built-in
   float notations, and then convert from primitive floats to Flocq floats.
   This would work accurately for Flocq's  binary64, but for other sizes it
   would suffer from double-rounding inaccuracies, or worse.

   Parsing floating-point numbers is easier (to implement correctly) than printing
   them accurately and concisely.  Therefore I take a translation-validation
   approach:  any candidate output of the printing function is reparsed
   for validation.

   It is possible that the printing functions may have bugs that, in some cases,
   produce None instead of Some(Number...).  Coq will handle that by outputting
   the underlying data structure representation, which is correct (although ugly).
   Therefore the translation-validation approach is safe.

   Bibliographic notes:
   It is well known that printing floating-point numbers accurately and concisely
   is nontrivial.  There are four kinds of solutions:
    1. Incorrect (in some cases, print a number that does not read back as the same number)
    2. Correct but unrounded, i.e. print 0.15 as 1.49999996e-1  which
            reads back correctly but does not look nice
   3.  Correct and concise by validation, i.e., print 0.15 as 0.15 or 1.5e-1
      by trying twice (rounding down, rounding up), and then checking in which case
      the rounding was done correctly
    4. Correct and concise by construction, i.e., sophisticated algorithms that
       get it right without needing to validate.
  This implementation takes approach #3.

  In programming languages without arbitrary-precision integers, all of this
  is more difficult, but in Coq we have the Z type that simplifies some issues.
*)

Local Set Warnings "-via-type-remapping,-via-type-mismatch".

From Flocq Require Import Binary Bits Core.
From vcfloat Require Import IEEE754_extra. (* This file should really be part of Flocq, not CompCert *)
From Coq Require Import ZArith.
Open Scope Z.

Definition b32_B754_zero : _ -> binary32 := B754_zero 24 128.
Definition b32_B754_infinity : _ -> binary32 := B754_infinity 24 128.
Definition b32_B754_nan : bool -> forall pl : positive, nan_pl 24 pl = true ->  binary32 := B754_nan 24 128.
Definition b32_B754_finite: bool ->
       forall (m : positive) (e : Z),
       SpecFloat.bounded 24 128 m e = true ->  binary32 := B754_finite 24 128.

Definition b64_B754_zero : _ -> binary64 := B754_zero 53 1024.
Definition b64_B754_infinity : _ -> binary64 := B754_infinity 53 1024.
Definition b64_B754_nan : bool -> forall pl : positive, nan_pl 53 pl = true ->  binary64 := B754_nan 53 1024.
Definition b64_B754_finite: bool ->
       forall (m : positive) (e : Z),
       SpecFloat.bounded 53 1024 m e = true ->  binary64 := B754_finite 53 1024.

Module Type BINARY_FLOAT_TO_NUMBER.
 Parameter number_to_binary_float:
  forall (prec emax: Z) (prec_gt_0: 0 <prec) (Hprecmax: prec < emax),
   Number.number -> option (binary_float prec emax).

 Parameter binary_float_to_number:
  forall (prec emax : Z)
       (prec_gt_0: 0 <prec) (Hmax: 3 <= emax) (Hprecmax: prec < emax),
   binary_float prec emax -> option Number.number.
End BINARY_FLOAT_TO_NUMBER.


Module BinaryFloat_to_Number <: BINARY_FLOAT_TO_NUMBER.

(* len_uint: Number of digits in a Decimal.uint *)
Fixpoint len_uint (d: Decimal.uint) : Z :=
 match d with
 | Decimal.Nil => Z0
 | Decimal.D0 d' => Z.succ (len_uint d')
 | Decimal.D1 d' => Z.succ (len_uint d')
 | Decimal.D2 d' => Z.succ (len_uint d')
 | Decimal.D3 d' => Z.succ (len_uint d')
 | Decimal.D4 d' => Z.succ (len_uint d')
 | Decimal.D5 d' => Z.succ (len_uint d')
 | Decimal.D6 d' => Z.succ (len_uint d')
 | Decimal.D7 d' => Z.succ (len_uint d')
 | Decimal.D8 d' => Z.succ (len_uint d')
 | Decimal.D9 d' => Z.succ (len_uint d')
 end.

(* len_int:  number of digits in a Decimal.int *)
Definition len_int (d: Decimal.int) : Z :=
 match d with
 | Decimal.Pos u => len_uint u
 | Decimal.Neg u => len_uint u
 end.

(* simple_negate avoids the issue of which nan to use *)
Definition simple_negate {prec emax} (x: option (binary_float prec emax)) : option (binary_float prec emax) :=
 match x with
  | Some (B754_finite _ _ s m e H) => Some (B754_finite _ _ (negb s) m e H)
  | Some (B754_zero _ _ s) => Some (B754_zero _ _ (negb s))
  | Some (B754_infinity _ _ s) => Some (B754_infinity _ _ (negb s))
  | _ => None
  end.

Definition ensure_finite prec emax (x: binary_float prec emax) :=
 match x with
 | B754_finite _ _ _ _ _ _ => Some x
 | _ => None
 end.

(*  PARSING arbitrary-sized IEEE floats *)
Definition number_to_binary_float' (prec emax: Z)
       (prec_gt_0: 0 <prec)
       (Hprecmax: prec < emax)
   (a: Decimal.int)  (* integer part of mantissa *)
   (b: Decimal.uint) (* fractional part of mantissa *)
   (e: Decimal.int)  (* exponent *)
         : option (binary_float prec emax) :=
let m' := Decimal.app_int a b in
match Z.of_int m' with
| Zpos m0 =>
    let e' := Z.of_int e - len_uint b in
    ensure_finite prec emax (Bparse prec emax prec_gt_0 Hprecmax 10 m0 e')
| Zneg m0 =>
    let e' := Z.of_int e - len_uint b in
    simple_negate (ensure_finite prec emax (Bparse prec emax prec_gt_0 Hprecmax 10 m0 e'))
| Z0 =>
    match m' with
    | Decimal.Pos _ => Some (B754_zero prec emax false)
    | Decimal.Neg _ => Some (B754_zero prec emax true)
    end
end.

Definition number_to_binary_float (prec emax: Z)
       (prec_gt_0: 0 <prec)
       (Hprecmax: prec < emax)
   (n: Number.number) : option (binary_float prec emax) :=
  (* input number [n] is a Decimal number (Hexadecimal not supported).
    If [n] is too large (overflow), produces None
    if [n] is tiny (underflow), produces a None
    if [n] is representable as a B754_finite, produces that floating point number.
 *)
 match n with
 | Number.Decimal (Decimal.Decimal a b) =>
     number_to_binary_float' prec emax prec_gt_0 Hprecmax a b (Decimal.Pos (Decimal.D0 Decimal.Nil))
 | Number.Decimal (Decimal.DecimalExp a b e) =>
     number_to_binary_float' prec emax prec_gt_0 Hprecmax a b e
 | _ => None
 end.

(** PRINTING arbitrary-size IEEE floats *)

Fixpoint do_rounding (n: nat) (round: bool) (d: Decimal.uint) : Decimal.uint * bool :=
  (* This function keeps only the first n digits of d,
     rounding down (if round=false)  or rounding up (if round=true).
     The result (fst part) is at most n digits long (trailing zeros are removed).
     The snd part of the result is the carry, true if a D1 digit should be
       prepended to the fst part of the result.
  *)
 match n with
 | O => (Decimal.Nil, round)
 | S n' =>
    match d with
    | Decimal.Nil => (Decimal.Nil, false)
    | Decimal.D0 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D1 d', false)
                            else if Decimal.uint_beq d' Decimal.Nil
                                    then (Decimal.Nil, false)
                                    else (Decimal.D0 d', false)
    | Decimal.D1 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D2 d', false) else (Decimal.D1 d', false)
    | Decimal.D2 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D3 d', false) else (Decimal.D2 d', false)
    | Decimal.D3 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D4 d', false) else (Decimal.D3 d', false)
    | Decimal.D4 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D5 d', false) else (Decimal.D4 d', false)
    | Decimal.D5 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D6 d', false) else (Decimal.D5 d', false)
    | Decimal.D6 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D7 d', false) else (Decimal.D6 d', false)
    | Decimal.D7 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D8 d', false) else (Decimal.D7 d', false)
    | Decimal.D8 d' => let (d', carry) := do_rounding n' round d'
                        in if carry then (Decimal.D9 d', false) else (Decimal.D8 d', false)
    | Decimal.D9 d' => let (d', carry) := do_rounding n' round d'
                        in if carry
                        then (Decimal.Nil, true)
                        else (Decimal.D9 d', false)
    end
 end.

(* format_mantissa' rounds the decimal number  DDDDDDDDD,
    to dec_precision digits,  rounding down (if round=false) or up (if round=true).
    If rounding up causes a carry to a number with more digits,
    return exponent 1, else exponent 0. *)
Definition format_mantissa' (dec_precision: nat) (round: bool) (d: Decimal.uint)
   : Decimal.uint * Z :=
       let (d', carry) := do_rounding dec_precision round d
              in if carry then (Decimal.D1 d', 1) else (d', 0).

Definition split_first_digit (m: Decimal.uint) : Decimal.uint * Decimal.uint :=
 match m with
  | Decimal.Nil => (Decimal.D0 Decimal.Nil, Decimal.Nil)
  | Decimal.D0 d' => (Decimal.D0 Decimal.Nil, d')
  | Decimal.D1 d' => (Decimal.D1 Decimal.Nil, d')
  | Decimal.D2 d' => (Decimal.D2 Decimal.Nil, d')
  | Decimal.D3 d' => (Decimal.D3 Decimal.Nil, d')
  | Decimal.D4 d' => (Decimal.D4 Decimal.Nil, d')
  | Decimal.D5 d' => (Decimal.D5 Decimal.Nil, d')
  | Decimal.D6 d' => (Decimal.D6 Decimal.Nil, d')
  | Decimal.D7 d' => (Decimal.D7 Decimal.Nil, d')
  | Decimal.D8 d' => (Decimal.D8 Decimal.Nil, d')
  | Decimal.D9 d' => (Decimal.D9 Decimal.Nil, d')
  end.

(* format_mantissa takes a sign (Decimal.Pos or Decimal.Neg)
   and a decimal mantissa  D[.]DDDDDDDD with implicit decimal point,
   and produces a rounded decimal number of the form +D.DDDDD or -D.DDDDD,
   with explicit decimal point, along with carry=1 if the implicit decimal point has
   shifted (because of carry out of high-order digit), otherwise carry=0.
   Or if input is d=zero, then no rounding or carry, just output 0.0 *)
Definition format_mantissa (dec_precision: nat)
                (round: bool)
                (sign: Decimal.uint -> Decimal.int)
                (d: Decimal.uint) : Decimal.decimal * Z :=
 if Decimal.uint_beq d Decimal.Nil
 then (Decimal.Decimal (sign (Decimal.D0 Decimal.Nil)) (Decimal.D0 Decimal.Nil), 0)
 else let (d',carry) := format_mantissa' dec_precision round d
         in let (h,t) := split_first_digit d'
         in (Decimal.Decimal (sign h) t, carry).

(* format_mantissa_int takes a decimal mantissa  +D[.]DDDDDDDD or -D[.]DDDDDDDD
   with implicit decimal point,
   and produces a rounded decimal number of the form +D.DDDDD or -D.DDDDD,
   with explicit decimal point, along with carry=1 if the implicit decimal point has
   shifted (because of carry out of high-order digit), otherwise carry=0.
   Or if input is d=zero, then no rounding or carry, just output 0.0 *)
Definition format_mantissa_int (dec_precision: nat) (round: bool) (d: Decimal.int)
    : Decimal.decimal * Z :=
 match d with
 | Decimal.Pos d' => format_mantissa dec_precision round Decimal.Pos d'
 | Decimal.Neg d' =>format_mantissa dec_precision round Decimal.Neg d'
 end.

(* Choose a beautiful way to express the decimal number h.frac x 10^e,
   where h is a single digit.  *)
Definition perhaps_exponent (h: Decimal.int) (frac: Decimal.uint) (e: Z)
                   : Decimal.decimal :=
 match e with
 | 0 => Decimal.Decimal h frac
 | 1 => let (d,r) := split_first_digit frac in
             Decimal.Decimal (Decimal.app_int h d) r
 | 2 => let (d1,r1) := split_first_digit frac in
             let (d2,r2) := split_first_digit r1 in
             Decimal.Decimal (Decimal.app_int h (Decimal.app d1 d2)) r2
 | -1 => match Decimal.app_int h frac with
               | Decimal.Pos u => Decimal.Decimal (Decimal.Pos (Decimal.D0 Decimal.Nil)) u
               | Decimal.Neg u => Decimal.Decimal (Decimal.Neg (Decimal.D0 Decimal.Nil)) u
              end
 | _ => Decimal.DecimalExp h frac (Z.to_int e)
 end.

(* format_float_num' takes a number
    (+/-)D.DDDDDDDDDDDDDD x 10^e,
   rounds it do dec_precision digits (rounding down if round=false, otherwise up),
   and produces a Number.Decimal representation.  It then validates the
   output by converting back to float and comparing with [goal].
   If success, produces Some, otherwise None. *)
Definition format_float_num' prec emax
       (prec_gt_0: 0 <prec)
       (Hprecmax: prec < emax)
   (goal: binary_float prec emax) (dec_precision: nat)
   (round: bool)  (d: Decimal.int) (e': Z) : option Number.number :=
  let (m, e'') := format_mantissa_int dec_precision round d in
  let e := e'+e'' in
  if Z.eqb e 0%Z
  then Some (Number.Decimal m)
  else match m with
          | Decimal.Decimal h t =>
                let n := Number.Decimal (perhaps_exponent h t e) in
                match number_to_binary_float _ _ prec_gt_0 Hprecmax n with
                | Some y =>
                      match Bcompare prec emax goal y with
                      | Some Eq => Some n
                      | _ => None
                      end
                | None => None
                end
         | _ => None
         end.


(* Measures approximately how many characters in the printed representation of n *)
Definition ugliness_of_number (n: Number.number) : Z :=
 match n with
 | Number.Decimal (Decimal.Decimal h Decimal.Nil) => len_int h
 | Number.Decimal (Decimal.Decimal h t) => len_int h + len_uint t + 1
 | Number.Decimal  (Decimal.DecimalExp h Decimal.Nil (Decimal.Pos e)) =>
             len_int h + 1 + len_uint e
 | Number.Decimal  (Decimal.DecimalExp h Decimal.Nil (Decimal.Neg e)) =>
             len_int h + 2 + len_uint e
 | Number.Decimal  (Decimal.DecimalExp h t (Decimal.Pos e)) =>
             len_int h + len_uint t + 2 + len_uint e
 | Number.Decimal  (Decimal.DecimalExp h t (Decimal.Neg e)) =>
             len_int h + len_uint t + 3 + len_uint e
 | _ => 1
 end.

Definition choose_least_ugly (a b: option Number.number) :=
 match a, b with
 | None, _ => b
 | _, None => a
 | Some n1, Some n2 =>
  if ugliness_of_number n1 <=? ugliness_of_number n2
  then a else b
 end.

(* format_float_num takes a decimal number DDDDDDD and exponent e,
   where DDDDDDD is considered an integer (decimal point at right),
   and produces (if possible) its Number.number representation *)
Definition format_float_num prec emax
       (prec_gt_0: 0 <prec)
       (Hprecmax: prec < emax)
   (goal: binary_float prec emax)
   (d: Decimal.int) (e: Z) : option Number.number :=
 let dec_precision := Z.to_nat (2 + prec * 100 / 332) in
 let e' := e + (len_int d-1) in
 let f := format_float_num' prec emax prec_gt_0 Hprecmax goal  in
 List.fold_left choose_least_ugly
   (f dec_precision false d e'
   :: f dec_precision true d e'
   :: f (dec_precision-1)%nat true d e'
   :: nil)
  None.

(*  binary_float_to_number_nonneg takes a nonnegative floating point number x,
   and converts it (if possible) to its Number.number representation *)
Definition binary_float_to_number_nonneg (prec emax : Z)
       (prec_gt_0: 0 <prec)
       (Hmax: 3 <= emax)
       (Hprecmax: prec < emax)
       (* x must be nonnegative! *)
       (x: binary_float prec emax) : option Number.number :=
    let '(y,e) := Bfrexp _ _ prec_gt_0 (*Hmax*) x in
    let z := Bldexp _ _ prec_gt_0 Hprecmax BinarySingleNaN.mode_NE y prec in
    match ZofB _ _ z
    with None =>None
    | Some i =>
      if Z.ltb prec e
       then let d := Z.to_int (i * Z.pow 2 (e-prec))
               in format_float_num prec emax prec_gt_0 Hprecmax x d Z0
       else let d := Z.to_int (i * Z.pow 5 (prec-e))
               in format_float_num prec emax prec_gt_0 Hprecmax x d (e-prec)
    end.

(*  binary_float_to_number_nonneg takes a floating point number x,
   and converts it (if possible) to its Number.number representation *)
Definition binary_float_to_number (prec emax : Z)
       (prec_gt_0: 0 <prec)
       (Hmax: 3 <= emax)
       (Hprecmax: prec < emax)
       (x: binary_float prec emax) : option Number.number :=
    match x with
    | B754_zero _ _ false => Some (Number.Decimal (Decimal.Decimal (Decimal.Pos (Decimal.D0 Decimal.Nil)) Decimal.Nil))
    | B754_zero _ _ true => Some (Number.Decimal (Decimal.Decimal (Decimal.Neg (Decimal.D0 Decimal.Nil)) Decimal.Nil))
    | B754_nan _ _ _ _ _ => None
    | B754_infinity _ _ _ => None
    | B754_finite _ _ false _ _ _ =>  binary_float_to_number_nonneg prec emax prec_gt_0 Hmax Hprecmax x
    | B754_finite _ _ true m e H =>
       match binary_float_to_number_nonneg  prec emax prec_gt_0 Hmax Hprecmax
                    (B754_finite prec emax false m e H) with
            | Some (Number.Decimal (Decimal.Decimal (Decimal.Pos d) m))
               => Some (Number.Decimal (Decimal.Decimal (Decimal.Neg d) m))
            | Some (Number.Decimal (Decimal.DecimalExp (Decimal.Pos d) m e))
               => Some (Number.Decimal (Decimal.DecimalExp (Decimal.Neg d) m e))
            | _ => None
            end
     end.
End BinaryFloat_to_Number.

Import BinaryFloat_to_Number.

(* We define the following inductive type, which is isomorphic
   to (binary_float 24 128), for two reasons:
  1. the Number Notation requires a "via" type in the case
    that it's notation for a noninductive type such as binary32.
    The workaround for that, avoiding a "via" type, would be
    to define binary32 as an abbreviation (Notation) instead
    of a Definition.
  2. The conversions to_bf32 and of_bf32 also have the effect
    of discarding large proofs and substituting small proofs.
    Without doing this, then the Number Notation would do a "cbv"
    that would blow up.  So the "via" actually serves a useful purpose.
*)

Inductive binary_float32  : Set :=
    B32_B754_zero : bool -> binary_float32
  | B32_B754_infinity : bool -> binary_float32
  | B32_B754_nan : bool ->
               forall pl : positive, binary_float32
  | B32_B754_finite : bool ->
                  forall (m : positive) (e : Z),
                   SpecFloat.bounded 24 128 m e = true ->  binary_float32.

Definition to_bf32 (x: binary32) : option binary_float32 :=
match x with
| B754_zero _ _ s => Some (B32_B754_zero s)
| B754_infinity _ _ s => Some (B32_B754_infinity s)
| B754_nan _ _ s pl e =>
    (if nan_pl 24 pl as b0
      return (nan_pl 24 pl = b0 -> b0 = true -> option binary_float32)
     then fun _ _ => Some (B32_B754_nan s pl)
     else fun _ _ => None)
     (eq_refl (nan_pl 24 pl)) e
| B754_finite _ _ s m e e0 =>
    (if SpecFloat.bounded 24 128 m e as b0
      return
        (SpecFloat.bounded 24 128 m e = b0 -> b0 = true -> option binary_float32)
     then fun H0 _ => Some (B32_B754_finite s m e H0)
     else fun _ _ => None)
    (eq_refl _) e0
end.

Definition of_bf32 (x: binary_float32) : option binary32 :=
match x with
| B32_B754_zero b => Some (B754_zero 24 128 b)
| B32_B754_infinity b => Some (B754_infinity 24 128 b)
| B32_B754_nan b pl =>
    (if nan_pl 24 pl as b1 return (nan_pl 24 pl = b1 -> option binary32)
     then fun H0 => Some (B754_nan 24 128 b pl H0)
     else fun _ => None) (eq_refl _)
| B32_B754_finite b m e e0 =>
    (if SpecFloat.bounded 24 128 m e as b1
      return (SpecFloat.bounded 24 128 m e = b1 -> b1 = true -> option binary32)
     then fun H0 _ => Some (B754_finite 24 128 b m e H0)
     else fun _ _ => None)
      (eq_refl _) e0
end.

Definition number_to_float32 (n: Number.number) : option binary_float32 :=
 match number_to_binary_float 24 128 ltac:(reflexivity)  ltac:(reflexivity)  n with
 | Some b => to_bf32 b
 | None => None
 end.

Definition float32_to_number (x: binary_float32) : option Number.number :=
  match of_bf32 x with
   | Some b => binary_float_to_number 24 128 ltac:(reflexivity) ltac:(clear; hnf; intro; discriminate) ltac:(reflexivity) b
   | None  => None
  end.

Inductive binary_float64  : Set :=
    B64_B754_zero : bool -> binary_float64
  | B64_B754_infinity : bool -> binary_float64
  | B64_B754_nan : bool ->
               forall pl : positive, binary_float64
  | B64_B754_finite : bool ->
                  forall (m : positive) (e : Z),
                   SpecFloat.bounded 53 1024 m e = true ->  binary_float64.

Definition to_bf64 (x: binary64) : option binary_float64 :=
match x with
| B754_zero _ _ s => Some (B64_B754_zero s)
| B754_infinity _ _ s => Some (B64_B754_infinity s)
| B754_nan _ _ s pl e =>
    (if nan_pl 53 pl as b0
      return (nan_pl 53 pl = b0 -> b0 = true -> option binary_float64)
     then fun _ _ => Some (B64_B754_nan s pl)
     else fun _ _ => None)
     (eq_refl (nan_pl 53 pl)) e
| B754_finite _ _ s m e e0 =>
    (if SpecFloat.bounded 53 1024 m e as b0
      return
        (SpecFloat.bounded 53 1024 m e = b0 -> b0 = true -> option binary_float64)
     then fun H0 _ => Some (B64_B754_finite s m e H0)
     else fun _ _ => None)
    (eq_refl _) e0
end.

Definition of_bf64 (x: binary_float64) : option binary64 :=
match x with
| B64_B754_zero b => Some (B754_zero 53 1024 b)
| B64_B754_infinity b => Some (B754_infinity 53 1024 b)
| B64_B754_nan b pl =>
    (if nan_pl 53 pl as b1 return (nan_pl 53 pl = b1 -> option binary64)
     then fun H0 => Some (B754_nan 53 1024 b pl H0)
     else fun _ => None) (eq_refl _)
| B64_B754_finite b m e e0 =>
    (if SpecFloat.bounded 53 1024 m e as b1
      return (SpecFloat.bounded 53 1024 m e = b1 -> b1 = true -> option binary64)
     then fun H0 _ => Some (B754_finite 53 1024 b m e H0)
     else fun _ _ => None)
      (eq_refl _) e0
end.

Definition number_to_float64 (n: Number.number) : option binary_float64 :=
 match number_to_binary_float 53 1024 ltac:(reflexivity)  ltac:(reflexivity)  n with
 | Some b => to_bf64 b
 | None => None
 end.

Definition float64_to_number (x: binary_float64) : option Number.number :=
  match of_bf64 x with
   | Some b => binary_float_to_number 53 1024 ltac:(reflexivity) ltac:(clear; hnf; intro; discriminate) ltac:(reflexivity) b
   | None  => None
  end.

Declare Scope float32_scope.
Delimit Scope float32_scope with F32.

Declare Scope float64_scope.
Delimit Scope float64_scope with F64.

Number Notation binary32 number_to_float32  float32_to_number
    (via binary_float32 mapping [
          [b32_B754_zero] => B32_B754_zero,
          [b32_B754_infinity] => B32_B754_infinity,
          [b32_B754_nan] => B32_B754_nan,
          [b32_B754_finite] => B32_B754_finite ] )
    :float32_scope.

Number Notation binary64 number_to_float64  float64_to_number
    (via binary_float64 mapping [
          [b64_B754_zero] => B64_B754_zero,
          [b64_B754_infinity] => B64_B754_infinity,
          [b64_B754_nan] => B64_B754_nan,
          [b64_B754_finite] => B64_B754_finite ] )
    :float64_scope.

Module Tests.

Open Scope float32_scope.

Check 0.0.
Check 0.
Check -0.00001.
Check 1.5.
Check 15.
Check 150.
Check 1500.
Check 0.15.
Check 0.015.
Check 0.0000000001.
Fail Check 1e-100.
Fail Check 1e100.
Check 1e20.
Check 1e-20.

Close Scope float32_scope.

Open Scope float64_scope.
Import Coq.Lists.List.

Check 0.0.
Check 0.
Check -0.00001.
Check 1.5.
Check 15.
Check 150.
Check 1500.
Check 0.15.
Check 0.015.
Check 0.0000000001.
Check 1e-100.
Fail Check 1e-1000.
Check 1e100.
Fail Check 1e1000.
Check 1e20.
Check 1e-20.
Check 3.0104791538616437e-006.

Close Scope float64_scope.

End Tests.
