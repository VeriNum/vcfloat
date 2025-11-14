From Coq Require Import List. Import ListNotations.
From Coq Require ProofIrrelevance.
From Coq Require Import JMeq.

Fixpoint function_type (args : list Type) (rhs : Type) {struct args} : Type :=
  match args with
  | [] => rhs
  | a :: r => a -> function_type r rhs
  end.

Section KLIST.
Context {type: Type}.

Inductive klist (k : type -> Type) : list type -> Type :=
| Knil : klist k []
| Kcons {ty tys} : k ty -> klist k tys -> klist k (ty :: tys).

Arguments Knil {k}.
Arguments Kcons {k ty tys}.

Lemma klist_nil {k: type -> Type} (al: klist k nil): al = Knil.
Proof.
exact
  match al with
  | Knil => eq_refl
  | Kcons _ _ => idProp
  end.
Qed.

Lemma klist_cons {k: type -> Type} {t: type} {tr: list type} (al: klist k (t::tr)) :
   exists h: k t, exists r: klist k tr, al = Kcons h r.
Proof.
refine 
 match al with Knil => idProp | Kcons _ _ => _ end.
eexists. eexists. reflexivity.
Qed.

Definition klist_cons1 {k: type -> Type} {t: type} {tr: list type} (al: klist k (t::tr)) : k t :=
  match al with
  | Knil => idProp
  | Kcons h _ => h
  end.

Definition klist_cons2 {k: type -> Type} {t: type} {tr: list type} (al: klist k (t::tr)) : klist k tr := 
  match al with
  | Knil =>idProp
  | Kcons _ tr => tr
  end.

Inductive Kforall {k: type -> Type} (P: forall ty, k ty -> Prop): forall {tys: list type} (es: klist k tys), Prop :=
 | Kforall_nil: Kforall P Knil
 | Kforall_cons: forall {t tr} (h: k t) (r: klist k tr),  P _ h -> Kforall P r -> Kforall P (Kcons h r).

Lemma Kforall_inv: forall (k: type -> Type) (P: forall ty, k ty -> Prop)
                 {ty: type} {tys: list type} (e: k ty) (es: klist k tys),
  Kforall P (Kcons e es) -> P _ e /\ Kforall P es.
Proof.
intros.
inversion H.
subst.
apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H2, H4.
subst; auto.
Qed.

Inductive Kforall2 {k1 k2: type -> Type} (P: forall ty, k1 ty -> k2 ty -> Prop): forall {tys: list type} (al: klist k1 tys) (bl: klist k2 tys), Prop :=
 | Kforall2_nil: Kforall2 P Knil Knil
 | Kforall2_cons: forall {t tr} (ah: k1 t) (bh: k2 t) (ar: klist k1 tr) (br: klist k2 tr),  
                     P _ ah bh -> Kforall2 P ar br -> Kforall2 P (Kcons ah ar) (Kcons bh br).

Lemma Kforall2_inv: forall (k1 k2: type -> Type) (P: forall ty, k1 ty -> k2 ty -> Prop)
                 {ty: type} {tys: list type} (a: k1 ty) (b: k2 ty) (al: klist k1 tys) (bl: klist k2 tys),
  Kforall2 P (Kcons a al) (Kcons b bl) -> P _ a b /\ Kforall2 P al bl.
Proof.
intros.
inversion H.
subst.
apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H2, H4, H5, H6.
subst; auto.
Qed.

Fixpoint kapp {tys1 tys2 : list type} {k: type -> Type} (a: klist k tys1) (b: klist k tys2) : klist k (tys1++tys2) :=
 match a in (klist _ l) return (klist k (l ++ tys2)) with
  | Knil => b
  | Kcons a1 ar => Kcons a1 (kapp ar b)
  end.

Lemma kapp_nil_r: forall tys1 k (al: klist k tys1),
  JMeq (kapp al Knil) al.
Proof.
induction al.
reflexivity.
simpl.
set (u := @kapp tys [] k al (@Knil k)) in *.
clearbody u.
set (tys' := tys ++ nil) in *.
assert (tys' = tys) by apply app_nil_r.
clearbody tys'.
subst tys'.
apply JMeq_eq in IHal.
subst.
reflexivity.
Qed.

Lemma kapp_assoc:
 forall (k: type -> Type) (ta tb tc: list type)
    (ea: klist k ta) (eb: klist k tb) (ec: klist k tc),
  JMeq (kapp ea (kapp eb ec)) (kapp (kapp ea eb) ec).
Proof.
intros.
clear.
induction ea; simpl; auto.
set (u := (tys++tb)++tc) in *.
set (v := tys++tb++tc) in *.
assert (u=v) by (symmetry; apply app_assoc).
set (tab := tys++tb) in *.
set (tbc := tb++tc) in *.
set (ebc := kapp eb ec) in *. clearbody ebc.
set (eab := kapp ea eb) in *; clearbody eab.
rename tys into ta.
set (abc1 := @kapp tab tc k eab ec) in *. 
set (abc2 := @kapp ta tbc k ea ebc) in *.
revert IHea.
fold u in abc1.
fold v in abc2.
clearbody abc1. clearbody abc2.
clearbody v. clearbody u.
clearbody tab. clearbody tbc.
subst u.
intro.
apply JMeq_eq in IHea.
subst abc2.
reflexivity.
Qed.

End KLIST.

Arguments Knil {type k}.
Arguments Kcons {type k ty tys}.

Fixpoint mapk {type: Type} {k1 k2: type -> Type} (f: forall ty: type, k1 ty -> k2 ty) 
  {tys: list type} (al: klist k1 tys) : klist k2 tys := 
    match al in (klist _ l) return (l = tys -> klist k2 tys) with
    | Knil =>
        fun H : [] = tys =>
          eq_rect [] (fun l : list type => klist k2 l) Knil tys H
    | @Kcons _ _ ty tys' x x0 =>
        fun (H : ty :: tys' = tys) =>
          eq_rect (ty :: tys')
            (fun l : list type => k1 ty -> klist k1 tys' -> klist k2 l)
            (fun (X1 : k1 ty) (X2 : klist k1 tys') =>Kcons (f ty X1) (mapk f X2))
            tys H x x0
    end  eq_refl.

Lemma mapk_mapk:
  forall {type: Type} [k1 k2 k3: type -> Type] (f: forall ty, k1 ty -> k2 ty) (g: forall ty, k2 ty -> k3 ty)
           (tys: list type) (l: klist k1 tys), 
     mapk g (mapk f l) = mapk (fun ty x => g ty (f ty x)) l.
Proof.
induction l; simpl; auto.
f_equal; auto.
Qed.

Definition applyk_aux {type: Type} {k: type -> Type}  (typemapper : type -> Type)
         (arg1: type) (args : list type) (res : type)
         (applyk : function_type (map typemapper args) (typemapper res) ->
              (forall ty : type, k ty -> typemapper ty) ->
             klist k args -> typemapper res)
         (f: function_type (map typemapper (arg1:: args)) (typemapper res))
         (valmapper: forall ty : type, k ty -> typemapper ty)
         (es: klist k (arg1::args)):
         typemapper res.
remember (arg1::args) as args0.
destruct es  as [ | arg1' args' e1 er] eqn:?H.
discriminate.
inversion Heqargs0; clear Heqargs0; subst.
apply (applyk (f (valmapper _ e1)) valmapper er).
Defined.

Fixpoint applyk {type: Type} {k: type -> Type}  
    (typemapper: type -> Type)
    (args: list type)
    (res: type)
    {struct args}
    : function_type (map typemapper args) (typemapper res) ->
     (forall ty: type, k ty -> typemapper ty) ->
       klist k args -> typemapper res :=
match
     args as l
     return
       (function_type (map typemapper l) (typemapper res) ->
         (forall ty: type, k ty -> typemapper ty) ->
        klist k l -> typemapper res)
   with
   | [] =>fun f _ _ => f
   | arg1 :: args0 =>
    applyk_aux typemapper arg1 args0 res
          (applyk typemapper args0 res)
   end.

From Coq Require Import Recdef.
Local Set Warnings "-funind-cannot-define-graph,-funind-cannot-build-inversion".
Module StuffNotNeeded.

Section KLIST.
Context {type: Type}.

Definition mapk_aux A {k: type -> Type} (f: forall ty: type, k ty -> A) 
  (t: type) (ts: list type)
    (mapk: klist k ts -> list A):  klist k (t::ts) -> list A :=
fun X: klist k (t::ts) =>
match
  X as k0 in (klist _ l)
  return (l = t :: ts -> list A)
with
| Knil =>
    fun (H : [] = t :: ts)  =>
    False_rect (list A) (eq_ind [] (fun e => match e with [] => True | _ :: _ => False end)
                                   I (t :: ts) H)
| @Kcons _ _ ty tys e k2 =>
    fun H2 : ty :: tys = t :: ts =>
                   (eq_rect_r (fun ty1 : type => k ty1 -> list A)
                      (fun e' : k t =>
                       eq_rect_r (fun tys2 : list type => klist k tys2 -> list A)
                         (fun k3 : klist k ts => f t e' :: mapk k3)  (f_equal (@tl type) H2) k2) 
                               (f_equal  (hd ty) H2) e)
end eq_refl .



Function mapk_aux1 {k: type -> Type} A (f: forall (ty: type), k ty -> A) (tys: list type) {measure length tys}:
     (klist k tys)  -> list A :=
match tys with 
| nil => fun _ => nil
| t::ts => mapk_aux A f t ts (@mapk_aux1 k A f ts)
end.
Proof.
intros.
simpl. apply PeanoNat.Nat.lt_succ_diag_r.
Defined.

Definition mapk {A} f {tys} l := mapk_aux1 A f tys l.

End KLIST.
End StuffNotNeeded.

