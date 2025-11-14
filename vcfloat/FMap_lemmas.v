From Coq Require FMapInterface.
From Coq Require FMapAVL.
Import OrderedType.


(* (c) 2022 Andrew W. Appel. 
 
 LEMMAS FOR REASONING ABOUT COMMUTATIVE FOLDS OVER TABLES.

 This module adds two extra lemmas to the FMapAVL functor.
 Because the lemmas rely on internal ("Raw") components of FMapAVL,
 this is structured as a functor that, when applied, instantiates FMapAVL.

 The purpose of the lemmas is to manipulate folds over tables.

  Suppose you have a table mapping keys to elements:
            tab : Table.t element.
  And suppose you fold a function over all the elements:
     fold_f (tab) :=  Table.fold (fun k x a => f (lift x) a) u tab
  where f is associative-commutative over type A, with u:A is a unit for f.

 Then you would think that if [Table.find k tab = None]  then,
      fold_f (Table.add k x tab) = f x tab.
  And if Table.find k tab = Some y, then a slightly more complicated
  relation should hold.

  That's just the purpose of the lemmas
        relate_fold_add lemma  and   fold_add_ignore,
  which (when used together) can facilitate reasoning about 
  table folds when  adding elements.

 The second module "Demonstration" illustrates an example of its use.
  In that case, the associative-commutative [f] is just Z.add,
  the element type is positive, the "lift" function is Z.pos.
  We prove that when you insert a positive number into a table,
  the "Table.fold (fun k x a => Z.add (Z.pos x) a)"  result will
  increase by the appropriate amount.

*)

Module FMapAVL_extra (Keys: OrderedType).

Module Table := FMapAVL.Make Keys.

Lemma fold_bal:
  forall [elt A] (f: Table.Raw.key -> elt -> A -> A) (t1 t2: Table.Raw.tree elt) k e x,
  Table.Raw.fold f (Table.Raw.bal t1 k e t2) x = 
   Table.Raw.fold f t2 (f k e (Table.Raw.fold f t1 x)).
Proof.
intros.
unfold Table.Raw.bal.
repeat match goal with
 | |- context [if ?A then _ else _] => destruct A 
 | |- context [match Table.Raw.add ?p ?x ?y with _ => _ end] => 
                   destruct (Table.Raw.add p x y) eqn:?H
 | |- context [match ?t with _ => _ end ] => is_var t; destruct t 
end;
simpl; auto.
Qed.

Lemma raw_in_congr:
 forall [elt k k'] [t: Table.Raw.tree elt],
        Keys.eq k k' -> (Table.Raw.In k t <-> Table.Raw.In k' t).
Proof.
intros.
induction t; simpl.
split; intros; inversion H0.
split; intro H0; inversion H0; clear H0; subst.
- constructor; apply Keys.eq_sym in H; eapply Keys.eq_trans; eauto.
- apply Table.Raw.InLeft; rewrite <- IHt1; auto.
- apply Table.Raw.InRight; rewrite <- IHt2; auto.
- constructor; eapply Keys.eq_trans; eauto.
- apply Table.Raw.InLeft; rewrite IHt1; auto.
- apply Table.Raw.InRight; rewrite IHt2; auto.
Qed.

Lemma relate_fold_add':
 forall [elt A: Type]
     [eqv: A -> A -> Prop] 
     (eqv_rel: Equivalence eqv)
     (lift: Table.key -> elt -> A)
     (lift_prop: forall k k' x, Keys.eq k k' -> eqv (lift k x) (lift k' x))
    (f:  A -> A -> A)
    (f_mor: forall x1 y1, eqv x1 y1 ->
              forall x2 y2, eqv x2 y2 ->
              eqv (f x1 x2) (f y1 y2))
    (f_assoc: forall x y z : A, eqv (f x (f y z)) (f (f x y) z))
    (f_commut: forall x y : A, eqv (f x y) (f y x))
    (u: A)
    (u_unit: forall x, eqv (f u x) x)
    (g: Table.key -> elt -> A -> A)
    (g_eqv: forall k x a, eqv (g k x a) (f (lift k x) a))
    (tab: Table.t elt)
    (k: Table.key),
    eqv (Table.fold g tab u)
      (f (match Table.find k tab with Some x => lift k x | None => u end)
       (Table.fold (fun k' x a => 
                           match Keys.compare k k' with EQ _ => a 
                                 | _ => g k' x a end) tab u)).
Proof.
intros.
destruct tab.
unfold Table.fold, Table.find; simpl.
set (h := fun (k' : Table.key) (x : elt) (a : A) =>
         match Keys.compare k k' with
         | EQ _ => a
         | _ => g k' x a
         end).
assert (g_mor: forall k x a b, eqv a b -> eqv (g k x a) (g k x b)). {
  intros. rewrite !g_eqv. apply f_mor; auto; reflexivity.
}
assert (FOLD1: forall t a,  ~Table.Raw.In k t ->
    Table.Raw.fold g t a = Table.Raw.fold h t a). {
 induction t; simpl; intros;auto.
 rewrite IHt1, IHt2.
 f_equal. set (uu := Table.Raw.fold _ _ _); clearbody uu.
 unfold h. clear -H.
 destruct (Keys.compare k k0); auto. contradiction H.
 constructor; auto.
 contradict H. constructor 3; auto.
 contradict H. constructor 2; auto.
}
assert (FOLD2: forall t a b, eqv a b -> eqv (Table.Raw.fold g t a) (Table.Raw.fold g t b)). {
 clear - eqv_rel g_mor.
  induction t; simpl; intros;auto.
}
assert (FOLD3: forall t k a b,
    eqv (Table.Raw.fold g t (g k a b)) (g k a (Table.Raw.fold g t b))). {
  induction t; simpl; intros. reflexivity.
  etransitivity; [ |   apply IHt2]. apply FOLD2.
  transitivity (g k0 e (g k1 a (Table.Raw.fold g t1 b))).
  apply g_mor; auto.
  set (v := Table.Raw.fold _ _ _). clearbody v.
  rewrite (g_eqv k0).
  etransitivity. apply f_mor. reflexivity.
  apply g_eqv.
  etransitivity; [apply f_assoc |].
  etransitivity. apply f_mor. apply f_commut. reflexivity.
  etransitivity; [symmetry; apply f_assoc |].
  symmetry.
  rewrite g_eqv. apply f_mor. reflexivity.  apply g_eqv.
}
destruct (Table.Raw.find k this) eqn:?H.
-
set (a:=u). clearbody a.
revert a; induction is_bst; simpl; intros; [ discriminate | ].
simpl in H.
unfold h at 2. 
destruct (Keys.compare k x).
+
specialize (IHis_bst1 H); clear IHis_bst2.
rewrite <- FOLD1
  by (apply (Table.Raw.Proofs.gt_tree_trans l0) in H1;
        apply Table.Raw.Proofs.gt_tree_not_in; auto).
etransitivity. apply FOLD2. apply g_mor. apply IHis_bst1.
set (v := Table.Raw.fold h l a). clearbody v.
symmetry.
etransitivity.
symmetry.
rewrite <- g_eqv.
apply FOLD3.
apply FOLD2.
rewrite g_eqv.
etransitivity. apply f_mor. reflexivity. apply g_eqv.
rewrite f_assoc.
etransitivity. apply f_mor. apply f_commut. reflexivity.
rewrite <- f_assoc.
rewrite g_eqv.
reflexivity.
+
assert (Hl: ~Table.Raw.In k l)
  by (rewrite (raw_in_congr e1);
        apply Table.Raw.Proofs.lt_tree_not_in; auto).
assert (Hr: ~Table.Raw.In k r)
  by (rewrite (raw_in_congr e1);
        apply Table.Raw.Proofs.gt_tree_not_in; auto).
inversion H; clear H; subst.
clear IHis_bst1 IHis_bst2.
rewrite <- !FOLD1 by auto.
etransitivity.
apply FOLD3.
rewrite !g_eqv.
apply f_mor; try reflexivity.
symmetry.
apply lift_prop; auto.
+
specialize (IHis_bst2 H); clear IHis_bst1.
assert (Hl: ~Table.Raw.In k l)
  by (apply (Table.Raw.Proofs.lt_tree_trans l0) in H0;
        apply Table.Raw.Proofs.lt_tree_not_in; auto).
etransitivity. apply IHis_bst2. clear IHis_bst2.
apply f_mor. reflexivity.
rewrite FOLD1 by auto. reflexivity.
-
assert (Hr: ~Table.Raw.In k this)
  by (apply Table.Raw.Proofs.not_find_iff; auto).
rewrite FOLD1 by auto.
rewrite u_unit.
reflexivity.
Qed.


Lemma relate_fold_add:
 forall [elt A: Type]
     [eqv: A -> A -> Prop] 
     (eqv_rel: Equivalence eqv)
     (lift: Table.key -> elt -> A)
     (lift_prop: forall k k' x, Keys.eq k k' -> eqv (lift k x) (lift k' x))
    (f:  A -> A -> A)
    (f_mor: forall x1 y1, eqv x1 y1 ->
              forall x2 y2, eqv x2 y2 ->
              eqv (f x1 x2) (f y1 y2))
    (f_assoc: forall x y z : A, eqv (f x (f y z)) (f (f x y) z))
    (f_commut: forall x y : A, eqv (f x y) (f y x))
    (u: A)
    (u_unit: forall x, eqv (f u x) x)
    (g: Table.key -> elt -> A -> A)
    (g_eqv: forall k x a, eqv (g k x a) (f (lift k x) a))
    (tab: Table.t elt)
    (k: Table.key),
    eqv (Table.fold g tab u)
      (f (match Table.find k tab with Some x => lift k x | None => u end)
       (Table.fold (fun k' x a => if Keys.eq_dec k k' then a else g k' x a) tab u)).
Proof.
intros.
rewrite (relate_fold_add' eqv_rel lift lift_prop f f_mor f_assoc f_commut u u_unit g g_eqv tab k).
apply f_mor.
reflexivity.
rewrite !Table.fold_1.
clear u_unit.
revert u.
induction (Table.elements (elt:=elt) tab); intro.
simpl. reflexivity.
simpl.
rewrite IHl.
set (ff := fold_left _).
clearbody ff.
match goal with |- eqv ?A ?B => replace B with A end.
reflexivity.
f_equal.
set (j := fst a). clearbody j.
clear.
destruct (Keys.compare k j); try apply Keys.lt_not_eq in l;
destruct (Keys.eq_dec k j); try contradiction; auto.
symmetry in e. contradiction.
Qed.


Lemma fold_add_ignore:
  forall [elt A]
   (f: Table.key -> elt -> A -> A)
   (tab: Table.t elt)
   (k: Table.key)
   (x: elt) (a0: A),
   (forall k' y a, Keys.eq k k' -> f k' y a = a) ->
   Table.fold f (Table.add k x tab) a0 =
   Table.fold f tab a0.
Proof.
intros.
destruct tab.
unfold Table.fold, Table.add; simpl.
revert a0; induction is_bst; intros.
unfold Table.Raw.add. simpl.
apply H; reflexivity.
simpl.
destruct (Keys.compare k x0); rewrite ?fold_bal.
rewrite IHis_bst1. auto.
simpl.
f_equal.
rewrite ?H; auto.
rewrite IHis_bst2. auto.
Qed.



Lemma relate_fold_add_alt:
 forall [elt A: Type]
     [eqv: A -> A -> Prop] 
     (eqv_rel: Equivalence eqv)
     (lift: Table.key -> elt -> A)
     (lift_prop: forall k k' x, Keys.eq k k' -> eqv (lift k x) (lift k' x))
    (f:  A -> A -> A)
    (f_mor: forall x1 y1, eqv x1 y1 ->
              forall x2 y2, eqv x2 y2 ->
              eqv (f x1 x2) (f y1 y2))
    (f_assoc: forall x y z : A, eqv (f x (f y z)) (f (f x y) z))
    (f_commut: forall x y : A, eqv (f x y) (f y x))
    (u: A)
    (u_unit: forall x, eqv (f u x) x)
    (g: Table.key -> elt -> A -> A)
    (g_eqv: forall k x a, eqv (g k x a) (f (lift k x) a))
    (tab: Table.t elt)
    (k: Table.key) (new oldnew : elt),
    eqv (f (lift k new) (match Table.find k tab with Some x => lift k x | None => u end)) (lift k oldnew) ->
    eqv (f (lift k new) (Table.fold g tab u)) (Table.fold g (Table.add k oldnew tab) u).
Proof.
intros.
pose proof relate_fold_add eqv_rel lift lift_prop f f_mor f_assoc f_commut u u_unit g g_eqv.
etransitivity.
apply f_mor.
reflexivity.
apply H0 with (k:=k).
rewrite f_assoc.
etransitivity.
apply f_mor.
apply H.
reflexivity.
rewrite H0 with (k:=k).
apply f_mor.
erewrite Table.find_1 by (apply Table.add_1; reflexivity).
reflexivity.
rewrite fold_add_ignore.
reflexivity.
intros.
destruct (Keys.eq_dec k k'); try contradiction.
auto.
Qed.

End FMapAVL_extra.

Module Demonstration.
Import ZArith.
Module Keys <: OrderedType.OrderedType.
Definition t := Z.
Definition cmp := Z.compare.
Definition lt := Z.lt.
Definition eq := Z.eq.
Lemma eq_refl: forall al, eq al al. exact (@eq_refl Z). Qed.
Lemma eq_sym : forall al bl, eq al bl -> eq bl al. exact (@eq_sym Z). Qed.
Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  exact (@eq_trans Z). Qed.
Definition lt_trans := Z.lt_trans.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
intros; intro. rewrite H0 in H. revert H. apply Z.lt_irrefl.
Qed.

Lemma cmp_antisym1: forall x y, cmp x y = Gt -> cmp y x = Lt.
Proof. intros. apply Zcompare_Gt_Lt_antisym; auto. Qed.
 
Definition compare ( x y : t) : OrderedType.Compare lt eq x y :=
match cmp x y as c0 return (cmp x y = c0 -> OrderedType.Compare lt eq x y) with
| Eq => fun H0 : cmp x y = Eq => OrderedType.EQ (Z.compare_eq _ _ H0)
| Lt => fun H0 : cmp x y = Lt => OrderedType.LT H0
| Gt => fun H0 : cmp x y = Gt => OrderedType.GT (cmp_antisym1 x y H0)
end (Logic.eq_refl _).

  Lemma eq_dec: forall x y, { eq x y } + { ~ eq x y }.
  Proof. apply Z.eq_dec. Qed.

 End Keys.

Module FM := FMapAVL_extra Keys.
Import FM.

Definition addup_table (tab: Table.t positive) :=
  Table.fold (fun k p i => Z.add (Z.pos p) i) tab Z0.

Definition add_to_table (k: Table.key) (p: positive) (tab: Table.t positive) :=
 match Table.find k tab with
 | Some x => Table.add k (p+x)%positive tab
 | None => Table.add k p tab
 end.

Lemma add_to_table_correct:
 forall k p tab,
  addup_table (add_to_table k p tab) = Z.add (addup_table tab) (Z.pos p).
Proof.
intros.
pose (lift (k: Table.key) p := Z.pos p).
pose (oldnew := Z.to_pos (lift k p + match Table.find (elt:=positive) k tab with
                | Some x => lift k x
                | None => 0
                end)).
pose proof relate_fold_add_alt Z.eq_equiv lift
   ltac:(intros; rewrite H; auto)
   Z.add
   ltac:(intros; subst; auto)
   Z.add_assoc Z.add_comm
   Z0
   Z.add_0_l
   (fun k p x => Z.add (lift k p) x)
   ltac:(intros; subst; reflexivity)
   tab k p oldnew.
unfold addup_table, add_to_table. 
set (f := fun (k : Table.key) (p : positive) (x : Z) => (lift k p + x)%Z) in *.
change (fun (_ : Table.key) (p1 : positive) (i : Z) => (Z.pos p1 + i)%Z) with f in *.
rewrite Z.add_comm.
change (Z.pos p) with (lift k p).
rewrite H; clear H.
f_equal.
destruct (Table.find k tab) eqn:?H; auto.
unfold oldnew.
set (b := match Table.find (elt:=positive) k tab with
                        | Some x => lift k x
                        | None => 0%Z
                        end).
assert (0 <= b)%Z.
subst b.
unfold lift.
destruct (Table.find (elt:=positive) k tab); simpl; Lia.lia.
unfold lift.
Lia.lia.
Qed.

End Demonstration.






















