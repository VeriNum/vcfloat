From MMaps Require MMaps AVLproofs.
From Coq Require Import Int Orders.

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

Module Raw := AVLproofs.AvlProofs Int.Z_as_Int Keys.
Module Table := Raw.Pack Keys Raw.

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
       (Table.fold (fun k' x a => 
                           match Keys.compare k k' with Eq => a 
                                 | _ => g k' x a end) tab u)).
Proof.
intros.
destruct tab.
unfold Table.fold, Table.find; simpl.
apply Raw.relate_fold_add; auto.
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
apply Raw.fold_add_ignore; auto.
Qed.

End FMapAVL_extra.




















