Require Import Lra Lia Interval.Tactic.
Import Raux.
Require Import Flocq.IEEE754.Binary.

Import List ListNotations.
Import Tree. (* must import this _after_ List *)
Import Interval Private Interval_helper I2 IT2.IH I2.T Xreal Interval.Eval.Reify.

Import Basic.
Import Bool.

Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Definition ring_simp_Mul (e1 e2 : expr) :=
     match e1, e2 with
     | Econst (Int 1), _ =>
                Some e2
     | _, Econst (Int 1) =>
                Some e1
     | Econst (Bpow 1 0), _ =>
                Some e2
     | _, Econst (Bpow 1 0) =>
                Some e1
     | Econst (Int 0), _ =>
                Some e1
     | _, Econst (Int 0) =>
                Some e2
     | Ebinary Add e11 e12, Ebinary Add e21 e22 =>
          Some (Ebinary Add 
                (Ebinary Add (Ebinary Mul e11 e21) (Ebinary Mul e11 e22))
                (Ebinary Add (Ebinary Mul e12 e21) (Ebinary Mul e12 e22)))
     | Ebinary Add e11 e12,  _ =>
           Some (Ebinary Add (Ebinary Mul e11 e2) (Ebinary Mul e12 e2))
     | _, Ebinary Add e21 e22 =>
           Some (Ebinary Add (Ebinary Mul e1 e21) (Ebinary Mul e1 e22))
     | _, _ => None
     end.

Lemma ring_simp_Mul_correct:
  forall e1 e2 e env, 
    ring_simp_Mul e1 e2 = Some e ->
    eval e env = eval (Ebinary Mul e1 e2) env.
Proof.
intros.
symmetry.
destruct e1, e2; simpl in *;
repeat
(lazymatch goal with
| H: Some _ = Some _ |- _ => injection H; clear H; intro H; subst; simpl
| H: None = _ |- _ => discriminate H
| H: context [match ?x with _ => _ end] |- _ => destruct x; simpl in *
| |- context [bpow' 0 ?x] => is_var x; destruct x; simpl
 end;
 try ring).
Qed.

Definition add_assoc op e1 e2 :=
 match op, e2 with
 | Add, Ebinary Add e21 e22 => Some (Ebinary Add (Ebinary Add e1 e21) e22)
 | Add, Ebinary Sub e21 e22 =>  Some (Ebinary Sub (Ebinary Add e1 e21) e22)
 | Sub, Ebinary Add e21 e22 =>  Some (Ebinary Sub (Ebinary Sub e1 e21) e22)
 | Sub, Ebinary Sub e21 e22 => Some (Ebinary Add (Ebinary Sub e1 e21) e22)
 | _, _ => None
 end.

Definition add_assoc' op e1 e2 :=
 match add_assoc op e1 e2 with Some e => e | None => Ebinary op e1 e2 end.

Lemma add_assoc'_correct:
 forall op e1 e2 env, eval (add_assoc' op e1 e2) env = eval (Ebinary op e1 e2) env.
Proof.
intros.
unfold add_assoc', add_assoc.
destruct op; simpl; auto.
destruct e2; simpl; auto.
destruct b; simpl; auto.
ring.
ring.
destruct e2; simpl; auto.
destruct b; simpl; auto.
ring.
ring.
Qed.

Fixpoint ring_simp1 (e: expr) :=
 match e with
 | Evar _ => None
 | Econst _ => None
 | Eunary Sqr e1 => 
      match ring_simp1 e1 with
      | Some e1' => match ring_simp_Mul e1' e1' with
                             | Some e => Some e
                             | None => Some (Ebinary Mul e1' e1')
                             end
      | None => Some (Ebinary Mul e1 e1)
      end
 | Eunary op e1 => 
      match ring_simp1 e1 with
      | Some e1' => Some (Eunary op e1')
      | None => None
      end
 | Ebinary op e1 e2 =>
    match op, ring_simp1 e1, ring_simp1 e2 with
    | Mul, None, None => ring_simp_Mul e1 e2
    | _, None, None => add_assoc op e1 e2
    | Mul, Some e1', None =>
            match ring_simp_Mul e1' e2 with
            | Some e => Some e
            | None => Some (Ebinary Mul e1' e2)
            end
    | Mul, None, Some e2' =>
            match ring_simp_Mul e1 e2' with
            | Some e => Some e
            | None => Some (Ebinary Mul e1 e2')
            end
    | _, Some e1', Some e2' => Some (add_assoc' op e1' e2')
    | _, Some e1', None => Some (add_assoc' op e1' e2)
    | _, None, Some e2' => Some (add_assoc' op e1 e2')
    end
 end.

Lemma ring_simp1_correct:
  forall e e' env, 
    ring_simp1 e = Some e' ->
    eval e env = eval e' env.
Proof.
induction e; simpl; intros; try discriminate.
destruct (ring_simp1 e) eqn:?H; inversion H; clear H; subst; simpl; auto.
-
destruct u; inversion H2; clear H2; subst; simpl in *; try solve [f_equal; auto].
destruct (ring_simp_Mul e0 e0) eqn:?H; inversion H1; clear H1; subst.
rewrite (ring_simp_Mul_correct _ _ _ env H); simpl.
unfold Rsqr. f_equal; auto.
simpl. unfold Rsqr. f_equal; auto.
-
destruct u; inversion H2; clear H2; subst; simpl in *; try solve [f_equal; auto].
-
destruct b; auto;
destruct (ring_simp1 e1) eqn:?H; try discriminate H;
destruct (ring_simp1 e2) eqn:?H; try discriminate H;
inversion H; clear H; subst; simpl; f_equal; auto;
erewrite ?IHe1 by eauto; erewrite ?IHe2 by auto; clear IHe1 IHe2;
rewrite ?add_assoc'_correct;
auto.
  + destruct e2; try destruct b; inversion H3; clear H3; subst; auto; simpl; ring.
  + destruct e2; try destruct b; inversion H3; clear H3; subst; auto; simpl; ring.
 +
  destruct (ring_simp_Mul e e2) eqn:?H; inversion H3; clear H3; subst.
  apply (ring_simp_Mul_correct _ _ _ env) in H; simpl in H; rewrite H; auto.
  simpl; auto.
 +
  destruct (ring_simp_Mul e1 e) eqn:?H; inversion H3; clear H3; subst.
  apply (ring_simp_Mul_correct _ _ _ env) in H; simpl in H; rewrite H; auto.
  simpl; auto.
 +
  apply (ring_simp_Mul_correct _ _ _ env) in H3; simpl in H3; rewrite H3; auto.
Qed.

Fixpoint ring_simp n e :=
 match n with
 | O => e
 | S n' => match ring_simp1 e with
               | Some e' => ring_simp n' e'
               | None => e
               end
 end.

Lemma ring_simp_correct:
  forall n e env, 
    eval e env = eval (ring_simp n e) env.
Proof.
induction n; simpl; intros; auto.
destruct (ring_simp1 e) eqn:?H; auto.
rewrite (ring_simp1_correct _ _ env H).
auto.
Qed.

Ltac simple_reify :=
match goal with
 |- Rabs ?t <= ?r =>
  let vars := get_vars t (@nil R) in
  let expr1 := reify t vars in
  let expr := fresh "__expr" in 
  pose (expr := expr1);
  change t with (eval expr vars);
find_hyps vars;
  let __vars := fresh "__vars" in set (__vars := vars) in *
end.

Ltac reified_ring_simplify e :=
 match goal with |- context [eval e ?vars] =>
   let H := fresh in let e1 := fresh e in
  assert (H :=ring_simp_correct 100 e vars);
  set (e1 := ring_simp 100 e) in H; 
  hnf in e1; cbv [add_assoc' add_assoc] in e1;
  rewrite H; clear H; try clear e
 end.


Ltac unfold_eval_hyps :=
 match goal with |- context [eval ?e _] => try unfold e; try clear e end;
 match goal with |- eval_hyps ?h ?v ?p =>
    try unfold h; try clear h;
    try unfold v; try clear v;
    try unfold p; try clear p
  end;
 cbv [eval_hyps eval_hyps_aux eval_hyp 
        add_assoc' add_assoc
        eval nullary_real unary_real binary_real]; 
  intros; simpl nth.

Definition fint := Float.f_interval F.type.


Definition decent_interval (f: fint) :=
 match f with
 | Float.Ibnd l u => F.real l && F.real u
 | _ => false
 end.

Fixpoint b_expr0 (e: expr) : fint :=
match e with
| Evar _ => Float.Inan
| Econst (Int n) => fromZ p52 n
| Econst (Bpow 2 n) => I.power_int p52 (fromZ p52 2) n
| Eunary Neg e' =>  neg (b_expr0 e')
| Eunary Abs e' => abs (b_expr0 e')
| Eunary Inv e' => let f := b_expr0 e' in
                            if decent_interval f then inv p52 (b_expr0 e') else Float.Inan
| Eunary (PowerInt i) e' => let f := b_expr0 e' in
                                        if decent_interval f then I.power_int p52 f i else Float.Inan
| Ebinary Mul e1 e2 => let f1 := b_expr0 e1 in let f2 := b_expr0 e2 in
                                      if decent_interval f1 && decent_interval f2 
                                      then mul p52 (b_expr0 e1) (b_expr0 e2)
                                      else Float.Inan
| _ => Float.Inan
end.

Definition fixup_fint (x: fint) : fint :=
 match x with
 | Float.Ibnd lo hi => if F.real lo && F.real hi then x else Float.Inan 
 | _ => x
 end.

Lemma classify_neg:
 forall l, F.classify (F.neg l) = 
          match F.classify l with
          | Sig.Fminfty => Sig.Fpinfty
          | Sig.Fpinfty => Sig.Fminfty
          | c => c
          end.
Proof.
intros.
pose proof (F.neg_correct l).
destruct (F.classify l) eqn:?H; auto.
unfold F.toX in H.
pose proof (F.classify_correct l).
pose proof (F.classify_correct (F.neg l)).
rewrite F'.real_neg in H2.
rewrite H1 in H2; clear H1.
rewrite H0 in H2.
destruct (F.classify (F.neg l)); auto; discriminate.
Qed.

Lemma toR_neg:
 forall u, F.real u = true -> F.toR (F.neg u) = - (F.toR u).
Proof.
intros.
unfold F.toR.
unfold proj_val.
rewrite I2.F'.neg_correct.
destruct (F.toX u); simpl; auto.
lra.
Qed.


Lemma toX_Xreal_real:
 forall x y, F.toX x = Xreal y -> F.real x = true.
Proof.
intros.
unfold F.real.
unfold F.toX, FtoX, F.toF in *.
rewrite FloatAxioms.classify_spec.
destruct (FloatOps.Prim2SF x); try destruct s; auto; inversion H; clear H; subst; simpl; auto;
destruct (match SpecFloat.digits2_pos m with
      | 53%positive => true
      | _ => false
      end); auto.
Qed.

Lemma fixup_fint_abs_correct:
 forall l u x, 
  match fixup_fint (Float.Ibnd l u) with
  | Float.Inan => True
  | Float.Ibnd lo hi => F.toR lo <= x <= F.toR hi
  end ->
 match fixup_fint (abs (Float.Ibnd l u)) with
 | Float.Inan => True
 | Float.Ibnd lo hi => F.toR lo <= unary_real Abs x <= F.toR hi
 end.
Proof.
intros.
simpl in H.
unfold unary_real.
simpl in *. unfold sign_large_.
rewrite (F.classify_correct l), (F.classify_correct u) in H.
rewrite (F.cmp_correct l F.zero), (F.cmp_correct u F.zero).
rewrite F'.classify_zero.
destruct (F.classify l) eqn:Hl,  (F.classify u) eqn:Hu; simpl in H;
try solve [
  simpl;
  try (destruct (Xcmp _ _); simpl);
  rewrite ?F'.real_neg,
   ?(F.classify_correct l), ?Hl,
   ?(F.classify_correct u), ?Hu; simpl; auto;
match goal with |- context [F.real (F.max ?a ?b)] =>
  let HM := fresh "HM" in assert (HM := F.max_correct a b);
  rewrite ?classify_neg, ?Hl, ?Hu in HM;
  rewrite F.classify_correct, HM; simpl; auto
end].
unfold Xcmp.
destruct (F.toX l) eqn:Hl1. {
  elimtype False; clear - Hl Hl1.
  unfold F.toX in *.
  unfold F.toF in *.
  unfold F.classify in *.
  rewrite FloatAxioms.classify_spec in Hl.
  destruct (FloatOps.Prim2SF l); try destruct s; simpl in *; try discriminate.
}
destruct (F.toX u) eqn:Hu1. {
  elimtype False; clear - Hu Hu1.
  unfold F.toX in *.
  unfold F.toF in *.
  unfold F.classify in *.
  rewrite FloatAxioms.classify_spec in Hu.
  destruct (FloatOps.Prim2SF u); try destruct s; simpl in *; try discriminate.
}
rewrite F.zero_correct.
rewrite F'.real_correct in Hl1, Hu1 by (rewrite F.classify_correct, ?Hl, ?Hu; auto).
inversion Hl1; clear Hl1; subst.
inversion Hu1; clear Hu1; subst.
change Tactic_float.Float.toR with F.toR.
assert (H2l := Rcompare_spec (F.toR l) 0).
assert (H2u := Rcompare_spec (F.toR u) 0).
inversion H2l; clear H2l;
inversion H2u; clear H2u; subst;
simpl; clear H0 H2;
try (rewrite (F.classify_correct (F.neg u)), classify_neg, Hu);
try (rewrite (F.classify_correct (F.neg l)), classify_neg, Hl);
try (rewrite (F.classify_correct l), Hl);
try (rewrite (F.classify_correct u), Hu);
simpl; auto;
rewrite ?toR_neg by (rewrite F.classify_correct, Hu; auto);
rewrite ?toR_neg by (rewrite F.classify_correct, Hl; auto);
try solve [unfold Rabs; destruct (Rcase_abs _); lra].
pose proof (F.max_correct (F.neg l) u).
rewrite classify_neg, Hl,Hu in H0.
rewrite (F'.real_correct (F.neg l)) in H0 by (rewrite F'.real_neg, F.classify_correct, Hl; auto).
rewrite (F'.real_correct u) in H0 by (rewrite F.classify_correct, Hu; auto).
simpl in H0.
rewrite (toX_Xreal_real _ _ H0).
unfold F.toR.
rewrite H0.
simpl.
change Tactic_float.Float.toR with F.toR.
rewrite ?toR_neg by (rewrite F.classify_correct, Hl; auto).
unfold Rabs, Rmax.
destruct (Rcase_abs _), (Rle_dec _ _); try lra.
rewrite H1 in *. rewrite H3 in *.
assert (x=0) by lra.
subst.
rewrite Rabs_R0.
change (F.toR F.zero) with 0.
lra.
Qed.


Lemma b_expr0_inv:
 forall l u x, 
    match (if F.real l && F.real u then Float.Ibnd l u else Float.Inan) with
      | Float.Inan => True
      | Float.Ibnd lo hi => F.toR lo <= x <= F.toR hi
      end ->
    contains (convert (div p52 (fromZ p52 1) (if F.real l && F.real u then Float.Ibnd l u else Float.Inan))) (Xreal (1 / x)).
Proof.
intros.
set (xx := if F.real l && F.real u then Float.Ibnd l u else Float.Inan) in *.
pose proof J.div_correct p52 (fromZ p52 1) xx 1 x.
match type of H0 with _ -> _ -> ?A => assert A; [apply H0 | ]; clear H0 end.
apply fromZ_correct.
subst xx.
destruct (F.real l) eqn:?H, (F.real u) eqn:?H; simpl in *; auto.
rewrite F'.valid_lb_real by auto.
rewrite F'.valid_ub_real by auto.
simpl.
rewrite F.real_correct in *.
unfold F.toR in *.
destruct (F.toX l) eqn:?H; try discriminate.
destruct (F.toX u) eqn:?H; try discriminate.
simpl in *. auto.
clear - H1.
subst xx.
red in H1.
simpl in H1.
auto.
Qed.

Lemma inv_div1:
  forall x, 
   decent_interval x = true -> 
   inv p52 x = div p52 (fromZ p52 1) x.
Proof.
intros.
unfold inv, div.
change (fromZ p52 1) with (Float.Ibnd I.c1 I.c1).
cbv iota.
change (sign_strict_ I.c1 I.c1) with Xgt.
destruct x; auto.
simpl in H. rewrite andb_true_iff in H. destruct H.
unfold Fdivz_DN, Fdivz_UP.
rewrite H, H0.
auto.
Qed.

Lemma b_expr0_correct:
  forall e,
 match fixup_fint (b_expr0 e) with
 | Float.Ibnd lo hi => F.toR lo <= eval e nil <= F.toR hi
 | Float.Inan => True
 end.
Proof.
induction e; simpl; auto.
-
destruct n; simpl; auto.
 + 
  destruct (F.real _) eqn:?H; [ | simpl; auto].
  destruct (F.real (F.fromZ_UP _ _)) eqn:?H; [ | simpl; auto].
  simpl.
  destruct (F.fromZ_DN_correct p52 n) as [_ ?].
  destruct (F.fromZ_UP_correct p52 n) as [_ ?].
  set (lo := F.fromZ_DN p52 n) in *; clearbody lo.
  set (hi := F.fromZ_UP p52 n) in *; clearbody hi.
  pose proof (le_contains _ _ _ H1 H2). clear H1 H2. 
  destruct H3.
  unfold F.toR, proj_val.
  rewrite I.F.real_correct in H,H0.
  change I.F.toX with F.toX in *.
  destruct (F.toX lo); try discriminate.
  destruct (F.toX hi); try discriminate.
  lra.
 +
   destruct r; simpl; auto.
   destruct p; simpl; auto.
   destruct p; simpl; auto.
   pose proof (I.power_int_correct p52 n (fromZ p52 2) (Xreal 2) (fromZ_correct _ 2)).
   simpl in H.
   destruct (I.power_int p52 (fromZ p52 2) n); simpl in *; auto.
   destruct (F.real l) eqn:?H; [ | simpl; auto].
   destruct (F.real u) eqn:?H; [ | simpl; auto].
   simpl.
   rewrite (F'.valid_lb_real _ H0) in H.
   rewrite (F'.valid_ub_real _ H1) in H.
   simpl in H.
   destruct (Xpower_int' 2 n) eqn:?H; try contradiction.
  rewrite I.F.real_correct in H0,H1.
  change I.F.toX with F.toX in *.
  unfold F.toR, proj_val.
  destruct (F.toX l); try discriminate.
  destruct (F.toX u); try discriminate.
  replace (bpow' 2 n) with r; auto.
  clear - H2.
  unfold Xpower_int', bpow' in *.
  destruct n; [ | | rewrite is_zero_false in H2 by lra];
  simpl in H2; injection H2; clear H2; intro H2; subst.
  auto. 
  rewrite Zpower_pos_powerRZ; rewrite pow_powerRZ; f_equal; lia.
  f_equal.
  rewrite Zpower_pos_powerRZ; rewrite pow_powerRZ; f_equal; lia.
-
  destruct u; try solve [simpl; auto].
 + destruct (b_expr0 e); simpl in *; auto.
   rewrite !F'.real_neg.
   change    Tactic_float.Float.real with F.real.
   destruct (F.real u) eqn:?H; [ | simpl; auto].
   destruct (F.real l) eqn:?H; [ | simpl; auto].
   simpl in *.
   pose proof (F'.neg_correct l).
   pose proof (F'.neg_correct u).
   change Tactic_float.Float.toX with F.toX in *.
   change    Tactic_float.Float.neg with F.neg in *.
   unfold F.toR in *. rewrite H1, H2.
  rewrite I.F.real_correct in H,H0.
  change I.F.toX with F.toX in *.
  destruct (F.toX l); try discriminate.
  destruct (F.toX u); try discriminate.
  simpl in *. lra.
 + destruct (b_expr0 e); auto.
   apply fixup_fint_abs_correct; auto.
 + destruct (b_expr0 e); auto.
     set (x := eval e nil) in *. clearbody x; clear e.
     destruct (decent_interval _) eqn:?H; [ | simpl; auto].
     simpl in H. rewrite andb_true_iff in H. destruct H.
     simpl in IHe. rewrite H, H0 in IHe. simpl in IHe.
     rewrite inv_div1 by (simpl; rewrite H, H0; auto).
     pose proof J.div_correct p52 (fromZ p52 1) (Float.Ibnd l u) 1 x.
     match type of H1 with _ -> _ -> ?A => assert A; [apply H1 | ]; clear H1 end.
     apply fromZ_correct.
     hnf; simpl.
     rewrite F'.valid_lb_real by auto.
     rewrite F'.valid_ub_real by auto.
     simpl.
     rewrite F.real_correct in *.
     unfold F.toR in *.
     destruct (F.toX l) eqn:?H; try discriminate.
     destruct (F.toX u) eqn:?H; try discriminate.
     simpl in *. auto.
     change I.div with div in H2.
     set (d := div _ _ _) in *. clearbody d.
     destruct d; simpl in *; auto.
     destruct (F.real l0) eqn:?H; simpl; auto.
     destruct (F.real u0) eqn:?H; simpl; auto.
     rewrite F'.valid_lb_real in H2 by auto.
     rewrite F'.valid_ub_real in H2 by auto. simpl in H2.
     unfold F.toR. rewrite F.real_correct in H1, H3.
     destruct (F.toX l0); try discriminate.
     destruct (F.toX u0); try discriminate.
     unfold Rdiv in H2; rewrite Rmult_1_l in H2.
     simpl; auto.
 + destruct (b_expr0 e); simpl in *; auto.
     destruct (F.real l) eqn:?H; simpl; auto.
     destruct (F.real u) eqn:?H; simpl; auto.
     simpl in IHe.   
     set (x := eval e nil) in *; clearbody x; clear e.
     pose proof (I.power_int_correct p52 n (Float.Ibnd l u) (Xreal x)).
     cbv beta in H1.
     match type of H1 with ?A -> _ => assert A end. {
       red. simpl.
       rewrite F'.valid_lb_real by auto.
       rewrite F'.valid_ub_real by auto.
       simpl.
       unfold F.toR in IHe.
     rewrite F.real_correct in *.
     destruct (F.toX l) eqn:?H; try discriminate.
     destruct (F.toX u) eqn:?H; try discriminate. apply IHe.
    }
    apply H1 in H2; clear H1.
    red in H2. destruct (I.power_int p52 (Float.Ibnd l u) n); simpl in *; auto.
    destruct (F.real l0) eqn:?H; simpl; auto.
    destruct (F.real u0) eqn:?H; simpl; auto.
       rewrite F'.valid_lb_real in H2 by auto.
       rewrite F'.valid_ub_real in H2 by auto.
       simpl in H2.
      destruct (Xpower_int' x n) eqn:?H; try contradiction.
      unfold F.toR.
     rewrite F.real_correct in H1,H3.
     destruct (F.toX l0); try discriminate.
     destruct (F.toX u0); try discriminate.
     simpl.
    destruct n; simpl in *. inversion H4; subst; auto.
    inversion H4; subst; auto.
    destruct (is_zero x); inversion H4; subst; auto.
- destruct b; simpl; auto.
   destruct (b_expr0 e1); try solve [simpl in *; auto].
   simpl in IHe1.
   unfold decent_interval at 1.
   destruct (F.real l) eqn:?H; [ | simpl; auto].
   destruct (F.real u) eqn:?H; [ | simpl; auto].
   destruct (b_expr0 e2); try solve [simpl in *; auto].
   simpl in IHe2.
   unfold decent_interval at 1.
   destruct (F.real l0) eqn:?H; [ | simpl; auto].
   destruct (F.real u0) eqn:?H; [ | simpl; auto].
   pose proof (mul_correct p52 (Float.Ibnd l u) (Float.Ibnd l0 u0) (Xreal (eval e1 nil)) (Xreal (eval e2 nil))).
   simpl in IHe1, IHe2.
   set (x1 := eval e1 nil) in *; clearbody x1.
   set (x2 := eval e2 nil) in *; clearbody x2. clear e1 e2.
   set (m := mul _ _ _) in *. clearbody m.
   simpl.
    unfold F.toR in *.
   match type of H3 with _ -> _ -> ?A => assert A; [apply H3 | clear H3 ] end.
 + (* Mul *)
   hnf; simpl.
       rewrite F'.valid_lb_real by auto.
       rewrite F'.valid_ub_real by auto.
      simpl.
    rewrite F.real_correct in H, H0.
    destruct (F.toX l); try discriminate.
    destruct (F.toX u); try discriminate.
    apply IHe1.
  +
   hnf; simpl.
       rewrite F'.valid_lb_real by auto.
       rewrite F'.valid_ub_real by auto.
      simpl.    
    rewrite F.real_correct in H1, H2.
    destruct (F.toX l0); try discriminate.
    destruct (F.toX u0); try discriminate.
    apply IHe2.
  +
     hnf in H4; simpl in H4.
     destruct m; simpl in *; auto.
     destruct (F.real l1) eqn:?H; [ | simpl; auto].
     destruct (F.real u1) eqn:?H; [ | simpl; auto].
     simpl.
       rewrite F'.valid_lb_real in H4 by auto.
       rewrite F'.valid_ub_real in H4 by auto.
   simpl in H4.
    rewrite F.real_correct in H3, H5.
    destruct (F.toX l1); try discriminate.
    destruct (F.toX u1); try discriminate.
    simpl in *. auto.
Qed.

Definition fint_to_option (x: fint) : option F.type :=
 match x with
 | Float.Ibnd _ hi => Some hi
 | Float.Inan => None
 end.


Definition zero : F.type := F.fromZ_DN p52 0.

Definition hyps_to_interval : list hyp -> Float.f_interval F.type :=
    List.fold_right (fun h x => I.meet (IT2.IH.R.eval_hyp_bnd p52 h) x) Float.Inan.

Lemma hyps_to_interval_correct:
 forall (hs: list hyp) r, 
      Forall (fun h => eval_hyp h r) hs -> 
      contains (convert (hyps_to_interval hs)) (Xreal r).
Proof.
intros.
induction hs; [ apply I | ].
inversion H; clear H; subst.
simpl.
specialize (IHhs H3).
apply I.meet_correct; auto.
clear - H2.
apply (PT2.IH.R.eval_hyp_bnd_correct p52) in H2; auto.
Qed.

Definition b_hyps (h: list hyp) : option F.type :=
   let u := upper (abs (hyps_to_interval h))
   in if F.real u then Some u else None.
  
Lemma b_hyps_correct: forall hs x r,
  b_hyps hs = Some x ->
  Forall (fun h => eval_hyp h r) hs ->
  F.real x = true /\ Rabs r <= F.toR x.
Proof.
intros.
unfold b_hyps in H.
set (u := upper _) in H.
destruct (F.real u) eqn:?H; inversion H; clear H; subst.
split; auto.
apply (hyps_to_interval_correct hs r) in H0.
set (i := hyps_to_interval hs) in *.
clearbody i.
subst u.
destruct i; [ inversion H1 | ].
apply (I2.abs_correct (Float.Ibnd l u) (Xreal r)) in H0.
simpl Xabs in H0.
set (a := abs _) in *; clearbody a.
hnf in H0.
destruct a; try discriminate.
simpl in H1|-*.
simpl in H0.
destruct (F.valid_lb l0) eqn:?H; simpl in H0.
rewrite F'.valid_ub_real in H0 by auto.
destruct H0 as [_ ?].
pose proof (F.real_correct u0). rewrite H1 in H2. 
destruct (F.toX u0) eqn:?H; try discriminate.
rewrite F'.real_correct in H3 by auto.
inversion H3; clear H3; subst.
auto.
lra.
Qed.

Fixpoint fint_eval_expr (e: expr) (env: list fint) : fint :=
match e with
| Evar i => nth i env Float.Inan
| Econst (Int n) => fromZ p52 n
| Econst (Bpow 2 n) => power_int p52 (fromZ p52 2) n
| Eunary op e1 => 
     match fint_eval_expr e1 env with 
     | Float.Inan => Float.Inan
     | b1 => 
          match op with 
          | Inv => inv p52 b1
          | Neg => neg b1
          | Abs => abs b1
          | Sqr => sqr p52 b1
          | _ => Float.Inan
          end
     end
| Ebinary op e1 e2 =>
     match fint_eval_expr e1 env, fint_eval_expr e2 env with
     | Float.Inan, _ => Float.Inan
     | _, Float.Inan => Float.Inan
     | b1, b2 => 
           match op with
           | Mul => mul p52 b1 b2
           | Div => div p52 b1 b2
           | Add  => add p52 b1 b2
           | Sub  => sub p52 b1 b2
           end
     end
| _ => Float.Inan
end.

Definition b_constexpr e := fint_eval_expr e nil.

Lemma fint_eval_expr_correct:
 forall e fenv env, 
     Forall2 (fun i x => contains (convert i) (Xreal x)) fenv env ->
     contains (convert (fint_eval_expr e fenv)) (Xreal (eval e env)).
Proof.
intros.
induction e.
- simpl.
    revert n; induction H; intros; simpl. destruct n; simpl; auto.
    destruct n; simpl; auto.
- simpl; destruct n.
  + apply fromZ_correct.
  + destruct r; auto; try apply I.
      destruct p; auto; try apply I.
      destruct p; auto; try apply I.
      pose proof (power_int_correct p52 n (fromZ p52 2)  (Xreal 2) (fromZ_correct p52 2)).
      cbv beta iota in H.
      unfold nullary_real.
      replace (Xreal (bpow' 2 n)) with (Xpower_int (Xreal 2) n); auto; clear.
      simpl.
      unfold bpow', Xpower_int'.
      destruct n; auto. 
      f_equal. rewrite Zpower_pos_powerRZ.
      rewrite pow_powerRZ. f_equal. lia.
      unfold is_zero.
      rewrite Req_bool_false by lra. f_equal.
      f_equal. rewrite Zpower_pos_powerRZ.
      rewrite pow_powerRZ. f_equal. lia.
  + apply I.
- unfold fint_eval_expr; fold fint_eval_expr.
    destruct (fint_eval_expr e fenv). apply I.
    destruct u; try apply I.
  + (* neg *) 
     simpl eval. set (x := eval e env) in *; clearbody x; clear e env H.
     apply (neg_correct (Float.Ibnd l u0) (Xreal x)); auto.
  + (* abs *) 
     simpl eval. set (x := eval e env) in *; clearbody x; clear e env H.
     apply (abs_correct (Float.Ibnd l u0) (Xreal x)); auto.
  + (* inv *) 
     simpl eval. set (x := eval e env) in *; clearbody x; clear e env H.
     apply (J.inv_correct p52 (Float.Ibnd l u0) x IHe).
  + (* sqr *) 
     simpl eval. set (x := eval e env) in *; clearbody x; clear e env H.
     apply (sqr_correct p52 (Float.Ibnd l u0) (Xreal x)); auto.
-
    unfold fint_eval_expr; fold fint_eval_expr.
    destruct (fint_eval_expr e1 fenv); auto.
    destruct (fint_eval_expr e2 fenv); auto.
    simpl eval.
    set (x1 := eval e1 env) in *; set (x2 := eval e2 env) in *; clearbody x1 x2.
    clear e1 e2 env H.
    unfold binary_real; destruct b.
  + (* add *) 
     apply (add_correct p52 (Float.Ibnd l u) (Float.Ibnd l0 u0) _ _ IHe1 IHe2).
  + (* sub *)
     apply (sub_correct p52 (Float.Ibnd l u) (Float.Ibnd l0 u0) _ _ IHe1 IHe2).
  + (* mul *)
     apply (mul_correct p52 (Float.Ibnd l u) (Float.Ibnd l0 u0) _ _ IHe1 IHe2).
  + (* div *) 
     pose proof (J.div_correct p52 (Float.Ibnd l u) (Float.Ibnd l0 u0) _ _ IHe1 IHe2).
     unfold Xbind2 in H. unfold Xdiv' in H.
     destruct (is_zero x2) eqn:?H; auto.
Qed.

Lemma b_constexpr_correct:
 forall e, contains (convert (b_constexpr e)) (Xreal (eval e nil)).
Proof.
intros.
apply (fint_eval_expr_correct e nil nil).
constructor.
Qed.

Definition check_bound (b: option F.type) (r: R) := 
        match b with
        | Some u => F.real u = true /\ Rabs r <= F.toR u
        | None => True
        end.

Fixpoint b_expr (e: expr) (hyps: list (option F.type)): option F.type :=
match b_constexpr e with
| Float.Ibnd lo hi => if F.real lo && F.real hi then Some (F.max (F.abs lo) (F.abs hi)) else None
| Float.Inan =>
match e with
| Evar i => nth i hyps None
| Eunary Neg e' =>  b_expr e' hyps
| Eunary Abs e' => b_expr e' hyps
| Eunary (PowerInt (Z.pos p)) e' => match b_expr e' hyps with
                             | Some x => let y := I.Fpower_pos_UP p52 x p
                                                  in if F.real y then Some y else None
                             | _ => None
                             end
| Ebinary Mul e1 e2 => match b_expr e1 hyps, b_expr e2 hyps with
                              | Some x1, Some x2 => let y := F.mul_UP p52 x1 x2
                                                        in if F.real y then Some y else None
                              | _, _ => None
                              end
| _ => None
end end.

Lemma Freal_abs: 
  forall x, F.real x = true -> F.real (F.abs x) = true.
Proof.
intros.
pose proof F.abs_correct x.
rewrite F.real_correct in H.
destruct (F.toX x); try discriminate; simpl in *.
destruct H0 as [? _].
rewrite F.real_correct. rewrite H0.
auto.
Qed.

Lemma Fmax_real: forall a b, F.real a = true -> F.real b = true -> F.real (F.max a b) = true.
Proof.
intros.
pose proof F.max_correct a b.
pose proof H; pose proof H0.
rewrite F.classify_correct in H,H0.
destruct (F.classify a); try discriminate.
destruct (F.classify b); try discriminate.
rewrite F.real_correct in *.
destruct (F.toX a); try discriminate.
destruct (F.toX b); try discriminate.
simpl in *.
rewrite H1; auto.
Qed.

Lemma bconstexpr_correct':
  forall e l u x vars, b_constexpr e = Float.Ibnd l u ->
      (if F.real l && F.real u then Some (F.max (F.abs l) (F.abs u)) else None) = Some x ->
      F.real x = true /\ Rabs (eval e vars) <= F.toR x.
Proof.
intros.
destruct (F.real l) eqn:?H; try discriminate.
destruct (F.real u) eqn:?H; try discriminate.
inversion H0; clear H0; subst.
split. apply Fmax_real; apply Freal_abs; auto.
pose proof (b_constexpr_correct e).
replace (eval e vars) with (eval e nil).
2: { clear - H.
      unfold b_constexpr in H.
      revert l u H; induction e; simpl; intros; auto.
      destruct n; discriminate.
      destruct (fint_eval_expr e nil) eqn:?H;try discriminate.
      destruct u; try discriminate;
      rewrite (IHe _ _  (eq_refl _)); auto.
      destruct (fint_eval_expr e1 nil) eqn:?H;try discriminate.
      destruct (fint_eval_expr e2 nil) eqn:?H;try discriminate.
      rewrite (IHe1 _ _ (eq_refl _)); auto.
      rewrite (IHe2 _ _ (eq_refl _)); auto.
}
rewrite H in H0; clear H.
set (r := eval e  nil) in *; clearbody r. clear e.
hnf in H0. simpl in H0.
rewrite F'.valid_lb_real  in H0 by auto.
rewrite F'.valid_ub_real  in H0 by auto.
simpl in H0.
pose proof (Freal_abs _ H1).
pose proof (Freal_abs _ H2).
pose proof (F.max_correct (F.abs l) (F.abs u)).
pose proof H; pose proof H3.
rewrite F.classify_correct in H, H3.
destruct (F.classify _); try discriminate.
destruct (F.classify _); try discriminate.
unfold F.toR.
rewrite H4. clear H4.
destruct H0.
destruct (F.abs_correct l) as [? _].
destruct (F.abs_correct u) as [? _].
rewrite F.real_correct in H1, H2.
destruct (F.toX l) eqn:?H; try discriminate.
destruct (F.toX u) eqn:?H; try discriminate.
rewrite F.real_correct in H5, H6.
destruct (F.toX (F.abs l)) eqn:?H; try discriminate.
destruct (F.toX (F.abs u)) eqn:?H; try discriminate.
simpl.
simpl in H7,H8.
inversion H7. inversion H8. subst.
clear - H0 H4.
unfold Rabs, Rmax.
repeat destruct (Rcase_abs _); destruct (Rle_dec _ _); lra.
Qed.

Lemma b_expr_correct:
  forall hyps vars e x,
    Forall2 check_bound hyps vars ->
    b_expr e hyps = Some x -> 
    F.real x = true /\ Rabs (eval e vars) <= F.toR x.
Proof.
intros.
revert x H0; induction e; unfold b_expr; fold b_expr; intros.
- (* var case *)
unfold b_constexpr in H0.
simpl in H0.
assert (nth n hyps None = Some x) by (destruct n; auto); clear H0.
revert n H1; induction H; intros.
destruct n; inversion H1.
destruct n.
simpl in H1. subst x0.
auto.
simpl.
apply IHForall2. auto.
- (* const case *)
pose proof (b_constexpr_correct (Econst n)).
simpl.
simpl eval in H1.
destruct (b_constexpr (Econst n)) eqn:?. discriminate.
apply (bconstexpr_correct' _ _ _ x vars Heqf H0).
- (* unary case *)
  destruct (b_constexpr (Eunary u e)) eqn:?H. 
  + destruct u; try discriminate.
    * apply IHe in H0. clear - H0.  simpl. rewrite Rabs_Ropp; auto. 
    * apply IHe in H0. clear - H0.  simpl.  rewrite Rabs_Rabsolu; auto.
    * destruct n; try discriminate.
       destruct (b_expr e hyps) eqn:?H; try discriminate.
       destruct (F.real (I.Fpower_pos_UP p52 t p)) eqn:?H; inversion H0; clear H0; subst.
       specialize (IHe _ (eq_refl _)). destruct IHe as [Ht IHe].
       split; auto.
       clear - H3 Ht IHe. simpl. set (i := eval e vars) in *; clearbody i.
       rewrite <- RPow_abs.
       pose proof Ht.
       rewrite F.real_correct in H. unfold F.toR in IHe.
       destruct (F.toX t) eqn:?H; inversion H; clear H; subst.
       simpl in IHe.
       pose proof (I.Fpower_pos_up_correct p52 t p).
       rewrite H0 in H.
       destruct H. apply F'.valid_ub_real; auto.
       simpl. clear - IHe. unfold Rabs in IHe. destruct (Rcase_abs _) in IHe;  lra.
       set (y := I.Fpower_pos_UP _ _ _) in *; clearbody y.
       red in H1.
       rewrite F.real_correct in H3.
       unfold F.toR.
       destruct (F.toX y); try discriminate.
       simpl in H1. simpl.
       eapply Rle_trans; try apply H1.
       apply pow_maj_Rabs. rewrite Rabs_Rabsolu. auto.
   + 
      apply (bconstexpr_correct' _ _ _ x vars H1 H0).
- (* binary case *)
  destruct (b_constexpr (Ebinary b e1 e2)) eqn:?H.
  + destruct b; try discriminate.
     destruct (b_expr e1 hyps) eqn:?H; try discriminate.
     destruct (b_expr e2 hyps) eqn:?H; try discriminate.
     specialize (IHe1 _ (eq_refl _)); destruct IHe1.
     specialize (IHe2 _ (eq_refl _)); destruct IHe2.
     simpl.
     destruct (F.real (F.mul_UP p52 t t0)) eqn:?H; inversion H0; clear H0; subst.
     clear H1. split; auto.
     rewrite Rabs_mult.
     eapply Rle_trans.
     apply Rmult_le_compat.
     apply Rabs_pos.
     apply Rabs_pos. eassumption. eassumption.
     destruct (F.mul_UP_correct p52 t t0).
     left. split.
     split. apply F'.valid_ub_real; auto.
     unfold F.toR in H5. rewrite F.real_correct in H4. destruct (F.toX t); try discriminate.
     simpl in H5. pose proof (Rabs_pos (eval e1 vars)); lra.
     split. apply F'.valid_ub_real; auto.
     unfold F.toR in H7. rewrite F.real_correct in H6. destruct (F.toX t0); try discriminate.
     simpl in H7. pose proof (Rabs_pos (eval e2 vars)); lra.
     unfold Xbind2 in H1.
     red in H1. unfold F.toR. rewrite F.real_correct in H8.
     destruct (F.toX (F.mul_UP p52 t t0)); try discriminate.
     rewrite F.real_correct in H4. destruct (F.toX t); try discriminate.
     rewrite F.real_correct in H6. destruct (F.toX t0); try discriminate. simpl. auto.
  +
      apply (bconstexpr_correct' _ _ _ x vars H1 H0).
Qed.

Definition eval_hyps1 (hyps: list hyp) (r: R) :=
   Forall (fun h => eval_hyp h r) hyps.

Lemma eval_hyps_correct:
  forall hyps vars P, 
    length hyps = length vars ->
     (eval_hyps hyps vars P <->
       (Forall2 eval_hyps1 hyps vars -> P)).
Proof.
induction hyps; destruct vars; simpl; intros; try discriminate.
split; intros; auto.
injection H; clear H; intro.
specialize (IHhyps _ P  H).
split; intros; auto.
inversion H1; clear H1; subst.
apply IHhyps; auto.
set (Q := eval_hyps _ _ P) in *.
clearbody Q.
clear - H0 H5.
induction a; auto.
unfold eval_hyps1 in H5.
inversion H5; clear H5; subst.
eauto.
assert (eval_hyps1 a r -> Forall2 eval_hyps1 hyps vars -> P).
intros.
apply H0.
constructor; auto.
clear H0.
rewrite <- IHhyps in H1; clear IHhyps.
set (Q := eval_hyps _ _ P) in *.
clearbody Q.
clear - H H1.
induction a; auto.
apply H1.
constructor.
intro.
apply IHa.
intro.
apply H1.
constructor; auto.
Qed.

Definition zeroexpr := Econst (Int 0).

Definition infinity := PrimFloat.infinity.

Fixpoint prune (hyps: list (option F.type)) (e: expr) (cutoff: F.type) :
           expr * F.type :=
 match b_expr e hyps with 
 | Some b => if F'.le b cutoff then (zeroexpr, b) else (e,zero)
 | None =>
 match e with
 | Ebinary Add e1 e2 =>
  let (e1',b1) := prune hyps e1 cutoff in 
  let (e2',b2) := prune hyps e2 cutoff in 
  (match e1', e2'  with
   | Econst (Int 0), _ => e2'
   | _, Econst (Int 0) => e1'
   | _, _ => Ebinary Add e1' e2'
   end, if F.real b1 && F.real b2 then F.add_UP p52 b1 b2 else infinity)
 | Ebinary Sub e1 e2 =>
  let (e1',b1) := prune hyps e1 cutoff in 
  let (e2',b2) := prune hyps e2 cutoff in 
  (match e1', e2' with
   | Econst (Int 0), _ => Eunary Neg e2'
   | _, Econst (Int 0) => e1'
   | _, _ => Ebinary Sub e1' e2'
   end, if F.real b1 && F.real b2 then F.add_UP p52 b1 b2 else infinity)
 | _ => (e, zero)
 end
end.

Lemma FtoR_zero: F.toR zero = 0.
Proof.
unfold F.toR. change zero with F.zero. rewrite F.zero_correct. reflexivity.
Qed.

Lemma prune_correct:
  forall env e cutoff e1 slop,
  prune env e cutoff = (e1,slop) ->
  F.real slop = true ->
  forall (vars: list R),
   Forall2 check_bound env vars ->
   Rabs (eval e vars - eval e1 vars) <= F.toR slop.
Proof.
intros until 1.
intro Hslop.
revert e1 slop H Hslop.
 induction e; intros; unfold prune in H; fold prune in H;
 try solve [
  match type of H with context [b_expr ?e ?env] => destruct (b_expr e env) eqn:?H end;
    [destruct (F'.le t cutoff) eqn:?H; inversion H; clear H; subst;
     apply (b_expr_correct _ vars _ _ H0) in H1;
     [destruct H1; simpl in H1|-*; rewrite Rminus_0_r; auto
     | rewrite Rminus_eq_0, Rabs_R0, FtoR_zero; lra
     ]
    | inversion H; clear H; subst; rewrite Rminus_eq_0, Rabs_R0, FtoR_zero; lra
    ]].
(* binary case *)
 destruct (b_expr (Ebinary b e1 e2) env) eqn:?H.
-
 destruct (b_expr_correct env vars (Ebinary b e1 e2) _ H0 H1); clear H1.
 destruct (F'.le t cutoff) eqn:?H.
    inversion H; clear H; subst.
    simpl eval in *. rewrite Rminus_0_r. auto.
    inversion H; clear H; subst. rewrite Rminus_eq_0, FtoR_zero, Rabs_R0; lra.
-
     destruct (prune env e1 cutoff) as [e1' b1].
     destruct (prune env e2 cutoff) as [e2' b2].
     specialize (IHe1 _ _ (eq_refl _)).
     specialize (IHe2 _ _ (eq_refl _)).
   clear H1.
 destruct b.
 + (* Add *)
     injection H; clear H; intros H H'.
     subst slop.
     destruct (F.real b1) eqn:R1; try discriminate.
     destruct (F.real b2) eqn:R2; try discriminate. simpl in Hslop.
     specialize (IHe1 (eq_refl _) _ H0).
     specialize (IHe2 (eq_refl _) _ H0).
     simpl in *.
     destruct (F.add_UP_correct p52 b1 b2); auto.
         apply F'.valid_ub_real; auto.
         apply F'.valid_ub_real; auto.
     red in H1.
     unfold F.toR  in *.
     rewrite F.real_correct in R1,R2.
     destruct (F.toX b1); try discriminate.
     destruct (F.toX b2); try discriminate.
     rewrite F.real_correct in Hslop. destruct ( F.toX (F.add_UP p52 b1 b2)); try discriminate.
     simpl in *.
     subst e0; revert IHe1 IHe2.
     destruct e1' as [ | [ [ | | ] | | ] | | ] ;
     destruct e2' as [ | [ [ | | ] | | ] | | ] ;
     simpl;
     unfold Rabs; repeat destruct (Rcase_abs _); lra.
 + (* Sub *)
     injection H; clear H; intros H H'.
     subst slop.
     destruct (F.real b1) eqn:R1; try discriminate.
     destruct (F.real b2) eqn:R2; try discriminate. simpl in Hslop.
     specialize (IHe1 (eq_refl _) _ H0).
     specialize (IHe2 (eq_refl _) _ H0).
     simpl in *.
     destruct (F.add_UP_correct p52 b1 b2); auto.
         apply F'.valid_ub_real; auto.
         apply F'.valid_ub_real; auto.
     red in H1.
     unfold F.toR  in *.
     rewrite F.real_correct in R1,R2.
     destruct (F.toX b1); try discriminate.
     destruct (F.toX b2); try discriminate.
     rewrite F.real_correct in Hslop. destruct ( F.toX (F.add_UP p52 b1 b2)); try discriminate.
     simpl in *.
     subst e0; revert IHe1 IHe2.
     destruct e1' as [ | [ [ | | ] | | ] | | ] ;
     destruct e2' as [ | [ [ | | ] | | ] | | ] ;
     simpl;
     unfold Rabs; repeat destruct (Rcase_abs _); lra.
 + inversion H; clear H; subst. rewrite Rminus_eq_0, FtoR_zero, Rabs_R0; lra.
 + inversion H; clear H; subst. rewrite Rminus_eq_0, FtoR_zero, Rabs_R0; lra.
Qed.

Lemma prune_terms_correct:
 forall hyps e cutoff e1 slop, 
   prune (map b_hyps hyps) e cutoff = (e1,slop) ->
  F.real slop = true ->
   forall vars r, 
     length hyps = length vars ->
     eval_hyps hyps vars (Rabs (eval e1 vars) <= r - F.toR slop) ->
      eval_hyps hyps vars (Rabs (eval e vars) <= r).
Proof.
intros.
apply eval_hyps_correct ; auto.
intros.
apply eval_hyps_correct in H2; auto.
clear H1.
assert (Forall2 check_bound (map b_hyps hyps) vars). {
clear - H3.
induction H3.
constructor.
constructor; auto.
clear - H.
destruct (b_hyps x) eqn:?H; auto.
2: simpl; auto.
simpl.
eapply b_hyps_correct in H0.
apply H0.
clear - H.
induction x.
constructor.
unfold eval_hyps1 in H.
inversion H; clear H; subst.
constructor; auto.
} clear H3.
pose proof (prune_correct _ _ _ _ _ H H0 vars H1).
clear - H2 H3.
revert H2 H3.
unfold Rabs. repeat destruct (Rcase_abs _); intros; lra.
Qed.

Ltac prune_terms cutoff := 
 simple_reify;
 match goal with |- eval_hyps _ _ (Rabs (eval ?e _) <= _) => reified_ring_simplify e end;
 match goal with |- eval_hyps _ _ (Rabs (eval ?e _) <= _) => 
    eapply (prune_terms_correct _ _ cutoff);  [compute; reflexivity | reflexivity | reflexivity |  try clear e]
 end;
 unfold_eval_hyps.

Definition cutoff := Tactic_float.Float.scale (Tactic_float.Float.fromZ 1) (-40)%Z.

Lemma test1:
 forall 
 (e0 d e1 e2 d0 e3 v : R)
 (BOUND : -2 <= v <= 2)
 (x : R)
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
/ 4068160.
Proof.
intros.
prune_terms cutoff.
 match goal with |- Rabs ?a <= _ => field_simplify a end.
match goal with |- Rabs ?t <= ?r => interval_intro (Rabs t) as H99 end.
eapply Rle_trans; [ apply H99 | clear H99 ].
compute; lra.
Qed.


