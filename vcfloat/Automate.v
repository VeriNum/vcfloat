(*  LGPL licensed; see ../LICENSE and, for historical notes, see ../OLD_LICENSE *)

(** Automate.v:  proof automation for "ftype" usage-style of VCFloat. *)
From Coq Require Import ZArith.
Require Import Flocq.IEEE754.Binary.
From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import Interval.Tactic.
Import Coq.Lists.List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Definition empty_collection: collection.
  (* don't make this an Instance unless the user explicitly chooses to *)
exists nil. hnf; intros. inversion H.
Defined.


(* The tactic  compute_every has a fast implementation,
  using Ltac2, and a slower implementation, just using Ltac.
 Here is the fast one: *)
Require vcfloat.compute_tactics_ltac2.
Ltac compute_every f := compute_tactics_ltac2.compute_every f.
(* But compute_every blows up on certain terms,  so these slightly
   slower ones can still be useful: *)
Ltac compute_every1 f :=
   let j := fresh "j" in repeat (set (j := f _); compute  in j; subst j).
Ltac compute_every2 f :=
   let j := fresh "j" in repeat (set (j := f _ _); compute  in j; subst j).
Ltac compute_every3 f :=
   let j := fresh "j" in repeat (set (j := f _ _ _); compute  in j; subst j).
Ltac compute_every4 f :=
   let j := fresh "j" in repeat (set (j := f _ _ _ _); compute  in j; subst j).
Ltac compute_every5 f :=
   let j := fresh "j" in repeat (set (j := f _ _ _ _ _); compute  in j; subst j).
Ltac compute_every6 f :=
   let j := fresh "j" in repeat (set (j := f _ _ _ _ _ _); compute  in j; subst j).

Definition generic_nan (prec emax : Z) :
      nan_pl prec 1 = true ->
       binary_float prec emax  :=
       B754_nan prec emax false 1.

Definition generic_nan64 :=
  generic_nan (fprec Tdouble) (femax Tdouble) (eq_refl _).

Import Zaux.

Ltac compute_B2R :=
 repeat (
 match goal with |- context [B2R ?a ?b ?c] =>
   lazymatch c with
   | b64_B754_finite _ _ _ _ => idtac
   | b64_B754_zero _ => idtac
   | b32_B754_finite _ _ _ _ => idtac
   | b32_B754_zero _ => idtac
  end;
 let x := constr:(B2R a b c) in
 let y := eval cbv beta iota zeta delta [
               FT2R b64_B754_finite B2R Defs.F2R Defs.Fnum Defs.Fexp
                 SpecFloat.cond_Zopp bpow radix2 radix_val
                 Z.pow_pos Pos.iter Z.mul Pos.mul] in x
 in lazymatch y with
    | Rmult ?u (Rinv ?v) => let z := constr:(Rdiv u v) in change x with z
    | _ => change x with y
    end
 end).

Record varinfo := {var_type: type; var_name: ident; var_lobound: R; var_hibound: R}.
Definition boundsmap := Maps.PTree.t varinfo.

Definition valmap_valid `{coll: collection} (vm: Maps.PTree.t (sigT ftype)) :=
 forall id ty, Maps.PTree.get id vm = Some ty -> incollection (projT1 ty).

Definition valmap `{coll: collection} := sig valmap_valid.

Definition ftype_of_val (v: sigT ftype) : type := projT1 v.
Definition fval_of_val (v: sigT ftype): ftype (ftype_of_val v) := projT2 v.

Definition type_hibound (t: type) :=
  bpow Zaux.radix2 (femax t) - bpow Zaux.radix2 (femax t - fprec t).

Definition trivbound_varinfo (t: type) (i: ident) : varinfo :=
  Build_varinfo t i (- type_hibound t) (type_hibound t).

Lemma trivbound_correct:
 forall (t: type) (x: ftype t),
 - type_hibound t <= FT2R x <= type_hibound t.
Proof.
intros.
assert (0 < type_hibound t). {
  unfold type_hibound.
  rewrite !bpow_powerRZ.
  pose proof (fprec_lt_femax t).
  pose proof (fprec_gt_0 t).
  red in H0.
  rewrite <- (Z2Nat.id (femax t - fprec t)) by lia.
  set (b := Z.to_nat _).
  rewrite <- (Z2Nat.id (femax t)) by lia.
  set (a := Z.to_nat _).
  rewrite <- !pow_powerRZ.
  simpl.
  assert (b<a)%nat by lia.
  assert (1<2) by lra.
  pose proof (Rlt_pow 2 b a) H2 H1.
  lra.
}
unfold FT2R.
destruct t as [? ? ? ? ? [|]]; simpl in *.
-
unfold type_hibound, FPCore.fprec in *; simpl in *.
apply nonstd_bounds.
-
destruct x; simpl; try lra.
pose proof (bounded_le_emax_minus_prec _ _ (fprec_gt_0 _) _ _ e0).
simpl.
change (bpow radix2 (FPCore.femax ?t) - _) with (type_hibound t) in H0.
pose proof (Float_prop.F2R_gt_0 Zaux.radix2 {| Defs.Fnum := Z.pos m; Defs.Fexp := e |})
   ltac:(simpl; lia).
destruct s; unfold SpecFloat.cond_Zopp.
rewrite Float_prop.F2R_Zopp.
lra.
lra.
Qed.

Definition boundsmap_denote `{coll: collection} (bm: boundsmap) (vm: valmap) : Prop :=
   forall i,
   match Maps.PTree.get i bm, Maps.PTree.get i (proj1_sig vm) with
   | Some {|var_type:=t; var_name:=i'; var_lobound:=lo; var_hibound:=hi|}, Some v =>
              i=i' /\ t = projT1 v /\
              is_finite (projT2 v) = true
               /\ lo <= FT2R (projT2 v) <= hi
   | None, None => True
   | _, _ => False
   end.

Definition boundsmap_denote_pred `{coll: collection} (vm: valmap) (ib: ident*varinfo) :=
 match ib with
  (i, {|var_type:=t; var_name:=i'; var_lobound:=lo; var_hibound:=hi|}) =>
         exists v,
         i=i' /\
         Maps.PTree.get i (proj1_sig vm) = Some (existT ftype t v) /\
         is_finite v = true /\ lo <= FT2R v <= hi
  end.

Lemma boundsmap_denote_e:
  forall `{coll: collection} bm vm, boundsmap_denote bm vm ->
 list_forall (boundsmap_denote_pred vm) (Maps.PTree.elements bm).
Proof.
intros.
red in H.
unfold boundsmap_denote_pred.
apply list_forall_spec.
intros [i [t i' lo hi]] ?.
apply Maps.PTree.elements_complete in H0.
specialize (H i). rewrite H0 in H.
destruct (Maps.PTree.get i (proj1_sig vm)) as [ [t' v] | ]; try contradiction.
simpl in *.
destruct H as [? [? [? ?]]].
subst.
exists v. auto.
Qed.

Lemma boundsmap_denote_i:
  forall `{coll: collection} bm vm,
 list_forall (boundsmap_denote_pred vm) (Maps.PTree.elements bm) ->
 list_forall (fun iv => match Maps.PTree.get (fst iv) bm with Some _ => True | _ => False end)
                   (Maps.PTree.elements (proj1_sig vm)) ->
 boundsmap_denote bm vm.
Proof.
intros.
rewrite list_forall_spec in H.
rewrite list_forall_spec in H0.
intro.
destruct (Maps.PTree.get i bm) as [[t i' lo hi]|] eqn:?H.
apply Maps.PTree.elements_correct in H1.
apply H in H1.
destruct H1 as [? [? [? [? ?]]]].
subst i'.
rewrite H2.
split; auto.
destruct (Maps.PTree.get i (proj1_sig vm)) eqn:?H; auto.
apply Maps.PTree.elements_correct in H2.
apply H0 in H2.
simpl in H2.
rewrite H1 in H2. auto.
Qed.

Ltac compute_PTree x :=
 match x with
 | Maps.PTree.Nodes ?y => let y' := compute_PTree y in constr:(Maps.PTree.Nodes y')
 | Maps.PTree.Empty => constr:(x)
 | Maps.PTree.Node001 ?y => let y' := compute_PTree y in constr:(Maps.PTree.Node001 y')
 | Maps.PTree.Node010 _ => constr:(x)
 | Maps.PTree.Node011 ?a ?y => let y' := compute_PTree y in constr:(Maps.PTree.Node011 a y')
 | Maps.PTree.Node100 ?y => let y' := compute_PTree y in constr:(Maps.PTree.Node100 y')
 | Maps.PTree.Node101 ?y ?z => let y' := compute_PTree y in
                                                 let z' := compute_PTree z in
                                                    constr:(Maps.PTree.Node101 y' z')
 | Maps.PTree.Node110 ?y ?a => let y' := compute_PTree y in constr:(Maps.PTree.Node110 y' a)
 | Maps.PTree.Node111 ?y ?a ?z => let y' := compute_PTree y in
                                                 let z' := compute_PTree z in
                                                    constr:(Maps.PTree.Node111 y' a z')
 | _ => let y := eval hnf in x in compute_PTree y
 end.

Definition boundsmap_of_list (vl: list varinfo) : boundsmap :=
  fold_left (fun m v => Maps.PTree.set (var_name v) v m) vl (Maps.PTree.empty _).


Definition valmap_of_list' (vl: list (ident * sigT ftype)) :=
  fold_left (fun m iv => let '(i,v) := iv in Maps.PTree.set i v m) vl (Maps.PTree.empty _).

Definition make_valmap `{coll: collection} (vm: Maps.PTree.t (sigT ftype))
      (VAL: valmap_valid vm) :=
 exist _ vm VAL.

Definition valmap_of_list `{coll: collection} (* obsolete? *)
     (vl: list (ident * sigT ftype)) VALID : valmap :=
  make_valmap (valmap_of_list' vl) VALID.

Fixpoint test_ptree' {T: Type} (P: T -> Prop) (t: Maps.PTree.tree' T) :=
 match t with
 | Maps.PTree.Node001 r => test_ptree' P r
 | Maps.PTree.Node010 x => P x
 | Maps.PTree.Node011 x r => P x /\ test_ptree' P r
 | Maps.PTree.Node100 l => test_ptree' P l
 | Maps.PTree.Node101 l r => test_ptree' P l /\ test_ptree' P r
 | Maps.PTree.Node110 l x => test_ptree' P l /\ P x
 | Maps.PTree.Node111 l x r => test_ptree' P l /\ P x /\ test_ptree' P r
 end.

Definition test_ptree {T: Type} (P: T -> Prop) (t: Maps.PTree.t T) :=
 match t with
 | Maps.PTree.Nodes t' => test_ptree' P t'
 | Maps.PTree.Empty => True
 end.

Lemma test_ptree_correct: forall (T: Type) (P: T -> Prop) (t: Maps.PTree.t T),
  test_ptree P t ->
   forall i x, Maps.PTree.get i t = Some x -> P x.
Proof.
intros ? ? ?.
unfold Maps.PTree.get.
destruct t; simpl in *.
discriminate.
induction t; simpl; intros; destruct i; simpl in *; eauto; try discriminate;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
eauto;
try solve [injection H0; intro; subst; auto].
Defined.


Lemma compute_valmap_valid `{coll: collection}:
 forall (vm: Maps.PTree.t (sigT ftype)),
 test_ptree (fun x => incollection (projT1 x)) vm ->
 valmap_valid vm.
Proof.
hnf; intros.
exact (test_ptree_correct _ _ _ H).
Defined.

(*

Lemma compute_valmap_valid `{coll: collection}:
 forall (vm: Maps.PTree.t (sigT ftype)),
 Forall (fun ix => incollection (projT1 (snd ix))) (Maps.PTree.elements vm) ->
 valmap_valid vm.
Proof.
intros.
red.
intros.
apply Maps.PTree.elements_correct in H0.
rewrite Forall_forall in H.
apply H in H0.
auto.
Qed.
*)

Ltac make_valmap_of_list vml :=
   lazymatch goal with |- valmap => idtac end;
   let z := compute_PTree (valmap_of_list' vml) in
   exists z;
   apply compute_valmap_valid;
   repeat apply conj; try apply I;
   cbv [test_ptree test_ptree']; prove_incollection.

Definition shiftmap := MSHIFT.

Definition is_standardb (t: type) : bool :=
 match nonstd t with Some _ => false | None => true end.

Definition typesize_eq_dec (t1 t2: type) :
   {(is_standardb t1, fprecp t1, femax t1)=(is_standardb t2, fprecp t2, femax t2)} +
   {(is_standardb t1, fprecp t1, femax t1)<>(is_standardb t2, fprecp t2, femax t2)}.
destruct (is_standardb t1), (is_standardb t2).
1,4: destruct (Pos.eq_dec (fprecp t1) (fprecp t2));
  [ destruct (Z.eq_dec (femax t1) (femax t2)) |];
  try (left; f_equal; [f_equal |]; assumption).
all: try (right; contradict n; injection n; auto).
all: right; intro; discriminate.
Defined.


Lemma incollection_eq: forall `{coll: collection} t1 t2,
  incollection t1 ->
  incollection t2 ->
  (is_standardb t1, fprecp t1, femax t1) = (is_standardb t2, fprecp t2, femax t2) ->
  t1=t2.
Proof.
intros.
destruct t1 as [? ? ? ? ? [|]], t2 as [? ? ? ? ? [|]];
simpl in *; try discriminate.
-
inversion H1; subst; auto.
destruct coll as [tl OK].
apply OK; auto.
-
inversion H1; clear H1; subst; auto.
clear H H0.
rewrite (Is_true_eq _ fprecp_not_one_bool0 fprecp_not_one_bool).
rewrite (Is_true_eq _ fprec_lt_femax_bool0 fprec_lt_femax_bool).
reflexivity.
Defined.

Definition env_ `{coll: collection} (tenv: valmap)
      ty (IN: incollection ty) (v: ident): ftype ty :=
  match
   Maps.PTree.get v (proj1_sig tenv) as o0
   return
     ((forall ty0 : {x : type & ftype x},
       o0 = Some ty0 -> incollection (projT1 ty0)) ->
      ftype ty)
 with
 | Some (existT _ x1 f) =>
      fun
         (v2 : forall ty0 : {x : type & ftype x},
               Some (existT ftype x1 f) = Some ty0 ->
               incollection (projT1 ty0)) =>
       match typesize_eq_dec ty x1 with
       | left e =>
            eq_rect ty
              (fun x2 : type => ftype x2 -> incollection x2 -> ftype ty)
              (fun (f0 : ftype ty) (_ : incollection ty) => f0)
              x1
              (incollection_eq ty x1 IN (v2 (existT ftype x1 f) eq_refl) e) f
              (v2 (existT ftype x1 f) eq_refl)
       | right _ => placeholder ty v
       end
 | None => fun _ => placeholder ty v
 end (proj2_sig tenv v).

(*
destruct tenv as [vm ?].
red in v0.
specialize (v0 v).
destruct (Maps.PTree.get v vm) as [[? ?] |].
specialize (v0 _ (eq_refl _)).
simpl in v0.
destruct (typesize_eq_dec ty x).
apply incollection_eq in e; auto.
subst x; apply f.
all: apply (placeholder ty v).
Defined.
*)
(*
Lemma env_get_type `{coll: collection}:
  forall (vm: valmap) ty i t v,
  incollection ty ->
  Maps.PTree.get i (proj1_sig vm) = Some (existT ftype t v) ->
  t=ty.
Proof.
intros.
destruct vm as [vm OK]; simpl in *.
destruct coll as [tl ?].
red in c.
red in OK.
specialize (OK _ _ H0).
simpl in OK.

red in OL
*)


(*

Lemma env_get `{coll: collection}:
  forall vm ty IN i,
  Maps.PTree.get i (proj1_sig vm) = Some (existT ftype ty (env_ vm ty IN i)).
Proof.
intros.
unfold env_.
destruct vm as [vm H].
simpl in *.
set (Hi := H i).
clearbody Hi.
clear H.
destruct (Maps.PTree.get _ _).
f_equal.
destruct s as [t v].
pose proof (Hi _ (eq_refl _)).
simpl in H.
destruct (typesize_eq_dec _ _).
unfold eq_rect.
destruct (incollection_eq _ _ _ _ _).
auto.
*)
(*
Lemma env_get `{coll: collection}:
  forall vm ty IN i t v,
  Maps.PTree.get i (proj1_sig vm) = Some (existT ftype t v) ->
  JMeq.JMeq (env_ vm ty IN i) v.
Proof.
intros.
unfold env_.
set (H2 := @proj2_sig (Maps.PTree.t {x : type & ftype x})
        (@valmap_valid coll) vm i).
clearbody H2.
destruct (Maps.PTree.get _ _).
inversion H; clear H; subst.
destruct (typesize_eq_dec _ _).
destruct (incollection_eq _ _ _ _ _).
simpl.
auto.
*)

Lemma placeholder_finite: forall ty i,
  is_finite (placeholder ty i) = true.
Proof.
intros.
 unfold placeholder. apply proj2_sig.
Qed.

Lemma finite_env `{coll: collection} (bmap: boundsmap) (vmap: valmap):
      boundsmap_denote bmap vmap ->
forall ty (IN: incollection ty) i, is_finite ((env_ vmap) ty IN i) = true.
Proof.
intros.
 specialize (H i).
 unfold env_.
 match goal with |- is_finite ((_ ?P)) = true =>
   set (H2 := P)
 end.
clearbody H2.
 destruct (Maps.PTree.get i bmap) as [[t i' lo hi]|],
    (Maps.PTree.get i (proj1_sig vmap)) as [[t' v]|] eqn:?; auto.
-
 destruct H as [? [? [??]]].
 simpl in H0, H1, H2.
 subst i' t'.
 destruct (typesize_eq_dec _ _).
 destruct (incollection_eq _ _ _ _ _).
 simpl.
 auto.
 apply placeholder_finite.
-
 apply placeholder_finite.
Qed.

Ltac unfold_fval :=
  cbv beta iota zeta delta [
      fop_of_binop fop_of_rounded_binop
      fop_of_unop fop_of_rounded_unop fop_of_exact_unop
      option_pair_of_options];
   repeat match goal with
  | |- context [binop_eqb ?a ?b] =>
    let u := constr:(binop_eqb a b) in
    let u := eval compute in u in
    change (binop_eqb a b) with u; cbv iota
  | |- context [binary_float_eqb ?a ?b] =>
    let u := constr:(binary_float_eqb a b) in
    let u := eval compute in u in
    change (binary_float_eqb a b) with u; cbv iota
  | |- context [to_inv_power_2 ?a] =>
    let u := constr:(to_inv_power_2 a) in
    let u := eval compute in u in
    change (to_inv_power_2 a) with u; cbv iota
  end;
   cbv beta iota zeta;
   repeat change (cast ?a _ ?x) with x.

Definition rndval_with_cond_result1 {NANS: Nans} `{coll: collection}
          env {ty} (e: expr ty) (r: rexpr) (s: MSHIFT) :=
    exists errors,
        (errors_bounded s errors)
        /\
        let fv := fval env e in
        is_finite fv = true
        /\
        reval r env errors = FT2R fv.

Lemma boundsmap_denote_pred_e_old `{coll: collection}:
  forall vm i' t i lo hi,
    boundsmap_denote_pred vm (i',
     {| var_type := t; var_name := i; var_lobound := lo; var_hibound := hi |}) ->
    match Maps.PTree.get i (proj1_sig vm) with
     | Some (existT _ t' v) => t' = t /\ (lo <= @FT2R t' v <= hi)%R
     | None => False
    end.
Proof.
intros.
destruct H.
destruct H as [? [? [??]]].
subst.
simpl in *. rewrite H0. auto.
Qed.

Axiom prop_ext: ClassicalFacts.prop_extensionality.

Lemma proof_irr      : ClassicalFacts.proof_irrelevance.
Proof. apply ClassicalFacts.ext_prop_dep_proof_irrel_cic.
 apply prop_ext.
Qed.
Arguments proof_irr [A] a1 a2.

Lemma boundsmap_denote_pred_e `{coll: collection}:
  forall vm i' t i lo hi
  (IN: incollection t),
  boundsmap_denote_pred vm (i',
   {| var_type:=t; var_name := i; var_lobound := lo; var_hibound := hi |}) ->
   (lo <= FT2R (env_ vm t IN i) <= hi)%R.
Proof.
intros.
destruct H as [v [? [? [? ?]]]]; subst.
unfold env_.
destruct vm as [vm Hvm]; simpl in *.
set (H := Hvm i); clearbody H.
destruct (Maps.PTree.get i vm); [ | discriminate].
inversion H0; clear H0; subst.
destruct (typesize_eq_dec t t); [ | congruence].
unfold eq_rect.
replace (incollection_eq t t IN (H (existT ftype t v) eq_refl) e)
  with (eq_refl t); auto.
apply proof_irr.
Qed.

Definition eval_cond' `{coll: collection} (s : shiftmap) (c: cond) (env: environ) : Prop :=
  eval_cond2 env s c.

Definition rndval_with_cond2 `{coll: collection} {ty} (e: expr ty) : rexpr * shiftmap * list (environ -> Prop) :=
 let '((r,(si,s)),p) := rndval_with_cond' 1 empty_shiftmap e
  in (r, s, map (eval_cond' s) p).

Lemma rndval_with_cond_correct2 {NANS: Nans} `{coll: collection}:
 forall
  ty (e: expr ty) (VALID: expr_valid e)
  (bm: boundsmap) (vm: valmap),
  boundsmap_denote bm vm ->
  let '(r,s,p) := rndval_with_cond2 e in
  Forall (fun c => c (env_ vm)) p ->
  exists errors,
      (errors_bounded s errors) /\
        let fv := fval (env_ vm) e in
        is_finite fv = true
        /\ reval r (env_ vm) errors = FT2R fv.
Proof.
intros.
assert (env_all_finite (env_ vm)) by (intros ? ? ; eapply finite_env; eauto).
destruct ( rndval_with_cond e) as [[r s] p] eqn:?H.
pose proof (rndval_with_cond_correct _ H0 _ VALID _ _ _ H1).
unfold rndval_with_cond in H1.
unfold rndval_with_cond2.
destruct (rndval_with_cond' 1 empty_shiftmap e) as [[? [? ?]] ?].
inversion H1; clear H1; subst.
intros.
destruct H2 as [errors [? [? ?]]].
-
induction l. constructor.
inversion H1; clear H1; subst.
apply Forall_cons; auto.
unfold eval_cond. unfold eval_cond' in H4.
apply eval_cond2_correct in H4; auto.
-
exists errors.
auto.
Qed.

Lemma invert_quad `{coll: collection} :
  forall (a a': rexpr) (b b': nat) (c c': shiftmap) (d d': list cond) (G: Prop),
  (a=a' -> b=b' -> c=c' -> d=d' -> G) ->
  (a,(b,c),d) = (a',(b',c'),d') -> G.
Proof.
intros.
inversion H0; auto.
Qed.

Ltac invert_rndval_with_cond' :=
 match goal with
 | |- rndval_with_cond' 1 empty_shiftmap ?e = (_, (_,_), _) -> ?M' =>
    let M := fresh "M" in set (M:=M');
   cbv beta iota zeta delta [rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          make_rounding round_knowl_denote];
   repeat change (binop_eqb _ _) with true;
   repeat change (binop_eqb _ _) with false;
 cbv beta iota zeta delta [rounding_cond_ast no_overflow app];
 match goal with |- (?r1,(_, ?s1), ?l1) = _ -> _ =>
    let r' := fresh "r" in let s' := fresh "s" in let l' := fresh "l" in
    set (r' := r1); set (s' := s1); set (l' := l1);
    let H1 := fresh "H" in
     apply invert_quad; intros; subst;

     cbv beta iota zeta delta [mset empty_shiftmap mempty
            Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set'
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
             fst snd] in s';

     subst r'; subst s'; subst l'
  end;
  subst M
 | _ => fail "invert_rndval_with_cond' at inappropriate goal"
 end.

(*
Ltac process_one_bound B :=
   apply boundsmap_denote_pred_e in B;
   lazymatch type of B
   with
   | match Maps.PTree.get ?i ?vmap with | _ => _  end =>

       let z := constr:(i) in
       let z := eval compute in z in
       change i with z in *;
       let t := fresh "t" in
       let u := constr:(Maps.PTree.get z vmap) in
       let u' := eval hnf in u in
       match u' with
       | Some _ =>  change u with u'
       | _ => let v := fresh "v" i in
                  destruct u as [[t v]|]; [ | solve [contradiction B]]
       | _ => let v := fresh "v" in
                  destruct u as [[t v]|]; [ | solve [contradiction B]]
       end;
       let B' := fresh in
       destruct B as [B' B]; try subst t;
       try match type of B' with ?x = ?y => constr_eq x y; clear B' end
   end.
*)

Ltac process_one_bound B :=
 lazymatch type of B with
 | boundsmap_denote_pred ?vm (_,
   {| var_type := ?t; var_name := _; var_lobound := _; var_hibound := _ |}) =>
  first [apply boundsmap_denote_pred_e with (IN:=I) in B
        | lazymatch goal with |- context [env_ vm t ?H _] =>
          apply boundsmap_denote_pred_e with (IN:=H) in B
          end
        | let H := fresh "IN" in assert (H: incollection t)
              by prove_incollection;
           apply boundsmap_denote_pred_e with (IN:=H) in B
        ]
  | boundsmap_denote_pred _ (_,?x) =>
     progress (let y := eval hnf in x in change x with y in B); process_one_bound B
 end.

Ltac process_boundsmap_denote :=
 lazymatch goal with
 | H: boundsmap_denote _ _ |- _ =>
   apply boundsmap_denote_e in H;
   simpl Maps.PTree.elements in H;
   unfold list_forall in H;
   repeat lazymatch type of H with
   | boundsmap_denote_pred _ _ /\ _ =>
      let B := fresh "BOUND" in destruct H as [B H];
      process_one_bound B
   | True => clear H
   | boundsmap_denote_pred _ _ =>
       let B := fresh "BOUND" in rename H into B;
      process_one_bound B
    end
  end;
  repeat change (type_eq_dec ?t _ ) with (@left (t=t) (t<>t) (eq_refl t)) in *;
(*  repeat match goal with |- context [type_eq_dec ?a ?b] =>
     let r := constr:(type_eq_dec a b) in
     let s := eval hnf in r in
     match s with right _ => change r with s end
   end;
*)
  cbv iota;
  repeat change (eq_rect_r ftype ?v eq_refl) with v in *.

Definition prove_rndval' {NANS: Nans} `{coll: collection} bm vm {ty} (e: expr ty) :=
 boundsmap_denote bm vm ->
  let
   '(r, s, _) := rndval_with_cond2 (fshift_div (fshift (fcval e))) in
    rndval_with_cond_result1 (env_ vm) e r s.

Definition prove_rndval {NANS: Nans} `{coll: collection} bm vm {ty} (e: expr ty) :=
  {rs | fst (rndval_with_cond2 (fshift_div (fshift (fcval e)))) = rs /\
         (boundsmap_denote bm vm ->
          let '(r,s) := rs in rndval_with_cond_result1 (env_ vm) e r s)}.

Lemma prove_rndval'_e {NANS: Nans} `{coll: collection} :
  forall bm vm {ty} (e: expr ty), prove_rndval' bm vm e -> prove_rndval bm vm e.
Proof.
unfold prove_rndval', prove_rndval; intros.
destruct (rndval_with_cond2 _) as [[r s] p]; simpl in *.
exists (r,s); auto.
Qed.

Lemma prove_rndval'_i1 {NANS: Nans} `{coll: collection} bm vm ty (e: expr ty) :
 (boundsmap_denote bm vm ->
  is_finite (fval (env_ vm) (fshift_div (fcval e))) = true ->
  let
   '(r, s, _) := rndval_with_cond2 (fshift_div (fcval e)) in
    rndval_with_cond_result1 (env_ vm) e r s)
 -> prove_rndval' bm vm e.
Proof.
intros.
red; intros.
specialize (H H0).
destruct (rndval_with_cond2 _) as [[? ?] ?].
red; intros.
Abort.

Lemma Rmult_Rinv_IZR: forall a b,
   Rmult (RinvImpl.Rinv (IZR a)) (RinvImpl.Rinv (IZR b)) =
   RinvImpl.Rinv (IZR (a*b)%Z).
Proof.
intros.
rewrite <- Rinv_mult.
f_equal.
symmetry; apply mult_IZR.
Qed.

Lemma adjust_bound:
  forall (u: R) (i: positive) (j: Z),
   u <= /2 * / IZR (Z.pow_pos 2 i) ->
   (j = Zpos (1 + i)) ->
  u <= / IZR (2 ^ j).
Proof.
intros. subst j.
rewrite Rmult_Rinv_IZR in H.
replace (2 ^ Z.pos (1 + i))%Z with  (2 * Z.pow_pos 2 i)%Z; auto.
replace (Z.pos (1+i)) with (1 + Z.pos i)%Z by lia.
rewrite Z.pow_add_r by lia.
reflexivity.
Qed.

Ltac process_conds :=
  repeat simple apply conj;
  try simple apply Logic.I;
  repeat
   (let H := fresh in intros ?u H;
   try (match type of H with _ _ (Rabs (error_bound ?x _)) =>
     rewrite (Rabs_pos_eq _ (error_bound_nonneg _ _)) in H;
     let y := constr:(x) in let y := eval hnf in y in change x with y in H
   end;
   cbv [error_bound bpow radix2 femax fprec fprecp Z.sub Z.add Z.opp
     Z.pos_sub Z.succ_double Pos.pred_double Z.mul
      radix_val Pos.iter Pos.add Pos.succ Pos.mul]  in H;
      (eapply adjust_bound in H; [ | compute; reflexivity]))).

Lemma fshift_div_fshift_fcval_correct {NANS: Nans} `{coll: collection} :
  forall (env : environ) ty (e : expr ty),
  float_equiv (fval env (fshift_div (fshift (fcval e))))
                (fval env e).
Proof.
intros.
eapply float_equiv_trans.
apply fshift_div_correct'.
rewrite fshift_correct.
rewrite fcval_correct.
apply float_equiv_refl.
Qed.

Lemma fshift_fcval_correct {NANS: Nans} `{coll: collection} :
  forall (env : environ) ty (e : expr ty),
  fval env (fshift (fcval e)) = fval env e.
Proof.
intros.
rewrite fshift_correct.
rewrite fcval_correct.
f_equal.
Qed.

Lemma rndval_with_cond_result1_fvals_eq {NANS: Nans} `{coll: collection} :
  forall env ty (e1 e2: expr ty) r s,
  float_equiv (fval env e1) (fval env e2) ->
  rndval_with_cond_result1 env e1 r s ->
  rndval_with_cond_result1 env e2 r s.
Proof.
intros.
destruct H0 as [errors [? [? ?]]].
exists errors. split; auto.
rewrite <- (float_equiv_eq _ (fval env e1) (fval env e2) H1); auto.
Qed.

Lemma rndval_with_cond_correct2_opt {NANS: Nans} `{coll: collection} :
      forall ty (e0 e1 e: expr ty) (EQ1: e1 = e),
       expr_valid e ->
       forall (bm : boundsmap) (vm : valmap),
       boundsmap_denote bm vm ->
       @float_equiv ty
            (fval (env_ vm) e1)
            (fval (env_ vm) e0) ->
       let  '(r, s, p) := rndval_with_cond2 e in
        Forall (fun c : environ -> Prop => c (env_ vm)) p ->
        rndval_with_cond_result1 (env_ vm) e0 r s.
Proof.
intros.
subst e1.
pose proof (rndval_with_cond_correct2 ty e H _ _ H0).
destruct (rndval_with_cond2 e) as [[? ?] ?].
intro.
specialize (H2 H3).
change (rndval_with_cond_result1 (env_ vm) e r s) in H2.
eapply rndval_with_cond_result1_fvals_eq.
 eassumption.
assumption.
Qed.

Lemma fast_apply_rndval_with_cond_correct2  {NANS: Nans} `{coll: collection}:
forall ty (e0 e1 e: expr ty) (EQ: e1 = e),
  expr_valid e ->
  forall (bm : boundsmap) (vm : valmap),
  boundsmap_denote bm vm ->
  float_equiv (fval (env_ vm) e1) (fval (env_ vm) e0) ->
  Forall (fun c : environ -> Prop => c (env_ vm))
        (snd (rndval_with_cond2 e)) ->
  let '(r, s, _) := rndval_with_cond2 e in
    rndval_with_cond_result1 (env_ vm) e0 r s.
Proof.
intros.
pose proof (rndval_with_cond_correct2_opt ty e0 e1 e).
destruct (rndval_with_cond2 e) as [[r s] p].
apply (H3 EQ H bm vm); auto.
Qed.

Ltac solve_Forall_conds:=
 lazymatch goal with
 | |- Forall _ _ =>

  (* the goal is a Forall of all the conds. Clean them up a bit. *)
  cbv beta iota zeta delta [
            mset empty_shiftmap mempty
            Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set'
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
             fst snd

          rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          make_rounding round_knowl_denote
         rounding_cond_ast no_overflow app];

  (* now process the boundsmap above the line, and the conds below the line *)
  process_boundsmap_denote;
  process_conds; interval
 | |- _ => idtac
 end.

Lemma Forall_nested_and:
  forall {A} (f: A -> Prop) al,
   List.fold_right and True (map f al) ->
   Forall f al.
Proof.
induction al; simpl; intros. constructor.
destruct H.
constructor; auto.
Qed.

Lemma fast_apply_rndval_with_cond_correct3 {NANS: Nans}  `{coll: collection}:
forall ty (e0: expr ty)  (bm : boundsmap) (vm : valmap),
   let e := fshift_div (fshift (fcval e0)) in
  expr_valid e ->
  (boundsmap_denote bm vm ->
   Forall (fun c : environ->Prop => c (env_ vm))
        (snd (rndval_with_cond2 e))) ->
     prove_rndval' bm vm e0.
Proof.
intros. intro.
pose proof rndval_with_cond_correct2_opt ty e0 e e (eq_refl _)
   H _ _ H1
  (fshift_div_fshift_fcval_correct _ _ _).
subst e.
destruct (rndval_with_cond2 _) as [[r s] p].
auto.
Qed.

Ltac compute_fshift_div1 :=
    let j := fresh "j" in
   set (j := fcval _);
cbv - [BPLUS BMULT BMINUS BDIV BOPP] in j;
subst j;
compute_binary_floats;
 set (j := fshift _);
cbv - [BPLUS BMULT BMINUS BDIV BOPP] in j;
subst j;
compute_binary_floats;
set (j := fshift_div _);
cbv - [BPLUS BMULT BMINUS BDIV BOPP] in j;
subst j;
compute_binary_floats;
fold Tsingle; fold Tdouble.

Ltac cbv_fcval :=
cbv [fcval fcval_nonrec option_pair_of_options
       fop_of_binop fop_of_unop
  fop_of_rounded_binop fop_of_rounded_unop fop_of_exact_unop
  fshift_mult binop_eqb andb rounded_binop_eqb
  option_eqb rounding_knowledge_eqb eqb
  (* new stuff *)
  rndval_with_cond2 rndval_with_cond'
  mset empty_shiftmap mempty
            Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set'
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
             fst snd
          rnd_of_cast_with_cond
          rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          make_rounding round_knowl_denote
         rounding_cond_ast no_overflow app
         rnd_of_func_with_cond rnd_of_func rnd_of_func' abs_error rel_error
  Bsign N.of_nat b64_B754_finite b32_B754_finite
];
  repeat change (ftype_of_float ?x) with x;
  repeat change (float_of_ftype ?x) with x.

Ltac compute_fshift_div_special_reduce :=
 cbv_fcval;
 repeat (
     compute_every @ff_args;
     compute_every @IEEE754_extra.Bexact_inverse;
     compute_every3 @to_power_2;
     compute_every3 @to_power_2_pos;
     compute_every3 @to_inv_power_2;
     compute_binary_floats;
     compute_every6 @binary_float_eqb;
     cbv_fcval).

Ltac compute_fshift_div2 :=
  (* don't use this one, it causes Qed blowup in (for example) the kepler1 benchmark *)
 match goal with |- context [fcval ?F] =>
   let g := eval hnf in F in change F with g end;
  let j := fresh "j" in let HIDE := fresh "HIDE" in
  set (j := fshift_div _);
  pattern j;
  match goal with |- ?H _ => set (HIDE:=H) end;
  subst j;
  compute_fshift_div_special_reduce;
  cbv delta [fshift]; compute_fshift_div_special_reduce;
  cbv delta [fshift_div]; compute_fshift_div_special_reduce;
  subst HIDE; cbv beta.

Ltac compute_fshift_div3 :=
  match goal with |- context [fcval ?F] =>
     let g := eval hnf in F in change F with g end;
  let j := fresh "j" in let HIDE := fresh "HIDE" in
  set (j := fshift_div _);
  pattern j;
  match goal with |- ?H _ => set (HIDE:=H) end;
  subst j;
  compute_fshift_div_special_reduce;
  cbv delta [fshift]; compute_fshift_div_special_reduce;
  cbv beta fix match zeta delta [fshift binop_eqb rounded_binop_eqb andb eqb];
  cbv beta fix match zeta delta [fshift_div fcval_nonrec binop_eqb rounded_binop_eqb andb eqb];
  compute_fshift_div_special_reduce;
  subst HIDE; cbv beta.

Ltac compute_fshift_div := compute_fshift_div3.

Ltac prove_rndval :=
 (* if necessary, convert goal into a prove_rndval'   goal*)
 lazymatch goal with
 | |- prove_rndval _ _ _ => apply prove_rndval'_e
 | |- _ => idtac
 end;

(*time "1"*) (
 eapply fast_apply_rndval_with_cond_correct3; [compute; repeat split; auto | intro ]);

(*time "2a"*) compute_fshift_div;  (*(compute_every @fshift_div);*)

(*time "2b"*) (
  cbv [rndval_with_cond2 rndval_with_cond'];
  cbv [ mset empty_shiftmap mempty
            Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set'
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
             fst snd
          rnd_of_cast_with_cond
          rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          make_rounding round_knowl_denote
         rounding_cond_ast no_overflow app
         rnd_of_func_with_cond rnd_of_func rnd_of_func'  abs_error rel_error
         func_no_overflow type_hibound'];
(* OLD
    repeat match goal with |- context [bounds_to_conds ?bnds ?es] =>
       let h := fresh "h" in set (h := bounds_to_conds bnds es); compute in h; subst h
      end;
  NEW: *)
    repeat match goal with |- context [bounds_to_conds ?bnds ?es] =>
       let h := fresh "h" in set (h := bounds_to_conds bnds es);
         simpl in h; unfold eq_rect_r, eq_rect in h; simpl in h; subst h
      end;
   simpl ff_rel; simpl ff_abs;
   compute_every type_leb;
   cbv beta iota zeta;
   apply Forall_nested_and;
   unfold map at 1 2;
   red;
   fold Tsingle; fold Tdouble);

(*time "3" *)
  (let U := fresh "U" in try set (U := Maps.PTree.Nodes _ );
   cbv [eval_cond' eval_cond2 reval];
   compute_every MSET.elements;
   try subst U;
   let j := fresh "j" in repeat (set (j := ff_realfunc _); simpl in j; subst j));

(*time "4"*)
   ( cbv [enum_forall enum_forall'
         mget Maps.PMap.get Maps.PTree.get fst snd Maps.PTree.get'
            mset empty_shiftmap mempty
            Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set'
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
            fst snd reval
         Prog.binary Prog.unary Prog.real_operations
         Tree.binary_real Tree.unary_real ];
  repeat change (B2R (fprec ?t) _ ?x) with (@FT2R t x);
  simpl F2R);

  (* now process the boundsmap above the line, and the conds below the line *)
(*time "5"*)  process_boundsmap_denote;
(*time "6"*)  process_conds.

Lemma errors_bounded_e:
  forall errors bound0 m, errors_bounded (bound0, m) errors ->
   Forall (fun it => let '(i,bound) := it in
                   Rle (Rabs (errors i)) (error_bound bound))
      (Maps.PTree.elements m).
Proof.
intros.
red in H.
apply Forall_forall.
intros.
destruct x as [i bound].
apply Maps.PTree.elements_complete in H0.
specialize (H i).
unfold mget, Maps.PMap.get in H. simpl in H. rewrite H0 in H. auto.
Qed.

Definition rndval_without_cond  `{coll: collection} {ty} (e: expr ty) : rexpr * shiftmap :=
 let '(r,s,p) := rndval_with_cond2 e in (r,s).

Lemma rndval_with_cond_result1_e {NANS: Nans}  `{coll: collection}:
  forall vm ty (e: expr ty) r s,
   rndval_with_cond_result1 (env_ vm) e r s ->
  let '(_, m) := s in
   exists errors: positive -> R,
     Forall (fun it => let '(i,bound) := it in
                   Rle (Rabs (errors i)) (error_bound bound))
      (Maps.PTree.elements m) /\
  (let fv := fval (env_ vm) e in
   is_finite fv = true /\
   reval r (env_ vm) errors =
   FT2R fv).
Proof.
intros.
destruct s as [bound m].
destruct H as [errors [? [? ?]]]; exists errors; split; auto.
apply (errors_bounded_e _ bound); auto.
Qed.

Definition rndval_result  {NANS: Nans} `{coll: collection}
   (bm : boundsmap) (vm : valmap) {ty} (e : expr ty) r s
  (H:  rndval_without_cond (fshift (fcval e)) = (r,s)) :=
   boundsmap_denote bm vm ->
  let '(_, m) := s in
   exists errors: positive -> R,
     Forall (fun it => let '(i,bound) := it in
                   Rle (Rabs (errors i)) (error_bound bound))
      (Maps.PTree.elements m) /\
  (let fv := fval (env_ vm) e in
   is_finite fv = true /\
   reval r (env_ vm) errors =
   FT2R fv).

Fixpoint evenlog' (p: positive)  : Z * Z :=
 match p with
 | xO q => match evenlog' q with (r,n) => (r, Z.succ n) end
 | _ => (Z.pos p, 0%Z)
 end.

Definition evenlog (i: Z) : Z * Z :=
 match i with
 | Z.pos p => evenlog' p
 | _ => (i,0%Z)
 end.

Lemma evenlog_e: forall i, i = (fst (evenlog i) * Z.pow 2 (snd (evenlog i)))%Z.
Proof.
intros.
unfold evenlog.
destruct i; simpl; rewrite ?Pos.mul_1_r; auto.
induction p; simpl; rewrite ?Pos.mul_1_r; auto.
destruct (evenlog' p) eqn:?H; simpl in *.
rewrite Pos2Z.inj_xO.
rewrite IHp.
rewrite Z.pow_succ_r.
lia.
clear - H.
revert z z0 H; induction p; simpl in *; intros.
inversion H; lia.
destruct (evenlog' p). inversion H; clear H; subst.
specialize (IHp _ _ (eq_refl _)).
lia.
inversion H; clear H; subst; lia.
Qed.

Lemma evenlog_nonneg: forall i, (0 <= snd (evenlog i))%Z.
Proof.
intros.
destruct i; simpl; try lia.
induction p; simpl; try lia.
destruct (evenlog' p); simpl in *.
lia.
Qed.

Definition cleanup_Fnum' f e :=
 let (f1,e1) := evenlog f in
 let e' := (e+e1)%Z
  in match e' with
      | Zpos _ =>   IZR (f1 * Z.pow 2 e')%Z
      | Z0 => IZR f1
      | Zneg p => IZR f1 / IZR (Z.pow 2 (Zpos p))
     end.

Lemma cleanup_Fnum:
  forall f e, F2R radix2 {| Defs.Fnum := f; Defs.Fexp := e |} = cleanup_Fnum' f e.
Proof.
intros.
unfold cleanup_Fnum'.
pose proof (evenlog_e f).
pose proof (evenlog_nonneg f).
destruct (evenlog f) as [r n].
simpl in *.
subst f.
destruct (e+n)%Z eqn:?H.
- rewrite mult_IZR.
rewrite (IZR_Zpower radix2) by auto.
rewrite Rmult_assoc.
rewrite <- bpow_plus.
rewrite Z.add_comm.
rewrite H.
apply Rmult_1_r.
-
rewrite <- H.
rewrite !mult_IZR.
rewrite Rmult_assoc.
f_equal.
rewrite  (IZR_Zpower radix2) by auto.
rewrite <- bpow_plus.
rewrite  <- (IZR_Zpower radix2) by lia.
rewrite Z.add_comm.
reflexivity.
-
rewrite !mult_IZR.
unfold Rdiv.
rewrite Rmult_assoc.
f_equal.
rewrite  !(IZR_Zpower radix2) by auto.
rewrite <- bpow_plus.
rewrite Z.add_comm.
rewrite H.
change (Z.neg p) with (Z.opp (Z.pos p)).
rewrite bpow_opp.
reflexivity.
Qed.

Definition roundoff_error_bound {NANS: Nans} `{coll: collection} (vm: valmap) {ty} (e: expr ty) (err: R):=
  is_finite (fval (env_ vm) e) = true /\
 Rle (Rabs (@FT2R ty (fval (env_ vm) e) - rval (env_ vm) e)) err.

Definition prove_roundoff_bound {NANS: Nans} `{coll: collection}
    (bm: boundsmap) (vm: valmap) {ty} (e: expr ty)
   (err: R): Prop :=
   boundsmap_denote bm vm ->
   roundoff_error_bound vm e err.

Ltac unfold_prove_rndval P :=
  (* Suppose you have proved a theorem P of the form, "prove_rndval bm vm e"
    where e is an expr (reified floating-point expression).
  Then in any proof goal where there is a boundsmap_denote above the line,
   use this tactic to apply-and-unfold P, for use in proving some consequence of P *)
match type of P with prove_rndval _ _ _ => idtac end;
let BMD := fresh "BMD" in
  match goal with H: boundsmap_denote _ _ |- _ => rename H into BMD end;
let H2 := fresh "H2" in let H3 := fresh "H3" in let r := fresh "r" in let s := fresh "s" in
destruct P as [[r s] [H2 H3]];
specialize (H3 BMD);
process_boundsmap_denote;
compute in H2; inversion H2; clear H2; subst;
fold Tsingle in H3; fold Tdouble in H3;
apply rndval_with_cond_result1_e in H3;
let errors := fresh "errors" in let H0 := fresh "H0" in
destruct H3 as [errors [H0 H2]];
let e := fresh "e" in
 match type of H2 with context [fval ?env ?ee] =>
   set (e := fval env ee) in H2;
  let e1 := eval hnf in ee in change ee with e1 in e;
  cbv beta iota zeta delta [
      fval
      fop_of_binop fop_of_rounded_binop
      fop_of_unop fop_of_rounded_unop fop_of_exact_unop
      option_pair_of_options] in e;
   repeat change (cast  _ _ ?x) with x in e;
   repeat
    match goal with
    | e := context [env_ ?a ?b ?c] |- _ =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v in *
   end
end;
 let FIN := fresh "FIN" in
 destruct H2 as [FIN H2];
 unfold e in H2;
cbv beta iota zeta delta [
         reval Prog.binary Prog.unary Prog.real_operations
         Tree.binary_real Tree.unary_real]
   in H2;
   repeat
    match type of H2 with context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v in H2
   end;
change (Build_radix _ _) with radix2 in H2;
 (* Don't do this stuff, any rewrites in H2 make Qed blow up
repeat
match type of H2 with
 context [ F2R radix2  {| Defs.Fnum := ?f; Defs.Fexp := ?e |} ] =>
   let H := fresh in assert (H := cleanup_Fnum f e);
      simpl Z.add in H; simpl fst in H;
      change (powerRZ _ 0) with 1%R in H;
      rewrite H in H2; clear H
end;
rewrite ?Rmult_1_l in H2;
*)
fold (@FT2R Tsingle) in *;
fold (@FT2R Tdouble) in *;
repeat (let E := fresh "E" in
            assert (E := Forall_inv H0);
            cbv delta [Maps.PTree.prev Maps.PTree.prev_append] in E;
            simpl in E;
          match type of E with
           |  Rle (Rabs ?a) (error_bound _ Normal') =>
                let d := fresh "d" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal') =>
                let d := fresh "e" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal2') =>
                   let d := fresh "e" in set (d := a) in *; clearbody d
           end;
           unfold error_bound in E;
           simpl bpow in E;
           rewrite Zpower_pos_powerRZ in E;
           rewrite mul_hlf_powerRZ in E;
           simpl Z.sub in E;
           apply Forall_inv_tail in H0);
try match type of H0 with Forall _ (Maps.PTree.elements Maps.PTree.Empty) => clear H0 end;
try match type of H0 with Forall _ nil => clear H0 end;
try clear errors;
fold e in H2;
revert H2; intro.

Ltac prove_IZR_neq :=
 change R0 with 0%R;
 let H := fresh in intro H; apply eq_IZR in H; discriminate H.

Lemma powerRZ_compute:
 forall b i, powerRZ (IZR (Zpos b)) (Zpos i)  = IZR (Z.pos (Pos.pow b i)).
Proof.
intros.
unfold powerRZ.
rewrite pow_IZR.
f_equal.
rewrite Pos2Z.inj_pow.
f_equal.
apply positive_nat_Z.
Qed.

Ltac compute_Zpow :=
repeat match goal with
 | |- context [Z.pow ?a ?b] =>
  let x := constr:(Z.pow a b) in let y := eval compute in x in
  change x with y in *
 | H: context [Z.pow ?a ?b] |- _ =>
  let x := constr:(Z.pow a b) in let y := eval compute in x in
  change x with y in *
end.

Ltac unfold_rval :=
 match goal with |- context [rval ?env ?x] =>
   let a := constr:(rval env x) in let b := eval hnf in a in change a with b
 end;
 cbv beta iota delta [rval Rop_of_binop Rop_of_unop
            Rop_of_rounded_binop Rop_of_exact_unop Rop_of_rounded_unop];
 fold (@FT2R Tsingle) in *; fold (@FT2R Tdouble);
 (* Perform all env lookups *)
 repeat
    match goal with
    | |- context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v
   end;
 (* Clean up all FT2R constants *)
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
 rewrite <- ?(F2R_eq radix2);
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end.

Lemma prove_rndval_is_finite {NANS} `{coll: collection} : forall bm vm ty (e: expr ty),
 boundsmap_denote bm vm ->
 @prove_rndval NANS _ bm vm ty e -> is_finite (fval (env_ vm) e) = true.
Proof.
intros.
destruct X as [[??]  [? ?]].
apply H1 in H; clear H1.
destruct H as [? [? [? ?]]].
apply H1.
Qed.

Ltac cbv_reval :=
 cbv [
       reval Prog.binary Prog.unary Prog.real_operations
      Tree.binary_real Tree.unary_real
      rval Rop_of_binop Rop_of_unop
            Rop_of_rounded_binop Rop_of_exact_unop
             Rop_of_rounded_unop
      rval_klist].

Ltac abstract_env_variables :=
repeat
match goal with
 | |- context [B2R ?prec ?emax (float_of_ftype (env_ ?vm ?t ?H ?i))] =>
    let j := fresh "v" i in
    set (j := B2R prec emax (float_of_ftype (env_ vm t H i))) in *; clearbody j
 | H0: context [B2R ?prec ?emax (float_of_ftype  (env_ ?vm ?t ?H ?i))] |- _ =>
    let j := fresh "v" i in
    set (j := B2R prec emax (float_of_ftype (env_ vm t H i))) in *; clearbody j
 end.

Ltac test_vmap_concrete vm :=
 let x := constr:(proj1_sig vm) in
 let x := eval hnf in x in
 lazymatch x with
 | Maps.PTree.Nodes _ => idtac
 | Maps.PTree.Empty => idtac
 end.

Ltac concrete_env_variables :=
 try
  lazymatch goal with |- context [env_ ?vm _ _ _] =>
    test_vmap_concrete vm;
    let h := fresh "h" in
    repeat (set (h := env_ vm _ _ _) in *; hnf in h; subst h)
   end.

Ltac prove_roundoff_bound2 :=

match goal with
| P: prove_rndval ?bmap ?vmap ?e |- prove_roundoff_bound ?bmap' ?vmap' ?e' _ =>
  constr_eq bmap bmap'; constr_eq vmap vmap'; constr_eq e e';
  revert P
| _ => fail "not the right kind of proof goal for prove_roundoff_bound2"
end;

let BMD := fresh "BMD" in
let H2 := fresh "H2" in let H3 := fresh "H3" in let FIN := fresh "FIN" in
   let e := fresh "e" in let r := fresh "r" in let s := fresh "s" in
 intros [[r s] [H2 H3]] BMD;
specialize (H3 BMD);
red;
match goal with |- ?G => let GG := fresh "GG" in set (GG := G);
  revert H2; compute_fshift_div; cbv_fcval; intro H2; subst GG
 end;
inversion H2; clear H2; subst;
fold Tsingle in H3; fold Tdouble in H3;
apply rndval_with_cond_result1_e in H3;
destruct H3 as [errors [H0 H2]];
 match type of H2 with context [fval ?env ?ee] =>
   set (e := fval env ee) in H2|-*;
  let e1 := eval hnf in ee in change ee with e1 in e
end;
 destruct H2 as [FIN H2]; split; [assumption  | ]; clear FIN;
 clearbody e;
 simpl in e;
 try change (B2R _ _ e) with (FT2R e) in H2;
 match goal with H2 : _ = @FT2R ?t1 e |- context [@FT2R ?t2 e] =>
  change t2 with t1
 end;
 rewrite <- H2; clear H2 e;

 match goal with |- context [rval ?env ?x] =>
   let a := constr:(rval env x) in let b := eval hnf in a in change a with b
 end;
 cbv_reval;
 simpl ff_args;
  let j := fresh "j" in repeat (set (j := ff_realfunc _); simpl in j; subst j);
(* unfold  env_; *)
 process_boundsmap_denote;

 repeat change (B2R (fprec ?t) _) with (@FT2R t);
 rewrite <- ?B2R_float_of_ftype in * by auto with typeclass_instances; (* NEW *)

 repeat (let E := fresh "E" in
            assert (E := Forall_inv H0);
            cbv delta [Maps.PTree.prev Maps.PTree.prev_append] in E;
            simpl in E;
           rewrite ?(Rabs_pos_eq _ (error_bound_nonneg _ _)) in E;
          match type of E with
           |  Rle (Rabs ?a) (error_bound _ Normal') =>
                let d := fresh "d" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal') =>
                let d := fresh "e" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal2') =>
                   let d := fresh "e" in set (d := a) in *; clearbody d
           | Rle (Rabs ?a) _ =>
                   let d := fresh "e" in set (d := a) in *; clearbody d
           end;
            try (eapply adjust_bound in E; [ | compute; reflexivity]);
           apply Forall_inv_tail in H0);
 try match type of H0 with Forall _ (Maps.PTree.elements Maps.PTree.Empty) => clear H0 end;
 try match type of H0 with Forall _ nil => clear H0 end;
 try clear errors;
 repeat match goal with B: context [FT2R ?v] |- _ =>
  is_var v; let u := fresh "u" in set (u := FT2R v) in *;
  clearbody u; clear v; rename u into v
 end;

 concrete_env_variables;
 abstract_env_variables;

 (* Clean up all FT2R constants *)
 repeat (change (FT2R ?x) with (B2R _ _ x) in *);
 simpl B2R in *;
(*
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
*)
 rewrite <- ?(F2R_eq Zaux.radix2);
 repeat match goal with |- context [F2R _ ?x] => unfold x end;
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end.

Ltac prove_roundoff_bound :=
 match goal with
 | |- prove_roundoff_bound ?bm ?vm ?e _ => assert (P: prove_rndval bm vm e)
 | H: boundsmap_denote ?bm ?vm |- is_finite _ _ (fval (env_ ?vm') ?e) = true =>
        unify vm vm'; assert (P: prove_rndval bm vm e); [ | apply (prove_rndval_is_finite _ _ _ H P)]
 end.

Lemma roundoff_bound_hack:
  forall i j k,
    (0 < i)%Z -> (0 < j)%Z -> (0 < k)%Z ->
    forall u,
    (Z.div j i = u)%Z ->
    (u >= k)%Z ->
    (IZR i / IZR j <= / (IZR k))%R.
Proof.
intros.
subst u. rename H3 into H2.
pose proof (IZR_lt _ _ H).
pose proof (IZR_lt _ _ H0).
pose proof (IZR_lt _ _ H1).
rewrite <- Rinv_div by lra.
apply Rinv_le. lra.
apply Rcomplements.Rle_div_r.
lra.
rewrite <- mult_IZR.
apply IZR_le.
pose proof (Zdiv.Zmod_eq j i ltac:(lia)).
assert (j/i * i = j - j mod i)%Z by lia.
apply Zmult_ge_compat_r with (p:=i) in H2; [ | lia].
rewrite H7 in H2.
pose proof (Z.mod_bound_pos j i ltac:(lia) ltac:(lia)).
lia.
Qed.

Definition bound_contains (i1 i2: ident * varinfo) :=
        (fst i1 = fst i2 /\ fst i1 = var_name (snd i1) /\ fst i2 = var_name (snd i2))
  /\ var_type (snd i1) = var_type (snd i2)
  /\   Rle (var_lobound (snd i1)) (var_lobound (snd i2))
  /\  Rge (var_hibound (snd i1)) (var_hibound (snd i2)).

Lemma Forall2_e1:
  forall {A B: Type} (f: A -> B -> Prop) al bl,
  Forall2 f al bl ->
  (forall x, In x al -> exists y, In y bl /\ f x y).
Proof.
induction 1; intros.
inversion H.
inversion H1; clear H1; subst.
exists y; split; auto. left; auto.
destruct (IHForall2 _ H2) as [y1 [? ?]].
exists y1; split; auto.
right; auto.
Qed.

Lemma Forall2_e2:
  forall {A B: Type} (f: A -> B -> Prop) al bl,
  Forall2 f al bl ->
  (forall y, In y bl -> exists x, In x al /\ f x y).
Proof.
induction 1; intros.
inversion H.
inversion H1; clear H1; subst.
exists x; split; auto. left; auto.
destruct (IHForall2 _ H2) as [x1 [? ?]].
exists x1; split; auto.
right; auto.
Qed.

Definition boundsmap_contains bm1 bm2 :=
  Forall2 bound_contains (Maps.PTree.elements bm1)
      (Maps.PTree.elements bm2).

Lemma boundsmap_denote_relax {NANS: Nans} `{coll: collection}:
 forall (bm1 bm2 : Maps.PTree.t varinfo)
          (vm : valmap),
  boundsmap_contains bm1 bm2 ->
      boundsmap_denote bm2 vm ->
     boundsmap_denote bm1 vm.
Proof.
intros.
intro i; specialize (H0 i).
destruct (Maps.PTree.get i bm1)  as [[t1 n1 lo1 hi1]|] eqn:?H.
-
destruct (Forall2_e1 _ _ _ H _ (Maps.PTree.elements_correct _ _ H1))
 as [[i' [t2 n2 lo2 hi2]] [? [[? [? ?]] [? [? ?]]]]]; simpl in *; subst.
apply Maps.PTree.elements_complete in H2.
rewrite H2 in H0.
destruct (Maps.PTree.get n2 (proj1_sig vm)); try contradiction; auto.
destruct H0 as [? [? [? ?]]]; subst.
split; [ | split; [ | split]]; auto.
lra.
-
destruct (Maps.PTree.get i bm2) eqn:?H; auto.
destruct (Forall2_e2 _ _ _ H _ (Maps.PTree.elements_correct _ _ H2))
 as [[i' ?] [? [[? _] _]]].
simpl in H4; subst.
apply Maps.PTree.elements_complete in H3.
congruence.
Qed.

Lemma prove_roundoff_bound_relax {NANS: Nans} `{coll: collection}:
  forall bm1 bm2 vm ty (e: expr ty) R,
    boundsmap_contains bm1 bm2 ->
 prove_roundoff_bound bm1 vm e R ->
 prove_roundoff_bound bm2 vm e R.
Proof.
intros.
intro; apply H0.
revert H1.
apply boundsmap_denote_relax; auto.
Qed.


Definition val_bound {NANS: Nans}  `{coll: collection} (vm: valmap) {ty} (e: expr ty) (b: R):=
 Rle (Rabs (@FT2R ty (fval (env_ vm) e))) b.

Definition prove_val_bound {NANS: Nans} `{coll: collection}
    (bm: boundsmap) (vm: valmap) {ty} (e: expr ty)
   (b: R): Prop :=
   boundsmap_denote bm vm ->
   val_bound vm e b.

Ltac prove_val_bound :=
 match goal with |- prove_val_bound ?bm ?vm ?e _ =>
  assert (P: prove_rndval bm vm e)
 end.

Ltac prove_val_bound2 :=
 match goal with P: prove_rndval _ _ _ |- prove_val_bound _ _ _ _ =>
   intro; unfold_prove_rndval P
 end;
 (* Unfold val_bound *)
 red;
 (* The fval below the line should match the e above the line *)
 match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end;
 (* cleanups *)
 fold (@FT2R Tsingle) in *; fold (@FT2R Tdouble);
 (* incorporate the equation above the line *)
match goal with H: _ = @FT2R _ _ |- _ => rewrite <- H; clear H end;
 (* Perform all env lookups *)
 repeat
    match goal with
    | |- context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v
   end;
 (* Clean up all FT2R constants *)
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
 rewrite <- ?(F2R_eq radix2);
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end;
 (* Abstract all FT2R variables *)
 repeat
  match goal with |- context [@FT2R ?t ?e] =>
     is_var e;
     let e' := fresh e in
     set (e' := @FT2R Tsingle e) in *; clearbody e'; clear e; rename e' into e
  end;
 (* clean up all powerRZ expressions *)
 try compute_Zpow.
 (* Don't do field simplify , it can blow things up, and the interval tactic
   doesn't actually need it.
 match goal with |- context [Rabs ?a <= _] => field_simplify a end.
*)


Ltac do_interval :=
lazymatch goal with
 | |- (Rabs ?e <= ?a - ?b)%R =>
    let G := fresh "G" in
    interval_intro (Rabs e) as [_ G];
    tryif is_evar a
    then (eapply Rle_trans; [apply G | clear G ];
             apply Rminus_plus_le_minus;
             apply Rle_refl)
    else (eapply Rle_trans; [apply G | ];
            try solve [compute; lra])
 | |- Rabs ?e <= _ =>
    let G := fresh "G" in
    interval_intro (Rabs e) as [_ G];
    try apply G;
    (eapply Rle_trans; [apply G | ];
     try solve [compute; lra])
end.

Definition find_and_prove_roundoff_bound {NANS}  `{coll: collection}(bmap: boundsmap) {ty} (e: expr ty) :=
  {bound: R | forall vmap, @prove_roundoff_bound NANS _ bmap vmap ty e bound}.


Ltac mult_le_compat_tac :=
try apply Rmult_le_compat; try apply Rabs_pos;
try apply Rmult_le_pos; try apply Rabs_pos;
try apply Rplus_le_le_0_compat; try apply Rabs_pos;
try apply Rmult_le_pos; try apply Rabs_pos;
try apply Rmult_le_pos; try apply Rabs_pos;
try apply Rmult_le_compat; try apply Rabs_pos;
try apply Rplus_le_le_0_compat; try apply Rabs_pos;
try apply Rmult_le_pos; try apply Rabs_pos;
try apply Rmult_le_pos; try apply Rabs_pos;
try apply Rplus_le_compat;
try apply Rmult_le_compat; try apply Rabs_pos.


Ltac error_rewrites :=
try rewrite Rplus_opp;
repeat match goal with
 | |- Rabs((?u1 - ?v1) * ?D + ?E - ?U) <= _ =>
    (replace ((u1 - v1) * D + E - U) with
      ((u1 * D - v1 * D) - U + E)  by nra) ;
(* main rewrite used here is Rminus_rel_error *)
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [rewrite Rminus_rel_error; eapply Rle_trans; [apply Rabs_triang| apply Rplus_le_compat];
          [ try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc
          | try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc]
          |idtac]
 | |- Rabs((?u1 + ?v1) * ?D + ?E - ?U) <= _ =>
    (replace ((u1 + v1) * D + E - U) with
      ((u1 * D + v1 * D) - U + E)  by nra) ;
(* main rewrite used here is Rplus_rel_error *)
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [rewrite Rplus_rel_error ; eapply Rle_trans ;[apply Rabs_triang| idtac] ; apply Rplus_le_compat;
          [ try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc
            | try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc]
          | idtac]
 | |- Rabs((?u1 * ?v1) * ?D + ?E - ?U) <= _ =>
    (replace ((u1 * v1) * D + E - U ) with
      ((u1 * D * v1) - U + E)  by nra);
(* main rewrite used here is Rmult_rel_error *)
        eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat;
        [rewrite Rmult_rel_error; eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat ;
              [eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat;
                  [rewrite Rabs_mult; apply Rmult_le_compat; mult_le_compat_tac|
                    rewrite Rabs_mult; apply Rmult_le_compat; mult_le_compat_tac]]
              | rewrite Rabs_mult; apply Rmult_le_compat; mult_le_compat_tac]  ]
        | idtac ] ] ; try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc
 | |- Rabs((?u1 / ?v1) * ?D + ?E -?U) <= _ =>
    (replace ((u1 / v1) * D + E - U ) with
      ((u1 * D)/v1 -  U + E)  by nra);
(* main rewrite used here is Rdiv_rel_error_no_u_div_reduced *)
        eapply Rle_trans; [apply Rabs_triang| idtac]; apply Rplus_le_compat;
        [eapply Rle_trans;
          [ apply Rdiv_rel_error_no_u_div_reduced; interval (* will sometimes fail *)
          | apply Rmult_le_compat; repeat try mult_le_compat_tac;
             try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc ]
        |try rewrite Rmult_plus_distr_r; try rewrite Rmult_assoc]
 | |- Rabs(- _) <= _ => rewrite Rabs_Ropp
end.

Ltac field_simplify_Rabs :=
match goal with
|- Rabs ?a <= _ =>
field_simplify a;
(repeat split;
try match goal with |-?z <> 0 =>
field_simplify z; interval
end)
end.

Definition hide_constraint {A} (x: A) := x.

Ltac bisect_all_vars t params :=
  lazymatch goal with
  | H: ?lo <= ?x <= ?hi |- ?A =>
    change (hide_constraint (lo <= x <= hi)) in H;
    lazymatch A with
    | context [x] =>
        let params' := constr:(i_bisect x :: params) in
          bisect_all_vars t params'
    | _ => bisect_all_vars t params
    end
  | |- _ => unfold hide_constraint in *;
             Private.do_interval_intro t Interval_helper.ie_none params
  end.

#[export] Existing Instance empty_collection.  (* By default, we don't have any
   nonstandard types. *)
