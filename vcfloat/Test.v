(** Test.v:  some experiments with application of VCFloat.
 Copyright (C) 2021 Andrew W. Appel.  Licensed with the same open-source
 license (GNU GPL v3 or later) as the rest of VCFloat.
*)

From vcfloat Require Import FPLang FPLangOpt RAux Rounding Reify.
Require Import compcert.common.AST compcert.common.Values.
Require Import compcert.lib.Floats.
Import Binary.
Import Rounding.
(*Import FPSolve.*)
Set Bullet Behavior "Strict Subproofs".

(*
Definition empty_env := env_ (Maps.PTree.empty val).

Lemma empty_env_finite: 
     forall (ty : type) (i : positive),
       is_finite (fprec ty) (femax ty) (empty_env ty i) = true.
Proof.
 apply env_finite.
 intros. rewrite Maps.PTree.gempty in H. inversion H.
Qed.

Require Import Lia Lra.

Definition empty_errors : nat -> R := fun _ => 0%R.

*)

Open Scope R_scope.


Definition FT2R (t: type) : ftype t -> R := B2R (fprec t) (femax t).

Import Interval.Tactic.

Record varinfo := {var_type: type; var_name: ident; var_lobound: R; var_hibound: R}.
Definition boundsmap := Maps.PTree.t varinfo.
Definition valmap := Maps.PTree.t (sigT ftype).

Definition ftype_of_val (v: sigT ftype) : type := projT1 v.
Definition fval_of_val (v: sigT ftype): ftype (ftype_of_val v) := projT2 v.

Definition bogus_type : type.
 refine {| fprecp := 2; femax := 3 |}.
 constructor. simpl. auto.
Defined.

Definition bogus_val : ftype bogus_type := B754_zero _ _ false.

Definition val_of_compcert_val (v: val) : sigT ftype :=
  match v with
  | Vsingle x => existT ftype Tsingle x
  | Vfloat x => existT ftype Tdouble x 
  | _ => existT ftype bogus_type  bogus_val 
 end.

Definition boundsmap_denote (bm: boundsmap) (vm: valmap) : Prop :=
   forall i, 
   match Maps.PTree.get i bm, Maps.PTree.get i vm with
   | Some {|var_type:=t; var_name:=i'; var_lobound:=lo; var_hibound:=hi|}, Some v => 
              i=i' /\ t = projT1 v /\ 
              is_finite (fprec _) (femax _) (projT2 v) = true /\ lo <= FT2R _ (projT2 v) <= hi
   | None, None => True
   | _, _ => False
   end.


Definition boundsmap_denote_pred (vm: valmap) (ib: ident*varinfo) := 
 match ib with
                  (i, {|var_type:=t; var_name:=i'; var_lobound:=lo; var_hibound:=hi|}) =>
                  exists v,
                    i=i' /\
                    Maps.PTree.get i vm = Some v /\
              is_finite (fprec _) (femax _) (projT2 v) = true /\ lo <= FT2R _ (projT2 v) <= hi
                   end.

Lemma boundsmap_denote_e:
  forall bm vm, boundsmap_denote bm vm -> 
 list_forall (boundsmap_denote_pred vm) (Maps.PTree.elements bm).
Proof.
intros.
red in H.
unfold boundsmap_denote_pred.
apply list_forall_spec.
intros [i [t i' lo hi]] ?.
apply Maps.PTree.elements_complete in H0.
specialize (H i). rewrite H0 in H.
destruct (Maps.PTree.get i vm) as [ v | ]; try contradiction.
destruct H as [? [? [? ?]]].
subst.
exists v. auto. 
Qed.

Definition mk_env (bm: boundsmap) (vm: valmap) (ty: type) (i: ident) : ftype ty.
destruct (Maps.PTree.get i bm) as [[t i' lo hi]|] eqn:?H.
destruct (type_eq_dec ty t).
subst.
destruct (Maps.PTree.get i vm) as [v |].
destruct (type_eq_dec (ftype_of_val v) t).
subst.
apply (fval_of_val v).
apply (B754_zero _ _ true).
apply (B754_zero _ _ true).
apply (B754_zero _ _ true).
apply (B754_zero _ _ true).
Defined.


Definition list_to_bound_env 
  (bindings: list  (ident * varinfo)) 
  (bindings2: list  (ident * sigT ftype)) :
  @environ ident :=
 let bm := Maps.PTree_Properties.of_list bindings in
 let vm := Maps.PTree_Properties.of_list bindings2 in 
 mk_env bm vm.

Module Test2.

Import Reify.TEST.
Import List ListNotations.

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

Definition valmap_of_list (vl: list (ident * sigT ftype)) : valmap :=
  fold_left (fun m iv => let '(i,v) := iv in Maps.PTree.set i v m) vl (Maps.PTree.empty _).

Definition leapfrog_bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _x (-1)  1 ;  Build_varinfo Tsingle _v (-1)  1 ].

Definition leapfrog_bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list leapfrog_bmap_list) in exact z).

Definition leapfrog_vmap_list (x v : ftype Tsingle) := 
   [(_x, existT ftype _ x);(_v, existT ftype _ v)].

Definition leapfrog_vmap (x v : ftype Tsingle) : valmap :=
 ltac:(let z := compute_PTree (valmap_of_list (leapfrog_vmap_list x v)) in exact z).

Instance identVars: VarType ident := Build_VarType ident Pos.eqb Pos.eqb_eq.

Import Float_notations.


Definition shiftmap := Maps.PMap.t (type * rounding_knowledge').

Instance shifts_MAP: Map nat (type * rounding_knowledge') shiftmap.
apply compcert_map. apply map_nat.
Defined.

Definition env_ (tenv: valmap) ty v: ftype ty :=
  match Maps.PTree.get v tenv with Some (existT _ t x) =>
      match type_eq_dec ty t with
        | left K => eq_rect_r _ x K
        | _ => B754_zero _ _ true
      end
    | _ => B754_zero _ _ true
  end.

Lemma finite_env (bmap: boundsmap) (vmap: valmap):
      boundsmap_denote bmap vmap ->
forall ty i, is_finite (fprec ty) (femax ty) ((env_ vmap) ty i) = true.
Proof. 
intros.
 unfold  env_.
 specialize (H i).
 destruct (Maps.PTree.get i bmap) as [[t i' lo hi]|],
    (Maps.PTree.get i vmap) as [[t' v]|]; auto.
 destruct H as [? [? [??]]].
simpl in H0, H1, H2.
subst i' t'.
destruct (type_eq_dec ty t); auto.
subst ty.
auto.
Qed.

Section WITHNANS.
Context {NANS: Nans}.

Ltac unfold_fval :=
  cbv beta iota zeta delta [
      fop_of_binop fop_of_rounded_binop cast_lub_l cast_lub_r
      fop_of_unop fop_of_rounded_unop fop_of_exact_unop
      option_pair_of_options];
   try change (type_lub _ _) with Tsingle;
   try change (type_lub _ _) with Tdouble;
   repeat change (type_lub ?x ?y) with x;
   repeat change (type_lub ?x ?y) with y;
   repeat change (binop_eqb _ _) with true;
   repeat change (binop_eqb _ _) with false;
   cbv match;
   repeat change (cast ?a _ ?x) with x.


Goal  fshift_div (fcval x') = x'.
unfold x' at 1.
cbv delta [fshift_div fcval fcval_nonrec]; unfold_fval.
Abort.

Definition rndval_with_cond_result1 env e (r: @rexpr ident) (s: Maps.PMap.t (type * rounding_knowledge')) :=
    exists errors,
        (errors_bounded s errors)
        /\
        let fv := fval env e in
        is_finite _ _ fv = true
        /\
        reval r env errors = B2R _ _ fv.


Lemma boundsmap_denote_pred_e:
  forall vm i' t i lo hi,
    boundsmap_denote_pred vm (i',
     {| var_type := t; var_name := i; var_lobound := lo; var_hibound := hi |}) ->
    match Maps.PTree.get i vm with
     | Some (existT _ t v) => (lo <= FT2R t v <= hi)%R                         
     | None => False
    end.
Proof.
intros.
destruct H.
destruct x.
destruct H as [? [? [??]]].
subst.
simpl in *. rewrite H0. auto.
Qed.

Definition eval_cond' s (c: cond) (env: environ) : Prop :=
  @eval_cond2 ident _ shifts_MAP _ (compcert_map nat R map_nat) env s c.


Definition rndval_with_cond2 (e: expr) : rexpr * shiftmap * list (environ -> Prop) :=
 let '((r,(si,s)),p) := rndval_with_cond' 0 empty_shiftmap e
  in (r, s, map (eval_cond' s) p).

Lemma rndval_with_cond_correct2:
 forall 
  (e: expr) (VALID: expr_valid e = true)
  (bm: boundsmap) (vm: valmap),
  boundsmap_denote bm vm ->
  let '(r,s,p) := rndval_with_cond2 e in 
  Forall (fun c => c (env_ vm)) p ->
  exists errors,
      (errors_bounded s errors) /\
        let fv := fval (env_ vm) e in
        is_finite _ _ fv = true
        /\ reval r (env_ vm) errors = B2R _ _ fv.
Proof.
intros.
assert (env_all_finite (env_ vm)) by (intros ? ? ; eapply finite_env; eauto).
destruct ( rndval_with_cond e) as [[r s] p] eqn:?H.
pose proof (rndval_with_cond_correct _ H0 _ VALID _ _ _ H1).
unfold rndval_with_cond in H1.
unfold rndval_with_cond2.
destruct (rndval_with_cond' 0 empty_shiftmap e) as [[? [? ?]] ?].
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

Lemma invert_quad:
  forall (a a': @rexpr ident) (b b': nat) (c c': shiftmap) (d d': list (@cond ident)) (G: Prop),
  (a=a' -> b=b' -> c=c' -> d=d' -> G) ->
  (a,(b,c),d) = (a',(b',c'),d') -> G.
Proof.
intros.
inversion H0; auto.
Qed.

Ltac invert_rndval_with_cond' :=
 match goal with
 | |- rndval_with_cond' 0 empty_shiftmap ?e = (_, (_,_), _) -> ?M' =>
    let M := fresh "M" in set (M:=M');
   cbv beta iota zeta delta [rndval_with_cond' rnd_of_binop_with_cond
          rnd_of_unop_with_cond is_div
          Rbinop_of_rounded_binop Runop_of_exact_unop Runop_of_rounded_unop
          type_of_expr make_rounding round_knowl_denote];
   try change (type_lub _ _) with Tsingle;
   try change (type_lub _ _) with Tdouble;
   repeat change (type_lub ?x ?y) with x;
   repeat change (type_lub ?x ?y) with y;
   repeat change (binop_eqb _ _) with true;
   repeat change (binop_eqb _ _) with false;
 cbv beta iota zeta delta [rounding_cond_ast no_overflow app];
 match goal with |- (?r1,(_, ?s1), ?l1) = _ -> _ =>
    let r' := fresh "r" in let s' := fresh "s" in let l' := fresh "l" in 
    set (r' := r1); set (s' := s1); set (l' := l1);
    let H1 := fresh "H" in 
     apply invert_quad; intros; subst;

     cbv beta iota zeta delta [mset shifts_MAP empty_shiftmap mempty
            compcert_map Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set' 
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
            index_of_tr map_nat fst snd] in s';

     subst r'; subst s'; subst l'
  end;
  subst M
 | _ => fail "invert_rndval_with_cond' at inappropriate goal"
 end.

Ltac process_boundsmap_denote :=
 lazymatch goal with
 | H: boundsmap_denote _ _ |- _ =>
  apply boundsmap_denote_e in H;
  simpl Maps.PTree.elements in H;
  unfold list_forall in H;
  decompose [and] H; clear H;
  repeat match goal with H: boundsmap_denote_pred _ _ |- _ => 
     apply boundsmap_denote_pred_e in H; simpl in H
   end
end.

Ltac process_eval_cond' :=
 lazymatch goal with 
 | |- eval_cond' _ _ _ => idtac
 | _ => fail 1 "inappropriate goal for process_eval_cond'"
 end;
    hnf;
  repeat 
   (let H := fresh in intros ?u H;
    cbv beta iota zeta delta [
    mget shifts_MAP compcert_map
    Maps.PMap.get Maps.PTree.get Maps.PTree.get'
      Pos.of_succ_nat Pos.succ
      index_of_tr map_nat fst snd] in H;
    unfold error_bound in H;
    simpl in H;
    unfold Z.pow_pos in H;
    simpl Pos.iter in H);

   cbv beta iota zeta delta [
            mset shifts_MAP empty_shiftmap mempty
            compcert_map Maps.PMap.set Maps.PMap.init
            Maps.PTree.empty Maps.PTree.set Maps.PTree.set' 
              Maps.PTree.set0 Pos.of_succ_nat Pos.succ
            index_of_tr map_nat fst snd];

 cbv beta iota zeta delta [reval
     Prog.binary Prog.unary Prog.real_operations
   Tree.binary_real Tree.unary_real
  ];

  cbv beta iota zeta delta [
    mget shifts_MAP compcert_map
    Maps.PMap.get Maps.PTree.get Maps.PTree.get'
      Pos.of_succ_nat Pos.succ
      index_of_tr map_nat fst snd];

 repeat 
   match goal with |- context [env_ ?m ?t ?i ] =>
     let j := fresh "j" in set (j := env_ m t i); hnf in j; subst j
   end;
 
  change (B2R (fprec ?t) _ ?x) with (FT2R t x).

Axiom proof_irr: forall (A: Prop) (x y: A), x=y.

Ltac simplify_consts :=
 lazymatch goal with
 | |- context [Const ?t ?x] =>
   let j := fresh "j" in let k := fresh "k" in 
      set (k := x); 
     set (j := Const t k); 
      idtac "simplifying" x;
      time simpl in k; subst k;
      revert j; 
      try replace (proj1 _) with (eq_refl true) by apply proof_irr;
      intro j;
      simplify_consts;
     subst j
 | _ => idtac
 end.

Ltac simplify_expr' j :=
  cbv beta iota zeta delta [
      fop_of_binop fop_of_rounded_binop cast_lub_l cast_lub_r
      fop_of_unop fop_of_rounded_unop fop_of_exact_unop
      option_pair_of_options] in j;
   try change (type_lub _ _) with Tsingle in j;
   try change (type_lub _ _) with Tdouble in j;
   repeat change (type_lub ?x ?y) with x in j;
   repeat change (type_lub ?x ?y) with y in j;
   repeat change (binop_eqb _ _) with true in j;
   repeat change (binop_eqb _ _) with false in j;
   cbv match in j;
   repeat change (cast ?a _ ?x) with x in j.

Ltac simplify_expr e :=
 (* take an expression "e" of the form (fshift_div e) or (fshift e)
          or (fcval e), or any sequence of those operators,
     above or below the line,  and reduce it  *)
  let j := fresh "j" in set (j := e) in *;
 hnf in j;
 cbv delta [fcval fcval_nonrec] in j; simplify_expr' j;
 cbv delta [fshift_div fshift fcval fcval_nonrec] in j;simplify_expr' j;
 subst j;
 simplify_consts.

Definition prove_rndval bm vm e :=
 boundsmap_denote bm vm ->
  let
   '(r, s, _) := rndval_with_cond2 e in
    rndval_with_cond_result1 (env_ vm) e r s.

Ltac prove_rndval :=
 lazymatch goal with
 | |- prove_rndval ?bm ?vm ?e => 
      simplify_expr e
 | _ => idtac
 end;
 lazymatch goal with
 | |- prove_rndval ?bm ?vm ?e => 
   let H := fresh in let H0 := fresh in 
   intro H;
   assert (H0 := rndval_with_cond_correct2 e (eq_refl _) _ _ H);
   let r := fresh "r" in let s := fresh "s" in let p := fresh "p" in
   let H1 := fresh in
   destruct (rndval_with_cond2 e) as [[r s] p] eqn:H1;
   apply H0; clear H0;
   revert H1;
   unfold rndval_with_cond2;
   let r1 := fresh "r" in let si1 := fresh "si" in let s1 := fresh "s" in let p := fresh "p" in
   let H2 := fresh in 
   destruct (rndval_with_cond' _ _ _) as [[r1 [si1 s1]] p1] eqn:H2;
   intro H1; inversion H1; clear H1; subst;
   revert H2;
   invert_rndval_with_cond';
   process_boundsmap_denote;
   repeat apply Forall_cons; try apply Forall_nil;
   process_eval_cond'
 | _ => fail 1 "inappropriate goal for prove_rndval"
 end.

Lemma rndval_with_cond_correct_optx:
  forall x v : float32,
  prove_rndval  (leapfrog_bmap ) (leapfrog_vmap x v) (fshift_div (fcval x')).
Proof.
intros.
prove_rndval; simpl; interval.
Qed.


Lemma rndval_with_cond_correct_optv:
  forall x v : float32,
  prove_rndval  (leapfrog_bmap ) (leapfrog_vmap x v) (fshift_div (fcval v')).
Proof.
intros.
prove_rndval; simpl; interval.
Qed.

End WITHNANS.
End Test2.


