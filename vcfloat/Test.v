Require Import FPLang FPLangOpt FPSolve.
Require Import compcert.common.AST compcert.common.Values.
Require Import compcert.lib.Floats.
Import Binary.
Import FPSolve.

Definition shiftmap := Maps.PMap.t (type * rounding_knowledge).

Instance shifts_MAP: Map nat (type * rounding_knowledge) shiftmap.
apply compcert_map. apply map_nat.
Defined.

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

Definition environ {V} := 
   forall ty: type, V -> binary_float (fprec ty) (femax ty).

Definition env_all_finite {V} (env: environ) :=
  forall (ty : type) (i : V),
        is_finite (fprec ty) (femax ty) (env ty i) = true.

Definition errors_bounded {MSHIFT} 
     {MAP : Map nat (type * rounding_knowledge) MSHIFT}
    (shift: MSHIFT) (errors: nat -> R) := 
   forall i ty k,
         mget shift i = (ty, k) ->
         (Rabs (errors i) <= error_bound ty k)%R.

Open Scope R_scope.

Definition sqrt_of_one : @expr AST.ident := Unop (Rounded1 SQRT None) (Const Tsingle (B2 _ 0)).

Definition _x : AST.ident := 5%positive.
Definition _v : AST.ident := 7%positive.

Definition h :=  B2 Tsingle (-5).
Definition half := B2 Tsingle (-1).

Definition F (x: @expr AST.ident) : @expr AST.ident :=
   Unop (Exact1 Opp) x.

Definition leapfrog_x : @expr AST.ident :=
 Binop (Rounded2 PLUS None) 
  (Binop (Rounded2 PLUS None) (Var Tsingle _x) 
         (Binop (Rounded2 MULT None) (Const Tsingle h) (Var Tsingle _v)))
  (Binop (Rounded2 MULT None)
   (Binop (Rounded2 MULT None)
     (Const Tsingle half) 
     (Binop (Rounded2 MULT None) (Const Tsingle h)  (Const Tsingle h)))
   (F (Var Tsingle _x))).

Lemma power_RZ_inv: forall x y, x <> 0 -> Rinv (powerRZ x y) = powerRZ x (-y).
Proof.
intros.
destruct y; simpl; auto.
apply Rinv_1.
apply Rinv_involutive.
apply pow_nonzero.
auto.
Qed.

Definition FT2R (t: type) : ftype t -> R := B2R (fprec t) (femax t).

Import Interval.Tactic.

Record varinfo := {var_type: type; var_name: AST.ident; var_lobound: R; var_hibound: R}.
Definition boundsmap := Maps.PTree.t varinfo.
Definition valmap := Maps.PTree.t val.

Definition bogus_type : type.
 refine 
 {| fprecp := 2; femax := 3 |}.
 constructor. simpl. auto.
Defined.

Definition bogus_val : ftype bogus_type := B754_zero _ _ false.

Definition ftype_of_val (v: val) := 
  match v with Vsingle _ => Tsingle | Vfloat _ => Tdouble | _ => bogus_type end.

Definition fval_of_val (v: val): ftype (ftype_of_val v) := 
 match v as v0 return (ftype (ftype_of_val v0)) with
 | Vfloat f => f
 | Vsingle f => f
 | _ => bogus_val
 end.

Definition boundsmap_denote (bm: boundsmap) (vm: valmap) : Prop :=
   forall i, 
   match Maps.PTree.get i bm, Maps.PTree.get i vm with
   | Some {|var_type:=t; var_name:=i'; var_lobound:=lo; var_hibound:=hi|}, Some v =>  
              exists x, i=i' /\ val_inject v t x /\
              is_finite (fprec t) (femax t) x = true /\ lo <= FT2R t x <= hi
   | None, None => True
   | _, _ => False
   end.

Definition boundsmap_denote_pred (vm: valmap) (ib: ident*varinfo) := 
 match ib with
                  (i, {|var_type:=t; var_name:=i'; var_lobound:=lo; var_hibound:=hi|}) =>
                  exists v, exists x,
                    i=i' /\
                    Maps.PTree.get i vm = Some v /\
                    val_inject v t x /\
              is_finite (fprec t) (femax t) x = true /\ lo <= FT2R t x <= hi
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
destruct (Maps.PTree.get i vm); try contradiction.
destruct H as [x [? [? [? ?]]]].
exists v,x. auto. 
Qed.

Definition mk_env (bm: boundsmap) (vm: valmap) (ty: type) (i: AST.ident) : ftype ty.
destruct (Maps.PTree.get i bm) as [[t i' lo hi]|] eqn:?H.
destruct (type_eq_dec ty t).
subst.
destruct (Maps.PTree.get i vm).
destruct (type_eq_dec (ftype_of_val v) t).
subst.
apply (fval_of_val v).
apply (B754_zero (fprec t) (femax t) true).
apply (B754_zero (fprec t) (femax t) true).
apply (B754_zero (fprec ty) (femax ty) true).
apply (B754_zero (fprec ty) (femax ty) true).
Defined.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma env_mk_env: 
  forall bmap vmap, boundsmap_denote bmap vmap ->
        env_ vmap = mk_env bmap vmap.
Proof.
intros.
apply functional_extensionality_dep; intro ty.
apply functional_extensionality; intro i.
unfold mk_env, env_.
specialize (H i).
 destruct (Maps.PTree.get i bmap) as [[t i' lo hi]|],
    (Maps.PTree.get i vmap) as [v|]; try contradiction; auto.
 destruct H as [x [_ [? _]]].
 inversion H; clear H; subst.
 destruct (type_eq_dec _ _); simpl in *; auto.
 destruct (type_eq_dec _ _); simpl in *; auto.
Qed.

Lemma calculate_rndval:
  forall (bmap: boundsmap) (vmap: valmap) (e: @expr AST.ident),
      expr_valid e = true ->
      boundsmap_denote bmap vmap ->
  forall r si2 s p,
   rndval_with_cond 0 (mempty  (Tsingle, Normal)) e = (r,(si2,s),p) ->
   list_forall (eval_cond2 (mk_env bmap vmap) s) p ->
   rndval_with_cond_result  (env_ vmap) e r si2 s.
Proof.
intros.
set (nv := env_ vmap) in *.
assert (EFIN: forall ty i, is_finite (fprec ty) (femax ty) (nv ty i) = true). {
 intros.
 unfold nv, env_.
 specialize (H0 i).
 destruct (Maps.PTree.get i bmap) as [[t i' lo hi]|],
    (Maps.PTree.get i vmap) as [v|]; auto.
 destruct H0 as [x [_ [? [? ?]]]].
 destruct v; simpl in *; auto.
 assert (t=Tdouble) by (inversion H0; subst; auto). subst.
 assert (f=x) by (inversion H0; clear H0; subst; apply Eqdep.EqdepTheory.inj_pair2 in H7; subst; auto).
 subst.
 destruct (type_eq_dec ty Tdouble); [ | reflexivity].
 subst; auto.
 assert (t=Tsingle) by (inversion H0; subst; auto). subst.
 assert (f=x) by (inversion H0; clear H0; subst; apply Eqdep.EqdepTheory.inj_pair2 in H7; subst; auto).
 subst.
 destruct (type_eq_dec ty Tsingle); [ | reflexivity].
 subst; auto.
}
apply (rndval_with_cond_correct _ EFIN _ H r si2 s p); auto.
rewrite <- env_mk_env in H2; auto. 
Qed.

Lemma list_forall_Forall:
  forall {A} f (al: list A),
   list_forall f al <-> List.Forall f al.
Proof.
induction al; split; intro.
constructor.
constructor.
destruct al.
constructor; auto.
destruct H; constructor; auto.
rewrite <- IHal; auto.
inversion H; clear H; subst.
destruct al.
auto.
constructor; auto.
rewrite IHal; auto.
Qed.

Ltac prepare_assumptions_about_free_variables :=
match goal with
  H: List.Forall (boundsmap_denote_pred ?vmap) (Maps.PTree.elements ?bmap)
  |- List.Forall (eval_cond2 (mk_env ?bmap ?vmap) ?s )?p
  => 
repeat
 (let j := fresh "j" in let t := fresh "t" in let i' := fresh "i'" in 
  let lo := fresh "lo" in let hi := fresh "hi" in let yy := fresh "yy" in 
 let v := fresh "v" in 
 let x := fresh "x" in let U := fresh "U" in let W := fresh "W" in
 let Hx := fresh "Hx" in let Hj := fresh "Hj" in let Ht := fresh "Ht"  in
 let Hi := fresh "Hi" in  
inversion H as [ | [j [t i' lo hi]] yy [v [x [U W]]] Hx [Hj Ht Hi]];
 clear H; rename Hx into H;
 rewrite U in *; clear U;
subst j t lo hi yy;
 match type of Hi with _ = ?i =>
  let valx := fresh "val" i in 
  let Hval := fresh "Hval" i in
  let Hinj := fresh "Hinj" i in
  let Hfin := fresh "Hfin" i in
  let Hrange := fresh "Hrange" i in
  rename x into valx;
  destruct W as [Hval [Hinj [Hfin Hrange]]];
 first [apply val_inject_single_inv_r in Hinj
       | apply val_inject_double_inv_r in Hinj
       | fail 88 "val_inject_inv failed" ];
  subst v i'
 end);
 match type of H with List.Forall _ nil => clear H end
 end.

Ltac solve_all_eval_cond2 :=
match goal with
 H0: rndval_with_cond 0 _ _ = (_, (_, _), _) |- _ =>
 inversion H0; clear H0; subst
end;
repeat
    match goal with |- context [ type_lub ?a ?b ] =>
     first [change (type_lub a b) with Tsingle 
            |change (type_lub a b) with Tdouble]
    end;
match goal with |- List.Forall (eval_cond2 _ ?M) _ =>
   let m := fresh "m" in set (m:=M); compute in m; subst m;
  fold Tsingle; fold Tdouble
end;
repeat (apply List.Forall_cons; try apply List.Forall_nil).

Lemma lesseq_less_or_eq:
 forall x y : R,  x <= y -> x < y \/ x = y.
Proof. intros. lra. Qed.

Ltac solve_one_eval_cond2 := 
match goal with |- eval_cond2 (mk_env ?bmap ?vmap) _ _ =>
 hnf;
 repeat
 (match goal with |- context [@mget _ _ _ _ _ _]  =>
       let x := fresh "x" in set (x := @mget _ _ _ _ _ _); compute in x; subst x
   end;
 cbv beta iota;
 fold Tsingle; fold Tdouble);
 repeat 
  (let H := fresh in intros ? H;
   simpl in H; cbv beta iota delta [error_bound Tsingle Tdouble fprec] in H;
   simpl in H);
 match goal with |- context [reval _ _ (mget ?M)] =>
   let m := fresh "m" in set (m:=M); compute in m;
    unfold reval;
    repeat match goal with |- context [@mget _ _ _ ?MAP m ?i]  =>
       let x := fresh "x" in set (x := @mget _ _ _ MAP m i); compute in x; subst x
   end;
   clear m
  end;
 simpl;
 rewrite ?Pos2Z.inj_pow_pos, ? IZR_Zpower_pos in *;
  rewrite ?power_RZ_inv  in * by lra;
   rewrite <- ?powerRZ_add in * by lra;
   simpl Z.add;
 repeat
  match goal with |- context [mk_env bmap vmap ?ty ?v'] =>
       match goal with H: Maps.PTree.get ?v vmap = _ |- _ =>
         change (mk_env bmap vmap ty v') with (mk_env bmap vmap ty v);
         let x := fresh "x" in set (x := mk_env _ vmap _ v); 
         hnf in x; (* ; rewrite H in x;  *)
        let jj := fresh "jj" in 
         set (jj := Maps.PTree.get v vmap) in *; clearbody jj; subst jj;
             compute in x; subst x
  end end;
 repeat change (B2R (fprec ?x) _) with (FT2R x);
 try apply lesseq_less_or_eq;
 rewrite ?Rmult_1_l;
 try interval
end.

Ltac prove_exists_rndval_with_cond_result := 
match goal with
 |- forall vmap: valmap,
     boundsmap_denote ?bmap vmap ->
  exists
  (r : rexpr) (si2 : nat) (s : Maps.PMap.t (type * rounding_knowledge)),
  rndval_with_cond_result (env_ vmap) ?e r si2 s
 =>
let H := fresh in intros ?vmap H;
let H0 := fresh "H0" in 
let r := fresh "r" in let si2 := fresh "si2" in let s := fresh "s" in let p := fresh "p" in 
destruct (rndval_with_cond O (mempty  (Tsingle, Normal)) e) as [[r [si2 s]] p] eqn:H0;
exists r,si2,s;
let H1 := fresh "H1" in 
assert (H1: expr_valid e = true) by reflexivity;
apply (calculate_rndval _ _ _ H1 H r si2 s p H0);
clear H1;
apply boundsmap_denote_e in H;
rewrite list_forall_Forall in H;
rewrite list_forall_Forall
end;
prepare_assumptions_about_free_variables;
solve_all_eval_cond2;
solve_one_eval_cond2.

Definition optimize {V: Type} {NANS: Nans} (e: expr) : expr :=
  @fshift V NANS (@fcval V NANS e).

Lemma optimize_type {V: Type}{NANS: Nans}: 
   forall e: expr, @type_of_expr V (optimize e) = @type_of_expr V e.
Proof.
intros.
apply (eq_trans (fshift_type (fcval e)) (@fcval_type V NANS e)) .
Defined.

Definition optimize_correct {V: Type} {NANS: Nans}: 
  forall env e,  (fval env (optimize e)) = eq_rect_r ftype (fval env e) (@optimize_type V NANS e).
Proof.
intros.
unfold optimize.
rewrite fshift_correct.
rewrite (@fcval_correct V NANS env).
unfold eq_rect_r.
rewrite rew_compose.
f_equal.
rewrite <- eq_trans_sym_distr.
f_equal.
Qed.

Lemma binary_float_eqb_eq_rect_r:
 forall ty1 ty2 (a b: binary_float (fprec ty2) (femax ty2))
  (H: ty1=ty2),
@binary_float_eqb (fprec ty1) (femax ty1) (fprec ty2) (femax ty2) 
  (@eq_rect_r type ty2 ftype a ty1 H) b = 
  binary_float_eqb a b.
Proof.
intros. subst ty2.
reflexivity.
Qed.

Definition optimize_correct' {V: Type} {NANS: Nans}:
  forall env e, 
   binary_float_eqb (fval env (@optimize V NANS e)) (fval env e) = true.
Proof.
intros.
rewrite optimize_correct.
rewrite binary_float_eqb_eq_rect_r.
apply binary_float_eqb_eq. auto.
Qed.

Lemma experiment1: 
   let e := leapfrog_x in 
   let bmap := Maps.PTree.set _v {|var_type:=Tsingle; var_name:=_v; var_lobound:=-1; var_hibound:=1|}
                       (Maps.PTree.set _x {|var_type:=Tsingle; var_name:=_x; var_lobound:=-1; var_hibound:=1|}
                         (Maps.PTree.empty _)) in 
   forall vmap : valmap,
      boundsmap_denote bmap vmap ->
  exists r: rexpr, exists si2 : nat, exists (s : Maps.PMap.t (type * rounding_knowledge)),
   rndval_with_cond_result  (env_ vmap) e r si2 s.
Proof.
intros ? ?.
 prove_exists_rndval_with_cond_result.
Qed.

Lemma experiment2: 
   let e := leapfrog_x in 
   let bmap := Maps.PTree.set _v {|var_type:=Tsingle; var_name:=_v; var_lobound:=-1; var_hibound:=1|}
                       (Maps.PTree.set _x {|var_type:=Tsingle; var_name:=_x; var_lobound:=-1; var_hibound:=1|}
                         (Maps.PTree.empty _)) in 
   forall vmap : valmap,
      boundsmap_denote bmap vmap ->
  exists r: rexpr, exists si2 : nat, exists (s : Maps.PMap.t (type * rounding_knowledge)),
   rndval_with_cond_result  (env_ vmap) (optimize e) r si2 s.
Proof.
intros ? ?.
 set (e' := optimize e). compute in e'.
 fold Tsingle in e'.
 change (Var Tsingle 5%positive) with (Var Tsingle _x) in e'.
 change (Var Tsingle 7%positive) with (Var Tsingle _v) in e'.
 clear e.
 prove_exists_rndval_with_cond_result.
Abort.

