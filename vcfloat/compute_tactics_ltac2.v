Require Import Ltac2.Ltac2.
Require Import Ltac2.Printf.
Require Import Ltac2.Bool.
Local Set Warnings "-ltac2-unused-variable".

(** * Restricted reduction/evaluation/computation *)

(** ** Ltac2 utilities *)

(** Get first and second of a pair *)

Ltac2 pair_first (x : 'a*'b) : 'a := let (a,b):=x in a.
Ltac2 pair_second (x : 'a*'b) : 'b := let (a,b):=x in b.

(** Type checker which throws an invalid argument in case the term does not type check *)

Ltac2 check_throw (term : constr) : constr :=
  match Constr.Unsafe.check term with
  | Val c => c
  | Err e => Control.throw e
  end.

(** Print the context (useful for creating a Goal for debugging)

    With these options:

      Set Printing Depth 1000.
      Set Printing Width 240.
      Unset Printing Notations.
      Set Printing Implicit.

    print_context should produce text which Coq can parse as Goal.
*)

Ltac2 print_hyps () :=
  let rec aux (hyps : (ident * constr option * constr) list) :=
    match hyps with
    | [] => ()
    | h :: t =>
      let (id, value, type) := h in
      match value with
      | Some value => printf "let %I := %t : %t in " id value type
      | None => printf "forall (%I : %t), " id type
      end;
      aux t
    end in
  aux (Control.hyps ())
.

Ltac2 print_goal () :=
  lazy_match! goal with
  | [ |- ?g ] => printf "%t" g
  end.

Ltac2 print_context () :=
    printf "Goal";
    print_hyps ();
    print_goal ();
    printf "."
  .

(** ** Construction of Ltac2 reductions flag records *)

Ltac2 redflags_full () :=
{
  (* beta: expand the application of an unfolded functions by substitution *)
  Std.rBeta := true;
  (* delta: true = expand all but rConst; false = expand only rConst *)
  Std.rDelta := true;
  (* Note: iota in tactics like cbv is a shorthand for match, fix and cofix *)
  (* iota-match: simplify matches by choosing a pattern *)
  Std.rMatch := true;
  (* iota-fix: simplify fixpoint expressions by expanding one level *)
  Std.rFix := true;
  (* iota-cofix: simplify cofixpoint expressions by expanding one level *)
  Std.rCofix := true;
  (* zeta: expand let expressions by substitution *)
  Std.rZeta := true;
  (* Symbols to expand or not to expand (depending on rDelta) *)
  Std.rConst := [];
  (* Just guessing that Norm is the right thing here: *)
  Std.rStrength := Std.Norm
}.

(** ** Ltac2 functions for evaluation restricted reductions on a term *)

(** ** CBV under application of the given head term with limited recursion:
 - arguments and function terms in applications
 - bound terms of products and lambdas
 - bound terms and values of let in bindings
 - values of cast expressions
 - values or primitive projections
 - match expressions and match case functions in matches, but no match return types
fixpoints, types and native arrays are copied unchanged.
The function returns a pair with a bool, which indicates if the match term was found and cbv was called on a part of the term.
There is an extended recusion variant of the function below.
*)

Ltac2 rec eval_cbv_uao_lr (head : constr) (rf : Std.red_flags) (term : constr) : constr * bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App func args =>
      if Constr.equal head func
      then
        (Std.eval_cbv rf term, true)
      else
        let (func_r, func_m) := eval_cbv_uao_lr head rf func in
        let args_e := Array.map (eval_cbv_uao_lr head rf) args in
        if func_m || (Array.exist pair_second args_e)
        then (Constr.Unsafe.make (Constr.Unsafe.App func_r (Array.map pair_first args_e)), true)
        else (term, false)

  | Constr.Unsafe.Prod binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_lr head rf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Prod binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.Lambda binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_lr head rf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Lambda binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.LetIn binder value bound =>
      let (value_r, value_m) := eval_cbv_uao_lr head rf value in
      let (bound_r, bound_m) := eval_cbv_uao_lr head rf bound in
      if value_m || bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.LetIn binder value_r bound_r), true)
      else (term, false)

  | Constr.Unsafe.Cast value cast type =>
      let (value_r, value_m) := eval_cbv_uao_lr head rf value in
      if value_m
      then (Constr.Unsafe.make (Constr.Unsafe.Cast value_r cast type), true)
      else (term, false)

(*  Commented this out for Coq 8.19
  | Constr.Unsafe.Proj projection value =>
      let (value_r, value_m) := eval_cbv_uao_lr head rf value in
      if value_m
      then  (Constr.Unsafe.make (Constr.Unsafe.Proj projection value_r), true)
      else (term, false)
*)

  | Constr.Unsafe.Case case_a constr_return case_b constr_match case_funcs =>
      let (match_r, match_m) := eval_cbv_uao_lr head rf constr_match in
      let case_funcs_e := Array.map (eval_cbv_uao_lr head rf) case_funcs in
      if match_m || (Array.exist pair_second case_funcs_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Case case_a constr_return case_b match_r (Array.map pair_first case_funcs_e)), true)
      else (term, false)

  | _ => (term, false)
  end.

(** ** CBV under application of the given head term with almsot full recusion.
    The search does not recurse into types in binders, because with Coq 8.16 Ltac2 one cannot safely reconstruct the term (fixed in 8.17)
*)

Ltac2 rec eval_cbv_uao_afr (head : constr) (rf : Std.red_flags) (term : constr) : constr * bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App func args =>
      if Constr.equal head func
      then
        (Std.eval_cbv rf term, true)
      else
        let (func_r, func_m) := eval_cbv_uao_afr head rf func in
        let args_e := Array.map (eval_cbv_uao_afr head rf) args in
        if func_m || (Array.exist pair_second args_e)
        then (Constr.Unsafe.make (Constr.Unsafe.App func_r (Array.map pair_first args_e)), true)
        else (term, false)

  | Constr.Unsafe.Prod binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_afr head rf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Prod binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.Lambda binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_afr head rf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Lambda binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.LetIn binder value bound =>
      let (value_r, value_m) := eval_cbv_uao_afr head rf value in
      let (bound_r, bound_m) := eval_cbv_uao_afr head rf bound in
      if value_m || bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.LetIn binder value_r bound_r), true)
      else (term, false)

  | Constr.Unsafe.Cast value cast type =>
      let (value_r, value_m) := eval_cbv_uao_afr head rf value in
      let (type_r, type_m) := eval_cbv_uao_afr head rf type in
      if value_m || type_m
      then (Constr.Unsafe.make (Constr.Unsafe.Cast value_r cast type_r), true)
      else (term, false)


(*  Commented this out for Coq 8.19
  | Constr.Unsafe.Proj projection value =>
      let (value_r, value_m) := eval_cbv_uao_afr head rf value in
      if value_m
      then  (Constr.Unsafe.make (Constr.Unsafe.Proj projection value_r), true)
      else (term, false)
*)
  | Constr.Unsafe.Case case_a constr_return_rel case_b constr_match case_funcs =>
      let (constr_return, relev) := constr_return_rel in
      let (return_r, return_m) := eval_cbv_uao_afr head rf constr_return in
      let (match_r, match_m) := eval_cbv_uao_afr head rf constr_match in
      let case_funcs_e := Array.map (eval_cbv_uao_afr head rf) case_funcs in
      if return_m || match_m || (Array.exist pair_second case_funcs_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Case case_a (return_r,relev) case_b match_r (Array.map pair_first case_funcs_e)), true)
      else (term, false)

  | Constr.Unsafe.Fix int_arr int binder_arr constr_arr =>
      let constr_arr_e := Array.map (eval_cbv_uao_afr head rf) constr_arr in
      if (Array.exist pair_second constr_arr_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Fix int_arr int binder_arr (Array.map pair_first constr_arr_e)), true)
      else (term, false)

  | Constr.Unsafe.CoFix int binder_arr constr_arr =>
      let constr_arr_e := Array.map (eval_cbv_uao_afr head rf) constr_arr in
      if (Array.exist pair_second constr_arr_e)
      then (Constr.Unsafe.make (Constr.Unsafe.CoFix int binder_arr (Array.map pair_first constr_arr_e)), true)
      else (term, false)

  | Constr.Unsafe.Array instance constr_arr constr_a constr_b =>
      let (constr_a_r, constr_a_m) := eval_cbv_uao_afr head rf constr_a in
      let (constr_b_r, constr_b_m) := eval_cbv_uao_afr head rf constr_b in
      let constr_arr_e := Array.map (eval_cbv_uao_afr head rf) constr_arr in
      if constr_a_m || constr_b_m || (Array.exist pair_second constr_arr_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Array instance (Array.map pair_first constr_arr_e) constr_a_r constr_b_r), true)
      else (term, false)

  | _ => (term, false)
  end.

(** ** Ltac2 tactics for evaluation restricted reductions on a term *)

Ltac2 cbv_uao_lr (head : constr) : unit :=
    let goal := Control.goal() in
    let (goal_r, goal_m) := eval_cbv_uao_lr head (redflags_full ()) goal in
    (* The line below can be commented out for performance tests - it is just an extra debug type check*)
    let goal_r := check_throw goal_r in
    change $goal_r.

Ltac2 cbv_uao_afr (head : constr) : unit :=
    let goal := Control.goal() in
    let (goal_r, goal_m) := eval_cbv_uao_afr head (redflags_full ()) goal in
    (* The line below can be commented out for performance tests - it is just an extra debug type check*)
    let goal_r := check_throw goal_r in
    change $goal_r.

(** ** Ltac1 wrapper *)

(** compute_every f
    will find every term below the line of the form  (f _) or (f _ _) etc. whose head is f,
    and fully reduce it using "compute".
    This tactic does NOT look for (f _) within types, fixpoints or native arrays.
*)
Ltac compute_every :=
  ltac2:(f |- compute_tactics_ltac2.cbv_uao_lr (Option.get (Ltac1.to_constr f))).

(** ** Tests / examples *)

(* Switch to normal Ltac1 mode (this is only required if Ltac2.Ltac2 is imported) *)
Set Default Proof Mode "Classic".

(* Test limited rewrite *)
Goal forall x:nat, let f := (fun x => x+2*3) in (x + (f (2*3)) + (2*3) + 2*3+4*5*6 = x + 144).
ltac2:(cbv_uao_afr '@Nat.mul).
(* Note: in general the head symbol can be given with just ' (Ltac2's term quotation), but definitions with implicit arguments must be given with @ ! *)
Abort.
