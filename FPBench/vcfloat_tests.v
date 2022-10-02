From vcfloat Require Import Automate FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Section WITHNANS.
Context {NANS:Nans}.

Definition ex0_bmap_list := [Build_varinfo Tdouble 1%positive (-10) (10);Build_varinfo Tdouble 2%positive (-10) (10);Build_varinfo Tdouble 3%positive (-10) (10);Build_varinfo Tdouble 4%positive (-10) (10);Build_varinfo Tdouble 5%positive (-10) (10);Build_varinfo Tdouble 6%positive (-10) (10);Build_varinfo Tdouble 7%positive (-10) (10);Build_varinfo Tdouble 8%positive (-10) (10);Build_varinfo Tdouble 9%positive (-10) (10)].

Definition ex0_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex0_bmap_list) in exact z).

Definition ex0_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b);(3%positive, existT ftype Tdouble c);(4%positive, existT ftype Tdouble d);(5%positive, existT ftype Tdouble e);(6%positive, existT ftype Tdouble f);(7%positive, existT ftype Tdouble g);(8%positive, existT ftype Tdouble h);(9%positive, existT ftype Tdouble i)].

Definition ex0_vmap (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex0_vmap_list a  b  c  d  e  f  g  h  i )) in exact z).

Definition ex0 (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) 
(g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (a) * cast Tdouble _ (e))%F64) * cast Tdouble _ (i))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (b) * cast Tdouble _ (f))%F64) * cast Tdouble _ (g))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (c) * cast Tdouble _ (d))%F64) * cast Tdouble _ (h))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (c) * cast Tdouble _ (e))%F64) * cast Tdouble _ (g))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (b) * cast Tdouble _ (d))%F64) * cast Tdouble _ (i))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (a) * cast Tdouble _ (f))%F64) * cast Tdouble _ (h))%F64))%F64))%F64).

Definition ex0_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive]) ex0 in exact e').

Definition ex1_bmap_list := [Build_varinfo Tdouble 1%positive (-10) (10);Build_varinfo Tdouble 2%positive (-10) (10);Build_varinfo Tdouble 3%positive (-10) (10);Build_varinfo Tdouble 4%positive (-10) (10);Build_varinfo Tdouble 5%positive (-10) (10);Build_varinfo Tdouble 6%positive (-10) (10);Build_varinfo Tdouble 7%positive (-10) (10);Build_varinfo Tdouble 8%positive (-10) (10);Build_varinfo Tdouble 9%positive (-10) (10)].

Definition ex1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex1_bmap_list) in exact z).

Definition ex1_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b);(3%positive, existT ftype Tdouble c);(4%positive, existT ftype Tdouble d);(5%positive, existT ftype Tdouble e);(6%positive, existT ftype Tdouble f);(7%positive, existT ftype Tdouble g);(8%positive, existT ftype Tdouble h);(9%positive, existT ftype Tdouble i)].

Definition ex1_vmap (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex1_vmap_list a  b  c  d  e  f  g  h  i )) in exact z).

Definition ex1 (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (a) * cast Tdouble _ ((cast Tdouble _ (e) * cast Tdouble _ (i))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (g) * cast Tdouble _ ((cast Tdouble _ (b) * cast Tdouble _ (f))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (c) * cast Tdouble _ ((cast Tdouble _ (d) * cast Tdouble _ (h))%F64))%F64))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (e) * cast Tdouble _ ((cast Tdouble _ (c) * cast Tdouble _ (g))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (i) * cast Tdouble _ ((cast Tdouble _ (b) * cast Tdouble _ (d))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (a) * cast Tdouble _ ((cast Tdouble _ (f) * cast Tdouble _ (h))%F64))%F64))%F64))%F64))%F64).

Definition ex1_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive]) ex1 in exact e').

Definition ex2_bmap_list := [Build_varinfo Tsingle 1%positive (1) (999)].

Definition ex2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex2_bmap_list) in exact z).

Definition ex2_vmap_list (t : ftype Tsingle) := [(1%positive, existT ftype Tsingle t)].

Definition ex2_vmap (t : ftype Tsingle) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex2_vmap_list t )) in exact z).

Definition ex2 (t : ftype Tsingle) := 
  cast Tsingle _ (let t_1 := let t1_2 := (cast Tsingle _ (t) + cast Tsingle _ (cast Tsingle Tsingle (1)%F32))%F32 in
      (cast Tdouble _ (t) / cast Tdouble _ (t1_2))%F64 in
  cast Tsingle _ (t_1)).

Definition ex2_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex2 in exact e').

Definition ex3_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition ex3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex3_bmap_list) in exact z).

Definition ex3_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition ex3_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex3_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition ex3 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x2) * cast Tdouble _ (x3))%F64) - cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x4))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x5))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (x3) * cast Tdouble _ (x6))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ (x5) * cast Tdouble _ (x6))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) + cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) - cast Tdouble _ (x4))%F64) + cast Tdouble _ (x5))%F64) + cast Tdouble _ (x6))%F64))%F64))%F64).

Definition ex3_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) ex3 in exact e').

Definition ex4_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition ex4_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex4_bmap_list) in exact z).

Definition ex4_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition ex4_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex4_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition ex4 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x4))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) + cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) - cast Tdouble _ (x4))%F64) + cast Tdouble _ (x5))%F64) + cast Tdouble _ (x6))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x5))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) - cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) + cast Tdouble _ (x4))%F64) - cast Tdouble _ (x5))%F64) + cast Tdouble _ (x6))%F64))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x3) * cast Tdouble _ (x6))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) + cast Tdouble _ (x2))%F64) - cast Tdouble _ (x3))%F64) + cast Tdouble _ (x4))%F64) + cast Tdouble _ (x5))%F64) - cast Tdouble _ (x6))%F64))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x2) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x4))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x5))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) * cast Tdouble _ (x2))%F64) * cast Tdouble _ (x6))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x4) * cast Tdouble _ (x5))%F64) * cast Tdouble _ (x6))%F64))%F64).

Definition ex4_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) ex4 in exact e').

Definition ex5_bmap_list := [Build_varinfo Tsingle 1%positive (1) (4);Build_varinfo Tsingle 2%positive (1) (4)].

Definition ex5_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex5_bmap_list) in exact z).

Definition ex5_vmap_list (x : ftype Tsingle) (y : ftype Tsingle) := [(1%positive, existT ftype Tsingle x);(2%positive, existT ftype Tsingle y)].

Definition ex5_vmap (x : ftype Tsingle) (y : ftype Tsingle) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex5_vmap_list x  y )) in exact z).

Definition ex5 (x : ftype Tsingle) (y : ftype Tsingle) := 
  cast Tsingle _ ((cast Tsingle _ (x) / cast Tsingle _ ((cast Tsingle _ (x) + cast Tsingle _ (y))%F32))%F32).

Definition ex5_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex5 in exact e').

Definition ex6_bmap_list := [Build_varinfo Tdouble 1%positive (1) (2);Build_varinfo Tdouble 2%positive (1) (2);Build_varinfo Tdouble 3%positive (1) (2)].

Definition ex6_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex6_bmap_list) in exact z).

Definition ex6_vmap_list (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x0);(2%positive, existT ftype Tdouble x1);(3%positive, existT ftype Tdouble x2)].

Definition ex6_vmap (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex6_vmap_list x0  x1  x2 )) in exact z).

Definition ex6 (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble _ (let p0 := (cast Tdouble _ ((cast Tdouble _ (x0) + cast Tdouble _ (x1))%F64) - cast Tdouble _ (x2))%F64 in
  let p1 := (cast Tdouble _ ((cast Tdouble _ (x1) + cast Tdouble _ (x2))%F64) - cast Tdouble _ (x0))%F64 in
  let p2 := (cast Tdouble _ ((cast Tdouble _ (x2) + cast Tdouble _ (x0))%F64) - cast Tdouble _ (x1))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (p0) + cast Tdouble _ (p1))%F64) + cast Tdouble _ (p2))%F64).

Definition ex6_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex6 in exact e').

Definition ex7_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition ex7_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex7_bmap_list) in exact z).

Definition ex7_vmap_list (z : ftype Tdouble) := [(1%positive, existT ftype Tdouble z)].

Definition ex7_vmap (z : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex7_vmap_list z )) in exact z).

Definition ex7 (z : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ (z) / cast Tdouble _ ((cast Tdouble _ (z) + cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64))%F64).

Definition ex7_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex7 in exact e').

Definition ex8_bmap_list := [Build_varinfo Tdouble 1%positive (1001e-3) (2);Build_varinfo Tdouble 2%positive (1001e-3) (2)].

Definition ex8_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex8_bmap_list) in exact z).

Definition ex8_vmap_list (x : ftype Tdouble) (y : ftype Tdouble) := [(1%positive, existT ftype Tdouble x);(2%positive, existT ftype Tdouble y)].

Definition ex8_vmap (x : ftype Tdouble) (y : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex8_vmap_list x  y )) in exact z).

Definition ex8 (x : ftype Tdouble) (y : ftype Tdouble) := 
  cast Tdouble _ (let t := (cast Tdouble _ (x) * cast Tdouble _ (y))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (t) - cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64) / cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (t) * cast Tdouble _ (t))%F64) - cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64))%F64).

Definition ex8_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex8 in exact e').

Definition ex9_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-5) (5)].

Definition ex9_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex9_bmap_list) in exact z).

Definition ex9_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2)].

Definition ex9_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex9_vmap_list x1  x2 )) in exact z).

Definition ex9 (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble _ (let a := (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x1))%F64) + cast Tdouble _ (x2))%F64) - cast Tdouble _ (cast Tdouble Tdouble (11)%F64))%F64 in
  let b := (cast Tdouble _ ((cast Tdouble _ (x1) + cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x2))%F64))%F64) - cast Tdouble _ (cast Tdouble Tdouble (7)%F64))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (a) * cast Tdouble _ (a))%F64) + cast Tdouble _ ((cast Tdouble _ (b) * cast Tdouble _ (b))%F64))%F64).

Definition ex9_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex9 in exact e').

Definition ex10_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition ex10_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex10_bmap_list) in exact z).

Definition ex10_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition ex10_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex10_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition ex10 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x5))%F64) + cast Tdouble _ ((cast Tdouble _ (x3) * cast Tdouble _ (x6))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x3))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ (x5) * cast Tdouble _ (x6))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) + cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) - cast Tdouble _ (x4))%F64) + cast Tdouble _ (x5))%F64) + cast Tdouble _ (x6))%F64))%F64))%F64).

Definition ex10_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) ex10 in exact e').

Definition ex11_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2)].

Definition ex11_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex11_bmap_list) in exact z).

Definition ex11_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4)].

Definition ex11_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex11_vmap_list x1  x2  x3  x4 )) in exact z).

Definition ex11 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x4))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) + cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) - cast Tdouble _ (x4))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) - cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) + cast Tdouble _ (x4))%F64))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (x3) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) + cast Tdouble _ (x2))%F64) - cast Tdouble _ (x3))%F64) + cast Tdouble _ (x4))%F64))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x4))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x3))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x2))%F64))%F64) - cast Tdouble _ (x4))%F64).

Definition ex11_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive]) ex11 in exact e').

Definition ex12_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition ex12_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex12_bmap_list) in exact z).

Definition ex12_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition ex12_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex12_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition ex12 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x4))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-x1) + cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) - cast Tdouble _ (x4))%F64) + cast Tdouble _ (x5))%F64) + cast Tdouble _ (x6))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x5))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) - cast Tdouble _ (x2))%F64) + cast Tdouble _ (x3))%F64) + cast Tdouble _ (x4))%F64) - cast Tdouble _ (x5))%F64) + cast Tdouble _ (x6))%F64))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x3) * cast Tdouble _ (x6))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) + cast Tdouble _ (x2))%F64) - cast Tdouble _ (x3))%F64) + cast Tdouble _ (x4))%F64) + cast Tdouble _ (x5))%F64) - cast Tdouble _ (x6))%F64))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x4))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x5))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x2))%F64) * cast Tdouble _ (x6))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x4) * cast Tdouble _ (x5))%F64) * cast Tdouble _ (x6))%F64))%F64).

Definition ex12_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) ex12 in exact e').

Definition ex13_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition ex13_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex13_bmap_list) in exact z).

Definition ex13_vmap_list (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble t)].

Definition ex13_vmap (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex13_vmap_list t )) in exact z).

Definition ex13 (t : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ (t) / cast Tdouble _ ((cast Tdouble _ (t) + cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64))%F64).

Definition ex13_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex13 in exact e').

Definition ex14_bmap_list := [Build_varinfo Tdouble 1%positive (1001e-3) (2);Build_varinfo Tdouble 2%positive (1001e-3) (2)].

Definition ex14_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex14_bmap_list) in exact z).

Definition ex14_vmap_list (x : ftype Tdouble) (y : ftype Tdouble) := [(1%positive, existT ftype Tdouble x);(2%positive, existT ftype Tdouble y)].

Definition ex14_vmap (x : ftype Tdouble) (y : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex14_vmap_list x  y )) in exact z).

Definition ex14 (x : ftype Tdouble) (y : ftype Tdouble) := 
  cast Tdouble _ (let t := (cast Tdouble _ (x) * cast Tdouble _ (y))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (t) - cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64) / cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (t) * cast Tdouble _ (t))%F64) - cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64))%F64).

Definition ex14_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex14 in exact e').

Definition ex15_bmap_list := [Build_varinfo Tdouble 1%positive (0) (77617);Build_varinfo Tdouble 2%positive (0) (33096)].

Definition ex15_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex15_bmap_list) in exact z).

Definition ex15_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b)].

Definition ex15_vmap (a : ftype Tdouble) (b : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex15_vmap_list a  b )) in exact z).

Definition ex15 (a : ftype Tdouble) (b : ftype Tdouble) := 
  cast Tdouble _ (let b2 := (cast Tdouble _ (b) * cast Tdouble _ (b))%F64 in
  let b4 := (cast Tdouble _ (b2) * cast Tdouble _ (b2))%F64 in
  let b6 := (cast Tdouble _ (b4) * cast Tdouble _ (b2))%F64 in
  let b8 := (cast Tdouble _ (b4) * cast Tdouble _ (b4))%F64 in
  let a2 := (cast Tdouble _ (a) * cast Tdouble _ (a))%F64 in
  let firstexpr := (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (11)%F64) * cast Tdouble _ (a2))%F64) * cast Tdouble _ (b2))%F64) - cast Tdouble _ (b6))%F64) - cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (121)%F64) * cast Tdouble _ (b4))%F64))%F64) - cast Tdouble _ (cast Tdouble Tdouble (2)%F64))%F64 in
  (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (33375e-2)%F64) * cast Tdouble _ (b6))%F64) + cast Tdouble _ ((cast Tdouble _ (a2) * cast Tdouble _ (firstexpr))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (55e-1)%F64) * cast Tdouble _ (b8))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (a) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (b))%F64))%F64))%F64).

Definition ex15_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex15 in exact e').

Definition ex16_bmap_list := [Build_varinfo Tdouble 1%positive (0) (77617);Build_varinfo Tdouble 2%positive (0) (33096)].

Definition ex16_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex16_bmap_list) in exact z).

Definition ex16_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b)].

Definition ex16_vmap (a : ftype Tdouble) (b : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex16_vmap_list a  b )) in exact z).

Definition ex16 (a : ftype Tdouble) (b : ftype Tdouble) := 
  cast Tdouble _ (let b2 := (cast Tdouble _ (b) * cast Tdouble _ (b))%F64 in
  let b4 := (cast Tdouble _ (b2) * cast Tdouble _ (b2))%F64 in
  let b6 := (cast Tdouble _ (b4) * cast Tdouble _ (b2))%F64 in
  let b8 := (cast Tdouble _ (b4) * cast Tdouble _ (b4))%F64 in
  let a2 := (cast Tdouble _ (a) * cast Tdouble _ (a))%F64 in
  let firstexpr := (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (11)%F64) * cast Tdouble _ (a2))%F64) * cast Tdouble _ (b2))%F64) - cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (121)%F64) * cast Tdouble _ (b4))%F64))%F64) - cast Tdouble _ (cast Tdouble Tdouble (2)%F64))%F64 in
  (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (33375e-2)%F64) - cast Tdouble _ (a2))%F64) * cast Tdouble _ (b6))%F64) + cast Tdouble _ ((cast Tdouble _ (a2) * cast Tdouble _ (firstexpr))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (55e-1)%F64) * cast Tdouble _ (b8))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ (a) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (b))%F64))%F64))%F64).

Definition ex16_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex16 in exact e').

Definition ex17_bmap_list := [Build_varinfo Tdouble 1%positive (-100) (100);Build_varinfo Tdouble 2%positive (20) (2e4);Build_varinfo Tdouble 3%positive (-30) (50)].

Definition ex17_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex17_bmap_list) in exact z).

Definition ex17_vmap_list (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble u);(2%positive, existT ftype Tdouble v);(3%positive, existT ftype Tdouble t)].

Definition ex17_vmap (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex17_vmap_list u  v  t )) in exact z).

Definition ex17 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble _ (let t1 := (cast Tdouble _ (cast Tdouble Tdouble (3314e-1)%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (6e-1)%F64) * cast Tdouble _ (t))%F64))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (-t1) * cast Tdouble _ (v))%F64) / cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (t1) + cast Tdouble _ (u))%F64) * cast Tdouble _ ((cast Tdouble _ (t1) + cast Tdouble _ (u))%F64))%F64))%F64).

Definition ex17_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex17 in exact e').

Definition ex18_bmap_list := [Build_varinfo Tdouble 1%positive (-125) (125);Build_varinfo Tdouble 2%positive (15) (25000);Build_varinfo Tdouble 3%positive (-40) (60)].

Definition ex18_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex18_bmap_list) in exact z).

Definition ex18_vmap_list (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble u);(2%positive, existT ftype Tdouble v);(3%positive, existT ftype Tdouble t)].

Definition ex18_vmap (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex18_vmap_list u  v  t )) in exact z).

Definition ex18 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble _ (let t1 := (cast Tdouble _ (cast Tdouble Tdouble (3314e-1)%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (6e-1)%F64) * cast Tdouble _ (t))%F64))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (-t1) * cast Tdouble _ (v))%F64) / cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (t1) + cast Tdouble _ (u))%F64) * cast Tdouble _ ((cast Tdouble _ (t1) + cast Tdouble _ (u))%F64))%F64))%F64).

Definition ex18_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex18 in exact e').

Definition ex19_bmap_list := [Build_varinfo Tdouble 1%positive (-30) (120);Build_varinfo Tdouble 2%positive (320) (20300);Build_varinfo Tdouble 3%positive (-50) (30)].

Definition ex19_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex19_bmap_list) in exact z).

Definition ex19_vmap_list (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble u);(2%positive, existT ftype Tdouble v);(3%positive, existT ftype Tdouble t)].

Definition ex19_vmap (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex19_vmap_list u  v  t )) in exact z).

Definition ex19 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := 
  cast Tdouble _ (let t1 := (cast Tdouble _ (cast Tdouble Tdouble (3314e-1)%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (6e-1)%F64) * cast Tdouble _ (t))%F64))%F64 in
  (cast Tdouble _ ((cast Tdouble _ (-t1) * cast Tdouble _ (v))%F64) / cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (t1) + cast Tdouble _ (u))%F64) * cast Tdouble _ ((cast Tdouble _ (t1) + cast Tdouble _ (u))%F64))%F64))%F64).

Definition ex19_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex19 in exact e').

Definition ex20_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition ex20_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex20_bmap_list) in exact z).

Definition ex20_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3)].

Definition ex20_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex20_vmap_list x1  x2  x3 )) in exact z).

Definition ex20 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (-(cast Tdouble _ (x1) * cast Tdouble _ (x2))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (x2))%F64) * cast Tdouble _ (x3))%F64))%F64) - cast Tdouble _ (x1))%F64) - cast Tdouble _ (x3))%F64).

Definition ex20_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex20 in exact e').

Definition ex21_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition ex21_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex21_bmap_list) in exact z).

Definition ex21_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3)].

Definition ex21_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex21_vmap_list x1  x2  x3 )) in exact z).

Definition ex21 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (x2))%F64) * cast Tdouble _ (x3))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x3))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x2) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (x2))%F64) * cast Tdouble _ (x3))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) * cast Tdouble _ (x3))%F64) * cast Tdouble _ (x3))%F64))%F64) - cast Tdouble _ (x2))%F64).

Definition ex21_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex21 in exact e').

Definition ex22_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-20) (5)].

Definition ex22_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex22_bmap_list) in exact z).

Definition ex22_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2)].

Definition ex22_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex22_vmap_list x1  x2 )) in exact z).

Definition ex22 (x1 : ftype Tdouble) (x2 : ftype Tdouble) := 
  cast Tdouble _ (let t := (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (x1))%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (x2))%F64))%F64) - cast Tdouble _ (x1))%F64 in
  let t_42_ := (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (x1))%F64) - cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (x2))%F64))%F64) - cast Tdouble _ (x1))%F64 in
  let d := (cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x1))%F64) + cast Tdouble _ (cast Tdouble Tdouble (1)%F64))%F64 in
  let s := (cast Tdouble _ (t) / cast Tdouble _ (d))%F64 in
  let s_42_ := (cast Tdouble _ (t_42_) / cast Tdouble _ (d))%F64 in
  (cast Tdouble _ (x1) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (s))%F64) * cast Tdouble _ ((cast Tdouble _ (s) - cast Tdouble _ (cast Tdouble Tdouble (3)%F64))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x1))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (4)%F64) * cast Tdouble _ (s))%F64) - cast Tdouble _ (cast Tdouble Tdouble (6)%F64))%F64))%F64))%F64) * cast Tdouble _ (d))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (s))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x1) * cast Tdouble _ (x1))%F64) * cast Tdouble _ (x1))%F64))%F64) + cast Tdouble _ (x1))%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) * cast Tdouble _ (s_42_))%F64))%F64))%F64).

Definition ex22_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) ex22 in exact e').

Definition ex23_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition ex23_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex23_bmap_list) in exact z).

Definition ex23_vmap_list (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := [(1%positive, existT ftype Tdouble v);(2%positive, existT ftype Tdouble w);(3%positive, existT ftype Tdouble r)].

Definition ex23_vmap (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex23_vmap_list v  w  r )) in exact z).

Definition ex23 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) / cast Tdouble _ ((cast Tdouble _ (r) * cast Tdouble _ (r))%F64))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (125e-3)%F64) * cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) - cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (v))%F64))%F64))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (w) * cast Tdouble _ (w))%F64) * cast Tdouble _ (r))%F64) * cast Tdouble _ (r))%F64))%F64) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) - cast Tdouble _ (v))%F64))%F64))%F64) - cast Tdouble _ (cast Tdouble Tdouble (45e-1)%F64))%F64).

Definition ex23_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex23 in exact e').

Definition ex24_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition ex24_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex24_bmap_list) in exact z).

Definition ex24_vmap_list (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := [(1%positive, existT ftype Tdouble v);(2%positive, existT ftype Tdouble w);(3%positive, existT ftype Tdouble r)].

Definition ex24_vmap (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex24_vmap_list v  w  r )) in exact z).

Definition ex24 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (6)%F64) * cast Tdouble _ (v))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (5e-1)%F64) * cast Tdouble _ (v))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (w) * cast Tdouble _ (w))%F64) * cast Tdouble _ (r))%F64) * cast Tdouble _ (r))%F64))%F64) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) - cast Tdouble _ (v))%F64))%F64))%F64) - cast Tdouble _ (cast Tdouble Tdouble (25e-1)%F64))%F64).

Definition ex24_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex24 in exact e').

Definition ex25_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition ex25_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex25_bmap_list) in exact z).

Definition ex25_vmap_list (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := [(1%positive, existT ftype Tdouble v);(2%positive, existT ftype Tdouble w);(3%positive, existT ftype Tdouble r)].

Definition ex25_vmap (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex25_vmap_list v  w  r )) in exact z).

Definition ex25 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (3)%F64) - cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) / cast Tdouble _ ((cast Tdouble _ (r) * cast Tdouble _ (r))%F64))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (125e-3)%F64) * cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (2)%F64) * cast Tdouble _ (v))%F64))%F64))%F64) * cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (w) * cast Tdouble _ (w))%F64) * cast Tdouble _ (r))%F64) * cast Tdouble _ (r))%F64))%F64) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) - cast Tdouble _ (v))%F64))%F64))%F64) - cast Tdouble _ (cast Tdouble Tdouble (5e-1)%F64))%F64).

Definition ex25_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) ex25 in exact e').

Definition ex26_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition ex26_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex26_bmap_list) in exact z).

Definition ex26_vmap_list (x : ftype Tdouble) := [(1%positive, existT ftype Tdouble x)].

Definition ex26_vmap (x : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex26_vmap_list x )) in exact z).

Definition ex26 (x : ftype Tdouble) := 
  cast Tdouble _ (let r := cast Tdouble Tdouble (4)%F64 in
  let k := cast Tdouble Tdouble (111e-2)%F64 in
  (cast Tdouble _ ((cast Tdouble _ (r) * cast Tdouble _ (x))%F64) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) + cast Tdouble _ ((cast Tdouble _ (x) / cast Tdouble _ (k))%F64))%F64))%F64).

Definition ex26_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex26 in exact e').

Definition ex27_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition ex27_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex27_bmap_list) in exact z).

Definition ex27_vmap_list (x : ftype Tdouble) := [(1%positive, existT ftype Tdouble x)].

Definition ex27_vmap (x : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex27_vmap_list x )) in exact z).

Definition ex27 (x : ftype Tdouble) := 
  cast Tdouble _ (let r := cast Tdouble Tdouble (4)%F64 in
  let k := cast Tdouble Tdouble (111e-2)%F64 in
  (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (r) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64) / cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (x) / cast Tdouble _ (k))%F64) * cast Tdouble _ ((cast Tdouble _ (x) / cast Tdouble _ (k))%F64))%F64))%F64))%F64).

Definition ex27_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex27 in exact e').

Definition ex28_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (5e-1)].

Definition ex28_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex28_bmap_list) in exact z).

Definition ex28_vmap_list (v : ftype Tdouble) := [(1%positive, existT ftype Tdouble v)].

Definition ex28_vmap (v : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex28_vmap_list v )) in exact z).

Definition ex28 (v : ftype Tdouble) := 
  cast Tdouble _ (let p := cast Tdouble Tdouble (35e6)%F64 in
  let a := cast Tdouble Tdouble (401e-3)%F64 in
  let b := cast Tdouble Tdouble (427e-7)%F64 in
  let t := cast Tdouble Tdouble (300)%F64 in
  let n := cast Tdouble Tdouble (1000)%F64 in
  let k := cast Tdouble Tdouble (13806503e-30)%F64 in
  (cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (p) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (a) * cast Tdouble _ ((cast Tdouble _ (n) / cast Tdouble _ (v))%F64))%F64) * cast Tdouble _ ((cast Tdouble _ (n) / cast Tdouble _ (v))%F64))%F64))%F64) * cast Tdouble _ ((cast Tdouble _ (v) - cast Tdouble _ ((cast Tdouble _ (n) * cast Tdouble _ (b))%F64))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (k) * cast Tdouble _ (n))%F64) * cast Tdouble _ (t))%F64))%F64).

Definition ex28_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex28 in exact e').

Definition ex29_bmap_list := [Build_varinfo Tdouble 1%positive (0) (1)].

Definition ex29_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list ex29_bmap_list) in exact z).

Definition ex29_vmap_list (x : ftype Tdouble) := [(1%positive, existT ftype Tdouble x)].

Definition ex29_vmap (x : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (ex29_vmap_list x )) in exact z).

Definition ex29 (x : ftype Tdouble) := 
  cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (1)%F64) + cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (5e-1)%F64) * cast Tdouble _ (x))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (125e-3)%F64) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64))%F64) + cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (625e-4)%F64) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64))%F64) - cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ ((cast Tdouble _ (cast Tdouble Tdouble (390625e-7)%F64) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64) * cast Tdouble _ (x))%F64))%F64).

Definition ex29_expr := 
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) ex29 in exact e').

End WITHNANS.