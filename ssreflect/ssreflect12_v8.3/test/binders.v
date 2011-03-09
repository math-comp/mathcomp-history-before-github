(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool eqtype.

Lemma test (x : bool) : True.
have H1 x := x.
have (x) := x => H2.
have H3 T (x : T) := x.
have ? : bool := H1 _ x.
have ? : bool := H2 _ x.
have ? : bool := H3 _ x.
have ? (z : bool) : forall y : bool, z = z := fun y => refl_equal _.
have ? (z : bool) : z = z.
  exact: refl_equal.
exact I.
Qed.

Lemma test1 (x : bool) : True.
suff (x : bool): True /\ True.
  by case=> _; apply: (fun x => x).
split; exact I.
Qed.