(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of the center of a group and a centraliser             *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.
Require Import normal.
Require Import cyclic.
Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Center.

Open Scope group_scope.
   
Variables (elt: finGroupType) (H: group elt).

(**********************************************************************)
(*  Definition of the center                                          *)
(*                                                                    *)
(*      x in C, if forall y in H, xy = yx                             *)
(**********************************************************************)

Definition center := {x, H x && (subset H (commute x))}.

Lemma centerP: forall x,
  reflect (H x /\ (forall y, H y -> x * y = y * x)) (center x).
Proof.
move => x; apply: (iffP idP);rewrite s2f.
  move/andP => [H1 H2]; split => // y Hy.
  by move/subsetP: H2 => H2; rewrite (eqP (H2 _ Hy)).
move => [H1 H2]; rewrite /center H1 /=; apply/subsetP => y Hy.
by apply/eqP;rewrite H2.
Qed.

Lemma subset_center: subset center H.
Proof. by apply/subsetP => x; move/centerP => [Hx _]. Qed.

Lemma group_centerP: group_set center.
Proof.
apply/groupP;rewrite !s2f group1 //=.
split; first by apply/subsetP=>x Hx; rewrite /commute mulg1 mul1g.
move => x y; move/centerP=>[Hx HHx];  move/centerP=>[Hy HHy].
apply/centerP; split; first by rewrite groupM.
by move=> z Hz; rewrite -mulgA (HHy z Hz) [z*(x*y)]mulgA -(HHx z Hz) mulgA.
Qed.

Canonical Structure group_center := Group group_centerP.
  
(*********************************************************************)
(*              Definition of the centraliser                        *)
(*    y is in the centraliser of x if y * x = y * x                  *)
(*********************************************************************)

Definition centraliser x := H :&: {y, commute x y}.

Lemma centraliser_id: forall x, H x -> centraliser x x.
Proof. by move => x Hx; rewrite !s2f /commute eq_refl; apply/andP. Qed.

Lemma centraliserP: forall x y,
  reflect (H y /\ x * y = y * x) (centraliser x y).
Proof. 
move=> x y; rewrite /centraliser /commute !s2f. 
by apply: (iffP andP); case; split => //; apply/eqP.
Qed.

Lemma subset_centraliser: forall x, subset (centraliser x) H.
Proof. by move => x; apply/subsetP => y; case/centraliserP. Qed.

Lemma centraliser1 : forall x, centraliser x 1.
Proof. by move=> x; apply/centraliserP; gsimpl. Qed.

Lemma group_centraliserP: forall x, group_set (centraliser x).
Proof.
move => x; apply/groupP; split; first exact: centraliser1.
move => x1 y1; case/centraliserP=> Hy cxx1; case/centraliserP=> Hz cxy1. 
apply/centraliserP; split; first by rewrite groupM.
by rewrite mulgA cxx1 -mulgA cxy1 mulgA.
Qed. 

Canonical Structure group_centraliser x := Group (@group_centraliserP x).

Lemma centraliserC: forall x y, H x -> centraliser x y -> centraliser y x.
Proof. by move => x y Hx; case/centraliserP=> *; apply/centraliserP. Qed.

Lemma centraliserM: forall x y z, 
  centraliser x y -> centraliser x z -> centraliser x (y * z). 
Proof. move=> *; exact: groupM. Qed.

Lemma centraliserV: forall x y,
  centraliser x y -> centraliser x (y^-1). 
Proof. by move=> *; rewrite groupV. Qed.

Lemma centraliserEr: forall x y n,
  centraliser x y -> centraliser x (y ** n). 
Proof. move=> *; exact: groupE. Qed.

Lemma centraliserEl: forall x y n, H x ->
  centraliser x y -> centraliser (x ** n) y. 
Proof.
move => x y n Hx; case/centraliserP=> Hy cxy.
by apply: centraliserC=>//; apply: centraliserEr; apply/centraliserP.
Qed.

Lemma normal_centraliser: forall x, H x ->
  normal (cyclic x) (centraliser x).
Proof.
move => x Hx; apply/normalP; move => y.
case/centraliserP=> Hy cxy; apply/isetP=>z.
by rewrite -cyclic_conjgs /conjg -mulgA cxy mulgA; gsimpl.
Qed.

Lemma cyclic_subset_centraliser: forall x,
     H x -> subset (cyclic x) (centraliser x).
Proof.
move => x Hx; apply/subsetP => y Hy; case/cyclicP: Hy => n Hn.
by rewrite -(eqP Hn) ?centraliserEr // centraliser_id.
Qed.

Lemma centraliser_normaliser: 
  forall x, H x -> subset (centraliser x) (normaliser (cyclic x)).
Proof.
move => x Hx.
move/subsetP:(cyclic_subset_centraliser Hx)=>Hcn.
apply/subsetP => y;case/centraliserP=> Hy cxy.
rewrite s2f; apply/subsetP=> z; rewrite s2f=> Czy.
have:=Czy; case/cyclicP=> n; rewrite /conjg; gsimpl; move/eqP=> dx.
case/centraliserP: (Hcn (z ^ y^-1) Czy) => Hz cxzy.
apply/cyclicP; exists n=>/=; apply/eqP.
apply: (can_inj (conjgK y^-1)); rewrite dx /conjg; gsimpl.
apply: (can_inj (mulgK x)).
move:cxzy; rewrite /conjg; gsimpl=><-.
rewrite -(@mulgA _ (x*y) z _) -(@mulgA _ x y _) (@mulgA _ y z _) -dx.
rewrite -(@mulgA _ _ y^-1 x) -(@mulgA _ _ z y^-1) -(@mulgA _ y y _).
rewrite (@mulgA _ y z _) -dx; gsimpl.
rewrite (eqP (commute_expn n _)); gsimpl; last by rewrite /commute cxy.
by rewrite (eqP (commute_expn n _)) // /commute.
Qed.

End Center.

Unset Implicit Arguments.
