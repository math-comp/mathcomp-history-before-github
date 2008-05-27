(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Semi-direct product                                                *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import finset.
Require Import groups.
Require Import normal.
Require Import div.
Require Import automorphism.
Require Import action.
Require Import group_perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ExternalSDirProd.

Variables gT1 gT2 : finGroupType.
Variable psi : action gT1 gT2.

Definition perm_of_act x := (perm_of (@inj_act _ _ psi x)).

Hypothesis Haut : forall x, Aut (@setT gT2) (perm_of_act x).

Definition extsprod_mulg (x y : gT1 * gT2) := 
  (x.1 * y.1, (perm_of_act y.1 x.2) * y.2).
Definition extsprod_invg (x : gT1 * gT2) := 
  (x.1^-1, (perm_of_act x.1^-1 x.2^-1)).

Lemma extsprod_mulgA : associative extsprod_mulg.
Proof.
move=> x y z; congr ( _ , _ ); rewrite /= ?permE ?mulgA //.
rewrite actM; set Hmorph := (proj2 (andP (Haut z.1))).
move/morphP: (Hmorph); move/(_ (psi x.2 y.1) y.2); rewrite !in_setT.
by move/(_ is_true_true is_true_true); rewrite !permE=> <-.
Qed.

Lemma extsprod_mulVg : left_inverse (1, 1) extsprod_invg extsprod_mulg.
Proof.
by move=> x; congr (_, _)=>/=; rewrite ?permE -?actM mulVg // act1 mulVg.
Qed.

Lemma extsprod_mul1g : left_unit (1, 1) extsprod_mulg.
Proof. case=> x1 x2; congr (_, _); rewrite ?permE /= ?act1 ?mul1g //.
by move: (morphic1 (proj2 (andP (Haut x1)))); rewrite !permE=>->; rewrite mul1g.
Qed.

Canonical Structure extprod_baseFinGroupType := Eval hnf in
  [baseFinGroupType of gT1 * gT2
     by extsprod_mulgA, extsprod_mul1g & extsprod_mulVg].

Canonical Structure sprod_group := FinGroupType extsprod_mulVg.

(*Lemma group_sprodsetX : forall (H1 : {group gT1}) (H2 : {group gT2}),
  group_set (setX H1 H2).
Proof.
move=> H1 H2; apply/group_setP; split; first by rewrite inE !group1.
case=> [x1 x2] [y1 y2]; rewrite !inE; case/andP=> Hx1 Hx2; case/andP=> Hy1 Hy2.
 rewrite /= !groupM //.
rewrite perm_closed //; move: (proj1 (andP (Haut y1))).
rewrite /perm_on.
Qed.

Canonical Structure setX_group H1 H2 := Group (group_setX H1 H2).*)

End ExternalSDirProd.