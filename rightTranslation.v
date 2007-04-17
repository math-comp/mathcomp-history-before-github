(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of the left translation as an action on cosets          *)
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
Require Import div.
Require Import action.
Require Import normal.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section RightTrans.

Open Scope group_scope.

Variable (G : finGroupType).

Lemma rtrans_1: forall s : setType G, s :* 1 = s.
Proof. exact: rcoset1. Qed.

Lemma rcoset_morph: forall x y (s : setType G),
  s :* (x * y) = s :* x :* y.
Proof.
move=> x y s; rewrite !rcoset_smul -smulgA; congr smulg. 
apply/isetP=> a; rewrite -rcoset_smul s2f.
apply/eqP/rcosetP; first by move=> Da; exists x; rewrite ?iset11 ?Da.
by move=> [z]; rewrite s2f; move/eqP => ->.
Qed.

Definition trans_action := Action rtrans_1 rcoset_morph.

End RightTrans.

Section Bij.

Open Scope group_scope.

Variable (G : finGroupType) (H K: group G).

Hypothesis subset_HK : subset H K.

Section LBij.

Variable L: group G.
Hypothesis subset_LK : subset L K.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the right           *)
(*    translation  of rcoset of H in K                                 *)
(*                                                                     *)
(***********************************************************************)

Definition rtrans_fix := rcosets H K :&: {s, act_fix (trans_action G) L s}.


Lemma act_fix_sub : forall x,
  act_fix (trans_action G) L (H :* x) -> subset L (H :^ x).
Proof.
move=> x; move/act_fixP => H1.
apply/subsetP => y Hy.
move: (H1 _ Hy) => /= H2.
have F1: (H :* x) x.
 by apply/rcosetP; exists (unitg G); rewrite ?group1 ?mul1g.
rewrite -H2 in F1; case/rcosetP: F1 => x1.
case/rcosetP => y1 Hy1 -> Hxy.
replace y with (y1 ^x)^-1; first by rewrite sconjg_inv ?sconjg_conj.
rewrite /conjg {1}Hxy; gsimpl.
Qed.

End LBij.

Lemma act_fix_norm : forall x,
  act_fix (trans_action G) H (H :* x) = normaliser H x.
Proof.
move=> x; apply/act_fixP/idP.
   rewrite -groupV s2f => dHx; apply/subsetP=> y. 
   rewrite s2f /conjg; gsimpl => Hxy. 
   rewrite -(actK (trans_action G) x H) /= -(dHx _ Hxy) /=. 
   by rewrite -!rcoset_morph /conjg s2f; gsimpl; exact group1.
move=> Nx y Hy => /=; rewrite (norm_rlcoset Nx).
by apply/isetP=> a; rewrite !s2f mulgA groupMr ?groupV.
Qed.

Lemma rtrans_fix_norm : rtrans_fix H = (rcoset H) @: (normaliser H :&: K).
Proof.
apply/isetP=> Hx; apply/isetIP/iimageP.
  case; rewrite s2f /rcosets;move/iimageP=> [x Kx ->] af.
  by exists x => //; rewrite act_fix_norm in af; rewrite s2f Kx andbC /=.
case=> x; case/isetIP=> Nx Kx dHx; split; last by rewrite s2f dHx act_fix_norm.
by apply/iimageP; exists x.
Qed.

End Bij.

Unset Implicit Arguments.
