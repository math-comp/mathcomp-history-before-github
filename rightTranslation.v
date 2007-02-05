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
Require Import baux.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section RightTrans.

Open Scope group_scope.

Variable (G : finGroupType).

Lemma rtrans_1: forall s : setType G, s :* 1 = s.
Proof. exact: rcoset1. Qed.

Lemma rtrans_morph: forall x y (s : setType G),
  s :* (x * y) = s :* x :* y.
Proof. symmetry; exact: rcoset_rcoset. Qed.

Definition trans_action := Action rtrans_1 rtrans_morph.

End RightTrans.

Section Bij.

Open Scope group_scope.

Variable (G : finGroupType) (H: setType G).

Hypothesis gH: group H.

Definition rcoset_set := (rcoset H) @: (isetA G).

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the right           *)
(*    translation  of rcoset of H in G                                 *)
(*                                                                     *)
(***********************************************************************)

Definition rtrans_fix := rcoset_set :&: {s, act_fix (trans_action G) H s}.

Lemma act_fix_norm : forall x,
  act_fix (trans_action G) H (H :* x) = normaliser H x.
Proof.
move=> x; rewrite /act_fix. 
apply/eqP/idP.
  rewrite -(groupV (group_normaliser H)) s2f => dH;apply/subsetP=> y.
  rewrite {1}dH !s2f /=; case/andP=> _; move/eqP=> dHx.
  rewrite -(actK (trans_action G) x H) /= -{}dHx !rcoset_rcoset /conjg.
  by gsimpl; exact: rcoset_refl.
move=> Nx; apply/isetP=> y; rewrite s2f; symmetry.
case Hy: (H y) => //=; apply/eqP; rewrite -(rcoset1 H) in Hy.
rewrite (norm_rcoset_lcoset gH Nx) lcoset_smul rcoset_smul -smulgA.
by congr smulg; rewrite -rcoset_smul -(rcoset_trans1 gH Hy) rcoset1.
Qed.

Lemma rtrans_fix_norm : rtrans_fix = (rcoset H) @: (normaliser H).
Proof.
apply/isetP=> Hx; apply/isetIP/iimageP.
  case; rewrite s2f /rcoset_set;move/iimageP=> [x _ ->] af.
  by exists x; rewrite act_fix_norm in af.
case=> x Nx ->; split; first by apply/iimageP; exists x =>//; rewrite s2f.
by rewrite s2f act_fix_norm.
Qed.

End Bij.

Unset Implicit Arguments.
