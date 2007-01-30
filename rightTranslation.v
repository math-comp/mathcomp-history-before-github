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

Variable (G : finGroupType) (H K L: setType G).

Hypothesis group_K: group K.
Hypothesis group_L: group L.
Hypothesis group_H: group H.
Hypothesis subset_HK: subset H K.
Hypothesis subset_LK: subset L K.

Definition rcosetSet := (fun x => L :* x) @: (setA G).
Definition repr_s := eq_sig rcosetSet.

Lemma  rtransP: forall (a:G) (s : repr_s), rcosetSet (val s :* a).
Proof.
move=> a [s] /=; rewrite /rcosetSet.
move/iimageP=>[z _ ->].
apply/iimageP; exists(z*a) => //.
exact: rcoset_rcoset.
Qed.

Definition rtrans (s : repr_s) (a:G) : repr_s := EqSig _ _ (rtransP a s).

Lemma rtrans_1: forall x, rtrans x 1 = x.
Proof.
move => [r p]; rewrite /rtrans.
apply:val_inj=> /=; exact : rcoset1.
Qed.

Lemma rtrans_morph: forall x y z,
  H x -> H y -> rtrans z (x * y) = rtrans (rtrans z x) y.
Proof.
move => x y [r p] Hx Hy.
rewrite /rtrans.
apply:val_inj=> /=.
symmetry; exact: rcoset_rcoset.
Qed.

End RightTrans.

Section Bij.

Open Scope group_scope.

Variable (G : finGroupType) (H K: setType G).

Hypothesis group_K: group K.
Hypothesis group_H: group H.
Hypothesis subset_HK: subset H K.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the left            *)
(*    translation  of coset of H in K                                  *)
(*                                                                     *)
(***********************************************************************)

Definition rSO := {x, SO H (@rtrans _ H) x}.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the quotient group of H and the normaliser of H      *)
(*                                                                     *)
(***********************************************************************)
  
Definition RGN := 
  (RG subgrp_H (normaliser_grp H (subgrp_K)) 
        (subset_normaliser subgrp_H subset_HK) (normaliser_normal subset_HK)).


Lemma th_to_rg: 
  forall (x : G)
    (Hx: setI (roots (lcoset H)) K x)
    (Hx1 : lS0 (EqSig _ _ Hx)), 
    (setI (roots (lcoset H)) (normaliser H K) (root (lcoset H) x)).
Proof.
move => x Hx Hx1.
set (e := root (lcoset H) x).
rewrite /setI; apply/andP; split.
  by apply: roots_root; apply lcoset_csym.
move: (andP Hx) => [Hx2 Hx3].
case/andP: (setI_roots Hx3); rewrite -/e; move => He1 He2.
apply/andP;split => //.
apply/subsetP => y Hy.
move/subsetP: Hx1 => Hx1.
rewrite conjsg_subset; first exact: eq_refl.
apply/subsetP => z Hz; rewrite /conjsg conjgE.
replace (e^-1 * z * e) with
          ((x^-1 * e)^-1 * (x^-1 * z * x) * (x^-1 * e)) ; last by gsimpl.
apply: subgrpM => //; last by exact: root_lcosetd.
apply: subgrpM => //; first by apply: subgrpV => //; exact: root_lcosetd.
have F1: (H z^-1) by apply subgrpV.
move: {F1}(Hx1 _ F1).
move/andP => [H4 H5].
move/val_eqP: H4 => //=.
rewrite /ltrans.
case (wb (H z^-1)); case => Hb1 //=; 
  last by move: Hb1; rewrite H5.
move/val_eqP => //= H6.
replace (x^-1 * z * x) with ((z^-1 * x)^-1 * x); last by gsimpl.
rewrite -{2}(eqP H6).
exact: root_lcosetd.
Qed.


(***********************************************************************)
(*                                                                     *)
(*  Definition of the iso morphism between lS0 and rgn                 *)
(*                                                                     *)
(***********************************************************************)

Definition to_RG: eq_sig lS0 ->  eq_sig RGN.
move => [[x Hx] Hx1].
have F1: setI (roots (lcoset H)) (normaliser H K) (root (lcoset H) x);
  last by exists (@EqSig G _ _ F1); rewrite /RG.
apply: (th_to_rg Hx1).
Defined.

Lemma th_to_RG_inv: forall
    (x : G)
    (Hx:   setI (roots (lcoset H)) (normaliser H K) x)
    (Hx1 : RGN (EqSig _ _ Hx))
    (F1:  setI (roots (lcoset (G:= G) H)) K x),
    lS0 (EqSig _ _ F1).
Proof.
move => x Hx Hx1 F1.
apply/subsetP => y.
move: (andP Hx) => [H1 H2].
move/andP: H2 => [H2 H3].
move/subsetP: H2 => H2.
rewrite /stabiliser /ltrans /setI => Hy.
apply/andP; split => //.
match goal with |- context[wb ?x] =>
  case (wb x); intros b1; case b1 => Hb1 //=
end; last by move: Hb1; rewrite Hy.
do 2 apply/val_eqP => //=.
rewrite -{2}(eqP H1) root_connect; last exact: lcoset_csym.
have F2: H y^-1 by apply subgrpV.
rewrite lcoset_trans //.
move: {H2}(H2 y^-1) => H2.
rewrite /lcoset invg_mul.
move: (eqP (H2 (subsetP subset_HK _ F2))); rewrite /conjsg conjgE => H4.
by rewrite H4; apply: subgrpV.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the inversion function                               *)
(*                                                                     *)
(***********************************************************************)

Definition to_RG_inv: eq_sig RGN -> eq_sig lS0.
move => [[x Hx] Hx1].
have F1:  setI (roots (lcoset (G:= G) H)) K x.
  move: (andP Hx) => [H1 H2].
  apply/andP; split => //.
  by apply (subsetP (normaliser_subset H K)).
exists (@EqSig G _ _ F1).
apply: (th_to_RG_inv Hx1).
Defined.

Lemma to_RG_bij: bijective to_RG.
Proof.
exists to_RG_inv => [] [[x Hx] Hx1]; rewrite /to_RG /to_RG_inv;
      do 3 apply/val_eqP => //=;
      by move: (andP Hx) => [H1 H2].
Qed.

Lemma to_RG_inv_bij: bijective to_RG_inv.
exists to_RG => [] [[x Hx] Hx1]; rewrite /to_RG /to_RG_inv;
      do 3 apply/val_eqP => //=;
      by move: (andP Hx) => [H1 H2].
Qed.

End Bij.

Unset Implicit Arguments.
