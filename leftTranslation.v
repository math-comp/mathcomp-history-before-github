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

Section LeftTrans.

Open Scope group_scope.

Variable (G : finGroupType) (H K L: set G).

Hypothesis group_K: group K.
Hypothesis group_L: group L.
Hypothesis group_H: group H.
Hypothesis subset_HK: subset H K.
Hypothesis subset_LK: subset L K.

(* In order to get opaque value for proof terms in the
   function ltrans we first prove them as theorems *)
Lemma th_ltrans1: setI (roots (lcoset L)) K (root (lcoset L) 1).
Proof.
apply/andP; split; first by rewrite roots_root //; exact: lcoset_csym.
apply (subsetP subset_LK).
exact: root_lcoset1.
Qed.

Lemma th_ltrans_gen: forall a b, H a -> 
  setI (roots (lcoset L)) K b ->
  setI (roots (lcoset L)) K (root (lcoset L) (a * b)).
Proof.
move => a b Hk.
move/andP => [Hk1 Hb].
apply/andP; split; first by rewrite roots_root //; exact: lcoset_csym.
have F1: K a by exact: (subsetP subset_HK).
have F2: K (a * b) by  apply: groupM => //.
replace (root (lcoset L) (a * b)) with 
(a * b * ((a * b)^-1 * root (lcoset L) (a * b))); last by gsimpl.
apply: groupM => //.
apply: (subsetP subset_LK).
exact: root_lcosetd.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the left translation as an action on cosets          *)
(*      a |->  [ bH |-> (ab)H]                                         *)
(*                                                                     *)
(***********************************************************************)

Definition ltrans := 
fun a : G =>
let (b, Hb) := wb (H a) in
(if b return (H a = b -> rootSet L K -> rootSet L K)
 then
  fun H x => let (x1, Hx1) := x in EqSig _ _ (th_ltrans_gen H Hx1)
 else
  fun _ _  => EqSig _ _ th_ltrans1) Hb.

Lemma ltrans_bij: forall x,
  H x -> bijective (ltrans x).
Proof.
move => x Hx.
have Hx1: H x^-1 by apply subgrpV.
exists (ltrans x^-1); move => [y Hy];
  rewrite /ltrans;
  (case (wb (H x)); case => Ux; last by move: Hx; rewrite Ux);
  (case (wb (H x^-1)); case => Ux1; last by move: Hx1; rewrite Ux1);
  apply/val_eqP => //=; apply/eqP;
  move/andP: Hy => [Hy1 Hy2];
  rewrite -{2}(eqP Hy1);
  (apply/rootP; first by exact: lcoset_csym).
  rewrite lcoset_trans // {1}/lcoset -{2}(invg_inv y) -invg_mul mulgA -invg_mul.
  apply: subgrpV => //.
  exact: root_lcosetd.
rewrite lcoset_trans // {1}/lcoset.
replace ((x * root (lcoset L) (x^-1 * y))^-1 * y) with
  (((x^-1 * y)^-1 * root (lcoset L) (x^-1 * y))^-1); last by gsimpl.
apply: subgrpV => //.
exact: root_lcosetd.
Qed.

Lemma ltrans_morph: forall x y z,
  H x -> H y -> ltrans (x * y) z = ltrans x (ltrans y z).
Proof.
move => x y [z Hx] Hkx Hky.
have F1: H (x * y) by apply: subgrpM.
rewrite /ltrans.
case (wb (H (x * y))); case; last (by rewrite F1); move => H1.
case (wb (H x)); case; last (by rewrite Hkx); move => H2.
case (wb (H y)); case; last (by rewrite Hky); move => H3.
apply/val_eqP => //=; apply/eqP.
apply/rootP; first by apply: lcoset_csym.
rewrite lcoset_trans // {1}/lcoset.
replace ((x * y * z)^-1 * (x * root (lcoset L) (y * z))) with
  ((y * z)^-1 * root (lcoset L) (y * z)); last by gsimpl.
exact: root_lcosetd.
Qed.

End LeftTrans.

Section Bij.

Open Scope group_scope.

Variable (G : finGroup) (H K: set G).

Hypothesis subgrp_K: subgrp K.
Hypothesis subgrp_H: subgrp H.
Hypothesis subset_HK: subset H K.


Lemma setI_roots: forall x, K x ->
  setI (roots (lcoset H)) K (root (lcoset H) x).
Proof.
move => x H1; rewrite /setI roots_root; last by apply: lcoset_csym.
rewrite andTb.
replace (root (lcoset H) x) with
  (x * (x^-1 * root (lcoset H) x)); last by gsimpl.
apply: subgrpM => //.
apply: (subsetP subset_HK).
exact: root_lcosetd.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the left            *)
(*    translation  of coset of H in K                                  *)
(*                                                                     *)
(***********************************************************************)

Definition lS0 := S0 H (ltrans subgrp_K subgrp_H subset_HK subset_HK).

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
