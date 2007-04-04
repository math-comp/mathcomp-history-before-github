(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of the production of two groups                        *)
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
Require Import div.
Require Import  baux.
Require Import  groups.



Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Prod.

Open Scope group_scope.

Variables (G: finGroup) (H K : set G).

(***********************************************************************)
(*                                                                     *)
(*  Definition of the product of two sets  H and K                     *)
(*                                                                     *)
(***********************************************************************)

Definition prodf (z: prod_finType G G) := eq_pi1 z * eq_pi2 z.

Definition prod := image prodf (prod_set H K).

Lemma prodP: forall z, 
  reflect (exists x, exists y, H x && K y && (z == x * y)) (prod z).
move => z; apply: (iffP idP).
  move => H1.
  pose (a := diinv H1).
  exists (eq_pi1 a); exists (eq_pi2 a).
  by move: (a_diinv H1) (f_diinv H1); rewrite -/a /prodf /prod_set => -> -> /=.
move => [x [y H1]]; case/andP: H1 => H1 H2; rewrite (eqP H2).
exact: (@image_f_imp _ _ prodf _ (EqPair x y)).
Qed.

Lemma in_prod : forall h k, H h -> K k -> prod (h*k).
Proof.
by move=>  h k Hh Hk;apply/prodP;exists h; exists k;rewrite Hh Hk /=.
Qed.

End Prod.
Section SubProd.
Open Scope group_scope.

Variable G: finGroup.

Section SubProd_subgrp.

Variables (H K : set G).
Hypothesis H_subgroup: subgrp H.
Hypothesis K_subgroup: subgrp K.

(***********************************************************************)
(*                                                                     *)
(*  HK is a subgroup iff HK = KH                                       *)
(*                                                                     *)
(***********************************************************************)

Lemma subprod_sbgrp: prod H K =1 prod K H -> subgrp (prod H K).
Proof.
move => prod_sym; apply: (@finstbl_sbgrp _ _ 1) => //.
  apply/prodP; exists (Group.unit G); exists (Group.unit G).
  by rewrite !subgrp1 // mul1g eq_refl.
move => x y.
move/prodP => [x1 [y1 Hxy1]]; case (andP Hxy1);
  move/andP => [H1 H2]; move/eqP => {Hxy1}H3; rewrite {}H3.
move/prodP => [x2 [y2 Hxy2]]; case (andP Hxy2);
  move/andP => [H4 H5]; move/eqP => {Hxy2}H6; rewrite {}H6.
rewrite -[(x1 * _) * _]mulgA (mulgA y1).
have P1: prod H K (y1 * x2).
  rewrite prod_sym; apply/prodP; exists y1; exists x2.
  by rewrite H2 H4 eq_refl.
case/prodP: P1; move => x3 [y3 Hxy3].
move:(andP Hxy3) => {Hxy3} [Hxy Hxy3].
move: Hxy; move/andP => [Hxy1 Hxy2].
rewrite (eqP Hxy3).
apply/prodP; exists (x1 * x3); exists (y3 * y2).
apply/andP; split; last by rewrite !mulgA eq_refl.
by apply/andP; split; rewrite subgrpMl.
Qed.

Lemma sbgrp_subprod: subgrp (prod H K) -> prod H K =1 prod K H.
Proof.
move => Hprodsbgrp z; apply eqb_imp; 
    [move/(subgrpV Hprodsbgrp) | 
     move => H1; apply (subgrpVl Hprodsbgrp); move: H1];
    case/prodP => x; case => y;
    case/andP; case/andP => Hx Ky Eqz;
    apply/prodP; exists (y^-1); exists (x^-1).
  rewrite (subgrpV K_subgroup Ky) (subgrpV H_subgroup Hx) /=.
  by apply/eqP; replace z with (z^-1^-1); first rewrite (eqP Eqz); 
     gsimpl.
rewrite (subgrpV H_subgroup Ky) (subgrpV K_subgroup Hx) /=.
by apply/eqP; replace z with (z^-1^-1); first rewrite (eqP Eqz); 
     gsimpl.
Qed.

End SubProd_subgrp.

Variables (H K : set G).
Hypothesis H_subgroup: subgrp H.
Hypothesis K_subgroup: subgrp K.

Lemma sbgrphk_sbgrpkh: subgrpb (prod H K) =  subgrpb (prod K H).
Proof.
apply/idP/idP => [Hhk|Hkh];
apply: subprod_sbgrp => //.
  by move/(sbgrp_subprod H_subgroup K_subgroup): Hhk => Hkheq x; 
     rewrite (Hkheq x).
by move/(sbgrp_subprod K_subgroup H_subgroup): Hkh => Hkheq x; 
   rewrite (Hkheq x).
Qed.

End SubProd.

Section card_prod.

Open Scope group_scope.

Variable G: finGroup.

Variables (H K : set G).
Hypothesis H_subgroup: subgrp H.
Hypothesis K_subgroup: subgrp K.

Lemma card_prodf_inv: forall z, prod_set  H K z ->
  card (setI H K) = card (setI (preimage (@prodf G) (set1 (prodf z))) (prod_set H K)).
Proof.
pose g z (x: G) := EqPair (eq_pi1 z *x) (x^-1 * eq_pi2 z).
move => z Hz.
have F1:  dinjective (setI H K) (g z).
  case: z Hz => z1 z2.
  rewrite /prod_set /=; case/andP => Hz1 Kz2;rewrite /dinjective /g => x y HiKx Hiky /=.
  by case/pair_eqP; case/andP; move/eqP => H1; move/eqP=>H2; apply: (mulg_injl z1).
have F2: image (g z) (setI H K) =1 
    (setI (preimage (@prodf G) (set1 (prodf z))) (prod_set H K)).
  case: z F1 Hz => z1 z2 F1.
  case/andP => /= [Hz1 Hz2] [x1 x2];apply eqb_imp => /= H1.
    rewrite /preimage /prodf /=; pose a:= (diinv H1).
    case/andP: (a_diinv H1); rewrite -/a => Ha Ka.
    case: (f_diinv H1); rewrite -/a => <- <-.
    by rewrite /setI /prod_set /=; apply/and3P; split => //; 
       first gsimpl; rewrite subgrpM // subgrpV.
  move: H1; case/andP => /= => H1; case/andP => /= => Hx1 Hx2;
  move: H1;rewrite /preimage; rewrite /prodf /=.
  move/eqP => Hzx; pose a:= z1^-1*x1.
  replace(EqPair (d1:=G) (d2:=G) x1 x2) with (g(EqPair z1 z2) a); last
    by rewrite /g /a /=;congr EqPair;gsimpl;
       apply:(mulg_injl x1);gsimpl.
  apply  image_f_imp.
  assert (z1^-1*x1 = z2*x2^-1).
    apply: (mulg_injl z1); gsimpl; apply: (mulg_injr x2); gsimpl.
    rewrite /a /setI subgrpM //=; last exact: subgrpV.
    by rewrite H0 subgrpM // subgrpV.
apply trans_equal with (@card (prod_finType G G) (image (g z) (setI H K ))).
 by symmetry; apply: card_dimage;apply F1.
by apply eq_card;exact: F2.
Qed.

Lemma image_prodf: image (@prodf G) (prod_set H K) =1 prod H K.
Proof.
move => x; apply eqb_imp.
  move => H1; apply /prodP; pose a:= (diinv H1);
  exists (eq_pi1 a);exists (eq_pi2 a).
  assert (f1 := a_diinv H1); case/andP: f1; rewrite -/a.
  move => -> -> /=.
  by apply/eqP; symmetry; apply: (f_diinv H1).
case/prodP => x1 [y1 H1]; replace x with (prodf (EqPair x1 y1)).
  by apply image_f_imp;by case/andP :H1.
by case/andP: H1=> _ h; symmetry; exact:(eqP h).
Qed.


(***********************************************************************)
(*                                                                     *)
(*  Cardinal of the product and cardinal of the intersection           *)
(*                                                                     *)
(***********************************************************************)

Theorem cardHK : (card H * card K = card (prod H K) * card (setI H K))%N.
Proof.
rewrite -card_prod_set; rewrite -(eq_card image_prodf).
apply: (card_partition_id (partition_preimage (prod_set H K) (@prodf G))).
move => x H1 ; symmetry.
replace x with (prodf (diinv H1)).
  by apply card_prodf_inv;exact:a_diinv.
exact: f_diinv.
Qed.

End card_prod.