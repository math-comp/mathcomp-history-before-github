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
Require Import groups.



Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SubProd.
Open Scope group_scope.

Variable G: finGroupType.

Section SubProd_subgrp.

Variables (H K : setType G).
Hypothesis group_H: group H.
Hypothesis group_K: group K.

(***********************************************************************)
(*                                                                     *)
(*  HK is a subgroup iff HK = KH                                       *)
(*                                                                     *)
(***********************************************************************)

Lemma prodg_sym_group: prodg H K =1 prodg K H -> group (prodg H K).
Proof.
move => prod_sym; apply/groupP; split.
  rewrite -(mulg1 1); apply/prodgP; exists (1:G) (1:G)=> //; exact: group1.
move => x y.
case/prodgP => x1 y1 Hx1 Hy1 ->. 
case/prodgP => x2 y2 Hx2 Hy2 ->. 
rewrite -[(x1 * _) * _]mulgA (mulgA y1).
have P1: prodg H K (y1 * x2) by rewrite prod_sym; apply/prodgP; exists y1 x2.
case/prodgP: P1 => x3 y3 Hx3 Hy3 ->.
by rewrite -(mulgA x3) mulgA; apply/prodgP; exists (x1*x3) (y3*y2) => //; rewrite groupM.
Qed.

Lemma group_prodg_sym: group (prodg H K) -> prodg H K =1 prodg K H.
Proof.
move => group_prod z; rewrite [prodg]lock; apply/idP/idP; unlock => H1.
 replace z with (z^-1^-1); last by gsimpl.
 case/prodgP: (groupVr group_prod H1) => x y Hx Hy ->; gsimpl.
 by apply/prodgP; exists y^-1 x^-1; rewrite ?groupV //.
rewrite -groupV //.
case/prodgP: H1 => x y Hx Hy ->; gsimpl.
apply/prodgP; exists y^-1 x^-1; rewrite ?groupV //.
Qed.

End SubProd_subgrp.

Variables (H K : setType G).
Hypothesis group_H: group H.
Hypothesis group_K: group K.

Lemma prodg_group_group: group (prodg H K) =  group (prodg K H).
Proof.
by apply/idP/idP => H1; apply: prodg_sym_group => // x;
  rewrite (group_prodg_sym _ _ H1).
Qed.

End SubProd.

Section card_prod.

Open Scope group_scope.

Variable G: finGroupType.

Variables (H K : setType G).
Hypothesis group_H: group H.
Hypothesis group_K: group K.

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
  case/andP => /= [Hz1 Hz2] [x1 x2]; 
    rewrite [image]lock; apply/idP/idP; unlock => /= H1.
    rewrite /preimage /prodf /=; pose a:= (diinv H1).
    case/andP: (a_diinv H1); rewrite -/a => Ha Ka.
    case: (f_diinv H1); rewrite -/a => <- <-.
    by rewrite /setI /prod_set /=; apply/and3P; split => //;
       first gsimpl; rewrite groupM // groupV.
  move: H1; case/andP => /= => H1; case/andP => /= => Hx1 Hx2;
  move: H1;rewrite /preimage; rewrite /prodf /=.
  move/eqP => Hzx; pose a:= z1^-1*x1.
  replace(EqPair (d1:=G) (d2:=G) x1 x2) with (g(EqPair z1 z2) a); last
    by rewrite /g /a /=;congr EqPair;gsimpl;
       apply:(mulg_injl x1);gsimpl.
  apply  image_f_imp.
  have Ha: z1^-1*x1 = z2*x2^-1.
    apply: (mulg_injl z1); gsimpl; apply: (mulg_injr x2); gsimpl.
  by rewrite /a /setI groupM //= ?groupV // Ha groupM // groupV.
apply trans_equal with (@card (prod_finType G G) (image (g z) (setI H K ))).
 by symmetry; apply: card_dimage;apply F1.
by apply eq_card;exact: F2.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Cardinal of the product and cardinal of the intersection           *)
(*                                                                     *)
(***********************************************************************)

Theorem cardHK : (card H * card K = card (prodg H K) * card (setI H K))%N.
Proof.
rewrite -card_prod_set; rewrite (eq_card (prodg_image H K)).
apply: (card_partition_id (partition_preimage (prod_set H K) (@prodf G))).
move => x H1 ; symmetry.
replace x with (prodf (diinv H1)).
  by apply card_prodf_inv;exact:a_diinv.
exact: f_diinv.
Qed.

End card_prod.