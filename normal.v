(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of conjugate set, normal set and quotient group        *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Normal.

Open Scope group_scope.

Variables (G: finGroupType) (H K: set G).

Hypothesis subgrp_H: group H.
Hypothesis subgrp_K: group K.
Hypothesis subset_HK: subset H K.


(**********************************************************************)
(*  Definition of the conjugate set xHx^-1,                           *)
(*                                                                    *)
(*      y in xHx^-1 iff x^-1yx is in H                                *)
(**********************************************************************)

(* le conjugué de y par x est dans H *)
Definition conjsg x y := H (y ^g x).

Theorem conjsgE : forall x y, conjsg x y = H (y ^g x).
Proof. done. Qed.

Theorem conjsg1: forall x, conjsg x 1.
Proof. by move=> x; rewrite/conjsg conj1g; apply: group1. Qed.

Theorem conjs1g: forall x, conjsg 1 x = H x.
Proof. by move=> x; rewrite/conjsg conjg1. Qed.

Theorem conjsg_inv: forall x y, conjsg x y -> conjsg x y^-1.
Proof. move=> x y; rewrite/conjsg  conjg_invg; exact: groupVr. Qed.

Theorem conjsg_conj: forall x y z, conjsg (x * y) z = conjsg y (z ^g x).
Proof. by move=> x y z;rewrite/conjsg conjg_conj. Qed.

Theorem conjsg_subgrp: forall x, group (conjsg x).
Proof. 
  move=> x.
  apply/andP; split; first by apply: conjsg1.
  apply/subsetP=> z; case/prodgP=> x1 x2 Hx1 Hx2 ->{z};rewrite /conjsg conjg_mul.
  exact: groupM. 
Qed.

Theorem conjsg_image: forall y,
  conjsg y =1 image (conjg y^-1) H.
Proof.
  move=> y x; rewrite {2} (_:x = conjg y^-1 (conjg y x )).
    rewrite/conjsg image_f; by [rewrite /conjg | apply conjg_inj].
  by rewrite conjgK.
Qed.

Theorem conjsg_inv1: forall x,
  (conjsg x) =1 H -> (conjsg x^-1) =1 H.
Proof. move=> x Hx y; by rewrite -conjs1g -(mulVg x) conjsg_conj Hx. Qed.

Theorem conjsg_card: forall x,
  card (conjsg x) = card H.
Proof. move=>x; rewrite (eq_card (conjsg_image x)); apply card_image; exact: conjg_inj. Qed.



(*********************************************************************)
(*              Definition of the normaliser                         *)
(*    the normaliser of H is the set of all elements x of G          *)
(*    such that  xHx^-1 = H                                           *)
(*********************************************************************)

(*
Definition normaliser x := 
  subset G (fun z => (conjsg x z == H z)).
*)
Definition normaliser x := subset H (conjsg x).

Theorem norm_conjsg : forall x,
  normaliser x -> H =1 (conjsg x).
Proof. 
  move=> x Hx;apply/subset_cardP.
  by symmetry;apply conjsg_card.
  by done.
Qed.


Theorem normaliser_grp: group normaliser.
Proof.
  apply/andP; split; apply/subsetP => x Hx.
    by rewrite /conjsg conjg1.
  apply/subsetP => z Hz; case/prodgP: Hx => u v Hu Hv -> {x}.
  by rewrite conjsg_conj; apply (subsetP Hv); rewrite -conjsgE -(norm_conjsg Hu z).
Qed.


Theorem subset_normaliser: subset H normaliser.
Proof.
apply/subsetP => x Hx;rewrite/normaliser;apply/subsetP => y Hy;rewrite/conjsg.
repeat apply: groupM;gsimpl; exact: groupVr;gsimpl.
Qed.

Lemma normaliser_rcoset : closed (rcoset H) normaliser.
Proof. apply closed_rcoset; [exact normaliser_grp | exact subset_normaliser]. Qed.

Lemma normaliser_prodg : subset K normaliser -> prodg H K =1 prodg K H.
Proof.
move=> HK x; apply/idPn/idPn; case/prodgP => u v Hu Hv ->; apply/set0Pn; rewrite/setI.
 exists (conjg v u); rewrite/rcoset {2}/conjg ; gsimpl; rewrite Hv -conjsgE.
 by rewrite (subsetP (subsetP HK v _) u).
exists u; rewrite /rcoset Hu -(invgK u) {2}(invgK u) -conjgE -conjsgE.
by rewrite (subsetP (subsetP HK (u^-1) _) v) // groupV //.
Qed.

Lemma normaliser_prodg_grp : subset K normaliser -> group (prodg H K).
Proof.
move=> H1; apply prodC_group => //; exact: normaliser_prodg.
Qed.

(********************************************************************)
(*              Definition of a normal set                          *)
(*    H is normal in K iff xHx^-1 = H forall x in K                 *)
(*    it is sufficient that H is included in xHx^¯1                 *)
(*    since both sets have same cardinal                            *)
(********************************************************************)


Definition normal := subset K normaliser. 

Theorem normalP:
  reflect (forall x y,  K x -> H y -> H (y ^g x)) normal.
Proof.
apply: (iffP idP).
  move/subsetP => H0 x y H1 H2; exact: (subsetP (H0 x H1)).
move => H0; apply/subsetP => x H1; apply/subsetP => y H2; exact: H0.
Qed.

Theorem conjsg_normal: forall x, 
  normal -> K x -> conjsg x =1 H.
Proof.
move => x H0 H1 y; apply/idP/idP => H2; last exact: (normalP H0) => //.
  rewrite /conjsg in H2; rewrite -conjs1g -(mulgV x) conjsg_conj; apply: (normalP H0) => //.
  exact: groupVr => //.
Qed.

End Normal.

Section NormalProp.

Open Scope group_scope.

Variables (G : finGroupType) (H K : set G).
Hypothesis subgrp_H: group H.
Hypothesis subgrp_K: group K.
Hypothesis subset_HK: subset H K.
Hypothesis normal_HK: normal H K.

Theorem eq_conjsg: forall a b (x: G),
  a =1 b -> conjsg a x =1 conjsg b x.
Proof. by move=> a b x H0 y; rewrite/conjsg H0. Qed.

Theorem normal_subset: forall L,
  group L -> subset H L -> subset L K -> normal H L.
Proof.
  move=> L Hl Hhl Hlk; apply/normalP=> x y Hx Hy;rewrite/conjg.
  by apply: (normalP _ _ normal_HK); first apply: (subsetP Hlk).
Qed.

Theorem normaliser_normal: normal H (normaliser H).
Proof. apply/normalP => x y;move/subsetP => Hx Hy;rewrite -conjsgE; exact: Hx. Qed.



End NormalProp.

Section RcosetRepr.

Open Scope group_scope.

Variables (G : finGroupType) (H : set G).
Hypothesis group_H: group H.

Let group_normH := normaliser_grp H.

Definition rcoset_repr x :=
  if H x then 1 else
  if pick (rcoset H x) is Some y then y else 1.


(* sûrement à mettre dans groups *)
Lemma rcoset_trans1 : forall x y, rcoset H x y -> rcoset H x =1 rcoset H y.
Proof. by move=> x y Hxy u; rewrite /rcoset -{1}(mulgKv y u) -mulgA groupMr. Qed.

Lemma rcoset_trans1r : forall x y, 
  rcoset H x y -> forall z, rcoset H z x = rcoset H z y.
Proof. move=> x y Hxy z; rewrite !(rcoset_sym _ z) //; exact: rcoset_trans1. Qed.

(* choisir x comme valeur par defaut aide pour le cas absurde *)
Lemma rcoset_rcoset_repr : forall x, rcoset H x (rcoset_repr x).
Proof.
rewrite /rcoset_repr => x; case Hx: (H x); first by rewrite rcoset_sym // rcoset1 //.
case pickP => // K; case/idP: {K}(K x); exact: rcoset_refl.
Qed.

(* si on choisis la valeur x par défaut dans le cas absurde, prouver celui là par 
réécriture devient pénible... *)
Lemma rcoset_reprP : forall x y,
  reflect (rcoset_repr x = rcoset_repr y) (rcoset H x y).
Proof.
move => x y; apply: (iffP idP) => [Hxy | Dx].
  rewrite /rcoset_repr (eq_pick (rcoset_trans1 Hxy)).
  by rewrite -!(rcoset1 H) (rcoset_trans1r Hxy).
by rewrite (rcoset_trans1r (rcoset_rcoset_repr y)) -Dx rcoset_rcoset_repr.
Qed.

Lemma rcoset_repr1 : rcoset_repr 1 = 1.
Proof. by rewrite /rcoset_repr [H 1]group1. Qed.

Lemma rcoset_repr1P : forall x, reflect (rcoset_repr x = 1) (H x).
Proof.
move=> x; rewrite -(rcoset1 H) rcoset_sym // -{1}rcoset_repr1; exact: rcoset_reprP.
Qed.

Lemma rcoset_repr_rcoset_repr : forall x, 
  rcoset_repr (rcoset_repr x) = rcoset_repr x.
Proof. move=> x; symmetry; apply/rcoset_reprP; exact:rcoset_rcoset_repr. Qed.

End RcosetRepr.

Section Quotient.

Open Scope group_scope.

Variables (G : finGroupType) (H : set G).
Hypothesis group_H: group H.

Let group_normH := normaliser_grp H.
(*********************************************************************)
(*                                                                   *)
(*    Definition of the finite set of all the elements               *)
(*    of N(H) that are canonical element of the right classes of H   *)
(*                                                                   *)
(*********************************************************************)


Definition coset_repr x := rcoset_repr H (x * (rcoset_repr (normaliser H) x)^-1).

Lemma coset_reprE : forall x,
  rcoset_repr H (x * (rcoset_repr (normaliser H) x)^-1) = coset_repr x.
Proof. move=> x; by rewrite/coset_repr. Qed.


Lemma norm_coset_repr : forall x, normaliser H (coset_repr x).
rewrite /coset_repr => x.
have H1 : rcoset (normaliser H) x (rcoset_repr (normaliser H) x).
  by rewrite rcoset_rcoset_repr // normaliser_grp //.
move : (rcosetP _ _ _ H1) => [y Hy] -> {H1}.
have H2 : rcoset H (x * (y * x)^-1) (rcoset_repr  H (x * (y * x)^-1)).
  by rewrite rcoset_rcoset_repr //.
move : (rcosetP _ _ _ H2) => [z Hz] -> {H2}; gsimpl.
rewrite groupM //; last by rewrite groupV.
by rewrite (subsetP (subset_normaliser group_H)) //.
Qed.

Lemma coset_repr_rcoset_repr : forall x, 
  normaliser H x -> coset_repr x = rcoset_repr H x.
Proof. 
rewrite /coset_repr => x; move /(rcoset_repr1P (normaliser_grp H)) => ->; gsimpl.
Qed.


Lemma coset_reprP : forall x y, normaliser H x -> normaliser H y ->
  reflect (coset_repr x = coset_repr y) (rcoset H x y).
Proof.
move=> x y Hx Hy; rewrite !coset_repr_rcoset_repr //=; exact: rcoset_reprP. 
Qed.


Lemma rcoset_coset_repr : forall x y, rcoset H x y -> coset_repr x = coset_repr y.
Proof. 
move=> x y Hxy; rewrite /coset_repr.
have Hxy2 : rcoset (normaliser H) x y. 
  case/rcosetP: Hxy => z Hz ->; apply/rcosetP; exists z => //. 
  by rewrite (subsetP (subset_normaliser group_H)).
rewrite (rcoset_reprP group_normH _ _ Hxy2).
case/rcosetP : Hxy => z Hz ->; apply /rcoset_reprP =>//; apply /rcosetP; exists z =>//.
by gsimpl.
Qed.


Definition coset_set : set G := fun x => coset_repr x == x.

Lemma coset_set_coset_repr : forall x, coset_set (coset_repr x).
Proof.
move=> x; rewrite /coset_set {1}/coset_repr {2}/rcoset_repr norm_coset_repr; gsimpl.
by rewrite /coset_repr rcoset_repr_rcoset_repr //.
Qed.


Definition coset_sig := eq_sig coset_set.

Coercion mem_coset(u:coset_sig) : set G := rcoset H (val u).

Canonical Structure coset_eqType := @EqType coset_sig _ (@val_eqP _ coset_set).

Lemma coset_eqP : forall u v : coset_sig, reflect (u =1 v) (u == v).
Proof.
move=> u v.
rewrite /mem_coset; apply: (iffP idP);case: u=> {u} u Hu; case: v=> {v} v Hv H1.
-apply: rcoset_trans1 =>//;rewrite (val_eqP H1) /val; exact: rcoset_refl.
-apply/eqP; apply: val_inj; rewrite /val /coset_set  in *.
rewrite  -(eqP Hu) -(eqP Hv). 
rewrite !coset_repr_rcoset_repr; try by rewrite -1?(eqP Hu) -1?(eqP Hv) norm_coset_repr.
by apply /rcoset_reprP => //=; rewrite H1 rcoset_refl.
Qed.


Canonical Structure coset_finType :=
  @FinType coset_eqType _ (@sub_enumP _ coset_set).

Definition coset x : coset_sig := locked (EqSig _ _ (coset_set_coset_repr x)).

Lemma cosetP : forall x y, normaliser H x -> normaliser H y ->
  reflect (coset x = coset y) (rcoset H x y).
Proof. move=> x y Hx Hy; unlock coset; apply: (iffP (coset_reprP Hx Hy)) => H1.
- by apply/val_eqP => /=; apply /eqP.
- case/val_eqP : H1 => H2; exact (eqP H2).
Qed.

Lemma rcoset_coset : forall x y, rcoset H x y -> coset x = coset y.
Proof. 
move=> x y Hxy; unlock coset; apply/val_eqP => /=; apply/eqP; exact: rcoset_coset_repr.
Qed.

Lemma val_coset : forall x, normaliser H x -> val (coset x) = rcoset_repr H x.
Proof. move=> x Hx; unlock coset; rewrite /= coset_repr_rcoset_repr //=. Qed.

(* est-ce utile de le sortir? 
Lemma coset_coset_repr : forall x, val (coset (coset_repr x)) = coset_repr x.
Proof.
move=> x; unlock coset =>/=; move :(coset_set_coset_repr x); rewrite/coset_set; exact: eqP.
Qed.
*)

Lemma coset_val : forall x, coset (val x) = x.
Proof.
move => x; case:x => {x} z; rewrite/coset_set => Hz ; apply/val_eqP => /=.
rewrite -(eqP Hz); apply/eqP; unlock coset =>/=; move :(coset_set_coset_repr z).
rewrite/coset_set; exact: eqP.
Qed.

Definition coset_unit := coset 1.

Definition coset_inv (u : coset_sig) := coset (val u)^-1.

Definition coset_mul (u v : coset_sig) := coset (val u * val v).

Lemma norm_val_coset : forall x, normaliser H (val (coset x)).
Proof. move=> x; unlock coset; exact:norm_coset_repr. Qed.

Notation Local N := (normaliser H).


Lemma coset_mul_morph : forall x y,
    normaliser H x ->
  coset (x * y) = coset_mul (coset x) (coset y).
Proof.
move=> x y Hx; rewrite /coset_mul; apply: val_inj.
symmetry; rewrite val_coset; last by apply groupM =>//; apply: norm_val_coset.
rewrite val_coset // /coset -!lock /=; apply /rcoset_reprP=> //.
rewrite -mulgA /coset_repr; set z := y * _; rewrite (_ : y * _ = z); last 
  by congr (y * _^-1); apply /rcoset_reprP=> //; rewrite /rcoset; gsimpl; rewrite groupV.
rewrite /rcoset (norm_conjsg Hx) /conjsg /conjg -groupV //; gsimpl.
rewrite -(mulgA _ _ z^-1) groupM //; last exact: rcoset_rcoset_repr.
rewrite (norm_conjsg (groupVr group_normH Hx)) // /conjsg /conjg; gsimpl.
exact: rcoset_rcoset_repr.
Qed.

Lemma normaliser_val : forall u:coset_sig, normaliser H (val u).
Proof. 
move=> u; move: (valP u); rewrite /coset_set=> Hu; rewrite -(eqP Hu); exact: norm_coset_repr.
Qed.

Hint Resolve normaliser_val.


Lemma coset_unitP : forall u, coset_mul coset_unit u = u.
Proof.
move=> u;rewrite -(coset_val u) /coset_unit -coset_mul_morph; by [gsimpl|apply group1].
Qed.


Lemma coset_invP : forall u, coset_mul (coset_inv u) u = coset_unit.
Proof.
move=> u; rewrite -{2}(coset_val u) /coset_inv -coset_mul_morph; first by gsimpl.
by rewrite groupV.
Qed.

Lemma coset_mulP : forall u v w,
  coset_mul u (coset_mul v w) = coset_mul (coset_mul u v) w.
Proof.
move=> u v w; rewrite -(coset_val u) -(coset_val v) -(coset_val w).
rewrite -!coset_mul_morph; gsimpl; exact: groupM.
Qed.


Canonical Structure coset_groupType :=
  @FinGroupType coset_finType _ _ _ coset_unitP coset_invP coset_mulP.

Lemma coset_morph : forall x y,
    normaliser H x ->
  coset (x * y) = coset x * coset y.
Proof. move=> x y Nx; rewrite coset_mul_morph //. Qed.

Lemma val_coset1 : val (1:coset_sig) = 1.
Proof. by rewrite/unitg /= /coset_unit val_coset ?rcoset_repr1 // group1. Qed.

(*********************************************************************)
(*              Definition of the quotient group                     *)
(*    the quotient of K by H  is the set of all canonical            *)
(*    elements with the group operations                             *)
(*********************************************************************)

Section OneQuotient.

Variable K : set G.

(* Ca c'est la definition plus simple, mais qui force la definition à être 
le "vrai" quotient H/K car le rcoset_repr caché ote le controle sur le temoins dans H
 et donc demande l'hypothese H inclus dans K.
Definition quotient : set coset_eqType := fun x => K (val x).
*)

(* This is in fact HK/H *)
Definition quotient : set coset_eqType := image coset K.
Hypothesis group_K : group K.
Hypothesis subset_K_N : subset K N.


Lemma group_quotient : group quotient.
Proof.
apply/andP; split.
 by apply/imageP; exists (1:G); first exact: group1.
apply/subsetP => x; case/prodgP => y1 y2; case/imageP => x1 Hx1 -> {y1}. 
case/imageP => x2 Hx2 -> {y2} -> {x}.
rewrite -coset_morph; last exact:(subsetP subset_K_N); apply/imageP; exists (x1 * x2) =>//.
exact: groupM.
Qed.

(* est-ce qu'on prouve ici les lemmes de cardinalite? *)

End OneQuotient.

End Quotient.


Section Morphism.

Open Scope group_scope.
 
Variables (G G': finGroupType) (H : set G) (H': set G').
Variable f : G -> G'.



Definition morphism := forall x y, H x -> H y -> f (x * y) = (f x) * (f y).

Hypothesis f_morph: morphism.

Hypothesis subgrp_H: group H.

Lemma morph1 :  f 1 = 1.
Proof. by apply: (mulg_injl (f 1)); rewrite -f_morph ?group1 // !mulg1. Qed.


Lemma morphV : forall x, 
  H x -> f (x ^-1) = (f x) ^-1.
Proof.
by move=> x Hx; apply: (mulg_injl (f x)); rewrite -f_morph ?groupV // !mulgV morph1.
Qed.

Lemma morph_conjg : forall x y, H x -> H y -> f (x ^g y) = (f x) ^g (f y).
Proof. move=> x y Hx Hy; rewrite/conjg -morphV // -!f_morph // ?groupM // groupV //. Qed.


Hypothesis group_H : group H.

Lemma morph_image_grp : group (image f H).
Proof.
apply/andP; split.
 by apply/imageP; exists (1:G); [apply: group1=>//| symmetry; exact: morph1].
apply/subsetP => x; move/prodgP => [y1 y2 Hy1 Hy2 ->].
move/imageP:Hy1 => [x1 Hx1 ->] {y1}; move/imageP:Hy2 => [x2 Hx2 ->] {y2}.
by rewrite -f_morph //; apply/imageP; exists (x1 * x2) => //; rewrite groupM //.
Qed.


Hypothesis group_H': group H'.

Lemma morph_preimage_grp : subset (preimage f H') H -> group (preimage f H').
Proof.
move/subsetP=>Hsubset; apply/andP; split; rewrite /preimage; first by rewrite morph1 group1 //.
by apply/subsetP=> x Hx; case/prodgP:Hx => x1 x2 Hx1 Hx2 ->; rewrite f_morph ?groupM ?Hsubset.
Qed.

Variable K : set G.

Hypothesis group_K : group K.
Hypothesis subset_KH : subset K H.

Lemma morph_normal_im : normal K H -> normal (image f K) (image f H).
Proof.
move/normalP =>Hn; apply/normalP => x y; move/imageP => [u Hu ->]; move/imageP => [v Hv ->].
apply/imageP; exists (v ^g u); first by apply Hn. rewrite -morph_conjg //. 
move/subsetP:subset_KH => -> //.
Qed.



End Morphism.

Unset Implicit Arguments.






