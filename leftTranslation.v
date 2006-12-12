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

Variable (G : finGroupType) (H K L: set G).

Hypothesis group_K: group K.
Hypothesis group_L: group L.
Hypothesis group_H: group H.
Hypothesis subset_HK: subset H K.
Hypothesis subset_LK: subset L K.

Let repr := rcoset_repr L.
Let repr_set := fun x:G => repr x == x. 
Let repr_sig := eq_sig repr_set.

Lemma repr_in : forall x, K x -> K (repr x).
Proof.
move =>x Kx.
rewrite /repr /rcoset_repr; case: pickP => //; last by rewrite if_same group1 //.
move => y; move/rcosetP => [h Lh ->].
case: (L x); first by rewrite group1 //.
rewrite groupM //.
exact: (subsetP subset_LK h Lh).
Qed.

Lemma th_rtrans1: repr_set (repr 1).
Proof. by rewrite /repr_set /repr !rcoset_repr1. Qed.

Lemma th_rtrans_gen: forall a b, H a -> repr_set b -> repr_set (repr (b*a^-1)).
Proof.
move => a b Ha; rewrite /repr_set /repr /= => rb.
rewrite rcoset_repr_rcoset_repr //.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the left translation as an action on cosets          *)
(*      a |->  [ bH |-> (ab)H]                                         *)
(*                                                                     *)
(***********************************************************************)

Definition raLinK (a : G) (rp : repr_sig) : option repr_sig :=
  let (r,p) := rp in
  if H a =P true is Reflect_true Ha then Some (EqSig _ _ (th_rtrans_gen Ha p)) 
  else None.

Definition rtrans (a : G) (rp : repr_sig) : repr_sig :=
  match raLinK a rp with
  | None => EqSig _ _ th_rtrans1
  | Some e => e
  end.

CoInductive raLinK_spec (a : G) (rp : repr_sig) : option repr_sig -> Type :=
  | Translated rp1 : H a -> repr (val rp1) = repr (val rp * a^-1) -> raLinK_spec a rp (Some rp1)
  | NotTranslated : ~~H a -> raLinK_spec a rp None.

Lemma raLinKP : forall a r, raLinK_spec a r (raLinK a r).
Proof.
move => a [r p]; rewrite /raLinK. 
case: eqP; last by move/negP => FHa; apply: (NotTranslated _ FHa).
move => Ha.
set rp1 := (EqSig _ (repr (r*a^-1)) (th_rtrans_gen Ha p)).
set rp := (EqSig repr_set r p).
cut (repr (val rp1) = repr (val rp * a^-1)); first move => XX2; last rewrite /rp1 /= /repr rcoset_repr_rcoset_repr //. 
exact: (Translated Ha XX2).
Qed.

Lemma rtrans_1: forall x, rtrans 1 x = x.
Proof.
move => [r p]; rewrite /rtrans.
case raLinKP; last by move/negP;have := (group1 group_H).
gsimpl=> [[r1 p1 /= _ E]]; apply: val_inj => /=.
by rewrite -(eqP p) -(eqP p1).
Qed.

(* with the old definition of action, this was the needed proof:

Lemma rtrans_bij: forall x, H x -> bijective (rtrans x).
Proof.
move => a Ha; exists (rtrans a^-1); rewrite/rtrans. 
  move => [r p].
  case raLinKP; last by move/negP=> Ha1; rewrite groupV in Ha1.
  move=> [r1 p1] Ha1; case raLinKP; last by move/negP => *.
  move => [r2 p2] _ /= Err2_rra Err1_rr2a.
  apply: val_inj => /=; rewrite -(eqP p1) -(eqP p). 
  apply/rcoset_reprP=>//; apply /rcosetP. 
  have Hr1 : rcoset L (r2 * a^-1^-1) r1 by apply/rcoset_reprP=>//.
  move/rcosetP:Hr1=>[l1 Ll1]; gsimpl => Dl1.
  have Hr2 : rcoset L (r * a^-1) r2 by apply/rcoset_reprP=>//.
  move/rcosetP:Hr2=>[l2 Ll2]; gsimpl => Dl2.
  exists (r*r1^-1); last by gsimpl.
  rewrite Dl1 Dl2; gsimpl.
  by rewrite groupM // groupV //.
move => [r p].
case raLinKP; last by move/negP=> *.
move=> [r1 p1] _; case raLinKP; last by move/negP => Ha1; rewrite groupV in Ha1.
move => [r2 p2] _ /= Err2_rra Err1_rr2a.
apply: val_inj => /=; rewrite -(eqP p1) -(eqP p).
apply/rcoset_reprP=>//; apply /rcosetP.
exists (r*r1^-1); last by gsimpl.
have Hr1 : rcoset L (r2 * a^-1) r1 by apply/rcoset_reprP=>//.
move/rcosetP:Hr1=>[l1 Ll1 ->]; gsimpl.
have Hr2 : rcoset L r2 (r * a^-1^-1) by apply/rcoset_reprP=>//.
move/rcosetP:Hr2=>[l2 Ll2]; gsimpl => ->; gsimpl.
by rewrite groupM // groupV //.
Qed.

*)

Lemma rtrans_morph: forall x y z,
  H x -> H y -> rtrans (x * y) z = rtrans x (rtrans y z).
Proof.
move => x y [r p] Hx Hy.
rewrite /rtrans.
case raLinKP; case raLinKP; try move/negP => //.
  move=> [r1 p1]; case raLinKP; last by move/negP.
  move=> [r2 p2] _ /= Err2_rry _ Err1_rr2x [r3 p3] /= Hxy Err3_rrxy.
  apply: val_inj => /=; rewrite -(eqP p3) -(eqP p1).
  apply/rcoset_reprP=>//; rewrite rcoset_sym //; apply /rcosetP.
  exists (r3*r1^-1); last by gsimpl.
  have :(rcoset L (r * y^-1) r2) by rewrite rcoset_sym //; apply/rcoset_reprP=>//.
  move/rcosetP => [l2 Ll2 Dl2].
  have :(rcoset L (r2 * x^-1)) r1 by apply/rcoset_reprP=>//.
  move/rcosetP => [l1 Ll1 Dl1].
  have :(rcoset L (r*(x * y)^-1) r3) by apply/rcoset_reprP=>//.
  move/rcosetP => [l3 Ll3 Dl3].
  rewrite Dl3 Dl1 Dl2; gsimpl.
  by rewrite !groupM // groupV.
move=> [r1 p1]; case raLinKP; last by move/negP.
move=> [r2 p2] _ /= _ _ _; move/negP=> FHxy.
by have : H (x*y) by rewrite groupM.
Qed.

End RightTrans.

Section Bij.

Open Scope group_scope.

Variable (G : finGroupType) (H K: set G).

Hypothesis group_K: group K.
Hypothesis group_H: group H.
Hypothesis subset_HK: subset H K.

Let repr := rcoset_repr H.
Let repr_set := fun x:G => repr x == x. 
Let repr_sig := eq_sig repr_set.

Lemma repr_in2: forall x, K x ->
  setI repr_set K (repr x).
Proof.
move => x H1; rewrite /setI (repr_in group_K subset_HK) // andbT.
rewrite /repr_set /repr rcoset_repr_rcoset_repr //.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the left            *)
(*    translation  of coset of H in K                                  *)
(*                                                                     *)
(***********************************************************************)

Let sH := filter H (enum G).

Definition rSO := SO sH (rtrans G group_H).

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
