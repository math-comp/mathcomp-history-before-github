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
Require Import baux.
Require Import normal.
Require Import cyclic.
Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Center.

Open Scope group_scope.
   
Variables (G: finGroupType) (H: setType G).

Hypothesis gH: group H.

(**********************************************************************)
(*  Definition of the center                                          *)
(*                                                                    *)
(*      x in C, if forall y in H, xy = yx                             *)
(**********************************************************************)

Definition center := {x, H x && (subset H (fun y => x * y == y * x))}.

Lemma centerP: forall x,
  reflect (H x /\ (forall y, H y -> x * y = y * x)) (center x).
Proof.
move => x; apply: (iffP idP);rewrite s2f.
  move/andP => [H1 H2]; split => // y Hy.
  by move/subsetP: H2 => H2; rewrite (eqP (H2 _ Hy)).
move => [H1 H2]; rewrite /center H1 /=; apply/subsetP => y Hy.
by rewrite H2.
Qed.

Lemma subset_center: subset center H.
Proof.
by apply/subsetP => x; move/centerP => [H1 _].
Qed.

Lemma subgrp_center: group center.
Proof.
apply/groupP;rewrite !s2f group1 //.
split; first by rewrite andTb; apply/subsetP=>x Hx; rewrite mulg1 mul1g.
move => x y; move/centerP=>[Hx HHx];  move/centerP=>[Hy HHy].
apply/centerP; split; first by rewrite groupM.
by move=> z Hz; rewrite -mulgA (HHy z Hz) [z*(x*y)]mulgA -(HHx z Hz) mulgA.
Qed.

  
(*********************************************************************)
(*              Definition of the centraliser                        *)
(*    y is in the centraliser of x if y * x = y * x                  *)
(*********************************************************************)

Definition centraliser x := {y, (H x && H y) && (x * y == y * x)}.

Lemma centraliser_id: forall x, H x -> centraliser x x.
Proof.
by move => x Hx; rewrite s2f Hx // eq_refl.
Qed.

Lemma centraliserP: forall x y,
  reflect (and3 (H x) (H y) (x * y = y * x)) (centraliser x y).
Proof.
move => x y; apply: (iffP idP);rewrite s2f.
  move/andP => [H1 H3]; case/andP: H1 => H1 H2; repeat split => //.
  by apply/eqP.
by move => [H1 [H2 H3]]; rewrite /centraliser H1 H2 /=; apply/eqP.
Qed.

Lemma subset_centraliser: forall x, subset (centraliser x) H.
Proof.
by move => x; apply/subsetP => y; move/centraliserP => [_ H1 _].
Qed.

Lemma group_centraliser: forall x, H x -> group (centraliser x).
Proof.
move => x Hx; apply/groupP;split.
  apply/centraliserP; repeat split => //; first exact: group1.
  by gsimpl.
move => x1 y1; move/centraliserP => [H1 H2 H3]; 
  move/centraliserP => [H4 H5 H6].
apply/centraliserP; repeat split => //; first exact: groupM. 
by rewrite mulgA H3 -mulgA H6 mulgA.
Qed. 

Lemma centraliserC: forall x y, centraliser x y -> centraliser y x.
Proof.
move => x y; move/centraliserP => [H1 H2 H3].
by apply/centraliserP; repeat split.
Qed.

Lemma centraliserM: forall x y z, H x ->
  centraliser x y -> centraliser x z -> 
  centraliser x (y * z). 
Proof.
move => x y z Hx.
case/centraliserP => Hy Hy1 Hy2.
case/centraliserP => Hz Hz1 Hz2.
apply/centraliserP; repeat split => //.
  by exact: groupM.
by rewrite mulgA Hy2 -mulgA Hz2; gsimpl.
Qed.

Lemma centraliserV: forall x y, H x ->
  centraliser x y -> centraliser x (y^-1). 
Proof.
move => x y Hx.
case/centraliserP => Hy Hy1 Hy2.
apply/centraliserP; repeat split => //.
  by rewrite groupV.
by apply: (mulg_injl y); apply: (mulg_injr y); gsimpl.
Qed.

Lemma centraliserEr: forall x y n, H x ->
  centraliser x y -> centraliser x (y ** n). 
Proof.
move => x y n Hx; elim: n => [| n].
  move => _; apply: group1; exact: group_centraliser.
move => H1 H2; move: (H1 H2).
move/centraliserP => [H3 H4 H5].
move/centraliserP: H2 => [H6 H7 H8].
apply/centraliserP.
repeat split => //; rewrite !gexpnS; first by rewrite groupM.
by rewrite mulgA H8 -!mulgA H5.
Qed.

Lemma centraliserEl: forall x y n, H x ->
  centraliser x y -> centraliser (x ** n) y. 
Proof.
move => x y n Hx H1; apply: centraliserC.
apply: centraliserEr; last exact: centraliserC.
by move/centraliserP:H1 => [H2 H3 H4].
Qed.

Lemma normal_centraliser: forall x, H x ->
  normal (cyclic x) (centraliser x).
Proof.
move => x Hx; apply/normalP.
move => x1 H1.
move/centraliserP: H1 => [H2 H3 H4].
apply/isetP=>y. 
rewrite -cyclic_conjgs /conjg -mulgA H4 mulgA; gsimpl.
Qed.

Lemma cyclic_subset_centraliser: forall x,
     H x -> subset (cyclic x) (centraliser x).
Proof.
move => x H1; apply/subsetP => y Hy.
case/cyclicP: Hy => n Hn.
by rewrite -(eqP Hn) ?centraliserEr // centraliser_id.
Qed.


(*********************************************************************)
(*              Definition of the quotient of the centraliser        *)
(*              by its cyclic group                                  *)
(*********************************************************************)

Section Kb.

Variable x: G.
Hypothesis Hx: H x.

Notation KRG := (RG (subgrp_cyclic x)(group_centraliser Hx)
                    (cyclic_subset_centraliser Hx)
                    (normal_centraliser Hx)).

Notation quotient :=
  ((quotient (subgrp_cyclic x)(group_centraliser Hx)
           (cyclic_subset_centraliser Hx)
           (normal_centraliser Hx)): G -> KRG).


Lemma KRG1P: forall (y: KRG),
  reflect (cyclic x (val y)) (y == 1).
Proof.
move => y; apply: (iffP idP) => Hx1.
  apply: (@quotient1_inv _ _ _
           (subgrp_cyclic x)(group_centraliser Hx)
           (cyclic_subset_centraliser Hx)
           (normal_centraliser Hx)); first by
    case: {Hx1}y => /= y; case/andP.
  rewrite (eqP Hx1); exact: quotient_val.
rewrite -(quotient_val
           (subgrp_cyclic x)(group_centraliser Hx)
           (cyclic_subset_centraliser Hx)
           (normal_centraliser Hx) y).
by apply/eqP; apply: quotient1.
Qed.

Lemma KRG_quotient1: forall y,
  centraliser x y -> quotient y = 1 -> exists i, y = x ^ i.
Proof.
move => y Cxy Hy.
case/cyclicP: (quotient1_inv Cxy Hy) => i Hi.
by exists i; apply sym_equal; apply/eqP.
Qed.

Lemma KRGE: forall (y: KRG),
  exists i,  x ^ i ==  (val y) ^ (orderg y).
Proof.
move => y.
have F0: centraliser x (val y).
  by case y => /= v; case/andP.
case: (@KRG_quotient1 ((val y)^(orderg y))); first by
  rewrite centraliserEr.
  rewrite quotient_expn // quotient_val.
  apply/eqP; exact: orderg_expn1.
by move => i ->; exists i.
Qed.

(* proof to be reworked *)
Lemma orderg_krg: forall p (Hp: prime p) l (y: KRG),
  (orderg x = p ^ (S l))%N ->
  coprime (orderg x) (orderg y) -> exists z:G,
     (coprime (orderg x) (orderg z)) && (quotient z == y) && 
     (centraliser x z).
move => p Hp l y Hox Hy.
case: (KRGE y) => i Hi.
move: (abezout_modn (orderg x) (orderg y)); 
case: abezoutn => u v.
move: (Hy); rewrite coprimeC {1}/coprime => Hy1; 
  rewrite (eqP Hy1).
rewrite (modn_small 1).
   move => HH.
have C0: centraliser x (val y).
  by case: (y) => y1 /=; case/andP.
have C1: centraliser x (x ^ v).
  by apply: centraliserEr => //; exact: centraliser_id.
have F0: commg x (val y).
  by case/andP: C0 => _; move/eqP.
have F1: x ^ (v * (orderg y)) = x.
  rewrite -(mul1g (gexpn _ _)) -(gexp1n G u)
          -(eqP (orderg_expn1 x)) gexpn_mul (mulnC _ u)
          gexpn_add.
  by rewrite (edivn_modn (_ + _) (orderg y * orderg x))
           HH -gexpn_add gexpn1 mulnC (mulnC (orderg _))
           -!mulnA -gexpn_mul (eqP (orderg_expn1 _))
           gexp1n mul1g.
have F2: x ^ ((i * v) * orderg y) = (val y) ^ (orderg y).
  by rewrite -(eqP Hi) -!mulnA mulnC -gexpn_mul F1.
set k1 := ((i * v) * (orderg x - 1))%N.
have F3: (x ^ k1 * (val y)) ^(orderg y) = 1.
  rewrite gexpnC; last 
    by apply: (commgC (commg_expn _ (commgC _))).
  rewrite gexpn_mul -F2 gexpn_add. 
  rewrite /k1 -!mulnA !(mulnA i) -muln_addr.
  rewrite -{2}(mul1n (orderg y)) -muln_addl.
  rewrite addnC leq_add_sub; last exact: orderg_pos.
  by rewrite mulnC -!mulnA -gexpn_mul (eqP (orderg_expn1 _))
         gexp1n.
have F4: centraliser x (x ^ k1).
  by apply: (centraliserEr _ _ _) => //;
     exact: centraliser_id.
exists (x ^ k1 * (val y)).
apply/andP; split; last
  by apply: (centraliserM _ _).
apply/andP; split.
  move/eqP: F3; rewrite -orderg_divn.
  case/divnP => k Hk.
  by move: Hy; rewrite Hk coprime_mulr; case/andP.
apply/eqP.
rewrite quotient_mul //.
rewrite (quotient_val
           (subgrp_cyclic x)(group_centraliser Hx)
           (cyclic_subset_centraliser Hx)
           (normal_centraliser Hx) y).
rewrite -{2}(mul1g y); congr mulg.
apply/eqP; apply/KRG1P.
case: (val_quotient
       (subgrp_cyclic x)(group_centraliser Hx)
       (cyclic_subset_centraliser Hx)
       (normal_centraliser Hx) F4).
intros k2; case/andP; case/cyclicP => k3.
move/eqP => <-; move/eqP => ->.
by rewrite gexpn_add cyclic_in.
apply: (@leq_trans (S (1 * orderg y))); first
  by rewrite mul1n ltnS orderg_pos.
rewrite lt_mul2r Hox; apply/andP; split.
  apply (@leq_trans (S (S l))) => //.
  apply: expn_lt; exact: prime_leq_2.
by move: (orderg_pos y); case (orderg y).
Qed.

Lemma KB_image: forall p (Hp: prime p) l s,
  (orderg x = p ^ (S l))%N -> (coprime (orderg x) s) ->
  image quotient
            (fun z => (centraliser x z) && (divn (orderg z) s)) =1
            (fun z => divn (orderg z) s).
move => p Hp l s H1 H2 x1; apply eqb_imp => H3.
  case: (Hdiinv H3) => y; case/and3P => HH1 HH2 HH3.
  rewrite orderg_divn; apply/KRG1P.
  rewrite (eqP HH1) -quotient_expn //.
  have F1: centraliser x (y ^ s).
    by apply: (centraliserEr _ _ _). 
  case: (val_quotient
         (subgrp_cyclic x)(group_centraliser Hx)
         (cyclic_subset_centraliser Hx)
         (normal_centraliser Hx) F1). 
  move => y2; case/andP; case/cyclicP => n1. 
  move/eqP => <-; move/eqP => ->.
  by rewrite orderg_divn in HH3;
     rewrite (eqP HH3) mul1g cyclic_in.
have F1: coprime (orderg x) (orderg x1).
  case/divnP: H3 => k1 Hk1.
  by move: H2; rewrite Hk1 coprime_mulr; case/andP.
case: (orderg_krg Hp H1 F1) => x2.
case/andP; case/andP => Hx1 Hx2 Hx3.
rewrite -(eqP Hx2) image_f_imp //.
rewrite Hx3 /=.
apply: (divntrans _ _ _ _ H3).
rewrite -(gauss _ (orderg x)); last by rewrite coprimeC.
rewrite mulnC orderg_divn.
have K1: x1 ^ (orderg x1) = 1.
   by apply/eqP; rewrite orderg_expn1.
move: K1; rewrite -{1}(eqP Hx2).
rewrite -quotient_expn // => HH.
have F2: centraliser x (x2 ^ (orderg x1))
  by apply: centraliserEr.
move: (quotient1_inv F2 HH); case/cyclicP => i.
rewrite -gexpn_mul; move/eqP => <-.
by rewrite gexpn_mul mulnC -gexpn_mul (eqP (orderg_expn1 _))
           gexp1n.
Qed.

Lemma KB_card_image: forall p (Hp: prime p) l s,
  (orderg x = p ^ (S l))%N -> (coprime (orderg x) s) ->
  card (fun z => (centraliser x z) && (divn (orderg z) s)) =
  card (fun z: KRG => divn (orderg z) s).
Proof.
move => p Hp l s Hx1 Hx2.
apply: etrans (eq_card (KB_image Hp Hx1 Hx2)).
apply: sym_equal; apply: card_dimage.
move => y1 y2; case/andP => H1 H2; case/andP => H3 H4 H5.
move: (quotient_quotient_inv H1 H3 H5).
case/cyclicP => i Hi.
have F0: y1 * x ^ i = y2 by rewrite (eqP Hi); gsimpl.
have F1: divn (orderg x) (i * (orderg y1 * orderg y2)).
  rewrite orderg_divn -gexpn_mul; apply/eqP.
  rewrite -(gexp1n _ (orderg y1)) -(eqP (orderg_expn1 y2))
          !gexpn_mul -F0 gexpnC //; last
    by apply: commg_expn; case/andP: H1 => _; move/eqP.
  by rewrite (mulnC _ (orderg y1)) -!gexpn_mul (eqP (orderg_expn1 _))
             gexp1n mul1g.
rewrite -F0 -{1}(mulg1 y1); congr mulg; apply sym_equal.
apply/eqP; rewrite -orderg_divn. 
rewrite mulnC gauss // in F1.
rewrite coprime_mulr; apply/andP; split.
  case/divnP: H2 => k1 Hk1.
  by rewrite Hk1 coprime_mulr in Hx2; case/andP: Hx2.
case/divnP: H4 => k1 Hk1.
by rewrite Hk1 coprime_mulr in Hx2; case/andP: Hx2.
Qed.

End Kb.

End Center.

Unset Implicit Arguments.
