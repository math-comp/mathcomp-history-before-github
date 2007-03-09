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
Require Import normal.
Require Import cyclic.
Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Center.

Open Scope group_scope.
   
Variables (G: finGroupType) (H: group G).

(**********************************************************************)
(*  Definition of the center                                          *)
(*                                                                    *)
(*      x in C, if forall y in H, xy = yx                             *)
(**********************************************************************)

Definition center := {x, H x && (subset H (commute x))}.

Lemma centerP: forall x,
  reflect (H x /\ (forall y, H y -> x * y = y * x)) (center x).
Proof.
move => x; apply: (iffP idP);rewrite s2f.
  move/andP => [H1 H2]; split => // y Hy.
  by move/subsetP: H2 => H2; rewrite (eqP (H2 _ Hy)).
move => [H1 H2]; rewrite /center H1 /=; apply/subsetP => y Hy.
by apply/eqP;rewrite H2.
Qed.

Lemma subset_center: subset center H.
Proof. by apply/subsetP => x; move/centerP => [Hx _]. Qed.

Lemma group_centerP: group_set center.
Proof.
apply/groupP;rewrite !s2f group1 //=.
split; first by apply/subsetP=>x Hx; rewrite /commute mulg1 mul1g.
move => x y; move/centerP=>[Hx HHx];  move/centerP=>[Hy HHy].
apply/centerP; split; first by rewrite groupM.
by move=> z Hz; rewrite -mulgA (HHy z Hz) [z*(x*y)]mulgA -(HHx z Hz) mulgA.
Qed.

Canonical Structure group_center := Group group_centerP.
  
(*********************************************************************)
(*              Definition of the centraliser                        *)
(*    y is in the centraliser of x if y * x = y * x                  *)
(*********************************************************************)

Definition centraliser x := H :&: {y, commute x y}.

Lemma centraliser_id: forall x, H x -> centraliser x x.
Proof. by move => x Hx; rewrite !s2f /commute eq_refl; apply/andP. Qed.

Lemma centraliserP: forall x y,
  reflect (H y /\ x * y = y * x) (centraliser x y).
Proof. 
move=> x y; rewrite /centraliser /commute !s2f. 
by apply: (iffP andP); case; split => //; apply/eqP.
Qed.

Lemma subset_centraliser: forall x, subset (centraliser x) H.
Proof. by move => x; apply/subsetP => y; case/centraliserP. Qed.

Lemma centraliser1 : forall x, centraliser x 1.
Proof. by move=> x; apply/centraliserP; gsimpl. Qed.

Lemma group_centraliserP: forall x, group_set (centraliser x).
Proof.
move => x; apply/groupP; split; first exact: centraliser1.
move => x1 y1; case/centraliserP=> Hy cxx1; case/centraliserP=> Hz cxy1. 
apply/centraliserP; split; first by rewrite groupM.
by rewrite mulgA cxx1 -mulgA cxy1 mulgA.
Qed. 

Canonical Structure group_centraliser x := Group (@group_centraliserP x).

Lemma centraliserC: forall x y, H x -> centraliser x y -> centraliser y x.
Proof. by move => x y Hx; case/centraliserP=> *; apply/centraliserP. Qed.

Lemma centraliserM: forall x y z, 
  centraliser x y -> centraliser x z -> centraliser x (y * z). 
Proof. move=> *; exact: groupM. Qed.

Lemma centraliserV: forall x y,
  centraliser x y -> centraliser x (y^-1). 
Proof. by move=> *; rewrite groupV. Qed.

Lemma centraliserEr: forall x y n,
  centraliser x y -> centraliser x (y ** n). 
Proof. move=> *; exact: groupE. Qed.

Lemma centraliserEl: forall x y n, H x ->
  centraliser x y -> centraliser (x ** n) y. 
Proof.
move => x y n Hx; case/centraliserP=> Hy cxy.
by apply: centraliserC=>//; apply: centraliserEr; apply/centraliserP.
Qed.

Lemma normal_centraliser: forall x, H x ->
  normal (cyclic x) (centraliser x).
Proof.
move => x Hx; apply/normalP; move => y.
case/centraliserP=> Hy cxy; apply/isetP=>z.
by rewrite -cyclic_conjgs /conjg -mulgA cxy mulgA; gsimpl.
Qed.

Lemma cyclic_subset_centraliser: forall x,
     H x -> subset (cyclic x) (centraliser x).
Proof.
move => x Hx; apply/subsetP => y Hy; case/cyclicP: Hy => n Hn.
by rewrite -(eqP Hn) ?centraliserEr // centraliser_id.
Qed.

(*********************************************************************)
(*              Definition of the quotient of the centraliser        *)
(*              by its cyclic group                                  *)
(*********************************************************************)

Section Kb.

Variable x: G.
Hypothesis Hx: H x.

Definition KRG := (coset_groupType (group_cyclic x)).


Lemma centraliser_normaliser: 
  forall y:G, centraliser x y -> normaliser (cyclic x) y.
Proof.
move/subsetP:(cyclic_subset_centraliser Hx)=>Hcn.
move=>y;case/centraliserP=> Hy cxy.
rewrite s2f; apply/subsetP=> z; rewrite s2f=> Czy.
have:=Czy; case/cyclicP=> n; rewrite /conjg; gsimpl; move/eqP=> dx.
case/centraliserP: (Hcn (z ^ y^-1) Czy) => Hz cxzy.
apply/cyclicP; exists n=>/=; apply/eqP.
apply: (can_inj (conjgK y^-1)); rewrite dx /conjg; gsimpl.
apply: (can_inj (mulgK x)).
move:cxzy; rewrite /conjg; gsimpl=><-.
rewrite -(@mulgA _ (x*y) z _) -(@mulgA _ x y _) (@mulgA _ y z _) -dx.
rewrite -(@mulgA _ _ y^-1 x) -(@mulgA _ _ z y^-1) -(@mulgA _ y y _).
rewrite (@mulgA _ y z _) -dx; gsimpl.
rewrite (eqP (commute_expn n _)); gsimpl; last by rewrite /commute cxy.
by rewrite (eqP (commute_expn n _)) // /commute.
Qed.


Lemma KRG_quotient1: forall y:G,
  centraliser x y -> coset (cyclic x) y = (1:KRG) -> exists i, x ** i == y.
Proof.
move=> y cxy; move:(centraliser_normaliser cxy)=> Ny {cxy}.
rewrite /coset Ny norm_grcoset //; move/isetP=> Cry {Ny}.
have:= Cry 1; rewrite s2f mul1g =>d11 {Cry}.
apply/cyclicP; apply: groupVl. rewrite d11; exact: group1.
Qed.


Lemma KRG_repr: forall (y: KRG), y (repr y).
Proof.
move => y; exact: coset_group_repr.
Qed.

Lemma KRG_coset_of_repr: forall (y: KRG), coset_of (cyclic x) (repr y) = y.
Proof.
move => y; exact: coset_of_repr.
Qed.


Lemma KRG1P: forall (y: KRG),
  reflect (cyclic x (repr y)) (y == 1).
Proof.
exact: repr_1.
Qed.

Lemma KRGE: forall (y: KRG),
  exists i,  x ** i ==  (repr y) ** (orderg y).
Proof.
move => y.
apply/cyclicP.
move: (@cosetE_repr _ (group_cyclic x) y (orderg y)).
by rewrite (eqP (@orderg_expn1 _ y)).
Qed.

(* proof to be reworked *)
Lemma orderg_krg: forall p (Hp: prime p) l (y: KRG),
  (centraliser x / cyclic x) y ->
  (orderg x = p ^ (S l))%N ->
  coprime (orderg x) (orderg y) -> exists z:G,
     (coprime (orderg x) (orderg z)) && (coset (cyclic x) z == y) && 
     (centraliser x z).
move => p Hp l y Hc Hox Hy.
case: (KRGE y) => i Hi.
move: (Hy); rewrite coprime_sym {1}/coprime => Hy1.
move:  (bezoutr (orderg x) (orderg_pos y)).
  rewrite gcdnC (eqP Hy1); case => u Hu.
  case/dvdnP => v Hv.
have C0: centraliser x (repr y).
  apply: quotient_repr => //.
  exact: cyclic_subset_centraliser.
have C1: centraliser x (x ** v).
  by apply: centraliserEr => //; exact: centraliser_id.
have F0: commute x (repr y).
  rewrite /centraliser in C0.
  by case/isetIP:C0 => /=; rewrite s2f.
have F1: x ** (v * (orderg y)) = x.
  by rewrite -Hv -gexpn_add gexpn1 mulnC -gexpn_mul
             (eqP (orderg_expn1 x)) gexp1n mulg1.
have F2: x ** ((i * v) * orderg y) = (repr y) ** (orderg y).
  by rewrite -(eqP Hi) -!mulnA mulnC -gexpn_mul F1.
set k1 := ((i * v) * (orderg x - 1))%N.
have F3: ((x ** k1) * (repr y)) ** (orderg y) = 1.
  rewrite gexpnC; last by
   apply: (commute_sym (commute_expn _ (commute_sym _))).
  rewrite gexpn_mul -F2 gexpn_add. 
  rewrite /k1 -!mulnA !(mulnA i) -muln_addr.
  rewrite -{2}(mul1n (orderg y)) -muln_addl.
  rewrite addnC leq_add_sub; last exact: orderg_pos.
  by rewrite mulnC -!mulnA -gexpn_mul (eqP (orderg_expn1 _))
         gexp1n.
have F4: centraliser x (x ** k1).
  by apply: centraliserEr; exact: centraliser_id.
exists ((x ** k1) * (repr y)).
apply/andP; split; last
  by apply: (centraliserM _ _).
apply/andP; split.
  move/eqP: F3; rewrite -orderg_dvd.
  case/dvdnP => k Hk.
  by move: Hy; rewrite Hk coprime_mulr; case/andP.
rewrite /= cosetN; last 
   by apply: centraliser_normaliser (centraliserM _ _).
rewrite -{2}(coset_of_repr y) {2}/set_of_coset /=.
rewrite /= cosetN //; last
   by apply: centraliser_normaliser.
apply/eqP.
apply: (@rcoset_trans1 _ (group_cyclic x)) => /=.
apply/rcosetP; exists ((x ** k1)^-1); gsimpl.
apply: groupVr; apply: cyclic_in.
Qed.

Lemma KB_image: forall p (Hp: prime p) l s,
  (orderg x = p ^ (S l))%N -> (coprime (orderg x) s) ->
  image (coset_of (cyclic x))
            (fun z => (centraliser x z) && (dvdn (orderg z) s)) =1
            (fun z => (centraliser x/cyclic x) z && dvdn (orderg z) s).
move => p Hp l s H1 H2 x1; apply/idP/idP => H3.
  case: (Hdiinv H3) => y; case/and3P => HH1 HH2 HH3.
  rewrite orderg_dvd.
  apply/andP; split; first
    by apply/iimageP; exists y => //; exact: (eqP HH1).
  rewrite (eqP HH1) -coset_ofE; last
    by apply: centraliser_normaliser.
  replace (y ** s) with (1:G); first by rewrite coset_of_id.
  by symmetry; apply/eqP; rewrite -orderg_dvd.
case/andP: H3 => H3 H4.
have F1: coprime (orderg x) (orderg x1).
  case/dvdnP: H4 => k1 Hk1.
  by move: H2; rewrite Hk1 coprime_mulr; case/andP.
case: (orderg_krg Hp H3 H1 F1) => x2.
case/andP; case/andP => Hx1 Hx2 Hx3.
have E1: x1 = coset_of (cyclic x) x2 by symmetry; apply/eqP.
rewrite E1 image_f_imp //.
rewrite Hx3 /=.
apply: dvdn_trans H4.
rewrite -(@gauss _ (orderg x)); last by rewrite coprime_sym.
rewrite mulnC orderg_dvd.
have K1: x1 ** (orderg x1) = 1.
   by apply/eqP; rewrite orderg_expn1.
move: K1; rewrite {1}E1.
rewrite -coset_ofE; last by apply: centraliser_normaliser.
have F2: centraliser x (x2 ** (orderg x1))
  by apply: centraliserEr.
move/eqP; move/(ker_cosetP (centraliser_normaliser F2)).
case/cyclicP => i.
rewrite -gexpn_mul; move/eqP => <-.
by rewrite gexpn_mul mulnC -gexpn_mul (eqP (orderg_expn1 _))
           gexp1n.
Qed.

Lemma KB_card_image: forall p (Hp: prime p) l s,
  (orderg x = (p ^ (S l))%N) -> (coprime (orderg x) s) ->
  card (fun z => (centraliser x z) && (dvdn (orderg z) s)) =
  card (fun z => (centraliser x/cyclic x) z && dvdn (orderg z) s).
Proof.
move => p Hp l s Hx1 Hx2.
apply: etrans (eq_card (KB_image Hp Hx1 Hx2)).
apply: sym_equal; apply: card_dimage.
move => y1 y2; case/andP => H1 H2; case/andP => H3 H4 H5.
have E0: coset_of (cyclic x) (y1^-1 * y2) == 1.
  rewrite morph_coset_of; first last; first by apply: centraliser_normaliser.
    apply: centraliser_normaliser.
    by apply centraliserV.
  rewrite -H5 coset_ofV; gsimpl.
  by apply: centraliser_normaliser.
have E1: normaliser (cyclic x) (y1^-1 * y2).
  apply: centraliser_normaliser.
  apply: centraliserM => //.
  by exact: centraliserV.
move/(ker_cosetP E1): E0.
case/cyclicP => i Hi.
have F0: y1 * (x ** i) = y2 by rewrite (eqP Hi); gsimpl.
have F1: dvdn (orderg x) (i * (orderg y1 * orderg y2)).
  rewrite orderg_dvd -gexpn_mul; apply/eqP.
  rewrite -(gexp1n _ (orderg y1)) -(eqP (orderg_expn1 y2))
          !gexpn_mul -F0 gexpnC //; last
    by apply: commute_expn; apply: commute_sym;
       case/isetIP: H1; rewrite s2f.
  by rewrite (mulnC _ (orderg y1)) -!gexpn_mul (eqP (orderg_expn1 _))
             gexp1n mul1g.
rewrite -F0 -{1}(mulg1 y1); congr mulg; apply sym_equal.
apply/eqP; rewrite -orderg_dvd. 
rewrite mulnC gauss // in F1.
rewrite coprime_mulr; apply/andP; split.
  case/dvdnP: H2 => k1 Hk1.
  by rewrite Hk1 coprime_mulr in Hx2; case/andP: Hx2.
case/dvdnP: H4 => k1 Hk1.
by rewrite Hk1 coprime_mulr in Hx2; case/andP: Hx2.
Qed.

End Kb.

End Center.

Unset Implicit Arguments.
