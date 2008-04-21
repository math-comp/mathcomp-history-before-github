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
Require Import ssrfun.
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
Require Import finset.
Require Import bigops.
Require Import automorphism.
Require Import group_perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Center.

Open Scope group_scope.

Variable (elt : finGroupType).

(**********************************************************************)
(*  Definition of the center                                          *)
(*                                                                    *)
(*      x in C, if forall y in H, xy = yx                             *)
(**********************************************************************)

Section CenterDefinitions.

Variable H : {group elt}.

Definition center := [set x \in H | H \subset (commute x : pred elt)].

Lemma centerP : forall x,
  reflect (x \in H /\ (forall y, y \in H -> x * y = y * x)) (x \in center).
Proof.
move => x; apply: (iffP idP); rewrite setE.
  move/andP => [H1 H2]; split => // y Hy.
  by move/subsetP: H2 => H2; rewrite (eqP (H2 _ Hy)).
move => [H1 H2]; rewrite /center H1 /=; apply/subsetP => y Hy.
by apply/eqP; rewrite H2.
Qed.

Lemma subset_center : center \subset H.
Proof. by apply/subsetP => x; move/centerP => [Hx _]. Qed.

Lemma group_centerP : group_set center.
Proof.
apply/groupP; rewrite !setE group1 //=.
split; first by apply/subsetP=> x Hx; rewrite -topredE /commute /= mulg1 mul1g.
move=> x y; move/centerP=> [Hx HHx]; move/centerP=> [Hy HHy].
apply/centerP; split; first by rewrite groupM.
by move=> z Hz; rewrite -mulgA (HHy z Hz) [z*(x*y)]mulgA -(HHx z Hz) mulgA.
Qed.

Canonical Structure group_center := Group group_centerP.

End CenterDefinitions.

Definition set_commute (H K : {set elt}) :=
  forall a b, a \in H -> b \in K -> commute a b.

Lemma centerC : forall H : {group elt}, set_commute (center H) H.
Proof.
by move => x y H; move/centerP => [Hy1 Hy2] Hx; rewrite /commute (Hy2 _ Hx).
Qed.

Lemma CtoN: forall (H : {group elt}) (K : {set elt}),
  set_commute K H  -> K \subset H -> K <| H.
Proof.
move => H K mulC SK; apply/normalP => x Kx.
apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP => y; rewrite /sconjg setE.
  move => Khyp; move:(mulC _ _ Khyp Kx); move/conjg_fpP; unlock conjg_fp;move/eqP=>Hrw.
  by move:Khyp; rewrite -Hrw /conjg invgK !mulgA mulVg mul1g -mulgA mulVg mulg1.
move => Ky; rewrite -groupV in Kx; move: (mulC _ _ Ky Kx).
by move/conjg_fpP; rewrite/conjg_fp; move/eqP =>->.
Qed.

Definition centerN (H:group elt) : (center H) <| H :=
  (CtoN (@centerC H) (subset_center _ )).

Lemma characteristic_center : forall (H : group elt),
  characteristic H (center H).
Proof.
move=> H; apply/subset_charP; split; first exact:subset_center.
move=> f Haut /=; apply/subsetP=> x Hfx; apply/centerP.
move/andP: (isom_morph_of_aut Haut)=> [Hm _]; split.
  move/eqP: Hm =><-; rewrite /morph_of_aut /= Haut /=.
  move/andP: (Haut)=>[_ Hmorph].
  rewrite -(dfequal_imset (dfequal_morphicrestr Hmorph)).
  by move/subsetP: (subset_imset f (subset_center H)); apply.
move=> y; rewrite -(eqP Hm)=> Hy; move/imsetP : Hfx=> [x0 Hx0 ->].
move/imsetP : Hy=> [y0 Hy0 ->]; rewrite /morph_of_aut /= Haut /=.
move/andP: (Haut)=>[_ Hmorph]; move/subsetP: (subset_center H)=>Hsub.
rewrite -(dfequal_morphicrestr Hmorph) //; move/morphP: (Hmorph)=> morphM.
by move/centerP: Hx0 => [Hx Hcen]; rewrite -!morphM // Hcen.
Qed.

Section CyclicCenter.

Variable H : group elt.

(* G. 1.3.4 *)

Lemma center_cyclic_abelian : forall a,
  (H / (center H)) = (cyclic a) -> H = {center H as group _}.
Proof.
move => a Ha; apply set_of_group_inj; apply/setP.
apply/subset_eqP; apply/andP; split; last exact:subset_center.
case trivco:(trivm (coset_of ({center H as group _}))).
  move/trivm_coset_of: trivco=>/= Hnorm.
  by move: (centerN H); rewrite /normal Hnorm.
have Hdec: forall z, z \in H ->
  exists2 x, x \in center H & exists n, z = x * (repr a ** n).
  move=> z Hz; move/subsetP: (centerN H); move/(_ z Hz)=> Nz.
  move:(rcoset_refl ({center H as group _}) z); rewrite -(coset_ofN Nz).
  have: coset_of (center H) z \in H / center H by apply/imsetP; exists z.
  rewrite Ha; move/cyclicP=> [n]; move/eqP=> <-.
  rewrite -{1}(coset_of_repr a) -coset_ofE; last first.
    by move/idPn: trivco;move/dom_coset=> ->; exact: norm_repr_coset.
  rewrite coset_ofN; last by apply :groupE; exact:norm_repr_coset.
  by move/rcosetP=>[x Hcen Hquo]; exists x =>//; exists n.
apply/subsetP=> /= x Hx; rewrite setE Hx andTb; apply/subsetP=> y Hy.
move: (Hdec _ Hx) (Hdec _ Hy) => [xx Hcx [nx Hnx]] [yy Hcy [ny Hny]].
have [Hxx Hyy]: xx \in H /\ yy \in H.
  by split; exact: (subsetP (subset_center H)).
have Hanx: repr a ** nx \in H by rewrite -(groupMl _ Hxx) -Hnx.
have Hany: repr a ** ny \in H by rewrite -(groupMl _ Hyy) -Hny.
rewrite Hnx Hny /commute -topredE /=.
rewrite mulgA -(mulgA xx _ yy); move/eqP: (centerC Hcy Hanx) => <-.
rewrite mulgA -(mulgA (xx * yy) _ _) gexpn_add addnC -gexpn_add.
rewrite mulgA -(mulgA xx yy _); move/eqP:(centerC Hcx (groupM Hyy Hany))=>->.
by rewrite mulgA eqxx.
Qed.

End CyclicCenter.

(*********************************************************************)
(*              Definition of the centraliser                        *)
(*    y is in the centraliser of x if y * x = x * y                  *)
(*********************************************************************)

Variable H : {group elt}.

Definition centraliser x := H :&: [set y | commute x y].

Lemma centraliser_id: forall x, x \in H -> x \in centraliser x.
Proof. by move => x Hx; rewrite !setE /commute eq_refl; apply/andP. Qed.

Lemma centraliserP: forall x y,
  reflect (y \in H /\ x * y = y * x) (y \in centraliser x).
Proof.
move=> x y; rewrite /centraliser /commute !setE.
by apply: (iffP andP); case; split => //; apply/eqP.
Qed.

Lemma subset_centraliser : forall x, centraliser x \subset H.
Proof. move=> x; exact: subsetIl. Qed.

Lemma centraliser1 : forall x, 1 \in centraliser x.
Proof. by move=> x; apply/centraliserP; gsimpl. Qed.

Lemma group_centraliserP : forall x, group_set (centraliser x).
Proof.
move=> x; apply/groupP; split; first exact: centraliser1.
move=> x1 y1; case/centraliserP=> Hy cxx1; case/centraliserP=> Hz cxy1.
apply/centraliserP; split; first by rewrite groupM.
by rewrite mulgA cxx1 -mulgA cxy1 mulgA.
Qed.

Canonical Structure group_centraliser x := Group (group_centraliserP x).

Lemma centraliserC : forall x y,
  x \in H -> y \in centraliser x -> x \in centraliser y.
Proof. by move => x y Hx; case/centraliserP=> *; apply/centraliserP. Qed.

Lemma centraliserM : forall x y z,
  y \in centraliser x -> z \in centraliser x -> y * z \in centraliser x.
Proof. move=> *; exact: groupM. Qed.

Lemma centraliserV : forall x y,
  y \in centraliser x -> y^-1 \in centraliser x.
Proof. by move=> *; rewrite groupV. Qed.

Lemma centraliserEr : forall x y n,
  y \in centraliser x -> y ** n \in centraliser x.
Proof. move=> *; exact: groupE. Qed.

Lemma centraliserEl : forall x y n, x \in H ->
  y \in centraliser x -> y \in centraliser (x ** n).
Proof.
move => x y n Hx; case/centraliserP=> Hy cxy.
by apply: centraliserC=>//; apply: centraliserEr; apply/centraliserP.
Qed.

Section CyclicCentraliser.

Lemma normal_centraliser: forall x, x \in H -> cyclic x <| centraliser x.
Proof.
move => x Hx; apply/normalP; move => y.
case/centraliserP=> Hy cxy; apply/setP=>z.
by rewrite -cyclic_conjgs /conjg -mulgA cxy mulgA; gsimpl.
Qed.

Lemma cyclic_subset_centraliser: forall x,
     x \in H -> cyclic x \subset centraliser x.
Proof.
move => x Hx; apply/subsetP => y Hy; case/cyclicP: Hy => n Hn.
by rewrite -(eqP Hn) ?centraliserEr // centraliser_id.
Qed.

Lemma centraliser_normaliser:
  forall x, x \in H -> centraliser x \subset normaliser (cyclic x).
Proof.
move => x Hx.
move/subsetP: (cyclic_subset_centraliser Hx) => Hcn.
apply/subsetP=> y; case/centraliserP=> Hy cxy.
rewrite setE; apply/subsetP=> z; rewrite setE => Czy.
have:= Czy; case/cyclicP=> n; rewrite /conjg; gsimpl; move/eqP=> dx.
case/centraliserP: (Hcn (z ^ y^-1) Czy) => Hz cxzy.
apply/cyclicP; exists n => /=; apply/eqP.
apply: (can_inj (conjgK y^-1)); rewrite dx /conjg; gsimpl.
apply: (can_inj (mulgK x)).
move: cxzy; rewrite /conjg; gsimpl => <-.
rewrite -(@mulgA _ (x*y) z _) -(@mulgA _ x y _) (@mulgA _ y z _) -dx.
rewrite -(@mulgA _ _ y^-1 x) -(@mulgA _ _ z y^-1) -(@mulgA _ y y _).
rewrite (@mulgA _ y z _) -dx; gsimpl.
rewrite (eqP (commute_expn n _)); gsimpl; last by rewrite /commute cxy.
by rewrite (eqP (commute_expn n _)) // /commute.
Qed.

End CyclicCentraliser.

End Center.

Section CharacteristicCentralizer.

Variable G: finGroupType.

Definition centralizer (H: group G) (A : {set _}) :=
  \bigcap_(i \in A) (centraliser H i).

Lemma group_centralizerP: forall H A, group_set (centralizer H A).
Proof.
move=> H A; apply:(@big_prop _ (@group_set _)); first exact:group_setA.
  move => a b HGa HGb; exact: group_setI (Group HGa) (Group HGb).
move => x I; exact: set_of_groupP.
Qed.

Canonical Structure centralizer_group H A := Group (group_centralizerP H A).

Lemma char_centralizer_ofchar : forall (I H: group _),
  characteristic I H ->
  characteristic I (centralizer I H).
Proof.
move=> I H HcharH.
have H1: forall k,
  k \in (centralizer I H) ->
  forall y f, Aut I f -> y \in H -> k * (perm_inv f y) = (perm_inv f y) * k.
  move=> k Hcen y f Haut Hy; move: Hy; move/andP: HcharH=>[HsubK]; move/forallP.
  move/(_ f); move/implyP; move/(_ Haut); move/eqP=><-.
  move/imsetP=> [y0 Hy0 ->]; rewrite permE !finv_f; last by apply: perm_inj.
  by move/bigcapP: Hcen; move/(_ _ Hy0); move/centraliserP=>[_ ->].
have H2: (centralizer_group I H) \subset I.
  apply/subsetP=> x; move/bigcapP; move/(_ _ (group1 H)).
  by move/centraliserP=>[HH _].
apply/subset_charP; split; first by trivial.
move=> f Haut; apply/subsetP=> fk Hfk; move/imsetP: Hfk=>[k Hk ->].
have H3: (f@: I = I) by apply:(autom_imset Haut).
apply/bigcapP=> i Hi; apply/centraliserP; split.
  by rewrite -H3 imset_f_imp //; apply: (subsetP H2).
have H4: ((perm_inv f)@: I = I) by apply:(autom_imset (automorphic_inv Haut)).
have H5: ((perm_inv f i) \in I).
  rewrite -H4 imset_f_imp //; move/subset_charP: HcharH=> [Hsub _].
  by apply:(subsetP Hsub).
 move/andP: (Haut)=> [_]; move/morphP=>Hmorph.
 move: (Hmorph _ _ (subsetP H2 _ Hk) H5).
rewrite (H1 k Hk i f Haut Hi) (Hmorph _ _ H5 (subsetP H2 _ Hk)) permE f_finv.
  by move=>->.
by apply:perm_inj.
Qed.

End CharacteristicCentralizer.

Unset Implicit Arguments.
