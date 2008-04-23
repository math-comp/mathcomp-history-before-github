(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Milne's lemmas for direct product                                  *)
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
Require Import finset.
Require Import normal.
Require Import div.
Require Import abelian.
Require Import automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section DirProd.

Variable elt: finGroupType.

Definition prodscal := fun (x y: elt * elt) => (x.1 * y.1, x.2 * y.2).

Notation Local "x '*_' y" := (prodscal x y) (at level 40).

Lemma unit_prod : forall x, (1, 1) *_ x = x.
Proof. by case=> s1 s2; rewrite /prodscal !mul1g. Qed.

Lemma inv_prod : forall x, (x.1 ^-1, x.2^-1) *_ x = (1,1).
Proof. by case=> s1 s2; rewrite /prodscal !mulVg. Qed.

Lemma mul_prod : forall x y z,
  x *_ (y *_ z) = x *_ y *_ z.
Proof. by move=> x y z; rewrite /prodscal /= !mulgA. Qed.

Canonical Structure prod_group := FinGroupType unit_prod inv_prod mul_prod.

Definition prod_dir  (H1 H2: {set elt}) := [set x| (x.1 \in H1) && (x.2 \in H2)].

Lemma group_prod_dirP : forall (H1 H2:group _), group_set (prod_dir H1 H2).
Proof.
move=> H1 H2; apply/groupP; split; first by rewrite setE !group1.
case => [x1 x2]; case=> [y1 y2]; rewrite !setE; move/andP=> /= [Hx1 Hx2].
by move/andP=> [Hy1 Hy2]; rewrite !groupM.
Qed.

Canonical Structure group_prod_dir H1 H2 := Group (group_prod_dirP H1 H2).

Definition mgmulg : elt * elt -> elt:= (fun x => x.1 * x.2).

Lemma mgmulg_imset : forall (H1 H2: group elt),
  mgmulg @: (prod_dir H1 H2) = (H1 :*: H2).
Proof.
move=> H1 H2.
apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP=> x Hx.
  move/imsetP: Hx=> [x0]; rewrite setE=> Hx0 ->; move/andP: Hx0=> [Hx01 Hx02].
  by apply/smulgP; apply: (@MemProdg _ _ _ _ x0.1 x0.2).
apply/imsetP; case/smulgP: Hx=> x1 x2 Hx1 Hx2 Heq.
by exists (x1, x2); rewrite ?setE ?Hx1 ?Hx2.
Qed.

Lemma dirprod_isom : forall (H1 H2 G:group _),
  reflect
  (com H1 H2  /\
  G = {H1 :**: H2 as group _} /\ disjointg H1 H2)
  (morphic (prod_dir H1 H2) mgmulg && isom mgmulg (prod_dir H1 H2) G).
Proof.
move=> H1 H2 G; apply: (iffP idP).
  move/andP=> [Hmorph]; move/andP=> [Heq Hinj]; split.
    apply/comP; move=> x y Hx Hy; move/morphP: Hmorph; move/(_ (1, y) (x, 1)).
    rewrite !setE Hx Hy !group1 andbT; move/(_ is_true_true is_true_true).
    by rewrite /prodscal /mgmulg /= !mul1g !mulg1.
  split.
    move: Heq; rewrite mgmulg_imset eq_sym; move/eqP.
    by move/group_gmul_eq=>Heq.
  apply/subsetP=> x Hx; move/setIP : Hx=> [H1x H2x].
  have Hinprod: (x, x^-1)\in (prod_dir H1 H2)
    by rewrite setE /= H1x groupV H2x andTb.
  have: (mgmulg (x, x^-1) = 1) by rewrite /mgmulg mulgV.
  move/(kermorphicP Hmorph); move: (injm_dom Hinj); rewrite -eqsetIl setIC.
  move/eqP=> /= ->; rewrite Hinprod; move/(_ is_true_true).
  have:= (ker_r_dom mgmulg)=><-; move/setIP=>[Hker Hindom].
  move: Hinprod; move/(conj Hker); move/setIP; rewrite (ker_injm Hinj).
  by rewrite setE; move/eqP; case=>-> _; rewrite setE eqxx.
move=>[Hcom [Hsurj Htriv]].
have Hmorph: (morphic (prod_dir H1 H2) mgmulg).
  apply/morphP=> x y; rewrite !setE; move/andP=> [Hx1 Hx2];move/andP=> [Hy1 Hy2].
  rewrite {1}/mulg /prodscal /mgmulg /= -2!mulgA (mulgA y.1) (mulgA x.2).
  by suff: (y.1 * x.2 = x.2 * y.1); [move=>->|move/comP: Hcom;apply].
apply/andP; split; first by trivial.
apply/andP; split.
  move: (com_smulgC Hcom) => Hprod; rewrite mgmulg_imset Hsurj /=.
  exact: com_gmulg_smulg Hcom.
have Hker: ker_(prod_dir H1 H2) mgmulg = [set 1].
  apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP;
  last by move=> x; rewrite setE; move/eqP=>->; rewrite setE !group1.
  case => [x1 x2]; rewrite setE; move/andP=> [Hker]; rewrite setE /=.
  move/andP=> [Hx1 Hx2]; move/(morphicmker Hmorph): Hker.
  rewrite setE /mgmulg /= -(mulgK x1 1) mul1g; move/mulg_injl=> Hx12.
  move: (Hx1); rewrite -groupV -Hx12=> Hx21; move: (Hx2); move/(conj Hx21).
  move/setIP; move/trivgP: (Htriv) =>/= ->; rewrite setE; move/eqP=> Hxx2.
  move: Hx2; rewrite {1}Hx12 groupV; move/(conj Hx1); move/setIP.
  move/trivgP: Htriv=>/= ->; rewrite setE; move/eqP=> Hxx1.
  by rewrite Hxx1 Hxx2 eqxx.
have Hinc: group_prod_dir H1 H2 \subset dom mgmulg.
  apply/subsetP=> x Hx.
  case e: (x == 1); first by apply: dom_k; move/eqP: e=>->; apply:group1.
  move/idP: e; move: x Hx; case => [x1 x2]; rewrite setE /=.
  move/andP=>[Hx1 Hx2] Heq; rewrite setE; apply/orP; right.
  rewrite setE /mgmulg /=; apply/negP=> HH; move/eqP: HH.
  rewrite -(mulgK x1 1) mul1g; move/mulg_injl=> Hx12; move: (Hx1).
  rewrite -groupV -Hx12=> Hx21; move: (Hx2); move/(conj Hx21); move/setIP.
  move/trivgP: (Htriv) =>/= ->; rewrite setE; move/eqP=> Hxx2.
  move: Hx2; rewrite Hx12 groupV; move/(conj Hx1); move/setIP.
  move/trivgP: Htriv=>/= ->; rewrite setE; move/eqP=> Hxx1; move: Heq.
  by rewrite Hxx1 Hxx2 eqxx.
by apply: (injm_ker Hinc).
Qed.

Lemma smulg_1set : forall (H1 H2: group elt), 
  (H1 :*: H2 == [set 1]) = (H1 == [set 1] :> set _) && (H2 == [set 1]:> set _).
Proof.
move=> H1 H2; apply/eqP/andP.
  move=> Hprod.
  have Hsub1: ([set 1] \subset H1) by rewrite subset_set1; apply group1.
  have Hsub2: ([set 1] \subset H2) by rewrite subset_set1; apply group1.
  split; apply/eqP; apply/setP; apply/subset_eqP; apply/andP; split=>//.
    by rewrite -Hprod -{1}(smulg1 H1); apply:smulgs.
  by rewrite -Hprod -{1}(smul1g H2); apply:smulsg.
move=> [HH1 HH2]; move/eqP: HH1=>->; move/eqP: HH2=>->.
by rewrite smulg_set1 mulg1.
Qed.

Lemma dirprod_normal_isom : forall (H1 H2 G:group _),
  reflect
  ( (H1 <| G  /\ H2 <| G) /\
  G = H1 :*: H2 :> set _ /\ disjointg H1 H2)
  (morphic (prod_dir H1 H2) mgmulg && isom mgmulg (prod_dir H1 H2) G).
Proof.
move=> H1 H2 G; apply: (iffP (dirprod_isom H1 H2 G));
move=> [Hcom [Hprod Htriv]]; split.
- split; apply/subsetP; 
  rewrite Hprod /= -(eqP (com_gmulg_smulg Hcom))=> x;
  move/smulgP; case=> [x1 x2 Hx1 Hx2 ->]; rewrite setE sconjgM.
    rewrite (@sconjg_com _ _ x2); first by apply/subsetP=> y; 
    rewrite /sconjg setE groupJr ?groupV.
    move=> y; rewrite /sconjg setE groupJr ?groupV // => Hy.
    by apply/eqP; move/comP: Hcom; move/(_ _ _ Hy Hx2).
  rewrite (@sconjg_com _ _ x1); 
  last by move=> y Hy; apply/eqP; move/comP: Hcom; move/(_ _ _ Hx1 Hy).
  by apply/subsetP=> y; rewrite /sconjg setE groupJr ?groupV.
- split; last by trivial.
  rewrite Hprod; move: (com_smulgC Hcom)=>/=.
  by move/eqP; move/smulC_gmul.
- move: Hcom => [Hnorm1 Hnorm2].
  case e: (H1 :*: H2 == H2 :*: H1).
    apply/comP=> h1 h2 Hh1 Hh2.
    have inH1: h1 * h2 * (h1^-1) * (h2^-1) \in H1.
      rewrite -!(mulgA h1); apply: groupM; first by trivial.
      move/normalP: Hnorm1; move/(_ (h2^-1)); rewrite Hprod /=.
      have Hp: ((h2^-1) \in H1:*:H2).
        apply/smulgP; apply: (MemProdg (group1 H1) (groupVr Hh2)).
        by rewrite mul1g.
      move/(_ Hp)=><-.
      by rewrite setE /conjg !invgK 2!mulgA mulVg mul1g -mulgA mulVg mulg1 groupV.
    have inH2: h1 * h2 * (h1^-1) * (h2^-1) \in H2.
      apply: groupM; last by apply: groupVr.
      move/normalP: Hnorm2; move/(_ (h1^-1)); rewrite Hprod /=.
      have Hp: ((h1^-1) \in H1:*:H2).
        apply/smulgP; apply: (MemProdg (groupVr Hh1) (group1 H2)).
        by rewrite mulg1.
      move/(_ Hp)=><-.
      by rewrite setE /conjg !invgK 2!mulgA mulVg mul1g -mulgA mulVg mulg1.
    move: inH2; move/(conj inH1); move/setIP; move/trivgP: Htriv =>/= ->.
    move/set1P; rewrite -(mulgA (h1 * h2)) -(invg_mul h1 h2) -(mulgV (h1 * h2)).
    by move/(mulg_injl (h1 * h2)); move/invg_inj=>->.
  have Heq: H1:*:H2 = [set 1].
    by move: (group_gmul Hprod)=>->; move:e; unlock gmulg gmulg_def smulg=>->.
  move/eqP: Heq; rewrite smulg_1set; move/andP=> [HH1 HH2]; apply/comP.
  move=> x y; rewrite (eqP HH1) (eqP HH2); move/set1P=>->; move/set1P=>->.
  by rewrite mulg1.
- split; last by trivial.
  by apply:set_of_group_inj; move: (group_gmul Hprod)=>/= <-.
Qed.


End DirProd.