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
Require Import finset.
Require Import groups.
Require Import normal.
Require Import div.
Require Import automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ExternalDirProd.

Variables gT1 gT2 : finGroupType.

Definition extprod_mulg (x y : gT1 * gT2) := (x.1 * y.1, x.2 * y.2).
Definition extprod_invg (x : gT1 * gT2) := (x.1^-1, x.2^-1).

Lemma extprod_mul1g : left_unit (1, 1) extprod_mulg.
Proof. case=> x1 x2; congr (_, _); exact: mul1g. Qed.

Lemma extprod_mulVg : left_inverse (1, 1) extprod_invg extprod_mulg.
Proof. by move=> x; congr (_, _); exact: mulVg. Qed.

Lemma extprod_mulgA : associative extprod_mulg.
Proof. by move=> x y z; congr (_, _); exact: mulgA. Qed.

Canonical Structure extprod_baseFinGroupType := Eval hnf in
  [baseFinGroupType of gT1 * gT2
     by extprod_mulgA, extprod_mul1g & extprod_mulVg].

Canonical Structure prod_group := FinGroupType extprod_mulVg.

Lemma group_setX : forall (H1 : {group gT1}) (H2 : {group gT2}),
  group_set (setX H1 H2).
Proof.
move=> H1 H2; apply/group_setP; split; first by rewrite inE !group1.
case=> [x1 x2] [y1 y2]; rewrite !inE; case/andP=> Hx1 Hx2; case/andP=> Hy1 Hy2.
by rewrite /= !groupM.
Qed.

Canonical Structure setX_group H1 H2 := Group (group_setX H1 H2).

End ExternalDirProd.

Section InternalDirProd.

Variables gT : finGroupType.
Implicit Types G H : {group gT}.

Definition mulg_pair := prod_curry (@mulg gT).

Lemma mulg_setX : forall H1 H2, mulg_pair @: (setX H1 H2) = H1 * H2.
Proof. by move=> H1 H2; rewrite -curry_imset2X. Qed.

Lemma dirprod_isom : forall H1 H2 G,
  reflect [/\ {in H1, central H2}, G = (H1 <*> H2)%G & trivg (H1 :&: H2)]
          (morphic (setX H1 H2) mulg_pair && isom mulg_pair (setX H1 H2) G).
Proof.
move=> H1 H2 G; set H := {2}(setX H1 H2); rewrite /isom mulg_setX.
apply: (iffP and3P) => [[pM] | [cH ->{G} trH]].
  move/eqP=> defG; move/(injmorphicP pM); rewrite /= -/H => injp.
  have cH: {in H1, central H2}.
    move=> x1 Hx1 /= x2 Hx2; have:= morphP pM (1, x2) (x1, 1).
    rewrite /= !inE !group1 andbT !mul1g !mulg1; exact.
  split=> //; first by apply: val_inj; rewrite /= central_mulgenE.
  apply/subsetP=> x; case/setIP=> H1x H2x; apply/set1P.
  have:= injp (x, 1) (1, x); rewrite !inE ?group1 andbT /= !gsimp. 
  by case/(_ H1x H2x (erefl x)).
have pM: morphic H mulg_pair.
  apply/morphP=> [[x1 x2] [y1 y2]]; rewrite !inE.
  case/andP=> _ Hx2; case/andP=> Hy1 _.
  by rewrite /= mulgA -(mulgA x1) (cH _ Hy1) ?mulgA.
split=> //=; first by rewrite central_mulgenE.
apply/subsetP=> u; case/setD1P=> nu1 Hu.
have npu1: mulg_pair u <> 1.
  apply/eqP; apply: contra nu1; case: u Hu => x1 x2 Hu /=.
  rewrite -eq_invg_mul; move/eqP=> def_x2.
  rewrite -{x2}def_x2 inE groupV -in_setI /= in Hu *.
  by move/(subsetP trH): Hu; move/set1P->; rewrite invg1 eqxx.
have Du: u \in dom mulg_pair by apply/setUP; right; rewrite inE; exact/eqP.
rewrite inE Du andbT; rewrite /H in pM; apply/(kermorphicP pM) => //.
by rewrite inE Hu Du.
Qed.

Lemma smulg_1set : forall H1 H2, 
  (H1 * H2 == 1) = (H1 == 1 :> set _) && (H2 == 1 :> set _).
Proof.
move=> H1 H2; rewrite !eqset_sub (subset_trans _ (mulG_subr _ _)) ?sub1G //=.
by rewrite !andbT -gen_subG genM_mulgen gen_subG subUset.
Qed.

Lemma dirprod_normal_isom : forall H1 H2 G,
  reflect [/\ H1 <| G, H2 <| G, G = H1 * H2 :> set _ & trivg (H1 :&: H2)]
          (morphic (setX H1 H2) mulg_pair && isom mulg_pair (setX H1 H2) G).
Proof.
move=> H1 H2 G.
apply: (iffP (dirprod_isom H1 H2 G)) => [[cH -> trH] | [nH1 nH2 defG trH]].
  rewrite /normal_subset /= {-2 4}central_mulgenE // mulG_subl // mulG_subr //.
  rewrite //= !gen_subG !subUset normG /= andbC normG /=.
  split=> //; apply/normalP; apply: in_central_normal => //.
  exact: central_sym.
suff: {in H1, central H2}.
  by split=> //; apply: val_inj; rewrite /= central_mulgenE.
(* This ia a classic use of commutators *)
move=> x1 Hx1 /= x2 Hx2; apply/commgP; rewrite -in_set1.
apply: (subsetP trH); rewrite inE {1}commgEl commgEr.
rewrite groupMl (groupMr _ Hx2, groupV) //.
case/normalsubP: nH1 => sH1 nH1; case/normalsubP: nH2 => sH2 nH2.
rewrite -(nH1 _ (subsetP sH2 _ Hx2)) -(nH2 _ (subsetP sH1 _ Hx1)).
by rewrite !memJ_conjg Hx1 groupV.
Qed.

End InternalDirProd.
