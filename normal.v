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
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import finfun.
Require Import finset.
Require Import groups.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Simple.

Variables (gT : finGroupType) (H : {set gT}).

Definition simple := forallb K : {group gT}, (K <| H) ==> pred2 1 H K.

Theorem simpleP:
  reflect
   (forall K : {group gT}, K <| H -> K = 1 :> {set gT} \/ K = H :> {set gT})
   simple.
Proof.
(* have F1: forall z, pred1 1 z = set1 (1: gT) z by move => z; rewrite inE. *)
apply: (iffP forallP) => /= [Hf K Hk | Hf K].
  by have:= Hf K; rewrite Hk; case/orP => HH; [left|right]; exact/eqP.
by apply/implyP; case/Hf=> ->; rewrite eqxx ?orbT.
Qed.

End Simple.

Section MorphismStructure.

Variables aT rT : finGroupType.

Structure morphism (A : {set aT}) : Type := Morphism {
  mfun :> aT -> FinGroup.sort rT;
  morphM : {in A &, {morph mfun : x y / x * y}}
}.

Definition morphism_for A of phant rT := morphism A.

Variables (A B : {set aT}) (C : {set rT}) (x : aT) (y : rT) (f : aT -> rT).

CoInductive morphim_spec : Prop := MorphimSpec z & z \in A & z \in B & y = f z.

Lemma morphimP : reflect morphim_spec (y \in f @: (A :&: B)).
Proof.
apply: (iffP imsetP) => [] [z]; first by case/setIP; exists z.
by exists z; first apply/setIP.
Qed.

Lemma morphpreP : reflect (x \in A /\ f x \in C) (x \in A :&: f @^-1: C).
Proof. rewrite !inE; exact: andP. Qed.

End MorphismStructure.

Notation "{ 'morphism' A >-> T }" := (morphism_for A (Phant T))
  (at level 0, format "{ 'morphism'  A  >->  T }") : group_scope.

Notation "[ 'morphism' 'of' h ]" :=
  (match [is h : _ -> _ <: morphism _ _] as s
   return {type of @Morphism _ _ _ for s} -> _ with
   | Morphism _ hM => fun k => k hM
   end (@Morphism _ _ _ h)) (at level 0, only parsing) : form_scope.

Implicit Arguments morphimP [aT rT A B f y].
Implicit Arguments morphpreP [aT rT A C f x].
Prenex Implicits morphimP morphpreP.

Section MorphismOps1.

Variables (aT rT : finGroupType) (A : {set aT}) (f : {morphism A >-> rT}).

Notation morphantom := (phantom (aT -> rT)).
Definition MorPhantom := @Phantom (aT -> rT).

Definition dom of morphantom f := A.

Definition morphim of morphantom f := fun B => f @: (A :&: B).

Definition morphpre of morphantom f := fun C : {set rT} => A :&: f @^-1: C.

Definition ker mph := morphpre mph 1.

End MorphismOps1.

Notation "''dom' f" := (dom (MorPhantom f))
  (at level 10, f at level 8, format "''dom'  f") : group_scope.

Notation "''ker' f" := (ker (MorPhantom f))
  (at level 10, f at level 8, format "''ker'  f") : group_scope.

Notation "''ker_' H f" := (H :&: 'ker f)
  (at level 10, H at level 2, f at level 8, format "''ker_' H  f")
  : group_scope.

Notation "f @* H" := (morphim (MorPhantom f) H)
  (at level 24, format "f  @*  H") : group_scope.

Notation "f @*^-1 L" := (morphpre (MorPhantom f) L)
  (at level 24, format "f  @*^-1  L") : group_scope.

Notation "''injm' f" := (trivg ('ker f))
  (at level 10, f at level 8, format "''injm'  f") : group_scope.

Section MorphismTheory.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types G H K : {group aT}.
Implicit Types C D : {set rT}.
Implicit Types L M : {group rT}.

Variables (G : {group aT}) (f : {morphism G >-> rT}).

Lemma morph1 : f 1 = 1.
Proof. by apply: (mulg_injl (f 1)); rewrite -morphM ?mulg1. Qed.

Lemma morphV : {in G, {morph f : x / x^-1}}.
Proof.
move=> x Gx; apply: (mulg_injl (f x)).
by rewrite -morphM ?groupV // !mulgV morph1.
Qed.

Lemma morphJ : {in G &, {morph f : x y / x ^ y}}.
Proof. by move=> * /=; rewrite !morphM ?morphV // ?groupM ?groupV. Qed.

Lemma morphX : forall n, {in G, {morph f : x / x ^+ n}}.
Proof.
by elim=> [|n IHn] x Dx; rewrite ?morph1 // !expgS morphM ?(groupX, IHn).
Qed.

Lemma morphR : {in G &, {morph f : x y / [~ x, y]}}.
Proof. by move=> * /=; rewrite morphM ?(groupV, groupJ) // morphJ ?morphV. Qed.

Lemma morphimE : forall A, f @* A = f @: (G :&: A). Proof. by []. Qed.
Lemma morphpreE : forall C, f @*^-1 C = G :&: f @^-1: C. Proof. by []. Qed.
Lemma kerE : 'ker f = f @*^-1 1. Proof. by []. Qed.

Lemma morphimEsub : forall A, A \subset G -> f @* A = f @: A.
Proof. by move=> A sAG; rewrite /morphim (setIidPr sAG). Qed.

Lemma morphimEdom : f @* G = f @: G.
Proof. exact: morphimEsub. Qed.

Lemma morphimIdom : forall A, f @* (G :&: A) = f @* A.
Proof. by move=> A; rewrite /morphim setIA setIid. Qed.

Lemma morphpreIdom : forall C, G :&: f @*^-1 C = f @*^-1 C.
Proof. by move=> A; rewrite /morphim setIA setIid. Qed.

Lemma morphpreIim : forall C, f @*^-1 (f @* G :&: C) = f @*^-1 C.
Proof.
move=> C; apply/setP=> x; rewrite morphimEdom !inE.
by case Gx: (x \in G); rewrite // mem_imset.
Qed.

Lemma morphimIim : forall A, f @* G :&: f @* A = f @* A.
Proof. by move=> A; apply/setIidPr; rewrite imsetS // setIid subsetIl. Qed.

Lemma morphimS : forall A B, A \subset B -> f @* A \subset f @* B.
Proof. by move=> A B sAB; rewrite imsetS ?setIS. Qed.

Lemma morphpreS : forall C D, C \subset D -> f @*^-1 C \subset f @*^-1 D.
Proof. by move=> C D sCD; rewrite setIS ?preimsetS. Qed.

Lemma morphim0 : f @* set0 = set0.
Proof.
by apply/setP=> y; rewrite inE; apply/morphimP=> [[x]]; rewrite inE.
Qed.

Lemma morphim_set1 : forall x, x \in G -> f @* [set x] = [set f x].
Proof.
move=> x; rewrite /morphim -sub1set; move/setIidPr->; exact: imset_set1.
Qed.

Lemma morphim1 : f @* 1 = 1.
Proof. by rewrite morphim_set1 ?morph1. Qed.

Lemma morphimV : forall A, f @* A^-1 = (f @* A)^-1.
Proof.
have subV: forall A, f @* A^-1 \subset (f @* A)^-1.
  move=> A; apply/subsetP=> y; case/morphimP=> x Gx; rewrite !inE => Ax' ->{y}.
  by rewrite -morphV // mem_imset // inE groupV Gx.
by move=> A; apply/eqP; rewrite eqset_sub subV -invSg invgK -{1}(invgK A) subV.
Qed.

Lemma morphpreV : forall C, f @*^-1 C^-1 = (f @*^-1 C)^-1.
Proof.
move=> C; apply/setP=> x; rewrite !inE groupV; case Gx: (x \in G) => //=.
by rewrite morphV.
Qed.

Lemma morphimMl : forall A B, A \subset G -> f @* (A * B) = f @* A * f @* B.
Proof.
move=> A B sAG; rewrite /morphim setIC -group_modl // (setIidPr sAG).
apply/setP=> fxy; apply/idP/idP.
  case/imsetP=> xy; case/imset2P=> x y Ax; case/setIP=> Gy By -> -> {fxy xy}.
  by rewrite morphM // (subsetP sAG, mem_imset2) // mem_imset // inE By.
case/imset2P=> fx fy; case/imsetP=> x Ax -> {fx}.
case/morphimP=> y Gy By -> {fy} ->{fxy}.
by rewrite -morphM // (subsetP sAG, mem_imset) // mem_mulg // inE By.
Qed.

Lemma morphimMr : forall A B, B \subset G -> f @* (A * B) = f @* A * f @* B.
Proof.
move=> A B sBG; apply: invg_inj.
by rewrite invMg -!morphimV invMg morphimMl // -invGid invSg.
Qed.

Lemma morphpreMl : forall C D,
  C \subset f @* G -> f @*^-1 (C * D) = f @*^-1 C * f @*^-1 D.
Proof.
move=> C D sCfG; apply/setP=> x; rewrite !inE.
apply/andP/imset2P=> [[Gx] | [y z]]; last first.
  rewrite !inE; case/andP=> Gy Cfy; case/andP=> Gz Cfz ->.
  by rewrite ?(groupM, morphM, mem_imset2).
case/imset2P=> fy fz Cfy Cfz def_fx.
case/morphimP: (subsetP sCfG fy Cfy) => y Gy _ def_fy.
exists y (y^-1 * x); last by rewrite mulKVg.
  by rewrite !inE Gy -def_fy.
by rewrite !inE groupM ?(morphM, morphV, groupV) // def_fx -def_fy mulKg.
Qed.

Lemma morphimJ : forall A x, x \in G -> f @* (A :^ x) = f @* A :^ f x.
Proof.
move=> A x Gx; rewrite !conjsgE morphimMl ?(morphimMr, sub1set, groupV) //.
by rewrite !(morphim_set1, groupV, morphV).
Qed.

Lemma morphpreJ : forall C x, x \in G -> f @*^-1 (C :^ f x) = f @*^-1 C :^ x.
Proof.
move=> C x Gx; apply/setP=> y; rewrite conjIg !inE conjGid // !mem_conjg inE.
by case Gy: (y \in G); rewrite // morphJ ?(morphV, groupV).
Qed.

Lemma morphimU : forall A B, f @* (A :|: B) = f @* A :|: f @* B.
Proof. by move=> A B; rewrite -imsetU -setIUr. Qed.

Lemma morphimI : forall A B, f @* (A :&: B) \subset f @* A :&: f @* B.
Proof. by move=> A B; rewrite subsetI // ?morphimS ?(subsetIl, subsetIr). Qed.

Lemma morphpre0 : f @*^-1 set0 = set0.
Proof. by apply/setP=> x; rewrite !inE andbF. Qed.

Lemma morphpreU : forall C D, f @*^-1 (C :|: D) = f @*^-1 C :|: f @*^-1 D.
Proof. by move=> C D; rewrite -setIUr -preimsetU. Qed.

Lemma morphpreI : forall C D, f @*^-1 (C :&: D) = f @*^-1 C :&: f @*^-1 D.
Proof. by move=> C D; rewrite -setIIr -preimsetI. Qed.

Lemma morphpreD : forall C D, f @*^-1 (C :\: D) = f @*^-1 C :\: f @*^-1 D.
Proof. by move=> C D; apply/setP=> x; rewrite !inE; case: (x \in G). Qed.

Lemma dom_ker : {subset 'ker f <= G}.
Proof. apply/subsetP; exact: subsetIl. Qed.

Lemma mker : forall x, x \in 'ker f -> f x = 1.
Proof. by move=> x; case/setIP=> _; rewrite inE; move/set1P. Qed.

Lemma mkerl : forall x y, x \in 'ker f -> y \in G -> f (x * y) = f y.
Proof. by move=> x y Kx Gy; rewrite morphM // ?(dom_ker, mker Kx, mul1g). Qed.

Lemma mkerr : forall x y, x \in G -> y \in 'ker f -> f (x * y) = f x.
Proof. by move=> x y Gx Ky; rewrite morphM // ?(dom_ker, mker Ky, mulg1). Qed.

Lemma rcoset_kerP : forall x y,
  x \in G -> y \in G -> reflect (f x = f y) (x \in 'ker f :* y).
Proof.
move=> x y Gx Gy; rewrite mem_rcoset !inE groupM ?morphM ?groupV //=.
rewrite morphV // -eq_mulgV1; exact: eqP.
Qed.

Lemma ker_rcoset : forall x y,
  x \in G -> y \in G -> f x = f y -> exists2 z, z \in 'ker f & x = z * y.
Proof. move=> x y Gx Gy eqfxy; apply/rcosetP; exact/rcoset_kerP. Qed.

Lemma norm_ker : G \subset 'N('ker f).
Proof.
apply/subsetP=> x Gx; rewrite inE; apply/subsetP=> yx.
case/imsetP=> y Ky -> {yx}.
by rewrite !inE groupJ ?morphJ // ?dom_ker //= mker ?conj1g.
Qed.

Lemma normal_ker : 'ker f <| G.
Proof. by rewrite /(_ <| G) subsetIl norm_ker. Qed.

Lemma morphimGI : forall H A,
  'ker f \subset H -> f @* (H :&: A) = f @* H :&: f @* A.
Proof.
move=> H A sKH; apply/eqP; rewrite eqset_sub morphimI setIC.
apply/subsetP=> y; case/setIP; case/morphimP=> x Gx Ax ->{y}.
case/morphimP=> z Gz Hz; case/ker_rcoset=> {Gz}// y Ky def_x.
have{z Hz y Ky def_x} Hx: x \in H by rewrite def_x groupMl // (subsetP sKH).
by rewrite mem_imset ?inE // Gx Hx Ax.
Qed.

Lemma morphimIG : forall (A : {set aT}) (H : {group aT}),
  'ker f \subset H -> f @* (A :&: H) = f @* A :&: f @* H.
Proof. by move=> A H sKH; rewrite setIC morphimGI // setIC. Qed.

Lemma morphimD : forall A B, f @* A :\: f @* B \subset f @* (A :\: B).
Proof.
move=> A B; rewrite subDset -morphimU morphimS //.
by rewrite setDE setUIr setUCr setIT subsetUr.
Qed.

Lemma morphimDG : forall A H,
  'ker f \subset H -> f @* (A :\: H) = f @* A :\: f @* H.
Proof.
move=> A H sKH; apply/eqP; rewrite eqset_sub morphimD andbT !setDE subsetI.
rewrite morphimS ?subsetIl // -[~: f @* H]setU0 -subDset setDE setCK.
by rewrite -morphimIG //= setIAC -setIA setICr setI0 morphim0.
Qed.

Lemma morphpre_groupset : forall M, group_set (f @*^-1 M).
Proof.
move=> M; apply/group_setP; split=> [|x y]; rewrite !inE ?(morph1, group1) //.
by case/andP=> Gx Mfx; case/andP=> Gy Mfy; rewrite morphM ?groupM.
Qed.

Lemma morphim_groupset : forall H, group_set (f @* H).
Proof.
move=> H; apply/group_setP; split=> [|fx fy].
  by rewrite -morph1 mem_imset ?group1.
case/morphimP=> x Gx Hx ->; case/morphimP=> y Gy Hy ->.
by rewrite -morphM ?mem_imset ?inE ?groupM.
Qed.

Canonical Structure morphpre_group fPh M :=
  @Group _ (morphpre fPh M) (morphpre_groupset M).

Canonical Structure morphim_group fPh H :=
  @Group _ (morphim fPh H) (morphim_groupset H).

Canonical Structure ker_group fPh := Eval hnf in [group of ker fPh].

Lemma morph_dom_groupset : group_set (f @: G).
Proof. by rewrite -morphimEdom groupP. Qed.

Canonical Structure morph_dom_group := Group morph_dom_groupset.

Lemma morphpreMr : forall C D,
  D \subset f @* G -> f @*^-1 (C * D) = f @*^-1 C * f @*^-1 D.
Proof.
move=> C D sDfG; apply: invg_inj.
by rewrite invMg -!morphpreV invMg morphpreMl // -invSg invgK invGid.
Qed.

Lemma morphimK : forall A, A \subset G -> f @*^-1 (f @* A) = 'ker f * A.
Proof.
move=> A sAG; apply/setP=> x; rewrite !inE; apply/idP/idP.
  case/andP=> Gx; case/morphimP=> y Gy Ay eqxy.
  rewrite -(mulgKV y x) mem_mulg // !inE !(groupM, morphM, groupV) //.
  by rewrite morphV //= eqxy mulgV.
case/imset2P=> z y Kz Ay ->{x}.
have [Gy Gz]: y \in G /\ z \in G by rewrite (subsetP sAG) // dom_ker.
by rewrite groupM // morphM // mker // mul1g mem_imset // inE Gy.
Qed.

Lemma morphimGK : forall H,
 'ker f \subset H -> H \subset G -> f @*^-1 (f @* H) = H.
Proof. by move=> H sKH sHG; rewrite morphimK // mulSGid. Qed.

Lemma morphpre_set1 : forall x, x \in G -> f @*^-1 [set f x] = 'ker f :* x.
Proof. by move=> x Gx; rewrite -morphim_set1 // morphimK ?sub1set. Qed.

Lemma morphpreK : forall C, C \subset f @* G -> f @* (f @*^-1 C) = C.
Proof.
move=> C sCfG; apply/setP=> y; apply/morphimP/idP=> [[x _] | Cy].
  by rewrite !inE; case/andP=> _ Cfx ->.
case/morphimP: (subsetP sCfG y Cy) => x Gx _ defy.
by exists x; rewrite // !inE Gx -defy.
Qed.

Lemma morphim_ker : f @* 'ker f = 1.
Proof. by rewrite morphpreK ?sub1G. Qed.

Lemma normal_ker_pre : forall M, 'ker f <| f @*^-1 M.
Proof.
by move=> H; rewrite /(_ <| _) morphpreS ?sub1G // subIset // norm_ker.
Qed.

Lemma morphpreSK : forall C D,
  C \subset f @* G -> (f @*^-1 C \subset f @*^-1 D) = (C \subset D).
Proof.
move=> C D sCfG; apply/idP/idP=> [sf'CD|]; last exact: morphpreS.
suffices: C \subset f @* G :&: D by rewrite subsetI sCfG.
rewrite -(morphpreK sCfG) -[_ :&: D]morphpreK (morphimS, subsetIl) //.
by rewrite morphpreI morphimGK ?subsetIl // setIA setIid.
Qed.

Lemma sub_morphim_pre : forall A C,
  A \subset G -> (f @* A \subset C) = (A \subset f @*^-1 C).
Proof.
move=> A C sAG; rewrite -morphpreSK (morphimS, morphimK) //.
apply/idP/idP; first by apply: subset_trans; exact: mulG_subr.
by move/(mulgS ('ker f)); rewrite -morphpreMl ?(sub1G, mul1g). 
Qed.

Lemma sub_morphpre_im : forall C H,
    'ker f \subset H -> H \subset G -> C \subset f @* G ->
  (f @*^-1 C \subset H) = (C \subset f @* H).
Proof. by symmetry; rewrite -morphpreSK ?morphimGK. Qed.

Lemma ker_trivg_morphim : forall A,
  (A \subset 'ker f) = (A \subset G) && trivg (f @* A).
Proof.
move=> A; case sAG: (A \subset G); first by rewrite -sub_morphim_pre.
by rewrite subsetI sAG.
Qed.

Lemma morphimSK : forall A B,
  A \subset G -> (f @* A \subset f @* B) = (A \subset 'ker f * B).
Proof.
move=> A B sAG; transitivity (A \subset 'ker f * (G :&: B)).
  by rewrite -morphimK ?subsetIl // -sub_morphim_pre // /morphim setIA setIid.
by rewrite setIC group_modl (subsetIl, subsetI) // andbC sAG.
Qed.

Lemma morphimSGK : forall A H,
  A \subset G -> 'ker f \subset H -> (f @* A \subset f @* H) = (A \subset H).
Proof. by move=> H K sHG skfK; rewrite morphimSK // mulSGid. Qed.

Lemma morphpre_inj :
  {in [pred C : {set _} | C \subset f @* G] &, injective (fun C => f @*^-1 C)}.
Proof. exact: in_can_inj morphpreK. Qed.

Lemma morphim_inj :
  {in [pred H : {group _} | ('ker f \subset H) && (H \subset G)] &,
   injective (fun H => f @* H)}.
Proof.
move=> H K; case/andP=> skH sHG; case/andP=> skK sKG eqfHK.
by apply: val_inj; rewrite /= -(morphimGK skH sHG) eqfHK morphimGK.
Qed.

Lemma morphim_gen : forall A, A \subset G -> f @* <<A>> = <<f @* A>>.
Proof.
move=> A sAG; apply/eqP.
rewrite eqset_sub andbC gen_subG morphimS; last exact: sub_geng.
by rewrite sub_morphim_pre gen_subG // -sub_morphim_pre // sub_geng.
Qed.

Lemma morphpre_gen : forall C,
  1 \in C -> C \subset f @* G -> f @*^-1 <<C>> = <<f @*^-1 C>>.
Proof.
move=> C C1 sCG; apply/eqP.
rewrite eqset_sub andbC gen_subG morphpreS; last exact: sub_geng.
rewrite -{1}(morphpreK sCG) -morphim_gen ?subsetIl // morphimGK //=.
  by rewrite (subset_trans _ (sub_geng _)) // setIS // preimsetS ?sub1set.
by rewrite gen_subG subsetIl.
Qed.

Lemma morphimR : forall A B,
  A \subset G -> B \subset G -> f @* [~: A, B] = [~: f @* A, f @* B].
Proof.
move=> A B; move/subsetP=> sAG; move/subsetP=> sBG.
rewrite morphim_gen; last first; last congr <<_>>.
  by apply/subsetP=> z; case/imset2P=> x y Ax By ->; rewrite groupR; auto.
apply/setP=> fz; apply/morphimP/imset2P=> [[z _] | [fx fy]].
  case/imset2P=> x y Ax By -> -> {z fz}.
  have Gx := sAG x Ax; have Gy := sBG y By.
  by exists (f x) (f y); rewrite ?(mem_imset, morphR) // ?(inE, Gx, Gy).
case/morphimP=> x Gx Ax ->{fx}; case/morphimP=> y Gy By ->{fy} -> {fz}.
by exists [~ x, y]; rewrite ?(inE, morphR, groupR, mem_imset2).
Qed.

Lemma injmP : reflect {in G &, injective f} ('injm f).
Proof.
apply: (iffP subsetP) => [injf x y Gx Gy | injf x Kx].
  by case/ker_rcoset=> // z; move/injf; move/set1P->; rewrite mul1g.
have Gx := dom_ker Kx; apply/set1P; apply: injf => //.
by apply/rcoset_kerP; rewrite // mulg1.
Qed.

Lemma ker_injm : 'injm f -> 'ker f = 1.
Proof. by case/trivgP. Qed.

Lemma morphim_norm : forall A, f @* 'N(A) \subset 'N(f @* A).
Proof.
move=> A; apply/subsetP=> fx; case/morphimP=> x Gx Nx -> {fx}.
by rewrite inE -morphimJ ?(normgP Nx).
Qed.

Lemma morphim_cent1 : forall x, x \in G -> f @* 'C[x] \subset 'C[f x].
Proof. by move=> x Gx; rewrite -(morphim_set1 Gx) morphim_norm. Qed.

Lemma morphim_cent : forall A, f @* 'C(A) \subset 'C(f @* A).
Proof.
move=> A; apply/bigcap_inP=> fx; case/morphimP=> x Gx Ax ->{fx}.
apply: subset_trans (morphim_cent1 Gx); apply: morphimS; exact: bigcap_inf.
Qed.

Lemma morphim_normal : forall A B,
  A \subset 'N(B) -> f @* A \subset 'N(f @* B).
Proof.
move=> A B nBA; apply: subset_trans (morphim_norm B); exact: morphimS.
Qed.

Lemma morphim_central : forall A B,
  A \subset 'C(B) -> f @* A \subset 'C(f @* B).
Proof.
move=> A B cBA; apply: subset_trans (morphim_cent B); exact: morphimS.
Qed.

Lemma morphim_centraliser : forall A x,
  x \in G -> A \subset 'C[x] -> f @* A \subset 'C[f x].
Proof.
move=> A x Gx cAx; apply: subset_trans (morphim_cent1 Gx); exact: morphimS.
Qed.

Lemma morphim_normalsub :  forall A B, A <| B -> f @* A <| f @* B.
Proof.
move=> A B; case/andP=> sAB nAB.
by rewrite /(_ <| _) morphimS // morphim_normal.
Qed.

Lemma morphpre_norm : forall C, f @*^-1 'N(C) \subset 'N(f @*^-1 C).
Proof.
move=> C; apply/subsetP=> x; rewrite !inE; case/andP=> Gx Nfx.
by rewrite -morphpreJ ?morphpreS.
Qed.

Lemma morphpre_cent1 : forall x, x \in G -> 'C_G[x] \subset f @*^-1 'C[f x].
Proof.
move=> x Gx; rewrite -sub_morphim_pre ?subsetIl //.
by apply: subset_trans (morphim_cent1 Gx); rewrite morphimS ?subsetIr.
Qed.

Lemma morphpre_cent : forall A, 'C_G(A) \subset f @*^-1 'C(f @* A).
Proof.
move=> C; rewrite -sub_morphim_pre ?subsetIl //.
rewrite morphimGI ?(subsetIl, subIset) // orbC.
by rewrite (subset_trans (morphim_cent _)).
Qed.

Lemma morphpre_normal : forall C D,
  C \subset 'N(D) -> f @*^-1 C \subset 'N(f @*^-1 D).
Proof.
move=> C D nDC; apply: subset_trans (morphpre_norm D); exact: morphpreS.
Qed.

Lemma morphpre_central : forall A C,
  C \subset f @* G -> f @*^-1 C \subset 'C(A) -> C \subset 'C(f @* A).
Proof. by move=> A C sCfG; move/morphim_central; rewrite morphpreK. Qed.

Lemma morphpre_centraliser : forall C x,
  x \in G ->  C \subset f @* G -> f @*^-1 C \subset 'C[x] -> C \subset 'C[f x].
Proof.
by move=> C x Gx sCfG; move/(morphim_centraliser Gx); rewrite morphpreK.
Qed.

Lemma morphpre_normalsub :  forall C D,
  C \subset f @* G -> D \subset f @* G -> (f @*^-1 C <| f @*^-1 D) = (C <| D).
Proof.
move=> C D sCfG sDfG; apply/idP/andP=> [|[sCD nDC]].
  by move/morphim_normalsub; rewrite !morphpreK //; case/andP.
by rewrite /(_ <| _) (subset_trans _ (morphpre_norm _)) morphpreS.
Qed.

End MorphismTheory.

Notation "''ker' f" := (ker_group (MorPhantom f)) : subgroup_scope.
Notation "''ker_' H f" := (H :&: 'ker f)%G : subgroup_scope.
Notation "f @* H" := (morphim_group (MorPhantom f) H) : subgroup_scope.
Notation "f @*^-1 H" := (morphpre_group (MorPhantom f) H) : subgroup_scope.
Notation "f @: G" := (morph_dom_group f G) : subgroup_scope.

Section IdentityMorphism.

Variable T : finGroupType.

Definition idm of {set T} := fun x : T => x : FinGroup.sort T.

Lemma idm_morphM : forall A : {set T}, {in A & , {morph idm A : x y / x * y}}.
Proof. by []. Qed.

Canonical Structure idm_morphism A := Morphism (@idm_morphM A).

Lemma injm_idm : forall G : {group T}, 'injm (idm G).
Proof. by move=> G; apply/injmP=> ?. Qed.

Lemma ker_idm : forall G : {group T}, 'ker (idm G) = 1.
Proof. by move=> G; apply/trivgP; exact: injm_idm. Qed.

Lemma morphim_idm : forall A B : {set T}, B \subset A -> idm A @* B = B.
Proof.
move=> A B; rewrite /morphim /= /idm; move/setIidPr->.
by apply/setP=> x; apply/imsetP/idP=> [[y By ->]|Bx]; last exists x.
Qed.

Lemma morphpre_idm : forall A B : {set T}, idm A @*^-1 B = A :&: B.
Proof. by move=> A B; apply/setP=> x; rewrite !inE. Qed.

End IdentityMorphism.

Prenex Implicits idm.

Module AfterMorph. End AfterMorph.

Section RestrictedMorphism.

Variables aT rT : finGroupType.
Variables A B : {set aT}.

Definition restrm of A \subset B := @id (aT -> FinGroup.sort rT).

Hypothesis sAB : A \subset B.
Variable f : {morphism B >-> rT}.
Notation fB := (restrm sAB (mfun f)).

Canonical Structure restrm_morphism :=
  @Morphism aT rT A fB (subin2 (subsetP sAB) (morphM f)).

Lemma morphim_restrm : forall C : {set aT}, fB @* C = f @* (A :&: C).
Proof. by move=> C; rewrite {2}/morphim setIA (setIidPr sAB). Qed.

Lemma morphpre_restrm : forall C : {set rT}, fB @*^-1 C = A :&: f @*^-1 C.
Proof. by move=> C; rewrite setIA (setIidPl sAB). Qed.

Lemma ker_restrm : 'ker (restrm sAB f) = 'ker_A f.
Proof. exact: morphpre_restrm. Qed.

Lemma injm_restrm : 'injm f -> 'injm (restrm sAB f).
Proof. by apply: subset_trans; rewrite ker_restrm subsetIr. Qed.

End RestrictedMorphism.

Prenex Implicits restrm.

Section TrivMorphism.

Variables aT rT : finGroupType.

Definition trivm of {set aT} & aT := 1 : FinGroup.sort rT.

Lemma trivm_morphM : forall A : {set aT},
  {in A & , {morph trivm A : x y / x * y}}.
Proof. by move=> A x y /=; rewrite mulg1. Qed.

Canonical Structure triv_morph A := Morphism (@trivm_morphM A).

Lemma morphim_trivm : forall (G H : {group aT}), trivm G @* H = 1.
Proof.
move=> G H; apply/setP=> /= y; rewrite inE.
apply/idP/eqP=> [|->]; first by case/morphimP.
by apply/morphimP; exists (1 : aT); rewrite /= ?group1.
Qed.

Lemma ker_trivm : forall G : {group aT}, 'ker (trivm G) = G.
Proof. by move=> G; apply/setIidPl; apply/subsetP=> x _; rewrite !inE /=. Qed.

End TrivMorphism.

Prenex Implicits trivm.

(* Canonical Structure of morphism for the composition of 2 morphisms. *)

Section MorphismComposition.

Variables gT hT rT : finGroupType.
Variables (G : {group gT}) (H : {group hT}).

Variable f : {morphism G >-> hT}.
Variable g : {morphism H >-> rT}.

Notation Local gof := (mfun g \o mfun f).

Lemma comp_morphM : {in f @*^-1 H &, {morph gof: x y / x * y}}.
Proof.
by move=> x y; rewrite /= !inE; do 2!case/andP=> ? ?; rewrite !morphM.
Qed.

Canonical Structure comp_morphism := Morphism comp_morphM.

Lemma ker_comp : 'ker gof = f @*^-1 'ker g.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma injm_comp : 'injm f -> 'injm g -> 'injm gof.
Proof. by move=> injf; rewrite ker_comp; case/trivgP=> ->. Qed.

Lemma morphim_comp : forall A : {set gT}, gof @* A = g @* (f @* A).
Proof.
move=> A; apply/setP=> z; apply/morphimP/morphimP=> [[x]|[y Hy fAy ->{z}]].
  rewrite !inE; case/andP=> Gx Hfx; exists (f x) => //.
  by apply/morphimP; exists x.
by case/morphimP: fAy Hy => x Gx Ax ->{y} Hfx; exists x; rewrite ?inE ?Gx.
Qed.

Lemma morphpre_comp : forall A : {set rT},
  gof @*^-1 A = f @*^-1 (g @*^-1 A).
Proof. by move=> A; apply/setP=> z; rewrite !inE andbA. Qed.

End MorphismComposition.

(* Canonical structure of morphism for the factor morphism *)

Section FactorMorphism.

Variables aT qT rT : finGroupType.

Variables G H : {group aT}.
Variable f : {morphism G >-> rT}.
Variable q : {morphism H >-> qT}.

Definition factm of G \subset H & 'ker q \subset 'ker f :=
  fun x => f (repr (q @*^-1 [set x])).

Hypothesis sGH : G \subset H.
Hypothesis sKqKf : 'ker q \subset 'ker f.

Notation ff := (factm sGH sKqKf).

Lemma factmE : forall x, x \in G -> ff (q x) = f x.
Proof.
rewrite /ff => x Gx; have Hx := subsetP sGH x Gx.
have: x \in q @*^-1 [set q x] by rewrite !inE Hx /=.
move/mem_repr; case/morphpreP; move: (repr _) => y Hy; move/set1P.
by case/ker_rcoset=> // z Kz ->; rewrite mkerl ?(subsetP sKqKf).
Qed.

Lemma factm_morphM : {in q @* G &, {morph ff : x y / x * y}}.
Proof.
move=> xq yq; case/morphimP=> x Hx Gx ->{xq}.
by case/morphimP=> y Hy Gy ->{yq}; rewrite -morphM ?factmE ?groupM // morphM.
Qed.

Canonical Structure factm_morphism := Morphism factm_morphM.

Lemma morphim_factm : forall A : {set aT}, ff @* (q @* A) = f @* A.
Proof.
move=> A; rewrite -morphim_comp /= {1}/morphim /= morphimGK //; last first.
  by rewrite (subset_trans sKqKf) ?subsetIl.
apply/setP=> y; apply/morphimP/morphimP;
  by case=> x Gx Ax ->{y}; exists x; rewrite //= factmE.
Qed.

Lemma morphpre_factm : forall C : {set rT}, ff @*^-1 C =  q @* (f @*^-1 C).
Proof.
move=> C; apply/setP=> y; rewrite !inE /=.
apply/andP/morphimP=> [[]|[x Hx]]; last first.
  by case/morphpreP=> Gx Cfx ->; rewrite factmE ?mem_imset ?inE ?Hx.
case/morphimP=> x Hx Gx ->; rewrite factmE //.
by exists x; rewrite // !inE Gx.
Qed.

Lemma ker_factm : 'ker ff = q @* 'ker f.
Proof. exact: morphpre_factm. Qed.

Lemma injm_factm : 'injm f -> 'injm ff.
Proof. by rewrite ker_factm; case/trivgP=> ->; rewrite morphim1. Qed.

Lemma injm_factmP : reflect ('ker f = 'ker q) ('injm ff).
Proof.
rewrite ker_factm -morphimIdom -[trivg _]andbT -sKqKf /trivg.
rewrite sub_morphim_pre ?subsetIl // setIA (setIidPr sGH) -eqset_sub.
exact: eqP.
Qed.

Lemma ker_factm_loc : forall K : {group aT}, 'ker_(q @* K) ff = q @* 'ker_K f.
Proof. by move=> K; rewrite ker_factm -morphimIG. Qed.

End FactorMorphism.

Prenex Implicits factm.

Section InverseMorphism.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types C D : {set rT}.
Variables (G : {group aT}) (f : {morphism G >-> rT}).
Hypothesis injf : 'injm f.

Lemma invm_subker : 'ker f \subset 'ker (idm G).
Proof. by rewrite ker_idm. Qed.

Definition invm := factm (subset_refl _) invm_subker.

Canonical Structure invm_morphism := Eval hnf in [morphism of invm].

Lemma invmE : {in G, cancel f invm}.
Proof. exact: factmE. Qed.

Lemma invmK : {in f @* G, cancel invm f}.
Proof. by move=> fx; case/morphimP=> x _ Gx ->; rewrite invmE. Qed.

Lemma morphpre_invm : forall A, invm @*^-1 A = f @* A.
Proof. by move=> A; rewrite morphpre_factm morphpre_idm morphimIdom. Qed.

Lemma morphim_invm : forall A, A \subset G -> invm @* (f @* A) = A.
Proof. by move=> A sAG; rewrite morphim_factm morphim_idm. Qed.

Lemma morphim_invmE : forall C, invm @* C = f @*^-1 C.
Proof.
move=> C; rewrite -morphpreIdom -(morphim_invm (subsetIl _ _)).
by rewrite morphimIdom -morphpreIim morphpreK (subsetIl, morphimIdom).
Qed.

Lemma injm_invm : 'injm invm.
Proof. by move/in_can_inj: invmK; move/injmP. Qed.

Lemma ker_invm : 'ker invm = 1.
Proof. by case/trivgP: injm_invm. Qed.

Lemma invm_dom : invm @* (f @* G) = G.
Proof. exact: morphim_invm. Qed.

End InverseMorphism.

Prenex Implicits invm.

(* Reflected (boolean) form of morphism and isomorphism properties *)

Section ReflectProp.

Variables aT rT : finGroupType.

Section Defs.

Variables (A : {set aT}) (B : {set rT}).

(* morphic is the morphM property of morphisms seen through morphicP *)
Definition morphic (f : aT -> rT) :=
  forallb u, (u \in [predX A & A]) ==> (f (u.1 * u.2) == f u.1 * f u.2).

Definition isom f := f @: A^# == B^#.

Definition misom f := morphic f && isom f.

Definition isog := existsb f : {ffun aT -> rT}, misom f.

Section MorphicProps.

Variable f : aT -> rT.

Lemma morphicP : reflect {in A &, {morph f : x y / x * y}} (morphic f).
Proof.
apply: (iffP forallP) => [fM x y Ax Ay | fM [x y] /=].
  by apply/eqP; have:= fM (x, y); rewrite inE /= Ax Ay.
by apply/implyP; case/andP=> Ax Ay; rewrite fM.
Qed.

Definition morphm of morphic f := f : aT -> FinGroup.sort rT.

Lemma morphmE : forall fM, morphm fM = f. Proof. by []. Qed.

Canonical Structure morphm_morphism fM :=
  @Morphism _ _ A (morphm fM) (morphicP fM).

End MorphicProps.

Lemma misomP : forall f, reflect {fM : morphic f & isom (morphm fM)} (misom f).
Proof. by move=> f; apply: (iffP andP) => [] [fM fiso] //; exists fM. Qed.

Lemma isom_isog : forall f : {morphism A >-> rT}, isom f -> isog.
Proof.
move=> f isof; apply/existsP; exists (ffun_of f); apply/andP; split.
  by apply/morphicP=> x y Ax Ay; rewrite !ffunE morphM.
by rewrite /isom (dfequal_imset (in1W (ffunE f))). 
Qed.

End Defs.

(* The real reflection properties only hold for true groups and morphisms. *)

Variables (G : group aT) (H : group rT).
Notation fMT := {morphism G >-> rT}.

Lemma isomP : forall f : fMT, reflect ('injm f /\ f @* G = H) (isom G H f).
Proof.
move=> f; apply: (iffP eqP) => [eqfGH | [injf <-]]; last first.
  rewrite !setD1E -morphimEsub ?subsetIl // !setC1E -!setDE.
  by rewrite morphimDG // morphim1.
split.
  apply/subsetP=> x; rewrite !inE /=; case/andP=> Gx fx1; apply/idPn=> nx1.
  by move/setP: eqfGH; move/(_ (f x)); rewrite mem_imset ?inE (nx1, fx1).
rewrite morphimEdom -{2}(setD1K (group1 G)) setU1E imsetU eqfGH.
by rewrite imset_set1 morph1 -setU1E setD1K.
Qed.

Lemma isom_card : forall f : fMT, isom G H f -> #|G| = #|H|.
Proof.
by move=> f; case/isomP; move/injmP=> injf <-; rewrite morphimEdom card_dimset.
Qed.

Lemma isogP : reflect (exists2 f : fMT, 'injm f & f @* G = H) (isog G H).
Proof.
apply: (iffP idP) => [| [f *]]; last by apply: isom_isog (f) _; exact/isomP.
by case/existsP=> f; case/misomP=> fM; case/isomP; exists (morphm_morphism fM).
Qed.

End ReflectProp.

Implicit Arguments morphicP [aT rT A f].
Implicit Arguments misomP [aT rT A B f].
Implicit Arguments isomP [aT rT G H f].
Implicit Arguments isogP [aT rT G H].
Prenex Implicits morphic morphicP morphm isom isog isomP misomP isogP.

Section Isomorphisms.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_refl : isog G G.
Proof.
by apply/isogP; exists [morphism of idm G]; rewrite /= ?injm_idm ?morphim_idm.
Qed.

Lemma isog_card : isog G H -> #|G| = #|H|.
Proof. case/isogP=> f injf <-; apply: isom_card (f) _; exact/isomP. Qed.

Lemma trivial_isog : trivg G -> trivg H -> isog G H.
Proof.
move/trivgP=> ->; move/trivgP=> ->; apply/isogP.
exists [morphism of @trivm gT hT 1]; rewrite /= ?morphim_trivm //.
rewrite ker_trivm; exact: subset_refl.
Qed.

Lemma isog_triv : isog G H -> trivg G = trivg H.
Proof. by move=> isoGH; rewrite !trivg_card isog_card. Qed.

Lemma isog_sym_imply : isog G H -> isog H G.
Proof.
case/isogP=> f injf <-; apply/isogP.
by exists [morphism of invm injf]; rewrite /= ?injm_invm // invm_dom.
Qed.

Lemma isog_trans : isog G H -> isog H K -> isog G K.
Proof.
case/isogP=> f injf <-; case/isogP=> g injg <-.
have defG: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
rewrite -morphim_comp -{1 8}defG.
by apply/isogP; exists [morphism of g \o f]; rewrite ?injm_comp.
Qed.

Lemma isog_simpl : isog G H -> simple G -> simple H.
Proof.
move/isog_sym_imply; case/isogP=> f injf <-.
move/simpleP=> simpH; apply/simpleP=> L nLH.
have: f @* L <| f @* H by rewrite morphim_normalsub.
case/andP: nLH => sLH _; rewrite -{-1}(morphim_invm injf sLH) {sLH}.
by case/simpH=> [] [->]; [left | right]; rewrite (morphim1, morphim_invm).
Qed.

End Isomorphisms.

Section IsoBoolEquiv.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_sym : isog G H = isog H G.
Proof. apply/idP/idP; exact: isog_sym_imply. Qed.

Lemma isog_transl : isog G H -> isog G K = isog H K.
Proof.
by move=> iso; apply/idP/idP; apply: isog_trans; rewrite // -isog_sym.
Qed.

Lemma isog_transr : isog G H -> isog K G = isog K H.
Proof.
by move=> iso; apply/idP/idP; move/isog_trans; apply; rewrite // -isog_sym.
Qed.

End IsoBoolEquiv.

(********************************************************************)
(*       Cosets are right cosets of elements in the normaliser      *)
(********************************************************************)

Section Cosets.

Variables (gT : finGroupType) (A : {set gT}).

(* We let cosets coerce to GroupSet.sort, so they inherit the   *)
(* group subset base group structure. Later we will define a    *)
(* proper group structure on cosets, which will then hide the   *)
(* inherited structure (once coset unifies with FinGroup.sort   *)
(* the coercion to GroupSet.sort will no longer be used). Note  *)
(* that for Hx Hy : coset H, Hx * Hy : {set gT} can be either   *)
(*           set_of_coset (mulg Hx Hy)                          *)
(*   or mulg (set_of_coset Hx) (set_of_coset Hy)                *)
(* However, since the two terms are actually convertible, we    *)
(* can live with this ambiguity.                                *)
(*   We take great care that neither the type coset H, nor its  *)
(* finGroupType structure, nor the coset_of H morphism depend   *)
(* the actual group structure of H; this is because the proof   *)
(* component of that structure can become quite involved (there *)
(* could be, for instance, several morphic images that depend   *)
(* in turn on side conditions), which would swamp the display.  *)
(* Further, all our equalities are stated at the set level, so  *)
(* rewriting would be extremely awkward.                        *)
(*   The trick we use is to interpret coset A, when A is any    *)
(* set, as the type of bilateral cosets of <<A>>, using the     *)
(* fact that this coincides with the cosets of A when A is a    *)
(* group. We restrict the domain of coset_of A to 'N(A), so     *)
(* that we get almost all the same conversion equalities as if  *)
(* we had forced A to be a group in the first place -- the only *)
(* exception is that 1 : coset H : set _ = <<H>> rather than H, *)
(* which hardly interferes as it's covered by the genGid lemma. *)

Notation H := <<A>>.
Definition coset_range := [pred B \in rcosets H 'N(H)].

Record coset : Type :=
  Coset { set_of_coset :> GroupSet.sort gT; _ : coset_range set_of_coset }.

Canonical Structure coset_subType := SubType set_of_coset coset_rect vrefl.
Canonical Structure coset_eqType := Eval hnf in [subEqType for set_of_coset].
Canonical Structure coset_finType := Eval hnf in [finType of coset by :>].
Canonical Structure coset_subFinType := Eval hnf in [subFinType of coset].

(* We build a new (canonical) structure of groupType for cosets.      *)
(* When A is a group, this is the largest possible quotient 'N(H) / H *)

Lemma coset_range_unit : coset_range H.
Proof. by apply/rcosetsP; exists (1 : gT); rewrite (group1, mulg1). Qed.
Definition coset_unit := Coset coset_range_unit.

Lemma coset_range_mul : forall B C : coset, coset_range (B * C).
Proof.
case=> B /=; case/rcosetsP=> x Nx ->{B} [C] /=; case/rcosetsP=> y Ny ->{C}.
by apply/rcosetsP; exists (x * y); rewrite (groupM, rcoset_mul).
Qed.
Definition coset_mul B C := Coset (coset_range_mul B C).

Lemma coset_range_inv : forall B : coset, coset_range B^-1.
Proof.
case=> B /=; case/rcosetsP=> x Nx ->{B}; rewrite norm_rlcoset // invg_lcoset.
by apply/rcosetsP; exists x^-1; rewrite ?groupV.
Qed.
Definition coset_inv B := Coset (coset_range_inv B).

Lemma coset_mulP : associative coset_mul.
Proof. by move=> B C D; apply: val_inj; rewrite /= mulgA. Qed.

Lemma coset_unitP : left_unit coset_unit coset_mul.
Proof.
case=> B coB; apply: val_inj => /=; case/rcosetsP: coB => x Hx ->{B}.
by rewrite mulgA mulGid.
Qed.

Lemma coset_invP : left_inverse coset_unit coset_inv coset_mul.
Proof.
case=> B coB; apply: val_inj => /=; case/rcosetsP: coB => x Hx ->{B}.
rewrite invg_rcoset -mulgA (mulgA H) mulGid.
by rewrite norm_rlcoset // -lcosetM mulVg mul1g.
Qed.

Canonical Structure coset_preGroupType :=
  [baseFinGroupType of coset by coset_mulP, coset_unitP & coset_invP].
Canonical Structure coset_groupType := FinGroupType coset_invP.

(* Projection of the initial group type over the cosets groupType  *)

Definition coset_of x : coset := insubd (1 : coset) (H :* x).

Lemma val_coset_of : forall x,
  val (coset_of x) = (if x \in 'N(H) then H :* x else H).
Proof. by move=> x; rewrite val_insubd /= mem_rcosets mulSGid ?normG. Qed.

Lemma coset_ofV : {morph coset_of : x / x^-1}.
Proof.
move=> x; apply: val_inj; rewrite /= !val_coset_of groupV /=.
by case: ifP => Nx; rewrite Nx ?invGid // -invg_lcoset norm_rlcoset.
Qed.

Lemma coset_of_morphM : {in 'N(A) &, {morph coset_of : x y / x * y}}.
Proof.
apply: (subin2 (subsetP (normg_gen A))) => x y Nx Ny; apply: val_inj.
by rewrite /= !val_coset_of Nx Ny groupM //= rcoset_mul.
Qed.

Canonical Structure coset_of_morphism := Morphism coset_of_morphM.

End Cosets.

Prenex Implicits coset coset_of.

Section Quotient.

Variable gT : finGroupType.

Implicit Types A B : {set gT}.
Implicit Types G H K : {group gT}.

Definition quotient A B : {set coset B} := coset_of B @* A.

Infix "/" := quotient : group_scope.

Lemma quotientE : forall A B, A / B = coset_of B @* A. Proof. by []. Qed.

Canonical Structure quotient_group G A := Eval hnf in [group of G / A].

Infix "/" := quotient_group : subgroup_scope.

(* From this point on, we work only with cosets of real groups. *)

Variable H : {group gT}.

Lemma set_of_coset_of : forall x,
  coset_of H x = (if x \in 'N(H) then H :* x else H) :> {set _}.
Proof. by move=> x; rewrite val_coset_of /= genGid. Qed.

Lemma coset_ofN : forall x, x \in 'N(H) -> coset_of H x = H :* x :> set _.
Proof. by move=> x; rewrite set_of_coset_of => ->. Qed.

Lemma coset_of_id : forall x, x \in H -> coset_of H x = 1.
Proof.
move=> x Hx; apply: val_inj => /=.
by rewrite coset_ofN ?(rcoset_id, genGid) // inE conjGid.
Qed.

Lemma coset_of_idr : forall x, x \in 'N(H) -> coset_of H x = 1 -> x \in H.
Proof.
move=> x Nx;  move/(congr1 val); rewrite /= genGid => <-.
by rewrite coset_ofN ?rcoset_refl.
Qed.

Lemma ker_coset : 'ker (coset_of H) = H.
Proof.
apply/setP=> x; rewrite inE; apply/andP/idP=> [[Nx] | Hx] /=.
  rewrite inE; move/set1P; exact: coset_of_idr.
by rewrite (subsetP (normG H)) // inE /= coset_of_id ?set11.
Qed.

Lemma coset_of_norm : forall G, coset_of H @: G = G / H.
Proof.
move=> G; apply/eqP; rewrite eqset_sub andbC imsetS ?subsetIr //=.
apply/subsetP=> xbar; case/imsetP=> x Gx -> {xbar}.
case Nx: (x \in 'N(H)); first by rewrite mem_imset 1?inE ?Nx.
by rewrite ((_ x =P 1) _) ?group1 // -val_eqE /= set_of_coset_of Nx genGid.
Qed.

Lemma norm_repr_coset : forall xbar : coset H, repr xbar \in 'N(H).
Proof.
case=> A /=; case/rcosetsP=> x; rewrite genGid => Nx ->{A}.
by case: repr_rcosetP => z Hz; rewrite groupMr // (subsetP (normG _)).
Qed.

Lemma coset_of_repr : forall xbar : coset H, coset_of H (repr xbar) = xbar.
Proof.
move=> xbar; apply: val_inj; rewrite /= set_of_coset_of norm_repr_coset.
case: xbar => A /=; case/rcosetsP=> x; rewrite genGid => Nx ->{A}.
exact: rcoset_repr.
Qed.

Lemma cosetP : forall xbar, {x | x \in 'N(H) & xbar = coset_of H x}.
Proof.
by move=> xbar; exists (repr xbar); rewrite ?coset_of_repr ?norm_repr_coset.
Qed.

Lemma morphpre_coset_set1 : forall xbar, coset_of H @*^-1 [set xbar] = xbar.
Proof.
move=> xbar; case: (cosetP xbar) => x Nx ->{xbar}; apply/setP=> y.
symmetry; rewrite inE !coset_ofN //; case Ny: (y \in 'N(H)).
  by rewrite !inE (sameP eqP (rcoset_kerP _ Ny Nx)) ker_coset.
apply/rcosetP=> [[z Hz def_y]]; case/idP: Ny.
by rewrite def_y groupMl // (subsetP (normG _)).
Qed. 

Lemma trivial_quotient : H / H = 1.
Proof. by rewrite -{3}ker_coset quotientE morphim_ker. Qed.
  
Lemma trivg_quotient : forall A,
  A \subset 'N(H) -> trivg (A / H) = (A \subset H).
Proof. by move=> A nHA; rewrite -{3}ker_coset ker_trivg_morphim nHA. Qed.

Lemma val_quotient : forall A, val @: (A / H) = rcosets H 'N_A(H).
Proof.
move=> A; apply/setP=> B; apply/imsetP/rcosetsP=> [[xb Axb]|[x ANx]] ->{B}.
  case/morphimP: Axb => x Nx Ax ->{xb}.
  by exists x; [rewrite inE Ax | rewrite /= coset_ofN].
case/setIP: ANx => Ax Nx.
by exists (coset_of H x); [apply/morphimP; exists x | rewrite /= coset_ofN].
Qed.

Lemma card_quotient : forall A, A \subset 'N(H) -> #|A / H| = indexg H A.
Proof.
by move=> A nHA; rewrite -(card_imset _ val_inj) val_quotient (setIidPl nHA).
Qed.

Lemma quotient_inj :
  {in [pred K : {group gT} | H <| K] &, injective (fun K => K / H)}.
Proof. by move=> G K nHG nHK; apply: morphim_inj; rewrite ker_coset. Qed.

Section InverseImage.

Variables (G : {group gT}) (Kbar : {group coset H}).

Hypothesis nHG : H <| G.

CoInductive inv_quotient_spec (P : pred {group gT}) : Prop :=
  InvQuotientSpec K of (Kbar = K / H)%G & H \subset K & P K.

Lemma inv_quotientS :
  Kbar \subset G / H -> inv_quotient_spec (fun K => K \subset G).
Proof.
case/andP: nHG => sHG nHG' sKbarG.
have sKdH: Kbar \subset 'N(H) / H by rewrite (subset_trans sKbarG) ?morphimS.
exists [group of coset_of H @*^-1 Kbar].
- by apply: val_inj; rewrite /= quotientE morphpreK.
- by rewrite -{1}ker_coset morphpreS ?sub1G.
by rewrite sub_morphpre_im ?ker_coset.
Qed.

Lemma inv_quotientN : Kbar <| G / H -> inv_quotient_spec (fun K => K <| G).
Proof.
case/andP: nHG => sHG nHG' nKbar; case: (andP nKbar) => sKbarG _.
case: (inv_quotientS sKbarG) => K defKbar sHK sKG.
have nHGbar: G / H \subset 'N(H) / H by rewrite morphimS; case/andP: nHG.
rewrite -(morphpre_normalsub (subset_trans sKbarG nHGbar) nHGbar) /= in nKbar.
exists K => //; rewrite defKbar !morphimGK ?ker_coset // in nKbar.
exact: subset_trans nHG'.
Qed.

End InverseImage.

Lemma quotient_mulg : forall A, A * H / H = A / H.
Proof.
move=> A; rewrite [_ /_]morphimMr ?normG //= -!quotientE.
by rewrite trivial_quotient mulg1.
Qed.

Lemma quotient_mulgr : forall A, H * A / H = A / H.
Proof.
move=> A; rewrite [_ /_]morphimMl ?normG //= -!quotientE.
by rewrite trivial_quotient mul1g.
Qed.

Lemma quotient_mulG : forall G, G \subset 'N(H) -> G <*> H / H = G / H.
Proof.
move=> G nHG; rewrite -genM_mulgen quotientE morphim_gen -?quotientE.
  by rewrite quotient_mulg genGid.
by rewrite -(mulSGid nHG) mulgS ?normG.
Qed.

End Quotient.

Notation "A / B" := (quotient A B) : group_scope.
Notation "A / H" := (quotient_group A H) : subgroup_scope.

Section QuotientMorphism.

Variable (gT : finGroupType) (G H : {group gT}) (f : {morphism G >-> gT}).

Hypotheses (nHG : H <| G) (nGf : f @* G = G) (nHf : f @* H = H).

Notation fH := (coset_of H \o f).

Lemma quotm_restr_proof : G \subset 'dom fH.
Proof. by rewrite -sub_morphim_pre // nGf; case/andP: nHG. Qed.

Notation fH_G := (restrm quotm_restr_proof fH).

Lemma quotm_fact_proof1 : G \subset 'N(H).
Proof. by case/andP: nHG. Qed.

Lemma quotm_fact_proof2 : 'ker (coset_of H) \subset 'ker fH_G.
Proof.
case/andP: nHG => sHG _; rewrite ker_restrm ker_comp ker_coset subsetI.
by rewrite -sub_morphim_pre sHG ?nHf /=.
Qed.

Definition quotm := factm quotm_fact_proof1 quotm_fact_proof2.
Canonical Structure quotm_morphism := Eval hnf in [morphism of quotm].

Lemma morphim_quotm : forall A : {set gT}, quotm @* (A / H) = f @* A / H.
Proof.
case/andP: nHG => sHG nHG' A.
by rewrite morphim_factm morphim_restrm morphim_comp morphimIdom.
Qed.

Lemma morphpre_quotm : forall A : {set gT},
  quotm @*^-1 (A / H) = f @*^-1 A / H.
Proof.
case/andP: nHG => sHG nHG' A; rewrite morphpre_factm morphpre_restrm.
rewrite morphpre_comp morphpreIdom quotientE -(morphimIdom _ A) /= -quotientE.
rewrite morphimK ?subsetIl // ker_coset morphpreMl ?nGf // -{3}nHf morphimK //.
rewrite -morphpreIim setIA -(morphpreIim _ A) !nGf (setIidPl nHG').
rewrite [_ * H]normC; last by apply: subset_trans nHG'; rewrite subsetIl.
by rewrite -mulgA quotient_mulgr -morphpreMl (mul1g, sub1G).
Qed.

Lemma ker_quotm : 'ker quotm = 'ker f / H.
Proof. by rewrite -morphpre_quotm /quotient morphim1. Qed.

Lemma injm_quotm : 'injm f -> 'injm quotm.
Proof. by move/trivgP=> /= kf1; rewrite ker_quotm kf1 quotientE morphim1. Qed.

End QuotientMorphism.

Section FirstIsomorphism.

Variables aT rT : finGroupType.
Implicit Types G H : {group aT}.

Lemma first_isom : forall G (f : {morphism G >-> rT}),
  isog (G / 'ker f) (f @* G).
Proof.
move=> G f; apply/isogP; have nkG := norm_ker f.
have skk: 'ker (coset_of ('ker f)) \subset 'ker f by rewrite ker_coset.
exists [morphism of factm nkG skk] => /=; last by rewrite morphim_factm.
by rewrite ker_factm -quotientE trivial_quotient.
Qed.

Lemma first_isom_loc : forall G H (f : {morphism G >-> rT}),
  H \subset G -> isog (H / 'ker_H f) (f @* H).
Proof.
move=> G H f sHG.
rewrite -{4}(setIid H) -(morphim_restrm sHG) -(ker_restrm sHG f).
exact: first_isom.
Qed.

End FirstIsomorphism.

Section SecondIsomorphism.

Variables (gT : finGroupType) (H K : {group gT}).

Hypothesis nKH : H \subset 'N(K).

Lemma second_isom : isog (H / (K :&: H)) (H / K).
Proof. rewrite setIC -{1 3}(ker_coset K); exact: first_isom_loc. Qed.

Lemma weak_second_isom : isog (H / (K :&: H)) (H * K / K).
Proof. rewrite quotient_mulg; exact: second_isom. Qed.

End SecondIsomorphism.

Section ThirdIsomorphism.

Variables (gT : finGroupType) (G H K : {group gT}).

Hypothesis sHK : H \subset K.
Hypothesis snHG : H <| G.
Hypothesis snKG : K <| G.

Theorem third_isom : isog (G / H / (K / H)) (G / K).
Proof.
case/andP: snKG => sKG nKG; case/andP: snHG => sHG nHG.
have sHker: 'ker (coset_of H) \subset 'ker (restrm nKG (coset_of K)).
  by rewrite ker_restrm !ker_coset subsetI sHG.
have:= first_isom_loc [morphism of factm nHG sHker] (subset_refl _) => /=.
rewrite ker_factm_loc morphim_factm morphim_restrm ker_restrm -!quotientE.
by rewrite ker_coset !(setIidPr sKG) setIid.
Qed.

End ThirdIsomorphism.
