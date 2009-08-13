(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype finfun finset.
Require Import groups.

(*****************************************************************************)
(* This file contains the definitions of:                                    *)
(*                                                                           *)
(*   {morphism A >-> gT} == the type of morphisms from domain set A of       *)
(*                          elements of a groupType, to groupType gT         *)
(*                                                                           *)
(* if p is a morphism of domain A:                                           *)
(*   dom p                      == A                                         *)
(*   p @* B                     == the image of B, where defined             *)
(*                              := f @: (A :&: B)                            *)
(*   p @*^-1 C                  == the pre-image of C, where defined         *)
(*                              :=  A :&: f @^-1: B                          *)
(*   'ker p                     == the kernel of p                           *)
(*                              :=  p @*^-1: 1                               *)
(*   'ker_H p                   ==  (p @*^-1: 1), intersected with H         *)
(*   'injm p                    <=> p injective                              *)
(*                              <-> ker p \subset 1)                         *)
(*   invm p (H :'injm f)        == the inverse morphism for an injective p   *)
(*   idm B                      == the identity morphism on B                *)
(*   restrm p (H : A \subset B) == the morphism that coincides with p on its *)
(*                                 domain A                                  *)
(*   trivm B                    == the trivial morphism on B                 *)
(*                                                                           *)
(* if, moreover, q is a morphism of domain B:                                *)
(*   factm (H1 : A \subset B) (H2 : 'ker q \subset 'ker p) == the natural    *)
(*                                  surjection between the ranges of q and p *)
(*                                                                           *)
(* for any function f between groupTypes :                                   *)
(*   morphic A f              <=> forall x,y in A, f(x * y) = (f x) * (f y)  *)
(*   isom A B f               <=> f @: (A  \: 1) = (B \: 1)                  *)
(*   misom A B f              <=> morphic A f && isom A B f                  *)
(*   A \isog B                <=> exists f, misom A B f                      *)
(*   morphm (H : morphic B f) == f with a canonical structure of morphism    *)
(*                               with domain B                               *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Reserved Notation "x \isog y" (at level 70).

Section MorphismStructure.

Variables aT rT : finGroupType.

Structure morphism (A : {set aT}) : Type := Morphism {
  mfun :> aT -> FinGroup.sort rT;
  _ : {in A &, {morph mfun : x y / x * y}}
}.

(* We give the most 'lightweight' possible specification to define morphisms:*)
(* local congruence with the group law of aT. We then provide the properties *)
(* for the 'textbook' notion of morphism, when the required structures are   *)
(* available (e.g. its domain is a group).                                   *)

Definition morphism_for A of phant rT := morphism A.

Definition repack_morphism A f :=
  let: Morphism _ fM := f
    return {type of @Morphism A for f} -> morphism_for A (Phant rT)
  in fun k => k fM.

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

Notation "[ 'morphism' 'of' f ]" :=
     (repack_morphism (fun fM => @Morphism _ _ _ f fM))
   (at level 0, format "[ 'morphism'  'of'  f ]") : form_scope.

Implicit Arguments morphimP [aT rT A B f y].
Implicit Arguments morphpreP [aT rT A C f x].
Prenex Implicits morphimP morphpreP.

(* domain, image, preimage, kernel, using "phantom" types to infer the domain *)

Section MorphismOps1.

Variables (aT rT : finGroupType) (A : {set aT}) (f : {morphism A >-> rT}).

Lemma morphM : {in A &, {morph f : x y / x * y}}.
Proof. by case f. Qed.

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

Notation "''injm' f" := (pred_of_set ('ker f) \subset pred_of_set 1)
  (at level 10, f at level 8, format "''injm'  f") : group_scope.

Section MorphismTheory.

Variables aT rT : finGroupType.
Implicit Types A B : {set aT}.
Implicit Types G H K : {group aT}.
Implicit Types C D : {set rT}.
Implicit Types L M : {group rT}.

Variables (G : {group aT}) (f : {morphism G >-> rT}).

(* the usual properties occur when the domain is a group. *)

Lemma morph1 : f 1 = 1.
Proof. by apply: (mulgI (f 1)); rewrite -morphM ?mulg1. Qed.

Lemma morphV : {in G, {morph f : x / x^-1}}.
Proof.
move=> x Gx; apply: (mulgI (f x)).
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

(* morphic image,preimage properties w.r.t. set-theoretic operations *)

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

Lemma mem_morphim : forall A x, x \in G -> x \in A -> f x \in f @* A.
Proof. by move=> A x Gx Ax; apply/morphimP; exists x. Qed.

Lemma mem_morphpre : forall C x, x \in G -> f x \in C -> x \in f @*^-1 C.
Proof. by move=> C x Gx Cfx; exact/morphpreP. Qed.

Lemma morphimS : forall A B, A \subset B -> f @* A \subset f @* B.
Proof. by move=> A B sAB; rewrite imsetS ?setIS. Qed.

Lemma morphim_sub : forall A, f @* A \subset f @* G.
Proof. by move=> A; rewrite imsetS // setIid subsetIl. Qed.

Lemma morphpreS : forall C D, C \subset D -> f @*^-1 C \subset f @*^-1 D.
Proof. by move=> C D sCD; rewrite setIS ?preimsetS. Qed.

Lemma morphim0 : f @* set0 = set0.
Proof. by rewrite morphimE setI0 imset0. Qed.

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
by move=> A; apply/eqP; rewrite eqEsubset subV -invSg invgK -{1}(invgK A) subV.
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
Proof. by rewrite morphpreE preimset0 setI0. Qed.

Lemma morphpreT : f @*^-1 setT = G.
Proof. by rewrite morphpreE preimsetT setIT. Qed.

Lemma morphpreU : forall C D, f @*^-1 (C :|: D) = f @*^-1 C :|: f @*^-1 D.
Proof. by move=> C D; rewrite -setIUr -preimsetU. Qed.

Lemma morphpreI : forall C D, f @*^-1 (C :&: D) = f @*^-1 C :&: f @*^-1 D.
Proof. by move=> C D; rewrite -setIIr -preimsetI. Qed.

Lemma morphpreD : forall C D, f @*^-1 (C :\: D) = f @*^-1 C :\: f @*^-1 D.
Proof. by move=> C D; apply/setP=> x; rewrite !inE; case: (x \in G). Qed.

(* kernel, domain properties *)

Lemma kerP : forall x, x \in G -> reflect (f x = 1) (x \in 'ker f).
Proof. move=> x Gx; rewrite 2!inE Gx; exact: set1P. Qed.

Lemma dom_ker : {subset 'ker f <= G}.
Proof. by move=> x; case/morphpreP. Qed.

Lemma mker : forall x, x \in 'ker f -> f x = 1.
Proof. by move=> x Kx; apply/kerP=> //; exact: dom_ker. Qed.

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

Lemma ker_norm : G \subset 'N('ker f).
Proof.
apply/subsetP=> x Gx; rewrite inE; apply/subsetP=> yx.
case/imsetP=> y Ky -> {yx}.
by rewrite !inE groupJ ?morphJ // ?dom_ker //= mker ?conj1g.
Qed.

Lemma ker_normal : 'ker f <| G.
Proof. by rewrite /(_ <| G) subsetIl ker_norm. Qed.

Lemma morphimGI : forall H A,
  'ker f \subset H -> f @* (H :&: A) = f @* H :&: f @* A.
Proof.
move=> H A sKH; apply/eqP; rewrite eqEsubset morphimI setIC.
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
move=> A H sKH; apply/eqP; rewrite eqEsubset morphimD andbT !setDE subsetI.
rewrite morphimS ?subsetIl // -[~: f @* H]setU0 -subDset setDE setCK.
by rewrite -morphimIG //= setIAC -setIA setICr setI0 morphim0.
Qed.

(* group structure preservation *)

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
  @group _ (morphpre fPh M) (morphpre_groupset M).
Canonical Structure morphim_group fPh H :=
  @group _ (morphim fPh H) (morphim_groupset H).
Canonical Structure ker_group fPh : {group aT} :=
  Eval hnf in [group of ker fPh].

Lemma morph_dom_groupset : group_set (f @: G).
Proof. by rewrite -morphimEdom groupP. Qed.

Canonical Structure morph_dom_group := group morph_dom_groupset.

Lemma morphpreMr : forall C D,
  D \subset f @* G -> f @*^-1 (C * D) = f @*^-1 C * f @*^-1 D.
Proof.
move=> C D sDfG; apply: invg_inj.
by rewrite invMg -!morphpreV invMg morphpreMl // -invSg invgK invGid.
Qed.

(* compatibility with inclusion *)

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

Lemma ker_sub_pre : forall M, 'ker f \subset f @*^-1 M.
Proof. by move=> M; rewrite morphpreS ?sub1G. Qed.

Lemma ker_normal_pre : forall M, 'ker f <| f @*^-1 M.
Proof. by move=> H; rewrite /normal ker_sub_pre subIset ?ker_norm. Qed.

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
  (A \subset 'ker f) = (A \subset G) && (f @* A \subset [1]).
Proof.
move=> A; case sAG: (A \subset G); first by rewrite sub_morphim_pre.
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

(* injectivity of image and preimage *)

Lemma morphpre_inj :
  {in [pred C : {set _} | C \subset f @* G] &, injective (fun C => f @*^-1 C)}.
Proof. exact: can_in_inj morphpreK. Qed.

Lemma morphim_injG :
  {in [pred H : {group _} | ('ker f \subset H) && (H \subset G)] &,
   injective (fun H => f @* H)}.
Proof.
move=> H K; case/andP=> skH sHG; case/andP=> skK sKG eqfHK.
by apply: val_inj; rewrite /= -(morphimGK skH sHG) eqfHK morphimGK.
Qed.

Lemma morphim_inj : forall H1 H2,
    ('ker f \subset H1) &&  (H1 \subset G) ->
    ('ker f \subset H2) &&  (H2 \subset G) ->
  f @* H1 = f @* H2 -> H1 :=: H2.
Proof. by move=> H1 H2 nH1f nH2f; move/morphim_injG->. Qed.

(* commutation with the generated group *)

Lemma morphim_gen : forall A, A \subset G -> f @* <<A>> = <<f @* A>>.
Proof.
move=> A sAG; apply/eqP.
rewrite eqEsubset andbC gen_subG morphimS; last exact: subset_gen.
by rewrite sub_morphim_pre gen_subG // -sub_morphim_pre // subset_gen.
Qed.

Lemma morphpre_gen : forall C,
  1 \in C -> C \subset f @* G -> f @*^-1 <<C>> = <<f @*^-1 C>>.
Proof.
move=> C C1 sCG; apply/eqP.
rewrite eqEsubset andbC gen_subG morphpreS; last exact: subset_gen.
rewrite -{1}(morphpreK sCG) -morphim_gen ?subsetIl // morphimGK //=.
  by rewrite sub_gen // setIS // preimsetS ?sub1set.
by rewrite gen_subG subsetIl.
Qed.

(* commutator, normaliser, normal, center properties*)

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

Lemma morphim_norm : forall A, f @* 'N(A) \subset 'N(f @* A).
Proof.
move=> A; apply/subsetP=> fx; case/morphimP=> x Gx Nx -> {fx}.
by rewrite inE -morphimJ ?(normP Nx).
Qed.

Lemma morphim_norms : forall A B,
  A \subset 'N(B) -> f @* A \subset 'N(f @* B).
Proof.
move=> A B nBA; apply: subset_trans (morphim_norm B); exact: morphimS.
Qed.

Lemma morphim_subnorm : forall A B, f @* 'N_A(B) \subset 'N_(f @* A)(f @* B).
Proof.
move=> A B; exact: subset_trans (morphimI A _) (setIS _ (morphim_norm B)).
Qed.

Lemma morphim_normal : forall A B, A <| B -> f @* A <| f @* B.
Proof.
move=> A B; case/andP=> sAB nAB.
by rewrite /(_ <| _) morphimS // morphim_norms.
Qed.

Lemma morphim_cent1 : forall x, x \in G -> f @* 'C[x] \subset 'C[f x].
Proof. by move=> x Gx; rewrite -(morphim_set1 Gx) morphim_norm. Qed.

Lemma morphim_cent1s : forall A x,
  x \in G -> A \subset 'C[x] -> f @* A \subset 'C[f x].
Proof.
move=> A x Gx cAx; apply: subset_trans (morphim_cent1 Gx); exact: morphimS.
Qed.

Lemma morphim_subcent1 : forall A x, x \in G ->
   f @* 'C_A[x] \subset 'C_(f @* A)[f x].
Proof. by move=> A x Gx; rewrite -(morphim_set1 Gx) morphim_subnorm. Qed.

Lemma morphim_cent : forall A, f @* 'C(A) \subset 'C(f @* A).
Proof.
move=> A; apply/bigcapsP=> fx; case/morphimP=> x Gx Ax ->{fx}.
apply: subset_trans (morphim_cent1 Gx); apply: morphimS; exact: bigcap_inf.
Qed.

Lemma morphim_cents : forall A B,
  A \subset 'C(B) -> f @* A \subset 'C(f @* B).
Proof.
move=> A B cBA; apply: subset_trans (morphim_cent B); exact: morphimS.
Qed.

Lemma morphim_subcent : forall A B, f @* 'C_A(B) \subset 'C_(f @* A)(f @* B).
Proof.
move=> A B; exact: subset_trans (morphimI A _) (setIS _ (morphim_cent B)).
Qed.

Lemma morphim_abelian : forall A, abelian A -> abelian (f @* A).
Proof. move=> A; exact: morphim_cents. Qed.

Lemma morphpre_norm : forall C, f @*^-1 'N(C) \subset 'N(f @*^-1 C).
Proof.
move=> C; apply/subsetP=> x; rewrite !inE; case/andP=> Gx Nfx.
by rewrite -morphpreJ ?morphpreS.
Qed.

Lemma morphpre_norms : forall C D,
  C \subset 'N(D) -> f @*^-1 C \subset 'N(f @*^-1 D).
Proof.
move=> C D nDC; apply: subset_trans (morphpre_norm D); exact: morphpreS.
Qed.

Lemma morphpre_normal :  forall C D,
  C \subset f @* G -> D \subset f @* G -> (f @*^-1 C <| f @*^-1 D) = (C <| D).
Proof.
move=> C D sCfG sDfG; apply/idP/andP=> [|[sCD nDC]].
  by move/morphim_normal; rewrite !morphpreK //; case/andP.
by rewrite /(_ <| _) (subset_trans _ (morphpre_norm _)) morphpreS.
Qed.

Lemma morphpre_subnorm : forall C D,
  f @*^-1 'N_C(D) \subset 'N_(f @*^-1 C)(f @*^-1 D).
Proof. by move=> C D; rewrite morphpreI setIS ?morphpre_norm. Qed.

Lemma morphim_normG : forall H,
  'ker f \subset H -> H \subset G -> f @* 'N(H) = 'N_(f @* G)(f @* H).
Proof.
move=> H sKH sHG; apply/eqP; rewrite eqEsubset -{1}morphimIdom morphim_subnorm.
rewrite -(morphpreK (subsetIl _ _)) morphimS //= morphpreI subIset // orbC.
by rewrite -{2}(morphimGK sKH sHG) morphpre_norm.
Qed.

Lemma morphim_subnormG : forall A H,
  'ker f \subset H -> H \subset G -> f @* 'N_A(H) = 'N_(f @* A)(f @* H).
Proof.
move=> A B sKB sBG; rewrite morphimIG ?normsG // morphim_normG //.
by rewrite setICA setIA morphimIim.
Qed.

Lemma morphpre_cent1 : forall x, x \in G -> 'C_G[x] \subset f @*^-1 'C[f x].
Proof.
move=> x Gx; rewrite -sub_morphim_pre ?subsetIl //.
by apply: subset_trans (morphim_cent1 Gx); rewrite morphimS ?subsetIr.
Qed.

Lemma morphpre_cent1s : forall C x,
  x \in G -> C \subset f @* G -> f @*^-1 C \subset 'C[x] -> C \subset 'C[f x].
Proof. by move=> C x Gx sCfG; move/(morphim_cent1s Gx); rewrite morphpreK. Qed.

Lemma morphpre_subcent1 : forall C x, x \in G ->
  'C_(f @*^-1 C)[x] \subset f @*^-1 'C_C[f x].
Proof.
move=> C x Gx; rewrite -morphpreIdom -setIA setICA morphpreI setIS //.
exact: morphpre_cent1.
Qed.

Lemma morphpre_cent : forall A, 'C_G(A) \subset f @*^-1 'C(f @* A).
Proof.
move=> C; rewrite -sub_morphim_pre ?subsetIl //.
rewrite morphimGI ?(subsetIl, subIset) // orbC.
by rewrite (subset_trans (morphim_cent _)).
Qed.

Lemma morphpre_cents : forall A C,
  C \subset f @* G -> f @*^-1 C \subset 'C(A) -> C \subset 'C(f @* A).
Proof. by move=> A C sCfG; move/morphim_cents; rewrite morphpreK. Qed.

Lemma morphpre_subcent : forall C A,
  'C_(f @*^-1 C)(A) \subset f @*^-1 'C_C(f @* A).
Proof.
move=> C A; rewrite -morphpreIdom -setIA setICA morphpreI setIS //.
exact: morphpre_cent.
Qed.

(* local injectivity properties *)

Lemma injmP : reflect {in G &, injective f} ('injm f).
Proof.
apply: (iffP subsetP) => [injf x y Gx Gy | injf x /= Kx].
  by case/ker_rcoset=> // z; move/injf; move/set1P->; rewrite mul1g.
have Gx := dom_ker Kx; apply/set1P; apply: injf => //.
by apply/rcoset_kerP; rewrite // mulg1.
Qed.

Section Injective.

Hypothesis injf : 'injm f.

Lemma ker_injm : 'ker f = 1.
Proof. exact/trivgP. Qed.

Lemma injmK : forall A, A \subset G -> f @*^-1 (f @* A) = A.
Proof. by move=> A sAG; rewrite morphimK // ker_injm // mul1g. Qed.

Lemma card_injm : forall A, A \subset G -> #|f @* A| = #|A|.
Proof.
move=> A sAG; rewrite morphimEsub // card_in_imset //.
exact: (sub_in2 (subsetP sAG) (injmP injf)).
Qed.

Lemma injm1 : forall x, x \in G -> f x = 1 -> x = 1.
Proof. by move=> x Gx; move/(kerP Gx); rewrite ker_injm; move/set1P. Qed.

Lemma injmSK : forall A B,
  A \subset G -> (f @* A \subset f @* B) = (A \subset B).
Proof. by move=> A B sAG; rewrite morphimSK // ker_injm mul1g. Qed.

Lemma sub_morphpre_injm : forall C A,
    A \subset G -> C \subset f @* G ->
  (f @*^-1 C \subset A) = (C \subset f @* A).
Proof. by move=> C A sAG sCfG; rewrite -morphpreSK ?injmK. Qed.

Lemma injmI : forall A B, f @* (A :&: B) = f @* A :&: f @* B.
Proof.
move=> A B; have sfI: f @* A :&: f @* B \subset f @* G.
  by apply/setIidPr; rewrite setIA morphimIim.
rewrite -(morphpreK sfI) morphpreI -(morphimIdom A) -(morphimIdom B).
by rewrite !injmK ?subsetIl // setICA -setIA !morphimIdom.
Qed.

Lemma injm_norm : forall A, A \subset G -> f @* 'N(A) = 'N_(f @* G)(f @* A).
Proof.
move=> A sAG; apply/eqP; rewrite -morphimIdom eqEsubset morphim_subnorm.
rewrite -sub_morphpre_injm ?subsetIl // morphpreI injmK // setIS //.
by rewrite -{2}(injmK sAG) morphpre_norm.
Qed.

Lemma injm_subnorm : forall A B,
  B \subset G -> f @* 'N_A(B) = 'N_(f @* A)(f @* B).
Proof.
by move=> A B sBG; rewrite injmI injm_norm // setICA setIA morphimIim.
Qed.

Lemma injm_cent1 : forall x, x \in G -> f @* 'C[x] = 'C_(f @* G)[f x].
Proof. by move=> x Gx; rewrite injm_norm ?morphim_set1 ?sub1set. Qed.

Lemma injm_subcent1 : forall A x, x \in G -> f @* 'C_A[x] = 'C_(f @* A)[f x].
Proof. by move=> A x Gx; rewrite injm_subnorm ?morphim_set1 ?sub1set. Qed.

Lemma injm_cent : forall A, A \subset G -> f @* 'C(A) = 'C_(f @* G)(f @* A).
Proof.
move=> A sAG; apply/eqP; rewrite -morphimIdom eqEsubset morphim_subcent.
apply/subsetP=> fx; case/setIP; case/morphimP=> x Gx _ ->{fx} cAfx.
rewrite mem_morphim // inE Gx -sub1set centsC cent_set1 -injmSK //.
by rewrite injm_cent1 // subsetI morphimS // -cent_set1 centsC sub1set.
Qed.

Lemma injm_subcent : forall A B,
  B \subset G -> f @* 'C_A(B) = 'C_(f @* A)(f @* B).
Proof.
by move=> A B sBG; rewrite injmI injm_cent // setICA setIA morphimIim.
Qed.

Lemma injm_abelian : forall A, A \subset G -> abelian (f @* A) = abelian A.
Proof.
move=> A sAG; rewrite /abelian !(sameP setIidPl eqP) -injm_subcent //.
by rewrite !eqEsubset !injmSK // subIset ?sAG.
Qed.

End Injective.

Variable g : {morphism G >-> rT}.

Lemma eq_morphim : {in G, f =1 g} -> forall A, f @* A = g @* A.
Proof.
by move=> efg A; apply: eq_in_imset; apply: sub_in1 efg => x; case/setIP.
Qed.

End MorphismTheory.

Notation "''ker' f" := (ker_group (MorPhantom f)) : subgroup_scope.
Notation "''ker_' H f" := (H :&: 'ker f)%G : subgroup_scope.
Notation "f @* H" := (morphim_group (MorPhantom f) H) : subgroup_scope.
Notation "f @*^-1 H" := (morphpre_group (MorPhantom f) H) : subgroup_scope.
Notation "f @: G" := (morph_dom_group f G) : subgroup_scope.

Section IdentityMorphism.

Variable gT : finGroupType.

Definition idm of {set gT} := fun x : gT => x : FinGroup.sort gT.

Lemma idm_morphM : forall A : {set gT}, {in A & , {morph idm A : x y / x * y}}.
Proof. by []. Qed.

Canonical Structure idm_morphism A := Morphism (@idm_morphM A).

Lemma injm_idm : forall G : {group gT}, 'injm (idm G).
Proof. by move=> G; apply/injmP=> ?. Qed.

Lemma ker_idm : forall G : {group gT}, 'ker (idm G) = 1.
Proof. by move=> G; apply/trivgP; exact: injm_idm. Qed.

Lemma morphim_idm : forall A B : {set gT}, B \subset A -> idm A @* B = B.
Proof.
move=> A B; rewrite /morphim /= /idm; move/setIidPr->.
by apply/setP=> x; apply/imsetP/idP=> [[y By ->]|Bx]; last exists x.
Qed.

Lemma morphpre_idm : forall A B : {set gT}, idm A @*^-1 B = A :&: B.
Proof. by move=> A B; apply/setP=> x; rewrite !inE. Qed.

End IdentityMorphism.

Prenex Implicits idm.

Module AfterMorph. End AfterMorph.

Section RestrictedMorphism.

Variables aT rT : finGroupType.
Variables A B : {set aT}.
Implicit Type C : {set aT}.
Implicit Type R : {set rT}.

Definition restrm of A \subset B := @id (aT -> FinGroup.sort rT).

Section Props.

Hypothesis sAB : A \subset B.
Variable f : {morphism B >-> rT}.
Notation fB := (restrm sAB (mfun f)).

Canonical Structure restrm_morphism :=
  @Morphism aT rT A fB (sub_in2 (subsetP sAB) (morphM f)).

Lemma morphim_restrm : forall C, fB @* C = f @* (A :&: C).
Proof. by move=> C; rewrite {2}/morphim setIA (setIidPr sAB). Qed.

Lemma morphpre_restrm : forall R, fB @*^-1 R = A :&: f @*^-1 R.
Proof. by move=> R; rewrite setIA (setIidPl sAB). Qed.

Lemma ker_restrm : 'ker (restrm sAB f) = 'ker_A f.
Proof. exact: morphpre_restrm. Qed.

Lemma injm_restrm : 'injm f -> 'injm (restrm sAB f).
Proof. by apply: subset_trans; rewrite ker_restrm subsetIr. Qed.

End Props.

Lemma restrmP : forall f : {morphism B >-> rT}, A \subset 'dom f ->
  exists g : {morphism A >-> rT},
    [/\ forall C, C \subset A -> f @* C = g @* C,
        'ker g = 'ker_A f & f = g :> (aT -> rT)].
Proof.
move=> f sAB; exists (restrm_morphism sAB f).
by split=> // [C sCA|]; rewrite ?ker_restrm // morphim_restrm (setIidPr sCA).
Qed.

End RestrictedMorphism.

Prenex Implicits restrm.
Implicit Arguments restrmP [aT rT A B].

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

Lemma morphpre_comp : forall C : {set rT},
  gof @*^-1 C = f @*^-1 (g @*^-1 C).
Proof. by move=> C; apply/setP=> z; rewrite !inE andbA. Qed.

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
rewrite ker_factm -morphimIdom sub_morphim_pre ?subsetIl //.
rewrite setIA (setIidPr sGH) (sameP setIidPr eqP) (setIidPl _) // eq_sym.
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

Definition invm := factm (subxx _) invm_subker.

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
Proof. by move/can_in_inj: invmK; move/injmP. Qed.

Lemma ker_invm : 'ker invm = 1.
Proof. by move/trivgP: injm_invm. Qed.

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

Lemma misom_isog : forall f, misom f -> isog.
Proof.
move=> f; case/andP=> fM iso_f; apply/existsP; exists (finfun f).
apply/andP; split; last by rewrite /misom /isom !(eq_imset _ (ffunE f)).
apply/forallP=> u; rewrite !ffunE; exact: forallP fM u.
Qed.

Lemma isom_isog : forall (D : {group aT}) (f : {morphism D >-> rT}),
  A \subset D -> isom f -> isog.
Proof.
move=> D f sAD isof; apply: (@misom_isog f); rewrite /misom isof andbT.
apply/morphicP; exact: (sub_in2 (subsetP sAD) (morphM f)).
Qed.

End Defs.

Implicit Arguments isom_isog [A B D].

Infix "\isog" := isog.

(* The real reflection properties only hold for true groups and morphisms. *)

Section Main.

Variables (G : {group aT}) (H : {group rT}).
Notation fMT := {morphism G >-> rT}.

Lemma isomP : forall f : fMT, reflect ('injm f /\ f @* G = H) (isom G H f).
Proof.
move=> f; apply: (iffP eqP) => [eqfGH | [injf <-]]; last first.
  by rewrite setDE -morphimEsub ?subsetIl // -setDE morphimDG // morphim1.
split.
  apply/subsetP=> x; rewrite !inE /=; case/andP=> Gx fx1; apply/idPn=> nx1.
  by move/setP: eqfGH; move/(_ (f x)); rewrite mem_imset ?inE (nx1, fx1).
rewrite morphimEdom -{2}(setD1K (group1 G)) imsetU eqfGH.
by rewrite imset_set1 morph1 setD1K.
Qed.

Lemma isom_card : forall f : fMT, isom G H f -> #|G| = #|H|.
Proof.
by move=> f; case/isomP; move/injmP=> injf <-; rewrite morphimEdom card_in_imset.
Qed.

Lemma isogP : reflect (exists2 f : fMT, 'injm f & f @* G = H) (G \isog H).
Proof.
apply: (iffP idP) => [| [f *]]; last by apply: (isom_isog f); last exact/isomP.
by case/existsP=> f; case/misomP=> fM; case/isomP; exists (morphm_morphism fM).
Qed.

End Main.

Variables (G : {group aT}) (f : {morphism G >-> rT}).

Lemma morphim_isom : forall (H : {group aT}) (K : {group rT}),
  H \subset G -> isom H K f -> f @* H = K.
Proof. by move=> H K; case/(restrmP f)=> g [-> // _ ->]; case/isomP. Qed.

Lemma sub_isom : forall (A : {set aT}) (C : {set rT}),
  A \subset G -> f @* A = C -> 'injm f -> isom A C f.
Proof.
move=> A C sAG; case: (restrmP f sAG) => g [_ _ fg] <-{C} injf.
rewrite /isom -morphimEsub ?morphimDG ?morphim1 //.
by rewrite subDset setUC subsetU ?sAG.
Qed.

Lemma sub_isog : forall (A : {set aT}),
  A \subset G -> 'injm f -> isog A (f @* A).
Proof. move=> A sAG injf; apply: (isom_isog f sAG); exact: sub_isom. Qed.

End ReflectProp.

Implicit Arguments morphicP [aT rT A f].
Implicit Arguments misomP [aT rT A B f].
Implicit Arguments isom_isog [aT rT A B D].
Implicit Arguments isomP [aT rT G H f].
Implicit Arguments isogP [aT rT G H].
Prenex Implicits morphic morphicP morphm isom isog isomP misomP isogP.
Notation "x \isog y":= (isog x y).

Section Isomorphisms.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_refl : G \isog G.
Proof.
by apply/isogP; exists [morphism of idm G]; rewrite /= ?injm_idm ?morphim_idm.
Qed.

Lemma isog_card : G \isog H -> #|G| = #|H|.
Proof. case/isogP=> f injf <-; apply: isom_card (f) _; exact/isomP. Qed.

Lemma trivial_isog : G :=: 1 -> H :=: 1 -> G \isog H.
Proof.
move=> -> ->; apply/isogP.
exists [morphism of @trivm gT hT 1]; rewrite /= ?morphim1 //.
rewrite ker_trivm; exact: subxx.
Qed.

Lemma isog_triv : G \isog H -> (G :==: 1) = (H :==: 1).
Proof. by move=> isoGH; rewrite !trivg_card1 isog_card. Qed.

Lemma isog_symr : G \isog H -> H \isog G.
Proof.
case/isogP=> f injf <-; apply/isogP.
by exists [morphism of invm injf]; rewrite /= ?injm_invm // invm_dom.
Qed.

Lemma isog_trans : G \isog H -> H \isog K -> G \isog K.
Proof.
case/isogP=> f injf <-; case/isogP=> g injg <-.
have defG: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
rewrite -morphim_comp -{1 8}defG.
by apply/isogP; exists [morphism of g \o f]; rewrite ?injm_comp.
Qed.

End Isomorphisms.

Section IsoBoolEquiv.

Variables gT hT kT : finGroupType.
Variables (G : {group gT}) (H : {group hT}) (K : {group kT}).

Lemma isog_sym : (G \isog H) = (H \isog G).
Proof. apply/idP/idP; exact: isog_symr. Qed.

Lemma isog_transl : G \isog H -> (G \isog K) = (H \isog K).
Proof.
by move=> iso; apply/idP/idP; apply: isog_trans; rewrite // -isog_sym.
Qed.

Lemma isog_transr : G \isog H -> (K \isog G) = (K \isog H).
Proof.
by move=> iso; apply/idP/idP; move/isog_trans; apply; rewrite // -isog_sym.
Qed.

Lemma isog_abelian :  G \isog H -> abelian G = abelian H.
Proof. by case/isogP=> f injf <-; rewrite injm_abelian. Qed.

End IsoBoolEquiv.

(* Isomorphism between a group and its subtype. *)

Section SubMorphism.

Variables (gT : finGroupType) (G : {group gT}).

Canonical Structure sgval_morphism := Morphism (@sgvalM _ G).
Canonical Structure subg_morphism := Morphism (@subgM _ G).

Lemma injm_sgval : 'injm sgval.
Proof. apply/injmP; apply: in2W; exact: subg_inj. Qed.

Lemma injm_subg : 'injm (subg G).
Proof. apply/injmP; exact: can_in_inj (@subgK _ _). Qed.
Hint Resolve injm_sgval injm_subg.

Lemma ker_sgval : 'ker sgval = 1. Proof. exact/trivgP. Qed.
Lemma ker_subg : 'ker (subg G) = 1. Proof. exact/trivgP. Qed.

Lemma subgEdom : subg G @* G = [subg G].
Proof.
apply/eqP; rewrite -subTset morphimEdom.
by apply/subsetP=> u _; rewrite -(sgvalK u) mem_imset ?subgP.
Qed.

Lemma sgval_sub : forall A, sgval @* A \subset G.
Proof. move=> A; apply/subsetP=> x; case/imsetP=> u _ ->; exact: subgP. Qed.

Lemma sgvalmK : forall A, subg G @* (sgval @* A) = A.
Proof.
move=> A; apply/eqP; rewrite eqEcard !card_injm ?subsetT ?sgval_sub //.
rewrite leqnn andbT -morphim_comp; apply/subsetP=> u /=.
by case/morphimP=> v _ Av ->; rewrite /= sgvalK.
Qed.

Lemma subgmK : forall A : {set gT}, A \subset G -> sgval @* (subg G @* A) = A.
Proof.
move=> A sAG; apply/eqP; rewrite eqEcard !card_injm ?subsetT //.
rewrite leqnn andbT -morphim_comp morphimE /= morphpreT.
by apply/subsetP=> u; case/morphimP=> v Gv Av -> /=; rewrite subgK.
Qed.

Lemma sgvalEdom : sgval @* [subg G] = G.
Proof. by rewrite -{2}subgEdom subgmK. Qed.

Lemma isom_subg : isom G [subg G] (subg G).
Proof. by apply/isomP; rewrite subgEdom. Qed.

Lemma isom_sgval : isom [subg G] G sgval.
Proof. by apply/isomP; rewrite sgvalEdom. Qed.

Lemma isog_subg : isog G [subg G].
Proof. exact: isom_isog isom_subg. Qed.

End SubMorphism.

