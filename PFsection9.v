(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8.

(******************************************************************************)
(* This file covers Peterfalvi, Section 9: On the maximal subgroups of Types  *)
(* II, III and IV. Defined here:                                              *)
(*   Ptype_Fcore_kernel MtypeP ==                                             *)
(*      a maximal normal subgroup of M contained in H = M`_\F and contained   *)
(*      in 'C_H(U), where MtypeP : of_typeP M U W1 (and provided M is not of  *)
(*      type V).                                                              *)
(*   typeP_Galois MtypeP ==                                                   *)
(*      U acts irreducibly on H / H0 where H0 = Ptype_Fcore_kernel MtypeP     *)
(*      with MtypeP : of_typeP M U W1 as above (this implies the structure of *)
(*      M / H0 is that of a Galois group acting on the multiplicative and     *)
(*      additive groups of a finite field).                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.

Module Type KeyedLockSpec.
Parameter lock : forall T, unit -> T -> T.
Axiom unlock : forall T k x, lock k x = x :> T.
Notation Unlockable c := (Unlockable (unlock _ _ : c = _)).
End KeyedLockSpec.
Module KeyedLock : KeyedLockSpec.
Definition lock T (k : unit) (x : T) := x.
Lemma unlock T k x : lock k x = x :> T. Proof. by []. Qed.
End KeyedLock.

Section MoreRMorphism.

Local Open Scope ring_scope.

Section Additive.

Variables (U V : zmodType) (k : unit) (f : {additive U -> V}).

Lemma raddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Proof. by move=> /inj_eq <-; rewrite raddf0. Qed.

Fact locked_is_additive : additive (KeyedLock.lock k (f : U -> V)).
Proof. by rewrite KeyedLock.unlock; case: f. Qed.
Canonical locked_additive := Additive locked_is_additive.

End Additive.

Section RMorphism.

Variables (R S : ringType) (k : unit) (f : {rmorphism R -> S}).

Fact locked_is_multiplicative : multiplicative (KeyedLock.lock k (f : R -> S)).
Proof. by rewrite KeyedLock.unlock; case: f => ? []. Qed.
Canonical locked_rmorphism := AddRMorphism locked_is_multiplicative.

Hypothesis inj_f : injective f.

Lemma rmorph_eq_nat x n : (f x == n%:R) = (x == n%:R).
Proof. by rewrite -(inj_eq inj_f) rmorph_nat. Qed.

Lemma rmorph_eq1 (x : R) : (f x == 1) = (x == 1).
Proof. exact: rmorph_eq_nat 1%N. Qed.

End RMorphism.

Section Linear.

Variables (R : ringType) (U  : lmodType R) (V : zmodType) (s : R -> V -> V).
Variables (k : unit) (f : {linear U -> V | s}).

Fact locked_is_scalable : scalable_for s (KeyedLock.lock k (f : U -> V)).
Proof. by rewrite KeyedLock.unlock; case: f => ? []. Qed.
Canonical locked_linear := AddLinear locked_is_scalable.

End Linear.

End MoreRMorphism.

Section MoreMorphism.

Variables (aT rT : finGroupType) (G H : {group aT}) (R : {group rT}).
Variable f : {morphism G >-> rT}.

Lemma restrmEsub (sHG : H \subset G) (A : {set aT}) :
  A \subset H -> restrm sHG f @* A = f @* A.
Proof. by rewrite morphim_restrm => /setIidPr->. Qed.

Hypothesis isoGR : isom G R f.
Lemma isom_inj : 'injm f. Proof. by have [] := isomP isoGR. Qed.
Lemma isom_im : f @* G = R. Proof. by have [] := isomP isoGR. Qed.
Lemma isom_sub_im : R \subset f @* G. Proof. by rewrite isom_im. Qed.
Definition isom_inv := restrm isom_sub_im (invm isom_inj).

Lemma isom_sym : isom R G isom_inv.
Proof.
by apply/isomP; rewrite injm_restrm ?injm_invm // im_restrm -isom_im im_invm.
Qed.

Lemma cfIsomK : cancel (cfIsom isoGR) (cfIsom isom_sym).
Proof.
move=> phi; apply/cfun_inP=> x Gx; rewrite -{1}(invmE isom_inj Gx).
by rewrite !cfIsomE // -isom_im mem_morphim.
Qed.

Lemma cfIsomKV : cancel (cfIsom isom_sym) (cfIsom isoGR).
Proof.
move=> phi; apply/cfun_inP=> y Ry; rewrite -{1}[y](invmK isom_inj) ?isom_im //.
suffices /morphpreP[fGy Gf'y]: y \in invm isom_inj @*^-1 G by rewrite !cfIsomE.
by rewrite morphpre_invm isom_im.
Qed.

Lemma cfIsom_inj : injective (cfIsom isoGR). Proof. exact: can_inj cfIsomK. Qed.

End MoreMorphism.

Implicit Arguments cfIsom_inj [[aT] [rT] [G] [R] x1 x2].

Section MoreGproduct.

Variable gT : finGroupType.

Implicit Types (G K H M : {group gT}) (A B : {set gT}).

Lemma restrm_cosetE G H A (nHG : G \subset 'N(H)) :
  A \subset G -> restrm nHG (coset H) @* A = A / H.
Proof. exact: restrmEsub. Qed.

Lemma pprodW A B G : pprod A B = G -> A * B = G. Proof. by case/pprodP. Qed.
Lemma pprodWC A B G : pprod A B = G -> B * A = G.
Proof. by case/pprodP=> _ <- /normC. Qed.
Lemma pprodWY A B G : pprod A B = G -> A <*> B = G.
Proof. by case/pprodP=> [[K H -> ->] <- /norm_joinEr]. Qed.

Section sdprod.

Variables (A B : {set gT}) (G M : {group gT}).
Hypothesis defG : A ><| B = G.

Lemma sdprodWpp : pprod A B = G.
Proof. by have [[K H -> ->] <- /pprodE] := sdprodP defG. Qed.
Lemma sdprodW : A * B = G. Proof. exact/pprodW/sdprodWpp. Qed.
Lemma sdprodWC : B * A = G. Proof. exact/pprodWC/sdprodWpp. Qed.
Lemma sdprodWY : A <*> B = G. Proof. exact/pprodWY/sdprodWpp. Qed.

Lemma sdprod_isom :
  {nAB : B \subset 'N(A) | isom B (G / A) (restrm nAB (coset A))}.
Proof.
have [[K H -> ->] <- nKH tiKH] := sdprodP defG.
by exists nKH; rewrite quotientMidl quotient_isom.
Qed.

Lemma sdprod_subr : M \subset B -> A ><| M = A <*> M.
Proof.
have [[K H -> ->] _ nKH tiKH] := sdprodP defG => sMH.
by rewrite sdprodEY ?(subset_trans sMH) //; apply/trivgP; rewrite -tiKH setIS.
Qed.

Lemma index_sdprodr : M \subset B -> #|B : M| =  #|G : A <*> M|.
Proof.
move=> sMB; move: sMB (sdprod_card defG) (sdprod_card (sdprod_subr sMB)).
have [[K H -> ->] mulKH nKH _] := sdprodP defG => sMH oG oKM.
rewrite -!divgS //=; last by rewrite -genM_join gen_subG -mulKH mulgS.
by rewrite -oG -oKM divnMl.
Qed.

Lemma isog_sdprodr_quotient : M <| B -> B / M \isog G / (A <*> M).
Proof.
case: (sdprodP defG) defG sdprod_isom => [[K H -> ->] mulKH _ _].
case/sdprod_context=> nsHG _ _ _ _ [nKH /isomP[injKH imKH]] nsMH.
have sMH := normal_sub nsMH; have nKM := subset_trans sMH nKH.
apply: isog_trans (third_isog (joing_subl K M) nsHG _) => /=; last first.
  by rewrite -quotientYK // -mulKH -quotientK ?cosetpre_normal ?quotient_normal.
rewrite quotientYidl //= -imKH -(restrm_cosetE nKH sMH) -morphim_quotm.
by rewrite sub_isog ?injm_quotm.
Qed.

End sdprod.

Lemma cprodWpp A B G : A \* B = G -> pprod A B = G.
Proof. by case/cprodP=> [[K H -> ->] <- /cents_norm/pprodE]. Qed.
Lemma cprodW A B G : A \* B = G -> A * B = G.
Proof. by move/cprodWpp/pprodW. Qed.
Lemma cprodWC A B G : A \* B = G -> B * A = G.
Proof. by move/cprodWpp/pprodWC. Qed.
Lemma cprodWY A B G : A \* B = G -> A <*> B = G.
Proof. by move/cprodWpp/pprodWY. Qed.

Lemma dprodWsd A B G : A \x B = G -> A ><| B = G.
Proof. by move=> defG; have [_ _ /dprodEsdprod <- _] := dprodP defG. Qed.
Lemma dprodWsdC A B G : A \x B = G -> B ><| A = G.
Proof. by rewrite dprodC => /dprodWsd. Qed.
Lemma dprodWcp A B G : A \x B = G -> A \* B = G.
Proof. by move=> defG; have [_ _ _ /dprodEcprod <-] := dprodP defG. Qed.
Lemma dprodW A B G : A \x B = G -> A * B = G.
Proof. by move/dprodWsd/sdprodW. Qed.
Lemma dprodWC A B G : A \x B = G -> B * A = G.
Proof. by move/dprodWsd/sdprodWC. Qed.
Lemma dprodWY A B G : A \x B = G -> A <*> B = G.
Proof. by move/dprodWsd/sdprodWY. Qed.

End MoreGproduct.

Section MoreChar.

Open Scope ring_scope.

Variable gT : finGroupType.
Implicit Types G H K L M : {group gT}.

Lemma card_imset_Ind_irr G H (X : {set Iirr H}) :
    H <| G -> {in X, forall i, 'Ind 'chi_i \in irr G} ->
    {in X & G, forall i y, conjg_Iirr i y \in X} ->
  #|X| = (#|G : H| * #|[set cfIirr ('Ind[G] 'chi_i) | i in X]|)%N.
Proof.
move=> nsHG irrIndX sXG_X; set f := fun i => cfIirr _.
rewrite -sum1_card (partition_big_imset f) /= mulnC -sum_nat_const.
apply: eq_bigr => _ /imsetP[i Xi ->]; transitivity (size (cfclass 'chi_i G)).
  rewrite -sum1_size -cfclass_sum //; apply: eq_bigl => j.
  case Xj: (j \in X).
    rewrite -(inj_eq irr_inj) !(cfIirrPE irrIndX) //.
    exact/eqP/cfclass_Ind_irrP.
  apply/esym/(contraFF _ Xj)=> /cfclassP[y Gy Dj].
  by rewrite -conjg_IirrE in Dj; rewrite (irr_inj Dj) sXG_X.
rewrite -(Lagrange_index (inertia_sub G 'chi_i)) ?sub_inertia ?normal_sub //.
rewrite -cfclass_size ((#|_ : _| =P 1)%N _) ?muln1 // -eqC_nat.
by rewrite -induced_prod_index // -(cfIirrPE irrIndX) ?cfnorm_irr.
Qed.

Lemma size_irr_subseq_seqInd K L (X : {set Iirr K}) S :
    subseq S (seqInd L X) -> {subset S <= irr L} -> K <| L ->
  (#|L : K| * size S = #|[set i | 'Ind 'chi[K]_i \in S]|)%N.
Proof.
move=> sScX irrS nsKL; rewrite (card_imset_Ind_irr nsKL); first 1 last.
- by move=> i; rewrite inE => /irrS.
- move=> i y; rewrite !inE => SiG Ly; congr (_ \in S): SiG.
  by apply: cfclass_Ind => //; apply/cfclassP; exists y; rewrite ?conjg_IirrE.
congr (_ * _)%N; rewrite -(size_map (@cfIirr _ _)).
rewrite -(card_uniqP _); last first.
  rewrite map_inj_in_uniq ?(subseq_uniq sScX) ?seqInd_uniq //.
  by apply: (@can_in_inj _ _ _ _ (tnth (irr L))) => phi /irrS/cfIirrE.
apply: eq_card => s; apply/mapP/imsetP=> [[phi Sphi ->] | [i]].
  have /seqIndP[i _ Dphi] := mem_subseq sScX Sphi.
  by exists i; rewrite ?inE -Dphi.
by rewrite inE => SiG ->; exists ('Ind 'chi_i).
Qed.

Lemma sub_inertia_Res (G K H : {group gT}) phi :
  G \subset 'N(K) -> 'I_G[phi] \subset 'I_G['Res[K, H] phi].
Proof.
move=> nKG; apply/subsetP=> y /setId2P[Gy nHy /eqP Iphi_y].
by rewrite inE Gy cfConjgRes_norm ?(subsetP nKG) ?Iphi_y /=.
Qed.

Section Sdprod.

Variables K H G : {group gT}.

Fact cfSdprodKey : unit. Proof. by []. Qed.

Hypothesis defG : K ><| H = G.

Definition cfSdprod :=
  KeyedLock.lock cfSdprodKey
   (cfMorph \o cfIsom (tagged (sdprod_isom defG)) : 'CF(H) -> 'CF(G)).

Canonical cfSdprod_unlockable := KeyedLock.Unlockable cfSdprod.
Canonical cfSdprod_additive := [additive of cfSdprod].
Canonical cfSdprod_linear := [linear of cfSdprod].
Canonical cfSdprod_rmorphism := [rmorphism of cfSdprod].
Canonical cfSdprod_lrmorphism := [lrmorphism of cfSdprod].

Let nsKG : K <| G. Proof. by have [] := sdprod_context defG. Qed.
Let sHG : H \subset G. Proof. by have [] := sdprod_context defG. Qed.
Let sKG : K \subset G. Proof. by have [] := andP nsKG. Qed.

Lemma cfker_Sdprod phi : K \subset cfker (cfSdprod phi).
Proof. by rewrite [cfSdprod]unlock cfker_Mod. Qed.

Lemma cfSdprodEr phi : {in H, cfSdprod phi =1 phi}.
Proof. by move=> y Hy; rewrite unlock cfModE ?cfIsomE ?(subsetP sHG). Qed.

Lemma cfSdprodE phi : {in K & H, forall x y, cfSdprod phi (x * y)%g = phi y}.
Proof.
by move=> x y Kx Hy; rewrite /= cfkerMl ?(subsetP (cfker_Sdprod _)) ?cfSdprodEr.
Qed.

Lemma cfSdprodK : cancel cfSdprod 'Res[H].
Proof. by move=> phi; apply/cfun_inP=> x Hx; rewrite cfResE ?cfSdprodEr. Qed.

Lemma cfRes_sdprodK phi : K \subset cfker phi -> cfSdprod ('Res[H] phi) = phi.
Proof.
move=> kerK; apply/cfun_inP=> _ /(mem_sdprod defG)[x [y [Kx Hy -> _]]].
by rewrite cfSdprodE // cfResE // cfkerMl ?(subsetP kerK).
Qed.

Lemma sdprod_cfker phi : K ><| cfker phi = cfker (cfSdprod phi).
Proof.
have [skerH [_ _ nKH tiKH]] := (cfker_sub phi, sdprodP defG).
rewrite unlock cfker_Morph ?normal_norm // cfker_Isom restrmEsub //=.
rewrite -(sdprod_modl defG) ?sub_cosetpre //=; congr (_ ><| _).
by rewrite quotientK ?(subset_trans skerH) // -group_modr //= setIC tiKH mul1g.
Qed.

Lemma cfSdprod_iso : isometry cfSdprod.
Proof. by move=> phi psi; rewrite unlock cfMod_iso // cfIsom_iso. Qed.

Lemma cfSdprod_char phi : phi \is a character -> cfSdprod phi \is a character.
Proof. by move=> Nphi; rewrite unlock cfMod_char ?cfIsom_char. Qed.

Lemma cfSdprod_lin_char phi :
  phi \is a linear_char -> cfSdprod phi \is a linear_char.
Proof. by move=> Nphi; rewrite unlock cfMod_lin_char ?cfIsom_lin_char. Qed.

Lemma cfSdprod_irr phi : phi \in irr H -> cfSdprod phi \in irr G.
Proof.
case/irrP=> i ->; rewrite irrEchar cfSdprod_char ?irr_char //=.
by rewrite cfSdprod_iso cfnorm_irr.
Qed.

Lemma cfConjgSdprod phi y :
  y \in 'N(K) -> y \in 'N(H) -> (cfSdprod phi ^ y = cfSdprod (phi ^ y))%CF.
Proof.
move=> nKy nHy.
have nGy: y \in 'N(G) by rewrite -sub1set -(sdprodW defG) normsM ?sub1set.
rewrite -{2}[phi]cfSdprodK cfConjgRes_norm // cfRes_sdprodK // cfker_conjg //.
by rewrite -{1}(normP nKy) conjSg cfker_Sdprod.
Qed.

Lemma inertia_sdprod L phi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfSdprod phi] = 'I_L[phi].
Proof.
move=> nKL nHL; have nGL: L \subset 'N(G) by rewrite -(sdprodW defG) normsM.
apply/setP=> z; rewrite ![z \in 'I__[_]]inE; apply: andb_id2l => Lz.
rewrite cfConjgSdprod ?(subsetP nKL) ?(subsetP nHL) ?(subsetP nGL) //=.
by rewrite (can_eq cfSdprodK).
Qed.

Definition sdprod_Iirr j := cfIirr (cfSdprod 'chi_j).

Lemma sdprod_IirrE j : 'chi_(sdprod_Iirr j) = cfSdprod 'chi_j.
Proof. by rewrite cfIirrE ?cfSdprod_irr ?mem_irr. Qed.

Definition Res_Iirr (A B : {group gT}) i := cfIirr ('Res[B] 'chi[A]_i).
Definition Ind_Iirr (A B : {group gT}) i := cfIirr ('Ind[B] 'chi[A]_i).

Lemma sdprod_IirrK : cancel sdprod_Iirr (Res_Iirr H).
Proof. by move=> j; rewrite /Res_Iirr sdprod_IirrE cfSdprodK irrK. Qed.

Lemma Res_sdprod_irr phi :
  K \subset cfker phi -> phi \in irr G -> 'Res phi \in irr H.
Proof.
move=> kerK /irrP[i Dphi]; rewrite irrEchar -cfSdprod_iso cfRes_sdprodK //.
by rewrite Dphi cfnorm_irr cfRes_char ?irr_char /=.
Qed.

Lemma sdprod_Res_IirrE i :
  K \subset cfker 'chi[G]_i -> 'chi_(Res_Iirr H i) = 'Res 'chi_i.
Proof. by move=> kerK; rewrite cfIirrE ?Res_sdprod_irr ?mem_irr. Qed.

Lemma sdprod_Res_IirrK i :
  K \subset cfker 'chi_i -> sdprod_Iirr (Res_Iirr H i) = i.
Proof.
by move=> kerK; rewrite /sdprod_Iirr sdprod_Res_IirrE ?cfRes_sdprodK ?irrK.
Qed.

End Sdprod.

Section MoreDprod.

Variables G K H : {group gT}.
Hypothesis KxH : K \x H = G.

Lemma sub_cfker_Dprodl phi : H \subset cfker (cfDprodl KxH phi).
Proof. by have /dprod_normal2[_ /andP[]] := cfker_Dprodl KxH phi. Qed.

Lemma sub_cfker_Dprodr psi : K \subset cfker (cfDprodr KxH psi).
Proof. by have /dprod_normal2[/andP[]] := cfker_Dprodr KxH psi. Qed.

Lemma cfConjgDprod phi psi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprod KxH phi psi ^ y = cfDprod KxH (phi ^ y) (psi ^ y))%CF.
Proof.
move=> nKy nHy; apply/cfun_inP=> _ /(mem_dprod KxH)[x1 [x2 [Kx1 Hx2 -> _]]].
rewrite cfConjgE; last by rewrite -sub1set -(dprodW KxH) normsM ?sub1set.
by rewrite conjMg !cfDprodE ?memJ_norm ?groupV // !cfConjgE.
Qed.

Lemma cfConjgDprodl phi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprodl KxH phi ^ y = cfDprodl KxH (phi ^ y))%CF.
Proof. by move=> nKy nHy; rewrite -!cfDprod1r cfConjgDprod ?rmorph1. Qed.

Lemma cfConjgDprodr psi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprodr KxH psi ^ y = cfDprodr KxH (psi ^ y))%CF.
Proof. by move=> nKy nHy; rewrite -!cfDprod1l cfConjgDprod ?rmorph1. Qed.

Lemma inertia_Dprodl L phi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfDprodl KxH phi] = 'I_L[phi].
Proof.
move=> nKL nHL; have nGL: L \subset 'N(G) by rewrite -(dprodW KxH) normsM.
apply/setP=> z; rewrite ![z \in 'I__[_]]inE; apply: andb_id2l => Lz.
rewrite cfConjgDprodl ?(subsetP nKL) ?(subsetP nHL) ?(subsetP nGL) //=.
by rewrite (can_eq (cfDprodlK KxH)).
Qed.

Lemma inertia_Dprodr L psi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfDprodr KxH psi] = 'I_L[psi].
Proof.
move=> nKL nHL; have nGL: L \subset 'N(G) by rewrite -(dprodW KxH) normsM.
apply/setP=> z; rewrite ![z \in 'I__[_]]inE; apply: andb_id2l => Lz.
rewrite cfConjgDprodr ?(subsetP nKL) ?(subsetP nHL) ?(subsetP nGL) //=.
by rewrite (can_eq (cfDprodrK KxH)).
Qed.

Lemma cfDprodKl (psi : 'CF(H)) (a := psi 1%g) :
  a != 0 -> cancel ((cfDprod KxH)^~ psi) (fun phi => a^-1 *: 'Res phi).
Proof.
have [/andP[sKG _] _] := dprod_normal2 KxH.
move=> nz_a phi; apply/cfun_inP=> x Kx; rewrite cfunE cfResE // -{1}[x]mulg1.
by rewrite mulrC cfDprodE // mulfK.
Qed.

Lemma cfDprodKr (phi : 'CF(K)) (a := phi 1%g) :
  a != 0 -> cancel (cfDprod KxH phi) (fun psi => a^-1 *: 'Res psi).
Proof.
have [_ /andP[sHG _]] := dprod_normal2 KxH.
move=> nz_a psi; apply/cfun_inP=> x Hx; rewrite cfunE cfResE // -{1}[x]mul1g.
by rewrite cfDprodE // mulKf.
Qed.

Lemma cfDprodKl_abelian j : abelian H -> cancel ((cfDprod KxH)^~ 'chi_j) 'Res.
Proof.
move=> cHH phi; apply/cfun_inP=> x Hx; have /mulG_sub[sKG _] := dprodW KxH.
rewrite cfResE // -{1}[x]mulg1 cfDprodE ?lin_char1 ?mulr1 //.
exact/char_abelianP.
Qed.

Lemma cfDprodKr_abelian i : abelian K -> cancel (cfDprod KxH 'chi_i) 'Res.
Proof.
move=> cKK phi; apply/cfun_inP=> x Hx; have /mulG_sub[_ sHG] := dprodW KxH.
rewrite cfResE // -{1}[x]mul1g cfDprodE ?lin_char1 ?mul1r //.
exact/char_abelianP.
Qed.

Lemma inertia_Dprod L (phi : 'CF(K)) (psi : 'CF(H)) :
    L \subset 'N(K) -> L \subset 'N(H) -> phi 1%g != 0 -> psi 1%g != 0 -> 
  'I_L[cfDprod KxH phi psi] = 'I_L[phi] :&: 'I_L[psi].
Proof.
move=> nKL nHL nz_phi nz_psi; apply/eqP; rewrite eqEsubset subsetI.
rewrite -{1}[phi as xi in 'I_L[xi]](cfDprodKl nz_psi).
rewrite -{1}[psi as xi in 'I_L[xi]](cfDprodKr nz_phi).
rewrite !inertia_scale_nz ?invr_eq0 // !sub_inertia_Res //=.
by rewrite -inertia_Dprodl -?inertia_Dprodr // inertia_mul.
Qed.

Lemma inertia_Dprod_irr L i j :
    L \subset 'N(K) -> L \subset 'N(H) ->
  'I_L[cfDprod KxH 'chi_i 'chi_j] = 'I_L['chi_i] :&: 'I_L['chi_j].
Proof. by move=> nKL nHL; rewrite inertia_Dprod ?irr1_neq0. Qed.

End MoreDprod.

Lemma sub_cfker_constt_Res_irr G H (A : {set gT}) i j :
    j \in irr_constt ('Res[H, G] 'chi_i) ->
    A \subset H -> H \subset G -> G \subset 'N(A) ->
  (A \subset cfker 'chi_j) = (A \subset cfker 'chi_i).
Proof.
move=> iHj sAH sHG nAG; apply/idP/idP=> kerA.
  have jGi: i \in irr_constt ('Ind 'chi_j) by rewrite constt_Ind_constt_Res.
  rewrite (subset_trans _ (cfker_constt _ jGi)) ?cfInd_char ?irr_char //=.
  by rewrite sub_cfker_Ind_irr.
rewrite (subset_trans _ (cfker_constt _ iHj)) ?cfRes_char ?irr_char //=.
by rewrite cfker_Res ?irr_char // subsetI sAH.
Qed.

Lemma sub_cfker_constt_Ind_irr G H (A : {set gT}) i j :
    i \in irr_constt ('Ind[G, H] 'chi_j) ->
    A \subset H -> H \subset G -> G \subset 'N(A) ->
  (A \subset cfker 'chi_j) = (A \subset cfker 'chi_i).
Proof. by rewrite constt_Ind_constt_Res; apply: sub_cfker_constt_Res_irr. Qed.

Lemma lin_char_prod G (xi : 'CF(G)) I r (P : pred I) x :
    xi \is a linear_char -> (forall i, P i -> x i \in G) ->
  xi (\prod_(i <- r | P i) x i)%g = \prod_(i <- r | P i) xi (x i).
Proof.
move=> lin_xi Gx; elim/(big_load (fun y => y \in G)): _.
elim/big_rec2: _ => [|i a y Pi [Gy <-]]; first by rewrite lin_char1.
by rewrite groupM ?lin_charM ?Gx.
Qed.

Section BigDprod.

Variables (I : finType) (P : pred I) (A : I -> {group gT}) (G : {group gT}).
Hypothesis defG : \big[dprod/1%g]_(i | P i) A i = G.

Let sAG i : P i -> A i \subset G.
Proof. by move=> Pi; rewrite -(bigdprodEY defG) (bigD1 i) ?joing_subl. Qed.

Fact cfBigdprod_subproof i :
  gval (if P i then A i else 1%G) \x <<\bigcup_(j | P j && (j != i)) A j>> = G.
Proof.
have:= defG; rewrite fun_if big_mkcond (bigD1 i) //= -big_filter -big_mkcond.
rewrite big_filter_cond big_andbC => defGi; congr (_ \x _ = G): (defGi).
by have{defGi} [[_ Gi _ defGi]] := dprodP defGi; rewrite (bigdprodEY defGi).
Qed.
Definition cfBigdprodi i := cfDprodl (cfBigdprod_subproof i) \o 'Res[_, A i].

Lemma cfBigdprodEi i (phi : 'CF(A i)) x :
    P i -> (forall j, P j -> x j \in A j) ->
  cfBigdprodi phi (\prod_(j | P j) x j)%g = phi (x i).
Proof.
move=> Pi Ax; rewrite -big_filter filter_index_enum; set r := enum P.
have r_i: i \in r by rewrite mem_enum.
pose n := index i r; set r1 := take n r; set r2 := drop n.+1 r.
have Dr: r = r1 ++ i :: r2.
  by rewrite -(nth_index i r_i) -drop_nth ?index_mem ?cat_take_drop.
have [r1'i r2'i]: i \notin r1 /\ i \notin r2.
  by have: uniq r := enum_uniq _; rewrite Dr cat_uniq /= => /and4P[_ /norP[]].
rewrite Dr big_cat big_cons //= cfkerMl.
  rewrite cfDprodEl ?cfResE ?Pi ?Ax // big_seq group_prod // => j r2j.
  have Pj: P j by have:= mem_drop r2j; rewrite mem_enum.
  by apply/mem_gen/bigcupP; exists j; last exact: Ax; rewrite Pj (memPn r2'i).
rewrite (subsetP (sub_cfker_Dprodl _ _)) //= big_seq group_prod // => j r1j.
have Pj: P j by have:= mem_take r1j; rewrite mem_enum.
by apply/mem_gen/bigcupP; exists j; last exact: Ax; rewrite Pj (memPn r1'i).
Qed.

Definition cfBigdprod (phi : forall i, 'CF(A i)) :=
  \prod_(i | P i) cfBigdprodi (phi i).

Lemma cfBigdprodE phi x :
    (forall i, P i -> x i \in A i) ->
  cfBigdprod phi (\prod_(i | P i) x i)%g = \prod_(i | P i) phi i (x i).
Proof.
move=> Ax; rewrite prod_cfunE; last by rewrite -(bigdprodE defG) mem_prodg.
by apply: eq_bigr => i Pi; rewrite cfBigdprodEi.
Qed.

Lemma cfBigdprod_lin phi :
  phi \is a linear_char -> phi = cfBigdprod (fun i => 'Res[A i] phi).
Proof.
move=> lin_phi; apply/cfun_inP=> _ /(mem_bigdprod defG)[x [Ax -> _]].
rewrite lin_char_prod ?cfBigdprodE // => [|i Pi]; last first.
  by rewrite (subsetP (sAG Pi)) ?Ax.
by apply/eq_bigr=> i Pi; rewrite cfResE ?sAG ?Ax.
Qed.

Lemma cfBigdprodK phi (psi := cfBigdprod phi) i :
    psi 1%g != 0 -> P i ->
  let a := phi i 1%g / psi 1%g in a != 0 /\ a *: 'Res psi = phi i.
Proof.
move=> nz_psi Pi a; pose b := \prod_(j | P j && (j != i)) phi j 1%g.
have Dpsi x: x \in A i -> psi x = b * phi i x.
  move=> Ai_x; pose F j := if j == i then x else 1%g.
  have /(cfBigdprodE phi) (j): P j -> F j \in A j.
    by rewrite /F; case: eqP => [-> | _] //.
  rewrite -big_filter -big_mkcond big_filter_cond.
  rewrite (big_pred1 i) => [->|j]; last by apply: andb_idl => /eqP->.
  rewrite (bigD1 i) // /F eqxx mulrC; congr (_ * _).
  by apply: eq_bigr => j /andP[_ /negPf->].
split.
  rewrite mulf_neq0 ?invr_eq0 // (contraNneq _ nz_psi) // => phi_i0.
  by rewrite Dpsi ?group1 // phi_i0 mulr0.
apply/cfun_inP=> x Aix; rewrite cfunE cfResE ?sAG // mulrAC.
by apply: canLR (mulfK nz_psi) _; rewrite !Dpsi // mulrC -mulrA mulrCA.
Qed.

Lemma cfBigdprodi_lin_char i (phi : 'CF(A i)) :
  phi \is a linear_char -> cfBigdprodi phi \is a linear_char.
Proof. by move=> Lphi; rewrite cfDprodl_lin_char ?cfRes_lin_char. Qed.

Lemma cfBigdprod_lin_char phi :
    (forall i, P i -> phi i \is a linear_char) ->
  cfBigdprod phi \is a linear_char.
Proof.
by move=> Lphi; apply/rpred_prod=> i /Lphi; apply: cfBigdprodi_lin_char.
Qed.

Lemma cfBigdprodKlin phi :
   (forall i, P i -> phi i \is a linear_char) ->
  forall i, P i -> 'Res (cfBigdprod phi) = phi i.
Proof.
move=> Lphi i Pi; have Lpsi := cfBigdprod_lin_char Lphi.
have [_ <-] := cfBigdprodK (lin_char_neq0 Lpsi (group1 G)) Pi.
by rewrite !lin_char1 ?Lphi // divr1 scale1r.
Qed.

Let linA i s : abelian G -> P i -> 'chi[A i]_s \is a linear_char.
Proof. by move=> /(abelianS _) cGG /sAG/cGG/char_abelianP->. Qed.

Lemma cfBigdprodKabelian Iphi (phi := fun i => 'chi_(Iphi i)) :
  abelian G -> forall i, P i -> 'Res (cfBigdprod phi) = 'chi_(Iphi i).
Proof. by move=> cGG; apply: cfBigdprodKlin => i; apply: linA. Qed.

Lemma inertia_bigdprod L phi (psi := cfBigdprod phi) :
    (forall i, P i -> L \subset 'N(A i)) -> psi 1%g != 0 -> 
  'I_L[cfBigdprod phi] = L :&: \bigcap_(i | P i) 'I_L[phi i].
Proof.
move=> nAL nz_psi; apply/eqP; rewrite eqEsubset; apply/andP; split.
  rewrite subsetI inertia_sub; apply/bigcapsP=> i Pi.
  have [] := cfBigdprodK nz_psi Pi; move: (_ / _) => a nz_a <-.
  by rewrite inertia_scale_nz ?sub_inertia_Res //= ?nAL.
apply: subset_trans (inertia_prod _ _ _ _); apply: setISS.
  rewrite subsetIidl -(bigdprodEY defG) norms_gen ?norms_bigcup //.
  exact/bigcapsP.
apply/bigcapsP=> i Pi; rewrite (bigcap_min i) ?inertia_Dprodl ?Pi ?cfRes_id //.
  exact: nAL.
by rewrite norms_gen ?norms_bigcup //; apply/bigcapsP=> j /andP[/nAL].
Qed.

Lemma inertia_bigdprod_abelian L Iphi (phi := fun i => 'chi_(Iphi i)) :
    (forall i, P i -> L \subset 'N(A i)) -> abelian G ->
  'I_L[cfBigdprod phi] = L :&: \bigcap_(i | P i) 'I_L[phi i].
Proof.
move=> nAL cGG; rewrite inertia_bigdprod // lin_char_neq0 //.
by apply: cfBigdprod_lin_char => i; apply: linA.
Qed.

Lemma cfBigdprodi_char i (phi : 'CF(A i)) :
  phi \is a character -> cfBigdprodi phi \is a character.
Proof. by move=> Nphi; rewrite cfDprodl_char ?cfRes_char. Qed.

Lemma cfBigdprod_char phi :
  (forall i, P i -> phi i \is a character) -> cfBigdprod phi \is a character.
Proof.
by move=> Nphi; apply: rpred_prod => i /Nphi; apply: cfBigdprodi_char.
Qed.

Lemma cfdot_bigdprod phi psi :
  '[cfBigdprod phi, cfBigdprod psi] = \prod_(i | P i) '[phi i, psi i].
Proof.
apply: canLR (mulKf (neq0CG G)) _; rewrite -(bigdprod_card defG).
rewrite (big_morph _ (@natrM _) (erefl _)) -big_split /=.
rewrite (eq_bigr _ (fun i _ => mulVKf (neq0CG _) _)) (big_distr_big_dep 1%g) /=.
set F := pfamily _ _ _; pose h (f : {ffun I -> gT}) := (\prod_(i | P i) f i)%g.
pose is_hK x f := forall f1, (f1 \in F) && (h f1 == x) = (f == f1).
have /fin_all_exists[h1 Dh1] x: exists f, x \in G -> is_hK x f.
  case Gx: (x \in G); last by exists [ffun _ => x].
  have [f [Af fK Uf]] := mem_bigdprod defG Gx.
  exists [ffun i => if P i then f i else 1%g] => _ f1.
  apply/andP/eqP=> [[/pfamilyP[Pf1 Af1] /eqP Dx] | <-].
    by apply/ffunP=> i; rewrite ffunE; case: ifPn => [/Uf-> | /(supportP Pf1)].
  split; last by rewrite fK; apply/eqP/eq_bigr=> i Pi; rewrite ffunE Pi.
  by apply/familyP=> i; rewrite ffunE !unfold_in; case: ifP => //= /Af.
rewrite (reindex_onto h h1) /= => [|x /Dh1/(_ (h1 x))]; last first.
  by rewrite eqxx => /andP[_ /eqP].
apply/eq_big => [f | f /andP[/Dh1<- /andP[/pfamilyP[_ Af] _]]]; last first.
  by rewrite !cfBigdprodE // rmorph_prod -big_split /=.
apply/idP/idP=> [/andP[/Dh1<-] | Ff]; first by rewrite eqxx andbT.
have /pfamilyP[_ Af] := Ff; suffices Ghf: h f \in G by rewrite -Dh1 ?Ghf ?Ff /=.
by apply/group_prod=> i Pi; rewrite (subsetP (sAG Pi)) ?Af.
Qed.

Lemma cfBigdprodi_irr i s : P i -> cfBigdprodi 'chi[A i]_s \in irr G.
Proof.
move=> Pi; rewrite /cfBigdprodi /=; move: (cfBigdprod_subproof i).
by rewrite Pi cfRes_id => /cfDprodl_irr->.
Qed.

Lemma cfBigdprod_irr Ixi : cfBigdprod (fun i => 'chi_(Ixi i)) \in irr G.
Proof.
rewrite irrEchar cfBigdprod_char => /= [|i _]; last exact: irr_char.
by rewrite cfdot_bigdprod big1 // => i _; rewrite cfnorm_irr.
Qed.

End BigDprod.

End MoreChar.

Section Nine.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

(* Peterfalvi (9.1) is covered by BGsection3.Frobenius_Wielandt_fixpoint. *)

(* These assumptions correspond to Peterfalvi, Hypothesis (9.2). *)

Variables M U W1 : {group gT}.
Hypotheses (maxM : M \in 'M) (MtypeP: of_typeP M U W1).
Hypothesis notMtype5 : FTtype M != 5.

Local Notation "'H'" := (gval M)`_\F%G (at level 0) : Group_scope.
Local Notation "'H'" := (gval M)`_\F : group_scope.
Local Notation "'W2'" := 'C_H(W1)%G (at level 0) : Group_scope.
Local Notation "'W2'" := 'C_H(gval W1) : group_scope.
Local Notation "'HU'" := M^`(1)%G (at level 0): Group_scope.
Local Notation "'HU'" := (gval M)^`(1)%g : group_scope.
Local Notation "'U''" := U^`(1)%G (at level 0) : Group_scope.
Local Notation "'U''" := (gval U)^`(1)%g : group_scope.

Let q := #|W1|.

Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.
Let nUW1 : W1 \subset 'N(U). Proof. by have [_ []] := MtypeP. Qed.
Let cHU' : U' \subset 'C(H). Proof. by have [_ []] := typeP_context MtypeP. Qed.

Let notMtype1 : FTtype M != 1%N.
Proof.
have notPF := FTtypePF_exclusion (conj _ MtypeP).
by apply/FTtypeP=> // [[U0 [/notPF]]].
Qed.

Let Mtype24 := compl_of_typeII_IV MtypeP maxM notMtype5.
Let ntU : U :!=: 1. Proof. by have [] := Mtype24. Qed.
Let pr_q : prime q. Proof. by have [] := Mtype24. Qed.
Let ntW2 : W2 != 1. Proof. by have [_ _ _ []] := MtypeP. Qed.

Lemma Ptype_Fcore_sdprod : H ><| (U <*> W1) = M.
Proof.
have [_ /= sW1M mulHUW1 _ tiHUW1] := sdprod_context defM. 
have [/= /andP[sHHU _] sUHU mulHU nHU tiHU] := sdprod_context defHU.
rewrite sdprodE /= norm_joinEr // ?mulgA ?mulHU //.
  by rewrite mulG_subG nHU (subset_trans sW1M) ?gFnorm.
rewrite setIC -(setIidPr sHHU) setIA -group_modl //.
by rewrite (setIC W1) tiHUW1 mulg1 setIC tiHU.
Qed.
Local Notation defHUW1 := Ptype_Fcore_sdprod.

Lemma Ptype_Fcore_coprime : coprime #|H| #|U <*> W1|.
Proof.
by rewrite (coprime_sdprod_Hall defHUW1) ?(pHall_Hall (Fcore_Hall M)).
Qed.
Let coH_UW1 := Ptype_Fcore_coprime.
Let coHU : coprime #|H| #|U|.
Proof. exact: coprimegS (joing_subl U W1) coH_UW1. Qed.

Let not_cHU : ~~ (U \subset 'C(H)).
Proof. by have [_ [_ ->]] := typeP_context MtypeP. Qed.

Lemma Ptype_compl_Frobenius : [Frobenius U <*> W1 = U ><| W1].
Proof.
have [[_ _ ntW1 _] _ _ [_ _ sW2H _ prHU_W1] _] := MtypeP.
have [[_ _ _ tiHUW1] [_ sUHU _ _ tiHU]] := (sdprodP defM, sdprod_context defHU).
apply/Frobenius_semiregularP=> // [|x /prHU_W1 defCx].
  by rewrite sdprodEY //; apply/trivgP; rewrite -tiHUW1 setSI.
apply/trivgP; rewrite -tiHU /= -{1}(setIidPl sUHU) -setIA defCx.
by rewrite setICA setIA subsetIl.
Qed.
Local Notation frobUW1 := Ptype_compl_Frobenius.

Let nilH : nilpotent H. Proof. exact: Fcore_nil. Qed.
Let solH : solvable H. Proof. exact: nilpotent_sol. Qed.

(* This is Peterfalvi (9.3). *)
Lemma typeII_IV_core (p := #|W2|) :
  if FTtype M == 2 then 'C_H(U) = 1 /\ #|H| = (#|W2| ^ q)%N
  else [/\ prime p, 'C_H(U <*> W1) = 1 & #|H| = (p ^ q * #|'C_H(U)|)%N].
Proof.
have [_ _ nHUW1 _] := sdprodP defHUW1.
have /= [oH _ oH1] := Frobenius_Wielandt_fixpoint frobUW1 nHUW1 coH_UW1 solH.
have [Mtype2 {oH}| notMtype2 {oH1}] := ifPn.
  suffices: 'C_H(U) = 1 by split=> //; exact: oH1.
  have [_ _ _ HUtypeF defHUF] := compl_of_typeII MtypeP maxM Mtype2.
  have [_ _ [U0 [sU0U _]]] := HUtypeF; rewrite {}defHUF => frobHU0.
  have /set0Pn[x U0x]: U0^# != set0.
    by rewrite setD_eq0 subG1; case/Frobenius_context: frobHU0.
  apply/trivgP; rewrite -(Frobenius_reg_ker frobHU0 U0x) setIS // -cent_cycle.
  by rewrite centS // cycle_subG (subsetP sU0U) //; case/setD1P: U0x.
have p_pr: prime p.
  case: ifP (FT_FPstructure gT) notMtype1 => [_ -> //| _ [W W1x W2x S T stG] _].
  have [_ _ _ _ /(_ M maxM notMtype1)[x defST]] := stG.
  without loss{defST} defSx: S T W1x W2x stG / M :=: S :^ x.
    by move=> IH; (case: defST; move: stG) => [|/FT_Pstructure_sym] /IH.
  have [[_ _ maxT] [defS defT _] [/idPn[]|Ttype2 _ _]] := stG.
    by rewrite -(FTtypeJ S x) -defSx.
  have defMx: M^`(1) ><| W1x :^ x = M by rewrite defSx derJ -sdprodJ defS.
  have /imsetP[y My defW1] := of_typeP_compl_conj defMx MtypeP.
  rewrite -[p](cardJg _ y) conjIg -centJ -FcoreJ conjGid //.
  rewrite defSx -defW1 FcoreJ centJ -conjIg cardJg (def_cycTIcompl stG).
  have [|V TtypeP] := compl_of_typeP defT maxT; first by rewrite (eqP Ttype2).
  by have [[]] := compl_of_typeII TtypeP maxT Ttype2.
rewrite -/H -/q -/p centY setICA -/W2 setIC in oH *.
suffices regUW2: 'C_W2(U) = 1 by rewrite -oH regUW2 cards1 exp1n mul1n.
apply: prime_TIg => //=; apply: contra not_cHU => /setIidPl cUW2.
rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl.
by rewrite -(@leq_pmul2l (p ^ q)) -?oH ?cUW2 //= expn_gt0 cardG_gt0.
Qed.

(* Existential witnesses for Peterfalvi (9.4). *)
Definition Ptype_Fcore_kernel of of_typeP M U W1 :=
  odflt 1%G [pick H0 : {group gT} | chief_factor M H0 H & 'C_H(U) \subset H0].
Let H0 := (Ptype_Fcore_kernel MtypeP).
Local Notation "'Hbar'" := (H / gval H0)%g (at level 0) : group_scope.
Local Notation "'Hbar'" := (H / gval H0)%G : Group_scope.
Let p := pdiv #|Hbar|.

(* This corresponds to Peterfalvi (9.4). *)
Lemma Ptype_Fcore_kernel_exists : chief_factor M H0 H /\ 'C_H(U) \subset H0.
Proof.
pose S := <<class_support 'C_H(U) H>> .
suffices [H1 maxH sCH1]: {H1 : {group gT} | maxnormal H1 H M & S \subset H1}.
  apply/andP; rewrite /H0 /Ptype_Fcore_kernel; case: pickP => // /(_ H1)/idP[].
  rewrite /chief_factor maxH Fcore_normal (subset_trans _ sCH1) ?sub_gen //.
  exact: sub_class_support.
apply/maxgroup_exists/andP; split.
  have snCH: 'C_H(U) <|<| H by rewrite nilpotent_subnormal ?subsetIl.
  by have [/setIidPl/idPn[] | // ] := subnormalEsupport snCH; rewrite centsC.
have [_ {3}<- nHUW1 _] := (sdprodP defHUW1).
rewrite norms_gen // mulG_subG class_support_norm norms_class_support //.
by rewrite normsI ?norms_cent // join_subG normG.
Qed.

Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists. Qed.
Let ltH0H : H0 \proper H.
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.
Let nH0M : M \subset 'N(H0).
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.
Let sH0H : H0 \subset H. Proof. exact: proper_sub ltH0H. Qed.
Let nsH0M : H0 <| M. Proof. by rewrite /normal (subset_trans sH0H) ?gFsub. Qed.
Let nsH0H : H0 <| H. Proof. by rewrite (normalS _ (Fcore_sub _)). Qed.
Let minHbar : minnormal Hbar (M / H0).
Proof. exact: chief_factor_minnormal. Qed.
Let ntHbar : Hbar != 1. Proof. by case/mingroupp/andP: minHbar. Qed.
Let solHbar: solvable Hbar. Proof. by rewrite quotient_sol. Qed.
Let abelHbar : p.-abelem Hbar.
Proof. by have [] := minnormal_solvable minHbar _ solHbar. Qed.
Let p_pr : prime p. Proof. by have [/pgroup_pdiv[]] := and3P abelHbar. Qed.

(* Coq does not let us use a keyword as a scope delimiter! *)
Delimit Scope C_scope with Cdiv.

(* This is Peterfalvi, Hypothesis (9.5). *)
Local Notation "'C'" := 'C_U(Hbar%g | 'Q)%G (at level 0) : Group_scope.
Local Notation "'C'" := 'C_(gval U)(Hbar | 'Q) : group_scope.
Local Notation "'Ubar'" := (U / C)%G (at level 0) : Group_scope.
Local Notation "'Ubar'" := (gval U / C)%g : group_scope.
Local Notation "'W1bar'" := (W1 / gval H0)%G (at level 0) : Group_scope.
Local Notation "'W1bar'" := (gval W1 / gval H0)%g : group_scope.
Local Notation "'W2bar'" := 'C_Hbar(W1bar%g)%G (at level 0) : Group_scope.
Local Notation "'W2bar'" := 'C_Hbar(W1bar) : group_scope.
Let c := #|C|.
Let u := #|Ubar|.
Local Notation tau := (FT_Dade0 maxM).
Local Notation "chi ^\tau" := (tau chi).
Let calX := Iirr_kerD M^`(1) H 1.
Let calS := seqIndD M^`(1) M M`_\F 1.
Let X_ Y := Iirr_kerD M^`(1) H Y.
Let S_ Y := seqIndD M^`(1) M M`_\F Y.

Local Notation inMb := (coset (gval H0)).

Local Notation "'H0C'" := (gval H0 <*> C)%G (at level 0) : Group_scope.
Local Notation "'H0C'" := (gval H0 <*> C) : group_scope.
Local Notation "'HC'" := (H <*> C)%G (at level 0) : Group_scope.
Local Notation "'HC'" := (H <*> C) : group_scope.
Local Notation "'H0U''" := (gval H0 <*> U')%G (at level 0) : Group_scope.
Local Notation "'H0U''" := (gval H0 <*> U'%g)%G : group_scope.
Local Notation "'H0C''" := (gval H0 <*> C^`(1)%g)%G (at level 0) : Group_scope.
Local Notation "'H0C''" := (gval H0 <*> C^`(1))%g : group_scope.

Let defW2bar : W2bar = W2 / H0.
Proof.
rewrite coprime_quotient_cent ?(subset_trans _ nH0M) //.
  by have [_ /mulG_sub[]] := sdprodP defM.
exact: coprimegS (joing_subr _ _) coH_UW1.
Qed.

Let nsCUW1 : C <| U <*> W1.
Proof.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
rewrite /normal subIset ?joing_subl // normsI //.
  by rewrite join_subG normG.
rewrite astabQ norm_quotient_pre ?norms_cent ?quotient_norms //.
exact: subset_trans sUW1M nH0M.
Qed.

Lemma Ptype_Fcore_extensions_normal :
  [/\ H0C <| M, HC <| M, H0U' <| M & H0C' <| M].
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have [sHM sUM] := (subset_trans sHHU sHUM, subset_trans sUHU sHUM).
have sCM: C \subset M by rewrite subIset ?sUM.
have sH0C_M: H0C \subset M by rewrite /normal join_subG (subset_trans sH0H).
have [nH0C nH0_H0C] := (subset_trans sCM nH0M, subset_trans sH0C_M nH0M).
have nsH0C: H0C <| M.
  rewrite /normal sH0C_M -{1}defM sdprodEY //= -defHU sdprodEY //= -joingA.
  rewrite join_subG andbC normsY ?(normal_norm nsCUW1) //=; last first.
    by rewrite (subset_trans _ nH0M) // join_subG sUM.
  rewrite -quotientYK // -{1}(quotientGK nsH0H) morphpre_norms //=.
  by rewrite cents_norm // centsC -quotient_astabQ quotientS ?subsetIr.
split=> //; first by rewrite /= -{1}(joing_idPl sH0H) -joingA normalY ?gFnormal.
  rewrite normalY // /normal (subset_trans (der_sub 1 U)) //=.
  rewrite -{1}defM sdprodEY //= -defHU sdprodEY //=.
  rewrite !join_subG gFnorm cents_norm 1?centsC //=.
  by rewrite (char_norm_trans (der_char _ _)).
suffices ->: H0C' :=: H0 <*> H0C^`(1).
  by rewrite normalY ?(char_normal_trans (der_char _ _)).
rewrite /= -2?quotientYK ?quotient_der ?(subset_trans (der_sub _ _)) //=.
by rewrite quotientYidl.
Qed.
Local Notation nsH0xx_M := Ptype_Fcore_extensions_normal.

Let Du: u = #|HU : HC|.
Proof.
have /andP[sCU nCU]: C <| U := normalS (subsetIl _ _) (joing_subl U _) nsCUW1.
by rewrite -(index_sdprodr defHU) -?card_quotient.
Qed.

(* This is Peterfalvi (9.6). *)
Lemma Ptype_Fcore_factor_facts : [/\ C != U, #|W2bar| = p & #|Hbar| = p ^ q]%N.
Proof.
have [defUW1 _ ntW1 _ _] := Frobenius_context Ptype_compl_Frobenius.
have coHW1: coprime #|H| #|W1| := coprimegS (joing_subr U W1) coH_UW1.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
have regUHb: 'C_Hbar(U / H0) = 1.
  have [_ sCH0] := Ptype_Fcore_kernel_exists.
  by rewrite -coprime_quotient_cent ?(nilpotent_sol nilH) ?quotientS1.
have ->: C != U.
  apply: contraNneq ntHbar => defU; rewrite -subG1 -regUHb subsetIidl centsC.
  by rewrite -defU -quotient_astabQ quotientS ?subsetIr.
have frobUW1b: [Frobenius U <*> W1 / H0 = (U / H0) ><| W1bar].
  have tiH0UW1 := coprime_TIg (coprimeSg sH0H coH_UW1).
  have /isomP[inj_f im_f] := quotient_isom nH0UW1 tiH0UW1.
  have:= injm_Frobenius (subxx _) inj_f frobUW1.
  by rewrite im_f !morphim_restrm !(setIidPr _) ?joing_subl ?joing_subr.
have{frobUW1b} oHbar: #|Hbar| = (#|W2bar| ^ q)%N.
  have nHbUW1 : U <*> W1 / H0 \subset 'N(Hbar) := quotient_norms H0 nHUW1.
  have coHbUW1 : coprime #|Hbar| #|U <*> W1 / H0| by exact: coprime_morph.
  have [//|_ _ -> //] := Frobenius_Wielandt_fixpoint frobUW1b nHbUW1 coHbUW1 _.
  by rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg ?(coprimeSg sH0H).
have abelW2bar: p.-abelem W2bar := abelemS (subsetIl _ _) abelHbar.
rewrite -(part_pnat_id (abelem_pgroup abelW2bar)) p_part in oHbar *.
suffices /eqP cycW2bar: logn p #|W2bar| == 1%N by rewrite oHbar cycW2bar.
have cycW2: cyclic W2 by have [_ _ _ []] := MtypeP.
rewrite eqn_leq -abelem_cyclic //= -/W2bar {1}defW2bar quotient_cyclic //=.
rewrite lt0n; apply: contraNneq ntHbar => W2bar1.
by rewrite trivg_card1 oHbar W2bar1 exp1n.
Qed.

Lemma def_Ptype_factor_prime : prime #|W2| -> p = #|W2|.
Proof.
move=> prW2; suffices: p \in \pi(W2) by rewrite !(primes_prime, inE) // => /eqP.
rewrite mem_primes p_pr cardG_gt0; have [_ <- _] := Ptype_Fcore_factor_facts.
by rewrite defW2bar dvdn_quotient.
Qed.

(* The first assertion of (9.4)(b) (the rest is subsumed by (9.6)). *)
Lemma typeIII_IV_core_prime : FTtype M != 2 -> p = #|W2|.
Proof.
by have:= typeII_IV_core => /=; case: ifP => // _ [/def_Ptype_factor_prime].
Qed.

Let frobUW1c : [Frobenius U <*> W1 / C = Ubar ><| W1 / C].
Proof.
apply: Frobenius_quotient frobUW1 _ nsCUW1 _.
  by apply: nilpotent_sol; have [_ []] := MtypeP.
by have [] := Ptype_Fcore_factor_facts; rewrite eqEsubset subsetIl.
Qed.  

Definition typeP_Galois := acts_irreducibly U Hbar 'Q.

(* This is Peterfalvi (9.7)(a). *)
Lemma typeP_Galois_Pn :
    ~~ typeP_Galois ->
  {H1 : {group coset_of H0} |
    [/\ #|H1| = p, U / H0 \subset 'N(H1), [acts U, on H1 | 'Q],
        \big[dprod/1]_(w in W1bar) H1 :^ w = Hbar
      & let a := #|U : 'C_U(H1 | 'Q)| in
        [/\ a > 1, a %| p.-1, cyclic (U / 'C_U(H1 | 'Q))
          & exists V : {group 'rV['Z_a]_q.-1}, Ubar \isog V]]}.
Proof.
have [_ sUW1M defHUW1 nHUW1 _] := sdprod_context defHUW1.
have [nHU nHW1] := joing_subP nHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
rewrite /typeP_Galois acts_irrQ //= => not_minHbarU.
have [H1 minH1 sH1Hb]: {H1 | minnormal (gval H1) (U / H0) & H1 \subset Hbar}.
  by apply: mingroup_exists; rewrite ntHbar quotient_norms.
exists H1; have [defH1 | ltH1H] := eqVproper sH1Hb.
  by rewrite -defH1 minH1 in not_minHbarU.
have [/andP[ntH1 nH1U] _] := mingroupP minH1.
have actsUH1: [acts U, on H1 | 'Q].
  by rewrite -(cosetpreK H1) actsQ ?norm_quotient_pre.
have [nH0H abHbar] := (normal_norm nsH0H, abelem_abelian abelHbar).
have [neqCU _ oHbar] := Ptype_Fcore_factor_facts.
have nUW1b: W1bar \subset 'N(U / H0) by exact: quotient_norms.
have oW1b: #|W1bar| = q.
  rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg //.
  by rewrite (coprimeSg sH0H) // (coprimegS (joing_subr U W1)).
have [oH1 defHbar]: #|H1| = p /\ \big[dprod/1]_(w in W1bar) H1 :^ w = Hbar.
  have nHbUW1: U <*> W1 / H0 \subset 'N(Hbar) by exact: quotient_norms.
  pose rUW1 := abelem_repr abelHbar ntHbar nHbUW1.
  have irrUW1: mx_irreducible rUW1.
    apply/abelem_mx_irrP/mingroupP; split=> [|H2]; first by rewrite ntHbar.
    case/andP=> ntH2 nH2UW1 sH2H; case/mingroupP: minHbar => _; apply=> //.
    by rewrite ntH2 -defHUW1 quotientMl // mulG_subG sub_abelian_norm.
  have nsUUW1: U / H0 <| U <*> W1 / H0 by rewrite quotient_normal // normalYl.
  pose rU := subg_repr rUW1 (normal_sub nsUUW1).
  pose V1 := rowg_mx (abelem_rV abelHbar ntHbar @* H1).
  have simV1: mxsimple rU V1 by exact/mxsimple_abelem_subg/mxsimple_abelemGP.
  have [W0 /subsetP sW01 [sumW0 dxW0]] := Clifford_basis irrUW1 simV1.
  have def_q: q = (#|W0| * \rank V1)%N.
    transitivity (\rank (\sum_(w in W0) V1 *m rUW1 w))%R.
      by rewrite sumW0 mxrank1 /= (dim_abelemE abelHbar) // oHbar pfactorK.
    rewrite (mxdirectP dxW0) -sum_nat_const; apply: eq_bigr => x /sW01/= Wx.
    by rewrite mxrankMfree ?row_free_unit ?repr_mx_unit.
  have oH1: #|H1| = (p ^ \rank V1)%N.
    by rewrite -{1}(card_Fp p_pr) -card_rowg rowg_mxK card_injm ?abelem_rV_injm.
  have oW0: #|W0| = q.
    apply/prime_nt_dvdP=> //; last by rewrite def_q dvdn_mulr.
    apply: contraTneq (proper_card ltH1H) => trivW0.
    by rewrite oHbar def_q trivW0 mul1n -oH1 ltnn.
  have q_gt0 := prime_gt0 pr_q.
  rewrite oH1 -(mulKn (\rank V1) q_gt0) -{1}oW0 -def_q divnn q_gt0.
  have defHbar: \big[dprod/1]_(w in W0) H1 :^ w = Hbar.
    have inj_rV_Hbar := rVabelem_injm abelHbar ntHbar.
    have/(injm_bigdprod _ inj_rV_Hbar)/= := bigdprod_rowg sumW0 dxW0.
    rewrite sub_im_abelem_rV rowg1 im_rVabelem => <- //=; apply: eq_bigr => w.
    by move/sW01=> Ww; rewrite abelem_rowgJ ?rowg_mxK ?abelem_rV_mK.
  have injW0: {in W0 &, injective (fun w => H1 :^ w)}.
    move=> x y Wx Wy /= eq_Hxy; apply: contraNeq ntH1 => neq_xy.
    rewrite -(conjsg_eq1 _ x) -[H1 :^ x]setIid {1}eq_Hxy; apply/eqP.
    rewrite (bigD1 y) // (bigD1 x) /= ?Wx // dprodA in defHbar.
    by case/dprodP: defHbar => [[_ _ /dprodP[_ _ _ ->] _]].
  have defH1W0: [set H1 :^ w | w in W0] = [set H1 :^ w | w in W1 / H0].
    apply/eqP; rewrite eqEcard (card_in_imset injW0) oW0 -oW1b leq_imset_card.
    rewrite andbT; apply/subsetP=> _ /imsetP[w /sW01/= Ww ->].
    move: Ww; rewrite norm_joinEr ?quotientMl // => /mulsgP[x w1 Ux Ww1 ->].
    by rewrite conjsgM (normsP nH1U) // mem_imset.
  have injW1: {in W1 / H0 &, injective (fun w => H1 :^ w)}.
    by apply/imset_injP; rewrite -defH1W0 (card_in_imset injW0) oW0 oW1b.
  by rewrite -(big_imset id injW1) -defH1W0 big_imset.
split=> //; set a := #|_ : _|; pose q1 := #|(W1 / H0)^#|.
have a_gt1: a > 1.
  rewrite indexg_gt1 subsetIidl /= astabQ -sub_quotient_pre //. 
  apply: contra neqCU => cH1U; rewrite (sameP eqP setIidPl) astabQ.
  rewrite -sub_quotient_pre // -(bigdprodEY defHbar) cent_gen centsC.
  by apply/bigcupsP=> w Ww; rewrite centsC centJ -(normsP nUW1b w) ?conjSg.
have Wb1: 1 \in W1bar := group1 _.
have ->: q.-1 = q1 by rewrite -oW1b (cardsD1 1) Wb1.
have /cyclicP[h defH1]: cyclic H1 by rewrite prime_cyclic ?oH1.
have o_h: #[h] = p by rewrite defH1 in oH1.
have inj_Zp_h w := injm_Zp_unitm (h ^ w).
pose phi w := invm (inj_Zp_h w) \o restr_perm <[h ^ w]> \o actperm 'Q.
have dU w: w \in W1bar -> {subset U <= 'dom (phi w)}.
  move=> Ww x Ux; have Qx := subsetP (acts_dom actsUH1) x Ux.
  rewrite inE Qx /= im_Zp_unitm inE mem_morphpre //=; last first.
    by apply: Aut_restr_perm (actperm_Aut 'Q _); rewrite //= quotientT.
  rewrite cycleJ -defH1 !inE /=; apply/subsetP=> z H1w_z; rewrite inE actpermK.
  rewrite qactJ (subsetP nH0U) ?memJ_norm // normJ mem_conjg.
  by rewrite (subsetP nH1U) // -mem_conjg (normsP nUW1b) ?mem_quotient.
have sUD := introT subsetP (dU _ _).
have Kphi w: 'ker (phi w) = 'C(H1 :^ w | 'Q).
  rewrite !ker_comp ker_invm -kerE ker_restr_perm defH1 -cycleJ.
  apply/setP=> x; rewrite !inE; congr (_ && _) => /=.
  by apply: eq_subset_r => h1; rewrite !inE actpermK.
have o_phiU w: w \in W1bar -> #|phi w @* U| = a.
  move=> Ww; have [w1 Nw1 Ww1 def_w] := morphimP Ww.
  rewrite card_morphim Kphi (setIidPr _) ?sUD // /a indexgI /= !astabQ.
  by rewrite centJ def_w morphpreJ // -{1}(normsP nUW1 w1 Ww1) indexJg.
have a_dv_p1: a %| p.-1.
  rewrite -(o_phiU 1) // (dvdn_trans (cardSg (subsetT _))) // card_units_Zp //.
  by rewrite conjg1 o_h (@totient_pfactor p 1) ?muln1.
have cycZhw w: cyclic (units_Zp #[h ^ w]).
  rewrite -(injm_cyclic (inj_Zp_h w)) // im_Zp_unitm Aut_prime_cyclic //=.
  by rewrite -orderE orderJ o_h.
have cyc_phi1U: cyclic (phi 1 @* U) := cyclicS (subsetT _) (cycZhw 1).
split=> //; last have{cyc_phi1U a_dv_p1} [z def_z] := cyclicP cyc_phi1U.
  by rewrite -(conjsg1 H1) -Kphi (isog_cyclic (first_isog_loc _ _)) ?sUD.
have o_hw w: #[h ^ w] = #[h ^ 1] by rewrite !orderJ.
pose phi1 w x := eq_rect _ (fun m => {unit 'Z_m}) (phi w x) _ (o_hw w).
have val_phi1 w x: val (phi1 w x) = val (phi w x) :> nat.
  by rewrite /phi1; case: _ / (o_hw _).
have mem_phi1 w x: w \in W1bar -> x \in U -> phi1 w x \in <[z]>%G.
  move=> Ww Ux; have: #|<[z]>%G| = a by rewrite /= -def_z o_phiU.
  rewrite /phi1; case: _ / (o_hw w) <[z]>%G => A oA /=.
  suffices <-: phi w @* U = A by rewrite mem_morphim // dU.
  by apply/eqP; rewrite (eq_subG_cyclic (cycZhw w)) ?subsetT // oA o_phiU.
have o_z: #[z] = a by rewrite orderE -def_z o_phiU.
pose phi0 w x := ecast m 'Z_m o_z (invm (injm_Zpm z) (phi1 w x)).
pose psi x := (\row_(i < q1) (phi0 (enum_val i) x * (phi0 1 x)^-1)%g)%R.
have psiM: {in U &, {morph psi: x y / x * y}}.
  have phi0M w: w \in W1bar -> {in U &, {morph phi0 w: x y / x * y}}.
    move=> Ww x y Ux Uy; rewrite /phi0; case: (a) / (o_z) => /=.
    rewrite -morphM; first 1 [congr (invm _ _)] || by rewrite im_Zpm mem_phi1.
    by rewrite /phi1; case: _ / (o_hw w); rewrite /= -morphM ?dU.
  move=> x y Ux Uy; apply/rowP=> i; have /setD1P[_ Ww] := enum_valP i.
  by rewrite !{1}mxE !{1}phi0M // addrCA -addrA -opprD addrCA addrA.
suffices Kpsi: 'ker (Morphism psiM) = C.
  by exists [group of Morphism psiM @* U]; rewrite /Ubar -Kpsi first_isog.
apply/esym/eqP; rewrite eqEsubset; apply/andP; split.
  apply/subsetP=> x /setIP[Ux cHx]; rewrite -(bigdprodEY defHbar) in cHx.
  suffices phi0x1 w: w \in W1bar -> phi0 w x = 1.
    rewrite !inE Ux; apply/eqP/rowP=> i; have /setD1P[_ Ww] := enum_valP i.
    by rewrite !mxE !phi0x1 ?mulgV.
  move=> Ww; apply: val_inj; rewrite /phi0; case: (a) / (o_z); congr (val _).
  suffices /eqP->: phi1 w x == 1 by rewrite morph1.
  rewrite -2!val_eqE [val _]val_phi1 -(o_hw w) [phi _ _]mker // Kphi.
  by apply: subsetP (astabS _ _) _ cHx; rewrite sub_gen // (bigcup_sup w).
have sKU: 'ker (Morphism psiM) \subset U by exact: subsetIl.
rewrite -quotient_sub1 -?(Frobenius_trivg_cent frobUW1c); last first.
  by apply: subset_trans (normal_norm nsCUW1); rewrite subIset ?joing_subl.
rewrite subsetI quotientS //= quotient_cents2r // subsetI.
rewrite (subset_trans (commSg W1 sKU)) ?commg_subl //= astabQ gen_subG /=.
apply/subsetP=> _ /imset2P[x w1 Kx Ww1 ->].
have:= Kx; rewrite -groupV 2!inE groupV => /andP[Ux /set1P/rowP psi_x'0].
have [nH0x Ux'] := (subsetP nH0U x Ux, groupVr Ux); pose x'b := (inMb x)^-1.
rewrite mem_morphpre ?groupR ?morphR //= ?(subsetP nH0W1) //.
have conj_x'b w: w \in W1bar -> (h ^ w) ^ x'b = (h ^ w) ^+ val (phi 1 x^-1).
  move=> Ww; transitivity (Zp_unitm (phi w x^-1) (h ^ w)).
    have /morphpreP[_ /morphpreP[Px' Rx']] := dU w Ww x^-1 Ux'.
    rewrite invmK ?restr_permE ?cycle_id //.
    by rewrite actpermE qactJ groupV nH0x morphV.
  have:= Ww; rewrite -(setD1K Wb1) autE ?cycle_id // => /setU1P[-> // | W'w].
  have /eqP := psi_x'0 (enum_rank_in W'w w); rewrite 2!mxE enum_rankK_in //.
  rewrite -eq_mulgV1 -val_eqE /phi0; case: (a) / (o_z); rewrite /= val_eqE.
  rewrite (inj_in_eq (injmP _ (injm_invm _))) /= ?im_Zpm ?mem_phi1 //.
  by rewrite -2!val_eqE /= !val_phi1 // => /eqP->.
rewrite -sub_cent1 -(bigdprodEY defHbar) gen_subG; apply/bigcupsP=> w2 Ww2.
rewrite defH1 -cycleJ cycle_subG cent1C inE conjg_set1 !conjgM // conj_x'b //.
rewrite conjXg -!conjgM -conj_x'b ?groupM ?groupV ?mem_quotient //.
by rewrite !conjgM !conjgKV.
Qed.

(* This is Peterfalvi (9.7)(b). *)
(* Note that part of this statement feeds directly into the final chapter of  *)
(* the proof (BGappendixC), and is not used before, so it may be useful to    *)
(* reformulate to suit the needs of this part.                                *)
(*   For example, we supply separately the three component of the semi-direct *)
(* product isomorphism, because no use is made of the global isomorphism. We  *)
(* also state explicitly that the image of W2bar is Fp because this is the    *)
(* fact used in B & G, Appendix C, it is readily available during the proof,  *)
(* whereas it can only be derived from the original statement of (9.7)(b) by  *)
(* using Galois theory. Indeed the Galois part of the isomorphism is only     *)
(* needed for this -- so with the formulation below it will not be used.      *)
(*   In order to avoid the use of the Wedderburn theorem on finite division   *)
(* rings we build the field F from the enveloping algebra of the              *)
(* representation of U rather than its endomorphism ring: then the fact that  *)
(* Ubar is abelian yield commutativity directly.                              *)
Lemma typeP_Galois_P :
    typeP_Galois ->
  {F : finFieldType & {phi : {morphism Hbar >-> F}
     & {psi : {morphism U >-> {unit F}} & {eta : {morphism W1 >-> {perm F}}
   & forall alpha : {perm F}, reflect (rmorphism alpha) (alpha \in eta @* W1)
   & [/\ 'injm eta, {in Hbar & W1, morph_act 'Q 'P phi eta}
       & {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}]}
   & 'ker psi = C /\ {in Hbar & U, morph_act 'Q 'U phi psi}}
   & [/\ #|F| = (p ^ q)%N, isom Hbar [set: F] phi & phi @* W2bar = <[1%R : F]>]}
   & [/\ cyclic Ubar, coprime u p.-1 & u %| (p ^ q).-1 %/ p.-1]}.
Proof.
move=> irrU; have [_ sUW1M _ /joing_subP[nHU nHW1] _] := sdprod_context defHUW1.
have [nHbU nHbW1] := (quotient_norms H0 nHU, quotient_norms H0 nHW1).
have{sUW1M} /joing_subP[nH0U nH0W1] := subset_trans sUW1M nH0M.
have [ltCU oW2b oHb] := Ptype_Fcore_factor_facts.
pose rU := abelem_repr abelHbar ntHbar nHbU.
pose inHb := rVabelem abelHbar ntHbar; pose outHb := abelem_rV abelHbar ntHbar.
have{irrU} irrU: mx_irreducible rU by apply/abelem_mx_irrP; rewrite -acts_irrQ.
pose E_U := [pred A | (A \in enveloping_algebra_mx rU)%MS].
have cEE A: A \in E_U -> centgmx rU A.
  case/envelop_mxP=> z_ ->{A}; rewrite -memmx_cent_envelop linear_sum.
  rewrite summx_sub // => x Ux; rewrite linearZ scalemx_sub {z_}//=.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Uy.
  rewrite -repr_mxM // commgC 2?repr_mxM ?(groupR, groupM) // -/rU.
  apply/row_matrixP=> i; rewrite row_mul; move: (row i _) => h.
  have cHbH': (U / H0)^`(1) \subset 'C(Hbar).
    by rewrite -quotient_der ?quotient_cents.
  apply: rVabelem_inj; rewrite rVabelemJ ?groupR //.
  by apply: (canLR (mulKg _)); rewrite -(centsP cHbH') ?mem_commg ?mem_rVabelem.
have{cEE} [F [outF [inF outFK inFK] E_F]]:
  {F : finFieldType & {outF : {rmorphism F -> 'M(Hbar)%Mg}
   & {inF : {additive _} | cancel outF inF & {in E_U, cancel inF outF}}
   & forall a, outF a \in E_U}}%R.
- pose B := row_base (enveloping_algebra_mx rU).
  have freeB: row_free B by exact: row_base_free.
  pose outF := [additive of vec_mx \o mulmxr B].
  pose inF := [additive of mulmxr (pinvmx B) \o mxvec].
  have E_F a: outF a \in E_U by rewrite !inE vec_mxK mulmx_sub ?eq_row_base.
  have inK: {in E_U, cancel inF outF}.
    by move=> A E_A; rewrite /= mulmxKpV ?mxvecK ?eq_row_base.
  have outI: injective outF := inj_comp (can_inj vec_mxK) (row_free_inj freeB).
  have outK: cancel outF inF by move=> a; apply: outI; rewrite inK ?E_F.
  pose one := inF 1%R; pose mul a b := inF (outF a * outF b)%R.
  have outM: {morph outF: a b / mul a b >-> a * b}%R.
    by move=> a b; rewrite inK //; apply: envelop_mxM; exact: E_F.
  have out0: outF 0%R = 0%R by exact: raddf0.
  have out1: outF one = 1%R by rewrite inK //; exact: envelop_mx1.
  have nzFone: one != 0%R by rewrite -(inj_eq outI) out1 out0 oner_eq0.
  have mulA: associative mul by move=> *; apply: outI; rewrite !{1}outM mulrA.
  have mulC: commutative mul.
    move=> a b; apply: outI; rewrite !{1}outM.
    by apply: cent_mxP (E_F a); rewrite memmx_cent_envelop cEE ?E_F.
  have mul1F: left_id one mul by move=> a; apply: outI; rewrite outM out1 mul1r.
  have mulD: left_distributive mul +%R%R.
    by move=> a1 a2 b; apply: canLR outK _; rewrite !raddfD mulrDl -!{1}outM.
  pose Fring_NC := RingType 'rV__ (ComRingMixin mulA mulC mul1F mulD nzFone).
  pose Fring := ComRingType Fring_NC mulC.
  have outRM: multiplicative (outF : Fring -> _) by [].
  have mulI (nza : {a | a != 0%R :> Fring}): GRing.rreg (val nza).
    case: nza => a /=; rewrite -(inj_eq outI) out0 => nzA b1 b2 /(congr1 outF).
    rewrite !{1}outM => /row_free_inj eqB12; apply/outI/eqB12.
    by rewrite row_free_unit (mx_Schur irrU) ?cEE ?E_F.
  pose inv (a : Fring) := oapp (fun nza => invF (mulI nza) one) a (insub a).
  have inv0: (inv 0 = 0)%R by rewrite /inv insubF ?eqxx.
  have mulV: GRing.Field.axiom inv.
    by move=> a nz_a; rewrite /inv insubT /= (f_invF (mulI (exist _ _ _))).
  pose Funit := FieldUnitMixin mulV inv0.
  pose FringUcl := @GRing.ComUnitRing.Class _ (GRing.ComRing.class Fring) Funit.
  have Ffield := @FieldMixin (GRing.ComUnitRing.Pack FringUcl nat) _ mulV inv0.
  pose F := FieldType (IdomainType _ (FieldIdomainMixin Ffield)) Ffield.
  by exists [finFieldType of F], (AddRMorphism outRM); first exists inF.
pose in_uF (a : F) : {unit F} := insubd (1 : {unit F}) a.
have in_uF_E a: a != 1 -> val (in_uF a) = a.
  by move=> nt_a; rewrite insubdK /= ?unitfE.
have [psi psiK]: {psi : {morphism U >-> {unit F}}
                      | {in U, forall x, outF (val (psi x)) = rU (inMb x)}}.
- pose psi x := in_uF (inF (rU (inMb x))).
  have psiK x: x \in U -> outF (val (psi x)) = rU (inMb x).
    move/(mem_quotient H0)=> Ux; have EUx := envelop_mx_id rU Ux.
    rewrite in_uF_E ?inFK //; apply: contraTneq (repr_mx_unitr rU Ux).
    by move/(canRL_in inFK EUx)->; rewrite rmorph0 unitr0.
  suffices psiM: {in U &, {morph psi: x y / x * y}} by exists (Morphism psiM).
  move=> x y Ux Uy /=; apply/val_inj/(can_inj outFK); rewrite rmorphM //.
  by rewrite !{1}psiK ?groupM // morphM ?(subsetP nH0U) ?repr_mxM ?mem_quotient.
have /trivgPn/sig2W[s W2s nts]: W2bar != 1 by rewrite -cardG_gt1 oW2b prime_gt1.
pose sb := outHb s; have [Hs cW1s] := setIP W2s.
have nz_sb: sb != 0%R by rewrite morph_injm_eq1 ?abelem_rV_injm.
pose phi' a : coset_of H0 := inHb (sb *m outF a)%R.
have Hphi' a: phi' a \in Hbar by exact: mem_rVabelem.
have phi'D: {in setT &, {morph phi' : a b / a * b}}.
  by move=> a b _ _; rewrite /phi' !raddfD [inHb _]morphM ?mem_im_abelem_rV.
have inj_phi': injective phi'.
  move=> a b /rVabelem_inj eq_sab; apply: contraNeq nz_sb.
  rewrite -[sb]mulmx1 idmxE -(rmorph1 outF) -subr_eq0 => /divff <-.
  by rewrite rmorphM mulmxA !raddfB /= eq_sab subrr mul0mx.
have injm_phi': 'injm (Morphism phi'D) by apply/injmP; exact: in2W.
have Dphi: 'dom (invm injm_phi') = Hbar.
  apply/setP=> h; apply/morphimP/idP=> [[a _ _ ->] // | Hh].
  have /cyclic_mxP[A E_A def_h]: (outHb h <= cyclic_mx rU sb)%MS.
    by rewrite -(mxsimple_cyclic irrU) ?submx1.
  by exists (inF A); rewrite ?inE //= /phi' inFK // -def_h [inHb _]abelem_rV_K.
have [phi [def_phi Kphi _ im_phi]] := domP _ Dphi.
have{Kphi} inj_phi: 'injm phi by rewrite Kphi injm_invm.
have{im_phi} im_phi: phi @* Hbar = setT by rewrite im_phi -Dphi im_invm.
have phiK: {in Hbar, cancel phi phi'} by rewrite def_phi -Dphi; exact: invmK.
have{def_phi Dphi injm_phi'} phi'K: cancel phi' phi.
  by move=> a; rewrite def_phi /= invmE ?inE.
have phi'1: phi' 1%R = s by rewrite /phi' rmorph1 mulmx1 [inHb _]abelem_rV_K.
have phi_s: phi s = 1%R by rewrite -phi'1 phi'K.
have phiJ: {in Hbar & U, forall h x, phi (h ^ inMb x) = phi h * val (psi x)}%R.
  move=> h x Hh Ux; have Uxb := mem_quotient H0 Ux.
  apply: inj_phi'; rewrite phiK ?memJ_norm ?(subsetP nHbU) // /phi' rmorphM.
  by rewrite psiK // mulmxA [inHb _]rVabelemJ // -/inHb [inHb _]phiK.
have Kpsi: 'ker psi = C.
  apply/setP=> x; rewrite 2!in_setI astabQ; apply: andb_id2l => Ux.
  have Ubx := mem_quotient H0 Ux; rewrite 3!inE (subsetP nH0U) //= inE.
  apply/eqP/centP=> [psi_x1 h Hh | cHx]; last first.
    by apply/val_inj; rewrite -[val _]mul1r -phi_s -phiJ // conjgE -cHx ?mulKg.
  red; rewrite (conjgC h) -[h ^ _]phiK ?memJ_norm ?(subsetP nHbU) ?phiJ //.
  by rewrite psi_x1 mulr1 phiK.
have etaP (w : subg_of W1): injective (fun a => phi (phi' a ^ inMb (val w))).
  case: w => w /=/(mem_quotient H0)/(subsetP nHbW1) => nHw a b eq_ab.
  apply/inj_phi'/(conjg_inj (inMb w)).
  by apply: (injmP _ inj_phi) eq_ab; rewrite memJ_norm ?mem_rVabelem.
pose eta w : {perm F} := perm (etaP (subg W1 w)).
have etaK: {in Hbar & W1, forall h w, eta w (phi h) = phi (h ^ inMb w)}.
  by move=> h w Hh Ww; rewrite /= permE subgK ?phiK.
have eta1 w: w \in W1 -> eta w 1%R = 1%R.
  move=> Ww; rewrite -phi_s etaK //.
  by rewrite conjgE (centP cW1s) ?mulKg ?mem_quotient.
have etaM: {in W1 &, {morph eta: w1 w2 / w1 * w2}}.
  move=> w1 w2 Ww1 Ww2; apply/permP=> a; rewrite -[a]phi'K permM.
  rewrite !etaK ?memJ_norm ?groupM ?(subsetP nHbW1) ?mem_quotient //.
  by rewrite -conjgM -morphM ?(subsetP nH0W1).
have etaMpsi a: {in U & W1, forall x w, 
  eta w (a * val (psi x)) = eta w a * val (psi (x ^ w)%g)}%R.
- move=> x w Ux Ww; rewrite -[a]phi'K (etaK _ w (Hphi' a) Ww).
  rewrite -!phiJ // ?memJ_norm ?(subsetP nHbW1, subsetP nUW1) ?mem_quotient //.
  rewrite etaK ?memJ_norm ?(subsetP nHbU) ?mem_quotient // -!conjgM.
  by rewrite conjgC -morphJ ?(subsetP nH0U x Ux, subsetP nH0W1 w Ww).
have psiJ: {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}.
  by move=> x w Ux Ww /=; rewrite -[val _]mul1r -(eta1 w Ww) -etaMpsi ?mul1r.
have etaRM w: w \in W1 -> rmorphism (eta w).
  move=> Ww; have nUw := subsetP nHbW1 _ (mem_quotient _ Ww).
  have etaD: additive (eta w).
    move=> a b; rewrite -[a]phi'K -[b]phi'K -!zmodMgE -!zmodVgE.
    rewrite -morphV // -morphM ?{1}etaK ?groupM ?groupV // conjMg conjVg.
    by rewrite morphM 1?morphV ?groupV // memJ_norm.
  do 2![split=> //] => [a b|]; last exact: eta1.
  rewrite -[a]outFK; have /envelop_mxP[d ->] := E_F a.
  rewrite raddf_sum mulr_suml ![eta w _](raddf_sum (Additive etaD)) mulr_suml.
  apply: eq_bigr => _ /morphimP[x Nx Ux ->]; move: {d}(d _) => dx.
  rewrite -[dx]natr_Zp scaler_nat !(mulrnAl, raddfMn); congr (_ *+ dx)%R.
  by rewrite -psiK //= outFK mulrC etaMpsi // mulrC psiJ.
have oF: #|F| = (p ^ q)%N by rewrite -cardsT -im_phi card_injm.
pose nF := <[1%R : F]>; have o_nF: #|nF| = p.
  by rewrite -orderE -phi_s (order_injm inj_phi) // (abelem_order_p abelHbar).
have cyc_uF := @field_unit_group_cyclic F.
exists F.
  exists phi; last first.
    split=> //; first exact/isomP; apply/esym/eqP; rewrite eqEcard o_nF -phi_s. 
    by rewrite (@cycle_subG F) mem_morphim //= card_injm ?subsetIl ?oW2b.
  exists psi => //; last first.
    by split=> // h x Hh Ux; rewrite qactJ (subsetP nH0U) ?phiJ.
  have inj_eta: 'injm (Morphism etaM).
    have /properP[_ [h Hh notW2h]]: W2bar \proper Hbar.
      by rewrite properEcard subsetIl oW2b oHb (ltn_exp2l 1) prime_gt1.
    apply/subsetP=> w /morphpreP[Ww /set1P/permP/(_ (phi h))].
    rewrite etaK // permE => /(injmP _ inj_phi) => chw.
    rewrite -(@prime_TIg _ W1 <[w]>) //; first by rewrite inE Ww cycle_id.
    rewrite proper_subn // properEneq cycle_subG Ww andbT.
    apply: contraNneq notW2h => defW1; rewrite inE Hh /= -defW1.
    rewrite quotient_cycle ?(subsetP nH0W1) // cent_cycle cent1C inE.
    by rewrite conjg_set1 chw ?memJ_norm // (subsetP nHbW1) ?mem_quotient.
  exists (Morphism etaM) => [alpha |]; last first.
    by split=> // h w Hh Ww /=; rewrite qactJ (subsetP nH0W1) -?etaK.
  pose autF (f : {perm F}) := rmorphism f. (* Bits of Galois theory... *)
  have [r prim_r]: {r : F | forall f g, autF f -> autF g -> f r = g r -> f = g}.
    have /cyclicP/sig_eqW[r def_uF] := cyc_uF [set: {unit F}]%G.
    exists (val r) => f g fRM gRM eq_fgr; apply/permP=> a.
    rewrite (_ : f =1 RMorphism fRM) // (_ : g =1 RMorphism gRM) //.
    have [-> | /in_uF_E <-] := eqVneq a 0%R; first by rewrite !rmorph0.
    have /cycleP[m ->]: in_uF a \in <[r]> by rewrite -def_uF inE.
    by rewrite val_unitX !rmorphX /= eq_fgr.
  have /sigW[P /and3P[Pr0 nP lePq]]:
    exists P: {poly F}, [&& root P r, all (mem nF) P & #|root P| <= q].
  - pose Mr := (\matrix_(i < q.+1) (sb *m outF (r ^+ i)))%R.
    have /rowV0Pn[v /sub_kermxP vMr0 nz_v]: kermx Mr != 0%R.
      rewrite kermx_eq0 neq_ltn ltnS (leq_trans (rank_leq_col Mr)) //.
      by rewrite (dim_abelemE abelHbar) // oHb pfactorK.
    pose P : {poly F} := (\poly_(i < q.+1) (v 0 (inord i))%:R)%R.
    have szP: size P <= q.+1 by exact: size_poly.
    exists P; apply/and3P; split.
    + apply/eqP/inj_phi'; congr (inHb _); rewrite rmorph0 mulmx0 -vMr0.
      rewrite horner_poly !raddf_sum mulmx_sum_row; apply: eq_bigr => i _.
      rewrite rowK inord_val //= mulr_natl rmorphMn -scaler_nat scalemxAr.
      by rewrite natr_Zp.
    + apply/(all_nthP 0%R)=> i /leq_trans/(_ szP) le_i_q.
      by rewrite coef_poly /= le_i_q mem_cycle.
    rewrite cardE -ltnS (leq_trans _ szP) //.
    rewrite max_poly_roots ?enum_uniq //; last first.
      by apply/allP=> r'; rewrite mem_enum.
    apply: contraNneq nz_v => /polyP P0; apply/eqP/rowP=> i; apply/eqP.
    have /eqP := P0 i; rewrite mxE coef0 coef_poly ltn_ord inord_val.
    have charF: p \in [char F]%R by rewrite !inE p_pr -order_dvdn -o_nF /=.
    by rewrite -(dvdn_charf charF) (dvdn_charf (char_Fp p_pr)) natr_Zp.
  have{Pr0 nP} fPr0 f: autF f -> root P (f r).
    move=> fRM; suff <-: map_poly (RMorphism fRM) P = P by exact: rmorph_root.
    apply/polyP=> i; rewrite coef_map.
    have [/(nth_default _)-> | lt_i_P] := leqP (size P) i; first exact: rmorph0.
    by have /cycleP[n ->] := all_nthP 0%R nP i lt_i_P; exact: rmorph_nat.
  apply: (iffP morphimP) => [[w _ Ww ->] | alphaRM]; first exact: etaRM.
  suffices /setP/(_ (alpha r)): [set (eta w) r | w in W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: etaRM.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: etaRM.
  rewrite (@cardsE F) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP _ inj_eta) => //; apply: eq_w12; exact: etaRM.
have isoUb: isog Ubar (psi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a in nF^#].
have unF_E: {in nF^#, cancel in_uF val} by move=> a /setD1P[/in_uF_E].
have unFg: group_set unF.
  apply/group_setP; split=> [|_ _ /imsetP[a nFa ->] /imsetP[b nFb ->]].
    have nF1: 1%R \in nF^# by rewrite !inE cycle_id oner_eq0.
    by apply/imsetP; exists 1%R => //; apply: val_inj; rewrite unF_E.
  have nFab: (a * b)%R \in nF^#.
    rewrite !inE mulf_eq0 negb_or.
    have [[-> /cycleP[m ->]] [-> /cycleP[n ->]]] := (setD1P nFa, setD1P nFb).
    by rewrite -natrM mem_cycle.
  by apply/imsetP; exists (a * b)%R => //; apply: val_inj; rewrite /= !unF_E.
have <-: #|Group unFg| = p.-1.
  by rewrite -o_nF (cardsD1 1 nF) group1 (card_in_imset (can_in_inj unF_E)).
have <-: #|[set: {unit F}]| = (p ^ q).-1.
  rewrite -oF -(cardC1 1) cardsT card_sub; apply: eq_card => a /=.
  by rewrite !inE unitfE.
rewrite /u (isog_cyclic isoUb) (card_isog isoUb) cyc_uF.
suffices co_u_p1: coprime #|psi @* U| #|Group unFg|.
  by rewrite -(Gauss_dvdr _ co_u_p1) mulnC divnK ?cardSg ?subsetT.
rewrite -(cyclic_dprod (dprodEY _ _)) ?cyc_uF //.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cyc_uF [set:_]%G))) ?subsetT.
apply/trivgP/subsetP=> _ /setIP[/morphimP[x Nx Ux ->] /imsetP[a nFa /eqP]].
have nCx: x \in 'N(C) by rewrite -Kpsi (subsetP (ker_norm _)).
rewrite -val_eqE (unF_E a) //; case/setD1P: nFa => _ /cycleP[n {a}->].
rewrite zmodXgE => /eqP def_psi_x; rewrite mker ?set11 // Kpsi coset_idr //.
apply/set1P; rewrite -set1gE -(Frobenius_trivg_cent frobUW1c) /= -/C.
rewrite inE mem_quotient //= -sub1set -quotient_set1 ?quotient_cents2r //.
rewrite gen_subG /= -/C -Kpsi; apply/subsetP=> _ /imset2P[_ w /set1P-> Ww ->].
have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
apply/kerP; rewrite (morphM, groupM) ?morphV ?groupV //.
apply/(canLR (mulKg _))/val_inj; rewrite psiJ // mulg1 def_psi_x.
exact: (rmorph_nat (RMorphism (etaRM w Ww))).
Qed.

(* First attempt at the proof. The LTac interpretation of this proof runs
   smoothly, but typechecking at Qed diverges and runs out of memory. The
   critical point seems to be the explicit definition of the finFieldType F;
   anything that uses that definition just causes the Coq kernel to blow up:
    admit. Qed. takes 1s before the definition, 6s after, and simply defining
    a constant of type {unit finF} causes the time to shoot up to 35s+.
Lemma typeP_Galois_P_failure :
    typeP_Galois ->
  {F : finFieldType & {phi : {morphism Hbar >-> F}
     & {psi : {morphism U >-> {unit F}} & {eta : {morphism W1 >-> {perm F}}
   & forall alpha : {perm F}, reflect (rmorphism alpha) (alpha \in eta @* W1)
   & [/\ 'injm eta, {in Hbar & W1, morph_act 'Q 'P phi eta}
       & {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}]}
   & 'ker psi = C /\ {in Hbar & U, morph_act 'Q 'U phi psi}}
   & [/\ #|F| = (p ^ q)%N, isom Hbar [set: F] phi & phi @* W2bar = <[1%R : F]>]}
   & [/\ cyclic Ubar, coprime u p.-1 & u %| (p ^ q).-1 %/ p.-1]}.
Proof.
move=> irrU; have [_ sUW1M defHUW1 nHUW1 _] := sdprod_context defHUW1.
have [nHU nHW1] := joing_subP nHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
have nUW1: W1 \subset 'N(U) by case: MtypeP => _ [].
have [ltCU oW2b oHb] := Ptype_Fcore_factor_facts.
pose fT := 'rV['F_p](Hbar); pose phi := [morphism of abelem_rV abelHbar ntHbar].
pose phi' := rVabelem abelHbar ntHbar.
have phi'_inj: injective phi' by exact: rVabelem_inj.
have phi_inj: 'injm phi by exact: abelem_rV_injm.
have [_ [cHU' _] _ _] := typeP_context MtypeP.
have nHbU: U / H0 \subset 'N(Hbar) by exact: quotient_norms.
pose rU := abelem_repr abelHbar ntHbar nHbU.
pose E_U := enveloping_algebra_mx rU.
have{irrU} irrU: mx_irreducible rU by apply/abelem_mx_irrP; rewrite -acts_irrQ.
have /trivgPn/sig2W[s W2s nts]: W2bar != 1 by rewrite -cardG_gt1 oW2b prime_gt1.
pose Fone := phi s; have [Hs cW1s] := setIP W2s.
have nzFone: Fone != 0%R by rewrite morph_injm_eq1.
pose psi1 : 'M_('dim Hbar) -> fT := mulmx Fone.
have psi'P a: {A | (A \in E_U)%MS & a = psi1 A}.
  by apply/sig2_eqW/cyclic_mxP; rewrite -(mxsimple_cyclic irrU) ?submx1.
pose psi' a := s2val (psi'P a); pose Fmul (a b : fT) := (a *m psi' b)%R.
have Epsi' h: (psi' h \in E_U)%MS by rewrite /psi'; case: (psi'P h).
have Fmul1: left_id Fone Fmul by rewrite /Fmul /psi' => h; case: (psi'P h).
have cEE A: (A \in E_U)%MS -> centgmx rU A.
  case/envelop_mxP=> z_ ->{A}; rewrite -memmx_cent_envelop linear_sum.
  rewrite summx_sub // => x Ux; rewrite linearZ scalemx_sub {z_}//=.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Uy.
  rewrite -repr_mxM // commgC 2?repr_mxM ?(groupR, groupM) // -/rU.
  apply/row_matrixP=> i; rewrite row_mul; move: (row i _) => h.
  apply: phi'_inj; rewrite [phi' _]rVabelemJ -/phi' ?groupR //.
  apply/conjg_fixP/commgP/cent1P/(subsetP _ _ (mem_rVabelem _ _ _)).
  rewrite sub_cent1 // (subsetP (quotient_cents H0 cHU')) //.
  by rewrite quotientR ?mem_commg.
have psi1K A: (A \in E_U)%MS -> psi' (psi1 A) = A.
  move=> E_A; have/eqP := Fmul1 (psi1 A); rewrite -subr_eq0 -mulmxBr.
  apply: contraTeq; rewrite -[in ~~ _]subr_eq0; set D := (_ - A)%R => nzD.
  rewrite -(mul0mx _ D) (can_eq (mulmxK _)) ?(mx_Schur irrU) ?cEE //.
  by rewrite linearB addmx_sub ?Epsi' ?eqmx_opp.
have FmulC: commutative Fmul.
  move=> h1 h2; rewrite -{1}[h1]Fmul1 -{2}[h2]Fmul1 /Fmul.
  by rewrite (hom_envelop_mxC _ (Epsi' _)) ?centgmx_hom ?cEE ?Epsi'.
have FmulA: associative Fmul.
  move=> h1 h2 h3; rewrite /Fmul -{1}[h2]Fmul1 -!mulmxA psi1K //.
  by apply: envelop_mxM; exact: Epsi'.
have FmulD: left_distributive Fmul +%R%R by move=> ? ? ?; rewrite -mulmxDl.
pose Fring_NC := RingType fT (ComRingMixin FmulA FmulC Fmul1 FmulD nzFone).
pose Fring := ComRingType Fring_NC FmulC.
pose Finv (h : Fring) : Fring := psi1 (invmx (psi' h)).
have FmulV: GRing.Field.axiom Finv.
  move=> h nz_h; apply/mulmxKV/(mx_Schur irrU); first exact/cEE/Epsi'.
  by apply: contraNneq nz_h => h_0; rewrite -[h]Fmul1 /Fmul h_0 linear0.
have Finv0: (Finv 0 = 0)%R.
  rewrite /Finv (_ : psi' 0 = 0%:M)%R ?invmx_scalar ?invr0 /psi1 ?raddf0 //.
  by apply: (canLR_in psi1K); [exact: mem0mx | rewrite /psi1 raddf0].
pose Funit := FieldUnitMixin FmulV Finv0.
pose FringUcl := @GRing.ComUnitRing.Class fT (GRing.ComRing.class Fring) Funit.
have Ffield := @FieldMixin (GRing.ComUnitRing.Pack FringUcl fT) _ FmulV Finv0.
pose F := FieldType (IdomainType _ (FieldIdomainMixin Ffield)) Ffield.
pose finF := [finFieldType of F]; pose unitF := [finGroupType of {unit finF}].
(* admit / Qed slow down sharply from this point on. *)
pose in_uF (a : finF) : unitF := insubd (1 : {unit finF}) a.
have in_uF_E a: a != 1 -> val (in_uF a) = a by rewrite -unitfE; exact: insubdK.
(* admit / Qed diverge from this point on. *)
pose psi x := in_uF (psi1 (rU (coset H0 x))).
have psiE x: x \in U -> val (psi x) = psi1 (rU (coset H0 x)).
  move=> Ux; apply/in_uF_E/eqP=> /(canRL (repr_mxK rU (mem_quotient H0 Ux))).
  by apply/eqP; rewrite mul0mx.
have psiK x: x \in U -> psi' (val (psi x)) = rU (coset H0 x).
  by move=> Ux; rewrite psiE // psi1K ?envelop_mx_id ?mem_quotient.
have psiM: {in U &, {morph psi: x y / x * y}}.
  move=> x y Ux Uy; apply: val_inj; rewrite /= 2?{1}psiE ?groupM //=.
  rewrite -[(_ * _)%R]mulmxA; congr (_ *m _)%R; rewrite psiK //.
  by rewrite morphM ?(subsetP nH0U) // repr_mxM ?mem_quotient.
pose Mpsi := @Morphism gT [finGroupType of unitF] U psi psiM.
have Kpsi: 'ker Mpsi = C.
  apply/setP=> x; rewrite 2!in_setI astabQ; apply: andb_id2l => Ux.
  have Ubx := mem_quotient H0 Ux; rewrite 3!inE (subsetP nH0U) //= inE.
  apply/eqP/centP=> [cHx h Hh | cHx].
    apply/esym/commgP/conjg_fixP/(injmP _ phi_inj) => //.
      by rewrite memJ_norm ?(subsetP nHbU).
    by rewrite /phi /= (abelem_rV_J _ _ nHbU) -?psiK // cHx; exact: (@mulr1 F).
  apply/val_inj/phi'_inj; rewrite -[val _]Fmul1 /Fmul psiK //.
  by rewrite [phi' _]rVabelemJ // conjgE -cHx ?mulKg // mem_rVabelem.
pose nF := <[1%R : finF]>; have o_nF: #|nF| = p.
  by rewrite -orderE (abelem_order_p (mx_Fp_abelem _ _ p_pr)) ?inE.
have psiJ: {in Hbar & U, morph_act 'Q 'U (phi : coset_of H0 -> finF) psi}.
  move=> h x Hh Ux /=; rewrite qactJ (subsetP nH0U) // -['U%act _ _]/(_ *m _)%R.
  by rewrite psiK // -abelem_rV_J ?mem_quotient.
have etaP w1: w1 \in W1 -> injective (fun a => phi (phi' a ^ coset H0 w1)).
  move/(mem_quotient H0)/(subsetP (quotient_norms _ nHW1)) => nHw a b eq_ab.
  apply/phi'_inj/(conjg_inj (coset H0 w1)).
  by apply: (injmP _ phi_inj); rewrite // memJ_norm ?mem_rVabelem.
pose eta w1 : {perm finF} := perm (etaP _ (subgP (subg W1 w1))).
have nHUW1b := quotient_norms H0 nHUW1.
pose rUW1 := abelem_repr abelHbar ntHbar nHUW1b.
have rUW1E x: x \in U -> rUW1 (coset H0 x) = rU (coset H0 x).
  have sUUW1b := quotientS H0 (joing_subl U W1).
  by move/(mem_quotient H0); exact: eq_abelem_subg_repr.
have eta1 w: eta w 1%R = 1%R.
  rewrite permE [phi' _]abelem_rV_K // conjgE (centP cW1s) ?mulKg //.
  by rewrite mem_quotient ?subgP.
have etaM: {in W1 &, {morph eta: w1 w2 / w1 * w2}}.
  move=> w1 w2 Ww1 Ww2; apply/permP=> h; rewrite !permE /= !permE.
  rewrite !subgK ?groupM // [coset H0 _]morphM ?(subsetP nH0W1) // conjgM.
  rewrite {2}/phi' abelem_rV_K // memJ_norm ?mem_quotient ?mem_rVabelem //.
  by rewrite (subsetP (quotient_norms H0 nHW1)) ?mem_quotient.
have etaEpsi: {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}.
  move=> x w Ux Ww; have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
  have [nH0x nH0w] := (subsetP nH0U x Ux, subsetP nH0W1 w Ww).
  rewrite permE subgK // !{1}psiE // -!rUW1E //.
  have /(mem_quotient H0)UW1x: x \in U <*> W1 by rewrite mem_gen ?inE ?Ux.
  have /(mem_quotient H0)UW1w: w \in U <*> W1 by rewrite mem_gen ?inE ?Ww ?orbT.
  rewrite -(rVabelemJ _ _ nHUW1b) // [phi _]rVabelemK -/rUW1.
  rewrite [psi1]lock morphJ // !repr_mxM ?groupM ?groupV // -lock.
  rewrite /psi1 !mulmxA; congr (_ *m _ *m _)%R; rewrite -abelem_rV_J ?groupV //.
  by rewrite conjgE (centP cW1s) ?mulKg // groupV mem_quotient.
have eta_Aut w: w \in W1 -> rmorphism (eta w).
  move=> Ww; have nUw := subsetP (quotient_norms H0 nHW1) _ (mem_quotient _ Ww).
  have etaD: additive (eta w).
    move=> a b; rewrite !permE subgK //.
    rewrite [phi' _]morphM ?morphV ?mem_im_abelem_rV //= -/phi'.
    by rewrite conjMg conjVg morphM ?morphV ?groupV ?memJ_norm ?mem_rVabelem.
  do 2![split=> //] => a b; have [_ /envelop_mxP[b_ ->] {b}->] := psi'P b.
  rewrite [psi1 _]mulmx_sumr mulr_sumr [eta w _](raddf_sum (Additive etaD)).
  rewrite [s in (_ * s)%R](raddf_sum (Additive etaD)) mulr_sumr.
  apply: eq_bigr => _ /morphimP[x nH0x Ux ->]; move: (b_ _) => {b_}bx.
  rewrite -scalemxAr -(natr_Zp bx) scaler_nat !(raddfMn, mulrnAr) -/(psi1 _).
  congr (_ *+ bx)%R => {bx}; rewrite -psiE //= -etaEpsi // !permE subgK //.
  have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
  rewrite -![(_ * _)%R]/(_ *m _)%R !psiK // -abelem_rV_J ?mem_quotient //.
    rewrite (morphJ _ nH0x) ?(subsetP nH0W1) // -conjgM -conjgC conjgM.
    by rewrite [phi' _]rVabelemJ ?mem_quotient.
  rewrite memJ_norm ?mem_rVabelem ?(subsetP (quotient_norms _ nHW1)) //.
  exact: mem_quotient.
have oF: #|finF| = (p ^ q)%N by rewrite -cardsT -card_rVabelem im_rVabelem.
have cyc_uF (uG : {group unitF}): cyclic uG. (* This should be in cyclic! *)
  apply: field_mul_group_cyclic (val : unitF -> _) _ _ => // x _.
  by split=> /eqP ?; exact/eqP.
exists finF.
  exists phi; last first.
    split=> //; first by apply/isomP; rewrite im_abelem_rV.
    apply/esym/eqP; rewrite eqEcard card_injm ?subsetIl // oW2b o_nF leqnn.
    by rewrite cycle_subG mem_morphim.
  pose autF (f : {perm finF}) := rmorphism f. (* Bits of Galois theory... *)
  have [r prim_r]: {r : F | forall f g, autF f -> autF g -> f r = g r -> f = g}.
    have /cyclicP/sig_eqW[r def_uF] := cyc_uF [set: unitF]%G.
    have exp_r m: (val r ^+ m)%R = val (r ^+ m).
      by case: m => //; elim=> //= m <-.
    exists (val r) => f g fRM gRM eq_fgr; apply/permP=> a.
    rewrite (_ : f =1 RMorphism fRM) // (_ : g =1 RMorphism gRM) //.
    have [-> | /in_uF_E <-] := eqVneq a 0%R; first by rewrite !rmorph0.
    have /cycleP[m ->]: in_uF a \in <[r]> by rewrite -def_uF inE.
    by rewrite -exp_r !rmorphX /= eq_fgr.
  have inj_eta: 'injm (Morphism etaM).
    have /properP[_ [h Hh notW2h]]: W2bar \proper Hbar.
      by rewrite properEcard subsetIl oW2b oHb (ltn_exp2l 1) prime_gt1.
    apply/subsetP=> w /morphpreP[Ww /set1P/permP/(_ (phi h))].
    rewrite !permE subgK // /phi' abelem_rV_K // => chw.
    rewrite -(@prime_TIg _ W1 <[w]>) //; first by rewrite inE Ww cycle_id.
    rewrite proper_subn // properEneq cycle_subG Ww andbT.
    apply: contraNneq notW2h => defW1; rewrite inE Hh /= -defW1.
    rewrite quotient_cycle ?(subsetP nH0W1) // cent_cycle cent1C inE.
    have Hhw: h ^ coset H0 w \in Hbar.
      by rewrite memJ_norm ?(subsetP (quotient_norms _ nHW1)) ?mem_quotient.
    by rewrite conjg_set1 sub1set inE -(inj_in_eq (injmP _ phi_inj)) ?chw.
  have /sigW[P /and3P[Pr0 nP lePq]]:
    exists P : {poly F}, [&& root P r, all (mem nF) P & #|root P| <= q].
  - pose Mr := (\matrix_(i < q.+1) (r ^+ i))%R.
    have /rowV0Pn[v /sub_kermxP vMr0 nz_v]: kermx Mr != 0%R.
      rewrite kermx_eq0 neq_ltn ltnS (leq_trans (rank_leq_col Mr)) //.
      by rewrite (dim_abelemE abelHbar) // oHb pfactorK.
    pose P : {poly finF} := (\poly_(i < q.+1) (v 0 (inord i))%:R)%R.
    have szP: size P <= q.+1 by exact: size_poly.
    exists P; apply/and3P; split.
    + apply/eqP; rewrite -vMr0 mulmx_sum_row horner_poly.
      apply: eq_bigr => i _; rewrite rowK inord_val // mulr_natl -scaler_nat.
      by rewrite natr_Zp.
    + apply/(all_nthP 0%R)=> i /leq_trans/(_ szP) le_i_q.
      by rewrite coef_poly /= le_i_q mem_cycle.
    rewrite cardE -ltnS (leq_trans _ szP) //.
    rewrite (@max_poly_roots finF) ?enum_uniq //; last first.
      by apply/allP=> r'; rewrite mem_enum.
    apply: contraNneq nz_v => /polyP P0; apply/eqP/rowP=> i; apply/eqP.
    have /eqP := P0 i; rewrite mxE coef0 coef_poly ltn_ord inord_val.
    have charF: p \in [char F]%R by rewrite !inE p_pr -order_dvdn -{2}o_nF /=.
    by rewrite -(dvdn_charf charF) (dvdn_charf (char_Fp p_pr)) natr_Zp.
  exists Mpsi => //; exists (Morphism etaM) => [alpha |]; last first.
    split=> // h w Hh Ww /=; rewrite /aperm permE subgK // /phi' abelem_rV_K //.
    by congr (phi _); rewrite qactJ (subsetP nH0W1).
  have{Pr0 nP} fPr0 f: autF f -> root P (f r).
    move=> fRM; suff <-: map_poly (RMorphism fRM) P = P by exact: rmorph_root.
    apply/polyP=> i; rewrite coef_map.
    have [/(nth_default _)-> | lt_i_P] := leqP (size P) i; first exact: rmorph0.
    by have /cycleP[n ->] := all_nthP 0%R nP i lt_i_P; exact: rmorph_nat.
  apply: (iffP morphimP) => [[w _ Ww ->] | alphaRM]; first exact: eta_Aut.
  suffices /setP/(_ (alpha r)): [set (eta w) r | w in W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: eta_Aut.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: eta_Aut.
  rewrite (@cardsE finF) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP _ inj_eta) => //; apply: eq_w12; exact: eta_Aut.
have isoUb: isog Ubar (Mpsi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a in nF^#].
have unF_E: {in nF^#, cancel in_uF val} by move=> a /setD1P[/in_uF_E].
have unFg: @group_set unitF unF.
  apply/group_setP; split=> [|_ _ /imsetP[a nFa ->] /imsetP[b nFb ->]].
    have nF1: 1%R \in nF^# by rewrite !inE cycle_id andbT.
    by apply/imsetP; exists 1%R => //; apply: val_inj; rewrite unF_E.
  have nFab: (a * b)%R \in nF^#.
    rewrite !inE mulf_eq0 negb_or.
    have [[-> /cycleP[m ->]] [-> /cycleP[n ->]]] := (setD1P nFa, setD1P nFb).
    by rewrite -natrM mem_cycle.
  by apply/imsetP; exists (a * b)%R => //; apply: val_inj; rewrite /= !unF_E.
have <-: #|Group unFg| = p.-1.
  by rewrite -o_nF (cardsD1 1 nF) group1 (card_in_imset (can_in_inj unF_E)).
have <-: #|[set: unitF]| = (p ^ q).-1.
  rewrite -oF -(cardC1 1) cardsT card_sub; apply: eq_card => a /=.
  by rewrite !inE unitfE.
rewrite /u (isog_cyclic isoUb) (card_isog isoUb) cyc_uF.
suffices co_u_p1: coprime #|Mpsi @* U| #|Group unFg|.
  by rewrite -(Gauss_dvdr _ co_u_p1) mulnC divnK ?cardSg ?subsetT.
rewrite -(cyclic_dprod (dprodEY _ _)) ?cyc_uF //.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cyc_uF [set:_]%G))) ?subsetT.
apply/trivgP/subsetP=> _ /setIP[/morphimP[x Nx Ux ->] /imsetP[a nFa /eqP]].
rewrite -val_eqE (unF_E a) //; case/setD1P: nFa => _ /cycleP[n {a}->].
rewrite FinRing.zmodXgE => /eqP def_psi_x.
have nCx: x \in 'N(C) by rewrite -Kpsi (subsetP (ker_norm _)).
rewrite mker ?set11 // Kpsi coset_idr //; apply/set1P; rewrite -set1gE.
rewrite -quotient1 -(Frobenius_trivg_cent frobUW1).
have solU: solvable U by apply: nilpotent_sol; case: MtypeP => _ [].
have nCW1: W1 \subset 'N(C).
  by rewrite normsI //= astabQ norm_quotient_pre ?norms_cent ?quotient_norms.
rewrite coprime_quotient_cent ?(Frobenius_coprime frobUW1) ?subsetIl //= -/C.
rewrite inE mem_quotient //= -/C -sub1set -quotient_set1 ?quotient_cents2r //.
rewrite gen_subG /= -/C -Kpsi; apply/subsetP=> _ /imset2P[_ w /set1P-> Ww ->].
have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
apply/kerP; rewrite (morphM, groupM) ?morphV ?groupV //.
apply/(canLR (mulKg _))/val_inj; rewrite etaEpsi // mulg1 def_psi_x.
exact: (rmorph_nat (RMorphism (eta_Aut w Ww))).
Qed.
*)

Local Open Scope ring_scope.

Let redM := [predC irr M].
Let mu_ := filter redM (S_ H0).

(* The reducible conterpart of size_irr_subseq_seqInd, valid for all maximal  *)
(* groups of type P; this does NOT depend on the notMtype5 hypothesis.        *)
Lemma size_red_subseq_seqInd_typeP (cX : {set Iirr HU}) cS :
    subseq cS (seqInd M cX) -> {subset cS <= redM} ->
  (size cS = #|[set i | 'Ind 'chi[HU]_i \in cS]|)%N.
Proof.
move=> sSX redS; pose h s := 'Ind[M, HU] 'chi_s.
apply/eqP; rewrite cardE -(size_map h).
rewrite -uniq_size_uniq ?(subseq_uniq sSX) ?seqInd_uniq // => [|xi]; last first.
  apply/imageP/idP=> [[i] | Sxi]; first by rewrite inE => ? ->.
  by have /seqIndP[s _ Dxi] := mem_subseq sSX Sxi; exists s; rewrite ?inE -?Dxi.
apply/dinjectiveP; pose h1 xi := cfIirr (q%:R^-1 *: 'Res[HU, M] xi).
apply: can_in_inj (h1) _ => s; rewrite inE => /redS red_s.
have [_ cycDD /= _ _] := FT_cDade_hyp maxM MtypeP.
have:= (Dade_Ind_chi'_irr cycDD) s; set im_chi := codom _ => chi_s.
have{im_chi chi_s} /imageP[j _ ->]: s \in im_chi.
  by apply: contraR red_s => /chi_s/=[/irrP[s2 ->] _]; apply: mem_irr.
apply: irr_inj; rewrite /h Dade_Ind_chi // /h1 raddf_sum /=.
rewrite -(eq_bigr _ (fun _ _ => Dade_chiE cycDD _ _)) sumr_const.
rewrite card_Iirr_abelian ?cyclic_abelian ?prime_cyclic //.
by rewrite -scaler_nat scalerK ?neq0CG ?irrK.
Qed.

(* This subproof is shared between (9.8)(b) and (9.9)(b). *)
Let nb_redM_H0 : size mu_ = p.-1 /\ {subset mu_ <= S_ H0C}.
Proof.
have centDD := FT_cDade_hyp maxM MtypeP; pose W := W1 <*> W2.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have nb_redM K:
  K <| M -> K \subset HU -> K :&: H = H0 -> count redM (S_ K) = p.-1.
- move=> nsKM sKHU tiKHbar; have [sKM nKM] := andP nsKM; pose b A := (A / K)%g.
  have [_ /= cycDD _ _] := centDD; rewrite -/W in cycDD.
  have[[_ ntW1 hallW1 cycW1] [_ sW2HU cycW2 prW1HU] [defW oddW]] := cycDD.
  have coHU_W1: coprime #|HU| #|W1|.
    by rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM).
  have [nKHU nKW1] := (subset_trans sHUM nKM, subset_trans sW1M nKM).
  have [nKW2 coKW1] := (subset_trans sW2HU nKHU, coprimeSg sKHU coHU_W1).
  have oW2b: #|b W2| = p.
    have [_ <- _] := Ptype_Fcore_factor_facts; rewrite defW2bar.
    rewrite !card_quotient ?(subset_trans (subset_trans sW2HU sHUM)) //.
    by rewrite -tiKHbar -indexgI /= -setIA setIIr (setIC K) indexgI /=.
  have{cycW2} cycW2b: cyclic (b W2) by exact: quotient_cyclic.
  have cycDDb: cyclicDade_hypothesis (b M) (b HU) (b W) (b W1) (b W2).
    split; last 1 first.
    + have nKW: W \subset 'N(K) by rewrite join_subG nKW1.
      rewrite (morphim_coprime_dprod _ nKW) ?morphim_odd //.
      by rewrite coprime_sym (coprimeSg sW2HU).
    + have isoW1: W1 \isog b W1 by rewrite quotient_isog ?coprime_TIg.
      rewrite -(isog_eq1 isoW1) morphim_cyclic ?morphim_Hall //.
      by rewrite (morphim_coprime_sdprod _ nKM).
    rewrite -cardG_gt1 oW2b ?prime_gt1 ?morphimS //=.
    split=> // Kx /setD1P[ntKx /morphimP[x nKx W1x Dx]] /=.
    have solHU := solvableS sHUM (mmax_sol maxM).
    rewrite -cent_cycle -cycle_eq1 Dx -quotient_cycle // in ntKx *.
    rewrite -?coprime_quotient_cent ?(coprimegS _ coHU_W1) ?cycle_subG //.
    rewrite cent_cycle prW1HU // !inE W1x andbT -cycle_eq1.
    rewrite -(isog_eq1 (quotient_isog _ _)) ?cycle_subG // in ntKx.
    by rewrite coprime_TIg ?(coprimegS _ coKW1) ?cycle_subG.
  pose muK (j : Iirr (b W2)) :=
    (Dade_mu (M / K) [group of b W] (W1 / K) j %% K)%CF.
  have inj_muK: injective muK.
    by move=> j1 j2 /(can_inj (cfModK nsKM))/(Dade_mu_inj cycDDb).
  transitivity (size (image muK (predC1 0))); last first.
    by rewrite size_map -cardE cardC1 card_Iirr_abelian ?oW2b ?cyclic_abelian.
  rewrite count_filter; apply: perm_eq_size.
  apply: uniq_perm_eq => [||phi]; first by rewrite filter_uniq ?seqInd_uniq.
    by apply/dinjectiveP=> j1 j2 _ _ /inj_muK.
  have nsKHU: K <| HU := normalS sKHU sHUM nsKM.
  rewrite mem_filter; apply/andP/imageP=> [[red_phi] | [j nz_j ->]].
    case/seqIndP=> s /setDP[]; rewrite !inE /= => kersK kers'H Dphi.
    pose s1 := quo_Iirr K s.
    have{Dphi} Dphi: phi = ('Ind 'chi_s1 %% K)%CF.
      rewrite quo_IirrE // cfIndQuo ?gFnormal // cfQuoK ?Dphi //.
      by rewrite sub_cfker_Ind_irr.
    have:= (Dade_Ind_chi'_irr cycDDb) s1; set im_chi := codom _ => chi_s1.
    have{chi_s1 im_chi} /imageP[j _ Ds1]: s1 \in im_chi.
      apply: contraR red_phi => /chi_s1[{chi_s1}/= /irrP[s2 Ds2] _].
      by rewrite Dphi Ds2 cfMod_irr.
    exists j; last by rewrite Dphi Ds1 Dade_Ind_chi.
    apply: contraNneq kers'H; rewrite -(quo_IirrK _ kersK) // -/s1 Ds1 => ->.
    by rewrite mod_IirrE // Dade_chi0 ?cfMod_cfun1 // cfker_cfun1.
  have red_j: redM (muK j).
    apply: contra (Dade_mu_not_irr cycDDb j) => /= /irrP[s Ds].
    by rewrite -[_ j](cfModK nsKM) -/(muK _) Ds cfQuo_irr // -Ds cfker_Mod.
  have [s Ds]: exists s, muK j = 'Ind[M, HU] 'chi_s.
    rewrite /muK -(Dade_Ind_chi cycDDb) -cfIndMod // -mod_IirrE //.
    by set s := mod_Iirr _; exists s.
  split=> //; apply/seqIndP; exists s; rewrite // !inE andbC.
  rewrite -!(@sub_cfker_Ind_irr _ M) ?gFnorm // -Ds cfker_Mod //=.
  have{s Ds}[j1 Dj1]: exists j1 : Iirr W2, muK j = Dade_mu M [group of W] W1 j1.
    have:= (Dade_Ind_chi'_irr cycDD) s; set im_chi := codom _ => chi_s.
    suffices /imageP[j1 _ Dj1]: s \in im_chi.
      by exists j1; rewrite Ds Dj1 Dade_Ind_chi.
    by apply: contraR red_j => /chi_s[] /=; rewrite Ds.
  rewrite Dj1 -(Dade_Ind_chi cycDD) sub_cfker_Ind_irr ?gFnorm //.
  rewrite (not_cDade_core_sub_cfker_chi centDD) //.
  rewrite -(inj_eq (Dade_irr_inj cycDD)) -(inj_eq irr_inj) Dade_chi0 //.
  rewrite irr_eq1 -subGcfker -(sub_cfker_Ind_irr _ _ sHUM) ?gFnorm //.
  rewrite Dade_Ind_chi // -{j1}Dj1 cfker_Morph // subsetI sHUM /=.
  rewrite -sub_quotient_pre // -(Dade_Ind_chi cycDDb).
  rewrite sub_cfker_Ind_irr ?quotientS ?quotient_norms ?gFnorm // subGcfker.
  apply: contra nz_j; rewrite -(inj_eq (Dade_irr_inj cycDDb)) => /eqP->.
  by rewrite eq_sym -irr_eq1 Dade_chi0.
have [sH0HU sH0M] := (subset_trans sH0H sHHU, subset_trans sH0H (gFsub _ _)).
have sz_mu: size mu_ = p.-1.
  by rewrite -count_filter nb_redM ?(setIidPl sH0H) // /normal sH0M.
have s_muC_mu: {subset filter redM (S_ H0C) <= mu_}.
  move=> phi; rewrite /= !mem_filter => /andP[->]; apply: seqIndS.
  by rewrite setSD // Iirr_kerS ?joing_subl.
have UmuC: uniq (filter redM (S_ H0C)) by rewrite filter_uniq ?seqInd_uniq.
have [|Dmu _] := leq_size_perm UmuC s_muC_mu; last first.
  by split=> // phi; rewrite -Dmu mem_filter => /andP[].
have [nsH0C_M _ _ _] := nsH0xx_M.
have sHOC_HU: H0C \subset HU by rewrite join_subG sH0HU subIset ?sUHU.
rewrite sz_mu -count_filter nb_redM //.
rewrite /= norm_joinEr /=; last by rewrite astabQ setICA subsetIl.
by rewrite -group_modl //= setIC setIA tiHU setI1g mulg1.
Qed.

Let isIndHC (zeta : 'CF(M)) :=
  [/\ zeta 1%g = (q * u)%:R, zeta \in S_ H0C
    & exists2 xi : 'CF(HC), xi \is a linear_char & zeta = 'Ind xi].

(* This is Peterfalvi (9.8). *)
Lemma typeP_nonGalois_characters (not_Galois : ~~ typeP_Galois) :
    let a := #|U : 'C_U(sval (typeP_Galois_Pn not_Galois) | 'Q)| in
  [/\ (*a*) {in X_ H0, forall s, (a %| 'chi_s 1%g)%Cdiv},
      (*b*) size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j},
      (*c*) exists t, isIndHC 'chi_t
    & (*d*) let irr_qa := [pred zeta in irr M | zeta 1%g == (q * a)%:R] in
            let lb_n := (p.-1 * #|U|)%N in let lb_d := (a ^ 2 * #|U'|)%N in
            (lb_d %| lb_n /\ lb_n %/ lb_d <= count irr_qa (S_ H0U'))%N].
Proof.
case: (typeP_Galois_Pn _) => H1 [oH1 nH1U nH1Uq defHbar aP]; rewrite [sval _]/=.
move => a; case: aP; rewrite -/a => a_gt1 a_dv_p1 cycUb1 isoUb.
set part_a := ({in _, _}); pose HCbar := (HC / H0)%G.
have [_ /mulG_sub[sHUM sW1M] nHUW1 tiHUW1] := sdprodP defM.
have [nsHHU _ /mulG_sub[sHHU sUHU] nHU tiHU] := sdprod_context defHU.
have [nH0H nHHU] := (normal_norm nsH0H, normal_norm nsHHU).
have [sHHC sCU]: H \subset HC /\ C \subset U by rewrite joing_subl subsetIl.
have [nH0HU sCHU] := (subset_trans sHUM nH0M, subset_trans sCU sUHU).
have nsH0_HU: H0 <| HU by rewrite /normal (subset_trans sH0H).
have nH0C := subset_trans sCHU nH0HU.
have [nsH0C_M nsHC_M nsH0U'_M _] := nsH0xx_M; have [sHC_M _] := andP nsHC_M.
have nsH0HC: H0 <| HC := normalS (subset_trans sH0H sHHC) sHC_M nsH0M.
have defHCbar: Hbar \x (C / H0)%g = HCbar.
  rewrite /= quotientY //.
  rewrite quotientIG /= ?quotient_astabQ ?astabQ ?sub_cosetpre //.
  by rewrite dprodEY ?subsetIr //= setIA -quotientGI // tiHU quotient1 setI1g.
have sHC_HU: HC \subset HU by rewrite join_subG sHHU.
have nsHC_HU: HC <| HU := normalS sHC_HU sHUM nsHC_M.
have defHb1 := defHbar; rewrite (big_setD1 1%g) ?group1 ?conjsg1 //= in defHb1.
have [[_ H1c _ defH1c] _ _ _] := dprodP defHb1; rewrite defH1c in defHb1.
have [nsH1H _] := dprod_normal2 defHb1; have [sH1H nH1H] := andP nsH1H.
have nHW1: W1 \subset 'N(H) := subset_trans sW1M (gFnorm _ _).
have nHbW1: W1bar \subset 'N(Hbar) by rewrite quotient_norms.
have sH1wH w: w \in W1bar -> H1 :^ w \subset Hbar.
  by move/(normsP nHbW1) <-; rewrite conjSg.
have nsH1wHUb w: w \in W1bar -> H1 :^ w <| HU / H0.
  move=> W1w; rewrite -(normsP (quotient_norms _ nHUW1) w W1w) normalJ.
  rewrite /normal (subset_trans sH1H) ?quotientS //.
  by rewrite -defHU sdprodE // quotientMl // mulG_subG nH1H.
have nH1wHUb := normal_norm (nsH1wHUb _ _).
have abHbar: abelian Hbar := abelem_abelian abelHbar.  
have Part_a: part_a.
  move=> s; rewrite !inE => /andP[kers'H kersH0].
  have [t sHt] := constt_cfRes_irr H s; pose theta := ('chi_t / H0)%CF.
  have{kers'H} t_neq0: t != 0.
    by rewrite -subGcfker (sub_cfker_constt_Res_irr sHt).
  have{kersH0} kertH0: H0 \subset cfker 'chi_t.
    by rewrite (sub_cfker_constt_Res_irr sHt).
  have Ltheta: theta \is a linear_char.
    by rewrite /theta -quo_IirrE // (char_abelianP _ _). 
  have Dtheta : theta = cfBigdprod _ _ := cfBigdprod_lin defHbar Ltheta.
  set T := 'I_HU['chi_t]; have sHT: H \subset T by rewrite sub_inertia.
  have sTHU: T \subset HU by rewrite inertia_sub.
  suffices{s sHt} a_dv_iTHU: a %| #|HU : T|.
    rewrite -(inertia_Ind_invE nsHHU sHt) cfInd1 //.
    by rewrite dvdC_mulr ?dvdC_nat // Cint_Cnat ?Cnat_irr1.
  have /exists_inP[w W1w nt_t_w]: [exists w in W1bar, 'Res[H1 :^ w] theta != 1].
    rewrite -negb_forall_in; apply: contra t_neq0 => /forall_inP=> tH1w1.
    rewrite -irr_eq1 -(cfQuoK nsH0H kertH0) -/theta Dtheta.
    rewrite [cfBigdprod _ _]big1 ?rmorph1 // => w /tH1w1/eqP->.
    by rewrite /cfBigdprodi rmorph1.
  have defT: H ><| (U :&: T) = T.
    by rewrite (sdprod_modl defHU) // (setIidPr sTHU).
  have /irrP[k Dk]: 'Res theta \in irr (H1 :^ w).
    by rewrite lin_char_irr ?cfRes_lin_char.
  rewrite -divgS // -(sdprod_card defHU) -(sdprod_card defT) divnMl // divgI.
  rewrite -indexgI; have ->: a = #|U : 'C_U(H1 :^ w | 'Q)|.
    have [w1 nH0w1 W1w1 ->] := morphimP W1w; rewrite astabQ centJ morphpreJ //.
    by rewrite -astabQ indexgI -(normsP nUW1 _ W1w1) indexJg -indexgI.
  rewrite indexgS ?setIS // sub_astabQ ?(subset_trans sTHU) //= -inertia_Quo //.
  apply: subset_trans (sub_inertia_Res _ (nH1wHUb w W1w)) _.
  by rewrite Dk (inertia_irr_prime _ _ p_pr) ?subsetIr ?cardJg // -irr_eq1 -Dk.
pose isoJ := conj_isom H1; pose cfJ w i := 'chi_(Iirr_isom (isoJ w) i).
pose thetaH (f : {ffun _}) := cfBigdprod defHbar (fun w => cfJ w (f w)).
pose theta f := cfDprodl defHCbar (thetaH f).
have abH1: abelian H1 by rewrite cyclic_abelian ?prime_cyclic ?oH1.
have linH1 i: 'chi[H1]_i \is a linear_char by apply/char_abelianP.
have lin_thetaH f: thetaH f \is a linear_char.
  by apply: cfBigdprod_lin_char => w _; rewrite /cfJ Iirr_isomE cfIsom_lin_char.
have nz_thetaH f: thetaH f 1%g != 0 by rewrite lin_char_neq0.
have Dtheta f: {in W1bar & H1, forall w xb, theta f (xb ^ w) = 'chi_(f w) xb}.
  move=> w xb W1w H1xb /=; have sHHCb := quotientS H0 sHHC.
  transitivity ('Res[H1 :^ w] ('Res[Hbar] (theta f)) (xb ^ w)); last first.
    by rewrite cfDprodlK cfBigdprodKabelian // Iirr_isomE cfIsomE.
  by rewrite cfResRes ?sH1wH // cfResE ?memJ_conjg ?(subset_trans (sH1wH w _)).
have lin_theta f: theta f \is a linear_char by exact: cfDprodl_lin_char.
pose dom_theta := pffun_on (0 : Iirr H1) W1bar (predC1 0).
have inj_theta: {in dom_theta &, injective theta}.
  move=> f1 f2 /pffun_onP[/supportP W1f1 _] /pffun_onP[/supportP W1f2 _] eq_f12.
  apply/ffunP=> w.
  have [W1w | W1'w] := boolP (w \in W1bar); last by rewrite W1f1 ?W1f2.
  by apply/irr_inj/cfun_inP=> x H1x; rewrite -!Dtheta ?eq_f12.
have irr_thetaH0 f: (theta f %% H0)%CF \in irr HC.
  by have /lin_char_irr/irrP[k ->] := lin_theta f; apply: cfMod_irr.
have def_Itheta f: f \in dom_theta -> 'I_HU[theta f %% H0]%CF = HC.
  case/pffun_onP=> _ nz_fW1; apply/eqP; rewrite eqEsubset sub_inertia //.
  rewrite inertia_Mod_pre //= -{1}(sdprodW defHU) -group_modl; last first.
    rewrite (subset_trans sHHC) // -sub_quotient_pre ?normal_norm //.
    by rewrite sub_inertia ?quotientS.
  rewrite -gen_subG genM_join genS ?setUS ?setIS //= sub_astabQ subsetIl.
  rewrite cosetpreK centsC -{1}(bigdprodEY defHbar) gen_subG.
  apply/bigcupsP=> w W1w; rewrite centsC.
  apply: subset_trans (sub_inertia_Res _ (quotient_norms _ nHHU)) _.
  rewrite cfDprodlK inertia_bigdprod_abelian // subIset // orbC.
  rewrite (bigcap_min w) // (inertia_irr_prime _ _ p_pr) ?cardJg ?subsetIr //.
  apply: contra (nz_fW1 _ (image_f f W1w)).
  by rewrite -!irr_eq1 Iirr_isomE rmorph_eq1 //; apply: cfIsom_inj.
have irrXtheta f: f \in dom_theta -> 'Ind (theta f %% H0)%CF \in irr HU.
  move/def_Itheta; rewrite -(cfIirrE (irr_thetaH0 f)) => I_f_HC.
  by rewrite inertia_Ind_irr ?I_f_HC //.
pose Mtheta := [set cfIirr (theta f %% H0)%CF | f in dom_theta].
pose Xtheta := [set cfIirr ('Ind[HU] 'chi_t) | t in Mtheta].
pose ffH1 t := ~~ [exists w in W1bar, H1 :^ w \subset cfker ('chi[HC]_t / H0)].
have defMtheta: Mtheta = [set t | H0C \subset cfker 'chi_t & ffH1 t].
  apply/setP=> t; rewrite inE; apply/imsetP/andP=> [[f /pffun_onP[_ nzf] ->]|].
    rewrite /ffH1 cfIirrE ?cfModK // cfker_Morph ?normal_norm // subsetI; split.
      by rewrite genS ?setSU // -quotientYK ?morphpreS ?sub_cfker_Dprodl.
    rewrite negb_exists_in; apply/forall_inP=> w W1w.
    rewrite -subsetIidl -{2}(setIidPl (sH1wH w W1w)) -setIA.
    rewrite -!cfker_Res ?sH1wH ?quotientS ?cfRes_char ?lin_charW //.
    rewrite cfDprodlK cfBigdprodKabelian // Iirr_isomE cfker_Isom.
    by rewrite morphim_conj conjSg subsetIidl subGcfker [~~ _]nzf ?image_f.
  case=> /joing_subP[kerH0 kerC] ff_t.
  have [t1 Dt1]: exists t1, 'chi_t = (cfDprodl defHCbar 'chi_t1 %% H0)%CF.
    have /imageP[[t1 t2] _ Dt] := dprod_Iirr_onto defHCbar (quo_Iirr H0 t).
    rewrite -(cfQuoK nsH0HC kerH0) -quo_IirrE //= Dt dprod_IirrE in kerC *.
    exists t1; rewrite -cfDprod1r; congr (cfDprod _ _ _ %% H0)%CF; apply/eqP.
    rewrite cfker_Morph ?normal_norm // subsetI joing_subr /= in kerC.
    rewrite irr_eq1 -subGcfker cfkerEirr; apply/subsetP=> y Cy; rewrite inE.
    rewrite -(inj_eq (mulfI (irr1_neq0 t1))) -!(cfDprodE defHCbar) // !mul1g.
    by rewrite cfker1 // (subsetP _ y Cy) // sub_quotient_pre.
  pose f0 w := cfIsom (isom_sym (isoJ w)) ('Res 'chi_t1).
  pose f := [ffun w => if w \in W1bar then cfIirr (f0 w) else 0]; exists f.
    apply/familyP=> w; rewrite ffunE; case: ifP => W1w; rewrite !inE //.
    have /irrP[t2 Dt2]: 'Res 'chi_t1 \in irr (H1 :^ w).
      by rewrite lin_char_irr // cfRes_lin_char //; apply/char_abelianP.
    rewrite /f0 Dt2 -Iirr_isomE irrK -subGcfker Iirr_isomE cfker_Isom.
    rewrite morphim_restrm morphim_invmE -sub_morphim_pre // morphim_conj.
    rewrite setIid -Dt2 cfker_Res ?irr_char ?sH1wH // !subsetIidl.
    apply: contra ff_t => kerH1w; apply/exists_inP; exists w => //.
    rewrite (subset_trans kerH1w) // Dt1 cfModK //.
    by have /dprodP[_ /mulG_sub[]] := cfker_Dprodl defHCbar 'chi_t1.
  apply/irr_inj; rewrite cfIirrE // {t ff_t kerH0 kerC}Dt1.
  have /(cfBigdprod_lin defHbar) Dt1 := char_abelianP _ abHbar t1.
  congr (cfDprodl _ _ %% H0)%CF; rewrite Dt1; apply/eq_bigr=> w W1w.
  congr (cfBigdprodi _ _); rewrite /cfJ ffunE W1w.
  have /irrP[t2 Dt2]: 'Res 'chi_t1 \in irr (H1 :^ w).
    by rewrite lin_char_irr // cfRes_lin_char //; apply/char_abelianP.
  by rewrite /f0 Dt2 Iirr_isomE cfIirrE ?cfIsom_irr // cfIsomKV.
have oXtheta: (u * #|Xtheta| = p.-1 ^ q)%N.
  transitivity #|dom_theta|; last first.
    rewrite card_pffun_on cardC1 card_Iirr_abelian // oH1.
    rewrite -(card_isog (quotient_isog _ _)) ?oW1 ?(subset_trans sW1M) //.
    by apply/trivgP; rewrite -tiHUW1 setSI ?(subset_trans sH0H).
  rewrite Du -card_imset_Ind_irr ?card_in_imset //.
  - move=> f1 f2 Df1 Df2 /(congr1 (tnth (irr HC))); rewrite !{1}cfIirrE //.
    by move/(can_inj (cfModK nsH0HC)); apply: inj_theta.
  - by move=> _ /imsetP[f Df ->]; rewrite cfIirrE ?irrXtheta.
  move=> t y; rewrite /= !defMtheta !inE => /andP[kerH0C ker'H1w] HUy.
  rewrite /ffH1 conjg_IirrE -(cfConjgQuo _ nsHC_HU) //.
  have nHCy := subsetP (normal_norm nsHC_HU) y HUy.
  rewrite !cfker_conjg ?(subsetP (quotient_norm _ _)) ?mem_quotient //.
  rewrite -(normsP (normal_norm nsH0C_M) _ (subsetP sHUM y HUy)) conjSg.
  rewrite kerH0C (contra _ ker'H1w) // => /exists_inP[w W1w kerH1].
  apply/exists_inP; exists w => //; rewrite -(conjSg _ _ (inMb y)).
  by rewrite (normsP (normal_norm (nsH1wHUb w W1w))) ?mem_quotient.
have sXthXH0C: Xtheta \subset X_ H0C.
  apply/subsetP=> _ /imsetP[t th_t ->]; have [f Df Dt] := imsetP th_t.
  rewrite !inE cfIirrE; last by rewrite Dt cfIirrE ?irrXtheta.
  rewrite !sub_cfker_Ind_irr ?(subset_trans sHUM) ?normal_norm ?gFnormal //.
  rewrite defMtheta inE in th_t; have [kerH0C /contra-> // kerH] := andP th_t.
  apply/exists_inP; exists 1%g; rewrite ?(subset_trans (sH1wH _ _)) ?group1 //.
  by rewrite cfker_Quo ?quotientS //; case/joing_subP: kerH0C.
pose mu_f (i : Iirr H1) := [ffun w => if w \in W1bar then i else 0].
have Dmu_f (i : Iirr H1): i != 0 -> mu_f i \in dom_theta.
  move=> nz_i; apply/pffun_onP; split=> [|_ /imageP[w W1w ->]].
    by apply/supportP=> w W1'w; rewrite ffunE (negPf W1'w).
  by rewrite ffunE W1w.
pose mk_mu i := 'Ind[HU] (theta (mu_f i) %% H0)%CF.
have sW1_Imu i: W1 \subset 'I_M[theta (mu_f i) %% H0]%CF.
  apply/subsetP=> w W1w; have Mw := subsetP sW1M w W1w; rewrite inE Mw.
  have nHC_W1 := subset_trans sW1M (normal_norm nsHC_M).
  rewrite (subsetP nHC_W1) ?(cfConjgMod _ nsHC_M) //; apply/eqP.
  have W1wb: inMb w \in W1bar by rewrite mem_quotient.
  rewrite cfConjgDprodl ?(subsetP _ _ W1wb) ?quotient_norms //; last first.
    by rewrite (subset_trans (joing_subr U W1)) ?normal_norm.
  congr (cfDprodl _ _ %% H0)%CF.
  apply/cfun_inP=> _ /(mem_bigdprod defHbar)[x [H1x -> _]].
  have Hx w1: w1 \in W1bar -> x w1 \in Hbar.
    by move=> W1w1; rewrite (subsetP (sH1wH w1 _)) ?H1x.
  rewrite !lin_char_prod ?cfConjg_lin_char //; apply/eq_bigr=> w1 W1w1.
  rewrite cfConjgE ?(subsetP nHbW1) //.
  have W1w1w: (w1 * (inMb w)^-1)%g \in W1bar by rewrite !in_group.
  rewrite -(cfResE _ (sH1wH _ W1w1w)) -?mem_conjg -?conjsgM ?mulgKV ?H1x //.
  rewrite -(cfResE _ (sH1wH _ W1w1)) ?H1x ?cfBigdprodKabelian //.
  rewrite !ffunE W1w1 W1w1w -[x w1](conjgKV w1) -conjgM !Iirr_isomE.
  by rewrite !cfIsomE -?mem_conjg ?H1x.
have inj_mu: {in predC1 0 &, injective (fun i => cfIirr (mk_mu i))}.
  move=> i1 i2 nz_i1 nz_i2 /(congr1 (tnth (irr HU))).
  rewrite !{1}cfIirrE ?irrXtheta ?Dmu_f // /mk_mu.
  do 2![move/esym; rewrite -{1}(cfIirrE (irr_thetaH0 _))].
  move/(cfclass_Ind_irrP _ _ nsHC_HU); rewrite !{1}cfIirrE //.
  case/cfclassP=> _ /(mem_sdprod defHU)[x [y [Hx Uy -> _]]].
  rewrite (cfConjgM _ nsHC_HU) ?(subsetP sHHU x) ?(subsetP sUHU) //.
  rewrite (inertiaJ (subsetP (sub_inertia _  sHC_M) x _)) ?(subsetP sHHC) //.
  move=> {x Hx} Dth1.
  suffices /inertiaJ: y \in 'I_HU[theta (mu_f i2) %% H0]%CF.
    rewrite -Dth1 => /(can_inj (cfModK nsH0HC))/inj_theta/ffunP/(_ 1%g).
    by rewrite !ffunE group1 => -> //; apply: Dmu_f.
  rewrite def_Itheta ?Dmu_f //= (subsetP (joing_subr _ _)) //.
  have nCy: y \in 'N(C).
    by rewrite (subsetP (normal_norm nsCUW1)) ?mem_gen ?inE ?Uy.
  have [_ _ /trivgPn[wb W1wb ntwb] _ _] := Frobenius_context frobUW1c.
  have /morphimP[w nCw W1w Dw] := W1wb.
  rewrite coset_idr //; apply/set1P; rewrite -set1gE; apply: wlog_neg => nty.
  rewrite -((Frobenius_reg_ker frobUW1c) wb); last by rewrite !inE ntwb.
  rewrite inE mem_quotient //= -/C; apply/cent1P/commgP.
  rewrite Dw -morphR //= coset_id //.
  suffices: [~ y, w] \in U :&: HC.
    rewrite /= norm_joinEr 1?subIset ?nHU // -group_modr ?subsetIl //=.
    by rewrite setIC tiHU mul1g.
  have Uyw: [~ y, w] \in U; last rewrite inE Uyw.
    by rewrite {1}commgEl groupMl ?groupV // memJ_norm ?(subsetP nUW1) // Uy.
  rewrite -(def_Itheta _ (Dmu_f _ nz_i1)) inE /= andbA -in_setI.
  rewrite (setIidPl (normal_norm nsHC_HU)).
  rewrite (subsetP sUHU) //= Dth1 -(cfConjgM _ nsHC_HU) ?(subsetP sUHU) //.
  have My: y \in M := subsetP (der_sub _ _) y (subsetP sUHU y Uy).
  rewrite mulKVg (cfConjgM _ nsHC_M) ?in_group // ?(subsetP sW1M w) //.
  have /inertiaJ->:= subsetP (sW1_Imu i2) _ (groupVr W1w).
  rewrite (cfConjgM _ nsHC_M) ?(subsetP sW1M w) // -Dth1.
  by have /inertiaJ-> := subsetP (sW1_Imu i1) w W1w.
pose Xmu := [set cfIirr (mk_mu i) | i in predC1 0].
have def_IXmu: {in Xmu, forall s, 'I_M['chi_s] = M}.
  move=> _ /imsetP[i nz_i ->]; apply/eqP; rewrite eqEsubset.
  rewrite {1}['I_M[_]%CF]setIdE subsetIl /=.
  rewrite -{1}defM sdprodE ?(subset_trans sW1M) ?gFnorm // mulG_subG.
  rewrite !{1}cfIirrE ?irrXtheta ?Dmu_f // sub_inertia ?gFsub //=.
  exact: subset_trans (sub_inertia_Ind _ (der_normal _ M)).
pose Smu := [seq 'Ind[M] 'chi_s | s in Xmu].
have sSmu_mu: {subset Smu <= mu_}.
  move=> _ /imageP[s Xmu_s ->]; rewrite mem_filter /=.
  rewrite irrEchar induced_prod_index ?gFnormal // def_IXmu //.
  rewrite -(sdprod_index defM) (eqC_nat _ 1) gtn_eqF ?prime_gt1 // andbF.
  rewrite mem_seqInd ?gFnormal /normal ?(subset_trans sH0H) ?gFsub //=.
  suffices /(subsetP sXthXH0C): s \in Xtheta.
    by apply: subsetP; rewrite setSD // Iirr_kerS ?joing_subl.
  have /imsetP[i nz_i ->] := Xmu_s; rewrite /Xtheta -imset_comp.
  by apply/imsetP; exists (mu_f i); rewrite /= ?cfIirrE ?Dmu_f.
have ResIndXmu: {in Xmu, forall s, 'Res ('Ind[M] 'chi_s) = q%:R *: 'chi_s}.
  move=> s /def_IXmu Imu_s; rewrite induced_sum_rcosets ?gFnormal ?Imu_s //.
  by rewrite -(sdprod_index defM) -Imu_s cfclass_inertia big_seq1.
have uSmu: uniq Smu.
  apply/dinjectiveP=> s1 s2 Xs1 Xs2 /(congr1 'Res[HU]); rewrite !ResIndXmu //.
  by move/(can_inj (scalerK (neq0CG W1)))/irr_inj.
have sz_Smu: size Smu = p.-1.
  by rewrite size_map -cardE card_in_imset // cardC1 card_Iirr_abelian ?oH1.
have [sz_mu s_mu_H0C] := nb_redM_H0.
have Dmu: Smu =i mu_.
  by have [|//] := leq_size_perm uSmu sSmu_mu; rewrite sz_mu sz_Smu.
split=> {Part_a part_a}//.
- split=> // phi mu_phi; have S_HOC_phi := s_mu_H0C _ mu_phi.
  move: mu_phi; rewrite -Dmu => /imageP[_ /imsetP[i nz_i ->]].
  rewrite cfIirrE ?irrXtheta ?Dmu_f // => Dphi.
  split=> //; rewrite Dphi ?cfInd1 ?cfIndInd //.
    rewrite -(sdprod_index defM) -/q -Du mulrA -natrM.
    by rewrite lin_char1 1?cfMod_lin_char ?mulr1.
  by exists (theta (mu_f i) %% H0)%CF; rewrite 1?cfMod_lin_char.
- have /eqVproper: Xmu \subset Xtheta.
    apply/subsetP=> _ /imsetP[i nz_i ->]; rewrite -[Xtheta]imset_comp /=.
    by apply/imsetP; exists (mu_f i); rewrite /= ?cfIirrE ?Dmu_f.
  case=> [defXmu | /andP[_ /subsetPn[s theta_s Xmu'_s]]]; last first.
    have [_ /imsetP[f Dth_f ->] Ds] := imsetP theta_s; rewrite cfIirrE // in Ds.
    have /irrP[t Dt]: 'Ind 'chi_s \in irr M; last 1 [exists t; rewrite -{t}Dt].
      apply: contraR Xmu'_s => red_Ind_s.
      have: 'Ind 'chi_s \in mu_.
        rewrite mem_filter /= red_Ind_s mem_seqInd ?gFnormal //=.
        apply: subsetP theta_s; rewrite (subset_trans  sXthXH0C) ?setSD //.
        by rewrite Iirr_kerS ?joing_subl.
      rewrite -Dmu => /imageP[s1 Xmu_s1] /(congr1 (cfdot ('Ind 'chi_s1)))/eqP.
      rewrite induced_prod_index ?gFnormal // eq_sym -cfdot_Res_l.
      rewrite ResIndXmu // cfdotZl cfdot_irr -natrM mulnC.
      by case: (s1 =P s) => [<- // | _] /idPn[]; apply: neq0CiG.
    split; first 2 [by rewrite mem_seqInd ?gFnormal ?(subsetP sXthXH0C)].
      rewrite Ds cfIirrE ?irrXtheta ?cfInd1 // -Du -(sdprod_index defM) -/q.
      by rewrite mulrA -natrM lin_char1 ?cfMod_lin_char ?mulr1.
    exists (theta f %% H0)%CF; first by rewrite cfMod_lin_char.
    by rewrite Ds  cfIirrE ?irrXtheta //= cfIndInd.
  suffices /(congr1 odd): u = (p.-1 ^ q.-1)%N.
    rewrite odd_exp -(subnKC (prime_gt1 pr_q)) /= -subn1 odd_sub ?prime_gt0 //.
    by rewrite -oH1 (oddSg sH1H) ?quotient_odd // mFT_odd.
  have p1_gt0: (0 < p.-1)%N by rewrite -(subnKC (prime_gt1 p_pr)).
  apply/eqP; rewrite -(eqn_pmul2r p1_gt0) -expnSr prednK ?prime_gt0 //. 
  by rewrite -oXtheta -defXmu card_in_imset // cardC1 card_Iirr_abelian ?oH1.
clear Xmu def_IXmu Smu sSmu_mu ResIndXmu uSmu sz_Smu sz_mu s_mu_H0C Dmu.
clear Xtheta ffH1 defMtheta oXtheta sXthXH0C mu_f Dmu_f mk_mu sW1_Imu inj_mu.
clear lin_theta dom_theta inj_theta irr_thetaH0 def_Itheta irrXtheta Mtheta.
clear lin_thetaH nz_thetaH theta Dtheta => irr_qa lb_n lb_d.
have sU'U: U' \subset U := der_sub 1 U.
have nH0U := subset_trans sUHU nH0HU; have nH0U' := subset_trans sU'U nH0U.
have sU'CH1: U' \subset 'C_U(H1 | 'Q).
  by rewrite subsetI sU'U sub_astabQ nH0U' (centsS sH1H) ?quotient_cents.
have sCH1_U: 'C_U(H1 | 'Q) \subset U := subsetIl U _.
have dvd_lb: lb_d %| lb_n.
  rewrite -[lb_d]mulnA dvdn_mul // -(Lagrange sCH1_U).
  by rewrite mulnC dvdn_pmul2r ?cardSg ?indexg_gt0.
split; rewrite ?leq_divLR // /lb_n -(Lagrange sCH1_U) -/a -(Lagrange sU'CH1).
rewrite mulnCA -mulnA mulnC !mulnA !leq_pmul2r ?cardG_gt0 ?indexg_gt0 // mulnC.
pose H1CH1 := (H1 <*> 'C_(U / H0)(H1))%G; pose HCH1 := (H <*> 'C_U(H1 | 'Q))%G.
have defH1CH1: H1 \x 'C_(U / H0)(H1) = H1CH1.
  rewrite dprodEY ?subsetIr ?coprime_TIg ?(coprimeSg sH1H) //.
  by rewrite (coprimegS (subsetIl _ _)) ?coprime_morph.
have sHCH1_HU: HCH1 \subset HU by rewrite join_subG sHHU (subset_trans sCH1_U).
have nsHCH1_HU: HCH1 <| HU.
  rewrite /normal sHCH1_HU -(sdprodW defHU) mulG_subG normsG ?joing_subl //=.
  by rewrite normsY // sub_der1_norm.
have nsH0_HCH1: H0 <| HCH1.
  by rewrite (normalS _ sHCH1_HU) // (subset_trans sH0H) ?joing_subl.
have nsH1cHU: H1c <| HU / H0.
  rewrite -(bigdprodEY defH1c) /normal gen_subG norms_gen ?andbT //.
    by apply/bigcupsP=> w /setD1P[_ /nsH1wHUb/andP[]].
  by apply/norms_bigcup/bigcapsP=> w /setD1P[_ /nH1wHUb].
have defHCH1: H1c ><| H1CH1 = (HCH1 / H0)%G.
  have /sdprodP[_ /mulG_sub[sH1cH _] nH1cH1 tiH1cH1] := dprodWsdC defHb1.
  rewrite sdprodE /= -(dprodW defH1CH1).
  - rewrite mulgA (dprodWC defHb1) -morphim_setIpre -astabQ -quotientMl //.
    by rewrite norm_joinEr // (subset_trans sCH1_U).
  - rewrite mul_subG ?subIset // (subset_trans (quotientS _ sUHU)) //.
    exact: normal_norm nsH1cHU.
  rewrite -(setIidPl sH1cH) setIAC -setIA -group_modl // coprime_TIg ?mulg1 //.
  by rewrite coprime_sym (coprimegS (subsetIl _ _)) ?coprime_morph.
have [nsH1cHCH1 sH1CH1_HCH1 _ nH1cH1C _] := sdprod_context defHCH1.
pose dom_lam := ('C_(U / H0)(H1) / (U' / H0))%G.
pose lam (j : Iirr dom_lam) := 'chi_(mod_Iirr j).
pose theta i j := cfSdprod defHCH1 (cfDprod defH1CH1 'chi_i (lam j)).
have nsU'CH1: U' <| 'C_U(H1 | 'Q) by rewrite (normalS _ sCH1_U) ?gFnormal.
have nsU'CH1b: U' / H0 <| 'C_(U / H0)(H1).
  by rewrite -morphim_setIpre -astabQ quotient_normal.
have lam_ab: abelian dom_lam.
  by rewrite sub_der1_abelian //= quotient_der ?dergS ?subsetIl.
have lam_lin j: lam j \is a linear_char.
  by rewrite /lam mod_IirrE ?cfMod_lin_char //; apply/char_abelianP.
have theta_lin i j: theta i j \is a linear_char.
  by rewrite cfSdprod_lin_char ?cfDprod_lin_char.
have <-: #|dom_lam|%g = #|'C_U(H1 | 'Q) : U'|.
  rewrite -card_quotient ?normal_norm //= /= -morphim_setIpre -astabQ.
  have nsU'U : U' <| U by apply: der_normal.
  rewrite -(restrmEsub _ _ sCH1_U) -(restrm_cosetE _ sU'U) -morphim_quotm.
  rewrite card_injm ?quotientS ?injm_quotm ?(isom_inj (quotient_isom _ _)) //.
  by rewrite coprime_TIg ?(coprimeSg sH0H).
pose Mtheta := [set mod_Iirr (cfIirr (theta i j)) | i in [set~ 0], j in setT].
have ->: (p.-1 * #|dom_lam|)%N = #|Mtheta|.
  rewrite [Mtheta]curry_imset2X card_imset ?cardsX => [|[i1 j1] [i2 j2] /=/eqP].
    by rewrite cardsC1 cardsT !card_Iirr_abelian ?(abelianS sH1H) ?oH1.
  rewrite (can_eq (mod_IirrK _)) // -(inj_eq irr_inj) !cfIirrE ?lin_char_irr //.
  rewrite (can_eq (cfSdprodK _)) -!dprod_IirrE (inj_eq irr_inj).
  by rewrite (can_eq (dprod_IirrK _)) => /eqP[->] /(can_inj (mod_IirrK _))->.
have{lam_lin} thetaH1 i j: 'Res[H1] (theta i j) = 'chi_i.
  rewrite -(cfResRes _ _ sH1CH1_HCH1) ?joing_subl // cfSdprodK -['Res _]scale1r.
  by rewrite -invr1 -(lin_char1 (lam_lin j)) cfDprodKl ?irr1_neq0.
have Itheta r: r \in Mtheta -> 'I_HU['chi_r]%CF = HCH1.
  case/imset2P=> i j; rewrite /= in_setC1 => nz_i _ Dr; apply/eqP.
  rewrite eqEsubset sub_inertia //= Dr mod_IirrE // cfIirrE ?lin_char_irr //.
  rewrite -(quotientSGK _ (normal_sub nsH0_HCH1)); last first.
    by rewrite (subset_trans (inertia_sub _ _)).
  rewrite andbT inertia_Mod_quo //.
  apply: subset_trans (sub_inertia_Res _ (nH1wHUb _ (group1 _))) _.
  rewrite /= conjsg1 thetaH1 (inertia_irr_prime _ _ p_pr) //.
  rewrite -morphim_setIpre -astabQ quotientS // -{1}(sdprodW defHU).
  by rewrite -genM_join sub_gen // group_modl // sub_astabQ nH0H (centsS sH1H).
have irr_Xtheta: {in Mtheta, forall r, 'Ind[HU] 'chi_r \in irr HU}.
  by move=> r Mr; rewrite /= inertia_Ind_irr ?Itheta.
pose Xtheta := [set cfIirr ('Ind[HU] 'chi_r) | r in Mtheta].
have Da: a = #|HU : HCH1| by rewrite -(index_sdprodr defHU).
have Xtheta_1: {in Xtheta, forall s, 'chi_s 1%g = a%:R}.
  move=> _ /imsetP[r Mr ->]; have /imset2P[i j _ _ Dr] := Mr.
  rewrite cfIirrE ?irr_Xtheta ?cfInd1 //= -Da lin_char1 ?mulr1 //.
  by rewrite Dr mod_IirrE ?cfMod_lin_char // cfIirrE ?lin_char_irr.
have nsH0U'HU: H0U' <| HU.
  by apply: normalS nsH0U'_M; rewrite // -(sdprodWY defHU) genS ?setUSS.
have sXthetaXH0U': Xtheta \subset X_ H0U'.
  apply/subsetP=> _ /imsetP[r Mr ->]; have [i j nz_i _ Dr] := imset2P Mr.
  rewrite !inE cfIirrE ?irr_Xtheta ?sub_cfker_Ind_irr //= ?normal_norm //.
  rewrite Dr mod_IirrE // cfIirrE ?lin_char_irr // join_subG andbCA.
  rewrite {1}cfker_Mod //= cfker_Morph ?normal_norm // subsetI joing_subl.
  rewrite -sub_quotient_pre // subsetI (subset_trans sU'CH1) ?joing_subr //=.
  rewrite -sub_quotient_pre //; apply/andP; split; last first.
    rewrite -(sdprodW (sdprod_cfker _ _)) (subset_trans _ (mulG_subr _ _)) //.
    apply: subset_trans (subset_trans (joing_subr _ _) (cfker_Dprod _ _ _)).
    by rewrite /lam mod_IirrE ?cfker_Mod.
  apply: contraL nz_i => /(subset_trans sH1H); rewrite !inE negbK.
  rewrite -subsetIidl -cfker_Res ?thetaH1 ?subGcfker ?lin_charW //.
  by rewrite (subset_trans sH1H) ?quotientS ?joing_subl.
have nsCH1_U: 'C_U(H1 | 'Q) <| U by rewrite sub_der1_normal.
have nH1cU: (U / H0)%g \subset 'N(H1c).
  rewrite -(bigdprodEY defH1c) norms_gen ?norms_bigcup //.
  apply/bigcapsP=> w /setD1P[_ W1w].
  by rewrite normJ -sub_conjgV (normsP (quotient_norms H0 nUW1)) ?groupV.
have ->: #|Mtheta| = (#|Xtheta| * a)%N.
  rewrite Da mulnC -card_imset_Ind_irr // => _ xy /imset2P[i j nz_i _ ->].
  case/(mem_sdprod defHU)=> x [y [Hx Uy -> _]]; have HUy := subsetP sUHU y Uy.
  pose yb := inMb y; have Uyb: yb \in (U / H0)%g by rewrite mem_quotient.
  pose iy := conjg_Iirr i yb; pose jy := conjg_Iirr j (coset (U' / H0)%g yb).
  apply/imset2P; exists iy jy; rewrite !inE ?conjg_Iirr_eq0 // in nz_i *.
  apply: irr_inj; have HCH1x: x \in HCH1 by rewrite mem_gen ?inE ?Hx.
  rewrite conjg_IirrE (cfConjgM _ nsHCH1_HU) ?(subsetP sHHU x) {Hx}//.
  rewrite (inertiaJ (subsetP (sub_inertia _ (subxx _)) x _)) {x HCH1x}//.
  rewrite !{1}mod_IirrE // !{1}cfIirrE ?lin_char_irr //.
  rewrite cfConjgMod_norm ?(subsetP nH0U) ?(subsetP (normal_norm nsHCH1_HU)) //.
  have nCH1_Ub: (U / H0)%g \subset 'N('C_(U / H0)(H1)).
    by rewrite normsI ?normG ?norms_cent.
  rewrite cfConjgSdprod ?cfConjgDprod ?(subsetP _ _ Uyb) ?normsY //.
  rewrite /theta /lam !{1}mod_IirrE // !{1}conjg_IirrE.
  by rewrite cfConjgMod_norm ?(subsetP _ _ Uyb) // quotient_norms ?gFnorm.
rewrite leq_pmul2r ?indexg_gt0 // cardE -(size_map (fun s => 'Ind[M] 'chi_s)).
have kerH1c s: s \in Xtheta -> H1c \subset (cfker 'chi_s / H0)%g.
  case/imsetP=> r Mr ->; have [i j _ _ Dr] := imset2P Mr.
  rewrite -(setIidPr (normal_sub nsH1cHCH1)) -morphim_setIpre quotientS //.
  rewrite cfIirrE ?irr_Xtheta ?sub_cfker_Ind_irr //; last first.
    by rewrite normsI ?normal_norm // -(quotientGK nsH0_HU) cosetpre_normal.
  rewrite Dr mod_IirrE // cfker_Morph ?normal_norm // cfIirrE ?lin_char_irr //.
  by rewrite setIS ?joing_subl ?morphpreS // cfker_Sdprod.
have injXtheta:
  {in M & Xtheta &, forall w s1 s2, 'chi_s1 = 'chi_s2 ^ w -> w \in HU}%CF.
- move=> _ s1 s2 /(mem_sdprod defM)[y [w [HUy W1w -> _]]] Xs1 Xs2.
  rewrite groupMl // cfConjgMnorm ?(subsetP (normG _) y) ?(subsetP nHUW1) //.
  rewrite (inertiaJ (subsetP (sub_inertia _ (subxx _)) y HUy)) {y HUy} => Ds1.
  have nH0w: w \in 'N(H0) by rewrite ?(subsetP nH0M) ?(subsetP sW1M).
  rewrite (subsetP (normal_sub nsH0_HU)) // coset_idr //.
  have /setDP[]:= subsetP sXthetaXH0U' s1 Xs1; rewrite !inE join_subG /=.
  case/andP=> kerH0s1 _; apply: contraNeq; rewrite -eq_invg1 => ntw.
  rewrite -(quotientSGK nH0H) // -(dprodW defHb1) mul_subG ?kerH1c //=.
  rewrite Ds1 cfker_conjg ?(subsetP nHUW1) // quotientJ // -sub_conjgV.
  rewrite (subset_trans _ (kerH1c s2 Xs2)) // -(bigdprodEY defH1c) sub_gen //.
  by rewrite (bigcup_max (inMb w)^-1%g) // !inE ntw groupV mem_quotient.
rewrite count_filter uniq_leq_size //.
  apply/dinjectiveP=> s1 s2 Xs1 Xs2.
  case/(cfclass_Ind_irrP _ _ (der_normal 1 M))/cfclassP=> y My Ds2.
  suffices /inertiaJ: y \in 'I_M['chi_s2]%CF by rewrite -Ds2 => /irr_inj.
  by rewrite (subsetP (sub_inertia _ _)) ?(injXtheta y s1 s2).
move=> _ /imageP[s Xs ->]; rewrite mem_filter /= cfInd1 // -(sdprod_index defM).
rewrite Xtheta_1 // -natrM eqxx mem_seqInd ?gFnormal //.
rewrite (subsetP sXthetaXH0U') // !andbT inertia_Ind_irr ?gFnormal //.
by apply/subsetP=> y /setId2P[My _ /eqP/esym/injXtheta->].
Qed.

Lemma dvdn_pred_predX n e : n.-1 %| (n ^ e).-1.
Proof. by rewrite binomial.predn_exp dvdn_mulr. Qed.

Import ssrnum Num.Theory.

(* This is Peterfalvi (9.9); we have exported the fact that HU / H0 is a      *)
(* Frobenius group in case (c), as this is directly used in (9.10).           *)
Lemma typeP_Galois_characters (is_Galois : typeP_Galois) :
  [/\ (*a*) {in X_ H0, forall s, (u %| 'chi_s 1%g)%Cx},
            {in X_ H0C', forall s, 'chi_s 1%g = u%:R /\
             (exists2 xi : 'CF(HC), xi \is a linear_char & 'chi_s = 'Ind xi)},
      (*b*) size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j}
    & (*c*) all redM (S_ H0C') ->
            [/\ C = 1%g, u = (p ^ q).-1 %/ p.-1
              & [Frobenius HU / H0 = Hbar ><| (U / H0)]%g]].
Proof.
have [F [phi [psi _ [Kpsi phiJ]]]] := typeP_Galois_P is_Galois.
case=> [oF /isomP[inj_phi im_phi] phiW2] [cycUbar co_u_p1 u_dv_pq1].
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have [nsH0C_M nsHC_M _ nsH0C'_M] := nsH0xx_M; have nH0H := normal_norm nsH0H.
have nsH0HU: H0 <| HU := normalS (subset_trans sH0H sHHU) sHUM nsH0M.
have nH0U: U \subset 'N(H0) := subset_trans sUHU (normal_norm nsH0HU).
have sCU: C \subset U := subsetIl U _; have nH0C := subset_trans sCU nH0U.
have sH0C_HU: H0C \subset HU by rewrite -(sdprodWY defHU) genS ?setUSS.
have nsH0C_HU: H0C <| HU := normalS sH0C_HU sHUM nsH0C_M.
have nH0C_HU := normal_norm nsH0C_HU.
have [coH0U coHC] := (coprimeSg sH0H coHU, coprimegS sCU coHU).
have [nH0C_H nH0C_U] := (subset_trans sHHU nH0C_HU, subset_trans sUHU nH0C_HU).
have tiHOC_H: H0C :&: H = H0.
  by rewrite /= norm_joinEr // -group_modl // setIC coprime_TIg ?mulg1.
have{coH0U} tiHOC_U: H0C :&: U = C.
  by rewrite /= norm_joinEr // setIC -group_modr // setIC coprime_TIg ?mul1g.
have isoHbar: Hbar \isog (H / H0C)%g.
  by have:= second_isog nH0C_H; rewrite tiHOC_H.
have isoUbar: Ubar \isog (U / H0C)%g.
  by have:= second_isog nH0C_U; rewrite tiHOC_U.
have defHUbar: ((H / H0C) ><| (U / H0C) = HU / H0C)%g.
  exact: quotient_coprime_sdprod.
have frobHU: [Frobenius HU / H0C = (H / H0C) ><| (U / H0C)]%g.
  apply/Frobenius_semiregularP=> //; first by rewrite -(isog_eq1 isoHbar).
    by rewrite -(isog_eq1 isoUbar); have [] := Frobenius_context frobUW1c.
  move=> yb /setD1P[ntyb /morphimP[y nH0Cy Uy] Dyb] /=; rewrite Dyb.
  apply/trivgP/subsetP=> _ /setIP[/morphimP[/= x nHOCx Hx ->] /cent1P/commgP].
  rewrite -morphR //; set xy := [~ x, y] => /eqP/coset_idr/=H0Cxy.
  have [nH0x nH0y] := (subsetP nH0H x Hx, subsetP nH0U y Uy).
  rewrite inE coset_id ?mem_gen // inE coset_idr //; apply: contraNeq ntyb.
  rewrite -(morph_injm_eq1 inj_phi) ?mem_quotient // => nz_x.
  rewrite {yb}Dyb /= coset_id ?mem_gen // -Kpsi !inE Uy orbC /= -val_eqE.
  rewrite -(inj_eq (mulfI nz_x)) mulr1 -[_ * _]phiJ ?mem_quotient // qactJ nH0y.
  rewrite -morphJ // conjg_mulR -/xy mkerr ?eqxx // ker_coset -tiHOC_H inE.
  by rewrite andbC groupM ?groupV ?memJ_norm ?(subsetP nHU) //= H0Cxy ?groupR.
have I_XH0_C i: i != 0 -> 'I_HU['chi[Hbar]_i %% H0]%CF = HC.
  move=> /= nz_i; apply/eqP; rewrite eqEsubset join_subG sub_inertia //= andbC.
  have{nz_i} [j nz_j Dj]: exists2 j : Iirr (H / H0C),
    j != 0 & {in H, forall x, 'chi_i (inMb x) = 'chi_j (coset H0C x)}.
  - have[] := second_isom nH0C_H; rewrite /= tiHOC_H => h injh Dh.
    have isoH: isom Hbar (H / H0C)%g h by apply/isomP; rewrite Dh.
    exists (Iirr_isom isoH i) => [|x Hx]; last rewrite Iirr_isomE.
      by rewrite -!irr_eq1 -(can_eq (cfIsomK isoH)) rmorph1 Iirr_isomE in nz_i*.
    have Hxb: inMb x \in Hbar by rewrite mem_quotient.
    suffices /set1P <-: h (inMb x) \in [set coset H0C x] by rewrite cfIsomE.
    rewrite -quotient_set1 ?(subsetP nH0C_H) // -Dh ?sub1set // mem_morphim //.
    by rewrite quotient_set1 ?(subsetP nH0H) ?inE.
  apply/andP; do [split; apply/subsetP] => [y /setIP[Uy] | xy Ixy].
    rewrite astabQ => /morphpreP[nH0y /centP cHby].
    have nHy := subsetP nHU y Uy.
    rewrite inE nHy (subsetP sUHU) //=; apply/eqP/cfun_inP=> /= x Hy.
    rewrite cfConjgE ?cfModE ?memJ_norm ?morphJ ?groupV // ?(subsetP nH0H) //=.
    by rewrite morphV // /conjg invgK mulgA cHby ?mem_quotient ?mulgK.
  have [/(mem_sdprod defHU)[x [y [Hx Uy Dxy _]]] _] := setIdP Ixy.
  have [nH0y nHOCy] := (subsetP nH0U y Uy, subsetP nH0C_U y Uy).
  rewrite {xy}Dxy groupMl ?(subsetP (sub_inertia _ _) x) //= in Ixy *.
  rewrite -genM_join mem_gen ?mem_mulg {x Hx}//= -/C.
  rewrite -tiHOC_U inE Uy andbT coset_idr //.
  have [nHy [_ _ _ tiHUbar]] := (subsetP nHU y Uy, sdprodP defHUbar).
  set yb := coset H0C y; have nHyb: yb \in 'N(H / H0C).
    by rewrite (subsetP (quotient_norm _ _)) ?mem_quotient.
  apply/set1P; rewrite -set1gE -tiHUbar inE -groupV andbC.
  rewrite -(inertia_Frobenius_ker (FrobeniusWker frobHU) nz_j).
  rewrite inE !groupV nHyb !{1}mem_quotient ?(subsetP sUHU) //=.
  apply/eqP/cfun_inP=> _ /morphimP[x nH0Cx Hx ->]; rewrite cfConjgE ?groupV //=.
  by rewrite invgK -morphJ -?Dj -?cfModE ?memJ_norm // (inertia_valJ _ Ixy).
have{coHC} tiHbC: (Hbar :&: C / H0 = 1)%g by rewrite coprime_TIg ?coprime_morph.
have{tiHbC} defHCbar: (Hbar \x (C / H0) = HC / H0)%g.
  by rewrite dprodEY ?quotientY // -quotient_astabQ quotientS ?subsetIr.
have sHCHU: HC \subset HU by rewrite -(sdprodWY defHU) genS ?setUS.
have nsHCHC: HC <| HU := normalS sHCHU sHUM nsHC_M.
have sH0HC: H0 \subset HC := subset_trans sH0H (joing_subl H C).
have nsH0HC: H0 <| HC := normalS sH0HC sHCHU nsH0HU.
have{I_XH0_C} irr_IndHC r: r \in Iirr_kerD HC H H0 -> 'Ind 'chi_r \in irr HU.
  rewrite !inE => /andP[ker'H kerH0]; apply: inertia_Ind_irr => //.
  apply: subset_trans (sub_inertia_Res _ (normal_norm nsHHU)) _.
  rewrite -{kerH0}(quo_IirrK _ kerH0) // mod_IirrE // in ker'H *.
  have /imageP[[i j] _ Dr] := dprod_Iirr_onto defHCbar (quo_Iirr H0 r).
  rewrite {r}Dr dprod_IirrE cfResMod ?joing_subl //= in ker'H *.
  rewrite (canRL (scalerKV _) (cfDprodKl defHCbar _ _)) ?irr1_neq0 //.
  rewrite linearZ inertia_scale_nz ?irr1_neq0 ?I_XH0_C //.
  apply: contraNneq ker'H => ->; rewrite irr0 cfDprod1l.
  rewrite cfker_Morph ?normal_norm // subsetI joing_subl /=.
  by rewrite -sub_quotient_pre ?sub_cfker_Dprodr.
have [nb_mu H0C_mu] := nb_redM_H0; set part_a' := ({in X_ H0C', _}).
have Part_a s: s \in X_ H0 -> exists r, 'chi_s = 'Ind[HU, HC] 'chi_r.
  rewrite !inE => /andP[Ks'H KsH0]; have [r sHCr] := constt_cfRes_irr HC s.
  have{KsH0} KrH0: H0 \subset cfker 'chi_r.
    by rewrite (sub_cfker_constt_Res_irr sHCr) // ?normal_norm.
  have{Ks'H} Kr'H: ~~ (H \subset cfker 'chi_r).
    by rewrite (sub_cfker_constt_Res_irr sHCr) ?joing_subl // ?normal_norm.
  have [|s1 Ds1] := irrP _ (irr_IndHC r _); first by rewrite !inE Kr'H.
  rewrite -constt_Ind_constt_Res Ds1 constt_irr inE in sHCr.
  by rewrite (eqP sHCr) -Ds1; exists r.
have Part_a': part_a'.
  move=> s /setDP[KsH0C' Ks'H]; have [|r Ds] := Part_a s.
    by rewrite inE Ks'H (subsetP (Iirr_kerS _ _) _ KsH0C') ?joing_subl.
  suffices lin_r: 'chi_r \is a linear_char.
    by split; [rewrite Du Ds cfInd1 ?lin_char1 ?mulr1 | exists 'chi_r].
  have KrH0C': H0C' \subset cfker 'chi_r.
    rewrite inE Ds sub_cfker_Ind_irr // in KsH0C'.
    by rewrite (subset_trans sHUM) ?normal_norm.
  rewrite lin_irr_der1 (subset_trans _ KrH0C') //=.
  have nH0HC := normal_norm nsH0HC.
  rewrite (norm_joinEr (subset_trans (der_sub 1 _) nH0C)).
  rewrite -quotientSK ?(subset_trans (der_sub 1 _)) ?quotient_der //= -/C.
  have [_ _ _ tiHCbar] := dprodP defHCbar; rewrite dprodEcprod // in defHCbar.
  by rewrite -(der_cprod 1 defHCbar) (derG1P (abelem_abelian abelHbar)) cprod1g.
split=> // [s /Part_a[r ->] | | {Part_a' part_a'}red_H0C'].
- by rewrite Du cfInd1 // dvdC_mulr // Cint_Cnat ?Cnat_irr1.
- split=> // mu_j /H0C_mu H0C_mu_j; have [s XH0Cs Dmuj] := seqIndP H0C_mu_j.
  have [|s1u [xi lin_xi Ds]] := Part_a' s.
    by rewrite (subsetP _ _ XH0Cs) ?Iirr_kerDS // genS ?setUS ?der_sub.
  split=> //; first by rewrite Dmuj cfInd1 // s1u -natrM -(sdprod_index defM).
  by rewrite Dmuj Ds cfIndInd //; exists xi.
have C1: C = 1%g.
  apply: contraTeq red_H0C' => ntC; apply/allPn.
  have sCM: C \subset M := subset_trans (joing_subr H C) (normal_sub nsHC_M).
  have{sCM} solCbar: solvable (C / H0)%g.
    by rewrite quotient_sol ?(solvableS sCM) ?mmax_sol.
  have [|{ntC solCbar} j lin_j nz_j] := solvable_has_lin_char _ solCbar.
    rewrite -(isog_eq1 (quotient_isog _ _)) ?(subset_trans sCU) //.
    by rewrite coprime_TIg ?(coprimegS sCU) ?(coprimeSg sH0H).
  have [i lin_i nz_i] := solvable_has_lin_char ntHbar solHbar.
  pose r := mod_Iirr (dprod_Iirr defHCbar (i, j)).
  have KrH0: H0 \subset cfker 'chi_r by rewrite mod_IirrE ?cfker_Mod.
  have Kr'H: ~~ (H \subset cfker 'chi_r).
    rewrite -subsetIidl -cfker_Res ?joing_subl ?irr_char // mod_IirrE //.
    rewrite cfResMod ?joing_subl ?cfker_Morph ?subsetIidl -?sub_quotient_pre //.
    rewrite -['Res _]scale1r -invr1 -(lin_char1 lin_j) dprod_IirrE.
    by rewrite cfDprodKl ?irr1_neq0 // subGcfker -irr_eq1.
  have [|s Ds] := irrP _ (irr_IndHC r _); first by rewrite !inE Kr'H.
  have Ks'H: s \notin Iirr_ker HU H.
    by rewrite inE -Ds sub_cfker_Ind_irr ?normal_norm.
  exists ('Ind 'chi_s).
    rewrite mem_seqInd ?gFnormal // inE Ks'H inE -Ds.
    rewrite sub_cfker_Ind_irr // ?(subset_trans sHUM) ?normal_norm //=.
    rewrite mod_IirrE ?cfker_Morph ?normal_norm // subsetI.
    rewrite genS ?setUSS ?der_sub //.
    rewrite -sub_quotient_pre // ?(subset_trans (normal_sub nsH0C'_M)) //.
    rewrite quotientYidl ?(subset_trans (der_sub 1 _)) ?quotient_der //= -/C.
    rewrite (subset_trans (dergS 1 (quotientS H0 (joing_subr H C)))) //=.
    by rewrite -lin_irr_der1 dprod_IirrE cfDprod_lin_char.
  apply: contra nz_j => red_j; have /implyP := H0C_mu ('Ind 'chi_s).
  rewrite mem_filter red_j !mem_seqInd ?gFnormal // !in_setD Ks'H !inE -Ds.
  rewrite !sub_cfker_Ind_irr ?(normal_norm nsH0HU) //.
  rewrite join_subG {1 2}mod_IirrE 1?cfker_Mod //=.
  rewrite -subsetIidl -cfker_Res ?irr_char ?joing_subr //.
  rewrite mod_IirrE // dprod_IirrE cfResMod ?joing_subr //.
  rewrite -['Res _]scale1r -invr1 -(lin_char1 lin_i) cfDprodKr ?irr1_neq0 //.
  by rewrite cfker_Morph // subsetIidl -sub_quotient_pre // subGcfker irr_eq1.
rewrite /= -/C C1 joingG1 in frobHU; split=> //; move/FrobeniusWker in frobHU.
have nsHbHU: Hbar <| (HU / H0)%g by rewrite quotient_normal.
have ->: (p ^ q).-1 = (#|X_ H0| * u)%N.
  rewrite -oF -cardsT -im_phi card_injm //.
  rewrite -(card_Iirr_abelian (abelem_abelian abelHbar)) -(cardsC1 0).
  rewrite (card_imset_Ind_irr nsHbHU) => [|i|i y]; last first.
  - by rewrite !inE conjg_Iirr_eq0.
  - by rewrite !inE => nz_i; rewrite inertia_Ind_irr ?inertia_Frobenius_ker.
  rewrite index_quotient_eq ?(subset_trans sHUM) ?subIset ?sH0H ?orbT //.
  apply/eqP; rewrite Du /= C1 joingG1 mulnC eqn_pmul2r //.
  rewrite -(card_imset _ (can_inj (mod_IirrK _))) // -imset_comp.
  apply/eqP/eq_card=> s; apply/imsetP/idP=> [[i nz_i -> /=] | Xs].
    rewrite !inE mod_IirrE 1?{1}cfker_Mod // andbT in nz_i *.
    rewrite cfIirrE ?inertia_Ind_irr ?inertia_Frobenius_ker //.
    rewrite cfker_Morph ?normal_norm // subsetI sHHU -sub_quotient_pre //=.
    rewrite sub_cfker_Ind_irr ?quotientS ?quotient_norms ?normal_norm //.
    by rewrite subGcfker.
  have [[]] := (Part_a s Xs, setDP Xs).
  rewrite /= C1 joingG1 !inE => r Ds [kerH0s].
  have:= kerH0s; rewrite Ds !sub_cfker_Ind_irr ?normal_norm // => kerH0 ker'H.
  exists (quo_Iirr H0 r).
    by rewrite !inE -subGcfker quo_IirrE // cfker_Quo ?quotientSGK.
  by rewrite quo_IirrE // cfIndQuo // -Ds -quo_IirrE // irrK quo_IirrK.
suffices ->: #|X_ H0| = p.-1 by rewrite -(subnKC (prime_gt1 p_pr)) mulKn.
rewrite -nb_mu (size_red_subseq_seqInd_typeP (filter_subseq _ _)); last first.
  by move=> xi; rewrite mem_filter => /andP[].
apply/esym/eq_card => i; rewrite inE mem_filter mem_seqInd ?gFnormal //.
rewrite andb_idl // => Xi; rewrite (allP red_H0C') //.
by rewrite mem_seqInd ?gFnormal //= C1 (trivgP (der_sub 1 _)) joingG1.
Qed.

(* This is Peterfalvi (9.10), formulated as a constructive alternative. *)
Lemma typeP_reducible_core_cases :
  {t : Iirr M & 'chi_t \in S_ H0C' /\ 'chi_t 1%g = (q * u)%:R
              & {xi | xi \is a linear_char & 'chi_t = 'Ind[M, HC] xi}}
  + [/\ typeP_Galois, [Frobenius HU / H0 = Hbar ><| (U / H0)]%g,
        cyclic U, #|U| = (p ^ q).-1 %/ p.-1
      & FTtype M == 2 -> [Frobenius HU = H ><| U]].
Proof.
have [GalM | Gal'M] := boolP typeP_Galois; last first.
  pose eqInHCb nu r := ('chi_r \is a linear_char) && (nu == 'Ind[M, HC] 'chi_r).
  pose isIndHCb (nu : 'CF(M)) :=
    (nu 1%g == (q * u)%:R) && [exists r, eqInHCb nu r].
  suffices /sig2W[t H0C't]: exists2 t, 'chi_t \in S_ H0C' & isIndHCb 'chi_t.
    case/andP=> /eqP t1qu /exists_inP/sig2W[r lin_r /eqP def_t].
    by left; exists t => //; exists 'chi_r.
  have [_ _ [t [t1qu H0Ct [xi lin_xi def_t]]] _] :=
    typeP_nonGalois_characters Gal'M.
  exists t.
    by apply: seqIndS H0Ct; rewrite Iirr_kerDS ?genS // setUS ?der_sub.
  apply/andP; rewrite t1qu def_t; split=> //; apply/exists_inP.
  by have /irrP[r Dxi] := lin_char_irr lin_xi; exists r; rewrite -Dxi.
have [_ IndHC_SH0C' _] := typeP_Galois_characters GalM; rewrite all_predC.
case: hasP => [/sig2W[eta H0C'eta /irrP/sig_eqW[t Dt]] _ | _ [//|C1 <- frobHU]].
  have /sig2_eqW[s /IndHC_SH0C'[s1u /sig2_eqW[xi lin_xi Ds]] Deta]
    := seqIndP H0C'eta.
  have [/mulG_sub[sHUM _] mulHU] := (sdprodW defM, sdprodW defHU).
  left; exists t; [split | exists xi]; rewrite -?Dt // Deta.
    by rewrite cfInd1 // -(sdprod_index defM) s1u -natrM.
  by rewrite Ds cfIndInd //= -genM_join gen_subG /= -mulHU mulgS ?subsetIl.
have cycU: cyclic U.
  rewrite (isog_cyclic (quotient1_isog _)) -C1.
  by have [_ _ []] := typeP_Galois_P GalM.
right; split=> //; first by rewrite /u /Ubar C1 -(card_isog (quotient1_isog _)).
case/(compl_of_typeII MtypeP) => // _ _ _ UtypeF <-.
have [_ -> _] := typeF_context UtypeF.
by apply/forall_inP=> S /and3P[_ /cyclicS->].
Qed.

Import ssrint.

(* This is Peterfalvi (9.11) *)
Lemma Ptype_core_coherence : coherent (S_ H0C') M^# tau.
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have nsCU: C <| U := normalS (subsetIl _ _) (joing_subl _ _) nsCUW1.
have [sCU nCU] := andP nsCU; have sC'C: C^`(1)%g \subset C := der_sub 1 _.
have coHC := coprimegS sCU coHU; have coH0C := coprimeSg sH0H coHC.
have [nsH0C_M nsHC_M nsH0U'_M nsH0C'_M] := nsH0xx_M; have [_ nH0H]:= andP nsH0H.
have nH0HU := subset_trans sHUM nH0M; have nH0U := subset_trans sUHU nH0HU.
have nH0C := subset_trans sCU nH0U; have nH0C' := subset_trans sC'C nH0C.
have sHCHU: HC \subset HU by rewrite join_subG sHHU (subset_trans sCU).
have [nsHCHC nHC] := (normalS sHCHU sHUM nsHC_M, subset_trans sCU nHU).
have tiHCbar: Hbar :&:(C / H0)%g = 1%g by rewrite coprime_TIg ?coprime_morph.
have defHCbar: Hbar \x (C / H0)%g = (HC / H0)%g.
  by rewrite dprodEY ?quotientY // -quotient_astabQ quotientS ?subsetIr.
have abHbar := abelem_abelian abelHbar.
have{tiHCbar} defHC'bar: (HC / H0)^`(1)%g = (C^`(1) / H0)%g.
  by rewrite -(der_dprod 1 defHCbar) (derG1P abHbar) dprod1g quotient_der.
have sU'U := der_sub 1 U; have nH0U' := subset_trans sU'U nH0U.
have sU'C: U' \subset C by rewrite subsetI sub_astabQ sU'U nH0U' quotient_cents.
have uS0: uniq (S_ H0C') by exact: seqInd_uniq.
have [rmR scohM]: exists R : 'CF(M) -> seq 'CF(G), subcoherent (S_ H0C') tau R.
  move: (FTtypeP_coh_base _ _) (FTtypeP_subcoherent maxM MtypeP) => R scohR.
  exists R; apply: (subset_subcoherent scohR); split=> //; last first.
    exact: cfAut_seqInd.
  by apply: seqIndS; rewrite Iirr_kerDS ?sub1G //= /M`_\s; case: ifP.
have [GalM | Gal'M] := boolP typeP_Galois.
  have [_ XOC'u _ _] := typeP_Galois_characters GalM.
  apply: uniform_degree_coherence scohM _.
  apply: all_pred1_constant (#|M : HU| * u)%:R _ _; rewrite all_map.
  by apply/allP=> _ /seqIndP[s /XOC'u[s1u _] ->] /=; rewrite natrM cfInd1 ?s1u.
have:= typeP_nonGalois_characters Gal'M.
set U1 := 'C_U(_ | _); set a := #|_ : _|.
case: (_ Gal'M) => /= H1 [oH1 nH1U _ defHbar aP] in U1 a *.
rewrite -/U1 -/a in aP; case: aP => a_gt1 a_dv_p1 cycU1 _.
case=> [a_dv_XH0 [nb_mu IndHCmu] has_irrHC lb_Sqa]; rewrite -[S_ _]/(S_ H0C').
have defHb1 := defHbar; rewrite (big_setD1 1%g) ?group1 ?conjsg1 //= in defHb1.
have [[_ H1c _ defH1c] _ _ _] := dprodP defHb1; rewrite defH1c in defHb1.
have [nsH1H _] := dprod_normal2 defHb1; have [sH1H _] := andP nsH1H.
have nsU1U: U1 <| U; last have [sU1U nU1U] := andP nsU1U.
  by rewrite norm_normalI // astabQ norm_quotient_pre ?norms_cent.
have Da: a = #|HU : H <*> U1|.
  rewrite /a -!divgS /= ?join_subG ?sHHU ?norm_joinEr ?(subset_trans sU1U) //=.
  by rewrite -(sdprod_card defHU) coprime_cardMg ?(coprimegS sU1U) ?divnMl.
have a_dv_u: a %| u by rewrite Da Du indexgS // genS ?setUS // setIS ?astabS.
have [a_gt0 q_gt0 u_gt0 p1_gt0]: [/\ 0 < a, 0 < q, 0 < u & 0 < p.-1]%N.
  rewrite !cardG_gt0 ltnW // -subn1 subn_gt0 prime_gt1 //.
have [odd_p odd_q odd_a]: [/\ odd p, odd q & odd a].
  by rewrite mFT_odd -oH1 (oddSg sH1H) ?(dvdn_odd a_dv_u) ?mFT_quo_odd.
have Dp: p = (2 * p.-1./2 + 1)%N.
  by rewrite mul2n -[p]odd_double_half odd_p half_double addn1.
(* Start of main proof. *)
pose S1 := filter [pred zeta : 'CF(M) | zeta 1%g == (q * a)%:R] (S_ H0C').
have ntS1: (0 < size S1)%N.
  have [lb_dv lbS1] := lb_Sqa; apply: leq_trans (leq_trans lbS1 _).
    by rewrite ltn_divRL // mul0n muln_gt0 p1_gt0 cardG_gt0.
  rewrite count_filter uniq_leq_size ?filter_uniq ?seqInd_uniq // => chi.
  rewrite !mem_filter -andbA /= => /and3P[_ ->].
  by apply: seqIndS; rewrite Iirr_kerDS // genS ?setUS ?dergS ?subsetIl.
have uccS1: [/\ uniq S1, {subset S1 <= S_ H0C'} & conjC_closed S1].
  split=> [||chi]; first by rewrite filter_uniq.
    by apply: mem_subseq; apply: filter_subseq.
  rewrite !mem_filter !inE cfunE => /andP[/eqP <- S0chi].
  by rewrite cfAut_seqInd // andbT conj_Cnat ?(Cnat_seqInd1 S0chi).
have cohS1: coherent S1 M^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohM uccS1) _.
  by apply: all_pred1_constant (q * a)%:R _ _; rewrite all_map filter_all.
pose S3 := filter [predC S1] (S_ H0C'); move: {2}_.+1 (ltnSn (size S3)) => nS. 
move: @S3 (uccS1) (cohS1); have: {subset S1 <= S1} by [].
elim: nS {-1}S1 => // nS IHnS S2 => sS12 S3 uccS2 cohS2; rewrite ltnS => leS3nS.
have [ntS3|] := boolP (size S3 > 0)%N; last first.
  rewrite -count_filter -has_count has_predC negbK => /allP sS02.
  exact: subset_coherent sS02 cohS2.
(* Ultimateley we'll contradict the maximality of S2 in (9.11.1) & (9.11.8). *)
suff [chi]: exists2 chi, chi \in S3 & coherent (chi :: chi^* ::S2)%CF M^# tau.
  rewrite mem_filter => /andP[/= S2'chi S0chi]; have[uS2 sS20 ccS2] := uccS2.
  move/IHnS; apply=> [psi /sS12 S1psi||]; first by rewrite 2?mem_behead.
    rewrite /= !inE negb_or S2'chi (contra (ccS2 _)) ?cfConjCK // eq_sym.
    split; first by rewrite (seqInd_conjC_neq _ _ _ S0chi) ?mFT_odd.
     by apply/allP; rewrite /= S0chi cfAut_seqInd //=; apply/allP.
    apply/allP; rewrite /= !inE cfConjCK !eqxx orbT /=.
    by apply/allP=> psi /ccS2; rewrite !inE orbA orbC => ->.
  apply: leq_trans leS3nS; rewrite ltnNge; apply: contra S2'chi.
  case/leq_size_perm=> [|psi|/(_ chi)]; first by rewrite filter_uniq.
    by rewrite !mem_filter !inE orbA negb_or -andbA => /andP[].
  by rewrite !mem_filter !inE eqxx S0chi !andbT => /esym/negbFE.
(* This is step (9.11.1). *) clear nS IHnS leS3nS.
without loss [[eqS12 irrS1 H0C_S1] [Da_p defC] [S3qa ne_qa_qu] [oS1 oS1ua]]:
  / [/\ [/\ S1 =i S2, {subset S1 <= irr M} & {subset S1 <= S_ H0C}],
        a = p.-1./2 /\ C = U',
        (forall chi, chi \in S3 -> chi 1%g == (q * u)%:R) /\ (q * u != q * a)%N
      & size S1 = (p.-1 * u %/ a ^ 2)%N /\ size S1 = (2 * u %/ a)%N].
- move=> IHwlog; have [[uS2 sS20 ccS2] [uS1 _ _]] := (uccS2, uccS1).
  pose is_qu := [pred chi : 'CF(M) | chi 1%g == (q * u)%:R].
  pose isn't_qu := [pred chi | is_qu chi ==> all is_qu S3].
  have /hasP[chi S3chi qu'chi]: has isn't_qu S3.
    rewrite /isn't_qu; have [_|] := boolP (all _ _); last by rewrite has_predC. 
    by rewrite (eq_has (fun _ => implybT _)) has_predT.
  have [S2'chi S0chi]: chi \notin S2 /\ chi \in S_ H0C'.
    by apply/andP; rewrite mem_filter in S3chi.
  have [s X0C's Dchi] := seqIndP S0chi.
  have Dchi1: chi 1%g = q%:R * 'chi_s 1%g.
    by rewrite Dchi cfInd1 // -(sdprod_index defM).
  (* We'll show lb0 <= lb1 <= lb <= lb3 <= sumnS S1' <= sumnS S2 <= lb0,   *)
  (* with equality under conditions that imply the conclusion of (9.11.1). *)
  pose lb0 := (2 * q * a)%:R * chi 1%g.
  pose lb1 : algC := (2 * a * q ^ 2 * u)%:R.
  pose lb2 : algC := (p.-1 * q ^ 2 * u)%:R.
  pose lb3 : algC := (p.-1 * q ^ 2 * #|U : U'|)%:R.
  pose S1' := filter [predI irr M & S_ H0U'] S1.
  pose szS1' := ((p.-1 * #|U : U'|) %/ a ^ 2)%N; set lbS1' := _ %/ _ in lb_Sqa.
  pose Snorm (psi : 'CF(M)) := psi 1%g ^+ 2 / '[psi].
  pose sumnS Si := \sum_(psi <- Si) Snorm psi.
  have lb01: lb0 <= lb1 ?= iff (chi 1%g == (q * u)%:R).
    rewrite /lb1 mulnA -mulnA natrM /lb0 mulnAC mono_lerif; last first.
      by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 a_gt0.
    apply: lerif_eq; rewrite Dchi1 natrM ler_pmul2l ?gt0CG //.
    have [KsH0C' _] := setDP X0C's; rewrite inE in KsH0C'.
    have [t sHCt] := constt_cfRes_irr HC s.
    have KtH0C': H0C' \subset cfker 'chi_t.
      apply: subset_trans (cfker_constt (cfRes_char _ (irr_char s)) sHCt).
      by rewrite cfker_Res ?irr_char // subsetI genS ?setUSS.
    rewrite -constt_Ind_constt_Res in sHCt.
    apply: ler_trans (char1_ge_constt (cfInd_char _ (irr_char t)) sHCt) _.
    rewrite cfInd1 // -Du lin_char1 ?mulr1 // lin_irr_der1.
    apply: subset_trans KtH0C'; rewrite /= (norm_joinEr nH0C') /= -/C.
    rewrite -quotientSK ?(subset_trans (der_sub _ _)) ?(subset_trans sHCHU) //.
    by rewrite -defHC'bar quotient_der ?(subset_trans sHCHU).
  have lb12: lb1 <= lb2 ?= iff (a == p.-1./2).
    rewrite -(@eqn_pmul2l 2) // -(canLR (addnK 1) Dp) subn1 lerif_nat.
    rewrite !(mono_leqif (fun _ _ => leq_pmul2r _)) ?expn_gt0 ?q_gt0 //.
    apply: leqif_eq; rewrite dvdn_leq // Gauss_dvd //.
       by rewrite {1}Dp addn1 dvdn_mulr.
    by rewrite prime_coprime ?dvdn2 ?negbK.
  have lb23: lb2 <= lb3 ?= iff (C == U') :> algC.
    rewrite lerif_nat [u]card_quotient //.
    rewrite (mono_leqif (fun _ _ => leq_pmul2l _)) ?muln_gt0 ?p1_gt0 ?q_gt0 //.
    rewrite -(mono_leqif (fun _ _ => leq_pmul2l (cardG_gt0 C))) Lagrange //.
    rewrite -(Lagrange sU'U) (mono_leqif (fun _ _ => leq_pmul2r _)) //.
    by rewrite eq_sym; apply: subset_leqif_cards.
  have lb3S1': lb3 <= sumnS S1' ?= iff (size S1' == szS1').
    rewrite /szS1' -(divnMr (cardG_gt0 U')) mulnAC -mulnA Lagrange // -/lbS1'.
    have{lb_Sqa} [dv_lb lbSqa] := lb_Sqa; rewrite [sumnS S1']big_seq.
    rewrite (eq_bigr (fun _ => ((q * a) ^ 2)%:R)) => [|psi]; last first.
      rewrite !mem_filter -!andbA => /and4P[/irrP[r ->] _ /=/eqP r1qa _].
      by rewrite /Snorm cfnorm_irr divr1 r1qa natrX.
    rewrite -big_seq (big_nth 0) -natr_sum sum_nat_const_nat subn0.
    rewrite mulnC natrM [*%R]lock /lb3 natrM natf_indexg ?der_sub // mulrA.
    rewrite -natrM mulnAC -(divnK dv_lb) mulnAC mulnA natrM mulfK ?neq0CG //.
    rewrite -/lbS1' -mulnA -expnMn natrM mulrC -lock mono_lerif; last first.
      by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 a_gt0 q_gt0.
    rewrite eq_sym lerif_nat; apply: leqif_eq; rewrite (leq_trans lbSqa) //.
    rewrite count_filter uniq_leq_size ?filter_uniq ?seqInd_uniq // => psi.
    rewrite !mem_filter -!andbA /= => /and3P[-> -> S0psi]; rewrite S0psi.
    by apply: seqIndS S0psi; rewrite Iirr_kerDS //= genS ?setUS ?dergS.
  have lbS1'2: sumnS S1' <= sumnS S2 ?= iff ~~ has [predC S1'] S2.
    have Ds2: perm_eq S2 (S1' ++ filter [predC S1'] S2).
      rewrite -(perm_filterC (mem S1')) perm_cat2r.
      rewrite uniq_perm_eq ?filter_uniq // => psi.
      by rewrite mem_filter andb_idr //= mem_filter => /andP[_ /sS12].
    rewrite [sumnS S2](eq_big_perm _ Ds2) big_cat /= -/(sumnS S1') big_filter.
    rewrite -all_predC -big_all_cond !(big_tnth _ _ S2) big_andE.
    rewrite -{1}[_ S1']addr0 mono_lerif; last exact: ler_add2l.
    set sumS2' := \sum_(i | _) _; rewrite -[0]/(sumS2' *+ 0) -sumrMnl.
    apply: lerif_sum => i _; apply/lerifP; rewrite lt0r !mulf_eq0 invr_eq0.
    set psi := tnth _ i; have Spsi := sS20 psi (mem_tnth _ _).
    rewrite !negb_or (seqInd1_neq0 _ Spsi) //= (cfnorm_seqInd_neq0 _ Spsi) //=.
    by rewrite divr_ge0 ?exprn_ge0 ?cfnorm_ge0 ?Cnat_ge0 ?(Cnat_seqInd1 Spsi).
  have [lb0S2 | ] := boolP (lb0 < sumnS S2).
    exists chi => //; have /hasP[xi S1xi _]: has predT S1 by rewrite has_predT.
    have xi1: xi 1%g = (q * a)%:R.
      by rewrite mem_filter in S1xi; have [/eqP] := andP S1xi.
    apply: ((extend_coherent scohM) _ xi) => //; first by rewrite S0chi sS12.
    split=> //; last by rewrite mulrAC xi1 -natrM mulnA.
    rewrite xi1 Dchi1 irr1_degree -natrM dvdC_nat dvdn_pmul2l ?cardG_gt0 //.
    rewrite -dvdC_nat /= !nCdivE -irr1_degree a_dv_XH0 //.
    by rewrite (subsetP (Iirr_kerDS _ _ _) _ X0C's) ?joing_subl.
  have lb1S2 := lerif_trans lb12 (lerif_trans lb23 (lerif_trans lb3S1' lbS1'2)).
  rewrite ltr_neqAle !(lerif_trans lb01 lb1S2) andbT has_predC !negbK.
  case/and5P=> /eqP chi1qu /eqP Da_p /eqP defC /eqP sz_S1' /allP sS21'.
  have defS1': S1' = S1.
    apply/eqP; rewrite -(geq_leqif (size_subseq_leqif (filter_subseq _ S1))).
    by rewrite uniq_leq_size // => psi /sS12/sS21'.
  apply: IHwlog; split=> //.
  + split=> psi; do 1?[rewrite -defS1' mem_filter andbC => /and3P[_ _] //=].
      by apply/idP/idP=> [/sS12 | /sS21']; rewrite ?defS1'.
    by congr (_ \in S_ _); apply/group_inj; rewrite /= defC.
  + split; first by apply/allP; apply: contraLR qu'chi; rewrite /= chi1qu eqxx.
    rewrite -eqC_nat -chi1qu; apply: contra S2'chi => chi1qa.
    by rewrite sS12 // mem_filter /= chi1qa.
  rewrite -defS1' sz_S1' /szS1' -defC -card_quotient // -/u.
  by split=> //; rewrite -mulnn {1}Dp addn1 -Da_p mulnAC divnMr.
have nCW1: W1 \subset 'N(C).
  by rewrite (subset_trans (joing_subr U W1)) ?normal_norm.
(* This is step (9.11.2). *) clear uccS2 cohS2 sS12 has_irrHC lb_Sqa sU'C.
have [tiU1 le_u_a2]: {in W1^#, forall w, U1 :&: U1 :^ w = C} /\ (u <= a ^ 2)%N.
  have tiU1 w: w \in W1^# -> U1 :&: U1 :^ w = C; last split => //.
    case/setD1P=> ntw W1w; have nH0w := subsetP (subset_trans sW1M nH0M) w W1w.
    pose wb := coset H0 w; have W1wb: wb \in W1bar^#.
      rewrite !inE mem_quotient ?(contraNneq _ ntw) // => /coset_idr H0w.
      rewrite -in_set1 -set1gE -tiHUW1 inE (subsetP sHHU) // (subsetP sH0H) //.
      by rewrite H0w.
    have [ntH1 abH1]: H1 :!=: 1%g /\ abelian H1.
      by rewrite -cardG_gt1 cyclic_abelian ?prime_cyclic ?prime_gt1 // oH1.
    have [t1 lin_t nz_t1] := solvable_has_lin_char ntH1 (abelian_sol abH1).
    pose theta1 := cfDprodl defHb1 'chi_t1.
    pose theta := (cfDprodl defHCbar (theta1 * (theta1 ^ wb)%CF))%CF.
    have lin_theta : theta \is a linear_char.
      by rewrite !(cfDprodl_lin_char, cfConjg_lin_char, rpredM).
    have KthC: (C / H0)%g \subset cfker theta.
      rewrite cfkerEchar ?lin_charW //; apply/subsetP=> y Cy; rewrite inE.
      rewrite (subsetP _ _ Cy) ?quotientS ?joing_subr //.
      rewrite -(mul1g 1%g) -(mul1g y) !cfDprodEl ?group1 //=.
    have [_ nsCbHC] := dprod_normal2 defHCbar.
    pose toHUb2 A := ((A / H0) / (C / H0))%g.
    have /irrP[t2 Dt2] := lin_char_irr lin_theta.
    have nsH2HU: toHUb2 HC <| toHUb2 HU by rewrite !quotient_normal.
    pose t2b : Iirr (toHUb2 HC) := quo_Iirr [group of C / H0]%g t2.
    have [s2 t2HUs2] := constt_cfInd_irr t2b (normal_sub nsH2HU).
    pose s2T := inertia_Ind_inv t2b 'chi_s2.
    have defIt: 'I_(toHUb2 HU)['chi_t2b] = toHUb2 (U1 :&: U1 :^ w) <*> toHUb2 HC.
      apply/eqP; rewrite eqEsubset join_subG sub_inertia ?quotientS //.
      rewrite andbT sub_gen.
        apply/subsetP=> yb /morphimP[_ _ /morphimP[y _ /setIP[U1y U1wy] ->] Dyb].
        have Uy := subsetP sU1U y U1y.
        have HUyb: yb \in toHUb2 HU by rewrite Dyb !mem_quotient ?(subsetP sUHU).
        have nHCyb: yb \in 'N(toHUb2 HC) by rewrite (subsetP _ _ HUyb) ?normal_norm.
        rewrite inE HUyb nHCyb; apply/eqP/cfun_inP=> xb HCxb.
Admitted.


End Nine.
