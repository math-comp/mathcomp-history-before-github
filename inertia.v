(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice div.
Require Import fintype tuple finfun bigop prime ssralg ssrnum finset fingroup.
Require Import morphism perm automorphism quotient action zmodp cyclic center.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import gproduct frobenius.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file contains the definitions and properties of inertia groups:       *)
(*   (phi ^ y)%CF == the y-conjugate of phi : 'CF(G), i.e., the class         *)
(*                   function mapping x ^ y to phi x provided y normalises G. *)
(*                   We take (phi ^ y)%CF = phi when y \notin 'N(G).          *)
(*  (phi ^: G)%CF == the sequence of all distinct conjugates of phi : 'CF(H)  *)
(*                   by all y in G.                                           *)
(*        'I[phi] == the inertia group of phi : CF(H), i.e., the set of y     *)
(*                   such that (phi ^ y)%CF = phi AND H :^ y = y.             *)
(*      'I_G[phi] == the inertia group of phi in G, i.e., G :&: 'I[phi].      *)
(* conjg_Iirr i y == the index j : Iirr G such that ('chi_i ^ y)%CF = 'chi_j. *)
(* cfclass_Iirr G i == the image of G under conjg_Iirr i, i.e., the set of j  *)
(*                   such that 'chi_j \in ('chi_i ^: G)%CF.                   *)
(*     detRepr rG == the linear character afforded by the determinant of rG.  *)
(*      cfDet phi == the linear character afforded by the determinant of a    *)
(*                   representation affording phi.                            *)
(*        'o(phi) == the "determinential order" of phi (the multiplicative    *)
(*                   order of cfDet phi.                                      *)
(******************************************************************************)

Reserved Notation "''I[' phi ]"
  (at level 8, format "''I[' phi ]").
Reserved Notation "''I_' G [ phi ]"
  (at level 8, G at level 2, format "''I_' G [ phi ]").

Section ConjDef.

Variables (gT : finGroupType) (B : {set gT}) (y : gT) (phi : 'CF(B)).
Local Notation G := <<B>>.

Fact cfConjg_subproof :
  is_class_fun G [ffun x => phi (if y \in 'N(G) then x ^ y^-1 else x)].
Proof.
apply: intro_class_fun => [x z _ Gz | x notGx].
  have [nGy | _] := ifP; last by rewrite cfunJgen.
  by rewrite -conjgM conjgC conjgM cfunJgen // memJ_norm ?groupV.
by rewrite cfun0gen //; case: ifP => // nGy; rewrite memJ_norm ?groupV.
Qed.
Definition cfConjg := Cfun 1 cfConjg_subproof.

End ConjDef.

Prenex Implicits cfConjg.
Notation "f ^ y" := (cfConjg y f) : cfun_scope.

Section Conj.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type phi : 'CF(G).

Lemma cfConjgE phi y x : y \in 'N(G) -> (phi ^ y)%CF x = phi (x ^ y^-1)%g.
Proof. by rewrite cfunElock genGid => ->. Qed.

Lemma cfConjgEJ phi y x : y \in 'N(G) -> (phi ^ y)%CF (x ^ y) = phi x.
Proof. by move/cfConjgE->; rewrite conjgK. Qed.

Lemma cfConjgEout phi y : y \notin 'N(G) -> (phi ^ y = phi)%CF.
Proof.
by move/negbTE=> notNy; apply/cfunP=> x; rewrite !cfunElock genGid notNy.
Qed.

Lemma cfConjgEin phi y (nGy : y \in 'N(G)) :
  (phi ^ y)%CF = cfIsom (norm_conj_isom nGy) phi.
Proof.
apply/cfun_inP=> x Gx.
by rewrite cfConjgE // -{2}[x](conjgKV y) cfIsomE ?memJ_norm ?groupV.
Qed.

Lemma cfConjgMnorm phi :
  {in 'N(G) &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CF.
Proof.
move=> y z nGy nGz.
by apply/cfunP=> x; rewrite !cfConjgE ?groupM // invMg conjgM.
Qed.

Lemma cfConjg_id phi y : y \in G -> (phi ^ y)%CF = phi.
Proof.
move=> Gy; apply/cfunP=> x; have nGy := subsetP (normG G) y Gy.
by rewrite -(cfunJ _ _ Gy) cfConjgEJ.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfConjgM L phi :
  G <| L -> {in L &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CF.
Proof. by case/andP=> _ /subsetP nGL; exact: sub_in2 (cfConjgMnorm phi). Qed.

Lemma cfConjgJ1 phi : (phi ^ 1)%CF = phi.
Proof. by apply/cfunP=> x; rewrite cfConjgE ?group1 // invg1 conjg1. Qed.

Lemma cfConjgK y : cancel (cfConjg y) (cfConjg y^-1 : 'CF(G) -> 'CF(G)).
Proof.
move=> phi; apply/cfunP=> x; rewrite !cfunElock groupV /=.
by case: ifP => -> //; rewrite conjgKV.
Qed.

Lemma cfConjgKV y : cancel (cfConjg y^-1) (cfConjg y : 'CF(G) -> 'CF(G)).
Proof. by move=> phi /=; rewrite -{1}[y]invgK cfConjgK. Qed.

Lemma cfConjg1 phi y : (phi ^ y)%CF 1%g = phi 1%g.
Proof. by rewrite cfunElock conj1g if_same. Qed.

Fact cfConjg_is_linear y : linear (cfConjg y : 'CF(G) -> 'CF(G)).
Proof. by move=> a phi psi; apply/cfunP=> x; rewrite !cfunElock. Qed.
Canonical cfConjg_additive y := Additive (cfConjg_is_linear y).
Canonical cfConjg_linear y := AddLinear (cfConjg_is_linear y).

Lemma cfConjg_cfuniJ A y : y \in 'N(G) -> ('1_A ^ y)%CF = '1_(A :^ y) :> 'CF(G).
Proof.
move=> nGy; apply/cfunP=> x; rewrite !cfunElock genGid nGy -sub_conjgV.
by rewrite -class_lcoset -class_rcoset norm_rlcoset ?memJ_norm ?groupV.
Qed.

Lemma cfConjg_cfuni A y : y \in 'N(A) -> ('1_A ^ y)%CF = '1_A :> 'CF(G).
Proof.
by have [/cfConjg_cfuniJ-> /normP-> | /cfConjgEout] := boolP (y \in 'N(G)).
Qed.

Lemma cfConjg_cfun1 y : (1 ^ y)%CF = 1 :> 'CF(G).
Proof.
by rewrite -cfuniG; have [/cfConjg_cfuni|/cfConjgEout] := boolP (y \in 'N(G)).
Qed.

Fact cfConjg_is_multiplicative y : multiplicative (cfConjg y : _ -> 'CF(G)).
Proof.
split=> [phi psi|]; last exact: cfConjg_cfun1.
by apply/cfunP=> x; rewrite !cfunElock.
Qed.
Canonical cfConjg_rmorphism y := AddRMorphism (cfConjg_is_multiplicative y).
Canonical cfConjg_lrmorphism y := [lrmorphism of cfConjg y].

Lemma cfAutConjg phi u y : cfAut u (phi ^ y) = (cfAut u phi ^ y)%CF.
Proof. by apply/cfunP=> x; rewrite !cfunElock. Qed.

Lemma conj_cfConjg phi y : (phi ^ y)^*%CF = (phi^* ^ y)%CF.
Proof. exact: cfAutConjg. Qed.

Lemma cfker_conjg x phi : x \in 'N(G) -> cfker (phi ^ x) = cfker phi :^ x.
Proof.
move=> nGx; rewrite cfConjgEin // cfker_isom.
by rewrite morphim_conj (setIidPr (cfker_sub _)).
Qed.

End Conj.

Section Inertia.

Variable gT : finGroupType.

Definition inertia (B : {set gT}) (phi : 'CF(B)) :=  
  [set y in 'N(B) | (phi ^ y)%CF == phi].

Local Notation "''I[' phi ]" := (inertia phi) : group_scope.
Local Notation "''I_' G [ phi ]" := (G%g :&: 'I[phi]) : group_scope.

Fact group_set_inertia (H : {group gT}) phi : group_set 'I[phi : 'CF(H)].
Proof.
apply/group_setP; split; first by rewrite inE group1 /= cfConjgJ1.
move=> y z /setIdP[nHy /eqP n_phi_y] /setIdP[nHz n_phi_z].
by rewrite inE groupM //= cfConjgMnorm ?n_phi_y.
Qed.
Canonical inertia_group H phi := Group (@group_set_inertia H phi).

Local Notation "''I[' phi ]" := (inertia_group phi) : Group_scope.
Local Notation "''I_' G [ phi ]" := (G :&: 'I[phi])%G : Group_scope.

Variables G H : {group gT}.
Implicit Type phi : 'CF(H).

Lemma inertiaJ phi y : y \in 'I[phi] -> (phi ^ y)%CF = phi.
Proof. by case/setIdP=> _ /eqP->. Qed.

Lemma inertia_valJ phi x y : y \in 'I[phi] -> phi (x ^ y)%g = phi x.
Proof. by case/setIdP=> nHy /eqP {1}<-; rewrite cfConjgEJ. Qed.

(* To disambiguate basic inclucion lemma names we capitalize Inertia for      *)
(* lemmas concerning the localized inertia group 'I_G[phi].                   *)
Lemma Inertia_sub phi : 'I_G[phi] \subset G.
Proof. exact: subsetIl. Qed.

Lemma norm_inertia phi : 'I[phi] \subset 'N(H).
Proof. by rewrite ['I[_]]setIdE subsetIl. Qed.

Lemma sub_inertia phi : H \subset 'I[phi].
Proof.
by apply/subsetP=> y Hy; rewrite inE cfConjg_id ?(subsetP (normG H)) /=.
Qed.

Lemma normal_inertia phi : H <| 'I[phi].
Proof. by rewrite /normal sub_inertia norm_inertia. Qed.

Lemma sub_Inertia phi : H \subset G -> H \subset 'I_G[phi].
Proof. by rewrite subsetI sub_inertia andbT. Qed.

Lemma norm_Inertia phi : 'I_G[phi] \subset 'N(H).
Proof. by rewrite setIC subIset ?norm_inertia. Qed.

Lemma normal_Inertia phi : H \subset G -> H <| 'I_G[phi].
Proof. by rewrite /normal norm_Inertia andbT; apply: sub_Inertia. Qed.

Lemma cfConjg_eqE phi :
    H <| G ->
  {in G &, forall y z, (phi ^ y == phi ^ z)%CF = (z \in 'I_G[phi] :* y)}.
Proof.
case/andP=> _ nHG y z Gy; rewrite -{1 2}[z](mulgKV y) groupMr // mem_rcoset.
move: {z}(z * _)%g => z Gz; rewrite 2!inE Gz cfConjgMnorm ?(subsetP nHG) //=.
by rewrite eq_sym (can_eq (cfConjgK y)).
Qed.

Lemma cent_sub_inertia phi : 'C(H) \subset 'I[phi].
Proof.
apply/subsetP=> y cHy; have nHy := subsetP (cent_sub H) y cHy.
rewrite inE nHy; apply/eqP/cfun_inP=> x Hx; rewrite cfConjgE //.
by rewrite /conjg invgK mulgA (centP cHy) ?mulgK.
Qed.

Lemma cent_sub_Inertia phi : 'C_G(H) \subset 'I_G[phi].
Proof. exact: setIS (cent_sub_inertia phi). Qed.

Lemma center_sub_Inertia phi : H \subset G -> 'Z(G) \subset 'I_G[phi].
Proof.
by move/centS=> sHG; rewrite setIS // (subset_trans sHG) // cent_sub_inertia.
Qed.

Lemma conjg_inertia phi y : y \in 'N(H) -> 'I[phi] :^ y = 'I[phi ^ y].
Proof.
move=> nHy; apply/setP=> z; rewrite !['I[_]]setIdE conjIg conjGid // !in_setI.
apply/andb_id2l=> nHz; rewrite mem_conjg !inE.
by rewrite !cfConjgMnorm ?in_group ?(can2_eq (cfConjgKV y) (cfConjgK y)) ?invgK.
Qed.

Lemma inertia_cfun0 : 'I[0 : 'CF(H)] = 'N(H).
Proof. by apply/setP=> x; rewrite !inE linear0 eqxx andbT. Qed.

Lemma inertia_add phi psi : 'I[phi] :&: 'I[psi] \subset 'I[phi + psi].
Proof.
rewrite !['I[_]]setIdE -setIIr setIS //.
by apply/subsetP=> x; rewrite !inE linearD /= => /andP[/eqP-> /eqP->].
Qed.

Lemma inertia_sum I r (P : pred I) (Phi : I -> 'CF(H)) :
  'N(H) :&: \bigcap_(i <- r | P i) 'I[Phi i]
     \subset 'I[\sum_(i <- r | P i) Phi i].
Proof.
elim/big_rec2: _ => [|i K psi Pi sK_Ipsi]; first by rewrite setIT inertia_cfun0.
by rewrite setICA; apply: subset_trans (setIS _ sK_Ipsi) (inertia_add _ _).
Qed.

Lemma inertia_scale a phi : 'I[phi] \subset 'I[a *: phi].
Proof.
apply/subsetP=> x /setIdP[nHx /eqP Iphi_x]. 
by rewrite inE nHx linearZ /= Iphi_x.
Qed.

Lemma inertia_scale_nz a phi : a != 0 -> 'I[a *: phi] = 'I[phi].
Proof.
move=> nz_a; apply/eqP.
by rewrite eqEsubset -{2}(scalerK nz_a phi) !inertia_scale.
Qed.

Lemma inertia_opp phi : 'I[- phi] = 'I[phi].
Proof. by rewrite -scaleN1r inertia_scale_nz // oppr_eq0 oner_eq0. Qed.

Lemma inertia_cfun1 : 'I[1 : 'CF(H)] = 'N(H).
Proof. by apply/setP=> x; rewrite inE rmorph1 eqxx andbT. Qed.

Lemma inertia_mul phi psi : 'I[phi] :&: 'I[psi] \subset 'I[phi * psi].
Proof.
rewrite !['I[_]]setIdE -setIIr setIS //.
by apply/subsetP=> x; rewrite !inE rmorphM /= => /andP[/eqP-> /eqP->].
Qed.

Lemma inertia_prod I r (P : pred I) (Phi : I -> 'CF(H)) :
  'N(H) :&: \bigcap_(i <- r | P i) 'I[Phi i]
     \subset 'I[\prod_(i <- r | P i) Phi i].
Proof.
elim/big_rec2: _ => [|i K psi Pi sK_psi]; first by rewrite inertia_cfun1 setIT.
by rewrite setICA; apply: subset_trans (setIS _ sK_psi) (inertia_mul _ _).
Qed.

Lemma inertia_injective (chi : 'CF(H)) :
  {in H &, injective chi} -> 'I[chi] = 'C(H).
Proof.
move=> inj_chi; apply/eqP; rewrite eqEsubset cent_sub_inertia andbT.
apply/subsetP=> y Ichi_y; have /setIdP[nHy _] := Ichi_y.
apply/centP=> x Hx; apply/esym/commgP/conjg_fixP.
by apply/inj_chi; rewrite ?memJ_norm ?(inertia_valJ _ Ichi_y).
Qed.

Lemma inertia_irr_prime p i :
  #|H| = p -> prime p -> i != 0 -> 'I['chi[H]_i] = 'C(H).
Proof. by move=> <- pr_H /(irr_prime_injP pr_H); apply: inertia_injective. Qed.

Lemma inertia_irr0 : 'I['chi[H]_0] = 'N(H).
Proof. by rewrite irr0 inertia_cfun1. Qed.

(* Isaacs' 6.1.c *)
Lemma cfConjg_iso y : isometry (cfConjg y : 'CF(H) -> 'CF(H)).
Proof.
move=> phi psi; congr (_ * _).
have [nHy | not_nHy] := boolP (y \in 'N(H)); last by rewrite !cfConjgEout.
rewrite (reindex_astabs 'J y) ?astabsJ //=.
by apply: eq_bigr=> x _; rewrite !cfConjgEJ.
Qed.
 
(* Isaacs' 6.1.d *)
Lemma cfdot_Res_conjg psi phi y :
  y \in G -> '['Res[H, G] psi, phi ^ y] = '['Res[H] psi, phi].
Proof.
move=> Gy; rewrite -(cfConjg_iso y _ phi); congr '[_, _]; apply/cfunP=> x.
rewrite !cfunElock !genGid; case nHy: (y \in 'N(H)) => //.
by rewrite !(fun_if psi) cfunJ ?memJ_norm ?groupV.
Qed.

(* Isaac's 6.1.e *)
Lemma cfConjg_char (chi : 'CF(H)) y :
  chi \is a character -> (chi ^ y)%CF \is a character.
Proof.
have [nHy Nchi | /cfConjgEout-> //] := boolP (y \in 'N(H)).
by rewrite cfConjgEin cfIsom_char.
Qed.

Lemma cfConjg_lin_char (chi : 'CF(H)) y :
  chi \is a linear_char -> (chi ^ y)%CF \is a linear_char.
Proof. by case/andP=> Nchi chi1; rewrite qualifE cfConjg1 cfConjg_char. Qed.

Lemma cfConjg_irr y chi : chi \in irr H -> (chi ^ y)%CF \in irr H.
Proof. by rewrite !irrEchar cfConjg_iso => /andP[/cfConjg_char->]. Qed.
 
Definition conjg_Iirr i y := cfIirr ('chi[H]_i ^ y)%CF.

Lemma conjg_IirrE i y : 'chi_(conjg_Iirr i y) = ('chi_i ^ y)%CF.
Proof. by rewrite cfIirrE ?cfConjg_irr ?mem_irr. Qed.

Lemma conjg_Iirr_eq0 i y : (conjg_Iirr i y == 0) = (i == 0).
Proof.
rewrite -(inj_eq irr_inj) conjg_IirrE irr0.
by rewrite (can2_eq (cfConjgK y) (cfConjgKV y)) rmorph1 irr_eq1.
Qed.

Lemma conjg_Iirr0 x : conjg_Iirr 0 x = 0.
Proof. by apply/eqP; rewrite conjg_Iirr_eq0. Qed.

Lemma cfdot_irr_conjg i y :
  H <| G -> y \in G -> '['chi_i, 'chi_i ^ y]_H = (y \in 'I_G['chi_i])%:R.
Proof.
move=> nsHG Gy; rewrite -conjg_IirrE cfdot_irr -(inj_eq irr_inj) conjg_IirrE.
by rewrite -{1}['chi_i]cfConjgJ1 cfConjg_eqE ?mulg1.
Qed.

Definition cfclass (A : {set gT}) (phi : 'CF(A)) (B : {set gT}) := 
  [seq (phi ^ repr Tx)%CF | Tx in rcosets 'I_B[phi] B].

Local Notation "phi ^: G" := (cfclass phi G) : cfun_scope.

Lemma cfclassP (A : {group gT}) phi psi :
  reflect (exists2 y, y \in A & psi = phi ^ y)%CF (psi \in phi ^: A)%CF.
Proof.
apply: (iffP imageP) => [[_ /rcosetsP[y Ay ->] ->] | [y Ay ->]].
  by case: repr_rcosetP => z /setIdP[Az _]; exists (z * y)%g; rewrite ?groupM.
without loss nHy: y Ay / y \in 'N(H).
  have [nHy | /cfConjgEout->] := boolP (y \in 'N(H)); first exact.
  by move/(_ 1%g); rewrite !group1 !cfConjgJ1; exact.
exists ('I_A[phi] :* y); first by rewrite -rcosetE mem_imset.
case: repr_rcosetP => z /setIP[_ /setIdP[nHz /eqP Tz]].
by rewrite cfConjgMnorm ?Tz.
Qed.

Lemma cfclassInorm phi : (phi ^: 'N_G(H) =i phi ^: G)%CF.
Proof.
move=> xi; apply/cfclassP/cfclassP=> [[x /setIP[Gx _] ->] | [x Gx ->]].
  by exists x.
have [Nx | /cfConjgEout-> //] := boolP (x \in 'N(H)).
  by exists x; first exact/setIP.
by exists 1%g; rewrite ?group1 ?cfConjgJ1.
Qed.

Lemma cfclass_refl phi : phi \in (phi ^: G)%CF.
Proof. by apply/cfclassP; exists 1%g => //; rewrite cfConjgJ1. Qed.

Lemma cfclass_transl phi psi :
  (psi \in phi ^: G)%CF -> (phi ^: G =i psi ^: G)%CF.
Proof.
rewrite -cfclassInorm; case/cfclassP=> x Gx -> xi; rewrite -!cfclassInorm.
have nHN: {subset 'N_G(H) <= 'N(H)} by apply/subsetP; exact: subsetIr.
apply/cfclassP/cfclassP=> [[y Gy ->] | [y Gy ->]].
  by exists (x^-1 * y)%g; rewrite -?cfConjgMnorm ?groupM ?groupV ?nHN // mulKVg.
by exists (x * y)%g; rewrite -?cfConjgMnorm ?groupM ?nHN.
Qed.

Lemma cfclass_sym phi psi : (psi \in phi ^: G)%CF = (phi \in psi ^: G)%CF.
Proof. by apply/idP/idP=> /cfclass_transl <-; exact: cfclass_refl. Qed.

Lemma cfclass_uniq phi : H <| G -> uniq (phi ^: G)%CF.
Proof.
move=> nsHG; rewrite map_inj_in_uniq ?enum_uniq // => Ty Tz; rewrite !mem_enum.
move=> {Ty}/rcosetsP[y Gy ->] {Tz}/rcosetsP[z Gz ->] /eqP.
case: repr_rcosetP => u Iphi_u; case: repr_rcosetP => v Iphi_v.
have [[Gu _] [Gv _]] := (setIdP Iphi_u, setIdP Iphi_v).
rewrite cfConjg_eqE ?groupM // => /rcoset_transl.
by rewrite !rcosetM (rcoset_id Iphi_v) (rcoset_id Iphi_u).
Qed.

Lemma inertia1 : H <| G -> 'I_G[1 : 'CF(H)] = G.
Proof. by rewrite inertia_cfun1 => /normal_norm/setIidPl. Qed.

Lemma cfclass1 : H <| G -> (1 ^: G)%CF = [:: 1 : 'CF(H)].
Proof.
move=> nsHG; rewrite /cfclass inertia1 // rcosets_id.
by rewrite /(image _ _) enum_set1 /= rmorph1.
Qed.

Lemma cfclass_sum R idx (op : Monoid.com_law idx) (F : 'CF(H) -> R) i :
     H <| G ->
  \big[op/idx]_(j | 'chi_j \in ('chi_i ^: G)%CF) F 'chi_j
     = \big[op/idx]_(chi <- ('chi_i ^: G)%CF) F chi.
Proof.
move/cfclass_uniq=> chiGuniq; rewrite -big_map -big_filter; apply: eq_big_perm.
rewrite -[index_enum _]enumT map_tnth_enum uniq_perm_eq // => [|chi].
  by rewrite filter_uniq // free_uniq // irr_free.
rewrite mem_filter andb_idr // => /imageP[Tx _ ->].
by rewrite cfConjg_irr ?mem_irr.
Qed.

Lemma ResIndchiE j:
  H <| G -> 'Res[H] ('Ind[G] 'chi_j) = #|H|%:R^-1 *: (\sum_(y in G) 'chi_j ^ y)%CF.
Proof.
case/andP=> [sHG /subsetP nHG].
rewrite (reindex_inj invg_inj); apply/cfun_inP=> x Hx.
rewrite  cfResE // cfIndE // ?cfunE ?sum_cfunE; congr (_ * _).
by apply: eq_big => [y | y Gy]; rewrite ?cfConjgE ?groupV ?invgK ?nHG.
Qed.


(* This is Isaacs, Theorem (6.2) *)
Lemma Clifford_Res_sum_cfclass i j :
     H <| G -> j \in irr_constt ('Res[H, G] 'chi_i) ->
  'Res[H] 'chi_i = 
     '['Res[H] 'chi_i, 'chi_j] *: (\sum_(chi <- ('chi_j ^: G)%CF) chi).
Proof.
move=> nsHG chiHj; have [sHG /subsetP nHG] := andP nsHG.
rewrite -cfclass_sum //= big_mkcond.
rewrite {1}['Res _]cfun_sum_cfdot linear_sum /=; apply: eq_bigr => k _.
have [[y Gy ->] | ] := altP (cfclassP _ _ _); first by rewrite cfdot_Res_conjg.
apply: contraNeq; rewrite scaler0 scaler_eq0 orbC => /norP[_ chiHk].
have{chiHk chiHj}: '['Res[H] ('Ind[G] 'chi_j), 'chi_k] != 0.
  rewrite !inE !cfdot_Res_l in chiHj chiHk *.
  apply: contraNneq chiHk; rewrite cfdot_sum_irr => /psumr_eq0P/(_ i isT)/eqP.
  rewrite -cfdotC cfdotC mulf_eq0 conjC_eq0 (negbTE chiHj) /= => -> // i1.
  by rewrite -cfdotC Cnat_ge0 // rpredM ?Cnat_cfdot_char ?cfInd_char ?irr_char.
rewrite ResIndchiE //.
rewrite cfdotZl mulf_eq0 cfdot_suml => /norP[_]; apply: contraR => not_chjGk.
rewrite big1 // => x Gx; apply: contraNeq not_chjGk.
rewrite -conjg_IirrE cfdot_irr pnatr_eq0; case: (_ =P k) => // <- _.
by rewrite conjg_IirrE; apply/cfclassP; exists x.
Qed.

(* This is Isaacs' 6.7 *)
Lemma constt0_Res_cfker i : 
  H <| G -> 0 \in irr_constt ('Res[H] 'chi[G]_i) -> H \subset cfker 'chi[G]_i.
Proof.
move=> nsHG /(Clifford_Res_sum_cfclass nsHG); have [sHG nHG] := andP nsHG.
rewrite irr0 cfdot_Res_l cfclass1 // big_seq1 cfInd_cfun1 //.
rewrite cfdotZr conjC_nat => def_chiH.
apply/subsetP=> x Hx; rewrite cfkerEirr inE -!(cfResE _ sHG) //.
by rewrite def_chiH !cfunE cfun11 cfun1E Hx.
Qed.

(* This is Isaacs' 6.8 *)
Lemma dvdn_constt_Res1_irr1 i j : 
    H <| G -> j \in irr_constt ('Res[H, G] 'chi_i) ->
  exists n, 'chi_i 1%g = n%:R * 'chi_j 1%g.
Proof.
move=> nsHG chiHj; have [sHG nHG] := andP nsHG; rewrite -(cfResE _ sHG) //.
rewrite {1}(Clifford_Res_sum_cfclass nsHG chiHj) cfunE sum_cfunE.
have /CnatP[n ->]: '['Res[H] 'chi_i, 'chi_j] \in Cnat.
  by rewrite Cnat_cfdot_char ?cfRes_char ?irr_char.
exists (n * size ('chi_j ^: G)%CF)%N; rewrite natrM -mulrA; congr (_ * _).
rewrite mulr_natl -[size _]card_ord big_tnth -sumr_const; apply: eq_bigr => k _.
by have /cfclassP[y Gy ->]:=  mem_tnth k (in_tuple _); rewrite cfConjg1.
Qed.

Lemma cfclass_Ind phi psi :
  H <| G ->  psi \in (phi ^: G)%CF -> 'Ind[G] phi = 'Ind[G] psi.
Proof.
move=> nsHG /cfclassP[y Gy ->]; have [sHG /subsetP nHG] := andP nsHG.
apply/cfun_inP=> x Hx; rewrite !cfIndE //; congr (_ * _).
rewrite (reindex_acts 'R _ (groupVr Gy)) ?astabsR //=.
by apply: eq_bigr => z Gz; rewrite conjgM cfConjgE ?nHG.
Qed.

Lemma size_cfclass i : size ('chi[H]_i ^: G)%CF = #|G : 'I_G['chi_i]|.
Proof. by rewrite size_map -cardE. Qed.

Definition cfclass_Iirr (A : {set gT}) i := conjg_Iirr i @: A.

Lemma cfclass_IirrE i j :
  (j \in cfclass_Iirr G i) = ('chi_j \in 'chi_i ^: G)%CF.
Proof.
apply/imsetP/cfclassP=> [[y Gy ->] | [y]]; exists y; rewrite ?conjg_IirrE //.
by apply: irr_inj; rewrite conjg_IirrE.
Qed.

Lemma eq_cfclass_IirrE i j :
  (cfclass_Iirr G j == cfclass_Iirr G i) = (j \in cfclass_Iirr G i).
Proof.
apply/eqP/idP=> [<- | iGj]; first by rewrite cfclass_IirrE cfclass_refl.
by apply/setP=> k; rewrite !cfclass_IirrE in iGj *; apply/esym/cfclass_transl.
Qed.

Lemma im_cfclass_Iirr i :
  H <| G -> perm_eq [seq 'chi_j | j in cfclass_Iirr G i] ('chi_i ^: G)%CF.
Proof.
move=> nsHG; have UchiG := cfclass_uniq 'chi_i nsHG.
apply: uniq_perm_eq; rewrite ?(map_inj_uniq irr_inj) ?enum_uniq // => phi.
apply/imageP/idP=> [[j iGj ->] | /cfclassP[y]]; first by rewrite -cfclass_IirrE.
by exists (conjg_Iirr i y); rewrite ?mem_imset ?conjg_IirrE.
Qed.

Lemma card_cfclass_Iirr i : H <| G -> #|cfclass_Iirr G i| = #|G : 'I_G['chi_i]|.
Proof.
move=> nsHG; rewrite -size_cfclass -(perm_eq_size (im_cfclass_Iirr i nsHG)).
by rewrite size_map -cardE.
Qed.

End Inertia.

Arguments Scope inertia [_ group_scope cfun_scope].
Arguments Scope cfclass [_ group_scope cfun_scope group_scope].
Notation "''I[' phi ] " := (inertia phi) : group_scope.
Notation "''I[' phi ] " := (inertia_group phi) : Group_scope.
Notation "''I_' G [ phi ] " := (G%g :&: 'I[phi]) : group_scope.
Notation "''I_' G [ phi ] " := (G :&: 'I[phi])%G : Group_scope.
Notation "phi ^: G" := (cfclass phi G) : cfun_scope.

Section ConjRestrict.

Variables (gT : finGroupType) (G H K : {group gT}).

Lemma cfConjgRes_norm phi y :
  y \in 'N(K) -> y \in 'N(H) -> ('Res[K, H] phi ^ y)%CF = 'Res (phi ^ y)%CF.
Proof.
move=> nKy nHy; have [sKH | not_sKH] := boolP (K \subset H); last first.
  by rewrite !cfResEout // linearZ rmorph1 cfConjg1.
by apply/cfun_inP=> x Kx; rewrite !(cfConjgE, cfResE) ?memJ_norm ?groupV.
Qed.

Lemma cfConjgRes phi y :
  H <| G -> K <| G -> y \in G -> ('Res[K, H] phi ^ y)%CF = 'Res (phi ^ y)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgRes_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma sub_inertia_Res phi :
  G \subset 'N(K) -> 'I_G[phi] \subset 'I_G['Res[K, H] phi].
Proof.
move=> nKG; apply/subsetP=> y /setIP[Gy /setIdP[nHy /eqP Iphi_y]].
by rewrite 2!inE Gy cfConjgRes_norm ?(subsetP nKG) ?Iphi_y /=.
Qed.

Lemma cfConjgInd_norm phi y :
  y \in 'N(K) -> y \in 'N(H) -> ('Ind[H, K] phi ^ y)%CF = 'Ind (phi ^ y)%CF.
Proof.
move=> nKy nHy; have [sKH | not_sKH] := boolP (K \subset H).
  by rewrite !cfConjgEin (cfIndIsom (norm_conj_isom nHy)).
rewrite !cfIndEout // linearZ -(cfConjg_iso y) rmorph1 /=; congr (_ *: _).
by rewrite cfConjg_cfuni ?norm1 ?inE.
Qed.

Lemma cfConjgInd phi y :
  H <| G -> K <| G -> y \in G -> ('Ind[H, K] phi ^ y)%CF = 'Ind (phi ^ y)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgInd_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma sub_inertia_Ind phi :
  G \subset 'N(H) -> 'I_G[phi] \subset 'I_G['Ind[H, K] phi].
Proof.
move=> nHG; apply/subsetP=> y /setIP[Gy /setIdP[nKy /eqP Iphi_y]].
by rewrite 2!inE Gy cfConjgInd_norm ?(subsetP nHG) ?Iphi_y /=.
Qed.

End ConjRestrict.

Section MoreInertia.

Variables (gT : finGroupType) (G H : {group gT}) (i : Iirr H).
Let T := 'I_G['chi_i].

Lemma inertia_id : 'I_T['chi_i] = T. Proof. by rewrite -setIA setIid. Qed.

Lemma cfclass_inertia : ('chi[H]_i ^: T)%CF = [:: 'chi_i].
Proof.
rewrite /cfclass inertia_id rcosets_id /(image _ _) enum_set1 /=.
by rewrite repr_group cfConjgJ1.
Qed.

End MoreInertia.

Section ConjMorph.

Variables (aT rT : finGroupType) (D G H : {group aT}) (f : {morphism D >-> rT}).

Lemma cfConjgMorph (phi : 'CF(f @* H)) y :
  y \in D -> y \in 'N(H) -> (cfMorph phi ^ y)%CF = cfMorph (phi ^ f y).
Proof.
move=> Dy nHy; have [sHD | not_sHD] := boolP (H \subset D); last first.
  by rewrite !cfMorphEout // linearZ rmorph1 cfConjg1.
apply/cfun_inP=> x Gx; rewrite !(cfConjgE, cfMorphE) ?memJ_norm ?groupV //.
  by rewrite morphJ ?morphV ?groupV // (subsetP sHD).
by rewrite (subsetP (morphim_norm _ _)) ?mem_morphim.
Qed.

Lemma inertia_morph_pre (phi : 'CF(f @* H)) :
  H <| G -> G \subset D -> 'I_G[cfMorph phi] = G :&: f @*^-1 'I_(f @* G)[phi].
Proof.
case/andP=> sHG nHG sGD; have sHD := subset_trans sHG sGD.
apply/setP=> y; rewrite !in_setI; apply: andb_id2l => Gy.
have [Dy nHy] := (subsetP sGD y Gy, subsetP nHG y Gy).
rewrite Dy inE nHy 4!inE mem_morphim // -morphimJ ?(normP nHy) // subxx /=.
rewrite cfConjgMorph //; apply/eqP/eqP=> [Iphi_y | -> //].
by apply/cfun_inP=> _ /morphimP[x Dx Hx ->]; rewrite -!cfMorphE ?Iphi_y.
Qed.

Lemma inertia_morph_im (phi : 'CF(f @* H)) :
  H <| G -> G \subset D -> f @* 'I_G[cfMorph phi] = 'I_(f @* G)[phi].
Proof.
move=> nsHG sGD; rewrite inertia_morph_pre // morphim_setIpre.
by rewrite (setIidPr _) ?Inertia_sub.
Qed.

Variables (R S : {group rT}).
Variables (g : {morphism G >-> rT}) (h : {morphism H >-> rT}).
Hypotheses (isoG : isom G R g) (isoH : isom H S h).
Hypotheses (eq_hg : {in H, h =1 g}) (sHG : H \subset G).

(* This does not depend on the (isoG : isom G R g) assumption. *)
Lemma cfConjgIsom phi y :
  y \in G -> y \in 'N(H) -> (cfIsom isoH phi ^ g y)%CF = cfIsom isoH (phi ^ y).
Proof.
move=> Gy nHy; have [_ defS] := isomP isoH.
rewrite morphimEdom (eq_in_imset eq_hg) -morphimEsub // in defS.
apply/cfun_inP=> gx; rewrite -{1}defS => /morphimP[x Gx Hx ->] {gx}.
rewrite cfConjgE; last by rewrite -defS inE -morphimJ ?(normP nHy).
by rewrite -morphV -?morphJ -?eq_hg ?cfIsomE ?cfConjgE ?memJ_norm ?groupV.
Qed.

Lemma inertia_isom phi : 'I_R[cfIsom isoH phi] = g @* 'I_G[phi].
Proof.
have [[_ defS] [injg <-]] := (isomP isoH, isomP isoG).
rewrite morphimEdom (eq_in_imset eq_hg) -morphimEsub // in defS.
rewrite /inertia !setIdE morphimIdom setIA -{1}defS -injm_norm ?injmI //.
apply/setP=> gy; rewrite !inE; apply: andb_id2l => /morphimP[y Gy nHy ->] {gy}.
rewrite cfConjgIsom // -sub1set -morphim_set1 // injmSK ?sub1set //= inE.
apply/eqP/eqP=> [Iphi_y | -> //].
by apply/cfun_inP=> x Hx; rewrite -!(cfIsomE isoH) ?Iphi_y.
Qed.

End ConjMorph.

Section ConjQuotient.

Variables gT : finGroupType.
Implicit Types G H K : {group gT}.

Lemma cfConjgMod_norm H K (phi : 'CF(H / K)) y :
  y \in 'N(K) -> y \in 'N(H) -> ((phi %% K) ^ y)%CF = (phi ^ coset K y %% K)%CF.
Proof. exact: cfConjgMorph. Qed.

Lemma cfConjgMod G H K (phi : 'CF(H / K)) y :
    H <| G -> K <| G -> y \in G ->
  ((phi %% K) ^ y)%CF = (phi ^ coset K y %% K)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgMod_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma cfConjgQuo_norm H K (phi : 'CF(H)) y :
  y \in 'N(K) -> y \in 'N(H) -> ((phi / K) ^ coset K y)%CF = (phi ^ y / K)%CF.
Proof.
move=> nKy nHy; have keryK: (K \subset cfker (phi ^ y)) = (K \subset cfker phi).
  by rewrite cfker_conjg // -{1}(normP nKy) conjSg.
have [kerK | not_kerK] := boolP (K \subset cfker phi); last first.
  by rewrite !cfQuoEout ?linearZ ?rmorph1 ?cfConjg1 ?keryK.
apply/cfun_inP=> _ /morphimP[x nKx Hx ->].
have nHyb: coset K y \in 'N(H / K) by rewrite inE -morphimJ ?(normP nHy).
rewrite !(cfConjgE, cfQuoEnorm) ?keryK // ?in_setI ?Hx //.
rewrite -morphV -?morphJ ?groupV // cfQuoEnorm //.
by rewrite inE memJ_norm ?Hx ?groupJ ?groupV.
Qed.

Lemma cfConjgQuo G H K (phi : 'CF(H)) y :
    H <| G -> K <| G -> y \in G ->
  ((phi / K) ^ coset K y)%CF = (phi ^ y / K)%CF.
Proof.
move=> /andP[_ nHG] /andP[_ nKG] Gy.
by rewrite cfConjgQuo_norm ?(subsetP nHG) ?(subsetP nKG).
Qed.

Lemma inertia_mod_pre G H K (phi : 'CF(H / K)) :
  H <| G -> K <| G -> 'I_G[phi %% K] = G :&: coset K @*^-1 'I_(G / K)[phi].
Proof. by move=> nsHG /andP[_]; apply: inertia_morph_pre. Qed.

Lemma inertia_mod_quo G H K (phi : 'CF(H / K)) :
  H <| G -> K <| G -> ('I_G[phi %% K] / K)%g = 'I_(G / K)[phi].
Proof. by move=> nsHG /andP[_]; apply: inertia_morph_im. Qed.

Lemma inertia_quo G H K (phi : 'CF(H)) :
    H <| G -> K <| G -> K \subset cfker phi ->
  'I_(G / K)[phi / K] = ('I_G[phi] / K)%g.
Proof.
move=> nsHG nsKG kerK; rewrite -inertia_mod_quo ?cfQuoK //.
by rewrite (normalS _ (normal_sub nsHG)) // (subset_trans _ (cfker_sub phi)).
Qed.

End ConjQuotient.

Section InertiaSdprod.

Variables (gT : finGroupType) (K H G : {group gT}).

Hypothesis defG : K ><| H = G.

Lemma cfConjgSdprod phi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfSdprod defG phi ^ y = cfSdprod defG (phi ^ y))%CF.
Proof.
move=> nKy nHy.
have nGy: y \in 'N(G) by rewrite -sub1set -(sdprodW defG) normsM ?sub1set.
rewrite -{2}[phi](cfSdprodK defG) cfConjgRes_norm // cfRes_sdprodK //.
by rewrite cfker_conjg // -{1}(normP nKy) conjSg cfker_sdprod.
Qed.

Lemma inertia_sdprod (L : {group gT}) phi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfSdprod defG phi] = 'I_L[phi].
Proof.
move=> nKL nHL; have nGL: L \subset 'N(G) by rewrite -(sdprodW defG) normsM.
apply/setP=> z; rewrite !in_setI ![z \in 'I[_]]inE; apply: andb_id2l => Lz.
rewrite cfConjgSdprod ?(subsetP nKL) ?(subsetP nHL) ?(subsetP nGL) //=.
by rewrite (can_eq (cfSdprodK defG)).
Qed.

End InertiaSdprod.

Section InertiaDprod.

Variables (gT : finGroupType) (G K H : {group gT}).
Implicit Type L : {group gT}.
Hypothesis KxH : K \x H = G.

Lemma cfConjgDprodl phi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprodl KxH phi ^ y = cfDprodl KxH (phi ^ y))%CF.
Proof. by move=> nKy nHy; apply: cfConjgSdprod. Qed.

Lemma cfConjgDprodr psi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprodr KxH psi ^ y = cfDprodr KxH (psi ^ y))%CF.
Proof. by move=> nKy nHy; apply: cfConjgSdprod. Qed.

Lemma cfConjgDprod phi psi y :
    y \in 'N(K) -> y \in 'N(H) ->
  (cfDprod KxH phi psi ^ y = cfDprod KxH (phi ^ y) (psi ^ y))%CF.
Proof. by move=> nKy nHy; rewrite rmorphM /= cfConjgDprodl ?cfConjgDprodr. Qed.

Lemma inertia_dprodl L phi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfDprodl KxH phi] = 'I_L[phi].
Proof. by move=> nKL nHL; apply: inertia_sdprod. Qed.

Lemma inertia_dprodr L psi :
  L \subset 'N(K) -> L \subset 'N(H) -> 'I_L[cfDprodr KxH psi] = 'I_L[psi].
Proof. by move=> nKL nHL; apply: inertia_sdprod. Qed.

Lemma inertia_dprod L (phi : 'CF(K)) (psi : 'CF(H)) :
    L \subset 'N(K) -> L \subset 'N(H) -> phi 1%g != 0 -> psi 1%g != 0 -> 
  'I_L[cfDprod KxH phi psi] = 'I_L[phi] :&: 'I_L[psi].
Proof.
move=> nKL nHL nz_phi nz_psi; apply/eqP; rewrite eqEsubset subsetI.
rewrite -{1}(inertia_scale_nz psi nz_phi) -{1}(inertia_scale_nz phi nz_psi).
rewrite -(cfDprod_Resl KxH) -(cfDprod_Resr KxH) !sub_inertia_Res //=.
by rewrite -inertia_dprodl -?inertia_dprodr // -setIIr setIS ?inertia_mul.
Qed.

Lemma inertia_dprod_irr L i j :
    L \subset 'N(K) -> L \subset 'N(H) ->
  'I_L[cfDprod KxH 'chi_i 'chi_j] = 'I_L['chi_i] :&: 'I_L['chi_j].
Proof. by move=> nKL nHL; rewrite inertia_dprod ?irr1_neq0. Qed.

End InertiaDprod.

Section InertiaBigdprod.

Variables (gT : finGroupType) (I : finType) (P : pred I).
Variables (A : I -> {group gT}) (G : {group gT}).
Implicit Type L : {group gT}.
Hypothesis defG : \big[dprod/1%g]_(i | P i) A i = G.

Section ConjBig.

Variable y : gT.
Hypothesis nAy: forall i, P i -> y \in 'N(A i).

Lemma cfConjgBigdprodi i (phi : 'CF(A i)) :
   (cfBigdprodi defG phi ^ y = cfBigdprodi defG (phi ^ y))%CF.
Proof.
rewrite cfConjgDprodl; try by case: ifP => [/nAy// | _]; rewrite norm1 inE.
  congr (cfDprodl _ _); case: ifP => [Pi | _].
    by rewrite cfConjgRes_norm ?nAy.
  by apply/cfun_inP=> _ /set1P->; rewrite !(cfRes1, cfConjg1).
rewrite -sub1set norms_gen ?norms_bigcup // sub1set.
by apply/bigcapP=> j /andP[/nAy].
Qed.

Lemma cfConjgBigdprod phi :
  (cfBigdprod defG phi ^ y = cfBigdprod defG (fun i => phi i ^ y))%CF.
Proof.
by rewrite rmorph_prod /=; apply: eq_bigr => i _; apply: cfConjgBigdprodi.
Qed.

End ConjBig.

Section InertiaBig.

Variable L : {group gT}.
Hypothesis nAL : forall i, P i -> L \subset 'N(A i).

Lemma inertia_bigdprodi i (phi : 'CF(A i)) :
  P i -> 'I_L[cfBigdprodi defG phi] = 'I_L[phi].
Proof.
move=> Pi; rewrite inertia_dprodl ?Pi ?cfRes_id ?nAL //.
by apply/norms_gen/norms_bigcup/bigcapsP=> j /andP[/nAL].
Qed.

Lemma inertia_bigdprod phi (Phi := cfBigdprod defG phi) :
  Phi 1%g != 0 -> 'I_L[Phi] = L :&: \bigcap_(i | P i) 'I_L[phi i].
Proof.
move=> nz_Phi; apply/eqP; rewrite eqEsubset; apply/andP; split.
  rewrite subsetI Inertia_sub; apply/bigcapsP=> i Pi.
  have [] := cfBigdprodK nz_Phi Pi; move: (_ / _) => a nz_a <-.
  by rewrite inertia_scale_nz ?sub_inertia_Res //= ?nAL.
rewrite subsetI subsetIl; apply: subset_trans (inertia_prod _ _ _).
apply: setISS.
  by rewrite -(bigdprodWY defG) norms_gen ?norms_bigcup //; apply/bigcapsP.
apply/bigcapsP=> i Pi; rewrite (bigcap_min i) //.
by rewrite -inertia_bigdprodi ?subsetIr.
Qed.

Lemma inertia_bigdprod_irr Iphi (phi := fun i => 'chi_(Iphi i)) :
  'I_L[cfBigdprod defG phi] = L :&: \bigcap_(i | P i) 'I_L[phi i].
Proof.
rewrite inertia_bigdprod // -[cfBigdprod _ _]cfIirrE ?irr1_neq0 //.
by apply: cfBigdprod_irr => i _; apply: mem_irr.
Qed.

End InertiaBig.

End InertiaBigdprod.

Section S611.

Variable (gT : finGroupType).

Section S611A.

Variable (H G : {group gT}).

Variable t : Iirr H.

Let T := 'I_G['chi_t]%G.

Hypothesis HnG : H <| G.

Let sHG : H \subset G. Proof. exact: normal_sub. Qed.

Let TsG : T \subset G. Proof. exact: subsetIl. Qed.

Let HsT : H \subset T. Proof. exact: sub_Inertia. Qed.

Let HnT : H <| T. Proof. exact: normal_Inertia. Qed.

Section Chi.

Variable p : Iirr T.

Hypothesis Hp : t \in irr_constt ('Res[H] 'chi_p).

Variable c : Iirr G.

Hypothesis Hc : c \in irr_constt ('Ind[G,T] 'chi_p).

Let ITC : 'Res[T] 'chi_c \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Let ITP : 'Res[T] 'chi_p \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Let IHC : 'Res[H] 'chi_c \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Let IHP : 'Res[H] 'chi_p \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Fact constt_Res_inertia_constt_Ind : p \in irr_constt ('Res[T] 'chi_c).
Proof. by rewrite -constt_Ind_constt_Res. Qed.

Fact constt_Res_constt_Ind : t \in irr_constt ('Res[H] 'chi_c).
Proof.
have:= constt_Res_trans ITC constt_Res_inertia_constt_Ind Hp.
by rewrite cfResRes.
Qed.

Let e := '['Res[H] 'chi_c, 'chi_t].

Let f := '['Res[H] 'chi_p, 'chi_t].

Let He : 'Res[H] 'chi_c = e *: (\sum_(f <- 'chi_t ^: G) f)%CF.
Proof. exact: (Clifford_Res_sum_cfclass HnG constt_Res_constt_Ind). Qed.

Let Hf : 'Res[H] 'chi_p = f *: 'chi_t.
Proof.
have:= Clifford_Res_sum_cfclass HnT Hp.
by rewrite cfclass_inertia big_seq1.
Qed.

Let He1 : 'chi_c 1%g = e * #|G : T|%:R * 'chi_t 1%g.
Proof.
rewrite -(cfResE _ (normal_sub HnG)) // He cfunE -mulrA; congr (_ * _).
rewrite sum_cfunE -(eq_big_perm _ (im_cfclass_Iirr _ _)) //= big_map big_filter.
rewrite -card_cfclass_Iirr // mulr_natl -sumr_const; apply: eq_bigr => j /=.
by case/imsetP=> y Gy ->; rewrite conjg_IirrE cfConjg1.
Qed.

Let Hpsi1 : ('Ind[G] 'chi_p) 1%g = f * #|G : T|%:R * ('chi_t 1%g).
Proof. by rewrite -mulrA mulrCA cfInd1 // -(cfResE _ HsT) // Hf cfunE. Qed.

Fact cfdot_constt_inertia_constt : f = e.
Proof.
have le_f_e: f <= e.
  have: '['Res 'chi_p, 'chi_t] <= '['Res[H] ('Res[T] 'chi_c), 'chi_t].
    by apply: cfdot_Res_ge_constt constt_Res_inertia_constt_Ind.
  rewrite Hf /= cfResRes // He !cfdotZl cfdot_irr eqxx mulr1.
  rewrite -cfclass_sum // cfdot_suml (bigD1 t) ?cfclass_refl //= cfdot_irr eqxx.
  rewrite big1 ?addr0 ?mulr1 // => i /andP[_ neq_it].
  by rewrite cfdot_irr (negbTE neq_it).
apply/eqP; rewrite eqr_le le_f_e /=.
have: 0 < #|G : T|%:R * 'chi_t 1%g.
  by rewrite pmulr_rgt0 // ?irr1_gt0 // ltr0n.
move/ler_pmul2r => <-; rewrite !mulrA -He1 -Hpsi1.
have IIP: 'Ind[G] 'chi_p \is a character := cfInd_char G (irr_char p).
case/(constt_charP _ IIP): Hc => chi' /= IC' ->.
by rewrite cfunE ler_addl Cnat_ge0 ?Cnat_char1.
Qed.

Fact cfInd_constt_inertia_constt : 'Ind[G] 'chi_p = 'chi_c.
Proof.
have ICI: 'Ind[G] 'chi_p \is a character := cfInd_char G (irr_char p).
case/(constt_charP _ ICI): Hc => chi' IC' /= Hchi'.
rewrite Hchi'; move/cfunP/(_ 1%g)/esym/eqP: Hchi'.
rewrite Hpsi1 cfdot_constt_inertia_constt -He1 cfunE addrC -subr_eq0 addrK.
by rewrite char1_eq0 // => /eqP->; rewrite addr0.
Qed.

End Chi.

Variable p : Iirr T.

Hypothesis Hp : t \in irr_constt ('Res[H] 'chi_p).

Let cP : 'Ind[G] 'chi_p != 0.
Proof. by rewrite cfInd_eq0 -?char1_eq0 ?irr_char ?irr1_neq0. Qed.

Let c := val (constt_cfInd_irr p TsG).

Let Hc : c \in irr_constt ('Ind[G] 'chi_p).
Proof. exact: valP (constt_cfInd_irr p TsG). Qed.

(* This is 6.11 (a) *)
Lemma cfInd_constt_inertia_irr : 'Ind[G] 'chi_p \in irr G.
Proof. by rewrite (cfInd_constt_inertia_constt Hp Hc) ?mem_irr. Qed.

(* This is 6.11 (d) *)
Lemma cfdot_constt_inertia :
  '['Res 'chi_p, 'chi_t] = '['Res ('Ind[G] 'chi_p), 'chi_t].
Proof. 
rewrite (cfInd_constt_inertia_constt Hp Hc).
by rewrite (cfdot_constt_inertia_constt Hp Hc).
Qed.

(* This is 6.11 (b) the domain of the induction is B *)
Lemma constt_Res_constt_inertia : t \in irr_constt ('Res ('Ind[G] 'chi_p)).
Proof. 
rewrite (cfInd_constt_inertia_constt Hp Hc).
by rewrite (constt_Res_constt_Ind Hp Hc).
Qed.

(* This is 6.11 c *)
Lemma single_constt_inertia (p' : Iirr T) :
    p' \in irr_constt ('Res ('Ind[G] 'chi_p)) ->
    t \in irr_constt('Res 'chi_p') ->
  p' = p.
Proof.
rewrite (cfInd_constt_inertia_constt Hp Hc) => Cp' Ct.
have IC: 'Res[T] 'chi_c \is a character := cfRes_char T (irr_char c).
case/(constt_charP _ IC): Cp' => chi1 IC1 Hchi1.
apply: contraTeq isT => Dpsi.
have /(constt_charP _ IC1)[chi2 IC2 Hchi2]: p \in irr_constt chi1.
  have: p \in irr_constt ('Res[T] 'chi_c).
    exact: constt_Res_inertia_constt_Ind.
  by rewrite !inE Hchi1 cfdotDl cfdot_irr (negPf Dpsi) add0r.
have: '['Res[H] 'chi_p, 'chi_t] < '['Res[H] ('Res[T] 'chi_c), 'chi_t].
  rewrite Hchi1 addrC Hchi2 !linearD !cfdotDl /=.
  rewrite -addrA addrC -subr_gt0 addrK ltr_paddl //.
    by rewrite Cnat_ge0 ?Cnat_cfdot_char_irr ?cfRes_char.
  rewrite ltr_def [~~ _]Ct Cnat_ge0 ?Cnat_cfdot_char_irr //.
  by rewrite cfRes_char ?irr_char.
rewrite cfdot_constt_inertia (cfInd_constt_inertia_constt Hp Hc).
by rewrite cfResRes // ltr_def eqxx.
Qed.

End S611A.

(* This is 6.11 b it is an injection *)
Lemma constt_inertia_inj (G H : {group gT}) (t : Iirr H) :
   H <| G ->
 {in [pred p | t \in irr_constt ('Res[H, 'I_G['chi_t]] 'chi_p)] &,
    injective (fun p => 'Ind[G, 'I_G['chi_t]] 'chi_p)}.
Proof.
move=> HnG p p' Hp Hp' Heq; set T := 'I_G[_].
have TsG: T \subset G := Inertia_sub G 'chi_t.
apply: (single_constt_inertia HnG Hp' _ Hp).
have IC1: 'Ind[G] 'chi_p \is a character := cfInd_char G (irr_char p).
have IC2: 'Res[T] ('Ind[G] 'chi_p) \is a character := cfRes_char _ IC1.
rewrite -Heq !inE cfdotC_char ?irr_char //.
rewrite Frobenius_reciprocity /= cfnorm_eq0 cfInd_eq0 ?irr_char //.
exact: (free_not0 (irr_free _) (mem_irr p)).
Qed.

(* 6.11 b the inverse function *)
Definition inertia_Ind_inv (G H : {group gT}) t (chi : 'CF(G)) :=
  odflt 0 (pick [pred t' | t \in irr_constt ('Res[H] 'chi_t') & 
                           t' \in irr_constt ('Res['I_G['chi_t]] chi)]).

Let inertia_coord (G H : {group gT}) (t : Iirr H) (c : Iirr G) :
    H <| G -> [pred p | t \in irr_constt ('Res[H] 'chi_p) &
                        p \in irr_constt ('Res['I_G['chi_t]] 'chi_c)]
               =1 xpred0 ->
   '['Res[H] 'chi_c, 'chi_t] == 0.
Proof.
set T := 'I_G['chi_t] => HnG HH.
have HsT: H \subset T := sub_Inertia _ (normal_sub HnG).
rewrite -(cfResRes _ HsT) ?Inertia_sub //= -/T.
rewrite ['Res 'chi_c]cfun_sum_cfdot linear_sum cfdot_suml big1 //= => i _.
move/negbT: (HH i); apply: contraNeq; rewrite linearZ cfdotZl mulf_eq0 //=.
by rewrite orbC negb_or.
Qed.

Lemma constt_inertia_Ind_inv (G H : {group gT}) t c :
    H <| G -> t \in irr_constt ('Res[H, G] 'chi_c) ->
  t \in irr_constt ('Res[H] 'chi_(inertia_Ind_inv t 'chi_c)).
Proof.
move=> HnG Ct.
rewrite /inertia_Ind_inv; case: pickP => [_ /andP[] //| HH].
by case/negP: Ct; apply: inertia_coord.
Qed.

Lemma inertia_Ind_inv_constt (G H : {group gT}) t c :
    H <| G -> t \in irr_constt ('Res[H, G] 'chi_c) ->
  inertia_Ind_inv t 'chi_c \in irr_constt ('Res['I_G['chi_t]] 'chi_c).
Proof.
move=> HnG Ct.
rewrite /inertia_Ind_inv; case: pickP => [_ /andP[] //| HH].
by case/negP: Ct; apply: inertia_coord.
Qed.

(* This is 6.11 b the surjective part *)
Lemma inertia_Ind_invE (G H : {group gT}) (t : Iirr H) (c : Iirr G) :
    H <| G -> t \in irr_constt ('Res[H] 'chi_c) ->
  'Ind[G] 'chi_(inertia_Ind_inv t 'chi_c) = 'chi_c.
Proof.
move=> HnG Cc.
apply: cfInd_constt_inertia_constt => //; first exact: constt_inertia_Ind_inv.
rewrite !inE -Frobenius_reciprocity cfdotC_char ?cfRes_char ?irr_char //.
exact: inertia_Ind_inv_constt.
Qed.

End S611.

Section InertiaBijection.
(* Another interface to the correspondence given by Isaacs (6.11). *)

Variables (gT : finGroupType) (G H : {group gT}) (t : Iirr H).
Variables (R : Type) (idR : R) (opR : Monoid.com_law idR) (F : 'CF(G) -> R).

Hypothesis nsHG : H <| G.
Let theta := 'chi_t.
Let T := 'I_G[theta].
Let calA := irr_constt ('Ind[T] theta).
Let calB := irr_constt ('Ind[G] theta).
Let constt_Ind_Res := constt_Ind_constt_Res.

Lemma inertia_Ind_IirrE p : p \in calA -> 'chi_(Ind_Iirr G p) = 'Ind[G] 'chi_p.
Proof.
by rewrite constt_Ind_Res => pTt; rewrite cfIirrE ?cfInd_constt_inertia_irr.
Qed.

Lemma inertia_Ind_Iirr_inj : {in calA &, injective (Ind_Iirr G)}.
Proof.
move=> p1 p2 tTp1 tTp2 /eqP; rewrite -(inj_eq irr_inj) !inertia_Ind_IirrE //.
rewrite (inj_in_eq (constt_inertia_inj _)) 1?inE -?constt_Ind_constt_Res //.
by move/eqP.
Qed.

Lemma Ind_Iirr_constt_inertia : Ind_Iirr G @: calA =i calB.
Proof.
move=> c; rewrite constt_Ind_Res; apply/imsetP/idP=> [[p tTp ->] | cGt].
  by rewrite inertia_Ind_IirrE // constt_Res_constt_inertia -?constt_Ind_Res.
pose p := inertia_Ind_inv t 'chi_c.
have calAp: p \in calA by rewrite constt_Ind_Res constt_inertia_Ind_inv.
by exists p => //; apply: irr_inj; rewrite inertia_Ind_IirrE ?inertia_Ind_invE.
Qed.

Lemma reindex_constt_inertia :
  \big[opR/idR]_(i in calB) F 'chi_i
     = \big[opR/idR]_(j in calA) F ('Ind 'chi_j).
Proof.
rewrite -(eq_bigl _ _ Ind_Iirr_constt_inertia).
rewrite (big_imset _ inertia_Ind_Iirr_inj).
by apply: eq_bigr => j /inertia_Ind_IirrE->.
Qed.

End InertiaBijection. 

(* Isaacs 6.28 preliminary *)
Section S628.

Variables (gT : finGroupType) (G : {group gT}).

Section DetRepr.

Variables (n : nat) (rG : mx_representation [fieldType of algC] G n).

Definition det_repr_mx x : 'M_1 := (\det (rG x))%:M.

Fact det_is_repr : mx_repr G det_repr_mx. 
Proof.
split=> [|g h Gg Gh]; first by rewrite /det_repr_mx repr_mx1 det1.
by rewrite /det_repr_mx repr_mxM // det_mulmx !mulmxE scalar_mxM.
Qed.

Canonical det_repr := MxRepresentation det_is_repr.
Definition detRepr := cfRepr det_repr.

Lemma detRepr_lin_char : detRepr \is a linear_char.
Proof.
by rewrite qualifE cfRepr_char cfunE group1 repr_mx1 mxtrace1 mulr1n /=.
Qed.

End DetRepr.

Definition cfDet phi := \prod_i detRepr 'Chi_i ^+ truncC '[phi, 'chi[G]_i].

Lemma cfDet_lin_char phi : cfDet phi \is a linear_char.
Proof. by apply: rpred_prod => i _; apply: rpredX; apply: detRepr_lin_char. Qed.

Lemma cfDetD :
  {in character &, {morph cfDet : phi psi / phi + psi >-> phi * psi}}.
Proof.
move=> phi psi Nphi Npsi; rewrite /= -big_split; apply: eq_bigr => i _ /=.
by rewrite -exprD cfdotDl truncCD ?nnegrE ?Cnat_ge0 // Cnat_cfdot_char_irr.
Qed.

Lemma cfDet0 : cfDet 0 = 1.
Proof. by rewrite /cfDet big1 // => i _; rewrite cfdot0l truncC0. Qed.

Lemma cfDetMn k :
  {in character, {morph cfDet : phi / phi *+ k >-> phi ^+ k}}.
Proof.
move=> phi Nphi; elim: k => [|k IHk]; rewrite ?cfDet0 // mulrS exprS -{}IHk.
by rewrite cfDetD ?rpredMn.
Qed.

Lemma cfDetRepr n rG : cfDet (cfRepr rG) = @detRepr n rG.
Proof.
transitivity (\prod_W detRepr (socle_repr W) ^+ standard_irr_coef rG W).
  rewrite (reindex _ (socle_of_Iirr_bij _)) /cfDet /=.
  apply: eq_bigr => i _; congr (_ ^+ _).
  rewrite (cfRepr_sim (mx_rsim_standard rG)) cfRepr_standard.
  rewrite cfdot_suml (bigD1 i) ?big1 //= => [|j i'j]; last first.
    by rewrite cfdotZl cfdot_irr (negPf i'j) mulr0.
  by rewrite cfdotZl cfnorm_irr mulr1 addr0 natCK.
apply/cfun_inP=> x Gx; rewrite prod_cfunE //.
transitivity (detRepr (standard_grepr rG) x); last first.
  rewrite !cfunE Gx !trace_mx11 !mxE eqxx !mulrb.
  case: (standard_grepr rG) (mx_rsim_standard rG) => /= n1 rG1 [B Dn1].
  rewrite -{n1}Dn1 in rG1 B *; rewrite row_free_unit => uB rG_B.
  by rewrite -[rG x](mulmxK uB) rG_B // !det_mulmx mulrC -!det_mulmx mulKmx.
rewrite /standard_grepr; elim/big_rec2: _ => [|W y _ _ ->].
  by rewrite cfunE trace_mx11 mxE Gx det1.
rewrite !cfunE Gx /= !{1}trace_mx11 !{1}mxE det_ublock; congr (_ * _).
rewrite exp_cfunE //; elim: (standard_irr_coef rG W) => /= [|k IHk].
  by rewrite /muln_grepr big_ord0 det1.
rewrite exprS /muln_grepr big_ord_recl det_ublock -IHk; congr (_ * _).
by rewrite cfunE trace_mx11 mxE Gx.
Qed.

Lemma cfDet_id xi : xi \is a linear_char -> cfDet xi = xi.
Proof.
move=> lin_xi; have /irrP[i Dxi] := lin_char_irr lin_xi.
apply/cfun_inP=> x Gx; rewrite Dxi -irrRepr cfDetRepr !cfunE trace_mx11 mxE.
move: lin_xi (_ x) => /andP[_]; rewrite Dxi irr1_degree pnatr_eq1 => /eqP-> X.
by rewrite {1}[X]mx11_scalar det_scalar1 trace_mx11.
Qed.

Definition cfDet_order phi := #[cfDet phi]%CF.

Definition cfDet_order_lin xi :
  xi \is a linear_char -> cfDet_order xi = #[xi]%CF.
Proof. by rewrite /cfDet_order => /cfDet_id->. Qed.

Lemma lin_char_group:
     {linG : finGroupType & {cF : linG -> 'CF(G) | 
         [/\ injective cF, forall l, cF l \is a linear_char
          & forall phi, phi \is a linear_char -> exists l, phi = cF l]
       & [/\ {morph cF : k l / (k * l)%g >-> (k * l)%R},
              cF 1%g = 1%R &
             {morph cF: l / l^-1%g >-> l^-1%CF} ]}}. 
Proof.
pose linT := {i : Iirr G | 'chi_i \is a linear_char}.
pose cF (k : linT) := 'chi_(sval k).
have cFlin k: cF k \is a linear_char := svalP k.
have cFinj: injective cF := inj_comp irr_inj val_inj.
have inT xi : xi \is a linear_char -> {k | cF k = xi}.
  move=> lin_xi; have /irrP/sig_eqW[i Dxi] := lin_char_irr lin_xi.
  by apply: (exist _ (Sub i _)) => //; rewrite -Dxi.
have [one cFone] := inT 1 (rpred1 _).
pose inv k := sval (inT _ (rpredVr (cFlin k))).
pose mul k l := sval (inT _ (rpredM (cFlin k) (cFlin l))).
have cFmul k l: cF (mul k l) = cF k * cF l := svalP (inT _ _).
have cFinv k: cF (inv k) = (cF k)^-1 := svalP (inT _ _).
have mulA: associative mul by move=> k l m; apply: cFinj; rewrite !cFmul mulrA.
have mul1: left_id one mul by move=> k; apply: cFinj; rewrite cFmul cFone mul1r.
have mulV: left_inverse one inv mul.
  by move=> k; apply: cFinj; rewrite cFmul cFinv cFone mulVr ?lin_char_unitr.
pose linB := BaseFinGroupType linT (FinGroup.Mixin mulA mul1 mulV).
by exists (@FinGroupType linB mulV), cF; split=> // xi /inT[k <-]; exists k.
Qed.

Section S616. 

Variable (N : {group gT}).

Variable t f: Iirr N.

Let T := 'I_G['chi_t]%G.
Let F := 'I_G['chi_f]%G.

Hypothesis NnG : N <| G.

Let sNG : N \subset G. Proof. exact: normal_sub. Qed.

Let FsG : F \subset G. Proof. exact: subsetIl. Qed.

Let NsF : N \subset F. Proof. exact: sub_Inertia. Qed.

Let NnF : N <| F. Proof. exact: normal_Inertia. Qed.

Hypothesis finv : 'I_G['chi_f] = G.

Fact ResIndchiquo: 'Res[N]  ('Ind[G] 'chi_f) = #|G : N|%:R *: 'chi_f.
Proof.
have [_ nNG] := andP NnG.
have sum_finv: \sum_(xi <- ('chi_f ^: G)%CF) xi = 'chi_f.
  by rewrite -finv cfclass_inertia  big_seq1.
have ResIndmulchi: 'Res[N]  ('Ind[G] 'chi_f) \in <['chi_f]> %VS. 
  rewrite (cfun_sum_constt ('Ind[G] 'chi_f)) linear_sum /= memv_suml // => i Hi.
  rewrite constt_Ind_constt_Res in Hi.
  rewrite linearZ /= (Clifford_Res_sum_cfclass NnG Hi) scalerA.
  by rewrite sum_finv  memvZ ?memv_line.
rewrite ResIndchiE //.
suff -> :  (\sum_(y in G) ('chi_f ^ y)%CF) = #|G|%:R *: 'chi_f.
  rewrite scalerA; congr (_ *: _);  apply :(mulfI (neq0CG N)).
  by rewrite mulrA  -natrM Lagrange // mulfV ?mul1r //  (neq0CG N).
apply/cfunP=> y; rewrite sum_cfunE !cfunE.
rewrite (eq_bigr (fun i => 'chi_f y)); first by rewrite sumr_const  mulr_natl.
move => i ; rewrite -finv inE => /andP [inG iner].
by rewrite inertiaJ.
Qed.
 
Hypothesis tinvariant : T = G.
Hypothesis ft_irr : 'chi_f * 'chi_t \in irr N.
Hypothesis indt_irr  : 'Ind[G] 'chi_t \in irr G.

Variable b : Iirr G.

Hypothesis Hb : b \in irr_constt ('Ind[G] 'chi_f).

End S616.

End S628.

Notation "''o' ( phi )" := (cfDet_order phi)
  (at level 8, format "''o' ( phi )") : cfun_scope.

Section Frobenius.

Variables (gT : finGroupType) (G K : {group gT}).

(* Because he only defines Frobenius groups in chapter 7, Isaacs does not     *)
(* state these theorems using the Frobenius property.                         *)
Hypothesis frobGK : [Frobenius G with kernel K].

(* This is Isaacs, Theorem 6.34(a1). *)
Theorem inertia_Frobenius_ker i : i != 0 -> 'I_G['chi[K]_i] = K.
Proof.
have [_ _ nsKG regK] := Frobenius_kerP frobGK; have [sKG nKG] := andP nsKG.
move=> nzi; apply/eqP; rewrite eqEsubset sub_Inertia // andbT.
apply/subsetP=> x /setIP[Gx /setIdP[nKx /eqP x_stab_i]].
have actIirrK: is_action G (@conjg_Iirr _ K).
  split=> [y j k eq_jk | j y z Gy Gz].
    by apply/irr_inj/(can_inj (cfConjgK y)); rewrite -!conjg_IirrE eq_jk.
  by apply: irr_inj; rewrite !conjg_IirrE (cfConjgM _ nsKG).
pose ito := Action actIirrK; pose cto := ('Js \ (subsetT G))%act.
have acts_Js : [acts G, on classes K | 'Js].
  apply/subsetP=> y Gy; have nKy := subsetP nKG y Gy.
  rewrite !inE; apply/subsetP=> _ /imsetP[z Gz ->]; rewrite !inE /=.
  rewrite -class_rcoset norm_rlcoset // class_lcoset.
  by apply: mem_imset; rewrite memJ_norm.
have acts_cto : [acts G, on classes K | cto] by rewrite astabs_ract subsetIidl.
pose m := #|'Fix_(classes K | cto)[x]|.
have def_m: #|'Fix_ito[x]| = m.
  apply: card_afix_irr_classes => // j y _ Ky /imsetP[_ /imsetP[z Kz ->] ->].
  by rewrite conjg_IirrE cfConjgEJ // cfunJ.
have: (m != 1)%N.
  rewrite -def_m (cardD1 (0 : Iirr K)) (cardD1 i) !(inE, sub1set) /=.
  by rewrite conjg_Iirr0 nzi eqxx -(inj_eq irr_inj) conjg_IirrE x_stab_i eqxx.
apply: contraR => notKx; apply/cards1P; exists 1%g; apply/esym/eqP.
rewrite eqEsubset !(sub1set, inE) classes1 /= conjs1g eqxx /=.
apply/subsetP=> _ /setIP[/imsetP[y Ky ->] /afix1P /= cyKx].
have /imsetP[z Kz def_yx]: y ^ x \in y ^: K.
  by rewrite -cyKx; apply: mem_imset; exact: class_refl.
rewrite inE classG_eq1; apply: contraR notKx => nty.
rewrite -(groupMr x (groupVr Kz)).
apply: (subsetP (regK y _)); first exact/setD1P.
rewrite !inE groupMl // groupV (subsetP sKG) //=.
by rewrite conjg_set1 conjgM def_yx conjgK.
Qed.

(* This is Isaacs, Theorem 6.34(a2) *)
Theorem irr_induced_Frobenius_ker i : i != 0 -> 'Ind[G, K] 'chi_i \in irr G.
Proof.
move/inertia_Frobenius_ker/group_inj=> defK.
have [_ _ nsKG _] := Frobenius_kerP frobGK.
have/(_ i):= cfInd_constt_inertia_irr nsKG; rewrite defK => -> //.
by rewrite inE /= cfRes_id cfnorm_eq0 irr_neq0.
Qed.

(* This is Isaacs, Theorem 6.34(b) *)
Theorem Frobenius_Ind_irrP j :
  reflect (exists2 i, i != 0 & 'chi_j = 'Ind[G, K] 'chi_i)
          (~~ (K \subset cfker 'chi_j)).
Proof.
have [_ _ nsKG _] := Frobenius_kerP frobGK; have [sKG nKG] := andP nsKG.
apply: (iffP idP) => [not_chijK1 | [i nzi ->]]; last first.
  by rewrite cfker_Ind_irr ?sub_gcore // subGcfker.
have /neq0_has_constt[i chijKi]: 'Res[K] 'chi_j != 0 by exact: Res_irr_neq0.
have nz_i: i != 0.
  by apply: contraNneq not_chijK1 => i0; rewrite constt0_Res_cfker // -i0.
have /irrP[k def_chik] := irr_induced_Frobenius_ker nz_i. 
have: '['chi_j, 'chi_k] != 0 by rewrite -def_chik -cfdot_Res_l.
by rewrite cfdot_irr pnatr_eq0; case: (j =P k) => // ->; exists i.
Qed.

End Frobenius.
