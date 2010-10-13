(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection11.

(******************************************************************************)
(*   This file covers B & G, section 12; it defines the prime sets for the    *)
(* complements of M`_\sigma in a maximal group M:                             *)
(*    \tau1(M) == the set of p not in \pi(M^`(1)) (thus not in \sigma(M)),    *)
(*                such that M has p-rank 1.                                   *)
(*    \tau2(M) == the set of p not in \sigma(M), such that M has p-rank 2.    *)
(*    \tau3(M) == the set of p not in \sigma(M), but \pi(M^`(1)), such that   *)
(*                M has p-rank 1.                                             *)
(*   We also define the following helper predicate, which encapsulates the    *)
(* notation conventions defined at the beginning of B & G, Section 12:        *)
(*   sigma_complement M E E1 E2 E3 <=>                                        *)
(*                E is a Hall \sigma(M)^'-subgroup of M, the Ei are Hall      *)
(*                \tau_i(M)-subgroups of E, and E2 * E1 is a group.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(* to go in prime.v *)
Lemma pi_of_partn : forall pi n, n > 0 -> \pi(n`_pi) =i [predI \pi(n) & pi].
Proof.
move=> pi n n_gt0 p; rewrite 5!inE !mem_primes n_gt0 part_gt0 /= -andbA.
apply: andb_id2l => p_pr; rewrite -{2}(partnC pi n_gt0) andbC.
have [pi_p | ] := boolP (p \in _).
  by rewrite mulnC gauss // (pnat_coprime _ (part_pnat _ _)) ?pnatE.
by apply: contraNF => pi_p; rewrite -pnatE // (pnat_dvd pi_p) ?part_pnat.
Qed.

Lemma sub_pnat_coprime : forall (pi rho : nat_pred) m n,
  {subset rho <= pi^'} -> pi.-nat m -> rho.-nat n -> coprime m n.
Proof.
move=> pi rho m n pi'rho pi_m; move/(sub_in_pnat (in1W pi'rho)).
exact: pnat_coprime.
Qed.

(* to go in finset.v *)
Lemma subset_leqif_cards : forall (fT : finType) (A B : {set fT}),
    A \subset B -> (#|A| <= #|B| ?= iff (A == B)).
Proof.
by move=> fT A B sAB; rewrite eqEsubset sAB; exact: subset_leqif_card.
Qed.

(* to go in commutator.v *)
Lemma derJ : forall (gT : finGroupType) (G : {group gT}) n x,
  (G :^ x)^`(n) = G^`(n) :^ x.
Proof.
by move=> gT G n x; elim: n => //= n IHn; rewrite !dergSn IHn -conjsRg.
Qed.

Section Definitions.

Variables (gT : minSimpleOddGroupType) (M : {set gT}).
Local Notation sigma' := \sigma(M)^'.

Definition tau1 :=
  [pred p \in sigma' | ('r_p(M) == 1%N) && ~~ (p %| #|M^`(1)|)].
Definition tau2 :=
  [pred p \in sigma' | 'r_p(M) == 2].
Definition tau3 :=
  [pred p \in sigma' | ('r_p(M) == 1%N) && (p %| #|M^`(1)|)].

Definition sigma_complement E E1 E2 E3 :=
  [/\ sigma'.-Hall(M) E, tau1.-Hall(E) E1, tau2.-Hall(E) E2, tau3.-Hall(E) E3
    & group_set (E2 * E1)].

End Definitions.

Notation "\tau1 ( M )" := (tau1 M)
  (at level 2, format "\tau1 ( M )") : group_scope.
Notation "\tau2 ( M )" := (tau2 M)
  (at level 2, format "\tau2 ( M )") : group_scope.
Notation "\tau3 ( M )" := (tau3 M)
  (at level 2, format "\tau3 ( M )") : group_scope.

Section Section12.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Let grT := {group gT}.

Implicit Types p q r : nat.
Implicit Types A E H K M Mstar N P Q R S T U V W X Y : {group gT}.

Section Introduction.

Variables M E : {group gT}.
Hypotheses (maxM : M \in 'M) (hallE : \sigma(M)^'.-Hall(M) E).

Lemma tau1J : forall x, \tau1(M :^ x) =i \tau1(M).
Proof. by move=> x p; rewrite 6!inE sigmaJ p_rankJ derg1 -conjsRg cardJg. Qed.

Lemma tau2J : forall x, \tau2(M :^ x) =i \tau2(M).
Proof. by move=> x p; rewrite 6!inE sigmaJ p_rankJ. Qed.

Lemma tau3J : forall x, \tau3(M :^ x) =i \tau3(M).
Proof. by move=> x p; rewrite 6!inE sigmaJ p_rankJ derg1 -conjsRg cardJg. Qed.

Lemma tau2'1 : {subset \tau1(M) <= \tau2(M)^'}.
Proof. by move=> p; rewrite !inE; case/and3P=> ->; move/eqP->. Qed.

Lemma tau3'1 : {subset \tau1(M) <= \tau3(M)^'}.
Proof. by move=> p; rewrite !inE; case/and3P=> -> ->. Qed.

Lemma tau3'2 : {subset \tau2(M) <= \tau3(M)^'}.
Proof. by move=> p; rewrite !inE; case/andP=> ->; move/eqP->. Qed.

Let solE : solvable E := solvableS (pHall_sub hallE) (mmax_sol maxM).

Let exHallE pi := exists Ei : {group gT}, pi.-Hall(E) Ei.
Lemma tau13_complements_exist : exHallE \tau1(M) /\ exHallE \tau3(M).
Proof. by split; exact: Hall_exists. Qed.

Lemma sigma_complement_exists : forall E1 E3,
    \tau1(M).-Hall(E) E1 -> \tau3(M).-Hall(E) E3 ->
  exists2 E2 : {group gT}, \tau2(M).-Hall(E) E2 & sigma_complement M E E1 E2 E3.
Proof.
move=> E1 E3 hallE1 hallE3; have [sE1E t1E1 _] := and3P hallE1.
pose tau12 := [predU \tau1(M) & \tau2(M)].
have t12E1: tau12.-group E1.
  by apply: sub_in_pnat t1E1 => p _ t1p; apply/orP; left.
have [E21 hallE21 sE1E21] := Hall_superset solE sE1E t12E1.
have [sE21E t12E21 _] := and3P hallE21.
have [E2 hallE2] := Hall_exists \tau2(M) (solvableS sE21E solE).
have [sE2E21 t2E2 _] := and3P hallE2.
have hallE2_E: \tau2(M).-Hall(E) E2.
  rewrite pHallE (subset_trans sE2E21 sE21E) (card_Hall hallE2).
  by rewrite (card_Hall hallE21) partn_part //= => p t2p; apply/orP; right.
exists E2 => //; split=> //.
suffices ->: E2 * E1 = E21 by exact: groupP.
have coE21: coprime #|E2| #|E1| := sub_pnat_coprime tau2'1 t2E2 t1E1.
apply/eqP; rewrite eqEcard mul_subG ?coprime_cardMg //=.
rewrite -(partnC \tau1(M) (cardG_gt0 E21)) (card_Hall hallE2) mulnC.
rewrite (card_Hall (pHall_subl sE1E21 sE21E hallE1)) leq_pmul2r //.
rewrite dvdn_leq // sub_in_partn // => p t12p t1'p.
by apply: contraLR (pnatPpi t12E21 t12p) => t2'p; exact/norP.
Qed.

Lemma coprime_sigma_compl : coprime #|M`_\sigma| #|E|.
Proof. exact: pnat_coprime (pcore_pgroup _ _) (pHall_pgroup hallE). Qed.
Let coMsE := coprime_sigma_compl.

Lemma pi_mmax_compl : \pi(#|E|) =i [predD \pi(#|M|) & \sigma(M)].
Proof. by move=> p; rewrite (card_Hall hallE) pi_of_partn // !inE andbC. Qed.

Lemma sdprod_mmax : M`_\sigma ><| E = M.
Proof.
have sEM := pHall_sub hallE.
rewrite sdprodE ?coprime_TIg ?(subset_trans sEM) ?bgFunc_norm //.
apply/eqP; rewrite eqEcard mul_subG ?pcore_sub ?coprime_cardMg //=.
by rewrite (card_Hall (Hall_M_Msigma maxM)) (card_Hall hallE) partnC.
Qed.

(* The preliminary remarks in the introduction of B & G, section 12. *)

Lemma der1_mmax_compl : M^`(1) :&: E = E^`(1).
Proof.
have [nsMsM sEM defM _ _] := sdprod_context sdprod_mmax.
rewrite  setIC (prod_norm_coprime_subs_derI defM _ (subxx E)) 1?coprime_sym //.
by rewrite (setIidPr (der_sub 1 E)).
Qed.

Lemma partition_pi_mmax :
  \pi(#|M|) =i
     [predU [predU [predU \tau1(M) & \tau2(M)] & \tau3(M)] & \sigma(M)].
Proof.
move=> p; symmetry; rewrite 8!inE /= -!andb_orr orbAC -andb_orr.
rewrite (orbC (~~ _)) orbC orb_andr !orbN andbT /=.
have [sMp | /= sM'p] := boolP (p \in _); first by rewrite sigma_sub_pi.
rewrite -p_rank_gt0 eqn_leq orbC orb_andr -ltnS -leq_eqVlt eqn_leq leqNgt.
by rewrite (contra ((alpha_sub_sigma maxM) p)) //= orb_idl //; exact: ltnW.
Qed.

Lemma partition_pi_mmax_compl :
  \pi(#|E|) =i [predU [predU \tau1(M) & \tau2(M)] & \tau3(M)].
Proof.
move=> p; rewrite pi_mmax_compl inE /= partition_pi_mmax !andb_orr /=.
by rewrite -(andbC (p \in \sigma(M))) andbN orbF !(andbb, andbA) -!andbA.
Qed.

Lemma tau2E : \tau2(M) =i [pred p \in \pi(#|E|) | 'r_p(E) == 2].
Proof.
move=> p; have [P sylP] := Sylow_exists p E.
rewrite 4!inE -(andb_idl (pnatPpi (pHall_pgroup hallE))) -andbA.
apply: andb_id2l => sM'p; have sylP_M := pSylow_Hall_Sylow hallE sM'p sylP.
rewrite (p_rank_Sylow sylP_M) -(p_rank_Sylow sylP) -p_rank_gt0 andbC.
by case: eqP => // ->.
Qed.

Lemma tau3E : \tau3(M) =i [pred p \in \pi(#|E^`(1)|) | 'r_p(E) == 1%N].
Proof.
move=> p; have [P sylP] := Sylow_exists p E.
have hallE': \sigma(M)^'.-Hall(M^`(1)) E^`(1).
  by rewrite -der1_mmax_compl setIC (Hall_setI_normal _ hallE) ?der_normal.
rewrite 4!inE -(andb_idl (pnatPpi (pHall_pgroup hallE'))) -andbA.
apply: andb_id2l => sM'p; have sylP_M := pSylow_Hall_Sylow hallE sM'p sylP.
rewrite (p_rank_Sylow sylP_M) -(p_rank_Sylow sylP) andbC; apply: andb_id2r.
rewrite eqn_leq p_rank_gt0 mem_primes; case/and3P=> _ p_pr _.
rewrite (card_Hall hallE') pi_of_partn 3?inE ?mem_primes ?cardG_gt0 //=.
by rewrite p_pr sM'p andbT.
Qed.

Lemma tau1E :
  \tau1(M) =i [pred p \in [predD \pi(#|E|) & \pi(#|E^`(1)|)] | 'r_p(E) == 1%N].
Proof.
move=> p; symmetry; rewrite inE /= andbAC andbC /= partition_pi_mmax_compl.
rewrite inE /= -orbA /=; apply/idP/idP=> [|t1p].
  case/and3P=> piEp not_piE'p rE; case/or3P: piEp => //=.
    by rewrite tau2E !inE (eqP rE) andbF.
  by rewrite tau3E 2!inE (negPf not_piE'p).
have [sM'p rpM _] := and3P t1p; have [P sylP] := Sylow_exists p E.
have:= tau3'1 t1p; rewrite t1p andTb inE /= tau3E !inE /= (p_rank_Sylow sylP).
by rewrite -(p_rank_Sylow (pSylow_Hall_Sylow hallE sM'p sylP)) rpM !andbT.
Qed.

(* This is B & G, Lemma 12.1(a). *)
Lemma mmax_compl_nil : nilpotent E^`(1).
Proof.
have [sE'E sEM] := (der_sub 1 E, pHall_sub hallE).
have nMaE: E \subset 'N(M`_\alpha) by rewrite (subset_trans sEM) ?bgFunc_norm.
have tiMaE': E^`(1) :&: M`_\alpha = 1.
  by apply/trivgP; rewrite -(coprime_TIg coMsE) setIC setISS ?Malpha_sub_Msigma.
rewrite (isog_nil (quotient_isog (subset_trans sE'E nMaE) tiMaE')).
by rewrite (nilpotentS (quotientS _ (dergS 1 sEM))) ?nil_M'Malpha.
Qed.

(* This is B & G, Lemma 12.1(g). *)
Lemma tau2_not_beta : forall p,
  p \in \tau2(M) -> p \notin \beta(G) /\ {subset 'E_p^2(M) <= 'E*_p(G)}. 
Proof.
move=> p; case/andP=> sM'p; move/eqP=> rpM.
split; first exact: sigma'_rank2_beta' rpM.
by apply/subsetP; exact: sigma'_rank2_max.
Qed.

End Introduction.

Implicit Arguments tau2'1 [[M] x].
Implicit Arguments tau3'1 [[M] x].
Implicit Arguments tau3'2 [[M] x].

(* This is the rest of B & G, Lemma 12.1 (parts b, c, d,e, and f). *)
Lemma sigma_complement_context : forall M E E1 E2 E3,
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
  [/\ (*b*) E3 \subset E^`(1) /\ E3 <| E,
      (*c*) E2 :==: 1 -> E1 :!=: 1,
      (*d*) cyclic E1 /\ cyclic E3,
      (*e*) E3 ><| (E2 ><| E1) = E /\ E3 ><| E2 ><| E1 = E 
    & (*f*) 'C_E3(E) = 1].
Proof.
move=> M E E1 E2 E3 maxM [hallE hallE1 hallE2 hallE3 groupE21].
have [sEM solM] := (pHall_sub hallE, mmax_sol maxM). 
have [[sE1E t1E1 _] [sE3E t3E3 _]] := (and3P hallE1, and3P hallE3).
have tiE'E1: E^`(1) :&: E1 = 1.
  rewrite coprime_TIg // coprime_pi' ?cardG_gt0 //.
  by apply: sub_in_pnat t1E1 => p _; rewrite (tau1E maxM hallE); do 2!case/andP.
have cycE1: cyclic E1.
  apply: nil_Zgroup_cyclic.
    rewrite odd_rank1_Zgroup ?mFT_odd //; apply: wlog_neg; rewrite -ltnNge.
    have [p p_pr ->]:= rank_witness E1; move/ltnW; rewrite p_rank_gt0.
    move/(pnatPpi t1E1); rewrite (tau1E maxM hallE); case/andP=> _.
    by move/eqP <-; rewrite p_rankS.
  rewrite abelian_nil // /abelian (sameP commG1P trivgP) -tiE'E1.
  by rewrite subsetI (der_sub 1) (dergS 1).
have solE: solvable E := solvableS sEM solM.
have nilE': nilpotent E^`(1) := mmax_compl_nil maxM hallE.
have nsE'piE: forall pi, 'O_pi(E^`(1)) <| E.
  move=> pi; exact: char_normal_trans (pcore_char _ _) (der_normal _ _).
have SylowE3: forall P,
  Sylow E3 P -> [/\ cyclic P, P \subset E^`(1) & 'C_P(E) = 1].
- move=> P; case/SylowP=> p p_pr sylP; have [sPE3 pP _] := and3P sylP.
  have [-> | ntP] := eqsVneq P 1.
    by rewrite cyclic1 sub1G (setIidPl (sub1G _)).
  have t3p: p \in \tau3(M).
    rewrite (pnatPpi t3E3) // -p_rank_gt0 (p_rank_Sylow sylP) -rank_pgroup //.
    by rewrite rank_gt0.
  have sPE: P \subset E := subset_trans sPE3 sE3E.
  have cycP: cyclic P.
    rewrite (odd_pgroup_rank1_cyclic pP) ?mFT_odd //.
    rewrite (tau3E maxM hallE) in t3p.
    by case/andP: t3p => _; move/eqP=> <-; rewrite p_rankS.
  have nEp'E: E \subset 'N('O_p^'(E)) by exact: bgFunc_norm.
  have nEp'P := subset_trans sPE nEp'E.
  have sylP_E := pSylow_Hall_Sylow hallE3 t3p sylP.
  have nsEp'P_E: 'O_p^'(E) <*> P <| E.
    rewrite sub_der1_normal ?mulgen_subG ?pcore_sub //=.
    rewrite norm_mulgenEr // -quotientSK //=; last first.
      by rewrite (subset_trans (der_sub 1 E)).
    have [_ /= <- _ _] := dprodP (nilpotent_pcoreC p nilE').
    rewrite -quotient_mulg -mulgA (mulSGid (pcore_max _ _)) ?pcore_pgroup //=.
    rewrite quotient_mulg quotientS //.
    apply: subset_trans (pcore_sub_Hall sylP_E).
    by rewrite pcore_max ?pcore_pgroup /=.
  have nEP_sol: solvable 'N_E(P) by rewrite (solvableS _ solE) ?subsetIl.
  have [K hallK] := Hall_exists p^' nEP_sol; have [sKNEP p'K _] := and3P hallK.
  have coPK: coprime #|P| #|K| := pnat_coprime pP p'K.
  have sP_NEP: P \subset 'N_E(P) by rewrite subsetI sPE normG.
  have mulPK: P * K = 'N_E(P).
    apply/eqP; rewrite eqEcard mul_subG //= coprime_cardMg // (card_Hall hallK).
    by rewrite (card_Hall (pHall_subl sP_NEP (subsetIl E _) sylP_E)) partnC.
  rewrite subsetI in sKNEP; case/andP: sKNEP => sKE nPK.
  have nEp'K := subset_trans sKE nEp'E.
  have defE: 'O_p^'(E) <*> K * P = E.
    have sP_Ep'P: P \subset 'O_p^'(E) <*> P := mulgen_subr _ _.
    have sylP_Ep'P := pHall_subl sP_Ep'P (normal_sub nsEp'P_E) sylP_E.
    rewrite -{2}(Frattini_arg nsEp'P_E sylP_Ep'P) /= !norm_mulgenEr //.
    by rewrite -mulgA (normC nPK) -mulPK -{1}(mulGid P) !mulgA.
  have ntPE': P :&: E^`(1) != 1.
    have sylPE' := Hall_setI_normal (der_normal 1 E) sylP_E. 
    rewrite -rank_gt0 (rank_pgroup (pHall_pgroup sylPE')).
    rewrite -(p_rank_Sylow sylPE') p_rank_gt0.
    by rewrite (tau3E maxM hallE) in t3p; case/andP: t3p.
  have defP := coprime_abelian_cent_dprod nPK coPK (cyclic_abelian cycP).
  have{defP} [[PK1 _]|[regKP defP]] := cyclic_pgroup_dprod_trivg pP cycP defP.
    have coP_Ep'K: coprime #|P| #|'O_p^'(E) <*> K|.
      rewrite (pnat_coprime pP) -/(pgroup _ _) ?norm_mulgenEr //.
      by rewrite pgroupM pcore_pgroup.
    rewrite -subG1 -(coprime_TIg coP_Ep'K) setIS ?der1_min // in ntPE'.
      rewrite -{1}defE mulG_subG normG norms_mulgen // cents_norm //.
      exact/commG1P.
    by rewrite -{2}defE quotient_mulgr quotient_abelian ?cyclic_abelian.
  split=> //; first by rewrite -defP commgSS.
  by apply/trivgP; rewrite -regKP setIS ?centS.
have sE3E': E3 \subset E^`(1).
  by rewrite -(Sylow_gen E3) gen_subG; apply/bigcupsP=> P; case/SylowE3.
have cycE3: cyclic E3.
  rewrite nil_Zgroup_cyclic ?(nilpotentS sE3E') //.
  by apply/forall_inP => P; case/SylowE3.
have regEE3: 'C_E3(E) = 1.
  have [// | [p p_pr]] := trivgVpdiv 'C_E3(E).
  case/Cauchy=> // x; case/setIP; rewrite -!cycle_subG=> sXE3 cEX ox.
  have pX: p.-elt x by rewrite /p_elt ox pnat_id.
  have [P sylP sXP] := Sylow_superset sXE3 pX.
  suffices: <[x]> == 1 by case/idPn; rewrite cycle_eq1 -order_gt1 ox prime_gt1.
  rewrite -subG1; case/SylowE3: (p_Sylow sylP) => _ _ <-.
  by rewrite subsetI sXP.
have nsE3E: E3 <| E.
  have hallE3_E' := pHall_subl sE3E'  (der_sub 1 E) hallE3.
  by rewrite (nilpotent_Hall_pcore nilE' hallE3_E') /=.
have [sE2E t2E2 _] := and3P hallE2; have [_ nE3E] := andP nsE3E.
have coE21: coprime #|E2| #|E1| := sub_pnat_coprime tau2'1 t2E2 t1E1.
have coE31: coprime #|E3| #|E1| := sub_pnat_coprime tau3'1 t3E3 t1E1.
have coE32: coprime #|E3| #|E2| := sub_pnat_coprime tau3'2 t3E3 t2E2.
have{groupE21} defE: E3 ><| (E2 ><| E1) = E.
  have defE21: E2 * E1 = E2 <*> E1 by rewrite -genM_mulgen gen_set_id.
  have sE21E: E2 <*> E1 \subset E by rewrite mulgen_subG sE2E.
  have nE3E21 := subset_trans sE21E nE3E.
  have coE312: coprime #|E3| #|E2 <*> E1|.
    by rewrite -defE21 coprime_cardMg // coprime_mulr coE32.
  have nE21: E1 \subset 'N(E2).
    rewrite (subset_trans (mulgen_subr E2 E1)) ?sub_der1_norm ?mulgen_subl //.
    rewrite /= -{2}(mulg1 E2) -(setIidPr (der_sub 1 _)) /=.
    rewrite -(coprime_mulG_setI_norm defE21) ?bgFunc_norm //.
    by rewrite mulgSS ?subsetIl // -tiE'E1 setIC setSI ?dergS.
  rewrite (sdprodEgen nE21) ?sdprodE ?coprime_TIg //=.
  apply/eqP; rewrite eqEcard mul_subG // coprime_cardMg //= -defE21.
  rewrite -(partnC \tau3(M) (cardG_gt0 E)) (card_Hall hallE3) leq_mul //.
  rewrite coprime_cardMg // (card_Hall hallE1) (card_Hall hallE2).
  rewrite -[#|E|`__](partnC \tau2(M)) ?leq_mul ?(partn_part _ tau3'2) //.
  rewrite -partnI dvdn_leq // sub_in_partn // => p piEp; apply/implyP.
  rewrite implybE orbC negb_and !negbK orbA orbAC.
  by rewrite (partition_pi_mmax_compl maxM hallE) in piEp.
split=> //; last split=> //.
  move/eqP=> E2_1; apply/eqP=> E1_1.
  apply: negP (sol_der1_proper solM (subxx _) (mmax_neq1 maxM)).
  case/sdprodP: (sdprod_mmax maxM hallE) => _ defM _ _.
  rewrite properE der_sub /= negbK -{1}defM mulG_subG Msigma_sub_M' //.
  by rewrite -defE E1_1 E2_1 !sdprodg1 (subset_trans sE3E') ?dergS //.
case/sdprodP: defE => [[_ E21 _ defE21]]; rewrite defE21 => defE nE321 tiE321.
have{defE21} [_ defE21 nE21 tiE21] := sdprodP defE21.
have [nE32 nE31] := (subset_trans sE2E nE3E, subset_trans sE1E nE3E).
rewrite [E3 ><| _]sdprodEgen ? sdprodE ?coprime_TIg ?norms_mulgen //=.
  by rewrite norm_mulgenEr // -mulgA defE21.
by rewrite norm_mulgenEr // coprime_cardMg // coprime_mull coE31.
Qed.

(* This is B & G, Lemma 12.2(a). *)
Lemma prime_class_mmax_norm : forall M p X,
     M \in 'M -> p.-group X -> 'N(X) \subset M ->
  (p \in \sigma(M)) || (p \in \tau2(M)).
Proof.
move=> M p X maxM pX sNM; rewrite -implyNb; apply/implyP=> sM'p. 
by rewrite 3!inE /= sM'p (sigma'_norm_mmax_rank2 _ _ pX).
Qed.

(* This is B & G, Lemma 12.2(b). *)
Lemma mmax_norm_notJ : forall M Mstar p X,
    M \in 'M -> Mstar \in 'M ->
    p.-group X -> X \subset M -> 'N(X) \subset Mstar ->
    [|| [&& p \in \sigma(M) & M :!=: Mstar], p \in \tau1(M) | p \in \tau3(M)] ->
  gval Mstar \notin M :^: G.
Proof.
move=> M Mstar p X maxM maxMstar pX sXM sNMstar.
apply: contraL => MG_Mstar; have [x Gx defMstar] := imsetP MG_Mstar.
have [sMp | sM'p] := boolP (p \in \sigma(M)); last first.
  have:= prime_class_mmax_norm maxMstar pX sNMstar.
  rewrite defMstar /= sigmaJ tau2J !negb_orb (negPf sM'p) /= => t2Mp.
  by rewrite (contraL (@tau2'1 _ p)) // [~~ _]tau3'2.
rewrite 4!inE /= sMp inE /= sMp /= orbF negbK.
have ntX: X :!=: 1.
  by apply: contraTneq sNMstar => ->; rewrite norm1 proper_subn ?mmax_proper.
have [_ transCX _ _] := mmax_sigma_core_nt_pgroup maxM sMp ntX pX.
set maxMX := finset _ in transCX.
have maxMX_Mstar: gval Mstar \in maxMX.
  by rewrite inE MG_Mstar (subset_trans (normG X)).
have maxMX_M: gval M \in maxMX by rewrite inE orbit_refl.
have [y cXy ->] := atransP2 transCX maxMX_Mstar maxMX_M.
by rewrite /= conjGid // (subsetP sNMstar) // (subsetP (cent_sub X)).
Qed.

(* This is B & G, Lemma 12.3. *)
Lemma nonuniq_p2Elem_cent_sigma : forall M Mstar p A A0,
    M \in 'M -> Mstar \in 'M -> Mstar :!=: M -> A \in 'E_p^2(M) ->
    A0 \in 'E_p^1(A) -> 'N(A0) \subset Mstar ->
 [/\ (*a*) p \notin \sigma(M) -> A \subset 'C(M`_\sigma :&: Mstar)
   & (*b*) p \notin \alpha(M) -> A \subset 'C(M`_\alpha :&: Mstar)].
Proof.
move=> M H p A A0 maxM maxH neqMH Ep2A EpA0 sNH.
have p_pr := pnElem_prime Ep2A.
have [sAM abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [sA0A _ _] := pnElemP EpA0; have pA0 := pgroupS sA0A pA.
have sAH: A \subset H.
  by apply: subset_trans (cents_norm _) sNH; exact: subset_trans (centS sA0A).
have nsHsH: H`_\sigma <| H by exact: pcore_normal.
have [sHsH nHsH] := andP nsHsH; have nHsA := subset_trans sAH nHsH.
have nsHsA_H: H`_\sigma <*> A <| H.
  have [sHp | sH'p] := boolP (p \in \sigma(H)).
    rewrite (mulgen_idPl _) ?pcore_normal //.
    rewrite (subset_normal_Hall _ (Hall_M_Msigma _)) ?pcore_normal //.
    by rewrite /psubgroup sAH /pgroup (pi_pnat pA).
  have [P sylP sAP] := Sylow_superset sAH pA.
  have excH: exceptional_FTmaximal p H A0 A by split=> //; exact/pnElemP.
  exact: exceptional_mul_sigma_normal excH sylP sAP.
have cAp': forall K,
    p^'.-group K -> A \subset 'N(K) -> K \subset H ->
  [~: K, A] \subset K :&: H`_\sigma.
- move=> K p'K nKA sKH; have nHsK := subset_trans sKH nHsH.
  rewrite subsetI commg_subl nKA /= -quotient_sub1 ?comm_subG // quotientR //=.
  have <-: K / H`_\sigma :&: A / H`_\sigma = 1.
    by rewrite setIC coprime_TIg ?coprime_morph ?(pnat_coprime pA p'K).
  rewrite subsetI commg_subl commg_subr /= -{2}(quotient_mulgenr nHsA).
  by rewrite !quotient_norms //= mulgenC (subset_trans sKH) ?normal_norm.
have [sMp | sM'p] := boolP (p \in \sigma(M)).
  split=> // aM'p; have notMGH: gval H \notin M :^: G.
    apply: mmax_norm_notJ maxM maxH pA0 (subset_trans sA0A sAM) sNH _.
    by rewrite sMp eq_sym neqMH.
  rewrite centsC (sameP commG1P trivgP).
  apply: subset_trans (cAp' _ _ _ (subsetIr _ _)) _.
  - apply: sub_in_pnat (pgroupS (subsetIl _ _) (pcore_pgroup _ _)) => q _.
    by apply: contraTneq => ->.
  - by rewrite (normsI _ (normsG sAH)) // (subset_trans sAM) ?bgFunc_norm.
  by rewrite setIAC; case/sigma_disjoint: notMGH => // -> _ _; exact: subsetIl.
suffices cMaA: A \subset 'C(M`_\sigma :&: H).
  by rewrite !{1}(subset_trans cMaA) ?centS ?setSI // Malpha_sub_Msigma.
have [sHp | sH'p] := boolP (p \in \sigma(H)); last first.
  apply/commG1P; apply: contraNeq neqMH => ntA_MsH.
  have [P sylP sAP] := Sylow_superset sAH pA.
  have excH: exceptional_FTmaximal p H A0 A by split=> //; exact/pnElemP.
  have maxAM: M \in 'M(A) by exact/setIdP.
  rewrite (exceptional_sigma_uniq maxH excH sylP sAP maxAM) //.
  apply: contraNneq ntA_MsH => tiMsHs; rewrite -subG1.
  have [sHsA_H nHsA_H] := andP nsHsA_H.
  have <-: H`_\sigma <*> A :&: M`_\sigma = 1.
    apply/trivgP; rewrite -tiMsHs subsetI subsetIr /=.
    rewrite -quotient_sub1 ?subIset ?(subset_trans sHsA_H) //.
    rewrite quotientGI ?mulgen_subl //= mulgenC quotient_mulgenr //.
    rewrite setIC coprime_TIg ?coprime_morph //.
    rewrite (pnat_coprime (pcore_pgroup _ _)) // (card_pnElem Ep2A).
    by rewrite pnat_exp ?orbF ?pnatE.
  rewrite commg_subI // subsetI ?mulgen_subr ?subsetIl. 
    by rewrite (subset_trans sAM) ?bgFunc_norm.
  by rewrite setIC subIset ?nHsA_H.
have sAHs: A \subset H`_\sigma.
  rewrite (subset_normal_Hall _ (Hall_M_Msigma maxH)) ?pcore_normal //.
  by rewrite /psubgroup sAH /pgroup (pi_pnat pA).
have [S sylS sAS] := Sylow_superset sAHs pA; have [sSHs pS _] := and3P sylS.
have nsHaH: H`_\alpha <| H := pcore_normal _ _; have [_ nHaH] := andP nsHaH.
have nHaS := subset_trans (subset_trans sSHs sHsH) nHaH.
have nsHaS_H: H`_\alpha <*> S <| H.
  rewrite -{2}(quotientGK nsHaH) (norm_mulgenEr nHaS) -quotientK //.
  rewrite cosetpre_normal; apply: char_normal_trans (quotient_normal _ nsHsH).
  rewrite /= (nilpotent_Hall_pcore _ (quotient_pHall _ sylS)) ?pcore_char //.
  exact: nilpotentS (quotientS _ (Msigma_sub_M' maxH)) (nil_M'Malpha maxH).
rewrite (sameP commG1P trivgP).
have <-: H`_\alpha <*> S :&: M`_\sigma = 1.
  have: gval M \notin H :^: G.
    by apply: contra sM'p; case/imsetP=> x _ ->; rewrite sigmaJ.
  case/sigma_disjoint=> // _ ti_aHsM _.
  rewrite setIC coprime_TIg ?(pnat_coprime (pcore_pgroup _ _)) //=.
  rewrite norm_mulgenEr // [pnat _ _]pgroupM /pgroup (pi_pnat pS) //.
  rewrite (sub_in_pnat _ (pcore_pgroup _ _)) => // q _ aHq.
  by apply: contraFN (ti_aHsM q); rewrite inE /= aHq.
rewrite commg_subI // subsetI ?subsetIl.
  by rewrite (subset_trans sAS) ?mulgen_subr ?(subset_trans sAM) ?bgFunc_norm.
by rewrite setIC subIset 1?normal_norm.
Qed.

(* This is B & G, Proposition 12.4. *)
Proposition p2Elem_mmax : forall M p A,
      M \in 'M -> A \in 'E_p^2(M) ->
    (*a*) 'C(A) \subset M
 /\ (*b*) ((forallb A0, (A0 \in 'E_p^1(A)) ==> ('M('N(A0)) != [set M])) ->
          [/\ p \in \sigma(M), M`_\alpha = 1 & nilpotent M`_\sigma]).
Proof.
move=> M p A maxM Ep2A; have p_pr := pnElem_prime Ep2A.
have [sAM abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [EpAnonuniq |] := altP forall_inP; last first.
  rewrite negb_forall_in; case/exists_inP=> A0 EpA0; rewrite negbK.
  move/eqP; case/mem_uniq_mmax=> _ sNA0_M; rewrite (subset_trans _ sNA0_M) //.
  by have [sA0A _ _] := pnElemP EpA0; rewrite cents_norm // centS.
have{EpAnonuniq} sCMkApCA: forall y, y \in A^# ->
  [/\ 'r('C_M(<[y]>)) <= 2,
      p \in \sigma(M)^' -> 'C_(M`_\sigma)[y] \subset 'C_M(A)
    & p \in \alpha(M)^' -> 'C_(M`_\alpha)[y] \subset 'C_M(A)].
- move=> y; case/setD1P=> nty Ay; pose Y := <[y]>%G.
  rewrite -cent_cycle -[<[y]>]/(gval Y).
  have EpY: Y \in 'E_p^1(A).
    by rewrite p1ElemE // 2!inE cycle_subG Ay -orderE (abelem_order_p abelA) /=.
  have [sYA abelY dimY] := pnElemP EpY; have [pY _] := andP abelY.
  have [H maxNYH neqHM]: exists2 H, H \in 'M('N(Y)) & H \notin [set M].
    apply/subsetPn; rewrite subset1 negb_or EpAnonuniq //=.
    apply/set0Pn; have [|H] := (@mmax_exists _ 'N(Y)); last by exists H.
    rewrite mFT_norm_proper ?(mFT_pgroup_proper pY) //.
    by rewrite -rank_gt0 (rank_abelem abelY) dimY.
  have{maxNYH} [maxH sNYH] := setIdP maxNYH; rewrite inE -val_eqE /= in neqHM.
  have ->: 'r('C_M(Y)) <= 2.
    apply: contraR neqHM; rewrite -ltnNge => rCMYgt2.
    have uniqCMY: 'C_M(Y)%G \in 'U.
      by rewrite rank3_Uniqueness ?(sub_mmax_proper maxM) ?subsetIl.
    have defU: 'M('C_M(Y)) = [set M] by apply: def_uniq_mmax; rewrite ?subsetIl.
    rewrite (eq_uniq_mmax defU maxH) ?subIset //.
    by rewrite orbC (subset_trans (cent_sub Y)).
  have [cAMs cAMa] := nonuniq_p2Elem_cent_sigma maxM maxH neqHM Ep2A EpY sNYH.
  rewrite !{1}subsetI !{1}(subset_trans (subsetIl _ _) (pcore_sub _ _)).
  by split=> //; [move/cAMs | move/cAMa]; rewrite centsC; apply: subset_trans;
     rewrite setIS ?(subset_trans (cent_sub Y)).
have ntA: A :!=: 1 by rewrite -rank_gt0 (rank_abelem abelA) dimA.
have ncycA: ~~ cyclic A by rewrite (abelem_cyclic abelA) dimA.
have rCMAle2: 'r('C_M(A)) <= 2.
  have [y Ay]: exists y, y \in A^# by apply/set0Pn; rewrite setDeq0 subG1.
  have [rCMy _ _] := sCMkApCA y Ay; apply: leq_trans rCMy.
  by rewrite rankS // setIS // centS // cycle_subG; case/setIdP: Ay.
have sMp: p \in \sigma(M).
  apply: contraFT (ltnn 1) => sM'p; rewrite -dimA -(rank_abelem abelA).
  suffices cMsA: A \subset 'C(M`_\sigma).
    rewrite -(setIidPl cMsA) sub'cent_sigma_rank1 //.
    by rewrite /psubgroup sAM /pgroup (pi_pnat pA).
  have nMsA: A \subset 'N(M`_\sigma) by rewrite (subset_trans sAM) ?bgFunc_norm.
  rewrite centsC /= -[M`_\sigma]/(gval _).
  rewrite (coprime_abelian_gen_cent1 _ _ nMsA) //; last first.
    exact: (pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _)).
  rewrite bigprodGE gen_subG; apply/bigcupsP=> y; case/sCMkApCA=> _ sCMsyCA _.
  by rewrite (subset_trans (sCMsyCA sM'p)) ?subsetIr.
have [P sylP sAP] := Sylow_superset sAM pA; have [sPM pP _] := and3P sylP.
pose Z := 'Ohm_1('Z(P)).
have sZA: Z \subset A.
  have maxA: A \in 'E*_p('C_M(A)).
    have sACMA: A \subset 'C_M(A) by rewrite subsetI sAM.
    rewrite (subsetP (p_rankElem_max _ _)) // !inE abelA sACMA.
    rewrite eqn_leq logn_le_p_rank /=; last by rewrite !inE sACMA abelA.
    by rewrite dimA (leq_trans (p_rank_le_rank _ _)).
  rewrite [Z](OhmE 1 (pgroupS (center_sub P) pP)) gen_subG.
  rewrite -(pmaxElem_LdivP p_pr maxA) -(setIA M) setIid setSI //=.
  by rewrite setISS // centS.
have{ntA} ntZ: Z != 1.
  apply: contraNneq ntA; rewrite -subG1 /= -[Z](setIidPr (Ohm_sub 1 _)).
  by move/TI_Ohm1; rewrite setIid; move/(trivg_center_pgroup pP)=> <-.
have rPle2: 'r(P) <= 2.
  have [z Zz ntz]: exists2 z, z \in Z & z \notin [1].
    by apply/subsetPn; rewrite subG1.
  have [|rCMz _ _] := sCMkApCA z; first by rewrite inE ntz (subsetP sZA).
  rewrite (leq_trans _ rCMz) ?rankS // subsetI sPM centsC cycle_subG.
  by rewrite (subsetP _ z Zz) // (subset_trans (Ohm_sub 1 _)) ?subsetIr.
have aM'p: p \in \alpha(M)^'.
   by rewrite !inE -leqNgt (p_rank_Sylow sylP) -rank_pgroup.
have sMaCMA: M`_\alpha \subset 'C_M(A).
  have nMaA: A \subset 'N(M`_\alpha) by rewrite (subset_trans sAM) ?bgFunc_norm.
  rewrite -[M`_\alpha]/(gval _).
  rewrite (coprime_abelian_gen_cent1 _ _ nMaA) //; last first.
    exact: (pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _)).
  rewrite bigprodGE gen_subG; apply/bigcupsP=> y; case/sCMkApCA=> _ _ sCMayCA.
  by rewrite (subset_trans (sCMayCA aM'p)) ?subsetIr.
have Ma1: M`_\alpha = 1.
  have [q q_pr rMa]:= rank_witness M`_\alpha.
  apply: contraTeq rCMAle2; rewrite -ltnNge -rank_gt0 rMa p_rank_gt0 => piMa_q.
  have aMq: q \in \alpha(M) := pnatPpi (pcore_pgroup _ _) piMa_q.
  apply: leq_trans (rankS sMaCMA); rewrite rMa.
  have [Q sylQ] := Sylow_exists q M`_\alpha; rewrite (p_rank_Sylow sylQ).
  by rewrite -(p_rank_Sylow (pSylow_Hall_Sylow (Hall_M_Malpha maxM) aMq sylQ)).
have nilMs: nilpotent M`_\sigma.
  rewrite (nilpotentS (Msigma_sub_M' maxM)) // (isog_nil (quotient1_isog _)).
  by rewrite -Ma1 nil_M'Malpha.
rewrite (subset_trans (cents_norm (centS sZA))) ?(mmax_normal maxM) //.
apply: char_normal_trans (char_trans (Ohm_char 1 _) (center_char P)) _.
have{sylP} sylP: p.-Sylow(M`_\sigma) P.
  apply: pHall_subl _ (pcore_sub _ _) sylP.
  rewrite (subset_normal_Hall _ (Hall_M_Msigma maxM)) ?pcore_normal //.
  by rewrite /psubgroup /pgroup sPM (pi_pnat pP).
by rewrite (nilpotent_Hall_pcore _ sylP) ?(char_normal_trans (pcore_char _ _)).
Qed.

(* This is B & G, Theorem 12.5(a) -- this part does not mention a specific   *)
(* rank 2 elementary abelian \tau_2(M) subgroup of M.                        *)

Theorem tau2_nil : forall M p,
  M \in 'M -> p \in \tau2(M) -> nilpotent M`_\sigma.
Proof.
move=> M p maxM t2Mp; have [sM'p] := andP t2Mp; move/eqP=> rpM.
have [A Ep2A] := p_rank_witness p M; rewrite rpM in Ep2A.
have [_]:= p2Elem_mmax maxM Ep2A; rewrite -negb_exists_in [p \in _](negPf sM'p).
have [[A0 EpA0] | _ [] //] := exists_inP.
move/eqP; case/mem_uniq_mmax=> _ sNA0M _.
have{EpA0 sNA0M} excM: exceptional_FTmaximal p M A0 A by [].
have [sAM abelA _] := pnElemP Ep2A; have [pA _] := andP abelA.
have [P sylP sAP] := Sylow_superset sAM pA.
exact: exceptional_sigma_nil maxM excM sylP sAP.
Qed.

(* This is B & G, Theorem 12.5 (b-f) -- the bulk of the Theorem. *)
Theorem tau2_context : forall M p A,
    M \in 'M -> p \in \tau2(M) -> A \in 'E_p^2(M) ->
  let Ms := M`_\sigma in
  [/\ (*b*) forall P, p.-Sylow(M) P ->
                abelian P
             /\ (A \subset P -> 'Ohm_1(P) = A /\ ~~ ('N(P) \subset M)),
      (*c*)  Ms <*> A <| M,
      (*d*) 'C_Ms(A) = 1,
      (*e*) forall Mstar, Mstar \in 'M(A) :\ M -> Ms :&: Mstar = 1
    & (*f*) exists2 A1, A1 \in 'E_p^1(A) & 'C_Ms(A1) = 1].
Proof.
move=> M p A maxM t2Mp Ep2A Ms; have [sM'p _] := andP t2Mp.
have [_]:= p2Elem_mmax maxM Ep2A; rewrite -negb_exists_in [p \in _](negPf sM'p).
have [[A0 EpA0] | _ [] //] := exists_inP.
move/eqP; case/mem_uniq_mmax=> _ sNA0M _.
have{EpA0 sNA0M} excM: exceptional_FTmaximal p M A0 A by [].
have strM := exceptional_structure maxM excM.
have [sAM abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [P sylP sAP] := Sylow_superset sAM pA.
have nsMsA_M : Ms <*> A <| M := exceptional_mul_sigma_normal maxM excM sylP sAP.
have [_ regA [A1 EpA1 [_ _ [_ regA1 _]]]] := strM P sylP sAP.
split=> // [P1 sylP1 | {P sylP sAP A0 excM}H| ]; last by exists A1.
  split=> [|sAP1]; first exact: (exceptional_Sylow_abelian _ excM sylP).
  split; first by case/strM: sylP1.
  by apply: contra sM'p => sNP1M; apply/exists_inP; exists P1.
case/setD1P; rewrite -val_eqE /= => neqHM; case/setIdP=> maxH sAH.
apply/trivgP; rewrite -regA subsetI subsetIl /=.
have Ep2A_H: A \in 'E_p^2(H) by exact/pnElemP.
have [_]:= p2Elem_mmax maxH Ep2A_H; rewrite -negb_exists_in.
have [[A0 EpA0] | _ [//|sHp _ nilHs]] := exists_inP.
  move/eqP; case/mem_uniq_mmax=> _ sNA0H _.
  have [cMSH_A _]:= nonuniq_p2Elem_cent_sigma maxM maxH neqHM Ep2A EpA0 sNA0H.
  by rewrite centsC cMSH_A.
have [P sylP sAP] := Sylow_superset sAH pA; have [sPH pP _] := and3P sylP.
have sylP_Hs: p.-Sylow(H`_\sigma) P.
  rewrite (pHall_subl _ (pcore_sub _ _) sylP) //.
  rewrite (subset_normal_Hall _ (Hall_M_Msigma maxH)) ?pcore_normal //.
  by rewrite /psubgroup /pgroup sPH (pi_pnat pP).
have nPH: H \subset 'N(P).
  rewrite (nilpotent_Hall_pcore nilHs sylP_Hs).
  by rewrite !(char_norm_trans (pcore_char _ _)) ?normG.
have coMsP: coprime #|M`_\sigma| #|P|.
  exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat pP _).
rewrite (sameP commG1P trivgP) -(coprime_TIg coMsP) commg_subI ?setIS //.
by rewrite subsetI sAP (subset_trans sAM) ?bgFunc_norm.
Qed.

(* This is B & G, Corollary 12.6 (a, b, c & f) -- i.e., the assertions that   *)
(* do not depend on the decomposition of the complement.                      *)
Corollary tau2_compl_context : forall M E p A,
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
  let Ms := M`_\sigma in
  [/\ (*a*) A <| E /\ 'E_p^1(E) = 'E_p^1(A),
      (*b*) [/\ 'C(A) \subset E, 'N_M(A) = E & ~~ ('N(A) \subset M)],
      (*c*) forall X, X \in 'E_p^1(E) -> 'C_Ms(X) != 1 -> 'M('C(X)) = [set M]
    & (*f*) forall Mstar,
              Mstar \in 'M -> gval Mstar \notin M :^: G ->
            Ms :&: Mstar`_\sigma = 1
         /\ [predI \sigma(M) & \sigma(Mstar)] =i pred0].
Proof.
move=> M E p A maxM hallE t2Mp Ep2A Ms; have [sEM sM'E _] := and3P hallE.
have [p_pr [sM'p _]] := (pnElem_prime Ep2A, andP t2Mp).
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [_ mulMsE nMsE tiMsE] := sdprodP (sdprod_mmax maxM hallE).
have Ep2A_M: A \in 'E_p^2(M) by rewrite (subsetP (pnElemS _ _ sEM)).
have [syl_p_M nsMsAM regA tiMsMA _] := tau2_context maxM t2Mp Ep2A_M.
have nMsA: A \subset 'N(Ms) := subset_trans sAE nMsE.
have nsAE: A <| E.
  rewrite /normal sAE -(mul1g A) -tiMsE setIC group_modr // normsI ?normG //.
  by rewrite (subset_trans sEM) // -(norm_mulgenEr nMsA) normal_norm.
have sAsylE: forall P, p.-Sylow(E) P -> 'Ohm_1(P) = A /\ ~~ ('N(P) \subset M).
  move=> P sylP; have sylP_M: p.-Sylow(M) P by exact: (pSylow_Hall_Sylow hallE).
  have [_] := syl_p_M P sylP_M; apply.
  exact: subset_trans (pcore_max pA nsAE) (pcore_sub_Hall sylP).
have not_sNA_M: ~~ ('N(A) \subset M).
  have [P sylP] := Sylow_exists p E; have [<-]:= sAsylE P sylP.
  exact: contra (subset_trans (char_norms (Ohm_char 1 P))).
have{sAsylE syl_p_M} defEpE: 'E_p^1(E) = 'E_p^1(A).
  apply/eqP; rewrite eqEsubset andbC pnElemS //; apply/subsetP=> X.
  case/pnElemP=> sXE abelX dimX; apply/pnElemP; split=> //.
  have [pX _ eX] := and3P abelX; have [P sylP sXP] := Sylow_superset sXE pX.
  have [<- _]:= sAsylE P sylP; have [_ pP _] := and3P sylP.
  by rewrite (OhmE 1 pP) sub_gen // subsetI sXP sub_LdivT.
have defNMA: 'N_M(A) = E.
  rewrite -mulMsE setIC -group_modr ?normal_norm //= setIC.
  rewrite coprime_norm_cent ?regA ?mul1g //.
  exact: (pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _)).
have [sCAM _]: 'C(A) \subset M /\ _  := p2Elem_mmax maxM Ep2A_M.
have sCAE: 'C(A) \subset E by rewrite -defNMA subsetI sCAM cent_sub.
split=> // [X EpX | H maxH not_MGH]; last first.
  by case/sigma_disjoint: not_MGH => // _ _; apply; exact: tau2_nil t2Mp.
rewrite defEpE in EpX; have [sXA abelX dimX] := pnElemP EpX.
have ntX: X :!=: 1 by rewrite -rank_gt0 (rank_abelem abelX) dimX.
apply: contraNeq => neq_maxCX_M.
have{neq_maxCX_M} [H]: exists2 H, H \in 'M('C(X)) & H \notin [set M].
  apply/subsetPn; rewrite subset1 negb_or neq_maxCX_M.
  have [H maxH]:= mmax_exists (mFT_cent_proper ntX).
  by apply/set0Pn; exists H.
case/setIdP=> maxH sCXH neqHM.
rewrite -subG1 -(tiMsMA H) ?setIS // inE neqHM inE maxH.
exact: subset_trans (sub_abelian_cent cAA sXA) sCXH.
Qed.

(* This is B & G, Corollary 12.6 (d, e) -- the parts that apply to a          *)
(* particular decomposition of the complement. We included an easy consequece *)
(* of part (a), that A is a subgroup of E2, as this is used implicitly later  *)
(* in sections 12 and 13.                                                     *)
Corollary tau2_regular : forall M E E1 E2 E3 p A,
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
    p \in \tau2(M) -> A \in 'E_p^2(E) ->
  let Ms := M`_\sigma in
  [/\ (*d*) forall x, x \in E3^# -> 'C_Ms[x] = 1,
      (*e*) forall x, x \in ('C_E1(A))^# -> 'C_Ms[x] = 1
          & A \subset E2].
Proof.
move=> M E E1 E2 E3 p A maxM complEi t2Mp Ep2A Ms.
have p_pr := pnElem_prime Ep2A.
have [hallE hallE1 hallE2 hallE3 _] := complEi.
have [sEM sM'E _] := and3P hallE; have [sM'p _] := andP t2Mp.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have Ep2A_M: A \in 'E_p^2(M) by rewrite (subsetP (pnElemS _ _ sEM)).
have [_ _ _ tiMsMA _] := tau2_context maxM t2Mp Ep2A_M.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp Ep2A.
have [sCAM _]: 'C(A) \subset M /\ _  := p2Elem_mmax maxM Ep2A_M.
have sAE2: A \subset E2.
  exact: normal_sub_max_pgroup (Hall_max hallE2) (pi_pnat pA _) nsAE.
split=> // x; last first.
  case/setD1P=> ntx; case/setIP; rewrite -cent_cycle -!cycle_subG => sXE1 cAX.
  pose q := pdiv #[x]; have piXq: q \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
  have [Q sylQ] := Sylow_exists q <[x]>; have [sQX qQ _] := and3P sylQ.
  have [sE1E t1E1 _] := and3P hallE1; have sQE1 := subset_trans sQX sXE1.
  have sQM := subset_trans sQE1 (subset_trans sE1E sEM).
  have [H]: {H | H \in 'M('N(Q))}.
    apply: mmax_exists; rewrite mFT_norm_proper ?(mFT_pgroup_proper qQ) //.
    by rewrite -rank_gt0 (rank_pgroup qQ) -(p_rank_Sylow sylQ) p_rank_gt0.
  case/setIdP=> maxH sNQH; apply/trivgP; rewrite -(tiMsMA H) ?setIS //.
    by rewrite (subset_trans _ sNQH) ?cents_norm ?centS.
  rewrite 3!inE maxH /=; apply/andP; split.
    apply: contraNneq (mmax_norm_notJ maxM maxH qQ sQM sNQH _) => [-> | ].
      exact: orbit_refl.
    by rewrite (pnatPpi (pgroupS sXE1 t1E1)) ?orbT.
  by rewrite (subset_trans _ sNQH) ?cents_norm // centsC (subset_trans sQX).
case/setD1P=> ntx; rewrite -cent_cycle -cycle_subG => sXE3.
pose q := pdiv #[x]; have piXq: q \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
have [Q sylQ] := Sylow_exists q <[x]>; have [sQX qQ _] := and3P sylQ.
have [sE3E t3E3 _] := and3P hallE3; have sQE3 := subset_trans sQX sXE3.
have sQM := subset_trans sQE3 (subset_trans sE3E sEM).
have [H]: {H | H \in 'M('N(Q))}.
  apply: mmax_exists; rewrite mFT_norm_proper ?(mFT_pgroup_proper qQ) //.
  by rewrite -rank_gt0 (rank_pgroup qQ) -(p_rank_Sylow sylQ) p_rank_gt0.
case/setIdP=> maxH sNQH; apply/trivgP; rewrite -(tiMsMA H) ?setIS //.
  by rewrite (subset_trans _ sNQH) ?cents_norm ?centS.
rewrite 3!inE maxH /=; apply/andP; split.
  apply: contraNneq (mmax_norm_notJ maxM maxH qQ sQM sNQH _) => [-> | ].
    exact: orbit_refl.
  by rewrite (pnatPpi (pgroupS sXE3 t3E3)) ?orbT.
rewrite (subset_trans _ sNQH) ?cents_norm // (subset_trans _ (centS sQE3)) //.
have coE3A: coprime #|E3| #|A|.
  by rewrite (pnat_coprime t3E3 (pi_pnat pA _)) ?tau3'2.
rewrite (sameP commG1P trivgP) -(coprime_TIg coE3A) subsetI commg_subl.
have [[_ nsE3E] _ _ _ _] := sigma_complement_context maxM complEi.
by rewrite commg_subr (subset_trans sE3E) ?(subset_trans sAE) ?normal_norm.
Qed.

(* This is B & G, Theorem 12.7. *)
Theorem nonabelian_tau2 : forall M E p A P0,
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-group P0 -> ~~ abelian P0 ->
 let Ms := M`_\sigma in let A0 := 'C_A(Ms)%G in
 [/\ (*a*) \tau2(M) =i (p : nat_pred),
     (*b*) #|A0| = p /\ Ms \x A0 = 'F(M),
     (*c*) forall X,
             X \in 'E_p^1(E) :\ A0 -> 'C_Ms(X) = 1 /\ ~~ ('C(X) \subset M)
   & (*d*) exists2 E0 : {group gT}, A0 ><| E0 = E
   & (*e*) forall x, x \in Ms^# -> {subset \pi(#|'C_E0[x]|) <= \tau1(M)}].
Proof.
move=> M E p A P0 maxM hallE t2Mp Ep2A pP0 not_cP0P0 Ms /=.
have p_pr := pnElem_prime Ep2A.
have [sEM sM'E _] := and3P hallE; have [sM'p _] := andP t2Mp.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have Ep2A_M: A \in 'E_p^2(M) by rewrite (subsetP (pnElemS _ _ sEM)).
have [[E1 hallE1] [E3 hallE3]] := tau13_complements_exist maxM hallE.
have [E2 hallE2 complEi] := sigma_complement_exists maxM hallE hallE1 hallE3.
have [regE3 _ sAE2] := tau2_regular maxM complEi t2Mp Ep2A.
have [P sylP sAP] := Sylow_superset sAE2 pA; have [sPE2 pP _] := and3P sylP.
have [S /= sylS sPS] := Sylow_superset (subsetT P) pP.
have pS := pHall_pgroup sylS; have sAS := subset_trans sAP sPS.
have sylP_E: p.-Sylow(E) P := pSylow_Hall_Sylow hallE2 t2Mp sylP.
have sylP_M: p.-Sylow(M) P := pSylow_Hall_Sylow hallE sM'p sylP_E.
have [syl_p_M _ regA _ _] := tau2_context maxM t2Mp Ep2A_M.
have{syl_p_M} cPP: abelian P by case: (syl_p_M P).
have{P0 pP0 not_cP0P0} not_cSS: ~~ abelian S.
  have [x _ sP0Sx] := Sylow_subJ sylS (subsetT P0) pP0.
  by apply: contra not_cP0P0 => cSS; rewrite (abelianS sP0Sx) ?abelianJ.
have [defP | ltPS] := eqVproper sPS; first by rewrite -defP cPP in not_cSS.
have [[nsAE defEp] [sCAE _ _] nregA _] :=
  tau2_compl_context maxM hallE t2Mp Ep2A.
have defCSA: 'C_S(A) = P.
  apply: (sub_pHall sylP_E (pgroupS (subsetIl _ _) pS)).
    by rewrite subsetI sPS (sub_abelian_cent2 cPP).
  by rewrite subIset // sCAE orbT.
have max2A: A \in 'E_p^2(G) :&: 'E*_p(G).
  by rewrite 3!inE subsetT abelA dimA; case: (tau2_not_beta maxM t2Mp) => _ ->.
have def_t2: \tau2(M) =i (p : nat_pred).
  move=> q; apply/idP/idP=> [t2Mq |]; last by move/eqnP->.
  apply: contraLR (proper_card ltPS); rewrite !inE /= eq_sym -leqNgt => q'p.
  apply: wlog_neg => p'q; have [B EqB] := p_rank_witness q E.
  have{EqB} Eq2B: B \in 'E_q^2(E).
    by move: t2Mq; rewrite (tau2E hallE); case/andP=> _; move/eqP <-.
  have [sBE abelB dimB]:= pnElemP Eq2B; have [qB _] := andP abelB.
  have coBA: coprime #|B| #|A| by exact: pnat_coprime qB (pi_pnat pA _).
  have [[nsBE _] [sCBE _ _] _ _] := tau2_compl_context maxM hallE t2Mq Eq2B.
  have nBA: A \subset 'N(B) by rewrite (subset_trans sAE) ?normal_norm.
  have cAB: B \subset 'C(A).
    rewrite (sameP commG1P trivgP) -(coprime_TIg coBA) subsetI commg_subl nBA.
    by rewrite commg_subr (subset_trans sBE) ?normal_norm.
  have{cAB} qCA: q %| #|'C(A)|.
    by apply: dvdn_trans (cardSg cAB); rewrite (card_pnElem Eq2B) dvdn_mull.
  have [Q maxQ sBQ] := max_normed_exists qB nBA.
  have nnQ: q.-narrow Q.
    apply/orP; right; apply/set0Pn; exists B.
    rewrite 3!inE sBQ abelB dimB (subsetP (pmaxElemS q (subsetT Q))) //=.
    rewrite setIC 2!inE sBQ; case: (tau2_not_beta maxM t2Mq) => _ -> //.
    by rewrite (subsetP (pnElemS _ _ sEM)).
  have [P1 [sylP1 _] [_ _]] := max_normed_2Elem_signaliser q'p max2A maxQ qCA.
  move/(_ nnQ)=> cQP1; have sylP1_E: p.-Sylow(E) P1.
    apply: pHall_subl (subset_trans _ sCBE) (subsetT E) sylP1.
    exact: subset_trans (centS sBQ).
  rewrite (card_Hall sylS) -(card_Hall sylP1).
  by rewrite (card_Hall sylP_E) -(card_Hall sylP1_E).
have coMsA: coprime #|Ms| #|A|.
  by exact: pnat_coprime (pcore_pgroup _ _) (pi_pnat pA _).
have defMs: <<\bigcup_(X \in 'E_p^1(A)) 'C_Ms(X)>> = Ms.
  have ncycA: ~~ cyclic A by rewrite (abelem_cyclic abelA) dimA.
  have [sAM _ _] := pnElemP Ep2A_M.
  have{sAM} nMsA: A \subset 'N(Ms) by rewrite (subset_trans sAM) ?bgFunc_norm.
  apply/eqP; rewrite eqEsubset andbC gen_subG.
  rewrite {1}[Ms](congr_group (coprime_abelian_gen_cent1 cAA ncycA nMsA coMsA)).
  rewrite bigprodGE genS; apply/bigcupsP=> x; rewrite ?subsetIl //.
  case/setD1P=> ntx Ax; rewrite /= -cent_cycle (bigcup_max <[x]>%G) //.
  by rewrite p1ElemE // 2!inE cycle_subG Ax /= -orderE (abelem_order_p abelA).
have [A0 EpA0 nregA0]: exists2 A0, A0 \in 'E_p^1(A) & 'C_Ms(A0) != 1.
  apply/exists_inP; rewrite -negb_forall_in.
  apply: contra (Msigma_neq1 maxM); move/forall_inP => regAp.
  rewrite -/Ms -defMs -subG1 gen_subG; apply/bigcupsP=> X EpX.
  by rewrite subG1 regAp.
have uniqCA0: 'M('C(A0)) = [set M].
  by rewrite nregA // (subsetP (pnElemS _ _ sAE)).
have defSM: S :&: M = P.
  apply: sub_pHall (pgroupS (subsetIl S M) pS) _ (subsetIr S M) => //.
  by rewrite subsetI sPS (pHall_sub sylP_M).
have{ltPS} not_sSM: ~~ (S \subset M).
  by rewrite (sameP setIidPl eqP) defSM proper_neq.
have not_sA0Z: ~~ (A0 \subset 'Z(S)).
  apply: contra not_sSM; rewrite subsetI centsC; case/andP=> _ sS_CA0.
  by case/mem_uniq_mmax: uniqCA0 => _; exact: subset_trans sS_CA0.
have [EpZ0 dxCSA transNSA] := basic_p2maxElem_structure max2A pS sAS not_cSS.
do [set Z0 := 'Ohm_1('Z(S))%G; set EpA' := _ :\ Z0] in EpZ0 dxCSA transNSA.
have sZ0Z: Z0 \subset 'Z(S) := Ohm_sub 1 _.
have [sA0A _ _] := pnElemP EpA0; have sA0P := subset_trans sA0A sAP.
have EpA'_A0: A0 \in EpA'.
  by rewrite 2!inE EpA0 andbT; apply: contraNneq not_sA0Z => ->.
have{transNSA sAP not_sSM defSM} regA0': forall X,
  X \in 'E_p^1(E) :\ A0 -> 'C_Ms(X) = 1 /\ ~~ ('C(X) \subset M).
- move=> X; case/setD1P=> neqXA0 EpX.
  suffices not_sCXM: ~~ ('C(X) \subset M).
    split=> //; apply: contraNeq not_sCXM => nregX.
    by case/mem_uniq_mmax: (nregA X EpX nregX).
  have [sXZ | not_sXZ] := boolP (X \subset 'Z(S)).
    apply: contra (subset_trans _) not_sSM.
    by rewrite centsC (subset_trans sXZ) ?subsetIr.
  have EpA'_X: X \in EpA'.
    by rewrite 2!inE -defEp EpX andbT; apply: contraNneq not_sXZ => ->.
  have [g NSAg /= defX] := atransP2 transNSA EpA'_A0 EpA'_X.
  have{NSAg} [Sg nAg] := setIP NSAg.
  have neqMgM: M :^ g != M.
    rewrite (sameP eqP normP) (norm_mmax maxM); apply: contra neqXA0 => Mg.
    rewrite defX [_ == _](sameP eqP normP) (subsetP (cent_sub A0)) //.
    by rewrite (subsetP (centSS (subxx _) sA0P cPP)) // -defSM inE Sg.
  apply: contra neqMgM; rewrite defX centJ sub_conjg.
  by move/(eq_uniq_mmax uniqCA0) => defM; rewrite -{1}defM ?mmaxJ ?actKV.
have{defMs} defA0: 'C_A(Ms) = A0.
  apply/eqP; rewrite eq_sym eqEcard subsetI sA0A (card_pnElem EpA0).
  have pCA: p.-group 'C_A(Ms) := pgroupS (subsetIl A _) pA.
  rewrite andbC (card_pgroup pCA) leq_exp2l ?prime_gt1 // -ltnS -dimA.
  rewrite properG_ltn_log //=; last first.
    rewrite properE subsetIl /= subsetI subxx centsC -(subxx Ms) -subsetI.
    by rewrite regA subG1 Msigma_neq1.
  rewrite centsC -defMs gen_subG (big_setD1 A0) //= subUset subsetIr /=.
  by apply/bigcupsP=> X; rewrite -defEp; case/regA0'=> -> _; rewrite sub1G.
rewrite defA0 (group_inj defA0) (card_pnElem EpA0).
have{dxCSA} [Y [cycY sZ0Y]] := dxCSA; move/(_ _ EpA'_A0)=> dxCSA.
have defCP_Ms: 'C_P(Ms) = A0.
  move: dxCSA; rewrite defCSA; case/dprodP=> _ mulA0Y cA0Y tiA0Y.
  rewrite -mulA0Y -group_modl /=; last by rewrite -defA0 subsetIr.
  rewrite setIC TI_Ohm1 ?mulg1 // setIC.
  have pY: p.-group Y by rewrite (pgroupS _ pP) // -mulA0Y mulG_subr.
  have cYY: abelian Y := cyclic_abelian cycY.
  have ->: 'Ohm_1(Y) = Z0.
    apply/eqP; rewrite eq_sym eqEcard (card_pnElem EpZ0) /= -['Ohm_1(_)]Ohm_id.
    rewrite OhmS // (card_pgroup (pgroupS (Ohm_sub 1 Y) pY)).
    rewrite leq_exp2l ?prime_gt1 -?p_rank_abelian // -rank_pgroup //.
    by rewrite -abelian_rank1_cyclic.
  rewrite prime_TIg ?(card_pnElem EpZ0) // centsC (sameP setIidPl eqP) eq_sym.
  case: (regA0' Z0) => [|-> _]; last exact: Msigma_neq1.
  by rewrite 2!inE defEp EpZ0 andbT; apply: contraNneq not_sA0Z => <-.
have [sPM pA0] := (pHall_sub sylP_M, pgroupS sA0A pA).
have cMsA0: A0 \subset 'C(Ms) by rewrite -defA0 subsetIr.
have nsA0M: A0 <| M.
  rewrite /normal (subset_trans sA0P) //.
  have [_ defM nMsE _] := sdprodP (sdprod_mmax maxM hallE).
  rewrite -defM mulG_subG cents_norm 1?centsC // -defA0 normsI ?norms_cent //.
  exact: normal_norm nsAE.
have defFM: Ms \x A0 = 'F(M).
  have nilF := Fitting_nil M.
  rewrite dprodE ?(coprime_TIg (coprimegS sA0A coMsA)) //.
  have [_ /= defFM cFpp' _] := dprodP (nilpotent_pcoreC p nilF).
  have defFp': 'O_p^'('F(M)) = Ms.
    apply/eqP; rewrite eqEsubset.
    rewrite (subset_normal_Hall _ (Hall_M_Msigma maxM)) ?pcore_normal //.
    rewrite /psubgroup (subset_trans (pcore_sub _ _) (Fitting_sub _)).
    rewrite /pgroup (sub_in_pnat _ (pcore_pgroup _ _)) => [|q piFq]; last first.
      have [Q sylQ] := Sylow_exists q 'F(M); have [sQF qQ _] := and3P sylQ.
      have ntQ: Q :!=: 1.
        rewrite -rank_gt0 (rank_pgroup qQ) -(p_rank_Sylow sylQ) p_rank_gt0.
        by rewrite (piSg _ piFq) ?pcore_sub.
      have sNQM: 'N(Q) \subset M.
        rewrite (mmax_normal maxM) // (nilpotent_Hall_pcore nilF sylQ).
        by rewrite p_core_Fitting pcore_normal.
      apply/implyP; rewrite implyNb /= -def_t2 orbC. 
      by rewrite (prime_class_mmax_norm maxM qQ).
    rewrite pcore_max ?[pgroup _ _](sub_in_pnat _ (pcore_pgroup _ _)) //.
      by move=> q _; apply: contraTneq => ->.
    rewrite /normal (subset_trans (Fitting_sub M)) ?bgFunc_norm //.
    rewrite Fitting_max ?pcore_normal ?(tau2_nil _ t2Mp) //.
  rewrite p_core_Fitting defFp' centsC in defFM cFpp'.
  rewrite -defFM (centC cFpp'); congr (Ms * _).
  apply/eqP; rewrite eqEsubset pcore_max //.
  by rewrite -defCP_Ms subsetI cFpp' pcore_sub_Hall.
split=> {defFM}//.
have [[sE1E t1E1 _] t2E2] := (and3P hallE1, pHall_pgroup hallE2).
have defE2: E2 :=: P by rewrite (sub_pHall sylP) // -(eq_pgroup _ def_t2) t2E2.
have [[_ nsE3E] _ _ [defEr _] _] := sigma_complement_context maxM complEi.
have [sE3E nE3E] := andP nsE3E; have{nE3E} nE3E := subset_trans _ nE3E.
have [[_ E21 _ defE21]] := sdprodP defEr; rewrite defE21 => defE nE321 tiE321.
rewrite defE2 in defE21; have{defE21} [_ defPE1 nPE1 tiPE1] := sdprodP defE21.
have [P0 defP nP0E1]: exists2 P0 : {group gT}, A0 \x P0 = P & E1 \subset 'N(P0).
  have p'E1b: p^'.-group (E1 / 'Phi(P)).
    rewrite quotient_pgroup //; apply: sub_in_pnat t1E1 => q _.
    by move/tau2'1; rewrite inE /= def_t2.
  have defPhiP: 'Phi(P) = 'Phi(Y).
    have [_ _ cA0Y tiA0Y] := dprodP dxCSA.
    rewrite defCSA dprodEcprod // in dxCSA.
    have [_ abelA0 _] := pnElemP EpA0; rewrite -trivg_Phi // in abelA0.
    by rewrite -(Phi_cprod pP dxCSA) (eqP abelA0) cprod1g.
  have abelPb := Phi_quotient_abelem pP; have sA0Pb := quotientS 'Phi(P) sA0P.
  have [||P0b] := Maschke_abelem abelPb p'E1b sA0Pb; rewrite ?quotient_norms //.
    by rewrite (subset_trans (subset_trans sE1E sEM)) ?normal_norm.
  case/dprodP=> _ defPb _ tiAP0b nP0E1b.
  have sP0Pb: P0b \subset P / 'Phi(P) by rewrite -defPb mulG_subr.
  have [P0 defP0b sPhiP0 sP0P] := inv_quotientS (Phi_normal P) sP0Pb.
  exists P0; last first.
    rewrite -(quotientSGK (char_norm_trans (Phi_char P) nPE1)); last first.
      by rewrite cents_norm ?(sub_abelian_cent2 cPP (Phi_sub P) sP0P).
    by rewrite quotient_normG -?defP0b ?(normalS _ _ (Phi_normal P)).
  rewrite dprodEgen ?(sub_abelian_cent2 cPP) //.
    apply/eqP; rewrite eqEsubset mulgen_subG sA0P sP0P /=.
    rewrite -(quotientSGK (normal_norm (Phi_normal P))) //=; last first.
      by rewrite sub_gen // subsetU // sPhiP0 orbT.
    rewrite cent_mulgenEr ?(sub_abelian_cent2 cPP) //.
    rewrite quotientMr //; last by rewrite (subset_trans sP0P) ?bgFunc_norm.
    by rewrite -defP0b defPb.
  apply/trivgP; case/dprodP: dxCSA => _ _ _ <-.
  rewrite subsetI subsetIl (subset_trans _ (Phi_sub Y)) // -defPhiP.
  rewrite -quotient_sub1 ?subIset ?(subset_trans sA0P) ?bgFunc_norm //.
  by rewrite quotientIG // -defP0b tiAP0b.
have nA0E := subset_trans _ (subset_trans sEM (normal_norm nsA0M)).
have{defP} [_ defAP0 _ tiAP0] := dprodP defP.
have sP0P: P0 \subset P by rewrite -defAP0 mulG_subr.
have sP0E := subset_trans sP0P (pHall_sub sylP_E).
pose E0 := (E3 <*> (P0 <*> E1))%G.
have sP0E1_E: P0 <*> E1 \subset E by rewrite mulgen_subG sP0E.
have sE0E:  E0 \subset E by rewrite mulgen_subG sE3E.
have mulA0E0: A0 * E0 = E.
  rewrite /= (norm_mulgenEr (nE3E _ sP0E1_E)) mulgA -(normC (nA0E _ sE3E)).
  by rewrite /= -mulgA (norm_mulgenEr nP0E1) (mulgA A0) defAP0 defPE1.
have tiA0E0: A0 :&: E0 = 1.
  rewrite cardMg_TI // mulA0E0 -defE /= (norm_mulgenEr (nE3E _ sP0E1_E)).
  rewrite !TI_cardMg //; last first.
    by apply/trivgP; rewrite -tiE321 setIS //= ?norm_mulgenEr // -defPE1 mulSg.
  rewrite mulnCA /= leq_mul // norm_mulgenEr //= -defPE1.
  rewrite !TI_cardMg //; last by apply/trivgP; rewrite -tiPE1 setSI.
  by rewrite mulnA -(TI_cardMg tiAP0) defAP0.
have defAE0: A0 ><| E0 = E by rewrite sdprodE ?nA0E.
exists E0 => // x; case/setD1P=> ntx Ms_x q piCE0x_q.
have: q \in \pi(#|E|) by apply: piSg piCE0x_q; rewrite subIset ?sE0E.
rewrite mem_primes in piCE0x_q; case/and3P: piCE0x_q => q_pr _.
case/Cauchy=> // z; case/setIP=> E0z cxz oz.
have ntz: z != 1 by rewrite -order_gt1 oz prime_gt1.
have ntCMs_z: 'C_Ms[z] != 1.
  apply: contraNneq ntx => reg_z; rewrite (sameP eqP set1gP) -reg_z inE Ms_x.
  by rewrite cent1C.
rewrite (partition_pi_mmax_compl maxM hallE) inE /= inE /= -orbA def_t2.
case/or3P => [-> // | pq | t3Mq].
  have EpA0'_z: <[z]>%G \in 'E_p^1(E) :\ A0.
    rewrite p1ElemE // !inE -orderE oz (eqnP pq) eqxx cycle_subG.
    rewrite (subsetP sE0E) // !andbT; apply: contraNneq ntz => eqA0z.
    by rewrite (sameP eqP set1gP) -tiA0E0 inE -eqA0z cycle_id E0z.
  have [reg_z _] := regA0' _ EpA0'_z.
  by rewrite -cent_cycle reg_z eqxx in ntCMs_z.
rewrite regE3 ?eqxx // !inE ntz /= in ntCMs_z.
by rewrite (mem_normal_Hall hallE3 nsE3E) ?(subsetP sE0E) // /p_elt oz pnatE.
Qed.

(* This is B & G, Theorem 12.8(c). This part does not use the decompotision   *)
(* of the complement, and needs to be proved ahead because it is used with    *)
(* different primes in \tau_2(M) in the main argument. We also include an     *)
(* auxiliary identity, which is needed in another part of the proof of 12.8.  *)
Theorem abelian_tau2_sub_Fitting : forall M E p A S,
    M \in 'M -> \sigma(M)^'.-Hall(M) E ->
    p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-Sylow(G) S -> A \subset S -> abelian S ->
  [/\        S \subset 'N(S)^`(1),
    'N(S)^`(1) \subset 'F(E),
         'F(E) \subset 'C(S),
         'C(S) \subset E
   &     'F('N(A)) = 'F(E)].
Proof.
move=> M E p A S maxM hallE t2Mp Ep2A sylS sAS cSS.
have [sAE abelA dimA]:= pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [sEM sM'E _] := and3P hallE.
have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
have eqFC: forall H, A <| H -> 'C(A) \subset H -> 'F(H) = 'F('C(A)).
  move=> H nsAH sCH; have [_ nAH] := andP nsAH.
  apply/eqP; rewrite eqEsubset !Fitting_max ?Fitting_nil //.
    by rewrite (char_normal_trans (Fitting_char _)) // /normal sCH norms_cent.
  apply: normalS sCH (Fitting_normal H).
  have [_ defF cFpFp' _] := dprodP (nilpotent_pcoreC p (Fitting_nil H)).
  have sAFp: A \subset 'O_p('F(H)) by rewrite p_core_Fitting pcore_max.
  have [x _ sFpSx] := Sylow_subJ sylS (subsetT _) (pcore_pgroup p 'F(H)).
  have cFpFp: abelian 'O_p('F(H)) by rewrite (abelianS sFpSx) ?abelianJ.
  by rewrite -defF mulG_subG (centSS _ _ cFpFp) // (centSS _ _ cFpFp').
have [[nsAE _] [sCAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp Ep2A.
have eqFN_FE: 'F('N(A)) = 'F(E) by rewrite (eqFC E) // eqFC ?cent_sub ?normalG.
have sN'FN: 'N(A)^`(1) \subset 'F('N(A)).
  rewrite rank2_der1_sub_Fitting ?mFT_odd //.
    rewrite ?mFT_sol // mFT_norm_proper ?(mFT_pgroup_proper pA) //.
    by rewrite -rank_gt0 (rank_abelem abelA) dimA.
  rewrite eqFN_FE (leq_trans (rankS (Fitting_sub E))) //.
  have [q q_pr ->]:= rank_witness E; apply: wlog_neg; rewrite -ltnNge => rEgt2.
  rewrite (leq_trans (p_rankS q sEM)) // leqNgt.
  apply: contra ((alpha_sub_sigma maxM) q) (pnatPpi sM'E _).
  by rewrite -p_rank_gt0 (leq_trans _ rEgt2).
have sSE: S \subset E by rewrite (subset_trans _ sCAE) // (centSS _ _ cSS).
have nA_NS: 'N(S) \subset 'N(A).
  have [ ] := tau2_context maxM t2Mp Ep2A_M; have sSM := subset_trans sSE sEM.
  have sylS_M: p.-Sylow(M) S := pHall_subl sSM (subsetT M) sylS.
  by case/(_ S) => // _ [// |<- _] _ _ _ _; exact: char_norms (Ohm_char 1 _).
have sS_NS': S \subset 'N(S)^`(1) := pSylow_norm_split_sub_norm_der1 sylS.
have sNS'_FE: 'N(S)^`(1) \subset 'F(E).
  by rewrite -eqFN_FE (subset_trans (dergS 1 nA_NS)).
split=> //; last by rewrite (subset_trans (centS sAS)).
have sSFE := subset_trans sS_NS' sNS'_FE; have nilFE := Fitting_nil E.
have sylS_FE := pHall_subl sSFE (subsetT 'F(E)) sylS.
suff sSZF: S \subset 'Z('F(E)) by rewrite centsC (subset_trans sSZF) ?subsetIr.
have [_ <- _ _] := dprodP (center_dprod (nilpotent_pcoreC p nilFE)).
by rewrite -(nilpotent_Hall_pcore nilFE sylS_FE) (center_idP cSS) mulG_subl.
Qed.

(* This is B & G, Theorem 12.8(a,b,d,e) -- the bulk of the Theorem. We prove  *)
(* part (f) separately below, as it does not depend on a decomposition of the *)
(* complement.                                                                *)
Theorem abelian_tau2 : forall M E E1 E2 E3 p A S,
    M \in 'M -> sigma_complement M E E1 E2 E3 ->
    p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-Sylow(G) S -> A \subset S -> abelian S ->
  let Ms := M`_\sigma in
  [/\ (*a*) E2 <| E /\ abelian E2,
      (*b*) \tau2(M).-Hall(G) E2,
      (*d*) [/\       'N(A) = 'N(S),
                      'N(S) = 'N(E2),
                     'N(E2) = 'N(E3 <*> E2)
            & 'N(E3 <*> E2) = 'N('F(E))]
    & (*e*) forall X, X \in 'E^1(E1) -> 'C_Ms(X) = 1 -> X \subset 'Z(E)].
Proof.
move=> M E E1 E2 E3 p A S maxM complEi t2Mp Ep2A sylS sAS cSS Ms.
have [hallE hallE1 hallE2 hallE3 _] := complEi.
have [sEM sM'E _] := and3P hallE.
have [sE1E t1E1 _] := and3P hallE1.
have [sE2E t2E2 _] := and3P hallE2.
have [sE3E t3E3 _] := and3P hallE3.
have nilF: nilpotent 'F(E) := Fitting_nil E.
have sylE2_sylG_ZFE: forall q Q,
  q.-Sylow(E2) Q -> Q :!=: 1 -> q.-Sylow(G) Q /\ Q \subset 'Z('F(E)).
- move=> q Q sylQ ntQ; have [sQE2 qQ _] := and3P sylQ.
  have piQq: q \in \pi(#|Q|) by rewrite -p_rank_gt0 -rank_pgroup // rank_gt0.
  have t2Mq: q \in \tau2(M) by rewrite (pnatPpi t2E2) // (piSg sQE2).
  have sylQ_E: q.-Sylow(E) Q := pSylow_Hall_Sylow hallE2 t2Mq sylQ.
  have rqQ: 'r_q(Q) = 2.
    rewrite (tau2E hallE) !inE (p_rank_Sylow sylQ_E) in t2Mq.
    by case/andP: t2Mq => _; move/eqP.
  have [B Eq2B sBQ]: exists2 B, B \in 'E_q^2(E) & B \subset Q.
    have [B Eq2B] := p_rank_witness q Q; have [sBQ abelB rBQ] := pnElemP Eq2B.
    exists B; rewrite // !inE rBQ rqQ abelB !andbT.
    exact: subset_trans sBQ (pHall_sub sylQ_E).
  have [T /= sylT sQT] := Sylow_superset (subsetT Q) qQ.
  have qT: q.-group T := pHall_pgroup sylT.
  have cTT: abelian T.
    apply: wlog_neg => not_cTT.
    have [def_t2 _ _ _] := nonabelian_tau2 maxM hallE t2Mq Eq2B qT not_cTT.
    rewrite def_t2 !inE in t2Mp; rewrite (eqP t2Mp) in sylS.
    by have [x _ ->] := Sylow_trans sylS sylT; rewrite abelianJ.
  have sTF: T \subset 'F(E).
    have subF := abelian_tau2_sub_Fitting maxM hallE t2Mq Eq2B sylT.
    have [sTN' sN'F _ _ _] := subF (subset_trans sBQ sQT) cTT.
    exact: subset_trans sTN' sN'F.
  have sTE: T \subset E := subset_trans sTF (Fitting_sub E).
  have <-: T :=: Q by exact: (sub_pHall sylQ_E).
  have sylT_F: q.-Sylow('F(E)) T := pHall_subl sTF (subsetT _) sylT.
  have [_ <- _ _] := dprodP (center_dprod (nilpotent_pcoreC q nilF)).
  by rewrite -(nilpotent_Hall_pcore nilF sylT_F) (center_idP cTT) mulG_subl.
have hallE2_G: \tau2(M).-Hall(G) E2.
  rewrite pHallE subsetT /= -(part_pnat_id t2E2); apply/eqnP.
  rewrite !(widen_partn _ (subset_leq_card (subsetT _))).
  apply: eq_bigr => q t2q; rewrite -!p_part.
  have [Q sylQ] := Sylow_exists q E2; have qQ := pHall_pgroup sylQ.
  have sylQ_E: q.-Sylow(E) Q := pSylow_Hall_Sylow hallE2 t2q sylQ.
  have ntQ: Q :!=: 1.
    rewrite -rank_gt0 (rank_pgroup qQ) -(p_rank_Sylow sylQ_E) p_rank_gt0.
    by rewrite (tau2E hallE) in t2q; case/andP: t2q.
  have [sylQ_G _] := sylE2_sylG_ZFE q Q sylQ ntQ.
  by rewrite -(card_Hall sylQ) -(card_Hall sylQ_G).
have sE2_ZFE: E2 \subset 'Z('F(E)).
  rewrite -Sylow_gen gen_subG; apply/bigcupsP=> Q; case/SylowP=> q q_pr sylQ.
  have [-> | ntQ] := eqsVneq Q 1; first exact: sub1G.
  by have [_ ->] := sylE2_sylG_ZFE q Q sylQ ntQ.
have cE2E2: abelian E2 := abelianS sE2_ZFE (center_abelian _).
have sE2FE: E2 \subset 'F(E) := subset_trans sE2_ZFE (center_sub _).
have nsE2E: E2 <| E.
  have hallE2_F := pHall_subl sE2FE (Fitting_sub E) hallE2.
  rewrite (nilpotent_Hall_pcore nilF hallE2_F).
  exact: char_normal_trans (pcore_char _ _) (Fitting_normal E).
have [_ _ [cycE1 cycE3] [_ defEl] _] := sigma_complement_context maxM complEi.
have [[K _ defK _] _ _ _] := sdprodP defEl; rewrite defK in defEl.
have [nsKE _ mulKE1 nKE1 _] := sdprod_context defEl; have [sKE _] := andP nsKE.
have [nsE3K sE2K _ nE32 tiE32] := sdprod_context defK.
rewrite -sdprodEgen // defK.
have{defK} defK: E3 \x E2 = K.
  rewrite dprodEsdprod // (sameP commG1P trivgP) -tiE32 subsetI commg_subr nE32.
  by rewrite commg_subl (subset_trans sE3E) ?normal_norm.
have cKK: abelian K.
  have [_ <- cE23 _] := dprodP defK.
  by rewrite abelianM centsC cE2E2 cyclic_abelian.
have [_ sNS'F _ sCS_E defFN] :=
  abelian_tau2_sub_Fitting maxM hallE t2Mp Ep2A sylS sAS cSS.
have{sCS_E} sSE2: S \subset E2.
  rewrite (subset_normal_Hall _ hallE2 nsE2E) /psubgroup /pgroup .
  by rewrite (subset_trans cSS sCS_E) (pi_pnat (pHall_pgroup sylS)).
have charS: S \char E2.
  have sylS_E2: p.-Sylow(E2) S := pHall_subl sSE2 (subsetT E2) sylS.
  by rewrite (nilpotent_Hall_pcore (abelian_nil cE2E2) sylS_E2) pcore_char.
have nsSE: S <| E := char_normal_trans charS nsE2E; have [sSE nSE] := andP nsSE.
have charA: A \char S.
  have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
  have sylS_M := pHall_subl (subset_trans sSE sEM) (subsetT M) sylS.
  have [] := tau2_context maxM t2Mp Ep2A_M; case/(_ S sylS_M)=> _ [//|<- _].
  by rewrite Ohm_char.
have charE2: E2 \char K.
  have hallE2_K := pHall_subl sE2K sKE hallE2.
  by rewrite (nilpotent_Hall_pcore (abelian_nil cKK) hallE2_K) pcore_char.
have coKE1: coprime #|K| #|E1|.
  rewrite -(dprod_card defK) coprime_mull (sub_pnat_coprime tau3'1 t3E3 t1E1).
  by rewrite (sub_pnat_coprime tau2'1 t2E2 t1E1).
have hallK: Hall 'F(E) K.
  have hallK: Hall E K.
    by rewrite /Hall -divgS sKE //= -(sdprod_card defEl) mulKn.
  have sKFE: K \subset 'F(E) by rewrite Fitting_max ?abelian_nil.
  exact: pHall_Hall (pHall_subl sKFE (Fitting_sub E) (Hall_pi hallK)).
have charK: K \char 'F(E).
  by rewrite (nilpotent_Hall_pcore nilF (Hall_pi hallK)) pcore_char.
have{defFN} [eqNAS eqNSE2 eqNE2K eqNKF]:
  [/\ 'N(A) = 'N(S), 'N(S) = 'N(E2), 'N(E2) = 'N(K) & 'N(K) = 'N('F(E))].
  have: #|'N(A)| <= #|'N('F(E))|.
    by rewrite subset_leq_card // -defFN bgFunc_norm.
  have leCN := subset_leqif_cards (@char_norms gT _ _ _).
  have trCN := leqif_trans (leCN _ _ _).
  have leq_KtoA := trCN _ _ _ _ charE2 (trCN _ _ _ _ charS (leCN _ _ charA)).
  rewrite (geq_leqif (trCN _ _ _ _ charK leq_KtoA)).
  by case/and4P; do 4!move/eqP->.
split=> // X E1_1_X regX.
have cK_NK': 'N(K)^`(1) \subset 'C(K).
  suffices sKZ: K \subset 'Z('F(E)).
    by rewrite -eqNE2K -eqNSE2 (centSS sNS'F sKZ) // centsC subsetIr.
  have{hallK} [pi hallK] := HallP hallK.
  have [_ <- _ _] := dprodP (center_dprod (nilpotent_pcoreC pi nilF)).
  by rewrite -(nilpotent_Hall_pcore nilF hallK) (center_idP cKK) mulG_subl.
have [q EqX] := nElemP E1_1_X; have [sXE1 abelX dimX] := pnElemP EqX.
have sXE := subset_trans sXE1 sE1E.
have nKX := subset_trans sXE (normal_norm nsKE).
have nCSX_NS: 'N(K) \subset 'N('C(K) * X).
  rewrite -(quotientGK (cent_normal _)) -quotientK ?norms_cent //.
  by rewrite morphpre_norms // sub_abelian_norm ?quotientS ?sub_der1_abelian.
have nKX_NS: 'N(S) \subset 'N([~: K, X]).
  have CK_K_1: [~: 'C(K), K] = 1 by exact/commG1P.
  rewrite eqNSE2 eqNE2K commGC -[[~: X, K]]mul1g -CK_K_1.
  by rewrite -commMG ?CK_K_1 ?norms1 ?normsR.
have not_sNKX_M: ~~ ('N([~: K, X]) \subset M).
  have [[sM'p _] sSM] := (andP t2Mp, subset_trans sSE sEM).
  apply: contra sM'p => sNKX_M; apply/existsP; exists S.
  by rewrite (pHall_subl sSM (subsetT _) sylS) // (subset_trans _ sNKX_M).
have cKX: K \subset 'C(X).
  apply: contraR not_sNKX_M; rewrite (sameP commG1P eqP) => ntKX.
  rewrite (mmax_normal maxM) //.
  have sM'K: \sigma(M)^'.-subgroup(M) K.
    by rewrite /psubgroup (subset_trans sKE sEM) (pgroupS sKE sM'E).
  have piE1q: q \in \pi(#|E1|).
    by rewrite -p_rank_gt0 -dimX logn_le_p_rank // inE sXE1.
  have sM'q: q \in \sigma(M)^' by rewrite (pnatPpi sM'E) // (piSg sE1E).
  have EpX_NK: X \in 'E_q^1('N_M(K)).
    by apply: subsetP EqX; rewrite pnElemS // subsetI (subset_trans sE1E).
  have q'K: q^'.-group K.
    rewrite /pgroup p'natEpi ?coprime_pi' // in coKE1 *.
    exact: (pnatPpi coKE1).
  by have []:= commG_sigma'_1Elem_cyclic maxM sM'K sM'q EpX_NK regX.
rewrite subsetI sXE /= -mulKE1 centM subsetI centsC cKX.
exact: subset_trans sXE1 (cyclic_abelian cycE1).
Qed.

(* This is B & G, Theorem 12.8(f). *)
Theorem abelian_tau2_norm_Sylow : forall M E p A S,
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    p.-Sylow(G) S -> A \subset S -> abelian S ->
  forall X, X \subset 'N(S) -> 'C_S(X) <| 'N(S) /\ [~: S, X] <| 'N(S).
Proof.
move=> M E p A S maxM hallE t2Mp Ep2A sylS sAS cSS X nSX.
have [_ sNS'F sFCS _ _] :=
   abelian_tau2_sub_Fitting maxM hallE t2Mp Ep2A sylS sAS cSS.
have{sNS'F sFCS} sNS'CS: 'N(S)^`(1) \subset 'C(S) := subset_trans sNS'F sFCS.
have nCSX_NS: 'N(S) \subset 'N('C(S) * X).
  rewrite -quotientK ?norms_cent // -{1}(quotientGK (cent_normal S)).
  by rewrite morphpre_norms // sub_abelian_norm ?quotientS ?sub_der1_abelian.
rewrite /normal subIset ?comm_subG ?normG //=; split.
  have ->: 'C_S(X) = 'C_S('C(S) * X).
    by rewrite centM setIA; congr (_ :&: _); rewrite (setIidPl _) // centsC.
  by rewrite normsI ?norms_cent.
have CS_S_1: [~: 'C(S), S] = 1 by exact/commG1P.
by rewrite commGC -[[~: X, S]]mul1g -CS_S_1 -commMG ?CS_S_1 ?norms1 ?normsR.
Qed.

(* This is B & G, Corollary 12.9. *)
Corollary tau1_act_tau2 : forall M E p A q Q (Ms := M`_\sigma),
    M \in 'M -> \sigma(M)^'.-Hall(M) E -> p \in \tau2(M) -> A \in 'E_p^2(E) ->
    q \in \tau1(M) -> Q \in 'E_q^1(E) -> 'C_Ms(Q) = 1 -> [~: A, Q] != 1 ->
 let A0 := [~: A, Q]%G in let A1 := ('C_A(Q))%G in
 [/\ (*a*) [/\ A0 \in 'E_p^1(A), 'C_A(Ms) = A0 & A0 <| M],
     (*b*) gval A0 \notin A1 :^: G
   & (*c*) A1 \in 'E_p^1(A) /\ ~~ ('C(A1) \subset M)].
Proof.
move=> M E p A q Q Ms maxM hallE t2Mp Ep2A t1Mq EqQ regQ ntA0 A0 A1.
have [sEM sM'E _] := and3P hallE.
have [sAE abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [sQE abelQ dimQ] := pnElemP EqQ; have [qQ _ _] := and3P abelQ.
have [p_pr q_pr] := (pnElem_prime Ep2A, pnElem_prime EqQ).
have p_gt1 := prime_gt1 p_pr.
have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
have [_ _ regA _ _] := tau2_context maxM t2Mp Ep2A_M.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp Ep2A.
have [_ nAE] := andP nsAE; have nAQ := subset_trans sQE nAE.
have coAQ: coprime #|A| #|Q|.
  exact: sub_pnat_coprime tau2'1 (pi_pnat pA t2Mp) (pi_pnat qQ t1Mq).
have defA: A0 \x A1 = A := coprime_abelian_cent_dprod nAQ coAQ cAA.
have [_ _ _ tiA01] := dprodP defA.
have sM'A: \sigma(M)^'.-subgroup(M) A.
  by rewrite /psubgroup (subset_trans sAE sEM) (pgroupS sAE sM'E).
have sM'q: q \in \sigma(M)^' by case/andP: t1Mq.
have EqQ_NA: Q \in 'E_q^1('N_M(A)).
  by apply: subsetP EqQ; rewrite pnElemS // subsetI sEM.
have q'A: q^'.-group A.
  rewrite /pgroup p'natEpi ?coprime_pi' // in coAQ *.
  by apply: (pnatPpi coAQ); rewrite -p_rank_gt0 (p_rank_abelem abelQ) dimQ.
have [] := commG_sigma'_1Elem_cyclic maxM sM'A sM'q EqQ_NA regQ q'A cAA.
rewrite -[[~: A, Q]]/(gval A0) -/Ms => cMsA0 cycA0 nsA0M.
have sA0A: A0 \subset A by rewrite commg_subl.
have EpA0: A0 \in 'E_p^1(A).
  have abelA0 := abelemS sA0A abelA; have [pA0 _] := andP abelA0.
  rewrite p1ElemE // !inE sA0A -(Ohm1_id abelA0) /=.
  by rewrite (Ohm1_cyclic_pgroup_prime cycA0 pA0).
have defA0: 'C_A(Ms) = A0.
  apply/eqP; rewrite eq_sym eqEcard subsetI sA0A cMsA0 (card_pnElem EpA0).
  have pCAMs: p.-group 'C_A(Ms) := pgroupS (subsetIl A _) pA.
  rewrite (card_pgroup pCAMs) leq_exp2l //= leqNgt.
  apply: contra (Msigma_neq1 maxM) => dimCAMs.
  rewrite eq_sym -regA (sameP eqP setIidPl) centsC (sameP setIidPl eqP).
  by rewrite eqEcard subsetIl (card_pnElem Ep2A) (card_pgroup pCAMs) leq_exp2l.
have EpA1: A1 \in 'E_p^1(A).
  rewrite p1ElemE // !inE subsetIl -(eqn_pmul2l (ltnW p_gt1)).
  by rewrite -{1}[p](card_pnElem EpA0) (dprod_card defA) (card_pnElem Ep2A) /=.
have defNA0: 'N(A0) = M by exact: mmax_normal.
have not_cA0Q: ~~ (Q \subset 'C(A0)).
  apply: contra ntA0 => cA0Q.
  by rewrite -subG1 -tiA01 !subsetI subxx sA0A centsC cA0Q.
have rqM: 'r_q(M) = 1%N by apply/eqP; case/and3P: t1Mq.
have q'CA0: q^'.-group 'C(A0).
  have [S sylS sQS] := Sylow_superset (subset_trans sQE sEM) qQ.
  have qS := pHall_pgroup sylS; rewrite (p_rank_Sylow sylS) in rqM.
  have cycS: cyclic S by rewrite (odd_pgroup_rank1_cyclic qS) ?mFT_odd ?rqM.
  have ntS: S :!=: 1 by rewrite -rank_gt0 (rank_pgroup qS) rqM.
  have defS1: 'Ohm_1(S) = Q.
    apply/eqP; rewrite eq_sym eqEcard -{1}(Ohm1_id abelQ) OhmS //=.
    by rewrite (card_pnElem EqQ) (Ohm1_cyclic_pgroup_prime cycS qS).
  have sylSC: q.-Sylow('C(A0)) 'C_S(A0).
    by rewrite (Hall_setI_normal _ sylS) // -defNA0 cent_normal.
  rewrite /pgroup -partn_eq1 ?cardG_gt0 // -(card_Hall sylSC) -trivg_card1 /=.
  by rewrite setIC TI_Ohm1 // defS1 setIC prime_TIg ?(card_pnElem EqQ).
do 2?split=> //.
  have: ~~ q^'.-group Q by rewrite /pgroup (card_pnElem EqQ) pnatE ?inE ?negbK.
  apply: contra; case/imsetP=> x _ defA01.
  rewrite defA01 centJ pgroupJ in q'CA0.
  by apply: pgroupS q'CA0; rewrite centsC subsetIr.
have [S sylS sAS] := Sylow_superset (subsetT A) pA.
have [cSS | not_cSS] := boolP (abelian S).
  have solE := solvableS sEM (mmax_sol maxM).
  have [E1 hallE1 sQE1] := Hall_superset solE sQE (pi_pnat qQ t1Mq).
  have [E3 hallE3] := Hall_exists \tau3(M) solE.
  have [E2 _ complEi] := sigma_complement_exists maxM hallE hallE1 hallE3.
  have [_ _ _ reg1Z] := abelian_tau2 maxM complEi t2Mp Ep2A sylS sAS cSS.
  have E1Q: Q \in 'E^1(E1).
    by apply/nElemP; exists q; rewrite // !inE sQE1 abelQ dimQ.
  rewrite (subset_trans (reg1Z Q E1Q regQ)) ?subIset // in not_cA0Q.
  by rewrite centS ?orbT // (subset_trans sA0A).
have pS := pHall_pgroup sylS.
have [_ _ not_cent_reg _] := nonabelian_tau2 maxM hallE t2Mp Ep2A pS not_cSS.
case: (not_cent_reg A1); rewrite // 2!inE (subsetP (pnElemS p 1 sAE)) // andbT.
by rewrite -val_eqE /= defA0 eq_sym; apply/(TIp1ElemP EpA0 EpA1).
Qed.

(* This is B & G, Corollary 12.10(a). *)
Corollary sigma'_nil_abelian : forall M N,
  M \in 'M -> N \subset M -> \sigma(M)^'.-group N -> nilpotent N -> abelian N.
Proof.
move=> M N maxM sNM sM'N nilN.
have [E hallE sNE] := Hall_superset (mmax_sol maxM) sNM sM'N.
have [[E1 hallE1] [E3 hallE3]] := tau13_complements_exist maxM hallE.
have [E2 hallE2 complEi] := sigma_complement_exists maxM hallE hallE1 hallE3.
have [_ _ [cycE1 cycE3] _ _] := sigma_complement_context maxM complEi.
rewrite (sameP center_idP eqP) eqEsubset subsetIl /= -{1}Sylow_gen gen_subG.
apply/bigcupsP=> P; case/SylowP=> p p_pr sylP; have [sPN pP _] := and3P sylP. 
have sPE := subset_trans sPN sNE.
have [-> | ntP] := eqsVneq P 1; first exact: sub1G.
suffices cPP: abelian P.
  have [_ /= <- _ _] := dprodP (center_dprod (nilpotent_pcoreC p nilN)).
  by rewrite -(nilpotent_Hall_pcore nilN sylP) (center_idP cPP) mulG_subl.
suffices [S sylS cSS]: exists2 S : {group gT}, p.-Sylow(E) S & abelian S.
  by have [x _ sPS]:= Sylow_subJ sylS sPE pP; rewrite (abelianS sPS) ?abelianJ.
have piEp: p \in \pi(#|E|).
  by rewrite (piSg sPE) // -p_rank_gt0 -rank_pgroup // rank_gt0.
rewrite (partition_pi_mmax_compl maxM hallE) inE /= orbC /= in piEp.
have{piEp} [t3p | /= t1p | /= t2p] := or3P piEp.
- have [S sylS] := Sylow_exists p E3.
  exists S; first exact: pSylow_Hall_Sylow hallE3 t3p sylS.
  exact: abelianS (pHall_sub sylS) (cyclic_abelian cycE3).
- have [S sylS] := Sylow_exists p E1.
  exists S; first exact: pSylow_Hall_Sylow hallE1 t1p sylS.
  exact: abelianS (pHall_sub sylS) (cyclic_abelian cycE1).
have [s'p rpM] := andP t2p; have [S sylS] := Sylow_exists p E; exists S => //.
have sylS_M := pSylow_Hall_Sylow hallE s'p sylS.
have [A Ep2A] := p_rank_witness p S; have{Ep2A}[sAS abelA dimA] := pnElemP Ep2A.
have Ep2A: A \in 'E_p^2(M).
  rewrite !inE abelA (subset_trans sAS (pHall_sub sylS_M)) dimA /=.
  by rewrite -(p_rank_Sylow sylS_M).
by have []:= tau2_context maxM t2p Ep2A; case/(_ S sylS_M).
Qed.

(* This is B & G, Corollary 12.10(b). Note that we do not require the full   *)
(* decomposition of the complement.                                          *)
Corollary der_mmax_compl_abelian  : forall M E,
    M \in 'M -> \sigma(M)^'.-Hall(M) E ->
   abelian E^`(1) /\ (forall E2, \tau2(M).-Hall(E) E2 -> abelian E2).
Proof.
move=> M E maxM hallE; have [sEM s'E _] := and3P hallE.
split=> [|E20 hallE20].
  have sE'E := der_sub 1 E; have sE'M := subset_trans sE'E sEM.
  exact: sigma'_nil_abelian (pgroupS _ s'E) (mmax_compl_nil maxM hallE).
have [-> | ntE20] := eqsVneq E20 1; first exact: abelian1.
have [p p_pr rpE20] := rank_witness E20; have [sE20E t2E20 _] := and3P hallE20.
have piE2p: p \in \pi(#|E20|) by rewrite -p_rank_gt0 -rpE20 rank_gt0.
have t2p := pnatPpi t2E20 piE2p.
have rpE: 'r_p(E) = 2 by apply/eqP; move: t2p; rewrite (tau2E hallE); case/andP.
have [A Ep2A] := p_rank_witness p E; rewrite rpE in Ep2A.
have [_ abelA _] := pnElemP Ep2A; have [pA _] := andP abelA.
have [S /= sylS sAS] := Sylow_superset (subsetT A) pA.
have [cSS | not_cSS] := boolP (abelian S).
  have [[E1 hallE1] [E3 hallE3]] := tau13_complements_exist maxM hallE.
  have [E2 hallE2 complEi] := sigma_complement_exists maxM hallE hallE1 hallE3.
  have [[_ cE2E2] _ _ _] := abelian_tau2 maxM complEi t2p Ep2A sylS sAS cSS.
  have solE := solvableS sEM (mmax_sol maxM).
  by have [x _ ->]:= Hall_trans solE hallE20 hallE2; rewrite abelianJ.
have [_ pS _] := and3P sylS.
have [def_t2 _ _ _] := nonabelian_tau2 maxM hallE t2p Ep2A pS not_cSS.
apply: sigma'_nil_abelian (subset_trans _ sEM) (pgroupS _ s'E) _ => //.
by rewrite (eq_pgroup _ def_t2) in t2E20; exact: pgroup_nil t2E20.
Qed.

End Section12.


Implicit Arguments tau2'1 [[gT] [M] x].
Implicit Arguments tau3'1 [[gT] [M] x].
Implicit Arguments tau3'2 [[gT] [M] x].

