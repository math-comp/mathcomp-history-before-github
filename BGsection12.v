(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection10 BGsection11.

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
Implicit Types A E H K M N P Q R S T U V W X Y : {group gT}.

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
Lemma tau13_complements_exist : exHallE \tau1(M) /\ exHallE \tau1(M).
Proof. by split; exact: Hall_exists. Qed.

Lemma sigma_complement_exists : forall E1 E3,
    \tau1(M).-Hall(E) E1 -> \tau3(M).-Hall(E) E3 ->
  exists E2 : {group gT}, sigma_complement M E E1 E2 E3.
Proof.
move=> E1 E3 hallE1 hallE3; have [sE1E t1E1 _] := and3P hallE1.
pose tau12 := [predU \tau1(M) & \tau2(M)].
have t12E1: tau12.-group E1.
  by apply: sub_in_pnat t1E1 => p _ t1p; apply/orP; left.
have [E21 hallE21 sE1E21] := Hall_superset solE sE1E t12E1.
have [sE21E t12E21 _] := and3P hallE21.
have [E2 hallE2] := Hall_exists \tau2(M) (solvableS sE21E solE).
have [sE2E21 t2E2 _] := and3P hallE2.
exists E2; split=> //.
  rewrite pHallE (subset_trans sE2E21 sE21E) (card_Hall hallE2).
  by rewrite (card_Hall hallE21) partn_part //= => p t2p; apply/orP; right.
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
move=> p; case/andP=> sM'p; move/eqP=> rpM; split.
  apply: contra (sigma'_prank2_Ep2_EpG maxM sM'p rpM); rewrite -subset0.
  case/beta_not_narrow; move/disjoint_setI0=> <- _.
  by rewrite setSI ?pnElemS ?subsetT.
by apply/subsetP; exact: sigma'_prank2_Ep2_sub.
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

End Section12.

Implicit Arguments tau2'1 [[gT] [M] x].
Implicit Arguments tau3'1 [[gT] [M] x].
Implicit Arguments tau3'2 [[gT] [M] x].

