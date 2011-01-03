(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection12 BGsection13.
Require Import BGsection14.

(******************************************************************************)
(*   This file covers B & G, section 15; it fills in the picture of maximal   *)
(* subgroups that was sketched out in section14, providing an intrinsic       *)
(* characterization of M`_\sigma and establishing the TI property for the     *)
(* "kernels" of maximal groups. We introduce only one new definition:         *)
(*    M`_\F == the (direct) product of all the normal Sylow subgroups of M;   *)
(*             equivalently, the largest normal nilpotent Hall subgroup of M  *)
(*             We will refer to M`_\F as the Fitting core or F-core of M.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Definitions.

Variables (gT : finGroupType) (M : {set gT}).

Definition Fitting_core :=
  <<\bigcup_(P : {group gT} | Sylow M P && (P <| M)) P>>.
Canonical Structure Fitting_core_group := [group of Fitting_core].

End Definitions.

Notation "M `_ \F" := (Fitting_core M)
  (at level 3, format "M `_ \F") : group_scope.
Notation "M `_ \F" := (Fitting_core_group M) : subgroup_scope.

Section FittingCore.

Variable (gT : finGroupType) (M : {group gT}).
Implicit Types H P : {group gT}.
Implicit Type p : nat.

Lemma Fcore_normal : M`_\F <| M.
Proof.
rewrite -[M`_\F]bigprodGE.
apply big_prop => [|P Q nsP nsG|P]; [exact: normal1 | | by case/andP].
by rewrite /normal normsY ?normal_norm // join_subG ?normal_sub.
Qed.
Hint Resolve Fcore_normal.

Lemma Fcore_sub : M`_\F \subset M.
Proof. by case/andP: Fcore_normal. Qed.

Lemma Fcore_sub_Fitting : M`_\F \subset 'F(M).
Proof.
rewrite gen_subG; apply/bigcupsP=> P; case/andP; case/SylowP=> p _.
by case/and3P=> _ pP _ nsP; rewrite Fitting_max // (pgroup_nil pP).
Qed.

Lemma Fcore_nil : nilpotent M`_\F.
Proof. exact: nilpotentS Fcore_sub_Fitting (Fitting_nil M). Qed.

Lemma Fcore_max : forall pi H,
  pi.-Hall(M) H -> H <| M -> nilpotent H -> H \subset M`_\F.
Proof.
move=> pi H hallH nsHM nilH; have [sHM pi_H _] := and3P hallH.
rewrite -(nilpotent_Fitting nilH) FittingEgen genS //.
apply/bigcupsP=> [[p /= _] piHp]; rewrite (bigcup_max 'O_p(H)%G) //.
have sylHp := nilpotent_pcore_Hall p nilH.
have sylHp_M := subHall_Sylow hallH (pnatPpi pi_H piHp) sylHp.
by rewrite (p_Sylow sylHp_M) (char_normal_trans (pcore_char _ _)).
Qed.

Lemma Fcore_dprod : \big[dprod/1]_(P | Sylow M (gval P) && (P <| M)) P = M`_\F.
Proof.
rewrite -[M`_\F]bigprodGE; apply/eqP; apply/bigdprodYP=> P; case/andP.
case/SylowP=> p p_pr sylP nsPM; have defP := normal_Hall_pcore sylP nsPM.
have [_ _ cFpFp' tiFpFp'] := dprodP (nilpotent_pcoreC p (Fitting_nil M)).
move/dprodYP: (dprodEY cFpFp' tiFpFp'); rewrite /= p_core_Fitting defP.
apply: subset_trans; rewrite bigprodGE gen_subG.
apply/bigcupsP=> Q; do 2![case/andP]; case/SylowP=> q _ sylQ nsQM neqQP.
have defQ := normal_Hall_pcore sylQ nsQM; rewrite -defQ -p_core_Fitting.
apply: sub_pcore => q'; move/eqnP->; apply: contraNneq neqQP => eq_qp.
by rewrite -val_eqE /= -defP -defQ eq_qp.
Qed.

Lemma Fcore_pcore_Sylow : forall p, p \in \pi(M`_\F) -> p.-Sylow(M) 'O_p(M).
Proof.
move=> p /=; rewrite -(bigdprod_card Fcore_dprod) mem_primes.
case/and3P=> p_pr _; have ?: ~ p %| 1 by rewrite gtnNdvd ?prime_gt1.
apply big_prop=> // [p1 p2 IH1 IH2|P].
  rewrite euclid //; case/orP; [exact: IH1 | exact: IH2].
case/andP; case/SylowP=> q q_pr sylP nsPM p_dv_P; have qP := pHall_pgroup sylP.
by rewrite (eqnP (pgroupP qP p p_pr p_dv_P)) (normal_Hall_pcore sylP).
Qed.

Lemma p_core_Fcore : forall p, p \in \pi(M`_\F) -> 'O_p(M`_\F) = 'O_p(M).
Proof.
move=> p piMFp /=; rewrite -(pcore_setI_normal p Fcore_normal).
apply/setIidPl; rewrite sub_gen // (bigcup_max 'O_p(M)%G) //= pcore_normal.
by rewrite (p_Sylow (Fcore_pcore_Sylow piMFp)).
Qed.

Lemma Fcore_Hall : \pi(M`_\F).-Hall(M) M`_\F.
Proof.
rewrite Hall_pi // /Hall Fcore_sub coprime_pi' ?cardG_gt0 //=.
apply/pnatP=> // p p_pr; apply: contraL => /= piMFp; rewrite -p'natE //.
rewrite -partn_eq1 // -(eqn_pmul2l (part_gt0 p #|M`_\F|)) muln1.
rewrite -partn_mul ?cardG_gt0 // LaGrange ?Fcore_sub //.
rewrite -(card_Hall (nilpotent_pcore_Hall p Fcore_nil)) /=.
by rewrite p_core_Fcore // (card_Hall (Fcore_pcore_Sylow piMFp)).
Qed.

Lemma pcore_Fcore : forall pi,
  {subset pi <= \pi(M`_\F)} -> 'O_pi(M`_\F) = 'O_pi(M).
Proof.
move=> pi s_pi_MF; rewrite -(pcore_setI_normal pi Fcore_normal); apply/setIidPl.
rewrite (sub_normal_Hall Fcore_Hall) ?pcore_sub //.
exact: sub_pgroup s_pi_MF (pcore_pgroup pi M).
Qed.

Lemma Fcore_pcore_Hall : forall pi,
  {subset pi <= \pi(M`_\F)} -> pi.-Hall(M) 'O_pi(M).
Proof.
move=> pi s_pi_MF; apply: (subHall_Hall Fcore_Hall s_pi_MF).
by rewrite /= -pcore_Fcore // (nilpotent_pcore_Hall pi Fcore_nil).
Qed.

End FittingCore.

Lemma Fcore_continuity : cont Fitting_core.
Proof.
move=> gT rT G f.
apply: (Fcore_max (morphim_pHall f (Fcore_sub G) (Fcore_Hall G))).
  by rewrite morphim_normal ?Fcore_normal.
by rewrite morphim_nil ?Fcore_nil.
Qed.

Lemma Fcore_hereditary : hereditary Fitting_core.
Proof.
move=> gT H G sHG; have nsGF_G := Fcore_normal G.
apply: Fcore_max (setI_normal_Hall nsGF_G (Fcore_Hall G) sHG) _ _.
  by rewrite /= setIC (normalGI sHG) //.
exact: nilpotentS (subsetIl _ _) (Fcore_nil G).
Qed.

Canonical Structure bgFunc_Fcore := [bgFunc by Fcore_sub & Fcore_continuity].

Canonical Structure gFunc_Fcore := GFunc Fcore_continuity.

Canonical Structure hgFunc_Fcore := HGFunc Fcore_hereditary.

Section MoreFittingCore.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Type M H : {group gT}.

Lemma Fcore_char : forall M, M`_\F \char M. Proof. exact: bgFunc_char. Qed.

Lemma FcoreJ : forall M x, (M :^ x)`_\F = M`_\F :^ x.
Proof.
move=> M x; rewrite -{1}(setTI M) -morphim_conj.
by rewrite -bgFunc_ascont ?injm_conj ?subsetT // morphim_conj setTI.
Qed.

Lemma morphim_Fcore : forall M, f @* M`_\F \subset (f @* M)`_\F.
Proof. move=> M; exact: hgFunc_morphim. Qed.

Lemma injm_Fcore : forall M,
  'injm f -> M \subset D -> f @* M`_\F = (f @* M)`_\F.
Proof. by move=> M injf sMD; rewrite bgFunc_ascont. Qed.

Lemma isom_Fcore : forall M (R : {group rT}),
  isom M R f -> M \subset D -> isom M`_\F R`_\F f.
Proof. by move=> M R isoMR sMD; exact: bgFunc_isom. Qed.

Lemma isog_Fcore : forall M (R : {group rT}), M \isog R -> M`_\F \isog R`_\F.
Proof. by move=> M R isoMR; exact: bgFunc_isog. Qed.

End MoreFittingCore.

Section Section15.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

Lemma Fcore_sub_Msigma : forall M, M \in 'M -> M`_\F \subset M`_\sigma.
Proof.
move=> M maxM; rewrite gen_subG; apply/bigcupsP=> P; case/andP.
case/SylowP=> p _ sylP nsPM; have [sPM pP _] := and3P sylP.
have [-> | ntP] := eqsVneq P 1; first exact: sub1G.
rewrite (sub_Hall_pcore (Msigma_Hall maxM)) // (pi_pgroup pP) //.
by apply/exists_inP; exists P; rewrite ?(mmax_normal maxM).
Qed.

Lemma Fcore_eq_Msigma : forall M,
  M \in 'M -> reflect (M`_\F = M`_\sigma) (nilpotent M`_\sigma).
Proof.
move=> M maxM; apply: (iffP idP) => [nilMs | <-]; last exact: Fcore_nil.
apply/eqP; rewrite eqEsubset Fcore_sub_Msigma //.
by rewrite (Fcore_max (Msigma_Hall maxM)) ?pcore_normal.
Qed.

(* This is B & G, Lemma 15.1. *)
(* We have made all semidirect products explicits, and omitted the assertion  *)
(* M`_\sigma \subset M^`(1), which is exactly covered by Msigma_der1.         *)
(*   Some refactoring is definitely needed here, to avoid the mindless cut    *)
(* and paste of a large fragment of the proof of Lemma 12.12.                 *)
Lemma kappa_structure : forall M U K (Ms := M`_\sigma),
     M \in 'M -> kappa_complement M U K ->
  [/\ (*a*) [/\ (Ms ><| U) ><| K = M, cyclic K & abelian (M^`(1) /  Ms)],
      (*b*) K :!=: 1 -> Ms ><| U = M^`(1) /\ abelian U,
      (*c*) forall X, X \subset U -> X :!=: 1 -> 'C_Ms(X) != 1 ->
            [/\ 'M('C(X)) = [set M], cyclic X & \tau2(M).-group X],
      (*d*) abelian <<\bigcup_(x \in Ms^#) 'C_U[x]>>
    & (*e*) U :!=: 1 -> exists U0,
            [/\ gval U0 \subset U, exponent (gval U0) = exponent U
             & [Frobenius Ms <*> U0 = Ms ><| U0]]].
Proof.
move=> M U K Ms maxM complU; have [hallU hallK _] := complU.
have [hallE defM _ regUK cUU] := kappa_compl_context maxM complU.
have [[_ E _ defE]] := sdprodP defM.
have [nsUE sKE mulUK nUK tiUK] := sdprod_context defE.
rewrite defE -{1 2}mulUK mulgA => defMl; case/mulGsubP=> nMsU nMsK tiMsE.
have [[sMsM nMsM] [sUE nUE]] := (andP (pcore_normal _ M : Ms <| M), andP nsUE).
rewrite norm_joinEr // mulUK in hallE.
have [[sEM s'M_E _] [sUM sk'U _]] := (and3P hallE, and3P hallU).
have defMsU: Ms ><| U = Ms <*> U.
  by apply: sdprodEY nMsU (trivgP _); rewrite -tiMsE -mulUK setIS ?mulG_subl.
have{defM} defM: Ms <*> U ><| K = M.
  rewrite sdprodE ?normsY  ?coprime_TIg //=; first by rewrite norm_joinEr.
  rewrite -(sdprod_card defMsU) coprime_mull andbC regular_norm_coprime //=.
  by rewrite (coprimegS sKE) ?(pnat_coprime (pcore_pgroup _ _)).
rewrite defMsU quotient_der //= -/Ms -{2}defMl -mulgA mulUK.
rewrite quotientMidl -quotient_der ?(subset_trans sEM) //.
rewrite quotient_abelian ?(der_mmax_compl_abelian maxM hallE) //.
set part_c := forall U, _; have c_holds: part_c.
  move=> X sXU ntX nregMsX; have sXE := subset_trans sXU sUE.
  have [x] := trivgPn _ nregMsX; case/setIP=> Ms_x cXx ntx.
  have Ms1x: x \in Ms^# by exact/setD1P.
  have piCx_hyp: {in X^#, forall x', x' \in ('C_M[x])^# /\ \sigma(M)^'.-elt x'}.
    move=> x'; case/setD1P=> ntx' Xx'; have Ex' := subsetP sXE x' Xx'.
    rewrite 3!inE ntx' (subsetP sEM) ?(mem_p_elt s'M_E) //=.
    by rewrite (subsetP _ _ Xx') ?sub_cent1.   
  have piCx := let: conj c e := piCx_hyp _ _ in pi_of_cent_sigma maxM Ms1x c e.
  have t2X: \tau2(M).-group X.
    apply/pgroupP=> p p_pr; case/Cauchy=> // x' Xx' ox'.
    have X1x': x' \in X^# by rewrite !inE Xx' -order_gt1 ox' prime_gt1.
    have [[]|[]] := piCx _ X1x'; last by rewrite /p_elt ox' pnatE.
    case/idPn; have:= mem_p_elt (pgroupS sXU sk'U) Xx'.
    by rewrite /p_elt ox' !pnatE //; case/norP. 
  suffices cycX: cyclic X.
    split=> //; have [x' defX] := cyclicP cycX.
    have X1x': x' \in X^# by rewrite !inE -cycle_eq1 -cycle_subG -defX ntX /=.
    have [[kX _]|[_ _]] := piCx _ X1x'; last by rewrite defX cent_cycle.
    rewrite -(setIid X) coprime_TIg ?eqxx // {2}defX in ntX.
    rewrite (pnat_coprime t2X (sub_pgroup _ kX)) // => p kp.
    by rewrite inE /= negb_and rank_kappa ?orbT.
  have [E2 hallE2 sXE2] := Hall_superset (sigma_compl_sol hallE) sXE t2X.
  rewrite abelian_rank1_cyclic; last first.
    exact: abelianS sXE2 (tau2_compl_abelian maxM hallE hallE2).
  have [p _ ->] := rank_witness X; rewrite leqNgt; apply: contra nregMsX => rpX.
  have t2p: p \in \tau2(M) by  rewrite (pnatPpi t2X) // -p_rank_gt0 ltnW.
  rewrite -(setIidPr (subset_trans sXE sEM)) in rpX.
  case/p_rank_geP: rpX => A; rewrite pnElemI -setIdE; case/setIdP=> Ep2A sAX.
  rewrite -subG1; have [_ _ <- _ _] := tau2_context maxM t2p Ep2A.
  by rewrite setIS ?centS.
have [K1 | ntK] := altP (K :=P: 1).
  rewrite {2}K1 cyclic1; rewrite K1 mulg1 in mulUK; rewrite -mulUK in hallE.
  have [x|[A0 [_ cA0A0 genA0] frobM]] := FTtypeF_complement maxM hallE.
    case/setD1P; rewrite -order_gt1 -pi_pdiv; set p := pdiv _ => pi_x_p Ux t13x.
    apply: contraNeq (pnatPpi (mem_p_elt sk'U Ux) pi_x_p) => nreg_x.
    apply/orP; right; unlock kappa; rewrite /= inE /= (pnatPpi t13x) //=.
    have sxM: <[x]> \subset M by rewrite cycle_subG (subsetP sUM).
    move: pi_x_p; rewrite -p_rank_gt0 /= -(setIidPr sxM); case/p_rank_geP=> P.
    rewrite pnElemI -setIdE; case/setIdP=> EpP sPx.
    apply/exists_inP; exists P; rewrite // (subG1_contra _ nreg_x) //=.
    by rewrite -cent_cycle setIS ?centS.
  by split => //; apply: abelianS cA0A0; rewrite gen_subG; exact/bigcupsP.
have PmaxM: M \in 'M_'P by rewrite inE maxM -(trivg_kappa maxM hallK) andbT.
have [L _ [_ _ _ [cycZ _ _ _ _] [_ _ _ defM']]] := Ptype_embedding PmaxM hallK.
have{cycZ cUU} [cycK cUU] := (cyclicS (joing_subl _ _) cycZ, cUU ntK).
split=> // [||ntU].
- split=> //; apply/eqP; rewrite eq_sym eqEcard -(leq_pmul2r (cardG_gt0 K)).
  have [nsMsU_M _ mulMsU _ _] := sdprod_context defM.
  rewrite  (sdprod_card defM) (sdprod_card defM') der1_min ?normal_norm //=.
  by rewrite -mulMsU quotientMidl cyclic_abelian ?quotient_cyclic.
- by apply: abelianS cUU; rewrite gen_subG -big_distrr subsetIl.
pose ntUsylow S := (S :!=: 1) && Sylow U S.
pose cyclicRegular Z := [&& Z \subset U, cyclic Z & 'C_Ms('Ohm_1(Z)) == 1].
pose sameExp Z S := exponent Z == exponent S.
suffices mkZ: forall S, {Z | ntUsylow S ==> sameExp Z S && cyclicRegular Z}.
  pose U0 := <<\bigcup_(S | ntUsylow S) sval (mkZ S)>>.
  have sU0U : U0 \subset U.
    rewrite gen_subG; apply/bigcupsP=> S sylS; case: (mkZ S) => Z /=.  
    by rewrite sylS; case/and3P.
  have nU0U: U \subset 'N(U0) := sub_abelian_norm cUU sU0U.
  have expU0U: exponent U0 = exponent U.
    apply/eqP; rewrite eqn_dvd exponentS //=.
    apply/dvdn_partP=> [|p _]; first exact: exponent_gt0.
    have [S sylS] := Sylow_exists p U; rewrite -(exponent_Hall sylS).
    have [-> | ntS] := eqsVneq S 1; first by rewrite exponent1 dvd1n.
    have ntU_S: ntUsylow S by rewrite /ntUsylow ntS (p_Sylow sylS).
    case defZ: (mkZ S) => [Z Zprops].
    have expZS: exponent Z == exponent S by case/andP: (implyP Zprops ntU_S). 
    by rewrite -(eqP expZS) exponentS ?sub_gen // (bigcup_max S) ?defZ.
  exists [group of U0]; split=> //.
  have ntU0: U0 != 1 by rewrite trivg_exponent expU0U -trivg_exponent.
  apply/Frobenius_semiregularP; rewrite ?Msigma_neq1 //.
    rewrite sdprodEY ?(subset_trans sU0U) //; apply/trivgP.
    by rewrite -tiMsE setIS ?(subset_trans sU0U).
  apply: semiregular_sym => x; case/setD1P=> ntx Ms_x; apply: contraNeq ntx.
  rewrite -rank_gt0; have [p p_pr ->] := rank_witness [group of 'C_U0[x]].
  rewrite -in_set1 -set1gE p_rank_gt0 => piCp.
  have [e Ce oe]: {e | e \in 'C_U0[x] & #[e] = p}.
    by move: piCp; rewrite mem_primes p_pr cardG_gt0; exact: Cauchy.
  have{Ce} [U0e cxe] := setIP Ce.
  have nte: e != 1 by rewrite -order_gt1 oe prime_gt1.
  have{piCp} piUp: p \in \pi(U).
    rewrite -pi_of_exponent -expU0U pi_of_exponent.
    by apply: piSg piCp; exact: subsetIl.
  have [S sylS] := Sylow_exists p U; have [sSU pS _] := and3P sylS.
  have ntS: S :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylS) p_rank_gt0.
  have ntU_S: ntUsylow S by rewrite /ntUsylow ntS (p_Sylow sylS).
  case defZ: (mkZ S) => [Z Zprops].
  have [eqexpZS sZU cycZ regZ1] := and4P (implyP Zprops ntU_S).
  suffices defZ1: 'Ohm_1(Z) == <[e]>.
    by rewrite -(eqP regZ1) (eqP defZ1) cent_cycle inE Ms_x cent1C.
  have pZ: p.-group Z by rewrite -pnat_exponent (eqnP eqexpZS) pnat_exponent.
  have sylZ: p.-Sylow(U0) Z.
    have:= sU0U; rewrite pHallE /U0 /= -bigprodGE (bigD1 S) //= defZ /=.
    rewrite joing_subl join_subG sZU /=; set U1 := (\prod_(Z | _) _)%G => sU1U.
    rewrite cent_joinEr ?(sub_abelian_cent2 cUU) //.
    suffices p'U1: p^'.-group U1.
      rewrite coprime_cardMg ?(pnat_coprime pZ) //.
      by rewrite partn_mul // part_pnat_id // part_p'nat // muln1.
    pose p'inU X := X \subset U -> p^'.-group X.
    apply: (@big_prop _ p'inU) => // [_|X Y IHX IHY|T]; first exact: pgroup1.
      rewrite /p'inU join_subG /=; case/andP=> sXE2 sYE2.
      by rewrite cent_joinEl ?(sub_abelian_cent2 cUU) // pgroupM IHX ?IHY.
    case/andP=> sylT neqTS; case: (mkZ T) => Y /=; rewrite sylT /=.
    case/andP; move/eqnP=> expYT _ _.
    rewrite -pnat_exponent expYT pnat_exponent.
    case/andP: sylT => _; case/SylowP=> q _ sylT.
    apply: (pi_pnat (pHall_pgroup sylT)); apply: contraNneq neqTS => eq_qp.
    have defOU := nilpotent_Hall_pcore (abelian_nil cUU).
    by rewrite -val_eqE /= (defOU _ _ sylS) (defOU _ _ sylT) eq_qp.
  have nZU0: Z <| U0.
    by rewrite -sub_abelian_normal ?(pHall_sub sylZ) ?(abelianS sU0U).
  have Ze: e \in Z by rewrite (mem_normal_Hall sylZ) // /p_elt oe pnat_id.
  rewrite (eq_subG_cyclic cycZ) ?Ohm_sub ?cycle_subG // -orderE oe.
  rewrite (Ohm1_cyclic_pgroup_prime _ pZ) //.
  by apply: contraNneq nte => Z1; rewrite Z1 inE in Ze.
move=> S; case sylS: (ntUsylow S); last by exists U.
apply: choice.sigW; case/andP: sylS => ntS; case/SylowP=> p p_pr sylS.
have [sSU pS _] := and3P sylS; have cSS := abelianS sSU cUU.
have piSp: p \in \pi(S) by rewrite -p_rank_gt0 -rank_pgroup ?rank_gt0.
have piUp := piSg sSU piSp; have [/= s'p k'p] := norP (pnatPpi sk'U piUp).
have: (p \in \tau13(M)) || (p \in \tau2(M)).
  by rewrite orbAC -orbA -(partition_pi_sigma_compl maxM hallE) (piSg sUE).
case/orP=> [t13p | t2p].
  exists S; rewrite /sameExp eqxx; have sSM := subset_trans sSU sUM.
  have cycS: cyclic S.
    move: t13p; rewrite inE /= -!andb_orr; case/and3P=> _; move/eqP=> rpM _.
    by rewrite abelian_rank1_cyclic // (rank_pgroup pS) -rpM p_rankS.
  rewrite andbA sSU cycS /=; apply: contraR k'p => nregS1; unlock kappa.
  rewrite /= inE /= t13p; apply/exists_inP; exists 'Ohm_1(S)%G => //.
  rewrite p1ElemE // 2!inE (subset_trans (Ohm_sub 1 S)) //=.
  by rewrite (Ohm1_cyclic_pgroup_prime cycS pS ntS).
have sylS_M := subHall_Sylow hallU (pnatPpi sk'U piUp) sylS.
have sSE := subset_trans sSU sUE.
have not_sNSM: ~~ ('N(S) \subset M).
  by apply: contra s'p => sNSM; apply/exists_inP; exists S.
have rpS: 'r_p(S) = 2.
  by apply/eqP; rewrite (p_rank_Sylow sylS_M); case/andP: t2p.
have [A]: exists A, A \in 'E_p^2(S) by apply/p_rank_geP; rewrite rpS.
rewrite -(setIidPr sSE) pnElemI -setIdE; case/setIdP=> Ep2A sAS.
have [_ [sCAE _ _] nregEp_uniq _] := tau2_compl_context maxM hallE t2p Ep2A.
have regNNS: forall Z (Z1 := 'Ohm_1(Z)),
  Z \subset S -> cyclic Z -> Z :!=: 1 -> 'N(S) \subset 'N(Z1) -> 'C_Ms(Z1) = 1.
- move=> Z Z1 sZS cycZ ntZ nZ1_NS; apply: contraNeq not_sNSM => nregZ1.
  have sZ1S: Z1 \subset S := subset_trans (Ohm_sub 1 Z) sZS.
  have EpZ1: [group of Z1] \in 'E_p^1(E).
    rewrite p1ElemE // !inE (subset_trans sZ1S) //=.
    by rewrite (Ohm1_cyclic_pgroup_prime _ (pgroupS sZS pS)).
  have [/= uCZ1] := nregEp_uniq _ EpZ1 nregZ1.
  apply: (subset_trans nZ1_NS); apply: (sub_uniq_mmax uCZ1 (cent_sub _)).
  by rewrite mFT_norm_proper ?(mFT_pgroup_proper (pgroupS sZ1S pS)) ?Ohm1_eq1.
have [bS defS typeS] := abelian_structure cSS.
move: (erefl (homocyclic S)); rewrite {2}/homocyclic cSS /=.
move: (abelian_type_gt1 S) (abelian_type_dvdn_sorted S).
move: (size_abelian_type cSS); rewrite -{}typeS size_map (rank_pgroup pS) rpS.
case: bS defS => [|x [|y []]] //=; rewrite big_cons big_seq1 !andbT => defS _.
rewrite !cardG_gt1 /=; case/andP=> ntX ntY leYX.
have expS: exponent S = #[x].
  rewrite -(dprod_exponent defS) !exponent_cycle.
  by apply/eqP; rewrite eqn_dvd dvdn_lcml dvdn_lcm dvdnn leYX.
have [Sx Sy]: <[x]> \subset S /\ <[y]> \subset S.
  by apply/andP; rewrite -mulG_subG; case/dprodP: defS => _ ->.
have [px py]: p.-elt x /\ p.-elt y by split; exact: pgroupS pS.
pose n := logn p #[x]; have p_gt1 := prime_gt1 p_pr.
have: #[y] <= #[x] by rewrite dvdn_leq.
rewrite leq_eqVlt; case: eqP => [eqYX _ | _ ltYX _]; last first.
  have defX1: 'Ohm_1(<[x]>) = 'Mho^n.-1(S).
    rewrite -(Mho_dprod _ defS) (Mho_p_cycle _ py).
    rewrite /order (card_pgroup px) (card_pgroup py) ltn_exp2l // -/n in ltYX.
    rewrite -{2}(subnKC ltYX) addSn expn_add -card_pgroup // expgn_mul.
    rewrite expg_order exp1gn cycle1 dprodg1.
    by rewrite (Ohm_p_cycle _ px) (Mho_p_cycle _ px) subn1.
  exists <[x]>%G; rewrite /sameExp expS exponent_cycle eqxx.
  rewrite /cyclicRegular (subset_trans Sx) //=.
  by rewrite regNNS ?cycle_cyclic //= defX1 char_norms ?Mho_char.
move/(Ohm1_homocyclicP pS cSS) => defS1.
have Ep2A_M := subsetP (pnElemS p 2 sEM) A Ep2A.
have [_ _ _ _ [A1 EpA1 regA1]] := tau2_context maxM t2p Ep2A_M.
have [sA1A _ oA1] := pnElemPcard EpA1.
have [zn defA1]: exists zn, A1 :=: <[zn]>.
  by apply/cyclicP; rewrite prime_cyclic ?oA1.
have S1zn: zn \in 'Ohm_1(S).
  rewrite (OhmE 1 pS) mem_gen // !inE -cycle_subG -defA1.
  by rewrite -oA1 (subset_trans sA1A) //= defA1 expg_order.
have [z Sz def_zn]: exists2 z, z \in S & zn = z ^+ (p ^ n.-1).
  by apply/imsetP; rewrite -(MhoEabelian _ pS cSS) /n -expS -defS1.
have oz: #[z] = #[x].
  rewrite defA1 def_zn in oA1; rewrite (orderXpfactor oA1) //.
  rewrite -expnSr prednK -?card_pgroup //.
  by rewrite -(ltn_exp2l _ _ p_gt1) -card_pgroup // cardG_gt1.
have defZ1: 'Ohm_1(<[z]>) = A1.
  by rewrite (Ohm_p_cycle _ (mem_p_elt pS Sz)) oz subn1 -def_zn -defA1.
exists <[z]>%G; rewrite /sameExp expS exponent_cycle oz eqxx.
by rewrite /cyclicRegular cycle_cyclic defZ1 regA1 cycle_subG (subsetP sSU) /=.
Qed.

(* This is B & G, Theorem 15.2. *)
(* It is this theorem that implies that the non-functorial definition of      *)
(* M`_\sigma used in B & G is equivalent to the original definition in FT     *)
(* (also used in Peterfalvi).                                                 *)
(*   Proof notes: this proof contained two non-structural arguments: taking D *)
(* to be K-invariant, and reusing the nilpotent Frobenius kernel argument for *)
(* Q1 (bottom of p. 118). We handled the first with a "without loss", but for *)
(* the second we had to spell out explicitly the assumptions and conclusions  *)
(* of the nilpotent kernel argument that were spread throughout the last      *)
(* paragraph p. 118.                                                          *)
(*  We also had to make a few additions to the argument at the top of p. 119  *)
(* while the statement of the Theorem states that F(M) = C_M(Qbar), the text  *)
(* only shows that F(M) = C_Msigma(Qbar), and we need to show that K acts     *)
(* regularly on Qbar to complete the proof; this follows from the values of   *)
(* orders of K,  Kstar and Qbar. In addition we need to show much earlier     *)
(* that K acts faithfully on Q, to show that C_M(Q) is included in Ms, and    *)
(* this requires a use of 14.2(e) not mentioned in the text; in addition, the *)
(* reference to coprime action (Proposition 1.5) on p. 119 l. 1 is somewhat   *)
(* somewhat misleading, since we actually need to use the coprime stabilizer  *)
(* Lemma 1.9 to show that C_D(Qbar) = C_D(Q) = 1 (unless we splice in the     *)
(* proof of that Lemma).                                                      *)
Theorem Fcore_structure : forall M (Ms := M`_\sigma),
  M \in 'M ->
    [/\ M`_\F != 1, M`_\F \subset Ms, Ms \subset M^`(1) & M^`(1) \proper M]
 /\ (forall K D : {group gT},
     \kappa(M).-Hall(M) K -> M`_\F != M`_\sigma ->
     let p := #|K| in let Ks := 'C_Ms(K) in
     let q := #|Ks| in let Q := 'O_q(M) in
     let Q0 := 'C_Q(D) in let Qbar := Q / Q0 in
     q^'.-Hall(M`_\sigma) D ->
    [/\ (*a*) [/\ M \in 'M_'P1, Ms ><| K = M & Ms = M ^`(1)],
        (*b*) [/\ prime p, prime q, q \in \pi(M`_\F) & q \in \beta(M)],
      [/\ (*c*) q.-Sylow(M) Q,
          (*d*) nilpotent D
        & (*e*) Q0 <| M],
        (*f*) [/\ minnormal Qbar (M / Q0), q.-abelem Qbar & #|Qbar| = (q ^ p)%N]
      & (*g*) [/\ Ms^`(1) = M^`(2),
                  M^`(2) \subset 'F(M),
                  [/\ Q <*> 'C_M(Q) = 'F(M),
                      'C_M(Qbar | 'Q) = 'F(M)
                    & 'C_Ms (Ks / Q0 | 'Q) = 'F(M)]
                & 'F(M) \proper Ms]]).
Proof.
move=> M Ms maxM; set M' := M^`(1); set M'' := M^`(2).
have nsMsM: Ms <| M := pcore_normal _ M; have [sMsM nMsM] := andP nsMsM.
have solM := mmax_sol maxM; have solMs: solvable Ms := solvableS sMsM solM.
have sMF_Ms: M`_\F \subset Ms := Fcore_sub_Msigma maxM.
have ltM'M: M' \proper M by rewrite (sol_der1_proper solM) ?mmax_neq1.
have sMsM': Ms \subset M' := Msigma_der1 maxM.
have [-> | ltMF_Ms] := eqVproper sMF_Ms; first by rewrite eqxx Msigma_neq1.
set KDpart := forall K D, _; suffices KD_holds: KDpart.
  do 2!split=> //;  have [K hallK] := Hall_exists \kappa(M) solM.
  pose q := #|'C_(M`_\sigma)(K)|; have [D hallD] := Hall_exists q^' solMs.
  have [_ [_ _ piMFq _] _ _ _] := KD_holds K D hallK (proper_neq ltMF_Ms) hallD.
  by rewrite -rank_gt0 (leq_trans _ (p_rank_le_rank q _)) ?p_rank_gt0.
move=> {KDpart} K D hallK neMF_Ms p Ks q Q /= hallD.
have not_nilMs: ~~ nilpotent Ms by rewrite (sameP (Fcore_eq_Msigma maxM) eqP).
have P1maxM: M \in 'M_'P1; last have [PmaxM _] := setIdP P1maxM.
  apply: contraR not_nilMs => notP1maxM; apply: notP1type_Msigma_nil.
  by rewrite orbC inE notP1maxM inE maxM andbT orNb.
have ntK: K :!=: 1 by rewrite inE maxM andbT -(trivg_kappa maxM hallK) in PmaxM.
have [defMs defM]: Ms = M' /\ Ms ><| K = M.
  have [U complU] := ex_kappa_compl maxM hallK.
  have U1: U :=: 1 by apply/eqP; rewrite (trivg_kappa_compl PmaxM complU).
  have [[defM _ _] [//| defM' _] _ _ _] := kappa_structure maxM complU.
  by rewrite U1 sdprodg1 in defM defM'.
have [_ mulMsK nMsK _] := sdprodP defM; rewrite /= -/Ms in mulMsK nMsK.
have [sKM kK _] := and3P hallK; have s'K := sub_pgroup (@kappa_sigma' _ _) kK.
have coMsK: coprime #|Ms| #|K| := pnat_coprime (pcore_pgroup _ _) s'K.
have q_pr: prime q.
  have [L _ [_ _ _ _ [_]]] := Ptype_embedding PmaxM hallK.
  by rewrite inE P1maxM => [[] []].
have hallMs: \sigma(M).-Hall(M) Ms := Msigma_Hall maxM.
have sMq: q \in \sigma(M).
  by rewrite -pnatE // -pgroupE (pgroupS (subsetIl _ _) (pcore_pgroup _ _)).
have{s'K kK} q'K: q^'.-group K := pi'_p'group s'K sMq.
have nsQM: Q <| M := pcore_normal q M; have [sQM nQM] := andP nsQM.
have qQ: q.-group Q := pcore_pgroup _ _.
have sQMs: Q \subset Ms by rewrite (sub_Hall_pcore hallMs) ?(pi_pgroup qQ).
have [K1 prK1 sK1K]: exists2 K1, prime #|gval K1| & K1 \subset K.
  have:= ntK; rewrite -rank_gt0; have [r r_pr ->] := rank_witness K.
  by case/p_rank_geP=> K1; case/pnElemPcard=> ? _ oK1; exists K1; rewrite ?oK1.
have coMsK1 := coprimegS sK1K coMsK; have coQK1 := coprimeSg sQMs coMsK1.
have prMsK: semiprime Ms K by have [[? _ []] ] := Ptype_structure PmaxM hallK.
have defCMsK1: 'C_Ms(K1) = Ks.
  by rewrite (cent_semiprime prMsK) // -cardG_gt1 prime_gt1.
have sK1M := subset_trans sK1K sKM; have nQK1 := subset_trans sK1M nQM.
have{sMsM'} sKsQ: Ks \subset Q.
  have defMsK: [~: Ms, K] = Ms by case/coprime_der1_sdprod: defM.
  have hallQ := nilpotent_pcore_Hall q (Fitting_nil M).
  rewrite -[Q]p_core_Fitting (sub_Hall_pcore hallQ) //; first exact: pnat_id.
  apply: prime_meetG => //; apply: contraNneq not_nilMs => tiKsFM.
  suffices <-: 'F(Ms) = Ms by exact: Fitting_nil.
  apply/eqP; rewrite eqEsubset Fitting_sub /= -{1}defMsK.
  rewrite (odd_sdprod_primact_commg_sub_Fitting defM) ?mFT_odd //.
  apply/trivgP; rewrite -tiKsFM setIAC setSI //= -/Ms subsetI Fitting_sub /=.
  by rewrite Fitting_max ?Fitting_nil // (char_normal_trans (Fitting_char _)).
have nilMs_Q: nilpotent (Ms / Q).
  have [nMsK1 tiQK1] := (subset_trans sK1K nMsK, coprime_TIg coQK1).
  have prK1b: prime #|K1 / Q| by rewrite -(card_isog (quotient_isog _ _)).
  have defMsK1: (Ms / Q) ><| (K1 / Q) = (Ms / Q) <*> (K1 / Q).
    by rewrite sdprodEY ?quotient_norms // coprime_TIg ?coprime_morph.
  apply: (prime_Frobenius_sol_kernel_nil defMsK1) => //.
    by rewrite (solvableS _ (quotient_sol _ solM)) ?join_subG ?quotientS.
  by rewrite -coprime_quotient_cent ?quotientS1 /= ?defCMsK1.
have defQ: 'O_q(Ms) = Q by rewrite -(setIidPl sQMs) pcore_setI_normal.
have sylQ: q.-Sylow(Ms) Q.
  have nsQMs: Q <| Ms by rewrite -defQ pcore_normal.
  rewrite -(pquotient_pHall qQ) // /= -/Q -{3}defQ.
  by rewrite -(pquotient_pcore _ qQ) ?nilpotent_pcore_Hall.
have{sMq hallMs} sylQ_M := subHall_Sylow hallMs sMq sylQ.
have sQ_MF: Q \subset M`_\F.
  by rewrite sub_gen ?(bigcup_max [group of Q]) ?(p_Sylow sylQ_M) ?pcore_normal.
have{sQ_MF} piMFq: q \in \pi(M`_\F).
  by rewrite (piSg sQ_MF) // (piSg sKsQ) // pi_of_prime ?inE /=.
without loss nDK: D hallD / K \subset 'N(D).
  have [E hallE nEK] := coprime_Hall_exists q^' nMsK coMsK solMs.
  have [x Ms_x ->] := Hall_trans solMs hallD hallE.
  set Q0 := 'C__(_)%G; rewrite (isog_nil (conj_isog _ _)) -['C_Q(_)]/(gval Q0).
  move/(_ E hallE nEK)=> IH; suffices ->: Q0 = [group of 'C_Q(E)] by [].
  apply: group_inj => /=; have Mx: x \in M := subsetP (pcore_sub _ _) x Ms_x.
  rewrite /= -/Q -{1}(normsP nQM x Mx) centJ -conjIg (normsP _ x Mx) //.
  by case: IH => _ _ [_ _]; case/andP.
set Q0 := 'C_Q(D); set Qb := Q / Q0.
have defQD: Q ><| D = Ms by rewrite -defQ in sylQ *; exact/sdprod_Hall_pcoreP.
have [_ mulQD nQD tiQD] := sdprodP defQD; rewrite /= -/Q -/Ms in mulQD nQD tiQD.
have nilD: nilpotent D.
  by rewrite (isog_nil (quotient_isog nQD tiQD)) /= -quotientMidl mulQD.
have [sDMs q'D _] := and3P hallD; have sDM := subset_trans sDMs sMsM.
have sDKM: D <*> K \subset M by rewrite join_subG sDM.
have q'DK: q^'.-group (D <*> K) by rewrite norm_joinEr // pgroupM q'D.
have{K1 sK1M sK1K coMsK1 coQK1 prK1 defCMsK1 nQK1 solMs} Qi_rec: forall Qi,
    Qi \in |/|_Q(D <*> K; q) -> Q0 \subset Qi -> Qi \proper Q ->
  exists L, [/\ L \in |/|_Q(D <*> K; q), Qi <| L, minnormal (L / Qi) (M / Qi)
               & ~~ ((Ks \subset L) ==> (Ks \subset Qi))].
- move=> Qi; case/setIdP; case/andP=> sQiQ qQi nQiDK sQ0i ltQiQ.
  have ltQiN := nilpotent_proper_norm (pgroup_nil qQ) ltQiQ.
  have [Lb minLb sLbQ]: {Lb | minnormal (gval Lb) (M / Qi) & Lb \subset Q / Qi}.
    apply: mingroup_exists; rewrite quotient_norms //= andbT -quotientInorm.
    by rewrite -subG1 quotient_sub1 ?subsetIr // proper_subn.
  have [ntLb nLbM] := andP (mingroupp minLb).
  have nsQiN: Qi <| 'N_M(Qi) by rewrite normal_subnorm (subset_trans sQiQ).
  have: Lb <| 'N_M(Qi) / Qi.
    by rewrite quotientInorm /normal (subset_trans sLbQ) ?quotientS.
  case/(inv_quotientN nsQiN) => L [defLb sQij] /=; case/andP.
  case/subsetIP=> sLM nQij nLN; exists L.
  have{sLbQ} sLQ: L \subset Q by rewrite -(quotientSGK nQij sQiQ) -defLb.
  rewrite inE /psubgroup /normal sLQ sQij nQij (pgroupS sLQ qQ) -defLb.
  have nLDK: D <*> K \subset 'N(L) by apply: subset_trans nLN; exact/subsetIP.
  have sLD_Ms: L <*> D \subset Ms by rewrite join_subG (subset_trans sLQ).
  have coLD_K1: coprime #|L <*> D| #|K1| := coprimeSg sLD_Ms coMsK1.
  have [[nQiD nQiK] [nLD nLK]] := (joing_subP nQiDK, joing_subP nLDK).
  have [nQiK1 nLK1] := (subset_trans sK1K nQiK, subset_trans sK1K nLK).
  split=> //; apply: contra ntLb => regLK.
  have [sLLD sDLD] := joing_subP (subxx (L <*> D)).
  suffices nilLDbar: nilpotent (L <*> D / Qi).
    rewrite defLb -subG1 -(quotientS1 sQ0i) /= -/Q.
    rewrite coprime_quotient_cent ?(pgroup_sol qQ) ?(pnat_coprime qQ) //=.
    rewrite subsetI quotientS //= (sub_nilpotent_cent2 nilLDbar) ?quotientS //.
    by rewrite coprime_morph ?(p'nat_coprime q'D (pgroupS sLQ qQ)).
  have defLK1b: (L <*> D / Qi) ><| (K1 / Qi) = (L <*> D / Qi) <*> (K1 / Qi).
    rewrite sdprodEY ?coprime_TIg ?quotient_norms //=.
      by rewrite (subset_trans sK1K) // normsY.
    by rewrite coprime_morph // (coprimeSg sLD_Ms).
  have [sQiLD sLD_M] := (subset_trans sQij sLLD, subset_trans sLD_Ms sMsM).
  have{regLK}: 'C_(L <*> D / Qi)(K1 / Qi) = 1.
    rewrite -coprime_quotient_cent ?(subset_trans sK1K) ?(solvableS sLD_M) //=.
    rewrite -(setIidPr sLD_Ms) setIAC defCMsK1 quotientS1 //= -/Ks joingC.
    rewrite norm_joinEl // -(setIidPl sKsQ) -setIA -group_modr // tiQD mul1g.
    have [-> | ntLKs] := eqVneq (Ks :&: L) 1; first exact: sub1G.
    by rewrite subIset ?(implyP regLK) // prime_meetG. 
  apply: (prime_Frobenius_sol_kernel_nil defLK1b).
    by apply: solvableS (quotient_sol _ solM); rewrite join_subG !quotientS.
  by rewrite -(card_isog (quotient_isog _ _)) ?coprime_TIg // (coprimeSg sQiQ).
have ltQ0Q: Q0 \proper Q.
  rewrite properEneq subsetIl andbT; apply: contraNneq not_nilMs => defQ0.
  rewrite -dprodEsdprod // in defQD; last by rewrite centsC -defQ0 subsetIr.
  by rewrite (dprod_nil defQD) (pgroup_nil qQ).
have [nQK coQK] := (subset_trans sKM nQM, pnat_coprime qQ q'K).
have solQ := pgroup_sol qQ. (* must come late: Coq diverges on solQ <> solMs *)
have [coDK coQD] := (coprimeSg sDMs coMsK, pnat_coprime qQ q'D).
have nQ0K: K \subset 'N(Q0) by rewrite normsI ?norms_cent.
have nQ0D: D \subset 'N(Q0) by rewrite cents_norm // centsC subsetIr.
have nQ0DK: D <*> K \subset 'N(Q0) by exact/joing_subP.
have [|Q1 [DKinvQ1 nsQ01 minQ1b nregQ1b]] := Qi_rec _ _ (subxx _) ltQ0Q.
  by rewrite inE /psubgroup (pgroupS _ qQ) ?subsetIl.
have{Qi_rec nregQ1b DKinvQ1} [tiQ0Ks defQ1]: Q0 :&: Ks = 1 /\ Q1 :=: Q.
  move: nregQ1b; rewrite negb_imply; case/andP=> sKsQ1 not_sKsQ0.
  split=> //; first by rewrite setIC prime_TIg.
  have [] := setIdP DKinvQ1; case/andP; case/eqVproper=> // ltQ1Q _ _.
  have [Q2 [_ _ _]] := Qi_rec Q1 DKinvQ1 (normal_sub nsQ01) ltQ1Q.
  by rewrite sKsQ1 implybT.
have [nsQ0Q minQb]: Q0 <| Q /\ minnormal Qb (M / Q0) by rewrite /Qb -defQ1.
have{Q1 defQ1 minQ1b nsQ01} abelQb: q.-abelem Qb.
  have qQb: q.-group Qb := quotient_pgroup _ qQ; have solQb := pgroup_sol qQb.
  by rewrite -is_abelem_pgroup // (minnormal_solvable_abelem minQb).
have [cQbQb [sQ0Q nQ0Q]] := (abelem_abelian abelQb, andP nsQ0Q).
have nQ0M: M \subset 'N(Q0) by rewrite -mulMsK -mulQD -mulgA !mul_subG.
have nsQ0M: Q0 <| M by rewrite /normal subIset ?sQM.
have sFM_QCQ: 'F(M) \subset Q <*> 'C_M(Q).
  have [_ /= mulQQ' cQQ' _] := dprodP (nilpotent_pcoreC q (Fitting_nil M)).
  rewrite -{3}mulQQ' p_core_Fitting cent_joinEr ?subsetIr //= -/Q in cQQ' *.
  by rewrite mulgS // subsetI (subset_trans (pcore_sub _ _) (Fitting_sub M)).
have sQCQ_CMsQb: Q <*> 'C_M(Q) \subset 'C_Ms(Qb | 'Q).
  rewrite join_subG !(subsetI _ Ms) sQMs /= !sub_astabQ nQ0Q /= -/Q0 -/Qb.
  rewrite -abelianE cQbQb quotient_cents ?subsetIr //= andbC subIset ?nQ0M //=.
  rewrite -(coprime_mulG_setI_norm mulMsK) ?norms_cent //= -/Ms.
  suffices ->: 'C_K(Q) = 1 by rewrite mulg1 subsetIl.
  have: ~~ (Q \subset Ks); last apply: contraNeq => ntCKQ.
    have [_ _ _ [_]] := Ptype_structure PmaxM hallK.
    by move/(_ q); rewrite pi_of_prime //; case/(_ (eqxx q) _ sylQ_M).
  rewrite -[Ks](cent_semiprime prMsK _ ntCKQ) ?subsetIl //.
  by rewrite subsetI sQMs centsC subsetIr.
have nCQb: M \subset 'N('C(Qb | 'Q)).
  by rewrite (subset_trans _ (astab_norm _ _)) ?actsQ.
have defFM: 'C_Ms(Qb | 'Q) = 'F(M).
  apply/eqP; rewrite eqEsubset andbC (subset_trans sFM_QCQ) //=.
  rewrite Fitting_max //=; first by rewrite /normal subIset ?sMsM //= normsI.
  rewrite -(coprime_mulG_setI_norm mulQD) ?(subset_trans sMsM) //= -/Q.
  rewrite mulg_nil ?(nilpotentS (subsetIl _ _)) ?(pgroup_nil qQ) //= -/Q.
  rewrite (centsS (subsetIl _ _)) //= -/Q.
  have cDQ0: 'C_D(Qb | 'Q) \subset 'C(Q0) by rewrite subIset // centsC subsetIr.
  rewrite (stable_factor_cent cDQ0) ?(coprimegS (subsetIl _ _) coQD) //.
  by rewrite /stable_factor commGC -sub_astabQR ?subsetIr // subIset ?nQ0D.
have{sFM_QCQ sQCQ_CMsQb} ->: Q <*> 'C_M(Q) = 'F(M).
  by apply/eqP; rewrite eqEsubset sFM_QCQ andbT -defFM.
have ltFM_Ms: 'F(M) \proper Ms.
  rewrite properEneq -{2}defFM subsetIl andbT.
  by apply: contraNneq not_nilMs => <-; exact: Fitting_nil.
have sQFM: Q \subset 'F(M) by rewrite -[Q]p_core_Fitting pcore_sub.
have not_cDQb: ~~ (D / Q0 \subset 'C(Qb)).
  apply: contra (proper_subn ltFM_Ms) => cDQb; rewrite -mulQD mulG_subG sQFM /=.
  by rewrite -defFM subsetI sDMs sub_astabQ nQ0D.
have [_ minQbP] := mingroupP minQb.
have regQbDb: 'C_Qb(D / Q0) = 1.
  apply: contraNeq not_cDQb => ntCQDb; rewrite centsC; apply/setIidPl.
  apply: minQbP (subsetIl _ _); rewrite ntCQDb /= -/Qb -(setIidPl cQbQb) -setIA.
  by rewrite -centM -quotientMl //= mulQD normsI ?norms_cent ?quotient_norms.
have tiQ0: forall R, q^'.-group R -> Q0 :&: R = 1.
  by move=> R; move/(pnat_coprime (pgroupS sQ0Q qQ)); exact: coprime_TIg.
have oKb: #|K / Q0| = p by rewrite -(card_isog (quotient_isog _ (tiQ0 _ _))).
have oKsb: #|Ks / Q0| = q.
  by rewrite -(card_isog (quotient_isog _ tiQ0Ks)) ?(subset_trans sKsQ).
have regDK: 'C_D(K) = 1.
  by rewrite -(setIidPl sDMs) -setIA setIC coprime_TIg ?(coprimeSg sKsQ).
have{tiQ0} frobDKb: [Frobenius D <*> K / Q0 = (D / Q0) ><| (K / Q0)].
  have ntDb: D / Q0 != 1 by apply: contraNneq not_cDQb => ->; exact: sub1G.
  have ntKb: K / Q0 != 1 by rewrite -(isog_eq1 (quotient_isog _ (tiQ0 _ _))).
  apply/Frobenius_semiregularP => // [|xb].
    by apply: quotient_coprime_sdprod; rewrite ?sdprodEY ?coprime_TIg.
  have [f [_ ker_f _ im_f]] := restrmP (coset_morphism Q0) nQ0DK.
  have{ker_f} inj_f: 'injm f by rewrite ker_f ker_coset setIC tiQ0.
  rewrite /= /quotient -!im_f ?joing_subl ?joing_subr //.
  rewrite 2!inE andbC; case/andP; case/morphimP => x DKx Kx ->{xb}.
  rewrite morph_injm_eq1 // -injm_subcent1 ?joing_subl // => ntx.
  rewrite -{3}(setIidPl sDMs) -setIA prMsK ?inE ?ntx //.
  by rewrite setICA regDK setIg1 morphim1.
have defKsb: 'C_Qb(K / Q0) = Ks / Q0.
  rewrite /Ks -mulQD coprime_cent_mulG // regDK mulg1.
  by rewrite coprime_quotient_cent ?subsetIl.
have{frobDKb regQbDb} [p_pr oQb cQbD']:
  [/\ prime p, #|Qb| = (q ^ p)%N & (D / Q0)^`(1) \subset 'C(Qb)].
- have ntQb: Qb != 1 by rewrite -subG1 quotient_sub1 ?proper_subn.
  have prQbK: semiprime Qb (K / Q0).
    move=> xb; rewrite 2!inE andbC; case/andP; case/morphimP=> x nQ0x Kx -> ntx.
    have{ntx} ntx: x != 1 by apply: contraNneq ntx => ->; rewrite morph1.
    transitivity ('C_Q[x] / Q0); last first.
      rewrite -(coprime_quotient_cent (subsetIl Q _) nQ0K coQK solQ) /= -/Q0.
      by rewrite -/Q -(setIidPl sQMs) -!setIA prMsK // !inE ntx.
    rewrite -!cent_cycle -quotient_cycle //; rewrite -!cycle_subG in Kx nQ0x.  
    by rewrite coprime_quotient_cent ?(coprimegS Kx).
  have:= Frobenius_primact frobDKb _ _ _ ntQb _ prQbK regQbDb.
  have [nQDK solDK] := (subset_trans sDKM nQM, solvableS sDKM solM).
  rewrite !quotient_sol ?quotient_norms // coprime_morph ?(pnat_coprime qQ) //=.
  rewrite -/Qb oKb defKsb prime_cyclic oKsb // subsetI der_sub /=.
  by case=> //= -> -> ->.
have{cQbD'} sM''FM: M'' \subset 'F(M).
  have nQMs := subset_trans sMsM nQM.
  rewrite [M'']dergSn -/M' -defMs -(quotientSGK _ sQFM) ?comm_subG //.
  rewrite (quotient_der 1) //= -/Ms -mulQD quotientMidl -quotient_der //= -/Q.
  by rewrite quotientS // -defFM subsetI sub_astabQ !comm_subG ?quotient_der. 
have sQ0Ms := subset_trans sQ0Q sQMs.
have ->: 'C_Ms(Ks / Q0 | 'Q) = 'F(M).
  have sFMcKsb: 'F(M) \subset 'C_Ms(Ks / Q0 | 'Q).
    by rewrite -defFM setIS ?astabS ?quotientS.
  have nCMsKsbM: M \subset 'N('C_Ms(Ks / Q0 | 'Q)).
    rewrite -{1}mulMsK mulG_subG sub_der1_norm ?subsetIl //= -/Ms; last first.
      by rewrite {1}defMs (subset_trans sM''FM sFMcKsb).
    rewrite normsI // (subset_trans _ (astab_norm _ _)) ?actsQ //.
    by rewrite cents_norm // centsC subsetIr.
  apply/eqP; rewrite eqEsubset sFMcKsb -defFM subsetI subsetIl.
  rewrite sub_astabQ /= -/Q0 subIset ?(subset_trans sMsM) //= andbT centsC.
  apply/setIidPl; apply: minQbP (subsetIl _ _).
  rewrite andbC normsI ?norms_cent ?quotient_norms //= -/Qb.
  have: Ks / Q0 != 1 by rewrite -cardG_gt1 oKsb prime_gt1.
  apply: subG1_contra; rewrite (quotientGI _ sQ0Ms) quotient_astabQ /= -/Q0.
  by rewrite subsetI quotientS // centsC subsetIr.
have ->: 'C_M(Qb | 'Q) = 'F(M).
  apply/eqP; rewrite eqEsubset -{2}defFM setSI //= andbT.
  rewrite -(coprime_mulG_setI_norm mulMsK) //= -defFM mulG_subG subxx /=.
  rewrite subsetI subsetIr -(quotientSGK _ sQ0Ms) 1?subIset ?nQ0K //= -/Q0.
  rewrite quotientIG; last by rewrite sub_astabQ normG trivg_quotient sub1G.
  rewrite quotient_astabQ /= -/Q0 prime_TIg ?sub1G ?oKb //.
  rewrite centsC -subsetIidl defKsb; apply: contra (@subset_leq_card _ _ _)  _.
  by rewrite -ltnNge oQb oKsb (ltn_exp2l 1) prime_gt1.
suffices ->: q \in \beta(M) by do 2!split=> //; last rewrite {1}defMs.
apply: contraR not_cDQb; rewrite negb_forall_in; case/exists_inP=> Q1 sylQ1.
rewrite negbK {Q1 sylQ1}(eq_Hall_pcore sylQ_M sylQ1) -/Q => nnQ.
have sD_DK': D \subset (D <*> K)^`(1).
  rewrite -{1}(coprime_cent_prod nDK) ?nilpotent_sol // regDK mulg1.
  by rewrite commgSS ?joing_subl ?joing_subr.
rewrite quotient_cents // (subset_trans sD_DK') //.
have nQDK := subset_trans sDKM nQM; have nCQDK := norms_cent nQDK.
rewrite der1_min // -(isog_abelian (second_isog nCQDK)) setIC /=.
rewrite -ker_conj_aut (isog_abelian (first_isog_loc _ _)) //=; set A := _ @* _.
have norm_q := normal_norm (pcore_normal q _).
rewrite {norm_q}(isog_abelian (quotient_isog (norm_q _ _) _)) /=; last first.
  by rewrite coprime_TIg ?coprime_morphr //= (pnat_coprime (pcore_pgroup q _)).
have AutA: A \subset [Aut Q] := Aut_conj_aut _ _.
have [|//] := Aut_narrow qQ (mFT_odd _) nnQ _ AutA (morphim_odd _ (mFT_odd _)).
exact: morphim_sol (solvableS sDKM solM).
Qed.

End Section15.


