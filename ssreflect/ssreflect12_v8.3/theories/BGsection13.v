(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection12.

(******************************************************************************)
(*   This file covers B & G, section 13; the title subject of the section,    *)
(* prime and regular actions, was defined in the frobenius.v file.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Section13.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q r : nat.
Implicit Types A E H K M Mstar N P Q R S T U V W X Y Z : {group gT}.

Section OneComplement.

Variables M E : {group gT}.
Hypotheses (maxM : M \in 'M) (hallE : \sigma(M)^'.-Hall(M) E).

Let sEM : E \subset M := pHall_sub hallE.
Let sM'E : \sigma(M)^'.-group E := pHall_pgroup hallE.

(* This is B & G, Lemma 13.1. *)
Lemma Msigma_setI_mmax_central : forall p H,
   H \in 'M -> p \in \pi(E) -> p \in \pi(H) -> p \notin \tau1(H) ->
   [~: M`_\sigma :&: H, M :&: H] != 1 -> gval H \notin M :^: G ->
 [/\ (*a*) forall P, P \subset M :&: H -> p.-group P ->
           P \subset 'C(M`_\sigma :&: H),
     (*b*) p \notin \tau2(H)
   & (*c*) p \in \tau1(M) -> p \in \beta(G)].
Proof.
move=> p H maxH piEp piHp t1H'p; set R := [~: _, _] => ntR notMGH.
have [q sMq piH'q]: exists2 q, q \in \sigma(M) & q \in \pi(H^`(1)).
  pose q := pdiv #|R|; have q_pr: prime q by rewrite pdiv_prime ?cardG_gt1.
  have q_dv : q %| _ := dvdn_trans (pdiv_dvd _) (cardSg _).
  exists q; last by rewrite mem_primes q_pr cardG_gt0 q_dv ?commgSS ?subsetIr.
  rewrite (pgroupP (pcore_pgroup _ M)) ?q_dv //.
  have sR_MsM: R \subset [~: M`_\sigma, M] by rewrite commgSS ?subsetIl.
  by rewrite (subset_trans sR_MsM) // commg_subl bgFunc_norm.
have [Y sylY] := Sylow_exists q H^`(1); have [sYH' qY _] := and3P sylY.
have nsHbH: H`_\beta <| H := pcore_normal _ _; have [_ nHbH] := andP nsHbH.
have sYH := subset_trans sYH' (der_sub 1 H); have nHbY := subset_trans sYH nHbH.
have nsHbY_H: H`_\beta <*> Y <| H.
  rewrite -{2}(quotientGK nsHbH) -quotientYK ?cosetpre_normal //.
  rewrite (char_normal_trans _ (der_normal 1 _)) //= -quotient_der //.
  rewrite (nilpotent_Hall_pcore _ (quotient_pHall nHbY sylY)) ?pcore_char //.
  exact: beta_der1_quo_nil.
have sYNY: Y \subset 'N_H(Y) by rewrite subsetI sYH normG.
have{nsHbY_H} defH: H`_\beta * 'N_H(Y) = H.
  rewrite -(mulSGid sYNY) mulgA -(norm_joinEr nHbY).
  rewrite (Frattini_arg _ (pHall_subl _ _ sylY)) ?joing_subr //.
  by rewrite join_subG Mbeta_der1.
have ntY: Y :!=: 1 by rewrite -cardG_gt1 (card_Hall sylY) p_part_gt1.
have{ntY} [_] := sigma_Jsub maxM (pi_pgroup qY sMq) ntY.
have maxY_H: H \in 'M(Y) by exact/setIdP.
move/(_ E p H hallE piEp _ maxY_H notMGH) => b'p_t3Hp.
case t2Hp: (p \in \tau2(H)).
  have b'p: p \notin \beta(G) by case/tau2_not_beta: t2Hp.
  have rpH: 'r_p(H) = 2 by apply/eqP; case/andP: t2Hp.
  have p'Hb: p^'.-group H`_\beta.
    rewrite (pi_p'group (pcore_pgroup _ H)) // inE /=.
    by rewrite -predI_sigma_beta // negb_and b'p orbT.
  case: b'p_t3Hp; rewrite // -(p_rank_p'quotient p'Hb) ?subIset ?nHbH //=.
  by rewrite -quotientMidl defH p_rank_p'quotient ?rpH.
have [S sylS] := Sylow_exists p H; have [sSH pS _] := and3P sylS.
have sSH': S \subset H^`(1).
  have [sHp | sH'p] := boolP (p \in \sigma(H)).
    apply: subset_trans (Msigma_der1 maxH).
    by rewrite (sub_Hall_pcore (Msigma_Hall _)) // (pi_pgroup pS).
  have sH'_S: \sigma(H)^'.-group S by rewrite (pi_pgroup pS).
  have [F hallF sSF] := Hall_superset (mmax_sol maxH) sSH sH'_S.
  have t3Hp: p \in \tau3(H).
    have:= partition_pi_sigma_compl maxH hallF p.
    by rewrite (pi_sigma_compl hallF) inE /= sH'p piHp (negPf t1H'p) t2Hp.
  have [[F1 hallF1] [F3 hallF3]] := ex_tau13_compl hallF.
  have [F2 _ complFi] := ex_tau2_compl hallF hallF1 hallF3.
  have [[sF3F' nsF3F] _ _ _ _] := sigma_compl_context maxH complFi.
  apply: subset_trans (subset_trans sF3F' (dergS 1 (pHall_sub hallF))). 
  by rewrite (sub_normal_Hall hallF3) ?(pi_pgroup pS).
have sylS_H' := pHall_subl sSH' (der_sub 1 H) sylS.
split=> // [P sPMH pP | t1Mp]; last first.
  apply/idPn=> b'p; have [_] := b'p_t3Hp b'p; move/(_ t1Mp); case/negP.
  have p'Hb: p^'.-group H`_\beta.
    rewrite (pi_p'group (pcore_pgroup _ H)) // inE /=.
    by rewrite -predI_sigma_beta // negb_and b'p orbT.
  rewrite -p_rank_gt0 -(p_rank_p'quotient p'Hb) ?comm_subG ?subIset ?nHbH //=.
  rewrite quotient_der ?subIset ?nHbH // -quotientMidl defH -quotient_der //=.
  rewrite p_rank_p'quotient ?comm_subG // -(rank_Sylow sylS_H').
  by rewrite (rank_Sylow sylS) p_rank_gt0.
have nsHaH: H`_\alpha <| H := pcore_normal _ _; have [_ nHaH] := andP nsHaH.
have [sPM sPH] := subsetIP sPMH; have nHaS := subset_trans sSH nHaH.
have nsHaS_H: H`_\alpha <*> S <| H.
  rewrite -{2}(quotientGK nsHaH) -quotientYK ?cosetpre_normal //.
  rewrite (char_normal_trans _ (der_normal 1 _)) //= -quotient_der //.
  rewrite (nilpotent_Hall_pcore _ (quotient_pHall nHaS sylS_H')) ?pcore_char //.
  exact: Malpha_quo_nil.
have [sHaS_H nHaS_H] := andP nsHaS_H.
have sP_HaS: P \subset H`_\alpha <*> S.
  have [x Hx sPSx] := Sylow_subJ sylS sPH pP; apply: subset_trans sPSx _.
  by rewrite sub_conjg (normsP nHaS_H) ?groupV ?joing_subr.
have coHaS_Ms: coprime #|H`_\alpha <*> S| #|M`_\sigma|.
  rewrite (p'nat_coprime _ (pcore_pgroup _ _)) // -pgroupE norm_joinEr //.
  rewrite pgroupM andbC (pi_pgroup pS) ?(pnatPpi (pHall_pgroup hallE)) //=.
  apply: sub_pgroup (pcore_pgroup _ _) => r aHr.
  have [|_ ti_aH_sM _] := sigma_disjoint maxH maxM; first by rewrite orbit_sym.
  by apply: contraFN (ti_aH_sM r) => sMr; exact/andP.
rewrite (sameP commG1P trivgP) -(coprime_TIg coHaS_Ms) commg_subI ?setIS //.
by rewrite subsetI sP_HaS (subset_trans sPM) ?bgFunc_norm.
Qed.

(* This is B & G, Corollary 13.2. *)
Corollary cent_norm_tau13_mmax : forall p P H,
    (p \in \tau1(M)) || (p \in \tau3(M)) ->
    P \subset M -> p.-group P -> H \in 'M('N(P)) ->
 [/\ (*a*) forall P1, P1 \subset M :&: H -> p.-group P1 ->
           P1 \subset 'C(M`_\sigma :&: H),
     (*b*) forall X, X \subset E :&: H -> \tau1(H)^'.-group X ->
           X \subset 'C(M`_\sigma :&: H)
   & (*c*) [~: M`_\sigma :&: H, M :&: H] != 1 ->
           p \in \sigma(H) /\ (p \in \tau1(M) -> p \in \beta(H))].
Proof.
move=> p P H t13Mp sPM pP; case/setIdP=> maxH sNP_H.
have ntP: P :!=: 1.
  by apply: contraTneq sNP_H => ->; rewrite norm1 proper_subn ?mmax_proper.
have st2Hp: (p \in \sigma(H)) || (p \in \tau2(H)).
  exact: (prime_class_mmax_norm maxH pP sNP_H).
have not_MGH: gval H \notin M :^: G.
  apply: contraL st2Hp; case/imsetP=> x _ ->; rewrite sigmaJ tau2J negb_or.
  by have:= t13Mp; rewrite -2!andb_orr !inE; case/and3P=> ->; move/eqP->.
set R := [~: _, _]; have [| ntR] := altP (R =P 1).
  move/commG1P; rewrite centsC => cMH_MsH.
  split=> // X sX_EH _; rewrite (subset_trans _ cMH_MsH) //.
  by rewrite (subset_trans sX_EH) ?setSI.
have piEp: p \in \pi(E).
  by rewrite (partition_pi_sigma_compl maxM) // orbCA t13Mp orbT.
have piHp: p \in \pi(H).
  by rewrite (partition_pi_mmax maxH) orbCA orbC -!orbA st2Hp !orbT.
have t1H'p: p \notin \tau1(H).
  by apply: contraL st2Hp; rewrite negb_or !inE; case/and3P=> ->; move/eqP->.
case: (Msigma_setI_mmax_central maxH piEp) => // cMsH t2H'p b_p.
split=> // [X sX_EH t1'X | _].
  have [sXE sXH] := subsetIP sX_EH.
  rewrite -(Sylow_gen X) gen_subG; apply/bigcupsP=> Q; case/SylowP=> q _ sylQ.
  have [-> | ntQ] := eqsVneq Q 1; first exact: sub1G.
  have piXq: q \in \pi(X) by rewrite -p_rank_gt0 -(rank_Sylow sylQ) rank_gt0.
  have [[piEq piHq] t1H'q] := (piSg sXE piXq, piSg sXH piXq, pnatPpi t1'X piXq).
  have [sQX qQ _] := and3P sylQ; have sXM := subset_trans sXE sEM.
  case: (Msigma_setI_mmax_central maxH piEq) => // -> //.
  by rewrite subsetI !(subset_trans sQX).
rewrite (negPf t2H'p) orbF in st2Hp.
by rewrite -predI_sigma_beta // {3}/in_mem /= st2Hp.
Qed.

(* This is B & G, Corollary 13.3(a). *)
Lemma cyclic_primact_Msigma : forall p P,
  p.-Sylow(E) P -> cyclic P -> semiprime P M`_\sigma.
Proof.
move=> p P sylP cycP x; have [sPE pP _] := and3P sylP.
case/setD1P; rewrite -cycle_subG -cycle_eq1 -cent_cycle => ntX sXP.
have sPM := subset_trans sPE sEM; have sXM := subset_trans sXP sPM.
have pX := pgroupS sXP pP; have ltXG := mFT_pgroup_proper pX.
have t13p: (p \in \tau1(M)) || (p \in \tau3(M)).
  rewrite (tau1E maxM hallE) (tau3E maxM hallE) -p_rank_gt0 -(rank_Sylow sylP).
  rewrite eqn_leq rank_gt0 (subG1_contra sXP) //= andbT -andb_orl orNb.
  by rewrite -abelian_rank1_cyclic ?cyclic_abelian.
have [H maxNH] := mmax_exists (mFT_norm_proper ntX ltXG).
have [cMsX _ _] := cent_norm_tau13_mmax t13p sXM pX maxNH.
have [_ sNH] := setIdP maxNH.
apply/eqP; rewrite eqEsubset andbC setIS ?centS // subsetI subsetIl /= centsC.
apply: subset_trans (cMsX P _ pP) (centS _).
  rewrite subsetI sPM (subset_trans (cents_norm _) sNH) //.
  by rewrite sub_abelian_cent // cyclic_abelian.
by rewrite setIS // (subset_trans (cent_sub _) sNH).
Qed.

(* This is B & G, Corollary 13.3(b). *)
Corollary tau3_primact_Msigma : forall E3,
  \tau3(M).-Hall(E) E3 -> semiprime E3 M`_\sigma.
Proof.
move=> E3 hallE3 x; have [sE3E t3E3 _] := and3P hallE3.
have [[E1 hallE1] _] := ex_tau13_compl hallE.
have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [[sE3E' nsE3E] _ [_ cycE3] _ _] := sigma_compl_context maxM complEi.
case/setD1P; rewrite -cycle_subG -cycle_eq1 -cent_cycle => ntX sXE3.
apply/eqP; rewrite eqEsubset andbC setIS ?centS // subsetI subsetIl /= centsC.
pose p := pdiv #[x]; have p_pr: prime p by rewrite pdiv_prime ?cardG_gt1.
have t3p: p \in \tau3(M) by rewrite (pgroupP (pgroupS sXE3 t3E3)) ?pdiv_dvd.
have t13p: [|| p \in \tau1(M) | p \in \tau3(M)] by rewrite t3p orbT.
have [y Xy oy]:= Cauchy p_pr (pdiv_dvd _).
have ntY: <[y]> != 1 by rewrite -cardG_gt1 -orderE oy prime_gt1.
have pY: p.-group <[y]> by rewrite /pgroup -orderE oy pnat_id.
have [H maxNH] := mmax_exists (mFT_norm_proper ntY (mFT_pgroup_proper pY)).
have sYE3: <[y]> \subset E3 by rewrite cycle_subG (subsetP sXE3).
have sYE := subset_trans sYE3 sE3E; have sYM := subset_trans sYE sEM.
have [_ cMsY _] := cent_norm_tau13_mmax t13p sYM pY maxNH.
have [_ sNH] := setIdP maxNH.
have sE3H': E3 \subset H^`(1).
  rewrite (subset_trans sE3E') ?dergS // (subset_trans _ sNH) ?normal_norm //.
  by rewrite (char_normal_trans _ nsE3E) // sub_cyclic_char.
apply: subset_trans (cMsY E3 _ _) (centS _).
- rewrite subsetI sE3E (subset_trans (cents_norm _) sNH) //.
  by rewrite sub_abelian_cent ?cyclic_abelian.
- rewrite (pgroupS sE3H') //; apply/pgroupP=> q _ q_dv_H'.
  by rewrite !inE q_dv_H' !andbF.
by rewrite setIS // (subset_trans _ sNH) // cents_norm ?centS ?cycle_subG.
Qed.

(* This is B & G, Theorem 3.4. *)
Theorem cent_tau1Elem_Msigma : forall p r P R (Ms := M`_\sigma),
    p \in \tau1(M) -> P \in 'E_p^1(E) -> R \in 'E_r^1('C_E(P)) ->
  'C_Ms(P) \subset 'C_Ms(R).
Proof.
set Ms := M`_\sigma; have [sMsM nMsM] := andP (pcore_normal _ M : Ms <| M).
have coMsE: coprime #|Ms| #|E| := coprime_sigma_compl hallE.
pose Ma := M`_\alpha; have sMaMs: Ma \subset Ms := Malpha_sub_Msigma maxM.
move=> p r P R /= t1Mp EpP; rewrite pnElemI -setIdE; case/setIdP=> ErR cPR.
without loss symPR: p r P R EpP ErR cPR t1Mp /
  r \in \tau1(M) -> 'C_Ma(P) \subset 'C_Ma(R) -> 'C_Ma(P) = 'C_Ma(R).
- move=> IH; apply: (IH p r) => // t1Mr sCaPR; apply/eqP; rewrite eqEsubset.
  rewrite sCaPR -(setIidPl sMaMs) -!setIA setIS ?(IH r p) 1?centsC // => _.
  by case/eqVproper; rewrite // /proper sCaPR andbF.
do [rewrite !subsetI !subsetIl /=; set cRCaP := _ \subset _] in symPR *.
pose Mz := 'O_(if cRCaP then \sigma(M) else \alpha(M))(M); pose C := 'C_Mz(P). 
suffices: C \subset 'C(R) by rewrite /C /Mz /cRCaP; case: ifP => // ->.
have sMzMs: Mz \subset Ms by rewrite /Mz; case: ifP => // _.
have sCMs: C \subset Ms by rewrite subIset ?sMzMs.
have [[sPE abelP dimP] [sRE abelR dimR]] := (pnElemP EpP, pnElemP ErR).
have [sPM sRM] := (subset_trans sPE sEM, subset_trans sRE sEM).
have [[pP cPP _] [rR _]] := (and3P abelP, andP abelR).
have coCR: coprime #|C| #|R| := coprimeSg sCMs (coprimegS sRE coMsE).
have ntP: P :!=: 1 by exact: nt_pnElem EpP _.
pose ST := [set S | Sylow C (gval S) && (R \subset 'N(S))].
have sST_CP: forall S, S \in ST -> S \subset C.
  by move=> S; case/setIdP; case/SylowP=> q _; case/andP.
rewrite -{sST_CP}[C](Sylow_transversal_gen sST_CP)  => [|q _]; last first.
  have nMzR: R \subset 'N(Mz) by rewrite (subset_trans sRM) // bgFunc_norm.
  have{nMzR} nCR: R \subset 'N(C) by rewrite normsI // norms_cent // cents_norm.
  have solC := solvableS (subset_trans sCMs sMsM) (mmax_sol maxM).
  have [S sylS nSR] := coprime_Hall_exists q nCR coCR solC.
  by exists S; rewrite // inE (p_Sylow sylS) nSR.
rewrite gen_subG; apply/bigcupsP=> S; case/setIdP {ST}.
case/SylowP=> q _ sylS nSR; have [sSC qS _] := and3P sylS.
have [sSMs [sSMz cPS]] := (subset_trans sSC sCMs, subsetIP sSC).
rewrite (sameP commG1P eqP) /=; set Q := [~: S, R]; apply/idPn => ntQ.
have sQS: Q \subset S by [rewrite commg_subl]; have qQ := pgroupS sQS qS.
have piQq: q \in \pi(Q) by rewrite -p_rank_gt0 -(rank_pgroup qQ) rank_gt0.
have{piQq} [nQR piSq] := (commg_normr R S : R \subset 'N(Q), piSg sQS piQq).
have [H maxNH] := mmax_exists (mFT_norm_proper ntP (mFT_pgroup_proper pP)).
have [maxH sNH] := setIdP maxNH; have sCPH := subset_trans (cent_sub _) sNH.
have [sPH sRH] := (subset_trans cPP sCPH, subset_trans cPR sCPH).
have [sSM sSH] := (subset_trans sSMs sMsM, subset_trans cPS sCPH).
have [sQM sQH] := (subset_trans sQS sSM, subset_trans sQS sSH).
have ntMsH_R: [~: Ms :&: H, R] != 1.
  by rewrite (subG1_contra _ ntQ) ?commSg // subsetI sSMs. 
have sR_EH: R \subset E :&: H by exact/subsetIP.
have ntMsH_MH: [~: Ms :&: H, M :&: H] != 1.
  by rewrite (subG1_contra _ ntMsH_R) ?commgS // (subset_trans sR_EH) ?setSI.
have t13Mp: p \in [predU \tau1(M) & \tau3(M)] by apply/orP; left.
have [_ cMsH_t1H' [//|sHp bHp]] := cent_norm_tau13_mmax t13Mp sPM pP maxNH.
have{cMsH_t1H'} t1Hr: r \in \tau1(H).
  apply: contraR ntMsH_R => t1H'r; rewrite (sameP eqP commG1P) centsC.
  by rewrite cMsH_t1H' // (pi_pgroup rR).
have ntCHaRQ: 'C_(H`_\alpha)(R <*> Q) != 1.
  rewrite centY (subG1_contra _ ntP) ?subsetI //= centsC cPR centsC.
  rewrite (subset_trans sQS cPS) (subset_trans _ (Mbeta_sub_Malpha H)) //.
  by rewrite (sub_Hall_pcore (Mbeta_Hall maxH)) // (pi_pgroup pP) ?bHp.
have not_MGH: gval H \notin M :^: G.
  by apply: contraL sHp; case/imsetP=> x _ ->; rewrite sigmaJ; case/andP: t1Mp.
have neqHM: H :!=: M := contra_orbit _ _ not_MGH.
have cSS: abelian S.
  apply: contraR neqHM; move/(nonabelian_Uniqueness qS) => uniqS.
  by rewrite (eq_uniq_mmax (def_uniq_mmax uniqS maxM sSM) maxH sSH).
have tiQcR: 'C_Q(R) = 1 by rewrite coprime_abel_cent_TI // (coprimeSg sSC).
have sMq: q \in \sigma(M) := pnatPpi (pcore_pgroup _ M) (piSg sSMs piSq).
have aH'q: q \notin \alpha(H).
  have [|_ tiHaMs _] := sigma_disjoint maxH maxM; first by rewrite orbit_sym.
  by apply: contraFN (tiHaMs q) => aHq; exact/andP.
have piRr: r \in \pi(R) by rewrite -p_rank_gt0 p_rank_abelem ?dimR.
have ErH_R: R \in 'E_r^1(H) by rewrite !inE sRH abelR dimR.
have{piRr} sM'r: r \in \sigma(M)^' := pnatPpi (pgroupS sRE sM'E) piRr.
have r'q: q \in r^' by apply: contraTneq sMq => ->.
have ntHa: H`_\alpha != 1 by rewrite (subG1_contra _ ntCHaRQ) ?subsetIl.
have uniqNQ: 'M('N(Q)) = [set H].
  apply: contraNeq ntCHaRQ; rewrite joingC.
  by case/(cent_Malpha_reg_tau1 _ _ r'q ErH_R) => //; case=> //= _ -> _.
have maxNQ_H: H \in 'M('N(Q)) :\ M by rewrite uniqNQ !inE neqHM /=. 
have{maxNQ_H} [_ _] := sigma_subgroup_embedding maxM sMq sQM qQ ntQ maxNQ_H.
have [sHq [_ st1HM [_ ntMa]] | _ [_ _ sM'MH]] := ifP; last first.
  have piPp: p \in \pi(P) by rewrite -p_rank_gt0 p_rank_abelem ?dimP.
  have sPMH: P \subset M :&: H by exact/subsetIP.
  by case/negP: (pnatPpi (pgroupS sPMH (pHall_pgroup sM'MH)) piPp).
have{st1HM} t1Mr: r \in \tau1(M).
  by case/orP: (st1HM r t1Hr); rewrite //= (contraNF ((alpha_sub_sigma _) r)).
have aM'q: q \notin \alpha(M).
  have [_ tiMaHs _] := sigma_disjoint maxM maxH not_MGH.
  by apply: contraFN (tiMaHs q) => aMq; exact/andP.
have ErM_R: R \in 'E_r^1(M) by rewrite !inE sRM abelR dimR.
have: 'M('N(Q)) != [set M] by rewrite uniqNQ (inj_eq (@set1_inj _)).
case/(cent_Malpha_reg_tau1 _ _ r'q ErM_R) => //.
case=> //= ntCMaP tiCMaPQ _; case/negP: ntCMaP.
rewrite -subG1 -{}tiCMaPQ centY setICA subsetIidr /= -/Ma -/Q centsC.
apply/commG1P; apply: three_subgroup; apply/commG1P.
  by rewrite commGC (commG1P _) ?sub1G ?subsetIr.
apply: subset_trans (subsetIr Ma _); rewrite /= -symPR //.
  rewrite commg_subl normsI //; last by rewrite norms_cent // cents_norm.
  by rewrite (subset_trans sSM) ?bgFunc_norm.
apply: contraR aM'q => not_cRCaP; apply: pnatPpi (pgroupS sSMz _) piSq.
by rewrite (negPf not_cRCaP) pcore_pgroup.
Qed.

(* This is B & G, Theorem 3.5. *)
Theorem tau1_primact_Msigma : forall E1,
  \tau1(M).-Hall(E) E1 -> semiprime E1 M`_\sigma.
Proof.
move=> E1 hallE1; have [sE1E t1E1 _] := and3P hallE1.
have [_ [E3 hallE3]] := ex_tau13_compl hallE.
have{hallE3} [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [_ _ [cycE1 _] _ _ {E2 E3 complEi}] := sigma_compl_context maxM complEi.
move=> x; case/setD1P; rewrite -cycle_subG -cent_cycle -cycle_eq1 => ntX sXE1.
apply/eqP; rewrite eqEsubset andbC setIS ?centS //= subsetI subsetIl /=.
have [p _ rX] := rank_witness <[x]>; rewrite -rank_gt0 {}rX in ntX.
have t1p: p \in \tau1(M) by rewrite (pnatPpi t1E1) // (piSg sXE1) -?p_rank_gt0.
have{ntX} [P EpP] := p_rank_geP ntX; have{EpP} [sPX abelP dimP] := pnElemP EpP.
have{sXE1} sPE1 := subset_trans sPX sXE1.
have{dimP} EpP: P \in 'E_p^1(E) by rewrite !inE abelP dimP (subset_trans sPE1).
apply: {x sPX abelP} subset_trans (setIS _ (centS sPX)) _; rewrite centsC.
rewrite -(Sylow_gen E1) gen_subG; apply/bigcupsP=> S; case/SylowP=> r _ sylS.
have [[sSE1 rS _] [-> | ntS]] := (and3P sylS, eqsVneq S 1); first exact: sub1G.
have [cycS sSE] := (cyclicS sSE1 cycE1, subset_trans sSE1 sE1E).
have [R ErR]: exists R, R \in 'E_r^1(S).
  by apply/p_rank_geP; rewrite -rank_pgroup ?rank_gt0.
have{ErR} [sRS abelR dimR] := pnElemP ErR; have sRE1 := subset_trans sRS sSE1.
have{abelR dimR} ErR: R \in 'E_r^1('C_E(P)).
  rewrite !inE abelR dimR (subset_trans sRE1) // subsetI sE1E.
  by rewrite sub_abelian_cent ?cyclic_abelian.
rewrite centsC (subset_trans (cent_tau1Elem_Msigma t1p EpP ErR)) //.
have [y defR]: exists y, R :=: <[y]> by apply/cyclicP; exact: cyclicS cycS.
have sylS_E: r.-Sylow(E) S.
  apply: subHall_Sylow hallE1 (pnatPpi t1E1 _) (sylS).
  by rewrite -p_rank_gt0 -(rank_Sylow sylS) rank_gt0.
rewrite defR cent_cycle (cyclic_primact_Msigma sylS_E cycS) ?subsetIr //.
by rewrite !inE -cycle_subG -cycle_eq1 -defR (nt_pnElem ErR).
Qed.

Lemma cent_semiprime : forall (rT : finGroupType) (H K X : {group rT}),
   semiprime H K -> X \subset H -> X :!=: 1 -> 'C_K(X) = 'C_K(H).
Proof.
move=> rT H K X prKH sXH; case/trivgPn=> x Xx ntx; apply/eqP.
rewrite eqEsubset -{1}(prKH x) ?inE ?(subsetP sXH) ?ntx //=.
by rewrite -cent_cycle !setIS ?centS ?cycle_subG.
Qed.

(* This is B & G, Lemma 13.6. *)
Lemma cent_cent_Msigma_tau1_uniq : forall E1 P q X (Ms := M`_\sigma),
    \tau1(M).-Hall(E) E1 -> P \subset E1 -> P :!=: 1 ->
     X \in 'E_q^1('C_Ms(P)) ->
 'M('C(X)) = [set M] /\ (forall S, q.-Sylow(Ms) S -> 'M(S) = [set M]).
Proof.
move=> E1 P q X Ms hallE1 sPE1 ntP EqX; have [sE1E t1E1 _] := and3P hallE1.
rewrite (cent_semiprime (tau1_primact_Msigma hallE1)) //= -/Ms in EqX.
have{P ntP sPE1} ntE1 := subG1_contra sPE1 ntP.
have [sMsM nMsM] := andP (pcore_normal _ M : Ms <| M).
have coMsE: coprime #|Ms| #|E| := coprime_sigma_compl hallE.
have [solMs nMsE] := (solvableS sMsM (mmax_sol maxM), subset_trans sEM nMsM).
apply: cent_der_sigma_uniq => //.
  by move: EqX; rewrite -(setIidPr sMsM) -setIA pnElemI; case/setIP.
have{EqX} [[sXcMsE1 abelX _] ntX] := (pnElemP EqX, nt_pnElem EqX isT).
apply: contraR ntX; case/norP=> b'q not_sXMs'; rewrite -subG1.
have [S sylS nSE] := coprime_Hall_exists q nMsE coMsE solMs.
have{abelX} [[sSMs qS _] [qX _]] := (and3P sylS, andP abelX).
have sScMsE': S \subset 'C_Ms(E^`(1)).
  have [H hallH cHE'] := der_compl_cent_beta' maxM hallE.
  have [Q sylQ] := Sylow_exists q H; have [sQH qQ _] := and3P sylQ.
  have{cHE' sQH} cQE' := centsS sQH cHE'; have sE'E := der_sub 1 E.
  have [nMsE' coMsE'] := (coprimegS sE'E coMsE, subset_trans sE'E nMsE).
  have{H hallH sylQ} sylQ := subHall_Sylow hallH b'q sylQ.
  have nSE' := subset_trans sE'E nSE; have nQE' := cents_norm cQE'.
  have [x cE'x ->] := coprime_Hall_trans coMsE' nMsE' solMs sylS nSE' sylQ nQE'.
  by rewrite conj_subG // subsetI (pHall_sub sylQ) centsC.
without loss{qX} sXS: X sXcMsE1 not_sXMs' / X \subset S.
  have [nMsE1 coMsE1 IH] := (subset_trans sE1E nMsE, coprimegS sE1E coMsE).
  have [nSE1 [sXMs cE1X]] := (subset_trans sE1E nSE, subsetIP sXcMsE1).
  have [|Q [sylQ nQE1 sXQ]] := coprime_Hall_subset nMsE1 coMsE1 solMs sXMs qX.
    by rewrite cents_norm // centsC.
  have [//|x cE1x defS] := coprime_Hall_trans nMsE1 _ solMs sylS nSE1 sylQ nQE1.
  have Ms_x: x \in Ms by case/setIP: cE1x.
  rewrite -(conjs1g x^-1) -sub_conjg IH //; last by rewrite defS conjSg.
    by rewrite -(conjGid cE1x) conjSg.
  by rewrite -(normsP (der_norm 1 _) x) ?conjSg.
have [sXMs cE1X] := subsetIP sXcMsE1.
have [_ [E3 hallE3]] := ex_tau13_compl hallE.
have{hallE3} [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have{not_sXMs' E3 complEi} ntE2: E2 :!=: 1.
  apply: contraNneq not_sXMs' => E2_1.
  have [[sE3E' _] _ _ [defE _] _] := sigma_compl_context maxM complEi.
  have [sCMsE_Ms' _ _] := sigma_compl_embedding maxM hallE.
  have{defE} [_ defE _ _] := sdprodP defE; rewrite E2_1 sdprod1g in defE.
  rewrite (subset_trans _ sCMsE_Ms') // -defE centM setIA subsetI.
  by rewrite (subset_trans (subset_trans sXS sScMsE')) ?setIS ?centS.
have{ntE2 E2 hallE2} [p p_pr t2p]: exists2 p, prime p & p \in \tau2(M).
  have [[p p_pr rE2] [_ t2E2 _]] := (rank_witness E2, and3P hallE2).
  by exists p; rewrite ?(pnatPpi t2E2) // -p_rank_gt0 -rE2 rank_gt0.
have [A Ep2A Ep2A_M] := ex_tau2Elem hallE t2p.
have [_ _ tiCMsA _ _] := tau2_context maxM t2p Ep2A_M.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2p Ep2A.
have [sAE abelA _] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have cCAE1_X: X \subset 'C('C_A(E1)).
  rewrite centsC; apply/subsetP=> y; case/setIP=> Ay cE1y.
  have [-> | nty] := eqVneq y 1; first exact: group1.
  have oY: #[y] = p := abelem_order_p abelA Ay nty.
  have [r _ rE1] := rank_witness E1.
  have{rE1} rE1: 'r_r(E1) > 0 by rewrite -rE1 rank_gt0.
  have [R ErR] := p_rank_geP rE1; have{ErR} [sRE1 abelR dimR] := pnElemP ErR.
  have t1r: r \in \tau1(M) by rewrite (pnatPpi t1E1) -?p_rank_gt0.
  have ErR: R \in 'E_r^1(E) by rewrite !inE abelR dimR (subset_trans sRE1).
  have EpY: <[y]>%G \in 'E_p^1('C_E(R)).
    rewrite p1ElemE // !inE -oY eqxx subsetI (centsS sRE1) cycle_subG //=.
    by rewrite (subsetP sAE).
  rewrite -sub_cent1 -cent_cycle (subset_trans sXcMsE1) //.
  apply: subset_trans (setIS _ (centS sRE1)) _.
  rewrite -subsetIidl setIAC subsetI subsetIr andbT.
  exact: cent_tau1Elem_Msigma t1r ErR EpY.
have nAE1 := subset_trans sE1E (normal_norm nsAE).
have coAE1: coprime #|A| #|E1|.
  by apply: pnat_coprime pA (pi_p'group t1E1 (contraL _ t2p)); exact: tau2'1.
rewrite -tiCMsA -(coprime_cent_prod nAE1 coAE1) ?abelian_sol // centM setIA.
rewrite subsetI cCAE1_X (subset_trans (subset_trans sXS sScMsE')) ?setIS //.
by rewrite centS ?commgSS.
Qed.

End OneComplement.


End Section13.

