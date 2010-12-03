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

End OneComplement.

End Section13.

