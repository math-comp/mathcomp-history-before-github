(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime binomial groups.
Require Import morphisms perm action automorphism normal zmodp cyclic.
Require Import gfunc pgroups gprod center commutators.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection8.

(******************************************************************************)
(*   This file covers B & G, section 9, i.e., the proof the Uniqueness        *)
(* Theorem, along with the several variants and auxiliary results. Note that  *)
(* this is the only file to import BGsection8.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Nine.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H K L M A B P Q R : {group gT}.
Implicit Types p q r : nat.

(* This is B & G, Theorem 9.1(b) *)
Lemma noncyclic_normed_sub_Uniqueness : forall p M B,
    M \in 'M -> B \in 'E_p(M) -> ~~ cyclic B ->
    \bigcup_(K \in |/|_G(B; p^')) K \subset M ->
  B \in 'U.
Proof.
move=> p M B maxM; case/pElemP=> sBM abelB ncycB snbBp'_M.
have prM := mmax_proper maxM; have solM := mFT_sol prM.
have [pB cBB _] := and3P abelB.
apply/uniq_mmaxP; exists M; symmetry; apply/eqP.
rewrite eqEsubset sub1set inE maxM sBM; apply/subsetPn=> [[H0 MB_H0 neH0M]].
have:= erefl [arg max_(H > H0 | (H \in 'M(B)) && (H :!=: M)) #|H :&: M|`_p].
have [|H] := arg_maxP; first by rewrite MB_H0; rewrite inE in neH0M.
rewrite inE -andbA; case/and3P=> maxH sBH neHM maxHM _ {H0 MB_H0 neH0M}.
have sB_HM: B \subset H :&: M by rewrite subsetI sBH.
have{sB_HM} [R sylR sBR] := Sylow_superset sB_HM pB.
have [] := and3P sylR; rewrite subsetI; case/andP=> sRH sRM pR _.
have [P sylP sRP] := Sylow_superset sRM pR; have [sPM pP _] := and3P sylP.
have sHp'M: 'O_p^'(H) \subset M.
  apply: subset_trans snbBp'_M; rewrite (bigcup_max 'O_p^'(H)%G) // inE -andbA.
  by rewrite subsetT pcore_pgroup (subset_trans sBH) ?bgFunc_norm.
have{snbBp'_M} defMp': <<\bigcup_(K \in |/|_G(P; p^')) K>> = 'O_p^'(M).
  have nMp'M: M \subset 'N('O_p^'(M)) by exact: bgFunc_norm.
  have nMp'P := subset_trans sPM nMp'M.
  apply/eqP; rewrite eqEsubset gen_subG sub_gen ?andbT; last first.
    by rewrite (bigcup_max 'O_p^'(M)%G) // inE -andbA subsetT pcore_pgroup.
  apply/bigcupsP=> K; rewrite inE -andbA; case/and3P=> _ p'K nKP.
  have sKM: K \subset M.
    apply: subset_trans snbBp'_M; rewrite (bigcup_max K) // inE -andbA subsetT.
    by rewrite p'K (subset_trans (subset_trans sBR sRP)).
  rewrite -quotient_sub1 ?(subset_trans sKM) //=; set Mp' := 'O__(M).
  have tiKp: 'O_p(M / Mp') :&: (K / _) = 1.
    exact: coprime_TIg (pnat_coprime (pcore_pgroup _ _) (quotient_pgroup _ _)).
  suffices sKMp: K / _ \subset 'O_p(M / Mp') by rewrite -(setIidPr sKMp) tiKp.
  rewrite -Fitting_eq_pcore ?trivg_pcore_quotient //.
  apply: subset_trans (cent_sub_Fitting (quotient_sol _ solM)).
  rewrite subsetI quotientS //= (Fitting_eq_pcore (trivg_pcore_quotient _ _)).
  rewrite (sameP commG1P trivgP) /= -/Mp' -tiKp subsetI commg_subl commg_subr.
  rewrite (subset_trans (quotientS _ sKM)) ?bgFunc_norm //=.
  apply: subset_trans (pcore_sub_Hall (quotient_pHall nMp'P sylP)) _.
  by rewrite quotient_norms.
have ntR: R :!=: 1.
  by case: eqP sBR ncycB => // ->; move/trivgP->; rewrite cyclic1.
have{defMp'} sNPM: 'N(P) \subset M.
  case: (eqVneq 'O_p^'(M) 1) => [Mp'1 | ntMp'].
    have nsZLP: 'Z('L(P)) <| M.
      apply: Puig_center_normal Mp'1 => //; exact: mFT_odd.
    rewrite -(mmax_normal maxM nsZLP).
      exact: char_norm_trans (center_Puig_char P) _.
    apply: contra ntR; move/eqP; move/(trivg_center_Puig_pgroup pP)=> P1.
    by rewrite -subG1 -P1.
  rewrite -(mmax_normal maxM (pcore_normal _ _) ntMp') /= -defMp' norms_gen //.
  apply/subsetP=> x nPx; rewrite inE sub_conjg; apply/bigcupsP=> K.
  rewrite inE -andbA -sub_conjg; case/and3P=> _ p'K nKP.
  rewrite (bigcup_max (K :^ x)%G) // inE -andbA subsetT pgroupJ p'K /=.
  by rewrite -(normP nPx) normJ conjSg.
have sylPG := mmax_sigma_Sylow maxM sylP sNPM.
have{sNPM} [sNRM sylRH]: 'N(R) \subset M /\ p.-Sylow(H) R.
  have:= sRP; rewrite subEproper; case/predU1P=> [defR | ltRP].
    by split; rewrite defR // (pHall_subl _ (subsetT _)) // -defR.
  have [|D]:= @mmax_exists _ 'N(R).
    by rewrite mFT_norm_proper // (mFT_pgroup_proper pR).
  case/setIdP=> maxD sND; move/implyP: (maxHM D); rewrite inE {}maxD /= leqNgt.
  rewrite (subset_trans (subset_trans sBR (normG R))) //= implybN.
  have ltRN := nilpotent_proper_norm (pgroup_nil pP) ltRP.
  rewrite -(card_Hall sylR) (leq_trans (proper_card ltRN)) /=; last first.
    rewrite setIC -(part_pnat_id (pgroupS (subsetIr _ _) pP)) dvdn_leq //.
    by rewrite partn_dvd ?cardG_gt0 // cardSg // setISS.
  move/eqP=> defD; rewrite defD in sND; split; rewrite // -Sylow_subnorm.
  by rewrite (pHall_subl _ _ sylR) ?setIS // subsetI sRH normG.
have sFH_RHp': 'F(H) \subset R * 'O_p^'(H).
  case/dprodP: (nilpotent_pcoreC p (Fitting_nil H)) => _ /= <- _ _.
  by rewrite p_core_Fitting mulgSS ?(pcore_sub_Hall sylRH) ?pcore_Fitting.
have sFH_M: 'F(H) \subset M by rewrite (subset_trans sFH_RHp') ?mul_subG.
case/(H :=P: M): neHM; case: (ltnP 2 'r('F(H))) => [le3r | ge2r].
  have [D uF_D] := uniq_mmaxP (Fitting_Uniqueness maxH le3r).
  by rewrite (eq_uniq_mmax uF_D maxM) // (eq_uniq_mmax uF_D maxH) ?Fitting_sub.
have nHp'R: R \subset 'N('O_p^'(H)) by rewrite (subset_trans sRH) ?bgFunc_norm.
have nsRHp'H: R <*> 'O_p^'(H) <| H.
  rewrite sub_der1_normal //= ?mulgen_subG ?sRH ?pcore_sub //.
  rewrite norm_mulgenEl // (subset_trans _ sFH_RHp') //.
  rewrite rank2_der1_sub_Fitting ?mFT_odd //.
  by rewrite mFT_sol ?mmax_proper.
have sylR_RHp': p.-Sylow(R <*> 'O_p^'(H)) R.
  by apply: (pHall_subl _ _ sylRH); rewrite ?mulgen_subl // normal_sub.
rewrite (mmax_max maxH) // -(Frattini_arg nsRHp'H sylR_RHp') /=.
by rewrite mulG_subG mulgen_subG sRM sHp'M /= setIC subIset ?sNRM.
Qed.

(* This is B & G, Theorem 9.1(a) *)
Lemma noncyclic_cent1_sub_Uniqueness : forall p M B,
    M \in 'M -> B \in 'E_p(M) -> ~~ cyclic B ->
    \bigcup_(b \in B^#) 'C[b] \subset M ->
  B \in 'U.
Proof.
move=> p M B maxM EpB ncycB sCB_M.
apply: (noncyclic_normed_sub_Uniqueness maxM EpB) => //.
apply/bigcupsP=> K; rewrite inE -andbA; case/and3P=> _ p'K nKB.
case/pElemP: EpB => _; case/and3P=> pB cBB _.
rewrite (coprime_abelian_gen_cent1 cBB ncycB nKB); last first.
  by rewrite coprime_sym (pnat_coprime pB).
rewrite bigprodGE gen_subG (subset_trans _ sCB_M) //.
by apply/bigcupsP=> b Bb; rewrite (bigcup_max b) // subsetIr.
Qed.

(* This is B & G, Corollary 9.2 *)
Lemma cent_uniq_Uniqueness : forall K L,
  L \in 'U -> K \subset 'C(L) -> 'r(K) >= 2 -> K \in 'U.
Proof.
move=> K L uL; have ntL := uniq_mmax_neq1 uL.
case/uniq_mmaxP: uL => H uL_H cLK; have [maxH sLH] := mem_uniq_mmax uL_H.
case/rank_geP=> B; case/nElemP=> p; case/pnElemP=> sBK abelB; move/eqP=> dimB2.
have scBH: \bigcup_(b \in B^#) 'C[b] \subset H.
  apply/bigcupsP=> b; case/setIdP; rewrite inE -cycle_eq1 => ntb Bb.
  apply: (sub_uniq_mmax uL_H); last by rewrite /= -cent_cycle mFT_cent_proper.
  by rewrite sub_cent1 (subsetP cLK) ?(subsetP sBK).
have EpB: B \in 'E_p(H).
  apply/pElemP; split=> //; rewrite -(setD1K (group1 B)) subUset sub1G /=.
  apply/subsetP=> b Bb; apply: (subsetP scBH).
  by apply/bigcupP; exists b => //; exact/cent1P.
have prK: K \proper G by rewrite (sub_proper_trans cLK) ?mFT_cent_proper.
apply: uniq_mmaxS prK (noncyclic_cent1_sub_Uniqueness _ EpB _ _) => //.
by rewrite (abelem_cyclic abelB) (eqP dimB2).
Qed.

(* This is B & G, Corollary 9.3 *)
Lemma any_cent_rank3_Uniquness : forall p A B,
    abelian A -> p.-group A -> 'r(A) >= 3 -> A \in 'U ->
    p.-group B -> ~~ cyclic B -> 'r_p('C(B)) >= 3 ->
  B \in 'U.
Proof.
move=> p A B cAA pA rA3 uA pB ncycB; case/p_rank_geP=> C /= Ep3C.
have [cBC abelC dimC3] := pnElemP Ep3C; have [pC cCC _] := and3P abelC.
have [P /= sylP sCP] := Sylow_superset (subsetT _) pC.
wlog sAP: A pA cAA rA3 uA / A \subset P.
  move=> IHA; have [x _] := Sylow_Jsub sylP (subsetT _) pA.
  by apply: IHA; rewrite ?pgroupJ ?abelianJ ?rankJ ?uniq_mmaxJ.
have ncycC: ~~ cyclic C by rewrite (abelem_cyclic abelC) dimC3.
have ncycP: ~~ cyclic P := contra (cyclicS sCP) ncycC.
have [D] := ex_odd_normal_abelem2 (pHall_pgroup sylP) (mFT_odd _) ncycP.
case/andP=> sDP nDP; case/pnElemP=> _ abelD dimD2.
have CADge2: 'r('C_A(D)) >= 2.
  move: rA3; rewrite (rank_pgroup pA); case/p_rank_geP=> E.
  case/pnElemP=> sEA abelE dimE3; apply: leq_trans (rankS (setSI _ sEA)).
  rewrite (rank_abelem (abelemS (subsetIl _ _) abelE)) -(leq_add2r 1) addn1.
  rewrite -dimE3 -leq_sub_add -logn_div ?cardSg ?divgS ?subsetIl //.
  rewrite logn_quotient_cent_abelem ?dimD2 //.
  exact: subset_trans (subset_trans sAP nDP).
have CCDge2: 'r('C_C(D)) >= 2.
  rewrite (rank_abelem (abelemS (subsetIl _ _) abelC)) -(leq_add2r 1) addn1.
  rewrite -dimC3 -leq_sub_add -logn_div ?cardSg ?divgS ?subsetIl //.
  by rewrite logn_quotient_cent_abelem ?dimD2 //; exact: subset_trans nDP.
rewrite centsC in cBC; apply: cent_uniq_Uniqueness cBC _; last first.
  by rewrite ltnNge (rank_pgroup pB) -odd_pgroup_rank1_cyclic ?mFT_odd.
have cCDC: C \subset 'C('C_C(D))
  by rewrite (sub_abelian_cent (abelem_abelian abelC)) ?subsetIl.
apply: cent_uniq_Uniqueness cCDC _; last by rewrite (rank_abelem abelC) dimC3.
apply: cent_uniq_Uniqueness (subsetIr _ _) CCDge2.
have cDCA: D \subset 'C('C_A(D)) by rewrite centsC subsetIr.
apply: cent_uniq_Uniqueness cDCA _; last by rewrite (rank_abelem abelD) dimD2.
by apply: cent_uniq_Uniqueness uA _ CADge2; rewrite subIset // -abelianE cAA.
Qed.

(* This is B & G, Lemma 9.4 *)
Lemma any_rank3_Fitting_Uniqueness : forall p M P,
  M \in 'M -> 'r_p('F(M)) >= 3 -> p.-group P -> 'r(P) >= 3 -> P \in 'U.
Proof.
move=> p M P maxM FMge3 pP; rewrite (rank_pgroup pP).
case/p_rank_geP=> B; case/pnElemP=> sBP abelB dimB3.
have [pB cBB _] := and3P abelB.
have CBge3: 'r_p('C(B)) >= 3 by rewrite -dimB3 -(p_rank_abelem abelB) p_rankS.
have ncycB: ~~ cyclic B by rewrite (abelem_cyclic abelB) dimB3.
apply: {P pP}uniq_mmaxS sBP (mFT_pgroup_proper pP) _.
case/orP: (orbN (p.-group 'F(M))) => [pFM | pFM'].
  have [P sylP sFP] := Sylow_superset (Fitting_sub _) pFM.
  have pP := pHall_pgroup sylP.
  have [|A SCN_A]:= p_rank_3_SCN pP (mFT_odd _).
    by rewrite (rank_pgroup pP) (leq_trans FMge3) ?p_rankS.
  have [_ _ uA] := SCN_Fitting_Uniqueness maxM pFM sylP FMge3 SCN_A.
  case/setIdP: SCN_A => SCN_A dimA3; case: (setIdP SCN_A); case/andP=> sAP _ _.
  have cAA := SCN_abelian SCN_A; have pA := pgroupS sAP pP.
  exact: (any_cent_rank3_Uniquness cAA pA).
have [A0 EpA0 A0ge3] := p_rank_pmaxElem_exists FMge3.
have uA := non_pcore_Fitting_Uniqueness maxM pFM' EpA0 A0ge3.
case/pmaxElemP: EpA0; case/setIdP=> _ abelA0 _.
have [pA0 cA0A0 _] := and3P abelA0; rewrite -rank_pgroup // in A0ge3.
rewrite (any_cent_rank3_Uniquness _ pA0) // (cent_uniq_Uniqueness uA) 1?ltnW //.
by rewrite centsC subsetIr.
Qed.

(* This is B & G, Lemma 9.5 *)
Lemma SCN_3_Uniqueness : forall p A, A \in 'SCN_3[p] -> A \in 'U.
Proof.
move=> p A SCN3_A; apply/idPn=> uA'.
have [P]:= bigcupP SCN3_A; rewrite inE => sylP; case/setIdP=> SCN_A Age3.
have [nsAP _] := setIdP SCN_A; have [sAP nAP] := andP nsAP.
have cAA := SCN_abelian SCN_A.
have pP := pHall_pgroup sylP; have pA := pgroupS sAP pP.
have ntA: A :!=: 1 by rewrite -rank_gt0 -(subnKC Age3).
have [p_pr _ [e oA]] := pgroup_pdiv pA ntA.
have{e oA} def_piA: \pi(#|A|) =i (p : nat_pred).
  by rewrite oA pi_of_exp //; exact: pi_of_prime.
have FmCAp_le2: forall M, M \in 'M('C(A)) -> 'r_p('F(M)) <= 2.
  move=> M; case/setIdP=> maxM cCAM; rewrite leqNgt; apply: contra uA' => Fge3.
  exact: (any_rank3_Fitting_Uniqueness maxM Fge3).
have sNP_mCA: forall M, M \in 'M('C(A)) -> 'N(P) \subset M.
  move=> M mCA_M; have Fple2 := FmCAp_le2 M mCA_M.
  case/setIdP: mCA_M => maxM sCAM; set F := 'F(M) in Fple2.
  have sNR_M: forall R, A \subset R -> R \subset P :&: M -> 'N(R) \subset M.
    move=> R sAR; rewrite subsetI; case/andP=> sRP sRM.
    pose q := if 'r(F) <= 2 then max_pdiv #|M| else s2val (rank_witness 'F(M)).
    have nMqR: R \subset 'N('O_q(M)) := subset_trans sRM (bgFunc_norm _ _).
    have{nMqR} [Q maxQ sMqQ] := max_normed_exists (pcore_pgroup _ _) nMqR.
    have [p'q sNQ_M]: q != p /\ 'N(Q) \subset M.
      case/mem_max_normed: maxQ sMqQ; rewrite {}/q.
      case: leqP => [Fle2 | ]; last first.
        case: rank_witness => q /= q_pr -> Fge3 qQ _ sMqQ; split=> //.
          by case: eqP Fge3 => // ->; rewrite ltnNge Fple2.
        have Mqge3: 'r('O_q(M)) >= 3.
          rewrite (rank_pgroup (pcore_pgroup _ _)) /= -p_core_Fitting.
          by rewrite -(p_rank_Sylow (nilpotent_pcore_Hall _ (Fitting_nil _))).
        have uMq: 'O_q(M)%G \in 'U.
          exact: (any_rank3_Fitting_Uniqueness _ Fge3 (pcore_pgroup _ _)).
        have uMqM := def_uniq_mmax uMq maxM (pcore_sub _ _).
        apply: sub_uniq_mmax (subset_trans sMqQ (normG _)) _ => //.
        apply: mFT_norm_proper (mFT_pgroup_proper qQ).
        by rewrite -rank_gt0 2?ltnW ?(leq_trans Mqge3) ?rankS.
      set q := max_pdiv _ => qQ _ sMqQ.
      have sylMq: q.-Sylow(M) 'O_q(M).
        by rewrite [pHall _ _ _]rank2_pcore_max_Sylow ?mFT_odd ?mmax_sol.
      have defNMq: 'N('O_q(M)) = M.
        rewrite (mmax_normal maxM (pcore_normal _ _)) // -rank_gt0.
        rewrite (rank_pgroup (pcore_pgroup _ _)) -(p_rank_Sylow sylMq).
        by rewrite p_rank_gt0 pi_max_pdiv cardG_gt1 mmax_neq1.
      have sylMqG: q.-Sylow(G) 'O_q(M).
        by rewrite (mmax_sigma_Sylow maxM) ?defNMq.
      rewrite (hall_maximal sylMqG (subsetT _) qQ) // defNMq; split=> //.
      have: 'r_p(G) > 2.
        by rewrite (leq_trans Age3) // (rank_pgroup pA) p_rankS ?subsetT.
      apply: contraL; move/eqP <-; rewrite (p_rank_Sylow sylMqG).
      rewrite -leqNgt -(rank_pgroup (pcore_pgroup _ _)) /=.
      by rewrite -p_core_Fitting (leq_trans _ Fle2) // rankS ?pcore_sub.
    have trCRq': [transitive 'O_p^'('C(R)), on |/|*(R; q) | 'JG].
      have cstrA: normed_constrained A.
        by apply: SCN_normed_constrained sylP _; rewrite inE SCN_A ltnW.
      have pR: p.-group R := pgroupS sRP pP.
      have snAR: A <|<| R by rewrite (nilpotent_subnormal (pgroup_nil pR)).
      have A'q: q \notin \pi(#|A|) by rewrite def_piA.
      rewrite -(eq_pgroup _ def_piA) in pR.
      have [|? []] := normed_trans_superset cstrA A'q snAR pR.
        by rewrite (eq_pcore _ (eq_negn def_piA)) Thompson_transitivity.
      by rewrite (eq_pcore _ (eq_negn def_piA)).
    apply/subsetP=> x nRx; have maxQx: (Q :^ x)%G \in |/|*(R; q).
      by rewrite (actsP (norm_acts_max_norm _ _)).
    have [y cRy [defQx]] := atransP2 trCRq' maxQ maxQx.
    rewrite -(mulgKV y x) groupMr.
      by rewrite (subsetP sNQ_M) // inE conjsgM defQx conjsgK.
    apply: subsetP cRy; apply: (subset_trans (pcore_sub _ _)).
    exact: subset_trans (centS _) sCAM.
  have sNA_M: 'N(A) \subset M.
    by rewrite sNR_M // subsetI sAP (subset_trans cAA).
  by rewrite sNR_M // subsetI subxx (subset_trans nAP).
pose P0 := [~: P, 'N(P)].
have ntP0: P0 != 1.
  apply/eqP; move/commG1P; rewrite centsC -(setIidPr (subsetT 'N(P))) /=.
  move/(Burnside_normal_complement sylP); case/sdprodP=> _ /= defG nGp'P _.
  have prGp': 'O_p^'(G) \proper G.
    rewrite properT; apply: contra ntA; move/eqP=> defG'.
    rewrite -(setIidPl (subsetT A)) /= -defG'.
    by rewrite coprime_TIg // (pnat_coprime pA (pcore_pgroup _ _)).
  have ntGp': 'O_p^'(G) != 1.
    apply: contraL (mFT_pgroup_proper pP).
    by rewrite -{2}defG; move/eqP->; rewrite mul1g proper_irrefl.
  by have:= mFT_norm_proper ntGp' prGp'; rewrite properE bgFunc_norm andbF.
have sP0P: P0 \subset P by rewrite commg_subl.
have pP0: p.-group P0 := pgroupS sP0P pP.
have uNP0_mCA: forall M, M \in 'M('C(A)) -> 'M('N(P0)) = [set M].
  move=> M mCA_M; have [maxM sCAM] := setIdP mCA_M.
  have sAM := subset_trans cAA sCAM.
  pose F := 'F(M); pose D := 'O_p^'(F).
  have cDP0: P0 \subset 'C(D).
    have sA1A := Ohm_sub 1 A.
    have nDA1: 'Ohm_1(A) \subset 'N(D).
      apply: subset_trans sA1A (subset_trans sAM (char_norm _)).
      exact: char_trans (pcore_char _ _) (Fitting_char _).
    have abelA1: p.-abelem 'Ohm_1(A) by rewrite Ohm1_abelem.
    have dimA1ge3: logn p #|'Ohm_1(A)| >= 3.
      by rewrite -(rank_abelem abelA1) rank_Ohm1.
    have coDA1: coprime #|D| #|'Ohm_1(A)|.
      rewrite coprime_sym (coprimeSg sA1A) //.
      exact: pnat_coprime pA (pcore_pgroup _ _).
    rewrite centsC -[D]/(gval _).
    rewrite (coprime_abelian_gen_cent (abelianS sA1A cAA) nDA1) //=.
    rewrite bigprodGE gen_subG /= -/D; apply/bigcupsP=> B.
    case/and3P=> cycqB sBA1 nBA1; have abelB := abelemS sBA1 abelA1.
    have sBA := subset_trans sBA1 sA1A.
    have{cycqB} ncycB: ~~ cyclic B.
      move: cycqB; rewrite (abelem_cyclic (quotient_abelem _ abelA1)).
      rewrite card_quotient // -divgS // logn_div ?cardSg // leq_sub_add addn1.
      move/(leq_trans dimA1ge3); rewrite ltnS ltnNge.
      by rewrite -(abelem_cyclic abelB).
    have [x Bx sCxM']: exists2 x, x \in B^# & ~~ ('C[x] \subset M).
      suff: ~~ (\bigcup_(x \in B^#) 'C[x] \subset M).
        case/subsetPn=> y; case/bigcupP=> x Bx cxy My'.
        by exists x; last by apply/subsetPn; exists y.
      have EpB: B \in 'E_p(M) by rewrite inE (subset_trans sBA sAM).
      apply: contra uA' => sCB_M.
      apply: uniq_mmaxS sBA (mFT_pgroup_proper pA) _.
      exact: noncyclic_cent1_sub_Uniqueness maxM EpB ncycB sCB_M.
    case/setD1P: Bx; rewrite -cycle_eq1 => ntx Bx.
    have{ntx} [L] := mmax_exists (mFT_cent_proper ntx).
    case/setIdP=> maxL; rewrite /= cent_cycle => sCxL.
    have{sCxM'} [neLM] : L != M by case: eqP sCxL sCxM' => // -> ->.
    have sNP_LM: 'N(P) \subset L :&: M.
      rewrite subsetI !sNP_mCA // inE maxL (subset_trans _ sCxL) // -cent_set1.
      by rewrite centS // sub1set (subsetP sBA).
    have sP0_LM': P0 \subset (L :&: M)^`(1).
      exact: subset_trans (commSg _ (normG _)) (dergS 1 sNP_LM).
    have DLle2: 'r(D :&: L) <= 2.
      apply: contraR neLM; rewrite -ltnNge -in_set1; case/rank_geP=> E.
      case/nElemP=> q /=; do 2!case/setIdP; rewrite subsetI /= -/D.
      case/andP=> sED sEL abelE; rewrite -p_rank_abelem //; move/eqP => dimE3.
      have sEF: E \subset F := subset_trans sED (pcore_sub _ _).
      have Fge3: 'r_q(F) >= 3 by rewrite -dimE3 p_rankS.
      have qE := abelem_pgroup abelE.
      have uE: E \in 'U.
        apply: any_rank3_Fitting_Uniqueness Fge3 _ _ => //.
        by rewrite (rank_pgroup qE) dimE3.
      rewrite -(def_uniq_mmax uE maxM (subset_trans sEF (Fitting_sub _))).
      by rewrite inE maxL.
    have cDL_P0: P0 \subset 'C(D :&: L).
      have nsDM: D <| M:= char_normal_trans (pcore_char _ _) (Fitting_normal M).
      have{nsDM} [sDM nDM] := andP nsDM.
      have sDL:  D :&: L \subset L :&: M by rewrite setIC setIS.
      have nsDL: D :&: L <| L :&: M by rewrite /normal sDL setIC normsIG.
      have [s ch_s last_s_DL] := chief_series_exists nsDL.
      have solLM := solvableS (subsetIl L M) (mmax_sol maxL).
      have solDL := solvableS sDL solLM.
      apply: (stable_series_cent (congr_group last_s_DL)) => //; first 1 last.
        rewrite coprime_sym (coprimegS (subsetIl _ _)) //.
        exact: pnat_coprime (pcore_pgroup _ _).
      have{last_s_DL}: last 1%G s \subset D :&: L by rewrite last_s_DL.
      rewrite /= -/P0; elim/last_ind: s ch_s => //= s U IHs.
      rewrite !path_rcons last_rcons /=; set V := last _ s.
      case/andP=> ch_s chUV sUDL; have [maxU _ nU_LM] := and3P chUV.
      case/andP: {maxU}(maxgroupp maxU); case/andP=> sVU _ nV_LM.
      have nVU := subset_trans sUDL (subset_trans sDL nV_LM).
      rewrite IHs ?(subset_trans sVU) // /stable_factor /normal sVU nVU !andbT.
      have nVP0 := subset_trans (subset_trans sP0_LM' (der_sub _ _)) nV_LM.
      rewrite commGC -sub_astabQR // (subset_trans sP0_LM') //. 
      have: is_abelem (U / V) := sol_chief_abelem solLM chUV.
      case/is_abelemP=> q _; case/andP=> qUV _.
      apply: rank2_cent_chief qUV sUDL; rewrite ?mFT_odd //.
      exact: leq_trans (p_rank_le_rank _ _) DLle2.
    rewrite centsC (subset_trans cDL_P0) ?centS ?setIS //.
    by rewrite (subset_trans _ sCxL) // -cent_set1 centS ?sub1set.
  case: (ltnP 2 'r(F)) => [| Fle2]. 
    have [q q_pr -> /= Fq3] := rank_witness [group of F].
    have Mq3: 'r('O_q(M)) >= 3.
      rewrite (rank_pgroup (pcore_pgroup _ _)) /= -p_core_Fitting.
      by rewrite -(p_rank_Sylow (nilpotent_pcore_Hall _ (Fitting_nil _))).
    have uMq: 'O_q(M)%G \in 'U.
      exact: any_rank3_Fitting_Uniqueness Fq3 (pcore_pgroup _ _) Mq3.
    apply: def_uniq_mmaxS (def_uniq_mmax uMq maxM (pcore_sub q _)); last first.
      exact: mFT_norm_proper ntP0 (mFT_pgroup_proper pP0).
    rewrite cents_norm // centsC (subset_trans cDP0) ?centS //=.
    rewrite -p_core_Fitting sub_pcore // => q1; move/eqnP=> ->{q1}.
    by apply/eqnP=> def_q; rewrite ltnNge def_q FmCAp_le2 in Fq3.
  rewrite (mmax_normal maxM) ?mmax_sup_id //.
  have sNP_M := sNP_mCA M mCA_M; have sPM := subset_trans (normG P) sNP_M.
  rewrite /normal comm_subG //= -/P0.
  have nFP: P \subset 'N(F) by rewrite (subset_trans _ (bgFunc_norm _ _)).
  have <-: F <*> P * 'N_M(P) = M.
    apply: Frattini_arg (pHall_subl (mulgen_subr _ _) (subsetT _) sylP).
    rewrite -(quotientGK (Fitting_normal M)) /= norm_mulgenEr //= -/F.
    rewrite -quotientK // cosetpre_normal -sub_abelian_normal ?quotientS //.
    by rewrite sub_der1_abelian ?rank2_der1_sub_Fitting ?mFT_odd ?mmax_sol.
  case/dprodP: (nilpotent_pcoreC p (Fitting_nil M)) => _ /= defF cDFp _.
  rewrite norm_mulgenEr //= -{}defF (centC cDFp) -/D p_core_Fitting /= -/F.
  rewrite -!mulgA mul_subG //; first by rewrite cents_norm // centsC.
  rewrite mulgA [_ * P]mulSGid ?pcore_sub_Hall 1?(pHall_subl _ (subsetT _)) //.
  by rewrite mulSGid ?subsetI ?sPM ?normG // subIset // orbC normsRr.
have [M mCA_M] := mmax_exists (mFT_cent_proper ntA).
have [maxM sCAM] := setIdP mCA_M; have sAM := subset_trans cAA sCAM.
have abelA1: p.-abelem 'Ohm_1(A) by rewrite Ohm1_abelem.
have sA1A := Ohm_sub 1 A.
have EpA1: 'Ohm_1(A)%G \in 'E_p(M) by rewrite inE (subset_trans sA1A).
have ncycA1: ~~ cyclic 'Ohm_1(A).
  rewrite (abelem_cyclic abelA1) -(rank_abelem abelA1) rank_Ohm1.
  by rewrite -(subnKC Age3).
have [x A1x sCxM']: exists2 x, x \in 'Ohm_1(A)^# & ~~ ('C[x] \subset M).
  suff: ~~ (\bigcup_(x \in 'Ohm_1(A)^#) 'C[x] \subset M).
    case/subsetPn=> y; case/bigcupP=> x A1 cxy My'.
    by exists x; last by apply/subsetPn; exists y.
  apply: contra uA' => sCA1_M.
  apply: uniq_mmaxS sA1A (mFT_pgroup_proper pA) _.
  exact: noncyclic_cent1_sub_Uniqueness maxM EpA1 ncycA1 sCA1_M.
case/setD1P: A1x; rewrite -cycle_eq1 => ntx A1x.
have: 'C[x] \proper G by rewrite -cent_cycle mFT_cent_proper.
case/mmax_exists=> L; case/setIdP=> maxL sCxL.
have mCA_L: L \in 'M('C(A)).
  rewrite inE maxL (subset_trans _ sCxL) //= -cent_set1 centS // sub1set.
  by rewrite (subsetP sA1A).
case/negP: sCxM'; move/uNP0_mCA: mCA_L; rewrite (uNP0_mCA M) //.
by move/set1_inj->.
Qed.

(* This is B & G, Theorem 9.6, first assertion; note that B & G omit the      *)
(* (required!) condition K \proper G.                                         *)
Theorem rank3_Uniqueness : forall K, K \proper G -> 'r(K) >= 3 -> K \in 'U.
Proof.
move=> K prK; case/rank_geP=> B; case/nElemP=> p.
case/pnElemP=> sBK abelB dimB3; have [pB cBB _] := and3P abelB.
suffices: B \in 'U by exact: uniq_mmaxS.
have [P sylP sBP] := Sylow_superset (subsetT _) pB.
have pP := pHall_pgroup sylP.
have [|A SCN3_A] :=  p_rank_3_SCN pP (mFT_odd _).
  by rewrite -dimB3 -(rank_abelem abelB) rankS.
have [SCN_A Age3] := setIdP SCN3_A.
have: A \in 'SCN_3[p] by apply/bigcupP; exists P; rewrite // inE.
move/SCN_3_Uniqueness=> uA; have cAA := SCN_abelian SCN_A.
case/setIdP: SCN_A; case/andP=> sAP _ _; have pA := pgroupS sAP pP.
apply: any_cent_rank3_Uniquness uA pB _ _ => //.
  by rewrite (abelem_cyclic abelB) dimB3.
by rewrite -dimB3 -p_rank_abelem ?p_rankS.
Qed.

(* This is B & G, Theorem 9.6, second assertion *)
Theorem cent_rank3_Uniqueness : forall K,
  'r(K) >= 2 -> 'r('C(K)) >= 3 -> K \in 'U.
Proof.
move=> K Kge2 CKge3; have cCK_K: K \subset 'C('C(K)) by rewrite centsC.
apply: cent_uniq_Uniqueness cCK_K _ => //.
apply: rank3_Uniqueness (mFT_cent_proper _) CKge3.
by rewrite -rank_gt0 ltnW.
Qed.

(* This is B & G, Theorem 9.6, final observation *)
Theorem nonmaxElem2_Uniqueness : forall p A,
  A \in 'E_p^2(G) :\: 'E*_p(G) -> A \in 'U.
Proof.
move=> p A; case/setDP=> EpA nmaxA; have [_ abelA dimA2]:= pnElemP EpA.
case/setIdP: EpA => EpA _; have [pA _] := andP abelA.
apply: cent_rank3_Uniqueness; first by rewrite -dimA2 -(rank_abelem abelA).
have [E maxE sAE] := pmaxElem_exists EpA.
have [] := pmaxElemP maxE; case/pElemP=> _ abelE _.
have [pE cEE _] := and3P abelE.
have: 'r(E) <= 'r('C(A)) by rewrite rankS // (subset_trans cEE) ?centS.
apply: leq_trans; rewrite (rank_abelem abelE) -dimA2 properG_ltn_log //.
by rewrite properEneq; case: eqP maxE nmaxA => //; move/group_inj=> -> ->.
Qed.

End Nine.

