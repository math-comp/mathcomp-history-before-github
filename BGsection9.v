(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime binomial groups.
Require Import morphisms perm action automorphism normal zmodp cyclic.
Require Import gfunc pgroups nilpotent gprod center commutators sylow abelian.
Require Import maximal hall BGsection1 psmall BGsection6 BGsection7 BGsection8.

(******************************************************************************)
(*   This file covers B & G, section 9, i.e., the proof the Uniqueness        *)
(* Theorem, along with the several variants and auxiliary results. Note that  *)
(* this is the only file to import BGsection8.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(* This should be the statement of B & G, Lemma 4.20(a) *)
Lemma p_rank_2_der1_sub_Fitting : forall (gT : finGroupType) (G : {group gT}),
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> G^`(1) \subset 'F(G).
Proof.
Admitted.

(* This is a dual to pdiv, and it should probably be equipped with a similar  *)
(* set of lemmas.                                                             *)
Definition max_pdiv n := last 1%N (primes n).

(* This is a consequence of B & G, Lemma 4.20, specifically of 4.20(c), which *)
(* asserts that 'O_q^'(G) is a q^'.-Hall subgroup, where q is the smallest    *)
(* prime divisor of #|G| -- namely, pdiv #|G|.                                *)
Lemma p_rank_2_max_pcore_Sylow : forall (gT : finGroupType) (G : {group gT}),
    odd #|G| -> solvable G -> 'r('F(G)) <= 2 ->
  let p := max_pdiv #|G| in p.-Sylow(G) 'O_p(G).
Proof.
Admitted.

Section Nine.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H M A X P B : {group gT}.
Implicit Types p q r : nat.

Lemma mmax_exists : forall H, H \proper G -> {M | M \in 'M(H)}.
Proof.
move=> H; case/(@maxgroup_exists _ (fun M => M \proper G)) => M maxM sHM.
by exists M; rewrite !inE sHM andbT.
Qed.

Lemma mmax_sub_eq : {in 'M &, forall M H, M \subset H -> M :=: H}.
Proof.
move=> M H; rewrite !inE; case/maxgroupP=> _ maxM; case/maxgroupP=> prH _.
by move/maxM->.
Qed.

(* This is B & G, Theorem 9.1(b) *)
Lemma noncyclic_normed_sub_Uniqueness : forall p M B,
    M \in 'M -> B \in 'E_p(M) -> ~~ cyclic B ->
    \bigcup_(K \in |/|_G(B; p^')) K \subset M ->
  B \in 'U.
Proof.
move=> p M B maxM; case/pElemP=> sBM abelB ncycB snbBp'_M.
have prM := mmax_proper maxM; have solM := proper_minSimple_sol prM.
have [pB cBB _] := and3P abelB.
rewrite inE -(cards1 M) subset_leq_card //; apply/subsetPn=> [[H0 MB_H0 neH0M]].
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
  apply: contra ncycB; move/eqP=> R1; rewrite R1 in sBR.
  by rewrite (trivgP sBR) cyclic1.
have{defMp'} sNPM: 'N(P) \subset M.
  case: (eqVneq 'O_p^'(M) 1) => [Mp'1 | ntMp'].
    have nsZLP: 'Z('L(P)) <| M.
      apply: Puig_center_normal Mp'1 => //; exact: minSimple_odd.
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
  have [|D]:= @mmax_exists 'N(R).
    by rewrite proper_norm_minSimple // (proper_pgroup_minSimple pR).
  case/setIdP=> maxD sND; move/implyP: (maxHM D); rewrite inE {}maxD /= leqNgt.
  rewrite (subset_trans (subset_trans sBR (normG R))) //= implybN.
  have ltRN := nilpotent_proper_norm (pgroup_nil pP) ltRP.
  rewrite -(card_Hall sylR) (leq_trans (proper_card ltRN)) /=; last first.
    rewrite setIC -(part_pnat (pgroupS (subsetIr _ _) pP)) dvdn_leq //.
    by rewrite partn_dvd ?cardG_gt0 // cardSg // setISS.
  move/eqP=> defD; rewrite defD in sND; split; rewrite // -Sylow_subnorm.
  by rewrite (pHall_subl _ _ sylR) ?setIS // subsetI sRH normG.
have sFH_RHp': 'F(H) \subset R * 'O_p^'(H).
  case/dprodP: (nilpotent_pcoreC p (Fitting_nil H)) => _ /= <- _ _.
  by rewrite p_core_Fitting mulgSS ?(pcore_sub_Hall sylRH) ?pcore_Fitting.
have sFH_M: 'F(H) \subset M by rewrite (subset_trans sFH_RHp') ?mul_subG.
case/eqP: neHM; case: (ltnP 2 'r('F(H))) => [le3r | ge2r].
  apply: congr_group.
  apply: (uniq_mmaxP (Fitting_Uniqueness maxH le3r)); rewrite inE ?maxM //.
  by rewrite maxH Fitting_sub.
have nHp'R: R \subset 'N('O_p^'(H)) by rewrite (subset_trans sRH) ?bgFunc_norm.
have nsRHp'H: R <*> 'O_p^'(H) <| H.
  rewrite sub_der1_normal //= ?mulgen_subG ?sRH ?pcore_sub //.
  rewrite norm_mulgenEl // (subset_trans _ sFH_RHp') //.
  rewrite p_rank_2_der1_sub_Fitting ?minSimple_odd //.
  by rewrite proper_minSimple_sol ?mmax_proper.
have sylR_RHp': p.-Sylow(R <*> 'O_p^'(H)) R.
  by apply: (pHall_subl _ _ sylRH); rewrite ?mulgen_subl // normal_sub.
apply: mmax_sub_eq; rewrite // -(Frattini_arg nsRHp'H sylR_RHp') /=.
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

End Nine.

