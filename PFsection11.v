(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum ssrint algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.
Require Import PFsection6 PFsection7 PFsection8 PFsection9 PFsection10.

(******************************************************************************)
(* This file covers Peterfalvi, Section 11: Maximal subgroups of Types        *)
(* III and IV.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.

Section Eleven.

(* This is Peterfalvi (11.1). *)
Lemma lbound_expn_odd_prime p q : 
   odd p -> odd q -> prime p -> prime q -> p != q -> 4 * q ^ 2 + 1 < p ^ q.
Proof.
move=> odd_p odd_q pr_p pr_q p_neq_q.
have{pr_p pr_q} [pgt2 qgt2] : 2 < p /\ 2 < q by rewrite !odd_prime_gt2.
have [qlt5 | qge5 {odd_q qgt2 p_neq_q}] := ltnP q 5.
  have /eqP q3: q == 3 by rewrite eqn_leq qgt2 andbT -ltnS -(odd_ltn 5).
  apply: leq_trans (_ : 5 ^ q <= p ^ q); first by rewrite q3.
  by rewrite leq_exp2r // odd_geq // ltn_neqAle pgt2 eq_sym -q3 p_neq_q.
apply: leq_trans (_ : 3 ^ q <= p ^ q); last by rewrite -(subnKC qge5) leq_exp2r.
elim: q qge5 => // q IHq; rewrite ltnS leq_eqVlt => /predU1P[<- // | qge5].
rewrite (expnS 3); apply: leq_trans {IHq}(leq_mul (leqnn 3) (IHq qge5)).
rewrite -!addnS mulnDr leq_add // mulnCA leq_mul // !(mul1n, mulSnr).
by rewrite -addn1 sqrnD muln1 -(subnKC qge5) !leq_add ?leq_mul.
Qed.

Local Open Scope ring_scope.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

Variables M U W W1 W2 : {group gT}.
Hypotheses (maxM : M \in 'M) (defW : W1 \x W2 = W) (MtypeP : of_typeP M U defW).
Hypothesis notMtype2 : FTtype M != 2.

Let notMtype5 : FTtype M != 5. Proof. exact: FTtype5_exclusion. Qed.
Let notMtype1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.
Let Mtype34 : FTtype M \in pred2 3 4.
Proof.
by have:= FTtype_range M; rewrite -mem_iota !inE !orbA orbC 3?[_ == _](negPf _).
Qed.
Let Mtype_gt2 : (FTtype M > 2)%N. Proof. by case/pred2P: Mtype34 => ->. Qed.

Local Notation H0 := (Ptype_Fcore_kernel MtypeP).
Local Notation "` 'H0'" := (gval H0) (at level 0, only parsing) : group_scope.
Local Notation "` 'M'" := (gval M) (at level 0, only parsing) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation H := `M`_\F%G.
Local Notation "` 'H'" := `M`_\F (at level 0) : group_scope.
Local Notation HU := M^`(1)%G.
Local Notation "` 'HU'" := `M^`(1)%g (at level 0) : group_scope.
Local Notation U' := U^`(1)%G.
Local Notation "` 'U''" := `U^`(1)%g (at level 0) : group_scope.
Local Notation C := 'C_U(`H)%G.
Local Notation "` 'C'" := 'C_`U(`H) (at level 0) : group_scope.
Local Notation HC := (`H <*> `C)%G.
Local Notation "` 'HC'" := (`H <*> `C) (at level 0) : group_scope.
Local Notation H0C := (`H0 <*> `C)%G.
Local Notation "` 'H0C'" := (`H0 <*> `C) (at level 0) : group_scope.

Local Notation S_ := (seqIndD HU M HU).
Local Notation tau := (FT_Dade0 maxM).
Local Notation R := (FTtypeP_coh_base maxM MtypeP).
Local Notation V := (cyclicTIset defW).

Let Mtype24 := compl_of_typeII_IV maxM MtypeP notMtype5.

Let defMs : M`_\s = HU. Proof. exact: FTcore_type_gt2. Qed.
Let defA1 : 'A1(M) = HU^#. Proof. by rewrite /= -defMs. Qed.
Let defA : 'A(M) = HU^#. Proof. by rewrite FTsupp_eq1. Qed.
Let defA0 : 'A0(M) = HU^# :|: class_support V M.
Proof. by rewrite -defA (FTtypeP_supp0_def _ MtypeP). Qed.

Let scohM : subcoherent (S_ 1) tau R.
Proof. by rewrite -{2}(group_inj defMs); apply: FTtypeP_subcoherent. Qed.

Let p := #|W2|.
Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.
Let ntW2 : W2 :!=: 1%g. Proof. by rewrite -cardG_gt1 prime_gt1. Qed.
Let cycW2 : cyclic W2. Proof. exact: prime_cyclic. Qed.

Let q := #|W1|.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.
Let ntW1 : W1 :!=: 1%g. Proof. by rewrite -cardG_gt1 prime_gt1. Qed.
Let cycW1 : cyclic W1. Proof. exact: prime_cyclic. Qed.

Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.

Let nsHUM : HU <| M. Proof. exact: gFnormal. Qed.
Let sHUM : HU \subset M. Proof. exact: gFsub. Qed.
Let sHHU : H \subset HU. Proof. by have /mulG_sub[] := sdprodW defHU. Qed.
Let sUHU : U \subset HU. Proof. by have /mulG_sub[] := sdprodW defHU. Qed.
Let sUM : U \subset M. Proof. exact: subset_trans sUHU sHUM. Qed.

Let coHUq : coprime #|HU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP. Qed.
Let coUq : coprime #|U| q. Proof. exact: coprimeSg coHUq. Qed.
	
Let solHU : solvable HU. Proof. exact: solvableS sHUM (mmax_sol maxM). Qed.
Let solH : solvable H. Proof. exact: solvableS sHHU solHU. Qed.

Let ltM''HU :  M^`(2)%g \proper HU.
Proof. by rewrite (sol_der1_proper solHU) // -defMs FTcore_neq1. Qed.

Let frobMbar : [Frobenius M / M^`(2) = (HU / M^`(2)) ><| (W1 / M^`(2))].
Proof.
have [[_ _ _ _] _ _ [_ _ _ sW2M'' prHUW1 ] _] := MtypeP.
by rewrite Frobenius_coprime_quotient ?gFnormal //; split=> // _ /prHUW1->.
Qed.

Let defHC : H \x C = HC.
Proof. 
by have [defHC _ _ _] := typeP_context MtypeP; rewrite /= (dprodWY defHC).
Qed.

Let nC_UW1 : U <*> W1 \subset 'N(C).
Proof.
have /sdprodP[_ _ nHUW1 _] := Ptype_Fcore_sdprod MtypeP.
by rewrite normsI ?norms_cent // join_subG normG; have [_ []] := MtypeP.
Qed.

Let nsCM : C <| M.
Proof.
rewrite /normal subIset ?sUM //= -{1}(sdprodW (Ptype_Fcore_sdprod MtypeP)).
by rewrite mulG_subG cents_norm // centsC subsetIr.
Qed.

Let nsCU : C <| U. Proof. exact: normalS (subsetIl _ _) sUM nsCM. Qed.
Let nsHC_M : HC <| M. Proof. by rewrite normalY ?gFnormal. Qed.
Let sHC_HU : HC \subset HU. Proof. by rewrite join_subG sHHU subIset ?sUHU. Qed.
Let nsHC_HU : HC <| HU. Proof. exact: normalS nsHC_M. Qed.

Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists maxM MtypeP notMtype5. Qed.

Let minHbar : minnormal (H / H0) (M / H0).
Proof. exact: chief_factor_minnormal. Qed.

Let abelHbar : p.-abelem (H / H0)%g.
Proof.
have solHbar : solvable (H / H0) by rewrite quotient_sol.
have [_ _] := minnormal_solvable minHbar (subxx _) solHbar.
by rewrite /is_abelem def_Ptype_factor_prime.
Qed.

Let sH0H : H0 \subset H.
Proof. by have/andP[/maxgroupp/andP[/proper_sub]]:= chiefH0. Qed.

Let nH0M: M \subset 'N(H0).
Proof. by have /andP[/maxgroupp/andP[]] := chiefH0. Qed.

Let nsH0H : H0 <| H.
Proof. by rewrite /normal sH0H (subset_trans (Fcore_sub _)). Qed.

Let nsH0C_M : H0C <| M.
Proof. by rewrite !normalY ?gFnormal /normal ?(subset_trans sH0H) ?gFsub. Qed.

Let defH0C : H0 \x C = H0C.
Proof.
have /dprodP[_ _ cHC tiHC] := defHC.
by rewrite dprodEY ?(centsS sH0H) //; apply/trivgP; rewrite -tiHC setSI.
Qed.

(* Group-theoretic consequences of the coherence and non-coherence theorems   *)
(* of Sections 5, 9 and 10 for maximal subgroups of type III and IV.          *)

(* This is Peterfalvi (11.3). *)
Lemma FTtype34_noncoherence : ~ coherent (S_ H0C) M^# tau.
Proof.
move/bounded_seqIndD_coherent => /= coh1; move/coh1: scohM => {coh1}coh1.
have []: ~ coherent (S_ 1) M^# tau by apply: FTtype345_noncoherence.
have /mulG_sub[_ sW1M] := sdprodW defM.
have [nsHHU _ _ nHU tiHU] := sdprod_context defHU.
have sHM: H \subset M := gFsub _ _.
have [sCM sH0C_M]: C \subset M /\ H0C \subset M by rewrite !normal_sub.
have nH0_C := subset_trans sCM nH0M.
have sH0C_HC: H0C \subset HC by apply: genS (setSU _ _).
have nilHC: nilpotent (HC / 1).
  have [defFM _ _ _] := typeP_context MtypeP.
  by rewrite quotient_nil //= -defHC defFM Fitting_nil.
apply: coh1 nilHC _; rewrite ?sub1G ?normal1 //.
have[_ _ oHbar] :=  Ptype_Fcore_factor_facts maxM MtypeP notMtype5.
rewrite -(index_sdprod defM) -divgS // -(dprod_card defHC) -(dprod_card defH0C).
rewrite divnMr ?cardG_gt0 // divg_normal // oHbar.
rewrite typeIII_IV_core_prime // -/q lbound_expn_odd_prime ?mFT_odd //.
apply: contraTneq coHUq => <-; rewrite coprime_sym prime_coprime ?cardSg //.
by rewrite -(typeP_cent_compl MtypeP) subsetIl.
Qed.

(* This is Peterfalvi (11.4). *)
Lemma bounded_proper_coherent H1 :
  H1 <| M -> H1 \proper HU -> coherent (S_ H1) M^# tau ->
    (#|HU : H1| <= 2 * q * #|U : C| + 1)%N.
Proof.
move=> nsH1_H psH1_M' cohH1; have [nsHHU _ _ _ _] := sdprod_context defHU.
rewrite -leC_nat natrD -ler_subl_addr.
have-> : (2 * q * #|U : C|)%:R = 2%:R * #|M : HC|%:R * sqrtC #|HC : HC|%:R.
  rewrite indexgg sqrtC1 mulr1 -mulnA natrM; congr (_ * _%:R).
  apply/eqP; rewrite // -(eqn_pmul2l (cardG_gt0 HC)) Lagrange ?normal_sub //.
  rewrite mulnCA -(dprod_card defHC) -mulnA (Lagrange (subsetIl _ _)).
  by rewrite -(sdprod_card defM) -(sdprod_card defHU) mulnC.
have /= := coherent_seqIndD_bound nsHUM solHU scohM _ _ cohH1.
case/(_ H0C HC HC)=> // [|/FTtype34_noncoherence//].
suffices /center_idP->: abelian (HC / H0C) by rewrite genS ?setSU. 
suffices /isog_abelian->: HC / H0C \isog H / H0 by apply: abelem_abelian p _ _.
by rewrite /= (joingC H0) isog_sym quotient_sdprodr_isog ?(dprodWsdC defHC).
Qed.

(* This is Peterfalvi (11.5). *)
Lemma FTtype34_der2 : M^`(2)%g = HC.
Proof.
have [defFM [_ not_cHU] _ _] := typeP_context MtypeP.
have{defFM} sM''_HC: M^`(2)%g \subset HC.
  by rewrite -defHC defFM; have [_ _ []] := MtypeP.
have scohM'': subcoherent (S_ M^`(2)) tau R.
  apply: (subset_subcoherent scohM).
  by split; [apply: seqInd_uniq | apply: seqInd_sub | apply: cfAut_seqInd].
have cohM'': coherent (S_ M^`(2)) M^# tau.
  apply: uniform_degree_coherence scohM'' _.
  apply: all_pred1_constant #|M : HU|%:R _ _; rewrite all_map.
  apply/allP=> _ /seqIndP[y /setDP[sM''Ky _] ->] /=; rewrite inE in sM''Ky.
  by rewrite cfInd1 ?gFsub // lin_char1 ?mulr1 ?lin_irr_der1.
have ubHC: (#|HC : M^`(2)| < 2 * q + 1)%N.
  rewrite -(ltn_pmul2r (indexg_gt0 U C)) mulnDl mul1n.
  apply: leq_ltn_trans (_ : 2 * q * #|U : C| + 1 < _)%N; last first.
    by rewrite ltn_add2l indexg_gt1 subsetIidl not_cHU //; have [] := Mtype24.
  have {1}->: #|U : C| = #|HU : HC| by apply: index_sdprodr (subsetIl _ _).
  by rewrite mulnC (Lagrange_index sHC_HU) // bounded_proper_coherent ?gFnormal.
have regHC_W1: semiregular (HC / M^`(2)) (W1 / M^`(2)).
  by apply: semiregularS (Frobenius_reg_ker frobMbar); rewrite quotientS.
have [_ sW1M _ _ tiHU_W1] := sdprod_context defM.
suffices /dvdnP[k Dk]: 2 * q %| #|HC : M^`(2)|.-1.
  apply: contraTeq ubHC; rewrite -leqNgt eqEsubset sM''_HC -indexg_gt1.
  rewrite addn1 -[#|_:_|]prednK // {}Dk !ltnS muln_gt0 => /andP[k_ge1 q2_gt0].
  by rewrite -(leq_pmul2r q2_gt0) mul1n in k_ge1.
rewrite Gauss_dvd; last by rewrite coprime2n mFT_odd.
rewrite dvdn2 -subn1 odd_sub // addbT negbK subn1.
rewrite -card_quotient; last by rewrite (subset_trans sHC_HU) // (der_norm 1).
have Dq: q = #|W1 / M^`(2)|%g.
  apply/card_isog/quotient_isog; first by rewrite (subset_trans sW1M) ?gFnorm.
  by apply/trivgP; rewrite -tiHU_W1 setSI // (der_sub 1).
rewrite quotient_odd ?mFT_odd //= Dq regular_norm_dvd_pred ?quotient_norms //.
by rewrite (subset_trans sW1M) ?normal_norm.
Qed.
Local Notation defM'' := FTtype34_der2.

(* This is  Peterfalvi (11.6). *)
Lemma FTtype34_facts (H' := H^`(1)%g):
  [/\ p.-group H, U \subset 'C(H0), H0 :=: H' & C :=: U']. 
Proof.
have nilH: nilpotent H := Fcore_nil M.
have /sdprod_context[/andP[_ nHM] sUW1M _ _ _] := Ptype_Fcore_sdprod MtypeP.
have coH_UW1: coprime #|H| #|U <*> W1| := Ptype_Fcore_coprime MtypeP.
have [[_ mulHU _ tiHU] [nHU isomHU]] := (sdprodP defHU, sdprod_isom defHU).
have{sUW1M} cH0U: U \subset 'C(H0).
  have frobUW1 := Ptype_compl_Frobenius maxM MtypeP notMtype5.
  have nH0_UW1 := subset_trans sUW1M nH0M; have [_ nH0W1] := joing_subP nH0_UW1.
  have [coH0_UW1 solH0] := (coprimeSg sH0H coH_UW1, solvableS sH0H solH).
  have [_ -> //] := Frobenius_Wielandt_fixpoint frobUW1 nH0_UW1 coH0_UW1 solH0.
  have ->: 'C_H0(W1) = H0 :&: 'C_H(W1) by rewrite setIA (setIidPl sH0H).
  have nH0C: 'C_H(W1) \subset 'N(H0) by rewrite subIset // normal_norm.
  rewrite cardMg_TI // -LagrangeMl -card_quotient {nH0C}//.
  rewrite coprime_quotient_cent ?(coprimeSg sHHU) //=.
  have [_ -> _] := Ptype_Fcore_factor_facts maxM MtypeP notMtype5.
  by rewrite (typeP_cent_core_compl MtypeP) (def_Ptype_factor_prime _ MtypeP).
have{isomHU} defC: C :=: U'.
  have [injHquo defHUb] := isomP isomHU.
  apply: (injm_morphim_inj injHquo); rewrite ?subsetIl ?morphim_der ?der_sub //.
  rewrite defHUb morphim_restrm -quotientE setIA setIid -quotientMidl /=.
  by rewrite (dprodW defHC) -defM'' -quotient_der // -mulHU mul_subG ?normG.
have{coH_UW1} defH0: H0 :=: H'.
  pose Hhat := (H / H')%g; pose Uhat := (U / H')%g; pose HUhat := (HU / H')%g.
  have nH'H: H \subset 'N(H') := gFnorm _ _.
  have nH'U: U \subset 'N(H') := char_norm_trans (der_char _ _) nHU.
  apply/eqP; rewrite eqEsubset andbC.
  rewrite der1_min ?(abelem_abelian abelHbar) ?normal_norm //=.
  rewrite -quotient_sub1 /= -/H'; last exact: subset_trans sH0H nH'H.
  suffices <-: 'C_Hhat(Uhat) = 1%g.
    by rewrite subsetI quotientS //= quotient_cents // centsC.
  suffices: ~~ ('C_Hhat(Uhat)^`(1)%g \proper 'C_Hhat(Uhat)).
    exact: contraNeq (sol_der1_proper (quotient_sol _ solH) (subsetIl Hhat _)).
  have {2}<-: HUhat^`(1)%g :&: 'C_Hhat(Uhat) = 'C_Hhat(Uhat).
    rewrite -quotient_der ?[HU^`(1)%g]defM''; last by rewrite -mulHU mul_subG.
    by rewrite (setIidPr _) ?subIset // quotientS ?joing_subl.
  suffices defHUhat: 'C_Hhat(Uhat) \x ([~: Hhat, Uhat] <*> Uhat) = HUhat.
    rewrite -(dprod_modl (der_dprod 1 defHUhat)) ?der_sub //= -/Hhat.
    rewrite [rhs in _ \x rhs](trivgP _) ?dprodg1 ?properxx //= -/Hhat.
    by have [_ _ _ <-] := dprodP defHUhat; rewrite setIC setIS ?der_sub.
  have coHUhat: coprime #|Hhat| #|Uhat|.
    by rewrite coprime_morph ?(coprimegS _ coH_UW1) ?joing_subl.
  have defHhat: 'C_Hhat(Uhat) \x [~: Hhat, Uhat] = Hhat. 
    by rewrite dprodC coprime_abelian_cent_dprod ?der_abelian ?quotient_norms.
  rewrite /HUhat -(sdprodWY defHU) quotientY //= -(dprodWY defHhat).
  have [_ _ cCRhat tiCRhat] := dprodP defHhat.
  rewrite dprodEY ?joingA //; first by rewrite join_subG cCRhat centsC subsetIr.
  apply/trivgP; rewrite /= joingC norm_joinEl ?commg_normr //= -/Hhat -/Uhat.
  rewrite -tiCRhat !(setIAC _ 'C(_)) setSI // subsetI subsetIl /=.
  by rewrite -group_modr ?commg_subl ?quotient_norms //= coprime_TIg ?mul1g.
suffices{defC defH0}: p.-group H by [].
pose R := 'O_p^'(H); have hallR: p^'.-Hall(H) R := nilpotent_pcore_Hall _ nilH.
have defRHp: R \x 'O_p(H) = H by rewrite dprodC nilpotent_pcoreC.
suffices R_1: R :=: 1%g by rewrite -defRHp R_1 dprod1g pcore_pgroup.
have /subsetIP[sRH cUR]: R \subset 'C_H(U).
  have oH: #|H| = (p ^ q * #|'C_H(U)|)%N.
    by have:= typeII_IV_core maxM MtypeP notMtype5 => /=; rewrite ifN => // -[].
  apply/setIidPl/eqP; rewrite eqEcard subsetIl /= (card_Hall hallR) {}oH.
  rewrite (card_Hall (setI_normal_Hall _ hallR _)) ?subsetIl ?gFnormal //.
  rewrite partnM ?expn_gt0 ?cardG_gt0 //= part_p'nat ?mul1n ?pnatNK //.
  by rewrite pnat_exp ?pnat_id.
suffices: ~~ (R^`(1)%g \proper R) by apply: contraNeq (sol_der1_proper solH _). 
have /setIidPr {2}<-: R \subset HU^`(1)%g.
  by rewrite [HU^`(1)%g]defM'' -(dprodWY defHC) sub_gen ?subsetU ?sRH.
suffices defRHpU: R \x ('O_p(H) <*> U) = HU.
  rewrite -(dprod_modl (der_dprod 1 defRHpU)) ?der_sub //= -/R setIC.
  rewrite [rhs in _ \x rhs](trivgP _) ?dprodg1 ?properxx //= -/R.
  by have /dprodP[_ _ _ <-] := defRHpU; rewrite setIS ?der_sub.
rewrite -(sdprodWY defHU) -[in RHS](dprodWY defRHp) -joingA.
have [_ _ cRHp tiRHp] := dprodP defRHp.
rewrite dprodEY //= -/R; first by rewrite join_subG cRHp centsC.
rewrite joingC (norm_joinEl (char_norm_trans (pcore_char p H) nHU)).
by rewrite -(setIidPl sRH) -setIA -group_modr ?gFsub // tiHU mul1g.
Qed.

Let frobUW1bar : [Frobenius U <*> W1 / C = (U / C) ><| (W1 / C)].
Proof.
have frobUW1: [Frobenius U <*> W1 = U ><| W1].
  exact: Ptype_compl_Frobenius MtypeP notMtype5.
have [defUW1 ntU _ _ _] := Frobenius_context frobUW1.
have [[_ _ _ defC] regUW1] := (FTtype34_facts, Frobenius_reg_ker frobUW1).
rewrite Frobenius_coprime_quotient // /normal ?subIset ?joing_subl //.
by split=> [|x /regUW1->]; rewrite ?sub1G //= defC (sol_der1_proper solHU).
Qed.

(* This is Peterfalvi (11.7).                                                 *)
(* We have recast the linear algebra arguments in the original text in pure-  *)
(* group-theoretic terms: the overhead of the abelem_rV correspondence is not *)
(* justifiable here, as the Ssreflect linear algebra library lacks specific   *)
(* support for bilinear forms: we use D y z := [~ coset Q y, coset Q z] as    *)
(* our "linear form". D is antisymmetric as D z y = (D y z)^-1, so we only    *)
(* show that D is "linear" in z, that is, that D y is a group morphism with   *)
(* domain H whose kernel contains H0, when y \in H, and we do not bother to   *)
(* factor D to obtain a form over Hbar = H / H0.                              *)
(*   We further rework the argument to support this change in perspective:    *)
(*  - We remove any reference to linear algebra in the "Galois" (9.7b) case,  *)
(*    where U acts irreducibly on Hbar: we revert to the proof of the         *)
(*    original Odd Order paper, using the fact that H / Q is extraspecial.    *)
(*  - In the "non-Galois" (9.7a) case, we use the W1-conjugation class of a   *)
(*    generator of H1 as an explicit basis of Hbar, indexed by W1, and we     *)
(*    use the elements xbar_ w = coset H0 (x_ w) of this basis instead of     *)
(*    arbitrary y in H_i, as the same argument then justifies extending       *)
(*    commutativity to all of Hbar.                                           *)
(*  - We construct phi as the morphism mapping ubar in Ubar to the n such     *)
(*    that the action of ubar on H1 is exponentiation by n. We derive a       *)
(*    morphism phi_ w ubar for the action of Ubar on H1 ^ w, for w in W1, by  *)
(*    composign with the action QV of W1 on Ubar by inverse conjugation.      *)
(*  - We exchange the two alternatives in the (9.7a) case; most of proof is   *)
(*    thus by contradiction with the C_U(Hbar) != u assertion in (9.6),       *)
(*    first establishing case 9.7a (as 9.7b contradicts q odd), then that D   *)
(*    is nontrivial for some x_ w1 and x_ w2 (as (H / Q)' = H0 / Q != 1),     *)
(*    whence (phi_ w1 u)(phi_ w2 u) = 1, whence (phi u)^-1 = phi u and        *)
(*    phi = 1, i.e., Ubar centralises Wbar.                                   *)
(* Note finally that we simply construct U as a maximal subgroup of H0 normal *)
(* in H, as the nilpotence of H / Q implies that H0 / Q lies in its center.   *)
Lemma FTtype34_Fcore_kernel_trivial :
  [/\ p.-abelem H, #|H| = (p ^ q)%N & `H0 = 1%g].
Proof.
have [[_ _ nHU tiHU] [pH cH0U defH' _]] := (sdprodP defHU, FTtype34_facts).
have [/mulG_sub[_ sW1M] nH0H] := (sdprodW defM, normal_norm nsH0H).
have nHW1: W1 \subset 'N(H) := subset_trans sW1M (gFnorm _ M).
have nUW1: W1 \subset 'N(U) by have [_ []] := MtypeP.
pose bar := coset_morphism H0; pose Hbar := (H / H0)%g; pose Ubar := (U / H0)%g.
have [Cbar_neqU _ /= oHbar] := Ptype_Fcore_factor_facts maxM MtypeP notMtype5.
rewrite -/Hbar def_Ptype_factor_prime // -/p -/q in oHbar.
have [nH0U nH0W1] := (subset_trans sUM nH0M, subset_trans sW1M nH0M).
suffices H0_1 : `H0 = 1%g.
  have isoHbar: H \isog H / H0 by rewrite H0_1 quotient1_isog.
  by rewrite (isog_abelem isoHbar) (card_isog isoHbar).
apply: contraNeq Cbar_neqU => ntH0; rewrite [Ptype_Fcompl_kernel _]unlock.
suffices: Hbar \subset 'C(Ubar).
  by rewrite (sameP eqP setIidPl) sub_astabQ nH0U centsC.
have pH0 := pgroupS sH0H pH; have{ntH0} [_ _ [k oH0]] := pgroup_pdiv pH0 ntH0.
have{k oH0} [Q maxQ nsQH]: exists2 Q : {group gT}, maximal Q H0 & Q <| H.
  have [Q [sQH0 nsQH oQ]] := normal_pgroup pH nsH0H (leq_pred _).
  exists Q => //; apply: p_index_maximal => //.
  by rewrite -divgS // oQ oH0 pfactorK //= expnS mulnK ?expn_gt0 ?cardG_gt0.
have nsQH0: Q <| H0 := p_maximal_normal (pgroupS sH0H pH) maxQ.
have [[sQH0 nQH0] nQH] := (andP nsQH0, normal_norm nsQH).
have nQU: U \subset 'N(Q) by rewrite cents_norm ?(centsS sQH0).
pose hat := coset_morphism Q; pose Hhat := (H / Q)%g; pose H0hat := (H0 / Q)%g.
have{maxQ} oH0hat: #|H0hat| = p by rewrite card_quotient ?(p_maximal_index pH0).
have defHhat': Hhat^`(1)%g = H0hat by rewrite -quotient_der -?defH'.
have ntH0hat: H0hat != 1%g by rewrite -cardG_gt1 oH0hat prime_gt1.
have pHhat: p.-group Hhat by apply: quotient_pgroup.
have nsH0Hhat: H0hat <| Hhat by apply: quotient_normal.
have sH0hatZ: H0hat \subset 'Z(Hhat).
  by rewrite prime_meetG ?oH0hat // meet_center_nil ?(pgroup_nil pHhat).
have{pHhat} gal'M: ~~ typeP_Galois MtypeP.
  have sZHhat: 'Z(Hhat) \subset Hhat := center_sub _.
  have nsH0hatZ: H0hat <| 'Z(Hhat) := normalS sH0hatZ sZHhat nsH0Hhat.
  have [f injf im_f] := third_isom sQH0 nsQH nsH0H.
  have fHhat: f @* (Hhat / H0hat)%g = Hbar by rewrite im_f.
  apply: contra (odd (logn p #|Hhat|)) _ _; last first.
    rewrite -(divnK (cardSg (quotientS Q sH0H))) divg_normal // oH0hat.
    by rewrite -(card_injm injf) // fHhat oHbar -expnSr pfactorK //= mFT_odd.
  rewrite /typeP_Galois acts_irrQ // => /mingroupP[_ minUHbar].
  suffices /(card_extraspecial pHhat)[n _ ->]: extraspecial Hhat.
    by rewrite pfactorK //= odd_double.
  have abelH: p.-abelem (Hhat / H0hat)%g by rewrite -(injm_abelem injf) ?fHhat.
  suffices{abelH} defZHhat: 'Z(Hhat) = H0hat.
    do 2?split; rewrite defZHhat ?oH0hat //.
    apply/eqP; rewrite eqEsubset (Phi_min pHhat) ?normal_norm //=.
    by rewrite (Phi_joing pHhat) defHhat' joing_subl.
  apply: contraNeq ntH0hat; rewrite eqEsubset sH0hatZ andbT => not_esHhat.
  rewrite -defHhat'; apply/eqP/derG1P/center_idP/(quotient_inj nsH0hatZ)=> //.
  apply: (injm_morphim_inj injf); rewrite ?quotientS //= fHhat -/Hhat -/H0hat.
  rewrite minUHbar //= -/Hbar -?fHhat 1?morphim_injm_eq1 ?morphimS // -subG1.
  rewrite quotient_sub1 ?(normal_norm nsH0hatZ) // not_esHhat -['Z(_)]cosetpreK.
  rewrite im_f ?sub_cosetpre_quo // quotient_norms ?norm_quotient_pre //.
  by rewrite (char_norm_trans (center_char _)) ?quotient_norms.
have [H1 []] := typeP_Galois_Pn maxM notMtype5 gal'M.
rewrite def_Ptype_factor_prime //= -/p => oH1 nH1Ubar _ /bigdprodWY-defHbar _.
have /cyclicP[xbar defH1]: cyclic H1 by rewrite prime_cyclic ?oH1.
have H1xbar: xbar \in H1 by rewrite defH1 cycle_id.
have sH1_Hbar: H1 \subset Hbar.
  by rewrite -[Hbar]defHbar (bigD1 1%g) ?group1 ?conjsg1 ?joing_subl.
have{sH1_Hbar} Hxbar: xbar \in Hbar := subsetP sH1_Hbar xbar H1xbar.
have /morphimP[x nH0x Hx /= Dxbar] := Hxbar.
have{oH1} oxbar: #[xbar] = p by rewrite orderE -defH1.
have memH0: {in H &, forall y z, [~ y, z] \in H0}.
  by rewrite defH'; apply: mem_commg.
have [_ /centsP-cHH0hat] := subsetIP sH0hatZ; move/subsetP in nQH.
pose D y z := [~ hat z, hat y].
have D_H0_1 y z: y \in H -> z \in H0 -> D y z = 1%g.
  by move=> Hy H0z; apply/eqP/commgP/cHH0hat; apply: mem_quotient.
have H0_D: {in H &, forall y z, D y z \in H0hat}.
  by move=> y z Hy Hz; rewrite -defHhat' mem_commg ?mem_quotient.
have Dsym y z: (D y z)^-1%g = D z y by rewrite invg_comm.
have Dmul y: y \in H -> {in H &, {morph D y: z t / z * t}}%g.
  move=> Hy z t Hz Ht; rewrite {1}/D morphM ?nQH // commMgR; congr (_ * _)%g.
  by rewrite -{2}morphR ?nQH // -/(D t _) D_H0_1 ?memH0 // mulg1.
pose Dm y Hy : {morphism H >-> coset_of Q} := Morphism (Dmul y Hy).
have{D_H0_1} kerDmH0 y Hy: H0 \subset 'ker (Dm y Hy).
  by rewrite subsetI sH0H; apply/subsetP=> z H0z; rewrite !inE /= D_H0_1.
pose x_ w := (x ^ w)%g; pose xbar_ w := (xbar ^ bar w)%g.
move/subsetP in nHW1; move/subsetP in nHU.
have Hx_ w: w \in W1 -> (x_ w \in H) * {in U, forall u, x_ w ^ u \in H}%g.
  by move/nHW1=> nHw; split=> [|u /nHU-nHu]; rewrite !memJ_norm.
have Dx: {in H &, forall y z, {in W1, forall w, D (x_ w) y = 1} -> D y z = 1}%g.
  move=> y z Hy Hz Dxy1; apply/(kerP (Dm y Hy) Hz); apply: subsetP z Hz.
  rewrite -(quotientSGK nH0H) ?kerDmH0 // -defHbar gen_subG.
  apply/bigcupsP=> _ /morphimP[w nH0w W1w ->] /=.
  rewrite defH1 Dxbar -quotient_cycle -?quotientJ ?quotientS // -cycleJ.
  by rewrite cycle_subG !inE /= Hx_ //= -Dsym eq_invg1 Dxy1.
pose ntrivD := [exists w in [predX W1 & W1], #[D (x_ w.1) (x_ w.2)] == p].
have{ntrivD Dx} /exists_inP[[w1 w2] /andP/=[Ww1 Ww2] /eqP-oDx12]: ntrivD.
  apply: contraR ntH0hat => Dx_1; rewrite -defHhat' -subG1 gen_subG.
  apply/subsetP=> _ /imset2P[_ _ /morphimP[y ? Hy ->] /morphimP[z ? Hz ->] ->].
  apply/set1P/Dx=> // w2 Ww2; rewrite Dx ?Hx_ // => w1 Ww1.
  have abelH0hat: p.-abelem H0hat by apply: prime_abelem.
  apply: contraNeq Dx_1 => /(abelem_order_p abelH0hat)oDx12.
  by apply/exists_inP; exists (w1, w2); rewrite ?inE ?Ww1 // oDx12 ?H0_D ?Hx_.
have /subsetP-nUW1bar: (W1 / H0)%g \subset 'N(Ubar) := quotient_norms H0 nUW1.
move/subsetP in nH0H; move/subsetP in nH0W1.
pose n (phi : {morphism Ubar >-> {unit 'F_p}}) ubar : nat := val (phi ubar).
have [phi Dphi]: {phi | {in Ubar, forall ub, xbar ^ ub =xbar ^+ n phi ub}}%g.
  pose xbar_Autm := invm (injm_Zp_unitm xbar).
  have /restrmP[phi [Dphi _ _ _]]: Ubar \subset 'dom (xbar_Autm \o conj_aut H1).
    by rewrite -sub_morphim_pre //= im_Zp_unitm -defH1 Aut_conj_aut.
  rewrite /n pdiv_id // -oxbar; exists phi => ubar /(subsetP nH1Ubar)Uubar.
  transitivity (Zp_unitm (phi ubar) xbar); last by rewrite autE /= -?defH1.
  by rewrite Dphi invmK ?im_Zp_unitm -?defH1 ?Aut_aut ?norm_conj_autE.
pose QV ubar w := (ubar ^ (bar w)^-1)%g.
have UbarQV: {in Ubar & W1, forall ubar w, QV ubar w \in Ubar}.
  by move=> ub w Uub W1w; rewrite /= memJ_norm ?groupV ?nUW1bar ?mem_quotient.
pose phi_ w ub := phi (QV ub w); pose nphi_ w ub := n phi (QV ub w).
have xbarJ: {in W1 & Ubar, forall w ub, xbar_ w ^ ub = xbar_ w ^+ nphi_ w ub}%g.
  by move=> w ubar * /=; rewrite -conjgM conjgCV conjgM Dphi ?UbarQV // conjXg.
have{oDx12} phi_w12 ubar: ubar \in Ubar -> (phi_ w1 ubar * phi_ w2 ubar = 1)%g.
  pose n_u := nphi_ ^~ ubar => Uubar; have [u nH0u Uu Dubar] := morphimP Uubar.
  suffices: n_u w1 * n_u w2 == 1 %[mod #[D (x_ w1) (x_ w2)]].
    by apply: contraTeq; rewrite oDx12 -!val_Fp_nat // natrM !natr_Zp.
  have DXn: {in H & W1, forall y w, D y (x_ w) ^+ n_u w = D y (x_ w ^ u)}%g.
    move=> y w Hy W1w; set z := x_ w; have [Hz /(_ u Uu) Hzu] := Hx_ w W1w.
    rewrite -(morphX (Dm y Hy)) //; apply/rcoset_kerP; rewrite ?groupX //.
    have /subsetP: H0 :* z ^ u \subset 'ker (Dm y Hy) :* z ^ u by rewrite mulSg.
    apply; apply/rcoset_kercosetP; rewrite ?groupX ?nH0H //.
    by rewrite morphX ?morphJ ?(nH0W1 w) // ?nH0H //= -Dubar -Dxbar xbarJ.
  rewrite -eq_expg_mod_order -{1}Dsym expgM expgVn ?(DXn, Dsym) ?Hx_ //.
  rewrite /D -!morphR ?nQH ?Hx_ // -conjRg (conjg_fixP _) //. 
  by apply/commgP/esym/(centsP cH0U); rewrite ?memH0 ?Hx_.
pose wbar := bar (w1 * w2 ^-1)%g; pose W1bar := (W1 / H0)%g.
have W1wbar: wbar \in W1bar by rewrite mem_quotient ?groupM ?groupV.
have{phi_w12} phiJ: {in Ubar, forall ubar, phi (ubar ^ wbar) = (phi ubar)^-1}%g.
  move=> ubar Uubar; apply/esym/eqP; rewrite eq_invg_mul.
  rewrite [wbar]morphM ?morphV ?nH0W1 ?groupV // -{1}[ubar](conjgK (bar w1)).
  by rewrite conjgM phi_w12 // memJ_norm ?nUW1bar ?mem_quotient.
have coW1bar2: coprime #|W1bar| 2 by rewrite coprimen2 quotient_odd ?mFT_odd.
have coUbar2: coprime #|Ubar| 2 by rewrite coprimen2 quotient_odd ?mFT_odd.
have{wbar phiJ W1wbar} phiV: {in Ubar, forall ubar, phi ubar = (phi ubar)^-1}%g.
  move=> ubar Uubar; rewrite /= -phiJ // -(expgK coW1bar2 W1wbar) -expgM mul2n.
  elim: (expg_invn _ _) => [|k IHk]; first by rewrite conjg1.
  by do 2!rewrite expgSr conjgM phiJ ?memJ_norm ?nUW1bar ?groupX // ?invgK.
rewrite -[Hbar]defHbar gen_subG defH1; apply/bigcupsP=> _ /morphimP[w _ Ww ->].
rewrite -cycleJ cycle_subG -/(xbar_ _); apply/centP=> ubar Uubar; apply/commgP.
apply/conjg_fixP; rewrite xbarJ // /nphi_ -[QV _ w](expgK coUbar2) ?UbarQV //.
by rewrite /n !morphX ?groupX 1?expgS 1?{1}phiV ?UbarQV // mulVg expg1n.
Qed.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel MtypeP :=: C.
Proof.
have [_ _ H0_1] := FTtype34_Fcore_kernel_trivial.
rewrite [Ptype_Fcompl_kernel MtypeP]unlock /= (group_inj H0_1).
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.

(* Character theory proper. *)

Let pddM := FT_prDade_hyp maxM MtypeP.
Let ptiWM : primeTI_hypothesis M HU defW := FT_primeTI_hyp MtypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddM.
Let ctiWM : cyclicTI_hypothesis M defW := prime_cycTIhyp ptiWM.

Local Notation sigma := (cyclicTIiso ctiWG).
Local Notation w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).
Local Notation mu_ := (primeTIred ptiWM).
Local Notation Idelta := (primeTI_Isign ptiWM).
Local Notation delta_ j := (primeTIsign ptiWM j).
Local Notation d := (FTtype345_TIirr_degree MtypeP).
Local Notation n := (FTtype345_ratio MtypeP).
Local Notation delta := (FTtype345_TIsign MtypeP).

Let mu2_ i j := primeTIirr ptiWM i j.
Let etaW := map sigma (irr W).

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.

Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Let SHC1 : {in S_ HC, forall xi : 'CF(M), xi 1%g = q%:R}.
Proof.
move=> _ /seqIndP[s /setDP[kerH' _] ->]; rewrite !inE in kerH'.
rewrite cfInd1 // -(index_sdprod defM) lin_char1 ?mulr1 // lin_irr_der1.
rewrite (subset_trans _ kerH') // der1_min //; first by case/andP: nsHC_HU.
have /isog_abelian <-: U / `C \isog HU / HC by apply: quotient_sdprodr_isog.
by have [_ _ _ ->] := FTtype34_facts; apply: der_abelian.
Qed.

Let scohM_HC : subcoherent (S_ HC) tau R.
Proof. exact/(subset_subcoherent scohM)/seqInd_conjC_subset1. Qed.

Let cohHC : coherent (S_ HC) M^# tau.
Proof.
apply: uniform_degree_coherence scohM_HC _.
by apply/(@all_pred1_constant _ q%:R)/allP=> _ /=/mapP[c /SHC1<- ->].
Qed.

Let SHC_irr : {subset S_ HC <= irr M}.
Proof.
move=> _ /seqIndP[s /setDP[kerHC kerHU] ->]; rewrite !inE in kerHC kerHU.
rewrite -(quo_IirrK _ kerHC) // mod_IirrE // cfIndMod // cfMod_irr //.
have /irr_induced_Frobenius_ker := FrobeniusWker frobMbar; rewrite defM''.
by apply; rewrite quo_Iirr_eq0 // -subGcfker.
Qed.

Let cfdot_SHC :  {in S_ HC &, forall phi psi, '[phi, psi] = (phi == psi)%:R}.
Proof.
have := sub_orthonormal SHC_irr (seqInd_uniq _ _) (irr_orthonormal _).
by case/orthonormalP.
Qed.

Let omu2 i j (z : 'CF(M)) (SHCz : z \in S_ HC) :  '[mu2_ i j, z] = 0.
Proof.
case/seqIndP: SHCz (SHC_irr SHCz)  => s _ -> Iind.
rewrite -cfdot_Res_l cfRes_prTIirr  cfdot_irr.
rewrite (negPf (contraNneq _ (prTIred_not_irr ptiWM j))) // => Ds.
by rewrite -cfInd_prTIres Ds.
Qed.

Let omu j (z : 'CF(M)) (SHCz : z \in S_ HC) :  '[mu_ j, z] = 0.
Proof. by rewrite cfdot_suml big1 // => i _; rewrite omu2. Qed.

Let cf_mu0Bz (z : 'CF(M)) (SHCz : z \in S_ HC) : mu_ 0 - z \in 'CF(M, 'A0(M)).
Proof.
apply: (cfun_onS (subsetUl _ _)).
rewrite [mu_ 0]prTIred0 defA cfun_onD1 !cfunE [z _]SHC1 //.
rewrite cfuniE // group1 mulr1 subrr rpredB ?rpredZ ?cfuni_on //=.
by have /seqInd_on-> := SHCz.
Qed.

(* This is 11.8.4 *)
Let ex_co_w_SHC_tau (z : 'CF(_)) (SHCz : z \in S_ HC) :
 orthogonal (tau (mu_ 0 - z) - \sum_i eta_ i 0) etaW ->
 exists2 tau1, coherent_with (S_ HC) M^# tau tau1 & 
               tau (mu_ 0 - z) = \sum_i eta_ i 0 - tau1 z.
Proof.
move: (SHCz); have /irrP[iz {z SHCz}->SHCz otauS] := SHC_irr SHCz.
pose z := 'chi_iz.
have[tau1 co_w_SHC_tau] := cohHC.
have [[Ztau1 Ptau1] Ctau1] := co_w_SHC_tau.
pose chi : 'CF(G) := \sum_i eta_ i 0 - tau (mu_ 0 - z).
have chiE : tau (mu_ 0 - z) = \sum_i eta_ i 0 - chi.
  by rewrite opprB [X in _ = X]addrC subrK.
have [chiEz|chiDz] := (chi =P tau1 z); first by exists tau1; rewrite -?chiEz.
have dirrChi : chi \in dirr G.
  apply: dirr_norm1.
    rewrite rpredB ?Dade_vchar ?rpred_sum 1?zchar_split // => [i _|].
      by apply: cycTIiso_vchar.
    by rewrite  cf_mu0Bz // rpredB ?char_vchar ?prTIred_char ?irr_char.
  have: '[tau (mu_ 0 - z)] = q%:R + 1.
    rewrite Dade_isometry ?cf_mu0Bz // (cfnormBd (omu _ _)) //. 
    by rewrite cfnorm_prTIred cfdot_SHC // eqxx.
  have /orthonormalP[_ cfeta] := cycTIiso_orthonormal ctiWG.
  rewrite chiE cfnormDd ?cfnormN ?cfdotNr ?cfdot_suml.
    rewrite (eq_bigr (fun i => 1%:R))=> [|i _].
      by rewrite sumr_const  nirrW1 -mulr_natl mulr1 // => /addrI.
    rewrite (bigD1 i) //= cfdotDr cfdot_sumr big1 ?addr0 // => [|i1 Dii1].
      by rewrite cfeta ?eqxx ?map_f ?mem_irr.
    by rewrite cfeta ?map_f ?mem_irr // cycTIiso_eqE eq_sym (negPf Dii1).
  rewrite -sumrN big1 // => i _; rewrite -cfdotNr opprB cfdotC.
  have /orthogonalP->// := otauS; rewrite ?conjC0 ?inE //.
  by apply: map_f (mem_irr _).
have SHC_dirr : {in S_ HC, forall l, tau1 l \in dirr G}.
  move=> l LiS1; rewrite /= dirrE Ztau1 ?Ptau1 ?mem_zchar //=.
  by rewrite cfdot_SHC // eqxx.
have cfdot_tau1B :
       {in S_ HC, forall z1 : 'CF(_), '[tau1 z - tau1 z1 , chi] = (z != z1)%:R}.
  move=> z1 SHCz1; rewrite /= cfdotBr cfdot_sumr big1 ?add0r => [|i _].
    rewrite -raddfB /= Ctau1 ?Dade_isometry ?cf_mu0Bz //.
    - rewrite cfdotBl !cfdotBr cfdotC omu // conjC0 sub0r.
      rewrite cfdot_SHC //= eqxx cfdotC omu // conjC0 sub0r.
      rewrite cfdot_SHC // eq_sym; case: (_ == _); first by rewrite addrN oppr0.
      by rewrite oppr0 subr0 opprK.
    - apply: cfun_onS (subsetUl _ _) _.
      rewrite defA cfun_onD1 rpredB //; last by apply: seqInd_on SHCz1.
        by rewrite !cfunE !SHC1 // addrN /=.
      by apply: seqInd_on SHCz.
    rewrite zchar_split rpredB ?mem_zchar // cfunD1E.
    by rewrite !cfunE !SHC1 // addrN /=.
  pose o_co := coherent_ortho_cycTIiso _ _ co_w_SHC_tau.
  by rewrite cfdotBl !o_co ?subr0 ?SHC_irr //; 
     apply: seqInd_conjC_subset1; rewrite -?defMs.
have [//|chiNE] : chi = tau1 z \/ chi = -tau1 z^*%CF.
  apply: cfdot_add_dirr_eq1; rewrite ?rpredN ?SHC_dirr ?cfAut_seqInd //.
  rewrite cfdot_tau1B ?cfAut_seqInd //.
  by rewrite eq_sym (seqInd_conjC_neq _ _ _ SHCz) ?mFT_odd.
case: (leqP (size (S_ HC)) 2)=> [S1le2|S1gt2].
  exists (dual_iso tau1); first by apply: dual_coherence scohM_HC _ _.
  by rewrite /= -chiNE.
pose S1 := rem z^*%CF (rem z (S_ HC)); pose x := S1`_0.
have [SHCx xDz xDzC] : [/\ x \in S_ HC, x != z & x != z^*%CF].
  have uSHC : uniq (S_ HC) := seqInd_uniq _ _.
  suff S1x : x \in S1.
    move: (S1x); rewrite /S1 !rem_filter ?filter_uniq //.
    rewrite !mem_filter //= => /andP[xDzC /andP[xDz _]].
    split=> //; apply: mem_rem (mem_rem S1x).
  rewrite mem_nth // !size_rem //; first by case: size S1gt2 => // [[|[]]].
  rewrite mem_rem_uniq // !inE.
  by rewrite (seqInd_conjC_neq _ _ _ SHCz) ?mFT_odd // cfAut_seqInd.
have [//|] : chi = tau1 z \/ chi = - tau1 x^*%CF.
  apply: cfdot_add_dirr_eq1; rewrite ?rpredN ?SHC_dirr ?cfAut_seqInd //.
  rewrite cfdot_tau1B ?cfAut_seqInd //.
  by case: eqP=> // zExC; case/eqP: xDzC; rewrite zExC cfConjCK.
rewrite chiNE=> NTE; case/eqP: xDz.
apply/(can_inj (@cfConjCK _ _))/(Zisometry_inj Ztau1 _ _).
- by apply/mem_zchar/cfAut_seqInd.
- by apply/mem_zchar/cfAut_seqInd.
by apply: oppr_inj.
Qed.

Let SC := seqIndD HU M HC C.
Let SHCdSC : {subset S_ HC <= [predC SC]}.
Proof.  
move=> s /seqIndP[] i; rewrite inE => /andP[_ iIk] ->.
by rewrite inE /= mem_seqInd // inE negb_and negbK iIk.
Qed.

Let Smu := [seq mu_ j | j in predC1 0].
Let Smu_nirr : {subset Smu <= [predC irr M]}.
Proof. by move=> _ /imageP[k _ ->]; apply: (prTIred_not_irr pddM). Qed.

Let S1nirr := filter [predC irr M] (seqIndD HU M H H0).
Let S1nirr_i_Smu : S1nirr =i Smu.
Proof.
have [szS1nirr _ S1nirr_s_Smu S1nirr_facts] := 
     typeP_reducible_core_Ind maxM MtypeP notMtype5.
have uS1nirr : uniq S1nirr by apply: filter_uniq (seqInd_uniq _ _).
have szSmu : size Smu = p.-1.
  by rewrite size_map -cardE cardC1 card_Iirr_abelian ?cyclic_abelian.
have []// := leq_size_perm uS1nirr S1nirr_s_Smu.
have [_ cH H0_1] := FTtype34_Fcore_kernel_trivial.
rewrite szS1nirr szSmu H0_1 -(card_isog (quotient1_isog _)) cH.
by case: q pr_q => // q1 _; rewrite pdiv_pfactor.
Qed.

Let u := #|(U/C)%g|.
Let mu1 j (nz_j : j != 0) : mu_ j 1%g = (q * u)%:R.
Proof.
have [szS4 _ S4sS3 pS4] := typeP_reducible_core_Ind maxM MtypeP notMtype5.
have /(pS4 _)[-> _ _] : mu_ j \in S1nirr 
  by rewrite S1nirr_i_Smu map_f // mem_enum.
by rewrite (group_inj Ptype_Fcompl_kernel_cent).
Qed.

Let Smu_i_SCnirr : Smu =i filter [predC irr M] SC.
Proof.
move=> mu_k.
have [szS1nirr _ S1nirr_s_Smu S1nirr_facts] := 
     typeP_reducible_core_Ind maxM MtypeP notMtype5.
rewrite -S1nirr_i_Smu /SC -(_ : (C <*> H)%G = HC) ?seqIndDY //=; last first.
  by apply/group_inj/dprodWY; rewrite -defHC dprodC.
apply/idP/idP=> [kIS4|].
  move: (kIS4); rewrite !mem_filter => /andP[-> _] /=.
  have/(S1nirr_facts _)[_] := kIS4.
  have [_ _ ->] := FTtype34_Fcore_kernel_trivial .
  by rewrite (group_inj (joing1G _)) (group_inj Ptype_Fcompl_kernel_cent).
rewrite !mem_filter !inE; case: (_ \in _)=> //=.
have [_ _ /group_inj->] := FTtype34_Fcore_kernel_trivial .
by apply: seqIndS (Iirr_kerDS _ (sub1G _) _) _.
Qed.

Local Notation "#1" := (inord 1).

(* This is PF (11.8). *)
Lemma FTtype34_not_ortho_cycTIiso (z : 'CF(_))  (SHCz : z \in S_ HC) : 
  ~~ orthogonal (tau (mu_ 0 - z) - \sum_i eta_ i 0) etaW.
Proof.
move: (SHCz); have /irrP[iz->] := SHC_irr SHCz=> {z SHCz}SHCz.
set z := 'chi_iz.
apply/negP=> otauS.
have u_gt0 : (u > 0)%N by exact: cardG_gt0.
have q_gt2 : (q > 2)%N by rewrite odd_gt2 ?mFT_odd ?cardG_gt1.
have size_SHC_q : (size (S_ HC) * q = u - 1)%N.
  pose X_ (S0 : seq 'CF(M)) := [set s | 'Ind[M, HU] 'chi_s \in S0].
  pose sumX_ cS0 := \sum_(s in X_ cS0) 'chi_s 1%g ^+ 2.
  have defX_SHC : X_ (S_ HC) = Iirr_kerD HU HU HC.
    by apply/setP=> s; rewrite !inE mem_seqInd // !inE.
  have defX : X_ (S_ 1) = Iirr_kerD HU HU 1%g.
    by apply/setP=> s; rewrite !inE mem_seqInd ?normal1 //= !inE.
  have sumX1 : sumX_ (S_ HC) = u%:R - 1.
    rewrite /sumX_ defX_SHC sum_Iirr_kerD_square // indexgg mul1r.
    by rewrite /u -!divgS // ?subsetIl // -(sdprod_card defHU) 
               -(dprod_card defHC) divnMl // divg_normal.
  apply/eqP; rewrite -eqC_nat mulnC [q](index_sdprod defM).
  rewrite (size_irr_subseq_seqInd _ (subseq_refl (S_ HC))) //.
  rewrite natrB ?cardG_gt0 // -sumr_const -sumX1.
  apply/eqP/esym/eq_bigr => s.
  rewrite defX_SHC !inE -defM'' -lin_irr_der1 => /and3P[_ _ /eqP->].
  by rewrite expr1n.
have nz_1j : #1 != 0 :> Iirr W2 by rewrite Iirr1_neq0.
(* First part of 11.8.1 *)
have Edu : d = u.
  apply/eqP; move/eqP: (mu1 nz_1j).
  rewrite /primeTIred  sum_cfunE (eq_bigr (fun i => d%:R))=> [|i _]; last first.
    by have [->] := FTtype345_constants maxM MtypeP notMtype2.
  rewrite sumr_const card_ord NirrW1 -mulr_natl -natrM eqC_nat eqn_pmul2l //.
  exact: cardG_gt0.
(* Second part of 11.8.1 *)
have Ed1 : delta = 1.
  suffices: (1 == delta %[mod q])%C.
    rewrite [delta]signrE /eqCmod addrC opprB subrK dvdC_nat.
    by case: (Idelta #1); rewrite ?subr0 // gtnNdvd.
  apply: eqCmod_trans (prTIirr1_mod ptiWM 0 #1); rewrite -/(mu2_ 0 #1) -/q.
  have [-> // _ _ _] := FTtype345_constants maxM MtypeP notMtype2.
  rewrite Edu eqCmod_sym /eqCmod -(@natrB _ u 1) ?indexg_gt0 // subn1 dvdC_nat.
  have /Frobenius_dvd_ker1 := frobUW1bar.
  have [nCU nCW1] := joing_subP nC_UW1; rewrite !card_quotient // -/u.
  by rewrite -indexgI setIC setIAC (coprime_TIg coUq) setI1g indexg1 -card_quotient.
(* Third part of 11.8.1 *)
have En : n = (size (S_ HC))%:R.
  rewrite /FTtype345_ratio Edu Ed1 -/q -(@natrB _  _ 1 %N) // -size_SHC_q.
  by rewrite natrM mulfK // (eqC_nat _ 0); case: q pr_q.
pose alpha_ := FTtype345_bridge MtypeP z.
have alphaE i j :  alpha_ i j = mu2_ i j - delta *: mu2_ i 0 - n *: z by [].
have S1z : z \in S_ 1 by apply: seqInd_sub SHCz.
have cf_alpha i j (nz_j : j != 0 ) : alpha_ i j \in 'CF(M, 'A0(M)).
  by rewrite supp_FTtype345_bridge // SHC1.
have cfdot_alpha i j (z1 : 'CF(M)) (SHCz1 : z1 \in S_ HC) :  
  '[alpha_ i j, z1] = (z1 == z)%:R * -n.
  move: (SHCz1); have/irrP[iz1 ->] := SHC_irr SHCz1=> {z1 SHCz1}SHCz1.
  rewrite !cfdotBl !cfdotZl !omu2 // mulr0 !(sub0r,oppr0).
  by rewrite mulrN mulrC cfdot_irr (inj_eq irr_inj) [iz1 == _]eq_sym.
have[tau1 co_w_tau_tau1 Etau] := ex_co_w_SHC_tau SHCz otauS.
have [[Ztau1 Ptau1] Ctau1] := co_w_tau_tau1.
pose a_ i j := '[tau (alpha_ i j), tau1 z] + n.
have Za i j (nz_j : j != 0) : a_ i j \in Cint.
  have [_ _ _ Nn] := FTtype345_constants maxM MtypeP notMtype2.
  rewrite rpredD ?(Cint_Cnat Nn) //.
  rewrite Cint_cfdot_vchar ?Ptau1 ?(mem_zchar SHCz) // Dade_vchar //.
  by rewrite zchar_split vchar_FTtype345_bridge ?mem_irr ?cf_alpha.
pose X_ i j :=
  tau (alpha_ i j) + n *: tau1 z - a_ i j *: \sum_(x <- S_ HC) tau1 x.
pose Y_ i j := - (n *: tau1 z) + a_ i j *: \sum_(x <- S_ HC) tau1 x.
(* This is the first part of 11.8.2 *)
have tau_alphaE i j : tau (alpha_ i j) = X_ i j + Y_ i j. 
  by rewrite addrA addrAC subrK addrK.
have cfdot_sum_tau1 (y : 'CF(_)) (SHCy : y \in S_ HC) :
      '[\sum_(x <- S_ HC) tau1 x, tau1 y] = 1.
  rewrite cfdot_suml (bigD1_seq y) ?seqInd_uniq //=.
  rewrite big_seq_cond big1 ?addr0 => [|x /andP[SHCx xDy]]; last first.
    by rewrite Ztau1 ?mem_zchar // (seqInd_ortho _ SHCx).
  rewrite Ztau1 ?mem_zchar //.
  by have /irrP[iy ->] := SHC_irr SHCy; exact: cfnorm_irr.
have oX_tau1 i j (nz_j : j != 0) (x : 'CF(_)) (SHCx : x \in S_ HC) : 
       '[X_ i j, tau1 x] = 0.
  rewrite cfdotBl cfdotDl !cfdotZl cfdot_sum_tau1 // mulr1.
  rewrite Ztau1 ?mem_zchar //.
  case: (boolP (z == x))=> [/eqP<-|zDx].
    by rewrite cfnorm_irr !mulr1 addrN.
  rewrite (seqInd_ortho _ SHCz) // mulr0 addr0.
  rewrite -{1}[x](subrK z) [tau1 _]raddfD cfdotDr.
  rewrite -addrA -[X in  _ + X]opprB [a_ _ _]addrC addrK.
  have ZSHCxBz : x - z \in 'Z[S_ HC, M^#].
    by rewrite  zcharD1 !cfunE !SHC1 // addrN ?eqxx zchar_onG rpredB ?mem_zchar.
  have ZsHU : {subset S_ HC <= 'CF(M, HU)}.
    by move=> u2 HU; apply: (seqInd_on (der_normal 1 _) HU).
  rewrite Ctau1 // Dade_isometry ?cf_alpha //; last first.
    rewrite (cfun_onS (subsetUl _ _)) // defA.
    rewrite  cfun_onD1 rpredB ?ZsHU ?mem_zchar //.
    by rewrite !cfunE !SHC1 ?addrN ?eqxx.
  rewrite cfdotBr !cfdot_alpha // eq_sym (negPf zDx) mul0r sub0r.
  by rewrite eqxx mul1r opprK addrN.
have oXY i j  (nz_j : j != 0) : '[X_ i j, Y_ i j] = 0.
  rewrite cfdotDr cfdotNr !cfdotZr oX_tau1 // mulr0 oppr0 add0r.
  rewrite cfdot_sumr big_seq_cond big1 ?mulr0 // => x /andP[SHCx _].
  by apply: oX_tau1.
have nY i j: j != 0 -> '[Y_ i j] = n * a_ i j * (a_ i j - 2%:R) + n ^+ 2.
  move=> nz_j; have [_ _ _ Nn] := FTtype345_constants maxM MtypeP notMtype2.
  rewrite /Y_ cfdotDl  !cfdotDr !cfdotNl !cfdotNr !cfdotZl !cfdotZr.
  rewrite (conj_Cnat Nn) (conj_Cint (Za _ _ nz_j)).
  rewrite Ztau1 ?mem_zchar // cfnorm_irr mulr1 opprK.
  rewrite cfdot_sum_tau1 // mulr1 cfdotC cfdot_sum_tau1 // conjC1 mulr1.
  have-> : '[\sum_(x <- S_ HC) tau1 x] = n.
    pose f1 i := 1 *: tau1 i.
    rewrite (eq_bigr f1)=> [|j2 Jj2]; last by rewrite /f1 scale1r.
    rewrite cfnorm_sum_orthogonal //; last first.
      by apply: seqInd_orthogonal => //; apply: der_normal.
    rewrite En [_ *+ _]Monoid.iteropE -count_predT -big_const_seq /=.
    apply: eq_big_seq => xi SHCxi.
    by rewrite normr1 expr1n mul1r irrWnorm ?SHC_irr.
  rewrite -addrA addrC mulrC; congr (_ + _); move: (_ * n) => b.
  by rewrite addrA addrC mulrC mulrBr mulr_natr opprD.
(* This is the second part of 11.8.2 *)
have le2 i j  (nz_j : j != 0): [|| a_ i j == 0, a_ i j == 1 | a_ i j == 2%:R].
  have /CintP[b Db]: a_ i j - 1 \in Cint by rewrite rpredB ?rpred1 ?Za.
  suffices: (`|b| ^ 2 < 2 ^ 2)%N.
    by rewrite ltn_sqr (canRL (subrK 1) Db) -!CintrE; case: (b); do 2?case.
  case Dm: (`|b| ^ 2)%N => // [m]; rewrite !ltnS /=.
  apply: (@leq_trans (size (S_ HC) * m)).
    by rewrite leq_pmull ?lt0n //; apply: contraL SHCz => /nilP->.
  rewrite -(addnK 1 m)%N addn1 -leC_nat natrM -En natrB // -Dm mulr1n.
  rewrite -abszX pmulrn abszE ger0_norm ?sqr_ge0 // rmorphX /= -Db.
  rewrite sqrrB expr1n addrK -mulrnAr -mulrBr mulrA -(ler_add2r (n ^+ 2)). 
  have ->: 2%:R + n ^+ 2 = '[tau (alpha_ i j)].
    by rewrite norm_FTtype345_bridge ?mem_irr // SHC1.
  by rewrite -nY // tau_alphaE cfnormDd ?oXY // ler_addr cfnorm_ge0.
(* This is the last part of 11.8.2 *)
have Xd i j (nz_j : j != 0) (Ca : (a_ i j == 0) || (a_ i j == 2%:R)) :
         X_ i j  = delta *: (eta_ i j - eta_ i 0).
  have co_w_SHC_tau1 : coherent_with (S_ HC) M^# tau tau1 by split.
  apply: (FTtype345_bridge_coherence _ _ S1z _ co_w_SHC_tau1 (tau_alphaE i j));
       rewrite ?SHC1 //.
  - exact: mem_irr.
  - by apply: seqInd_conjC_subset1; rewrite /= ?defMs.
  - rewrite rpredD ?rpredN ?rpredZ_Cint ?Za ?Cint_Cnat ?En //.
      by rewrite mem_zchar // map_f.
    by rewrite big_seq; apply: rpred_sum => x SHCx; rewrite mem_zchar // map_f.
  - rewrite cfdotC oXY ?conjC0 //.
  by rewrite nY //; case/pred2P: Ca => ->; rewrite ?subrr ?Monoid.simpm.
pose beta_ i j := tau (alpha_ i j) - (eta_ i j - eta_ i 0) + n *: tau1 z.
pose beta := beta_ 0 #1.
(* First part of 11.8.3 *)
have betaE i j: j != 0 -> beta_ i j = beta.
- move=> nz_j; congr (_ + _); rewrite -[eta_ 0 #1](subrK (eta_ 0 j)) -addrA.
  apply/(canLR (addrK _)); rewrite addrC addrA addrAC; apply/(canRL (subrK _)).
  rewrite -[RHS]scale1r -Ed1 opprD addrA addrAC opprD opprK addrACA addrA.
  have [Dmu2 Ddelta _ _] := FTtype345_constants maxM MtypeP notMtype2.
  rewrite scalerBr -(prDade_sub2_TIirr pddM) {}Ddelta -!{1}/(mu2_ _ _) //=.
  move/prDade_sub_TIirr: pddM => <-; rewrite ?{}Dmu2 //= -!{1}/(mu2_ _ _).
  rewrite -linearZ -!linearB /= scalerDr !scalerBr !signrZK; congr (tau _).
  by rewrite !opprB !addrA subrK -!{1}/(mu2_ _ _) 2![_ + mu2_ 0 j]addrAC subrK.
(* This is the last part of 11.8.3 *)
have Rbeta : cfReal beta.
  have nCn: n \in Cnat by rewrite En.
  apply/eqP; rewrite rmorphD !rmorphB /= raddfZ_Cnat //=.
  rewrite ![(eta_ _ _)^*%CF]cfAut_cycTIiso -!cycTIirr_aut !aut_Iirr0.
  set k1 := aut_Iirr conjC #1; rewrite -(betaE 0 k1) ?aut_Iirr_eq0 //.
  rewrite (cfConjC_Dade_coherent co_w_tau_tau1) ?mFT_odd ?mem_irr //.
  apply: canRL (subrK _) _; rewrite -[LHS]addrA addrAC -!raddfB; congr (_ - _).
  rewrite -opprB Ctau1 ?rpredN ?zcharD1_seqInd ?seqInd_sub_aut_zchar //=.
  rewrite opprB -linearZ -Dade_aut -linearD scalerBr addrA; congr (tau _).
  apply: canLR (addrK _) _; rewrite -raddfZ_Cnat // -rmorphD !subrK /=.
  by rewrite raddfB raddfZsign /= -!prTIirr_aut !aut_Iirr0.
have SHC_dirr : {in S_ HC, forall x : 'CF(_), tau1 x \in dirr G}.
  move=> x SHCx; rewrite /= dirrE Ztau1 ?Ptau1 ?mem_zchar //=.
  by rewrite cfdot_SHC ?eqxx.
(* This is 11.8.5 *)
have otau1_eta i j : {in S_ HC, forall z : 'CF(M), '[tau1 z, eta_ i j] = 0}.
  move=> x SHCx.
  rewrite /= (coherent_ortho_cycTIiso _ _ co_w_tau_tau1) ?SHC_irr //.
  by apply seqInd_conjC_subset1=> //=; rewrite ?defMs.
have a_is_zero  i j (nz_j : j != 0) : a_ i j = 0.
  have acfdot : a_ i j = '[\sum_i eta_ i 0, beta].
    have E1n : '[tau (mu_ 0 - z), tau (alpha_ i j)] = -1 + n.
      rewrite Dade_isometry ?cf_mu0Bz ?cf_alpha //.
      rewrite alphaE Ed1 scale1r cfdotBl !cfdotBr.
      rewrite  cfdotC cfdot_prTIirr_red (negPf nz_j) conjC0 sub0r. 
      rewrite  cfdotC cfdot_prTIirr_red eqxx conjC1.
      rewrite  !cfdotZr En ?conjC_nat omu // mulr0 subr0.
      rewrite ['[z]]cfdot_SHC // eqxx mulr1 !['[z,_]]cfdotC !omu2 //.
      by rewrite conjC0 sub0r oppr0 sub0r opprK.
    suff Eb1an : '[tau (mu_ 0 - z), tau (alpha_ i j)] = 
             '[\sum_i0 eta_ i0 0, beta] - 1 - a_ i j + n.
      apply: (addIr (- 1 - a_ i j + n)).
      rewrite ![X in X = _]addrA [a_ i j + _]addrC subrK -E1n Eb1an.
      by rewrite !addrA.
    rewrite Etau -(betaE i _ nz_j) /a_ -!addrA opprD subrK !addrA.
    rewrite cfdotBl cfdotDr !cfdotBr -!addrA; congr (_ + _).
    rewrite !cfdot_suml big1 ?sub0r ?opprK => [|i1 _]; last first.
      by rewrite cfdot_cycTIiso [_ == j]eq_sym (negPf nz_j) andbF.
    rewrite (bigD1 i) //= big1 ?addr0 => [|i1 i1Di]; last first.
      by rewrite cfdot_cycTIiso (negPf i1Di).
    rewrite big1 ?add0r => [|i1 _]; last first.
      by rewrite cfdotZr cfdotC otau1_eta // conjC0 mulr0.
    rewrite cfdot_cycTIiso !eqxx addrA addrN add0r.
    rewrite cfdotC conj_Cint // -[X in X \in _](addrK n) rpredB ?Za //.
    by rewrite En // Cint_Cnat.
  have a_even : (2 %| a_ i j)%C.
    rewrite acfdot cfdot_real_vchar_even ?mFT_odd //; first 1 last.
    - split; first by rewrite rpred_sum // => i1 _; exact: cycTIiso_vchar.
      rewrite /cfReal rmorph_sum /=; apply/eqP.
      rewrite (reindex_inj (can_inj (@conjC_IirrK _ _))) /=.
      apply: eq_bigr => i1 _; rewrite cfAut_cycTIiso -cycTIirr_aut aut_Iirr0.
      by rewrite [aut_Iirr _ _]conjC_IirrK.
    - split=> //; rewrite rpredD ?rpredB ?cycTIiso_vchar ?Dade_vchar //.
        by rewrite zchar_split vchar_FTtype345_bridge ?mem_irr ?cf_alpha.
      by rewrite En rpredZnat // Ptau1 // mem_zchar.
    have eta00: eta_ 0 0 = 1 by rewrite cycTIirr00 cycTIiso1.
    rewrite orbC cfdotDl 2!cfdotBl cfdotZl eta00 cfnorm1.
    rewrite -{2 3}eta00 otau1_eta // cfdot_cycTIiso (negPf nz_1j).
    rewrite Dade_reciprocity ?cf_alpha // => [| x _ y _]; last first.
      by rewrite !cfun1E !inE.
    rewrite cfRes_cfun1 alphaE !cfdotBl !cfdotZl -(prTIirr00 ptiWM).
    rewrite !cfdot_prTIirr (negPf nz_1j) Ed1 mulr1 cfdotC omu2 //.
    by rewrite conjC0 mulr0 subr0 addr0 subrr rpred0.
  move: acfdot; rewrite -(betaE i j) // /beta_ tau_alphaE Xd //; last first.
    case/or3P: (le2 i _ nz_j) a_even => /eqP->; rewrite ?eqxx ?orbT //.
    by rewrite (dvdC_nat 2 1).
  rewrite [_ + Y_ i j]addrC Ed1 scale1r addrK /Y_  [- _ + _]addrC subrK.
  rewrite cfdot_suml big1 ?scaler0 // => i1 _.
  rewrite cfdotZr cfdot_sumr  big_seq_cond big1 ?mulr0 // => i2 /andP[SHCi2 _].
  by rewrite cfdotC otau1_eta ?conjC0.
(* This is 11.8.6 *)
have [j nz_j] := has_nonprincipal_irr ntW2.
have mujE : mu_ j - d%:R *: z  = mu_ 0 - z + \sum_i alpha_ i j.
  rewrite !sumrB -scaler_sumr Ed1 scale1r [X in _ = X]addrC -!addrA -/(mu_ 0).
  congr (_ + _); rewrite [X in _ = _ + X]addrC !addrA addNr add0r -opprD.
  congr (- _); rewrite sumr_const nirrW1 -scaler_nat scalerA mulrC.
  by rewrite divfK ?neq0CG // Ed1 addrC  scalerBl scale1r subrK.
have tmujE : tau(mu_ j - d%:R *: z) = \sum_i eta_ i j - d%:R *: tau1 z.
  pose f i := eta_ i j - eta_ i 0 - n *: tau1 z.
  have taE i : tau (alpha_ i j) = f i.
    rewrite /f tau_alphaE Xd /Y_ ?a_is_zero ?scale0r ?addr0 ?eqxx //.
    by rewrite Ed1 scale1r.
  rewrite mujE [tau _]raddfD raddf_sum /= -/tau (eq_bigr f) // /f.
  rewrite Etau !sumrB  [X in X = _]addrC -!addrA; congr (_ + _).
  rewrite -opprB -opprD -opprB; congr (- _).
  rewrite !addrA opprK subrK.
  rewrite sumr_const nirrW1 -scaler_nat scalerA mulrC.
  by rewrite divfK ?neq0CG // Ed1  scalerBl scale1r subrK.
case: FTtype34_noncoherence.
have [_ _ ->] := FTtype34_Fcore_kernel_trivial .
rewrite /= (group_inj (joing1G _)).
have /perm_eq_coherent: perm_eq (SC ++ S_ HC) (S_ C); last apply.
  apply: uniq_perm_eq; rewrite ?cat_uniq ?seqInd_uniq ?andbT //=.
    exact/hasPn/SHCdSC.
  move=> xi; rewrite mem_cat.
  apply/idP/idP=> [/orP[]|].
  - by apply: (seqIndS (Iirr_kerDS _ _ _)).
  - by apply: (seqIndS (Iirr_kerDS _ (joing_subr _ _) _)).
  case/seqIndP => i HI->; rewrite !mem_seqInd // inE [X in _ || X]inE.
  by move: HI; rewrite inE => /andP[-> ->]; case: (_ \in _).
suffices [tau2 co_w_tau_tau2 Etau2] : 
  exists2 tau2, coherent_with SC M^# tau tau2 & tau2 (mu_ j) = \sum_i eta_ i j.
- rewrite -Etau2 -raddfZnat in tmujE.
  pose bc := bridge_coherent scohM.
  apply: bc tmujE => //; try by apply: seqInd_conjC_subset1.
  have S1n_muj: mu_ j \in S1nirr by rewrite S1nirr_i_Smu map_f // mem_enum.
  split.
  + by move: S1n_muj; rewrite S1nirr_i_Smu Smu_i_SCnirr mem_filter => /andP[].
  + by apply: scale_zchar; [apply: Cint_Cnat | apply: mem_zchar].
  rewrite mujE cfunD1E !cfunE (SHC1 SHCz).
  rewrite prTIred0 !cfunE cfuniE // group1 mulr1 subrr add0r.
  rewrite sum_cfunE big1 // => i _.
  apply/eqP; rewrite -cfunD1E.
  by apply: cfun_onS (FTsupp0_sub _) (cf_alpha _ _ _).
have [/all_filterP Ef|/allPn[x SCx irrx]] := boolP (all [predC irr M] SC).
  have [_ [tau2 Dtau2 [Ztau2 Ctau2]]] := uniform_prTIred_coherent pddM nz_j.
  have sSC_unif : {subset SC <= uniform_prTIred_seq pddM j}.
    move=> mu_k; rewrite -Ef mem_filter !inE => /andP[kNirr kIS2].
    have: mu_k \in S1nirr
      by rewrite S1nirr_i_Smu Smu_i_SCnirr mem_filter [X in X && _]kNirr.
    rewrite S1nirr_i_Smu; case/imageP=> k nz_k ->.
    by rewrite image_f // !inE [_ != 0]nz_k /= !mu1.
  exists tau2.
    split=> [|k /(zchar_subset sSC_unif)/Ctau2 //].
    by apply:  sub_iso_to (zchar_subset _) _ Ztau2.
  have [_ /(_ _ nz_j) Ez _ _] := FTtype345_constants maxM MtypeP notMtype2.
  by rewrite -[X in _ = X]scale1r -Ed1 -Ez -Dtau2.
move: irrx SCx; rewrite negbK => /irrP[{x}  i -> SCi].
have /CnatP[n chi1En] := Cnat_irr1 i.
have SCmuj : mu_ j \in SC.
  have: mu_ j \in Smu by apply: image_f; exact: nz_j.
  by rewrite Smu_i_SCnirr mem_filter => /andP[].
have [tau2 co_w_tau_tau2] : coherent SC M^# tau.
  rewrite /SC -(_ : (C <*> H)%G = HC) ?seqIndDY //=; last first.
    by apply/group_inj/dprodWY; rewrite -defHC dprodC.
  apply: subset_coherent (Ptype_core_coherence maxM MtypeP notMtype5).
  apply: seqIndS (Iirr_kerDS _ _ _)=> //.
  have [_ _ /group_inj->] := FTtype34_Fcore_kernel_trivial .
  by rewrite (group_inj (joing1G _)) (group_inj Ptype_Fcompl_kernel_cent) der_sub.
exists tau2=> //.
pose xx := 'chi_ i 1%g *: mu_ j - mu_ j 1%g *: 'chi_ i.
have cf_xx : xx \in 'CF(M, HU^#).
  rewrite cfun_onD1 ?cfunE ?1mulrC ?subrr ?eqxx //.
  by rewrite rpredB ?rpredZ  ?(seqInd_on _ SCi) ?(seqInd_on _ SCmuj).
pose yy := mu_ j - d%:R *: z.
have sHU_A0 :  HU^# \subset 'A0(M) by rewrite defA0 subsetUl.
have cf_yy : yy \in 'CF(M, HU^#).
  rewrite cfun_onD1 ?rpredB ?rpredZ ?(seqInd_on _ SHCz) ?(seqInd_on _ SCmuj) //.
  by rewrite !cfunE (SHC1 SHCz) mu1 // Edu mulrC natrM subrr eqxx.
have: '[tau xx, tau yy] != 0.
  rewrite Dade_isometry ?(cfun_onS sHU_A0) //.
  rewrite cfdotBl !cfdotBr !cfdotZl !cfdotZr cfnorm_prTIred omu //. 
  rewrite  !mulr0 subr0 (seqInd_ortho _ _ SCmuj) ?mulr0 ?sub0r //; last first.
    by apply: contra (prTIred_not_irr ptiWM j) => /eqP<-; exact: mem_irr.
  rewrite (seqInd_ortho nsHUM (seqInd_subT SCi) (seqInd_subT SHCz)) //.
    by rewrite !mulr0 oppr0 subr0 mulf_neq0 ?irr1_neq0 // -/q natrG_neq0.
  by apply: contra (SHCdSC SHCz)=> /eqP<-.
have [Ztau2 Ctau2] := co_w_tau_tau2.
have /orthogonalP cfdot_map_SC_SHC :
              orthogonal (map tau2 SC) (map tau1 (S_ HC)).
  by apply: (coherent_ortho scohM)=> //; apply: seqInd_conjC_subset1.
rewrite -[tau xx]Ctau2 ?tmujE /=; last first.
  rewrite zcharD1E; move: cf_xx; rewrite cfun_onD1 => /andP[_ ->].
  by rewrite rpredB // scale_zchar ?mem_zchar ?mu1 ?chi1En ?Cint_Cnat.
rewrite cfdotBr cfdotZr {2}[tau2 xx]raddfB cfdotBl chi1En mu1 // !raddfZnat //.
rewrite !cfdotZl !['[_,tau1 _]]cfdot_map_SC_SHC ?map_f //.
rewrite !(mulr0, subr0) raddfB chi1En mu1 // cfdotBl !raddfZnat !cfdotZl.
rewrite ['[tau2 'chi_ i, _]]cfdot_sumr.
rewrite [in X in _- X != 0 -> _]big1 ?mulr0 ?subr0 => [|k _]; last first.
  apply: (coherent_ortho_cycTIiso _ _ co_w_tau_tau2); rewrite ?mem_irr //.
  by rewrite (group_inj defMs); apply: seqInd_conjC_subset1.
have [|[b k] ->[[-> ->]|[-> -> _]]] // :=
     FTtypeP_coherent_TIred _ co_w_tau_tau2 (mem_irr _) SCi SCmuj.
- by apply: seqInd_conjC_subset1; rewrite (group_inj defMs).
- have [_ /(_ _ nz_j)-> _ _] := FTtype345_constants maxM MtypeP notMtype2.
  by rewrite Ed1 scale1r.
case/eqP; rewrite cfdotZl cfdot_suml big1 ?mulr0 // => k1 _.
rewrite cfdot_sumr big1 ?mulr0 // => k2 _.
rewrite cfdot_cycTIiso.
case: (boolP (_ == j))=> [/eqP Cjj|]; last by rewrite andbF.
suffices /eqP[] : (mu_ j)^*%CF != mu_ j.
  by rewrite -prTIred_aut /aut_Iirr -conjC_IirrE Cjj irrK.
by apply: seqInd_conjC_neq SCmuj; rewrite  ?mFT_odd //.
Qed.

Implicit Types r : {rmorphism algC -> algC}.

(* This is PF (11.9). *)
Lemma FTtype34_structure :
  [/\ (*a*) {in S_ HC, forall z : 'CF(M),
             orthogonal (tau (mu_ 0 - z) - \sum_j eta_ 0 j) etaW},
      (*b*) (p < q)%N
    & (*c*) FTtype M == 3 /\ typeP_Galois MtypeP].
Proof. 
have oXeta : {in S_ HC, forall z,
             orthogonal (tau (mu_ 0 - z) - \sum_j eta_ 0 j) etaW}.
  move=>  z SHCz; move: (SHCz).
  have /irrP[iz ->] := SHC_irr SHCz => {z SHCz}SHCz.
  pose z := 'chi_iz; set psi := mu_ 0 - z.
  pose Wsig := map sigma (irr W).
  have [X wsigX [chi [tau_XDchi oX_chi oX]]] := orthogonal_split Wsig (tau psi).
  have [Isigma Zsigma] := cycTI_Zisometry ctiWG.
  have ochi_eta i j : '[chi, eta_ i j] = 0.
    by rewrite (orthoPl oX) ?map_f ?mem_irr.
  have onWsig : orthonormal Wsig by rewrite map_orthonormal ?irr_orthonormal.
  have [a_ Da defX] := orthonormal_span onWsig wsigX.
  have{Da} Da i j : a_ (eta_ i j) = '[tau psi, eta_ i j].
    by rewrite tau_XDchi cfdotDl ochi_eta addr0 Da.
  have eX : X = \sum_i \sum_j a_ (eta_ i j) *: eta_ i j.
    rewrite pair_bigA defX big_map (big_nth 0) size_tuple big_mkord /=.
    rewrite (reindex (dprod_Iirr defW)) /=.
      by apply: eq_bigr => [[i j] /= _]; rewrite -tnth_nth.
    exists (inv_dprod_Iirr defW) => ij; first by rewrite dprod_IirrK.
    by rewrite inv_dprod_IirrK.
  have irr_psi : psi \in 'Z[irr M, HU^#].
    rewrite zchar_split // rpredB  ?irr_vchar //; last first.
      by rewrite rpred_sum // => i _; apply: irr_vchar.
    rewrite cfun_onD1 ?rpredB ?cfunE ?prTIred0 ?(seqInd_on _ SHCz) //.
      by rewrite (SHC1 SHCz) cfunE cfuniE //= group1 mulr1 subrr.
    by rewrite rpredZ // cfuni_on.
  have cf_psi : psi \in 'CF(M, 'A0(M)).
    by apply: cfun_onS (zchar_on irr_psi); rewrite defA0 subsetUl.
  have a00_1 : a_ (eta_ 0 0) = 1.
    rewrite Da [w_ 0 0](cycTIirr00 defW) [sigma 1]cycTIiso1.
    rewrite Dade_reciprocity // => [|x _ y _]; last by rewrite !cfun1E !inE.
    rewrite rmorph1 /= -(prTIirr00 ptiWM) -/(mu2_ 0 0) cfdotC.
    by rewrite cfdotBr cfdot_prTIirr_red omu2 // subr0 rmorph1.
  have aPsi r : cfAut r (tau psi) = tau psi + tau (z - cfAut r z).
    rewrite -Dade_aut !rmorphB !raddfB /= !addrA subrK.
    by rewrite -prTIred_aut aut_Iirr0.
  have aijCint i j : a_ (eta_ i j) \in Cint.
    rewrite Da Cint_cfdot_vchar ?cycTIiso_vchar ?Dade_vchar //.
    by apply: zchar_onS irr_psi; rewrite defA0 subsetUl.
  have aijE i j : a_ (eta_ i j) = '[X, eta_ i j].
    by rewrite Da tau_XDchi cfdotDl ochi_eta addr0.
  have cfAut_a r i j : a_ (cfAut r (eta_ i j)) = a_ (eta_ i j).
    have S1z: z \in S_ 1 by rewrite (seqIndS _ SHCz) ?Iirr_kerDS ?sub1G.
    have S1rz: cfAut r z \in S_ 1 by rewrite cfAut_seqInd.
    have rz1: z 1%g == cfAut r z 1%g by rewrite cfAut_char1 ?(seqInd_char S1z).
    have [S2 [S2z S2rz sS21] []] := pair_degree_coherence scohM S1z S1rz rz1.
    move=> tau2 cohS2; have [_ Dtau2] := cohS2.
    rewrite -{2}(group_inj defMs) in sS21.
    have otau2 := coherent_ortho_cycTIiso MtypeP sS21 cohS2.
    transitivity '[cfAut r (tau psi), cfAut r (eta_ i j)]; last first.
      rewrite -(aut_Cint r (aijCint i j)) Da.
      have /dirrP[i1 [b ->]] := cycTIiso_dirr ctiWG i j.
      by rewrite linearZ !cfdotZr rmorphM !rmorph_sign cfdot_aut_irr.
    rewrite aPsi cfdotDl cfAut_cycTIiso -cycTIirr_aut.
    rewrite tau_XDchi cfdotDl ochi_eta addr0 -aijE.
    have ->: tau (z - cfAut r z) = tau2 z - tau2 (cfAut r z).
      rewrite -Dtau2 ?raddfB // zcharD1E 2!cfunE subr_eq0 rz1 andbT.
      by rewrite rpredB ?mem_zchar.
    by rewrite cfdotBl !otau2 ?subrr ?addr0 // ?cfAut_irr ?mem_irr.
  have nz_1i : #1 != 0 :> Iirr W1 by rewrite Iirr1_neq0.
  have nz_1j : #1 != 0 :> Iirr W2 by rewrite Iirr1_neq0.
  have aiE i (nz_i : i != 0) : a_ (eta_ i 0) = a_ (eta_ #1 0).
    have [k co_k_i1 Di] := cfExp_prime_transitive (pr_q) nz_1i nz_i.
    rewrite -(cforder_dprodl defW) -dprod_IirrEl in co_k_i1.
    have{co_k_i1} [[r Di1r] _] := cycTIiso_aut_exists ctiWG co_k_i1.
    rewrite dprod_IirrEl -rmorphX -Di /= -!dprod_IirrEl -!/(w_ _ _) in Di1r.
    by rewrite Di1r  cfAut_a.
  have ajE j (nz_j : j != 0) : a_ (eta_ 0 j) = a_ (eta_ 0 #1).
    have [k co_k_j1 Dj] := cfExp_prime_transitive (pr_p) nz_1j nz_j.
    rewrite -(cforder_dprodr defW) -dprod_IirrEr in co_k_j1.
    have{co_k_j1} [[r Dj1r] _] := cycTIiso_aut_exists ctiWG co_k_j1.
    rewrite dprod_IirrEr -rmorphX -Dj /= -!dprod_IirrEr -!/(w_ _ _) in Dj1r.
    by rewrite Dj1r  cfAut_a.
  have aijnz_E i j (nz_i : i != 0) (nz_j : j != 0) :
      a_ (eta_ i j) = a_ (eta_ i 0) + a_ (eta_ 0 j) - a_ (eta_ 0 0).
    apply: (addIr (a_ (eta_ 0 0))); rewrite subrK !Da.
    apply: cycTIiso_cfdot_exchange => x Vx /=.
    rewrite Dade_id ?defA0; last by rewrite inE orbC mem_class_support.
    rewrite (cfun_on0 (zchar_on irr_psi)) // -defA.
    suffices /setDP[] : x \in 'A0(M) :\: 'A(M) by [].
    by rewrite (FTsupp0_typeP maxM MtypeP) // mem_class_support.
  have normX : '[X] = 1 + q.-1%:R * a_(eta_ #1 0) ^+ 2 
                        + p.-1%:R * a_(eta_ 0 #1) ^+ 2
                        + p.-1%:R * q.-1%:R * a_ (eta_ #1 #1) ^+ 2.
    have -> : '[X] = \sum_i \sum_j a_(eta_ i j)^+2.
      rewrite defX cfnorm_sum_orthonormal //.
      rewrite pair_bigA big_map (big_nth 0) size_tuple big_mkord /=.
      rewrite (reindex (dprod_Iirr defW)) /=.
        apply: eq_bigr => [[i j] /= _]; rewrite -tnth_nth.
        by rewrite Cint_normK // aijCint.
      exists (inv_dprod_Iirr defW) => ij; first by rewrite dprod_IirrK.
      by rewrite inv_dprod_IirrK.
    pose cD := cardD1 0.
    have pm1E : p.-1 = #|[predD1 Iirr W2 & 0]| by rewrite -nirrW2 cD inE.
    have qm1E : q.-1 = #|[predD1 Iirr W1 & 0]| by rewrite -nirrW1 cD inE.
    rewrite (bigD1 0) //= (bigD1 0) //=.
    rewrite (eq_bigr (fun i => a_ (eta_ 0 #1) ^+ 2)); last first.
      by move=> j nz_j; rewrite ajE.
    rewrite sumr_const (@eq_card _ _ [predD1 Iirr W2 & 0]); last first.
      by move=> i /=; rewrite !inE andbT /in_mem /=; case: (_ == _).
    rewrite -pm1E mulr_natl.
    pose f i := a_ (eta_ #1 0) ^+ 2 + p.-1%:R * a_ (eta_ #1 #1) ^+ 2.
    rewrite (eq_bigr (f _))=> [|i nz_i]; last first.
      rewrite (bigD1 0) ?aiE //=; congr (_ + _).
      rewrite (eq_bigr (fun _ => a_ (eta_ #1 #1) ^+ 2))=> [|j nz_j]; last first.
        rewrite (aijnz_E _ _ nz_i nz_j).
        rewrite [in X in _ = X](aijnz_E _ _ nz_1i nz_1j).
        by rewrite aiE // ajE.
      rewrite sumr_const (@eq_card _ _ [predD1 Iirr W2 & 0]); last first.
        by move=> i1 /=; rewrite !inE andbT /in_mem /=; case: (_ == _).
      by rewrite -pm1E mulr_natl.
    rewrite /f /= sumr_const (@eq_card _ _ [predD1 Iirr W1 & 0]); last first.
      by move=> i /=; rewrite !inE andbT /in_mem /=; case: (_ == _).
    rewrite -qm1E !mulr_natl mulrnDl !addrA; congr (_ + _).
      by rewrite addrAC a00_1 expr1n.
    by rewrite -!mulrnA mulnC mulr_natl.
  have normX_le_q : '[X] <= q%:R.
     have En : '[tau psi] = '[X] + '[chi] by rewrite tau_XDchi cfnormDd.
     have Eq : '[tau psi] = q%:R + 1.
       rewrite Dade_isometry ?cf_mu0Bz // cfnormDd.
         by rewrite cfnorm_prTIred cfnormN cfdot_SHC // eqxx.
       by rewrite cfdotNr omu ?oppr0.
    rewrite -(ler_add2r '[chi]) -En Eq ler_add2l.
     suff: '[chi] != 0.
       suff /CnatP[nc->] : '[chi] \in Cnat.
         by rewrite (ler_nat _ 1%N) (eqr_nat _ _ 0%N); case: nc.
       rewrite CnatEint cfnorm_ge0 andbT.
       have-> : '[chi] = '[tau psi] - '[X] .
         by rewrite En ['[X] + _]addrC addrK.
       rewrite rpredB ?Eq ?rpredD  ?Cint_Cnat //.
       rewrite defX cfdot_sum_orthonormal //.
       rewrite big_seq_cond rpred_sum // => i.
       rewrite andbT => /mapP[x /(cycTIirrP defW)[i1 [j1 ->]]->].
       rewrite conj_Cint ?aijCint //.
       by apply: (@Cnat_exp_even (a_ _) 2%N).
    have: '[tau psi, tau (z - z^*%CF)] != 0.
      rewrite Dade_isometry=> //.
         rewrite !cfdotBl !cfdotBr ?omu ?cfAut_seqInd //.
         rewrite cfnorm_irr -conjC_IirrE cfdot_irr.
         rewrite [iz == _]eq_sym -(inj_eq irr_inj) conjC_IirrE.
         rewrite (negPf (seqInd_conjC_neq _ _ _ SHCz)) ?mFT_odd //.
         by rewrite !subr0 sub0r oppr_eq0 oner_neq0.
      have cf_SHC : {subset S_ HC <= 'CF(M, HU)}.
        by apply: (seqInd_on (der_normal 1 _)).
      apply: (cfun_onS (subsetUl _ _))=> //.
      rewrite defA cfun_onD1 rpredB ?cf_SHC ?cfAut_seqInd ?mem_zchar //.
      by rewrite !cfunE irr1_degree ?rmorph_nat subrr eqxx.
    rewrite cfnorm_eq0 tau_XDchi; apply: contra=> /eqP->; rewrite addr0.
    have[tau1 co_w_SHC] := cohHC; have [[Ztau1 Ptau1] Ctau1] := co_w_SHC.
    rewrite -Ctau1 ?raddfB /=; last first.
      rewrite  zcharD1 2!cfunE !SHC1 ?cfAut_seqInd ?subrr ?eqxx //.
      by rewrite zchar_onG rpredB // mem_zchar // cfAut_seqInd.
    suff oX_tau1 : {in S_ HC, forall x : 'CF(M), '[X, tau1 x] = 0}.
        by rewrite !oX_tau1 ?cfAut_seqInd // subrr.
    move=> x SHCx; rewrite /= cfdotC defX cfdot_sumr big_seq_cond.
    pose cirrP := cycTIirrP defW.
    pose otau1 := coherent_ortho_cycTIiso _ _ co_w_SHC.
    rewrite big1 ?conjC0 // => i /andP[/mapP[y /cirrP[i1 [j1 ->]]->] _] //.
    rewrite cfdotZr /= otau1 ?SHC_irr ?mulr0 //.
    by apply seqInd_conjC_subset1=> //=; rewrite ?defMs.
  have even2 : ~~ odd 2 by [].
  have sqrt_a_ge0 i j : 0 <= a_ (eta_ i j) ^+ 2.
     have /CnatP[na->] := Cnat_exp_even even2 (aijCint i j).
     by apply: ler0n.
  have [/eqP a11_0|nz_a11] := boolP (a_ (eta_ #1 #1) == 0); last first.
    suff /ler_trans/(_ normX_le_q) : '[X] >= (2 * q.-1)%:R.
      rewrite ler_nat leqNgt=> /negP[].
      case: q pr_q (mFT_odd W1 : odd q)=>  [|[|[|q1]]] // _ _.
      by rewrite mulSn mul1n addnS -addSn -addn1 leq_add2l.
    rewrite normX ler_paddl ?addr_ge0 ?[0 <= _%:R * _]mulr_ge0 ?ler0n ?Pa //.
      by apply: (ler0n _ 1%N).
    have: a_ (eta_ #1 #1) ^+ 2 != 0.
      by apply: contra nz_a11; rewrite mulf_eq0 => [/orP[]].
    have/CnatP[na->] := Cnat_exp_even even2 (aijCint #1 #1).
    rewrite -!natrM ler_nat (eqr_nat _ _ 0%N); case: na=> // na _.
    rewrite -[(2 * _)%N]muln1 !leq_mul //.
    by case: p pr_p (mFT_odd W2 : odd p)=> [|[|[|]]] //= _.
  rewrite a11_0 expr0n /= mulr0 addr0 in normX.
  have [/eqP a10_0|nz_a10] := boolP (a_ (eta_ #1 0) == 0); last first.
    have /ler_trans/(_ normX_le_q) : 
          '[X] >= q%:R + (p.-1)%:R  * a_ (eta_ 0 #1) ^+ 2.
      rewrite normX ler_add2r.
      have: a_ (eta_ #1 0) ^+ 2 != 0.
        by apply: contra nz_a10; rewrite mulf_eq0 => [/orP[]].
      have/CnatP[na->] := Cnat_exp_even even2 (aijCint #1 0).
      rewrite -!natrM -(natrD _ 1%N) ler_nat (eqr_nat _ _ 0%N).
      case: na=> // na _.
      rewrite mulnS addnA add1n; case: q pr_q => // q1 _.
      by apply: leq_addr.
    rewrite ger_addl pmulr_rle0=> [sqr_a10_le_0|]; last first.
      by rewrite (ltr_nat _ 0); case: p pr_p => [|[|]].
    have sqr_a01_0 : a_ (eta_ 0 #1) ^+ 2 == 0.
      have/CnatP[na naE] := Cnat_exp_even even2 (aijCint 0 #1).
      by move: sqr_a10_le_0; rewrite {}naE (ler_nat _ _ 0); case: na.
    have a01_0 :  a_ (eta_ 0 #1) = 0.
      by move: sqr_a01_0; rewrite mulf_eq0 => [/orP[]/eqP].
    have a10_1 : a_ (eta_ #1 0) = 1.
      have := aijnz_E _ _ nz_1i nz_1j.
      rewrite  a11_0 a01_0 a00_1 addr0.
      by move/eqP; rewrite eq_sym subr_eq add0r => /eqP.
    suff X_is_sum : X = \sum_i eta_ i 0.
      have /negP[] := FTtype34_not_ortho_cycTIiso SHCz.
      by rewrite -/psi tau_XDchi -X_is_sum [X + _]addrC addrK.
    rewrite eX; apply: eq_bigr=> i _.
    have[/eqP->|nz_i] := boolP (i == 0).
      rewrite (bigD1 0) //= big1 ?addr0 ?a00_1 ?scale1r // => j nz_j.
      by rewrite ajE // a01_0 scale0r.
      rewrite (bigD1 0) //= big1 => [|j nz_j].
        by rewrite addr0 aiE // a10_1 scale1r.
      rewrite aijnz_E // aiE // ajE // a01_0 a10_1 a00_1.
      by rewrite addr0 subrr scale0r.
  have a01_1 : a_ (eta_ 0 #1) = 1.
    have := aijnz_E _ _ nz_1i nz_1j.
    rewrite  a11_0 a10_0 a00_1 add0r.
    by move/eqP; rewrite eq_sym subr_eq add0r => /eqP.
  have <- : X = \sum_j eta_ 0 j.
    rewrite eX (bigD1 0) //=  [X in _ + X = _]big1 => [|i nz_i].
      rewrite addr0; apply: eq_bigr => i _.
      by have [/eqP->|nz_i] := boolP (i == 0);
        rewrite ?a00_1 ?ajE // ?a01_1 scale1r.
    apply: big1 => j _; have [/eqP->|nz_j] := boolP (j == 0).
      by rewrite aiE // a10_0 scale0r.
    rewrite aijnz_E // aiE // ajE // -(aijnz_E _ _ nz_1i nz_1j).
    by rewrite a11_0 scale0r.
  by rewrite tau_XDchi [X + _]addrC addrK.
have [z SHCz] : exists z, z \in S_ HC.
  have ntHU : HU :!=: 1%g by rewrite -defMs FTcore_neq1.
  have sol_HU := solvableS (der_subS 0 _) (of_typeP_sol MtypeP).
  have [i lin_i nzi] := solvable_has_lin_char ntHU sol_HU.
  exists ('Ind 'chi_i); rewrite mem_seqInd -?defM'' ?gFnormal // !inE.
  by rewrite subGcfker -irr_eq1 nzi lin_char_der1.
move: (SHCz); have /irrP[iz ->] := SHC_irr SHCz => {z SHCz}SHCz.
pose z := 'chi_iz.
have pLq : (p < q)%N.
  have S1z : z \in  S_ 1 by apply: (seqIndS (Iirr_kerDS _ (sub1G _) _) SHCz).
  have [//|qLp|pEq] :=  ltngtP p q; last first.
    have: coprime q p by rewrite -(cyclic_dprod defW); have [] := ctiWM.
    by rewrite pEq /coprime gcdnn; case: q pr_q => [|[|]].
  have /negP[] := FTtype34_not_ortho_cycTIiso SHCz.
  have [chi [chiE _ _ ochi_eta]] :=   
    FTtype345_Dade_bridge0 maxM MtypeP notMtype2 (mem_irr _) S1z (SHC1 SHCz) qLp.
  rewrite /(mu_ _) /ptiWM /= chiE addrAC subrr sub0r.
  apply/orthogonalP=> i oi.
  rewrite inE => /eqP-> /mapP[x /(cycTIirrP defW)[i1 [j1 ->]]->].
  by rewrite cfdotNl ochi_eta oppr0.
have [Gal|NGal] := boolP (typeP_Galois MtypeP).
  have [F [phi _ _ [cyUbar _ _]]] := typeP_Galois_P maxM notMtype5 Gal.
  have [_ _ _ CeU'] := FTtype34_facts.
  rewrite Ptype_Fcompl_kernel_cent (group_inj CeU') in cyUbar.
  have [_ [nilU _ _ _] _ _ _] := MtypeP.
  move: Mtype34; rewrite inE => /orP[->|] // /(compl_of_typeIV maxM MtypeP).
  case=> _ /negP[]; apply: cyclic_abelian.
  by apply: cyclic_nilpotent_quo_der1_cyclic.
split=> //.
have [_ _ _ U'eC] := FTtype34_facts.
have [pAbH cardH trivH0] := FTtype34_Fcore_kernel_trivial.
have [Ha [sSHH0 Hb] _] := typeP_nonGalois_characters maxM notMtype5 NGal.
case: (_ NGal) Ha => 
    H1 /= [divH1 NH1 actH1 sumH1 [a_gt1 aDiv cyclU [V1 isoV1]]] Ha.
have cHH0 : pdiv #|(`H / H0)%g| = p.
  rewrite trivH0 -(card_isog (quotient1_isog _)) cardH.
  by case: q pr_q => // q1 _; rewrite pdiv_pfactor.
rewrite {}cHH0 in divH1 aDiv Ha *.
set U1 := 'C_U(H1 | 'Q) in a_gt1 aDiv Ha *.
set a := #|U : U1| in a_gt1 aDiv Ha *.
set irr_qa := [pred _ | _]; set lb_n := (_.-1 * #|_|)%N; set lb_d := (_ * _)%N.
case=> dLbdLbn countIrr_qa.
have/leq_trans/(_ countIrr_qa) : (0 < lb_n %/ lb_d)%N.
  by rewrite divn_gt0 dvdn_leq // !muln_gt0 ?cardG_gt0 
             ?(ltn_trans (ltn0Sn _) a_gt1) //; case: p pr_p => [|[|]] //.
rewrite -has_count => /hasP[xj SH0Cxj] .
rewrite inE -/q => /andP[/irrP[ib def_ib] lamb1].
rewrite {xj}def_ib in SH0Cxj lamb1.
set lamb := 'chi_ib in lamb1 SH0Cxj.
have [j nz_j] := has_nonprincipal_irr ntW2.
have: mu_ j \in Smu by apply: map_f; rewrite mem_enum.
rewrite -S1nirr_i_Smu => /Hb .
rewrite  trivH0 (group_inj (joing1G _)).
rewrite Ptype_Fcompl_kernel_cent /= -/q -/u.
rewrite (group_inj Ptype_Fcompl_kernel_cent)=> [[muj1 SCHmuj exMuj]].
have HC_swap : HC = (C <*> H)%G.
   by apply/sym_equal/group_inj/dprodWY; rewrite -defHC dprodC.
have [tau2 co_w_tau2] : coherent SC M^# tau.
  rewrite /SC HC_swap ?seqIndDY //=.
  apply: subset_coherent (Ptype_core_coherence maxM MtypeP notMtype5).
  apply: seqIndS (Iirr_kerDS _ _ _)=> //.
  have [_ _ /group_inj->] := FTtype34_Fcore_kernel_trivial .
  by rewrite (group_inj (joing1G _)) (group_inj Ptype_Fcompl_kernel_cent) der_sub.
have SClamb : lamb \in SC.
  rewrite /SC HC_swap ?seqIndDY //.
  by rewrite  trivH0 (group_inj (joing1G _)) -(group_inj U'eC) in SH0Cxj.
have SCmuj : mu_ j \in SC by rewrite /SC HC_swap ?seqIndDY.
have cfConj_SC : cfConjC_subset SC (seqIndD HU M M`_\s 1).
  by apply: seqInd_conjC_subset1; rewrite (group_inj defMs).
have [[b k] /=] := FTtypeP_coherent_TIred  cfConj_SC co_w_tau2 (mem_irr _) SClamb SCmuj.
rewrite -[primeTIred _ _]/(mu_ j) => Etau2muj Cbk.
pose psi := mu_ j - (u %/ a)%:R *: lamb.
have aDu : a %| u.
  case/seqIndP: SCHmuj muj1=> i iIkerD ->.
  have/eqP := Lagrange sHUM.
  rewrite cfInd1 // -(sdprod_card defM) eqn_mul2l.
  rewrite (negPf (lt0n_neq0 (cardG_gt0 HU))) /= => /eqP-> /eqP.
  have: (a %| 'chi_i 1%g)%C.
    apply/Ha/(subsetP (Iirr_kerDS _ _ _) _ iIkerD)=> //.
    by rewrite trivH0 sub1G.
  have a_ge0 : 0 <= a%:R :> algC by rewrite (ler_nat _ 0%N a).
  case/(dvdCP_nat a_ge0 (char1_ge0 (irr_char i)))=> nc ->.
  rewrite -!natrM eqr_nat eqn_mul2l.
  rewrite (negPf (lt0n_neq0 (cardG_gt0 W1)))=> /= /eqP<-.
  by rewrite dvdn_mull // divnn.
have psi1 : psi 1%g == 0.
  rewrite !cfunE muj1 (eqP lamb1).
  rewrite subr_eq0 /= -natrM eqr_nat  [(_ * a)%N]mulnC.
  by rewrite mulnA divnK // [(q * _)%N]mulnC.
have: '[tau (mu_ 0 - z), tau psi] = 0.
  have irr_psi : psi \in 'Z[irr M, HU^#]. 
    rewrite zchar_split // rpredB.
    - rewrite cfun_onD1 psi1 rpredB ?(seqInd_on _ SCmuj) //.
      by apply/rpredZ/(seqInd_on _ SClamb).
    - by rewrite rpred_sum // => i _; apply: irr_vchar.
    by rewrite scale_zchar ?mem_zchar ?Cint_Cnat // mem_irr.
  rewrite Dade_isometry ?cf_mu0Bz //; last first.
    by apply: cfun_onS (zchar_on irr_psi); rewrite defA0 subsetUl.
  rewrite cfdotBl !cfdotBr !cfdotZr cfdot_prTIred.
  rewrite [0 == _]eq_sym (negPf nz_j) sub0r cfdot_irr.
  case: (_ =P _)=> [Ezb|_]; rewrite ?mulr0 ?subr0.
    by move: (SHCdSC SHCz); rewrite !inE Ezb => /negP[].
  rewrite ['[z, _]]cfdotC  ['[_, z]]omu // ?conjC0 subr0.
  suff -> : '[mu_ 0, lamb] = 0  by rewrite mulr0 oppr0.
  have Tmu0 : mu_ 0 \in seqIndT HU M.
    by rewrite -[mu_ 0]cfInd_prTIres mem_seqIndT.
  rewrite (seqInd_ortho _ Tmu0 (seqInd_subT SClamb)) // /lamb.
  by apply: contraTneq (mem_irr ib) => <-; apply: prTIred_not_irr.
pose chi : 'CF(G) := tau (mu_ 0 - z) - \sum_j eta_ 0 j.
have chiE : tau (mu_ 0 - z) = \sum_j eta_ 0 j + chi.
  by rewrite [X in _ = X]addrC subrK.
have ochi_eta : orthogonal chi etaW := oXeta _ SHCz.
have [Ztau2 Ctau2] := co_w_tau2.
rewrite chiE -Ctau2; last first.
  rewrite  zcharD1 psi1 zchar_onG rpredB // ?scale_zchar ?mem_zchar //.
  by rewrite Cint_Cnat.
rewrite raddfB Etau2muj raddfZnat cfdotDl !cfdotBr !cfdotZr.
rewrite cfdot_suml (bigD1 k) //=  cfdot_sumr (bigD1 0) //=. 
rewrite cfdot_cycTIiso !eqxx /= big1 ?addr0=> [|i nz_i]; last first.
  by rewrite cfdot_cycTIiso [0 == _]eq_sym (negPf nz_i).
rewrite big1 ?addr0=> [|i nz_i]; last first.
rewrite cfdot_sumr big1 // => i1 nz_i1.
  by rewrite cfdot_cycTIiso  (negPf nz_i) andbF.
rewrite cfdotC cfdot_sumr big1 ?mulr0 ?subr0=> [|i _]; last first.
  apply: (coherent_ortho_cycTIiso _ _ co_w_tau2); rewrite ?mem_irr //.
rewrite conjC0 mulr0 subr0 mulr1.
rewrite cfdot_sumr big1 ?mulr0 ?addr0 => [|i _]; last first.
  by rewrite (orthoPl ochi_eta) ?map_f ?mem_irr.
rewrite sub0r conjC_nat rmorph_sign => /(canRL (subrK _))/(congr1 Num.norm).
case/esym/eqP/idPn; rewrite add0r normrM normr_sign normr_nat.
rewrite Cnat_mul_eq1 ?rpred_nat ?Cnat_norm_Cint //; last first.
  rewrite Cint_cfdot_vchar //.
    rewrite rpredB ?rpred_sum // => [|j1 _]; last exact: cycTIiso_vchar.
    rewrite Dade_vchar // zchar_split cf_mu0Bz // rpredB ?irr_vchar //.
    by rewrite char_vchar // prTIred_char.
  by have [[_ ->//]] := co_w_tau2; apply: mem_zchar.
rewrite pnatr_eq1 -eqn_mul ?indexg_gt0 // mul1n gtn_eqF //.
have ltqu : (q < u)%N.
  have ugt1 : (1 < u)%N 
    by rewrite cardG_gt1; case/Frobenius_context: frobUW1bar.
  rewrite -(subnKC ugt1) addSn ltnS dvdn_leq // addnBA // subSS subn1 /q.
  have nCW1 : W1 \subset 'N(C) by apply: subset_trans (joing_subr _ _) nC_UW1.
  have tiCW1: C :&: W1 = 1%g by rewrite coprime_TIg ?(coprimeSg (subsetIl U _)).
  rewrite (card_isog (quotient_isog nCW1 tiCW1)).
  exact: Frobenius_dvd_ker1 frobUW1bar.
suffices /ltn_trans/(_ (ltn_trans pLq ltqu)): (a < p)%N by [].
rewrite -(prednK (prime_gt0 pr_p)) ltnS dvdn_leq //.
by rewrite -(subnKC (prime_gt1 pr_p)).
Qed.

End Eleven.
