(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator gseries nilpotent.
Require Import sylow abelian maximal hall.
Require Import matrix mxalgebra mxrepresentation vector algC.
Require Import classfun character frobenius inertia vcharacter integral_char. 
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 6:                                    *)
(* Some Coherence Theorems                                                    *)
(* Defined here:                                                              *)
(*   odd_Frobenius_quotient K L M <->                                         *)
(*      L has odd order, M <| L, K with K / M is nilpotent, and L / H1 is a   *)
(*      Frobenius group with kernel K / H1, where H1 / M = (K / M)^(1).       *)
(*      This is the statement of Peterfalvi, Hypothesis (6.4), except for     *)
(*      the K <| L and subcoherence assumptions, to be required separately.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* The main section *)
Section Six.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types H K L M : {group gT}.

(* Grouping lemmas that assume Hypothesis (6.1). *)
Section GeneralCoherence.

Variables K L : {group gT}.
Local Notation S M := (seqIndD K L K M).
Local Notation calS := (S 1).

Variables (R : 'CF(L) -> seq 'CF(G)) (tau : {linear 'CF(L) -> 'CF(G)}).

(* These may need to be grouped, in order to make the proofs of 6.8, 10.10, *)
(* and 12.6 more manageable.                                                *)
Hypotheses (nsKL : K <| L) (solK : solvable K).
Hypothesis Itau : {in 'Z[calS, L^#] &, isometry tau}.
Hypothesis scohS : subcoherent calS tau R.

Let sKL : K \subset L. Proof. exact: normal_sub. Qed.
Let nKL : L \subset 'N(K). Proof. exact: normal_norm. Qed.
Let orthS: pairwise_orthogonal calS. Proof. by case: scohS. Qed.
Let sSS M : {subset S M <= calS}. Proof. exact: seqInd_sub. Qed.
Let ccS M : conjC_closed (S M). Proof. exact: cfAut_seqInd. Qed.
Let uniqS M : uniq (S M). Proof. exact: seqInd_uniq. Qed.
Let nrS : ~~ has cfReal calS. Proof. by case: scohS => [[]]. Qed.

Lemma exists_linInd M :
  M \proper K -> M <| K -> exists2 phi, phi \in S M & phi 1%g = #|L : K|%:R.
Proof.
move=> ltMK nsMK; have [sMK nMK] := andP nsMK.
have ntKM: (K / M)%g != 1%g by rewrite -subG1 quotient_sub1 // proper_subn.
have [r /andP[_ r1] ntr] := lin_char_solvable ntKM (quotient_sol M solK).
exists ('Ind[L, K] ('chi_r %% M)%CF); last first.
  by rewrite cfInd1 // cfModE // morph1 (eqP r1) mulr1.
apply/seqIndP; exists (mod_Iirr r); last by rewrite mod_IirrE.
rewrite !inE subGcfker mod_IirrE ?cfker_Mod //= andbT.
apply: contraNneq ntr => /(canRL (mod_IirrK nsMK))->.
by rewrite quo_IirrE // chi0_1 ?cfker_cfun1 ?cfQuo_cfun1.
Qed.

(* This is Peterfalvi (6.2). *)
Lemma coherent_seqIndD_bound (A B C D : {group gT}) :
        [/\ A <| L, B <| L, C <| L & D <| L] ->
  (*a*) [/\ A \proper K, B \subset D, D \subset C, C \subset K
          & D / B \subset 'Z(C / B)]%g ->
  (*b1*) coherent (S A) L^# tau ->
  (*b2*) coherent (S B) L^# tau
  \/ #|K : A|%:R - 1 <= 2%:R * #|L : C|%:R * sqrtC #|C : D|%:R.
Proof.
move=> [nsAL nsBL nsCL nsDL] [ltAK sBD sDC sCK sDbZC] cohA.
have [|not_ineq] := boolP (_ <= _); [by right | left].
have sBC := subset_trans sBD sDC; have sBK := subset_trans sBC sCK.
have [sAK nsBK] := (proper_sub ltAK, normalS sBK sKL nsBL).
have{sBC} [nsAK nsBC] := (normalS sAK sKL nsAL, normalS sBC sCK nsBK).
pose wf S1 := [/\ uniq S1, {subset S1 <= calS} & conjC_closed S1].
pose S1 := [::] ++ S A; set S2 := [::] in S1; rewrite -[S A]/S1 in cohA.
have wfS1: wf S1 by split; [exact: uniqS | exact: sSS | exact: ccS].
move: {2}_.+1 (ltnSn (size calS - size S1)) => n.
elim: n => // n IHn in (S2) S1 wfS1 cohA *; rewrite ltnS => leSnS1.
have [uniqS1 sS1S ccS1] := wfS1.
have [sAB1 | /allPn[psi /= SBpsi notS1psi]] := altP (@allP _ (mem S1) (S B)).
  apply: subset_coherent cohA => //.
  exact: orthogonal_free (sub_pairwise_orthogonal _ _ orthS).
have [neq_psi_c SBpsic] := (hasPn nrS _ (sSS SBpsi), ccS SBpsi).
have wfS1': wf [:: psi, psi^* & S1]%CF.
  split=> [|xi|xi]; rewrite /= !inE 1?andbC.
  - rewrite negb_or eq_sym neq_psi_c notS1psi uniqS1 (contra (ccS1 _)) //.
    by rewrite cfConjCK.
  - by case/predU1P=> [|/predU1P[|/sS1S]] -> //; rewrite (@sSS B).
  do 2![case/predU1P=> [-> |]; first by rewrite ?cfConjCK eqxx ?orbT // eq_sym].
  by move/ccS1=> ->; rewrite !orbT.
apply: (IHn [:: psi, psi^* & S2]%CF) => //; last first.
  rewrite -leq_subS ?uniq_leq_size //; try by case: wfS1'.
  by rewrite /= subSS (leq_trans _ leSnS1) // leq_sub2l ?leqW.
have [phi SAphi phi1] := exists_linInd ltAK nsAK.
have: [&& phi \in S1, psi \in calS & psi \notin S1].
  by rewrite mem_cat SAphi orbT (@sSS B).
have /seqIndP[i /setDP[kBi _] def_psi] := SBpsi; rewrite inE in kBi.
move/(extend_coherent scohS); apply; rewrite // {phi SAphi}phi1; split=> //.
  by rewrite def_psi cfInd1 // dvdC_mulr // isIntCE isNatC_irr1.
have Spos xi: xi \in calS -> 0 <= xi 1%g by move/seqInd1_Nat/posC_Nat.
rewrite big_cat sum_seqIndD_square //= ltC_sub -addrA sposC_addl //=.
  rewrite big_seq posC_sum // => xi S2xi.
  by rewrite !posC_mul ?posC_inv ?cfnorm_posC ?Spos ?sS1S // mem_cat S2xi.
rewrite mulrC -mulr_subl sposC_mul ?sposGiC // -ltC_sub.
rewrite realC_ltNge /isRealC ?rmorph_sub ?rmorph1 ?rmorph_nat //; last first.
  by rewrite posC_conjK ?posC_mul ?posC_nat // Spos ?(sSS SBpsi).
apply: contra not_ineq => /leC_trans-> //.
rewrite -mulrA leC_pmul2l -?(ltn_ltC 0) // def_psi cfInd1 //.
rewrite -(LaGrange_index sKL sCK) natr_mul -mulrA leC_pmul2l ?sposGiC //.
exact: irr1_bound_quo sDbZC.
Qed.

(* This is Peterfalvi, Theorem (6.3). *)
Theorem bounded_seqIndD_coherent M H H1 :
   [/\ M <| L, H <| L & H1 <| L] ->
   [/\ M \subset H1, H1 \subset H & H \subset K] ->
 (*a*) nilpotent (H / M)%g ->
 (*b*) coherent (S H1) L^# tau ->
 (*c*) (#|H : H1| > 4 * #|L : K| ^ 2 + 1)%N ->
 coherent (S M) L^# tau.
Proof.
move: H1 => A [nsML nsHL nsAL] [sMA sAH sHK] nilHb cohA lbHA.
elim: {A}_.+1 {-2}A (ltnSn #|A|) => // m IHm A leAm in nsAL sMA sAH cohA lbHA *.
have [/group_inj-> // | ltMA] := eqVproper sMA; have [sAL nAL] := andP nsAL.
have{ltMA} [B maxB sMB]: {B : {group gT} | maxnormal B A L & M \subset B}.
  by apply: maxgroup_exists; rewrite ltMA normal_norm.
have /andP[ltBA nBL] := maxgroupp maxB; have [sBA not_sAB] := andP ltBA.
have [sBH sBL] := (subset_trans sBA sAH, subset_trans sBA sAL).
have nsBL: B <| L by exact/andP.
suffices{m IHm leAm} cohB: coherent (S B) L^# tau.
  apply: IHm cohB _ => //; first exact: leq_trans (proper_card ltBA) _.
  by rewrite (leq_trans lbHA) // dvdn_leq // indexgS.
have /andP[sHL nHL] := nsHL.
have sAbZH: (A / B \subset 'Z(H / B))%g.
  have nBA := subset_trans sAL nBL; have nsBA : B <| A by exact/andP.
  have minBb: minnormal (A / B)%g (L / B)%g.
    apply/mingroupP; split=> [|Db /andP[ntDb nDLb] sDAb].
      by rewrite -subG1 quotient_sub1 // not_sAB quotient_norms.
    have: Db <| (L / B)%g by rewrite /normal (subset_trans sDAb) ?quotientS.
    case/(inv_quotientN nsBL)=> D defDb sBD /andP[sDL nDL].
    apply: contraNeq ntDb => neqDAb; rewrite defDb quotientS1 //.
    case/maxgroupP: maxB => /= _ /(_ D) {1}<- //.
    rewrite -(quotient_proper (normalS sBD sDL nsBL)) // -defDb.
    by rewrite properEneq sDAb neqDAb.
  apply/setIidPl; case/mingroupP: minBb => /andP[ntAb nALb].
  apply; rewrite ?subsetIl //.
  have nZHb := char_norm_trans (center_char (H / B)) (quotient_norms _ nHL).
  rewrite andbC normsI //= meet_center_nil //=; last first.
    by rewrite quotient_normal // (normalS sAH sHL).
  suffices /homgP[f /= <-]: (H / B)%g \homg (H / M)%g by rewrite morphim_nil.
  by apply: homg_quotientS; rewrite ?(subset_trans sHL) ?normal_norm.
have [defA | ltAH] := eqVproper sAH.
  by rewrite addn1 defA indexgg in lbHA.
have [sAK ltAK] := (subset_trans sAH sHK, proper_sub_trans ltAH sHK).
case: (@coherent_seqIndD_bound A B H A) => // /idPn[].
apply: contraL lbHA; rewrite -ltnNge ltn_ltC -(LaGrange_index sHK sAH) natr_mul.
set x := #|H : A|%:R => ub_x.
have nz_x2: sqrtC x != 0 by rewrite sqrtC_eq0 neq0GiC.
have x2_gt0: 0 < sqrtC x by rewrite ltCE nz_x2 sqrtC_pos posC_nat.
have{ub_x}: sqrtC x - (sqrtC x)^-1 <= (2 * #|L : K|)%:R.
  rewrite -(leC_pmul2r _ _ (sposGiC K H)) -natr_mul -mulnA LaGrange_index //.
  rewrite natr_mul -(leC_pmul2r _ _ x2_gt0) mulrC mulr_subl mulr_subr.
  rewrite !mulrA -expr2 sqrtCK divff // (leC_trans _ ub_x) // mulrC.
  by rewrite leC_add2l leC_opp mul1r -(leq_leC 1).
rewrite -(@leC_exp2r 2) ?posC_nat //; last first.
  rewrite leC_sub -(leC_pmul2r _ _ x2_gt0) -expr2 mulVf // sqrtCK.
  by rewrite -(leq_leC 1).
rewrite -natr_exp expn_mull -(leC_add2r 2%:R) -addnS natr_add.
apply: ltC_leC_trans; rewrite sqrr_sub // expr_inv sqrtCK divff //.
by rewrite addrAC subrK addrC ltC_sub addrK sposC_inv sposGiC.
Qed.

(* This is the statement of Peterfalvi, Hypothesis (6.4). *)
Definition odd_Frobenius_quotient M (H1 := K^`(1) <*> M) :=
  [/\ (*a*) odd #|L|,
      (*b*) [/\ M <| L, M \subset K & nilpotent (K / M)]
    & (*c*) [Frobenius L / H1 with kernel K / H1] ]%g.

(*
Lemma proper_odd_mod1 m d :
  (odd m -> odd d -> m > 1 -> m == 1 %[mod d] -> 2 * d + 1 <= m)%N.
Proof.
move=> odd_m odd_d m_gt1; rewrite eqn_mod_dvd ?(ltnW m_gt1) //.
rewrite -[m]odd_double_half odd_m subn1 /= -mul2n addn1 ltnS leq_pmul2l //.
rewrite gauss; last by rewrite coprime_sym prime_coprime // dvdn2 odd_d.
by apply: dvdn_leq; rewrite -(subnKC m_gt1).
Qed.
*)

(* This is Peterfalvi (6.5). *)
Lemma non_coherent_chief M (H1 := (K^`(1) <*> M)%G) :
   odd_Frobenius_quotient M ->
   coherent (S M) L^# tau
\/ [/\ (*a*) chief_factor L H1 K /\ (#|K : H1| <= 4 * #|L : K| ^ 2 + 1)%N
     & (*b*) exists2 p : nat, p.-group (K / M)%g /\ ~~ abelian (K / M)%g
     & (*c*) ~~ (#|L : K| %| p - 1)].
Proof.
case=> oddL [nsML sMK nilKb]; rewrite /= -(erefl (gval H1)) => frobLb.
set e := #|L : K|; have odd_e: odd e := dvdn_odd (dvdn_indexg L K) oddL.
have{odd_e} mod1e_lb m: (odd m -> m > 1 -> m == 1 %[mod e] -> 2 * e + 1 <= m)%N.
  move=> odd_m m_gt1; rewrite eqn_mod_dvd ?(ltnW m_gt1) //.
  rewrite -[m]odd_double_half odd_m subn1 /= -mul2n addn1 ltnS leq_pmul2l //.
  rewrite gauss; last by rewrite coprime_sym prime_coprime // dvdn2 odd_e.
  by apply: dvdn_leq; rewrite -(subnKC m_gt1).
have nsH1L: H1 <| L by rewrite normalY // (char_normal_trans (der_char 1 K)).
have sH1K: H1 \subset K by rewrite join_subG der_sub.
have cohH1: coherent (S H1) L^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohS _) _ => //.
  apply/(@all_pred1_constant _ #|L : K|%:R)/allP=> _ /mapP[chi Schi ->] /=.
  have [i /setIdP[_]] := seqIndP Schi; rewrite inE join_subG -lin_irr_der1.
  by do 2![case/andP]=> _ /eqP chi1 _ ->; rewrite cfInd1 // chi1 mulr1.
have sMH1: M \subset H1 by exact: joing_subr.
have [ubK | lbK] := leqP; last by left; exact: bounded_seqIndD_coherent lbK.
have{ubK} ubK: (#|K : H1| < (2 * e + 1) ^ 2)%N.
  rewrite sqrn_add expn_mull (leq_ltn_trans ubK) // -subn_gt0 addKn.
  by rewrite !muln_gt0 indexg_gt0.
have [-> | neqMH1] := eqVneq M H1; [by left | right].
have{neqMH1} ltMH1: M \proper H1 by rewrite properEneq neqMH1.
have{frobLb} [[E1b frobLb] [sH1L nH1L]] := (existsP frobLb, andP nsH1L).
have [defLb ntKb _ _ /andP[sE1L _]] := Frobenius_context frobLb.
have nH1K: K \subset 'N(H1) := subset_trans sKL nH1L.
have chiefH1: chief_factor L H1 K.
  have ltH1K: H1 \proper K by rewrite /proper sH1K -quotient_sub1 ?subG1.
  rewrite /chief_factor nsKL andbT; apply/maxgroupP; rewrite ltH1K.
  split=> // H2 /andP[ltH2K nH2L] sH12; have sH2K := proper_sub ltH2K.
  have /eqVproper[// | ltH21] := sH12; case/idPn: ubK; rewrite -leqNgt.
  have dv_e H3: H1 \subset H3 -> H3 \subset K -> L \subset 'N(H3) ->
    #|H3 : H1| == 1 %[mod e].
  - move=> sH13 sH3K nH3L; rewrite eqn_mod_dvd // subn1.
    rewrite /e -(index_quotient_eq _ sKL nH1L) ?subIset ?sH1K ?orbT //.
    rewrite -[#|_ : _|]divgS ?quotientS // -(sdprod_card defLb) mulKn //.
    rewrite -card_quotient ?(subset_trans (subset_trans sH3K sKL)) //.
    rewrite regular_norm_dvd_pred ?(subset_trans sE1L) ?quotient_norms //.
    apply: semiregular_sym; apply: sub_in1 (Frobenius_reg_compl frobLb).
    by apply/subsetP; rewrite setSD ?quotientS.
  have dv_H21 := dv_e H2 sH12 sH2K nH2L.
  have dv_KH2: #|K : H2| == 1 %[mod e].
    have:= dv_e K sH1K (subxx K) nKL; rewrite -(LaGrange_index sH2K sH12).
    by rewrite -modn_mulmr (eqP dv_H21) modn_mulmr muln1.
  have odd_iK := dvdn_odd (dvdn_indexg _ _) (oddSg (subset_trans _ sKL) oddL).
  have iK_gt1 H3 H4: H4 \proper H3 -> (#|H3 : H4| > 1)%N.
    by rewrite indexg_gt1 => /andP[].
  by rewrite -(LaGrange_index sH2K sH12) leq_mul ?mod1e_lb ?odd_iK ?iK_gt1.
split=> //; have nMK := subset_trans sKL (normal_norm nsML).
have not_abKb: ~~ abelian (K / M).
  apply: contra (proper_subn ltMH1) => /derG1P/trivgP.
  rewrite /= join_subG subxx andbT -quotient_der ?quotient_sub1 //.
  exact: subset_trans (der_sub 1 K) nMK.
have /is_abelemP[p p_pr /and3P[pKb _ _]]: is_abelem (K / H1)%g.
  have: solvable (K / H1)%g by exact: quotient_sol solK.
  by case/(minnormal_solvable (chief_factor_minnormal chiefH1)).  
have [_ p_dv_Kb _] := pgroup_pdiv pKb ntKb.
have iso3M := third_isog sMH1 (normalS sMK sKL nsML) (normalS sH1K sKL nsH1L).
have pKM: p.-group (K / M)%g.
  have /dprodP[_ defKM cKMpp' tiKMpp'] := nilpotent_pcoreC p nilKb.
  rewrite -defKM (eqP (forall_inP (nilpotent_sol nilKb) 'O_p^'(_)%G _)).
    by rewrite mulg1 pcore_pgroup.
  have /isomP[inj_quo im_quo] := quotient_isom (cents_norm cKMpp') tiKMpp'.
  rewrite subsetI pcore_sub /= -(injmSK inj_quo) // (morphim_der _ 1) //.
  rewrite {inj_quo}im_quo /= -[Q in Q^`(1)%g]quotientMidl defKM.
  rewrite -quotient_der ?gFnorm ?quotientS //.
  rewrite -quotient_sub1 ?(subset_trans (pcore_sub _ _) (der_norm _ _)) //.
  rewrite -[(_ / _)%g]setIid coprime_TIg //.
  apply: pnat_coprime (quotient_pgroup _ (pcore_pgroup _ _)).
  apply: pgroupS (quotientS _ (pcore_sub _ _)) _.
  rewrite /= -quotient_der // -(quotientYidr (subset_trans (der_sub 1 K) nMK)).
  by rewrite (isog_pgroup _ iso3M) ?(normalS sMK sKL nsML).
exists p => //; apply: contra not_abKb => e_dv_p1.
rewrite cyclic_abelian // Phi_quotient_cyclic //.
have /homgP[f <-]: (K / M / 'Phi(K / M) \homg K / H1)%g.
  apply: homg_trans (isog_hom iso3M).
  rewrite homg_quotientS ?gFnorm ?quotient_norms //=.
  rewrite quotientYidr ?(subset_trans (der_sub 1 K)) // quotient_der //.
  by rewrite (Phi_joing pKM) joing_subl.
rewrite {f}morphim_cyclic // abelian_rank1_cyclic; last first.
  by rewrite sub_der1_abelian ?joing_subl.
rewrite (rank_pgroup pKb) (leq_trans (p_rank_le_logn _ _)) //.
rewrite -ltnS -(ltn_exp2l _ _ (prime_gt1 p_pr)) -p_part part_pnat_id //.
rewrite card_quotient // (leq_trans ubK) // leq_exp2r //.
have odd_p: odd p := dvdn_odd p_dv_Kb (quotient_odd _ (oddSg sKL oddL)).
by rewrite mod1e_lb // ?eqn_mod_dvd ?prime_gt0 ?prime_gt1.
Qed.

(* This is Peterfalvi (6.6). *)
Lemma seqIndD_irr_coherence (Z : {group gT}) (calX := seqIndD K L Z 1) :
    odd_Frobenius_quotient 1%G ->
    [/\ Z <| L, Z :!=: 1 & Z \subset 'Z(K)]%g ->
    {subset calX <= irr L} ->
  calX =i [pred chi \in irr L | ~~ (Z \subset cfker chi)]
  /\ coherent calX L^#tau.
Proof.
move=> Frob_quo1 [nsZL ntZ sZ_ZK] irrX; have [sZL nZL] := andP nsZL.
have abZ: abelian Z by rewrite (abelianS sZ_ZK) ?center_abelian.
have /andP[sZK nZK]: Z <| K := sub_center_normal sZ_ZK.
split=> [chi|].
  apply/idP/andP=> [Xchi | [/irrP[r ->{chi}] nkerZr]].
    rewrite irrX //; case/seqIndP: Xchi => t /setIdP[nkerZt _] ->.
    by rewrite inE in nkerZt; rewrite sub_cfker_Ind_irr.
  have [t Res_r_t] := neq0_has_constt (Res_irr_neq0 r sKL).
  pose chi := 'Ind[L] 'chi_t; have chi_r: '[chi, 'chi_r] != 0.
    by rewrite -cfdot_Res_r cfdotC fmorph_eq0 -irr_consttE.
  have Xchi: chi \in calX.
    apply/seqIndP; exists t; rewrite // !inE sub1G andbT.
    rewrite -(sub_cfker_Ind_irr t nZL sKL).
    apply: contra nkerZr => /subset_trans-> //.
    by rewrite cfker_constt // cfInd_char ?irr_char //.
  case/irrX/irrP: Xchi chi_r (Xchi) => r' ->.
  by rewrite cfdot_irr -neq0N_neqC -lt0n; case: eqP => // ->.
have [|[]] := non_coherent_chief Frob_quo1.
  by apply: subset_coherent; [exact: seqInd_sub | exact: orthogonal_free].
have [oddL _] := Frob_quo1; rewrite /= joingG1 => frobLb _ [p []].
set e := #|L : K|; have e_gt0: (e > 0)%N by exact: indexg_gt0.
have isoK1 := isog_symr (quotient1_isog K).
rewrite (isog_abelian isoK1) {isoK1}(isog_pgroup _ isoK1).
have [-> | ntK pK _ not_e_dv_p1] := eqsVneq K [1]; first by rewrite abelian1.
have{ntK} [p_pr p_dv_K _] := pgroup_pdiv pK ntK.
set Y := calX; pose d (xi : 'CF(L)) := logn p (getNatC (xi 1%g) %/ e).
have: conjC_closed Y by exact: cfAut_seqInd.
have: perm_eq (Y ++ [::]) calX by rewrite cats0.
have: {in Y & [::], forall xi1 xi2, d xi1 <= d xi2}%N by [].
elim: {Y}_.+1 {-2}Y [::] (ltnSn (size Y)) => // m IHm Y X' leYm leYX' defX ccY.
have sYX: {subset Y <= calX}.
  by move=> xi Yxi; rewrite -(perm_eq_mem defX) mem_cat Yxi.
have sX'X: {subset X' <= calX}.
  by move=> xi X'xi; rewrite -(perm_eq_mem defX) mem_cat X'xi orbT.
have uniqY: uniq Y.
  have: uniq calX := seqInd_uniq L _.
  by rewrite -(perm_eq_uniq defX) cat_uniq => /and3P[].
have sYS: {subset Y <= calS} by move=> xi /sYX/seqInd_sub->.
case homoY: (constant [seq (xi : 'CF(L)) 1%g | xi <- Y]).
  exact: uniform_degree_coherence (subset_subcoherent scohS _) homoY.
have Ndg: {in calX, forall xi : 'CF(L), xi 1%g = (e * p ^ d xi)%:R}.
  rewrite /d => _ /seqIndP[i _ ->]; rewrite cfInd1 // -/e.
  have:= dvd_irr1_cardG i; have /isNatCP[n ->] := isNatC_irr1 i.
  rewrite -natr_mul getNatC_nat dvdC_nat mulKn // -p_part => dv_n_K.
  by rewrite part_pnat_id // (pnat_dvd dv_n_K).  
have [chi Ychi leYchi]: {chi | chi \in Y & {in Y, forall xi, d xi <= d chi}%N}.
  have [/eqP/nilP Y0 | ntY] := posnP (size Y); first by rewrite Y0 in homoY.
  pose i := [arg max_(i > Ordinal ntY) d Y`_i].
  exists Y`_i; [exact: mem_nth | rewrite {}/i; case: arg_maxP => //= i _ max_i].
  by move=> _ /(nthP 0)[j ltj <-]; exact: (max_i (Ordinal ltj)).
have{homoY} /hasP[xi1 Yxi1 lt_xi1_chi]: has (fun xi => d xi < d chi)%N Y.
  apply: contraFT homoY => geYchi; apply: (@all_pred1_constant _ (chi 1%g)).
  rewrite all_map; apply/allP=> xi Yxi; rewrite /= !Ndg ?sYX // -eqN_eqC.
  rewrite eqn_pmul2l // eqn_exp2l ?prime_gt1 //.
  by rewrite eqn_leq leYchi //= leqNgt (hasPn geYchi).
pose Y' := rem chi^*%CF (rem chi Y); pose X'' := [:: chi, chi^*%CF & X'].
have ccY': conjC_closed Y'.
  move=> xi; rewrite !(inE, mem_rem_uniq) ?rem_uniq //.
  by rewrite !(inv_eq (@cfConjCK _ _)) cfConjCK => /and3P[-> -> /ccY->].
have Xchi := sYX _ Ychi; have defY: perm_eq [:: chi, chi^*%CF & Y'] Y.
  rewrite (perm_eqrP (perm_to_rem Ychi)) perm_cons perm_eq_sym perm_to_rem //.
  by rewrite mem_rem_uniq ?inE ?ccY // (seqInd_conjC_neq _ _ _ Xchi).
apply: perm_eq_coherent (defY) _ _.
  have: free calX by exact: seqInd_free.
  by rewrite (free_perm_eq defY) -(free_perm_eq defX); exact: free_catl. 
have d_chic: d chi^*%CF = d chi.
  by rewrite /d cfunE isNatC_conj // (seqInd1_Nat Xchi).
have /andP[uniqY' Y'x1]: uniq Y' && (xi1 \in Y').
  rewrite !(inE, mem_rem_uniq) ?rem_uniq // Yxi1 andbT -negb_or.
  by apply: contraL lt_xi1_chi => /pred2P[] ->; rewrite ?d_chic ltnn.
have xi1P: [&& xi1 \in Y', chi \in calS & chi \notin Y'].
  by rewrite Y'x1 sYS ?(inE, mem_rem_uniq) ?rem_uniq // eqxx andbF.
have sY'Y: {subset Y' <= Y} by move=> xi /mem_rem/mem_rem.
apply: (extend_coherent scohS) xi1P _; first by split=> // xi /sY'Y/sYS. 
have{defX} defX: perm_eq (Y' ++ X'') calX.
  by rewrite (perm_catCA Y' [::_; _]) catA -(perm_eqrP defX) perm_cat2r.
have{d_chic} le_chi_X'': {in X'', forall xi, d chi <= d xi}%N.
  by move=> xi /or3P[/eqP-> | /eqP-> | /leYX'->] //; rewrite d_chic.
rewrite !Ndg ?sYX // dvdC_nat dvdn_pmul2l // dvdn_exp2l 1?ltnW //; split=> //.
  apply: IHm defX ccY' => [|xi xi' /sY'Y/leYchi le_xi_chi /le_chi_X''].
    by rewrite -ltnS // (leq_trans _ leYm) // -(perm_eq_size defY) ltnW.
  exact: leq_trans.
have pos_p n: (0 < p ^ n)%N by rewrite expn_gt0 prime_gt0.
rewrite -!natr_mul; apply: (@ltC_leC_trans (e ^ 2 * (p ^ d chi) ^ 2)%:R).
  rewrite -ltn_ltC -expn_mull -mulnn mulnAC !mulnA 2?ltn_pmul2r //.
  rewrite -mulnA mulnCA ltn_pmul2l // -(subnK lt_xi1_chi) addnS expnS.
  rewrite expn_add mulnA ltn_pmul2r // -(muln1 3) leq_mul //.
  rewrite ltn_neqAle prime_gt1 // eq_sym (sameP eqP (prime_oddPn p_pr)).
  by rewrite (dvdn_odd p_dv_K) // (oddSg sKL).
have [r] := seqIndP (sYX _ Ychi); rewrite !inE => /andP[nkerZr _] def_chi.
have d_r: 'chi_r 1%g = (p ^ d chi)%:R.
  by apply: (mulfI (neq0GiC L K)); rewrite -cfInd1 // -def_chi -natr_mul Ndg.
pose sum_p2d S := (\sum_(xi <- S) p ^ (d xi * 2))%N.
pose sum_xi1 (S : seq 'CF(L)) := \sum_(xi <- S) xi 1%g ^+ 2 / '[xi].
have def_sum_xi1 S: {subset S <= calX} -> sum_xi1 S = (e ^ 2 * sum_p2d S)%:R.
  move=> sSX; rewrite big_distrr natr_sum /=; apply: eq_big_seq => xi /sSX Xxi.
  rewrite expn_mulr -expn_mull natr_exp -Ndg //.
  by have /irrP[i ->] := irrX _ Xxi; rewrite cfnorm_irr divr1.
rewrite -/(sum_xi1 _) def_sum_xi1 -?leq_leC 1?dvdn_leq => [|||_ /sY'Y/sYX] //.
  by rewrite muln_gt0 expn_gt0 e_gt0 [_ Y'](bigD1_seq xi1) //= addn_gt0 pos_p.
have coep: coprime e p.
  have:= Frobenius_ker_coprime frobLb; rewrite coprime_sym.
  have /andP[_ nK'L] := char_normal_trans (der_char 1 K) nsKL.
  rewrite index_quotient_eq ?subIset ?der_sub ?orbT {nK'L}// -/e.
  have ntKb: (K / K^`(1))%g != 1%g by case/Frobenius_kerP: frobLb.
  have [_ _ [k ->]] := pgroup_pdiv (quotient_pgroup _ pK) ntKb.
  by rewrite coprime_pexpr.
rewrite -expn_mulr gauss_inv ?coprime_expl ?coprime_expr {coep}// dvdn_mulr //=.
have /dvdn_addl <-: p ^ (d chi * 2) %| e ^ 2 * sum_p2d X''.
  rewrite big_distrr big_seq dvdn_sum //= => xi /le_chi_X'' le_chi_xi.
  by rewrite dvdn_mull // dvdn_exp2l ?leq_pmul2r.
rewrite -muln_addr -big_cat (eq_big_perm _ defX) -(getNatC_nat (e ^ 2 * _)) /=.
rewrite -def_sum_xi1 // /sum_xi1 sum_seqIndD_square ?normal1 ?sub1G //.
rewrite indexg1 -(natr_sub _ (cardG_gt0 Z)) -natr_mul getNatC_nat.
rewrite -(LaGrange_index sKL sZK) mulnAC dvdn_mull //.
have /p_natP[k defKZ]: p.-nat #|K : Z| by rewrite (pnat_dvd (dvdn_indexg K Z)).
rewrite defKZ dvdn_exp2l // -(leq_exp2l _ _ (prime_gt1 p_pr)) -{k}defKZ.
rewrite leq_leC expn_mulr natr_exp -d_r ?(leC_trans (irr1_bound r).1) //.
rewrite -leq_leC dvdn_leq ?indexgS ?(subset_trans sZ_ZK) //=.
by rewrite -cap_cfcenter_irr bigcap_inf.
Qed.

End GeneralCoherence.

Section MoreMorphism.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Type A : {set aT}.

Lemma morphimD1 A : (f @* A)^# \subset f @* A^#.
Proof. by rewrite -!set1gE -(morphim1 f) morphimD. Qed.

Lemma morphim_class x A :
  x \in D -> A \subset D -> f @* (x ^: A) = f x ^: f @* A.
Proof.
move=> Dx sAD; rewrite !morphimEsub ?class_subG // /class -!imset_comp.
by apply: eq_in_imset => y Ay /=; rewrite morphJ // (subsetP sAD).
Qed.

Lemma classes_morphim A :
  A \subset D -> classes (f @* A) = [set f @* xA | xA <- classes A].
Proof.
move=> sAD; rewrite morphimEsub // /classes -!imset_comp.
apply: eq_in_imset => x /(subsetP sAD) Dx /=.
by rewrite morphim_class ?morphimEsub.
Qed.

Hypothesis injf : 'injm f.

Lemma injmD1 A : f @* A^# = (f @* A)^#.
Proof. by have:= morphimDG A injf; rewrite morphim1. Qed.

Lemma nclasses_injm A : A \subset D -> #|classes (f @* A)| = #|classes A|.
Proof.
move=> sAD; rewrite classes_morphim // card_in_imset //.
move=> _ _ /imsetP[x Ax ->] /imsetP[y Ay ->].
by apply: injm_morphim_inj; rewrite // class_subG ?(subsetP sAD).
Qed.

End MoreMorphism.

Lemma nclasses_isog (jT hT : finGroupType) (G1 : {group jT}) (H : {group hT}) :
  G1 \isog H -> #|classes G1| = #|classes H|.
Proof. by case/isogP=> f injf <-; rewrite nclasses_injm. Qed.

Section MoreQuotient.
Close Scope ring_scope.
Variables (aT : finGroupType) (H : {group aT}).
Implicit Type A : {set aT}.

Lemma quotientD1 A : (A / H)^# \subset A^# / H.
Proof. exact: morphimD1. Qed.

Lemma quotient_class x A :
  x \in 'N(H) -> A \subset 'N(H) -> x ^: A / H  = coset H x ^: (A / H).
Proof. exact: morphim_class. Qed.

Lemma classes_quotient A :
  A \subset 'N(H) -> classes (A / H) = [set xA / H | xA <- classes A].
Proof. exact: classes_morphim. Qed.

Lemma quotient_neq1 A : H <| A -> (A / H != 1) = (H \proper A).
Proof.
case/andP=> sHA  nHA; rewrite /proper sHA -trivg_quotient eqEsubset andbC.
by rewrite quotientS //= quotientSGK.
Qed.

End MoreQuotient.

Lemma Frobenius_coprime_quotient (g1T : finGroupType) (G1 K H N : {group g1T}) :
    K ><| H = G1 -> N <| G1 ->
    coprime #|K| #|H| /\ H :!=: 1%g ->
    N \proper K /\ {in H^#, forall x, 'C_K[x] \subset N} ->
  [Frobenius G1 / N = (K / N) ><| (H / N)]%g.
Proof.
move=> defG nsNG [coKH ntH] [ltNK regH].
have [[sNK _] [_ /mulG_sub[sKG sHG] _ _]] := (andP ltNK, sdprodP defG).
have [_ nNG] := andP nsNG; have nNH := subset_trans sHG nNG.
apply/Frobenius_semiregularP; first exact: quotient_coprime_sdprod.
- by rewrite quotient_neq1 ?(normalS _ sKG).
- by rewrite -(isog_eq1 (quotient_isog _ _)) ?coprime_TIg ?(coprimeSg sNK).
move=> _ /(subsetP (quotientD1 _ _))/morphimP[x nNx H1x ->].
rewrite -cent_cycle -quotient_cycle //=.
rewrite -strongest_coprime_quotient_cent ?cycle_subG //.
- by rewrite cent_cycle quotientS1 ?regH.
- by rewrite subIset ?sNK.
- rewrite (coprimeSg (subsetIl N _)) ?(coprimeSg sNK) ?(coprimegS _ coKH) //.
  by rewrite cycle_subG; case/setD1P: H1x.
by rewrite orbC abelian_sol ?cycle_abelian.
Qed.

(* Classfun omission; subsumes PFsection1.IndGT_chi !!! *)
Lemma cfIndInd (L H K : {group gT}) phi :
  H \subset L -> K \subset H -> 'Ind[L] ('Ind[H, K] phi) = 'Ind[L] phi.
Proof.
move=> sHL sKH; apply/cfun_inP=> x Lx; rewrite !cfIndE ?(subset_trans sKH) //.
apply: canLR (mulKf (neq0GC H)) _; rewrite -mulr_sumr mulr_natl.
transitivity (\sum_(y \in L) \sum_(z \in H) #|K|%:R^-1 * phi ((x ^ y) ^ z)).
  by apply: eq_bigr => y Ly; rewrite cfIndE // mulr_sumr.
symmetry; rewrite exchange_big /= -sumr_const; apply: eq_bigr => z Hz.
rewrite (reindex_inj (mulIg z)); apply: eq_big => [y | y _].
  by rewrite groupMr // (subsetP sHL).
by rewrite conjgM.
Qed.

Lemma vchar_onG (L : {group gT}) (S : seq 'CF(L)) : 'Z[S, L] =i 'Z[S].
Proof. by move=> phi; rewrite vchar_split cfun_onG andbT. Qed.

Definition dual_iso (L : {group gT}) (nu : {additive 'CF(L) -> 'CF(G)}) :=
  [additive of -%R \o nu \o cfAut conjC].

Lemma dual_coherence (L : {group gT}) (S : seq 'CF(L)) tau R nu :
    subcoherent S tau R -> coherent_with S L^# tau nu -> (size S <= 2)%N ->
  coherent_with S L^# tau (dual_iso nu).
Proof.
move=> [[charS nrS ccS] _ oSS _ _] [[Inu Znu] Dnu] szS2.
split=> [|{Inu Znu oSS} phi ZSphi].
  have{oSS} ccZS := cfAut_vchar (orthogonal_free oSS) ccS.
  have vcharS: {subset S <= 'Z[irr L]} by move=> phi /(allP charS)/char_vchar.
  split=> [phi1 phi2 Sphi1 Sphi2 | phi Sphi].
    rewrite cfdotNl cfdotNr opprK Inu ?ccZS // cfdot_conjC isIntC_conj //.
    by rewrite cfdot_vchar_Int ?(vchar_sub_irr vcharS).
  by rewrite opp_vchar Znu ?ccZS.
rewrite -{}Dnu //; move: ZSphi; rewrite vcharD1E => /andP[].
case/vchar_expansion=> z Zz ->{phi}.
case: S charS nrS ccS szS2 => [|eta S1]; first by rewrite !big_nil !raddf0.
case/andP=> Neta _ /norP[eta'c _] /allP/andP[S1_etac _].
rewrite inE [_ == _](negPf eta'c) /= in S1_etac.
case: S1 S1_etac => [|_ []] // /predU1P[] // <- _.
rewrite big_cons big_seq1 !raddfD !raddfZ_IntC ?Zz //.
rewrite !cfunE (isNatC_conj (char1_Nat Neta)) -mulr_addl mulf_eq0.
rewrite addr_eq0 char1_eq0 // !scalerN cfConjCK addrC.
by case/pred2P=> ->; rewrite ?raddf0 // !scaleNr opprK.
Qed.

Lemma signrE (R : ringType) (b : bool) : (-1) ^+ b = 1 - b.*2%:R :> R.
Proof. by case: b; rewrite ?subr0 // oppr_add addNKr. Qed.

Lemma cfdot_dirr_eq1 (L : {group gT}) phi psi :
  phi \in dirr L -> psi \in dirr L -> ('[phi, psi] == 1) = (phi == psi).
Proof.
move=> /dirrP[b1 [i1 ->]] /dirrP[b2 [i2 ->]].
rewrite eq_signed_irr cfdotZl cfdotZr rmorph_sign cfdot_irr mulrA -signr_addb.
rewrite signrE mulr_subl (can2_eq (subrK _) (addrK _)) mul1r -natr_mul.
rewrite -(natr_add _ 1) -eqN_eqC -negb_add.
by case: (i1 == _) (_ (+) _) => [] [].
Qed.

Lemma cfdot_add_dirr_eq1 (L : {group gT}) :
  {in dirr L & &, forall phi1 phi2 psi,
    '[phi1 + phi2, psi] = 1 -> psi = phi1 \/ psi = phi2}.
Proof.
move=> _ _ _ /dirrP[b1 [i1 ->]] /dirrP[b2 [i2 ->]] /dirrP[c [j ->]] /eqP.
rewrite cfdotDl !cfdotZl !cfdotZr !rmorph_sign !cfdot_irr !mulrA -!signr_addb.
rewrite 2!{1}signrE !mulr_subl !mul1r -!natr_mul addrCA -subr_eq0 -!addrA.
rewrite -!oppr_add addrA subr_eq0 -mulrSr -!natr_add -eqN_eqC => eq_phi_psi.
apply/pred2P; rewrite /= !eq_signed_irr -!negb_add !(eq_sym j) !(addbC c).
by case: (i1 == j) eq_phi_psi; case: (i2 == j); do 2!case: (_ (+) c).
Qed.

Lemma coherent_seqInd_conjCirr (L : {group gT}) (S : seq 'CF(L)) tau R nu r :
    subcoherent S tau R -> coherent_with S L^# tau nu ->
    let chi := 'chi_r in let chi2 := (chi :: chi^*)%CF in
    chi \in S ->
  [/\ {subset map nu chi2 <= 'Z[irr G]}, orthonormal (map nu chi2),
      chi - chi^*%CF \in 'Z[S, L^#] & (nu chi - nu chi^*)%CF 1%g == 0].
Proof.
move=> [[charS nrS ccS] [_ Ztau] oSS _ _] [[Inu Znu] Dnu] chi chi2 Schi.
have sSZ: {subset S <= 'Z[S]} by have /mem_vchar := orthogonal_free oSS.
have vcharS: {subset S <= 'Z[irr L]} by move=> phi /(allP charS)/char_vchar.
have Schi2: {subset chi2 <= 'Z[S]} by apply/allP; rewrite /= !sSZ ?ccS.
have Schi_diff: chi - chi^*%CF \in 'Z[S, L^#].
  by rewrite sub_Aut_vchar // vchar_onG sSZ ?ccS.
split=> // [_ /mapP[xi /Schi2/Znu ? -> //]||].
  apply: map_orthonormal; first by apply: sub_in2 Inu; exact: vchar_trans_on.
  rewrite orthonormalE (conjC_pair_orthogonal ccS) //=.
  by rewrite cfnorm_conjC !cfnorm_irr !eqxx.
by rewrite -raddf_sub -cfunD1E Dnu // irr_vchar_on ?Ztau.
Qed.

(* This is Peterfalvi (1.9)(b). *)
(* We have corrected a quantifier inversion in the original statement: the    *)
(* automorphism is constructed uniformly for all characters, and indeed for   *)
(* all virtual characters. We have also removed the spurrious condition that  *)
(* a be a \pi(a) part of #|G| -- indeed the proof should work for all a!      *)
Lemma make_pi_cfAut (L : {group gT}) a k :
    coprime k a ->
  exists2 u : {rmorphism algC -> algC}, algC_Aut u &
    {in 'Z[irr G] & G, forall chi x,
          [/\ (#[x] %| a)%N -> cfAut u chi x = chi (x ^+ k)%g
            & coprime #[x] a -> cfAut u chi x = chi x]}.
Admitted.

(* This is Peterfalvi (6.7). *)
(* In (6.8) we only know initially the P is Sylow in L; perhaps the lemma     *)
(* should be stated with this equivalent (but weaker) assumption.             *)
Lemma constant_irr_mod_TI_Sylow (Z L P : {group gT}) p i :
     p.-Sylow(G) P -> odd #|L| -> normedTI P^# G L ->
     [/\ Z <| L, Z :!=: 1%g & Z \subset 'Z(P)] ->
     {in Z^# &, forall x y, #|'C_L[x]| = #|'C_L[y]| } ->
     let phi := 'chi[G]_i in
     {in Z^# &, forall x y, phi x = phi y} ->
   {in Z^#, forall x, isIntC (phi x) /\ dvdNC #|P| (phi x - phi 1%g)}.
Admitted.

(* This is Peterfalvi, Theorem (6.8). *)
(* We omit the semi-direct structure of L in assumption (a), since it is      *)
(* implied by our statement of assumption (c).                                *)
Theorem Sibley_coherence (L H W1 : {group gT}) :
  (*a*) [/\ odd #|L|, nilpotent H & normedTI H^# G L] ->
  (*b*) let calS := seqIndD H L H 1 in let tau := 'Ind[G, L] in
  (*c*) [\/ (*c1*) [Frobenius L = H ><| W1]
         |  (*c2*) exists2 W2 : {group gT}, prime #|W2| /\ W2 \subset H^`(1)%G
                   & centralDade_hypothesis H^# G H L H (W1 <*> W2) W1 W2] ->
  coherent calS L^# tau.
Proof.
set A := H^# => [][oddL nilH tiA] S tau structL.
set case_c1 := [Frobenius L = H ><| _] in structL.
have sLG: L \subset G by have [_ /eqP <-] := andP tiA; exact: subsetIl.
have [defL ntH ntW1]: [/\ H ><| W1 = L, H :!=: 1 & W1 :!=: 1]%g.
  have [/Frobenius_context[]// | [W2 _ [? [[-> -> _ _] [ntW2]]]]] := structL.
  by move/subG1_contra->.
have [nsHL _ /mulG_sub[sHL sW1L] _ _] := sdprod_context defL.
have uccS: [/\ uniq S, {subset S <= S}, ~~ has cfReal S & conjC_closed S].
  by rewrite seqInd_uniq seqInd_notReal //; split=> //; exact: cfAut_seqInd.
have defZS: 'Z[S, L^#] =i 'Z[S, A] by exact: vcharD1_seqInd.
have c1_irr: case_c1 -> {subset S <= irr L}.
  move/FrobeniusWker=> frobL _ /seqIndC1P[i nz_i ->].
  exact: irr_induced_Frobenius_ker.
move defW2: 'C_H(W1)%G => W2; move defW: (W1 <*> W2)%G => W.
pose c2hyp := centralDade_hypothesis A G H L H W W1 W2.
have c1W2: case_c1 -> W2 = 1%G by move/Frobenius_trivg_cent/group_inj <-.
have{structL} c2W2: ~~ case_c1 -> [/\ prime #|W2|, W2 \subset H^`(1)%G & c2hyp].
  case: structL => [-> // | [W3 [prW3 sW3] W3hyp] _]; rewrite /c2hyp -defW.
  suffices /group_inj->: W2 :=: W3 by [].
  have [/= _ [[_ _ _ cycW1] [_ _ _ prW13] _ _ _]] := W3hyp.
  have [x defW1] := cyclicP cycW1; rewrite -defW2 /= defW1 cent_cycle prW13 //.
  by rewrite !inE defW1 cycle_id -cycle_eq1 -defW1 ntW1.
pose sigma := @cyclicTIsigma _ G W W1 W2.
have [R scohS oRW]: exists2 R, subcoherent S tau R & ~~ case_c1 ->
  {in [predI S & irr L] & irr W, forall phi w, orthogonal (R phi) (sigma w)}.
- have sAG: A \subset G^# by rewrite setSD // (subset_trans (normal_sub nsHL)).
  have Itau: {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]}.
    split=> [xi1 xi2 | xi].
      rewrite !defZS => /vchar_on Axi1 /vchar_on Axi2.
      exact: normedTI_isometry Axi1 Axi2.
    rewrite !vcharD1E => /andP[Zxi /eqP xi1_0].
    rewrite cfInd1 // xi1_0 mulr0 eqxx cfInd_vchar //.
    by apply: vchar_trans_on Zxi; exact: seqInd_virrW.
  have [Hc1 | Hc2] := boolP case_c1.
    suffices [R]: {R | subcoherent S tau R} by exists R.
    by apply: irr_subcoherent; first by case: uccS (c1_irr Hc1).
  have [_ _ ddA0] := c2W2 Hc2.
  have [R [subcohR oRW _]] := PtypeDade_subcoherent ddA0 uccS.
  exists R => //; set tau0 := Dade _ in subcohR.
  have Dtau: {in 'CF(L, A), tau =1 tau0}.
    have nAL: L \subset 'N(A) by rewrite normD1 normal_norm.
    move=> phi Aphi; rewrite /tau0 -(restr_DadeE ddA0 (subsetUl _ _) nAL) //.
    apply/esym/Dade_Ind=> //; set ddA := restr_Dade_hyp _ _ _.
    by rewrite -subG1 -setD_eq0 -/A in ntH; case/Dade_normedTI_P: tiA.
  have [Sok _ oSS Rok oRR] := subcohR; split=> // phi Sphi.
  have [ZR oNR <-] := Rok _ Sphi; split=> //.
  by rewrite Dtau ?irr_vchar_on ?sub_conjC_vchar ?(seqInd_virr nsHL Sphi).
have [nsH'H nsH'L] := (der_normal 1 H, char_normal_trans (der_char 1 H) nsHL).
have [nH'L solH] := (normal_norm nsH'L, nilpotent_sol nilH).
have ltH'H: H^`(1)%g \proper H by rewrite ?(nil_comm_properl nilH) ?subsetIidl.
have coHW1: coprime #|H| #|W1|.
  have [/Frobenius_coprime// | /c2W2[_ _]] := boolP case_c1.
  by rewrite (coprime_sdprod_Hall defL) (sdprod_Hall defL) => [] [? [[]]].
have oW1: #|W1| = #|L : H| by rewrite -divgS // -(sdprod_card defL) mulKn.
have frobL1: [Frobenius L / H^`(1) = (H / H^`(1)) ><| (W1 / H^`(1))]%g.
  apply: (Frobenius_coprime_quotient defL nsH'L) => //; split=> // x W1x.
  have [/Frobenius_reg_ker-> //|] := boolP case_c1; first exact: sub1G.
  by case/c2W2=> _ sW2H' [/= ? [_ [_ _ _ -> //]]].
have odd_frobL1: odd_Frobenius_quotient H L 1.
  have ? := FrobeniusWker frobL1.
  by split=> //=; rewrite ?joingG1 // normal1 sub1G quotient_nil.
without loss [/p_groupP[p p_pr pH] not_cHH]: / p_group H /\ ~~ abelian H.
  have [//| [_] [p []]] := non_coherent_chief nsHL solH scohS odd_frobL1.
  rewrite (isog_abelian (quotient1_isog H)) -(isog_pgroup p (quotient1_isog H)).
  by move=> /pgroup_p-> -> _; exact.
have sylH: p.-Sylow(G) H. (* required for (6.7) *)
  have sylH: p.-Sylow(L) H.
    apply/and3P; split=> //; rewrite -oW1 p'natE // -prime_coprime //.
    by case/pgroup_pdiv: pH coHW1 => // _ _ [m ->]; rewrite coprime_pexpl.
  have [P sylP sHP] := Sylow_superset (subset_trans sHL sLG) pH.
  have [sPG pP _] := and3P sylP; have nilP := pgroup_nil pP.
  rewrite -(nilpotent_sub_norm nilP sHP) // (sub_normal_Hall sylH) //.
    exact: pgroupS (subsetIl P _) pP.
  by have [_ /eqP <-] := andP tiA; rewrite normD1 setSI.
pose caseA := 'Z(H) :&: W2 == [1].
have caseB_P: ~~ caseA -> [/\ ~~ case_c1, W2 :!=: [1] & W2 \subset 'Z(H)].
  rewrite /caseA; have [-> |] := eqsVneq W2 [1]; first by rewrite setIg1 eqxx.
  have [/c1W2-> | /c2W2[prW2 _ _] ->] := boolP case_c1; first by rewrite eqxx.
  by rewrite setIC => /prime_meetG->.
pose Z := if caseA then ('Z(H) :&: H^`(1))%G else W2.
have /subsetIP[sZZ sZH']: Z \subset 'Z(H) :&: H^`(1)%g.
  by rewrite /Z; case: ifPn => // /caseB_P[/c2W2[]] *; exact/subsetIP.
have caseB_cZL: ~~ caseA -> Z \subset 'Z(L).
  move=> inB; have [_ _ /subsetIP[sW2H cW2H]] := caseB_P inB.
  have [_ mulHW1 _ _] := sdprodP defL.
  rewrite /Z (negPf inB) subsetI (subset_trans sW2H) //.
  by rewrite -mulHW1 centM subsetI cW2H -defW2 subsetIr.
have nsZL: Z <| L.
  have [inA | /caseB_cZL/sub_center_normal//] := boolP caseA.
  by rewrite /Z inA (char_normal_trans _ nsHL) // charI ?gFchar.
have ntZ: Z :!=: [1].
  rewrite /Z; case: ifPn => [_ | /caseB_P[]//].
  by rewrite /= setIC meet_center_nil // (sameP eqP derG1P).
have nsZH := sub_center_normal sZZ; have [sZH nZH] := andP nsZH.
have regZL: {in Z^# &, forall x y, #|'C_L[x]| = #|'C_L[y]| }.
  have [inA | /caseB_cZL cZL] := boolP caseA; last first.
    suffices defC x: x \in Z^# -> 'C_L[x] = L by move=> x y /defC-> /defC->.
    by case/setD1P=> _ /(subsetP cZL)/setIP[_]; rewrite -sub_cent1 => /setIidPl.
  suffices defC x: x \in Z^# -> 'C_L[x] = H by move=> x y /defC-> /defC->.
  case/setD1P=> ntx Zx; have /setIP[Hx cHx] := subsetP sZZ x Zx.
  have [_ <- _ _] := sdprodP defL; rewrite -group_modl ?sub_cent1 //=.
  suffices ->: 'C_W1[x] = 1%g by rewrite mulg1.
  have [/Frobenius_reg_compl-> // | in_c2] := boolP case_c1; first exact/setD1P.
  have [_ _ [/= ? [_ [_ _ _ regW1] _] _ _]] := c2W2 in_c2.
  apply: contraNeq ntx => /trivgPn[y /setIP[W1y cxy] nty].
  rewrite -in_set1 -set1gE -((_ =P [1]) inA) -(regW1 y) 2!inE ?nty //.
  by rewrite inE cent1C cHx Hx.
have Zconst_modH := constant_irr_mod_TI_Sylow sylH oddL tiA
                                (And3 nsZL ntZ sZZ) regZL.
pose X := seqIndD H L Z 1; pose Y := seqIndD H L H H^`(1).
have X'Y: ~~ has (mem X) Y.
  apply/hasPn=> _ /seqIndP[i /setIdP[_ kH'i] ->]; rewrite inE in kH'i.
  by rewrite /= mem_seqInd ?normal1 // !inE sub1G (subset_trans sZH').
have irrY: {subset Y <= irr L}.
  move=> _ /seqIndP[i /setIdP[not_kHi kH'i] ->]; rewrite !inE in not_kHi kH'i.
  have kH'iInd: (H^`(1))%G \subset cfker ('Ind[L] 'chi_i).
    by rewrite sub_cfker_Ind_irr ?normal_norm.
  rewrite -(cfQuoK nsH'L kH'iInd) -induced_quotientE // -quo_IirrE //.
  set i1 := quo_Iirr _ i; have /irrP[k ->]: 'Ind 'chi_i1 \in irr (L / H^`(1)).
    apply: irr_induced_Frobenius_ker; first exact: FrobeniusWker frobL1.
    apply: contraNneq not_kHi; rewrite -(quo_IirrK nsH'H kH'i) -/i1 => ->.
    by rewrite mod_IirrE // chi0_1 cfMod_cfun1 ?cfker_cfun1.
  by rewrite -mod_IirrE ?irr_chi.
have uniY: {in Y, forall phi : 'CF(L), phi 1%g = #|W1|%:R}.
  move=> _ /seqIndP[i /setIdP[_ kH'i] ->]; rewrite inE -lin_irr_der1 in kH'i.
  rewrite cfInd1 // -divgS // -(sdprod_card defL) mulKn //.
  by case/andP: kH'i => _ /eqP->; rewrite mulr1.
have sXS: {subset X <= S} by apply: seqIndS; rewrite Iirr_kerDS.
have sYS: {subset Y <= S} by apply: seqIndS; rewrite Iirr_kerDS ?sub1G.
have scohY: subcoherent Y tau R.
  apply: (subset_subcoherent scohS); rewrite seqInd_uniq.
  by split=> //; exact: cfAut_seqInd.
have [tau1 cohY]: coherent Y L^# tau.
  apply/(uniform_degree_coherence scohY)/(@all_pred1_constant _ #|W1|%:R).
  by apply/allP=> _ /mapP[phi Yphi ->]; rewrite /= uniY.
have [[Itau1 Ztau1] Dtau1] := cohY.
have [eta1 Yeta1]: exists eta1, eta1 \in Y.
  pose IY := Iirr_kerD H H H^`(1)%G.
  have [IY0 | [j IYj]] := set_0Vmem IY; last first.
    by exists ('Ind 'chi_j); apply/seqIndP; exists j.
  have /idPn[]: \sum_(j \in IY) ('chi_j 1%g) ^+ 2 == 0 by rewrite IY0 big_set0.
  rewrite sum_Iirr_kerD_square ?der_sub // indexgg mul1r subr_eq0.
  by rewrite -(eqN_eqC _ 1) indexg_eq1 proper_subn.
have caseA_coh12: caseA -> coherent (X ++ Y) L^# tau.
  move=> haveA; have scohX: subcoherent X tau R.
    apply: (subset_subcoherent scohS); rewrite seqInd_uniq.
    by split=> //; exact: cfAut_seqInd.
  have irrX: {subset X <= irr L}.
    have [/c1_irr irrS | /c2W2[]] := boolP case_c1.
      move=> phi Xphi; apply: irrS; apply: seqIndS phi Xphi.
      by rewrite Iirr_kerDS // (subset_trans sZH') ?der_sub.
    move=> prW2 sW2H' [/= _ PtypeL _ _].
    have [[_ _ _ cycW1] [ntW2 sW2H cycW2 prW1H] [W1xW2 oddW]] := PtypeL.
    have nZL := normal_norm nsZL; have nZW1 := subset_trans sW1L nZL.
    have isoW2: (W2 / Z)%g \isog W2.
      apply/isog_symr/quotient_isog; first exact: subset_trans sW2H nZH.
      by rewrite -(setIidPr sZZ) setIAC ((_ =P [1]) haveA) setI1g.
    have PtypeL1:
      (cyclicDade_hypothesis (L / Z) (H / Z) (W / Z) (W1 / Z) (W2 / Z))%G.
    - split; last 1 first.
      + rewrite quotient_odd // (quotient_coprime_dprod _ W1xW2) //.
          by rewrite -defW join_subG nZW1 (subset_trans sW2H).
        by rewrite coprime_sym (coprimeSg sW2H).
      + have defLZ := quotient_coprime_sdprod nZL defL coHW1.
        rewrite -(sdprod_Hall defLZ) -(coprime_sdprod_Hall defLZ).
        rewrite coprime_morph ?quotient_cyclic //.
        rewrite -(isog_eq1 (quotient_isog _ _)) ?coprime_TIg //.
        by rewrite (coprimeSg sZH).
      rewrite (isog_eq1 isoW2) quotientS ?quotient_cyclic //.
      split=> //= _ /(subsetP (quotientD1 _ _))/morphimP[x nZx ntW1x ->].
      have [_ W1x] := setD1P ntW1x; rewrite -cent_cycle -quotient_cycle //.
      rewrite -coprime_quotient_cent ?(coprimegS _ coHW1) ?cycle_subG //.
      by rewrite cent_cycle prW1H.
    pose Ichi := @Dade_chi _ L H W W1 W2.
    pose Ichi1 := @Dade_chi _ (L / Z) (H / Z) (W / Z) (W1 / Z) (W2 / Z).
    have eq_Ichi: codom (fun j1 => mod_Iirr (Ichi1 j1)) =i codom Ichi.
      apply/subset_cardP.
        rewrite !card_codom; last first; try exact: Dade_chi_inj.
          apply: inj_comp (Dade_chi_inj PtypeL1).
          exact: can_inj (mod_IirrK (sub_center_normal sZZ)).
        by rewrite !card_ord !NirrE (nclasses_isog isoW2).
      apply/subsetP=> _ /imageP[/= j1 _ ->].
      apply: contraR (Dade_mu_not_irr PtypeL1 j1).
      case/(Dade_Ind_chi'_irr PtypeL)=> /irrP[ell Dell] _.
      rewrite -(Dade_Ind_chi PtypeL1) -/Ichi1 -['chi__]cfModK //.
      rewrite -mod_IirrE ?induced_quotientE ?Dell ?mod_IirrE ?cfker_Mod //.
      rewrite -quo_IirrE ?irr_chi // -Dell sub_cfker_Ind_irr //.
      by rewrite mod_IirrE ?cfker_Mod.
    move=> _ /seqIndP[k /setDP[_ kZ'k] ->].
    case: ((Dade_Ind_chi'_irr PtypeL) k) => //; rewrite -eq_Ichi.
    by apply: contra kZ'k => /imageP[j1 _ ->]; rewrite inE mod_IirrE ?cfker_Mod.
  have [//|] := seqIndD_irr_coherence nsHL solH scohS odd_frobL1 _ irrX.
  rewrite -/X => defX [tau2 cohX]; have [[Itau2 Ztau2] Dtau2] := cohX.
  have [xi1 Xxi1 Nd]:
    exists2 xi1, xi1 \in X & forall xi, xi \in X -> dvdC (xi1 1%g) (xi 1%g).
  - pose IX := Iirr_kerD H Z 1%G; have [i0 IXi0]: exists i0, i0 \in IX.
      apply/set0Pn; apply: contraNneq ntZ => IX_0.
      have: \sum_(i \in IX) ('chi_i 1%g) ^+ 2 == 0 by rewrite IX_0 big_set0.
      rewrite sum_Iirr_kerD_square ?normal1 ?sub1G // indexg1 mulf_eq0.
      by rewrite (negPf (neq0GiC H Z)) subr_eq0 trivg_card1 eqN_eqC.
    have:= erefl [arg min_(i < i0 | i \in IX) getNatC ('chi_i 1%g)].
    have [//|{i0 IXi0} i1 IXi1 min_i1 _] := arg_minP.
    exists ('Ind 'chi_i1); first by apply/seqIndP; exists i1.
    move=> _ /seqIndP[i /min_i1 le_i1_i] ->; rewrite !cfInd1 //.
    have pHP := p_natP (pnat_dvd _ pH).
    move: (dvd_irr1_cardG i1) (dvd_irr1_cardG i) le_i1_i.
    rewrite !irr1_degree -!natr_mul !dvdC_nat => /pHP[m1 ->] /pHP[m ->].
    rewrite !getNatC_nat leq_exp2l ?prime_gt1 // => /subnKC <-.
    by rewrite expn_add mulnA dvdn_mulr.
  pose d (xi : 'CF(L)) : algC := (getNatC (xi 1%g / xi1 1%g))%:R.
  have{Nd} def_d xi: xi \in X -> xi 1%g = d xi * xi1 1%g.
    rewrite /d => Xxi; move: Xxi (Nd _ Xxi) => /irrX/irrP[i ->].
    have /irrX/irrP[i1 ->] := Xxi1.
    rewrite !irr1_degree dvdC_nat => /dvdnP[q ->].
    by rewrite natr_mul -irr1_degree mulfK ?irr1_neq0 // getNatC_nat.
  have d_xi1: d xi1 = 1.
    by apply: (mulIf (seqInd1_neq0 nsHL Xxi1)); rewrite mul1r -def_d.
  have oXY: orthogonal X Y.
    apply/orthogonalP=> xi eta Xxi Yeta.
    have [_ _ /pairwise_orthogonalP[_ oSS] _ _] := scohS.
    apply: oSS; try by [exact: sXS | exact: sYS].
    by rewrite (memPn (hasPn X'Y _ Yeta)).
  have [_ [Itau Ztau] /orthogonal_free freeS _ _] := scohS.
  have o_tauXY: orthogonal (map tau2 X) (map tau1 Y).
    apply/orthogonalP=> _ _ /mapP[xi Xxi ->] /mapP[eta Yeta ->].
    have [/irrP[i Di] /irrP[j Dj]] := (irrX _ Xxi, irrY _ Yeta).
    rewrite Di Dj in Xxi Yeta *.
    have [Zi oNi Zi2 vi] := coherent_seqInd_conjCirr scohX cohX Xxi.
    have [Zj oNj Zj2 vj] := coherent_seqInd_conjCirr scohY cohY Yeta.
    apply: (orthonormal_vchar_diff_ortho (conj Zi Zj)); first by rewrite !oNi.
    rewrite vi vj !andbT -2!raddf_sub Dtau1 // Dtau2 //.
    rewrite Itau ?(vchar_subset _ sXS Zi2) ?(vchar_subset _ sYS Zj2) //.
    have [[Xi2 _] [Yj2 _]] := (andP Zi2, andP Zj2).
    by rewrite (span_orthogonal oXY) // eqxx.
  have [a Na Dxi11]: exists2 a, isNatC a & xi1 1%g = a * #|W1|%:R.
    have [i1 _ ->] := seqIndP Xxi1.
    exists ('chi_i1 1%g); first exact: isNatC_irr1.
    by rewrite cfInd1 // -divgS // -(sdprod_card defL) ?mulKn // mulrC.
  pose psi1 := xi1 - a *: eta1; have Za: isIntC a by rewrite isIntCE Na.
  have Zpsi1: psi1 \in 'Z[S, L^#].
    rewrite vcharD1E !cfunE (uniY _ Yeta1) -Dxi11 subrr eqxx.
    by rewrite sub_vchar ?scale_vchar ?mem_vchar ?(sXS _ Xxi1) // sYS.    
  have [Y1 [X1 [dX1 dY1 oX1tauY]]] := orthogonal_split (map tau1 Y) (tau psi1).
  have [uX uY]: uniq X /\ uniq Y by rewrite !seqInd_uniq.
  have oY: orthonormal Y by exact: sub_orthonormal (irr_orthonormal L).
  have oYtau: orthonormal (map tau1 Y) by exact: map_orthonormal.
  have{dX1 Y1 dY1} [b Zb Dpsi1]: {b | isIntC b &
    tau psi1 = X1 - a *: tau1 eta1 + b *: (\sum_(eta <- Y) tau1 eta)}.
  - exists ('[tau psi1, tau1 eta1] + a).
      rewrite isIntC_add // cfdot_vchar_Int ?Ztau1 ?seqInd_vcharW //.
      exact: vcharW (Ztau _ Zpsi1).
    rewrite {1}dX1 addrC -addrA; congr (_ + _).
    have [_ -> ->] := orthonormal_span oYtau dY1.
    rewrite -[Y1](addrK X1) -dX1 big_map !(big_rem eta1 Yeta1) /=.
    rewrite cfdot_subl (orthoPl oX1tauY) ?map_f // subr0.
    rewrite scaler_addr addrA; congr (_ + _).
      by rewrite addrC -scaleNr -scaler_addl addrK.
    rewrite raddf_sum; apply: eq_big_seq => eta.
    rewrite mem_rem_uniq ?seqInd_uniq // => /andP[eta1'eta /= Yeta].
    congr (_ *: _); rewrite cfdot_subl (orthoPl oX1tauY) ?map_f // subr0 addrC.
    apply: canRL (subrK _) _; rewrite -2!raddf_sub /=.
    have Zeta: (eta - eta1) \in 'Z[Y, L^#].
      by rewrite vcharD1E sub_vchar ?seqInd_vcharW //= !cfunE !uniY ?subrr.
    rewrite Dtau1 // Itau // ?(vchar_subset _ sYS) //.
    rewrite cfdot_subl cfdotZl !cfdot_subr 2?(orthogonalP oXY) // subr0 add0r.
    have [_ oYY] := orthonormalP oY; rewrite !oYY // eqxx.
    by rewrite eq_sym (negPf eta1'eta) add0r mulrN mulr1 opprK.
  pose psi := 'Res[L] (tau1 eta1).
  have [X2 [xi' [dxi' dX2 oxi'X]]] := orthogonal_split X psi.
  have oX: orthonormal X by exact: sub_orthonormal (irr_orthonormal L).
  have Zpsi: psi \in 'Z[irr L] by rewrite cfRes_vchar ?Ztau1 ?seqInd_vcharW.
  pose sumXd := \sum_(xi <- X) d xi *: xi.
  have Zxi1Xd xi: xi \in X -> xi - d xi *: xi1 \in 'Z[X, L^#].
    move=> Xxi; rewrite vcharD1E !cfunE -def_d // subrr eqxx.
    by rewrite sub_vchar ?scale_vchar ?seqInd_vcharW ?isIntC_nat.
  have{dxi' X2 dX2} [c Zc Dpsi]: {c | isIntC c & psi = c *: sumXd + xi'}.
    exists '[psi, xi1]; first by rewrite cfdot_vchar_Int ?(seqInd_virrW Xxi1).
    rewrite {1}dxi'; congr (_ + _); have [_ -> ->] := orthonormal_span oX dX2.
    rewrite -[X2](addrK xi') -dxi' raddf_sum; apply: eq_big_seq => /= xi Xxi.
    rewrite cfdot_subl (orthoPl oxi'X) // subr0 scalerA; congr (_ *: _).
    apply/eqP; rewrite -subr_eq0 mulrC -[d xi]isNatC_conj ?isNatC_nat //.
    rewrite -cfdotZr -cfdot_subr cfdot_Res_l -Dtau2 ?Zxi1Xd //.
    rewrite cfdotC raddf_sub raddfZ_NatC ?isNatC_nat // cfdot_subl cfdotZl.
    by rewrite !(orthogonalP o_tauXY) ?map_f // mulr0 subr0 conjC0.
  have Exi' z: z \in Z -> xi' z = xi' 1%g.
    move=> Zz; rewrite [xi']cfun_sum_cfdot !sum_cfunE; apply: eq_bigr => ell _.
    have [Xell |] := boolP ('chi_ell \in X).
      by rewrite !cfunE (orthoPl oxi'X) ?mul0r.
    by rewrite !cfunE defX inE /= irr_chi negbK => /subsetP/(_ z Zz)/cfker1->.
  have Eba: '[psi, psi1] = b - a.
    rewrite cfdot_Res_l -/tau Dpsi1 -addrA !cfdotDr cfdotNr cfdotZr.
    rewrite cfdotC (orthoPl oX1tauY) ?map_f // conjC0 add0r addrC.
    rewrite cfdotC raddf_sum cfproj_sum_orthonormal // !isIntC_conj //.
    by have [_ ->] := orthonormalP oYtau; rewrite ?map_f // eqxx mulr1.
  have nz_xi11: xi1 1%g != 0 by have /irrX/irrP[i ->] := Xxi1; exact: irr1_neq0.
  have {Eba} Ebc: dvdC a (b - c).
    rewrite -[b](subrK a) -Eba cfdot_subr {1}Dpsi cfdotDl cfdotZl.
    rewrite cfproj_sum_orthonormal // (orthoPl oxi'X) // addr0 d_xi1 mulr1.
    rewrite addrC -addrA addKr dvdC_add // cfdotZr isIntC_conj //.
    by rewrite dvdC_opp dvdC_mulr // cfdot_vchar_Int ?(seqInd_virrW Yeta1).
  have DsumXd: sumXd = (xi1 1%g)^-1 *: (cfReg L - cfReg (L / Z)%g %% Z)%CF.
    apply: canRL (scalerK nz_xi11) _; rewrite !cfReg_sum 2!linear_sum /=.
    pose F (xi : 'CF(L)) := xi 1%g *: xi; transitivity (\sum_(xi <- X) F xi).
      by apply: eq_big_seq => xi Xxi; rewrite scalerA mulrC -def_d.
    rewrite (bigID (mem (Iirr_ker L Z))) /=; apply: canRL (addrK _) _.
    rewrite addrC; congr (_ + _).
      rewrite (eq_bigl _ _ (in_set _)) (reindex _ (mod_Iirr_bij nsZL)) /=.
      apply: eq_big => [i | i _]; first by rewrite mod_IirrE ?cfker_Mod.
      by rewrite linearZ mod_IirrE // cfMod1.
    transitivity (\sum_(xi <- [image 'chi_i | i <- [predC Iirr_ker L Z]]) F xi).
      apply: eq_big_perm; apply: uniq_perm_eq => // [|xi].
        by rewrite (map_inj_uniq chi_inj) ?enum_uniq.
      rewrite defX inE /=; apply/andP/imageP=> [[/irrP[i ->] kerZ'i] | [i]].
        by exists i; rewrite ?inE.
      by rewrite !inE => ? ->; rewrite irr_chi.
    by rewrite big_map big_filter; apply: eq_bigl => i; rewrite !inE.
  have eta1tauZ z: z \in Z^# -> tau1 eta1 z - tau1 eta1 1%g = - c * #|H|%:R / a.
    case/setD1P=> ntz Zz; transitivity (psi z - psi 1%g).
      by rewrite !cfResE ?(subsetP (normal_sub nsZL)).
    rewrite Dpsi DsumXd !cfunE Exi' ?cfuniE ?normal1 // set11 inE (negPf ntz).
    rewrite mulr0 mulr1 sub0r Dxi11 cfker1 ?cfker_Reg_Quo //.
    set cc := c * _ + _; rewrite 2!mulr_addr -[rhs in _ - rhs]addrA -/cc.
    rewrite addrC oppr_add {cc}subrK -(sdprod_card defL) mulnC natr_mul.
    by rewrite invf_mul !mulrA divfK ?neq0GC // mulrAC -2!mulNr.
  have{eta1tauZ} dvHpsi: dvdNC #|H| (- c * #|H|%:R / a).
    have /dirrP[e [i Deta1]]: tau1 eta1 \in dirr G.
      rewrite dirrE Ztau1 ?Itau1 ?seqInd_vcharW //=.
      by have [_ ->] := orthonormalP oY; rewrite ?eqxx.
    have [z ntz Zz] := trivgPn _ ntZ; have Z1z: z \in Z^# by exact/setD1P.
    have /(Zconst_modH i)[|_] := Z1z.
      move=> z1 z2 Zz1 Zz2; rewrite -(canLR (signrZK e) Deta1) !cfunE.
      by apply/eqP; do 2!rewrite eq_sym (canRL (subrK _) (eta1tauZ _ _)) //.
    rewrite -(canLR (signrZK e) Deta1) !cfunE -mulr_subr eta1tauZ //.
    by rewrite dvdC_mul_sign.
  have nz_a: a != 0 by rewrite Dxi11 mulf_eq0 negb_or neq0GC andbT in nz_xi11.
  have{dvHpsi} dv_ac: dvdC a c.
    move: dvHpsi; rewrite !mulNr mulrAC dvdC_opp => /dvdCP[q Zq].
    by move/(mulIf (neq0GC H))/(canRL (divfK nz_a))->; exact: dvdC_mull.
  have{Ebc dv_ac} /dvdCP[q Zq Db]: dvdC a b by rewrite -[b](subrK c) dvdC_add.
  pose m : algC := (size Y)%:R.
  have Da1: 1 + a ^+ 2 = '[X1] + a ^+ 2 * ((q - 1) ^+ 2 + (m - 1) * q ^+ 2).
    transitivity '[psi1].
      rewrite cfnorm_subd; last by rewrite cfdotZr (orthogonalP oXY) ?mulr0. 
      rewrite cfnormZ int_normCK //.
      have [_ -> //] := orthonormalP oX; have [_ -> //] := orthonormalP oY.
      by rewrite !eqxx mulr1.
    rewrite -Itau // Dpsi1 -addrA cfnormDd; last first.
      rewrite addrC cfdot_subr !cfdotZr cfdot_sumr (orthoPl oX1tauY) ?map_f //.
      rewrite big_seq big1 ?mulr0 ?subrr // => eta Yeta.
      by rewrite (orthoPl oX1tauY) ?map_f //.
    congr (_ + _); rewrite cfnormD cfnormN !cfnormZ.
    have [_ ->] := orthonormalP oYtau; rewrite ?map_f // eqxx mulr1.
    rewrite cfnorm_map_orthonormal // -/m !int_normCK // cfdotNl cfdotZl.
    rewrite linear_sum cfdotC cfproj_sum_orthonormal // rmorphN rmorphM.
    rewrite conjCK !isIntC_conj // -mulr2n mulNrn -[_ - _]addrAC.
    rewrite mulr_addr -{1}[m](addNKr 1) mulr_addr mulr1 addrA -sqrr_sub.
    congr (_ + _); last by rewrite mulrCA -exprn_mull (mulrC a) addrC -Db mulrC.
    by rewrite -exprn_mull -sqrrN oppr_sub mulr_subr mulr1 (mulrC a) -Db.
  have{Da1} maxq: ~~ (2%:R <= (q - 1) ^+ 2 + (m - 1) * q ^+ 2).
    have a2_gt1: a ^+ 2 > 1.
      have /seqIndP[i1 /setDP[_ not_kerH'i1] Dxi1] := Xxi1.
      apply: contraR not_kerH'i1; rewrite inE ltC1exp ?posC_Nat //.
      have [n Da] := isNatCP a Na; rewrite Da -(ltn_ltC 1) -leqNgt leq_eqVlt.
      rewrite ltnNge lt0n !eqN_eqC -{n}Da nz_a orbF => /eqP a_eq1.
      rewrite (subset_trans sZH') // -lin_irr_der1 /lin_char irr_char.
      rewrite -(inj_eq (mulfI (neq0GiC L H))) -cfInd1 // -Dxi1 Dxi11 a_eq1.
      by rewrite mul1r mulr1 -divgS //= -(sdprod_card defL) mulKn.
    rewrite -(leC_pmul2l _ _ (ltC_trans sposC1 a2_gt1)) ltC_geF // mulr_natr.
    apply: leC_ltC_trans (_ : 1 + a ^+ 2 < _); last by rewrite ltC_add2r.
    by rewrite Da1 -leC_sub addrK cfnorm_posC.
  clear psi Dpsi Zpsi Zb c sumXd DsumXd Zc xi' Exi' oxi'X.
  wlog{Dpsi1 Itau1 Ztau1 Dtau1 oYtau b q maxq Db Zq} Dpsi1:
    tau1 cohY o_tauXY oX1tauY / tau psi1 = X1 - a *: tau1 eta1.
  - move=> IH; have [q0 | nz_q] := eqVneq q 0.
      by apply: (IH tau1) => //; rewrite Dpsi1 Db q0 mul0r scale0r addr0.
    have m1_ge1: 1 <= m - 1.
      have /irrY/irrP[j1 Deta1] := Yeta1; rewrite Deta1 in Yeta1.
      rewrite -(leC_add2r 1) subrK -(leq_leC 2).
      exact: seqInd_nontrivial Yeta1.
    have q1: q = 1.
      apply: contraNeq maxq; rewrite -subr_eq0 => nz_q1.
      rewrite leC_add // ?isIntC_expr2_ge1 ?isIntC_sub //.
      rewrite (leC_trans m1_ge1) // -{1}[m - 1]mulr1.
      by rewrite leC_pmul2l ?isIntC_expr2_ge1 // (ltC_leC_trans sposC1).
    have szY2: (size Y <= 2)%N.
      move: maxq; rewrite q1 subrr exprS mul0r add0r mulrA !mulr1.
      by rewrite -(leC_add2r 1) subrK -mulrSr -leq_leC -leqNgt.
    have [[_ nrY ccY] _ _ _ _] := scohY.
    have defY: perm_eq Y (eta1 :: eta1^*)%CF.
      have uYeta: uniq (eta1 :: eta1^*)%CF.
        by rewrite /= andbT inE eq_sym (hasPn nrY).
      rewrite perm_eq_sym uniq_perm_eq //.
      have [|//]:= leq_size_perm uYeta _ szY2.
      by apply/allP; rewrite /= Yeta1 ccY.
    have memYtau1c: {subset map (tau1 \o cfAut conjC) Y <= map tau1 Y}.
      by move=> _ /mapP[eta Yeta ->]; rewrite /= map_f ?ccY.     
    apply: (IH _ (dual_coherence scohY cohY szY2)).
    - rewrite (map_comp -%R) orthogonal_opp.
      by apply/orthogonalP=> phi psi ? /memYtau1c; exact: (orthogonalP o_tauXY).
    - rewrite (map_comp -%R) orthogonal_opp.
      by apply/orthoPl=> psi /memYtau1c; exact: (orthoPl oX1tauY).
    rewrite Dpsi1 (eq_big_perm _ defY) Db q1 /= mul1r big_cons big_seq1.
    by rewrite scaler_addr addrA subrK -scalerN opprK.
  have [[[Itau1 Ztau1] Dtau1] [_ oXX]] := (cohY, orthonormalP oX).
  have n1X1: '[X1] = 1.
    apply: (addIr '[a *: tau1 eta1]).
    rewrite -cfnorm_subd; last first.
      by rewrite cfdotZr (orthoPl oX1tauY) ?mulr0 ?map_f.
    rewrite -Dpsi1 Itau // cfnorm_subd; last first.
      by rewrite cfdotZr (orthogonalP oXY) ?mulr0.
    by rewrite !cfnormZ Itau1 ?seqInd_vcharW // oXX ?eqxx.
  without loss{Itau2 Ztau2 Dtau2} defX1: tau2 cohX o_tauXY / X1 = tau2 xi1.
    move=> IH; have [[_ nrX ccX] _ _ _ _] := scohX.
    have ZX: {subset X <= 'Z[X]} by exact: seqInd_vcharW.
    have dirrXtau xi: xi \in X -> tau2 xi \in dirr G.
      by move=> Xxi; rewrite dirrE Ztau2 1?Itau2 ?ZX //= oXX ?eqxx.
    have dirrX1: X1 \in dirr G.
      rewrite dirrE n1X1 eqxx -[X1](subrK (a *: tau1 eta1)) -Dpsi1.
      rewrite add_vchar ?scale_vchar ?(vcharW (Ztau _ _)) //.
      by rewrite Ztau1 ?seqInd_vcharW.
    have oX1_Xd xi:
      xi \in X -> xi != xi1 -> '[d xi *: tau2 xi1 - tau2 xi, X1] = d xi.
    - move=> Xxi xi1'xi; have ZXxi := Zxi1Xd xi Xxi.
      rewrite -[X1](subrK (a *: tau1 eta1)) -Dpsi1 cfdotDr cfdotZr addrC.
      rewrite cfdot_subl cfdotZl 2?(orthogonalP o_tauXY) ?map_f //.
      rewrite !(mulr0, subr0, conjC0) add0r -{1}raddfZ_NatC ?isNatC_nat //.
      rewrite -oppr_sub cfdotNl -raddf_sub Dtau2 //.
      rewrite Itau //; last exact: vchar_subset ZXxi.
      rewrite cfdot_subr cfdotZr addrC !cfdot_subl !cfdotZl.
      rewrite 2?(orthogonalP oXY) // !(mulr0, oppr0, add0r, conjC0).
      by rewrite !oXX // eqxx (negPf xi1'xi) add0r opprK mulr1.
   have Xxi2: xi1^*%CF \in X by exact: ccX.
   have xi1'2: xi1^*%CF != xi1 by exact: (hasPn nrX).
   have xi2tau_irr: - tau2 xi1^*%CF \in dirr G by rewrite dirr_opp dirrXtau.
   have d_xi2: d xi1^*%CF = 1.
     by rewrite /d cfunE isNatC_conj // (seqInd1_Nat Xxi1).
   have [||def_X1]:= cfdot_add_dirr_eq1 (dirrXtau _ Xxi1) xi2tau_irr dirrX1.
   - by rewrite -[tau2 xi1]scale1r -d_xi2 oX1_Xd.
   - exact: IH.
   have sX_xi12: {subset X <= xi1 :: xi1^*%CF}.
     apply/allP/allPn=> [[xi3 Xxi3 /norP[xi1'3 /norP[xi2'3 _]]]].
     suffices d3_0: d xi3 = 0.
       by have:= seqInd1_neq0 nsHL Xxi3; rewrite def_d // d3_0 mul0r eqxx.
     rewrite -oX1_Xd // def_X1 cfdotNr cfdot_subl cfdotZl !Itau2 ?ZX //.
     by rewrite !oXX // (negPf xi2'3) eq_sym (negPf xi1'2) mulr0 add0r opprK.
   have{sX_xi12 defX} defX: perm_eq X (xi1 :: xi1^*%CF).
     have uXxi: uniq (xi1 :: xi1^*)%CF by rewrite /= andbT inE eq_sym.
     rewrite perm_eq_sym uniq_perm_eq // => xi.
     by apply/idP/idP; [rewrite !inE => /pred2P[]-> | exact: sX_xi12].
    have szX2: (size X <= 2)%N by rewrite (perm_eq_size defX).
    apply: (IH _ (dual_coherence scohX cohX szX2)) def_X1.
    rewrite (map_comp -%R) orthogonal_sym orthogonal_opp -orthogonal_sym.
    apply/orthogonalP=> _ eta /mapP[xi Xxi ->].
    by apply: (orthogonalP o_tauXY); rewrite map_f ?ccX.
  have [[Itau2 Ztau2] Dtau2] := cohX.
  have [oXtau oYtau] := (map_orthonormal Itau2 oX, map_orthonormal Itau1 oY).
  have ooXY: pairwise_orthogonal (X ++ Y).
    by rewrite pairwise_orthogonal_cat oXY !orthonormal_orthogonal.
  have ooXYtau: pairwise_orthogonal (map tau2 X ++ map tau1 Y).
    by rewrite pairwise_orthogonal_cat o_tauXY !orthonormal_orthogonal.
  have [||tau3 Dtau3 Ztau3] := Zisometry_of_cfnorm ooXY ooXYtau.
  - rewrite !map_cat -!map_comp; congr (_ ++ _); apply: eq_in_map => phi Sphi.
      by rewrite /= Itau2 ?mem_vchar ?orthonormal_free.
    by rewrite /= Itau1 ?mem_vchar ?orthonormal_free.
  - apply/allP; rewrite all_cat !all_map; apply/andP; split.
      by apply/allP=> phi Xphi; rewrite /= Ztau2 ?mem_vchar ?orthonormal_free.
    by apply/allP=> phi Yphi; rewrite /= Ztau1 ?mem_vchar ?orthonormal_free.
  exists tau3; split => // phi; rewrite vcharD1E => /andP[].
  case/vchar_expansion=> z Zz ->{phi}; rewrite big_cat /= cfunE addrC addr_eq0.
  set phi2 := \sum_(i <- X) _; set phi1 := \sum_(i <- Y) _ => /eqP opp_phi12.
  have Dtau32: {in X, forall xi, tau3 xi = tau2 xi}.
    move=> xi Xxi; pose i := index xi X; have:= congr1 (nth 0 ^~ i) Dtau3.
    have ltiX: (i < size X)%N by rewrite index_mem.
    by rewrite map_cat !nth_cat !size_map ltiX !(nth_map 0) // nth_index.
  have Dtau31: {in Y, forall eta, tau3 eta = tau1 eta}.
    move=> eta Yeta; pose j := index eta Y.
    have:= congr1 (nth 0 ^~ (size X + j)%N) Dtau3.
    have ltjY: (j < size Y)%N by rewrite index_mem.
    rewrite map_cat !nth_cat !size_map ltnNge leq_addr addKn /=.
    by rewrite !(nth_map 0) // nth_index.
  transitivity (tau2 phi2 + tau1 phi1).
    rewrite raddfD !raddf_sum; congr (_ + _).
      by apply: eq_big_seq => xi Xxi; rewrite !raddfZ_IntC ?Zz //= Dtau32.
    by apply: eq_big_seq => eta Yeta; rewrite !raddfZ_IntC ?Zz //= Dtau31.
  pose u := - \sum_(xi <- X) z xi * d xi; pose v := \sum_(eta <- Y) z eta.
  have {opp_phi12} Dv: a * u = v.
    apply: (mulIf (neq0GC W1)); apply: etrans (etrans (esym opp_phi12) _).
      rewrite mulrAC -Dxi11 mulrN -mulr_sumr sum_cfunE /=; congr (- _).
      by apply: eq_big_seq => xi Xxi; rewrite mulrC cfunE -mulrA -def_d.
    rewrite -mulr_suml sum_cfunE /=.
    by apply: eq_big_seq => eta Yeta; rewrite cfunE uniY.
  have Zu: isIntC u.
    rewrite isIntC_opp big_seq isIntC_sum // => xi Xxi.
    by rewrite isIntC_mul ?Zz ?isIntC_nat.
  apply: (addIr (u *: tau psi1)); rewrite {1}Dpsi1 {Dpsi1}defX1.
  rewrite -raddfZ_IntC // scaler_subr -!raddfZ_IntC //= scalerA Dv.
  rewrite addrCA !addrA -!raddfD /= -addrA -raddf_sub.
  rewrite scaler_subr scalerA mulrC Dv addrCA -addrA addrA !scaleNr.
  rewrite !(addrC (- _)) !scaler_suml -!sumr_sub raddfD !raddf_sum /= -/tau.
  congr (_ + _); apply: eq_big_seq => xi Sxi.
    rewrite -scalerA -scaler_subr /tau !(raddfZ_IntC _ _ (Zz xi)) /= -/tau.
    by congr (_ *: _); rewrite Dtau2 ?Zxi1Xd.
  rewrite -scaler_subr /tau !raddfZ_IntC ?Zz //= Dtau1 // vcharD1E.
  by rewrite sub_vchar ?seqInd_vcharW //= !cfunE subr_eq0 !uniY.
have{caseA_coh12} cohXY: coherent (X ++ Y) L^# tau.
  have [/caseA_coh12// | caseB] := boolP caseA.
  have defZ: Z = W2 by rewrite /Z (negPf caseB).
  have{caseB} [case_c2 _ _] := caseB_P caseB; move/(_ case_c2) in oRW.
  have{case_c2} [pr_w2 _ PtypeL] := c2W2 case_c2; set w2 := #|W2| in pr_w2.
  have /cyclicP[z0 cycZ]: cyclic Z by rewrite defZ prime_cyclic.
  have idYZ: {in Y & Z^#, forall (eta : 'CF(L)) x, tau1 eta x = tau1 eta z0}.
    move=> eta x Yeta; rewrite !inE andbC cycZ => /andP[/cyclePmin[k]].
    rewrite orderE -cycZ defZ -/w2 => lt_k_w2 -> nt_z0k.
    have k_gt0: (0 < k)%N by rewrite lt0n (contraNneq _ nt_z0k) // => ->.
    have cokw2: coprime k w2 by rewrite coprime_sym prime_coprime // gtnNdvd.
    have sW2G: W2 \subset G by rewrite -defW2 subIset // (subset_trans sHL).
    have [u _ vcharGu]:= make_pi_cfAut G cokw2.
    have [] := vcharGu (tau1 eta) z0.
    - by rewrite Ztau1 ?seqInd_vcharW.
    - by rewrite -cycle_subG -cycZ defZ.
    move <- => [_|]; last by rewrite orderE -cycZ defZ.
    have /irrY/irrP[j def_eta] := Yeta; rewrite def_eta in Yeta *.
    have nAL: L \subset 'N(A) by rewrite normD1 normal_norm.
    pose ddA := restr_Dade_hyp PtypeL (subsetUl _ _) nAL.
    have cohY_Dade: coherent_with Y A (Dade ddA) tau1.
      split=> // phi YAphi; have Aphi := vchar_on YAphi.
      have sAG1: A \subset G^# by rewrite setSD ?(subset_trans sHL).
      rewrite Dtau1; last by rewrite (vchar_onS (setSD _ sHL)).
      apply/esym/Dade_Ind=> //.
      by rewrite -subG1 -setD_eq0 -/A in ntH; case/Dade_normedTI_P: tiA. 
    rewrite (cfAut_Dade_coherent cohY_Dade); last by []; last first.
    - rewrite seqInd_free // (seqInd_nontrivial_irr _ _ _ Yeta) //.
      by split; last exact: cfAut_seqInd.
    - exact: vcharD1_seqInd.
    rewrite -[cfAut u _](subrK 'chi_j) raddfD cfunE.
    apply: canLR (subrK _) _; rewrite subrr.
    have [_ ->] := cohY_Dade; last first.
      rewrite -opp_vchar oppr_sub -vcharD1_seqInd //.
      rewrite sub_Aut_vchar ?vchar_onG ?seqInd_vcharW ?cfAut_seqInd //.
      exact: seqInd_virrW.
    rewrite -{j}def_eta in Yeta *; rewrite Dade_id; last first.
      by rewrite !inE -cycle_eq1 -cycle_subG -cycZ ntZ.
    rewrite !cfunE cfker1 ?rmorph_NatC ?subrr ?(seqInd1_Nat Yeta) //.
    rewrite -cycle_subG -cycZ (subset_trans sZH') //.
    have [j /setDP[kerH'j _] ->] := seqIndP Yeta.
    by rewrite inE in kerH'j; rewrite sub_cfker_Ind_irr.
  have [_ [Itau _] oSS _ _] := scohS.
  have [uX uY]: uniq X /\ uniq Y by rewrite !seqInd_uniq.
  have oY: orthonormal Y by exact: sub_orthonormal (irr_orthonormal L).
  have oYtau: orthonormal (map tau1 Y) by exact: map_orthonormal.
  have oXY: orthogonal X Y.
    apply/orthogonalP=> xi eta Xxi Yeta.
    have /pairwise_orthogonalP[_ -> //] := oSS; [exact: sXS | exact: sYS |].
    by rewrite (memPn (hasPn X'Y _ Yeta)).
  have [Y1 Dpsi1 defY1]: exists2 Y1,
    forall i : Iirr Z, i != 0 ->
      exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
            & tau ('Ind 'chi_i - #|H : Z|%:R *: eta1) = X1 - #|H : Z|%:R *: Y1
      & Y1 = tau1 eta1 \/ size Y = 2 /\ Y1 = dual_iso tau1 eta1.
  - have [i0 nz_i0]: exists i0 : Iirr Z, i0 != 0.
      by apply: (ex_intro _ (Sub 1%N _)) => //; rewrite NirrE classes_gt1.
    pose psi1 := tau1 eta1; pose b := psi1 z0.
    pose a :=  (psi1 1%g - b) / #|Z|%:R.
    have sZL := normal_sub nsZL; have sZG := subset_trans sZL sLG.
    have Dpsi1: 'Res psi1 = a *: cfReg Z + b%:A.
      apply/cfun_inP=> z Zz.
      rewrite cfResE // !cfunE cfun1E Zz mulr1 cfuniE ?normal1 // inE.
      have [-> | ntz] := altP eqP; first by rewrite mulr1 divfK ?neq0GC ?subrK.
      by rewrite !mulr0 add0r idYZ // !inE ntz.
    have /dvdCP[x0 Zx0 Dx0]: dvdNC #|H : Z| a.
      have /dvdCP[x Zx Dx]: dvdNC #|H| (b - psi1 1%g).
        have psi1Z z: z \in Z^# -> psi1 z = b.
          case/setD1P=> ntz Zz; rewrite -(cfResE _ _ Zz) // Dpsi1 !cfunE cfun1E.
          by rewrite cfuniE ?normal1 // Zz inE (negPf ntz) !mulr0 mulr1 add0r.
        have /dirrP[e [i /(canLR (signrZK e)) Epsi1]]: psi1 \in dirr G.
          have [_ oYt] := orthonormalP oYtau.
          by rewrite dirrE oYt ?map_f // !eqxx Ztau1 ?seqInd_vcharW.
        have Zz: z0 \in Z^# by rewrite !inE -cycle_eq1 -cycle_subG -cycZ ntZ /=.
        have/(Zconst_modH i)[z1 Zz1 z2 Zz2 |_] := Zz.
          by rewrite -Epsi1 !cfunE !psi1Z.
        by rewrite -Epsi1 !cfunE -mulr_subr dvdC_mul_sign psi1Z.
      apply/dvdCP; exists (- x); first by rewrite isIntC_opp.
      rewrite /a -oppr_sub Dx -(LaGrange sZH) mulnC natr_mul -!mulNr.
      by rewrite !mulrA !mulfK ?neq0GC.
    pose x1 := '[eta1, 'Res psi1]; pose x := x0 + 1 - x1.
    have Zx: isIntC x.
      rewrite isIntC_sub ?isIntC_add // cfdot_vchar_Int //.
        exact: (seqInd_virrW Yeta1).
      by rewrite cfRes_vchar // Ztau1 ?seqInd_vcharW.
    pose Y1 := - \sum_(eta <- Y) (x - (eta == eta1)%:R) *: tau1 eta.
    pose alpha i := 'Ind[L, Z] 'chi_i - #|H : Z|%:R *: eta1.
    have IZfacts i: i != 0 ->
      [/\ 'chi_i 1%g = 1, 'Ind[L, Z] 'chi_i \in 'Z[X] & alpha i \in 'Z[S, L^#]].
    - move=> nzi; have /andP[_ /eqP lin_i]: lin_char 'chi_i.
        by rewrite lin_irr_der1 (derG1P _) ?sub1G // cycZ cycle_abelian.
      have Xchi: 'Ind 'chi_i \in 'Z[X].
        rewrite -(cfIndInd _ sHL) // ['Ind[H] _]cfun_sum_constt linear_sum.
        apply: sum_vchar => k k_i; rewrite linearZ; apply: scale_vchar.
          by rewrite cfdot_vchar_irr_Int // cfInd_vchar ?irr_vchar.
        rewrite seqInd_vcharW //; apply/seqIndP; exists k => //.
        rewrite !inE sub1G andbT; apply: contra k_i => kerZk.
        rewrite -Frobenius_reciprocity.
        have ->: 'Res[Z] 'chi_k = ('chi_k 1%g)%:A.
          apply: cfun_inP => z Zz; rewrite cfunE cfun1E Zz mulr1 cfResE //.
          by rewrite cfker1 ?(subsetP kerZk).
        by rewrite cfdotZr -chi0_1 cfdot_irr (negPf nzi) mulr0.
      split=> //; rewrite vcharD1E !cfunE cfInd1 // uniY // lin_i mulr1.
      rewrite -divgS // -(sdprod_card defL) -(LaGrange sZH) -mulnA mulKn //.
      rewrite -natr_mul subrr sub_vchar //=.
        by rewrite (vchar_subset _ sXS) ?seqInd_free.
      by rewrite scale_vchar ?isIntC_nat // seqInd_vcharW ?sYS. 
    have Dalpha (i : Iirr Z) (nzi : i != 0) :
      exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
            & tau (alpha i) = X1 - #|H : Z|%:R *: Y1.
    - have [lin_i Xchi Zalpha] := IZfacts i nzi.
      have Da: '[tau (alpha i), psi1] = a - #|H : Z|%:R * x1.
        rewrite !(=^~ Frobenius_reciprocity, cfdot_subl) cfResRes // cfdotZl.
        congr (_ - _); rewrite cfdotC Dpsi1 cfdotDl cfdotZl cfReg_sum.
        rewrite cfdot_suml (bigD1 i) //= big1 => [|j i'j]; last first.
          by rewrite cfdotZl cfdot_irr (negPf i'j) mulr0.
        rewrite !cfdotZl cfnorm_irr lin_i addr0 !mulr1.
        rewrite -chi0_1 cfdot_irr eq_sym (negPf nzi) mulr0 addr0.
        by rewrite isIntC_conj // Dx0 isIntC_mul ?isIntC_nat.
      have [Y2 [X1 [dX1 dY2 oX1Yt]]] :=
        orthogonal_split (map tau1 Y) (tau (alpha i)).
      exists X1 => //; rewrite dX1 addrC scalerN opprK scaler_sumr.
      congr (_ + _); have [_ -> ->] := orthonormal_span oYtau dY2.
      rewrite big_map; apply: eq_big_seq => eta Yeta.
      rewrite scalerA -[Y2](addrK X1) -dX1 cfdot_subl (orthoPl oX1Yt) ?map_f //.
      congr (_ *: _); rewrite subr0 !mulr_subr mulr_addr mulrC -Dx0.
      rewrite (addrAC a) -Da -addrA -mulr_subr addrC; apply: canRL (subrK _) _.
      have Zeta: eta - eta1 \in 'Z[Y, L^#].
        by rewrite vcharD1E sub_vchar ?seqInd_vcharW //= !cfunE !uniY ?subrr.
      rewrite -cfdot_subr -raddf_sub Dtau1 // Itau //; last first.
        by rewrite (vchar_subset _ sYS) ?seqInd_free.
      rewrite cfdot_subl (span_orthogonal oXY) ?(vchar_span Xchi)//; last first.
        by rewrite memv_sub ?memv_span.
      have [_ oYY] := orthonormalP oY; rewrite cfdotZl cfdot_subr !oYY //.
      by rewrite eqxx sub0r -mulrN oppr_sub eq_sym.
    exists Y1 => //; have{Dalpha} [X1 oX1Y Dalpha] := Dalpha i0 nz_i0.
    have [lin_i Xchi Zalpha] := IZfacts i0 nz_i0.
    have norm_alpha: '[tau (alpha i0)] = (#|L : Z| + #|H : Z| ^ 2)%:R.
      rewrite natr_add Itau // cfnorm_subd; last first.
        rewrite (span_orthogonal oXY) ?(vchar_span Xchi) //.
        by rewrite memvZl ?memv_span.
      rewrite induced_prod_index //; congr (#|_ : _|%:R + _).
        apply/setP=> y; rewrite 2!inE -andbA andb_idr // => Ly.
        have cZy: y \in 'C(Z).
          rewrite (subsetP _ y Ly) //; have [_ <- _ _] := sdprodP defL.
          rewrite mulG_subG centsC (subset_trans sZZ) ?subsetIr //=.
          by rewrite centsC defZ -defW2 subsetIr.
          have nZy := subsetP (cent_sub Z) _ cZy.
        rewrite nZy //; apply/eqP/cfun_inP=> t Zt; rewrite cfConjgE //.
        by rewrite conjgE invgK mulgA (centP cZy) ?mulgK.
      have [_ oYY] := orthonormalP oY; rewrite cfnormZ oYY // eqxx mulr1.
      by rewrite sqrtCK rmorph_nat -natr_mul.
    have{norm_alpha} ub_norm_alpha: '[tau (alpha i0)] < (#|H : Z| ^ 2).*2%:R.
      rewrite norm_alpha -addnn -ltn_ltC ltn_add2r.
      rewrite -divgS // -(sdprod_card defL) -(LaGrange sZH) -mulnA mulKn //.
      rewrite ltn_pmul2l //.
      have frobL2: [Frobenius L / Z = (H / Z) ><| (W1 / Z)]%g.
        apply: (Frobenius_coprime_quotient defL nsZL) => //.
        split=> [|y W1y]; first exact: sub_proper_trans ltH'H.
        by rewrite defZ; have [/= ? [_ [_ _ _ ->]]] := PtypeL.
      have nZW1 := subset_trans sW1L (normal_norm nsZL).
      rewrite (card_isog (quotient_isog nZW1 _)); last first.
        by rewrite coprime_TIg ?(coprimeSg sZH).
      rewrite -(prednK (indexg_gt0 H Z)) ltnS -card_quotient //.
      rewrite dvdn_leq ?(Frobenius_dvd_ker1 frobL2) // -subn1 subn_gt0.
      by rewrite cardG_gt1; case/Frobenius_context: frobL2.
    pose m : algC := (size Y)%:R.
    have{ub_norm_alpha} ub_xm: ~~ (2%:R <= (x - 1) ^+ 2 + (m - 1) * x ^+ 2).
      have: ~~ (2%:R <= '[Y1]).
        rewrite -2!(leC_pmul2l _ _ (sposGiC H Z)) -!natr_mul mulnA muln2.
        rewrite ltC_geF //; apply: leC_ltC_trans ub_norm_alpha.
        rewrite Dalpha cfnorm_subd.
          by rewrite cfnormZ sqrtCK rmorph_nat mulrA -leC_sub addrK cfnorm_posC.
        rewrite scalerN -scaleNr cfdotZr cfdot_sumr big_seq.
        rewrite big1 ?mulr0 // => eta Yeta.
        by rewrite cfdotZr (orthoPl oX1Y) ?map_f ?mulr0.
      rewrite cfnormN cfnorm_sum_orthonormal // (big_rem eta1) //= eqxx.
      rewrite big_seq (eq_bigr (fun _ => (x ^+ 2))) => [|eta]; last first.
        rewrite mem_rem_uniq // => /andP[/negPf-> _].
        by rewrite subr0 int_normCK.
      rewrite int_normCK 1?isIntC_sub //= -big_seq; congr (~~ (_ <= _ + _)).
      rewrite big_const_seq count_predT // -Monoid.iteropE.
      rewrite /m (perm_eq_size (perm_to_rem Yeta1)) /=.
      by rewrite mulrSr addrK mulr_natl.
    have [x_eq0 | nz_x] := eqVneq x 0.
      left; rewrite /Y1 x_eq0 (big_rem eta1) //= eqxx sub0r scaleN1r.
      rewrite big_seq big1 => [|eta]; last first.
        by rewrite mem_rem_uniq // => /andP[/negPf-> _]; rewrite subrr scale0r.
      by rewrite addr0 opprK.
    have m1_ge1: 1 <= m - 1.
      case/irrY/irrP: Yeta1 (Yeta1) => j1 -> /seqInd_nontrivial ntY.
      by rewrite -(leC_add2r 1) subrK -(leq_leC 2) ntY.
    right; have x_eq1: x = 1.
      apply: contraNeq ub_xm; rewrite -subr_eq0 => nz_x1; apply: leC_add.
        by rewrite isIntC_expr2_ge1 // isIntC_sub.
      rewrite (leC_trans m1_ge1) // -{1}[m - 1]mulr1 leC_pmul2l.
        exact: isIntC_expr2_ge1.
      exact: ltC_leC_trans sposC1 m1_ge1.
    have szY2: size Y = 2.
      apply: contraNeq ub_xm => Yneq2; rewrite x_eq1 /m subrr !exprS mul0r.
      rewrite add0r !mul1r mulr1 -(leC_add2r 1) subrK -mulrSr -leq_leC.
      by rewrite ltn_neqAle eq_sym Yneq2 leq_leC -/m -[m](subrK 1) leC_add2r.
    have eta1'2: eta1^*%CF != eta1 by exact: seqInd_conjC_neq Yeta1.
    have defY: perm_eq Y (eta1 :: eta1^*%CF).
      have uY2: uniq (eta1 :: eta1^*%CF) by rewrite /= inE eq_sym eta1'2.
      rewrite perm_eq_sym uniq_perm_eq //.
      have sY2Y: {subset (eta1 :: eta1^*%CF) <= Y}.
        by apply/allP; rewrite /= cfAut_seqInd ?Yeta1.
      by have [|//]:= leq_size_perm uY2 sY2Y; rewrite szY2.
    split=> //; congr (- _); rewrite (eq_big_perm _ defY) /= x_eq1.
    rewrite big_cons big_seq1 eqxx (negPf eta1'2) subrr scale0r add0r.
    by rewrite subr0 scale1r.
  have [a Za Dxa]: exists2 a, forall xi, isIntC (a xi)
                  & forall xi, xi \in X -> xi 1%g = a xi * #|W1|%:R
                    /\ (exists2 X1 : 'CF(G), orthogonal X1 (map tau1 Y)
                              & tau (xi - a xi *: eta1) = X1 - a xi *: Y1).
  - pose aX (xi : 'CF(L)) : algC := (getNatC (xi 1%g / #|W1|%:R))%:R.
    exists aX => [xi | xi Xxi]; first exact: isIntC_nat.
    have [k kerZ'k def_xi] := seqIndP Xxi; rewrite !inE sub1G andbT in kerZ'k.
    set a := aX xi; have Dxi1: xi 1%g = a * #|W1|%:R.
      rewrite /a /aX def_xi cfInd1 // -divgS // -(sdprod_card defL) mulKn //.
      by rewrite mulrC mulfK ?neq0GC // irr1_degree getNatC_nat.
    split=> //; have Da: a = 'chi_k 1%g.
       apply: (mulIf (neq0GC W1)); rewrite -Dxi1 def_xi cfInd1 //.
       by rewrite mulrC -divgS // -(sdprod_card defL) mulKn.
    have [i0 nzi0 Res_k]: exists2 i: Iirr Z, i != 0 & 'Res 'chi_k = a *: 'chi_i.
      have [chi /andP[Nchi lin_chi] defRkZ] := cfcenter_Res 'chi_k.
      have sZ_Zk: Z \subset 'Z('chi_k)%CF.
        by rewrite (subset_trans sZZ) // -cap_cfcenter_irr bigcap_inf.
      have{Nchi lin_chi} /irrP[i defRk] : 'Res chi \in irr Z.
        by rewrite lin_char_irr // /lin_char cfRes_char // cfRes1.
      have{chi defRk defRkZ} defRk: 'Res 'chi_k = a *: 'chi_i.
        by rewrite -defRk -linearZ Da -defRkZ /= cfResRes ?cfcenter_sub.
      exists i => //; apply: contra kerZ'k.
      rewrite -subGcfker => /subsetP sZker.
      apply/subsetP=> t Zt; rewrite cfker_irrE inE.
      by rewrite -!(cfResE _ sZH) // defRk !cfunE cfker1 ?sZker.
    set phi := 'chi_i0 in Res_k; pose a_ i := '['Ind[H] phi, 'chi_i].
    pose rp := irr_constt ('Ind[H] phi).
    have defIphi: 'Ind phi = \sum_(i \in rp) a_ i *: 'chi_i.
      exact: cfun_sum_constt.
    have a_k: a_ k = a.
      rewrite /a_ -Frobenius_reciprocity Res_k cfdotZr cfnorm_irr mulr1.
      by rewrite rmorph_nat.
    have rp_k: k \in rp by rewrite inE ['[_, _]]a_k Da irr1_neq0.
    have resZr i: i \in rp -> 'Res[Z] 'chi_i = a_ i *: phi.
      move=> r_i; rewrite ['Res _]cfun_sum_cfdot.
      rewrite (bigD1 i0) // big1 => /= [|j i0'j].
        rewrite cfdot_Res_l addr0 -/phi cfdotC isNatC_conj //.
        by rewrite cfdot_char_irr_Nat ?cfInd_char ?irr_char.
      apply/eqP; rewrite scaler_eq0 cfdot_Res_l.
      rewrite -(inj_eq (mulfI r_i)) mulr0 -/(a_ i) -cfdotZl.
      have: '['Ind[H] phi, 'Ind[H] 'chi_j] = 0.
        apply: not_cfclass_Ind_ortho => //.
        have defIj: 'I_H['chi_j] = H.
          apply/setP=> y; rewrite 2!inE -andbA andb_idr // => Hy.
          have cZy: y \in 'C(Z).
            by rewrite (subsetP _ _ Hy) // centsC (subset_trans sZZ) ?subsetIr.
          have nZy := subsetP (cent_sub Z) y cZy; rewrite nZy.
          apply/eqP/cfun_inP=> t Zt; rewrite cfConjgE // conjgE invgK mulgA.
          by rewrite (centP cZy) ?mulgK.
        rewrite -[H in (_ ^: H)%CF](group_inj defIj) cfclass_inertia inE.
        by rewrite eq_sym (inj_eq chi_inj).
      rewrite defIphi cfdot_suml => /posC_sum_eq0-> //; first by rewrite eqxx.
      move=> i1 _; rewrite cfdotZl.
      by rewrite posC_mul ?posC_Nat ?cfdot_char_Nat ?cfInd_char ?irr_char.
    have lin_phi: phi 1%g = 1.
      apply: (mulfI (irr1_neq0 k)); have /resZr/cfunP/(_ 1%g) := rp_k.
      by rewrite cfRes1 // cfunE mulr1 a_k Da.
    have Da_ i: i \in rp -> 'chi_i 1%g = a_ i.
      move/resZr/cfunP/(_ 1%g); rewrite cfRes1 // cfunE => ->.
      by rewrite lin_phi mulr1.
    pose chi i := 'Ind[L, H] 'chi_i; pose alpha i := chi i - a_ i *: eta1.
    have Aalpha i: i \in rp -> alpha i \in 'CF(L, A).
      move=> r_i; rewrite cfun_onD1 !cfunE cfInd1 // (uniY _ Yeta1).
      rewrite -divgS // -(sdprod_card defL) mulKn // Da_ // mulrC subrr eqxx.
      by rewrite memv_sub ?cfInd_normal ?memvZl // (seqInd_on _ Yeta1).
    have [sum_alpha sum_a2]:
         'Ind phi - #|H : Z|%:R *: eta1 = \sum_(i \in rp) a_ i *: alpha i
      /\ \sum_(i \in rp) a_ i ^+ 2 = #|H : Z|%:R.
    + set rhs2 := _%:R; set lhs1 := _ - _; set rhs1 := \sum_(i | _) _.
      set lhs2 := \sum_(i | _) _.
      have eq_diff: lhs1 - rhs1 = (lhs2 - rhs2) *: eta1.
        rewrite scaler_subl addrAC; congr (_ - _).
        rewrite -(cfIndInd _ sHL sZH) defIphi linear_sum -sumr_sub scaler_suml.
        apply: eq_bigr => i rp_i; rewrite linearZ scaler_subr oppr_add addNKr.
        by rewrite opprK scalerA.
      have: (lhs1 - rhs1) 1%g == 0.
        rewrite !cfunE -(cfIndInd _ sHL sZH) !cfInd1 // lin_phi mulr1.
        rewrite -divgS // -(sdprod_card defL) mulKn // mulrC uniY // subrr.
        rewrite sum_cfunE big1 ?subrr // => i rp_i.
        by rewrite cfunE (cfun_on0 (Aalpha i rp_i)) ?mulr0 // !inE eqxx.
      rewrite eq_diff cfunE mulf_eq0 subr_eq0 (negPf (seqInd1_neq0 _ Yeta1)) //.
      rewrite orbF => /eqP sum_a2; split=> //; apply/eqP; rewrite -subr_eq0.
      by rewrite eq_diff sum_a2 subrr scale0r.
    have Xchi i: i \in rp -> chi i \in X.
      move=> rp_i; apply/seqIndP; exists i => //; rewrite !inE sub1G andbT.
      apply: contra rp_i => kerZi; rewrite -cfdot_Res_r.
      suffices ->: 'Res[Z] 'chi_i = ('chi_i 1%g)%:A.
         by rewrite cfdotZr -chi0_1 cfdot_irr (negPf nzi0) mulr0.
      apply/cfun_inP=> t Zt; rewrite cfResE // cfunE cfun1E Zt mulr1.
      by rewrite cfker1 ?(subsetP kerZi).
    have oRY i: i \in rp -> orthogonal (R (chi i)) (map tau1 Y).
      move/Xchi=> Xchi_i; apply/orthogonalP=> aa _ Ri_aa /mapP[eta Yeta ->].
      have sY2Y: {subset (eta :: eta^*)%CF <= Y}.
        by apply/allP; rewrite /= Yeta cfAut_seqInd.
      have [||E sER ->] := (coherent_sum_subseq scohY) _ tau1 Yeta.
      + exact: sub_iso_to (vchar_subset (seqInd_free _ _) sY2Y) sub_refl _.
      + rewrite Dtau1 // sub_Aut_vchar ?vchar_onG
             ?seqInd_vcharW ?cfAut_seqInd //.
        exact: seqInd_virrW.
      rewrite cfdot_sumr big_seq big1 // => bb /(mem_subseq sER) Rbb.
      have [_ _ _ _ oRR] := scohS.
      rewrite (orthogonalP (oRR eta (chi i) (sYS _ _) (sXS _ _) _)) //.
      by apply/orthoPl=> eta2 /sY2Y Yeta2; exact: (orthogonalP oXY).
    have n1Y1: '[Y1] = 1.
      have [_ oYYt] := orthonormalP oYtau.
      have [-> | [_ ->]] := defY1;
        by rewrite ?cfnormN oYYt ?eqxx ?map_f // cfAut_seqInd.
    have YtauY1: Y1 \in 'Z[map tau1 Y].
      by have [-> | [_ ->]] := defY1;
        rewrite ?opp_vchar mem_vchar ?orthonormal_free ?map_f ?cfAut_seqInd.
    have /fin_all_exists[XbZ defXbZ] i: exists XbZ, let: (X1, b, Z1) := XbZ in
      [/\ tau (alpha i) = X1 - b *: Y1 + Z1,
          i \in rp -> X1 \in 'Z[R (chi i)], i \in rp -> isRealC b,
          '[Z1, Y1] = 0 & i \in rp -> orthogonal Z1 (R (chi i))].
    - have [X1 [YZ1 [dXYZ dX1 oYZ1R]]] :=
        orthogonal_split (R (chi i)) (tau (alpha i)).
      have [Y1b [Z1 [dYZ1 dY1b oZY1]]] := orthogonal_split Y1 YZ1.
      have{dY1b} [|b Db dY1b] := orthogonal_span _ dY1b.
        by rewrite /pairwise_orthogonal /= inE eq_sym -cfnorm_eq0 n1Y1 oner_eq0.
      exists (X1, - b Y1, Z1); split.
      + by rewrite dXYZ dYZ1 dY1b scaleNr big_seq1 opprK addrA.
      + have [_ _ _ Rok _] := scohS => /Xchi/sXS/Rok[ZR oRR _].
        have [_ -> ->] := orthonormal_span oRR dX1.
        rewrite big_seq sum_vchar // => aa Raa.
        rewrite scale_vchar ?mem_vchar ?orthonormal_free //.
        rewrite -[X1](addrK YZ1) -dXYZ cfdot_subl (orthoPl oYZ1R) // subr0.
        rewrite cfdot_vchar_Int ?(ZR aa) //.
        rewrite !(sub_vchar, cfInd_vchar) ?irr_vchar //.
        rewrite scale_vchar ?(seqInd_virrW Yeta1) // cfdot_vchar_irr_Int //.
        by rewrite cfInd_vchar ?irr_vchar.
      + move=> rp_i; rewrite Db -[Y1b](addrK Z1) -dYZ1 cfdot_subl (orthoP oZY1).
        rewrite subr0 n1Y1 divr1 -[YZ1](addKr X1) -dXYZ cfdotDl cfdotNl.
        rewrite (span_orthogonal (oRY i rp_i)) ?(vchar_span YtauY1) //.
        rewrite oppr0 add0r isIntC_Real // isIntC_opp cfdot_vchar_Int //.
          rewrite !(cfInd_vchar, sub_vchar) ?irr_vchar //.
          rewrite -Da_ // scale_vchar ?isIntC_Nat ?isNatC_irr1 //.
          exact: (seqInd_virrW Yeta1).
        apply: vchar_trans_on YtauY1 => _ /mapP[eta Yeta ->].
        by rewrite Ztau1 ?seqInd_vcharW.
      + exact: (orthoP oZY1).
      move/oRY=> oRiY; apply/orthoPl=> aa Raa.
      rewrite -[Z1](addKr Y1b) -dYZ1 cfdotDl cfdotNl cfdotC (orthoPl oYZ1R) //.
      rewrite dY1b addr0 big_seq1 cfdotZr.
      by have [-> | [_ ->]] := defY1;
        rewrite ?cfdotNr (orthogonalP oRiY) ?map_f ?cfAut_seqInd //;
        rewrite ?(oppr0, mulr0, rmorph0).
    pose X1 i := (XbZ i).1.1; pose b i := (XbZ i).1.2; pose Z1 i := (XbZ i).2.
    have R_X1 i: i \in rp -> X1 i \in 'Z[R (chi i)].
      by rewrite /X1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have Rb i: i \in rp -> isRealC (b i).
      by rewrite /b; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have oZY1 i: '[Z1 i, Y1] = 0.
      by rewrite /Z1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have oZ1R i: i \in rp -> orthogonal (Z1 i) (R (chi i)).
      by rewrite /Z1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have{defXbZ} defXbZ i: tau (alpha i) = X1 i - b i *: Y1 + Z1 i.
      by rewrite /X1 /b /Z1; case: (XbZ i) (defXbZ i) => [[? ?] ?] [].
    have ub_alpha i: i \in rp ->
       [/\ '[chi i] <= '[X1 i]
         & '[a_ i *: eta1] <= '[b i *: Y1 - Z1 i] ->
           [/\ '[X1 i] = '[chi i], '[b i *: Y1 - Z1 i] = '[a_ i *: eta1]
             & exists2 E, subseq E (R (chi i)) & X1 i = \sum_(aa <- E) aa]].
    - move=> rp_i; apply: (subcoherent_norm scohS) (erefl _) _.
      + rewrite sXS ?Xchi // scale_vchar ?(seqInd_virrW Yeta1) //; last first.
          by rewrite cfdot_vchar_irr_Int // cfInd_vchar ?irr_vchar.
        split=> //; apply/orthoPr=> xi2; rewrite !inE => Dxi2.
        rewrite cfdotZr (orthogonalP oXY) ?mulr0 //.
        by case/pred2P: Dxi2 => ->; rewrite ?cfAut_seqInd ?Xchi.
      + have [_ IZtau _ _ _] := scohS.
        apply: sub_iso_to IZtau; [apply: vchar_trans_on | exact: vcharW].
        apply/allP; rewrite /= vchar_split (cfun_onS (setSD _ sHL)) ?Aalpha //.
        rewrite sub_vchar ?scale_vchar ?seqInd_vcharW ?(sYS eta1) ?sXS ?Xchi //.
          by rewrite sub_Aut_vchar ?vchar_onG ?seqInd_vcharW ?cfAut_seqInd;
            rewrite ?sXS ?Xchi //; exact: seqInd_virrW.
        by rewrite -Da_ // irr1_degree isIntC_nat.
      rewrite R_X1 //= oppr_add opprK addrA -defXbZ; split=> //.
      apply/orthoPl=> aa Raa.
      rewrite cfdot_subl cfdotZl (orthoPl (oZ1R i _)) //.
      by rewrite subr0 cfdotC; have [-> | [_ ->]] := defY1;
        rewrite ?cfdotNr (orthogonalP (oRY i _)) ?map_f ?cfAut_seqInd //;
        by rewrite ?(mulr0, oppr0, rmorph0).
    have leba i: i \in rp -> b i <= a_ i.
      move=> rp_i; have ai_gt0: a_ i > 0 by rewrite -Da_ ?ltC_irr1.
      have /realC_leP[le_b0 | b_ge0] := Rb i rp_i.
        by apply: leC_trans le_b0 _; rewrite ltCW.
      rewrite -(@leC_exp2r 2) //; last exact: ltCW.
      apply: leC_trans (_ : '[b i *: Y1 - Z1 i] <= _).
        rewrite cfnorm_subd; last by rewrite cfdotZl cfdotC oZY1 ?conjC0 ?mulr0.
        rewrite cfnormZ normC_pos // n1Y1 mulr1 addrC -leC_sub addrK.
        exact: cfnorm_posC.
      rewrite -(leC_add2l '[X1 i]) -cfnorm_subd; last first.
        rewrite cfdot_subr cfdotZr (span_orthogonal (oRY i _)) //; last first.
        - exact: (vchar_span YtauY1).
        - exact: (vchar_span (R_X1 i rp_i)).
        rewrite mulr0 sub0r cfdotC (span_orthogonal (oZ1R i _)) ?raddf0 //.
          exact: memv_span1.
        exact: (vchar_span (R_X1 i rp_i)).
      have Salpha: alpha i \in 'Z[S, L^#].
        rewrite vchar_split (cfun_onS (setSD _ sHL)) ?Aalpha //.
        rewrite sub_vchar ?scale_vchar ?seqInd_vcharW
                   ?(sYS _ Yeta1) ?sXS ?Xchi //.
        by rewrite -Da_ // irr1_degree isIntC_nat.
      rewrite  oppr_add opprK addrA -defXbZ // Itau ?Salpha //.
      rewrite cfnorm_subd; last first.
        by rewrite cfdotZr (orthogonalP oXY) ?mulr0 ?Xchi.
      rewrite cfnormZ normC_pos ?(ltCW ai_gt0) //.
      have [_ /(_ eta1)->//] := orthonormalP oY; rewrite eqxx mulr1 leC_add2r.
      by have [] := ub_alpha i rp_i.
    have{leba} eq_ab: {in rp, a_ =1 b}.
      move=> i rp_i; apply/eqP; rewrite -subr_eq0; apply/eqP.
      apply: (mulfI (irr1_neq0 i)); rewrite mulr0 Da_ // mulr_subr.
      move: i rp_i; apply: posC_sum_eq0 => [i rp_i | ].
        by rewrite leC_sub leC_pmul2l ?leba // -Da_ ?ltC_irr1.
      rewrite sumr_sub sum_a2.
      have [X2 oX2Y /(congr1 (cfdotr Y1))] := Dpsi1 i0 nzi0.
      rewrite sum_alpha /tau linear_sum /= cfdot_suml cfdot_subl.
      rewrite (span_orthogonal oX2Y) ?memv_span1 ?(vchar_span YtauY1) // add0r.
      rewrite cfdotZl n1Y1 mulr1 => /(canLR (@opprK _)) <-.
      rewrite -oppr_add -big_split big1 ?oppr0 //= => i rp_i.
      rewrite linearZ cfdotZl /= -/tau defXbZ addrC cfdotDl oZY1 addr0.
      rewrite cfdot_subl cfdotZl n1Y1 mulr1.
      rewrite (span_orthogonal (oRY i _)) ?(vchar_span YtauY1) //.
        by rewrite add0r mulrN subrr.
      exact: (vchar_span (R_X1 i rp_i)).
    exists (X1 k).
      apply/orthoPl=> psi /memv_span Ypsi.
      by rewrite (span_orthogonal (oRY k _)) // (vchar_span (R_X1 k rp_k)).
    apply/eqP; rewrite def_xi -a_k defXbZ addrC -subr_eq0 eq_ab // addrK.
    have n1eta1: '[eta1] = 1 by have [_ -> //] := orthonormalP oY; rewrite eqxx.
    rewrite -cfnorm_eq0 -(inj_eq (addrI '[b k *: Y1])).
    have [_ [|_]] := ub_alpha k rp_k.
      rewrite cfnorm_subd; last by rewrite cfdotZl cfdotC oZY1 conjC0 mulr0.
      by rewrite addrC !cfnormZ eq_ab // n1Y1 n1eta1 -leC_sub addrK cfnorm_posC.
    rewrite cfnorm_subd; last by rewrite cfdotZl cfdotC oZY1 conjC0 mulr0.
    by move=> -> _; rewrite addr0 !cfnormZ eq_ab // n1Y1 n1eta1.
  have oX: pairwise_orthogonal X by rewrite (sub_pairwise_orthogonal sXS).
  have ooXY: pairwise_orthogonal (X ++ Y).
    by rewrite pairwise_orthogonal_cat oX orthonormal_orthogonal.
  have [_ oYY] := orthonormalP oY.
  have n1eta: '[eta1] = 1 by rewrite oYY ?eqxx.
  pose tau22 xi := tau (xi - a xi *: eta1) + a xi *: Y1.
  pose tau21 eta := tau (eta - eta1) + Y1.
  pose XY2 := map tau22 X ++ map tau21 Y.
  have n1Y1: '[Y1] = 1.
    have [_ oYYt] := orthonormalP oYtau.
    have [-> | [_ ->]] := defY1;
      by rewrite ?cfnormN oYYt ?eqxx ?map_f // cfAut_seqInd.
  have YtauY1: Y1 \in span (map tau1 Y).
    by have [-> | [_ ->]] := defY1;
      rewrite ?memvN memv_span ?map_f ?cfAut_seqInd.
  have Zalpha xi: xi \in X -> xi - a xi *: eta1 \in 'Z[S, L^#].
    move=> Xxi; rewrite vcharD1E sub_vchar ?scale_vchar;
                rewrite ?seqInd_vcharW ?(sXS xi) ?sYS //.
    by rewrite !cfunE (uniY eta1) //= subr_eq0; have [<-] := Dxa xi Xxi.
  have Zbeta eta: eta \in Y -> eta - eta1 \in 'Z[S, L^#].
    by move=> Yeta; rewrite vcharD1E sub_vchar ?seqInd_vcharW;
                  rewrite ?seqInd_vcharW ?sYS //= !cfunE !uniY ?subrr.
  have nza xi: xi \in X -> a xi != 0.
    move=> Xxi; have [/eqP Dxi1 _] := Dxa _ Xxi; apply: contraTneq Dxi1 => ->.
    by rewrite mul0r (seqInd1_neq0 _ Xxi).
  have alphaY xi: xi \in X -> '[tau (xi - a xi *: eta1), Y1] = - a xi.
    case/Dxa=> _ [X1 oX1Y ->]; rewrite cfdot_subl cfdotZl n1Y1 mulr1.
    by rewrite (span_orthogonal oX1Y) ?memv_span1 ?add0r.
  have betaY eta: eta \in Y -> '[tau (eta - eta1), Y1] = (eta == eta1)%:R - 1.
    move=> Yeta; rewrite -Dtau1; last first.
      by rewrite vchar_split (vchar_on (Zbeta eta _)) ?sub_vchar ?seqInd_vcharW.
    rewrite raddf_sub cfdot_subl.
    have [-> | [szY2 ->]] := defY1.
      by rewrite !{1}Itau1 ?seqInd_vcharW // !oYY // !eqxx.
    rewrite !cfdotNr opprK !{1}Itau1 ?oYY ?seqInd_vcharW ?cfAut_seqInd //.
    have defY: (eta1 :: eta1^*)%CF =i Y.
      apply: proj1 (leq_size_perm _ _ _); last by rewrite szY2.
        by rewrite /= inE eq_sym (seqInd_conjC_neq _ _ _ Yeta1).
      by apply/allP; rewrite /= Yeta1 cfAut_seqInd.
    rewrite -defY !inE in Yeta; case/pred2P: Yeta => ->.
      rewrite eqxx eq_sym (negPf (seqInd_conjC_neq _ _ _ Yeta1)) //.
      by rewrite addrC !subrr.
    by rewrite eqxx eq_sym (negPf (seqInd_conjC_neq _ _ _ Yeta1)) ?add0r ?addr0.
  have Itau22: {in X &, isometry tau22}.
    move=> xi1 xi2 Xxi1 Xxi2; rewrite /= cfdotDl !cfdotDr Itau ?Zalpha //.
    rewrite cfdot_subl !cfdot_subr oppr_sub !cfdotZr !isIntC_conj ?Za //.
    rewrite !cfdotZl (cfdotC Y1) !alphaY // n1Y1 n1eta rmorphN isIntC_conj //.
    rewrite (cfdotC eta1) !(orthogonalP oXY _ eta1) // !(mulr0, conjC0).
    by rewrite !mulr1 !subr0 !mulrN mulrC !addrA subrK addrK.
  have tau22_inj: {in X &, injective tau22}.
    move=> xi1 xi2 Xxi1 Xxi2 /=/(congr1 (cfdot (tau22 xi2)))/eqP.
    rewrite !Itau22 //; apply: contraTeq; rewrite eq_sym => xi2'1.
    have [_ -> //] := pairwise_orthogonalP oX.
    by rewrite eq_sym (cfnorm_seqInd_neq0 _ Xxi2).
  have Itau21: {in Y &, isometry tau21}.
    move=> eta3 eta4 Yeta3 Yeta4; rewrite /= cfdotDl !cfdotDr n1Y1.
    rewrite (cfdotC Y1) !betaY // Itau ?Zbeta // cfdot_subl !cfdot_subr !oYY //.
    rewrite eqxx rmorph_sub rmorph1 rmorph_nat subrK (eq_sym eta1) oppr_sub.
    by rewrite !addrA 3!(addrAC _ (- _)) addrK (addrAC _ 1) subrK addrK.
  have tau21_inj: {in Y &, injective tau21}.
    move=> eta3 eta4 Yeta3 Yeta4 /=/(congr1 (cfdot (tau21 eta4)))/eqP.
    by rewrite !Itau21 // !oYY // eqxx -eqN_eqC; case: (eta4 =P eta3). 
  have ooXY2: pairwise_orthogonal XY2.
    rewrite pairwise_orthogonal_cat; apply/and3P; split.
    - apply/pairwise_orthogonalP; split=> /=.
        rewrite map_inj_in_uniq // uX andbT.
        apply/mapP=> [[xi2 Xxi2 /esym/eqP/idPn[]]].
        by rewrite -cfnorm_eq0 Itau22 // (cfnorm_seqInd_neq0 _ Xxi2).
      move=> _ _ /mapP[xi1 Xxi1 ->] /mapP[xi2 Xxi2 ->].
      rewrite Itau22 // (inj_in_eq tau22_inj) //.
      by have [_ oXX] := pairwise_orthogonalP oX; exact: oXX.
    - apply/pairwise_orthogonalP; split=> /=.
        rewrite map_inj_in_uniq // uY andbT.
        apply/mapP=> [[eta3 Yeta3 /esym/eqP/idPn[]]].
        by rewrite -cfnorm_eq0 Itau21 // (cfnorm_seqInd_neq0 _ Yeta3).
      move=> _ _ /mapP[eta3 Yeta3 ->] /mapP[eta4 Yeta4 ->].
      by rewrite Itau21 // (inj_in_eq tau21_inj) // oYY // => /negPf->.
    apply/orthogonalP=> _ _ /mapP[xi1 Xxi1 ->] /mapP[eta3 Yeta3 ->].
    rewrite cfdotDl !cfdotDr Itau ?Zalpha ?Zbeta // alphaY //.
    rewrite cfdot_subl !cfdotZl !cfdot_subr 2?(orthogonalP oXY) // n1eta n1Y1.
    rewrite oYY // cfdotC betaY // rmorph_sub rmorph_nat rmorph1 subrr add0r.
    by rewrite mulr1 eq_sym -oppr_add addNr.
  have [||tau2 Dtau2 Itau2] := Zisometry_of_cfnorm ooXY ooXY2.
  - rewrite !map_cat -!map_comp; congr (_ ++ _).
      by apply: eq_in_map => xi1 Xxi1; rewrite /= !Itau22.
    by apply: eq_in_map => eta3 Yeta3; rewrite /= !Itau21.
  - have [_ [_ Ztau] _ _ _] := scohS.
    have ZY1: Y1 \in 'Z[irr G].
      have [-> | [_ ->]] := defY1; rewrite ?opp_vchar Ztau1 ?seqInd_vcharW //.
      by rewrite cfAut_seqInd.
    apply/allP; rewrite all_cat !all_map; apply/andP; split.
      apply/allP=> xi1 Xxi1; rewrite /= add_vchar ?scale_vchar ?Za //.
      by rewrite (vcharW (Ztau _ _)) ?Zalpha.
    apply/allP=> eta3 Yeta3; rewrite /= add_vchar //.
    by rewrite (vcharW (Ztau _ _)) ?Zbeta.
  exists tau2; split=> // phi; rewrite vcharD1E => /andP[].
  case/vchar_expansion=> c Zc ->{phi}; rewrite big_cat /= cfunE.
  set phi2 := \sum_(i <- X) _; set phi1 := \sum_(i <- Y) _ => /eqP opp_phi12.
  have Dtau22: {in X, forall xi, tau2 xi = tau22 xi}.
    move=> xi Xxi; pose i := index xi X; have:= congr1 (nth 0 ^~ i) Dtau2.
    have ltiX: (i < size X)%N by rewrite index_mem.
    by rewrite map_cat !nth_cat !size_map ltiX !(nth_map 0) // nth_index.
  have Dtau21: {in Y, forall eta, tau2 eta = tau21 eta}.
    move=> eta Yeta; pose j := index eta Y.
    have:= congr1 (nth 0 ^~ (size X + j)%N) Dtau2.
    have ltjY: (j < size Y)%N by rewrite index_mem.
    rewrite map_cat !nth_cat !size_map ltnNge leq_addr addKn /=.
    by rewrite !(nth_map 0) // nth_index.
  pose u := \sum_(xi <- X) c xi * a xi; pose v := \sum_(eta <- Y) c eta.
  have{opp_phi12} uv0: u + v = 0.
    apply: (mulIf (neq0GC W1)); rewrite mul0r mulr_addl -{}opp_phi12.
    rewrite -!mulr_suml !sum_cfunE; congr (_ + _); apply: eq_big_seq.
      by move=> xi /Dxa[Dxi1 _]; rewrite !cfunE -mulrA -Dxi1.
    by move=> eta Yeta; rewrite /= cfunE /= uniY.
  rewrite raddfD /= -[tau2 _]subr0 -{2}[phi2]subr0 -(scale0r Y1).
  rewrite -(scale0r eta1) -{}uv0 !scaler_addl !oppr_add !addrA [_ + _]addrAC.
  rewrite [psi in tau psi]addrAC !scaler_suml -addrA.
  rewrite 4!(raddf_sum, =^~ sumr_sub) -addrA -!sumr_sub /tau raddfD !raddf_sum.
  congr (_ + _); apply: eq_big_seq.
    move=> xi Xxi; rewrite /= -!scalerA linearZ -!scaler_subr Dtau22 //.
    by rewrite addrK -linearZ.
  by move=> eta Yeta; rewrite /= linearZ -!scaler_subr Dtau21 // addrK -linearZ.
pose wf S1 := [/\ uniq S1, {subset X ++ Y <= S1},
                 {subset S1 <= S} & conjC_closed S1].
pose S1 := [::] ++ X ++ Y; set S2 := [::] in S1; rewrite -[X ++ Y]/S1 in cohXY.
have wfS1: wf S1.
  rewrite /wf /S1 /= cat_uniq !seqInd_uniq X'Y; split=> // phi.
    by rewrite mem_cat => /orP[/sXS | /sYS].
  by rewrite !mem_cat => /orP[]/cfAut_seqInd-> //; rewrite orbT.
move: {2}_.+1 (ltnSn (size S - size S1)) => n.
elim: n => // n IHn in (S2) S1 wfS1 cohXY *; rewrite ltnS => leSnS1.
have [uniqS1 sXYS1 sS1S ccS1] := wfS1.
have [sSS1 | /allPn[psi /= Spsi notS1psi]] := altP (@allP _ (mem S1) S).
  apply: subset_coherent cohXY => //; have [_ _ oSS _ _] := scohS.
  exact: orthogonal_free (sub_pairwise_orthogonal _ _ oSS).
have [_ _ nrS ccS] := uccS.
have [neq_psi_c Spsic] := (hasPn nrS _ Spsi, ccS _ Spsi).
have wfS1': wf [:: psi, psi^* & S1]%CF.
  split=> [|xi|xi|xi]; rewrite /= !inE 1?andbC.
  - rewrite negb_or eq_sym neq_psi_c notS1psi uniqS1 (contra (ccS1 _)) //.
    by rewrite cfConjCK.
  - by move/sXYS1->; rewrite !orbT.
  - by case/predU1P=> [|/predU1P[|/sS1S]] ->.
  do 2![case/predU1P=> [-> |]; first by rewrite ?cfConjCK eqxx ?orbT // eq_sym].
  by move/ccS1=> ->; rewrite !orbT.
apply: (IHn [:: psi, psi^* & S2]%CF) => //; last first.
  rewrite -leq_subS ?uniq_leq_size //; try by case: wfS1'.
  by rewrite /= subSS (leq_trans _ leSnS1) // leq_sub2l ?leqW.
have ltZH': Z \proper H^`(1)%g.
  rewrite properEneq sZH' andbT; apply: contraNneq notS1psi => eqZH'.
  have [i /setDP[_ nt_i] ->] := seqIndP Spsi; rewrite sXYS1 // mem_cat.
  rewrite !mem_seqInd ?normal1 //= -eqZH' !inE in nt_i *.
  by rewrite sub1G nt_i andbT orNb.
have: [&& eta1 \in S1, psi \in S & psi \notin S1].
  by rewrite Spsi sXYS1 //  mem_cat Yeta1 orbT.
have /seqIndC1P[i nzi Dpsi] := Spsi.
move/(extend_coherent scohS); apply; split=> //.
  rewrite uniY // Dpsi cfInd1 // -divgS // -(sdprod_card defL) mulKn //.
  by rewrite dvdC_mulr // isIntC_Nat ?isNatC_irr1.
rewrite !big_cat //= (big_rem _ Yeta1) /= addrC -!addrA -big_cat //=.
rewrite sum_seqIndD_square ?normal1 ?sub1G // indexg1 addrC.
rewrite ltC_sub -!addrA sposC_addr //.
  have /irrY/irrP[j ->] := Yeta1.
  by rewrite cfnorm_irr divr1 sposC_exp ?ltC_irr1.
rewrite big_seq posC_add ?posC_sum // => [phi Sphi|].
  rewrite posC_div ?cfnorm_posC ?posC_exp // ?char1_pos //.
  suffices /(allP (seqInd_char _ _)): phi \in S by [].
  rewrite sS1S // !mem_cat; rewrite mem_cat in Sphi.
  by case/orP: Sphi => [/mem_rem-> | ->]; rewrite ?orbT.
rewrite leC_sub -(LaGrange_index sHL sZH) -oW1 natr_mul mulrC -mulrA.
rewrite uniY ?leC_pmul2l ?sposGC //.
rewrite  -(prednK (cardG_gt0 Z)) [zz in zz - 1]mulrSr addrK -natr_mul.
rewrite Dpsi cfInd1 // -oW1.
rewrite -(@leC_exp2r 2) ?posC_mul ?posC_nat ?char1_pos ?irr_char //.
rewrite !exprn_mull -!natr_exp mulrA -natr_mul.
apply: leC_trans (_ : (4 * #|W1| ^ 2)%:R * #|H : Z|%:R <= _).
  rewrite leC_pmul2l; last by rewrite -(ltn_ltC 0) muln_gt0 !expn_gt0 cardG_gt0.
  rewrite (leC_trans (irr1_bound i)) // -leq_leC dvdn_leq // indexgS //.
  by rewrite (subset_trans sZZ) // -cap_cfcenter_irr bigcap_inf.
rewrite -natr_mul -leq_leC expn_mull mulnC -mulnA leq_pmul2l //.
have [in_caseA | in_caseB] := boolP caseA.
  have regW1Z: semiregular Z W1.
    have [in_c1 | in_c2] := boolP case_c1.
      move=> x /(Frobenius_reg_ker in_c1) regHx; apply/trivgP.
      by rewrite -regHx setSI.
    have [_ _ [/= _ [_ [_ _ _ prW1H] _] _ _]] := c2W2 in_c2.
    move=> x /prW1H prHx; apply/trivgP; rewrite -((_ =P [1]) in_caseA) -prHx.
    by rewrite subsetI subIset ?sZZ // setSI.
  rewrite -(mul1n (4 * _)%N) leq_mul // -(expn_mull 2 _ 2) leq_exp2r //.
  rewrite dvdn_leq //; first by rewrite -subn1 subn_gt0 cardG_gt1.
  rewrite gauss_inv ?(@pnat_coprime 2) -?odd_2'nat ?(oddSg sW1L) //.
  rewrite dvdn2 -{1}subn1 odd_sub // (oddSg (normal_sub nsZL)) //=.
  by rewrite regular_norm_dvd_pred // (subset_trans sW1L) ?normal_norm.
rewrite -(muln1 (4 * _)%N) leq_mul //; last first.
  by rewrite expn_gt0 -subn1 subn_gt0 orbF cardG_gt1.
rewrite -(expn_mull 2 _ 2) -(LaGrange_index (der_sub 1 H) sZH') leq_mul //.
  rewrite -(prednK (indexg_gt0 _ _)) leqW // dvdn_leq //.
    by rewrite -subn1 subn_gt0 indexg_gt1 proper_subn.
  rewrite gauss_inv ?(@pnat_coprime 2) -?odd_2'nat ?(oddSg sW1L) //.
  rewrite dvdn2 -{1}subn1 odd_sub // -card_quotient ?der_norm //.
  rewrite quotient_odd ?(oddSg sHL) //=.
  rewrite (card_isog (quotient_isog (subset_trans sW1L nH'L) _)); last first.
    by rewrite coprime_TIg ?(coprimeSg (der_sub 1 H)).
  exact: Frobenius_dvd_ker1 frobL1.
rewrite -(prednK (indexg_gt0 _ _)) leqW // dvdn_leq //.
  by rewrite -subn1 subn_gt0 indexg_gt1 proper_subn.
rewrite gauss_inv ?(@pnat_coprime 2) -?odd_2'nat ?(oddSg sW1L) //.
rewrite dvdn2 -{1}subn1 odd_sub //.
rewrite -card_quotient ?(subset_trans (der_sub 1 H)) //.
rewrite quotient_odd ?(oddSg (der_sub 1 H)) ?(oddSg sHL) //=.
have /andP[sZL nZL] := nsZL.
rewrite (card_isog (quotient_isog (subset_trans sW1L nZL) _)); last first.
  by rewrite coprime_TIg ?(coprimeSg sZH).
suffices: [Frobenius (H^`(1) / Z) <*> (W1 / Z) = (H^`(1) / Z) ><| (W1 / Z)]%g.
  exact: Frobenius_dvd_ker1.
suffices: [Frobenius (L / Z) = (H / Z) ><| (W1 / Z)]%g.
  apply: Frobenius_subl (quotientS Z (der_sub 1 H)) _.
    by rewrite quotient_neq1 // (normalS sZH' (der_sub 1 H)).
  by rewrite quotient_norms ?(subset_trans sW1L).
apply: (Frobenius_coprime_quotient defL nsZL) => //; split=> [|x W1x].
  exact: sub_proper_trans sZH' ltH'H.
have /caseB_P[/c2W2[_ _ [/= _ [_ [_ _ _ -> //] _] _ _]] _ _] := in_caseB.
by rewrite /Z (negPf in_caseB).
Qed.

End Six.


