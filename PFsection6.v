(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator gseries nilpotent.
Require Import sylow abelian maximal.
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
Import Prenex Implicits.

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
  rewrite (leq_trans lbHA) // -(divgS sBH) leq_divr // -(LaGrange sAH).
  by rewrite mulnC leq_pmul2r // subset_leq_card.
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
    & (*c*) exists E1, [Frobenius L / H1 = (K / H1) ><| gval E1] ]%g.

(* This is Peterfalvi (6.5). *)
Lemma non_coherent_chief M (H1 := (K^`(1) <*> M)%G) :
   odd_Frobenius_quotient M ->
   coherent (S M) L^# tau
\/ [/\ (*a*) chief_factor L H1 K /\ (#|K : H1| <= 4 * #|L : K| ^ 2 + 1)%N
     & (*b*) exists2 p : nat, p.-group (K / M)%g /\ ~~ abelian (K / M)%g
     & (*c*) ~~ (#|L : K| %| p - 1)].
Proof.
case=> oddL [nsML sMK nilKb]; rewrite /= -(erefl (gval H1)) => frobLb.
have nsH1L: H1 <| L by rewrite normalY // (char_normal_trans (der_char 1 K)).
have sH1K: H1 \subset K by rewrite join_subG der_sub.
have cohH1: coherent (S H1) L^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohS _) _ => //.
  apply/(@all_pred1_constant _ #|L : K|%:R)/allP=> _ /mapP[chi Schi ->] /=.
  have [i /setIdP[_]] := seqIndP Schi; rewrite inE join_subG -lin_irr_der1.
  by do 2![case/andP]=> _ /eqP chi1 _ ->; rewrite cfInd1 // chi1 mulr1.
have sMH1: M \subset H1 by exact: joing_subr.
have [ubK | lbK] := leqP; last by left; exact: bounded_seqIndD_coherent lbK.
have [-> | neqMH1] := eqVneq M H1; [by left | right].
have{neqMH1} ltMH1: M \proper H1 by rewrite properEneq neqMH1.
have{frobLb} [[E1b frobLb] [sH1L nH1L]] := (frobLb, andP nsH1L).
have [defLb ntKb _ _ /andP[sE1L _]] := Frobenius_context frobLb.
have nH1K: K \subset 'N(H1) := subset_trans sKL nH1L.
have chiefH1: chief_factor L H1 K.
  have ltH1K: H1 \proper K by rewrite /proper sH1K -quotient_sub1 ?subG1.
  rewrite /chief_factor nsKL andbT; apply/maxgroupP; rewrite ltH1K.
  split=> // H2 /andP[ltH2K nH2L] sH12; have sH2K := proper_sub ltH2K.
  have /eqVproper[// | ltH21] := sH12; case/idPn: ubK; set e := #|L : K|.
  have dv_e H3: H1 \subset H3 -> H3 \subset K -> L \subset 'N(H3) ->
    #|H3 : H1| == 1 %[mod e].
  - move=> sH13 sH3K nH3L; rewrite eqn_mod_dvd // subn1.
    rewrite /e -(index_quotient_eq _ sKL nH1L) ?subIset ?sH1K ?orbT //.
    rewrite -[#|_ : _|]divgS ?quotientS // -(sdprod_card defLb) mulKn //.
    rewrite -card_quotient ?(subset_trans (subset_trans sH3K sKL)) //.
    rewrite regular_norm_dvd_pred ?(subset_trans sE1L) ?quotient_norms //.
    move=> x /(Frobenius_reg_ker frobLb) cKx1; apply/trivgP.
    by rewrite -cKx1 setSI ?quotientS.
  have dv_H21 := dv_e H2 sH12 sH2K nH2L.
  have dv_KH2: #|K : H2| == 1 %[mod e].
    have:= dv_e K sH1K (subxx K) nKL; rewrite -(LaGrange_index sH2K sH12).
    by rewrite -modn_mulmr (eqP dv_H21) modn_mulmr muln1.
  have lt_dv_e H3 H4 (m := #|H3 : H4|):
    H4 \proper H3 -> H3 \subset K -> m == 1 %[mod e] -> (2 * e + 1 <= m)%N.
  - move=> ltH43 sH3K; rewrite eqn_mod_dvd ?indexg_gt0 // -[m]odd_double_half.
    rewrite (dvdn_odd (dvdn_indexg _ _)) ?(oddSg (subset_trans sH3K sKL)) //.
    rewrite addnC addnK leq_add2r -mul2n leq_pmul2l // gauss.
      by move/dvdn_leq->; rewrite ?(@half_leq 2) // indexg_gt1 proper_subn.
    by rewrite coprime_sym prime_coprime // dvdn2 (dvdn_odd (dvdn_indexg _ _)).
  rewrite -ltnNge -(LaGrange_index sH2K sH12).
  apply: leq_trans (leq_mul (lt_dv_e _ _ _ _ _) (lt_dv_e _ _ _ _ _)) => //.
  rewrite mulnn sqrn_add expn_mull -addnA ltn_add2l add1n muln1 ltnS.
  by rewrite !muln_gt0 indexg_gt0.
have nMK := subset_trans sKL (normal_norm nsML).
have not_abKb: ~~ abelian (K / M).
  apply: contra (proper_subn ltMH1) => /derG1P/trivgP.
  rewrite /= join_subG subxx andbT -quotient_der ?quotient_sub1 //.
  exact: subset_trans (der_sub 1 K) nMK.
have [|_ _]:= minnormal_solvable (chief_factor_minnormal chiefH1) (subxx _).
  exact: quotient_sol solK.
case/is_abelemP=> p p_pr /and3P[pKb _ _].
have [_ p_dv_Kb _] := pgroup_pdiv pKb ntKb.
have pKM: p.-group (K / M)%g.
  have /dprodP[_ defKM cKMpp' tiKMpp'] := nilpotent_pcoreC p nilKb.
  rewrite -defKM (eqP (forall_inP (nilpotent_sol nilKb) 'O_p^'(_)%G _)).
    by rewrite  mulg1 pcore_pgroup.
  have /isomP[inj_quo im_quo] := quotient_isom (cents_norm cKMpp') tiKMpp'.
  rewrite subsetI pcore_sub /= -(injmSK inj_quo) // (morphim_der _ 1) //.
  rewrite {inj_quo}im_quo /= -[Q in Q^`(1)%g]quotientMidl defKM.
  rewrite -quotient_der ?gFnorm ?quotientS //.
  rewrite -quotient_sub1 ?(subset_trans (pcore_sub _ _) (der_norm _ _)) //.
  rewrite -[(_ / _)%g]setIid coprime_TIg //.
  apply: pnat_coprime (quotient_pgroup _ (pcore_pgroup _ _)).
  apply: pgroupS (quotientS _ (pcore_sub _ _)) _.
  rewrite /= -quotient_der // -(quotientYidr (subset_trans (der_sub 1 K) nMK)).
  rewrite (isog_pgroup _ (third_isog _ _ _)) ?(normalS sMK sKL nsML) //.
  exact: (normalS sH1K sKL nsH1L).
split=> //; exists p => //.
set e := #|L : K|; apply: contra not_abKb => e_dv_p1.
rewrite cyclic_abelian // Phi_quotient_cyclic //.
have /homgP[f <-]: (K / M / 'Phi(K / M) \homg K / H1)%g.
  have:= third_isog sMH1 (normalS sMK sKL nsML) (normalS sH1K sKL nsH1L).
  move/isog_hom; apply: homg_trans.
  rewrite homg_quotientS ?gFnorm ?quotient_norms //=.
  rewrite quotientYidr ?(subset_trans (der_sub 1 K)) // quotient_der //.
  by rewrite (Phi_joing pKM) joing_subl.
rewrite {f}morphim_cyclic // abelian_rank1_cyclic; last first.
  by rewrite sub_der1_abelian ?joing_subl.
rewrite (rank_pgroup pKb) (leq_trans (p_rank_le_logn _ _)) //.
rewrite -ltnS -(ltn_exp2l _ _ (prime_gt1 p_pr)) -p_part part_pnat_id //.
rewrite card_quotient // (leq_ltn_trans ubK) //.
have{e_dv_p1} lb_p: (2 * #|L : K| + 1 <= p)%N.
  move: e_dv_p1; rewrite -[p]odd_double_half.
  rewrite (dvdn_odd p_dv_Kb) ?quotient_odd ?(oddSg sKL) //.
  rewrite addnC addnK leq_add2r -mul2n leq_pmul2l // gauss.
    by move/dvdn_leq->; rewrite ?(@half_leq 2) // prime_gt1.
  by rewrite coprime_sym prime_coprime // dvdn2 (dvdn_odd (dvdn_indexg _ _)).
apply: leq_trans (leq_mul lb_p lb_p).
rewrite mulnn sqrn_add expn_mull -addnA ltn_add2l add1n muln1 ltnS.
by rewrite !muln_gt0 indexg_gt0.
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
have isoK1 := isog_symr (quotient1_isog K).
have [oddL _ []] := Frob_quo1; set e := #|L : K|.
have e_gt0: (e > 0)%N by exact: indexg_gt0.
rewrite /= joingG1 => Eb frobLb _ [p [pK not_abK] not_e_dv_p1].
rewrite (isog_abelian isoK1) {isoK1}(isog_pgroup _ isoK1) in not_abK pK.
have ntK: K :!=: 1%g by apply: contraNneq not_abK => ->; exact: abelian1.
have{ntK not_abK} [p_pr p_dv_K _] := pgroup_pdiv pK ntK.
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
pose mrem := (inE, mem_rem_uniq, subseq_uniq (rem_subseq _ _)).
pose Y' := rem chi^*%CF (rem chi Y); pose X'' := [:: chi, chi^*%CF & X'].
have ccY': conjC_closed Y'.
  move=> xi; rewrite !mrem // !(inv_eq (@cfConjCK _ _)) cfConjCK andbCA.
  by case/and3P=> -> -> /ccY.
have Xchi := sYX _ Ychi; have defY: perm_eq [:: chi, chi^*%CF & Y'] Y.
  rewrite (perm_eqrP (perm_to_rem Ychi)) perm_cons perm_eq_sym perm_to_rem //.
  by rewrite !mrem ?ccY // (seqInd_conjC_neq _ _ _ Xchi).
apply: perm_eq_coherent (defY) _ _.
  have: free calX by exact: seqInd_free.
  by rewrite (free_perm_eq defY) -(free_perm_eq defX); exact: free_catl. 
have d_chic: d chi^*%CF = d chi.
  by rewrite /d cfunE isNatC_conj // (seqInd1_Nat Xchi).
have /andP[uniqY' Y'x1]: uniq Y' && (xi1 \in Y').
  rewrite ?mrem // Yxi1 andbT -negb_or.
  by apply: contraL lt_xi1_chi => /pred2P[] ->; rewrite ?d_chic ltnn.
have{mrem} xi1P: [&& xi1 \in Y', chi \in calS & chi \notin Y'].
  by rewrite Y'x1 sYS ?mrem // eqxx andbF.
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
set sum_Y' := \sum_( xi <- Y') _.
pose sum_X'' := (\sum_(xi <- X'') (e * p ^ d xi) ^ 2)%N.
have def_sumX: sum_Y' + sum_X''%:R = (#|L : Z| * #|Z|.-1)%:R.
  rewrite -subn1 -(indexg1 Z) natr_mul natr_sub //.
  rewrite -(sum_seqIndD_square nsKL) ?normal1 ?sub1G // -/calX.
  rewrite -(eq_big_perm _ defX) big_cat /= -/sum_Y'; congr (_ + _).
  rewrite natr_sum; apply: eq_big_seq => xi X''xi.
  have Xxi: xi \in calX by rewrite -(perm_eq_mem defX) mem_cat X''xi orbT.
  by have /irrP[i {3 4}->] := irrX _ Xxi; rewrite cfnorm_irr divr1 natr_exp Ndg.
have def_sumY': sum_Y' = (e ^ 2 * \sum_(xi <- Y') p ^ (d xi).*2)%:R.
  rewrite big_distrr natr_sum /=; apply: eq_big_seq => xi /sY'Y/sYX Xxi.
  rewrite -muln2 expn_mulr -expn_mull natr_exp -Ndg //.
  by have /irrP[i ->] := irrX _ Xxi; rewrite cfnorm_irr divr1.
rewrite -expn_mulr muln2 def_sumY' -leq_leC dvdn_leq //.
  by rewrite muln_gt0 expn_gt0 e_gt0 /= (bigD1_seq xi1) //= addn_gt0 pos_p.
rewrite gauss_inv ?coprime_expl ?coprime_expr //; last first.
  have [defLb ntKb _ _ _] := Frobenius_context frobLb.
  have ->: e = #|Eb|.
    apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 K)) LaGrange //.
    have /andP[sK'L nK'L] := char_normal_trans (der_char 1 K) nsKL.
    rewrite -(LaGrange sK'L) -card_quotient // -(sdprod_card defLb).
    by rewrite card_quotient ?der_norm // mulnA LaGrange ?der_sub.
  have:= Frobenius_coprime frobLb.
  have [_ _ [k ->]] := pgroup_pdiv (quotient_pgroup _ pK) ntKb.
  by rewrite coprime_pexpl // coprime_sym.
have dv_chi2_X'': p ^ (d chi).*2 %| sum_X''.
  rewrite /sum_X'' big_seq dvdn_sum // => xi /le_chi_X'' le_chi_xi.
  by rewrite expn_mull -expn_mulr -muln2 dvdn_mull // dvdn_exp2l ?leq_pmul2r.
rewrite dvdn_mulr //= -(dvdn_addl _ dv_chi2_X'') -(getNatC_nat (_ + _)).
rewrite natr_add -def_sumY' def_sumX getNatC_nat dvdn_mulr //.
rewrite -(LaGrange_index sKL sZK) dvdn_mull //.
have /p_natP[k defKZ]: p.-nat #|K : Z| by rewrite (pnat_dvd (dvdn_indexg K Z)).
rewrite defKZ dvdn_exp2l // -(leq_exp2l _ _ (prime_gt1 p_pr)) -{k}defKZ.
rewrite leq_leC -muln2 expn_mulr natr_exp -d_r -divgS //.
rewrite (leC_trans (irr1_bound r).1) // -leq_leC leq_divr // mulnC.
rewrite -(LaGrange (cfcenter_sub 'chi_r)) leq_pmul2r // subset_leq_card //.
by rewrite (subset_trans sZ_ZK) // -cap_cfcenter_irr bigcap_inf.
Qed.

End GeneralCoherence.

End Six.


