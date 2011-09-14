(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator nilpotent.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import frobenius inertia vcharacter. 
Require Import PFsection1 PFsection2 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 6:                                    *)
(* Some Coherence Theorems                                                    *)
(* Defined here:                                                              *)
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

(* PF 6.1 *)
Section PF61.

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
Let orthS: pairwise_orthogonal calS. Proof. by case: scohS. Qed.
Let sSS M : {subset S M <= calS}. Proof. exact: seqInd_sub. Qed.
Let ccS M : conjC_closed (S M). Proof. exact: cfAut_seqInd. Qed.
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
  (*b2*) unless (coherent (S B) L^# tau)
  (#|K : A|%:R - 1 <= 2%:R * #|L : C|%:R * sqrtC #|C : D|%:R).
Proof.
move=> [nsAL nsBL nsCL nsDL] [ltAK sBD sDC sCK sDbZC] cohA.
apply: unless_contra => not_ineq.
have sBC := subset_trans sBD sDC; have sBK := subset_trans sBC sCK.
have [sAK nsBK] := (proper_sub ltAK, normalS sBK sKL nsBL).
have{sBC} [nsAK nsBC] := (normalS sAK sKL nsAL, normalS sBC sCK nsBK).
pose wf S1 := [/\ uniq S1, {subset S1 <= calS} & conjC_closed S1].
pose S1 := [::] ++ S A; set S2 := [::] in S1; rewrite -[S A]/S1 in cohA.
have wfS1: wf S1 by split; [exact: seqInd_uniq | exact: sSS | exact: ccS].
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

End PF61.

End Six.



