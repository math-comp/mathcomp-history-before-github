(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection10.

(******************************************************************************)
(*   This file covers B & G, section 11.                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Section11.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Types p q r : nat.
Implicit Types A E H K M N P Q R S T U V W X Y : {group gT}.

Variables (p : nat) (M A0 A P : {group gT}).

(* This definition corresponsd to Hypothesis 11.1; however we have made the   *)
(* dependency on A explicit, because in the only two lemmas that make use of  *)
(* the results in this section (Lemma 12.3 and Theorem 12.5) A is known; in   *)
(* addition, Lemma 10.5 would make it easy to generate A from A0.             *)
Definition exceptional_FTmaximal :=
  [/\ p \in \sigma(M)^', A \in 'E_p^2(M), A0 \in 'E_p^1(A) & 'N(A0) \subset M].

Hypotheses (maxM : M \in 'M) (excM : exceptional_FTmaximal).
Hypotheses (sylP : p.-Sylow(M) P) (sAP : A \subset P).

(* Splitting the excM hypothesis. *)
Let sM'p : p \in \sigma(M)^'. Proof. by case: excM. Qed.
Let Ep2A : A \in 'E_p^2(M). Proof. by case: excM. Qed.
Let Ep1A0 : A0 \in 'E_p^1(A). Proof. by case: excM. Qed.
Let sNA0_M : 'N(A0) \subset M. Proof. by case: excM. Qed.

(* Arithmetics of p. *)
Let p_pr : prime p := pnElem_prime Ep2A.
Let p_gt1 : p > 1 := prime_gt1 p_pr.
Let p_gt0 : p > 0 := prime_gt0 p_pr.

(* Group orders. *)
Let oA : #|A| = (p ^ 2)%N := card_pnElem Ep2A.
Let oA0 : #|A0| = p := card_pnElem Ep1A0.

(* Structure of A. *)
Let abelA : p.-abelem A. Proof. by case/pnElemP: Ep2A. Qed.
Let pA : p.-group A := abelem_pgroup abelA.
Let cAA : abelian A := abelem_abelian abelA.

(* Various set inclusions. *)
Let sA0A : A0 \subset A. Proof. by case/pnElemP: Ep1A0. Qed.
Let sPM : P \subset M := pHall_sub sylP.
Let sAM : A \subset M := subset_trans sAP sPM.
Let sCA0_M : 'C(A0) \subset M := subset_trans (cent_sub A0) sNA0_M.
Let sCA_M : 'C(A) \subset M := subset_trans (centS sA0A) sCA0_M.

(* Alternative E_p^1 memberships for A0; the first is the one used to state   *)
(* Hypothesis 11.1 in B & G, the second is the form expected by Lemma 10.5.   *)
(* Note that #|A0| = p (oA0 above) would wokr just as well.                   *)
Let Ep1A0_M : A0 \in 'E_p^1(M) := subsetP (pnElemS p 1 sAM) A0 Ep1A0.
Let Ep1A0_G : A0 \in 'E_p^1(G) := subsetP (pnElemS p 1 (subsetT M)) A0 Ep1A0_M.

(* This does not depend on exceptionalM, and could move to Section 10. *)
Lemma sigma'_Sylow_contra : p \in \sigma(M)^' -> ~~ ('N(P) \subset M).
Proof. by apply: contra => sNM; apply/existsP; exists P; rewrite sylP. Qed.

(* First preliminary remark of Section 11; only depends on sM'p and sylP. *)
Let not_sNP_M: ~~ ('N(P) \subset M) := sigma'_Sylow_contra sM'p.

(* Second preliminary remark of Section 11; only depends on sM'p, Ep1A0_M,    *)
(* and sNA0_M.                                                                *)
Lemma p_rank_exceptional : 'r_p(M) = 2.
Proof. exact: sigma'_Ep1G_rpM2 (sNA0_M). Qed.
Let rM := p_rank_exceptional.

(* Third preliminary remark of Section 11. *)
Lemma exceptional_pmaxElem : A \in 'E*_p(G).
Proof.
have [_ _ dimA]:= pnElemP Ep2A.
apply/pmaxElemP; split=> [|E EpE sAE]; first by rewrite !inE subsetT.
have [//|ltAE]: A :=: E \/ A \proper E := eqVproper sAE.
have [_ abelE] := pElemP EpE; have [pE cEE _] := and3P abelE.
suffices: logn p #|E| <= 'r_p(M) by rewrite leqNgt rM -dimA properG_ltn_log.
by rewrite logn_le_p_rank // inE (subset_trans cEE) ?(subset_trans (centS sAE)).
Qed.
Let EpmA := exceptional_pmaxElem.

(* This is B & G, Lemma 11.1. *)
Lemma exceptional_TIsigmaJ : forall g q Q1 Q2,
    g \notin M -> A \subset M :^ g ->
    q.-Sylow(M`_\sigma) Q1 -> q.-Sylow(M`_\sigma :^ g) Q2 ->
    A \subset 'N(Q1) :&: 'N(Q2) ->
     (*a*) Q1 :&: Q2 = 1
  /\ (*b*) (forall X, X \in 'E_p^1(A) -> 'C_Q1(X) = 1 \/ 'C_Q2(X) = 1).
Proof.
move=> g q Q1 Q2 notMg sAMg sylQ1 sylQ2; rewrite subsetI; case/andP=> nQ1A nQ2A.
have [-> | ntQ1] := eqsVneq Q1 1.
  by split=> [|? _]; last left; exact: (setIidPl (sub1G _)).
have [sQ1Ms qQ1 _] := and3P sylQ1.
have{qQ1} [q_pr q_dv_Q1 _] := pgroup_pdiv qQ1 ntQ1.
have{sQ1Ms q_dv_Q1} sMq: q \in \sigma(M).
  exact: pgroupP (pgroupS sQ1Ms (pcore_pgroup _ _)) q q_pr q_dv_Q1.
have{sylQ1} sylQ1: q.-Sylow(M) Q1.
  by rewrite (pSylow_Hall_Sylow (Hall_M_Msigma maxM)).
have sQ1M := pHall_sub sylQ1.
have{sylQ2} sylQ2g': q.-Sylow(M) (Q2 :^ g^-1).
  by rewrite (pSylow_Hall_Sylow (Hall_M_Msigma _)) // -(pHallJ2 _ _ _ g) actKV.
have sylQ2: q.-Sylow(G) Q2.
  by rewrite -(pHallJ _ _ (in_setT g^-1)) (Sylow_Sylow_sigma maxM).
suffices not_Q1_CA_Q2: gval Q2 \notin Q1 :^: 'O_(\pi(#|A|))^'('C(A)).
  have ncA: normed_constrained A.
    have ntA: A :!=: 1 by rewrite -cardG_gt1 oA (ltn_exp2l 0).
    exact: plength_1_normed_constrained ntA EpmA (mFT_proper_plength1 _).
  have q'A: q \notin \pi(#|A|).
    rewrite oA !(inE, primes_exp, primes_prime) //.
    by apply: contraNneq (sM'p) => <-.
  have maxnAq: forall Q, q.-Sylow(G) Q -> A \subset 'N(Q) -> Q \in |/|*(A; q).
    move=> Q sylQ; case/(max_normed_exists (pHall_pgroup sylQ)) => R maxR sQR.
    have [qR _] := mem_max_normed maxR.
    by rewrite -(group_inj (Hall_maximal sylQ (subsetT R) qR sQR)).
  have maxQ1 := maxnAq Q1 (Sylow_Sylow_sigma maxM sMq sylQ1) nQ1A.
  have maxQ2 := maxnAq Q2 sylQ2 nQ2A.
  have transCAQ := normed_constrained_meet_trans ncA q'A _ _ maxQ1 maxQ2.
  split=> [|X EpX].
    apply: contraNeq not_Q1_CA_Q2 => ntQ12; apply/imsetP.
    apply: transCAQ (sAM) (mmax_proper maxM) _ _.
      by rewrite (setIidPl sQ1M).
    by apply: contraNneq ntQ12 => tiQ2M; rewrite setIC -subG1 -tiQ2M setIS.
  apply/pred2P; apply: contraR not_Q1_CA_Q2; case/norP=> ntCQ1 ntCQ2.
  have [sXA _ oX] := pnElemPcard EpX.
  apply/imsetP; apply: transCAQ (centSS _ sXA cAA) _ ntCQ1 ntCQ2 => //.
  by rewrite mFT_cent_proper // -cardG_gt1 oX prime_gt1.
apply: contra notMg; case/imsetP=> k cAk defQ2.
have{cAk} Mk := subsetP sCA_M k (subsetP (pcore_sub _ _) k cAk).
have{k Mk defQ2} sQ2M: Q2 \subset M by rewrite defQ2 conj_subG.
have [sQ2g'M qQ2g' _] := and3P sylQ2g'.
case/(mmax_sigma_core_nt_pgroup maxM): qQ2g' => // [|_ _ _ -> //].
  by rewrite -!cardG_gt1 ?(card_Hall sylQ2g') ?(card_Hall sylQ1) in ntQ1 *.
by rewrite actKV.
Qed.

(* This is B & G, Corollary 11.2. *)
Corollary exceptional_TI_MsigmaJ : forall g,
  g \notin M -> A \subset M :^ g ->
    (*a*) M`_\sigma :&: M :^ g = 1
 /\ (*b*) M`_\sigma :&: 'C(A0 :^ g) = 1.
Proof.
Admitted.

End Section11.
