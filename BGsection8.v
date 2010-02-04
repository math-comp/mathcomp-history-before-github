(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime binomial groups.
Require Import morphisms perm action automorphism normal zmodp cyclic.
Require Import gfunc pgroups nilpotent gprod center commutators sylow abelian.
Require Import maximal hall BGsection1 BGsection6 BGsection7.

(******************************************************************************)
(*   This file covers B & G, section 8, i.e., the proof of two special cases  *)
(* of the Uniqueness Theorem, for maximal groups with Fitting subgroups of    *)
(* rank at least 3.                                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ToLibrary.

Variables (pi : nat_pred) (gT : finGroupType).
Implicit Type G : {group gT}.

Lemma bigcap_p'core : forall G,
  G :&: \bigcap_(p < #|G|.+1 | (p : nat) \in pi) 'O_p^'(G) = 'O_pi^'(G).
Proof.
move=> G; apply/eqP; rewrite eqEsubset subsetI pcore_sub pcore_max /=.
- by apply/bigcapsP=> p pi_p; apply: sub_pcore => r; apply: contra; move/eqnP->.
- apply/pgroupP=> q q_pr qGpi'; apply: contraL (eqxx q) => /= pi_q.
  apply: (pgroupP _ _ (pcore_pgroup q^' G)) => //.
  have qG: q %| #|G| by rewrite (dvdn_trans qGpi') // cardSg ?subsetIl.
  have ltqG: q < #|G|.+1 by rewrite ltnS dvdn_leq.
  rewrite (dvdn_trans qGpi') ?cardSg ?subIset //= orbC.
  by rewrite (bigcap_inf (Ordinal ltqG)).
rewrite /normal subsetIl normsI ?normG //.
apply big_prop => [|H K nHG nKG|p _]; rewrite ?normsI ?bgFunc_norm //.
by rewrite normsG // subsetT.
Qed.

Lemma trivg_Fitting : forall G, solvable G -> ('F(G) == 1) = (G :==: 1).
Proof.
move=> G solG; apply/idP/idP=> [F1|]; last first.
  by rewrite -!subG1; apply: subset_trans; exact: Fitting_sub.
apply/idPn; case/(solvable_norm_abelem _ (normal_refl _)) => // M [_] nsMG ntM.
case/is_abelemP=> p _; case/and3P=> pM _ _; case/negP: ntM.
by rewrite -subG1 -(eqP F1) Fitting_max ?(pgroup_nil pM).
Qed.

Lemma coprime_pcoreC : forall (xT : finGroupType) G (H : {group xT}),
  coprime #|'O_pi(G)| #|'O_pi^'(H)|.
Proof. move=> *; exact: pnat_coprime (pcore_pgroup _ _) (pcore_pgroup _ _). Qed.

Lemma TI_pcoreC : forall G H : {group gT}, 'O_pi(G) :&: 'O_pi^'(H) = 1.
Proof. by move=> G H; rewrite coprime_TIg ?coprime_pcoreC. Qed.

End ToLibrary.

Section Eight.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H M A X P: {group gT}.
Variable p : nat.

Local Notation "K ` q" := 'O_(nat_pred_of_nat q)(K)
  (at level 8, q at level 2, format "K ` q") : group_scope.
Local Notation "K ` q" := 'O_(nat_pred_of_nat q)(K)%G : subgroup_scope.

(* This is B & G, Theorem 8.1(a) *)
Lemma non_pcore_Fitting_Uniqueness : forall M A0,
    M \in 'M -> ~~ p.-group ('F(M)) -> A0 \in 'E*_p('F(M)) -> 'm(A0) >= 3 ->
  'C_('F(M))(A0)%G \in 'U.
Proof.
move=> M A0 maxM; set F := 'F(M) => p'F; case/pmaxElemP; rewrite 2!inE /= -/F.
case/andP=> sA0F abelA0 maxA0; have [pA0 cA0A0 _] := and3P abelA0.
rewrite grank_abelian // (rank_abelem abelA0) => dimA0_3.
set A := 'C_F(A0); pose pi := \pi(#|A|).
have [sZA sAF]: 'Z(F) \subset A /\ A \subset F by rewrite subsetIl setIS ?centS.
have piZ: \pi(#|'Z(F)|) = \pi(#|F|) by rewrite pi_center_nilpotent ?Fitting_nil.
have def_pi: pi = \pi(#|F|).
  by apply/eq_piP=> q; apply/idP/idP; last rewrite -piZ; exact: piSg.
have def_nZq: forall q, q \in pi -> 'N('Z(F)`q) = M.
  move=> q; rewrite def_pi -piZ -[q \in _]logn_gt0 -logn_part.
  rewrite -(card_Hall (nilpotent_pcore_Hall _ _)) /= -/F => [qZ|]; last first.
    by rewrite abelian_nil ?abelian_center.
  apply: normal_max_group => //=.
    apply: char_normal_trans (char_trans (pcore_char _ _) (center_char _)) _.
    exact: Fitting_normal.
  by apply: contraL qZ; move/eqP->; rewrite cards1 logn1.
have sCqM: forall q, q \in pi -> 'C(A`q) \subset M.
  move=> q; move/def_nZq <-; rewrite cents_norm // centS //.
  rewrite (subset_normal_Hall _ (nilpotent_pcore_Hall _ _)) ?pcore_normal //.
    by rewrite /psubgroup pcore_pgroup (subset_trans (pcore_sub _ _)).
  by apply: nilpotentS (Fitting_nil M); exact: subsetIl.
have sA0A: A0 \subset A by rewrite subsetI sA0F.
have pi_p: p \in pi.
  by apply: (piSg sA0A); rewrite -[p \in _]logn_gt0 (leq_trans _ dimA0_3).
have sCAM: 'C(A) \subset M.
  by rewrite (subset_trans (centS (pcore_sub p _))) ?sCqM.
have prM: M \proper G by rewrite inE in maxM; case/maxgroupP: maxM.
have piCA: pi.-group('C(A)).
  apply/pgroupP=> q q_pr; case/Cauchy=> // x cAx oxq; apply/idPn=> pi'q.
  have Mx := subsetP sCAM x cAx; pose C := 'C_F(<[x]>).
  have sAC: A \subset C by rewrite subsetI sAF centsC cycle_subG.
  have sCFC_C: 'C_F(C) \subset C.
    by rewrite (subset_trans _ sAC) ?setIS // centS ?(subset_trans _ sAC). 
  have cFx: x \in 'C_M(F).
    rewrite inE Mx -cycle_subG coprime_nil_faithful_cent_stab ?Fitting_nil //=.
      by rewrite cycle_subG (subsetP (bgFunc_norm _ _)).
    by rewrite -orderE coprime_pi' ?cardG_gt0 // -def_pi oxq pnatE.
  case/negP: pi'q; rewrite def_pi mem_primes q_pr cardG_gt0 -oxq cardSg //.
  by rewrite cycle_subG (subsetP (cent_sub_Fitting _)) ?proper_minSimple_sol.
have{p'F} pi_alt: forall q, exists2 r, r \in pi & r != q.
  move=> q; case: (eqVneq p q) => [<-{q} | ]; last by exists p.
  rewrite def_pi; apply/allPn; apply: contra p'F; move/allP=> /= pF.
  by apply/pgroupP=> q q_pr qF; rewrite !inE pF // mem_primes q_pr cardG_gt0.
have sNZqXq': forall (q : nat) X,
  A \subset X -> X \proper G -> 'O_q^'('N_X('Z(F)`q)) \subset 'O_q^'(X).
- move=> q X sAX prX.
  have sZqX: 'Z(F)`q \subset X.
    exact: subset_trans (pcore_sub _ _) (subset_trans sZA sAX).
  have cZqNXZ: 'O_q^'('N_X('Z(F)`q)) \subset 'C('Z(F)`q).
    have coNq'Zq: coprime #|'O_q^'('N_X('Z(F)`q))| #|'Z(F)`q|.
      by rewrite coprime_sym coprime_pcoreC.
    rewrite (sameP commG1P trivgP) -(coprime_TIg coNq'Zq) subsetI commg_subl /=.
    rewrite commg_subr /= andbC (subset_trans (pcore_sub _ _)) ?subsetIr //=.
    by rewrite (char_norm_trans (pcore_char _ _)) ?normsG // subsetI sZqX normG.
  have: 'O_q^'('C_X(('Z(F))`q)) \subset 'O_q^'(X).
    apply: p'core_cent_pgroup (proper_minSimple_sol prX).
    by rewrite /psubgroup sZqX pcore_pgroup.
  apply: subset_trans; apply: subset_trans (pcoreS _ (subcent_sub _ _)).
  by rewrite !subsetI subxx cZqNXZ (subset_trans (pcore_sub _ _)) ?subsetIl.
have sArXq': forall q r X,
  q \in pi -> q != r -> A \subset X -> X \proper G -> A`r \subset 'O_q^'(X).
- move=> q r X pi_q r'q sAX prX; apply: subset_trans (sNZqXq' q X sAX prX).
  apply: subset_trans (pcoreS _ (subsetIr _ _)).
  rewrite -setIA (setIidPr (pcore_sub _ _)) subsetI.
  rewrite (subset_trans (pcore_sub _ _)) //= def_nZq //.
  apply: subset_trans (pcore_Fitting _ _); rewrite -/F.
  have hallFq' := nilpotent_pcore_Hall q^' (Fitting_nil M).
  rewrite (subset_normal_Hall _ hallFq') ?pcore_normal //.
  rewrite /psubgroup (subset_trans (pcore_sub _ _)) //=.
  by apply: (pi_pnat (pcore_pgroup _ _)); rewrite !inE eq_sym.
have cstrA: normed_constrained A.
  split=> [||X Y sAX prX].
  - by apply/eqP=> A1; rewrite /pi A1 cards1 in pi_p.
  - exact: sub_proper_trans (subset_trans sAF (Fitting_sub _)) prM.
  rewrite !inE -/pi -andbA; case/and3P=> sYX pi'Y nYA.
  rewrite -bigcap_p'core subsetI sYX; apply/bigcapsP=> [[q /= _] pi_q].
  have [r pi_r q'r] := pi_alt q.
  have{sArXq'} sArXq': A`r \subset 'O_q^'(X) by apply: sArXq'; rewrite 1?eq_sym.
  have cA_CYr: 'C_Y(A`r) \subset 'C(A).
    have coYF: coprime #|Y| #|F|.
      by rewrite coprime_sym coprime_pi' ?cardG_gt0 // -def_pi.
    rewrite (sameP commG1P trivgP) -(coprime_TIg coYF) commg_subI //.
      by rewrite setIS // (subset_trans (sCqM r pi_r)) // bgFunc_norm.
    by rewrite subsetI subsetIl.
  have{cA_CYr} CYr1: 'C_Y(A`r) = 1.
    rewrite -(setIid Y) setIAC coprime_TIg // (coprimeSg cA_CYr) //.
    by rewrite (pnat_coprime piCA).
  have{CYr1} ->: Y :=: [~: Y, A`r].
    rewrite -(mulg1 [~: Y, _]) -CYr1 coprime_cent_prod //.
    - by rewrite (subset_trans (pcore_sub _ _)).
    - rewrite coprime_sym (coprimeSg (pcore_sub _ _)) //= -/A.
      by rewrite coprime_pi' ?cardG_gt0.
    by rewrite proper_minSimple_sol // (sub_proper_trans sYX).
  rewrite (subset_trans (commgS _ sArXq')) // commg_subr.
  by rewrite (char_norm_trans (pcore_char _ _)) ?normsG.
have{cstrA} nbyApi'1: forall q, q \in pi^' -> |/|*(A; q) = [set 1%G].
  move=> q pi'q.
  have trA: [transitive 'O_pi^'('C(A)), on |/|*(A; q) | 'JG].
    apply: normed_constrained_rank3_trans; rewrite //= -/A.
    rewrite -rank_abelem // in dimA0_3; apply: leq_trans dimA0_3 (rankS _).
    by rewrite /= -/A subsetI sA0A centsC subsetIr.
  have [Q maxQ defAmax]: exists2 Q, Q \in |/|*(A; q) & |/|*(A; q) = [set Q].
    case/imsetP: trA => Q maxQ defAmax; exists Q; rewrite // {maxQ}defAmax.
    suff ->: 'O_pi^'('C(A)) = 1 by rewrite /orbit imset_set1 act1.
    rewrite -(setIidPr (pcore_sub _ _)) coprime_TIg //.
    exact: pnat_coprime piCA (pcore_pgroup _ _).
  have{maxQ} qQ: q.-group Q by rewrite inE in maxQ; case/andP: (maxgroupp maxQ).
  case: (eqVneq Q 1%G) => [<- // |]; rewrite -val_eqE /= => ntQ.
  have{defAmax trA} defFmax: |/|*(F; q) = [set Q].
    apply/eqP; rewrite eqEcard cards1 -defAmax.
    have snAF: A <|<| F by rewrite nilpotent_subnormal ?Fitting_nil.
    have piF: pi.-group F by rewrite def_pi /pgroup pnat_pi ?cardG_gt0.
    case/(normed_trans_superset _ _ snAF): trA => //= _.
    by case/imsetP=> R maxR _ -> _; rewrite (cardsD1 R) maxR.
  have nQM: M \subset 'N(Q).
    apply/normsP=> x Mx; apply: congr_group; apply/set1P.
    rewrite -defFmax (acts_act (norm_acts_max_norm _ _)) ?defFmax ?set11 //.
    by apply: subsetP Mx; exact: bgFunc_norm.
  have{nQM} nsQM: Q <| M.
    rewrite inE in maxM; case/maxgroupP: maxM => _ maxM.
    rewrite -(maxM 'N(Q)%G) ?normalG ?proper_norm_minSimple // properT.
    by apply: contraL (pgroup_sol qQ); move/eqP->; exact: minSimple_nonSolvable.
  have sQF: Q \subset F by rewrite Fitting_max ?(pgroup_nil qQ).
  rewrite -(setIidPr sQF) coprime_TIg ?eqxx // in ntQ.
  by rewrite coprime_pi' ?cardG_gt0 // -def_pi (pi_pnat qQ).
rewrite -(cards1 M) subset_leq_card //; apply/subsetP=> H.
case/setIdP=> maxH sAH; rewrite inE -val_eqE /=; pose D := 'F(H).
have prH: H \proper G by rewrite inE in maxH; exact: (maxgroupp maxH).
have piD: \pi(#|D|) = pi.
  set sigma := \pi(_); have pi_sig: {subset sigma <= pi}.
    move=> q; rewrite -[q \in _]logn_gt0 -logn_part.
    rewrite -(card_Hall (nilpotent_pcore_Hall _ (Fitting_nil _))) /= -/D.
    case: (eqVneq D`q 1) => [-> | ntDq _]; first by rewrite cards1 logn1.
    apply: contraR ntDq; move/nbyApi'1=> defAmax; rewrite -subG1.
    pose qnA Q := q.-group Q && (A \subset 'N(Q)).
    have [|Q /= maxQ] := @maxgroup_exists _ qnA [group of D`q].
      rewrite /qnA pcore_pgroup (char_norm_trans (pcore_char _ _)) //.
      by rewrite (subset_trans sAH) ?bgFunc_norm.
    by rewrite (@set1P _ Q 1%G _) // -defAmax inE.
  apply/eq_piP=> q; apply/idP/idP=> [|pi_q]; first exact: pi_sig.
  apply/idPn=> sig'q; case: (eqVneq A`q 1) => [Aq1 | ntAq].
    move: pi_q; rewrite -[q \in _]logn_gt0 -logn_part.
    have nilA := nilpotentS sAF (Fitting_nil _).
    by rewrite -(card_Hall (nilpotent_pcore_Hall _ nilA)) /= Aq1 cards1 logn1.
  case/negP: ntAq; rewrite -subG1.
  have <-: 'O_sigma^'(H) = 1.
    apply/eqP; rewrite -trivg_Fitting; last first.
      by rewrite proper_minSimple_sol ?(sub_proper_trans (pcore_sub _ _)).
    have sFs'D: 'F(('O_sigma^'(H))) \subset D.
      rewrite Fitting_max ?Fitting_nil ?(char_normal_trans (Fitting_char _)) //.
      exact: pcore_normal.
    rewrite -(setIidPr sFs'D) coprime_TIg // coprime_pi' ?cardG_gt0 //.
    exact: pgroupS (Fitting_sub _) (pcore_pgroup _ _).
  rewrite -bigcap_p'core subsetI (subset_trans (pcore_sub _ _)) //=.
  apply/bigcapsP=> [[r /= _] sig_r]; apply: sArXq' => //; first exact: pi_sig.
  by apply: contra sig'q; move/eqP <-.
have cAD: forall q r, q != r -> D`q \subset 'C(A`r).
  move=> q r r'q; case: (eqVneq D`q 1) => [-> |]; first by rewrite sub1G.
  case/(pgroup_pdiv (pcore_pgroup _ _))=> q_pr qDq _.
(*
  case: (eqVneq A`r 1) => [-> |]; first by rewrite cents1.
  case/(pgroup_pdiv (pcore_pgroup _ _))=> r_pr rAr _. *)
  have sArHq': A`r \subset 'O_q^'(H).
    rewrite sArXq' // -piD mem_primes cardG_gt0 q_pr (dvdn_trans qDq) //.
    by rewrite cardSg ?pcore_sub.
  have coHqHq': coprime #|D`q| #|'O_q^'(H)| by rewrite coprime_pcoreC.
  rewrite (sameP commG1P trivgP) -(coprime_TIg coHqHq') commg_subI //.
    rewrite subsetI subxx /= p_core_Fitting (subset_trans (pcore_sub _ _)) //.
    exact: bgFunc_norm.
  rewrite subsetI sArHq' (subset_trans (subset_trans (pcore_sub _ _) sAH)) //.
  by rewrite /= p_core_Fitting bgFunc_norm.
have sDM: D \subset M.
  rewrite -[D]Sylow_gen gen_subG; apply/bigcupsP=> Q; case/SylowP=> q _.
  move/nilpotent_Hall_pcore=> ->; rewrite ?Fitting_nil //= -/D.
  have [r pi_r r'q] := pi_alt q.
  by apply: subset_trans (sCqM r pi_r); apply: cAD; rewrite eq_sym.
have cApHp': A`p \subset 'C('O_p^'(H)).
  have coApHp': coprime #|'O_p^'(H)| #|A`p|.
    by rewrite coprime_sym coprime_pcoreC.
  have solHp': solvable 'O_p^'(H).
    exact: solvableS (pcore_sub _ _) (proper_minSimple_sol prH).
  have nHp'Ap: A`p \subset 'N('O_p^'(H)).
    by rewrite (subset_trans (subset_trans (pcore_sub _ _) sAH)) ?bgFunc_norm.
  apply: subset_trans (coprime_cent_Fitting nHp'Ap coApHp' solHp').
  rewrite subsetI subxx centsC /= -['F(_)]Sylow_gen gen_subG.
  apply/bigcupsP=> Q; case/SylowP=> q q_pr.
  move/nilpotent_Hall_pcore=> ->; rewrite ?Fitting_nil //=.
  case: (eqVneq q p) => [-> |].
    rewrite -(setIidPl (subset_trans (pcore_sub _ _) (Fitting_sub _))).
    by rewrite TI_pcoreC sub1G.
  move/cAD; apply: subset_trans; rewrite !p_core_Fitting.
  by rewrite pcore_max ?pcore_pgroup //= -pcoreI pcore_normal.
have sHp'M: 'O_p^'(H) \subset M.
  by apply: subset_trans (sCqM p pi_p); rewrite centsC.
have ntDp: D`p != 1.
  apply: contraL pi_p; rewrite trivg_card1; move/eqnP=> Dq1.
  rewrite -piD -[p \in _]logn_gt0 -logn_part.
  by rewrite -(card_Hall (nilpotent_pcore_Hall _ (Fitting_nil _))) Dq1 logn1.
have sHp'_NMDp': 'O_p^'(H) \subset 'O_p^'('N_M(D`p)).
  apply: subset_trans (pcoreS _ (subsetIr _ _)).
  rewrite -setIA (setIidPr (pcore_sub _ _)) /= (normal_max_group maxH) //.
    by rewrite subsetI sHp'M subxx.
  by rewrite /= p_core_Fitting pcore_normal.
have{sHp'_NMDp'} sHp'Mp': 'O_p^'(H) \subset 'O_p^'(M).
  have pM_D: p.-subgroup(M) D`p.
    by rewrite /psubgroup pcore_pgroup (subset_trans (pcore_sub _ _)).
  apply: subset_trans (p'core_cent_pgroup pM_D (proper_minSimple_sol prM)).
  apply: subset_trans (pcoreS _ (subcent_sub _ _)).
  rewrite !subsetI sHp'_NMDp' sHp'M andbT /= (sameP commG1P trivgP).
  have coHp'Dp: coprime #|'O_p^'(H)| #|D`p|.
    by rewrite coprime_sym coprime_pcoreC.
  rewrite -(coprime_TIg coHp'Dp) subsetI commg_subl commg_subr /=.
  by rewrite p_core_Fitting !(subset_trans (pcore_sub _ _)) ?bgFunc_norm.
have sMp'H: 'O_p^'(M) \subset H.
  rewrite -(normal_max_group maxH (pcore_normal p H)) /= -p_core_Fitting //.
  rewrite -/D (subset_trans _ (cent_sub _)) // centsC.
  have solMp' := solvableS (pcore_sub p^' _) (proper_minSimple_sol prM).
  have coMp'Dp: coprime #|'O_p^'(M)| #|D`p|.
    by rewrite coprime_sym coprime_pcoreC.
  have nMp'Dp: D`p \subset 'N('O_p^'(M)).
    by rewrite (subset_trans (subset_trans (pcore_sub _ _) sDM)) ?bgFunc_norm.
  apply: subset_trans (coprime_cent_Fitting nMp'Dp coMp'Dp solMp').
  rewrite subsetI subxx centsC /= -['F(_)]Sylow_gen gen_subG.
  apply/bigcupsP=> Q; case/SylowP=> q _.
  move/nilpotent_Hall_pcore=> ->{Q}; rewrite ?Fitting_nil //.
  case: (eqVneq p q) => [<- |].
    rewrite -(setIidPl (subset_trans (pcore_sub _ _) (Fitting_sub _))).
    by rewrite TI_pcoreC sub1G.
  move/cAD; rewrite centsC; apply: subset_trans; rewrite !p_core_Fitting.
  rewrite pcore_max ?pcore_pgroup //= /normal subsetI Fitting_max; last first.
  - exact: pgroup_nil (pcore_pgroup _ _).
  - by rewrite /= -pcoreI pcore_normal.
  rewrite (subset_trans (pcore_sub _ _)) /=; last first.
    have sA0Fp: A0 \subset F`p.
      have hallFp: p.-Sylow(F) F`p := nilpotent_pcore_Hall p (Fitting_nil M).
      by rewrite (subset_normal_Hall _ hallFp) ?pcore_normal // /psubgroup sA0F.
    rewrite centsC (subset_trans sA0Fp) // (sameP commG1P trivgP).
    rewrite -(TI_pcoreC p M M) /= p_core_Fitting subsetI commg_subl commg_subr.
    by rewrite !(subset_trans (pcore_sub _ _)) ?bgFunc_norm.
  rewrite (subset_trans (subset_trans sAF (Fitting_sub _))) //.
  by rewrite -pcoreI bgFunc_norm.
have{sHp'Mp' sMp'H} eqHp'Mp': 'O_p^'(H) = 'O_p^'(M).
  apply/eqP; rewrite eqEsubset sHp'Mp'.
  apply: subset_trans (sNZqXq' p H sAH prH).
  apply: subset_trans (pcoreS _ (subsetIr _ _)).
  rewrite -setIA (setIidPr (pcore_sub _ _)) subsetI sMp'H /=.
  rewrite (normal_max_group maxM (char_normal_trans (pcore_char _ _) _)) //.
    by rewrite (char_normal_trans (center_char _)) ?Fitting_normal.
  apply: contraL pi_p; rewrite def_pi -piZ trivg_card1; move/eqnP=> Zp1.
  have sylZp := nilpotent_pcore_Hall p (abelian_nil (abelian_center 'F(M))).
  by rewrite -[p \in _]logn_gt0 -logn_part -(card_Hall sylZp) Zp1 logn1.
have ntHp': 'O_p^'(H) != 1.
  have [q pi_q p'q] := pi_alt p; apply: contraL pi_q => Hp'1.
  have sylDq: q.-Sylow(D) D`q := nilpotent_pcore_Hall q (Fitting_nil H).
  have Dq1: #|D`q| = 1%N.
    apply/eqP; rewrite -trivg_card1 -subG1 -(eqP Hp'1) /= p_core_Fitting.
    by rewrite sub_pcore // => r; move/eqnP->.
  by rewrite -piD -[q \in _]logn_gt0 -logn_part -(card_Hall sylDq) Dq1 logn1.
rewrite -(normal_max_group maxH (pcore_normal p^' H)) //= eqHp'Mp'.
by rewrite (normal_max_group maxM (pcore_normal _ _)) //= -eqHp'Mp'.
Qed.

End Eight.

