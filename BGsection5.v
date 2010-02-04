(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import gfunc pgroups nilpotent gprod center commutators.
Require Import sylow abelian maximal hall BGsection1 BGsection2.
Require Import psmall.

(******************************************************************************)
(*   This file covers B & G section 5.                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Five.

Variable gT : finGroupType. 
Implicit Types G H K E R: {group gT}.
Implicit Type p : nat.

Axiom five_1a : forall R, 
  odd #|R| -> 2 < 'r(R) -> 'SCN_3(R) != set0.

(* lemmas whose pragmatics is still unclear to me *)
Lemma logn_ntG : forall G p, 0 < logn p #|G| -> G != 1%G.
Proof.
move => G p cardG; rewrite -proper1G properEcard sub1G. 
case: #|G| cardG; rewrite ?logn0 //; case; rewrite ?logn1 //= => *.
by apply: (@leq_trans 2); rewrite ?ltnS -?trivg_card_le1 ?eqxx.
Qed.

Lemma logn_injcard : forall G H p, 
    p.-group G -> p.-group H -> 0 < logn p #|G| <= logn p #|H| -> 
  #|G| <= #|H|.
Proof.
move=> G H p pG pH; case/andP=> cardG_ge0 HgeG.
have cardH_ge0 := leq_trans cardG_ge0 HgeG.
have ntG := logn_ntG cardG_ge0.
have ntH := logn_ntG cardH_ge0.
move: HgeG; case: (pgroup_pdiv pG ntG) => [pr_p _ [n ->]].
case: (pgroup_pdiv pH ntH) => [_ _ [m ->]].
by rewrite !pfactorK // leq_exp2l //; case/primeP: pr_p.
Qed.

Lemma logn_injcard1 : forall G H p, 
    p.-group G -> p.-group H -> 0 < logn p #|G| < logn p #|H| -> 
  #|G| < #|H|.
Proof.
move=> G H p pG pH; case/andP=> cardG_ge0 HgeG.
have cardH_ge0 := ltn_trans cardG_ge0 HgeG.
have ntG := logn_ntG cardG_ge0.
have ntH := logn_ntG cardH_ge0.
move: HgeG; case: (pgroup_pdiv pG ntG) => [pr_p _ [n ->]].
case: (pgroup_pdiv pH ntH) => [_ _ [m ->]].
by rewrite !pfactorK // ltn_exp2l //; case/primeP: pr_p.
Qed.

Lemma  five_1b : forall R E p, 
  p.-group R -> odd #|R| -> 2 < 'r(R) -> E \in 'E_p^2(R) -> E <| R ->
    exists2 B, B \in 'SCN_3(R) & E \subset B.
Proof.
move=> R E p pR oddR rgt2 EE nER.
have ntR : R != 1%G by rewrite -rank_gt0 (ltn_trans _ rgt2).
have [p_pr pdvR [r oRpr]] := pgroup_pdiv pR ntR.
have pE := pgroupS (normal_sub nER) pR.
case/pnElemP: EE=> sER abelemE cardE.
have {nER} nER := normal_norm nER.
have [B nBR pnelemB] : exists2 B : {group gT}, B <| R & B \in 'E_p^3(R). 
  case: (set_0Vmem 'SCN_3(R)).
    move=> abs; move: (five_1a oddR rgt2); rewrite -abs. 
    by move/negP; rewrite eqxx; case. (* ?? *)
  case=> B; case/setIdP=> scnB rB.
  have abelianB := SCN_abelian scnB; have [nBR cBB] := SCN_P _ _ scnB.
  have pB := pgroupS (normal_sub nBR) pR. 
  have cardB : 3 <= logn p #|B|. 
    move: rB; rewrite (rank_pgroup pB); case/p_rank_geP=> B'. 
    case/pnElemP=> sB'B abelemB' cardB'.
    by rewrite (leq_trans _ (lognSg _ sB'B)) // cardB'. 
  case: (normal_pgroup pR nBR cardB)=> C [sCB nCR cardC].
  exists C=> //; apply/pnElemP. 
  rewrite cardC logn_exp logn_prime // eqxx muln1 (normal_sub nCR); split=> //.
  apply/(abelemP p_pr); rewrite (abelianS sCB abelianB); split=> //.
  admit. (* do I really need it's elementary? *)
have sBR := normal_sub nBR; have {nBR} nBR := normal_norm nBR.
pose Bs := E <*> 'C_B(E).
have sBsR : Bs <| R.
  rewrite /Bs norm_mulgenEr ?subIset ?cent_sub 1?orbC //.
  rewrite normalM /normal ?sER ?nER // subIset ?sBR //= normsI //.
  by rewrite (subset_trans _ (cent_norm _)).
have pB : p.-group B by case/pnElemP: pnelemB=> _; case/andP.
have pBs : p.-group Bs.
  rewrite /Bs norm_mulgenEr ?subIset ?cent_sub 1?orbC //.
  by rewrite pgroupM pE (pgroupS _ pB) ?subIset ?subxx.
have cardB : logn p #|B| = 3 by case/pnElemP: pnelemB.
have abelianB : abelian B by case/pnElemP: pnelemB=> _; case/and3P.
case: (ltnP (logn p #|Bs|) 3); last first.
  have := centralizer_scn_pgroup_eq.
  admit.
move=> cardBs.
  have defE : Bs :=: E.
    apply/eqP; rewrite eq_sym eqEcard mulgen_subl.
    rewrite (logn_injcard pBs pE) // cardE -(@ltnS _ 2) cardBs.
    by rewrite (leq_trans _ (lognSg p (mulgen_subl _ _))) // cardE.
  have sCE : 'C_B(E) \subset E by rewrite -{2}defE /Bs mulgen_subr.
  have nEB : B \subset 'N(E) by exact: subset_trans sBR nER.
  have cardBq' : logn p #| B / 'C_B(E) | <= 1.
    rewrite card_quotient ?normsI ?normG ?(subset_trans _ (cent_norm E)) //.
    by rewrite logn_quotient_cent_abelem ?cardE ?(subset_trans sBR).
  have ? : 2 <= logn p #|'C_B(E)|.
    rewrite -cardE. 
    (* still unused cardBq' *)
    admit.
  have defE' : 'C_B(E) :=: E.
    apply/eqP; rewrite eqEcard sCE (logn_injcard pE) // 1?cardE //=.
    by rewrite (@pgroupS _ _ B) // subIset ?subxx.
  have abs1 : E \proper B.
    rewrite -defE' properEcard subIset ?subxx //= defE'.
    by rewrite (logn_injcard1 pE pB) // !cardE cardB.
  have abs2 : 'C_B(E) :=: B.
    apply/eqP; rewrite eqEsubset subIset ?subxx //.
    (* still unused cardBq' *)
    admit.
by move/eqP: abs2; rewrite eqEproper; case/andP=> _; case/negP; rewrite defE'.
Qed.

End Five.
