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
case: (ltnP (logn p #|Bs|) 3); move=> cardBs.
  have defE : Bs :=: E.
    apply/eqP; rewrite eq_sym eqEcard mulgen_subl.
    rewrite (logn_injcard pBs pE) // cardE -(@ltnS _ 2) cardBs.
    by rewrite (leq_trans _ (lognSg p (mulgen_subl _ _))) // cardE.
  have sCE : 'C_B(E) \subset E by rewrite -{2}defE /Bs mulgen_subr.
  have nEB : B \subset 'N(E) by exact: subset_trans sBR nER.
  have cardBq' : logn p #| B / 'C_B(E) | <= 1.
    rewrite card_quotient ?normsI ?normG ?(subset_trans _ (cent_norm E)) //.
    by rewrite logn_quotient_cent_abelem ?cardE ?(subset_trans sBR).
  have cardCBE : 2 <= logn p #|'C_B(E)|.
    move: cardBq'; rewrite card_quotient; last first. 
      by rewrite normsI ?normG ?(subset_trans nEB (norms_cent _)). 
    rewrite -divgS ?subIset ?subxx //=. 
    rewrite logn_div ?cardB ?cardSg ?subIset ?subxx //.
    by case: (logn _ _)=> //; case.
  have defE' : 'C_B(E) :=: E.
    apply/eqP; rewrite eqEcard sCE (logn_injcard pE) // 1?cardE ?cardCBE //=.
    by rewrite (@pgroupS _ _ B) // subIset ?subxx.
  have abs1 : E \proper B.
    rewrite -defE' properEcard subIset ?subxx //= defE'.
    by rewrite (logn_injcard1 pE pB) // !cardE cardB.
  have abs2 : 'C_B(E) :=: B.
    apply/eqP; rewrite eqEsubset subIset ?subxx // subsetI subxx /=.
    by rewrite sub_abelian_cent // proper_sub.
  by move/eqP: abs2; rewrite eqEproper; case/andP=> _; case/negP; rewrite defE'.
have p44 := centralizer_scn_pgroup_eq.
admit.
Qed.

Lemma five_2 : forall R E p,
  odd #|R| -> p.-group(R) -> 2 < 'r(R) -> E \in 'E*_p(R) -> 'r(E) = 2 ->
  let T := 'C_R('Ohm_1('Z_2(R))) in
  [/\ ~~ (E \subset T),  #| 'Ohm_1('Z(R)) | = p, 'Ohm_1('Z_2(R))%G \in 'E_p^2(R),
      T \char R & #| R : T | = p ].
Proof.
move=> R E p oddp pR rankR pmaxE; case/pmaxElemP: (pmaxE).
case/pElemP=> sER abelemE maxE rankE T.
have ntR : (R != 1)%G by rewrite -rank_gt0 (ltn_trans _ rankR).
have [p_pr pdvR [r oRpr]] := pgroup_pdiv pR ntR.
pose Z := 'Ohm_1('Z(R)); pose W := 'Ohm_1('Z_2(R)).
have defEZ : E <*> Z :=: E * Z.
  have ? : R \subset 'N('Z(R)) by rewrite ?(char_norm _) ?center_char.
  by rewrite /= norm_mulgenEl ?(char_norm_trans (Ohm_char 1 'Z(R))) ?(subset_trans sER) //=.
have pZ : p.-group 'Z(R) by rewrite (pgroupS (center_sub _)).
have ? := abelian_center R.
have abelemEZ : p.-abelem (E <*> Z).
  apply/(abelemP p_pr); split.
    rewrite /= defEZ abelianM (abelem_abelian abelemE) (abelem_abelian (Ohm1_abelem pZ _)) //=.
    apply: (centSS sER (Ohm_sub _ _)). apply/centsP=> x Rx y. case/centerP=> Ry Cy.
    by apply: commute_sym; apply Cy. 
  move=> x; rewrite /= defEZ; case/mulsgP=> e z Ee Zz -> {x}.
  have commz : z \in 'Z(R) := subsetP (Ohm_sub _ _) _ Zz.
  have defzp : z^+p = 1.
    have Gz : group_set [set x \in 'Z(R) | x ^+p == 1].
      rewrite /group_set !inE !in_group exp1gn eqxx; apply/subsetP=> x.
      case/mulsgP=> x1 x2; case/setIdP=> Zx1 xp1; case/setIdP=> Zx2 xp2 ->.
      rewrite inE groupM // expMgn ?(eqP xp1) ?(eqP xp2) ?mulg1 ?eqxx //.
      by case/centerP: Zx1=> Rx1; apply; apply: (subsetP (center_sub _)).
    suff: z \in Group Gz by rewrite inE; case/andP=> _; move/eqP.
    apply: (subsetP _ _ Zz); rewrite gen_subG; apply/subsetP=> x.
    case/setIdP=> Zx xp /=; rewrite inE Zx -(eqP xp).
    case: (eqVneq x 1); first by move ->; rewrite !exp1gn eqxx.
    move=> x1; rewrite (pdiv_p_elt (mem_p_elt (pgroupS (center_sub _) pR) Zx) x1). 
    by rewrite expn1 eqxx.
  have ? : commute z e by case/centerP: commz=> _; apply; apply: (subsetP sER). 
  by rewrite expMgn // defzp mulg1; case/(abelemP p_pr): abelemE=> _; apply.
have defE : E * Z = E.
  rewrite -defEZ maxE ?mulgen_subl //; rewrite inE abelemEZ mulgen_subG sER.
  by rewrite (subset_trans (char_sub (Ohm_char 1 _))) ?center_sub.
have sZE : Z \subset E by rewrite -defE mulg_subr.
have rankCRE : 'r('C_R(E)%G) = 2.
  by rewrite -rankE -rank_Ohm1 (Ohm_cent pmaxE pR). 
have five1b : #| Z | = p.
  case: (eqVneq 'Z(R) 1) => trivZ.
    move: ntR; have defR := (trivg_center_pgroup pR trivZ). 
    by case/negP; rewrite -(inj_eq (@group_inj _)) /= defR eqxx. 
  apply:  Ohm1_cyclic_pgroup_prime; rewrite ?(pgroupS (center_sub _) pR) //.
  (*
  rewrite (odd_pgroup_rank1_cyclic pZ) ?(oddSg (center_sub _)) //=.

  apply/eqP; rewrite eqn_leq -(odd_pgroup_rank1_cyclic pZ). p_rank_abelian //.
  *)
  admit.
have five1a : Z \proper E.
  rewrite properEcard sZE (logn_injcard1 (pgroupS _ pR)) ?abelem_pgroup //.
     exact: subset_trans (Ohm_sub _ _) (center_sub _).
  by rewrite -(rank_abelem abelemE) rankE five1b logn_prime // eqxx.
admit.
Qed.

End Five.
