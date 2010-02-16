(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import gfunc pgroups nilpotent gprod center commutators.
Require Import sylow abelian maximal hall BGsection1 BGsection2.
Require Import BGsection4.



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

(* lemmas whose pragmatics is still unclear to me *)
Lemma logn_ntG : forall G p, 0 < logn p #|G| -> G :!=: 1.
Proof. by move=> G p; case: eqP => // ->; rewrite cards1 logn1. Qed.

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

(* B&G 5.1(a) *)
Lemma p_rank_3_SCN : forall p R, 
  p.-group R -> odd #|R| -> 2 < 'r(R) -> exists A, A \in 'SCN_3(R).
Proof.
move=> p R pR oddR rRgt2; apply/set0Pn. 
by rewrite -(rank2_SCN3_empty pR oddR) leqNgt rRgt2.
Qed.


(* B&G 5.1(b) *)
Lemma p_rank_3_normal_abelem_SCN : forall p R E, 
  p.-group R -> odd #|R| -> 2 < 'r(R) -> E \in 'E_p^2(R) -> E <| R ->
    exists2 B, B \in 'SCN_3(R) & E \subset B.
Proof.
move=> p R E pR oddR rRgt2 EE nER.
have ntR : R != 1%G by rewrite -rank_gt0 (ltn_trans _ rRgt2).
have [p_pr pdvR [r oRpr]] := pgroup_pdiv pR ntR.
have pE := pgroupS (normal_sub nER) pR.
case/pnElemP: EE=> sER abeE cardE.
have {nER} nER := normal_norm nER.
have [B nBR pnelemB] : exists2 B : {group gT}, B <| R & B \in 'E_p^3(R). 
  have [C] := p_rank_3_SCN pR oddR rRgt2.
  case/setIdP=> scnC rC; have [nCR cCC] := SCN_P _ _ scnC.
  case/maxgroupP: (SCN_max scnC); case/andP => _ abelianC maxC.
  have pC : p.-group C := pgroupS (normal_sub nCR) pR.
  have abelemOC : p.-abelem 'Ohm_1(C) := Ohm1_abelem pC abelianC.
  have cardOC : 3 <= logn p #|'Ohm_1(C)|.
    by rewrite -(rank_abelem abelemOC) rank_Ohm1.
  have nOCR : 'Ohm_1(C) <| R := char_normal_trans (Ohm_char 1 _) nCR.
  case: (normal_pgroup pR nOCR cardOC)=> B [sBOC nBR cardB].
  exists B => //; apply/pnElemP; rewrite (normal_sub _) //.
  by rewrite cardB logn_exp logn_prime // eqxx muln1 (abelemS sBOC abelemOC). 
have sBR := normal_sub nBR; have {nBR} nBR := normal_norm nBR.
pose Bs := (E <*> 'C_B(E))%G.
have nBsR : Bs <| R.
  rewrite /Bs /= norm_mulgenEr ?subIset ?cent_sub 1?orbC //.
  rewrite normalM /normal ?sER ?nER // subIset ?sBR //= normsI //.
  by rewrite (subset_trans _ (cent_norm _)).
have pB : p.-group B by case/pnElemP: pnelemB=> _; case/andP.
have pBs : p.-group Bs.
  rewrite /Bs /= norm_mulgenEr ?subIset ?cent_sub 1?orbC //.
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
have abelianBs : abelian Bs.
  rewrite /Bs /= mulgenC norm_mulgenEl ?subIset ?cent_sub 1?orbC //=.
  rewrite abelianM (abelem_abelian abeE) (abelianS (subsetIl _ _) abelianB).
  by rewrite /= subIset // subxx orbC.
have abeBs : p.-abelem Bs.
  apply/(abelemP p_pr); rewrite abelianBs; split=> //= x.
  rewrite norm_mulgenEr ?subIset ?cent_sub 1?orbC //=.
  case/mulsgP=> e c Ee; case/setIP=> Bc CEc -> {x}.
  move/centP: CEc=> centsc; have ? := (commute_sym (centsc _ Ee)).
  rewrite expMgn //; case/(abelemP p_pr): abeE=> _ ->; rewrite // mul1g.
  by case/pnElemP: pnelemB=> _; case/(abelemP p_pr) => _ ->.
have [C maxC sBsC] : {H | [max H | (H <| R) && abelian H ] & Bs \subset H}.
  by apply: maxgroup_exists; rewrite nBsR abelianBs.
exists C; last  by rewrite (subset_trans (mulgen_subl _ 'C_B(E))) //.
apply/setIdP; split; first exact: (max_SCN pR).
by rewrite (leq_trans cardBs) // -(rank_abelem abeBs) rankS.
Qed.

Lemma p_rank_3_maxElem_2_Ohm_ucl : forall R E p,
    odd #|R| -> p.-group(R) -> 2 < 'r(R) -> E \in 'E*_p(R) -> 'r(E) = 2 ->
    let T := 'C_R('Ohm_1('Z_2(R))) in
  [/\ ~~ (E \subset T), 
      #| 'Ohm_1('Z(R)) | = p, 'Ohm_1('Z_2(R))%G \in 'E_p^2(R),
      T \char R & #| R : T | = p ].
Proof.
move=> R E p oddR pR rankR pmaxE; case/pmaxElemP: (pmaxE).
case/pElemP=> sER abeE maxE rankE.
set Z := 'Ohm_1('Z(R)); set W := 'Ohm_1('Z_2(R))%G; move=> T.
have ntR : (R != 1)%G by rewrite -rank_gt0 (ltn_trans _ rankR).
have [p_pr pdvR [r oRpr]] := pgroup_pdiv pR ntR.
have nZR : R \subset 'N(Z).
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (center_char R)).
have nWR : R \subset 'N(W). 
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (ucn_char 2 R)) .
have defEZ : E <*> Z :=: E * Z.
  by rewrite /= norm_mulgenEl ?(subset_trans sER).
have pZ : p.-group 'Z(R) by rewrite (pgroupS (center_sub _)).
have ? := center_abelian R.
have abeEZ : p.-abelem (E <*> Z).
  apply/(abelemP p_pr); split.
    rewrite /= defEZ abelianM (abelem_abelian abeE).
    rewrite (abelem_abelian (Ohm1_abelem pZ _)) //=.
    apply: (centSS sER (Ohm_sub _ _)); apply/centsP=> x Rx y.
    by case/centerP=> Ry Cy; apply: commute_sym; apply Cy. 
  move=> x; rewrite /= defEZ; case/mulsgP=> e z Ee Zz -> {x}.
  have commz : z \in 'Z(R) := subsetP (Ohm_sub _ _) _ Zz.
  have defzp : z^+p = 1. (* fix this detour *)
    have Gz : group_set [set x \in 'Z(R) | x ^+p == 1].
      rewrite /group_set !inE !in_group exp1gn eqxx; apply/subsetP=> x.
      case/mulsgP=> x1 x2; case/setIdP=> Zx1 xp1; case/setIdP=> Zx2 xp2 ->.
      rewrite inE groupM // expMgn ?(eqP xp1) ?(eqP xp2) ?mulg1 ?eqxx //.
      by case/centerP: Zx1=> Rx1; apply; apply: (subsetP (center_sub _)).
    suff: z \in Group Gz by rewrite inE; case/andP=> _; move/eqP.
    apply: (subsetP _ _ Zz); rewrite gen_subG; apply/subsetP=> x.
    case/setIdP=> Zx xp /=; rewrite inE Zx -(eqP xp).
    case: (eqVneq x 1) => defx; first by rewrite defx !exp1gn eqxx.
    rewrite (pdiv_p_elt (mem_p_elt (pgroupS (center_sub _) pR) Zx) defx). 
    by rewrite expn1 eqxx.
  have ? : commute z e by case/centerP: commz=> _; apply; apply: (subsetP sER). 
  by rewrite expMgn // defzp mulg1; case/(abelemP p_pr): abeE=> _; apply.
have defE : E * Z = E.
  rewrite -defEZ maxE ?mulgen_subl //; rewrite inE abeEZ mulgen_subG sER.
  by rewrite (subset_trans (char_sub (Ohm_char 1 _))) ?center_sub.
have sZE : Z \subset E by rewrite -defE mulg_subr.
have rankCRE : 'r('C_R(E)%G) = 2.
  by rewrite -rank_Ohm1 (Ohm_cent pmaxE pR) rankE.
have pZZ : p.-group Z.
  by rewrite (pgroupS _ pR) //= (subset_trans (Ohm_sub 1 _) (center_sub _)).
have five1b : #| Z | = p.
  have ntZ : Z != 1.
    apply/negP; move/eqP => defZ; move: rankR.
    rewrite (nil_TI_Z (pgroup_nil pR) (normal_refl R)) ?rank1 //.
    by rewrite TI_Ohm1 // -/Z defZ; apply/setIidPr; rewrite sub1G.
  case: (pgroup_pdiv pZZ ntZ)=> _ _ [q]; case:q=> //= q; rewrite -/Z => cardZ.
  suff defR: 'C_R(E) = R.
    by rewrite /= defR in rankCRE; move: rankR; rewrite rankCRE.
  suff zSC : E \subset 'Z(R).
    apply/eqP; rewrite eqEsubset subsetIl /= subsetI subxx.
    apply/centsP=> x xR e eE; have Ze : e \in 'Z(R) by exact: subsetP zSC _ eE.
    by case/centerP: Ze => _ centra; move: (centra x xR); exact: commute_sym.
  suff -> : E :=: Z by exact: Ohm_sub.
  apply/eqP; rewrite eq_sym eqEcard sZE.
  apply: (logn_injcard (abelem_pgroup abeE) (pgroupS (Ohm_sub _ _) pZ)).
  by move: rankE; rewrite (rank_abelem abeE) cardZ (pfactorK _ p_pr) => ->.
have five1a : Z \proper E.
  rewrite properEcard sZE (logn_injcard1 (pgroupS _ pR)) ?abelem_pgroup //.
     exact: subset_trans (Ohm_sub _ _) (center_sub _).
  by rewrite -(rank_abelem abeE) rankE five1b logn_prime // eqxx.
have ncR : ~~ cyclic R.
  rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt -(rank_pgroup pR).
  by rewrite (leq_trans _ rankR).
case: (Ohm1_odd_ucn2 pR oddR ncR); rewrite -/W => ncW exponentW.
have sWR : W \subset R := (subset_trans (Ohm_sub 1 _) (ucn_sub _ _)).
have pW : p.-groupW := pgroupS sWR pR.
have abelemZ : p.-abelem Z by exact: (Ohm1_abelem pZ).
have five2a : Z \proper W.
  rewrite properEneq OhmS /= -?ucn1 ?ucn_subS 1?andbC //=.
  apply/negP; move/eqP=>defZ.
  move: ncW; rewrite (odd_pgroup_rank1_cyclic pW (oddSg sWR oddR)) /= -ltnNge. 
  by rewrite -defZ (p_rank_abelem abelemZ) five1b (logn_prime _ p_pr) eqxx.
have five2b : [~: W, R] \subset Z.
  have sWC : [~: W, R] \subset W by rewrite commg_subl.
  rewrite -(setIidPl sWC).
  admit.
have EWpE: [~: E, W] \proper E.
  by rewrite (sub_proper_trans (subset_trans _ five2b) five1a) 1?commGC ?commgS.
have nEW : W \subset 'N(E). 
  by move: EWpE; rewrite properEneq -commg_subl; case/andP.
have sCWEE : 'C_W(E) \subset E.
  have expCWE : exponent 'C_W(E) %| p.
    exact: dvdn_trans (exponentS (subsetIl _ _)) exponentW.
  apply/subsetP=> z zC; move/exponentP: expCWE=> expCWE.
  have zp1 := (expCWE _ zC).
  have abelemX : (E <*> <[z]>)%G \in 'E_p(R).
    rewrite inE /= mulgen_subG sER cycle_subG (subsetP _ _ zC) ?subIset ?sWR //.
    rewrite (cprod_abelem p (cprodEgen _)); last first.
      by rewrite centsC cycle_subG; case/setIP: zC.
    by rewrite abeE cycle_abelem 1?orbC ?p_pr // order_dvdn zp1 eqxx.
  rewrite -(maxE _ abelemX) ?mulgen_subl // (subsetP (mulgen_subr E _) z) //. 
  exact: cycle_id. 
have sZCWE : Z \subset 'C_W(E).  (* there must be a smarter way *)
  rewrite subsetI (proper_sub _) //= (subset_trans (Ohm_sub 1 _)) //=.
  apply/subsetP=> z; case/centerP=> zR zc; apply/centP=> e Ee.
  exact: zc e (subsetP sER _ Ee).
case: (eqsVneq E 'C_W(E)) => [defCEW | CEWnE].
  have sCERE : [~: E, R] \proper E.
    rewrite (sub_proper_trans _ five1a) // (subset_trans _ five2b) // commSg //.
    by rewrite defCEW subsetIl.
  have nER : E <| R by rewrite /normal sER -commg_subl (proper_sub sCERE).
  have Ep2E : E \in 'E_p^2(R).
    by apply/pnElemP; rewrite abeE sER -(rank_abelem abeE) rankE.
  case: (p_rank_3_normal_abelem_SCN pR oddR rankR Ep2E nER) => B scn3B sEB.
  case/setIdP: scn3B=> scnB rankB; case/SCN_P: scnB=> nBR CB.
  suff rb :'r(B) = 2 by rewrite rb in rankB. 
  rewrite (rank_pgroup (pgroupS _ pR)); last by rewrite -CB subIset ?subxx.
  have sEOB : E \subset 'Ohm_1(B) by rewrite -(Ohm1_id abeE) OhmS.
  have pE := (abelem_pgroup abeE).
  rewrite -p_rank_Ohm1 (maxE _ _ sEOB) -?(rank_pgroup pE) ?rankE //.
  rewrite inE Ohm1_abelem ?(pgroupS (normal_sub nBR) pR) 1?andbC //=.
    exact: subset_trans (char_sub (Ohm_char 1 B)) (normal_sub nBR).
  by rewrite /abelian -{1}CB subIset // orbC subxx.
have {CEWnE sCWEE} CWEpE : 'C_W(E) \proper E.
  by rewrite properEneq eq_sym CEWnE sCWEE.
have defCWE : 'C_W(E) = Z.
  apply/eqP; rewrite eq_sym eqEcard sZCWE andbC /= andbC.
  apply: (logn_injcard (pgroupS _ pR) pZZ).
  rewrite (subset_trans (subsetIl _ _)) //.
  move: CWEpE; rewrite properEcard five1b (logn_prime _ p_pr) eqxx -/W. 
  have -> : #|E| = (p^2)%N.
    have ntE : E :!=: 1 by move: rankE; case: eqP => // ->; rewrite rank1.
    have [_ _ [t cE]] := pgroup_pdiv (pgroupS sER pR) ntE.
    by move: rankE; rewrite (rank_abelem abeE) cE => <-; rewrite pfactorK.
  have ntCE : 'C_W(E) :!=: 1.
    apply/negP; move/eqP=> defCWE; move: sZCWE; rewrite defCWE.
    rewrite subG1 /=; move/eqP => abs; move: five1b; rewrite /Z abs cards1=> p1.
    by case/primeP: p_pr; rewrite p1 ltnn.
  have [_ _ [s ->]] := pgroup_pdiv (pgroupS (subsetIl _ _) pW) ntCE.
  case/andP=> _; case s; rewrite ?logn_prime ?expn1 ?eqxx // => m.
  rewrite !expnS; case/primeP : p_pr => gtp0 _.
  rewrite ltn_mul2l [0 < _](leqW gtp0) ltn_mul2l [0 < _](leqW gtp0) //= expn0.
  rewrite -(exp1n m); case m; rewrite ?expn0 // => w; rewrite ltn_exp2r //.
  by move/(leq_trans gtp0).
have WCWEgt0 : 1 < #| W / 'C_W(E) |.
  rewrite defCWE (_:1%N = #| Z / Z |); last first.
    by apply/eqP; rewrite eq_sym trivg_quotient -trivg_card1 eqxx.
  apply: proper_card; rewrite quotient_proper // /normal proper_sub //= -/Z.
  by rewrite (subset_trans _ nZR).
have cardWZ : #| W / Z | = p.
  rewrite -defCWE; move: rankE; rewrite (rank_abelem abeE) => cE.
  have ntWCWE : (W / 'C_W(E)) != 1 by rewrite -cardG_gt1.
  have pQ : p.-group (W/'C_W(E)) := quotient_pgroup _ pW.
  have [_ _ [n cardCWE]] := pgroup_pdiv pQ ntWCWE.
  have := logn_quotient_cent_abelem nEW abeE (eq_leq cE).
  rewrite -card_quotient  ?normsI ?normG ?norms_cent //.
  by move: WCWEgt0; rewrite cardCWE (pfactorK _ p_pr); case n.
have cardW : #| W | = (p^2)%N.
  rewrite -(LaGrange (proper_sub five2a)) five1b.
  by rewrite -card_quotient ?divgS ?(subset_trans _ nZR) // cardWZ. 
have pabW : p.-abelem W.
  rewrite (abelem_Ohm1 (pgroupS (ucn_sub 2 _) pR)) /=.
  exact: card_p2group_abelian cardW.
have cardRT : #| R / T | = p.
  have cW : logn p #| W | <= 2 by rewrite cardW (pfactorK _ p_pr).
  have := logn_quotient_cent_abelem nWR pabW cW.
  rewrite -card_quotient  ?normsI ?normG ?norms_cent //.
  have pQ : p.-group (R/'C_R(W)) := quotient_pgroup _ pR.
  case: (eqsVneq (R/T) 1) => [defRT | ntQ].
    admit.
  have [_ _ [n ->]] := pgroup_pdiv pQ ntQ.
  by rewrite (pfactorK _ p_pr); case n.
have idxRT :  #| R : T | = p.
  by rewrite -card_quotient //= normsI ?(subset_trans _ (cent_norm _)) ?normG.
have charTR : T \char R.
  by rewrite subcent_char ?char_refl //= (char_trans (Ohm_char 1 _)) ?ucn_char.
have sET : ~~ (E \subset T).
  case: subsetP => //.
  admit.
rewrite idxRT five1b; split => //.
by rewrite (pnElemE _ _ p_pr) inE cardW eqxx inE pabW sWR.
Qed.

End Five.
