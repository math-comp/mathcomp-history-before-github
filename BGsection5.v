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
have [p_pr pdvR [r oRpr]] := pgroup_pdiv pR ntR;  have pgt1 := prime_gt1 p_pr.
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
    apply/eqP; rewrite eq_sym eqEcard mulgen_subl -(part_pnat_id pE).
    by rewrite -(part_pnat_id pBs) !p_part cardE leq_exp2l.
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
    apply/eqP; rewrite eqEcard sCE -{1}(part_pnat_id pE) p_part cardE.
    by rewrite -(part_pnat_id (pgroupS (subsetIl _ _) pB)) p_part leq_exp2l.
  have abs1 : E \proper B.
    rewrite -defE' properEcard subIset ?subxx //= defE' -(part_pnat_id pE).
    by rewrite -(part_pnat_id pB) !p_part ltn_exp2l ?cardE ?cardB.
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

Variable R : {group gT}.
Let Z := 'Ohm_1('Z(R)).
Let W := 'Ohm_1('Z_2(R)).
Let T := 'C_R(W).

(* B&G 5.2 *)
Lemma p_rank_3_maxElem_2_Ohm_ucn : forall E p,
    odd #|R| -> p.-group(R) -> 2 < 'r(R) -> E \in 'E*_p(R) -> 'r(E) = 2 ->
  [/\ ~~ (E \subset T), 
      #| Z | = p, [group of W] \in 'E_p^2(R),
      T \char R & #| R : T | = p ].
Proof.
move=> E p oddR pR rR maE rE; case/pmaxElemP:(maE); case/pElemP=> sER abeE maxE.
have [|[p_pr _ [r cR]]] := pgroup_pdiv pR. 
  by case: eqP rR => // ->; rewrite rank1.
have [|[_ _ [t cE]]] := pgroup_pdiv (pgroupS sER pR).
  by case: eqP rE => // ->; rewrite rank1.
have {t cE} cE : #|E| = (p^2)%N.
  by move: rE; rewrite (rank_abelem abeE) cE => <-; rewrite pfactorK.
have pZ := (pgroupS (center_sub _) pR); have aZ := center_abelian R.
have nZR : R \subset 'N(Z).
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (center_char R)).
have nWR : R \subset 'N(W). 
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (ucn_char 2 R)) .
have cZE : E \subset 'C(Z).
  by rewrite (centSS sER (Ohm_sub _ _)) // centsC subsetIr.
have sZR : Z \subset R := subset_trans (char_sub (Ohm_char 1 _)) (center_sub _).
have abeZ : p.-abelem (Z) by rewrite (Ohm1_abelem pZ).
have sWR : W \subset R := (subset_trans (Ohm_sub 1 _) (ucn_sub _ _)).
have pW : p.-groupW := pgroupS sWR pR.
have abeEZ : p.-abelem (E <*> Z).
  by rewrite (cprod_abelem p (cprodEgen cZE)) ?abeE ?abeZ.
have defE : E <*> Z = E.
  by rewrite maxE ?mulgen_subl //; rewrite inE abeEZ mulgen_subG sER sZR.
have sZE : Z \subset E by rewrite -defE mulgen_subr.
have rCRE : 'r('C_R(E)%G) = 2.
  by rewrite -rank_Ohm1 (Ohm_cent maE pR) rE.
have pZZ : p.-group Z.
  by rewrite (pgroupS _ pR) //= (subset_trans (Ohm_sub 1 _) (center_sub _)).
have cZ : #| Z | = p.
  have ntZ : Z != 1.
    case: eqP (nil_TI_Z (pgroup_nil pR) (normal_refl R)) rR => // defZ R1.
    by rewrite R1 ?rank1 // TI_Ohm1 // -/Z defZ (setIidPr (sub1G _)).
  case: (pgroup_pdiv pZZ ntZ)=> _ _ [q]; case:q=> //= q; rewrite -/Z => cZ.
  suff defR: 'C_R(E) = R by move: rR; rewrite -rCRE /= defR ltnn.
  suff sEZ : E \subset 'Z(R).
    apply/eqP; rewrite eqEsubset subsetIl /= subsetI subxx.
    by rewrite centsC (subset_trans sEZ) // subsetIr.
  rewrite (eqP (_: E :==: Z)) ?Ohm_sub // eq_sym eqEcard sZE cE cZ.
  by rewrite leq_pexp2l ?prime_gt0.
have pZE : Z \proper E.
  by rewrite properEcard sZE cZ cE -(expn1 p) ltn_exp2l ?prime_gt1.
have ncR : ~~ cyclic R.
  rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt -(rank_pgroup pR) //=.
  by rewrite (leq_trans _ rR).
case: (Ohm1_odd_ucn2 pR oddR ncR); rewrite -/W => ncW expW.
have sWp1 : W \subset [set x | x ^+ (p ^ 1) == 1].
  by apply/subsetP=> x Wx; rewrite inE (exponentP expW).
have pZW : Z \proper W.
  rewrite properEneq OhmS /= -?ucn1 ?ucn_subS 1?andbC //=; move: ncW.
  rewrite (odd_pgroup_rank1_cyclic pW (oddSg sWR _)) //= -ltnNge -/W. 
  by case: eqP => //= <-; rewrite (p_rank_abelem abeZ) cZ logn_prime ?eqxx.
have sWRZ : [~: W, R] \subset Z.
  rewrite [Z](OhmE 1 pZ) sub_gen // setIdE subsetI.
  rewrite /= -ucn1 (subset_trans (commSg _ (Ohm_sub _ _))) ?ucn_comm //=.
  by rewrite (subset_trans (_ : _ \subset W)) ?commg_subl.
have pEWE: [~: E, W] \proper E.
  by rewrite (sub_proper_trans (subset_trans _ sWRZ) pZE) 1?commGC ?commgS.
have nEW : W \subset 'N(E). 
  by move: pEWE; rewrite properEneq -commg_subl; case/andP.
have sCWEE : 'C_W(E) \subset E.  
  have expCWE := exponentP (dvdn_trans (exponentS (subsetIl _ 'C(E))) expW).
  apply/subsetP=> z zC; have abeEz : (E <*> <[z]>)%G \in 'E_p(R).
    rewrite inE /= mulgen_subG sER cycle_subG (subsetP _ _ zC) ?subIset ?sWR //.
    rewrite (cprod_abelem p (cprodEgen _)); last first.
      by rewrite centsC cycle_subG; case/setIP: zC.
    by rewrite abeE cycle_abelem 1?orbC ?p_pr // order_dvdn (expCWE _ zC) eqxx.
  by rewrite -(maxE _ abeEz) ?mulgen_subl -?cycle_subG ?mulgen_subr.
have sZCWE : Z \subset 'C_W(E).
  rewrite subsetI (proper_sub _) //= (subset_trans (Ohm_sub 1 _)) //=.
  by rewrite (subset_trans _ (centS sER)) // subsetIr.
case: (eqsVneq E 'C_W(E)) => [defCEW | CEWnE].
  have sCERE : [~: E, R] \proper E.
    rewrite (sub_proper_trans _ pZE) // (subset_trans _ sWRZ) // commSg //.
    by rewrite defCEW subsetIl.
  have nER : E <| R by rewrite /normal sER -commg_subl (proper_sub sCERE).
  have Ep2E : E \in 'E_p^2(R).
    by apply/pnElemP; rewrite abeE sER cE pfactorK.
  case: (p_rank_3_normal_abelem_SCN pR oddR rR Ep2E nER) => B scn3B sEB.
  case/setIdP: scn3B=> scnB rankB; case/SCN_P: scnB=> nBR CB.
  suff rb :'r(B) = 2 by rewrite rb in rankB. 
  rewrite (rank_pgroup (pgroupS _ pR)); last by rewrite -CB subIset ?subxx.
  have sEOB : E \subset 'Ohm_1(B) by rewrite -(Ohm1_id abeE) OhmS.
  have pE := (abelem_pgroup abeE).
  rewrite -p_rank_Ohm1 (maxE _ _ sEOB) -?(rank_pgroup pE) ?rE //.
  rewrite inE Ohm1_abelem ?(pgroupS (normal_sub nBR) pR) 1?andbC //=.
    exact: subset_trans (char_sub (Ohm_char 1 B)) (normal_sub nBR).
  by rewrite /abelian -{1}CB subIset // orbC subxx.
have {CEWnE sCWEE} pCWEE : 'C_W(E) \proper E.
  by rewrite properEneq eq_sym CEWnE sCWEE.
have defCWE : 'C_W(E) = Z.
  have ntCE : 'C_W(E) :!=: 1.
    apply/negP; move/eqP=> defCWE; move: sZCWE; rewrite defCWE.
    rewrite subG1 /=; move/eqP => abs; move: cZ; rewrite /Z abs cards1=> p1.
    by case/primeP: p_pr; rewrite p1 ltnn.
  have [_ _ [s cCWE]] := pgroup_pdiv (pgroupS (subsetIl _ _) pW) ntCE.
  apply/eqP; rewrite eq_sym eqEcard sZCWE /=; move: (proper_card pCWEE).
  by rewrite cCWE cZ cE; case s => // m; rewrite ltn_exp2l ?prime_gt1.
have WCWEgt0 : 1 < #| W / 'C_W(E) |.
  rewrite defCWE (_:1%N = #| Z / Z |); last first.
    by apply/eqP; rewrite eq_sym trivg_quotient -trivg_card1 eqxx.
  apply: proper_card; rewrite quotient_proper // /normal proper_sub //= -/Z.
  by rewrite (subset_trans _ nZR).
have cWZ : #| W / Z | = p.
  rewrite -defCWE; move: rE; rewrite (rank_abelem abeE) => clE.
  have ntWCWE : (W / 'C_W(E)) != 1 by rewrite -cardG_gt1.
  have pQ : p.-group (W/'C_W(E)) := quotient_pgroup _ pW.
  have := logn_quotient_cent_abelem nEW abeE (eq_leq clE).
  rewrite -card_quotient  ?normsI ?normG ?norms_cent //= -/W; move: WCWEgt0.
  have [_ _ [n ->]] := pgroup_pdiv pQ ntWCWE.
  by rewrite (pfactorK _ p_pr); case n.
have cW : #| W | = (p^2)%N.
  rewrite -(LaGrange (proper_sub pZW)) cZ /= -/W -/Z.
  by rewrite -card_quotient ?divgS ?(subset_trans _ nZR) // cWZ. 
have abeW : p.-abelem W.
  rewrite (abelem_Ohm1 (pgroupS (ucn_sub 2 _) pR)) /=.
  exact: card_p2group_abelian cW.
have nTR : R \subset 'N(T).
  by rewrite normsI ?(subset_trans _ (cent_norm _)) ?normG.
have cardRT : #| R / T | = p.
  have clW : logn p #| W | <= 2 by rewrite cW (pfactorK _ p_pr).
  have := logn_quotient_cent_abelem nWR abeW clW.
  rewrite -card_quotient  ?normsI ?normG ?norms_cent //.
  have pQ : p.-group (R/'C_R(W)) := quotient_pgroup _ pR.
  case: (eqsVneq T R) => [defR | ntRT].
    move: (proper_subn pZW); rewrite [Z](OhmE 1 pZ) sub_gen ?setIdE ?subsetI //.
    by rewrite sWp1 sWR centsC; move/setIidPl: defR => ->.
  have ntQ : R / T != 1.
    case: eqP => //; move/eqP; rewrite eqEsubset quotient_sub1 // -ntRT.
    by case/andP; rewrite eqEsubset subsetIl => ->.
  have [_ _ [n ->]] := pgroup_pdiv pQ ntQ.
  by rewrite (pfactorK _ p_pr); case n.
have charTR : T \char R.
  by rewrite subcent_char ?char_refl //= (char_trans (Ohm_char 1 _)) ?ucn_char.
have sET : ~~ (E \subset T).
  by have:= proper_subn pZW; rewrite -defCWE !subsetI subxx sER centsC.
rewrite -card_quotient ?cZ //; split => //.
by rewrite (pnElemE _ _ p_pr) inE cW eqxx inE abeW sWR.
Qed.

Definition narrow p G := 
    ('E_p^3(G) == set0) ||
    existsb R0 : {set gT}, existsb R1, 
      [&& R0 \x R1 == 'C_G(R0), R0 \subset G, R1 \subset G, #|R0| == p & cyclic R1]. 

Lemma narrow_maxp2Elem_set0 : forall p, p.-group R -> 2 < 'r(R) -> narrow p R -> 
  'E_p^2(R) :&: 'E*_p(R) != set0.
Proof.
move=> p pR rR; case/orP. 
  move/eqP; move/setP=> abs; rewrite (rank_pgroup pR) in rR. 
  by case: (p_rank_geP rR) => x; rewrite (abs x) in_set0.
case/existsP=> ?; case/existsP=>?; case/and5P; move/eqP; case/dprodP=>[[R0 R1 ->->]].
move=> defCRR0 sR0CR1 TI_R10 sR0R sR1R cR0 cyR1. 
have [|[p_pr _ [r cR]]] := pgroup_pdiv pR. 
  by case: eqP rR => // ->; rewrite rank1.
move: (p_pr); rewrite -(eqP cR0); move/prime_cyclic=> cyR0.
have pabR0 : p.-abelem R0.
  by rewrite (abelemE _ p_pr) cyclic_abelian // -(eqP cR0) exponent_dvdn.
have pabOR1 :  p.-abelem 'Ohm_1(R1).
  by rewrite Ohm1_abelem ?cyclic_abelian ?(pgroupS sR1R pR).
have aCRR0 : abelian 'C_R(R0) by rewrite -defCRR0 abelianM ?cyclic_abelian.
have pCRR0 : p.-group 'C_R(R0) := pgroupS (subsetIl _ _) pR.
have ntR0 : R0 != 1%G. 
  case: (eqVneq R0 1%G) cR0 (prime_gt1 p_pr) => // ->.
  by rewrite /= set1gE cards1; move/eqP=> <-. 
have key : R0 * 'Ohm_1(R1) = 'Ohm_1('C_R(R0)).
  rewrite (OhmEabelian (pgroupS (subsetIl _ _) pR) (abelianS (Ohm_sub _ _ ) aCRR0)) -defCRR0.
  apply/eqP; rewrite eqEsubset; apply/andP; split. (* factor *)
    apply/subsetP=> x; rewrite /= !inE; case/mulsgP => x0 x1 xR0 xR1 -> {x}.
    have ? : x1 \in R1 by exact: subsetP (Ohm_sub 1 _) _ xR1.
    rewrite mem_mulg //=.
    have peltx1 : p.-elt x1 by exact: mem_p_elt (pgroupS sR1R pR) _.
    have ? : x0 \in 'C[x1]. 
      by rewrite (subsetP _ _ xR0) // (subset_trans sR0CR1) -?cent_set1 ?centS ?sub1set.
    rewrite expMgn; last by apply/cent1P.
    case/(abelemP p_pr): pabR0 => _ -> //; case/(abelemP p_pr): pabOR1 => _ -> //.
    by rewrite mulg1 eqxx.
  apply/subsetP=> x; rewrite /= !inE expn1; case/andP; case/mulsgP=> x0 x1 xR0 xR1 -> xp1 {x}.
  rewrite mem_mulg // mem_gen // inE xR1.
  have peltx1 : p.-elt x1 by exact: (mem_p_elt (pgroupS sR1R pR) xR1).
  have ? : x0 \in 'C[x1]. 
    by rewrite (subsetP _ _ xR0) // (subset_trans sR0CR1) -?cent_set1 ?centS ?sub1set.
  case: (eqVneq x1 1) => [->|ntx1]; rewrite ?exp1gn ?eqxx //=.
  have def_pdivx1 : pdiv #[x1] = p by rewrite (pdiv_p_elt peltx1 ntx1) ?exp1gn ?mul1g.
  move: xp1; rewrite expMgn; last by apply/cent1P.
  case: (eqVneq x0 1) => [->|]; first by rewrite def_pdivx1 exp1gn mul1g.
  move => ntx0; rewrite -eq_invg_mul -expVgn def_pdivx1; move/eqP=> <-; rewrite -order_dvdn.
  by case/cyclicP: cyR0 cR0 xR0 => b ->; move/eqP=> <-; move/groupVr=> x0b; apply: order_dvdG. 
have TI_R0OR1 : R0 :&: 'Ohm_1(R1) = 1.
  by apply/eqP; rewrite eqEsubset sub1G -TI_R10 setISS ?subxx ?Ohm_sub.
have rCRR0 : 'r('C_R(R0)) < 'r(R).
  rewrite (leq_ltn_trans _ rR) // (rank_pgroup pCRR0).
  case: (eqsVneq R1 1)=> [defR1|ntR1].
    rewrite -defCRR0 defR1 mulGSid ?sub1G // p_rank_abelian ?cyclic_abelian //.
    by rewrite (Ohm1_id pabR0) (eqP cR0) logn_prime // ?eqxx.
  have sOR1NR0 : 'Ohm_1(R1)\subset 'N(R0).
    by rewrite (subset_trans (Ohm_sub 1 _)) ?(subset_trans _ (cent_sub _)) 1?centsC.
  have {ntR1} cOR1 : #|'Ohm_1(R1)| = p.
    by rewrite (Ohm1_cyclic_pgroup_prime cyR1 (pgroupS sR1R pR)).
  have {cOR1 TI_R0OR1} lgCRR0 : logn p #|R0 <*> 'Ohm_1(R1)| <= 2.
    by rewrite norm_mulgenEr // (TI_cardMg TI_R0OR1) (eqP cR0) cOR1 (@pfactorK _ 2).
  rewrite p_rank_abelian // (leq_trans _ lgCRR0) // lognSg //= {lgCRR0} norm_mulgenEr //. 
  by rewrite key subxx.
have nsR0Z : ~~ (R0 \subset Z).
  apply/negP; move/centS; move/(setIS R); move/rankS => sR0Z.
  move: (leq_ltn_trans sR0Z rCRR0); rewrite /= (_:'C_R(Z) = R) ?ltnn //; apply/eqP.
  rewrite eqEsubset subsetIl subsetI subxx /Z (subset_trans _ (centS (Ohm_sub 1 _))) //=.
  by rewrite centsC subsetIr.
have TI_R0Z : R0 :&: Z = 1 by rewrite prime_TIg //= (eqP cR0).
have pR0CRR0 : R0 \proper 'C_R(R0).
  rewrite (proper_sub_trans _ (_:R0 * Z \subset _)) -?defCRR0 ?mulgS //.
  rewrite properEneq mulG_subl andbC; apply/negP; move/eqP=> defR0.
  move: TI_R0Z; rewrite defR0.
    admit. (* Z != 1 missing *)
  admit. (* mhhhmm....*)
have ntR1 : R1 :!=: 1.
  move: pR0CRR0; rewrite -defCRR0; case: (eqVneq R1 1%G) => [->| //].
  by rewrite mulg1 properE !subxx andbC. 
pose E := 'Ohm_1('C_R(R0))%G.
have defE : R0 \x 'Ohm_1(R1) = E by rewrite dprodE // ?(centsS (Ohm_sub 1 _)). (* useless *)
have pabE : p.-abelem E by rewrite Ohm1_abelem.
apply/set0Pn; exists E; rewrite in_setI (eqP cR0).
rewrite (pnElemE _ _ p_pr) !inE (subset_trans (Ohm_sub _ _)) ?pabE ?subsetIl //=.
admit.
Qed.

(*
Lemma foo : forall p, odd #|R| -> p.-group(R) -> 2 < 'r(R) ->
  'E_p^2(R) :&: 'E*_p(R) != set0 ->
  [/\ (forall H, H \subset T -> ~~ (H \in 'E_p^2(R) :&: 'E*_p(R))),
      #|Z| = p /\ [group of W] \in 'E_p^2(R),
      T \char R /\ #|R : T| = p &
      forall (S : {group gT}), #|S| = p -> S \subset R ->
        'r('C_R(S)) <= 2 -> 
          [/\ cyclic 'C_T(S), S :&: R^`(1) = 1, S :&: T = 1 &
              'C_R(S) = S \x 'C_T(S)]].
Proof.
move=> p oddR pR rRgt2 nR.

Qed.
*)

End Five.
