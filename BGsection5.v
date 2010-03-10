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

Implicit Types G H K E: {group gT}.

Definition narrow p G := exists2 E, E \in 'E_p^2(G) & E \in 'E*_p(G).

Notation "p .-narrow" := (narrow p)
  (at level 2, format "p .-narrow") : group_scope.

Variables (R : {group gT}) (p : nat).
Hypotheses (pR : p.-group R) (oddR : odd #|R|) (rR : 2 < 'r(R)).

Let ntR : R != 1%G. Proof. by case: eqP rR => // ->; rewrite rank1. Qed.
Let p_pr : prime p. Proof. by case: (pgroup_pdiv pR ntR). Qed.

(* B&G 5.1(a) *)
Lemma p_rank_3_SCN : exists A, A \in 'SCN_3(R).
Proof.
by apply/set0Pn; rewrite -(rank2_SCN3_empty pR oddR) leqNgt rR.
Qed.

(* B&G 5.1(b) *)
Lemma p_rank_3_normal_abelem_SCN : forall E, 
  E \in 'E_p^2(R) -> E <| R ->
  exists2 B, B \in 'SCN_3(R) & E \subset B.
Proof.
move=> E EE nER.
have pgt1 := prime_gt1 p_pr; have pE := pgroupS (normal_sub nER) pR.
case/pnElemP: EE=> sER abeE cardE; have {nER} nER := normal_norm nER.
have [B nBR pnelemB] : exists2 B : {group gT}, B <| R & B \in 'E_p^3(R). 
  have [C] := p_rank_3_SCN.
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

Let Z := 'Ohm_1('Z(R)).
Let W := 'Ohm_1('Z_2(R)).
Let T := 'C_R(W).

Let sZR : Z \subset R. 
Proof. exact: subset_trans (char_sub (Ohm_char 1 _)) (center_sub _). Qed.

Let abeZ : p.-abelem (Z). 
Proof. by rewrite (Ohm1_abelem (pgroupS _ pR)) ?center_sub ?center_abelian. Qed.

Let sWR : W \subset R. 
Proof. exact: subset_trans (Ohm_sub 1 _) (ucn_sub _ _). Qed.

Let pOZ : p.-group Z.
Proof. exact: pgroupS (Ohm_sub 1 _) (pgroupS (center_sub _) pR). Qed.

Let defCRZ : 'C_R(Z) = R.
Proof.
apply/eqP; rewrite eqEsubset subsetIl subsetI subxx.
by rewrite /Z (subset_trans _ (centS (Ohm_sub 1 _))) //= centsC subsetIr.
Qed.

Let ntZ : Z != 1.
Proof.
case: eqP (nil_TI_Z (pgroup_nil pR) (normal_refl R)) rR => // defZ R1.
by rewrite R1 ?rank1 // TI_Ohm1 // -/Z defZ (setIidPr (sub1G _)).
Qed.

Let nWR : R \subset 'N(W). 
Proof. exact: char_norm_trans (Ohm_char 1 _) (char_norm (ucn_char 2 R)). Qed.

(* B&G 5.2 *)
Lemma p_rank_3_maxElem_2_Ohm_ucn : forall E,
    E \in 'E*_p(R) -> 'r(E) = 2 ->
  [/\ ~~ (E \subset T), 
      #| Z | = p, [group of W] \in 'E_p^2(R),
      T \char R & #| R : T | = p ].
Proof.
move=> E maE rE; case/pmaxElemP:(maE); case/pElemP=> sER abeE maxE.
have pZ := (pgroupS (center_sub _) pR).
have cE : #|E| = (p^2)%N.
  case: (pgroup_pdiv (pgroupS sER pR)) => [|[_ _ [r cE]]].
    by case: eqP rE => // ->; rewrite rank1.
  by move: rE; rewrite (rank_abelem abeE) cE => <-; rewrite pfactorK.
have nZR : R \subset 'N(Z).
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (center_char R)).
have cZE : E \subset 'C(Z).
  by rewrite (centSS sER (Ohm_sub _ _)) // centsC subsetIr.
have pW : p.-groupW := pgroupS sWR pR.
have abeEZ : p.-abelem (E <*> Z).
  by rewrite (cprod_abelem p (cprodEgen cZE)) ?abeE ?abeZ.
have defE : E <*> Z = E.
  by rewrite maxE ?mulgen_subl //; rewrite inE abeEZ mulgen_subG sER sZR.
have sZE : Z \subset E by rewrite -defE mulgen_subr.
have rCRE : 'r('C_R(E)%G) = 2.
  by rewrite -rank_Ohm1 (Ohm_cent maE pR) rE.
have cZ : #| Z | = p. (* factor? *)
  case: (pgroup_pdiv pOZ ntZ)=> _ _ [q]; case:q=> //= q; rewrite -/Z => cZ.
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
  case: (p_rank_3_normal_abelem_SCN Ep2E nER) => B scn3B sEB.
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
have nsET : ~~ (E \subset T).
  by have:= proper_subn pZW; rewrite -defCWE !subsetI subxx sER centsC.
rewrite -card_quotient ?cZ //; split => //.
by rewrite (pnElemE _ _ p_pr) inE cW eqxx inE abeW sWR.
Qed.

Definition CR0R1 p G :=
    ('E_p^3(G) == set0) ||
    existsb R0 : {group gT}, existsb R1, 
      [&& R0 \x R1 == 'C_G(R0), R0 \subset G, 
          R1 \subset G, #|R0| == p & cyclic R1]. 

Lemma CR0R1_narrow : CR0R1 p R -> p.-narrow R.
Proof.
case/orP. 
  by move/set0Pn; move: rR; rewrite (rank_pgroup pR); move/p_rank_geP.
case/existsP => R0'; case/existsP => R1'; case/and5P; move/eqP => dpCRR0.
move: (Ohm_dprod 1 dpCRR0); case/dprodP: dpCRR0 =>[[R0 R1 -> ->/=]].
move=> defCRR0 sR0CR1 TI_R10 defOCRR0 sR0R sR1R; move/eqP=>cR0 cyR1 {R0' R1'}.
have cyR0 : cyclic R0 by rewrite prime_cyclic // cR0.
have pabR0 : p.-abelem R0.
  by rewrite (abelemE _ p_pr) cyclic_abelian // -cR0 exponent_dvdn.
have pabOR1 :  p.-abelem 'Ohm_1(R1).
  by rewrite Ohm1_abelem ?cyclic_abelian ?(pgroupS sR1R pR).
have aCRR0 : abelian 'C_R(R0) by rewrite -defCRR0 abelianM ?cyclic_abelian.
have pCRR0 : p.-group 'C_R(R0) := pgroupS (subsetIl _ _) pR.
have ntR0 : R0 != 1%G. 
  by case: eqP cR0 (@cards1 gT 1) (prime_gt1 p_pr) => // -> <- ->.
have TI_R0OR1 : R0 :&: 'Ohm_1(R1) = 1.
  by apply/eqP; rewrite eqEsubset sub1G -TI_R10 setISS ?subxx ?Ohm_sub.
have {defOCRR0} defOCRR0 : R0 * 'Ohm_1(R1) = 'Ohm_1('C_R(R0)).
  rewrite -defOCRR0 (Ohm1_id pabR0) dprodE // (subset_trans sR0CR1) // centS //.
  exact: Ohm_sub R1.
have rCRR0le2 : 'r('C_R(R0)) <= 2.
  rewrite (rank_pgroup pCRR0) /=.
  case: (eqsVneq R1 1)=> [defR1|ntR1].
    rewrite -defCRR0 defR1 mulGSid ?sub1G ?p_rank_abelian ?cyclic_abelian //.
    by rewrite (Ohm1_id pabR0) cR0 logn_prime // ?eqxx.
  have sOR1NR0 : 'Ohm_1(R1)\subset 'N(R0).
    rewrite (subset_trans (Ohm_sub 1 _)) ?(subset_trans _ (cent_sub _)) //.
    by rewrite centsC.
  have {ntR1} cOR1 : #|'Ohm_1(R1)| = p.
    by rewrite (Ohm1_cyclic_pgroup_prime cyR1 (pgroupS sR1R pR)).
  have {cOR1 TI_R0OR1} lgCRR0 : logn p #|R0 <*> 'Ohm_1(R1)| <= 2.
    by rewrite norm_mulgenEr // (TI_cardMg TI_R0OR1) cR0 cOR1 (@pfactorK _ 2).
  rewrite p_rank_abelian // (leq_trans _ lgCRR0) // lognSg ?norm_mulgenEr //.
  by rewrite /= -defOCRR0 ?norm_mulgenEr ?subxx.
have rCRR0 : 'r('C_R(R0)) < 'r(R) := leq_ltn_trans rCRR0le2  rR.
have nsR0Z : ~~ (R0 \subset Z).
  apply/negP; move/centS; move/(setIS R); move/rankS => sR0Z.
  by move: (leq_ltn_trans sR0Z rCRR0); rewrite /= defCRZ ltnn.
have TI_R0Z : R0 :&: Z = 1 by rewrite prime_TIg //= cR0.
have pR0CRR0 : R0 \proper 'C_R(R0).
  rewrite (proper_sub_trans _ (_:R0 * Z \subset _)) //; last first.
    rewrite subsetI !mul_subG ?sR0R ?sZR //; first exact: cyclic_abelian cyR0.
    by rewrite (subset_trans (Ohm_sub _ _)) // subIset //= centS ?sR0R 1?orbC.
  rewrite properEcard mulG_subl (TI_cardMg TI_R0Z) cR0 /= -/Z.
  have [_ _ [s /= ->]] := pgroup_pdiv (pgroupS sZR pR) ntZ.
  rewrite expnS ltn_Pmulr ?(prime_gt0 p_pr) ?(leq_trans (prime_gt1 p_pr)) //.
  by rewrite leq_pmulr ?expn_gt0 // (prime_gt0 p_pr).
have ntR1 : R1 :!=: 1.
  move: pR0CRR0; rewrite -defCRR0; case: (eqVneq R1 1%G) => [->| //].
  by rewrite mulg1 properE !subxx andbC. 
pose E := 'Ohm_1('C_R(R0))%G.
have pabE : p.-abelem E by rewrite Ohm1_abelem.
have EE : E \in 'E_p(R). 
  by rewrite inE ?pabE ?(subset_trans (Ohm_sub _ _)) ?subsetIl.
have cE : (#|E| = p^2)%N .
  rewrite /E /= -defOCRR0 (TI_cardMg TI_R0OR1) cR0.
  by rewrite (Ohm1_cyclic_pgroup_prime cyR1 (pgroupS sR1R pR)).
exists E; first by rewrite inE cE EE pfactorK ?p_pr ?eqxx. 
apply/pmaxElemP; rewrite inE; split; first by move: EE; rewrite inE.
move=> H EH sEH; apply/eqP; rewrite eqEsubset sEH andbC /=.
rewrite (OhmEabelian pCRR0 (abelianS (Ohm_sub _ _) aCRR0)).
apply/subsetP=>x xH; rewrite inE.
case/pElemP: EH => sHR;case/(abelemP p_pr)=> aH ->; rewrite // eqxx andbC /=.
rewrite (subsetP _ _ xH) // subsetI sHR.
rewrite centsC (subset_trans _ aH) // (subset_trans _ sEH)//.
by rewrite /E /= -defOCRR0 mulG_subl.
Qed.

Lemma narrow_CR0R1 : p.-narrow R -> CR0R1 p R.
Proof.
move=> [E]; case/pnElemP=> sER abeE cE maxE.
have rCRE : 'r('C_R(E)) = 2.
  by rewrite -rank_Ohm1 (Ohm_cent maxE pR) (rank_abelem abeE).
have {cE} cE : #|E| = (p^2)%N.
  by rewrite -cE -p_part (part_pnat_id (abelem_pgroup abeE)).
have cZE : E \subset 'C(Z).
  by rewrite (centSS sER (Ohm_sub _ _)) // centsC subsetIr.
have abeEZ : p.-abelem (E <*> Z).
  by rewrite (cprod_abelem p (cprodEgen cZE)) ?abeE ?abeZ.
have defE : E <*> Z = E.
  case/pmaxElemP: maxE => _ maxE.
  by rewrite maxE ?mulgen_subl //; rewrite inE abeEZ mulgen_subG sER sZR.
have sZE : Z \subset E by rewrite -defE mulgen_subr.
have {defE} cZ : #| Z | = p. (* 5.2? *)
  case: (pgroup_pdiv pOZ ntZ)=> _ _ [q]; case: q; rewrite //= -/Z => q cZ.
  have sEZ : E \subset 'Z(R).
    rewrite -(eqP (_: Z :==: E)) ?Ohm_sub // eqEcard sZE cZ cE.
    by rewrite leq_pexp2l ?prime_gt0.
  have defR: 'C_R(E) = R.
    apply/eqP; rewrite eqEsubset subsetIl /= subsetI subxx.
    by rewrite centsC (subset_trans sEZ) // subsetIr.
  by move: rR; rewrite -rCRE /= defR ltnn.
have pZE : Z \proper E.
  by rewrite properEcard cE cZ ltn_Pmulr ?prime_gt0 ?prime_gt1 ?sZE.
have [S] := splitsP (abelem_splits abeE (proper_sub pZE)).
case/complP; rewrite /= -/Z => TI_ZS defE.
have cS : #|S| = p.
  have := (prime_gt0 p_pr); have : #|Z * S| == #|E| by rewrite defE.
  by rewrite cE (TI_cardMg TI_ZS) /= cZ expnS eqn_mul2l; case/orP; move/eqP=>->.
have sSR : S \subset R by rewrite (subset_trans _ sER) // -defE mulG_subr.
have sSE : S \subset E by rewrite -defE mulG_subr.
case: (p_rank_3_maxElem_2_Ohm_ucn maxE)=> [|nsET _ ep2W cTR idxTR].
  by rewrite (rank_abelem abeE) // cE pfactorK.
have rCRS : 'r('C_R(S)) = 2.
  rewrite -rCRE !(@rank_pgroup _ p) ?(pgroupS (subsetIl _ _) pR) //=.
  rewrite (eqP _ : 'C_R(S) = 'C_R(E)) //.
  rewrite eq_sym eqEsubset setIS ?centS //=.
  by rewrite subsetI subsetIl /= -defE centM /= -/Z setSI // -defCRZ subsetIr.
have pS : p.-group S := pgroupS sSR pR.
have aS : abelian S by rewrite (p2group_abelian pS) // cS logn_prime // eqxx.
have TI_ST : S :&: T :=: 1.
  rewrite prime_TIg ?cS //; apply/negP=> abs. 
  move/negP: nsET; apply.
  rewrite -defE mul_subG // subsetI sZR centsC (subset_trans sWR) //.
  by rewrite /Z (subset_trans _ (centS (Ohm_sub 1 _))) //= centsC subsetIr.
have defST : S * T = R.
  apply/eqP; rewrite eqEcard TI_cardMg ?mul_subG ?subsetIl //.
  move: idxTR; rewrite -cS /= -/T mulnC => <-.
  by rewrite LaGrange ?leqnn ?subsetIl. 
have defCRS : S \x 'C_T(S) == 'C_R(S).
  rewrite dprodE /= -/T. (* duplicate with 5.3 *)
    rewrite eqEsubset group_modl ?[_ \subset _]aS //= subsetI.
    by rewrite subsetIr defST subsetIl subxx.
    by rewrite centsC subIset 1?orbC ?subxx.
  suff nsSCTS : ~~ (S \subset 'C_T(S)) by rewrite (prime_TIg _ nsSCTS) ?cS.
  apply/negP=> abs.
  move: (subset_trans abs (subsetIl _ _)) => sST.
  have : S :&: T \subset 1%G by rewrite TI_ST subxx.
  rewrite (setIidPl sST) => sS1.
  have defS : S :==: 1 by rewrite eqEsubset sub1G sS1.
  move: cS (prime_gt1 p_pr); rewrite (eqP defS); rewrite cards1 => ->.
  by rewrite ltnn.
have cyCTS : cyclic 'C_T(S). (* duplicate with 5.3 *)
  have sCTSR : 'C_T(S) \subset R by rewrite !subIset // subxx.
  have rCTS : 'r_p('C_T(S)) <= 1%N.
    rewrite leqNgt; apply/negP => abs.
    case/p_rank_geP: abs=> F; rewrite /= -/T; case/pnElemP => sFCTS abeF clF.
    have sFR : F \subset R by rewrite (subset_trans sFCTS).
    have sFCE : F \subset 'C(E). 
      rewrite -defE centM /= -/Z subsetI !(subset_trans sFCTS) ?subsetIr //.
      by rewrite (subset_trans _ (@subsetIr _ R _)) // defCRZ subIset // (char_sub cTR).
    have abeFS : (F <*> E)%G \in 'E_p(R).
      by rewrite inE /= (cprod_abelem p (cprodEgen sFCE)) abeE abeF mulgen_subG sFR sER.
    have nFE := (subset_trans sFCE (cent_sub _)).
    have nFZ : F \subset 'N(Z).
      by rewrite (subset_trans _ (cent_sub _)) // (subset_trans _ (subsetIr R _)) // defCRZ. 
    have nFS : F \subset 'N(S).
      by rewrite (subset_trans sFCTS) // (subset_trans _ (cent_sub _)) // subsetIr.
    have rFS : 2 < 'r(F <*> E).
      case/pElemP: abeFS => _ abeFS; rewrite (rank_abelem abeFS).
      have sFSFE : F <*> S \subset F <*> E.
        by rewrite !norm_mulgenEl // mulgS. 
      rewrite (leq_trans _ (lognSg _ sFSFE)) //= norm_mulgenEl // TI_cardMg.
        by rewrite cS logn_mul // ?prime_gt0 // clF ?logn_prime ?eqxx.
      apply/eqP; rewrite -subG1 -TI_ST /= setIC setIS //. 
      by rewrite (subset_trans _ (subsetIr 'C(S) _)) // setIC.
    have eqFSE : F <*> E = E.
      by case/pmaxElemP: maxE => _ maxE; rewrite (maxE _ abeFS) // mulgen_subr.
    by move: rFS; rewrite eqFSE (rank_abelem abeE) cE pfactorK //.
  by rewrite (odd_pgroup_rank1_cyclic (pgroupS _ pR) (oddSg _ oddR)) //= -?rCTS.
apply/orP; right; apply/existsP; exists S; apply/existsP; exists 'C_T(S).
by rewrite cS cyCTS defCRS sSR !subIset ?subxx ?eqxx.
Qed.

(* B&G 5.3 *)
Theorem odd_rank3_narrow : 
    p.-narrow R ->
  [/\ (forall H, H \subset T -> ~~ (H \in 'E_p^2(R) :&: 'E*_p(R))),
      #|Z| = p /\ [group of W] \in 'E_p^2(R),
      T \char R /\ #|R : T| = p &
      forall (S : {group gT}), #|S| = p -> S \subset R ->
        'r('C_R(S)) <= 2 -> 
          [/\ cyclic 'C_T(S), S :&: R^`(1) = 1, S :&: T = 1 &
              'C_R(S) = S \x 'C_T(S)]].
Proof.
move=> nR; have [E pab2E pmaxE] := nR.
have rE : 'r(E) = 2.
  by case/pnElemP: pab2E=> _ pabE rE; rewrite (rank_abelem pabE).
case: (p_rank_3_maxElem_2_Ohm_ucn pmaxE rE)=> nsET cZ e2W charT idxT.
clear pab2E rE pmaxE nsET E. (* ... *)
rewrite charT idxT e2W cZ; split=> // [H sHT|S cS sSR rS].
  apply/negP; case/setIP=> e2H maxH.
  have rH : 'r(H) = 2 by case/pnElemP: e2H=> _ pabH; rewrite (rank_abelem pabH).
  case: (p_rank_3_maxElem_2_Ohm_ucn maxH rH)=> nsHT *.
  by move/negP: nsHT; apply.
have TI_SZ : S :&: Z = 1.
  rewrite prime_TIg ?cS //= -/Z.
  apply/negP; move/centS; move/(setIS R); move/rankS => sR0Z.
  by move: (leq_ltn_trans (leq_trans sR0Z rS) rR); rewrite /= defCRZ ltnn.
pose SZ := (S <*> [group of Z])%G.
have cZS : S \subset 'C(Z).   
  by rewrite (subset_trans sSR) // -defCRZ // subsetIr.
have nZS : S \subset 'N(Z). 
  by rewrite (subset_trans _ (cent_sub _)).
have pS : p.-group S := pgroupS sSR pR.
have cSZ : #|SZ| = (p^2)%N.
  by rewrite /SZ /= norm_mulgenEl //= TI_cardMg //= cS cZ.
have e2SZ : SZ \in 'E_p^2(R).
  rewrite (pnElemE _ _ p_pr) inE cSZ.
  rewrite eqxx andbC /= inE /SZ /= norm_mulgenEl // mul_subG //=.
  rewrite -norm_mulgenEl // (cprod_abelem p (cprodEgen cZS)) /= abeZ /abelem.
  rewrite pS (p2group_abelian pS) ?cS ?logn_prime ?eqxx // andbC /=.
  by rewrite -cS exponent_dvdn.
have rSZ : 'r(SZ) = 2.
  move:e2SZ; rewrite inE; case/andP; case/pElemP=>_ abeSZ. 
  by rewrite -rank_abelem //; move/eqP=> <-.
have peSZ : SZ \in 'E_p(R) by apply/pElemP; split; case/pnElemP: e2SZ.
have maxSZ : SZ \in 'E*_p(R).
  apply/pmaxElemP; rewrite inE; split; first by move: peSZ; rewrite inE.
  move=> H EH sEH; apply/eqP; rewrite eq_sym eqEcard sEH /= cSZ.
   case/pElemP: EH => // sHR abeH.
  have sHCRS: H \subset 'C_R(S).
    rewrite subsetI sHR centsC.
    rewrite (subset_trans (mulgen_subl _ Z)) // (subset_trans sEH) //.
    exact: abelem_abelian abeH.
  case: (eqsVneq H 1) => [->|ntH]; first by rewrite cards1 expn_gt0 prime_gt0.
  have [_ _ [[]]] := (pgroup_pdiv (abelem_pgroup abeH) ntH).
    by move=>->; rewrite leq_exp2l ?prime_gt1.
  case; first by move=>->; rewrite leq_exp2l ?prime_gt1.
  move=> r cH; move: (leq_trans (rankS sHCRS) rS).
  by rewrite (rank_abelem abeH) cH pfactorK.
have nsSZT : ~~ (SZ \subset T).
  by case: (p_rank_3_maxElem_2_Ohm_ucn maxSZ rSZ).
have sZT : Z \subset T.
  rewrite subsetI sZR centsC (subset_trans _ (subsetIr R _)) // defCRZ.
  exact: (subset_trans (Ohm_sub 1 _) (ucn_sub _ _)).
have TI_ST : S :&: T :=: 1.
  rewrite prime_TIg ?cS //; apply/negP=> abs; move/negP: nsSZT; apply.
  by rewrite /SZ /= norm_mulgenEl //= mul_subG.
have defST : S * T = R.
  apply/eqP; rewrite eqEcard TI_cardMg ?mul_subG ?subsetIl //.
  move: idxT; rewrite -cS /= -/T mulnC => <-.
  by rewrite LaGrange ?leqnn ?subsetIl.
have aS : abelian S by rewrite (p2group_abelian pS) // cS logn_prime // eqxx.  
have sR'T : R^`(1) \subset T.
  rewrite der1_min ?normsI ?normG  ?norms_cent //= -/T.
  by rewrite -defST quotient_mulg quotient_abelian. 
have TI_SR' : S :&: R^`(1) :=: 1.
  rewrite prime_TIg ?cS //; apply/negP=> abs; move/negP: nsSZT; apply.
  by rewrite /SZ /= norm_mulgenEl //= mul_subG // (subset_trans abs).
have defCRS : 'C_R(S) = S \x 'C_T(S).
  have TI_SCTS : S :&: 'C_T(S) == 1.
    by rewrite eqEsubset sub1G -TI_ST subsetI subsetIl 2?subIset ?subxx // orbC.
  rewrite dprodE ?(eqP TI_SCTS) //= -/T.
    apply/eqP; rewrite eq_sym eqEsubset subsetI -{1}defST.
    rewrite mul_subG ?[_ \subset _]aS ?subsetIr //.
    rewrite mulgS ?subsetIl //=.
    by rewrite group_modl ?[_ \subset _]aS //= defST subxx.
  rewrite (subset_trans _ (centI _ _)) //.
  by rewrite (subset_trans _ (mulgen_subr _ _)) // centsC subxx.
have aRT : abelian (R / T) := sub_der1_abelian sR'T.
have rCTS : 'r_p('C_T(S)) <= 1%N. (* huge duplicate with prev th *)
  rewrite leqNgt; apply/negP=> abs.
  case/p_rank_geP: abs=> F; rewrite /= -/T; case/pnElemP=> sFCTS abeF clF.
  have sCTSR : 'C_T(S) \subset R.  
    by rewrite subIset // -defST mulg_subr. 
  have sFR : F \subset R by rewrite (subset_trans sFCTS).
  have sFCE : F \subset 'C(SZ). 
    rewrite /SZ /= norm_mulgenEl //= centM /= -/Z subsetI !(subset_trans sFCTS) ?subsetIr //.
    by rewrite (subset_trans _ (@subsetIr _ R _)) // defCRZ subIset // (char_sub charT).
    have abeSZ : p.-abelem SZ by case/pElemP: peSZ.
    have sSZR : SZ \subset R by case/pElemP: peSZ.
    have abeFS : (F <*> SZ)%G \in 'E_p(R).
      by rewrite inE /= (cprod_abelem p (cprodEgen sFCE)) abeSZ abeF mulgen_subG sFR sSZR.
    have nFE := (subset_trans sFCE (cent_sub _)).
    have nFZ : F \subset 'N(Z).
      by rewrite (subset_trans _ (cent_sub _)) // (subset_trans _ (subsetIr R _)) // defCRZ. 
    have nFS : F \subset 'N(S).
      by rewrite (subset_trans sFCTS) // (subset_trans _ (cent_sub _)) // subsetIr.
    have rFS : 2 < 'r(F <*> SZ).
      case/pElemP: abeFS => _ abeFS; rewrite (rank_abelem abeFS).
      have sFSFE : F <*> S \subset F <*> SZ.
        by rewrite !norm_mulgenEl // mulgS // mulgen_subl. 
      rewrite (leq_trans _ (lognSg _ sFSFE)) //= norm_mulgenEl // TI_cardMg.
        by rewrite cS logn_mul // ?prime_gt0 // clF ?logn_prime ?eqxx.
      apply/eqP; rewrite -subG1 -TI_ST /= setIC setIS //. 
      by rewrite (subset_trans _ (subsetIr 'C(S) _)) // setIC.
    have eqFSE : F <*> SZ = SZ.
      by case/pmaxElemP: maxSZ => _ maxE; rewrite (maxE _ abeFS) // mulgen_subr.
    by move: rFS; rewrite eqFSE (rank_abelem abeSZ) cSZ pfactorK //.
have cyCTS : cyclic 'C_T(S).
  have sCTSR : 'C_T(S) \subset R by rewrite !subIset // subxx.
  by rewrite (odd_pgroup_rank1_cyclic (pgroupS _ pR) (oddSg _ oddR)) //= -?rCTS.
by split.
Qed.

(* B&G 5.4 *)
Corollary narrow_CRS2 : 
    p.-narrow R -> 
  exists S : {group gT}, [/\ S \subset R , #|S| = p & 'r('C_R(S)) <= 2].
Proof.
move/narrow_CR0R1; case/orP.
  by move/set0Pn; move: rR; rewrite (rank_pgroup pR); move/p_rank_geP.
case/existsP => R0'; case/existsP => R1'; case/and5P; move/eqP => dpCRR0.
move: (Ohm_dprod 1 dpCRR0); case/dprodP: dpCRR0 =>[[R0 R1 -> ->/=]].
move=> defCRR0 sR0CR1 TI_R10 defOCRR0 sR0R sR1R; move/eqP=>cR0 cyR1 {R0' R1'}.
have pR0 : p.-group R0 := pgroupS sR0R pR.
have aR0 : abelian R0 by rewrite (p2group_abelian pR0) // cR0 logn_prime ?eqxx. 
have aCRR0 : abelian 'C_R(R0) by rewrite -defCRR0 abelianM ?aR0 ?cyclic_abelian.
have pabR0 : p.-abelem R0 by rewrite abelemE // aR0 -cR0 exponent_dvdn.
have cyR0 : cyclic R0 by rewrite prime_cyclic // cR0. 
have TI_R0OR1 : R0 :&: 'Ohm_1(R1) = 1.
  by apply/eqP; rewrite eqEsubset sub1G -TI_R10 setISS ?subxx ?Ohm_sub.
have rCRR0le2 : 'r('C_R(R0)) <= 2.
  rewrite (rank_pgroup (pgroupS (subsetIl _ _) pR)) /=.
  case: (eqsVneq R1 1)=> [defR1|ntR1].
    rewrite -defCRR0 defR1 mulGSid ?sub1G ?p_rank_abelian ?cyclic_abelian //.
    by rewrite (Ohm1_id pabR0) cR0 logn_prime // ?eqxx.
  have sOR1NR0 : 'Ohm_1(R1)\subset 'N(R0).
    rewrite (subset_trans (Ohm_sub 1 _)) ?(subset_trans _ (cent_sub _)) //.
    by rewrite centsC.
  have {ntR1} cOR1 : #|'Ohm_1(R1)| = p.
    by rewrite (Ohm1_cyclic_pgroup_prime cyR1 (pgroupS sR1R pR)).
  have lgCRR0 : logn p #|R0 <*> 'Ohm_1(R1)| <= 2.
    by rewrite norm_mulgenEr // (TI_cardMg TI_R0OR1) cR0 cOR1 (@pfactorK _ 2).
  rewrite p_rank_abelian // (leq_trans _ lgCRR0) // lognSg ?norm_mulgenEr //=.
  have ? : R0 \subset 'C('Ohm_1(R1)).
    by rewrite (subset_trans sR0CR1) ?centS ?Ohm_sub // Ohm_sub.
  by rewrite -defOCRR0 (Ohm1_id pabR0) norm_mulgenEl ?cents_norm // dprodE. 
exists R0; split => //.
Qed.

Corollary CRS2_narrow : 
    (exists S : {group gT}, [/\ S \subset R , #|S| = p & 'r('C_R(S)) <= 2]) ->
  p.-narrow R.
Proof.
move=> [S [sSR cS rCRS]].
have TI_SZ : S :&: Z = 1.
  rewrite prime_TIg ?cS //= -/Z.
  apply/negP; move/centS; move/(setIS R); move/rankS => sR0Z.
  by move: (leq_ltn_trans (leq_trans sR0Z rCRS) rR); rewrite /= defCRZ ltnn.
pose SZ := (S <*> [group of Z])%G.
have cZS : S \subset 'C(Z).   
  by rewrite (subset_trans sSR) // -defCRZ // subsetIr.
have nZS : S \subset 'N(Z). 
  by rewrite (subset_trans _ (cent_sub _)).
have pS : p.-group S := pgroupS sSR pR.
have abeS : p.-abelem S. 
  rewrite /abelem (p2group_abelian pS) ?cS ?logn_prime // ?eqxx //.
  by rewrite pS -cS exponent_dvdn.
have abeSZ : p.-abelem SZ.
  by rewrite (cprod_abelem p (cprodEgen cZS)) /= abeZ abeS.
have peSZ : SZ \in 'E_p(R) by rewrite inE abeSZ mulgen_subG sSR sZR.
have rS : 'r(S) = 1%N by rewrite (rank_abelem abeS) cS logn_prime ?eqxx.
have cZ : #|Z| = p.
  admit.
have cSZ : #|SZ| = (p^2)%N.
  rewrite /SZ /= norm_mulgenEl // TI_cardMg //= -/Z.
  by rewrite cS cZ expnS.
have e2SZ : SZ \in 'E_p^2(R).
  by rewrite (pnElemE _ _ p_pr) inE peSZ cSZ eqxx.
have maxSZ : SZ \in 'E*_p(R).
  apply/pmaxElemP; rewrite inE; split; first by move: peSZ; rewrite inE.
  move=> H EH sEH; apply/eqP; rewrite eq_sym eqEcard sEH /= cSZ.
   case/pElemP: EH => // sHR abeH.
  have sHCRS: H \subset 'C_R(S).
    rewrite subsetI sHR centsC.
    rewrite (subset_trans (mulgen_subl _ Z)) // (subset_trans sEH) //.
    exact: abelem_abelian abeH.
  case: (eqsVneq H 1) => [->|ntH]; first by rewrite cards1 expn_gt0 prime_gt0.
  have [_ _ [[]]] := (pgroup_pdiv (abelem_pgroup abeH) ntH).
    by move=>->; rewrite leq_exp2l ?prime_gt1.
  case; first by move=>->; rewrite leq_exp2l ?prime_gt1.
  move=> r cH; move: (leq_trans (rankS sHCRS) rCRS).
  by rewrite (rank_abelem abeH) cH pfactorK.
by exists (S <*> 'Ohm_1('Z(R)))%G.
Qed.

(* B&G 5.5
Theorem narrow_solvable_Aut :
  forall A, solvable A -> odd #|A| -> A \subset Aut R ->
   [/\ p^'.-group (A / 'O_p(A)), abelian (A / 'O_p(A)),
       2 < 'r(R) -> forall x, p^'.-elt x -> #[x] %| p.-1,
       prime #|A| -> ~~ (#|A| %| .... ].
*)

End Five.