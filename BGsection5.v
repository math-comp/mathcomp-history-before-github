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
Lemma p_rank_3_maxElem_2_Ohm_ucn : 
    p.-narrow R ->
  [/\ (forall H, H \subset T -> ~~ (H \in 'E_p^2(R) :&: 'E*_p(R))), 
      #| Z | = p, [group of W] \in 'E_p^2(R),
      T \char R & #| R : T | = p ].
Proof.
move=> [E e2E meE]; case/pmaxElemP: (meE); case/pElemP=> sER abeE maxE.
case/pnElemP: (e2E) => _ _; rewrite -(rank_abelem abeE) => rE.
have pZ := (pgroupS (center_sub _) pR).
have cE : #|E| = (p^2)%N.
  case: (pgroup_pdiv (pgroupS sER pR)) => [|[_ _ [r cE]]].
    by case: eqP rE => // ->; rewrite rank1.
  by move: rE; rewrite (rank_abelem abeE) cE => <-; rewrite pfactorK.
have nZR : R \subset 'N(Z).
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (center_char R)).
have pW : p.-groupW := pgroupS sWR pR.
have sZE : Z \subset E by rewrite -(Ohm_cent meE pR) OhmS // setIS // centS.
have rCRE : 'r('C_R(E)%G) = 2 by rewrite -rank_Ohm1 (Ohm_cent meE pR) rE.
have cZ : #| Z | = p. 
  case: (pgroup_pdiv pOZ ntZ)=> _ _ [q]; case:q=> //= q; rewrite -/Z => cZ.
  suff defR: 'C_R(E) = R by move: rR; rewrite -rCRE /= defR ltnn.
  suff sEZ : E \subset 'Z(R).
    apply/eqP; rewrite eqEsubset subsetIl /= subsetI subxx.
    by rewrite centsC (subset_trans sEZ) // subsetIr.
  rewrite (eqP (_: E :==: Z)) ?Ohm_sub // eq_sym eqEcard sZE cE cZ.
  by rewrite leq_pexp2l ?prime_gt0.
have ncR : ~~ cyclic R.
  rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt -(rank_pgroup pR) //=.
  by rewrite (leq_trans _ rR).
case: (Ohm1_odd_ucn2 pR oddR ncR); rewrite -/W => ncW expW.
have sWp1 : W \subset [set x | x ^+ (p ^ 1) == 1].
  by apply/subsetP=> x Wx; rewrite inE (exponentP expW).
have sWRZ : [~: W, R] \subset Z.
  rewrite [Z](OhmE 1 pZ) sub_gen // setIdE subsetI.
  rewrite /= -ucn1 (subset_trans (commSg _ (Ohm_sub _ _))) ?ucn_comm //=.
  by rewrite (subset_trans (_ : _ \subset W)) ?commg_subl.
have pZW : Z \proper W.
  rewrite properEneq OhmS /= -?ucn1 ?ucn_subS 1?andbC //=; move: ncW.
  rewrite (odd_pgroup_rank1_cyclic pW (oddSg sWR _)) //= -ltnNge -/W. 
  by case: eqP => //= <-; rewrite (p_rank_abelem abeZ) cZ logn_prime ?eqxx.
have core_lemma : forall H, H \in 'E_p^2(R) :&: 'E*_p(R) -> 'C_W(H) = Z.
  move=> H; case/setIP=> e2H meH; case/pnElemP: e2H => sHR abeH clH.
  case/pmaxElemP: (meH) => eH maxH; have pH := (abelem_pgroup abeH).
  have cH : #|H| = (p^2)%N by rewrite -clH -p_part (part_pnat_id pH).
  have pZH : Z \proper H.
    rewrite properEcard cZ cH -{1}(expn1 p) ltn_exp2l ?prime_gt1 //.
    rewrite -(_:H <*> Z = H) ?mulgen_subr //.
    rewrite maxH // ?inE ?mulgen_subG ?sHR ?sZR ?mulgen_subl //=.
    rewrite (cprod_abelem p (cprodEgen _)) ?abeH ?abeZ //= -/Z.
    by rewrite (centSS sHR (Ohm_sub _ _)) // centsC subsetIr.
  case: (eqsVneq H 'C_W(H)) => [defCHW | CHWnH].
    have sHRH : [~: H, R] \proper H.
      rewrite (sub_proper_trans _ pZH) // (subset_trans _ sWRZ) // commSg //.
      by rewrite defCHW subsetIl.
    have nHR : H <| R by rewrite /normal sHR -commg_subl (proper_sub sHRH).
    have e2H : H \in 'E_p^2(R).
      by apply/pnElemP; rewrite abeH sHR cH pfactorK.
    case: (p_rank_3_normal_abelem_SCN e2H nHR) => B scn3B sEB.
    case/setIdP: scn3B=> scnB rankB; case/SCN_P: (scnB) => nBR CB.
    suff rb :'r(B) = 2 by rewrite rb in rankB. 
    rewrite (rank_pgroup (pgroupS _ pR)); last by rewrite -CB subIset ?subxx.
    have sHOB : H \subset 'Ohm_1(B) by rewrite -(Ohm1_id abeH) OhmS.
    rewrite -p_rank_Ohm1 (maxH _ _ sHOB) ?(p_rank_abelem abeH) // inE.
    rewrite Ohm1_abelem ?(pgroupS (normal_sub nBR) pR) ?(SCN_abelian scnB) //.
    by rewrite (subset_trans (Ohm_sub _ _) (normal_sub nBR)).
  have pCWHH : 'C_W(H) \proper H. (* this proof stinks *)
    rewrite properEneq eq_sym CHWnH.
    have expCWE := exponentP (dvdn_trans (exponentS (subsetIl _ 'C(H))) expW).
    apply/subsetP=> z zC; have abeHz : (H <*> <[z]>)%G \in 'E_p(R).
      rewrite inE mulgen_subG sHR cycle_subG (subsetP _ _ zC) ?subIset ?sWR //.
      rewrite (cprod_abelem p (cprodEgen _)); last first.
        by rewrite centsC cycle_subG; case/setIP: zC.
      by rewrite abeH cycle_abelem 1?orbC ?p_pr// order_dvdn (expCWE _ zC) eqxx.
    by rewrite -(maxH _ abeHz) ?mulgen_subl -?cycle_subG ?mulgen_subr.
  have sZCWH : Z \subset 'C_W(H).
    rewrite subsetI (proper_sub _) //= (subset_trans (Ohm_sub 1 _)) //=.
    by rewrite (subset_trans _ (centS sHR)) // subsetIr.
  have ntCH : 'C_W(H) :!=: 1.
    apply/negP=> abs; move: sZCWH; rewrite (eqP abs) subG1 /= -/Z => trivZ.
    by case/negP: ntZ.
  have [_ _ [s cCWH]] := pgroup_pdiv (pgroupS (subsetIl _ _) pW) ntCH.
  apply/eqP; rewrite eq_sym eqEcard /= sZCWH; move: (proper_card pCWHH).
  by rewrite cCWH cZ cH; case s => //= m; rewrite ltn_exp2l ?prime_gt1.
have defCWE : 'C_W(E) = Z by rewrite core_lemma // inE e2E meE.
have WCWEgt0 : 1 < #| W / 'C_W(E) |.
  rewrite defCWE (_:1%N = #| Z / Z |); last first.
    by apply/eqP; rewrite eq_sym trivg_quotient -trivg_card1 eqxx.
  apply: proper_card; rewrite quotient_proper // /normal proper_sub //= -/Z.
  by rewrite (subset_trans _ nZR).
have cWZ : #| W / Z | = p.
  have pEWE: [~: E, W] \proper E.
    have pZE : Z \proper E.
      by rewrite properEcard sZE cZ cE -(expn1 p) ltn_exp2l ?prime_gt1.
    by rewrite (sub_proper_trans (subset_trans _ sWRZ) pZE) 1?commGC ?commgS.
  have nEW : W \subset 'N(E). 
    by move: pEWE; rewrite properEneq -commg_subl; case/andP.
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
have idxT : #|R : T| = p by rewrite -card_quotient ?cZ.
have e2W : [group of W] \in 'E_p^2(R).
  by rewrite (pnElemE _ _ p_pr) inE cW eqxx inE abeW sWR.
split=> // H sHT; apply/negP; move/(core_lemma _) => defCWH.
move: (sHT); apply/negP; have:= proper_subn pZW.
by rewrite -defCWH !subsetI subxx (subset_trans sHT (char_sub charTR)) centsC.
Qed.

Definition CR0R1 p G :=
    ('E_p^3(G) :=: set0) \/
    exists R0 : {group gT}, exists R1 : {group gT}, 
      [/\ R0 \x R1 = 'C_G(R0), R0 \subset G, 
          R1 \subset G, #|R0| = p & cyclic R1]. 

(* B&G 5.3(d), the rest of 5.3 is covered by 5.2 *)
Theorem odd_rank3_narrow : 
    p.-narrow R ->  
    forall S : {group gT}, #|S| = p -> S \subset R -> 'r('C_R(S)) <= 2 -> 
  [/\ cyclic 'C_T(S), S :&: R^`(1) = 1, S :&: T = 1 & 'C_R(S) = S \x 'C_T(S)].
Proof.
move=> nR; have [E] := nR; case/pnElemP=> _ _ cE pmaxE S cS sSR rS.
case: (p_rank_3_maxElem_2_Ohm_ucn nR) => nsTifE2 cZ e2W charTR idxT.
case/pmaxElemP: pmaxE; case/pElemP => sER abeE maxE.
have {cE} cE : #|E| = (p^2)%N.
  by rewrite -cE -p_part (part_pnat_id (abelem_pgroup abeE)).
have TI_SZ : S :&: Z = 1.
  rewrite prime_TIg ?cS //= -/Z.
  move: rR; apply: contraL; move/centS; move/(setIS R); move/rankS => sR0Z.
  by move: (leq_ltn_trans (leq_trans sR0Z rS) rR); rewrite /= defCRZ ltnn.
pose SZ := (S <*> [group of Z])%G.
have cZS : S \subset 'C(Z).   
  by rewrite (subset_trans sSR) // -defCRZ // subsetIr.
have nZS : S \subset 'N(Z). 
  by rewrite (subset_trans _ (cent_sub _)).
have pS : p.-group S := pgroupS sSR pR.
have aS : abelian S by rewrite (p2group_abelian pS) // cS logn_prime // eqxx.  
have cSZ : #|SZ| = (p^2)%N by rewrite /SZ /= norm_mulgenEl ?TI_cardMg ?cS ?cZ.
have abeSZ : p.-abelem SZ.
  by rewrite (cprod_abelem p (cprodEgen cZS)) abelemE// aS -{1}cS exponent_dvdn.
have rSZ : 'r(SZ) = 2 by rewrite (rank_abelem abeSZ) cSZ pfactorK.
have e2SZ : SZ \in 'E_p^2(R).
  by rewrite (pnElemE _ _ p_pr) inE cSZ eqxx inE abeSZ mulgen_subG sSR sZR.
have maxSZ : SZ \in 'E*_p(R).
  apply/pmaxElemP; split=> [|H]; first by rewrite inE mulgen_subG sSR sZR.
  case/pElemP=> // sHR aH sSZH; apply/eqP; rewrite eq_sym eqEcard sSZH /= cSZ.
  case: (eqsVneq H 1) => [->|ntH]; first by rewrite cards1 expn_gt0 prime_gt0.
  have [_ _ [[]]] := (pgroup_pdiv (abelem_pgroup aH) ntH).
    by move=>->; rewrite leq_exp2l ?prime_gt1.
  case=> [->|r cH]; first by rewrite leq_exp2l ?prime_gt1.
  suff: 'r(H) <= 2 by rewrite (rank_abelem aH) cH pfactorK.
  rewrite (leq_trans _ rS) // rankS // subsetI sHR centsC.
  exact: subset_trans (mulgen_subl _ _) (subset_trans sSZH (abelem_abelian aH)).
have nsSZT : ~~ (SZ \subset T).
  by apply/negP; move/(nsTifE2 _); rewrite inE maxSZ e2SZ.
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
have sR'T : R^`(1) \subset T.
  rewrite der1_min ?normsI ?normG  ?norms_cent //= -/T.
  by rewrite -defST quotient_mulg quotient_abelian. 
have TI_SR' : S :&: R^`(1) :=: 1.
  rewrite prime_TIg ?cS //; apply/negP=> abs; move/negP: nsSZT; apply.
  by rewrite /SZ /= norm_mulgenEl //= mul_subG // (subset_trans abs).
have defCRS : S \x 'C_T(S) = 'C_R(S).
  have TI_SCTS : S :&: 'C_T(S) == 1.
    by rewrite eqEsubset sub1G -TI_ST subsetI subsetIl 2?subIset ?subxx // orbC.
  rewrite dprodE ?(eqP TI_SCTS) //= -/T.
    apply/eqP; rewrite eqEsubset subsetI -{1}defST.
    rewrite mul_subG ?[_ \subset _]aS ?subsetIr // mulgS ?subsetIl //=.
    by rewrite group_modl ?[_ \subset _]aS //= defST subxx.
  rewrite (subset_trans _ (centI _ _)) //.
  by rewrite (subset_trans _ (mulgen_subr _ _)) // centsC subxx.
have aRT : abelian (R / T) := sub_der1_abelian sR'T.
split=> {E sER abeE maxE cE} //.
have sCTSR : 'C_T(S) \subset R by rewrite !subIset // subxx.
have rCTS : 'r_p('C_T(S)) <= 1%N.
  rewrite leqNgt; apply/negP; case/p_rank_geP=> F; rewrite /= -/T; case/pnElemP.
  move => sFCTS abeF clF; have sFR : F \subset R := (subset_trans sFCTS sCTSR).
  pose E := (S <*> [group of Z])%G.
  have sFCE : F \subset 'C(E).
    rewrite /E /= norm_mulgenEl //. 
    rewrite centM /= -/Z subsetI !(subset_trans sFCTS) ?subsetIr //.
    by rewrite subIset // (subset_trans (char_sub charTR)) // -defCRZ subsetIr.
  have sER : E \subset R by rewrite /E mulgen_subG sSR sZR.
  have abeFS : (F <*> E)%G \in 'E_p(R).
    by rewrite inE (cprod_abelem p (cprodEgen sFCE)) abeF mulgen_subG sFR sER.
  have nFE := (subset_trans sFCE (cent_sub _)).
  have nFZ : F \subset 'N(Z).
    move: (subset_trans (subsetIr R _) (cent_sub Z)); rewrite defCRZ.
    by move/(subset_trans sFR).
  have nFS : F \subset 'N(S).
    by rewrite (subset_trans sFCTS) ?(subset_trans _ (cent_sub _)) ?subsetIr.
  have rFS : 2 < 'r(F <*> E).
    case/pElemP: abeFS => _ abeFS; rewrite (rank_abelem abeFS).
    have sFSFE : F <*> S \subset F <*> E.  
      by rewrite !norm_mulgenEl // mulgS // mulgen_subl.
    rewrite (leq_trans _ (lognSg _ sFSFE)) //= norm_mulgenEl // TI_cardMg.
      by rewrite cS logn_mul // ?prime_gt0 // clF ?logn_prime ?eqxx.
    apply/eqP; rewrite -subG1 -TI_ST /= setIC setIS //. 
    by rewrite (subset_trans _ (subsetIr 'C(S) _)) // setIC.
  have eqFSE : F <*> E = E.
    case/pmaxElemP: maxSZ => _ maxE.
    by rewrite (maxE _ abeFS) // mulgen_subr.
  by move: rFS; rewrite eqFSE (rank_abelem abeSZ) cSZ pfactorK.
by rewrite (odd_pgroup_rank1_cyclic (pgroupS _ pR) (oddSg _ oddR)) //= -?rCTS.
Qed.

Lemma narrow_CR0R1 : p.-narrow R -> CR0R1 p R.
Proof.
move=> nR; move: (nR) => [E]; case/pnElemP=> sER abeE clE maxE.
have [_ cZ _ cTR _] := p_rank_3_maxElem_2_Ohm_ucn nR.
have cE : #|E| = (p^2)%N.
  by rewrite -clE -p_part (part_pnat_id (abelem_pgroup abeE)).
have sZE : Z \subset E by rewrite -(Ohm_cent maxE pR) OhmS // setIS // centS.
have pZE : Z \proper E.  
  by rewrite properEcard cE cZ sZE ltn_Pmulr ?prime_gt0 ?prime_gt1.
have [S] := splitsP (abelem_splits abeE (proper_sub pZE)).
case/complP; rewrite /= -/Z => TI_ZS defE.
have cS : #|S| = p.
  have := (prime_gt0 p_pr); have : #|Z * S| == #|E| by rewrite defE.
  by rewrite cE (TI_cardMg TI_ZS) /= cZ expnS eqn_mul2l; case/orP; move/eqP=>->.
have sSR : S \subset R by rewrite (subset_trans _ sER) // -defE mulG_subr.
have sSE : S \subset E by rewrite -defE mulG_subr.
have rCRS : 'r('C_R(S)) = 2.
  have -> : 'C_R(S) = 'C_R(E).
    apply/eqP; rewrite eq_sym eqEsubset setIS ?centS //=.
    by rewrite subsetI subsetIl /= -defE centM /= -/Z setSI // -defCRZ subsetIr.
  by rewrite -rank_Ohm1 (Ohm_cent maxE pR) (rank_abelem abeE).
case: (odd_rank3_narrow nR cS sSR (eq_leq rCRS)) => cyCTS _ _ defCTS.
right; exists S; exists [group of 'C_T(S)]; split=> //=.
by rewrite subIset // (char_sub cTR).
Qed.

(* fix it... *)
Lemma CR0R1_narrow : CR0R1 p R -> p.-narrow R.
Proof.
case. 
  by move/eqP;move/set0Pn; move: rR; rewrite (rank_pgroup pR); move/p_rank_geP.
move=> [R0] [R1 [dpCRR0]]; case/dprodP: (dpCRR0) => [_ defCRR0 sR0CR1 TI_R10].
move=> sR0R sR1R cR0 cyR1.
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
have defOCRR0 : R0 * 'Ohm_1(R1) = 'Ohm_1('C_R(R0)).
  rewrite -(Ohm_dprod 1 dpCRR0) (Ohm1_id pabR0) dprodE //.
  by rewrite (subset_trans sR0CR1) // centS // Ohm_sub.
have rCRR0le2 : 'r('C_R(R0)) <= 2.
  rewrite (rank_pgroup pCRR0). 
  have rp_cyc1: forall H, p.-group H -> cyclic H -> logn p #|'Ohm_1(H)| <= 1.
    move=> C pC; move/(cyclicS (Ohm_sub 1 _))=> cycC1.
    by rewrite -abelem_cyclic // abelem_Ohm1 ?cyclic_abelian.
  rewrite -add1n p_rank_abelian // -(dprod_card (Ohm_dprod _ dpCRR0)).
  by rewrite logn_mul ?cardG_gt0 // leq_add ?rp_cyc1 // (pgroupS _ pR).
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

Implicit Type C : {group gT}.

(* B&G 5.4 *)
Corollary narrow_CRS2 : 
    p.-narrow R -> 
  exists S : {group gT}, [/\ S \subset R , #|S| = p & 'r('C_R(S)) <= 2].
Proof.
case/narrow_CR0R1 => [| [R0] [R1] [] dpCRR0 sR0R sR1R cR0 cyR1].
  by move/eqP; case/set0Pn; apply/p_rank_geP; rewrite -rank_pgroup.
have cycR0 : cyclic R0 by rewrite prime_cyclic ?cR0.
have aCRR0 : abelian 'C_R(R0). 
  by case/dprodP: dpCRR0 => _ <- cR01 _; rewrite abelianM cR01 !cyclic_abelian.
suffices: 'r_p('C_R(R0)) <= 2.
  by exists R0; split; rewrite // (rank_pgroup (pgroupS (subsetIl _ _) pR)).
have rp_cyc1: forall C, p.-group C -> cyclic C -> logn p #|'Ohm_1(C)| <= 1.
  move=> C pC; move/(cyclicS (Ohm_sub 1 _))=> cycC1.
  by rewrite -abelem_cyclic // abelem_Ohm1 ?cyclic_abelian.
rewrite -add1n p_rank_abelian // -(dprod_card (Ohm_dprod _ dpCRR0)).
by rewrite logn_mul ?cardG_gt0 // leq_add ?rp_cyc1 // (pgroupS _ pR).
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
have nsSZ : ~~ (S \subset Z).
  apply/negP=> sSZ; move: cS (prime_gt1 p_pr) (ltnn p).
  by rewrite -(setIidPl sSZ) TI_SZ cards1 => -> ->.
have sSZCRS : SZ \subset 'C_R(S).
  rewrite mulgen_subG /= subsetI sSR [_ \subset _](abelem_abelian abeS).
  by rewrite subsetI sZR /= centsC (subset_trans sSR) // -defCRZ subsetIr.
have cZ : #|Z| = p.
  have [_ _ [[] //= r cZ]] := pgroup_pdiv pOZ  ntZ.
  move: (leq_trans (rankS sSZCRS) rCRS).
  rewrite (rank_abelem abeSZ) /SZ /= norm_mulgenEl // TI_cardMg //= -/Z.
  rewrite cS cZ logn_mul ?expn_gt0 ?(prime_gt0 p_pr) //.
  by rewrite logn_prime ?eqxx //= pfactorK.
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

End Five.

Section Five5.

Variable gT : finGroupType. 
Variables (R : {group gT}) (p : nat).
Hypotheses (pR : p.-group R) (oddR : odd #|R|).

(* B&G 5.5, for internal actions 
Theorem narrow_solvable_Aut :
  narrow p R -> forall A, solvable A -> 
  (* 'C_A(R) :=: 1 -> A \subset 'N(R) -> *) A \in Aut R ->
  odd #|A| ->
   [/\ p^'.-group (A / 'O_p(A)), abelian (A / 'O_p(A)),
       2 < 'r(R) -> forall x:gT, p^'.-elt x -> #[x] %| p.-1 &
         prime #|A| -> ~~ (#|A| %| p * (p.-1)) -> 
       (* 2 * #|A| %| p.+1 /\ 
       [~: R, A] :=: R -> ~~ (abelian R) -> #|R| = (p^3)%N *) ].
Proof.
have ntR : R :!=: 1.
  admit.
have [p_pr _ [r cR]] := pgroup_pdiv pR ntR.
have oddp : odd p.
  by case: (even_prime p_pr) oddR => // p2; rewrite cR p2 odd_exp eqn0Ngt.
case: (critical_odd _ pR)=> // H [cHR sHRZ] nc2 exH pCAu nR A solA oddA cAR1.
have ntH : H :!=: 1.
  admit.
split.
  have pcAR : p.-group 'C_A(H).
    
- admit.
- admit. 
  move=> rR.
  case/orP: (narrow_CR0R1 pR oddR rR nR). 
    by move/set0Pn; move: rR; rewrite (rank_pgroup pR); move/p_rank_geP.
  case/existsP=> R0; case/existsP=> R1; case/and5P.
  move => dpR0R1 sR0R sR1R; move/eqP=> cR0 cyR1 x p'x.
  have pR0 := pgroupS sR0R pR.
  have aR0 : abelian R0 by rewrite (p2group_abelian pR0)// cR0 logn_prime ?eqxx.
  pose U := R0 <*> 'Z(H).
  have nsR0H : ~~ (R0 \subset H).
    apply/negP=> sR0H.
    have cHZH : H \subset 'C('Z(H)).
      by rewrite centsC subsetIr.
    have nZHR0 : R0 \subset 'N('Z(H)). 
      by rewrite (subset_trans sR0H) // normsI ?norms_cent ?normsG.
    have sUH : U \subset H.
      by rewrite mulgen_subG sR0H subsetIl.
    have abeU : p.-abelem U.
      rewrite abelemE //= norm_mulgenEl //= abelianM center_abelian.
      rewrite aR0 (subset_trans sR0H cHZH).
      by rewrite -norm_mulgenEl // (dvdn_trans (exponentS sUH)) // exH.
  have rCRR0le2 : 'r('C_R(R0)) <= 2.
    admit. (* duplicate *)
  have mU : 'm(U) <= 'r('C_R(R0)).
    rewrite (grank_abelian (abelem_abelian abeU)).
    rewrite rankS //= subsetI (subset_trans _ (char_sub cHR)) //.
    by rewrite norm_mulgenEl // mul_subG // centsC (subset_trans sR0H).
  have sUR : U \subset R.
    rewrite /U norm_mulgenEl // mul_subG // (subset_trans _ (char_sub cHR)) //.
    by rewrite center_sub.
  move: (leq_trans mU rCRR0le2); rewrite leq_eqVlt; case/orP.
    move/eqP=> mU2.
    have ep2U : [group of U] \in 'E_p^2(R).
      rewrite pnElemE // !inE /= sUR abeU; move: mU2.
      rewrite (grank_abelian (abelem_abelian abeU)) (rank_abelem abeU)=> <-.
      by rewrite -p_part (part_pnat_id (pgroupS sUR pR)) eqxx.
    have nUH : H \subset 'N(U).
      rewrite -commg_subr /= -/U.
      rewrite (subset_trans (commgS _ (subset_trans sUH (char_sub cHR)))) //.
      by rewrite (subset_trans _ (subset_trans sHRZ (mulgen_subr _ _))).
    have nUR : U <| R.
      apply: char_normal_trans _  (char_normal cHR); rewrite charMgen ?center_char //.
      apply/charP; split => // f injf fH.
      (* [u,r] < [h,r] < u *)

      admit.
    case: (p_rank_3_normal_abelem_SCN pR oddR rR ep2U nUR) => F SCN_F sUF.
    suff: 2 < 'r('C_R(R0)) by move/(leq_ltn_trans rCRR0le2); rewrite ltnn.
    have sCR0CU : 'C_R(U) \subset 'C_R(R0).
      by rewrite setIS // centS // mulgen_subl.
    rewrite (leq_trans _ (rankS sCR0CU)) //=. 
    move: SCN_F; rewrite inE; case/andP; case/SCN_P=> sFR defF lt2.
    rewrite (leq_trans lt2) //.
    by rewrite rankS // -defF // setIS // centS.
  admit.
- admit.
admit.
Qed.*)

End Five5. 