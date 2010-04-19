(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import gfunc pgroups gprod center commutators gseries nilpotent.
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
case/pnElemP: (e2E) => _ _ clE; have pZ := (pgroupS (center_sub _) pR).
have cE : #|E| = (p^2)%N.  
  by rewrite -clE -p_part (part_pnat_id (abelem_pgroup abeE)).
have nZR : R \subset 'N(Z).
  exact: char_norm_trans (Ohm_char 1 _) (char_norm (center_char R)).
have pW : p.-groupW := pgroupS sWR pR.
have sZE : Z \subset E by rewrite -(Ohm_cent meE pR) OhmS // setIS // centS.
have rCRE : 'r('C_R(E)%G) = 2.
  by rewrite -rank_Ohm1 (Ohm_cent meE pR) (rank_abelem abeE).
have cZ : #| Z | = p. 
  have [_ _ [[] //= r cZ]] := pgroup_pdiv pOZ  ntZ.
  suff defZ : Z = E by move: rR; rewrite -rCRE /= -defZ defCRZ ltnn.
  by apply/eqP; rewrite eqEcard sZE cE cZ leq_pexp2l ?prime_gt0.
have ncR : ~~ cyclic R.
  by rewrite (odd_pgroup_rank1_cyclic pR) // -(rank_pgroup pR) leqNgt ltnW.
case: (Ohm1_odd_ucn2 pR); rewrite // -/W => ncW expW.
have sWRZ : [~: W, R] \subset Z.
  move/exponentP: expW => xp1W.
  rewrite [Z](OhmE 1 pZ) sub_gen //= setIdE -ucn1 subsetI.
  rewrite (subset_trans (commSg _ (Ohm_sub _ _))) ?ucn_comm //=.
  by apply/subsetP=>x xWR; rewrite inE xp1W ?(subsetP _ _ xWR) ?commg_subl.
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
    rewrite -(_:H <*> Z = H) ?mulgen_subr // maxH ?mulgen_subl ?inE //=.
    rewrite mulgen_subG sHR sZR (cprod_abelem p (cprodEgen _)) ?abeH ?abeZ //.
    by rewrite (centSS sHR (Ohm_sub _ _)) // centsC subsetIr.
  case: (eqsVneq H 'C_W(H)) => [defCHW | CHWnH].
    have sHRH : [~: H, R] \proper H.
      rewrite (sub_proper_trans _ pZH) // (subset_trans _ sWRZ) // commSg //.
      by rewrite defCHW subsetIl.
    have nHR : H <| R by rewrite /normal sHR -commg_subl (proper_sub sHRH).
    have e2H : H \in 'E_p^2(R).
      by apply/pnElemP; rewrite abeH sHR cH pfactorK.
    case: (p_rank_3_normal_abelem_SCN e2H nHR) => B scn3B sEB.
    case/setIdP: scn3B => scnB; case/SCN_P: (scnB) => nBR CB.
    have sHOB : H \subset 'Ohm_1(B) by rewrite -(Ohm1_id abeH) OhmS.
    rewrite -rank_Ohm1 -clH -(rank_abelem abeH) (maxH _ _ sHOB) ?ltnn ?inE //.
    rewrite (subset_trans (Ohm_sub _ _)) ?Ohm1_abelem ?(pgroupS _ pR) //;
      by rewrite ?(normal_sub nBR) ?(SCN_abelian scnB).
  have pCWHH : 'C_W(H) \proper H.
    have expCWE := exponentP (dvdn_trans (exponentS (subsetIl _ 'C(H))) expW).
    rewrite properEneq eq_sym CHWnH; apply/subsetP=> z zC.
    have abeHz : (H <*> <[z]>)%G \in 'E_p(R).
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
  have nEW : W \subset 'N(E).
    by rewrite -commg_subr (subset_trans (commgS _ sER)) ?(subset_trans sWRZ).
  have ntWCWE : (W / 'C_W(E)) != 1 by rewrite -cardG_gt1.
  have pQ : p.-group (W/'C_W(E)) := quotient_pgroup _ pW.
  have := logn_quotient_cent_abelem nEW abeE (eq_leq clE).
  rewrite -defCWE -card_quotient  ?normsI ?normG ?norms_cent //= -/W.
  have [_ _ [n cQ]] := pgroup_pdiv pQ ntWCWE.
  by move: WCWEgt0; rewrite cQ (pfactorK _ p_pr); case n.
have cW : #| W | = (p^2)%N.
  rewrite -(LaGrange (proper_sub pZW)) cZ /= -/W -/Z.
  by rewrite -card_quotient ?divgS ?(subset_trans _ nZR) // cWZ. 
have abeW : p.-abelem W.
  by rewrite (abelem_Ohm1 (pgroupS _ pR)) ?(card_p2group_abelian _ cW) ?ucn_sub.
have nTR : R \subset 'N(T).
  by rewrite normsI ?(subset_trans _ (cent_norm _)) ?normG.
have cardRT : #| R / T | = p.
  have clW : logn p #| W | <= 2 by rewrite cW (pfactorK _ p_pr).
  have pQ : p.-group (R/'C_R(W)) := quotient_pgroup _ pR.
  have: logn p #|R:T| <= 1 := logn_quotient_cent_abelem nWR abeW clW. 
  rewrite -card_quotient ?normsI ?normG ?norms_cent //=.
  case: (eqsVneq T R) => [defR | ntRT].
    move: (proper_subn pZW); rewrite [Z](OhmE 1 pZ) sub_gen ?setIdE ?subsetI //.
    rewrite sWR centsC; move/setIidPl: defR => ->. 
    by apply/subsetP=> x *; rewrite inE (exponentP expW).
  have ntQ : R / T != 1.
    apply: contra ntRT => /= Q1; rewrite eqEsubset subIset ?subxx //.
    by rewrite -quotient_sub1 ?(eqP Q1) ?nTR ?subxx.
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

(* B&G 5.3(d), the rest of 5.3 is covered by 5.2 *)
Theorem odd_rank3_narrow : 
    p.-narrow R ->  
    forall S : {group gT}, #|S| = p -> S \subset R -> 'r('C_R(S)) <= 2 -> 
  [/\ cyclic 'C_T(S), S :&: R^`(1) = 1, S :&: T = 1 & 'C_R(S) = S \x 'C_T(S)].
Proof.
move=> nR; case: (nR) => E e2E meE.
case/p_rank_3_maxElem_2_Ohm_ucn: nR => nsTifE2 cZ e2W charTR idxT S cS sSR rS.
have cZS : S \subset 'C(Z) by rewrite (subset_trans sSR) // -defCRZ // subsetIr.
have nZS : S \subset 'N(Z) by rewrite (subset_trans _ (cent_sub _)).
have pS : p.-group S := pgroupS sSR pR.
have aS : abelian S by rewrite (p2group_abelian pS) // cS logn_prime // eqxx.  
pose SZ := (S <*> [group of Z])%G.
have abeSZ : p.-abelem SZ.
  by rewrite (cprod_abelem p (cprodEgen cZS)) abelemE// aS -{1}cS exponent_dvdn.
have TI_SZ : S :&: Z = 1.
  rewrite prime_TIg ?cS //= -/Z.
  move: rR; apply: contraL; move/centS; move/(setIS R); move/rankS => sR0Z.
  by move: (leq_ltn_trans (leq_trans sR0Z rS) rR); rewrite /= defCRZ ltnn.
have cSZ : #|SZ| = (p^2)%N by rewrite /SZ /= norm_mulgenEl ?TI_cardMg ?cS ?cZ.
have e2SZ : SZ \in 'E_p^2(R).
  by rewrite (pnElemE _ _ p_pr) inE cSZ eqxx inE abeSZ mulgen_subG sSR sZR.
have maxSZ : SZ \in 'E*_p(R).
  apply/pmaxElemP; split=> [|H]; first by rewrite inE mulgen_subG sSR sZR.
  case/pElemP=> // sHR aH sSZH; apply/eqP; rewrite eq_sym eqEcard sSZH /= cSZ.
  case: (eqsVneq H 1) => [->|ntH]; first by rewrite cards1 expn_gt0 prime_gt0.
  have [_ _ [[->|[->|r cH]]]] := (pgroup_pdiv (abelem_pgroup aH) ntH);
    rewrite ?leq_exp2l ?prime_gt1 //.
  suff: 'r(H) <= 2 by rewrite (rank_abelem aH) cH pfactorK.
  rewrite (leq_trans _ rS) // rankS // subsetI sHR centsC.
  exact: subset_trans (mulgen_subl _ _) (subset_trans sSZH (abelem_abelian aH)).
have nsSZT : ~~ (SZ \subset T).
  by apply/negP; move/(nsTifE2 _); rewrite inE maxSZ e2SZ.
have sZT : Z \subset T.
  rewrite subsetI sZR centsC (subset_trans _ (subsetIr R _)) // defCRZ.
  exact: (subset_trans (Ohm_sub 1 _) (ucn_sub _ _)).
have TI_ST : S :&: T :=: 1.
  rewrite prime_TIg ?cS //; apply: contra nsSZT => *. 
  by rewrite /SZ /= norm_mulgenEl //= mul_subG.
have defST : S * T = R.
  apply/eqP; rewrite eqEcard TI_cardMg ?mul_subG ?subsetIl // mulnC.
  by rewrite -(LaGrange (subsetIl R 'C(W))) cS idxT leqnn.
have sR'T : R^`(1) \subset T.
  rewrite der1_min ?normsI ?normG  ?norms_cent //= -/T.
  by rewrite -defST quotient_mulg quotient_abelian. 
have TI_SR' : S :&: R^`(1) :=: 1.
  rewrite prime_TIg ?cS //; apply: contra nsSZT => *.
  by rewrite /SZ /= norm_mulgenEl //= mul_subG // (subset_trans _ sR'T).
have defCRS : S \x 'C_T(S) = 'C_R(S).
  rewrite (dprodE _ (eqP _)) /= -/T; last first.
    by rewrite eqEsubset sub1G -TI_ST subsetI subsetIl 2?subIset ?subxx // orbC.
  - rewrite (subset_trans _ (centI _ _)) //.
    by rewrite (subset_trans _ (mulgen_subr _ _)) // centsC subxx.
  apply/eqP; rewrite eqEsubset subsetI -{1}defST.
  rewrite mul_subG ?[_ \subset _]aS ?subsetIr // mulgS ?subsetIl //=.
  by rewrite group_modl ?[_ \subset _]aS //= defST subxx.
have aRT : abelian (R / T) := sub_der1_abelian sR'T.
have sCTSR : 'C_T(S) \subset R by rewrite !subIset // subxx.
have rCTS : 'r_p('C_T(S)) <= 1%N. 
  apply: contraLR (leqnn #|SZ|); rewrite -!ltnNge; case/p_rank_geP=> /= F.
  case/pnElemP; rewrite -/T {1}cSZ => sFCTS abeF <-; rewrite -p_part.
  have sFCE : F \subset 'C(S <*> Z).
    rewrite norm_mulgenEl // centM subsetI !(subset_trans sFCTS) ?subsetIr //.
    by rewrite subIset ?(subset_trans (char_sub charTR)) // -{1}defCRZ subsetIr.
  have nFE : F \subset 'N(S <*> Z) by apply: subset_trans sFCE (cents_norm _).
  have sFR : F \subset R := (subset_trans sFCTS sCTSR).
  suff eFSZ: (F <*> SZ)%G \in 'E_p(R).
    case/pmaxElemP: maxSZ => _; move/(_ _ eFSZ)=> <-; rewrite ?mulgen_subr //.
    rewrite /= norm_mulgenEl // (part_pnat_id (abelem_pgroup abeF)).
    apply: (leq_trans _ (subset_leq_card (mulgS _ (mulgen_subl _ _)))).
    have TI_FS : F :&: S == 1.
      by rewrite -subG1 -TI_ST setIC setSI ?(subset_trans sFCTS) ?subsetIl.
    by rewrite TI_cardMg ?(cS,ltn_Pmulr,prime_gt1,cardG_gt0) // (eqP TI_FS).
  by rewrite inE (cprod_abelem p (cprodEgen _)) ?(abeF,mulgen_subG,sFR,sSR,sZR).
by split; rewrite // (odd_pgroup_rank1_cyclic (pgroupS _ pR) (oddSg _ oddR)).
Qed.

Definition CR0R1 p G :=
    ('E_p^3(G) :=: set0) \/
    exists R0 : {group gT}, exists R1 : {group gT}, 
      [/\ R0 \x R1 = 'C_G(R0), R0 \subset G, 
          R1 \subset G, #|R0| = p & cyclic R1]. 

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

Corollary CRS2_narrow : 
    forall S : {group gT}, S \subset R  -> #|S| = p -> 'r('C_R(S)) <= 2 ->
  p.-narrow R.
Proof.
move=> S sSR cS rCRS.
pose SZ := (S <*> [group of Z])%G.
have pS := pgroupS sSR pR.
have aS : abelian S by rewrite (p2group_abelian pS) // cS logn_prime // eqxx.  
have cZS : S \subset 'C(Z) by rewrite (subset_trans sSR) // -defCRZ // subsetIr.
have abeSZ : p.-abelem SZ.
  by rewrite (cprod_abelem p (cprodEgen cZS)) abelemE// aS -{1}cS exponent_dvdn.
have TI_SZ : S :&: Z = 1.
  rewrite prime_TIg ?cS //= -/Z.
  move: rR; apply: contraL; move/centS; move/(setIS R); move/rankS => sR0Z.
  by move: (leq_ltn_trans (leq_trans sR0Z rCRS) rR); rewrite /= defCRZ ltnn.
have sSZCRS : SZ \subset 'C_R(S).
  rewrite mulgen_subG /= subsetI sSR [_ \subset _]aS.
  by rewrite subsetI sZR /= centsC (subset_trans sSR) // -defCRZ subsetIr.
have cZ : #|Z| = p.
  have [_ _ [[] //= r cZ]] := pgroup_pdiv pOZ  ntZ.
  move: (leq_trans (rankS sSZCRS) rCRS).
  rewrite (rank_abelem abeSZ) /SZ /= cent_mulgenEl // TI_cardMg //= -/Z.
  rewrite cS cZ logn_mul ?expn_gt0 ?(prime_gt0 p_pr) //.
  by rewrite logn_prime ?eqxx //= pfactorK.
have cSZ : #|SZ| = (p^2)%N by rewrite /SZ /= cent_mulgenEl ?TI_cardMg ?cS ?cZ.
have e2SZ : SZ \in 'E_p^2(R).
  by rewrite (pnElemE _ _ p_pr) inE cSZ eqxx inE abeSZ mulgen_subG sSR sZR.
have maxSZ : SZ \in 'E*_p(R).
  apply/pmaxElemP; split=> [|H]; first by rewrite inE mulgen_subG sSR sZR.
  case/pElemP=> // sHR aH sSZH; apply/eqP; rewrite eq_sym eqEcard sSZH /= cSZ.
  case: (eqsVneq H 1) => [->|ntH]; first by rewrite cards1 expn_gt0 prime_gt0.
  have [_ _ [[->|[->|r cH]]]] := (pgroup_pdiv (abelem_pgroup aH) ntH);
    rewrite ?leq_exp2l ?prime_gt1 //.
  suff: 'r(H) <= 2 by rewrite (rank_abelem aH) cH pfactorK.
  rewrite (leq_trans _ rCRS) // rankS // subsetI sHR centsC.
  exact: subset_trans (mulgen_subl _ _) (subset_trans sSZH (abelem_abelian aH)).
by exists SZ.
Qed.

Let rp_cyc1: forall H, p.-group H -> cyclic H -> logn p #|'Ohm_1(H)| <= 1.
Proof.
move=> C pC; move/(cyclicS (Ohm_sub 1 _))=> cycC1.
by rewrite -abelem_cyclic // abelem_Ohm1 ?cyclic_abelian.
Qed.

Lemma CR0R1_narrow : CR0R1 p R -> p.-narrow R.
Proof.
case=>[| [R0] [R1] [] dpCRR0 sR0R sR1R cR0 cyR1].
  by move/eqP;move/set0Pn; move: rR; rewrite (rank_pgroup pR); move/p_rank_geP.
case/dprodP: (dpCRR0) => [_ defCRR0 sR0CR1 TI_R10].
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
  rewrite -add1n p_rank_abelian // -(dprod_card (Ohm_dprod _ dpCRR0)).
  by rewrite logn_mul ?cardG_gt0 // leq_add ?rp_cyc1 // (pgroupS _ pR).
exact: CRS2_narrow sR0R cR0 rCRR0le2.
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
rewrite -add1n p_rank_abelian // -(dprod_card (Ohm_dprod _ dpCRR0)).
by rewrite logn_mul ?cardG_gt0 // leq_add ?rp_cyc1 // (pgroupS _ pR).
Qed.

End Five.

Section Five5.

Variable gT : finGroupType. 
Variables (R : {group gT}) (p : nat).
Hypotheses (pR : p.-group R) (oddR : odd #|R|).

(* duplicate *)
Let rp_cyc1: forall H : {group gT}, 
  p.-group H -> cyclic H -> logn p #|'Ohm_1(H)| <= 1.
Proof.
move=> C pC; move/(cyclicS (Ohm_sub 1 _))=> cycC1.
by rewrite -abelem_cyclic // abelem_Ohm1 ?cyclic_abelian.
Qed.

(* B&G 5.5, *)
Theorem narrow_solvable_Aut :
  narrow p R -> forall A:{group perm_of_finGroupType gT}, 
  solvable A -> A \subset Aut R ->
  odd #|A| ->
   [/\ p^'.-group (A / 'O_p(A)), abelian (A / 'O_p(A)) &
       2 < 'r(R) -> forall x, x \in A -> p^'.-elt x -> #[x] %| p.-1 ].
Proof.
move=> nR.
have ntR : R :!=: 1.
  case: eqP nR => // defR [E]; case/pnElemP; rewrite defR; move/trivgP=> -> _.
  by rewrite cards1 logn1.
have [p_pr _ [r cR]] := pgroup_pdiv pR ntR.
have oddp : odd p.
  by case: (even_prime p_pr) oddR => // p2; rewrite cR p2 odd_exp eqn0Ngt.
case: (critical_odd _ pR)=> // H [cHR sHRZ] nc2 exH pCAu A solA sAAu oddA.
have sCO : 'C_A(H | 'P) \subset 'O_p(A).
  apply: pcore_max; first by apply: pgroupS (setSI _ sAAu) pCAu.
  rewrite /normal subsetIl normsI ?normG ?(subset_trans _ (astab_norm _ _))//.
  apply/subsetP=> a Aa; rewrite !inE /=; case/andP: cHR => sHR.
  move/forallP; move/(_ a);move/implyP; move/(_ (subsetP sAAu _ Aa)) => ch.
  have aAutR : a \in Aut R by rewrite (subsetP sAAu _ Aa).
  have:= sub_morphim_pre [morphism of autm aAutR] H sHR; simpl.
  by rewrite !morphimEsub // morphpreE subsetI sHR /= => <-.
have ntH : H :!=: 1.
  by case: eqP exH (prime_gt1 p_pr) => // ->; rewrite exponent1 => ->; rewrite ltnn.
split.
  (* useless, but I'd like to understand what went wrong here *)
  wlog useless_ntH : / H :!=: 1.
    case: (eqsVneq H 1) => [trivH _|?]; last by apply.
    rewrite (_:A / _ = 1) ?pgroup1 //; apply/trivgP.
    rewrite quotient_sub1 ?char_norm ?pcore_char //.
    rewrite (subset_trans _ sCO) // trivH subsetI subxx.
    (* here I'm using actions in a bad way... *)
    rewrite /astab subsetI subsetT; apply/subsetP=>x Ax; rewrite inE.
    apply/subsetP=> e; move/set1P=> ->; rewrite inE; apply/eqP.
    have sA : A \subset [set: perm_of_finGroupType gT] by apply: subsetT.
    have gA : is_groupAction R (perm_action gT \ sA).
      move=> a Aa /=. rewrite ractpermE (subsetP sAAu) //.
      by rewrite (_: actperm 'P a = a) //; apply/permP => y; rewrite actpermE.
    by apply: @gact1 _ _ A R (GroupAction gA) _ Ax.
- admit. (* 2 < r(R) -> 1.9 stable_factor_cent, otherwise 4.17 *)
- admit. 
move=> rR.
case: (narrow_CR0R1 pR oddR rR nR). 
  by move/eqP;move/set0Pn;move: rR; rewrite (rank_pgroup pR); move/p_rank_geP.
move=> [R0 [R1 [dpR0R1 sR0R sR1R cR0 cyR1 x xA p'x]]].
have pR0 := pgroupS sR0R pR.
have aR0 : abelian R0 by rewrite (p2group_abelian pR0)// cR0 logn_prime ?eqxx.
have cyR0 : cyclic R0 by rewrite prime_cyclic // cR0.
have aCRR0 : abelian 'C_R(R0).
  by case/dprodP: dpR0R1 => _ <- *; rewrite abelianM aR0 ?cyclic_abelian.
pose U := R0 <*> 'Z(H).
have nsR0H : ~~ (R0 \subset H).
  apply/negP=> sR0H.
  have nZHR0 : R0 \subset 'N('Z(H)). 
    by rewrite (subset_trans sR0H) // normsI ?norms_cent ?normsG.
  have sUH : U \subset H.
    by rewrite mulgen_subG sR0H subsetIl.
  have abeU : p.-abelem U.
    rewrite abelemE //= norm_mulgenEl //= abelianM center_abelian.
    rewrite aR0 (subset_trans sR0H) 1?centsC ?subsetIr //.
    by rewrite -norm_mulgenEl // (dvdn_trans (exponentS sUH)) // exH.
  have rCRR0le2 : 'r('C_R(R0)) <= 2.
    rewrite (rank_pgroup (pgroupS (subsetIl _ _) pR)) /=.
    rewrite -add1n p_rank_abelian // -(dprod_card (Ohm_dprod _ dpR0R1)).
    by rewrite logn_mul ?cardG_gt0 // leq_add ?rp_cyc1 // (pgroupS _ pR).
  have mU : 'm(U) <= 'r('C_R(R0)).
    rewrite (grank_abelian (abelem_abelian abeU)).
    rewrite rankS //= subsetI (subset_trans _ (char_sub cHR)) ?norm_mulgenEl //.
      by rewrite mul_subG // centsC (subset_trans sR0H) 1?centsC ?subsetIr.
    by rewrite mul_subG // subsetIl.
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
      rewrite /normal sUR -commg_subl (subset_trans (commSg _ sUH)) //= -/U.
      by rewrite (subset_trans sHRZ) // mulgen_subr.
    case: (p_rank_3_normal_abelem_SCN pR oddR rR ep2U nUR) => F SCN_F sUF.
    suff: 2 < 'r('C_R(R0)) by move/(leq_ltn_trans rCRR0le2); rewrite ltnn.
    have sCR0CU : 'C_R(U) \subset 'C_R(R0).
      by rewrite setIS // centS // mulgen_subl.
    rewrite (leq_trans _ (rankS sCR0CU)) //=. 
    move: SCN_F; rewrite inE; case/andP; case/SCN_P=> sFR defF lt2.
    rewrite (leq_trans lt2) //.
    by rewrite rankS // -defF // setIS // centS.
  rewrite (grank_abelian (abelem_abelian abeU)) /= -/U.
  rewrite (rank_abelem abeU) /= -/U.
  have ntU : U != 1.
    case: eqP cR0 => //; move/trivgP; move/(subset_trans (mulgen_subl _ _)).
    move/trivgP => ->; rewrite cards1 => abs; move: (prime_gt1 p_pr).
    by rewrite abs ltnn.
  have [_ _ [[cU _|k ->]]] := pgroup_pdiv (abelem_pgroup abeU) ntU; last first.
    by rewrite pfactorK.
  have defU : U = R0.
    by apply/eqP; rewrite eq_sym eqEcard cR0 cU mulgen_subl leqnn.
  have nUR : U <| R.
    rewrite /normal sUR -commg_subr (subset_trans _ (mulgen_subr _ _)) //.
    by rewrite /= [_ <*> _]defU (subset_trans _ sHRZ) // commGC commSg. 
  have sR0Z : R0 \subset 'Z(R).
    have := nil_meet_Z (pgroup_nil pR) nUR ntU. 
    move: cU; rewrite /= [_ <*> _]defU expn1 => cR0p.
    by apply: contraR => nsR0Z; rewrite (prime_TIg _ nsR0Z) ?eqxx // cR0p.
  have defR : 'C_R(R0) = R.
    apply/eqP; rewrite eqEsubset subsetIl subsetI subxx centsC.
    by rewrite (subset_trans sR0Z) // subsetIr.
  by rewrite defR in rCRR0le2; move: (leq_trans rR rCRR0le2); rewrite ltnn.
have sCHR0x : 'C_H(R0) \subset R0 \x 'Ohm_1(R1).
  have pabR0 : p.-abelem R0.
    by rewrite (abelemE _ p_pr) cyclic_abelian // -cR0 exponent_dvdn.
  rewrite -(Ohm1_id pabR0) (Ohm_dprod 1 dpR0R1) (Ohm1_id pabR0).
  apply/subsetP=> h; case/setIP=> Hh CR0h.
  rewrite (OhmE 1 (pgroupS (subsetIl _ _) pR)) mem_gen // !inE /=.
  by rewrite CR0h (subsetP _ _ Hh) ?char_sub // -exH expg_exponent ?eqxx.
have ntHIZ : H :&: 'Z(R) != 1.
  apply: contraL ntH; move/eqP=> abs.
  by rewrite (nil_TI_Z (pgroup_nil pR) (char_normal cHR)) // eqxx.
have cCHR0 : #|'C_H(R0)| = p.
  admit.
move/constt1P: p'x. have := stable_factor_cent. 
(* Search _ constt. Locate constt. Set Printing All. idtac. *)
admit.
Qed.

End Five5. 