(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum ssrint algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.
Require Import PFsection6 PFsection7 PFsection8 PFsection9 PFsection10.

(******************************************************************************)
(* This file covers Peterfalvi, Section 11: Maximal subgroups of Types        *)
(* III and IV.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.

Section Eleven.

(* This is Peterfalvi (11.1). *)
Lemma lbound_expn_odd_prime p q : 
   odd p -> odd q -> prime p -> prime q -> p != q -> 4 * q ^ 2 + 1 < p ^ q.
Proof.
move=> odd_p odd_q pr_p pr_q p_neq_q.
have{pr_p pr_q} [pgt2 qgt2] : 2 < p /\ 2 < q by rewrite !odd_prime_gt2.
have [qlt5 | qge5 {odd_q qgt2 p_neq_q}] := ltnP q 5.
  have /eqP q3 : q == 3 by rewrite eqn_leq qgt2 andbT -ltnS -(odd_ltn 5).
  apply: leq_trans (_ : 5 ^ q <= p ^ q); first by rewrite q3.
  by rewrite leq_exp2r // odd_geq // ltn_neqAle pgt2 eq_sym -q3 p_neq_q.
apply: leq_trans (_ : 3 ^ q <= p ^ q); last by rewrite -(subnKC qge5) leq_exp2r.
elim: q qge5 => // q IHq; rewrite ltnS leq_eqVlt => /predU1P[<- // | qge5].
rewrite (expnS 3); apply: leq_trans {IHq}(leq_mul (leqnn 3) (IHq qge5)).
rewrite -!addnS mulnDr leq_add // mulnCA leq_mul // !(mul1n, mulSnr).
by rewrite -addn1 sqrnD muln1 -(subnKC qge5) !leq_add ?leq_mul.
Qed.

Local Open Scope ring_scope.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

Variables M U W W1 W2 : {group gT}.
Hypotheses (maxM : M \in 'M) (defW : W1 \x W2 = W) (MtypeP : of_typeP M U defW).
Hypothesis Mtypen2 : FTtype M != 2.

Let Mtypen5 : FTtype M != 5. Proof. exact: FTtype5_exclusion. Qed.
Let Mtypen1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.
Let Mtype_gt2 : (FTtype M > 2)%N.
Proof. by move: (FTtype M) Mtypen1 Mtypen2 (FTtype_range M)=> [|[|[]]]. Qed.
Let Mtype34 : FTtype M \in pred2 3 4.
Proof.
by move: (FTtype M) Mtype_gt2 Mtypen5 (FTtype_range M)=> [|[|[|[|[|[|[]]]]]]].
Qed.

Local Notation H0 := (Ptype_Fcore_kernel MtypeP).
Local Notation "` 'H0'" := (gval H0) (at level 0, only parsing) : group_scope.
Local Notation "` 'M'" := (gval M) (at level 0, only parsing) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation H := `M`_\F%G.
Local Notation "` 'H'" := `M`_\F (at level 0) : group_scope.
Local Notation HU := M^`(1)%G.
Local Notation "` 'HU'" := `M^`(1) (at level 0) : group_scope.
Local Notation U' := U^`(1)%G.
Local Notation "` 'U''" := `U^`(1) (at level 0) : group_scope.
Local Notation C := 'C_U(`H)%G.
Local Notation "` 'C'" := 'C_`U(`H) (at level 0) : group_scope.
Local Notation HC := (`H <*> `C)%G.
Local Notation "` 'HC'" := (`H <*> `C) (at level 0) : group_scope.
Local Notation H0C := (`H0 <*> `C)%G.
Local Notation "` 'H0C'" := (gval H0 <*> `C) (at level 0) : group_scope.

Let Mtype24 := compl_of_typeII_IV maxM MtypeP Mtypen5.
 
Let p := #|W2|.
Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.

Let q := #|W1|.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.

Let nsHUM : HU <| M := der_normal _ _.

Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.

Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists maxM MtypeP Mtypen5. Qed.

Let defMs : M`_\s = HU. Proof. by rewrite /FTcore andbC leqNgt Mtype_gt2. Qed.

Notation S_ := (seqIndD HU M HU).

Local Notation tau :=  (FT_Dade0 maxM).
Local Notation R := (FTtypeP_coh_base maxM MtypeP).

Let subc_M : subcoherent (S_ 1) tau R.
Proof. by rewrite -{2}(group_inj defMs); apply: FTtypeP_subcoherent. Qed.

Let sH0H : H0 \subset H.
Proof.  by have/andP[/maxgroupp/andP[/proper_sub]]:= chiefH0. Qed.

Let nsH0H : H0 <| H.
Proof.
rewrite /normal sH0H (subset_trans (Fcore_sub _)) //.
by have/andP[/maxgroupp/andP[]]:= chiefH0.
Qed.

Let nsCM : C <| M.
Proof.
have [[_ [_ _ nUW1 _] _ _ _] /mulG_sub[_ sW1M]] := (MtypeP, sdprodW defM).
have [_ sUHU mulHU nHU _] := sdprod_context defHU.
rewrite -{2}(sdprodW defM) /normal subIset ?(subset_trans sUHU) ?mulG_subl //=.
rewrite mulG_subG /= -mulHU mulG_subG cents_norm 1?centsC ?subsetIr //.
by rewrite !normsI ?norms_cent ?normG // ?(subset_trans sW1M) ?gFnorm.
Qed.

Let defHC : H \x C = HC.
Proof. 
apply: dprodEY; first by exact: subsetIr.
by have[/dprodP[]]:= typeP_context MtypeP.
Qed.

Let defH0C : H0 \x C = H0C.
Proof.
have /dprodP [_ _ sC_CH iH_C] := defHC.
apply: dprodEY; first by apply: subset_trans (subsetIr _ _) (centS sH0H).
by apply/eqP; rewrite -subG1 -iH_C setSI.
Qed.

Let normal_hyps : [/\ 1 <| M, HC <| M & H0C <| M].
Proof.
have/andP[/maxgroupp/andP[/proper_sub H0sH nH0M nsHM]] := chiefH0.
by rewrite normal1 ?normalY // /normal (subset_trans _ (normal_sub nsHM)).
Qed.

(* This is Peterfalvi (11.3). *)
Lemma ncoH0C : ~ coherent (S_ H0C) M^# tau.
Proof.
move=> coH0C.
have[] : ~ coherent (S_ 1) M^# tau by exact: FTtype345_noncoherence.
have [_ /mulG_sub[sHUM sW1M] _ _] := sdprodP defM.
have [nsHHU sUHU /mulG_sub[sHHU sUM'] nHU tiHU] := sdprod_context defHU.
have [sHM sUM] := (subset_trans sHHU sHUM, subset_trans sUHU sHUM).
have sCM : C \subset M by rewrite subIset ?sUM.
have sH0C_M : H0C \subset M by rewrite /normal join_subG (subset_trans sH0H).
have/andP[/maxgroupp/andP[_ nsH0M _]] := chiefH0.
have nH0_C := subset_trans sCM nsH0M.
have sH0C_HC : H0C \subset HC by apply: genS (setSU _ _).
apply: (bounded_seqIndD_coherent _ _ subc_M normal_hyps)=> //.
- by exact: solvableS (der_subS 0 _) (of_typeP_sol MtypeP).
- by rewrite sub1G sH0C_HC join_subG sHHU subIset ?sUHU.
-  have[HC_F _ _ _] := typeP_context MtypeP.
   by rewrite quotient_nil //= -defHC HC_F Fitting_nil.
have[_ _ cHbar] :=  Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
rewrite -(index_sdprod defM) -divgS // -(dprod_card defHC) -(dprod_card defH0C).
rewrite divnMr ?cardG_gt0 // divg_normal // cHbar.
rewrite typeIII_IV_core_prime // -/q lbound_expn_odd_prime ?mFT_odd //.
have coHUq : coprime #|HU| q.
  by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP.
apply: contraTneq coHUq => <-; rewrite coprime_sym prime_coprime ?cardSg //.
by rewrite -(typeP_cent_compl MtypeP) subsetIl.
Qed.

Let minHbar : minnormal (H / H0)%g (M / H0)%g.
Proof. by exact: chief_factor_minnormal. Qed.

Let pabHbar : p.-abelem (H / H0)%g.
Proof.
have solHbar : solvable (H / H0)%g.
  by rewrite quotient_sol // nilpotent_sol // Fcore_nil.
have [_ _] := minnormal_solvable minHbar (subxx _) solHbar.
by rewrite /is_abelem def_Ptype_factor_prime.
Qed.

(* This is Peterfalvi (11.4). *)
Lemma bounded_proper_coherent H1 :
  H1 <| M -> H1 \proper HU -> coherent (S_ H1) M^# tau ->
    (#|HU : H1| <= 2 * q * #|U : C| + 1)%N.
Proof.
move=> nsH1_H psH1_M' coH1.
have [nsHHU _ /mulG_sub[sHHU sUHU] _ _] := sdprod_context defHU.
rewrite -leC_nat natrD -ler_subl_addr.
have-> : (2 * q * #|U : C|)%:R = 2%:R * #|M : HC|%:R * sqrtC #|HC : HC|%:R.
  rewrite indexgg sqrtC1 mulr1 -mulnA natrM; congr (_ * _%:R).
  apply/eqP; rewrite // -(eqn_pmul2l (cardG_gt0 HC)).
  rewrite Lagrange; last by case normal_hyps=> _ /andP[].
  rewrite mulnCA -(dprod_card defHC) -mulnA (Lagrange (subsetIl _ _)).
  by rewrite -(sdprod_card defM) -(sdprod_card defHU) mulnC.
pose sol_HU := solvableS (der_subS 0 _) (of_typeP_sol MtypeP).
pose CSB := coherent_seqIndD_bound nsHUM sol_HU subc_M _ _ coH1.
have {CSB}[||/ncoH0C|] // := CSB H0C HC%G HC%G; first by have [] := normal_hyps.
split=> //.
  apply: genS (setSU _ _)=> //. 
  by rewrite join_subG sHHU subIset ?sUHU.
rewrite (center_idP _) //.
have/isog_abelian->// : (HC / H0C)%g \isog (H / H0)%g.
rewrite /= (joingC H0) isog_sym quotient_sdprodr_isog ?(dprodWsdC defHC) //.
by exact: abelem_abelian pabHbar.
Qed.

(* This is Peterfalvi (11.5). *)
Lemma derM2_HC : (M^`(2) = HC)%g.
Proof.
have [defFM [_ sUCH] _ _] := typeP_context MtypeP.
have {defFM}sderM2_HC : M^`(2)%g \subset HC.
  by rewrite -defHC defFM; have [_ _ []] := MtypeP.
have sub_derM2 : subcoherent (S_ M^`(2)) tau R.
  by apply: (subset_subcoherent subc_M); split;
   [exact: seqInd_uniq | apply: seqInd_sub | exact: cfAut_seqInd].
have co_derM2 : coherent (S_ M^`(2)%G) M^# tau.
  apply: uniform_degree_coherence sub_derM2 _.
  apply: all_pred1_constant #|M : HU|%:R _ _.
  rewrite all_map; apply/allP=> _ /seqIndP [y /setDP[sM2K _] ->] /=.
  rewrite inE in sM2K.
  by rewrite cfInd1 ?gFsub // lin_char1 ?mulr1 ?lin_irr_der1.
have sol_HU := solvableS (der_subS 0 _) (of_typeP_sol MtypeP).
have [_ _ /mulG_sub[sHHU sUHU] _ _] := sdprod_context defHU.
have sHC_HU : (HC \subset HU)%g.
  by rewrite join_subG sHHU subIset // sUHU.
have B_HC : (#|HC : (M^`(2))%g| < 2 * q + 1)%N.
  rewrite -(ltn_pmul2r (indexg_gt0 U C)) mulnDl mul1n.
  apply: leq_ltn_trans (_ : 2 * q * #|U : C| + 1 < _)%N; last first.
    by rewrite ltn_add2l indexg_gt1 subsetIidl sUCH //; have [] := Mtype24.
  have {1}-> : #|U : C| = #|HU : HC|.
    rewrite -!divgS // ?subsetIl // -(sdprod_card defHU) -(dprod_card defHC).
    by rewrite divnMl.
  rewrite mulnC (Lagrange_index sHC_HU) //.
  rewrite bounded_proper_coherent ?gFnormal //.
  rewrite (sol_der1_proper sol_HU) // -subG1.
  have : (H / H0 != 1)%g by case/mingroupp/andP : minHbar.
  by apply: contra => /(subset_trans sHHU) /trivgP->; rewrite quotient1.
have regHC_W1 : semiregular (HC / M^`(2))%g (W1 / M^`(2))%g.
  move=> /= g /setD1P[ntg /morphimP[w nM''w W1w] /= Dg].
  rewrite -cent_cycle Dg -quotient_cycle //.
  rewrite -coprime_quotient_cent ?cycle_subG //; last first.
  - by apply: solvableS sHC_HU _.
  - rewrite (coprimeSg sHC_HU) // (coprime_dvdr (order_dvdG W1w)) //.
    by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP.
  apply: quotientS1=> /=.
  have [_ _ _ [_ _ _ sW2M'' prW1HU] _] := MtypeP.
  rewrite (subset_trans _ sW2M'') // cent_cycle -(prW1HU w) ?setSI //.
  by rewrite !inE (contraNneq _ ntg) // Dg => ->; rewrite morph1.
have [_ sW1M _ _ tiHU_W1] := sdprod_context defM.
suff /dvdnP[k Dk] : 2 * q %| #|HC : M^`(2)%g|.-1.
  rewrite -(prednK (indexg_gt0 _ _)) Dk addn1 ltnS in B_HC.
  rewrite mulnA ltn_pmul2r ?cardG_gt0 ?(@ltn_pmul2r 2 _ 1) // in B_HC.
  rewrite ltnS leqn0 in B_HC.
  apply/eqP; rewrite eqEsubset sderM2_HC -indexg_eq1.
  by rewrite -(prednK (indexg_gt0 _ _)) Dk (eqP B_HC).
rewrite -card_quotient; last first.
   by rewrite (subset_trans sHC_HU) // (der_norm 1).
rewrite Gauss_dvd; last by rewrite coprime2n mFT_odd.
rewrite dvdn2 -[~~ _]/(odd _.+1) prednK ?cardG_gt0 //.
rewrite quotient_odd ?mFT_odd //=.
have-> : q = #|(W1 / M^`(2))%g|.
  apply/card_isog/quotient_isog.
    by rewrite (subset_trans sW1M) ?gFnorm.
  by apply/trivgP; rewrite -tiHU_W1 setSI // (der_sub 1).
apply: regular_norm_dvd_pred=> //.
rewrite quotient_norms // (subset_trans sW1M) //.
by have [_ /andP[]] :=  normal_hyps.
Qed.

(* This is  Peterfalvi (11.6). *)
Lemma Mtype34_facts :
  ([/\ p.-group H, U \subset 'C(H0), H0 :=: H^`(1) & `C = U^`(1)])%g. 
Proof.
have nH := Fcore_nil M.
have CHsH := subsetIl H 'C(U).
have nHH' : H \subset 'N(H^`(1))%g by exact: der_norm.
have /sdprod_context[_ UsM' HeU UsNH tHiU] :=  defHU.
have nUH' : U \subset 'N(H^`(1))%g by apply: (char_norm_trans (der_char _ _)).
have HUsH :  [~: H, U] \subset H by rewrite commg_subl.
have UsCHO : U \subset 'C(H0).
  have Frob := Ptype_compl_Frobenius maxM MtypeP Mtypen5.
  have nUW1_NH0 : U <*> W1 \subset 'N(H0).
    have [/andP[sHUM _] sW1M _ _ _] := sdprod_context defM.
    have/andP[/maxgroupp/andP[_ nH0M _]] := chiefH0.
    by rewrite join_subG !(subset_trans _ nH0M) // (subset_trans _ sHUM).
  have [||_->]// := Frobenius_Wielandt_fixpoint Frob nUW1_NH0.
  - by apply: coprimeSg (Ptype_Fcore_coprime MtypeP).
  - by apply/nilpotent_sol/(nilpotentS _ nH).
  have-> : 'C_H0(W1) = H0 :&: 'C_H(W1).
    by rewrite setIA; move/setIidPl : (normal_sub nsH0H)->.
  rewrite cardMg_TI // -LagrangeMl -card_quotient; last first.
    by apply: subset_trans (subsetIl _ _) _; case/andP : nsH0H.
  have/coprime_subcent_quotient_pgroup<-// : q.-group W1.
  - apply/pgroupP=> p2 Pp2 /prime_nt_dvdP->; rewrite ?inE //.
    by case: p2 Pp2=> // [[]].
  - have [_] := Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
    rewrite /= (typeP_cent_core_compl  MtypeP) //.
    by rewrite (def_Ptype_factor_prime maxM MtypeP) // => ->.
  - case/andP : chiefH0 => /maxgroupp/andP[_ /(subset_trans _)-> //].
    by case/sdprod_context : defM.
  apply: (coprimeSg (normal_sub nsH0H) (coprimegS (joing_subr U W1) _)).
  by exact: Ptype_Fcore_coprime MtypeP.
split=> //.
(* p.-group H *)
- apply/pnatP=> //= r Pr rDh; rewrite -topredE /=; case: eqP=> // /eqP rDp.
  have CrHr : (#|'C_H(U)|`_r = #|H|`_r)%N.
    have /= := typeII_IV_core maxM MtypeP Mtypen5.
    rewrite (negPf Mtypen2) -/p -/q => [[_ _ ->]].
    rewrite !(partnM,partnX) // ?(expn_gt0, prime_gt0) //.
    rewrite [X in (X ^ _)%N]part_p'nat ?(exp1n, mul1n) // p'natE //.
    by apply/prime_nt_dvdP=> //; [case: (r) Pr=> // [[|[]]] | apply/eqP].
  have rDC : r %| #|'C_H(U)|.
    apply: (dvdn_trans _ (dvdn_part \pi(r) _)).
    move: CrHr; rewrite -!(eq_partn _ (pi_of_prime Pr))=>->.
    by rewrite -{1}[r]partn_pi ?prime_gt0 // partn_dvd.
  case: (Sylow_exists r 'C_H(U))=> R1 S_CR1.
  have R1sH := subset_trans (pHall_sub S_CR1) (subsetIl _ _).
  suff : (R1^`(1) == R1)%g.
    rewrite eqEproper=> /andP[_ /negP[]].
    apply: (sol_der1_proper (nilpotent_sol nH) R1sH).
    apply/negP=> trivR1; move/card_Hall : S_CR1.
    move/eqP; rewrite (eqP trivR1) CrHr cards1 eq_sym p_part_eq1 /=.
    move: (pi_of_dvd rDh (cardG_gt0 _))=> -> //.
    by rewrite pi_of_prime // inE.
  have /setIidPl {2}<- : R1 \subset (HU^`(1))%g.
   rewrite derg1 -dergSn derM2_HC; case/dprodP : defHC=> _ <- _ _.
   by rewrite (subset_trans _ (mulg_subl _ _)).
  suff def1HU : R1 \x ('O_r^'(H) <*> U) = HU.
    case/(der_dprod 1)/dprodP : (def1HU)=> _ <- _ _.
    rewrite  setIC -group_modl ?der_sub // setIC.
    suff-> : (R1 :&: ('O_r^'(H) <*> U)^`(1) = 1)%g by rewrite mulg1.
    apply/trivgP/(subset_trans (setIS _ (der_sub _ _)))/trivgP.
    by case/dprodP : def1HU.
  have /dprodP[_ eRO OsCR tRiO] : R1 \x 'O_r^'(H) = H.
    rewrite -{2}(nilpotent_pcoreC r nH); congr (_ \x _).
    apply: (eq_Hall_pcore (nilpotent_pcore_Hall r nH)).
    by rewrite pHallE R1sH -CrHr; case/pHallP : S_CR1=> _ ->/=.
  have UnN : U \subset 'N('O_r^'(H)).
    by case/sdprodP : defHU=> _ _ /char_norm_trans->//; apply: pcore_char.
  rewrite dprodE /=.
  - by rewrite norm_joinEr // mulgA eRO.
  - rewrite join_subG OsCR centsC.
    by case/pHallP : S_CR1; rewrite subsetI=> /andP[].
  rewrite norm_joinEr // - (setIidPl R1sH).
  rewrite -setIA [_ :&: (_ * _)%g]setIC -group_modl ?pcore_sub //.
  by rewrite [U :&: _]setIC tHiU mulg1 tRiO.
(* H0 = (H^`(1))%g *)
- pose H1 := (H / H^`(1))%g.
  pose U1 := (U / H^`(1))%g.
  pose HU1 := (HU / H^`(1))%g.
  apply/eqP; rewrite  eqEsubset andbC.
  rewrite der1_min ?(abelem_abelian pabHbar) //=; last by case/andP: nsH0H.
  rewrite -quotient_sub1; last by case/andP: nsH0H=> /subset_trans->.
  suff <- : 'C_H1(U1) = 1%g.
    rewrite subsetI quotientS //=.
    by apply: quotient_cents; rewrite // centsC // -quotient_sub1.
  have defH1 : ('C_H1(U1) \x [~: H1, U1] = H1)%g. 
    rewrite dprodC.
    apply: coprime_abelian_cent_dprod (der_abelian _ _).
      by apply: quotient_norms; case/sdprodP: defHU.
    apply: coprime_morph.
    by apply: coprimegS (joing_subl U W1) (Ptype_Fcore_coprime MtypeP).
  have defHU1 : ('C_H1(U1) \x  ([~: H1, U1] <*> U1) = HU1)%g.
    have/dprodP[_ _ cH1U1sC tCicH1U1] := defH1.
    rewrite /HU1 -(sdprodWY defHU) quotientY //= -[X in _ = X <*> _]defH1.
    rewrite  !dprodEY ?joingA //.
      by rewrite join_subG [X in _ && X]centsC subsetIr andbT.
    apply/trivgP; rewrite /= norm_joinEr.
    move/setIidPl: (subsetIl H1 'C(U1))<-.
    rewrite -[_ :&: H1 :&: _]setIA [_ :&: (_ * _)%g]setIC -group_modl.
    rewrite -quotientIG ?der_sub // [U :&: _]setIC tHiU.
    - by rewrite quotient1 mulg1 tCicH1U1.
    - by rewrite /= -quotientR ?quotientS.
    apply: normsR (normG _).
    by apply: subset_trans (quotientS _ _) (quotient_norm _ _).
  suff: ('C_H1(U1) == 'C_H1(U1)^`(1))%g.
    rewrite eq_sym eqEproper=> /andP[_ NP].
    apply/eqP; apply: contraR NP=> Ntriv.
    apply: (sol_der1_proper (quotient_sol _ (nilpotent_sol nH)))=> //.
    by apply: subsetIl.
  have {1}<- : ('C_H1(U1) :&: HU1^`(1) = 'C_H1(U1))%g.
    rewrite -quotient_der; last by rewrite -HeU mul_subG.
    rewrite [(HU^`(1))%g]derM2_HC .
    apply/setIidPl/(subset_trans (subsetIl _ _)).
    apply: quotientS; case/dprodP: defHC=> _ <- _ _.
    by apply: mulG_subl.
  rewrite -(der_dprod 1 defHU1).
  have/dprodP[_ _ CHH1 tHH1] := (der_dprod 1 defHU1).
  rewrite dprodE // setIC -group_modl ?der_sub //= -/U1 -/H1.
  suff-> : (([~: H1, U1] <*> U1)^`(1) :&: 'C_H1(U1) = 1)%g by rewrite mulg1.
  rewrite setIC; apply/trivgP.
  case/dprodP: defHU1 => _ _ _ /trivgP/(subset_trans _)->//.
  by rewrite setIS // der_sub.
(* C = U' *)
apply/eqP; rewrite eqEsubset andbC.
rewrite subsetI der_sub; have[_ [->/= _] _ _] := typeP_context MtypeP.
have/subset_trans->// : C \subset (M^`(2) :&: U)%g.
  rewrite derM2_HC -(dprodW defHC) setIC -group_modr ?subsetIl // setIC.
  by rewrite tHiU mul1g.
have-> : (U^`(1) = (H <*> U^`(1)) :&: U)%g.
  rewrite norm_joinEr; last by apply: (subset_trans (der_sub _ _)).
  by rewrite setIC -group_modr ?der_sub // setIC tHiU mul1g.
apply: setSI.
have-> : (M^`(2))%g = [~: HU, HU] by done.
rewrite -{1}HeU commMG; last by apply: normsRr.
rewrite -HeU commGC [[~: U, _]]commGC !commMG; last 2 first.
- by apply: normsRr.
- by apply: char_norm_trans (der_char 1 _) _.
rewrite [[~: U, _]]commGC mulgA !mul_subG //;
  try by apply: subset_trans (joing_subl _ _); rewrite ?(der_sub 1). 
by exact: joing_subr.
Qed.

(* This is Peterfalvi (11.7). *)
(* We revert to the proof of the original Odd Order paper, using the fact     *)
(* that H / Q is extra special in the typeP_Galois case.                      *)
Lemma FTtype34_Fcore_kernel_trivial :
  [/\ p.-abelem H, #|H| = (p ^ q)%N & `H0 = 1%g].
Proof.
have [not_cHbarU _ oHbar] := Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
rewrite def_Ptype_factor_prime // -/p -/q in oHbar.
suffices H0_1 : `H0 = 1%g.
  rewrite (isog_abelem (quotient1_isog H)) (card_isog (quotient1_isog H)).
  by rewrite /= -H0_1.
have [_ sUHU _ nHU tiHU] := sdprod_context defHU.
have sUM : U \subset M := subset_trans sUHU (der_sub 1 M).
have/andP[/maxgroupp/andP[_ nH0M _]] := chiefH0.
have nH0U : U \subset 'N(H0) := subset_trans sUM nH0M.
apply: contraNeq not_cHbarU => ntH0; rewrite [Ptype_Fcompl_kernel _]unlock.
rewrite (sameP eqP setIidPl) sub_astabQ nH0U /= centsC.
set Ubar := (U / H0)%g; set Hbar := (H / H0)%g.
have [pH cH0U der1H _] := Mtype34_facts.
have{ntH0} [_ _ [r oH0]] := pgroup_pdiv (pgroupS sH0H pH) ntH0.
have /(normal_pgroup pH nsH0H)[Q [sQH0 nsQH oQ]] : (r <= logn p #|H0|)%N.
  by rewrite oH0 pfactorK ?leqW.
have nQU : U \subset 'N(Q) by rewrite cents_norm ?(centsS sQH0).
have nsQH0 : Q <| H0 := normalS sQH0 sH0H nsQH.
pose Hhat := (H / Q)%g; pose H0hat := (H0 / Q)%g.
have oH0hat : #|H0hat| = p.
  by rewrite -divg_normal // oH0 oQ expnS mulnK // expn_gt0 cardG_gt0.
have der1Hhat : Hhat^`(1)%g = H0hat.
  by rewrite -quotient_der -?der1H ?normal_norm.
have ntH0hat : H0hat != 1%g by rewrite -cardG_gt1 oH0hat prime_gt1.
have ab'Hhat : ~~ abelian Hhat by rewrite (sameP derG1P eqP) der1Hhat.
have pHhat : p.-group Hhat by rewrite quotient_pgroup.
have nsH0Hhat : H0hat <| Hhat by apply: quotient_normal.
have sH0hatZ : H0hat \subset 'Z(Hhat).
  by rewrite prime_meetG ?oH0hat // meet_center_nil ?(pgroup_nil pHhat).
have [f injf imf] := third_isom sQH0 nsQH nsH0H.
have fHhat : f @* (Hhat / H0hat)%g = Hbar by rewrite imf.
have gal'M : ~~ typeP_Galois MtypeP.
  rewrite /typeP_Galois acts_irrQ //; have : ~~ odd q.+1 by rewrite /= mFT_odd.
  apply: contra => /mingroupP[_ minUHbar].
  have -> : q.+1 = logn p #|Hhat|.
    rewrite card_quotient ?normal_norm // -(Lagrange_index sH0H sQH0).
    by rewrite -!card_quotient ?normal_norm // oHbar oH0hat -expnSr pfactorK.
  suffices /(card_extraspecial pHhat)[n _ ->] : extraspecial Hhat.
    by rewrite pfactorK //= odd_double.
  suffices ZHhat : 'Z(Hhat) = H0hat.
    do 2?split; rewrite ZHhat ?oH0hat //.
    apply/eqP; rewrite eqEsubset (Phi_min pHhat) ?normal_norm //=; last first.
      by rewrite -(injm_abelem injf) ?fHhat.
    by rewrite (Phi_joing pHhat) der1Hhat joing_subl.
  have sZHhat : 'Z(Hhat) \subset Hhat := center_sub _.
  have nsH0hatZ := normalS sH0hatZ sZHhat nsH0Hhat.
  apply: contraNeq ab'Hhat; rewrite eqEsubset sH0hatZ andbT => not_esHhat.
  apply/center_idP/(quotient_inj nsH0hatZ)=> //.
  apply: (injm_morphim_inj injf); rewrite ?quotientS // fHhat.
  rewrite minUHbar //= -/Hbar -?fHhat 1?morphim_injm_eq1 ?morphimS // -subG1.
  rewrite quotient_sub1 ?(normal_norm nsH0hatZ) // not_esHhat -['Z(_)]cosetpreK.
  rewrite imf ?sub_cosetpre_quo ?quotient_norms ?norm_quotient_pre //.
  by rewrite (char_norm_trans (center_char _)) ?quotient_norms.
have [H1 []] := typeP_Galois_Pn maxM Mtypen5 gal'M.
rewrite def_Ptype_factor_prime //= -/p -/Hbar -/Ubar => oH1 nH1U _ defHbar _.
have /cyclicP[xbar defH1] : cyclic H1 by rewrite prime_cyclic ?oH1.
have H1xbar : xbar \in H1 by rewrite defH1 cycle_id.
have Hxbar : xbar \in Hbar.
  rewrite -cycle_subG -defH1 -(bigdprodWY defHbar) (bigD1 1%g) ?group1 //=.
  by rewrite conjsg1 joing_subl.
have /morphimP[x nH0x Hx /= Dx] := Hxbar.
have oxbar : #[xbar] = p by rewrite orderE -defH1.
have [phi Dphi] : {phi : {morphism Ubar >-> {unit 'F_p}} |
    {in Ubar, forall u, xbar ^ u = xbar ^+ val (phi u)}%g}.
- have injAxbar := injm_Zp_unitm xbar.
  have /restrmP[phi [Dphi]] : Ubar \subset 'dom (invm injAxbar \o conj_aut H1).
    by rewrite -sub_morphim_pre //= im_Zp_unitm -defH1 Aut_conj_aut.
  rewrite pdiv_id // -oxbar; exists phi => u /(subsetP nH1U) nH1u.
  transitivity (Zp_unitm (phi u) xbar); last by rewrite autE ?cycle_id.
  by rewrite Dphi invmK ?im_Zp_unitm -?defH1 ?Aut_aut ?norm_conj_autE.
have /mulG_sub[_ sW1M] := sdprodW defM.
have nUW1 : W1 \subset 'N(U) by have [_ []] := MtypeP.
have nHW1 : W1 \subset 'N(H) := subset_trans sW1M (gFnorm _ M).
have sxW1_H : x ^: W1 \subset H by rewrite class_sub_norm.
have defHhat : Hhat = (H0hat * <<x ^: W1 / Q>>)%g.
  apply/eqP; rewrite eqEsubset mulG_subG gen_subG !quotientS //= andbT.
  rewrite -quotient_gen ?(subset_trans sxW1_H) ?normal_norm //.
  rewrite -quotientSK ?normal_norm // -(injmSK injf) ?imf // ?gen_subG //.
  rewrite -(bigdprodWY defHbar) // gen_subG.
  apply/bigcupsP=> _ /morphimP[w nH0w W1w ->]; rewrite defH1 Dx.
  rewrite -quotient_cycle // -quotientJ // -cycleJ quotientS ?genS // sub1set.
  by rewrite mem_orbit.
apply: contraR ab'Hhat => not_cUHbar.
rewrite defHhat abelianM andbCA centsC -subsetI -centM -defHhat abelian_gen.
have [_ cHbarH0] := subsetIP sH0hatZ; rewrite cHbarH0 andbT.
apply/centsP=> _ /morphimP[x1 nQx1 xWx1 ->] _ /morphimP[x2 nQx2 xWx2 ->].
apply/commgP; rewrite -morphR //=.
have [Hx1 Hx2] : x1 \in H /\ x2 \in H by rewrite !(subsetP sxW1_H).
have [[w1 Ww1 Dx1] [w2 Ww2 Dx2]] := (imsetP xWx1, imsetP xWx2).
pose Jv_ u w := (u ^ (coset H0 w)^-1)%g.
have U_Jv : {in Ubar & W1, forall u w, Jv_ u w \in Ubar}%g.
  move=> u w Uu W1w; rewrite /= memJ_norm // groupV.
  by rewrite (subsetP (quotient_norms H0 nUW1)) ?mem_quotient.
pose x_ w := (xbar ^ coset H0 w)%g; pose phi_ w u := phi (Jv_ u w).
have Dphi_ w u : w \in W1 -> u \in Ubar -> (x_ w ^ u = x_ w ^+ val (phi_ w u))%g.
  by move=> Ww Uu; rewrite -conjgM conjgCV conjgM Dphi ?U_Jv // conjXg.
pose Qr y z := coset Q [~ y, z]; apply: contraR not_cUHbar => Qr12_neq1.
have phi12_id u : u \in Ubar -> (phi_ w1 u * phi_ w2 u = 1)%g.
  move=> Uu; have [u0 nH0u0 Uu0 Du] := morphimP Uu.
  have H0r : {in H &, forall z1 z2, [~ z1, z2] \in H0}.
    by rewrite der1H; apply: mem_commg.
  have{Qr12_neq1} oQr12 : #[Qr x1 x2] = p.
    apply/prime_nt_dvdP; rewrite ?order_eq1 // -oH0hat ?order_dvdG //.
    by rewrite mem_quotient ?H0r.
  have [[_ /subsetP nQH] [_ /subsetP nH0H]] := (andP nsQH, andP nsH0H).
  have QrC : {in H &, forall y1 y2, Qr y1 y2 = (Qr y2 y1)^-1}%g.
    by move=> y1 y2 Hy1 Hy2; rewrite /= -morphV ?invg_comm // nQH // groupR.
  have Qr_u0 y1 w (y2 := (x ^ w)%g) : y1 \in H -> y2 \in H -> w \in W1 -> 
    (Qr y1 (y2 ^ u0) = Qr y1 y2 ^+ val (phi_ w u))%g.
  - move=> Hy1 Hy2 Ww; set n : nat := val (phi_ w u).
    have nH0w := subsetP (subset_trans sW1M nH0M) w Ww.
    have: coset H0 (y2 ^ u0) = (coset H0 (y2 ^+ n))%g.
      by rewrite morphX ?morphJ // ?nH0H //= -Du -Dx -Dphi_.
    case/kercoset_rcoset=> [||z H0z ->]; rewrite ?nH0H ?groupX //.
      by rewrite memJ_norm // (subsetP nHU).
    rewrite /Qr !morphR 1?morphM ?nQH // ?groupM ?groupX // ?(subsetP sH0H) //=.
    have cQy1z : [~ coset Q y1, coset Q z] = 1%g.
      by apply/eqP/commgP/esym/(centsP cHbarH0); apply: mem_quotient.
    rewrite commgMJ cQy1z conj1g mulg1 morphX ?nQH // commgX //.
    by apply/esym/(centsP cHbarH0); rewrite -?morphR ?nQH ?mem_quotient ?H0r.
  apply/eqP; rewrite -!val_eqE /= [d in _ == _ %[mod d]]Fp_cast //.
  rewrite -[d in _ == _ %[mod d]]oQr12 -eq_expg_mod_order mulnC expgM.
  have Hx2u : (x2 ^ u0)%g \in H by rewrite ?memJ_norm ?(subsetP nHU).
  rewrite Dx2 -Qr_u0 -?Dx2 // !(QrC x1) // expgVn Dx1 -Qr_u0 -?Dx1 //.
  apply/eqP; congr (coset Q _)^-1%g; rewrite -conjRg /conjg.
  by rewrite -(centsP cH0U _ Uu0) ?mulKg ?H0r.
pose w := coset H0 (w1 * w2 ^-1)%g.
have Ww : w \in (W1 / H0)%g by rewrite mem_quotient ?groupM ?groupV.
have{phi12_id} phi_w : {in Ubar, forall u, phi (u ^ w) = (phi u)^-1}%g.
  have /subsetP nH0W1 := subset_trans sW1M nH0M.
  move=> u Uu; apply/esym/eqP.
  rewrite eq_invg_mul [w]morphM ?morphV ?nH0W1 ?groupV // conjgM /=.
  rewrite -{1}[u](conjgK (coset H0 w1)) phi12_id //.
  by rewrite -[w1]invgK morphV ?nH0W1 ?U_Jv ?groupV.
have{w phi_w Ww} phiV : {in Ubar, forall u, phi u = (phi u)^-1}%g.
  have coW12 : coprime #|W1 / H0|%g 2 by rewrite coprimen2 quotient_odd ?mFT_odd.
  move=> u Uu; rewrite /= -phi_w // -(expgK coW12 Ww) -expgM mul2n.
  elim: (expg_invn _ _) => [|n IHn]; rewrite ?conjg1 //.
  have nUw := subsetP (quotient_norms _ nUW1) w Ww.
  by do 2!rewrite expgSr conjgM phi_w ?memJ_norm ?groupX // ?invgK.
rewrite -[Hbar](bigdprodWY defHbar) gen_subG defH1.
apply/bigcupsP=> _ /morphimP[w _ Ww ->]; rewrite -cycleJ cycle_subG -/(x_ w).
apply/centP=> u Uu; apply/commgP/conjg_fixP; rewrite Dphi_ // /phi_.
move: {u Uu Ww}(Jv_ u w) (U_Jv u w Uu Ww) => u Uu.
suffices -> : phi u = 1%g by [].
have coU2 : coprime #|Ubar| 2 by rewrite coprimen2 quotient_odd ?mFT_odd.
by rewrite -(expgK coU2 Uu) morphX ?groupX // morphM // {1}phiV // mulVg expg1n.
Qed.

Let pddM := FT_prDade_hyp maxM MtypeP.
Let ptiWM : primeTI_hypothesis M HU defW := FT_primeTI_hyp MtypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddM.
Let ctiWM : cyclicTI_hypothesis M defW := prime_cycTIhyp ptiWM.

Local Notation sigma := (cyclicTIiso ctiWG).
Local Notation w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).
Local Notation mu_ := (primeTIred ptiWM).
Local Notation Idelta := (primeTI_Isign ptiWM).
Local Notation delta_ j := (primeTIsign ptiWM j).
Local Notation d := (FTtype345_TIirr_degree MtypeP).
Local Notation n := (FTtype345_ratio MtypeP).
Local Notation delta := (FTtype345_TIsign MtypeP).

Let mu2_ i j := primeTIirr ptiWM i j.

Let codom_sigma := map sigma (irr W).
Let ntW1 : (W1 :!=: 1)%g. Proof. by have [[]] := MtypeP. Qed.
Let ntW2 : (W2 :!=: 1)%g. Proof. by have [_ _ _ []] := MtypeP. Qed.

Let sHHU : H \subset HU.
Proof. by have [_ _ /mulG_sub[]] := sdprod_context defHU. Qed.
Let sUHU : U \subset HU.
Proof. by have [_ _ /mulG_sub[]] := sdprod_context defHU. Qed.
Let sHC_HU : (HC \subset HU)%g.
Proof.  by rewrite join_subG sHHU subIset // sUHU. Qed.
Let sHUM : HU \subset M.
Proof. by have [_ _ /mulG_sub[]] := sdprod_context defM. Qed.
Let nsHC_HU : HC <| HU.
Proof.
have [_ nsHC_M _] := normal_hyps.
by exact: normalS sHC_HU sHUM nsHC_M.
Qed.
Let nsCU : C <| U.
Proof.  by apply: normalS (subsetIl _ _) (subset_trans _ sHUM) nsCM. Qed.

Let frobMbar : [Frobenius M / HC = (HU / HC) ><| (W1 / HC)].
Proof.
have [[_ hallW1 _ _] _ _ [_ _ _ sW2M'' regM'W1 ] _] := MtypeP.
have [_ nsHC_M _] := normal_hyps.
apply: Frobenius_coprime_quotient => //.
  by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP.
split=> [|w /regM'W1-> //]; rewrite -derM2_HC //.
apply: (sol_der1_proper (mmax_sol maxM)) => //.
by apply: subG1_contra ntW2; apply: subset_trans sW2M'' (der_sub 1 HU).
Qed.

Let cW1 : cyclic W1. Proof. by have [[]] := MtypeP. Qed.
Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let  NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.

Let cW2 : cyclic W2. Proof. by have [_ _  _ []] := MtypeP. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let  NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel MtypeP :=: C.
Proof.
have [_ _ H0_1] := FTtype34_Fcore_kernel_trivial.
rewrite [Ptype_Fcompl_kernel MtypeP]unlock /= (group_inj H0_1).
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.

Let AUC : abelian (U / C).
Proof. by apply: sub_der1_abelian; have[_ _ _ <-] := Mtype34_facts. Qed.

Let SHC1 : {in S_ HC, forall xi : 'CF(M), xi 1%g = q%:R}.
Proof.
move=> _ /seqIndP[s /setDP[kerH' _] ->]; rewrite !inE in kerH'.
rewrite cfInd1 // -(index_sdprod defM) lin_char1 ?mulr1 // lin_irr_der1.
rewrite (subset_trans _ kerH') // der1_min //; first by case/andP: nsHC_HU.
suff/isog_abelian-> : (HU / HC)%g \isog (U / C)%g by [].
by rewrite isog_sym quotient_sdprodr_isog.
Qed.

Let sub_co_SHC_tau : subcoherent (S_ HC) tau R.
Proof.  apply: (subset_subcoherent subc_M); exact: seqInd_conjC_subset1. Qed.
Let co_SHC_tau : coherent (S_ HC) M^# tau.
Proof.
apply: uniform_degree_coherence sub_co_SHC_tau _.
apply/(@all_pred1_constant _ q%:R)/allP=> c /mapP[c1 c1IS1 ->].
by rewrite /= SHC1.
Qed.

Let defA1 : 'A1(M) = HU^#. Proof. by rewrite /= -FTcore_eq_der1. Qed.
Let defA : 'A(M) = HU^#. Proof. by rewrite FTsupp_eq1 ?defA1. Qed.
Notation V := (class_support  (cyclicTIset defW) M).
Let defA0 : 'A0(M) = HU^# :|: V.
Proof. by rewrite -defA (FTtypeP_supp0_def _ MtypeP). Qed.

Let SHC_irr : {subset (S_ HC) <= irr M}.
Proof.
have [_ nsHC_M _] := normal_hyps.
move=> _ /seqIndP[s /setDP[kerHC kerHU] ->]; rewrite !inE in kerHC kerHU.
rewrite -(quo_IirrK _ kerHC) // mod_IirrE // cfIndMod // cfMod_irr //.
rewrite (irr_induced_Frobenius_ker (FrobeniusWker frobMbar)) //.
by rewrite quo_Iirr_eq0 // -subGcfker.
Qed.

Let cfdot_SHC :  {in S_ HC &, forall phi psi, '[phi, psi] = (phi == psi)%:R}.
Proof.
have := sub_orthonormal SHC_irr (seqInd_uniq _ _) (irr_orthonormal _).
by case/orthonormalP.
Qed.

Let omu2 i j (z : 'CF(M)) (SHCz : z \in S_ HC) :  '[mu2_ i j, z] = 0.
Proof.
case/seqIndP: SHCz (SHC_irr SHCz)  => s _ -> Iind.
rewrite -cfdot_Res_l cfRes_prTIirr  cfdot_irr.
rewrite (negPf (contraNneq _ (prTIred_not_irr ptiWM j))) // => Ds.
by rewrite -cfInd_prTIres Ds.
Qed.

Let omu j (z : 'CF(M)) (SHCz : z \in S_ HC) :  '[mu_ j, z] = 0.
Proof. by rewrite cfdot_suml big1 // => i _; rewrite omu2. Qed.

Let cf_mu0Bz (z : 'CF(M)) (SHCz : z \in S_ HC) : mu_ 0 - z \in 'CF(M, 'A0(M)).
Proof.
apply: (cfun_onS (subsetUl _ _)).
rewrite [mu_ 0]prTIred0 defA cfun_onD1 !cfunE [z _]SHC1 //.
rewrite cfuniE // group1 mulr1 subrr rpredB ?rpredZ ?cfuni_on //=.
by have /seqInd_on-> := SHCz.
Qed.

(* This is 11.8.4 *)
Let ex_co_w_SHC_tau (z : 'CF(_)) (SHCz : z \in S_ HC) :
 orthogonal (tau (mu_ 0 - z) - \sum_i eta_ i 0) codom_sigma ->
 exists2 tau1, coherent_with (S_ HC) M^# tau tau1 & 
               tau (mu_ 0 - z) = \sum_i eta_ i 0 - tau1 z.
Proof.
move: (SHCz); have /irrP[iz {z SHCz}->SHCz otauS] := SHC_irr SHCz.
pose z := 'chi_iz.
have[tau1 co_w_SHC_tau] := co_SHC_tau.
have [[Ztau1 Ptau1] Ctau1] := co_w_SHC_tau.
pose chi : 'CF(G) := \sum_i eta_ i 0 - tau (mu_ 0 - z).
have chiE : tau (mu_ 0 - z) = \sum_i eta_ i 0 - chi.
  by rewrite opprB [X in _ = X]addrC subrK.
have [chiEz|chiDz] := (chi =P tau1 z).
  by exists tau1; rewrite -?chiEz //.
have dirrChi : chi \in dirr G.
  apply: dirr_norm1.
    rewrite rpredB ?Dade_vchar ?rpred_sum 1?zchar_split // => [i _|].
      by apply: cycTIiso_vchar.
    by rewrite  cf_mu0Bz // rpredB ?char_vchar ?prTIred_char ?irr_char.
  have: '[tau (mu_ 0 - z)] = q%:R + 1.
    rewrite Dade_isometry ?cf_mu0Bz // (cfnormBd (omu _ _)) //. 
    by rewrite cfnorm_prTIred cfdot_SHC // eqxx.
  pose etaW := map sigma (irr W).
  have /orthonormalP[_ cfeta] := cycTIiso_orthonormal ctiWG.
  rewrite chiE cfnormDd ?cfnormN ?cfdotNr ?cfdot_suml.
    rewrite (eq_bigr (fun i => 1%:R))=> [|i _].
      by rewrite sumr_const  nirrW1 -mulr_natl mulr1 // => /addrI.
    rewrite (bigD1 i) //= cfdotDr cfdot_sumr big1 ?addr0 // => [|i1 Dii1].
      by rewrite cfeta ?eqxx ?map_f ?mem_irr.
    by rewrite cfeta ?map_f ?mem_irr // cycTIiso_eqE eq_sym (negPf Dii1).
  rewrite -sumrN big1 // => i _; rewrite -cfdotNr opprB cfdotC.
  have /orthogonalP->// := otauS; rewrite ?conjC0 ?inE //.
  by apply: map_f (mem_irr _).
have SHC_dirr : {in S_ HC, forall l, tau1 l \in dirr G}.
  move=> l LiS1; rewrite /= dirrE Ztau1 ?Ptau1 ?mem_zchar //=.
  by rewrite cfdot_SHC // eqxx.
have cfdot_tau1B :
       {in S_ HC, forall z1 : 'CF(_), '[tau1 z - tau1 z1 , chi] = (z != z1)%:R}.
  move=> z1 SHCz1; rewrite /= cfdotBr cfdot_sumr big1 ?add0r => [|i _].
    rewrite -raddfB /= Ctau1 ?Dade_isometry ?cf_mu0Bz //.
    - rewrite cfdotBl !cfdotBr cfdotC omu // conjC0 sub0r.
      rewrite cfdot_SHC //= eqxx cfdotC omu // conjC0 sub0r.
      rewrite cfdot_SHC // eq_sym; case: (_ == _); first by rewrite addrN oppr0.
      by rewrite oppr0 subr0 opprK.
    - apply: cfun_onS (subsetUl _ _) _.
      rewrite defA cfun_onD1 rpredB //; last by apply: seqInd_on SHCz1.
        by rewrite !cfunE !SHC1 // addrN /=.
      by apply: seqInd_on SHCz.
    rewrite zchar_split rpredB ?mem_zchar // cfunD1E.
    by rewrite !cfunE !SHC1 // addrN /=.
  pose o_co := coherent_ortho_cycTIiso _ _ co_w_SHC_tau.
  by rewrite cfdotBl !o_co ?subr0 ?SHC_irr //; 
     apply: seqInd_conjC_subset1; rewrite -?defMs.
have [//|chiNE] : chi = tau1 z \/ chi = -tau1 z^*%CF.
  apply: cfdot_add_dirr_eq1; rewrite ?rpredN ?SHC_dirr ?cfAut_seqInd //.
  rewrite cfdot_tau1B ?cfAut_seqInd //.
  by rewrite eq_sym (seqInd_conjC_neq _ _ _ SHCz) ?mFT_odd.
case: (leqP (size (S_ HC)) 2)=> [S1le2|S1gt2].
  exists (dual_iso tau1); first by apply: dual_coherence sub_co_SHC_tau _ _.
  by rewrite /= -chiNE.
pose S1 := rem z^*%CF (rem z (S_ HC)); pose x := S1`_0.
have [SHCx xDz xDzC] : [/\ x \in S_ HC, x != z & x != z^*%CF].
  have uSHC : uniq (S_ HC) := seqInd_uniq _ _.
  suff S1x : x \in S1.
    move: (S1x); rewrite /S1 !rem_filter ?filter_uniq //.
    rewrite !mem_filter //= => /andP[xDzC /andP[xDz _]].
    split=> //; apply: mem_rem (mem_rem S1x).
  rewrite mem_nth // !size_rem //; first by case: size S1gt2 => // [[|[]]].
  rewrite mem_rem_uniq // !inE.
  by rewrite (seqInd_conjC_neq _ _ _ SHCz) ?mFT_odd // cfAut_seqInd.
have [//|] : chi = tau1 z \/ chi = - tau1 x^*%CF.
  apply: cfdot_add_dirr_eq1; rewrite ?rpredN ?SHC_dirr ?cfAut_seqInd //.
  rewrite cfdot_tau1B ?cfAut_seqInd //.
  by case: eqP=> // zExC; case/eqP: xDzC; rewrite zExC cfConjCK.
rewrite chiNE=> NTE; case/eqP: xDz.
apply/(can_inj (@cfConjCK _ _))/(Zisometry_inj Ztau1 _ _).
- by apply/mem_zchar/cfAut_seqInd.
- by apply/mem_zchar/cfAut_seqInd.
by apply: oppr_inj.
Qed.

Let SC := seqIndD HU M HC C.
Let SHCdSC : {subset S_ HC <= [predC SC]}.
Proof.  
have [_ nsHCM _] := normal_hyps.
move=> s /seqIndP[] i; rewrite inE => /andP[_ iIk] ->.
by rewrite inE /= mem_seqInd // inE negb_and negbK iIk.
Qed.

Let Smu := [seq mu_ j | j in predC1 0].
Let Smu_nirr : {subset Smu <= [predC irr M]}.
Proof. by move=> _ /imageP[k _ ->]; apply: (prTIred_not_irr pddM). Qed.

Let S1nirr := filter [predC irr M] (seqIndD HU M H H0).
Let S1nirr_i_Smu : S1nirr =i Smu.
Proof.
have [szS1nirr _ S1nirr_s_Smu S1nirr_facts] := 
     typeP_reducible_core_Ind maxM MtypeP Mtypen5.
have uS1nirr : uniq S1nirr by apply: filter_uniq (seqInd_uniq _ _).
have szSmu : size Smu = p.-1.
  by rewrite size_map -cardE cardC1 card_Iirr_abelian ?cyclic_abelian.
have []// := leq_size_perm uS1nirr S1nirr_s_Smu.
have [_ cH H0_1] := FTtype34_Fcore_kernel_trivial.
rewrite szS1nirr szSmu H0_1 -(card_isog (quotient1_isog _)) cH.
by case: q pr_q => // q1 _; rewrite pdiv_pfactor.
Qed.

Let u := #|(U/C)%g|.
Let mu1 j (nz_j : j != 0) : mu_ j 1%g = (q * u)%:R.
Proof.
have [szS4 _ S4sS3 pS4] := typeP_reducible_core_Ind maxM MtypeP Mtypen5.
have /(pS4 _)[-> _ _] : mu_ j \in S1nirr 
  by rewrite S1nirr_i_Smu map_f // mem_enum.
by rewrite (group_inj Ptype_Fcompl_kernel_cent).
Qed.

Let Smu_i_SCnirr : Smu =i filter [predC irr M] SC.
Proof.
move=> mu_k.
have [szS1nirr _ S1nirr_s_Smu S1nirr_facts] := 
     typeP_reducible_core_Ind maxM MtypeP Mtypen5.
rewrite -S1nirr_i_Smu /SC -(_ : (C <*> H)%G = HC) ?seqIndDY //=; last first.
  by apply/group_inj/dprodWY; rewrite -defHC dprodC.
apply/idP/idP=> [kIS4|].
  move: (kIS4); rewrite !mem_filter => /andP[-> _] /=.
  have/(S1nirr_facts _)[_] := kIS4.
  have [_ _ ->] := FTtype34_Fcore_kernel_trivial .
  by rewrite (group_inj (joing1G _)) (group_inj Ptype_Fcompl_kernel_cent).
rewrite !mem_filter !inE; case: (_ \in _)=> //=.
have [_ _ /group_inj->] := FTtype34_Fcore_kernel_trivial .
by apply: seqIndS (Iirr_kerDS _ (sub1G _) _) _.
Qed.

Notation "#1" := (inord 1).

Let coUq : coprime #|U| q.
Proof.
have /sdprod_context[_ /coprimeSg->//] := defHU.
by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP.
Qed.
	
Let nC_UW1 : U <*> W1 \subset 'N(C).
Proof.
have /sdprodP[_ _ nPUW1 _] := Ptype_Fcore_sdprod MtypeP.
by rewrite normsI ?norms_cent // join_subG normG; have [_ []] := MtypeP.
Qed.

Let FrobUW1QC : [Frobenius U <*> W1 / C = (U / C) ><| (W1 / C)].
Proof.
have [_ _ _ defC] := Mtype34_facts.
have FrobUW1 : [Frobenius U <*> W1 = U ><| W1].
  by exact: Ptype_compl_Frobenius MtypeP _.
have [defUW1 _ _ _ _] := Frobenius_context FrobUW1.
rewrite Frobenius_coprime_quotient // /normal ?subIset ?joing_subl //.
split=> [|x /(Frobenius_reg_ker FrobUW1)->]; last exact: sub1G.
have /Frobenius_context[ _ UnT _ _ _] := FrobUW1.
rewrite /= defC (sol_der1_proper  (of_typeP_sol MtypeP)) //.
have /sdprodP [_ <- _ _] := defM; have /sdprodP [_ <- _ _] := defHU.
by exact: subset_trans (mulG_subr _ _) (mulG_subl _ _).
Qed.

(* This is PF (11.8). *)
Lemma FTtype34_not_ortho_cycTIiso (z : 'CF(_))  (SHCz : z \in S_ HC) : 
  ~~ orthogonal (tau (mu_ 0 - z) - \sum_i eta_ i 0) codom_sigma.
Proof.
move: (SHCz); have /irrP[iz->] := SHC_irr SHCz=> {z SHCz}SHCz.
set z := 'chi_iz.
apply/negP=> otauS.
have u_gt0 : (u > 0)%N by exact: cardG_gt0.
have q_gt2 : (q > 2)%N by rewrite odd_gt2 ?mFT_odd ?cardG_gt1.
have size_SHC_q : (size (S_ HC) * q = u - 1)%N.
  pose X_ (S0 : seq 'CF(M)) := [set s | 'Ind[M, HU] 'chi_s \in S0].
  pose sumX_ cS0 := \sum_(s in X_ cS0) 'chi_s 1%g ^+ 2.
  have defX_SHC : X_ (S_ HC) = Iirr_kerD HU HU HC.
    have [_ nsHC_M _] := normal_hyps.
    by apply/setP=> s; rewrite !inE mem_seqInd // !inE.
  have defX : X_ (S_ 1) = Iirr_kerD HU HU 1%g.
    by apply/setP=> s; rewrite !inE mem_seqInd ?normal1 //= !inE.
  have sumX1 : sumX_ (S_ HC) = u%:R - 1.
    rewrite /sumX_ defX_SHC sum_Iirr_kerD_square // indexgg mul1r.
    by rewrite /u -!divgS // ?subsetIl // -(sdprod_card defHU) 
               -(dprod_card defHC) divnMl // divg_normal.
  apply/eqP; rewrite -eqC_nat mulnC [q](index_sdprod defM).
  rewrite (size_irr_subseq_seqInd _ (subseq_refl (S_ HC))) //.
  rewrite natrB ?cardG_gt0 // -sumr_const -sumX1.
  apply/eqP/esym/eq_bigr => s.
  rewrite defX_SHC !inE -derM2_HC -lin_irr_der1 => /and3P[_ _ /eqP->].
  by rewrite expr1n.
have nz_1j : #1 != 0 :> Iirr W2 by rewrite Iirr1_neq0.
(* First part of 11.8.1 *)
have Edu : d = u.
  apply/eqP; move/eqP: (mu1 nz_1j).
  rewrite /primeTIred  sum_cfunE (eq_bigr (fun i => d%:R))=> [|i _]; last first.
    by have [->] := FTtype345_constants maxM MtypeP Mtypen2.
  rewrite sumr_const card_ord NirrW1 -mulr_natl -natrM eqC_nat eqn_pmul2l //.
  by exact: prime_gt0.
(* Second part of 11.8.1 *)
have Ed1 : delta = 1.
  suffices: (1 == delta %[mod q])%C.
    rewrite [delta]signrE /eqCmod addrC opprB subrK dvdC_nat.
    by case: (Idelta #1); rewrite ?subr0 // gtnNdvd.
  apply: eqCmod_trans (prTIirr1_mod ptiWM 0 #1); rewrite -/(mu2_ 0 #1) -/q.
  have [-> // _ _ _] := FTtype345_constants maxM MtypeP Mtypen2.
  rewrite Edu eqCmod_sym /eqCmod -(@natrB _ u 1) ?indexg_gt0 // subn1 dvdC_nat.
  have /Frobenius_dvd_ker1 := FrobUW1QC.
  have [nCU nCW1] := joing_subP nC_UW1; rewrite !card_quotient // -/u.
  by rewrite -indexgI setIC setIAC (coprime_TIg coUq) setI1g indexg1 -card_quotient.
(* Third part of 11.8.1 *)
have En : n = (size (S_ HC))%:R.
  rewrite /FTtype345_ratio Edu Ed1 -/q -(@natrB _  _ 1 %N) // -size_SHC_q.
  by rewrite natrM mulfK // (eqC_nat _ 0); case: q pr_q.
pose alpha_ := FTtype345_bridge MtypeP iz.
have alphaE i j :  alpha_ i j = mu2_ i j - delta *: mu2_ i 0 - n *: z by [].
have S1z : z \in S_ 1 by apply: seqInd_sub SHCz.
have cf_alpha i j (nz_j : j != 0 ) : alpha_ i j \in 'CF(M, 'A0(M)).
  by rewrite supp_FTtype345_bridge // SHC1.
have cfdot_alpha i j (z1 : 'CF(M)) (SHCz1 : z1 \in S_ HC) :  
  '[alpha_ i j, z1] = (z1 == z)%:R * -n.
  move: (SHCz1); have/irrP[iz1 ->] := SHC_irr SHCz1=> {z1 SHCz1}SHCz1.
  rewrite !cfdotBl !cfdotZl !omu2 // mulr0 !(sub0r,oppr0).
  by rewrite mulrN mulrC cfdot_irr (inj_eq irr_inj) [iz1 == _]eq_sym.
have[tau1 co_w_tau_tau1 Etau] := ex_co_w_SHC_tau SHCz otauS.
have [[Ztau1 Ptau1] Ctau1] := co_w_tau_tau1.
pose a_ i j := '[tau (alpha_ i j), tau1 z] + n.
have Za i j (nz_j : j != 0) : a_ i j \in Cint.
  have [_ _ _ Nn] := FTtype345_constants maxM MtypeP Mtypen2.
  rewrite rpredD ?(Cint_Cnat Nn) //.
  rewrite  Cint_cfdot_vchar ?Ptau1 ?(mem_zchar SHCz) //.
  by rewrite Dade_vchar // zchar_split //vchar_FTtype345_bridge ?cf_alpha.
pose X_ i j := 
  tau (alpha_ i j) + n *: tau1 z - a_ i j *: \sum_(x <- S_ HC) tau1 x.
pose Y_ i j := - (n *: tau1 z) + a_ i j *: \sum_(x <- S_ HC) tau1 x.
(* This is the first part of 11.8.2 *)
have tau_alphaE i j : tau (alpha_ i j) = X_ i j + Y_ i j. 
  by rewrite addrA addrAC subrK addrK.
have cfdot_sum_tau1 (y : 'CF(_)) (SHCy : y \in S_ HC) :
      '[\sum_(x <- S_ HC) tau1 x, tau1 y] = 1.
  rewrite cfdot_suml (bigD1_seq y) ?seqInd_uniq //=.
  rewrite big_seq_cond big1 ?addr0 => [|x /andP[SHCx xDy]]; last first.
    by rewrite Ztau1 ?mem_zchar // (seqInd_ortho _ SHCx).
  rewrite Ztau1 ?mem_zchar //.
  by have /irrP[iy ->] := SHC_irr SHCy; exact: cfnorm_irr.
have oX_tau1 i j (nz_j : j != 0) (x : 'CF(_)) (SHCx : x \in S_ HC) : 
       '[X_ i j, tau1 x] = 0.
  rewrite cfdotBl cfdotDl !cfdotZl cfdot_sum_tau1 // mulr1.
  rewrite Ztau1 ?mem_zchar //.
  case: (boolP (z == x))=> [/eqP<-|zDx].
    by rewrite cfnorm_irr !mulr1 addrN.
  rewrite (seqInd_ortho _ SHCz) // mulr0 addr0.
  rewrite -{1}[x](subrK z) [tau1 _]raddfD cfdotDr.
  rewrite -addrA -[X in  _ + X]opprB [a_ _ _]addrC addrK.
  have ZSHCxBz : x - z \in 'Z[S_ HC, M^#].
    by rewrite  zcharD1 !cfunE !SHC1 // addrN ?eqxx zchar_onG rpredB ?mem_zchar.
  have ZsHU : {subset S_ HC <= 'CF(M, HU)}.
    by move=> u2 HU; apply: (seqInd_on (der_normal 1 _) HU).
  rewrite Ctau1 // Dade_isometry ?cf_alpha //; last first.
    rewrite (cfun_onS (subsetUl _ _)) // defA.
    rewrite  cfun_onD1 rpredB ?ZsHU ?mem_zchar //.
    by rewrite !cfunE !SHC1 ?addrN ?eqxx.
  rewrite cfdotBr !cfdot_alpha // eq_sym (negPf zDx) mul0r sub0r.
  by rewrite eqxx mul1r opprK addrN.
have oXY i j  (nz_j : j != 0) : '[X_ i j, Y_ i j] = 0.
  rewrite cfdotDr cfdotNr !cfdotZr oX_tau1 // mulr0 oppr0 add0r.
  rewrite cfdot_sumr big_seq_cond big1 ?mulr0 // => x /andP[SHCx _].
  by apply: oX_tau1.
have nY i j  (nz_j : j != 0) : '[Y_ i j] = (n * a_ i j * (a_ i j - 2%:R)) + n ^+ 2.
  rewrite /Y_ cfdotDl  !cfdotDr !cfdotNl !cfdotNr !cfdotZl !cfdotZr.
  have [_ _ _ Nn] := FTtype345_constants maxM MtypeP Mtypen2.
  rewrite (conj_Cnat Nn) (conj_Cint (Za _ _ nz_j)).
  rewrite Ztau1 ?mem_zchar // cfnorm_irr mulr1 opprK.
  rewrite cfdot_sum_tau1 // mulr1 cfdotC cfdot_sum_tau1 // conjC1 mulr1.
  have-> : '[\sum_(x <- S_ HC) tau1 x] = n.
    pose f1 i := 1 *: tau1 i.
    rewrite (eq_bigr f1)=> [|j2 Jj2]; last by rewrite /f1 scale1r.
    rewrite cfnorm_sum_orthogonal //; last first.
      by apply: seqInd_orthogonal=> //; exact: der_normal.
    rewrite big_seq_cond.
    rewrite (eq_bigr (fun i => 1)) => [|x /andP[SHCx _]]; last first.
      have /irrP[i1 ->] := SHC_irr SHCx.
      by rewrite normr1 expr1n mul1r cfnorm_irr.
    rewrite -big_seq_cond /= big_const_seq.
    have: all xpredT (S_ HC) by apply/allP.
    rewrite -[n]addr0 En all_count=> /eqP->.
    elim: (size (S_ HC)) 0=> /= [x|n IH x]; first by rewrite add0r.
    by  rewrite IH /= -add1n natrD addrA.
 (* ring would be handy! *)
  rewrite mulrBr [_ * (1 + 1)]mulrDr opprD !mulr1 !addrA -expr2.
  rewrite [a_ _ _ * n]mulrC [a_ _ _ * (n * _)]mulrC.
  rewrite [X in X = _]addrC -!addrA; congr (_ + _).
  by rewrite [X in X = _]addrC !addrA.
(* This is the second part of 11.8.2 *)
have le2 i j  (nz_j : j != 0): [|| a_ i j == 0, a_ i j == 1 | a_ i j == 2%:R].
  have: n * a_ i j * (a_ i j - 2%:R) <= 2%:R.
    rewrite -(ler_add2r (n ^+2)) -nY //=.
    set XX := _ + _; have-> : XX = '[tau (alpha_ i j)].
      by rewrite norm_FTtype345_bridge // SHC1.
  by rewrite tau_alphaE cfnormDd ?oXY // ler_addr cfnorm_ge0.
  have: (0 < size (S_ HC))%N by move: SHCz; case: (S_ HC); rewrite ?inE.
  rewrite En; case: size => // ns _.
  have /CintP[x ->] := (Za i _ nz_j); case: (intP x)=> [|n1|n1].
  - by rewrite eqxx.
  - case: n1=> [|n1]; first by rewrite eqxx orbT.
    rewrite -natrB // -!natrM ler_nat !subnS subn0.
    case: n1=> [|n1]; first by rewrite eqxx orbA orbT.
    by rewrite mulnC !mulnA.
  rewrite -opprD !mulrN -mulNr opprK -natrD -!natrM ler_nat.
  by rewrite addnS addn1.
(* This is the last part of 11.8.2 *)
have Xd i j  (nz_j : j != 0) (Ca : (a_ i j == 0) || (a_ i j == 2%:R)) :
         X_ i j  = delta *: (eta_ i j - eta_ i 0).
  have co_w_SHC_tau1 : coherent_with (S_ HC) M^# tau tau1 by split.
  apply: (FTtype345_bridge_coherence _ S1z _ co_w_SHC_tau1 (tau_alphaE i j));
       rewrite ?SHC1 //.
  - by apply: seqInd_conjC_subset1; rewrite /= ?defMs.
  - rewrite rpredD // ?rpredN // ?scale_zchar ?Za ?Cint_Cnat ?En //.
      by rewrite mem_zchar // map_f.
    rewrite big_seq_cond; apply: rpred_sum=> x /andP[SHCx _].
    by rewrite mem_zchar // map_f.
  - rewrite cfdotC oXY ?conjC0 //.
  rewrite nY //;  have /orP[/eqP->|/eqP->] := Ca.
    by rewrite mulr0 mul0r add0r.
  by rewrite subrr mulr0 add0r.
pose beta := tau (alpha_ 0 #1) - delta *: (eta_ 0 #1 - eta_ 0 0)  + n *: tau1 z.
(* First part of 11.8.3 *)
have betaE i j  (nz_j : j != 0) :
    beta = tau (alpha_ i j) - delta *: (eta_ i j - eta_ i 0) + n *: tau1 z.
  congr (_ + _).
  have-> : tau (alpha_ i j) = tau (alpha_ i j - alpha_ i #1) + tau (alpha_ i #1).
    by rewrite -raddfD subrK.
  rewrite [alpha_ i j]alphaE {1}[alpha_ i #1]alphaE.
  rewrite opprB !addrA subrK opprB !addrA subrK.
  have-> : tau (mu2_ i j - mu2_ i #1) = delta_ j *: (eta_ i j - eta_ i #1).
    apply: prDade_sub_TIirr pddM _ _ _ _ _ _ => //.
    by have [Hmu _ _] := FTtype345_constants maxM MtypeP Mtypen2; rewrite !Hmu.
  have [_ /(_ _ nz_j)-> _ _] := FTtype345_constants maxM MtypeP Mtypen2.
  have-> : tau (alpha_ i #1) = tau (alpha_ i #1 - alpha_ 0 #1) + tau (alpha_ 0 #1).
    by rewrite -raddfD subrK.
  rewrite [alpha_ i #1]alphaE {2}[alpha_ 0 #1]alphaE.
  rewrite opprB !addrA subrK opprB !addrA.
  rewrite [_ + tau _]addrC -!addrA; congr (_ + _); rewrite !addrA.
  have-> : 
     tau (mu2_ i #1 - delta *: mu2_ i 0 + delta *: mu2_ 0 0 - mu2_ 0 #1) =
          delta *: (eta_ i #1 - eta_ 0 #1 - eta_ i 0 + eta_ 0 0).
    have<- : 
     tau (delta_ #1 *: mu2_ i #1 - delta_ #1 *: mu2_ 0 #1 - mu2_ i 0 + mu2_ 0 0)
             = eta_ i #1 - eta_ 0 #1 - eta_ i 0 + eta_ 0 0.
       by apply: (prDade_sub2_TIirr pddM).
    rewrite-[_ *: tau _]raddfZ_Cint; last first.
      rewrite /delta -signr_odd; case: odd=> //.
      by rewrite CintE opprK Cnat1 orbT.
    congr (tau _); rewrite !scalerDr !scalerN !scalerA -signr_addb addbb.
    by rewrite !scale1r -!addrA; congr (_ + _); rewrite !addrA addrC -!addrA.
  rewrite !scalerDr !scalerN !addrA subrK !opprB [X in _ = X]addrC !addrA subrK.
  by rewrite addrC; congr (_ + _); rewrite [X in _ = X - _]addrC addrK.
(* This is the last part of 11.8.3 *)
have Rbeta : cfReal beta.
  have nCn : n \in Cnat by rewrite En.
  rewrite /cfReal rmorphD rmorphB /=.
  rewrite Ed1 scale1r /= rmorphB raddfZ_Cnat //=.
  rewrite ![(eta_ _ _)^*%CF]cfAut_cycTIiso -![(w_ _ _)^*%CF]cycTIirr_aut.
  rewrite !aut_Iirr0 /tau -Dade_aut -/tau.
  have ZSHC_A0 : 'Z[S_ HC, M^#] =i 'Z[S_ HC, 'A0(M)].
    move=> u1; apply/idP/idP; last first.
      by apply: (zchar_onS (FTsupp0_sub _)).
    rewrite zchar_split=> /andP[IZ CZ]; rewrite zchar_split IZ /=.
    have/cfun_onS->// :  HU^# \subset 'A0(M) by rewrite defA0 subsetUl.
    move: CZ; rewrite !cfun_onD1=> /andP[_ ->]; rewrite andbT.
    have /(zchar_expansion (seqInd_uniq _ _))[s Hs ->] := IZ.
    rewrite big_seq_cond; apply: rpred_sum=> x /andP[SHCx _].
    by apply/rpredZ/(seqInd_on (der_normal 1 _) SHCx).
  have co_A0 : coherent_with (S_ HC) 'A0(M) tau tau1.
    by split=> // v Hv; apply: Ctau1; rewrite ZSHC_A0.
  rewrite (cfAut_Dade_coherent co_A0)=> //; last first.
    rewrite (seqInd_nontrivial_irr _ _ _ SHCz) ?mFT_odd //.
    rewrite seqInd_free //; split=> //=.
    by apply: cfAut_seqInd.
  have -> : (alpha_ 0 #1)^*%CF = 
               alpha_ 0 (aut_Iirr conjC #1) + n *: (z - z^*%CF).
    rewrite !alphaE scalerBr addrA subrK Ed1 scale1r.
    by rewrite 2!rmorphB /=  raddfZ_Cnat // -!prTIirr_aut !aut_Iirr0.
  rewrite [tau _]raddfD /= -/tau [tau (_ *: _)]raddfZ_Cnat //= -/tau.
  rewrite -[tau (_ - _)]Ctau1; last first.
    rewrite  zcharD1 !cfunE !SHC1 // conj_Cnat // addrN ?eqxx andbT.
    by rewrite zchar_onG rpredB ?mem_zchar // cfAut_seqInd.
  have nz_a1 :  aut_Iirr conjC #1 != 0 :> Iirr W2 by rewrite aut_Iirr_eq0.
  rewrite  [tau1 _]raddfB (betaE 0 _ nz_a1) Ed1 scale1r -!addrA.
  apply/eqP; congr (_ + _); rewrite addrC -!addrA; congr (_ + _).
  by rewrite addrC scalerBr subrK.
have SHC_dirr : {in S_ HC, forall x : 'CF(_), tau1 x \in dirr G}.
  move=> x SHCx; rewrite /= dirrE Ztau1 ?Ptau1 ?mem_zchar //=.
  by rewrite cfdot_SHC ?eqxx.
(* This is 11.8.5 *)
have otau1_eta i j : {in S_ HC, forall z : 'CF(M), '[tau1 z, eta_ i j] = 0}.
  move=> x SHCx.
  rewrite /= (coherent_ortho_cycTIiso _ _ co_w_tau_tau1) ?SHC_irr //.
  by apply seqInd_conjC_subset1=> //=; rewrite ?defMs.
have a_is_zero  i j (nz_j : j != 0) : a_ i j = 0.
  have acfdot : a_ i j = '[\sum_i eta_ i 0, beta].
    have E1n : '[tau (mu_ 0 - z), tau (alpha_ i j)] = -1 + n.
      rewrite Dade_isometry ?cf_mu0Bz ?cf_alpha //.
      rewrite alphaE Ed1 scale1r cfdotBl !cfdotBr.
      rewrite  cfdotC cfdot_prTIirr_red (negPf nz_j) conjC0 sub0r. 
      rewrite  cfdotC cfdot_prTIirr_red eqxx conjC1.
      rewrite  !cfdotZr En ?conjC_nat omu // mulr0 subr0.
      rewrite ['[z]]cfdot_SHC // eqxx mulr1 !['[z,_]]cfdotC !omu2 //.
      by rewrite conjC0 sub0r oppr0 sub0r opprK.
    suff Eb1an : '[tau (mu_ 0 - z), tau (alpha_ i j)] = 
             '[\sum_i0 eta_ i0 0, beta] - 1 - a_ i j + n.
      apply: (addIr (- 1 - a_ i j + n)).
      rewrite ![X in X = _]addrA [a_ i j + _]addrC subrK -E1n Eb1an.
      by rewrite !addrA.
    rewrite Etau (betaE i _ nz_j) /a_ -!addrA opprD subrK !addrA.
    rewrite Ed1 scale1r.
    rewrite cfdotBl cfdotDr !cfdotBr -!addrA; congr (_ + _).
    rewrite !cfdot_suml big1 ?sub0r ?opprK => [|i1 _]; last first.
      by rewrite cfdot_cycTIiso [_ == j]eq_sym (negPf nz_j) andbF.
    rewrite (bigD1 i) //= big1 ?addr0 => [|i1 i1Di]; last first.
      by rewrite cfdot_cycTIiso (negPf i1Di).
    rewrite big1 ?add0r => [|i1 _]; last first.
      by rewrite cfdotZr cfdotC otau1_eta // conjC0 mulr0.
    rewrite cfdot_cycTIiso !eqxx addrA addrN add0r.
    rewrite cfdotC conj_Cint // -[X in X \in _](addrK n) rpredB ?Za //.
    by rewrite En // Cint_Cnat.
  have a_even : (2 %| a_ i j)%C.
    rewrite acfdot cfdot_real_vchar_even ?mFT_odd //.
    - apply/orP; right.
      (* There should be a faster way to prove this *)
      have [i1 nz_i1] := has_nonprincipal_irr ntW1.
      rewrite (betaE i1 _ nz_j) cfdotDl cfdotBl Ed1 scale1r.
      have {2 3}-> : 1 = eta_ 0 0 by rewrite cycTIirr00 cycTIiso1.
      rewrite cfdotBl !cfdot_cycTIiso (negPf nz_i1) subrr subr0.
      rewrite cfdotZl otau1_eta // mulr0 addr0.
      rewrite Dade_reciprocity ?cf_alpha // => [| x _ y _]; last first.
        by rewrite !cfun1E !inE.
      rewrite  cfRes_cfun1 alphaE !cfdotBl !cfdotZl -(prTIirr00 ptiWM).
      rewrite  !cfdot_prTIirr (negPf nz_i1) ?mulr0 subrr sub0r.
      by rewrite cfdotC omu2 // conjC0 mulr0 oppr0 (dvdC_nat 2 0).
    - split; first by rewrite rpred_sum // => i1 _; exact:  cycTIiso_vchar.
      rewrite /cfReal rmorph_sum /=; apply/eqP.
      rewrite  (reindex_inj (can_inj (@conjC_IirrK _ _))) /=.
      apply: eq_bigr=> i1 _.
      rewrite cfAut_cycTIiso -cycTIirr_aut [aut_Iirr _ _]conjC_IirrK.
      by rewrite [aut_Iirr _ _]conjC_Iirr0.
    split=> //; rewrite rpredD ?rpredB ?Dade_isometry //.
    - by rewrite Dade_vchar // zchar_split //vchar_FTtype345_bridge ?cf_alpha.
    - by rewrite Ed1 scale1r rpredB // cycTIiso_vchar.
    rewrite scale_zchar ?En ?Cint_Cnat //.
    by have := SHC_dirr _ SHCz; rewrite dirrE => /andP[].
  move: acfdot; rewrite (betaE i j) // tau_alphaE Xd //; last first.
    case/or3P: (le2 i _ nz_j) a_even => /eqP->; rewrite ?eqxx ?orbT //.
    by rewrite (dvdC_nat 2 1).
  rewrite [_ + Y_ i j]addrC addrK /Y_  [- _ + _]addrC subrK.
  rewrite cfdot_suml big1 ?scaler0 // => i1 _.
  rewrite cfdotZr cfdot_sumr  big_seq_cond big1 ?mulr0 // => i2 /andP[SHCi2 _].
  by rewrite cfdotC otau1_eta ?conjC0.
(* This is 11.8.6 *)
have [j nz_j] := has_nonprincipal_irr ntW2.
have mujE : mu_ j - d%:R *: z  = mu_ 0 - z + \sum_i alpha_ i j.
  rewrite !sumrB -scaler_sumr Ed1 scale1r [X in _ = X]addrC -!addrA -/(mu_ 0).
  congr (_ + _); rewrite [X in _ = _ + X]addrC !addrA addNr add0r -opprD.
  congr (- _); rewrite sumr_const nirrW1 -scaler_nat scalerA mulrC.
  by rewrite divfK ?neq0CG // Ed1 addrC  scalerBl scale1r subrK.
have tmujE : tau(mu_ j - d%:R *: z) = \sum_i eta_ i j - d%:R *: tau1 z.
  pose f i := eta_ i j - eta_ i 0 - n *: tau1 z.
  have taE i : tau (alpha_ i j) = f i.
    rewrite /f tau_alphaE Xd /Y_ ?a_is_zero ?scale0r ?addr0 ?eqxx //.
    by rewrite Ed1 scale1r.
  rewrite mujE [tau _]raddfD raddf_sum /= -/tau (eq_bigr f) // /f.
  rewrite Etau !sumrB  [X in X = _]addrC -!addrA; congr (_ + _).
  rewrite -opprB -opprD -opprB; congr (- _).
  rewrite !addrA opprK subrK.
  rewrite sumr_const nirrW1 -scaler_nat scalerA mulrC.
  by rewrite divfK ?neq0CG // Ed1  scalerBl scale1r subrK.
case: ncoH0C.
have [_ _ ->] := FTtype34_Fcore_kernel_trivial .
rewrite /= (group_inj (joing1G _)).
have: perm_eq (SC ++ S_ HC) (S_ C).
  apply: uniq_perm_eq; rewrite ?cat_uniq ?seqInd_uniq ?andbT //=.
    by apply/hasPn; exact: SHCdSC.
  move=> xi; rewrite mem_cat.
  apply/idP/idP=> [/orP[]|].
  - by apply: (seqIndS (Iirr_kerDS _ _ _)).
  - by apply: (seqIndS (Iirr_kerDS _ (joing_subr _ _) _)).
  have [_ nsHC_M _] := normal_hyps.
  case/seqIndP => i HI->; rewrite !mem_seqInd // inE [X in _ || X]inE.
  by move: HI; rewrite inE => /andP[-> ->]; case: (_ \in _).
move/perm_eq_coherent; apply.
suff[tau2 co_w_tau_tau2 Etau2] : 
    exists2 tau2, 
      coherent_with SC M^# tau tau2 & tau2 (mu_ j) = \sum_i eta_ i j.
  rewrite -Etau2 -raddfZnat in tmujE.
  pose bc := bridge_coherent subc_M.
  apply: bc tmujE => //; try by apply: seqInd_conjC_subset1.
  have S1n_muj : mu_ j \in S1nirr by rewrite S1nirr_i_Smu map_f // mem_enum.
  split; last 2 first.
  - by apply: scale_zchar; [apply: Cint_Cnat | apply: mem_zchar].
  - rewrite mujE cfunD1E !cfunE (SHC1 SHCz).
    rewrite prTIred0 !cfunE cfuniE // group1 mulr1 subrr add0r.
    rewrite sum_cfunE big1 // => i _.
    apply/eqP; rewrite -cfunD1E.
    by apply: cfun_onS (FTsupp0_sub _) (cf_alpha _ _ _).
  by move: S1n_muj; rewrite S1nirr_i_Smu Smu_i_SCnirr mem_filter => /andP[].
have [/all_filterP Ef|/allPn[x SCx irrx]] := boolP (all [predC irr M] SC).
  have [_ [tau2 Dtau2 [Ztau2 Ctau2]]] := uniform_prTIred_coherent pddM nz_j.
  have sSC_unif : {subset SC <= uniform_prTIred_seq pddM j}.
    move=> mu_k; rewrite -Ef mem_filter !inE => /andP[kNirr kIS2].
    have: mu_k \in S1nirr
      by rewrite S1nirr_i_Smu Smu_i_SCnirr mem_filter [X in X && _]kNirr.
    rewrite S1nirr_i_Smu; case/imageP=> k nz_k ->.
    by rewrite image_f // !inE [_ != 0]nz_k /= !mu1.
  exists tau2.
    split=> [|k /(zchar_subset sSC_unif)/Ctau2 //].
    by apply:  sub_iso_to (zchar_subset _) _ Ztau2.
  have [_ /(_ _ nz_j) Ez _ _] := FTtype345_constants maxM MtypeP Mtypen2.
  by rewrite -[X in _ = X]scale1r -Ed1 -Ez -Dtau2.
move: irrx SCx; rewrite negbK => /irrP[{x}  i -> SCi].
have /CnatP[n chi1En] := Cnat_irr1 i.
have SCmuj : mu_ j \in SC.
  have: mu_ j \in Smu by apply: image_f; exact: nz_j.
  by rewrite Smu_i_SCnirr mem_filter => /andP[].
have [tau2 co_w_tau_tau2] : coherent SC M^# tau.
  rewrite /SC -(_ : (C <*> H)%G = HC) ?seqIndDY //=; last first.
    by apply/group_inj/dprodWY; rewrite -defHC dprodC.
  apply: subset_coherent (Ptype_core_coherence maxM MtypeP Mtypen5).
  apply: seqIndS (Iirr_kerDS _ _ _)=> //.
  have [_ _ /group_inj->] := FTtype34_Fcore_kernel_trivial .
  by rewrite (group_inj (joing1G _)) (group_inj Ptype_Fcompl_kernel_cent) der_sub.
exists tau2=> //.
pose xx := 'chi_ i 1%g *: mu_ j - mu_ j 1%g *: 'chi_ i.
have cf_xx : xx \in 'CF(M, HU^#).
  rewrite cfun_onD1 ?cfunE ?1mulrC ?subrr ?eqxx //.
  by rewrite rpredB ?rpredZ  ?(seqInd_on _ SCi) ?(seqInd_on _ SCmuj).
pose yy := mu_ j - d%:R *: z.
have sHU_A0 :  HU^# \subset 'A0(M) by rewrite defA0 subsetUl.
have cf_yy : yy \in 'CF(M, HU^#).
  rewrite cfun_onD1 ?rpredB ?rpredZ ?(seqInd_on _ SHCz) ?(seqInd_on _ SCmuj) //.
  by rewrite !cfunE (SHC1 SHCz) mu1 // Edu mulrC natrM subrr eqxx.
have: '[tau xx, tau yy] != 0.
  rewrite Dade_isometry ?(cfun_onS sHU_A0) //.
  rewrite cfdotBl !cfdotBr !cfdotZl !cfdotZr cfnorm_prTIred omu //. 
  rewrite  !mulr0 subr0 (seqInd_ortho _ _ SCmuj) ?mulr0 ?sub0r //; last first.
    by apply: contra (prTIred_not_irr ptiWM j) => /eqP<-; exact: mem_irr.
  rewrite (seqInd_ortho nsHUM (seqInd_subT SCi) (seqInd_subT SHCz)) //.
    by rewrite !mulr0 oppr0 subr0 mulf_neq0 ?irr1_neq0 // -/q natrG_neq0.
  by apply: contra (SHCdSC SHCz)=> /eqP<-.
have [Ztau2 Ctau2] := co_w_tau_tau2.
have /orthogonalP cfdot_map_SC_SHC :
              orthogonal (map tau2 SC) (map tau1 (S_ HC)).
  by apply: (coherent_ortho subc_M)=> //; apply: seqInd_conjC_subset1.
rewrite -[tau xx]Ctau2 ?tmujE /=; last first.
  rewrite zcharD1E; move: cf_xx; rewrite cfun_onD1 => /andP[_ ->].
  by rewrite rpredB // scale_zchar ?mem_zchar ?mu1 ?chi1En ?Cint_Cnat.
rewrite cfdotBr cfdotZr {2}[tau2 xx]raddfB cfdotBl chi1En mu1 // !raddfZnat //.
rewrite !cfdotZl !['[_,tau1 _]]cfdot_map_SC_SHC ?map_f //.
rewrite !(mulr0, subr0) raddfB chi1En mu1 // cfdotBl !raddfZnat !cfdotZl.
rewrite ['[tau2 'chi_ i, _]]cfdot_sumr.
rewrite [in X in _- X != 0 -> _]big1 ?mulr0 ?subr0 => [|k _]; last first.
  apply: (coherent_ortho_cycTIiso _ _ co_w_tau_tau2); rewrite ?mem_irr //.
  by rewrite (group_inj defMs); apply: seqInd_conjC_subset1.
have [|[b k] ->[[-> ->]|[-> -> _]]] // :=
     FTtypeP_coherent_TIred _ co_w_tau_tau2 SCi SCmuj.
- by apply: seqInd_conjC_subset1; rewrite (group_inj defMs).
- have [_ /(_ _ nz_j)-> _ _] := FTtype345_constants maxM MtypeP Mtypen2.
  by rewrite Ed1 scale1r.
case/eqP; rewrite cfdotZl cfdot_suml big1 ?mulr0 // => k1 _.
rewrite cfdot_sumr big1 ?mulr0 // => k2 _.
rewrite cfdot_cycTIiso.
case: (boolP (_ == j))=> [/eqP Cjj|]; last by rewrite andbF.
suff /eqP[] : (mu_ j)^*%CF != mu_ j.
  by rewrite -prTIred_aut /aut_Iirr -conjC_IirrE Cjj irrK.
by apply: seqInd_conjC_neq SCmuj; rewrite  ?mFT_odd //.
Qed.

Implicit Types r : {rmorphism algC -> algC}.

(* This is PF (11.9). *)
Lemma FTtype34_structure :
  [/\ (*a*) {in S_ HC, forall z : 'CF(M),
             orthogonal (tau (mu_ 0 - z) - \sum_j eta_ 0 j) codom_sigma},
      (*b*) (p < q)%N
    & (*c*) FTtype M == 3 /\ typeP_Galois MtypeP].
Proof. 
have oXeta : {in S_ HC, forall z,
             orthogonal (tau (mu_ 0 - z) - \sum_j eta_ 0 j) codom_sigma}.
  move=>  z SHCz; move: (SHCz).
  have /irrP[iz ->] := SHC_irr SHCz => {z SHCz}SHCz.
  pose z := 'chi_iz; set psi := mu_ 0 - z.
  pose Wsig := map sigma (irr W).
  have [X wsigX [chi [tau_XDchi oX_chi oX]]] := orthogonal_split Wsig (tau psi).
  have [Isigma Zsigma] := cycTI_Zisometry ctiWG.
  have ochi_eta i j : '[chi, eta_ i j] = 0.
    by rewrite (orthoPl oX) ?map_f ?mem_irr.
  have onWsig : orthonormal Wsig by rewrite map_orthonormal ?irr_orthonormal.
  have [a_ Da defX] := orthonormal_span onWsig wsigX.
  have{Da} Da i j : a_ (eta_ i j) = '[tau psi, eta_ i j].
    by rewrite tau_XDchi cfdotDl ochi_eta addr0 Da.
  have eX : X = \sum_i \sum_j a_ (eta_ i j) *: eta_ i j.
    rewrite pair_bigA defX big_map (big_nth 0) size_tuple big_mkord /=.
    rewrite (reindex (dprod_Iirr defW)) /=.
      by apply: eq_bigr => [[i j] /= _]; rewrite -tnth_nth.
    exists (inv_dprod_Iirr defW) => ij; first by rewrite dprod_IirrK.
    by rewrite inv_dprod_IirrK.
  have irr_psi : psi \in 'Z[irr M, HU^#].
    rewrite zchar_split // rpredB  ?irr_vchar //; last first.
      by rewrite rpred_sum // => i _; apply: irr_vchar.
    rewrite cfun_onD1 ?rpredB ?cfunE ?prTIred0 ?(seqInd_on _ SHCz) //.
      by rewrite (SHC1 SHCz) cfunE cfuniE //= group1 mulr1 subrr.
    by rewrite rpredZ // cfuni_on.
  have cf_psi : psi \in 'CF(M, 'A0(M)).
    by apply: cfun_onS (zchar_on irr_psi); rewrite defA0 subsetUl.
  have a00_1 : a_ (eta_ 0 0) = 1.
    rewrite Da [w_ 0 0](cycTIirr00 defW) [sigma 1]cycTIiso1.
    rewrite Dade_reciprocity // => [|x _ y _]; last by rewrite !cfun1E !inE.
    rewrite rmorph1 /= -(prTIirr00 ptiWM) -/(mu2_ 0 0) cfdotC.
    by rewrite cfdotBr cfdot_prTIirr_red omu2 // subr0 rmorph1.
  have aPsi r : cfAut r (tau psi) = tau psi + tau (z - cfAut r z).
    rewrite -Dade_aut !rmorphB !raddfB /= !addrA subrK.
    by rewrite -prTIred_aut aut_Iirr0.
  have aijCint i j : a_ (eta_ i j) \in Cint.
    rewrite Da Cint_cfdot_vchar ?cycTIiso_vchar ?Dade_vchar //.
    by apply: zchar_onS irr_psi; rewrite defA0 subsetUl.
  have aijE i j : a_ (eta_ i j) = '[X, eta_ i j].
    by rewrite Da tau_XDchi cfdotDl ochi_eta addr0.
  have cfAut_a r i j : a_ (cfAut r (eta_ i j)) = a_ (eta_ i j).
    have S1z: z \in S_ 1 by rewrite (seqIndS _ SHCz) ?Iirr_kerDS ?sub1G.
    have S1rz: cfAut r z \in S_ 1 by rewrite cfAut_seqInd.
    have rz1: z 1%g == cfAut r z 1%g by rewrite cfAut_char1 ?(seqInd_char S1z).
    have [S2 [S2z S2rz sS21] []] := pair_degree_coherence subc_M S1z S1rz rz1.
    move=> tau2 cohS2; have [_ Dtau2] := cohS2.
    rewrite -{2}(group_inj defMs) in sS21.
    have otau2 := coherent_ortho_cycTIiso MtypeP sS21 cohS2.
    transitivity '[cfAut r (tau psi), cfAut r (eta_ i j)]; last first.
      rewrite -(aut_Cint r (aijCint i j)) Da.
      have /dirrP[i1 [b ->]] := cycTIiso_dirr ctiWG i j.
      by rewrite linearZ !cfdotZr rmorphM !rmorph_sign cfdot_aut_irr.
    rewrite aPsi cfdotDl cfAut_cycTIiso -cycTIirr_aut.
    rewrite tau_XDchi cfdotDl ochi_eta addr0 -aijE.
    have ->: tau (z - cfAut r z) = tau2 z - tau2 (cfAut r z).
      rewrite -Dtau2 ?raddfB // zcharD1E 2!cfunE subr_eq0 rz1 andbT.
      by rewrite rpredB ?mem_zchar.
    by rewrite cfdotBl !otau2 ?subrr ?addr0 // ?cfAut_irr ?mem_irr.
  have nz_1i : #1 != 0 :> Iirr W1 by rewrite Iirr1_neq0.
  have nz_1j : #1 != 0 :> Iirr W2 by rewrite Iirr1_neq0.
  have aiE i (nz_i : i != 0) : a_ (eta_ i 0) = a_ (eta_ #1 0).
    have [k co_k_i1 Di] := cfExp_prime_transitive (pr_q) nz_1i nz_i.
    rewrite -(cforder_dprodl defW) -dprod_IirrEl in co_k_i1.
    have{co_k_i1} [[r Di1r] _] := cycTIiso_aut_exists ctiWG co_k_i1.
    rewrite dprod_IirrEl -rmorphX -Di /= -!dprod_IirrEl -!/(w_ _ _) in Di1r.
    by rewrite Di1r  cfAut_a.
  have ajE j (nz_j : j != 0) : a_ (eta_ 0 j) = a_ (eta_ 0 #1).
    have [k co_k_j1 Dj] := cfExp_prime_transitive (pr_p) nz_1j nz_j.
    rewrite -(cforder_dprodr defW) -dprod_IirrEr in co_k_j1.
    have{co_k_j1} [[r Dj1r] _] := cycTIiso_aut_exists ctiWG co_k_j1.
    rewrite dprod_IirrEr -rmorphX -Dj /= -!dprod_IirrEr -!/(w_ _ _) in Dj1r.
    by rewrite Dj1r  cfAut_a.
  have aijnz_E i j (nz_i : i != 0) (nz_j : j != 0) :
      a_ (eta_ i j) = a_ (eta_ i 0) + a_ (eta_ 0 j) - a_ (eta_ 0 0).
    apply: (addIr (a_ (eta_ 0 0))); rewrite subrK !Da.
    apply: cycTIiso_cfdot_exchange => x Vx /=.
    rewrite Dade_id ?defA0; last by rewrite inE orbC mem_class_support.
    rewrite (cfun_on0 (zchar_on irr_psi)) // -defA.
    suffices /setDP[] : x \in 'A0(M) :\: 'A(M) by [].
    by rewrite (FTsupp0_typeP maxM MtypeP) // mem_class_support.
  have normX : '[X] = 1 + q.-1%:R * a_(eta_ #1 0) ^+ 2 
                        + p.-1%:R * a_(eta_ 0 #1) ^+ 2
                        + p.-1%:R * q.-1%:R * a_ (eta_ #1 #1) ^+ 2.
    have -> : '[X] = \sum_i \sum_j a_(eta_ i j)^+2.
      rewrite defX cfnorm_sum_orthonormal //.
      rewrite pair_bigA big_map (big_nth 0) size_tuple big_mkord /=.
      rewrite (reindex (dprod_Iirr defW)) /=.
        apply: eq_bigr => [[i j] /= _]; rewrite -tnth_nth.
        by rewrite Cint_normK // aijCint.
      exists (inv_dprod_Iirr defW) => ij; first by rewrite dprod_IirrK.
      by rewrite inv_dprod_IirrK.
    pose cD := cardD1 0.
    have pm1E : p.-1 = #|[predD1 Iirr W2 & 0]| by rewrite -nirrW2 cD inE.
    have qm1E : q.-1 = #|[predD1 Iirr W1 & 0]| by rewrite -nirrW1 cD inE.
    rewrite (bigD1 0) //= (bigD1 0) //=.
    rewrite (eq_bigr (fun i => a_ (eta_ 0 #1) ^+ 2)); last first.
      by move=> j nz_j; rewrite ajE.
    rewrite sumr_const (@eq_card _ _ [predD1 Iirr W2 & 0]); last first.
      by move=> i /=; rewrite !inE andbT /in_mem /=; case: (_ == _).
    rewrite -pm1E mulr_natl.
    pose f i := a_ (eta_ #1 0) ^+ 2 + p.-1%:R * a_ (eta_ #1 #1) ^+ 2.
    rewrite (eq_bigr (f _))=> [|i nz_i]; last first.
      rewrite (bigD1 0) ?aiE //=; congr (_ + _).
      rewrite (eq_bigr (fun _ => a_ (eta_ #1 #1) ^+ 2))=> [|j nz_j]; last first.
        rewrite (aijnz_E _ _ nz_i nz_j).
        rewrite [in X in _ = X](aijnz_E _ _ nz_1i nz_1j).
        by rewrite aiE // ajE.
      rewrite sumr_const (@eq_card _ _ [predD1 Iirr W2 & 0]); last first.
        by move=> i1 /=; rewrite !inE andbT /in_mem /=; case: (_ == _).
      by rewrite -pm1E mulr_natl.
    rewrite /f /= sumr_const (@eq_card _ _ [predD1 Iirr W1 & 0]); last first.
      by move=> i /=; rewrite !inE andbT /in_mem /=; case: (_ == _).
    rewrite -qm1E !mulr_natl mulrnDl !addrA; congr (_ + _).
      by rewrite addrAC a00_1 expr1n.
    by rewrite -!mulrnA mulnC mulr_natl.
  have normX_le_q : '[X] <= q%:R.
     have En : '[tau psi] = '[X] + '[chi] by rewrite tau_XDchi cfnormDd.
     have Eq : '[tau psi] = q%:R + 1.
       rewrite Dade_isometry ?cf_mu0Bz // cfnormDd.
         by rewrite cfnorm_prTIred cfnormN cfdot_SHC // eqxx.
       by rewrite cfdotNr omu ?oppr0.
    rewrite -(ler_add2r '[chi]) -En Eq ler_add2l.
     suff: '[chi] != 0.
       suff /CnatP[nc->] : '[chi] \in Cnat.
         by rewrite (ler_nat _ 1%N) (eqr_nat _ _ 0%N); case: nc.
       rewrite CnatEint cfnorm_ge0 andbT.
       have-> : '[chi] = '[tau psi] - '[X] .
         by rewrite En ['[X] + _]addrC addrK.
       rewrite rpredB ?Eq ?rpredD  ?Cint_Cnat //.
       rewrite defX cfdot_sum_orthonormal //.
       rewrite big_seq_cond rpred_sum // => i.
       rewrite andbT => /mapP[x /(cycTIirrP defW)[i1 [j1 ->]]->].
       rewrite conj_Cint ?aijCint //.
       by apply: (@Cnat_exp_even (a_ _) 2%N).
    have: '[tau psi, tau (z - z^*%CF)] != 0.
      rewrite Dade_isometry=> //.
         rewrite !cfdotBl !cfdotBr ?omu ?cfAut_seqInd //.
         rewrite cfnorm_irr -conjC_IirrE cfdot_irr.
         rewrite [iz == _]eq_sym -(inj_eq irr_inj) conjC_IirrE.
         rewrite (negPf (seqInd_conjC_neq _ _ _ SHCz)) ?mFT_odd //.
         by rewrite !subr0 sub0r oppr_eq0 oner_neq0.
      have cf_SHC : {subset S_ HC <= 'CF(M, HU)}.
        by apply: (seqInd_on (der_normal 1 _)).
      apply: (cfun_onS (subsetUl _ _))=> //.
      rewrite defA cfun_onD1 rpredB ?cf_SHC ?cfAut_seqInd ?mem_zchar //.
      by rewrite !cfunE irr1_degree ?rmorph_nat subrr eqxx.
    rewrite cfnorm_eq0 tau_XDchi; apply: contra=> /eqP->; rewrite addr0.
    have[tau1 co_w_SHC] := co_SHC_tau; have [[Ztau1 Ptau1] Ctau1] := co_w_SHC.
    rewrite -Ctau1 ?raddfB /=; last first.
      rewrite  zcharD1 2!cfunE !SHC1 ?cfAut_seqInd ?subrr ?eqxx //.
      by rewrite zchar_onG rpredB // mem_zchar // cfAut_seqInd.
    suff oX_tau1 : {in S_ HC, forall x : 'CF(M), '[X, tau1 x] = 0}.
        by rewrite !oX_tau1 ?cfAut_seqInd // subrr.
    move=> x SHCx; rewrite /= cfdotC defX cfdot_sumr big_seq_cond.
    pose cirrP := cycTIirrP defW.
    pose otau1 := coherent_ortho_cycTIiso _ _ co_w_SHC.
    rewrite big1 ?conjC0 // => i /andP[/mapP[y /cirrP[i1 [j1 ->]]->] _] //.
    rewrite cfdotZr /= otau1 ?SHC_irr ?mulr0 //.
    by apply seqInd_conjC_subset1=> //=; rewrite ?defMs.
  have even2 : ~~ odd 2 by [].
  have sqrt_a_ge0 i j : 0 <= a_ (eta_ i j) ^+ 2.
     have /CnatP[na->] := Cnat_exp_even even2 (aijCint i j).
     by apply: ler0n.
  have [/eqP a11_0|nz_a11] := boolP (a_ (eta_ #1 #1) == 0); last first.
    suff /ler_trans/(_ normX_le_q) : '[X] >= (2 * q.-1)%:R.
      rewrite ler_nat leqNgt=> /negP[].
      case: q pr_q (mFT_odd W1 : odd q)=>  [|[|[|q1]]] // _ _.
      by rewrite mulSn mul1n addnS -addSn -addn1 leq_add2l.
    rewrite normX ler_paddl ?addr_ge0 ?[0 <= _%:R * _]mulr_ge0 ?ler0n ?Pa //.
      by apply: (ler0n _ 1%N).
    have: a_ (eta_ #1 #1) ^+ 2 != 0.
      by apply: contra nz_a11; rewrite mulf_eq0 => [/orP[]].
    have/CnatP[na->] := Cnat_exp_even even2 (aijCint #1 #1).
    rewrite -!natrM ler_nat (eqr_nat _ _ 0%N); case: na=> // na _.
    rewrite -[(2 * _)%N]muln1 !leq_mul //.
    by case: p pr_p (mFT_odd W2 : odd p)=> [|[|[|]]] //= _.
  rewrite a11_0 expr0n /= mulr0 addr0 in normX.
  have [/eqP a10_0|nz_a10] := boolP (a_ (eta_ #1 0) == 0); last first.
    have /ler_trans/(_ normX_le_q) : 
          '[X] >= q%:R + (p.-1)%:R  * a_ (eta_ 0 #1) ^+ 2.
      rewrite normX ler_add2r.
      have: a_ (eta_ #1 0) ^+ 2 != 0.
        by apply: contra nz_a10; rewrite mulf_eq0 => [/orP[]].
      have/CnatP[na->] := Cnat_exp_even even2 (aijCint #1 0).
      rewrite -!natrM -(natrD _ 1%N) ler_nat (eqr_nat _ _ 0%N).
      case: na=> // na _.
      rewrite mulnS addnA add1n; case: q pr_q => // q1 _.
      by apply: leq_addr.
    rewrite ger_addl pmulr_rle0=> [sqr_a10_le_0|]; last first.
      by rewrite (ltr_nat _ 0); case: p pr_p => [|[|]].
    have sqr_a01_0 : a_ (eta_ 0 #1) ^+ 2 == 0.
      have/CnatP[na naE] := Cnat_exp_even even2 (aijCint 0 #1).
      by move: sqr_a10_le_0; rewrite {}naE (ler_nat _ _ 0); case: na.
    have a01_0 :  a_ (eta_ 0 #1) = 0.
      by move: sqr_a01_0; rewrite mulf_eq0 => [/orP[]/eqP].
    have a10_1 : a_ (eta_ #1 0) = 1.
      have := aijnz_E _ _ nz_1i nz_1j.
      rewrite  a11_0 a01_0 a00_1 addr0.
      by move/eqP; rewrite eq_sym subr_eq add0r => /eqP.
    suff X_is_sum : X = \sum_i eta_ i 0.
      have /negP[] := FTtype34_not_ortho_cycTIiso SHCz.
      by rewrite -/psi tau_XDchi -X_is_sum [X + _]addrC addrK.
    rewrite eX; apply: eq_bigr=> i _.
    have[/eqP->|nz_i] := boolP (i == 0).
      rewrite (bigD1 0) //= big1 ?addr0 ?a00_1 ?scale1r // => j nz_j.
      by rewrite ajE // a01_0 scale0r.
      rewrite (bigD1 0) //= big1 => [|j nz_j].
        by rewrite addr0 aiE // a10_1 scale1r.
      rewrite aijnz_E // aiE // ajE // a01_0 a10_1 a00_1.
      by rewrite addr0 subrr scale0r.
  have a01_1 : a_ (eta_ 0 #1) = 1.
    have := aijnz_E _ _ nz_1i nz_1j.
    rewrite  a11_0 a10_0 a00_1 add0r.
    by move/eqP; rewrite eq_sym subr_eq add0r => /eqP.
  have <- : X = \sum_j eta_ 0 j.
    rewrite eX (bigD1 0) //=  [X in _ + X = _]big1 => [|i nz_i].
      rewrite addr0; apply: eq_bigr => i _.
      by have [/eqP->|nz_i] := boolP (i == 0);
        rewrite ?a00_1 ?ajE // ?a01_1 scale1r.
    apply: big1 => j _; have [/eqP->|nz_j] := boolP (j == 0).
      by rewrite aiE // a10_0 scale0r.
    rewrite aijnz_E // aiE // ajE // -(aijnz_E _ _ nz_1i nz_1j).
    by rewrite a11_0 scale0r.
  by rewrite tau_XDchi [X + _]addrC addrK.
have [z SHCz] : exists z, z \in S_ HC.
  have ntHU : HU :!=: 1%g by rewrite -defMs FTcore_neq1.
  have sol_HU := solvableS (der_subS 0 _) (of_typeP_sol MtypeP).
  have [i lin_i nzi] := solvable_has_lin_char ntHU sol_HU.
  exists ('Ind 'chi_i); rewrite mem_seqInd -?derM2_HC ?gFnormal // !inE.
  by rewrite subGcfker -irr_eq1 nzi lin_char_der1.
move: (SHCz); have /irrP[iz ->] := SHC_irr SHCz => {z SHCz}SHCz.
pose z := 'chi_iz.
have pLq : (p < q)%N.
  have S1z : z \in  S_ 1 by apply: (seqIndS (Iirr_kerDS _ (sub1G _) _) SHCz).
  have [//|qLp|pEq] :=  ltngtP p q; last first.
    have [ciW _ _ _] := ctiWM.
    have: coprime q p by rewrite -(cyclic_dprod defW).
    by rewrite pEq /coprime gcdnn; case: q pr_q => [|[|]].
  have /negP[] := FTtype34_not_ortho_cycTIiso SHCz.
  have [chi [chiE _ _ ochi_eta]] :=   
       FTtype345_Dade_bridge0 maxM MtypeP Mtypen2 S1z (SHC1 SHCz) qLp.
  rewrite /(mu_ _) /ptiWM /= chiE addrAC subrr sub0r.
  apply/orthogonalP=> i oi.
  rewrite inE => /eqP-> /mapP[x /(cycTIirrP defW)[i1 [j1 ->]]->].
  by rewrite cfdotNl ochi_eta oppr0.
have [Gal|NGal] := boolP (typeP_Galois MtypeP).
  have [F [phi _ _ [cyUbar _ _]]] := typeP_Galois_P maxM Mtypen5 Gal.
  have [_ _ _ CeU'] := Mtype34_facts.
  rewrite Ptype_Fcompl_kernel_cent (group_inj CeU') in cyUbar.
  have [_ [nilU _ _ _] _ _ _] := MtypeP.
  move: Mtype34; rewrite inE => /orP[->|] // /(compl_of_typeIV maxM MtypeP).
  case=> _ /negP[]; apply: cyclic_abelian.
  by apply: cyclic_nilpotent_quo_der1_cyclic.
split=> //.
have [_ _ _ U'eC] := Mtype34_facts.
have [pAbH cardH trivH0] := FTtype34_Fcore_kernel_trivial.
have [Ha [sSHH0 Hb] _] := typeP_nonGalois_characters maxM Mtypen5 NGal.
case: (_ NGal) Ha => 
    H1 /= [divH1 NH1 actH1 sumH1 [a_gt1 aDiv cyclU [V1 isoV1]]] Ha.
have cHH0 : pdiv #|(`H / H0)%g| = p.
  rewrite trivH0 -(card_isog (quotient1_isog _)) cardH.
  by case: q pr_q => // q1 _; rewrite pdiv_pfactor.
rewrite {}cHH0 in divH1 aDiv Ha *.
set U1 := 'C_U(H1 | 'Q) in a_gt1 aDiv Ha *.
set a := #|U : U1| in a_gt1 aDiv Ha *.
set irr_qa := [pred _ | _]; set lb_n := (_.-1 * #|_|)%N; set lb_d := (_ * _)%N.
case=> dLbdLbn countIrr_qa.
have/leq_trans/(_ countIrr_qa) : (0 < lb_n %/ lb_d)%N.
  by rewrite divn_gt0 dvdn_leq // !muln_gt0 ?cardG_gt0 
             ?(ltn_trans (ltn0Sn _) a_gt1) //; case: p pr_p => [|[|]] //.
rewrite -has_count => /hasP[xj SH0Cxj] .
rewrite inE -/q => /andP[/irrP[ib def_ib] lamb1].
rewrite {xj}def_ib in SH0Cxj lamb1.
set lamb := 'chi_ib in lamb1 SH0Cxj.
have [j nz_j] := has_nonprincipal_irr ntW2.
have: mu_ j \in Smu by apply: map_f; rewrite mem_enum.
rewrite -S1nirr_i_Smu => /Hb .
rewrite  trivH0 (group_inj (joing1G _)).
rewrite Ptype_Fcompl_kernel_cent /= -/q -/u.
rewrite (group_inj Ptype_Fcompl_kernel_cent)=> [[muj1 SCHmuj exMuj]].
have HC_swap : HC = (C <*> H)%G.
   by apply/sym_equal/group_inj/dprodWY; rewrite -defHC dprodC.
have [tau2 co_w_tau2] : coherent SC M^# tau.
  rewrite /SC HC_swap ?seqIndDY //=.
  apply: subset_coherent (Ptype_core_coherence maxM MtypeP Mtypen5).
  apply: seqIndS (Iirr_kerDS _ _ _)=> //.
  have [_ _ /group_inj->] := FTtype34_Fcore_kernel_trivial .
  by rewrite (group_inj (joing1G _)) (group_inj Ptype_Fcompl_kernel_cent) der_sub.
have SClamb : lamb \in SC.
  rewrite /SC HC_swap ?seqIndDY //.
  by rewrite  trivH0 (group_inj (joing1G _)) -(group_inj U'eC) in SH0Cxj.
have SCmuj : mu_ j \in SC by rewrite /SC HC_swap ?seqIndDY.
have cfConj_SC : cfConjC_subset SC (seqIndD HU M M`_\s 1).
  by apply: seqInd_conjC_subset1; rewrite (group_inj defMs).
have [[b k] /=] := FTtypeP_coherent_TIred  cfConj_SC co_w_tau2 SClamb SCmuj.
rewrite -[primeTIred _ _]/(mu_ j) => Etau2muj Cbk.
pose psi := mu_ j - (u %/ a)%:R *: lamb.
have aDu : a %| u.
  case/seqIndP: SCHmuj muj1=> i iIkerD ->.
  have/eqP := Lagrange sHUM.
  rewrite cfInd1 // -(sdprod_card defM) eqn_mul2l.
  rewrite (negPf (lt0n_neq0 (cardG_gt0 HU))) /= => /eqP-> /eqP.
  have: (a %| 'chi_i 1%g)%C.
    apply/Ha/(subsetP (Iirr_kerDS _ _ _) _ iIkerD)=> //.
    by rewrite trivH0 sub1G.
  have a_ge0 : 0 <= a%:R :> algC by rewrite (ler_nat _ 0%N a).
  case/(dvdCP_nat a_ge0 (char1_ge0 (irr_char i)))=> nc ->.
  rewrite -!natrM eqr_nat eqn_mul2l.
  rewrite (negPf (lt0n_neq0 (cardG_gt0 W1)))=> /= /eqP<-.
  by rewrite dvdn_mull // divnn.
have psi1 : psi 1%g == 0.
  rewrite !cfunE muj1 (eqP lamb1).
  rewrite subr_eq0 /= -natrM eqr_nat  [(_ * a)%N]mulnC.
  by rewrite mulnA divnK // [(q * _)%N]mulnC.
have: '[tau (mu_ 0 - z), tau psi] = 0.
  have irr_psi : psi \in 'Z[irr M, HU^#]. 
    rewrite zchar_split // rpredB.
    - rewrite cfun_onD1 psi1 rpredB ?(seqInd_on _ SCmuj) //.
      by apply/rpredZ/(seqInd_on _ SClamb).
    - by rewrite rpred_sum // => i _; apply: irr_vchar.
    by rewrite scale_zchar ?mem_zchar ?Cint_Cnat // mem_irr.
  rewrite Dade_isometry ?cf_mu0Bz //; last first.
    by apply: cfun_onS (zchar_on irr_psi); rewrite defA0 subsetUl.
  rewrite cfdotBl !cfdotBr !cfdotZr cfdot_prTIred.
  rewrite [0 == _]eq_sym (negPf nz_j) sub0r cfdot_irr.
  case: (_ =P _)=> [Ezb|_]; rewrite ?mulr0 ?subr0.
    by move: (SHCdSC SHCz); rewrite !inE Ezb => /negP[].
  rewrite ['[z, _]]cfdotC  ['[_, z]]omu // ?conjC0 subr0.
  suff -> : '[mu_ 0, lamb] = 0  by rewrite mulr0 oppr0.
  have Tmu0 : mu_ 0 \in seqIndT HU M.
    by rewrite -[mu_ 0]cfInd_prTIres mem_seqIndT.
  rewrite (seqInd_ortho _ Tmu0 (seqInd_subT SClamb)) // /lamb.
  by apply: contraTneq (mem_irr ib) => <-; apply: prTIred_not_irr.
pose chi : 'CF(G) := tau (mu_ 0 - z) - \sum_j eta_ 0 j.
have chiE : tau (mu_ 0 - z) = \sum_j eta_ 0 j + chi.
  by rewrite [X in _ = X]addrC subrK.
have ochi_eta : orthogonal chi codom_sigma := oXeta _ SHCz.
have [Ztau2 Ctau2] := co_w_tau2.
rewrite chiE -Ctau2; last first.
  rewrite  zcharD1 psi1 zchar_onG rpredB // ?scale_zchar ?mem_zchar //.
  by rewrite Cint_Cnat.
rewrite raddfB Etau2muj raddfZnat cfdotDl !cfdotBr !cfdotZr.
rewrite cfdot_suml (bigD1 k) //=  cfdot_sumr (bigD1 0) //=. 
rewrite cfdot_cycTIiso !eqxx /= big1 ?addr0=> [|i nz_i]; last first.
  by rewrite cfdot_cycTIiso [0 == _]eq_sym (negPf nz_i).
rewrite big1 ?addr0=> [|i nz_i]; last first.
rewrite cfdot_sumr big1 // => i1 nz_i1.
  by rewrite cfdot_cycTIiso  (negPf nz_i) andbF.
rewrite cfdotC cfdot_sumr big1 ?mulr0 ?subr0=> [|i _]; last first.
  apply: (coherent_ortho_cycTIiso _ _ co_w_tau2); rewrite ?mem_irr //.
rewrite conjC0 mulr0 subr0 mulr1.
rewrite cfdot_sumr big1 ?mulr0 ?addr0 => [|i _]; last first.
  by rewrite (orthoPl ochi_eta) ?map_f ?mem_irr.
rewrite sub0r conjC_nat rmorph_sign => /(canRL (subrK _))/(congr1 Num.norm).
case/esym/eqP/idPn; rewrite add0r normrM normr_sign normr_nat.
rewrite Cnat_mul_eq1 ?rpred_nat ?Cnat_norm_Cint //; last first.
  rewrite Cint_cfdot_vchar //.
    rewrite rpredB ?rpred_sum // => [|j1 _]; last exact: cycTIiso_vchar.
    rewrite Dade_vchar // zchar_split cf_mu0Bz // rpredB ?irr_vchar //.
    by rewrite char_vchar // prTIred_char.
  by have [[_ ->//]] := co_w_tau2; apply: mem_zchar.
rewrite pnatr_eq1 -eqn_mul ?indexg_gt0 // mul1n gtn_eqF //.
have ltqu : (q < u)%N.
  have ugt1 : (1 < u)%N 
    by rewrite cardG_gt1; case/Frobenius_context : FrobUW1QC.
  rewrite -(subnKC ugt1) addSn ltnS dvdn_leq // addnBA // subSS subn1 /q.
  have nCW1 : W1 \subset 'N(C) by apply: subset_trans (joing_subr _ _) nC_UW1.
  have FrobUW1 : [Frobenius U <*> W1 = U ><| W1].
    by exact: Ptype_compl_Frobenius MtypeP _.
  have [defUW1 _ _ _ _] := Frobenius_context FrobUW1.
  have [_ _ _ _ tiUW1] := sdprod_context defUW1.
  have tiCW1 : C :&: W1 = 1%g .
    by apply/trivgP; rewrite -tiUW1 setSI // (subsetIl _).
  by rewrite (card_isog (quotient_isog nCW1 _)) ?(Frobenius_dvd_ker1 FrobUW1QC).
suff /ltn_trans/(_ (ltn_trans pLq ltqu)) : (a < p)%N by [].
rewrite -(prednK (prime_gt0 pr_p)) ltnS dvdn_leq //.
by rewrite -(subnKC (prime_gt1 pr_p)).
Qed.

End Eleven.
