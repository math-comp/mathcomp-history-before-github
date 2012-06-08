(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum ssrint algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8 PFsection9.

(******************************************************************************)
(* This file covers Peterfalvi, Section 11: Maximal subgroups of Types        *)
(* III and IV.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Eleven.

Lemma lbound_expn_odd_prime p q : 
   odd p -> odd q -> prime p -> prime q -> p != q -> (4 * q ^ 2 + 1 < p ^ q)%N.
Proof.
case: p=> [|[|[|p]]] //; case: q=> [|[|[|[|[|q]]]]] //.
  case: p=> [|[|p]] // _ _ _ _ _.
  by have /(leq_trans _)-> : (5 ^ 3 <= p.+1.+4 ^ 3)%N by rewrite leq_exp2r.
set y := p.+3; set x := _.+4; move=> _ _ _ _ _.
have /(leq_trans _)-> //: (3 ^ x <= y ^ x)%N by rewrite leq_exp2r.
rewrite {y}/x; elim: q => [| q IH] //.
rewrite [(3 ^ _)%N]expnS; set x := q.+1.+4 in IH |- *.
rewrite  -(ltn_pmul2l (_ : 0 < 3)%N) // in IH.
apply: (leq_trans _ IH); rewrite ltnS.
set X := (_ + 1)%N.
have{X}->: (X = 4 * x ^ 2 + (x * (7 * 1).+1 + (2 * 1 + 3)))%N
  by rewrite /X; ring.
set X := (3 * _)%N.
have{X}->: (X = 4 * x ^ 2 +  (x * (7 * x) + (x * x + 3)))%N 
  by rewrite /X; ring.
rewrite leq_add2l; apply: leq_add; first by rewrite leq_mul2l ltn_mul2l.
by rewrite leq_add2r leq_mul.
Qed.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

Variables M U W1 : {group gT}.
Hypotheses (maxM : M \in 'M) (MtypeP: of_typeP M U W1).
Hypothesis Mtype34 : FTtype M \in pred2 3 4.
Let Mtypen5 : FTtype M != 5.
Proof. by case/orP: Mtype34=> /eqP->. Qed.
Let Mtype24 := compl_of_typeII_IV MtypeP maxM Mtypen5.
Let Mtypen2 : FTtype M != 2.
Proof. by case/orP: Mtype34=> /eqP->. Qed.

Local Notation "'H'" := (gval M)`_\F (at level 0) : group_scope.
Local Notation "'H'" := ((gval M)`_\F)%G (at level 0) : Group_scope.
Local Notation "'W2'" := 'C_H(gval W1) (at level 0) : group_scope.
Local Notation "'W2'" := 'C_H(gval W1)%G (at level 0) : Group_scope.
Local Notation "'C'" := 'C_(gval U)(H) (at level 0) : group_scope.
Local Notation "'C'" := ('C_(gval U)(H))%G (at level 0) : Group_scope.
Local Notation "'HC'" := (H <*> C) (at level 0) : group_scope.
Local Notation "'HC'" := (H <*> C)%G (at level 0) : Group_scope.
Local Notation "'HU'" := (gval M)^`(1)%g (at level 0) : group_scope. 
Local Notation "'HU'" := M^`(1)%G (at level 0) : Group_scope.
 
Let H0 := Ptype_Fcore_kernel MtypeP.
Local Notation "'H0C'" := (gval H0 <*> C) (at level 0) : group_scope.
Local Notation "'H0C'" := (gval H0 <*> C)%G (at level 0) : group_scope.

Let p := #|W2|.
Let q := #|W1|.

Let pr_p : prime p.
Proof.
have:= typeII_IV_core maxM MtypeP Mtypen5.
by rewrite (negPf Mtypen2); case.
Qed.
Let pr_q : prime q. Proof. by case: Mtype24. Qed.
  
Let sol_M : solvable M := of_typeP_sol MtypeP.
Let sol_HU: solvable HU := solvableS (der_subS 0 _) sol_M.
Let nsHUM : HU <| M := der_normal _ _.
Let tau :=  FT_Dade0 maxM.
Let R := FTtypeP_coh_base maxM MtypeP.
Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.
Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists maxM MtypeP Mtypen5. Qed.

Let subc_M : subcoherent (seqIndD HU M HU 1) tau R.
Proof.
suff{2}->: (HU = M`_\s)%G by apply: FTtypeP_subcoherent.
apply/val_eqP; rewrite /= /FTcore.
by case/orP: Mtype34=> /eqP->.
Qed.

Let ltH0H : H0 \proper H.
Proof. by have/andP[/maxgroupp/andP[]]:= chiefH0. Qed.
Let sH0H : H0 \subset H := proper_sub ltH0H.
Let sH0M : M \subset 'N(H0).
Proof. by have/andP[/maxgroupp/andP[]]:= chiefH0. Qed.
Let nsH0H : H0 <| H.
Proof. by rewrite /normal sH0H (subset_trans (Fcore_sub _)). Qed.

Local Notation defHUW1 := (Ptype_Fcore_sdprod MtypeP).

Let nC_U_W1 : C <| U <*> W1.
Proof.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
have [_ [_ _ nUW1 _] _ _ _] := MtypeP.
rewrite /normal subIset ?joing_subl // normsI //.
  by rewrite join_subG normG; have [_ []] := MtypeP.
by rewrite norms_cent.
Qed.

Let defHC : H \x C = HC.
Proof. 
apply: dprodEY; first by exact: subsetIr.
by have[/dprodP[]]:= typeP_context MtypeP.
Qed.

Let defH0C : H0 \x C = H0C.
Proof.
have /dprodP [_ _ sC_CH iH_C] := defHC.
apply: dprodEY.
  by apply: subset_trans (subsetIr _ _) (centS sH0H).
by apply/eqP; rewrite -subG1 -iH_C setSI.
Qed.

Let nsH0M : H0 <| M.
Proof. by rewrite /normal (subset_trans sH0H) ?gFsub. Qed.

Let normal_hyps : [/\ 1 <| M, HC <| M & H0C <| M].
Proof.
suff nsCM: C <| M by rewrite normal1 !normalY ?gFnormal.
have [_ _ nHUW1 TI_HUW1] := sdprodP defM.
have [_ sUHU _ nHU TI_HU] := sdprod_context defHU.
rewrite /normal subIset ?(subset_trans sUHU) ?gFsub //=.
rewrite -{1}defM sdprodEY //= -defHU sdprodEY //= -joingA.
by rewrite join_subG cents_norm ?normal_norm // centsC subsetIr.
Qed.

Let S_ K := seqIndD M^`(1) M M^`(1) K.

(* This should be proved in 10.8 *)
Lemma nco1 : ~ coherent (S_ 1) M^# tau.
Proof. admit. Qed.

(* This is PF11.3 *)
Lemma ncoH0C : ~ coherent (S_ H0C) M^# tau.
Proof.
move=> coH0C; case: nco1.
have [_ /mulG_sub[sHUM sW1M] _ _] := sdprodP defM.
have [nsHHU sUHU /mulG_sub[sHHU sUM'] nHU tiHU] := sdprod_context defHU.
have [sHM sUM] := (subset_trans sHHU sHUM, subset_trans sUHU sHUM).
have sCM: C \subset M by rewrite subIset ?sUM.
have sH0C_M: H0C \subset M by rewrite /normal join_subG (subset_trans sH0H).
have nH0_C := subset_trans sCM sH0M.
have sH0C_HC : H0C \subset HC by apply: genS (setSU _ _). 
apply: (bounded_seqIndD_coherent nsHUM sol_HU subc_M normal_hyps)=> //.
- by rewrite sub1G sH0C_HC join_subG sHHU subIset ?sUHU.
- rewrite quotient_nil //= -defHC.
  have[-> _ _ _]:= typeP_context MtypeP.
  by exact: Fitting_nil.
rewrite -(sdprod_index defM) -/q.
rewrite -divgS // -(dprod_card defHC) -(dprod_card defH0C).
rewrite divnMr ?cardG_gt0 // divg_normal //.
have[_ _ ->] :=  Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
rewrite typeIII_IV_core_prime // -/q.
apply: lbound_expn_odd_prime=> //; try by apply: mFT_odd.
apply: contraTneq (cyclicTI_coprime (FT_cycTI_hyp MtypeP))=> ->.
by rewrite prime_coprime // dvdnn.
Qed.

Let minHbar : minnormal (H / H0)%g (M / H0)%g.
Proof. by exact: chief_factor_minnormal. Qed.
Let ntHbar : (H/H0 != 1)%g.
Proof. by case/mingroupp/andP: minHbar. Qed.
Let solHbar: solvable (H / H0)%g.
Proof. by rewrite quotient_sol // nilpotent_sol // Fcore_nil. Qed.
Let abelHbar: abelian (H /H0)%g.
Proof.
by case: (minnormal_solvable minHbar _ solHbar)=> // _ _ /and3P[].
Qed.

(* This is PF 11.4 *)
Lemma bounded_proper_coherent H1 :
  H1 <| M -> H1 \proper HU -> coherent (S_ H1) M^# tau ->
    (#|HU : H1| <= 2 * q * #|U : C| + 1)%N.
Proof.
move=> nsH1_H psH1_M' coH1.
have [nsHHU _ /mulG_sub[sHHU sUHU] _ _] := sdprod_context defHU.
rewrite -leC_nat natrD -ler_subl_addr.
have->: (2 * q * #|U : C|)%:R = 2%:R * #|M : HC|%:R * sqrtC #|HC : HC|%:R.
  rewrite indexgg sqrtC1 mulr1 -mulnA natrM; congr (_ * _%:R).
  apply/eqP; rewrite // -(eqn_pmul2l (cardG_gt0 HC)).
  rewrite Lagrange; last by case normal_hyps=> _ /andP[].
  rewrite mulnCA -(dprod_card defHC) -mulnA (Lagrange (subsetIl _ _)).
  by rewrite -(sdprod_card defM) -(sdprod_card defHU) mulnC.
pose CSB := coherent_seqIndD_bound nsHUM sol_HU subc_M _ _ coH1.
have {CSB}[||/ncoH0C|] // := CSB H0C HC%G HC%G; first by have [] := normal_hyps.
split=> //; first by apply: genS (setSU _ _). 
  by rewrite join_subG sHHU subIset ?sUHU.
rewrite (center_idP _) //.
suff/isog_abelian->: (HC / H0C)%g \isog (H / H0)%g by [].
have [_ /andP[sHCM nHCM] /andP[sH0CM nH0CM]] := normal_hyps.
have /joing_subP [nH0C_H nH0C_C] := subset_trans sHCM nH0CM.
rewrite quotientY // (quotientS1 (joing_subr _ _)) joingG1.
congr (_ \isog H / _)%g : (isog_symr (second_isog nH0C_H)).
have [[_ <- _ _][_ _ _ TI_HC]] := (dprodP defH0C, dprodP defHC).
by rewrite -group_modl // setIC TI_HC mulg1.
Qed.

(* This is PF 11.5 *)
Lemma derM2_HC : (M^`(2) = HC)%g.
Proof.
have [defFM [_ sUCH] _ _] := typeP_context MtypeP.
have {defFM}sderM2_HC: M^`(2)%g \subset HC.
  rewrite -defHC defFM.
  by have [_ _ []] := MtypeP.
have co_derM2 : coherent (S_ M^`(2)%G) M^# tau.
  have: subcoherent (S_ M^`(2)) tau R.
    by apply: (subset_subcoherent subc_M); split;
     [exact: seqInd_uniq | apply: seqInd_sub | exact: cfAut_seqInd].
  move/uniform_degree_coherence; apply.
  apply: all_pred1_constant #|M : HU|%:R _ _.
  rewrite all_map; apply/allP=> _ /seqIndP [y /setDP[sM2K _] ->] /=.
  rewrite inE in sM2K.
  by rewrite cfInd1 ?gFsub // lin_char1 ?mulr1 ?lin_irr_der1.
have [_ _ /mulG_sub[sHHU sUHU] _ _] := sdprod_context defHU.
have sHC_HU: (HC \subset HU)%g.
  by rewrite join_subG sHHU subIset // sUHU.
have B_HC: (#|HC : (M^`(2))%g| < 2 * q + 1)%N.
  rewrite -(ltn_pmul2r (indexg_gt0 U C)) mulnDl mul1n.
  apply: leq_ltn_trans (_ : 2 * q * #|U : C| + 1 < _)%N; last first.
    rewrite ltn_add2l indexg_gt1 subsetIidl sUCH //.
    by have [] := Mtype24.
  have {1}->: #|U : C| = #|HU : HC|.
    by rewrite -!divgS // ?subsetIl // -(sdprod_card defHU) 
               -(dprod_card defHC) divnMl.
  rewrite mulnC (Lagrange_index sHC_HU) //.
  rewrite bounded_proper_coherent ?gFnormal //.
  rewrite (sol_der1_proper sol_HU) // -subG1.
  apply: contra ntHbar=> /(subset_trans sHHU) /trivgP->.
  by rewrite quotient1.
have regHC_W1: semiregular (HC / M^`(2))%g (W1 / M^`(2))%g.
  move=> /= g /setD1P[ntg /morphimP[w nM''w W1w] /= Dg].
  rewrite -cent_cycle Dg -quotient_cycle //.
  rewrite -coprime_quotient_cent ?cycle_subG //; last first.
  - exact: solvableS sHC_HU _.
  - rewrite (coprimeSg sHC_HU) // (coprime_dvdr (order_dvdG W1w)) //.
    rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM).
    by have [[]] := MtypeP.
  apply: quotientS1=> /=.
  have [_ _ _ [_ _ _ sW2M'' prW1HU] _] := MtypeP.
  rewrite (subset_trans _ sW2M'') // cent_cycle -(prW1HU w) ?setSI //.
  rewrite !inE (contraNneq _ ntg) // Dg => ->.
  by rewrite morph1.
have [_ sW1M _ _ tiHU_W1] := sdprod_context defM.
have/dvdnP[k Dk]: 2 * q %| #|HC : M^`(2)%g|.-1.
  rewrite -card_quotient; last first.
     by rewrite (subset_trans sHC_HU) // (der_norm 1).
  rewrite Gauss_dvd; last by rewrite coprime2n mFT_odd.
  rewrite dvdn2 -[~~ _]/(odd _.+1) prednK ?cardG_gt0 //.
  rewrite quotient_odd ?mFT_odd //=.
  have->: q = #|(W1 / M^`(2))%g|.
    apply/card_isog/quotient_isog.
      by rewrite (subset_trans sW1M) ?gFnorm.
    by apply/trivgP; rewrite -tiHU_W1 setSI // (der_sub 1).
  apply: regular_norm_dvd_pred=> //.
  rewrite quotient_norms // (subset_trans sW1M) //.
  by have [_ /andP[]] :=  normal_hyps.
rewrite -(prednK (indexg_gt0 _ _)) Dk addn1 ltnS in B_HC.
rewrite mulnA ltn_pmul2r ?cardG_gt0 ?(@ltn_pmul2r 2 _ 1) // ltnS leqn0 in B_HC.
apply/eqP; rewrite eqEsubset sderM2_HC -indexg_eq1.
by rewrite -(prednK (indexg_gt0 _ _)) Dk (eqP B_HC).
Qed.

End Eleven.
