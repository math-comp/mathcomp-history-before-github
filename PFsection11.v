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
Require Import PFsection5 PFsection6 PFsection8 PFsection9 PFsection10.

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

(* This is Peterfalvi (11.1). *)
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

Variables M U W W1 W2 : {group gT}.
Hypotheses (maxM : M \in 'M) (defW : W1 \x W2 = W) (MtypeP: of_typeP M U defW).
Hypothesis Mtypen2 : FTtype M != 2.

Let Mtypen5 : FTtype M != 5. Proof. exact: FTtype5_exclusion. Qed.
Let Mtypen1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.
Let Mtype_gt2 : (FTtype M > 2)%N.
Proof. by move: (FTtype M) Mtypen1 Mtypen2 (FTtype_range M); do 3?case. Qed.
Let Mtype34 : FTtype M \in pred2 3 4.
Proof. by move: (FTtype M) Mtype_gt2 Mtypen5 (FTtype_range M); do 6?case. Qed.

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
Let q := #|W1|.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxM MtypeP. Qed.

Let sW2H : W2 \subset H. Proof. by have [_ _ _ []] := MtypeP. Qed.
Let defW2 : 'C_H(W1) = W2. Proof. exact: typeP_cent_core_compl MtypeP. Qed.
  
Let sol_M : solvable M := of_typeP_sol MtypeP.
Let sol_HU: solvable HU := solvableS (der_subS 0 _) sol_M.
Let nsHUM : HU <| M := der_normal _ _.
Let tau :=  FT_Dade0 maxM.
Let R := FTtypeP_coh_base maxM MtypeP.
Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.
Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists maxM MtypeP Mtypen5. Qed.

Let coHUq : coprime #|HU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defM); have [[]] := MtypeP. Qed.

Let q'p : p != q.
Proof.
apply: contraTneq coHUq => <-; rewrite coprime_sym prime_coprime ?cardSg //.
by rewrite -(typeP_cent_compl MtypeP) subsetIl.
Qed.

Let defMs : M`_\s = HU. Proof. by rewrite /FTcore andbC leqNgt Mtype_gt2. Qed.
Let subc_M : subcoherent (seqIndD HU M HU 1) tau R.
Proof. by rewrite -{2}(group_inj defMs); apply: FTtypeP_subcoherent. Qed.

Let ltH0H : H0 \proper H.
Proof. by have/andP[/maxgroupp/andP[]]:= chiefH0. Qed.
Let sH0H : H0 \subset H := proper_sub ltH0H.
Let sH0M : M \subset 'N(H0).
Proof. by have/andP[/maxgroupp/andP[]]:= chiefH0. Qed.
Let nsH0H : H0 <| H.
Proof. by rewrite /normal sH0H (subset_trans (Fcore_sub _)). Qed.
Let nsH0M : H0 <| M.
Proof. by rewrite /normal (subset_trans sH0H) ?gFsub. Qed.

Local Notation defHUW1 := (Ptype_Fcore_sdprod MtypeP).

Let nsCM: C <| M.
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
apply: dprodEY.
  by apply: subset_trans (subsetIr _ _) (centS sH0H).
by apply/eqP; rewrite -subG1 -iH_C setSI.
Qed.

Let normal_hyps : [/\ 1 <| M, HC <| M & H0C <| M].
Proof. by rewrite normal1 !normalY ?gFnormal. Qed.

Let S_ K := seqIndD M^`(1) M M^`(1) K.

(* This should be proved in Peterfalvi (10.8).*)
Lemma nco1 : ~ coherent (S_ 1) M^# tau.
Proof. exact: FTtype345_noncoherence. Qed.

(* This is Peterfalvi (11.3). *)
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
rewrite -(index_sdprod defM) -/q.
rewrite -divgS // -(dprod_card defHC) -(dprod_card defH0C).
rewrite divnMr ?cardG_gt0 // divg_normal //.
have[_ _ ->] :=  Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
rewrite typeIII_IV_core_prime // -/q.
by apply: lbound_expn_odd_prime=> //; apply: mFT_odd.
Qed.

Let minHbar : minnormal (H / H0)%g (M / H0)%g.
Proof. by exact: chief_factor_minnormal. Qed.
Let ntHbar : (H / H0 != 1)%g.
Proof. by case/mingroupp/andP: minHbar. Qed.
Let solHbar: solvable (H / H0)%g.
Proof. by rewrite quotient_sol // nilpotent_sol // Fcore_nil. Qed.
Let abelHbar: abelian (H / H0)%g.
Proof.
by case: (minnormal_solvable minHbar _ solHbar) => // _ _ /and3P[].
Qed.

(* This is Peterfalvi (11.4). *)
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
by rewrite /= (joingC H0) isog_sym quotient_sdprodr_isog ?(dprodWsdC defHC).
Qed.

(* This is Peterfalvi (11.5). *)
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
  - by rewrite (coprimeSg sHC_HU) // (coprime_dvdr (order_dvdG W1w)).
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

(* This is  Peterfalvi (11.6). *)
Lemma Mtype34_facts :
  ([/\ p.-group H, U \subset 'C(H0), H0 :=: H^`(1) & `C = U^`(1)])%g. 
Proof.
have nH := Fcore_nil M.
have CHsH := subsetIl H 'C(U).
have nHH': H \subset 'N(H^`(1))%g by exact: der_norm.
have /sdprod_context[_ UsM' HeU UsNH tHiU]:=  defHU.
have nUH': U \subset 'N(H^`(1))%g by apply: (char_norm_trans (der_char _ _)).
have HUsH:  [~: H, U] \subset H by rewrite commg_subl.
have UsCHO : U \subset 'C(H0).
  have Frob := Ptype_compl_Frobenius maxM MtypeP Mtypen5.
  have nUW1_NH0: U <*> W1 \subset 'N(H0).
    have [/andP[sHUM _] sW1M _ _ _] := sdprod_context defM. 
    have/andP[_ MsNH0] := nsH0M.
    by rewrite join_subG !(subset_trans _ MsNH0) // (subset_trans _ sHUM).
  have [||_->]// := Frobenius_Wielandt_fixpoint Frob nUW1_NH0.
  - by apply: coprimeSg (Ptype_Fcore_coprime MtypeP).
  - by apply/nilpotent_sol/(nilpotentS _ nH).
  have->: 'C_H0(W1) = H0 :&: 'C_H(W1).
    by rewrite setIA; move/setIidPl: (normal_sub nsH0H)->.
  rewrite cardMg_TI // -LagrangeMl -card_quotient; last first.
    by apply: subset_trans (subsetIl _ _) _; case/andP: nsH0H.
  have/coprime_subcent_quotient_pgroup<-//: q.-group W1.
  - apply/pgroupP=> p2 Pp2 /prime_nt_dvdP->; rewrite ?inE //.
    by case: p2 Pp2=> // [[]].
  - have [_] := Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
    by rewrite /= defW2 (def_Ptype_factor_prime maxM MtypeP) // => ->.
  - case/andP: chiefH0 => /maxgroupp/andP[_ /(subset_trans _)-> //].
    by case/sdprod_context: defM.
  apply: (coprimeSg (normal_sub nsH0H) (coprimegS (joing_subr U W1) _)).
  by exact: Ptype_Fcore_coprime MtypeP.
split=> //.
(* p.-group H *)
- apply/pnatP=> //= r Pr rDh; rewrite -topredE /=; case: eqP=> // /eqP rDp.
  have CrHr: (#|'C_H(U)|`_r = #|H|`_r)%N.
    have /= := typeII_IV_core maxM MtypeP Mtypen5.
    rewrite (negPf Mtypen2) -/p -/q => [[_ _ ->]].
    rewrite !(partnM,partnX) // ?(expn_gt0, prime_gt0) //.
    rewrite [X in (X ^ _)%N]part_p'nat ?(exp1n, mul1n) // p'natE //.
    by apply/prime_nt_dvdP=> //; [case: (r) Pr=> // [[|[]]] | apply/eqP].
  have rDC: r %| #|'C_H(U)|.
    apply: (dvdn_trans _ (dvdn_part \pi(r) _)).
    move: CrHr; rewrite -!(eq_partn _ (pi_of_prime Pr))=>->.
    by rewrite -{1}[r]partn_pi ?prime_gt0 // partn_dvd.
  case: (Sylow_exists r 'C_H(U))=> R1 S_CR1.
  have R1sH := subset_trans (pHall_sub S_CR1) (subsetIl _ _).
  suff: (R1^`(1) == R1)%g.
    rewrite eqEproper=> /andP[_ /negP[]].
    apply: (sol_der1_proper (nilpotent_sol nH) R1sH).
    apply/negP=> trivR1; move/card_Hall: S_CR1.
    move/eqP; rewrite (eqP trivR1) CrHr cards1 eq_sym p_part_eq1 /=.
    move:(pi_of_dvd rDh (cardG_gt0 _))=> -> //.
    by rewrite pi_of_prime // inE.
  have /setIidPl {2}<-: R1 \subset (HU^`(1))%g.
   rewrite derg1 -dergSn derM2_HC; case/dprodP: defHC=> _ <- _ _.
   by rewrite (subset_trans _ (mulg_subl _ _)).
  suff def1HU: R1 \x ('O_r^'(H) <*> U) = HU.
    case/(der_dprod 1)/dprodP: (def1HU)=> _ <- _ _.
    rewrite  setIC -group_modl ?der_sub // setIC.
    suff->: (R1 :&: ('O_r^'(H) <*> U)^`(1) = 1)%g by rewrite mulg1.
    apply/trivgP/(subset_trans (setIS _ (der_sub _ _)))/trivgP.
    by case/dprodP: def1HU.
  have /dprodP[_ eRO OsCR tRiO]: R1 \x 'O_r^'(H) = H.
    rewrite -{2}(nilpotent_pcoreC r nH); congr (_ \x _).
    apply: (eq_Hall_pcore (nilpotent_pcore_Hall r nH)).
    by rewrite pHallE R1sH -CrHr; case/pHallP: S_CR1=> _ ->/=.
  have UnN: U \subset 'N('O_r^'(H)).
    by case/sdprodP: defHU=> _ _ /char_norm_trans->//; apply: pcore_char.
  rewrite dprodE /=.
  - by rewrite norm_joinEr // mulgA eRO.
  - rewrite join_subG OsCR centsC.
    by case/pHallP: S_CR1; rewrite subsetI=> /andP[].
  rewrite norm_joinEr // - (setIidPl R1sH).
  rewrite -setIA [_ :&: (_ * _)%g]setIC -group_modl ?pcore_sub //.
  by rewrite [U :&: _]setIC tHiU mulg1 tRiO.
(* H0 = (H^`(1))%g *)
- pose H1 := (H / H^`(1))%g.
  pose U1 := (U / H^`(1))%g.
  pose HU1 := (HU / H^`(1))%g.
  apply/eqP; rewrite  eqEsubset andbC.
  rewrite der1_min //=; last by case/andP: nsH0H.
  rewrite -quotient_sub1; last by case/andP: nsH0H=> /subset_trans->.
  suff<-: 'C_H1(U1) = 1%g.
    rewrite subsetI quotientS //=.
    by apply: quotient_cents; rewrite // centsC // -quotient_sub1.
  have defH1: ('C_H1(U1) \x [~: H1, U1] = H1)%g. 
    rewrite dprodC.
    apply: coprime_abelian_cent_dprod (der_abelian _ _).
      by apply: quotient_norms; case/sdprodP: defHU.
    apply: coprime_morph.
    by apply: coprimegS (joing_subl U W1) (Ptype_Fcore_coprime MtypeP).
  have defHU1: ('C_H1(U1) \x  ([~: H1, U1] <*> U1) = HU1)%g.
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
  have{1}<-: ('C_H1(U1) :&: HU1^`(1) = 'C_H1(U1))%g.
    rewrite -quotient_der; last by rewrite -HeU mul_subG.
    rewrite [(HU^`(1))%g]derM2_HC .
    apply/setIidPl/(subset_trans (subsetIl _ _)).
    apply: quotientS; case/dprodP: defHC=> _ <- _ _.
    by apply: mulG_subl.
  rewrite -(der_dprod 1 defHU1).
  have/dprodP[_ _ CHH1 tHH1] := (der_dprod 1 defHU1).
  rewrite dprodE // setIC -group_modl ?der_sub //= -/U1 -/H1.
  suff->: (([~: H1, U1] <*> U1)^`(1) :&: 'C_H1(U1) = 1)%g by rewrite mulg1.
  rewrite setIC; apply/trivgP.
  case/dprodP: defHU1 => _ _ _ /trivgP/(subset_trans _)->//.
  by rewrite setIS // der_sub.
(* C = U' *)
apply/eqP; rewrite eqEsubset andbC.
rewrite subsetI der_sub; have[_ [->/= _] _ _]:= typeP_context MtypeP.
have/subset_trans->//: C \subset (M^`(2) :&: U)%g.
  rewrite derM2_HC -(dprodW defHC) setIC -group_modr ?subsetIl // setIC.
  by rewrite tHiU mul1g.
have->: (U^`(1) = (H <*> U^`(1)) :&: U)%g.
  rewrite norm_joinEr; last by apply: (subset_trans (der_sub _ _)).
  by rewrite setIC -group_modr ?der_sub // setIC tHiU mul1g.
apply: setSI.
have->: (M^`(2))%g = [~: HU, HU] by done.
rewrite -{1}HeU commMG; last by apply: normsRr.
rewrite -HeU commGC [[~: U, _]]commGC !commMG; last 2 first.
- by apply: normsRr.
- by apply: char_norm_trans (der_char 1 _) _.
rewrite [[~: U, _]]commGC mulgA !mul_subG //;
  try by apply: subset_trans (joing_subl _ _); rewrite ?(der_sub 1). 
by exact: joing_subr.
Qed.

(* This will be (11.7). *)
Lemma FTtype34_Fcore_kernel_trivial :
  [/\ p.-abelem H, #|H| = (p ^ q)%N & `H0 = 1%g].
Proof. move: derM2_HC; admit. Qed.

Let pddM := FT_prDade_hyp maxM MtypeP.
Let ptiWM : primeTI_hypothesis M HU defW := FT_primeTI_hyp MtypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddM.
Let ctiWM : cyclicTI_hypothesis M defW := prime_cycTIhyp ptiWM.

Local Notation sigma := (cyclicTIiso ctiWG).
Local Notation w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).
Local Notation mu_ := (primeTIred ptiWM).

Let codom_sigma := map sigma (irr W).
Let ntW1 : (W1 :!=: 1)%g. Proof. by have [[]] := MtypeP. Qed.
Let ntW2 : (W2 :!=: 1)%g. Proof. by have [_ _ _ []] := MtypeP. Qed.


Let sHHU : H \subset HU.
Proof. by have [_ _ /mulG_sub[]] := sdprod_context defHU. Qed.
Let sUHU : U \subset HU.
Proof. by have [_ _ /mulG_sub[]] := sdprod_context defHU. Qed.
Let sHC_HU: (HC \subset HU)%g.
Proof.  by rewrite join_subG sHHU subIset // sUHU. Qed.
Let sHUM : HU \subset M.
Proof. by have [_ _ /mulG_sub[]] := sdprod_context defM. Qed.
Let nsHCHU: HC <| HU.
Proof.
have [_ nsHC_M _] := normal_hyps.
by exact: normalS sHC_HU sHUM nsHC_M.
Qed.
Let nsCU : C <| U.
Proof.  by apply: normalS (subsetIl _ _) (subset_trans _ sHUM) nsCM. Qed.

Let frobMbar : [Frobenius M / HC = (HU / HC) ><| (W1 / HC)].
Proof.
have [[_ hallW1 _ _] _ _ [_ _ _ sW2M'' regM'W1 ] _] := MtypeP.
apply: Frobenius_coprime_quotient => //.
  by have[] := normal_hyps.
split=> [|w /regM'W1-> //]; rewrite -derM2_HC //.
apply: (sol_der1_proper (mmax_sol maxM)) => //.
by apply: subG1_contra ntW2; apply: subset_trans sW2M'' (der_sub 1 HU).

Qed.


Local Notation Idelta := (primeTI_Isign ptiWM).
Local Notation delta_ j := (primeTIsign ptiWM j).
Local Notation d := (FTtype345_TIirr_degree MtypeP).
Local Notation n := (FTtype345_ratio MtypeP).
Local Notation delta := (FTtype345_TIsign MtypeP).

Let mu2_ i j := primeTIirr ptiWM i j.

Let  NirrW1 : Nirr W1 = q.
Proof.
have [[cW1 _ _ _] _ _ _ _] := MtypeP.
by rewrite /q -card_Iirr_cyclic // card_ord.
Qed.

Let  NirrW2 : Nirr W2 = p.
Proof.
have cW2: cyclic W2 by have [_ _ _ []] := MtypeP.
by rewrite /p -card_Iirr_cyclic // card_ord.
Qed.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel MtypeP :=: C.
Proof.
have [_ _ H0_1] := FTtype34_Fcore_kernel_trivial.
rewrite [Ptype_Fcompl_kernel MtypeP]unlock /= (group_inj H0_1).
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.

(* This will be (11.8). *)
Lemma FTtype34_not_ortho_cycTIiso zeta :
    zeta \in S_ HC ->
  ~~ orthogonal (tau (mu_ 0 - zeta) - \sum_i eta_ i 0) codom_sigma.
Proof.
move=>ZiSHC.
pose S1 := S_ HC.
pose u := #|(U/C)%g|.
have Pu : (u > 0)%N by exact: cardG_gt0.
have qgt2 : (q > 2)%N by rewrite odd_gt2 ?mFT_odd ?cardG_gt1.
have FUW1 : [Frobenius U <*> W1 = U ><| W1].
  by exact: Ptype_compl_Frobenius MtypeP _.
have AUC : abelian (U / C).
  by apply: sub_der1_abelian; have[_ _ _ <-] := Mtype34_facts.
have S1w1: {in S1, forall xi : 'CF(M), xi 1%g = q%:R}.
  move=> _ /seqIndP[s /setDP[kerH' _] ->]; rewrite !inE in kerH'.
  rewrite cfInd1 // -(index_sdprod defM) lin_char1 ?mulr1 // lin_irr_der1.
  rewrite (subset_trans _ kerH') // der1_min //; first by case/andP: nsHCHU.
  suff/isog_abelian->: (HU / HC)%g \isog (U / C)%g by [].
  by rewrite isog_sym quotient_sdprodr_isog.
have SS1: (size S1 * q = u - 1)%N.
  pose X_ (S0 : seq 'CF(M)) := [set s | 'Ind[M, HU] 'chi_s \in S0].
  pose sumX_ cS0 := \sum_(s in X_ cS0) 'chi_s 1%g ^+ 2.
  have defX1: X_ S1 = Iirr_kerD HU HU HC.
    have [_ nsHC_M _] := normal_hyps.
    by apply/setP=> s; rewrite !inE mem_seqInd // !inE.
  have defX: X_ (S_ 1) = Iirr_kerD HU HU 1%g.
    by apply/setP=> s; rewrite !inE mem_seqInd ?normal1 //= !inE.
  have sumX1: sumX_ S1 = u%:R - 1.
    rewrite /sumX_ defX1 sum_Iirr_kerD_square // indexgg mul1r.
    by rewrite /u -!divgS // ?subsetIl // -(sdprod_card defHU) 
               -(dprod_card defHC) divnMl // divg_normal.
  have irrS1: {subset S1 <= irr M}.
    have [_ nsHC_M _] := normal_hyps.
    move=> _ /seqIndP[s /setDP[kerHC kerHU] ->]; rewrite !inE in kerHC kerHU.
    rewrite -(quo_IirrK _ kerHC) // mod_IirrE // cfIndMod // cfMod_irr //.
    rewrite (irr_induced_Frobenius_ker (FrobeniusWker frobMbar)) //.
    by rewrite quo_Iirr_eq0 // -subGcfker.
  apply/eqP; rewrite -eqC_nat mulnC [q](index_sdprod defM).
  rewrite (size_irr_subseq_seqInd _ (subseq_refl S1)) //.
  rewrite natrB ?cardG_gt0 // -sumr_const -sumX1.
  apply/eqP/esym/eq_bigr => s.
  rewrite defX1 !inE -derM2_HC -lin_irr_der1 => /and3P[_ _ /eqP->].
  by rewrite expr1n.
pose j : Iirr W2 := inord 1.
have nZj : j != 0.
  apply/eqP=>  /val_eqP /=.
  by rewrite inordK // NirrW2; case: (p) pr_p=> [|[]].
 (* First part of 11.8.1 *)
have Edu : d = u.
  apply/eqP.
  have/eqP: mu_ j 1%g = (q * u)%:R.
    have Imuj : mu_ j \in filter [predC irr M] (seqIndD HU M H H0).
      rewrite mem_filter /= prTIred_not_irr /=. 
      rewrite -[mu_ j]cfInd_prTIres mem_seqInd ?gFnormal ?normal1 //=.
      have [_ _ ->] := FTtype34_Fcore_kernel_trivial.
      by rewrite !inE sub1G (cfker_prTIres (FT_prDade_hypF maxM MtypeP)).
   case: (boolP (typeP_Galois MtypeP))=> TG.
     have [_ _ [_ /(_ _ Imuj)[]]] := typeP_Galois_characters maxM Mtypen5 TG.
     by rewrite Ptype_Fcompl_kernel_cent.
   have [_ [_ /(_ _ Imuj)[]]] := typeP_nonGalois_characters maxM Mtypen5 TG.
   by rewrite /u -Ptype_Fcompl_kernel_cent.
  rewrite /primeTIred  sum_cfunE (eq_bigr (fun i => d%:R))=> [|i _]; last first.
    by have [->] := FTtype345_constants maxM MtypeP Mtypen2.
  rewrite sumr_const card_ord NirrW1 -mulr_natl -natrM eqC_nat eqn_pmul2l //.
  by exact: prime_gt0.
 (* Second part of 11.8.1 *)
have Ed1 : delta = 1.
  suffices: (1 == delta %[mod q])%C.
    rewrite [delta]signrE /eqCmod addrC opprB subrK dvdC_nat.
    by case: (Idelta j); rewrite ?subr0 // gtnNdvd.
  apply: eqCmod_trans (prTIirr1_mod ptiWM 0 j); rewrite -/(mu2_ 0 j) -/q.
  have [-> // _ _ _] := FTtype345_constants maxM MtypeP Mtypen2.
  rewrite Edu eqCmod_sym /eqCmod -(@natrB _ u 1) ?indexg_gt0 // subn1 dvdC_nat.
  have nC_UW1: U <*> W1 \subset 'N(C).
    have /sdprodP[_ _ nPUW1 _] := Ptype_Fcore_sdprod MtypeP.
    by rewrite normsI ?norms_cent // join_subG normG; have [_ []] := MtypeP.
  have coUq: coprime #|U| q.
    by have /sdprod_context[_ /coprimeSg->] := defHU.
  have /Frobenius_dvd_ker1: [Frobenius U <*> W1 / C = (U / C) ><| (W1 / C)].
    have [_ _ _ defC] := Mtype34_facts.
    have [defUW1 _ _ _ _] := Frobenius_context FUW1.
    rewrite Frobenius_coprime_quotient // /normal ?subIset ?joing_subl //.
    split=> [|x /(Frobenius_reg_ker FUW1)->]; last exact: sub1G.
    have /Frobenius_context[ _ UnT _ _ _] := FUW1.
    rewrite /= defC (sol_der1_proper sol_M) //.
    have /sdprodP [_ <- _ _] := defM; have /sdprodP [_ <- _ _] := defHU.
    by exact: subset_trans (mulG_subr _ _) (mulG_subl _ _).
  have [nCU nCW1] := joing_subP nC_UW1; rewrite !card_quotient // -/u.
  by rewrite -indexgI setIC setIAC (coprime_TIg coUq) setI1g indexg1 -card_quotient.
 (* Third part of 11.8.1 *)
have En : n = (size S1)%:R.
  rewrite /FTtype345_ratio Edu Ed1 -/q -(@natrB _  _ 1 %N) // -SS1.
  by rewrite natrM mulfK // (eqC_nat _ 0); case: q pr_q.
admit.
Qed.

(* This will be (11.9). *)
Lemma FTtype34_structure :
  [/\ (*a*) {in S_ HC, forall zeta,
             orthogonal (tau (mu_ 0 - zeta) - \sum_j eta_ 0 j) codom_sigma},
      (*b*) (p < q)%N
    & (*c*) FTtype M == 3 /\ typeP_Galois MtypeP].
Proof. move: derM2_HC; admit. Qed.

End Eleven.
