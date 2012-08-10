(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum algC classfun character integral_char inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection7 PFsection8 PFsection9.
Require Import PFsection10 PFsection11 PFsection12.

(******************************************************************************)
(* This file covers Peterfalvi, Section 13: The Subgroups S and T.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.

Section Thirteen.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Section Thirteen_2_3_5_8.

(* These assumptions correspond to the part of Peterfalvi, Hypothesis (13.1)  *)
(* used to prove (13.2), (13.3), (13.5) and (13.8). Due to the limitations of *)
(* Coq's Section mechanism they will need to be repeated twice down this file *)
(* as we exploit the symmetry between S and T.                                *)

Variables S U W W1 W2 : {group gT}.
Hypotheses (maxS : S \in 'M) (defW : W1 \x W2 = W).
Hypotheses (StypeP : of_typeP S U defW).

Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation V := (cyclicTIset defW).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.
Local Notation C := 'C_U(`P)%G.
Local Notation "` 'C'" := 'C_`U(`P) (at level 0) : group_scope.
Local Notation PC := (`P <*> `C)%G.
Local Notation "` 'PC'" := (`P <*> `C) (at level 0) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.

Let notStype1 : FTtype S != 1%N. Proof. exact: FTtypeP_neq1 StypeP. Qed.
Let notStype5 : FTtype S != 5%N. Proof. exact: FTtype5_exclusion maxS. Qed.

Let pddS := FT_prDade_hyp maxS StypeP.
Let ptiWS : primeTI_hypothesis S PU defW := FT_primeTI_hyp StypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := StypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := StypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := StypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p := #|W2|.
Let q := #|W1|.
Let c := #|C|.
Let u := #|U : C|.

Let oU : #|U| = (u * c)%N. Proof. by rewrite mulnC Lagrange ?subsetIl. Qed.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.

Let qgt2 : q > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let pgt2 : p > 2. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coPUq : coprime #|PU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defS); have [[]] := StypeP. Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Local Open Scope ring_scope.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Local Notation Imu2 := (primeTI_Iirr ptiWS).
Let mu2_ i j := primeTIirr ptiWS i j.
Let mu_ := primeTIred ptiWS.
Local Notation chi_ j := (primeTIres ptiWS j).

Local Notation Idelta := (primeTI_Isign ptiWS).
Local Notation delta_ j := (primeTIsign ptiWS j).

Local Notation tau := (FT_Dade0 maxS).
Local Notation "chi ^\tau" := (tau chi).

Let calS0 := seqIndD PU S S`_\s 1.
Let rmR := FTtypeP_coh_base maxS StypeP.
Let scohS0 : subcoherent calS0 tau rmR.
Proof. exact: FTtypeP_subcoherent StypeP. Qed.

Let calS := seqIndD PU S P 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

Local Notation type34ker1 := (FTtype34_Fcore_kernel_trivial maxS StypeP).
Local Notation type34facts := (FTtype34_structure maxS StypeP).
Local Notation type2facts := (FTtypeII_prime_facts maxS StypeP).
Local Notation compl2facts := (compl_of_typeII maxS StypeP).
Local Notation compl3facts := (compl_of_typeIII maxS StypeP).

Local Notation H0 := (Ptype_Fcore_kernel StypeP).

Lemma Ptype_factor_prime : pdiv #|P / H0|%g = p.
Proof. exact: def_Ptype_factor_prime. Qed.
Local Notation pHbar_p := Ptype_factor_prime.

Lemma Ptype_Fcore_kernel_trivial : H0 = 1%G.
Proof.
apply: val_inj.
have [/type2facts[_ oP _]| /type34ker1[]//] := boolP (FTtype S == 2).
have [/and3P[]] := Ptype_Fcore_kernel_exists maxS StypeP notStype5.
case/maxgroupp=> /andP[/proper_sub sH0P nH0S] /subset_trans/(_ nH0S)nH0P _ _.
apply: card1_trivg; rewrite -(divg_indexS sH0P) -card_quotient //.
have [_ _ ->] := Ptype_Fcore_factor_facts maxS StypeP notStype5.
by rewrite pHbar_p -{}oP divnn ?cardG_gt0.
Qed.
Local Notation H0_1 := Ptype_Fcore_kernel_trivial.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel StypeP = C.
Proof.
apply: val_inj; rewrite [Ptype_Fcompl_kernel StypeP]unlock /= H0_1.
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.
Local Notation CHbar_C := Ptype_Fcompl_kernel_cent.

Lemma FTsupp0_neq0 M (maxM : M \in 'M) : 'A0(M : {group gT}) != set0.
Proof.
apply: contraNneq (proper_subn (mmax_proper maxM)) => A0_0.
by rewrite -(norm_FTsupp0 maxM) A0_0 -(setDv [1]) normD1 norms1.
Qed.

Import BGsection14.

(* This is Peterfalvi (13.2). *)
Lemma FTtypeP_facts :
  [/\ (*a*) [/\ pred2 2 3 (FTtype S), q < p -> FTtype S == 2,
                [Frobenius U <*> W1 = U ><| W1] & abelian U],
      (*b*) p.-abelem P /\ #|P| = p ^ q,
      (*c*) u <= (p ^ q).-1 %/ p.-1,
      (*d*) coherent calS S^# tau
    & (*e*) normedTI 'A0(S) G S /\ {in 'CF(S, 'A0(S)), tau =1 'Ind}]%N.
Proof.
have type23: pred2 2 3 (FTtype S).
  by rewrite /= -implyNb; apply/implyP=> /type34facts[_ _ [->]].
have [_ ntU _ tiFS] := compl_of_typeII_IV maxS StypeP notStype5.
have [_ /mulG_sub[_ sUPU] nPU tiPU] := sdprodP defPU.
have cUU: abelian U by case/orP: type23 => [/compl2facts | /compl3facts] [_ ->].
split.
- split=> //; first by rewrite ltnNge; apply: contraR => /type34facts[_ /ltnW].
  have [_ [_ _ nUW1 _] _ [_ _ sW2P _ prPUW1] _] := StypeP.
  apply/Frobenius_semiregularP=> // [|x /prPUW1 defCPUx].
    by rewrite sdprodEY ?coprime_TIg ?(coprimeSg sUPU).
  by apply/trivgP; rewrite /= -(setIidPr sUPU) setIAC defCPUx -tiPU setSI.
- by have [/type2facts[] | /type34ker1[]] := boolP (FTtype S == 2).
- have ->: u = #|U / C|%g by rewrite card_quotient ?normsI ?normG ?norms_cent.
  have p1gt0: (0 < p.-1)%N by rewrite -(subnKC pgt2).
  have [/typeP_Galois_P[]| /typeP_Galois_Pn[]]// := boolP (typeP_Galois StypeP).
    move=> _ _ [_ _]; rewrite pHbar_p CHbar_C // -/u -/q; apply: dvdn_leq.
    by rewrite divn_gt0 // -!subn1 leq_sub2r // (leq_exp2l 1) ltnW // ltnW.
  rewrite -/q CHbar_C pHbar_p => H1 [_ _ _ _ [agt1 a_dv_p1 _ [V /card_isog->]]].
  apply: leq_trans (_ : p.-1 ^ q.-1 <= _)%N; last first.
    have ltp1q: (p.-1 ^ q < p ^ q)%N by rewrite ltn_exp2r ?prednK // 2?ltnW.
    by rewrite leq_divRL // -expnSr (ltn_predK qgt2) -ltnS (ltn_predK ltp1q).
  rewrite dvdn_leq ?expn_gt0 ?p1gt0 // (dvdn_trans (cardSg (subsetT V))) //.
  by rewrite cardsT card_matrix mul1n dvdn_exp2r //= card_ord Zp_cast.
- have:= Ptype_core_coherence maxS StypeP notStype5; rewrite H0_1 CHbar_C.
  by rewrite (derG1P (abelianS _ cUU)) ?subsetIl ?(group_inj (joing1G _)).
have ntA0: 'A0(S) != set0 := FTsupp0_neq0 maxS.
have tiA0: normedTI 'A0(S) G S.
  apply/normedTI_memJ_P=> //; rewrite subsetT; split=> // x g A0x Gg.
  apply/idP/idP=> [A0xg | /(subsetP (FTsupp0_norm S))/memJ_norm->//].
  apply/idPn=> S'g; have Dx: x \in [set y in 'A0(S) | ~~ ('C[y] \subset S)].
    rewrite inE A0x; have [_ _ [_ _ _ wccA0 _] _] := pddS.
    have /imsetP[y Sy Dxy]: x ^ g \in x ^: S by rewrite wccA0 // mem_orbit.
    apply/subsetPn; exists (g * y^-1)%g; last by rewrite groupMr ?groupV.
    by rewrite !inE conjg_set1 conjgM Dxy conjgK.
  have [_ [_ /(_ x Dx) defL] /(_ x Dx)[_ _ []]] := FTsupport_facts maxS.
  have{defL} [maxL _] := mem_uniq_mmax defL; set L := 'N[x] in maxL *.
  rewrite -mem_iota !inE => ALx [/orP[Ltype1 _ | Ltype2]]; last first.
    by case/(_ _)/existsP=> // ? /Frobenius_of_typeF/(typePF_exclusion StypeP).
  have /Frobenius_kerP[_ _ _ regLF_L] := FTtype1_Frobenius maxL Ltype1.
  case/andP: ALx => A1'x /bigcupP[z A1z /setD1P[ntx cLz_z]]; case/negP: A1'x.
  rewrite ntx /'A1(L) -(Fcore_eq_FTcore _ _) ?(eqP Ltype1) //= in cLz_z A1z *.
  exact: subsetP (regLF_L z A1z) _ cLz_z.
have [|ddS1 tauS1_1] := Dade_normedTI_P _ _ ntA0 tiA0.
  by rewrite (subset_trans (FTsupp0_sub S)) ?setSD ?subsetT.
split=> //; apply: Dade_Ind => x A0x.
by rewrite (def_Dade_signalizer _ (Dade_sdprod ddS1)) ?tauS1_1.
Qed.

End Thirteen_2_3_5_8.

End Thirteen.
