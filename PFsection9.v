(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8.

(******************************************************************************)
(* This file covers Peterfalvi, Section 9: On the maximal subgroups of Types  *)
(* II, III and IV. Defined here:                                              *)
(*   Ptype_Fcore_kernel MtypeP ==                                             *)
(*      a maximal normal subgroup of M contained in H = M`_\F and contained   *)
(*      in 'C_H(U), where MtypeP : of_typeP M U W1 (and provided M is not of  *)
(*      type V).                                                              *)
(*   typeP_Galois MtypeP ==                                                   *)
(*      U acts irreducibly on H / H0 where H0 = Ptype_Fcore_kernel MtypeP     *)
(*      with MtypeP : of_typeP M U W1 as above (this implies the structure of *)
(*      M / H0 is that of a Galois group acting on the multiplicative and     *)
(*      additive groups of a finite field).                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.

Section Nine.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

(* Peterfalvi (9.1) is covered by BGsection3.Frobenius_Wielandt_fixpoint. *)

(* These assumptions correspond to Peterfalvi, Hypothesis (9.2). *)

Variables M U W1 : {group gT}.
Hypotheses (maxM : M \in 'M) (MtypeP: of_typeP M U W1).
Hypothesis notMtype5 : FTtype M != 5.
Local Notation H := (gval M)`_\F.
Local Notation W2 := 'C_H(gval W1).
Let q := #|W1|.

Let notMtype1 : FTtype M != 1%N.
Proof.
have notPF := FTtypePF_exclusion (conj _ MtypeP).
by apply/FTtypeP=> // [[U0 [/notPF]]].
Qed.

Let Mtype24 := compl_of_typeII_IV MtypeP maxM notMtype5.
Let ntU : U :!=: 1. Proof. by have [] := Mtype24. Qed.
Let pr_q : prime q. Proof. by have [] := Mtype24. Qed.
Let ntW2 : W2 != 1. Proof. by have [_ _ _ []] := MtypeP. Qed.

Lemma Ptype_Fcore_sdprod : H ><| (U <*> W1) = M.
Proof.
have [[_ _ _ defM] [_ _ nUW1 defM'] _ _ _] := MtypeP; rewrite -/H in defM'.
have{defM} [_ /= sW1M defM _ tiM'W1] := sdprod_context defM. 
have{defM'} [/= /andP[sHM' _] sUM' defM' nHU tiHU] := sdprod_context defM'.
rewrite sdprodE /= norm_joinEr // ?mulgA ?defM' //.
  by rewrite mulG_subG nHU (subset_trans sW1M) ?gFnorm.
rewrite setIC -(setIidPr sHM') setIA -group_modl //.
by rewrite (setIC W1) tiM'W1 mulg1 setIC tiHU.
Qed.
Local Notation defHUW1 := Ptype_Fcore_sdprod.

Lemma Ptype_Fcore_coprime : coprime #|H| #|U <*> W1|.
Proof.
by rewrite (coprime_sdprod_Hall defHUW1) ?(pHall_Hall (Fcore_Hall M)).
Qed.
Let coHUW1 := Ptype_Fcore_coprime.

Let not_cHU : ~~ (U \subset 'C(H)).
Proof. by have [_ [_ ->]] := typeP_context MtypeP. Qed.

Lemma Ptype_compl_Frobenius : [Frobenius U <*> W1 = U ><| W1].
Proof.
have [[_ _ ntW1 defM] [_ _ nUW1 defM'] _ [_ _ sW2H _ prM'W1] _] := MtypeP.
rewrite -/H -/W2 in defM' sW2H prM'W1.
have{defM} [_ _ _ tiM'W1] := sdprodP defM.
have{defM'} [_ /= sUM' _ _ tiHU] := sdprod_context defM'.
apply/Frobenius_semiregularP=> // [|x /prM'W1 defCx].
  by rewrite sdprodEY //; apply/trivgP; rewrite -tiM'W1 setSI.
apply/trivgP; rewrite -tiHU /= -{1}(setIidPl sUM') -setIA defCx.
by rewrite setICA setIA subsetIl.
Qed.
Local Notation frobUW1 := Ptype_compl_Frobenius.

Let nilH : nilpotent H. Proof. exact: Fcore_nil. Qed.
Let solH : solvable H. Proof. exact: nilpotent_sol. Qed.

(* This is Peterfalvi (9.3). *)
Lemma typeII_IV_core (p := #|W2|) :
  if FTtype M == 2 then 'C_H(U) = 1 /\ #|H| = (#|W2| ^ q)%N
  else [/\ prime p, 'C_H(U <*> W1) = 1 & #|H| = (p ^ q * #|'C_H(U)|)%N].
Proof.
have [_ _ nHUW1 _] := sdprodP defHUW1.
have /= [oH _ oH1] := Frobenius_Wielandt_fixpoint frobUW1 nHUW1 coHUW1 solH.
have [Mtype2 {oH}| notMtype2 {oH1}] := ifPn.
  suffices: 'C_H(U) = 1 by split=> //; exact: oH1.
  have [_ _ _ M'typeF defM'F] := compl_of_typeII MtypeP maxM Mtype2.
  have [_ _ [U0 [sU0U _]]] := M'typeF; rewrite {}defM'F => frobHU0.
  have /set0Pn[x U0x]: U0^# != set0.
    by rewrite setD_eq0 subG1; case/Frobenius_context: frobHU0.
  apply/trivgP; rewrite -(Frobenius_reg_ker frobHU0 U0x) setIS // -cent_cycle.
  by rewrite centS // cycle_subG (subsetP sU0U) //; case/setD1P: U0x.
have p_pr: prime p.
  case: ifP (FT_FPstructure gT) notMtype1 => [_ -> //| _ [W W1x W2x S T stG] _].
  have [_ _ _ _ /(_ M maxM notMtype1)[x defST]] := stG.
  without loss{defST} defSx: S T W1x W2x stG / M :=: S :^ x.
    by move=> IH; (case: defST; move: stG) => [|/FT_Pstructure_sym] /IH.
  have [[_ _ maxT] [defS defT _] [/idPn[]|Ttype2 _ _]] := stG.
    by rewrite -(FTtypeJ S x) -defSx.
  have defMx: M^`(1) ><| W1x :^ x = M by rewrite defSx derJ -sdprodJ defS.
  have /imsetP[y My defW1] := of_typeP_compl_conj defMx MtypeP.
  rewrite -[p](cardJg _ y) conjIg -centJ -FcoreJ conjGid //.
  rewrite defSx -defW1 FcoreJ centJ -conjIg cardJg (def_cycTIcompl stG).
  have [|V TtypeP] := compl_of_typeP defT maxT; first by rewrite (eqP Ttype2).
  by have [[]] := compl_of_typeII TtypeP maxT Ttype2.
rewrite -/H -/q -/p centY setICA -/W2 setIC in oH *.
suffices regUW2: 'C_W2(U) = 1 by rewrite -oH regUW2 cards1 exp1n mul1n.
apply: prime_TIg => //=; apply: contra not_cHU => /setIidPl cUW2.
rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl.
by rewrite -(@leq_pmul2l (p ^ q)) -?oH ?cUW2 //= expn_gt0 cardG_gt0.
Qed.

(* Existential witnesses for Peterfalvi (9.4). *)
Definition Ptype_Fcore_kernel of of_typeP M U W1 :=
  odflt 1%G [pick H0 : {group gT} | chief_factor M H0 H & 'C_H(U) \subset H0].
Let H0 := (Ptype_Fcore_kernel MtypeP).
Local Notation Hbar := (H / gval H0).
Let p := pdiv #|Hbar|.

(* This corresponds to Peterfalvi (9.4). *)
Lemma Ptype_Fcore_kernel_exists : chief_factor M H0 H /\ 'C_H(U) \subset H0.
Proof.
pose C := <<class_support 'C_H(U) H>> .
suffices [H1 maxH sCH1]: {H1 : {group gT} | maxnormal H1 H M & C \subset H1}.
  apply/andP; rewrite /H0 /Ptype_Fcore_kernel; case: pickP => // /(_ H1)/idP[].
  rewrite /chief_factor maxH Fcore_normal (subset_trans _ sCH1) ?sub_gen //.
  exact: sub_class_support.
apply/maxgroup_exists/andP; split.
  have snCH: 'C_H(U) <|<| H by rewrite nilpotent_subnormal ?subsetIl.
  by have [/setIidPl/idPn[] | // ] := subnormalEsupport snCH; rewrite centsC.
have [[_ [_ _ nUW1 _] _ _ _] [_ {3}<- nHUW1 _]] := (MtypeP, sdprodP defHUW1).
rewrite norms_gen // mulG_subG class_support_norm norms_class_support //.
by rewrite normsI ?norms_cent // join_subG normG.
Qed.

Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists. Qed.
Let ltH0H : H0 \proper H.
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.
Let nH0M : M \subset 'N(H0).
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.
Let sH0H : H0 \subset H. Proof. exact: proper_sub ltH0H. Qed.
Let nsH0H : H0 <| H.
Proof. by rewrite /normal sH0H (subset_trans (Fcore_sub _)). Qed.
Let minHbar : minnormal Hbar (M / H0).
Proof. exact: chief_factor_minnormal. Qed.
Let ntHbar : Hbar != 1. Proof. by case/mingroupp/andP: minHbar. Qed.
Let solHbar: solvable Hbar. Proof. by rewrite quotient_sol. Qed.
Let abelHbar : p.-abelem Hbar.
Proof. by have [] := minnormal_solvable minHbar _ solHbar. Qed.
Let p_pr : prime p. Proof. by have [/pgroup_pdiv[]] := and3P abelHbar. Qed.

(* This is Peterfalvi, Hypothesis (9.5). *)
Let C := 'C_U(Hbar | 'Q).
Let Ubar := U / C.
Let W2bar := 'C_Hbar(W1 / H0).
Let c := #|C|.
Let u := #|Ubar|.
Local Notation tau := (FT_Dade0 maxM).
Local Notation "chi ^\tau" := (tau chi).
Let calX := Iirr_kerD M^`(1) H 1.
Let calS := seqIndD M^`(1) M M`_\F 1.
Let X_ Y := Iirr_kerD M^`(1) H Y.
Let S_ Y := seqIndD M^`(1) M M`_\F Y.

Let defW2bar : W2bar = W2 / H0.
Proof.
rewrite coprime_quotient_cent ?(subset_trans _ nH0M) //.
  by have [_ /joing_subP[]] := sdprod_context defHUW1.
exact: coprimegS (joing_subr _ _) coHUW1.
Qed.

Let nsCUW1 : C <| U <*> W1.
Proof.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
have [_ [_ _ nUW1 _] _ _ _] := MtypeP.
rewrite /normal subIset ?joing_subl // normsI //.
  by rewrite join_subG normG; have [_ []] := MtypeP.
rewrite astabQ norm_quotient_pre ?norms_cent ?quotient_norms //.
exact: subset_trans sUW1M nH0M.
Qed.

Local Notation inMb := (coset (gval H0)).

(* This is Peterfalvi (9.6). *)
Lemma Ptype_Fcore_factor_facts : [/\ C != U, #|W2bar| = p & #|Hbar| = p ^ q]%N.
Proof.
have [defUW1 _ ntW1 _ _] := Frobenius_context Ptype_compl_Frobenius.
have /andP[coHU coHW1] : coprime #|H| #|U| && coprime #|H| #|W1|.
  by rewrite -coprime_mulr (sdprod_card defUW1).
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
have regUHb: 'C_Hbar(U / H0) = 1.
  have [_ sCH0] := Ptype_Fcore_kernel_exists.
  by rewrite -coprime_quotient_cent ?(nilpotent_sol nilH) ?quotientS1.
have ->: C != U.
  apply: contraNneq ntHbar => defU; rewrite -subG1 -regUHb subsetIidl centsC.
  by rewrite -defU -quotient_astabQ quotientS ?subsetIr.
have frobUW1b: [Frobenius U <*> W1 / H0 = (U / H0) ><| (W1 / H0)].
  have tiH0UW1 := coprime_TIg (coprimeSg sH0H coHUW1).
  have /isomP[inj_f im_f] := quotient_isom nH0UW1 tiH0UW1.
  have:= injm_Frobenius (subxx _) inj_f frobUW1.
  by rewrite im_f !morphim_restrm !(setIidPr _) ?joing_subl ?joing_subr.
have{frobUW1b} oHbar: #|Hbar| = (#|W2bar| ^ q)%N.
  have nHbUW1 : U <*> W1 / H0 \subset 'N(Hbar) := quotient_norms H0 nHUW1.
  have coHbUW1 : coprime #|Hbar| #|U <*> W1 / H0| by exact: coprime_morph.
  have [//|_ _ -> //] := Frobenius_Wielandt_fixpoint frobUW1b nHbUW1 coHbUW1 _.
  by rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg ?(coprimeSg sH0H).
have abelW2bar: p.-abelem W2bar := abelemS (subsetIl _ _) abelHbar.
rewrite -(part_pnat_id (abelem_pgroup abelW2bar)) p_part in oHbar *.
suffices /eqP cycW2bar: logn p #|W2bar| == 1%N by rewrite oHbar cycW2bar.
have cycW2: cyclic W2 by have [_ _ _ []] := MtypeP.
rewrite eqn_leq -abelem_cyclic //= -/W2bar {1}defW2bar quotient_cyclic //=.
rewrite lt0n; apply: contraNneq ntHbar => W2bar1.
by rewrite trivg_card1 oHbar W2bar1 exp1n.
Qed.

Lemma def_Ptype_factor_prime : prime #|W2| -> p = #|W2|.
Proof.
move=> prW2; suffices: p \in \pi(W2) by rewrite !(primes_prime, inE) // => /eqP.
rewrite mem_primes p_pr cardG_gt0; have [_ <- _] := Ptype_Fcore_factor_facts.
by rewrite defW2bar dvdn_quotient.
Qed.

(* The first assertion of (9.4)(b) (the rest is subsumed by (9.6)). *)
Lemma typeIII_IV_core_prime : FTtype M != 2 -> p = #|W2|.
Proof.
by have:= typeII_IV_core => /=; case: ifP => // _ [/def_Ptype_factor_prime].
Qed.

Let frobUW1c : [Frobenius U <*> W1 / C = Ubar ><| W1 / C].
Proof.
apply: Frobenius_quotient frobUW1 _ nsCUW1 _.
  by apply: nilpotent_sol; have [_ []] := MtypeP.
by have [] := Ptype_Fcore_factor_facts; rewrite eqEsubset subsetIl.
Qed.  

Definition typeP_Galois := acts_irreducibly U Hbar 'Q.

(* This is Peterfalvi (9.7)(a). *)
Lemma typeP_Galois_Pn :
    ~~ typeP_Galois ->
  {H1 : {group coset_of H0} |
    [/\ #|H1| = p, U / H0 \subset 'N(H1), [acts U, on H1 | 'Q],
        \big[dprod/1]_(w in W1 / H0) H1 :^ w = Hbar
      & let a := #|U : 'C_U(H1 | 'Q)| in
        [/\ a > 1, a %| p.-1, cyclic (U / 'C_U(H1 | 'Q))
          & exists V : {group 'rV['Z_a]_q.-1}, Ubar \isog V]]}.
Proof.
have [_ sUW1M defHUW1 nHUW1 _] := sdprod_context defHUW1.
have [nHU nHW1] := joing_subP nHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
have nUW1: W1 \subset 'N(U) by case: MtypeP => _ [].
rewrite /typeP_Galois acts_irrQ //= => not_minHbarU.
have [H1 minH1 sH1Hb]: {H1 | minnormal (gval H1) (U / H0) & H1 \subset Hbar}.
  by apply: mingroup_exists; rewrite ntHbar quotient_norms.
exists H1; have [defH1 | ltH1H] := eqVproper sH1Hb.
  by rewrite -defH1 minH1 in not_minHbarU.
have [/andP[ntH1 nH1U] _] := mingroupP minH1.
have actsUH1: [acts U, on H1 | 'Q].
  by rewrite -(cosetpreK H1) actsQ ?norm_quotient_pre.
have [nH0H abHbar] := (normal_norm nsH0H, abelem_abelian abelHbar).
have [neqCU _ oHbar] := Ptype_Fcore_factor_facts.
have nUW1b: W1 / H0 \subset 'N(U / H0) by exact: quotient_norms.
have oW1b: #|W1 / H0| = q.
  rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg //.
  by rewrite (coprimeSg sH0H) // (coprimegS (joing_subr U W1)).
have [oH1 defHbar]: #|H1| = p /\ \big[dprod/1]_(w in W1 / H0) H1 :^ w = Hbar.
  have nHbUW1: U <*> W1 / H0 \subset 'N(Hbar) by exact: quotient_norms.
  pose rUW1 := abelem_repr abelHbar ntHbar nHbUW1.
  have irrUW1: mx_irreducible rUW1.
    apply/abelem_mx_irrP/mingroupP; split=> [|H2]; first by rewrite ntHbar.
    case/andP=> ntH2 nH2UW1 sH2H; case/mingroupP: minHbar => _; apply=> //.
    by rewrite ntH2 -defHUW1 quotientMl // mulG_subG sub_abelian_norm.
  have nsUUW1: U / H0 <| U <*> W1 / H0 by rewrite quotient_normal // normalYl.
  pose rU := subg_repr rUW1 (normal_sub nsUUW1).
  pose V1 := rowg_mx (abelem_rV abelHbar ntHbar @* H1).
  have simV1: mxsimple rU V1 by exact/mxsimple_abelem_subg/mxsimple_abelemGP.
  have [W0 /subsetP sW01 [sumW0 dxW0]] := Clifford_basis irrUW1 simV1.
  have def_q: q = (#|W0| * \rank V1)%N.
    transitivity (\rank (\sum_(w in W0) V1 *m rUW1 w))%R.
      by rewrite sumW0 mxrank1 /= (dim_abelemE abelHbar) // oHbar pfactorK.
    rewrite (mxdirectP dxW0) -sum_nat_const; apply: eq_bigr => x /sW01/= Wx.
    by rewrite mxrankMfree ?row_free_unit ?repr_mx_unit.
  have oH1: #|H1| = (p ^ \rank V1)%N.
    by rewrite -{1}(card_Fp p_pr) -card_rowg rowg_mxK card_injm ?abelem_rV_injm.
  have oW0: #|W0| = q.
    apply/prime_nt_dvdP=> //; last by rewrite def_q dvdn_mulr.
    apply: contraTneq (proper_card ltH1H) => trivW0.
    by rewrite oHbar def_q trivW0 mul1n -oH1 ltnn.
  have q_gt0 := prime_gt0 pr_q.
  rewrite oH1 -(mulKn (\rank V1) q_gt0) -{1}oW0 -def_q divnn q_gt0.
  have defHbar: \big[dprod/1]_(w in W0) H1 :^ w = Hbar.
    have inj_rV_Hbar := rVabelem_injm abelHbar ntHbar.
    have/(injm_bigdprod _ inj_rV_Hbar)/= := bigdprod_rowg sumW0 dxW0.
    rewrite sub_im_abelem_rV rowg1 im_rVabelem => <- //=; apply: eq_bigr => w.
    by move/sW01=> Ww; rewrite abelem_rowgJ ?rowg_mxK ?abelem_rV_mK.
  have injW0: {in W0 &, injective (fun w => H1 :^ w)}.
    move=> x y Wx Wy /= eq_Hxy; apply: contraNeq ntH1 => neq_xy.
    rewrite -(conjsg_eq1 _ x) -[H1 :^ x]setIid {1}eq_Hxy; apply/eqP.
    rewrite (bigD1 y) // (bigD1 x) /= ?Wx // dprodA in defHbar.
    by case/dprodP: defHbar => [[_ _ /dprodP[_ _ _ ->] _]].
  have defH1W0: [set H1 :^ w | w in W0] = [set H1 :^ w | w in W1 / H0].
    apply/eqP; rewrite eqEcard (card_in_imset injW0) oW0 -oW1b leq_imset_card.
    rewrite andbT; apply/subsetP=> _ /imsetP[w /sW01/= Ww ->].
    move: Ww; rewrite norm_joinEr ?quotientMl // => /mulsgP[x w1 Ux Ww1 ->].
    by rewrite conjsgM (normsP nH1U) // mem_imset.
  have injW1: {in W1 / H0 &, injective (fun w => H1 :^ w)}.
    by apply/imset_injP; rewrite -defH1W0 (card_in_imset injW0) oW0 oW1b.
  by rewrite -(big_imset id injW1) -defH1W0 big_imset.
split=> //; set a := #|_ : _|; pose q1 := #|(W1 / H0)^#|.
have a_gt1: a > 1.
  rewrite indexg_gt1 subsetIidl /= astabQ -sub_quotient_pre //. 
  apply: contra neqCU => cH1U; rewrite (sameP eqP setIidPl) astabQ.
  rewrite -sub_quotient_pre // -(bigdprodEY defHbar) cent_gen centsC.
  by apply/bigcupsP=> w Ww; rewrite centsC centJ -(normsP nUW1b w) ?conjSg.
have Wb1: 1 \in W1 / H0 := group1 _.
have ->: q.-1 = q1 by rewrite -oW1b (cardsD1 1) Wb1.
have /cyclicP[h defH1]: cyclic H1 by rewrite prime_cyclic ?oH1.
have o_h: #[h] = p by rewrite defH1 in oH1.
have inj_Zp_h w := injm_Zp_unitm (h ^ w).
pose phi w := invm (inj_Zp_h w) \o restr_perm <[h ^ w]> \o actperm 'Q.
have dU w: w \in W1 / H0 -> {subset U <= 'dom (phi w)}.
  move=> Ww x Ux; have Qx := subsetP (acts_dom actsUH1) x Ux; rewrite inE Qx /=.
  rewrite im_Zp_unitm inE mem_morphpre //=; last first.
    by apply: Aut_restr_perm (actperm_Aut 'Q _); rewrite //= quotientT.
  rewrite cycleJ -defH1 !inE /=; apply/subsetP=> z H1w_z; rewrite inE actpermK.
  rewrite qactJ (subsetP nH0U) ?memJ_norm // normJ mem_conjg.
  by rewrite (subsetP nH1U) // -mem_conjg (normsP nUW1b) ?mem_quotient.
have Kphi w: 'ker (phi w) = 'C(H1 :^ w | 'Q).
  rewrite !ker_comp ker_invm -kerE ker_restr_perm defH1 -cycleJ.
  apply/setP=> x; rewrite !inE; congr (_ && _) => /=.
  by apply: eq_subset_r => h1; rewrite !inE actpermK.
have o_phiU w: w \in W1 / H0 -> #|phi w @* U| = a.
  move=> Ww; have [w1 Nw1 Ww1 def_w] := morphimP Ww.
  rewrite card_morphim Kphi (setIidPr _); last by apply/subsetP; exact: dU.
  rewrite /a indexgI /= !astabQ centJ def_w morphpreJ //.
  by rewrite -{1}(normsP nUW1 w1 Ww1) indexJg.
have a_dv_p1: a %| p.-1.
  rewrite -(o_phiU 1) // (dvdn_trans (cardSg (subsetT _))) // card_units_Zp //.
  by rewrite conjg1 o_h (@totient_pfactor p 1) ?muln1.
have cycZhw w: cyclic (units_Zp #[h ^ w]).
  rewrite -(injm_cyclic (inj_Zp_h w)) // im_Zp_unitm Aut_prime_cyclic //=.
  by rewrite -orderE orderJ o_h.
have cyc_phi1U: cyclic (phi 1 @* U) := cyclicS (subsetT _) (cycZhw 1).
split=> //; last have{cyc_phi1U a_dv_p1} [z def_z] := cyclicP cyc_phi1U.
  rewrite -(conjsg1 H1) -Kphi (isog_cyclic (first_isog_loc _ _)) //.
  by apply/subsetP; apply: dU.
have o_hw w: #[h ^ w] = #[h ^ 1] by rewrite !orderJ.
pose phi1 w x := eq_rect _ (fun m => {unit 'Z_m}) (phi w x) _ (o_hw w).
have val_phi1 w x: val (phi1 w x) = val (phi w x) :> nat.
  by rewrite /phi1; case: _ / (o_hw _).
have mem_phi1 w x: w \in W1 / H0 -> x \in U -> phi1 w x \in <[z]>%G.
  move=> Ww Ux; have: #|<[z]>%G| = a by rewrite /= -def_z o_phiU.
  rewrite /phi1; case: _ / (o_hw w) <[z]>%G => A oA /=.
  suffices <-: phi w @* U = A by rewrite mem_morphim // dU.
  by apply/eqP; rewrite (eq_subG_cyclic (cycZhw w)) ?subsetT // oA o_phiU.
have o_z: #[z] = a by rewrite orderE -def_z o_phiU.
pose phi0 w x := eq_rect _ (fun m => 'Z_m) (invm (injm_Zpm z) (phi1 w x)) _ o_z.
pose psi x := (\row_(i < q1) (phi0 (enum_val i) x * (phi0 1 x)^-1)%g)%R.
have psiM: {in U &, {morph psi: x y / x * y}}.
  have phi0M w: w \in W1 / H0 -> {in U &, {morph phi0 w: x y / x * y}}.
    move=> Ww x y Ux Uy; rewrite /phi0; case: (a) / (o_z) => /=.
    rewrite -morphM; first 1 [congr (invm _ _)] || by rewrite im_Zpm mem_phi1.
    by rewrite /phi1; case: _ / (o_hw w); rewrite /= -morphM ?dU.
  move=> x y Ux Uy; apply/rowP=> i; have /setD1P[_ Ww] := enum_valP i.
  by rewrite !{1}mxE !{1}phi0M // addrCA -addrA -opprD addrCA addrA.
suffices Kpsi: 'ker (Morphism psiM) = C.
  by exists [group of Morphism psiM @* U]; rewrite /Ubar -Kpsi first_isog.
apply/esym/eqP; rewrite eqEsubset; apply/andP; split.
  apply/subsetP=> x /setIP[Ux cHx]; rewrite -(bigdprodEY defHbar) in cHx.
  suffices phi0x1 w: w \in W1 / H0 -> phi0 w x = 1.
    rewrite !inE Ux; apply/eqP/rowP=> i; have /setD1P[_ Ww] := enum_valP i.
    by rewrite !mxE !phi0x1 ?mulgV.
  move=> Ww; apply: val_inj; rewrite /phi0; case: (a) / (o_z); congr (val _).
  suffices /eqP->: phi1 w x == 1 by rewrite morph1.
  rewrite -2!val_eqE [val _]val_phi1 -(o_hw w) [phi _ _]mker // Kphi.
  by apply: subsetP (astabS _ _) _ cHx; rewrite sub_gen // (bigcup_sup w).
have sKU: 'ker (Morphism psiM) \subset U by exact: subsetIl.
rewrite -quotient_sub1 -?(Frobenius_trivg_cent frobUW1c); last first.
  by apply: subset_trans (normal_norm nsCUW1); rewrite subIset ?joing_subl.
rewrite subsetI quotientS //= quotient_cents2r // subsetI.
rewrite (subset_trans (commSg W1 sKU)) ?commg_subl //= astabQ gen_subG /=.
apply/subsetP=> _ /imset2P[x w1 Kx Ww1 ->].
have:= Kx; rewrite -groupV 2!inE groupV => /andP[Ux /set1P/rowP psi_x'0].
have [nH0x Ux'] := (subsetP nH0U x Ux, groupVr Ux); pose x'b := (inMb x)^-1.
rewrite mem_morphpre ?groupR ?morphR //= ?(subsetP nH0W1) //.
have conj_x'b w: w \in W1 / H0 -> (h ^ w) ^ x'b = (h ^ w) ^+ val (phi 1 x^-1).
  move=> Ww; transitivity (Zp_unitm (phi w x^-1) (h ^ w)).
    have /morphpreP[_ /morphpreP[Px' Rx']] := dU w Ww x^-1 Ux'.
    rewrite invmK ?restr_permE ?cycle_id //.
    by rewrite actpermE qactJ groupV nH0x morphV.
  have:= Ww; rewrite -(setD1K Wb1) autE ?cycle_id // => /setU1P[-> // | W'w].
  have /eqP := psi_x'0 (enum_rank_in W'w w); rewrite 2!mxE enum_rankK_in //.
  rewrite -eq_mulgV1 -val_eqE /phi0; case: (a) / (o_z); rewrite /= val_eqE.
  rewrite (inj_in_eq (injmP _ (injm_invm _))) /= ?im_Zpm ?mem_phi1 //.
  by rewrite -2!val_eqE /= !val_phi1 // => /eqP->.
rewrite -sub_cent1 -(bigdprodEY defHbar) gen_subG; apply/bigcupsP=> w2 Ww2.
rewrite defH1 -cycleJ cycle_subG cent1C inE conjg_set1 !conjgM // conj_x'b //.
rewrite conjXg -!conjgM -conj_x'b ?groupM ?groupV ?mem_quotient //.
by rewrite !conjgM !conjgKV.
Qed.

(* This is Peterfalvi (9.7)(b). *)
(* Note that part of this statement feeds directly into the final chapter of  *)
(* the proof (BGappendixC), and is not used before, so it may be useful to    *)
(* reformulate to suit the needs of this part.                                *)
(*   For example, we supply separately the three component of the semi-direct *)
(* product isomorphism, because no use is made of the global isomorphism. We  *)
(* also state explicitly that the image of W2bar is Fp because this is the    *)
(* fact used in B & G, Appendix C, it is readily available during the proof,  *)
(* whereas it can only be derived from the original statement of (9.7)(b) by  *)
(* using Galois theory. Indeed the Galois part of the isomorphism is only     *)
(* needed for this -- so with the formulation below it will not be used.      *)
(*   In order to avoid the use of the Wedderburn theorem on finite division   *)
(* rings we build the field F from the enveloping algebra of the              *)
(* representation of U rather than its endomorphism ring: then the fact that  *)
(* Ubar is abelian yield commutativity directly.                              *)
Lemma typeP_Galois_P :
    typeP_Galois ->
  {F : finFieldType & {phi : {morphism Hbar >-> F}
     & {psi : {morphism U >-> {unit F}} & {eta : {morphism W1 >-> {perm F}}
   & forall alpha : {perm F}, reflect (rmorphism alpha) (alpha \in eta @* W1)
   & [/\ 'injm eta, {in Hbar & W1, morph_act 'Q 'P phi eta}
       & {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}]}
   & 'ker psi = C /\ {in Hbar & U, morph_act 'Q 'U phi psi}}
   & [/\ #|F| = (p ^ q)%N, isom Hbar [set: F] phi & phi @* W2bar = <[1%R : F]>]}
   & [/\ cyclic Ubar, coprime u p.-1 & u %| (p ^ q).-1 %/ p.-1]}.
Proof.
move=> irrU; have nUW1: W1 \subset 'N(U) by case: MtypeP => _ [].
have [_ sUW1M _ /joing_subP[nHU nHW1] _] := sdprod_context defHUW1.
have [nHbU nHbW1] := (quotient_norms H0 nHU, quotient_norms H0 nHW1).
have{sUW1M} /joing_subP[nH0U nH0W1] := subset_trans sUW1M nH0M.
have [ltCU oW2b oHb] := Ptype_Fcore_factor_facts.
pose rU := abelem_repr abelHbar ntHbar nHbU.
pose inHb := rVabelem abelHbar ntHbar; pose outHb := abelem_rV abelHbar ntHbar.
have{irrU} irrU: mx_irreducible rU by apply/abelem_mx_irrP; rewrite -acts_irrQ.
pose E_U := [pred A | (A \in enveloping_algebra_mx rU)%MS].
have cEE A: A \in E_U -> centgmx rU A.
  case/envelop_mxP=> z_ ->{A}; rewrite -memmx_cent_envelop linear_sum.
  rewrite summx_sub // => x Ux; rewrite linearZ scalemx_sub {z_}//=.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Uy.
  rewrite -repr_mxM // commgC 2?repr_mxM ?(groupR, groupM) // -/rU.
  apply/row_matrixP=> i; rewrite row_mul; move: (row i _) => h.
  have cHbH': (U / H0)^`(1) \subset 'C(Hbar).
    rewrite -quotient_der ?quotient_cents //.
    by have [_ []] := typeP_context MtypeP.
  apply: rVabelem_inj; rewrite rVabelemJ ?groupR //.
  by apply: (canLR (mulKg _)); rewrite -(centsP cHbH') ?mem_commg ?mem_rVabelem.
have{cEE} [F [outF [inF outFK inFK] E_F]]:
  {F : finFieldType & {outF : {rmorphism F -> 'M(Hbar)%Mg}
   & {inF : {additive _} | cancel outF inF & {in E_U, cancel inF outF}}
   & forall a, outF a \in E_U}}%R.
- pose B := row_base (enveloping_algebra_mx rU).
  have freeB: row_free B by exact: row_base_free.
  pose outF := [additive of vec_mx \o mulmxr B].
  pose inF := [additive of mulmxr (pinvmx B) \o mxvec].
  have E_F a: outF a \in E_U by rewrite !inE vec_mxK mulmx_sub ?eq_row_base.
  have inK: {in E_U, cancel inF outF}.
    by move=> A E_A; rewrite /= mulmxKpV ?mxvecK ?eq_row_base.
  have outI: injective outF := inj_comp (can_inj vec_mxK) (row_free_inj freeB).
  have outK: cancel outF inF by move=> a; apply: outI; rewrite inK ?E_F.
  pose one := inF 1%R; pose mul a b := inF (outF a * outF b)%R.
  have outM: {morph outF: a b / mul a b >-> a * b}%R.
    by move=> a b; rewrite inK //; apply: envelop_mxM; exact: E_F.
  have out0: outF 0%R = 0%R by exact: raddf0.
  have out1: outF one = 1%R by rewrite inK //; exact: envelop_mx1.
  have nzFone: one != 0%R by rewrite -(inj_eq outI) out1 out0 oner_eq0.
  have mulA: associative mul by move=> *; apply: outI; rewrite !{1}outM mulrA.
  have mulC: commutative mul.
    move=> a b; apply: outI; rewrite !{1}outM.
    by apply: cent_mxP (E_F a); rewrite memmx_cent_envelop cEE ?E_F.
  have mul1F: left_id one mul by move=> a; apply: outI; rewrite outM out1 mul1r.
  have mulD: left_distributive mul +%R%R.
    by move=> a1 a2 b; apply: canLR outK _; rewrite !raddfD mulrDl -!{1}outM.
  pose Fring_NC := RingType 'rV__ (ComRingMixin mulA mulC mul1F mulD nzFone).
  pose Fring := ComRingType Fring_NC mulC.
  have outRM: multiplicative (outF : Fring -> _) by [].
  have mulI (nza : {a | a != 0%R :> Fring}): GRing.rreg (val nza).
    case: nza => a /=; rewrite -(inj_eq outI) out0 => nzA b1 b2 /(congr1 outF).
    rewrite !{1}outM => /row_free_inj eqB12; apply/outI/eqB12.
    by rewrite row_free_unit (mx_Schur irrU) ?cEE ?E_F.
  pose inv (a : Fring) := oapp (fun nza => invF (mulI nza) one) a (insub a).
  have inv0: (inv 0 = 0)%R by rewrite /inv insubF ?eqxx.
  have mulV: GRing.Field.axiom inv.
    by move=> a nz_a; rewrite /inv insubT /= (f_invF (mulI (exist _ _ _))).
  pose Funit := FieldUnitMixin mulV inv0.
  pose FringUcl := @GRing.ComUnitRing.Class _ (GRing.ComRing.class Fring) Funit.
  have Ffield := @FieldMixin (GRing.ComUnitRing.Pack FringUcl nat) _ mulV inv0.
  pose F := FieldType (IdomainType _ (FieldIdomainMixin Ffield)) Ffield.
  by exists [finFieldType of F], (AddRMorphism outRM); first exists inF.
pose in_uF (a : F) : {unit F} := insubd (1 : {unit F}) a.
have in_uF_E a: a != 1 -> val (in_uF a) = a.
  by move=> nt_a; rewrite insubdK /= ?unitfE.
have [psi psiK]: {psi : {morphism U >-> {unit F}}
                      | {in U, forall x, outF (val (psi x)) = rU (inMb x)}}.
- pose psi x := in_uF (inF (rU (inMb x))).
  have psiK x: x \in U -> outF (val (psi x)) = rU (inMb x).
    move/(mem_quotient H0)=> Ux; have EUx := envelop_mx_id rU Ux.
    rewrite in_uF_E ?inFK //; apply: contraTneq (repr_mx_unitr rU Ux).
    by move/(canRL_in inFK EUx)->; rewrite rmorph0 unitr0.
  suffices psiM: {in U &, {morph psi: x y / x * y}} by exists (Morphism psiM).
  move=> x y Ux Uy /=; apply/val_inj/(can_inj outFK); rewrite rmorphM //.
  by rewrite !{1}psiK ?groupM // morphM ?(subsetP nH0U) ?repr_mxM ?mem_quotient.
have /trivgPn/sig2W[s W2s nts]: W2bar != 1 by rewrite -cardG_gt1 oW2b prime_gt1.
pose sb := outHb s; have [Hs cW1s] := setIP W2s.
have nz_sb: sb != 0%R by rewrite morph_injm_eq1 ?abelem_rV_injm.
pose phi' a : coset_of H0 := inHb (sb *m outF a)%R.
have Hphi' a: phi' a \in Hbar by exact: mem_rVabelem.
have phi'D: {in setT &, {morph phi' : a b / a * b}}.
  by move=> a b _ _; rewrite /phi' !raddfD [inHb _]morphM ?mem_im_abelem_rV.
have inj_phi': injective phi'.
  move=> a b /rVabelem_inj eq_sab; apply: contraNeq nz_sb.
  rewrite -[sb]mulmx1 idmxE -(rmorph1 outF) -subr_eq0 => /divff <-.
  by rewrite rmorphM mulmxA !raddfB /= eq_sab subrr mul0mx.
have injm_phi': 'injm (Morphism phi'D) by apply/injmP; exact: in2W.
have Dphi: 'dom (invm injm_phi') = Hbar.
  apply/setP=> h; apply/morphimP/idP=> [[a _ _ ->] // | Hh].
  have /cyclic_mxP[A E_A def_h]: (outHb h <= cyclic_mx rU sb)%MS.
    by rewrite -(mxsimple_cyclic irrU) ?submx1.
  by exists (inF A); rewrite ?inE //= /phi' inFK // -def_h [inHb _]abelem_rV_K.
have [phi [def_phi Kphi _ im_phi]] := domP _ Dphi.
have{Kphi} inj_phi: 'injm phi by rewrite Kphi injm_invm.
have{im_phi} im_phi: phi @* Hbar = setT by rewrite im_phi -Dphi im_invm.
have phiK: {in Hbar, cancel phi phi'} by rewrite def_phi -Dphi; exact: invmK.
have{def_phi Dphi injm_phi'} phi'K: cancel phi' phi.
  by move=> a; rewrite def_phi /= invmE ?inE.
have phi'1: phi' 1%R = s by rewrite /phi' rmorph1 mulmx1 [inHb _]abelem_rV_K.
have phi_s: phi s = 1%R by rewrite -phi'1 phi'K.
have phiJ: {in Hbar & U, forall h x, phi (h ^ inMb x) = phi h * val (psi x)}%R.
  move=> h x Hh Ux; have Uxb := mem_quotient H0 Ux.
  apply: inj_phi'; rewrite phiK ?memJ_norm ?(subsetP nHbU) // /phi' rmorphM.
  by rewrite psiK // mulmxA [inHb _]rVabelemJ // -/inHb [inHb _]phiK.
have Kpsi: 'ker psi = C.
  apply/setP=> x; rewrite 2!in_setI astabQ; apply: andb_id2l => Ux.
  have Ubx := mem_quotient H0 Ux; rewrite 3!inE (subsetP nH0U) //= inE.
  apply/eqP/centP=> [psi_x1 h Hh | cHx]; last first.
    by apply/val_inj; rewrite -[val _]mul1r -phi_s -phiJ // conjgE -cHx ?mulKg.
  red; rewrite (conjgC h) -[h ^ _]phiK ?memJ_norm ?(subsetP nHbU) ?phiJ //.
  by rewrite psi_x1 mulr1 phiK.
have etaP (w : subg_of W1): injective (fun a => phi (phi' a ^ inMb (val w))).
  case: w => w /=/(mem_quotient H0)/(subsetP nHbW1) => nHw a b eq_ab.
  apply/inj_phi'/(conjg_inj (inMb w)).
  by apply: (injmP _ inj_phi) eq_ab; rewrite memJ_norm ?mem_rVabelem.
pose eta w : {perm F} := perm (etaP (subg W1 w)).
have etaK: {in Hbar & W1, forall h w, eta w (phi h) = phi (h ^ inMb w)}.
  by move=> h w Hh Ww; rewrite /= permE subgK ?phiK.
have eta1 w: w \in W1 -> eta w 1%R = 1%R.
  move=> Ww; rewrite -phi_s etaK //.
  by rewrite conjgE (centP cW1s) ?mulKg ?mem_quotient.
have etaM: {in W1 &, {morph eta: w1 w2 / w1 * w2}}.
  move=> w1 w2 Ww1 Ww2; apply/permP=> a; rewrite -[a]phi'K permM.
  rewrite !etaK ?memJ_norm ?groupM ?(subsetP nHbW1) ?mem_quotient //.
  by rewrite -conjgM -morphM ?(subsetP nH0W1).
have etaMpsi a: {in U & W1, forall x w, 
  eta w (a * val (psi x)) = eta w a * val (psi (x ^ w)%g)}%R.
- move=> x w Ux Ww; rewrite -[a]phi'K (etaK _ w (Hphi' a) Ww).
  rewrite -!phiJ // ?memJ_norm ?(subsetP nHbW1, subsetP nUW1) ?mem_quotient //.
  rewrite etaK ?memJ_norm ?(subsetP nHbU) ?mem_quotient // -!conjgM.
  by rewrite conjgC -morphJ ?(subsetP nH0U x Ux, subsetP nH0W1 w Ww).
have psiJ: {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}.
  by move=> x w Ux Ww /=; rewrite -[val _]mul1r -(eta1 w Ww) -etaMpsi ?mul1r.
have etaRM w: w \in W1 -> rmorphism (eta w).
  move=> Ww; have nUw := subsetP nHbW1 _ (mem_quotient _ Ww).
  have etaD: additive (eta w).
    move=> a b; rewrite -[a]phi'K -[b]phi'K -!zmodMgE -!zmodVgE.
    rewrite -morphV // -morphM ?{1}etaK ?groupM ?groupV // conjMg conjVg.
    by rewrite morphM 1?morphV ?groupV // memJ_norm.
  do 2![split=> //] => [a b|]; last exact: eta1.
  rewrite -[a]outFK; have /envelop_mxP[d ->] := E_F a.
  rewrite raddf_sum mulr_suml ![eta w _](raddf_sum (Additive etaD)) mulr_suml.
  apply: eq_bigr => _ /morphimP[x Nx Ux ->]; move: {d}(d _) => dx.
  rewrite -[dx]natr_Zp scaler_nat !(mulrnAl, raddfMn); congr (_ *+ dx)%R.
  by rewrite -psiK //= outFK mulrC etaMpsi // mulrC psiJ.
have oF: #|F| = (p ^ q)%N by rewrite -cardsT -im_phi card_injm.
pose nF := <[1%R : F]>; have o_nF: #|nF| = p.
  by rewrite -orderE -phi_s (order_injm inj_phi) // (abelem_order_p abelHbar).
have cyc_uF := @field_unit_group_cyclic F.
exists F.
  exists phi; last first.
    split=> //; first exact/isomP; apply/esym/eqP; rewrite eqEcard o_nF -phi_s. 
    by rewrite (@cycle_subG F) mem_morphim //= card_injm ?subsetIl ?oW2b.
  exists psi => //; last first.
    by split=> // h x Hh Ux; rewrite qactJ (subsetP nH0U) ?phiJ.
  have inj_eta: 'injm (Morphism etaM).
    have /properP[_ [h Hh notW2h]]: W2bar \proper Hbar.
      by rewrite properEcard subsetIl oW2b oHb (ltn_exp2l 1) prime_gt1.
    apply/subsetP=> w /morphpreP[Ww /set1P/permP/(_ (phi h))].
    rewrite etaK // permE => /(injmP _ inj_phi) => chw.
    rewrite -(@prime_TIg _ W1 <[w]>) //; first by rewrite inE Ww cycle_id.
    rewrite proper_subn // properEneq cycle_subG Ww andbT.
    apply: contraNneq notW2h => defW1; rewrite inE Hh /= -defW1.
    rewrite quotient_cycle ?(subsetP nH0W1) // cent_cycle cent1C inE.
    by rewrite conjg_set1 chw ?memJ_norm // (subsetP nHbW1) ?mem_quotient.
  exists (Morphism etaM) => [alpha |]; last first.
    by split=> // h w Hh Ww /=; rewrite qactJ (subsetP nH0W1) -?etaK.
  pose autF (f : {perm F}) := rmorphism f. (* Bits of Galois theory... *)
  have [r prim_r]: {r : F | forall f g, autF f -> autF g -> f r = g r -> f = g}.
    have /cyclicP/sig_eqW[r def_uF] := cyc_uF [set: {unit F}]%G.
    exists (val r) => f g fRM gRM eq_fgr; apply/permP=> a.
    rewrite (_ : f =1 RMorphism fRM) // (_ : g =1 RMorphism gRM) //.
    have [-> | /in_uF_E <-] := eqVneq a 0%R; first by rewrite !rmorph0.
    have /cycleP[m ->]: in_uF a \in <[r]> by rewrite -def_uF inE.
    by rewrite val_unitX !rmorphX /= eq_fgr.
  have /sigW[P /and3P[Pr0 nP lePq]]:
    exists P: {poly F}, [&& root P r, all (mem nF) P & #|root P| <= q].
  - pose Mr := (\matrix_(i < q.+1) (sb *m outF (r ^+ i)))%R.
    have /rowV0Pn[v /sub_kermxP vMr0 nz_v]: kermx Mr != 0%R.
      rewrite kermx_eq0 neq_ltn ltnS (leq_trans (rank_leq_col Mr)) //.
      by rewrite (dim_abelemE abelHbar) // oHb pfactorK.
    pose P : {poly F} := (\poly_(i < q.+1) (v 0 (inord i))%:R)%R.
    have szP: size P <= q.+1 by exact: size_poly.
    exists P; apply/and3P; split.
    + apply/eqP/inj_phi'; congr (inHb _); rewrite rmorph0 mulmx0 -vMr0.
      rewrite horner_poly !raddf_sum mulmx_sum_row; apply: eq_bigr => i _.
      rewrite rowK inord_val //= mulr_natl rmorphMn -scaler_nat scalemxAr.
      by rewrite natr_Zp.
    + apply/(all_nthP 0%R)=> i /leq_trans/(_ szP) le_i_q.
      by rewrite coef_poly /= le_i_q mem_cycle.
    rewrite cardE -ltnS (leq_trans _ szP) //.
    rewrite max_poly_roots ?enum_uniq //; last first.
      by apply/allP=> r'; rewrite mem_enum.
    apply: contraNneq nz_v => /polyP P0; apply/eqP/rowP=> i; apply/eqP.
    have /eqP := P0 i; rewrite mxE coef0 coef_poly ltn_ord inord_val.
    have charF: p \in [char F]%R by rewrite !inE p_pr -order_dvdn -o_nF /=.
    by rewrite -(dvdn_charf charF) (dvdn_charf (char_Fp p_pr)) natr_Zp.
  have{Pr0 nP} fPr0 f: autF f -> root P (f r).
    move=> fRM; suff <-: map_poly (RMorphism fRM) P = P by exact: rmorph_root.
    apply/polyP=> i; rewrite coef_map.
    have [/(nth_default _)-> | lt_i_P] := leqP (size P) i; first exact: rmorph0.
    by have /cycleP[n ->] := all_nthP 0%R nP i lt_i_P; exact: rmorph_nat.
  apply: (iffP morphimP) => [[w _ Ww ->] | alphaRM]; first exact: etaRM.
  suffices /setP/(_ (alpha r)): [set (eta w) r | w in W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: etaRM.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: etaRM.
  rewrite (@cardsE F) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP _ inj_eta) => //; apply: eq_w12; exact: etaRM.
have isoUb: isog Ubar (psi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a in nF^#].
have unF_E: {in nF^#, cancel in_uF val} by move=> a /setD1P[/in_uF_E].
have unFg: group_set unF.
  apply/group_setP; split=> [|_ _ /imsetP[a nFa ->] /imsetP[b nFb ->]].
    have nF1: 1%R \in nF^# by rewrite !inE cycle_id oner_eq0.
    by apply/imsetP; exists 1%R => //; apply: val_inj; rewrite unF_E.
  have nFab: (a * b)%R \in nF^#.
    rewrite !inE mulf_eq0 negb_or.
    have [[-> /cycleP[m ->]] [-> /cycleP[n ->]]] := (setD1P nFa, setD1P nFb).
    by rewrite -natrM mem_cycle.
  by apply/imsetP; exists (a * b)%R => //; apply: val_inj; rewrite /= !unF_E.
have <-: #|Group unFg| = p.-1.
  by rewrite -o_nF (cardsD1 1 nF) group1 (card_in_imset (can_in_inj unF_E)).
have <-: #|[set: {unit F}]| = (p ^ q).-1.
  rewrite -oF -(cardC1 1) cardsT card_sub; apply: eq_card => a /=.
  by rewrite !inE unitfE.
rewrite /u (isog_cyclic isoUb) (card_isog isoUb) cyc_uF.
suffices co_u_p1: coprime #|psi @* U| #|Group unFg|.
  by rewrite -(Gauss_dvdr _ co_u_p1) mulnC divnK ?cardSg ?subsetT.
rewrite -(cyclic_dprod (dprodEY _ _)) ?cyc_uF //.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cyc_uF [set:_]%G))) ?subsetT.
apply/trivgP/subsetP=> _ /setIP[/morphimP[x Nx Ux ->] /imsetP[a nFa /eqP]].
have nCx: x \in 'N(C) by rewrite -Kpsi (subsetP (ker_norm _)).
rewrite -val_eqE (unF_E a) //; case/setD1P: nFa => _ /cycleP[n {a}->].
rewrite zmodXgE => /eqP def_psi_x; rewrite mker ?set11 // Kpsi coset_idr //.
apply/set1P; rewrite -set1gE -(Frobenius_trivg_cent frobUW1c) /= -/C.
rewrite inE mem_quotient //= -sub1set -quotient_set1 ?quotient_cents2r //.
rewrite gen_subG /= -/C -Kpsi; apply/subsetP=> _ /imset2P[_ w /set1P-> Ww ->].
have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
apply/kerP; rewrite (morphM, groupM) ?morphV ?groupV //.
apply/(canLR (mulKg _))/val_inj; rewrite psiJ // mulg1 def_psi_x.
exact: (rmorph_nat (RMorphism (etaRM w Ww))).
Qed.

(* First attempt at the proof. The LTac interpretation of this proof runs
   smoothly, but typechecking at Qed diverges and runs out of memory. The
   critical point seems to be the explicit definition of the finFieldType F;
   anything that uses that definition just causes the Coq kernel to blow up:
    admit. Qed. takes 1s before the definition, 6s after, and simply defining
    a constant of type {unit finF} causes the time to shoot up to 35s+.
Lemma typeP_Galois_P_failure :
    typeP_Galois ->
  {F : finFieldType & {phi : {morphism Hbar >-> F}
     & {psi : {morphism U >-> {unit F}} & {eta : {morphism W1 >-> {perm F}}
   & forall alpha : {perm F}, reflect (rmorphism alpha) (alpha \in eta @* W1)
   & [/\ 'injm eta, {in Hbar & W1, morph_act 'Q 'P phi eta}
       & {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}]}
   & 'ker psi = C /\ {in Hbar & U, morph_act 'Q 'U phi psi}}
   & [/\ #|F| = (p ^ q)%N, isom Hbar [set: F] phi & phi @* W2bar = <[1%R : F]>]}
   & [/\ cyclic Ubar, coprime u p.-1 & u %| (p ^ q).-1 %/ p.-1]}.
Proof.
move=> irrU; have [_ sUW1M defHUW1 nHUW1 _] := sdprod_context defHUW1.
have [nHU nHW1] := joing_subP nHUW1.
have nH0UW1 := subset_trans sUW1M nH0M; have [nH0U nH0W1] := joing_subP nH0UW1.
have nUW1: W1 \subset 'N(U) by case: MtypeP => _ [].
have [ltCU oW2b oHb] := Ptype_Fcore_factor_facts.
pose fT := 'rV['F_p](Hbar); pose phi := [morphism of abelem_rV abelHbar ntHbar].
pose phi' := rVabelem abelHbar ntHbar.
have phi'_inj: injective phi' by exact: rVabelem_inj.
have phi_inj: 'injm phi by exact: abelem_rV_injm.
have [_ [cHU' _] _ _] := typeP_context MtypeP.
have nHbU: U / H0 \subset 'N(Hbar) by exact: quotient_norms.
pose rU := abelem_repr abelHbar ntHbar nHbU.
pose E_U := enveloping_algebra_mx rU.
have{irrU} irrU: mx_irreducible rU by apply/abelem_mx_irrP; rewrite -acts_irrQ.
have /trivgPn/sig2W[s W2s nts]: W2bar != 1 by rewrite -cardG_gt1 oW2b prime_gt1.
pose Fone := phi s; have [Hs cW1s] := setIP W2s.
have nzFone: Fone != 0%R by rewrite morph_injm_eq1.
pose psi1 : 'M_('dim Hbar) -> fT := mulmx Fone.
have psi'P a: {A | (A \in E_U)%MS & a = psi1 A}.
  by apply/sig2_eqW/cyclic_mxP; rewrite -(mxsimple_cyclic irrU) ?submx1.
pose psi' a := s2val (psi'P a); pose Fmul (a b : fT) := (a *m psi' b)%R.
have Epsi' h: (psi' h \in E_U)%MS by rewrite /psi'; case: (psi'P h).
have Fmul1: left_id Fone Fmul by rewrite /Fmul /psi' => h; case: (psi'P h).
have cEE A: (A \in E_U)%MS -> centgmx rU A.
  case/envelop_mxP=> z_ ->{A}; rewrite -memmx_cent_envelop linear_sum.
  rewrite summx_sub // => x Ux; rewrite linearZ scalemx_sub {z_}//=.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Uy.
  rewrite -repr_mxM // commgC 2?repr_mxM ?(groupR, groupM) // -/rU.
  apply/row_matrixP=> i; rewrite row_mul; move: (row i _) => h.
  apply: phi'_inj; rewrite [phi' _]rVabelemJ -/phi' ?groupR //.
  apply/conjg_fixP/commgP/cent1P/(subsetP _ _ (mem_rVabelem _ _ _)).
  rewrite sub_cent1 // (subsetP (quotient_cents H0 cHU')) //.
  by rewrite quotientR ?mem_commg.
have psi1K A: (A \in E_U)%MS -> psi' (psi1 A) = A.
  move=> E_A; have/eqP := Fmul1 (psi1 A); rewrite -subr_eq0 -mulmxBr.
  apply: contraTeq; rewrite -[in ~~ _]subr_eq0; set D := (_ - A)%R => nzD.
  rewrite -(mul0mx _ D) (can_eq (mulmxK _)) ?(mx_Schur irrU) ?cEE //.
  by rewrite linearB addmx_sub ?Epsi' ?eqmx_opp.
have FmulC: commutative Fmul.
  move=> h1 h2; rewrite -{1}[h1]Fmul1 -{2}[h2]Fmul1 /Fmul.
  by rewrite (hom_envelop_mxC _ (Epsi' _)) ?centgmx_hom ?cEE ?Epsi'.
have FmulA: associative Fmul.
  move=> h1 h2 h3; rewrite /Fmul -{1}[h2]Fmul1 -!mulmxA psi1K //.
  by apply: envelop_mxM; exact: Epsi'.
have FmulD: left_distributive Fmul +%R%R by move=> ? ? ?; rewrite -mulmxDl.
pose Fring_NC := RingType fT (ComRingMixin FmulA FmulC Fmul1 FmulD nzFone).
pose Fring := ComRingType Fring_NC FmulC.
pose Finv (h : Fring) : Fring := psi1 (invmx (psi' h)).
have FmulV: GRing.Field.axiom Finv.
  move=> h nz_h; apply/mulmxKV/(mx_Schur irrU); first exact/cEE/Epsi'.
  by apply: contraNneq nz_h => h_0; rewrite -[h]Fmul1 /Fmul h_0 linear0.
have Finv0: (Finv 0 = 0)%R.
  rewrite /Finv (_ : psi' 0 = 0%:M)%R ?invmx_scalar ?invr0 /psi1 ?raddf0 //.
  by apply: (canLR_in psi1K); [exact: mem0mx | rewrite /psi1 raddf0].
pose Funit := FieldUnitMixin FmulV Finv0.
pose FringUcl := @GRing.ComUnitRing.Class fT (GRing.ComRing.class Fring) Funit.
have Ffield := @FieldMixin (GRing.ComUnitRing.Pack FringUcl fT) _ FmulV Finv0.
pose F := FieldType (IdomainType _ (FieldIdomainMixin Ffield)) Ffield.
pose finF := [finFieldType of F]; pose unitF := [finGroupType of {unit finF}].
(* admit / Qed slow down sharply from this point on. *)
pose in_uF (a : finF) : unitF := insubd (1 : {unit finF}) a.
have in_uF_E a: a != 1 -> val (in_uF a) = a by rewrite -unitfE; exact: insubdK.
(* admit / Qed diverge from this point on. *)
pose psi x := in_uF (psi1 (rU (coset H0 x))).
have psiE x: x \in U -> val (psi x) = psi1 (rU (coset H0 x)).
  move=> Ux; apply/in_uF_E/eqP=> /(canRL (repr_mxK rU (mem_quotient H0 Ux))).
  by apply/eqP; rewrite mul0mx.
have psiK x: x \in U -> psi' (val (psi x)) = rU (coset H0 x).
  by move=> Ux; rewrite psiE // psi1K ?envelop_mx_id ?mem_quotient.
have psiM: {in U &, {morph psi: x y / x * y}}.
  move=> x y Ux Uy; apply: val_inj; rewrite /= 2?{1}psiE ?groupM //=.
  rewrite -[(_ * _)%R]mulmxA; congr (_ *m _)%R; rewrite psiK //.
  by rewrite morphM ?(subsetP nH0U) // repr_mxM ?mem_quotient.
pose Mpsi := @Morphism gT [finGroupType of unitF] U psi psiM.
have Kpsi: 'ker Mpsi = C.
  apply/setP=> x; rewrite 2!in_setI astabQ; apply: andb_id2l => Ux.
  have Ubx := mem_quotient H0 Ux; rewrite 3!inE (subsetP nH0U) //= inE.
  apply/eqP/centP=> [cHx h Hh | cHx].
    apply/esym/commgP/conjg_fixP/(injmP _ phi_inj) => //.
      by rewrite memJ_norm ?(subsetP nHbU).
    by rewrite /phi /= (abelem_rV_J _ _ nHbU) -?psiK // cHx; exact: (@mulr1 F).
  apply/val_inj/phi'_inj; rewrite -[val _]Fmul1 /Fmul psiK //.
  by rewrite [phi' _]rVabelemJ // conjgE -cHx ?mulKg // mem_rVabelem.
pose nF := <[1%R : finF]>; have o_nF: #|nF| = p.
  by rewrite -orderE (abelem_order_p (mx_Fp_abelem _ _ p_pr)) ?inE.
have psiJ: {in Hbar & U, morph_act 'Q 'U (phi : coset_of H0 -> finF) psi}.
  move=> h x Hh Ux /=; rewrite qactJ (subsetP nH0U) // -['U%act _ _]/(_ *m _)%R.
  by rewrite psiK // -abelem_rV_J ?mem_quotient.
have etaP w1: w1 \in W1 -> injective (fun a => phi (phi' a ^ coset H0 w1)).
  move/(mem_quotient H0)/(subsetP (quotient_norms _ nHW1)) => nHw a b eq_ab.
  apply/phi'_inj/(conjg_inj (coset H0 w1)).
  by apply: (injmP _ phi_inj); rewrite // memJ_norm ?mem_rVabelem.
pose eta w1 : {perm finF} := perm (etaP _ (subgP (subg W1 w1))).
have nHUW1b := quotient_norms H0 nHUW1.
pose rUW1 := abelem_repr abelHbar ntHbar nHUW1b.
have rUW1E x: x \in U -> rUW1 (coset H0 x) = rU (coset H0 x).
  have sUUW1b := quotientS H0 (joing_subl U W1).
  by move/(mem_quotient H0); exact: eq_abelem_subg_repr.
have eta1 w: eta w 1%R = 1%R.
  rewrite permE [phi' _]abelem_rV_K // conjgE (centP cW1s) ?mulKg //.
  by rewrite mem_quotient ?subgP.
have etaM: {in W1 &, {morph eta: w1 w2 / w1 * w2}}.
  move=> w1 w2 Ww1 Ww2; apply/permP=> h; rewrite !permE /= !permE.
  rewrite !subgK ?groupM // [coset H0 _]morphM ?(subsetP nH0W1) // conjgM.
  rewrite {2}/phi' abelem_rV_K // memJ_norm ?mem_quotient ?mem_rVabelem //.
  by rewrite (subsetP (quotient_norms H0 nHW1)) ?mem_quotient.
have etaEpsi: {in U & W1, forall x w, val (psi (x ^ w)) = eta w (val (psi x))}.
  move=> x w Ux Ww; have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
  have [nH0x nH0w] := (subsetP nH0U x Ux, subsetP nH0W1 w Ww).
  rewrite permE subgK // !{1}psiE // -!rUW1E //.
  have /(mem_quotient H0)UW1x: x \in U <*> W1 by rewrite mem_gen ?inE ?Ux.
  have /(mem_quotient H0)UW1w: w \in U <*> W1 by rewrite mem_gen ?inE ?Ww ?orbT.
  rewrite -(rVabelemJ _ _ nHUW1b) // [phi _]rVabelemK -/rUW1.
  rewrite [psi1]lock morphJ // !repr_mxM ?groupM ?groupV // -lock.
  rewrite /psi1 !mulmxA; congr (_ *m _ *m _)%R; rewrite -abelem_rV_J ?groupV //.
  by rewrite conjgE (centP cW1s) ?mulKg // groupV mem_quotient.
have eta_Aut w: w \in W1 -> rmorphism (eta w).
  move=> Ww; have nUw := subsetP (quotient_norms H0 nHW1) _ (mem_quotient _ Ww).
  have etaD: additive (eta w).
    move=> a b; rewrite !permE subgK //.
    rewrite [phi' _]morphM ?morphV ?mem_im_abelem_rV //= -/phi'.
    by rewrite conjMg conjVg morphM ?morphV ?groupV ?memJ_norm ?mem_rVabelem.
  do 2![split=> //] => a b; have [_ /envelop_mxP[b_ ->] {b}->] := psi'P b.
  rewrite [psi1 _]mulmx_sumr mulr_sumr [eta w _](raddf_sum (Additive etaD)).
  rewrite [s in (_ * s)%R](raddf_sum (Additive etaD)) mulr_sumr.
  apply: eq_bigr => _ /morphimP[x nH0x Ux ->]; move: (b_ _) => {b_}bx.
  rewrite -scalemxAr -(natr_Zp bx) scaler_nat !(raddfMn, mulrnAr) -/(psi1 _).
  congr (_ *+ bx)%R => {bx}; rewrite -psiE //= -etaEpsi // !permE subgK //.
  have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
  rewrite -![(_ * _)%R]/(_ *m _)%R !psiK // -abelem_rV_J ?mem_quotient //.
    rewrite (morphJ _ nH0x) ?(subsetP nH0W1) // -conjgM -conjgC conjgM.
    by rewrite [phi' _]rVabelemJ ?mem_quotient.
  rewrite memJ_norm ?mem_rVabelem ?(subsetP (quotient_norms _ nHW1)) //.
  exact: mem_quotient.
have oF: #|finF| = (p ^ q)%N by rewrite -cardsT -card_rVabelem im_rVabelem.
have cyc_uF (uG : {group unitF}): cyclic uG. (* This should be in cyclic! *)
  apply: field_mul_group_cyclic (val : unitF -> _) _ _ => // x _.
  by split=> /eqP ?; exact/eqP.
exists finF.
  exists phi; last first.
    split=> //; first by apply/isomP; rewrite im_abelem_rV.
    apply/esym/eqP; rewrite eqEcard card_injm ?subsetIl // oW2b o_nF leqnn.
    by rewrite cycle_subG mem_morphim.
  pose autF (f : {perm finF}) := rmorphism f. (* Bits of Galois theory... *)
  have [r prim_r]: {r : F | forall f g, autF f -> autF g -> f r = g r -> f = g}.
    have /cyclicP/sig_eqW[r def_uF] := cyc_uF [set: unitF]%G.
    have exp_r m: (val r ^+ m)%R = val (r ^+ m).
      by case: m => //; elim=> //= m <-.
    exists (val r) => f g fRM gRM eq_fgr; apply/permP=> a.
    rewrite (_ : f =1 RMorphism fRM) // (_ : g =1 RMorphism gRM) //.
    have [-> | /in_uF_E <-] := eqVneq a 0%R; first by rewrite !rmorph0.
    have /cycleP[m ->]: in_uF a \in <[r]> by rewrite -def_uF inE.
    by rewrite -exp_r !rmorphX /= eq_fgr.
  have inj_eta: 'injm (Morphism etaM).
    have /properP[_ [h Hh notW2h]]: W2bar \proper Hbar.
      by rewrite properEcard subsetIl oW2b oHb (ltn_exp2l 1) prime_gt1.
    apply/subsetP=> w /morphpreP[Ww /set1P/permP/(_ (phi h))].
    rewrite !permE subgK // /phi' abelem_rV_K // => chw.
    rewrite -(@prime_TIg _ W1 <[w]>) //; first by rewrite inE Ww cycle_id.
    rewrite proper_subn // properEneq cycle_subG Ww andbT.
    apply: contraNneq notW2h => defW1; rewrite inE Hh /= -defW1.
    rewrite quotient_cycle ?(subsetP nH0W1) // cent_cycle cent1C inE.
    have Hhw: h ^ coset H0 w \in Hbar.
      by rewrite memJ_norm ?(subsetP (quotient_norms _ nHW1)) ?mem_quotient.
    by rewrite conjg_set1 sub1set inE -(inj_in_eq (injmP _ phi_inj)) ?chw.
  have /sigW[P /and3P[Pr0 nP lePq]]:
    exists P : {poly F}, [&& root P r, all (mem nF) P & #|root P| <= q].
  - pose Mr := (\matrix_(i < q.+1) (r ^+ i))%R.
    have /rowV0Pn[v /sub_kermxP vMr0 nz_v]: kermx Mr != 0%R.
      rewrite kermx_eq0 neq_ltn ltnS (leq_trans (rank_leq_col Mr)) //.
      by rewrite (dim_abelemE abelHbar) // oHb pfactorK.
    pose P : {poly finF} := (\poly_(i < q.+1) (v 0 (inord i))%:R)%R.
    have szP: size P <= q.+1 by exact: size_poly.
    exists P; apply/and3P; split.
    + apply/eqP; rewrite -vMr0 mulmx_sum_row horner_poly.
      apply: eq_bigr => i _; rewrite rowK inord_val // mulr_natl -scaler_nat.
      by rewrite natr_Zp.
    + apply/(all_nthP 0%R)=> i /leq_trans/(_ szP) le_i_q.
      by rewrite coef_poly /= le_i_q mem_cycle.
    rewrite cardE -ltnS (leq_trans _ szP) //.
    rewrite (@max_poly_roots finF) ?enum_uniq //; last first.
      by apply/allP=> r'; rewrite mem_enum.
    apply: contraNneq nz_v => /polyP P0; apply/eqP/rowP=> i; apply/eqP.
    have /eqP := P0 i; rewrite mxE coef0 coef_poly ltn_ord inord_val.
    have charF: p \in [char F]%R by rewrite !inE p_pr -order_dvdn -{2}o_nF /=.
    by rewrite -(dvdn_charf charF) (dvdn_charf (char_Fp p_pr)) natr_Zp.
  exists Mpsi => //; exists (Morphism etaM) => [alpha |]; last first.
    split=> // h w Hh Ww /=; rewrite /aperm permE subgK // /phi' abelem_rV_K //.
    by congr (phi _); rewrite qactJ (subsetP nH0W1).
  have{Pr0 nP} fPr0 f: autF f -> root P (f r).
    move=> fRM; suff <-: map_poly (RMorphism fRM) P = P by exact: rmorph_root.
    apply/polyP=> i; rewrite coef_map.
    have [/(nth_default _)-> | lt_i_P] := leqP (size P) i; first exact: rmorph0.
    by have /cycleP[n ->] := all_nthP 0%R nP i lt_i_P; exact: rmorph_nat.
  apply: (iffP morphimP) => [[w _ Ww ->] | alphaRM]; first exact: eta_Aut.
  suffices /setP/(_ (alpha r)): [set (eta w) r | w in W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: eta_Aut.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: eta_Aut.
  rewrite (@cardsE finF) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP _ inj_eta) => //; apply: eq_w12; exact: eta_Aut.
have isoUb: isog Ubar (Mpsi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a in nF^#].
have unF_E: {in nF^#, cancel in_uF val} by move=> a /setD1P[/in_uF_E].
have unFg: @group_set unitF unF.
  apply/group_setP; split=> [|_ _ /imsetP[a nFa ->] /imsetP[b nFb ->]].
    have nF1: 1%R \in nF^# by rewrite !inE cycle_id andbT.
    by apply/imsetP; exists 1%R => //; apply: val_inj; rewrite unF_E.
  have nFab: (a * b)%R \in nF^#.
    rewrite !inE mulf_eq0 negb_or.
    have [[-> /cycleP[m ->]] [-> /cycleP[n ->]]] := (setD1P nFa, setD1P nFb).
    by rewrite -natrM mem_cycle.
  by apply/imsetP; exists (a * b)%R => //; apply: val_inj; rewrite /= !unF_E.
have <-: #|Group unFg| = p.-1.
  by rewrite -o_nF (cardsD1 1 nF) group1 (card_in_imset (can_in_inj unF_E)).
have <-: #|[set: unitF]| = (p ^ q).-1.
  rewrite -oF -(cardC1 1) cardsT card_sub; apply: eq_card => a /=.
  by rewrite !inE unitfE.
rewrite /u (isog_cyclic isoUb) (card_isog isoUb) cyc_uF.
suffices co_u_p1: coprime #|Mpsi @* U| #|Group unFg|.
  by rewrite -(Gauss_dvdr _ co_u_p1) mulnC divnK ?cardSg ?subsetT.
rewrite -(cyclic_dprod (dprodEY _ _)) ?cyc_uF //.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cyc_uF [set:_]%G))) ?subsetT.
apply/trivgP/subsetP=> _ /setIP[/morphimP[x Nx Ux ->] /imsetP[a nFa /eqP]].
rewrite -val_eqE (unF_E a) //; case/setD1P: nFa => _ /cycleP[n {a}->].
rewrite FinRing.zmodXgE => /eqP def_psi_x.
have nCx: x \in 'N(C) by rewrite -Kpsi (subsetP (ker_norm _)).
rewrite mker ?set11 // Kpsi coset_idr //; apply/set1P; rewrite -set1gE.
rewrite -quotient1 -(Frobenius_trivg_cent frobUW1).
have solU: solvable U by apply: nilpotent_sol; case: MtypeP => _ [].
have nCW1: W1 \subset 'N(C).
  by rewrite normsI //= astabQ norm_quotient_pre ?norms_cent ?quotient_norms.
rewrite coprime_quotient_cent ?(Frobenius_coprime frobUW1) ?subsetIl //= -/C.
rewrite inE mem_quotient //= -/C -sub1set -quotient_set1 ?quotient_cents2r //.
rewrite gen_subG /= -/C -Kpsi; apply/subsetP=> _ /imset2P[_ w /set1P-> Ww ->].
have Uxw: x ^ w \in U by rewrite memJ_norm ?(subsetP nUW1).
apply/kerP; rewrite (morphM, groupM) ?morphV ?groupV //.
apply/(canLR (mulKg _))/val_inj; rewrite etaEpsi // mulg1 def_psi_x.
exact: (rmorph_nat (RMorphism (eta_Aut w Ww))).
Qed.
*)

Local Open Scope ring_scope.

Local Notation H0Cg := (gval H0 <*> C).
Local Notation H0C := [group of H0Cg].
Local Notation HCg := (H <*> C).
Local Notation HC := [group of HCg].
Local Notation HUg := (gval M)^`(1)%g.
Local Notation HU := M^`(1)%G.
Local Notation U'g := (gval U)^`(1)%g.
Local Notation U' := U^`(1)%G.
Local Notation H0U'g := (gval H0 <*> U')%g.
Local Notation H0U' := (H0 <*> U^`(1))%G.
Local Notation H0C'g := (gval H0 <*> C^`(1))%g.
Local Notation H0C' := [group of H0C'g].

Let defM : HU ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = HU. Proof. by have [_ []] := MtypeP. Qed.

Lemma Ptype_Fcore_extensions_normal : [/\ H0C <| M, HC <| M & H0C' <| M].
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have [sHM sUM] := (subset_trans sHHU sHUM, subset_trans sUHU sHUM).
have sCM: C \subset M by rewrite subIset ?sUM.
have sH0C_M: H0C \subset M by rewrite /normal join_subG (subset_trans sH0H).
have [nH0C nH0_H0C] := (subset_trans sCM nH0M, subset_trans sH0C_M nH0M).
have nsH0C: H0C <| M.
  rewrite /normal sH0C_M -defM sdprodEY //= -defHU sdprodEY //= -joingA.
  rewrite join_subG andbC normsY ?(normal_norm nsCUW1) //=; last first.
    by rewrite (subset_trans _ nH0M) // join_subG sUM.
  rewrite -[H0Cg]quotientYK // -{1}(quotientGK nsH0H) morphpre_norms //=.
  by rewrite cents_norm // centsC -quotient_astabQ quotientS ?subsetIr.
split=> //; first by rewrite /= -(joing_idPl sH0H) -joingA normalY ?gFnormal.
suffices ->: H0C' :=: H0 <*> H0C^`(1).
  rewrite normalY ?(char_normal_trans (der_char _ _)) //.
  by rewrite /normal (subset_trans sH0H).
rewrite /= -2?quotientYK ?quotient_der ?(subset_trans (der_sub _ _)) //=.
by rewrite quotientYidl.
Qed.
Local Notation nsH0xx_M := Ptype_Fcore_extensions_normal.

Let isIndHC (zeta : 'CF(M)) :=
  [/\ zeta 1%g = (q * u)%:R, zeta \in S_ H0C
    & exists2 xi : 'CF(HC), xi \is a linear_char & zeta = 'Ind xi].

Let redM := [predC irr M].
Let mu_ := filter redM (S_ H0).

(* This subproof is shared between (9.8)(b) and (9.9)(b). *)
Let nb_redM_H0 : size mu_ = p.-1 /\ {subset mu_ <= S_ H0C}.
Proof.
have centDD := FT_cDade_hyp maxM MtypeP; pose W := W1 <*> W2.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have nb_redM (K : {group gT}):
  K <| M -> K \subset HU -> K :&: H = H0 -> count redM (S_ K) = p.-1.
- move=> nsKM sKHU tiKHbar; have [sKM nKM] := andP nsKM; pose b A := (A / K)%g.
  have [_ /= cycDD _ _] := centDD; rewrite -/W in cycDD.
  have[[_ ntW1 hallW1 cycW1] [_ sW2HU cycW2 prW1HU] [defW oddW]] := cycDD.
  have coHU_W1: coprime #|HU| #|W1|.
    by rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM).
  have [nKHU nKW1] := (subset_trans sHUM nKM, subset_trans sW1M nKM).
  have [nKW2 coKW1] := (subset_trans sW2HU nKHU, coprimeSg sKHU coHU_W1).
  have oW2b: #|b W2| = p.
    have [_ <- _] := Ptype_Fcore_factor_facts; rewrite defW2bar.
    rewrite !card_quotient ?(subset_trans (subset_trans sW2HU sHUM)) //.
    by rewrite -tiKHbar -indexgI /= -setIA setIIr (setIC K) indexgI /=.
  have{cycW2} cycW2b: cyclic (b W2) by exact: quotient_cyclic.
  have cycDDb: cyclicDade_hypothesis (b M) (b HU) (b W) (b W1) (b W2).
    split; last 1 first.
    + have nKW: W \subset 'N(K) by rewrite join_subG nKW1.
      rewrite (morphim_coprime_dprod _ nKW) ?morphim_odd //.
      by rewrite coprime_sym (coprimeSg sW2HU).
    + have isoW1: W1 \isog b W1 by rewrite quotient_isog ?coprime_TIg.
      rewrite -(isog_eq1 isoW1) morphim_cyclic ?morphim_Hall //.
      by rewrite (morphim_coprime_sdprod _ nKM).
    rewrite -cardG_gt1 oW2b ?prime_gt1 ?morphimS //=.
    split=> // Kx /setD1P[ntKx /morphimP[x nKx W1x Dx]] /=.
    have solHU := solvableS sHUM (mmax_sol maxM).
    rewrite -cent_cycle -cycle_eq1 Dx -quotient_cycle // in ntKx *.
    rewrite -?coprime_quotient_cent ?(coprimegS _ coHU_W1) ?cycle_subG //.
    rewrite cent_cycle prW1HU // !inE W1x andbT -cycle_eq1.
    rewrite -(isog_eq1 (quotient_isog _ _)) ?cycle_subG // in ntKx.
    by rewrite coprime_TIg ?(coprimegS _ coKW1) ?cycle_subG.
  pose muK (j : Iirr (b W2)) :=
    (Dade_mu (M / K) [group of b W] (W1 / K) j %% K)%CF.
  have inj_muK: injective muK.
    by move=> j1 j2 /(can_inj (cfModK nsKM))/(Dade_mu_inj cycDDb).
  transitivity (size (image muK (predC1 0))); last first.
    by rewrite size_map -cardE cardC1 card_Iirr_abelian ?oW2b ?cyclic_abelian.
  rewrite count_filter; apply: perm_eq_size.
  apply: uniq_perm_eq => [||phi]; first by rewrite filter_uniq ?seqInd_uniq.
    by apply/dinjectiveP=> j1 j2 _ _ /inj_muK.
  have nsKHU: K <| HU := normalS sKHU sHUM nsKM.
  rewrite mem_filter; apply/andP/imageP=> [[red_phi] | [j nz_j ->]].
    case/seqIndP=> s /setDP[]; rewrite !inE /= => kersK kers'H Dphi.
    pose s1 := quo_Iirr K s.
    have{Dphi} Dphi: phi = ('Ind 'chi_s1 %% K)%CF.
      rewrite quo_IirrE // cfIndQuo ?gFnormal // cfQuoK ?Dphi //.
      by rewrite sub_cfker_Ind_irr.
    have:= (Dade_Ind_chi'_irr cycDDb) s1; set im_chi := codom _ => chi_s1.
    have{chi_s1 im_chi} /imageP[j _ Ds1]: s1 \in im_chi.
      apply: contraR red_phi => /chi_s1[{chi_s1}/= /irrP[s2 Ds2] _].
      by rewrite Dphi Ds2 cfMod_irr.
    exists j; last by rewrite Dphi Ds1 Dade_Ind_chi.
    apply: contraNneq kers'H => j0; rewrite -(quo_IirrK _ kersK) ?mod_IirrE //.
    by rewrite -/s1 Ds1 j0 Dade_chi0 ?cfMod_cfun1 // cfker_cfun1.
  have red_j: redM (muK j).
    apply: contra (Dade_mu_not_irr cycDDb j) => /= /irrP[s Ds].
    by rewrite -[_ j](cfModK nsKM) -/(muK _) Ds cfQuo_irr // -Ds cfker_Mod.
  have [s Ds]: exists s, muK j = 'Ind[M, HU] 'chi_s.
    rewrite /muK -(Dade_Ind_chi cycDDb); set s := _ j; pose s1 := mod_Iirr s.
    exists s1; rewrite -(cfModK nsKHU 'chi_s) -mod_IirrE // -/s1.
    have kers1K: K \subset cfker 'chi_s1 by rewrite mod_IirrE ?cfker_Mod.
    by rewrite cfIndQuo ?gFnormal ?cfQuoK ?sub_cfker_Ind_irr.
  split=> //; apply/seqIndP; exists s; rewrite // !inE andbC.
  rewrite -!(@sub_cfker_Ind_irr _ M) ?gFnorm // -Ds cfker_Mod //=.
  have{s Ds}[j1 Dj1]: exists j1 : Iirr W2, muK j = Dade_mu M [group of W] W1 j1.
    have:= (Dade_Ind_chi'_irr cycDD) s; set im_chi := codom _ => chi_s.
    suffices /imageP[j1 _ Dj1]: s \in im_chi.
      by exists j1; rewrite Ds Dj1 Dade_Ind_chi.
    by apply: contraR red_j => /chi_s[] /=; rewrite Ds.
  rewrite Dj1 -(Dade_Ind_chi cycDD) sub_cfker_Ind_irr ?gFnorm //.
  rewrite (not_cDade_core_sub_cfker_chi centDD) //.
  rewrite -(inj_eq (Dade_irr_inj cycDD)) -(inj_eq irr_inj) Dade_chi0 //.
  rewrite irr_eq1 -subGcfker -(sub_cfker_Ind_irr _ _ sHUM) ?gFnorm //.
  rewrite Dade_Ind_chi // -{j1}Dj1 cfker_Morph // subsetI sHUM /=.
  rewrite -sub_quotient_pre // -(Dade_Ind_chi cycDDb).
  rewrite sub_cfker_Ind_irr ?quotientS ?quotient_norms ?gFnorm // subGcfker.
  rewrite -irr_eq1 -(Dade_chi0 cycDDb) (inj_eq irr_inj).
  by rewrite (inj_eq (Dade_irr_inj cycDDb)).
have [sH0HU sH0M] := (subset_trans sH0H sHHU, subset_trans sH0H (gFsub _ _)).
have sz_mu: size mu_ = p.-1.
  by rewrite -count_filter nb_redM ?(setIidPl sH0H) // /normal sH0M.
have s_muC_mu: {subset filter redM (S_ H0C) <= mu_}.
  move=> phi; rewrite /= !mem_filter => /andP[->]; apply: seqIndS.
  by rewrite setSD // Iirr_kerS ?joing_subl.
have UmuC: uniq (filter redM (S_ H0C)) by rewrite filter_uniq ?seqInd_uniq.
have [|Dmu _] := leq_size_perm UmuC s_muC_mu; last first.
  by split=> // phi; rewrite -Dmu mem_filter => /andP[].
have [nsH0C_M _ _] := nsH0xx_M.
have sHOC_HU: H0C \subset HU by rewrite join_subG sH0HU subIset ?sUHU.
rewrite sz_mu -count_filter nb_redM //.
rewrite /= norm_joinEr /=; last by rewrite astabQ setICA subsetIl.
by rewrite -group_modl //= setIC setIA tiHU setI1g mulg1.
Qed.

(* This is Peterfalvi (9.8). *)
Lemma typeP_nonGalois_characters (not_Galois : ~~ typeP_Galois) :
    let a := #|U : 'C_U(sval (typeP_Galois_Pn not_Galois) | 'Q)| in
  [/\ (*a*) {in X_ H0, forall s, a %| 'chi_s 1%g}%C,
      (*b*) size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j},
      (*c*) exists t, isIndHC 'chi_t
    & (*d*) let irr_qa := [pred zeta in irr M | zeta 1%g == (q * a)%:R] in
            let lb_n := (p.-1 * #|U|)%N in let lb_d := (a ^ 2 * #|U'|)%N in
            (lb_d %| lb_n /\ lb_n %/ lb_d <= count irr_qa (S_ H0U'))%N].
Proof.
case: (typeP_Galois_Pn _) => H1 [oH1 nH1U nH1Uq defHbar aP].
rewrite [sval _]/= => a; case: aP; rewrite -/a => a_gt1 a_dv_p1 cycUb1 isoUb.
set part_a := ({in _, _}); set part_b := _ /\ _.
set part_c := exists t, _; set part_d := let irr_qa := _ in _.
pose HCbar := (HC / H0)%G; set W1bar := (W1 / H0)%g in defHbar.
have [_ [_ _ nUW1 _] _ _ _] := MtypeP.
have [_ /mulG_sub[sHUM sW1M] _ tiHUW1] := sdprodP defM.
have [nsHHU _ /mulG_sub[sHHU sUHU] nHU tiHU] := sdprod_context defHU.
have{sHUM} [nH0H nH0HU] := (normal_norm nsH0H, subset_trans sHUM nH0M).
have nH0C : C \subset 'N(H0) by rewrite subIset ?(subset_trans sUHU).
have nsH0HC: H0 <| HC.
  by rewrite /normal (subset_trans sH0H) ?joing_subl // join_subG nH0H.
have defHCbar: Hbar \x (C / H0)%g = HCbar.
  rewrite /= quotientY //.
  rewrite quotientIG /= ?quotient_astabQ ?astabQ ?sub_cosetpre //.
  by rewrite dprodEY ?subsetIr //= setIA -quotientGI // tiHU quotient1 setI1g.
have defHb1 := defHbar; rewrite (big_setD1 1%g) ?group1 ?conjsg1 //= in defHb1.
have [[_ H1c _ defH1c] _ _ _] := dprodP defHb1; rewrite defH1c in defHb1.
have [nsH1H _] := dprod_normal2 defHb1; have [sH1H _] := andP nsH1H.
have Part_a: part_a.
  move=> s; rewrite !inE => /andP[kers'H kersH0].
  have NsH: 'Res[H] 'chi_s \is a character := cfRes_char _ (irr_char s).
  have /neq0_has_constt[t sHt]: 'Res[H] 'chi_s != 0.
    by rewrite cfRes_eq0 ?irr_char ?irr_neq0.
  have{kers'H} t_neq0: t != 0.
    by apply: contraNneq kers'H => t0; rewrite constt0_Res_cfker -?t0.
    have{kersH0} kertH0: H0 \subset cfker 'chi_t.
    apply: subset_trans (cfker_constt NsH sHt).
    apply/subsetP=> x H0x; rewrite cfkerEchar // inE cfRes1 //.
    by rewrite cfResE ?(subsetP sH0H) //= cfker1 // (subsetP kersH0).
  set T := 'I_HU['chi_t]; have sHT: H \subset T by rewrite sub_inertia.
  have sTHU: T \subset HU by rewrite inertia_sub.
  suffices{s sHt NsH} a_dv_iTHU: a %| #|HU : T|.
    rewrite -(inertia_Ind_invE nsHHU sHt) cfInd1 //.
    by rewrite dvdC_mulr ?dvdC_nat // Cint_Cnat ?Cnat_irr1.
  pose theta := ('chi_t / H0)%CF.
  have nHW1: W1 \subset 'N(H) by rewrite (subset_trans sW1M) ?gFnorm.
  have nHbarW1 := quotient_norms H0 nHW1.
  have [w W1w nt_th_w]: exists2 w, w \in (W1 / H0)%g & 'Res[H1 :^ w] theta != 1.
    apply/exists_inP; rewrite -negb_forall_in.
    apply: contra t_neq0 => /forall_inP=> tH1w1; apply/eqP/irr_inj.
    rewrite irr0 -(cfMod_cfun1 _ H0) -(quo_IirrK nsH0H kertH0) mod_IirrE //.
    congr (_ %% H0)%CF; apply/eqP; rewrite irr_eq1 -subGcfker.
    rewrite -{1}(bigdprodEY defHbar) gen_subG /= cfkerEirr quo_IirrE //=.
    apply/bigcupsP=> w W1w; apply/subsetP=> x H1w_x; rewrite inE.
    have sH1wH: H1 :^ w \subset Hbar.
      by rewrite sub_conjg (normP _) // groupV (subsetP nHbarW1).
    rewrite -(cfResE _ _ H1w_x) // cfker1 ?cfResE // (eqP (tH1w1 _ W1w)).
    by rewrite cfker_cfun1.
  have sH1wH: H1 :^ w \subset Hbar.
    by rewrite sub_conjg (normP _) // groupV (subsetP nHbarW1).
  set th_w := 'Res _ in nt_th_w.
  have abHbar := abelem_abelian abelHbar.
  have lin_th_w: th_w \is a linear_char.
    by rewrite cfRes_lin_char // /theta -quo_IirrE //; apply/char_abelianP.
  have{nt_th_w} th_w_ff: cfaithful th_w.
    rewrite cfaithfulE -(setIidPr (cfker_sub _)) prime_TIg ?cardJg ?oH1 //.
    apply: contra nt_th_w; have /irrP[i ->] := lin_char_irr lin_th_w.
    by rewrite irr_eq1 subGcfker.
  have{th_w th_w_ff lin_th_w} theta_inj: {in H1 :^ w &, injective theta}.
    move=> z1 z2 Hz1 Hz2 eq_th_z12.
    by apply: (fful_lin_char_inj lin_th_w); rewrite ?cfResE.
  have defT: H ><| (U :&: T) = T.
    by rewrite (sdprod_modl defHU) // (setIidPr sTHU).
  rewrite -divgS // -(sdprod_card defHU) -(sdprod_card defT) divnMl // divgI.
  rewrite -indexgI; have ->: a = #|U : 'C_U(H1 :^ w | 'Q)|.
    have [w1 nH0w1 W1w1 ->] := morphimP W1w; rewrite astabQ centJ morphpreJ //.
    by rewrite -astabQ indexgI -(normsP nUW1 _ W1w1) indexJg -indexgI.
  apply/indexgS/subsetP=> x /= /setIP[Ux /setId2P[_ _ /eqP tx_t]].
  rewrite astabQ 2!inE Ux (subsetP nH0HU) ?(subsetP sUHU) //= inE.
  apply/centP=> z H1z; have H1xz: (z ^ inMb x)%g \in H1 :^ w.
    rewrite memJ_norm // normJ mem_conjg (subsetP nH1U) // -mem_conjg.
    by rewrite (normsP (quotient_norms H0 nUW1)) ?mem_quotient.
  apply/esym/commgP/conjg_fixP/theta_inj; rewrite ?cfResE {H1xz}//.
  have{z H1z} /morphimP[z nH0z Hz ->]: z \in Hbar := subsetP sH1wH z H1z.
  have nH0x : x \in 'N(H0) by rewrite (subsetP nH0HU) ?(subsetP sUHU).
  rewrite -morphJ ?cfQuoE ?memJ_norm ?(subsetP nHU) //.
  by rewrite -{1}tx_t cfConjgEnorm ?(subsetP nHU).
pose H1toH i := cfDprodl defHb1 'chi_i.
pose theta (f : {ffun _}) :=
  cfDprodl defHCbar (\prod_(w in W1bar) (H1toH (f w) ^ w)%CF).
have nHW1: W1 \subset 'N(H) := subset_trans sW1M (gFnorm _ _).
have nHbW1: W1bar \subset 'N(Hbar) by rewrite quotient_norms.
have abH1: abelian H1 by rewrite cyclic_abelian ?prime_cyclic ?oH1.
have linH1 i: 'chi[H1]_i \is a linear_char by apply/char_abelianP.
have Dtheta f: {in W1bar & H1, forall w xb, theta f (xb ^ w) = 'chi_(f w) xb}.
  move=> w xb W1w H1xb; have nHw := subsetP nHbW1 _ W1w.
  have Hxbw: xb ^ w \in Hbar by rewrite memJ_norm ?(subsetP sH1H).
  rewrite /= -[xb ^ w]mulg1 cfDprodEl ?prod_cfunE // (bigD1 w) ?cfConjgEnorm //.
  rewrite /= -{1}[xb]mulg1 cfDprodEl // big1 ?mulr1 // => v /andP[W1v w'v].
  rewrite cfConjgE ?(subsetP nHbW1) // -conjgM.
  rewrite -[xb ^ _] mul1g cfDprodEl ?lin_char1 //.
  rewrite -(bigdprodEY defH1c) mem_gen //.
  apply/bigcupP; exists (w * v^-1)%g; last exact/mem_imset.
  by rewrite !inE -eq_mulgV1 eq_sym w'v !in_group.
have lin_theta f: theta f \is a linear_char.
  rewrite cfDprodl_lin_char ?rpred_prod // => w _.
  by rewrite cfConjg_lin_char ?cfDprodl_lin_char.
pose dom_theta := pffun_on (0 : Iirr H1) W1bar (predC1 0).
have inj_theta: {in dom_theta &, injective theta}.
  move=> f1 f2 /pffun_onP[/supportP W1f1 _] /pffun_onP[/supportP W1f2 _] eq_f12.
  apply/ffunP=> w.
  have [W1w | W1'w] := boolP (w \in W1bar); last by rewrite W1f1 ?W1f2.
  by apply/irr_inj/cfun_inP=> x H1x; rewrite -!Dtheta ?eq_f12.
have nsHC_HU: HC <| HU.
  have [_ nsHC_M _] := nsH0xx_M; rewrite (normalS _ _ nsHC_M) ?gFsub //.
  by rewrite join_subG sHHU subIset ?sUHU.
have def_Itheta f (T := 'I_HU[theta f %% H0]%CF): f \in dom_theta -> T = HC.
  case/pffun_onP=> _ nz_fW1; have [sHC_HU _] := andP nsHC_HU.
  apply/eqP; rewrite eqEsubset sub_inertia //.
  rewrite -[T](setIidPr (inertia_sub _ _)) -{1}defHU sdprodE //.
  rewrite -group_modl ?(subset_trans _ (sub_inertia _ _)) ?joing_subl //=.
  rewrite -[in rhs in _ \subset rhs]genM_join sub_gen ?mulgS //.
  apply/subsetP=> y /setIP[Uy Ty]; rewrite inE Uy /=.
  have /setId2P[_ nHCy _] := Ty.
  have nH0y: y \in 'N(H0) := subsetP (subset_trans sUHU nH0HU) y Uy.
  rewrite astabQ inE nH0y inE /= -sub_cent1 -(bigdprodEY defHbar) gen_subG.
  apply/bigcupsP=> w W1w; apply/subsetP=> _ /imsetP[x H1x ->].
  apply/cent1P/commgP/conjg_fixP; rewrite -conjgM conjgCV conjgM.
  have inj_fw: {in H1 &, injective 'chi_(f w)}.
    apply: fful_lin_char_inj => //.
    rewrite cfaithfulE -(setIidPr (cfker_sub _)) prime_TIg ?cardJg ?oH1 //.
    by rewrite subGcfker [~~ _]nz_fW1 ?image_f.
  set xy := (x ^ _)%g; have H1xy: xy \in H1.
    rewrite memJ_norm // (subsetP nH1U) ?memJ_norm ?mem_quotient //.
    by rewrite groupV (subsetP _ _ W1w) // quotient_norms.
  congr (_ ^ w)%g; apply: inj_fw; rewrite -?Dtheta // -conjgM -conjgCV conjgM.
  have /morphimP[x0 nH0x0 Hx0 ->]: x ^ w \in Hbar.
    by rewrite memJ_norm ?(subsetP sH1H) ?(subsetP nHbW1).
  rewrite -morphJ // -[theta f](cfModK nsH0HC).
  have HCx0: x0 \in HC by rewrite mem_gen // inE Hx0.
  by rewrite !cfQuoE ?cfker_Mod ?memJ_norm ?(inertia_valJ _ Ty).
have irr_theta f: f \in dom_theta -> 'Ind[HU] (theta f %% H0)%CF \in irr HU.
  move/def_Itheta=> defIthf.
  have /irrP[s Ds]: theta f \in irr (HC / H0)%g by exact: lin_char_irr.
  by rewrite Ds -mod_IirrE // inertia_Ind_irr ?mod_IirrE // -{s}Ds defIthf.
(*pose Xtheta := irr_Iirr (fun f => 'Ind[HU] (theta f %% H0)%CF) @: dom_theta.*)
have theta_kerC f: (C / H0)%g \subset cfker (theta f).
  rewrite cfkerEchar ?lin_charW //; apply/subsetP=> y Cy.
  rewrite inE (subsetP (quotientS H0 (joing_subr _ _))) //=.
  rewrite -[y]mul1g cfDprodEl ?lin_char1 ?rpred_prod // => w _.
  by rewrite cfConjg_lin_char ?cfDprodl_lin_char.  
pose thJ (f : {ffun _}) y w :=
  [ffun w1 => conjg_Iirr (f (w1 * (inMb w)^-1) : Iirr H1)
                         (inMb y ^ (inMb w * w1^-1))]%g.
have dom_thJ: {in dom_theta & W1, forall f w y, thJ f y w \in dom_theta}.
  move=> f w /pffun_onP[/supportP W1f nz_f] W1w y.
  apply/pffun_onP; split=> [|_ /imageP[w1 W1w1 ->]].
    apply/supportP=> w1 W1'w1; rewrite ffunE W1f ?conjg_Iirr0 ?groupMr //.
    by rewrite groupV mem_quotient.
  rewrite ffunE inE /= -irr_eq1 conjg_IirrE.
  rewrite (can2_eq (cfConjgK _) (cfConjgKV _)) cfConjg_cfun1 irr_eq1.
  by apply/nz_f/image_f; rewrite groupMr ?groupV ?mem_quotient.  
have def_thJ f y w : y \in HU -> w \in W1 ->
 (theta (thJ f y w) %% H0 = (theta f %% H0) ^ (y * w))%CF.
- move=> HUy W1w; set f1 := thJ f y w.
  have [nsH0C_M /normal_norm nHC_M _] := nsH0xx_M.
  have [My Mw] := (subsetP (gFsub _ _) y HUy, subsetP sW1M w W1w).
  have Myw: (y * w)%g \in M by exact: groupM.
  have [nHCyw nH0yw] := (subsetP nHC_M _ Myw, subsetP nH0M _ Myw).
  apply/cfun_inP=> x HCx.
  rewrite cfConjgE // !(cfModE _ nsH0HC) ?memJ_norm ?groupV //.
  rewrite morphJ ?groupV ?morphV // ?(subsetP (normal_norm nsH0HC)) //=.
  have{x HCx}/(mem_dprod defHCbar)[x [x2 [Hx Cx2 -> _]]] := mem_quotient H0 HCx.
  have nCbarM: (M / H0)%g \subset 'N(C / H0).
    by rewrite -(quotientYidl nH0C) quotient_norms ?normal_norm.
  rewrite conjMg 2?cfkerMr ?(subsetP (theta_kerC _)) ?memJ_norm //; last first.
    by rewrite groupV (subsetP nCbarM) ?mem_quotient.
  have nHCbM := quotient_norms H0 nHC_M.
  have nHCb_yw := subsetP nHCbM _ (mem_quotient H0 Myw); rewrite -cfConjgE //.
  have lin_fyf1: (theta f ^ inMb (y * w)%g)%CF / theta f1 \is a linear_char.
    by rewrite rpred_div ?cfConjg_lin_char.
  suffices: x \in cfker ((theta f ^ inMb (y * w)%g)%CF / theta f1)%R.
    rewrite -{2}[(_ ^ _)%CF](divrK (lin_char_unitr (lin_theta f1))) cfunE.
    by move/cfker1->; rewrite lin_char1 ?mul1r.
  apply: subsetP x Hx; rewrite /= -(bigdprodEY defHbar) gen_subG /=.
  apply/bigcupsP=> w1 W1w1; rewrite cfkerEchar ?lin_charW //.
  apply/subsetP=> _ /imsetP[x H1x ->]; rewrite inE lin_char1 //.
  rewrite memJ_norm ?(subsetP nHCbM) ?(subsetP _ w1 W1w1) ?quotientS //.
  rewrite (subsetP _ _ H1x) ?(subset_trans sH1H) ?quotientS ?joing_subl //=.
  rewrite invr_lin_char // !cfunE cfConjgE //= morphM ?(subsetP nH0M) //=.
  rewrite -conjgM invMg mulgA conjgCV conjgM invMg invgK conjVg.
  have nH1yw: inMb y ^ (inMb w * w1^-1) \in 'N(H1).
    have /subsetP-> //: (HU / H0)%g \subset 'N(H1).
      by rewrite -defHU sdprodE // quotientMl // mulG_subG normal_norm.
    rewrite memJ_norm ?mem_quotient // (subsetP (quotient_norm _ _)) //.
    rewrite groupM ?groupV ?mem_quotient ?(subsetP (gFnorm _ _)) //.
    by rewrite (subsetP _ _ W1w1) ?quotientS // (subset_trans sW1M) ?gFnorm.
  rewrite !Dtheta ?memJ_norm ?groupV // ?in_group ?mem_quotient //.
  rewrite ffunE conjg_IirrE cfConjgE // -normCK.
  by rewrite normC_lin_char ?expr1n ?memJ_norm ?groupV.
pose Xtheta :=  (fun f => cfIirr ('Ind[HU] (theta f %% H0)%CF)) @: dom_theta.
have oXtheta: (u * #|Xtheta| = p.-1 ^ q)%N.
  transitivity #|dom_theta|; last first.
    rewrite card_pffun_on cardC1 card_Iirr_abelian // oH1.
    rewrite -(card_isog (quotient_isog _ _)) ?oW1 ?(subset_trans sW1M) //.
    by apply/trivgP; rewrite -tiHUW1 setSI ?(subset_trans sH0H).
  symmetry; rewrite mulnC -sum_nat_const -sum1_card.
  rewrite (partition_big (fun f => cfIirr ('Ind[HU] (theta f %% H0)%CF))
                         (mem Xtheta)) /=; last first.
    by move=> f Dth_f; apply/imsetP; exists f.
  apply: eq_bigr => i /imsetP[f Dth_f Di].
  have /irrP[s Ds]: theta f \in irr (HC / H0)%g by exact: lin_char_irr.
  transitivity (size ((theta f %% H0) ^: HU)%CF); last first.
    rewrite Ds -mod_IirrE // cfclass_size // mod_IirrE // -Ds def_Itheta //.
    rewrite -divgS ?normal_sub //= norm_joinEr 1?subIset ?nHU //=.
    rewrite TI_cardMg 1?setIA ?tiHU ?setI1g //= -(sdprod_card defHU) divnMl //.
    by rewrite divg_normal // (normalS _ _ nsCUW1) ?subsetIl ?joing_subl.
  have th' xi: {f1 | f1 \in dom_theta &
                xi \in (theta f %% H0) ^: HU -> theta f1 %% H0 = xi}%CF.
  - case: cfclassP => [/sig2_eqW[y HUy ->] | _]; last by exists f.
    exists (thJ f y 1%g) => [|_]; first exact: dom_thJ.
    by rewrite def_thJ ?mulg1.
  rewrite -(size_map (fun xi => s2val (th' xi))) sum1_card cardE /=.
  apply: perm_eq_size; apply: uniq_perm_eq => [||f1]; first exact: enum_uniq.
    rewrite map_inj_in_uniq ?cfclass_uniq //.
    apply: can_in_inj (fun f => theta f %% H0)%CF _ => xi.
    exact: (s2valP' (th' xi)).
  have /irrP[s1 Ds1]: theta f1 \in irr (HC / H0)%g by exact: lin_char_irr.
  rewrite mem_enum; apply/andP/mapP=> [[Dth_f1] | [xi fHUxi]].
    rewrite -(inj_eq irr_inj) Di !cfIirrE ?irr_theta  // {1}Ds Ds1.
    rewrite -!mod_IirrE // => /eqP/cfclass_Ind_irrP/=/(_ nsHC_HU).
    rewrite !mod_IirrE // -Ds -Ds1 => fHUf1; exists (theta f1 %% H0)%CF => //.
    case: (th' _) => f2 /= Dth_f2 /(_ fHUf1).
    by move/(can_inj (cfModK nsH0HC))/inj_theta->.
  case: (th' _) => /= f2 Dth_f1 Dxi Df2; rewrite -Df2 in Dth_f1.
  split; rewrite // -(inj_eq irr_inj) Di !cfIirrE ?irr_theta //.
  rewrite Ds Ds1 -!mod_IirrE //; apply/eqP/cfclass_Ind_irrP=> //.
  by rewrite !mod_IirrE // -Ds -Ds1 Df2 Dxi. 
have sXthXH0C: Xtheta \subset X_ H0C.
  apply/subsetP=> i; rewrite inE => /imsetP[f Dth_f Di].
  have /irrP[s Ds]: theta f \in irr (HC / H0)%g by exact: lin_char_irr.
  rewrite !inE Di cfIirrE ?irr_theta // Ds -mod_IirrE //.
  rewrite !sub_cfker_Ind_irr ?(normal_sub nsHC_HU) //; first 1 last.
  - have [/andP[_ nH0C_M] _ _] := nsH0xx_M; apply: subset_trans nH0C_M.
    exact: gFsub.
  - exact: normal_norm nsHHU.
  rewrite join_subG /= {1 3}cfkerEirr mod_IirrE // cfker_Mod //= -Ds.
  rewrite cfMod1 // {1}lin_char1 //; have /pffun_onP[_ nz_f] := Dth_f.
  rewrite (contra _ (nz_f _ (image_f f (group1 _)))) => [ | fH1].
    apply/subsetP=> x Cx; rewrite inE cfModE ?(subsetP (joing_subr _ _)) //.
    by rewrite (cfker1 (subsetP (theta_kerC _) _ _)) ?mem_quotient.
  rewrite -irr_eq1; apply/eqP/cfun_inP=> x H1x.
  rewrite cfun1E H1x -Dtheta ?group1 // conjg1.
  have{x H1x} /morphimP[x nH0x Hx ->] := subsetP sH1H x H1x.
  rewrite -cfModE ?(subsetP (joing_subl _ _)) //.
  by have:= subsetP fH1 x Hx; rewrite inE => /eqP.
pose mu_f (i : Iirr H1) := [ffun w => if w \in W1bar then i else 0].
have Dmu_f (i : Iirr H1): i != 0 -> mu_f i \in dom_theta.
  move=> nz_i; apply/pffun_onP; split=> [|_ /imageP[w W1w ->]].
    by apply/supportP=> w W1'w; rewrite ffunE (negPf W1'w).
  by rewrite ffunE W1w.
pose mk_mu i := 'Ind[HU] (theta (mu_f i) %% H0)%CF.
have sW1_Ithmu i: W1 \subset 'I_M[theta (mu_f i) %% H0]%CF.
  apply/subsetP=> w W1w; have Mw := subsetP sW1M w W1w.
  have nHCw: w \in 'N(HC) by have [_ /normal_norm/subsetP->] := nsH0xx_M.
  rewrite inE Mw nHCw /=; apply/eqP/cfun_inP=> x HCx.
  rewrite -[w]mul1g -def_thJ //; congr ((theta _ %% H0)%CF x).
  apply/ffunP=> w1; apply: irr_inj; rewrite ffunE morph1 conj1g !ffunE.
  by rewrite conjg_IirrE cfConjg1 groupMr // groupV mem_quotient.
have inj_th_mu: {in predC1 0 &, injective ((@cfIirr _ _) \o mk_mu)}.
  move=> i1 i2 nz_i1 nz_i2 /eqP; rewrite -(inj_eq irr_inj).
  rewrite !cfIirrE ?irr_theta ?Dmu_f //.
  have /lin_char_irr/irrP[s1 Ds1]:= cfMod_lin_char (lin_theta (mu_f i1)).
  have /lin_char_irr/irrP[s2 Ds2]:= cfMod_lin_char (lin_theta (mu_f i2)).
  rewrite /mk_mu Ds1 Ds2 => /eqP/cfclass_Ind_irrP/=/(_ nsHC_HU).
  rewrite -{s1}Ds1 -{s2}Ds2.
  case/cfclassP=> _ /(mem_sdprod defHU)[x [y [Hx Uy -> _]]].
  rewrite (cfConjgM _ nsHC_HU) ?(subsetP sHHU x) ?(subsetP sUHU) //.
  have{x Hx} /setId2P[_ _ /eqP->]: x \in 'I_HU[theta (mu_f i2) %% H0]%CF.
    by rewrite def_Itheta ?Dmu_f // mem_gen ?inE ?Hx.
  move=> Dth1.
  suffices /setId2P[_ _ /eqP]: y \in 'I_HU[theta (mu_f i2) %% H0]%CF.
    rewrite -Dth1 => /(can_inj (cfModK nsH0HC))/inj_theta.
    rewrite !Dmu_f // => /(_ isT isT)/ffunP/(_ 1%g).
    by rewrite !ffunE group1 => ->.
  rewrite def_Itheta ?Dmu_f //= mem_gen // inE orbC.
  have nCy: y \in 'N(C).
    by rewrite (subsetP (normal_norm nsCUW1)) ?mem_gen ?inE ?Uy.
  have [_ _ /trivgPn[_ /morphimP[w nH0w W1w ->] ntw] _ _] :=
    Frobenius_context frobUW1c.
  rewrite coset_idr //; apply/set1P; rewrite -set1gE; apply: wlog_neg => nty.
  rewrite -((Frobenius_reg_ker frobUW1c) (coset C w)); last first.
    by rewrite !inE mem_quotient ?ntw.
  rewrite inE mem_quotient //= -/C; apply/cent1P/commgP.
  rewrite -morphR //= coset_id //.
  suffices: [~ y, w] \in U :&: HC.
    rewrite /= norm_joinEr 1?subIset ?nHU // -group_modr ?subsetIl //=.
    by rewrite setIC tiHU mul1g.
  have Uyw: [~ y, w] \in U; last rewrite inE Uyw.
    by rewrite {1}commgEl groupMl ?groupV // memJ_norm ?(subsetP nUW1) // Uy.
  rewrite -(def_Itheta _ (Dmu_f _ nz_i1)) inE /= andbA -in_setI.
  rewrite (setIidPl (normal_norm nsHC_HU)).
  rewrite (subsetP sUHU) //= Dth1 -(cfConjgM _ nsHC_HU) ?(subsetP sUHU) //.
  have [_ nsHC_M _] := nsH0xx_M.
  have My: y \in M := subsetP (der_sub _ _) y (subsetP sUHU y Uy).
  rewrite mulKVg (cfConjgM _ nsHC_M) ?in_group // ?(subsetP sW1M w) //.
  have /setId2P[_ _ /eqP->] := subsetP (sW1_Ithmu i2) _ (groupVr W1w).
  rewrite (cfConjgM _ nsHC_M) ?(subsetP sW1M w) // -Dth1.
  by have /setId2P[_ _ /eqP->] := subsetP (sW1_Ithmu i1) w W1w.
pose Xmu := (fun f => (cfIirr (mk_mu f))) @: predC1 0.
have def_IXmu: {in Xmu, forall s, 'I_M['chi_s] = M}.
  move=> _ /imsetP[i nz_i ->]; apply/eqP; rewrite eqEsubset.
  rewrite {1}['I_M[_]%CF]setIdE subsetIl /=.
  rewrite -{1}defM sdprodE ?(subset_trans sW1M) ?gFnorm // mulG_subG.
  rewrite (cfIirrPE (fun j nz_j => irr_theta _ (Dmu_f j nz_j))) //.
  rewrite sub_inertia ?gFsub //; apply/subsetP=> w W1w.
  have /setId2P[Mw _ def_mui_w] := subsetP (sW1_Ithmu i) w W1w.
  rewrite inE Mw (subsetP (gFnorm _ _)) //=; apply/eqP/cfun_inP=> x HUx.
  rewrite cfConjgE ?(subsetP (der_norm _ _)) // !cfIndE ?normal_sub //=.
  congr (_ * _); rewrite (reindex_inj (conjg_inj w^-1%g)) /=.
  apply: eq_big => y; rewrite memJ_norm ?groupV ?(subsetP (der_norm 1 M)) //.
  move=> HUy; rewrite -conjJg -cfConjgE ?(eqP def_mui_w) //.
  by have [_ /normal_norm/subsetP-> //] := nsH0xx_M.
pose Smu := [seq 'Ind[M] 'chi_s | s in Xmu].
have sSmu_mu: {subset Smu <= mu_}.
  move=> _ /imageP[s Xmu_s ->]; rewrite mem_filter /=.
  rewrite irrEchar induced_prod_index ?gFnormal // def_IXmu //.
  rewrite -(sdprod_index defM) (eqC_nat _ 1) gtn_eqF ?prime_gt1 // andbF.
  rewrite mem_seqInd ?gFnormal /normal ?(subset_trans sH0H) ?gFsub //=.
  suffices /(subsetP sXthXH0C): s \in Xtheta.
    by apply: subsetP; rewrite setSD // Iirr_kerS ?joing_subl.
  have /imsetP[i nz_i ->] := Xmu_s.
  by apply/imsetP; exists (mu_f i) => //; apply: Dmu_f.
have ResIndXmu: {in Xmu, forall s, 'Res ('Ind[M] 'chi_s) = q%:R *: 'chi_s}.
  move=> s Xmu_s; rewrite /= induced_sum_rcosets ?gFnormal // def_IXmu //.
  rewrite -(sdprod_index defM) (big_rem 'chi_s) ?cfclass_refl //= -/q.
  rewrite [rem _ _]size0nil ?big_nil ?addr0 // size_rem ?cfclass_refl //.
  by rewrite cfclass_size def_IXmu ?indexgg.
have uSmu: uniq Smu.
  rewrite map_inj_in_uniq ?enum_uniq // => s1 s2; rewrite !mem_enum => Xs1 Xs2.
  move/(congr1 'Res[HU]); rewrite !ResIndXmu //.
  by move/(can_inj (scalerK (neq0CG W1)))/irr_inj.
have sz_Smu: size Smu = p.-1.
  by rewrite size_map -cardE card_in_imset // cardC1 card_Iirr_abelian ?oH1.
have [sz_mu s_mu_H0C] := nb_redM_H0.
have Dmu: Smu =i mu_.
  by have [|//] := leq_size_perm uSmu sSmu_mu; rewrite sz_mu sz_Smu.
have Du: u = #|HU : HC|.
  rewrite -divgS ?normal_sub //= norm_joinEr 1?subIset ?nHU //=.
  rewrite TI_cardMg 1?setIA ?tiHU ?setI1g //= -(sdprod_card defHU) divnMl //.
  by rewrite divg_normal // (normalS _ _ nsCUW1) ?subsetIl ?joing_subl.
split=> {Part_a part_a}//.
- split=> // phi mu_phi; have S_HOC_phi := s_mu_H0C _ mu_phi.
  move: mu_phi; rewrite -Dmu => /imageP[_ /imsetP[i nz_i ->] Dphi].
  rewrite (cfIirrPE (fun j nz_j => irr_theta _ (Dmu_f j nz_j))) // in Dphi.
  split=> //; rewrite Dphi ?cfInd1 ?cfIndInd ?gFsub ?normal_sub //.
    rewrite -(sdprod_index defM) -/q -Du mulrA -natrM.
    by rewrite lin_char1 1?cfMod_lin_char ?mulr1.
  by exists (theta (mu_f i) %% H0)%CF; rewrite 1?cfMod_lin_char.
- have /eqVproper: Xmu \subset Xtheta.
    apply/subsetP=> _ /imsetP[i nz_i ->]; apply/imsetP.
    by exists (mu_f i); rewrite ?Dmu_f.
  case=> [defXmu | /andP[_ /subsetPn[s theta_s Xmu'_s]]]; last first.
    have [f Dth_f Ds] := imsetP theta_s.
    have /irrP[t Dt]: 'Ind 'chi_s \in irr M.
      apply: contraR Xmu'_s => red_Ind_s.
      have: 'Ind 'chi_s \in mu_.
        rewrite mem_filter /= red_Ind_s mem_seqInd ?gFnormal //; last first.
          by rewrite /normal (subset_trans sH0H) ?gFsub.
        apply: subsetP theta_s; rewrite (subset_trans  sXthXH0C) ?setSD //.
        by rewrite Iirr_kerS ?joing_subl.
      rewrite -Dmu => /imageP[s1 Xmu_s1] /(congr1 (cfdot ('Ind 'chi_s1)))/eqP.
      rewrite induced_prod_index ?gFnormal // eq_sym -cfdot_Res_l.
      rewrite ResIndXmu // cfdotZl cfdot_irr.
      by case: (s1 =P s) => [<- // | _] /idPn[]; rewrite mulr0 neq0CiG.
    exists t; rewrite -{t}Dt; split.
    + rewrite Ds cfIirrE ?irr_theta //= ?cfInd1 ?gFsub ?normal_sub // -Du.
      rewrite -(sdprod_index defM) -/q mulrA -natrM.
      by rewrite lin_char1 1?cfMod_lin_char ?mulr1.
    + rewrite mem_seqInd ?gFnormal //; last by have [] := nsH0xx_M.
      exact: (subsetP sXthXH0C).
    exists (theta f %% H0)%CF; first by rewrite cfMod_lin_char.
    by rewrite Ds cfIirrE ?irr_theta //= ?cfIndInd ?gFsub ?normal_sub.
  suffices /(congr1 odd): u = (p.-1 ^ q.-1)%N.
    rewrite odd_exp -(subnKC (prime_gt1 pr_q)) /= -subn1 odd_sub ?prime_gt0 //.
    rewrite Du -card_quotient ?normal_norm // -oH1.
    by rewrite (oddSg sH1H) ?quotient_odd ?mFT_odd.
  apply/eqP; rewrite -(@eqn_pmul2r p.-1); last first.
    by rewrite -(subnKC (prime_gt1 p_pr)).
  rewrite -expnSr prednK ?prime_gt0 // -oXtheta -defXmu.
  by rewrite card_in_imset // cardC1 card_Iirr_abelian ?oH1.
clear Xmu def_IXmu Smu sSmu_mu ResIndXmu uSmu sz_Smu sz_mu s_mu_H0C Dmu.
clear thJ dom_thJ def_thJ oXtheta sXthXH0C mu_f Dmu_f mk_mu sW1_Ithmu inj_th_mu.
clear theta Dtheta lin_theta inj_theta def_Itheta irr_theta Xtheta theta_kerC.
clear dom_theta part_b part_c => irr_qa lb_n lb_d {part_d}.
have sU'CH1: U' \subset 'C_U(H1 | 'Q).
  apply: der1_min; last exact: cyclic_abelian.
  rewrite normsI ?normG //= astabQ (subset_trans _ (morphpre_norm _ _)) //.
  by rewrite -sub_quotient_pre ?(subset_trans sUHU) // norms_cent.
have sCH1_U: 'C_U(H1 | 'Q) \subset U by apply: subsetIl.
have dvd_lb: lb_d %| lb_n.
  rewrite -[lb_d]mulnA dvdn_mul // -(Lagrange sCH1_U).
  by rewrite mulnC dvdn_pmul2r ?cardSg ?indexg_gt0.
split; rewrite ?leq_divLR // /lb_n -(Lagrange sCH1_U) -/a -(Lagrange sU'CH1).
rewrite mulnCA -mulnA mulnC !mulnA !leq_pmul2r ?cardG_gt0 ?indexg_gt0 // mulnC.
pose HCH1 := (H <*> 'C_U(H1 | 'Q)); pose HU' := (H <*> U').
have nsHU'HCH1: HU' <| HCH1.
  rewrite /HU' /HCH1 -!quotientYK ?(subset_trans _ nHU) ?gFsub //=.
  by rewrite cosetpre_normal quotient_normal // (normalS _ _ (der_normal _ _)).
have nsH0M: H0 <| M.
  by rewrite /normal (subset_trans (subset_trans sH0H sHHU)) ?gFsub //.
have [[_ mulHb1 _ tiH1Hc] [_ nsH1cH]] := (dprodP defHb1, dprod_normal2 defHb1).
have nsH0HCH1: H0 <| HCH1.
  rewrite (normalS _ _ nsH0M) ?sub_gen ?subsetU ?sH0H // join_subG.
  by rewrite gFsub subIset ?(subset_trans sUHU) ?gFsub.
have defHCH1b: (HCH1 / H0)%g = Hbar <*> 'C_(U / H0)(H1).
  rewrite quotientY // 1?subIset ?(subset_trans sUHU) //.
  by rewrite astabQ quotientIG ?sub_cosetpre //= cosetpreK.
have nsH1cHCH1: H1c <| HCH1 / H0.
  rewrite defHCH1b /normal join_subG normal_norm //.
  rewrite sub_gen ?subsetU ?(normal_sub nsH1cH) //= subIset //.
  rewrite -(bigdprodEY defH1c) norms_gen ?norms_bigcup //.
  apply/bigcapsP=> w /setD1P[_ W1w]; rewrite normJ.
  by rewrite -(normsP (quotient_norms _ nUW1) w W1w) conjSg.
have defHCH1hat: ((Hbar / H1c) \x ('C_(U / H0)(H1) / H1c) = HCH1 / H0 / H1c)%g.
  rewrite defHCH1b quotientY // ?(normal_norm nsH1cH) //; first 1 last.
    by rewrite (subset_trans _ (normal_norm nsH1cHCH1)) // defHCH1b joing_subr.
  rewrite dprodEY //=.
    by rewrite -mulHb1 quotientMidr quotient_cents ?subsetIr.
  rewrite -quotientGI; last by rewrite /= -mulHb1 mulG_subr.
  by rewrite setIA -quotientGI // tiHU quotient1 setI1g quotient1.
have nsHCH1_HU: HCH1 <| HU.
  rewrite sub_der1_normal //; last first.
    by rewrite -defHU sdprodEY // genS ?setUS ?subsetIl.
  apply: subset_trans (normal_sub nsHU'HCH1).
  rewrite /HU' -quotientYK ?(subset_trans (der_sub 1 U)) //.
  rewrite -sub_quotient_pre ?(subset_trans (der_sub 1 _)) ?gFnorm //.
  rewrite quotient_der ?normal_norm //= -defHU sdprodE // quotientMidl.
  by rewrite quotient_der.
pose lam j := ('chi[HCH1 / HU']_j %% HU')%CF : 'CF(HCH1).
pose theta1 i := (cfDprodl defHCH1hat 'chi_i %% H1c %% H0)%CF : 'CF(HCH1).
have oHhat: #|Hbar / H1c|%g = p.
  by rewrite -divg_normal // -(dprod_card defHb1) oH1 mulnK.
have abHhat: abelian (Hbar / H1c).
  by rewrite cyclic_abelian ?prime_cyclic ?oHhat.
have theta1_lin i: theta1 i \is a linear_char.
  by rewrite !(cfDprodl_lin_char, cfMod_lin_char) //; apply/char_abelianP.
have abCH1lam: abelian (HCH1 / HU').
  rewrite sub_der1_abelian //= -!quotientYK ?(subset_trans _ nHU) ?der_sub //=.
  rewrite -sub_quotient_pre ?(subset_trans (der_sub 1 _)) ?subsetIl //=.
  by rewrite !quotient_der ?subsetIl //= cosetpreK dergS ?quotientS ?subsetIl.
have lam_lin j: lam j \is a linear_char.
  by rewrite cfMod_lin_char //; apply/char_abelianP.
have <-: #|HCH1 / HU'|%g = #|'C_U(H1 | 'Q) : U'|.
  rewrite -divg_normal //= !norm_joinEr ?(subset_trans _ nHU) ?der_sub //=.
  rewrite !TI_cardMg ?divnMl -?divgS //; apply/trivgP; rewrite -tiHU setIS //.
  exact: der_sub.
pose theta i j := cfIirr (theta1 i * lam j).
have theta_lin i j: 'chi_(theta i j) \is a linear_char.
  by rewrite cfIirrE ?lin_char_irr ?rpredM.
have thetaEl i j x: x \in H -> 'chi_(theta i j) x = 'chi_i (coset _ (inMb x)).
  move=> Hx; rewrite cfIirrE; last by rewrite lin_char_irr ?rpredM.
  rewrite cfunE mulrC [_ x]cfker1 ?lin_char1 ?mul1r //; last first.
    by rewrite (subsetP (cfker_Mod _ _)) // mem_gen ?inE ?Hx.
  have HCH1x: x \in HCH1 by rewrite mem_gen ?inE ?Hx.
  rewrite 2?cfModE ?mem_quotient //.
  by rewrite -{1}[coset _ _]mulg1 cfDprodEl ?mem_quotient.
have thetaEr i j x:
  x \in 'C_U(H1 | 'Q) -> 'chi_(theta i j) x = 'chi_j (coset _ x).
- move=> CH1x; rewrite cfIirrE; last by rewrite lin_char_irr ?rpredM.
  have HCH1x: x \in HCH1 by rewrite mem_gen 1?inE ?CH1x ?orbT.
  rewrite cfunE 2?cfModE ?mem_quotient // -{1}[coset _ _]mul1g.
  rewrite [lam j x]cfModE //.
  rewrite cfDprodEl ?lin_char1 ?mul1r // /=; first exact/char_abelianP.
  rewrite -['C(H1)]cosetpreK -quotientIG ?sub_cosetpre //=.
  by rewrite -astabQ !mem_quotient.
pose Ctheta := theta @2:([set~ 0], setT).
have ->: (p.-1 * #|(HCH1 / HU')%g|)%N = #|Ctheta|.
  rewrite [Ctheta]curry_imset2X card_imset ?cardsX => [|[i1 j1] [i2 j2] /=/eqP].
    by rewrite cardsC1 cardsT !card_Iirr_abelian // oHhat.
  rewrite -(inj_eq irr_inj) => /eqP/cfunP eq_th12.
  congr (_, _); apply/irr_inj/cfun_inP.
    move=> _ /morphimP[_ _ /morphimP[x _ Hx ->] ->].
    by rewrite -(thetaEl i1 j1) // eq_th12 thetaEl.
  move=> HU'y; rewrite /= -{1}quotientYidl ?normal_norm //=.
  rewrite joingA -(joingC H) joingA (joing_idl _ U') setUid.
  rewrite quotientYidl ?(subset_trans _ (normal_norm nsHU'HCH1)) ?joing_subr //.
  by case/morphimP=> y _ CH1y ->; rewrite -(thetaEr i1 j1) // eq_th12 thetaEr.
have chi_i_inj i:
  i \in [set~ 0] -> {in Hbar / H1c &, injective 'chi[Hbar / H1c]_i}%g.
- move=> nz_i; apply: fful_lin_char_inj; first exact/char_abelianP.
  rewrite cfaithfulE -(setIidPr (cfker_sub _)) prime_TIg ?oHhat //.
  by apply: contraL nz_i; rewrite subGcfker !inE negbK.
have Itheta r: r \in Ctheta -> 'I_HU['chi_r]%CF = HCH1.
  case/imset2P=> i j nz_i _ Dr; apply/eqP.
  have [sHCH1_HU _] := andP nsHCH1_HU.
  rewrite eqEsubset sub_inertia //= andbT; apply/subsetP=> xy /setId2P[].
  case/(mem_sdprod defHU)=> x [y [Hx Uy -> _]] _ /eqP/cfunP.
  rewrite (cfConjgM _ nsHCH1_HU) ?(subsetP sHHU x) ?(subsetP sUHU) //.
  have /setId2P[_ _ /eqP->] : x \in 'I_HU['chi_r]%CF.
    by rewrite (subsetP (sub_inertia _ _)) // mem_gen 1?inE ?Hx.
  move=> Dry; rewrite -[HCH1]genM_join mem_gen ?mem_mulg {x Hx}//= inE Uy.
  have nH0y: y \in 'N(H0) by rewrite (subsetP nH0HU) ?(subsetP sUHU).
  rewrite astabQ inE nH0y inE; apply/centP=> xb H1xb.
  have /morphimP[x nH0x Hx Dxb] := subsetP sH1H _ H1xb.
  apply/esym/commgP; rewrite -in_set1 -set1gE -tiH1Hc inE /=.
  have H1xy: [~ xb, inMb y] \in H1.
    by rewrite groupMl ?groupV // memJ_norm //= (subsetP nH1U) ?mem_quotient.
  rewrite H1xy coset_idr // ?(subsetP (normal_norm nsH1cH)) ?(subsetP sH1H) //.
  apply: (chi_i_inj i); rewrite ?group1 ?mem_quotient ?(subsetP sH1H) //.
  rewrite lin_char1; last exact/char_abelianP.
  have Hxy: x ^ y \in H by rewrite memJ_norm ?(subsetP nHU).
  rewrite Dxb -morphR // -(thetaEl i j); last by rewrite groupM ?groupV.
  rewrite lin_charM ?(subsetP (joing_subl _ _)) ?groupV // -{2}Dr -Dry.
  rewrite cfConjgEnorm ?(subsetP (normal_norm nsHCH1_HU)) ?(subsetP sUHU) //.
  rewrite Dr -lin_charM ?(subsetP (joing_subl _ _)) ?groupV //.
  by rewrite mulVg lin_char1.
have irr_Xtheta: {in Ctheta, forall r, 'Ind[HU] 'chi_r \in irr HU}.
  by move=> r Cth_r; rewrite /= inertia_Ind_irr ?Itheta.
pose Xtheta := (fun r => cfIirr ('Ind[HU] 'chi_r)) @: Ctheta.
have Da: a = #|HU : HCH1|.
  rewrite /a -!divgS ?subsetIl ?normal_sub //= norm_joinEr 1?subIset ?nHU //=.
  by rewrite -(sdprod_card defHU) TI_cardMg ?divnMl // setIA tiHU setI1g.
have Xtheta_1: {in Xtheta, forall s, 'chi_s 1%g = a%:R}.
  move=> _ /imsetP[r Cth_r ->]; rewrite cfIirrE ?irr_Xtheta //=.
  rewrite cfInd1 ?join_subG ?sHHU 1?subIset ?sUHU //= -Da.
  by have /imset2P[i j _ _ ->] := Cth_r; rewrite lin_char1 ?mulr1.
have nsH0U'M: H0U' <| M.
  rewrite normalY // /normal (subset_trans (subset_trans _ sUHU)) ?der_sub //.
  rewrite -defM sdprodE ?(subset_trans sW1M) ?gFnorm //= mulG_subG andbC.
  rewrite (char_norm_trans (gFchar _ _)) // -defHU sdprodE // mulG_subG gFnorm.
  by rewrite cents_norm // centsC; have [_ [cHU']] := typeP_context MtypeP.
have nsH0U'HU: H0U' <| HU.
  apply: normalS nsH0U'M; rewrite ?der_sub // join_subG (subset_trans sH0H) //.
  by rewrite (subset_trans _ sUHU) ?der_sub.
have sXthetaXH0U': Xtheta \subset X_ H0U'.
  apply/subsetP=> _ /imsetP[r Cth_r ->]; have [i j nz_i _ Dr] := imset2P Cth_r.
  rewrite !inE cfIirrE ?irr_Xtheta //=.
  rewrite !sub_cfker_Ind_irr ?normal_norm ?(normal_sub nsHCH1_HU) //.
  apply/andP; split; last first.
    rewrite join_subG /= cfkerEirr Dr; apply/andP; split.
      apply/subsetP=> x H0x; rewrite inE lin_char1 //.
      rewrite thetaEl ?(subsetP sH0H) // (coset_id H0x) morph1 lin_char1 //.
      exact/char_abelianP.
    apply/subsetP=> y U'y; rewrite inE lin_char1 //.
    rewrite thetaEr ?(subsetP sU'CH1) // coset_id ?mem_gen ?inE ?U'y ?orbT //.
    by rewrite lin_char1 //; exact/char_abelianP.
  apply: contraL nz_i => ker_i_H; rewrite !inE negbK -irr_eq1.
  apply/eqP/cfun_inP=> _ /morphimP[_ _ /morphimP[x _ Hx ->] ->].
  rewrite cfun1E !mem_quotient // -(thetaEl i j) // cfker1 ?lin_char1 //.
  by rewrite -Dr (subsetP ker_i_H).
have nsCH1_U: 'C_U(H1 | 'Q) <| U by rewrite sub_der1_normal.
have nH1cU: (U / H0)%g \subset 'N(H1c).
  rewrite -(bigdprodEY defH1c) norms_gen ?norms_bigcup //.
  apply/bigcapsP=> w /setD1P[_ W1w].
  by rewrite normJ -sub_conjgV (normsP (quotient_norms H0 nUW1)) ?groupV.
have ->: #|Ctheta| = (#|Xtheta| * a)%N.
  rewrite -sum1_card -sum_nat_const.
  rewrite (partition_big_imset (fun r => (cfIirr ('Ind[HU] 'chi_r)))) /=.
  apply: eq_bigr => _ /imsetP[r Cth_r ->].
  transitivity (\sum_(r1 | 'chi_r1 \in ('chi_r ^: HU)%CF) 1)%N; last first.
    rewrite (cfclass_sum _ (fun _ => 1%N)) // (big_nth 0) sum_nat_const_nat.
    by rewrite subn0 muln1 cfclass_size ?Itheta.
  apply: eq_bigl => r1; rewrite -(inj_eq irr_inj).
  have [Cth_r1 | Cth'r1] := boolP (r1 \in Ctheta).
    rewrite !cfIirrE ?irr_Xtheta //.
    by rewrite (sameP (cfclass_Ind_irrP _ _ nsHCH1_HU) eqP).
  apply/esym; apply: contraNF Cth'r1 => /cfclassP[z HUz].
  have{z HUz} /(mem_sdprod defHU)[z0 [z [Hz0 Uz -> _]]] := HUz.
  rewrite (cfConjgM _ nsHCH1_HU) ?(subsetP sHHU z0) ?(subsetP sUHU) //.
  have [sHCH1_HU _] := andP nsHCH1_HU.
  have{z0 Hz0} /setId2P[_ _ /eqP->]: z0 \in 'I_HU['chi_r]%CF.
    by rewrite (subsetP (sub_inertia _ _)) // mem_gen ?inE ?Hz0.
  move=> Dr1; have [i j nz_i _ Dr] := imset2P Cth_r; apply/imset2P.
  exists (conjg_Iirr i (coset _ (inMb z))) (conjg_Iirr j (coset _ z)).
  - rewrite !inE -!irr_eq1 conjg_IirrE in nz_i *.
    by rewrite (can2_eq (cfConjgK _) (cfConjgKV _)) cfConjg_cfun1.
  - by rewrite inE.
  apply/irr_inj/cfun_inP=> xy /=; rewrite {1}norm_joinEr 1?subIset ?nHU //.
  case/mulsgP=> x y Hx CH1y ->{xy}; rewrite Dr1 Dr.
  rewrite cfConjgE ?(subsetP (normal_norm nsHCH1_HU)) ?(subsetP sUHU) //.
  have Hxz: (x ^ z^-1)%g \in H by rewrite memJ_norm ?groupV ?(subsetP nHU).
  have CH1yz: (y ^ z^-1)%g \in 'C_U(H1 | 'Q).
    by rewrite memJ_norm ?groupV ?(subsetP (normal_norm nsCH1_U)).
  rewrite conjMg lin_charM ?(subsetP (joing_subl H _) _ Hxz) //; last first.
    by rewrite (subsetP (joing_subr H _)).
  have [nH0U [Uy _]] := (subset_trans sUHU nH0HU, setIP CH1y).
  have [nH0x nH0z] := (subsetP nH0H x Hx, subsetP nH0U z Uz).
  rewrite thetaEl // thetaEr // morphJ ?groupV ?morphV //=.
  have nH1c_z: inMb z \in 'N(H1c) by rewrite (subsetP nH1cU) ?mem_quotient.
  rewrite morphJ ?morphV ?groupV //; first 1 last.
    by rewrite (subsetP (normal_norm nsH1cH) (inMb x)) ?mem_quotient.
  have nHU'U: U \subset 'N(HU') by rewrite normsY ?gFnorm.
  rewrite morphJ ?morphV ?groupV ?(subsetP nHU'U) //.
  rewrite -!cfConjgE; last first.
  - by rewrite !(subsetP (quotient_norm _ _), mem_quotient) ?(subsetP nHU).
  - rewrite (subsetP (quotient_norm _ _)) ?mem_quotient //.
    by rewrite (subsetP (normal_norm nsHCH1_HU)) ?(subsetP sUHU).
  rewrite lin_charM ?(subsetP (joing_subl _ _) x) //; last first.
    by rewrite (subsetP (joing_subr _ _)) //.
  by rewrite thetaEl // thetaEr // !conjg_IirrE.
rewrite leq_pmul2r ?indexg_gt0 // cardE -(size_map (fun s => 'Ind[M] 'chi_s)).
have kerH1c s: s \in Xtheta -> restrm nH0H inMb @*^-1 H1c \subset cfker 'chi_s.
  case/imsetP=> r Cth_r Ds; have [i j _ _ Dr] := imset2P Cth_r.
  rewrite Ds cfIirrE ?irr_Xtheta //.
  rewrite sub_cfker_Ind_irr; last first; first by rewrite normal_sub.
    rewrite morphpre_restrm normsI ?(subset_trans _ (gFnorm _ _)) ?der_sub //.
    rewrite (subset_trans _ (morphpre_norm _ _)) // -sub_quotient_pre //.
    by rewrite -defHU sdprodE ?quotientMl // mulG_subG normal_norm.
  apply/subsetP=> x /morphpreP[Hx H1c_x]; rewrite Dr cfkerEirr inE.
  by rewrite lin_char1 ?thetaEl // coset_id ?lin_char1 //; apply/char_abelianP.
have injXtheta:
  {in M & Xtheta &, forall w s1 s2, 'chi_s1 = 'chi_s2 ^ w -> w \in HU}%CF.
- move=> _ s1 s2 /(mem_sdprod defM)[y [w [HUy W1w -> _]]] Xth_s1 Xth_s2.
  rewrite (cfConjgM _ (der_normal 1 M)) ?(subsetP sW1M w) //; last first.
    by rewrite (subsetP (der_sub 1 M)).
  have /setId2P[_ _ /eqP-> Ds1]: y \in 'I_M['chi_s2]%CF.
    by rewrite (subsetP (sub_inertia _ _)) ?der_sub.
  suffices{y HUy} ->: w = 1%g by rewrite mulg1.
  have /setDP[_] := subsetP sXthetaXH0U' s1 Xth_s1; apply: contraNeq => ntw.
  rewrite inE; apply/subsetP=> x Hx.
  have /mulsgP[x1b x2b H1x1b H1cx2b Dxb]: inMb x \in (H1 * H1c)%g.
    by rewrite mulHb1 mem_quotient.
  have /morphimP[x1 nH0x1 Hx1 Dx1] := subsetP sH1H _ H1x1b.
  rewrite -[x](mulKVg x1) groupM //; last first.
    rewrite (subsetP (kerH1c _ _)) // !inE groupM ?groupV //.
    by rewrite morphM ?morphV ?groupV //= /restrm -Dx1 Dxb mulKg.
  rewrite /= cfkerEirr inE {1}Ds1.
  rewrite cfConjgE ?(subsetP (der_norm 1 M)) ?(subsetP sW1M) //.
  rewrite cfker1 ?Xtheta_1 // (subsetP (kerH1c _ _)) // !inE.
  rewrite memJ_norm ?groupV ?(subsetP nHW1) // Hx1 /= /restrm.
  have nH0W1 := subset_trans sW1M nH0M.
  rewrite morphJ ?(subsetP nH0H x1) ?(subsetP nH0W1) ?groupV //= -Dx1.
  rewrite -(bigdprodEY defH1c) mem_gen //; apply/bigcupP.
  exists (inMb w^-1)%g; last by rewrite memJ_conjg ?mem_quotient.
  rewrite !inE mem_quotient ?groupV // -[inMb _]/(restrm nH0W1 inMb w^-1%g).
  rewrite andbT morph_injm_eq1 ?eq_invg1 ?groupV //.
  by rewrite ker_restrm ker_coset setIC -tiHUW1 setSI ?(subset_trans sH0H).
rewrite count_filter uniq_leq_size //.
  apply/dinjectiveP=> s1 s2 Xth_s1 Xth_s2.
  case/(cfclass_Ind_irrP _ _ (der_normal 1 M))/cfclassP=> y My Ds2.
  suffices /setId2P[_ _ /eqP]: y \in 'I_M['chi_s2]%CF.
    by rewrite -Ds2 => /irr_inj.
  by rewrite (subsetP (sub_inertia _ _)) ?der_sub ?(injXtheta y s1 s2).
move=> _ /imageP[s Xth_s ->]; rewrite mem_filter /=.
rewrite cfInd1 ?der_sub // -(sdprod_index defM) Xtheta_1 // -natrM eqxx.
rewrite mem_seqInd ?gFnormal // (subsetP sXthetaXH0U') // !andbT.
rewrite inertia_Ind_irr ?gFnormal //.
by apply/subsetP=> y /setId2P[My _ /eqP/esym/injXtheta->].
Qed.

Lemma dvdn_pred_predX n e : n.-1 %| (n ^ e).-1.
Proof. by rewrite binomial.predn_exp dvdn_mulr. Qed.

Import ssrnum Num.Theory.

(* This is Peterfalvi (9.9); we have exported the fact that HU / H0 is a      *)
(* Frobenius group in case (c), as this is directly used in (9.10).           *)
Lemma typeP_Galois_characters (is_Galois : typeP_Galois) :
  [/\ (*a*) {in X_ H0, forall s, u %| 'chi_s 1%g}%C,
            {in X_ H0C', forall s, 'chi_s 1%g = u%:R /\
             (exists2 xi : 'CF(HC), xi \is a linear_char & 'chi_s = 'Ind xi)},
      (*b*) size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j}
    & (*c*) all redM (S_ H0C') ->
            [/\ C = 1%g, u = (p ^ q).-1 %/ p.-1
              & [Frobenius HU / H0 = Hbar ><| (U / H0)]%g]].
Proof.
have [F [phi [psi _ [Kpsi phiJ]]]] := typeP_Galois_P is_Galois.
case=> [oF /isomP[inj_phi im_phi] phiW2] [cycUbar co_u_p1 u_dv_pq1].
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have [nsH0C_M nsHC_M nsH0C'_M] := nsH0xx_M; have nH0H := normal_norm nsH0H.
have nsH0HU: H0 <| HU.
  by rewrite /normal (subset_trans sH0H) ?(subset_trans sHUM).
have nH0U: U \subset 'N(H0) := subset_trans sUHU (normal_norm nsH0HU).
have sCU: C \subset U := subsetIl U _; have nH0C := subset_trans sCU nH0U.
have sH0C_HU: H0C \subset HU.
  by rewrite join_subG normal_sub ?(subset_trans sCU). 
have nsH0C_HU := normalS sH0C_HU sHUM nsH0C_M.
have nH0C_HU := normal_norm nsH0C_HU.
have coHU: coprime #|H| #|U|.
  have hallH: \pi(H).-Hall(HU) H := pHall_subl sHHU sHUM (Fcore_Hall M).
  by rewrite (coprime_sdprod_Hall defHU) (pHall_Hall hallH).
have [coH0U coHC] := (coprimeSg sH0H coHU, coprimegS sCU coHU).
have [nH0C_H nH0C_U] := (subset_trans sHHU nH0C_HU, subset_trans sUHU nH0C_HU).
have{coHC} tiHOC_H: H0C :&: H = H0.
  by rewrite /= norm_joinEr // -group_modl // setIC coprime_TIg ?mulg1.
have{coH0U} tiHOC_U: H0C :&: U = C.
  by rewrite /= norm_joinEr // setIC -group_modr // setIC coprime_TIg ?mul1g.
have isoHbar: Hbar \isog (H / H0C)%g.
  by have:= second_isog nH0C_H; rewrite tiHOC_H.
have isoUbar: Ubar \isog (U / H0C)%g.
  by have:= second_isog nH0C_U; rewrite tiHOC_U.
have defHUbar: ((H / H0C) ><| (U / H0C) = HU / H0C)%g.
  exact: quotient_coprime_sdprod.
have frobHU: [Frobenius HU / H0C = (H / H0C) ><| (U / H0C)]%g.
  apply/Frobenius_semiregularP=> //; first by rewrite -(isog_eq1 isoHbar).
    by rewrite -(isog_eq1 isoUbar); have [] := Frobenius_context frobUW1c.
  move=> yb /setD1P[ntyb /morphimP[y nH0Cy Uy] Dyb] /=; rewrite Dyb.
  apply/trivgP/subsetP=> _ /setIP[/morphimP[/= x nHOCx Hx ->] /cent1P/commgP].
  rewrite -morphR //; set xy := [~ x, y] => /eqP/coset_idr/=H0Cxy.
  rewrite inE coset_id ?mem_gen // inE coset_idr ?(subsetP nH0H) //.
  apply: contraNeq ntyb.
  rewrite -(morph_injm_eq1 inj_phi) ?mem_quotient // => nz_x.
  rewrite {yb}Dyb /= coset_id ?mem_gen // -Kpsi !inE Uy orbC /= -val_eqE.
  have [nH0x nH0y] := (subsetP nH0H x Hx, subsetP nH0U y Uy).
  rewrite -(inj_eq (mulfI nz_x)) mulr1 -[_ * _]phiJ ?mem_quotient // qactJ nH0y.
  rewrite -morphJ // conjg_mulR -/xy mkerr ?eqxx // ker_coset -tiHOC_H inE.
  by rewrite andbC groupM ?groupV ?memJ_norm ?(subsetP nHU) //= H0Cxy ?groupR.
have I_XH0_C i: i != 0 -> 'I_HU['chi[Hbar]_i %% H0]%CF = HC.
  move=> /= nz_i; apply/eqP; rewrite eqEsubset join_subG sub_inertia //= andbC.
  have [j Dj]: exists j : Iirr (H / H0C),
    {in H, forall x, 'chi_i (inMb x) = 'chi_j (coset H0C x)}.
  - have{nz_i} [h injh Dh] := second_isom nH0C_H.
    have [h' [Dh' _ _ im_h']] := domP (invm_morphism injh) (Dh _ (subxx _)).
    do [set K := H0C; rewrite -tiHOC_H -(im_invm injh) -im_h' Dh //=] in i *.
    exists (cfIirr (cfMorph 'chi_i)) => x Hx.
    rewrite cfIirrE ?cfMorph_irr //.
    rewrite cfMorphE ?mem_quotient //=; congr ('chi_i _).
    rewrite Dh'; apply: (canRL_in (invmE injh)); first exact: mem_quotient.
    apply: set1_inj; rewrite -morphim_set1 ?mem_quotient //.
    rewrite -!quotient_set1 ?Dh ?sub1set ?(subsetP nH0C_H) //= tiHOC_H.
    by rewrite (subsetP nH0H).
  have{nz_i} nz_j: j != 0.
    apply: contraNneq nz_i => j0.
    apply/eqP/irr_inj/cfun_inP=> _ /morphimP[x _ Hx ->].
    by rewrite Dj // j0 !irr0 !cfun1E !mem_quotient.
  apply/andP; do [split; apply/subsetP] => [y /setIP[Uy] | xy Ixy].
    rewrite astabQ => /morphpreP[nH0y /centP cHby].
    have nHy := subsetP nHU y Uy.
    rewrite inE nHy (subsetP sUHU) //=; apply/eqP/cfun_inP=> /= x Hy.
    rewrite cfConjgE ?cfModE ?memJ_norm ?morphJ ?groupV // ?(subsetP nH0H) //=.
    by rewrite morphV // /conjg invgK mulgA cHby ?mem_quotient ?mulgK.
  have [x [y [Hx Uy Dxy _]]] :=
    mem_sdprod defHU (subsetP (inertia_sub _ _) _ Ixy).
  have [nH0y nHOCy] := (subsetP nH0U y Uy, subsetP nH0C_U y Uy).
  rewrite -genM_join Dxy mem_gen ?mem_mulg //= -/C.
  rewrite -tiHOC_U inE Uy andbT coset_idr //.
  rewrite {xy}Dxy groupMl ?(subsetP (sub_inertia _ _) x) {x Hx}//= in Ixy.
  have [nHy [_ _ _ tiHUbar]] := (subsetP nHU y Uy, sdprodP defHUbar).
  set yb := coset H0C y; have nHyb: yb \in 'N(H / _).
    by rewrite (subsetP (quotient_norm _ _)) ?mem_quotient.
  apply/set1P; rewrite -set1gE -tiHUbar inE -groupV andbC.
  rewrite -(inertia_Frobenius_ker (FrobeniusWker frobHU) nz_j).
  rewrite inE !groupV nHyb !{1}mem_quotient ?(subsetP sUHU) //=.
  apply/eqP/cfun_inP=> _ /morphimP[x nH0Cx Hx ->].
  rewrite cfConjgE ?groupV //= invgK.
  by rewrite -morphJ -?Dj -?cfModE ?memJ_norm // (inertia_valJ _ Ixy).
have defHCbar: (Hbar \x (C / H0) = HC / H0)%g.
  rewrite /= quotientY //.
  rewrite quotientIG /= ?quotient_astabQ ?astabQ ?sub_cosetpre //.
  by rewrite dprodEY ?subsetIr //= setIA -quotientGI // tiHU quotient1 setI1g.
have sHCHU: HC \subset HU by rewrite join_subG sHHU (subset_trans sCU).
have nsHCHC: HC <| HU := normalS sHCHU sHUM nsHC_M.
have nsH0HC: H0 <| HC :=
  normalS (subset_trans sH0H (joing_subl _ _)) sHCHU nsH0HU.
have{I_XH0_C} irr_IndHC r: r \in Iirr_kerD HC H H0 -> 'Ind 'chi_r \in irr HU.
  rewrite !inE andbC => /andP[/quo_IirrK <- //]; have nHHU := normal_norm nsHHU.
  rewrite -[_ r](inv_dprod_IirrK defHCbar).
  case: (inv_dprod_Iirr _ _) => i j Kij'H.
  have{Kij'H} nz_i: i != 0.
    apply: contraNneq Kij'H => ->.
    rewrite mod_IirrE ?cfker_Morph ?normal_norm // cfkerEirr dprod_IirrE.
    rewrite subsetI joing_subl -sub_quotient_pre //; apply/subsetP=> x Hx.
    by rewrite irr0 cfDprod1l !inE -[1%g]mulg1 -[x]mulg1 !cfDprodEr.
  rewrite inertia_Ind_irr // mod_IirrE // dprod_IirrE; apply/subsetP=> y Iij_y.
  have /setId2P[HUy nHCy _] := Iij_y; have nHy := subsetP nHHU y HUy.
  rewrite -(I_XH0_C i nz_i) -groupV inE !groupV HUy nHy /=.
  apply/eqP/cfun_inP=> x Hx; have HCx: x \in HC by rewrite mem_gen 1?inE ?Hx.
  rewrite cfConjgE ?groupV ?invgK ?cfModE ?memJ_norm //.
  apply: (mulIf (irr1_neq0 j)).
  rewrite -!(cfDprodE defHCbar) ?mem_quotient ?mulg1 -?cfModE ?memJ_norm //.
  by rewrite (inertia_valJ _ Iij_y).
have [nb_mu H0C_mu] := nb_redM_H0; set part_a' := ({in X_ H0C', _}).
have Part_a s: s \in X_ H0 -> exists r, 'chi_s = 'Ind[HU, HC] 'chi_r.
  rewrite !inE => /andP[Ks'H KsH0]; have [r sHCr] := constt_cfRes_irr HC s.
  have{KsH0} KrH0: H0 \subset cfker 'chi_r.
    apply: subset_trans (cfker_constt (cfRes_char _ (irr_char s)) sHCr).
    by rewrite cfker_Res ?irr_char // subsetI normal_sub.
  rewrite -constt_Ind_constt_Res in sHCr.
  have{Ks'H} Kr'H: ~~ (H \subset cfker 'chi_r).
    apply: contra Ks'H => KrH.
    apply: subset_trans (cfker_constt (cfInd_char _ (irr_char r)) sHCr).
    by rewrite cfker_Ind_irr ?sub_gcore ?normal_norm.
  have [|s1 Ds1] := irrP _ (irr_IndHC r _); first by rewrite !inE Kr'H.
  by exists r; rewrite Ds1 constt_irr !inE in sHCr *; rewrite (eqP sHCr).
have Du: u = #|HU : HC|.
  rewrite -divgS //= norm_joinEr ?(subset_trans sCU) //.
  rewrite coprime_cardMg ?(coprimegS sCU) // -(sdprod_card defHU).
  by rewrite divnMl ?divg_normal //= -/C -tiHOC_U setIC norm_normalI.
have Part_a': part_a'.
  move=> s /setDP[KsH0C' Ks'H]; have [|r Ds] := Part_a s.
    by rewrite inE Ks'H (subsetP (Iirr_kerS _ _) _ KsH0C') ?joing_subl.
  suffices lin_r: 'chi_r \is a linear_char.
    by split; [rewrite Du Ds cfInd1 ?lin_char1 ?mulr1 | exists 'chi_r].
  have KrH0C': H0C' \subset cfker 'chi_r.
    rewrite inE Ds in KsH0C'.
    by rewrite sub_cfker_Ind_irr ?(subset_trans sHUM) ?normal_norm in KsH0C'.
  rewrite lin_irr_der1 (subset_trans _ KrH0C') //=.
  have nH0HC := subset_trans sHCHU (normal_norm nsH0HU).
  rewrite (norm_joinEr (subset_trans (der_sub 1 _) nH0C)).
  rewrite -quotientSK ?(subset_trans (der_sub 1 _)) ?quotient_der //= -/C.
  have [_ _ _ tiHCbar] := dprodP defHCbar; rewrite dprodEcprod // in defHCbar.
  by rewrite -(der_cprod 1 defHCbar) (derG1P (abelem_abelian abelHbar)) cprod1g.
split=> // [s /Part_a[r ->] | | {Part_a' part_a'}red_H0C'].
- by rewrite Du cfInd1 // dvdC_mulr // Cint_Cnat ?Cnat_irr1.
- split=> // mu_j /H0C_mu H0C_mu_j; have [s XH0Cs Dmuj] := seqIndP H0C_mu_j.
  have [|s1u [xi lin_xi Ds]] := Part_a' s.
    by rewrite (subsetP _ _ XH0Cs) ?Iirr_kerDS // genS ?setUS ?der_sub.
  split=> //; first by rewrite Dmuj cfInd1 // s1u -natrM -(sdprod_index defM).
  by rewrite Dmuj Ds cfIndInd //; exists xi.
have nsH0M: H0 <| M by rewrite /normal (subset_trans (normal_sub nsH0HU)).
have C1: C = 1%g.
  apply: contraTeq red_H0C' => ntC; apply/allPn.
  have solCbar: solvable (C / H0)%g.
    rewrite quotient_sol ?(solvableS sCU) ?nilpotent_sol //.
    by have [_ []] := MtypeP.
  have [|{ntC solCbar} j lin_j nz_j] := solvable_has_lin_char _ solCbar.
    rewrite -(isog_eq1 (quotient_isog _ _)) ?(subset_trans sCU) //.
    by rewrite coprime_TIg ?(coprimegS sCU) ?(coprimeSg sH0H).
  have [|i lin_i nz_i] := solvable_has_lin_char ntHbar.
    exact: abelian_sol (abelem_abelian abelHbar).
  pose r := mod_Iirr (dprod_Iirr defHCbar (i, j)).
  have KrH0: H0 \subset cfker 'chi_r by rewrite mod_IirrE ?cfker_Mod.
  have Kr'H: ~~ (H \subset cfker 'chi_r).
    apply: contra nz_i => KrH; apply/eqP/cfun_inP=> xb /= Hxb.
    rewrite -[_ xb]mulr1 -(lin_char1 lin_j) -(cfDprodE defHCbar) // mulg1.
    rewrite cfun1E Hxb cfker1 ?lin_char1 ?cfDprod_lin_char //.
    rewrite (subsetP _ _ Hxb) // sub_quotient_pre // (subset_trans KrH) //.
    by rewrite mod_IirrE // dprod_IirrE cfker_Morph ?normal_norm ?subsetIr.
  have [|s Ds] := irrP _ (irr_IndHC r _); first by rewrite !inE Kr'H.
  have Ks'H: s \notin Iirr_ker HU H.
    by rewrite inE -Ds sub_cfker_Ind_irr ?normal_norm.
  exists ('Ind 'chi_s).
    rewrite mem_seqInd ?gFnormal // inE Ks'H inE -Ds.
    rewrite sub_cfker_Ind_irr ?(subset_trans sHUM) ?normal_norm //=.
    rewrite mod_IirrE ?cfker_Morph ?normal_norm // subsetI.
    rewrite genS ?setUSS ?der_sub //.
    rewrite -sub_quotient_pre ?(subset_trans (normal_sub nsH0C'_M)) //.
    rewrite quotientYidl ?(subset_trans (der_sub 1 _)) ?quotient_der //= -/C.
    rewrite (subset_trans (dergS 1 (quotientS H0 (joing_subr H C)))) //=.
    by rewrite -lin_irr_der1 dprod_IirrE cfDprod_lin_char.
  apply: contra nz_j => red_j; have /implyP := H0C_mu ('Ind 'chi_s).
  rewrite mem_filter red_j !mem_seqInd ?gFnormal // !in_setD Ks'H !inE -Ds.
  rewrite !sub_cfker_Ind_irr ?(normal_norm nsH0HU) //.
  rewrite mod_IirrE 1?{1}cfker_Mod //= dprod_IirrE.
  rewrite cfker_Morph ?(subset_trans (subset_trans sHCHU sHUM)) //=.
  rewrite subsetI !join_subG andbA andbC -sub_quotient_pre //= => /andP[KijC _].
  apply/eqP/cfun_inP=> yb Cyb; rewrite -[_ yb]mul1r -(lin_char1 lin_i) cfun1E.
  rewrite Cyb -(cfDprodE defHCbar) // mul1g cfker1 ?(subsetP KijC) //.
  by rewrite lin_char1 ?cfDprod_lin_char.
rewrite /= -/C C1 joingG1 /= in frobHU; split=> //.
move/FrobeniusWker in frobHU.
have ->: (p ^ q).-1 = (#|X_ H0| * u)%N.
  rewrite -oF -cardsT -im_phi card_injm // -sum_nat_const.
  rewrite -(card_Iirr_abelian (abelem_abelian abelHbar)) -(cardC1 0).
  pose h r := mod_Iirr (cfIirr ('Ind[HU / H0, Hbar] 'chi_r)).
  have hE := cfIirrPE (irr_induced_Frobenius_ker frobHU).
  rewrite -sum1_card (partition_big h (mem (X_ H0))) => [|r nz_r]; last first.
    rewrite !inE mod_IirrE // cfker_Mod // andbT hE //.
    rewrite cfker_Morph ?normal_norm // subsetI sHHU -sub_quotient_pre //.
    rewrite sub_cfker_Ind_irr ?quotientS ?quotient_norms ?normal_norm //.
    by rewrite subGcfker.
  apply: eq_bigr => s; rewrite !inE andbC => /andP[/quo_IirrK <- //].
  move/(quo_Iirr H0) in s *.
  rewrite mod_IirrE // cfker_Morph ?normal_norm // subsetI sHHU.
  rewrite -sub_quotient_pre // => /(Frobenius_Ind_irrP frobHU)[r nzr Ds].
  transitivity (\sum_(r1 | 'chi_r1 \in 'chi_r ^: (HU / H0)) 1)%N%CF.
    apply/esym/eq_bigl=> r1; rewrite !inE; have [-> | nz_r1] /= := altP eqP.
      rewrite cfclass_sym irr0 cfclass1 ?quotient_normal //.
      by rewrite inE irr_eq1 (negPf nzr).
    rewrite -(inj_eq irr_inj) !mod_IirrE ?hE //.
    rewrite (can_eq (fun _ => cfModK _ _)) //.
    by rewrite Ds (sameP (cfclass_Ind_irrP _ _ _) eqP) ?quotient_normal.
  rewrite Du (cfclass_sum _ (fun _ => 1%N)) ?quotient_normal //= C1 joingG1.
  rewrite (big_nth 0) sum_nat_const_nat subn0.
  rewrite cfclass_size inertia_Frobenius_ker //= muln1.
  by rewrite index_quotient_eq ?(subset_trans sHUM) // setIC subIset ?sH0H.
suffices ->: #|X_ H0| = p.-1 by rewrite -(subnKC (prime_gt1 p_pr)) mulKn.
have{red_H0C'} red_H0: all redM (S_ H0).
  by rewrite (group_inj _ : H0 = H0C') //= C1 derg1 commG1 joingG1.
rewrite cardE -(size_map (fun r => 'Ind[M] 'chi_r)) -nb_mu.
apply/perm_eq_size/uniq_perm_eq; first 1 last.
- by rewrite ?filter_uniq ?seqInd_uniq.
- move=> eta; rewrite mem_filter (andb_idl (allP red_H0 eta)).
  by rewrite (sameP imageP seqIndP).
pose unInd eta : 'CF(HU) := q%:R^-1 *: 'Res[HU, M] eta.
suffices IndH0_K: {in X_ H0, forall s, unInd ('Ind 'chi_s) = 'chi_s}.
  have unInd_irr: {in S_ H0, forall eta, unInd eta \in irr HU}.
    by move=> _ /seqIndP[s /IndH0_K Ind_s_K ->]; rewrite Ind_s_K mem_tnth.
  apply/dinjectiveP.
  apply: can_in_inj (fun (x : 'CF(M)) => cfIirr (unInd x)) _ => s XH0s.
  apply/irr_inj.
  by rewrite (cfIirrPE unInd_irr) ?IndH0_K ?mem_seqInd ?gFnormal.
move=> s XH0s; rewrite /= /unInd induced_sum_rcosets //; set T := 'I_M[_]%CF.
have [sHUT sTM]: HU \subset T /\ T \subset M by rewrite inertia_sub sub_inertia.
suffices defT: T = M.
  rewrite defT -(sdprod_index defM) scalerK ?neq0CG //.
  by rewrite -[in M in (_ ^: M)%CF]defT cfclass_inertia big_seq1.
apply/eqP; rewrite eqEcard sTM -(Lagrange sHUT) /= -/T.
suffices ->: #|T : HU| = q by rewrite /q (sdprod_index defM) Lagrange.
apply/prime_nt_dvdP=> //; last by rewrite /q (sdprod_index defM) indexSg.
have: redM ('Ind 'chi_s) by apply/(allP red_H0)/seqIndP; exists s.
by apply: contra; rewrite indexg_eq1; apply: inertia_Ind_irr.
Qed.

(* This is Peterfalvi (9.10), formulated as a constructive alternative. *)
Lemma typeP_reducible_core_cases :
  {t : Iirr M & 'chi_t \in S_ H0C' /\ 'chi_t 1%g = (q * u)%:R
              & {xi | xi \is a linear_char & 'chi_t = 'Ind[M, HC] xi}}
  + [/\ typeP_Galois, [Frobenius HU / H0 = Hbar ><| (U / H0)]%g,
        cyclic U, #|U| = (p ^ q).-1 %/ p.-1
      & FTtype M == 2 -> [Frobenius HU = H ><| U]].
Proof.
have [GalM | Gal'M] := boolP typeP_Galois; last first.
  pose eqInHCb nu r := ('chi_r \is a linear_char) && (nu == 'Ind[M, HC] 'chi_r).
  pose isIndHCb (nu : 'CF(M)) :=
    (nu 1%g == (q * u)%:R) && [exists r, eqInHCb nu r].
  suffices /sig2W[t H0C't]: exists2 t, 'chi_t \in S_ H0C' & isIndHCb 'chi_t.
    case/andP=> /eqP t1qu /exists_inP/sig2W[r lin_r /eqP def_t].
    by left; exists t => //; exists 'chi_r.
  have [_ _ [t [t1qu H0Ct [xi lin_xi def_t]]] _] :=
    typeP_nonGalois_characters Gal'M.
  exists t.
    by apply: seqIndS H0Ct; rewrite Iirr_kerDS ?genS // setUS ?der_sub.
  apply/andP; rewrite t1qu def_t; split=> //; apply/exists_inP.
  by have /irrP[r Dxi] := lin_char_irr lin_xi; exists r; rewrite -Dxi.
have [_ IndHC_SH0C' _] := typeP_Galois_characters GalM; rewrite all_predC.
case: hasP => [/sig2W[eta H0C'eta /irrP/sig_eqW[t Dt]] _ | _ [//|C1 <- frobHU]].
  have /sig2_eqW[s /IndHC_SH0C'[s1u /sig2_eqW[xi lin_xi Ds]] Deta]
    := seqIndP H0C'eta.
  have [[_ /mulG_sub[sHUM _] _ _] [_ mulHU _ _]]
    := (sdprodP defM, sdprodP defHU).
  left; exists t; [split | exists xi]; rewrite -?Dt // Deta.
    by rewrite cfInd1 // -(sdprod_index defM) s1u -natrM.
  by rewrite Ds cfIndInd //= -genM_join gen_subG /= -mulHU mulgS ?subsetIl.
have cycU: cyclic U.
  rewrite (isog_cyclic (quotient1_isog _)) -C1.
  by have [_ _ []] := typeP_Galois_P GalM.
right; split=> //; first by rewrite /u /Ubar C1 -(card_isog (quotient1_isog _)).
case/(compl_of_typeII MtypeP) => // _ _ _ UtypeF <-.
have [_ -> _] := typeF_context UtypeF.
by apply/forall_inP=> S /and3P[_ /cyclicS->].
Qed.

Import ssrint.

(* This is Peterfalvi (9.11) *)
Lemma Ptype_core_coherence : coherent (S_ H0C') M^# tau.
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU _] nHU tiHU] := sdprod_context defHU.
have coHU: coprime #|H| #|U|.
  have hallH: \pi(H).-Hall(HU) H := pHall_subl sHHU sHUM (Fcore_Hall M).
  by rewrite (coprime_sdprod_Hall defHU) (pHall_Hall hallH).
have nsCU: C <| U := normalS (subsetIl _ _) (joing_subl _ _) nsCUW1.
have [sCU nCU] := andP nsCU; have sC'C: C^`(1)%g \subset C := der_sub 1 _.
have coHC := coprimegS sCU coHU; have coH0C := coprimeSg sH0H coHC.
have [nsH0C_M nsHC_M nsH0C'_M] := nsH0xx_M; have nH0H := normal_norm nsH0H.
have nH0HU := subset_trans sHUM nH0M; have nH0U := subset_trans sUHU nH0HU.
have nH0C := subset_trans sCU nH0U; have nH0C' := subset_trans sC'C nH0C.
have sHCHU: HC \subset HU by rewrite join_subG sHHU (subset_trans sCU).
have [nsHCHC nHC] := (normalS sHCHU sHUM nsHC_M, subset_trans sCU nHU).
have Du: u = #|HU : HC|.
  rewrite -divgS //= -(sdprod_card defHU) norm_joinEr // coprime_cardMg //.
  by rewrite divnMl ?divg_normal.
have tiHCbar: Hbar :&:(C / H0)%g = 1%g by rewrite coprime_TIg ?coprime_morph.
have defHCbar: Hbar \x (C / H0)%g = (HC / H0)%g.
  by rewrite dprodEY ?quotientY // -quotient_astabQ quotientS ?subsetIr.
have{tiHCbar} defHC'bar: (HC / H0)^`(1)%g = (C^`(1) / H0)%g.
  rewrite dprodEcprod // in defHCbar; rewrite -(der_cprod 1 defHCbar).
  by rewrite (derG1P (abelem_abelian abelHbar)) cprod1g quotient_der.
have sU'U := der_sub 1 U; have nH0U' := subset_trans sU'U nH0U.
have sU'C: U' \subset C.
  have [_ [cHU' _] _ _] := typeP_context MtypeP.
  by rewrite subsetI sub_astabQ sU'U nH0U' quotient_cents.
have uS0: uniq (S_ H0C') by exact: seqInd_uniq.
have [rmR scohM]: exists R : 'CF(M) -> seq 'CF(G), subcoherent (S_ H0C') tau R.
  move: (FTtypeP_coh_base _ _) (FTtypeP_subcoherent maxM MtypeP) => R scohR.
  exists R; apply: (subset_subcoherent scohR); split=> //; last first.
    exact: cfAut_seqInd.
  by apply: seqIndS; rewrite Iirr_kerDS ?sub1G //= /M`_\s; case: ifP.
have [GalM | Gal'M] := boolP typeP_Galois.
  have [_ XOC'u _ _] := typeP_Galois_characters GalM.
  apply: uniform_degree_coherence scohM _.
  apply: all_pred1_constant (#|M : HU| * u)%:R _ _.
  apply/allP=> _ /mapP[_ /seqIndP[s /XOC'u[s1u _] ->] ->] /=.
  by rewrite natrM cfInd1 ?s1u.
have:= typeP_nonGalois_characters Gal'M.
set U1 := 'C_U(_ | _); set a := #|_ : _|.
case: (_ Gal'M) => /= H1 [oH1 nH1U _ defHbar aP] in U1 a *.
rewrite -/U1 -/a in aP; case: aP => a_gt1 a_dv_p1 cycU1 _.
case=> [a_dv_XH0 [nb_mu IndHCmu] has_irrHC lb_Sqa]; rewrite -[S_ _]/(S_ H0C').
have defHb1 := defHbar; rewrite (big_setD1 1%g) ?group1 ?conjsg1 //= in defHb1.
have [[_ H1c _ defH1c] _ _ _] := dprodP defHb1; rewrite defH1c in defHb1.
have [nsH1H _] := dprod_normal2 defHb1; have [sH1H _] := andP nsH1H.
have nsU1U: U1 <| U; last have [sU1U nU1U] := andP nsU1U.
  by rewrite norm_normalI // astabQ norm_quotient_pre ?norms_cent.
have Da: a = #|HU : H <*> U1|.
  rewrite /a -!divgS /= ?join_subG ?sHHU ?norm_joinEr ?(subset_trans sU1U) //=.
  by rewrite -(sdprod_card defHU) coprime_cardMg ?(coprimegS sU1U) ?divnMl.
have a_dv_u: a %| u by rewrite Da Du indexgS // genS ?setUS // setIS ?astabS.
have [a_gt0 q_gt0 u_gt0 p1_gt0]: [/\ 0 < a, 0 < q, 0 < u & 0 < p.-1]%N.
  rewrite !cardG_gt0 ltnW // -subn1 subn_gt0 prime_gt1 //.
have [odd_p odd_q odd_a]: [/\ odd p, odd q & odd a].
  by rewrite mFT_odd -oH1 (oddSg sH1H) ?(dvdn_odd a_dv_u) ?mFT_quo_odd.
have Dp: p = (2 * p.-1./2 + 1)%N.
  by rewrite mul2n -[p]odd_double_half odd_p half_double addn1.
(* Start of main proof. *)
pose S1 := filter [pred zeta : 'CF(M) | zeta 1%g == (q * a)%:R] (S_ H0C').
have ntS1: (0 < size S1)%N.
  have [lb_dv lbS1] := lb_Sqa; apply: leq_trans (leq_trans lbS1 _).
    by rewrite ltn_divRL // mul0n muln_gt0 p1_gt0 cardG_gt0.
  rewrite count_filter uniq_leq_size ?filter_uniq ?seqInd_uniq // => chi.
  rewrite !mem_filter -andbA /= => /and3P[_ ->].
  by apply: seqIndS; rewrite Iirr_kerDS // genS ?setUS ?dergS ?subsetIl.
have uccS1: [/\ uniq S1, {subset S1 <= S_ H0C'} & conjC_closed S1].
  split=> [||chi]; first by rewrite filter_uniq.
    by apply: mem_subseq; apply: filter_subseq.
  rewrite !mem_filter !inE cfunE => /andP[/eqP <- S0chi].
  by rewrite cfAut_seqInd // andbT conj_Cnat ?(Cnat_seqInd1 S0chi).
have cohS1: coherent S1 M^# tau.
  apply: uniform_degree_coherence (subset_subcoherent scohM uccS1) _.
  by apply: all_pred1_constant (q * a)%:R _ _; rewrite all_map filter_all.
pose S3 := filter [predC S1] (S_ H0C'); move: {2}_.+1 (ltnSn (size S3)) => nS. 
move: @S3 (uccS1) (cohS1); have: {subset S1 <= S1} by [].
elim: nS {-1}S1 => // nS IHnS S2 => sS12 S3 uccS2 cohS2; rewrite ltnS => leS3nS.
have [ntS3|] := boolP (size S3 > 0)%N; last first.
  rewrite -count_filter -has_count has_predC negbK => /allP sS02.
  exact: subset_coherent sS02 cohS2.
(* Ultimateley we'll contradict the maximality of S2 in (9.11.1) & (9.11.8). *)
suff [chi]: exists2 chi, chi \in S3 & coherent (chi :: chi^* ::S2)%CF M^# tau.
  rewrite mem_filter => /andP[/= S2'chi S0chi]; have[uS2 sS20 ccS2] := uccS2.
  move/IHnS; apply=> [psi /sS12 S1psi||]; first by rewrite 2?mem_behead.
    rewrite /= !inE negb_or S2'chi (contra (ccS2 _)) ?cfConjCK // eq_sym.
    split; first by rewrite (seqInd_conjC_neq _ _ _ S0chi) ?mFT_odd.
     by apply/allP; rewrite /= S0chi cfAut_seqInd //=; apply/allP.
    apply/allP; rewrite /= !inE cfConjCK !eqxx orbT /=.
    by apply/allP=> psi /ccS2; rewrite !inE orbA orbC => ->.
  apply: leq_trans leS3nS; rewrite ltnNge; apply: contra S2'chi.
  case/leq_size_perm=> [|psi|/(_ chi)]; first by rewrite filter_uniq.
    by rewrite !mem_filter !inE orbA negb_or -andbA => /andP[].
  by rewrite !mem_filter !inE eqxx S0chi !andbT => /esym/negbFE.
(* This is step (9.11.1). *) clear nS IHnS leS3nS.
without loss [[eqS12 irrS1 H0C_S1] [Da_p defC] [S3qa ne_qa_qu] [oS1 oS1ua]]:
  / [/\ [/\ S1 =i S2, {subset S1 <= irr M} & {subset S1 <= S_ H0C}],
        a = p.-1./2 /\ C = U',
        (forall chi, chi \in S3 -> chi 1%g == (q * u)%:R) /\ (q * u != q * a)%N
      & size S1 = (p.-1 * u %/ a ^ 2)%N /\ size S1 = (2 * u %/ a)%N].
- move=> IHwlog; have [[uS2 sS20 ccS2] [uS1 _ _]] := (uccS2, uccS1).
  pose is_qu := [pred chi : 'CF(M) | chi 1%g == (q * u)%:R].
  pose isn't_qu := [pred chi | is_qu chi ==> all is_qu S3].
  have /hasP[chi S3chi qu'chi]: has isn't_qu S3.
    rewrite /isn't_qu; have [_|] := boolP (all _ _); last by rewrite has_predC. 
    by rewrite (eq_has (fun _ => implybT _)) has_predT.
  have [S2'chi S0chi]: chi \notin S2 /\ chi \in S_ H0C'.
    by apply/andP; rewrite mem_filter in S3chi.
  have [s X0C's Dchi] := seqIndP S0chi.
  have Dchi1: chi 1%g = q%:R * 'chi_s 1%g.
    by rewrite Dchi cfInd1 // -(sdprod_index defM).
  (* We'll show lb0 <= lb1 <= lb <= lb3 <= sumnS S1' <= sumnS S2 <= lb0,   *)
  (* with equality under conditions that imply the conclusion of (9.11.1). *)
  pose lb0 := (2 * q * a)%:R * chi 1%g.
  pose lb1 : algC := (2 * a * q ^ 2 * u)%:R.
  pose lb2 : algC := (p.-1 * q ^ 2 * u)%:R.
  pose lb3 : algC := (p.-1 * q ^ 2 * #|U : U'|)%:R.
  pose S1' := filter [predI irr M & S_ H0U'] S1.
  pose szS1' := ((p.-1 * #|U : U'|) %/ a ^ 2)%N; set lbS1' := _ %/ _ in lb_Sqa.
  pose Snorm (psi : 'CF(M)) := psi 1%g ^+ 2 / '[psi].
  pose sumnS Si := \sum_(psi <- Si) Snorm psi.
  have lb01: lb0 <= lb1 ?= iff (chi 1%g == (q * u)%:R).
    rewrite /lb1 mulnA -mulnA natrM /lb0 mulnAC.
    rewrite mono_lerif; last by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 a_gt0.
    apply: lerif_eq; rewrite Dchi1 natrM ler_pmul2l ?gt0CG //.
    have [KsH0C' _] := setDP X0C's; rewrite inE in KsH0C'.
    have [t sHCt] := constt_cfRes_irr HC s.
    have KtH0C': H0C' \subset cfker 'chi_t.
      apply: subset_trans (cfker_constt (cfRes_char _ (irr_char s)) sHCt).
      by rewrite cfker_Res ?irr_char // subsetI genS ?setUSS.
    rewrite -constt_Ind_constt_Res in sHCt.
    apply: ler_trans (char1_ge_constt (cfInd_char _ (irr_char t)) sHCt) _.
    rewrite cfInd1 // -Du lin_char1 ?mulr1 // lin_irr_der1.
    apply: subset_trans KtH0C'; rewrite /= (norm_joinEr nH0C') /= -/C.
    rewrite -quotientSK ?(subset_trans (der_sub _ _)) ?(subset_trans sHCHU) //.
    by rewrite -defHC'bar quotient_der ?(subset_trans sHCHU).
  have lb12: lb1 <= lb2 ?= iff (a == p.-1./2).
    rewrite -(@eqn_pmul2l 2) // -(canLR (addnK 1) Dp) -eqC_nat subn1.
    rewrite /lb2 -mulnA mulnC natrM /lb1 -mulnA mulnC natrM.
    rewrite mono_lerif; last by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 q_gt0.
    apply: lerif_eq; rewrite leC_nat dvdn_leq // Gauss_dvd //.
       by rewrite {1}Dp addn1 dvdn_mulr.
    by rewrite prime_coprime ?dvdn2 ?negbK.
  have lb23: lb2 <= lb3 ?= iff (C == U') :> algC.
    rewrite /lb3 natrM /lb2 natrM [u]card_quotient // !natf_indexg //= -/C.
    rewrite 2?mono_lerif; first 2 [by apply: ler_pmul2l; apply: gt0CG]; last first.
      by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 p1_gt0 q_gt0.
    have /subset_leqif_cards[leU'C eqU'C] := sU'C.
    rewrite eq_sym -{}eqU'C eq_sym -eqC_nat -(inj_eq invr_inj).
    by apply: lerif_eq; rewrite lef_pinv ?posrE ?gt0CG // leC_nat.
  have lb3S1': lb3 <= sumnS S1' ?= iff (size S1' == szS1').
    rewrite /szS1' -(divnMr (cardG_gt0 U')) mulnAC -mulnA Lagrange // -/lbS1'.
    have{lb_Sqa} [dv_lb lbSqa] := lb_Sqa; rewrite [sumnS S1']big_seq.
    rewrite (eq_bigr (fun _ => ((q * a) ^ 2)%:R)) => [|psi]; last first.
      rewrite !mem_filter -!andbA => /and4P[/irrP[r ->] _ /=/eqP r1qa _].
      by rewrite /Snorm cfnorm_irr divr1 r1qa natrX.
    rewrite -big_seq (big_nth 0) -natr_sum sum_nat_const_nat subn0.
    rewrite mulnC natrM [*%R]lock /lb3 natrM natf_indexg ?der_sub // mulrA.
    rewrite -natrM mulnAC -(divnK dv_lb) mulnAC mulnA natrM mulfK ?neq0CG //.
    rewrite -/lbS1' -mulnA -expnMn natrM mulrC -eqC_nat -lock mono_lerif; last first.
      by apply: ler_pmul2l; rewrite ltr0n !muln_gt0 a_gt0 q_gt0.
    rewrite eq_sym; apply: lerif_eq; rewrite leC_nat (leq_trans lbSqa) //.
    rewrite count_filter uniq_leq_size ?filter_uniq ?seqInd_uniq // => psi.
    rewrite !mem_filter -!andbA /= => /and3P[-> -> S0psi]; rewrite S0psi.
    by apply: seqIndS S0psi; rewrite Iirr_kerDS //= genS ?setUS ?dergS.
  have lbS1'2: sumnS S1' <= sumnS S2 ?= iff ~~ has [predC S1'] S2.
    have Ds2: perm_eq S2 (S1' ++ filter [predC S1'] S2).
      rewrite -(perm_filterC (mem S1')) perm_cat2r.
      rewrite uniq_perm_eq ?filter_uniq // => psi.
      by rewrite mem_filter andb_idr //= mem_filter => /andP[_ /sS12].
    rewrite [sumnS S2](eq_big_perm _ Ds2) big_cat /= -/(sumnS S1') big_filter.
    rewrite -all_predC -big_all_cond !(big_tnth _ _ S2) big_andE.
    rewrite -{1}[_ S1']addr0 mono_lerif; last exact: ler_add2l.
    set sumS2' := \sum_(i | _) _; rewrite -[0]/(sumS2' *+ 0) -sumrMnl.
    apply: lerif_sum => i _; apply/lerifP; rewrite lt0r !mulf_eq0 invr_eq0.
    set psi := tnth _ i; have Spsi := sS20 psi (mem_tnth _ _).
    rewrite !negb_or (seqInd1_neq0 _ Spsi) //= (cfnorm_seqInd_neq0 _ Spsi) //=.
    by rewrite divr_ge0 ?exprn_ge0 ?cfnorm_ge0 ?Cnat_ge0 ?(Cnat_seqInd1 Spsi).
  have [lb0S2 | ] := boolP (lb0 < sumnS S2).
    exists chi => //; have /hasP[xi S1xi _]: has predT S1 by rewrite has_predT.
    have xi1: xi 1%g = (q * a)%:R.
      by rewrite mem_filter in S1xi; have [/eqP] := andP S1xi.
    apply: ((extend_coherent scohM) _ xi) => //; first by rewrite S0chi sS12.
    split=> //; last by rewrite mulrAC xi1 -natrM mulnA.
    rewrite xi1 Dchi1 irr1_degree -natrM dvdC_nat dvdn_pmul2l ?cardG_gt0 //.
    rewrite -dvdC_nat /= !nCdivE -irr1_degree a_dv_XH0 //.
    by rewrite (subsetP (Iirr_kerDS _ _ _) _ X0C's) ?joing_subl.
  have lb1S2 := lerif_trans lb12 (lerif_trans lb23 (lerif_trans lb3S1' lbS1'2)).
  rewrite ltr_neqAle !(lerif_trans lb01 lb1S2) andbT has_predC !negbK.
  case/and5P=> /eqP chi1qu /eqP Da_p /eqP defC /eqP sz_S1' /allP sS21'.
  have defS1': S1' = S1.
    apply/eqP; rewrite -(geq_leqif (size_subseq_leqif (filter_subseq _ S1))).
    by rewrite uniq_leq_size // => psi /sS12/sS21'.
  apply: IHwlog; split=> //.
  + split=> psi; do 1?[rewrite -defS1' mem_filter andbC => /and3P[_ _] //=].
      by apply/idP/idP=> [/sS12 | /sS21']; rewrite ?defS1'.
    by congr (_ \in S_ _); apply/group_inj; rewrite /= defC.
  + split; first by apply/allP; apply: contraLR qu'chi; rewrite /= chi1qu eqxx.
    rewrite -eqC_nat -chi1qu; apply: contra S2'chi => chi1qa.
    by rewrite sS12 // mem_filter /= chi1qa.
  rewrite -defS1' sz_S1' /szS1' -defC -card_quotient // -/u.
  by split=> //; rewrite -mulnn {1}Dp addn1 -Da_p mulnAC divnMr.
have nCW1: W1 \subset 'N(C).
  by rewrite (subset_trans (joing_subr U W1)) ?normal_norm.
(* This is step (9.11.2). *) clear uccS2 cohS2 sS12 has_irrHC lb_Sqa sU'C.
have [tiU1 le_u_a2]: {in W1^#, forall w, U1 :&: U1 :^ w = C} /\ (u <= a ^ 2)%N.
  have tiU1 w: w \in W1^# -> U1 :&: U1 :^ w = C; last split => //.
    case/setD1P=> ntw W1w; have nH0w := subsetP (subset_trans sW1M nH0M) w W1w.
    pose wb := coset H0 w; have W1wb: wb \in (W1 / H0)^#%g.
      rewrite !inE mem_quotient ?(contraNneq _ ntw) // => /coset_idr H0w.
      rewrite -in_set1 -set1gE -tiHUW1 inE (subsetP sHHU) // (subsetP sH0H) //.
      by rewrite H0w.
    have [ntH1 abH1]: H1 :!=: 1%g /\ abelian H1.
      by rewrite -cardG_gt1 cyclic_abelian ?prime_cyclic ?prime_gt1 // oH1.
    have [t1 lin_t nz_t1] := solvable_has_lin_char ntH1 (abelian_sol abH1).
    pose theta1 := cfDprodl defHb1 'chi_t1.
    pose theta := (cfDprodl defHCbar (theta1 * (theta1 ^ wb)%CF))%CF.
    have lin_theta : theta \is a linear_char.
      by rewrite !(cfDprodl_lin_char, cfConjg_lin_char, rpredM).
    have KthC: (C / H0)%g \subset cfker theta.
      rewrite cfkerEchar ?lin_charW //; apply/subsetP=> y Cy; rewrite inE.
      rewrite (subsetP _ _ Cy) ?quotientS ?joing_subr //.
      rewrite -(mul1g 1%g) -(mul1g y) !cfDprodEl ?group1 //=.
    have [_ nsCbHC] := dprod_normal2 defHCbar.
    pose toHUb2 A := ((A / H0) / (C / H0))%g.
    have /irrP[t2 Dt2] := lin_char_irr lin_theta.
    have nsH2HU: toHUb2 HC <| toHUb2 HU by rewrite !quotient_normal.
    pose t2b : Iirr (toHUb2 HC) := quo_Iirr [group of C / H0]%g t2.
    have [s2 t2HUs2] := constt_cfInd_irr t2b (normal_sub nsH2HU).
    pose s2T := inertia_Ind_inv t2b 'chi_s2.
    have defIt: 'I_(toHUb2 HU)['chi_t2b] = toHUb2 (U1 :&: U1 :^ w) <*> toHUb2 HC.
      apply/eqP; rewrite eqEsubset join_subG sub_inertia ?quotientS //.
      rewrite andbT sub_gen.
        apply/subsetP=> yb /morphimP[_ _ /morphimP[y _ /setIP[U1y U1wy] ->] Dyb].
        have Uy := subsetP sU1U y U1y.
        have HUyb: yb \in toHUb2 HU by rewrite Dyb !mem_quotient ?(subsetP sUHU).
        have nHCyb: yb \in 'N(toHUb2 HC) by rewrite (subsetP _ _ HUyb) ?normal_norm.
        rewrite inE HUyb nHCyb; apply/eqP/cfun_inP=> xb HCxb.
Admitted.

End Nine.
