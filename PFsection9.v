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
  odflt 1%G [pick H0 : {group _} | chief_factor M H0 H && ('C_H(U) \subset H0)].
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
Notation "chi ^\tau" := (FT_Dade maxM chi).
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
        \big[dprod/1]_(w \in W1 / H0) H1 :^ w = Hbar
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
have [oH1 defHbar]: #|H1| = p /\ \big[dprod/1]_(w \in W1 / H0) H1 :^ w = Hbar.
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
    transitivity (\rank (\sum_(w \in W0) V1 *m rUW1 w))%R.
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
  have defHbar: \big[dprod/1]_(w \in W0) H1 :^ w = Hbar.
    have inj_rV_Hbar := rVabelem_injm abelHbar ntHbar.
    have/(injm_bigdprod _ inj_rV_Hbar)/= := bigdprod_rowg sumW0 dxW0.
    rewrite sub_im_abelem_rV rowg1 im_rVabelem => <- //=; apply: eq_bigr => w.
    by move/sW01=> Ww; rewrite abelem_rowgJ ?rowg_mxK ?abelem_rV_mK.
  have injW0: {in W0 &, injective (fun w => H1 :^ w)}.
    move=> x y Wx Wy /= eq_Hxy; apply: contraNeq ntH1 => neq_xy.
    rewrite -(conjsg_eq1 _ x) -[H1 :^ x]setIid {1}eq_Hxy; apply/eqP.
    rewrite (bigD1 y) // (bigD1 x) /= ?Wx // dprodA in defHbar.
    by case/dprodP: defHbar => [[_ _ /dprodP[_ _ _ ->] _]].
  have defH1W0: [set H1 :^ w | w <- W0] = [set H1 :^ w | w <- W1 / H0].
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
pose E_U := [pred A | A \in enveloping_algebra_mx rU]%MS.
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
  suffices /setP/(_ (alpha r)): [set (eta w) r | w <- W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: etaRM.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: etaRM.
  rewrite (@cardsE F) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP _ inj_eta) => //; apply: eq_w12; exact: etaRM.
have isoUb: isog Ubar (psi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a <- nF^#].
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
  suffices /setP/(_ (alpha r)): [set (eta w) r | w <- W1] = [set t | root P t].
    rewrite inE fPr0 // => /imsetP[w Ww def_wr]; exists w => //.
    by apply: prim_r => //; exact: eta_Aut.
  apply/eqP; rewrite eqEcard; apply/andP; split.
    by apply/subsetP=> _ /imsetP[w Ww ->]; rewrite inE fPr0 //; exact: eta_Aut.
  rewrite (@cardsE finF) card_in_imset // => w1 w2 Ww1 Ww2 /= /prim_r eq_w12.
  by apply: (injmP _ inj_eta) => //; apply: eq_w12; exact: eta_Aut.
have isoUb: isog Ubar (Mpsi @* U) by rewrite /Ubar -Kpsi first_isog.
pose unF := [set in_uF a | a <- nF^#].
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

Lemma cfConjg_lin_char (g1T : finGroupType) (H : {group g1T}) (phi : 'CF(H)) yy:
  phi \is a linear_char -> (phi ^ yy)%CF \is a linear_char.
Proof. by case/andP=> Nphi phi1; rewrite qualifE cfConjg_val1 cfConjg_char. Qed.

Local Notation H0C := (gval H0 <*> C).
Local Notation H0Cg := [group of H0C].
Local Notation HC := (H <*> C).
Local Notation HCg := [group of HC].
Local Notation HU := (gval M)^`(1)%g.
Local Notation HUg := M^`(1)%G.
Local Notation U' := (gval U)^`(1)%g.
Local Notation U'g := U^`(1)%G.
Local Notation H0U' := (gval H0 <*> U')%g.
Local Notation H0U'g := (H0 <*> U^`(1))%G.

Lemma typeP_nonGalois_characters (not_Galois : ~~ typeP_Galois) :
    let H1 := sval (typeP_Galois_Pn not_Galois) in
    let a := #|U : 'C_U(H1 | 'Q)| in
    let isIndHC (zeta : 'CF(M)) :=
      [/\ zeta 1%g = (q * u)%:R, zeta \in S_ H0Cg
        & exists2 xi, xi \is a linear_char & zeta = 'Ind[M, HC] xi] in
  [/\ (*a*) {in X_ H0, forall s, a %| 'chi_s 1%g}%C,
      (*b*) let mu_ := filter [predC irr M] (S_ H0) in
            size mu_ = p.-1 /\ {in mu_, forall mu_j, isIndHC mu_j},
      (*c*) exists t, isIndHC 'chi_t
    & (*d*) let irr_qa := [pred zeta \in irr M | zeta 1%g == (q * a)%:R] in
            let lb_num := (p.-1 * #|U|)%N in
            let lb_den := (a ^ 2 * #|U'|)%N in
            (lb_den %| lb_num
             /\ lb_num %/ lb_den <= count irr_qa (S_ H0U'g))%N].
Proof.
case: (typeP_Galois_Pn _) => H1 [oH1 nH1U nH1Uq defHbar aP]; rewrite [sval _]/=.
move=> H1d; rewrite {+}/H1d => {H1d} a isIndHC; rewrite -/a in aP.
have{aP}[a_gt1 a_dv_p1 cycUb1 _] := aP.
set redM := [predC irr M]; set muH0 := filter redM _.
set part_a := ({in _, _}); set part_b := let mu := muH0 in _.
set part_c := exists t, _; set part_d := let irr_qa := _ in _.
pose HCbar := (HCg / H0)%G; set W1bar := (W1 / H0)%g in defHbar.
have [[_ _ _ defM] [_ _ nUW1 defHU] _ _ _] := MtypeP.
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
    apply/subsetP=> x H0x; rewrite cfker_charE // inE cfRes1 //.
    by rewrite cfResE ?(subsetP sH0H) //= cfker1 // (subsetP kersH0).
  set T := 'I_HU['chi_t]; have sHT: H \subset T by rewrite sub_inertia.
  have sTHU: T \subset HU by rewrite inertia_sub.
  suffices{s sHt NsH} a_dv_iTHU: a %| #|HU : T|.
  (* The statement of (1.7)(a) is clumsy: what's this silly witness for ?!!? *)
    have /neq0_has_constt[r0 tTr0]: 'Ind[T] 'chi_t != 0.
      by rewrite cfInd_eq0 ?irr_char ?irr_neq0.
    have my17a := induced_inertia_irr nsHHU _ tTr0.
    set tT := irr_constt _ in my17a tTr0.
    suffices: existsb r, (r \in tT) && ('['chi_s, 'Ind 'chi_r] != 0).
      case/exists_inP=> r /my17a[/irrP[r1 DrHU] _] /eqP.
      rewrite DrHU cfdot_irr; case: eqP => // -> _; rewrite -DrHU cfInd1 //.
      by rewrite dvdC_mulr ?dvdC_nat // Cint_Cnat ?Cnat_irr1.
    rewrite -negb_forall_in; apply: contraL sHt => /forall_inP tT_s_0.
    rewrite inE negbK cfdot_Res_l; have [_ [_ ->]] := my17a _ tTr0.
    rewrite cfdot_sumr big1 // => r tTr; apply/eqP.
    by rewrite cfdotZr mulf_eq0 orbC tT_s_0.
  pose theta := ('chi_t / H0)%CF.
  have nHW1: W1 \subset 'N(H) by rewrite (subset_trans sW1M) ?gFnorm.
  have nHbarW1 := quotient_norms H0 nHW1.
  have [w W1w nt_th_w]: exists2 w, w \in (W1 / H0)%g & 'Res[H1 :^ w] theta != 1.
    apply/exists_inP; rewrite -negb_forall_in.
    apply: contra t_neq0 => /forall_inP=> tH1w1; apply/eqP/chi_inj.
    rewrite chi0_1 -(cfMod_cfun1 nsH0H) -(quo_IirrK nsH0H kertH0) mod_IirrE //.
    congr (_ %% H0)%CF; apply/eqP; rewrite irr_eq1 -subGcfker.
    rewrite -{1}(bigdprodEY defHbar) gen_subG /= cfker_irrE quo_IirrE //=.
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
    move=> z1 z2 Hz1 Hz2 eq_th_z12; apply/eqP.
    rewrite eq_mulgV1 -in_set1 (subsetP th_w_ff) // cfker_charE ?lin_charW //.
    rewrite inE groupM ?lin_charM ?groupV // lin_charV ?lin_char1 //=.
    by rewrite -(divff (lin_char_neq0 lin_th_w Hz2)) !cfResE // eq_th_z12.
  have defT: H ><| (U :&: T) = T.
    by rewrite (sdprod_modl defHU) // (setIidPr sTHU).
  rewrite -divgS // -(sdprod_card defHU) -(sdprod_card defT) divnMl // divgI.
  rewrite -indexgI; have ->: a = #|U : 'C_U(H1 :^ w | 'Q)|.
    have [w1 nH0w1 W1w1 ->] := morphimP W1w; rewrite astabQ centJ morphpreJ //.
    by rewrite -astabQ indexgI -(normsP nUW1 _ W1w1) indexJg -indexgI.
  apply/indexgS/subsetP=> x /= /setIP[Ux /setIdP[_ /eqP tx_t]].
  rewrite astabQ 2!inE Ux (subsetP nH0HU) ?(subsetP sUHU) //= inE.
  apply/centP=> z H1z; have H1xz: (z ^ inMb x)%g \in H1 :^ w.
    rewrite memJ_norm // normJ mem_conjg (subsetP nH1U) // -mem_conjg.
    by rewrite (normsP (quotient_norms H0 nUW1)) ?mem_quotient.
  apply/esym/commgP/conjg_fixP/theta_inj; rewrite ?cfResE {H1xz}//.
  have{z H1z} /morphimP[z nH0z Hz ->]: z \in Hbar := subsetP sH1wH z H1z.
  have nH0x : x \in 'N(H0) by rewrite (subsetP nH0HU) ?(subsetP sUHU).
  rewrite -morphJ ?cfQuoE ?memJ_norm ?(subsetP nHU) //.
  by rewrite -{1}tx_t cfConjgEnorm ?(subsetP nHU).
Admitted.
     

End Nine.
