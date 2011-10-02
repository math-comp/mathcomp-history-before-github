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
Import Prenex Implicits.

Import GroupScope GRing.Theory.

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
Let calX := Iirr_kerD [the {group _} of H] H 1.
Let calS := seqIndD [the {group _} of H] M [the {group _} of H] 1.
Let X_ Y := Iirr_kerD [the {group _} of H] H Y.
Let S_ Y := seqIndD [the {group _} of H] M [the {group _} of H] Y.

Let defW2bar : W2bar = W2 / H0.
Proof.
rewrite coprime_quotient_cent ?(subset_trans _ nH0M) //.
  by have [_ /joing_subP[]] := sdprod_context defHUW1.
exact: coprimegS (joing_subr _ _) coHUW1.
Qed.

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

(* The first assertion of (9.4)(b). *)
Lemma typeIII_IV_core_prime : FTtype M != 2 -> p = #|W2|.
Proof.
by have:= typeII_IV_core => /=; case: ifP => // _ [/def_Ptype_factor_prime].
Qed.

Definition typeP_Galois := acts_irreducibly U Hbar 'Q.

(* This is Peterfalvi (9.7)(a). *)
Lemma typeP_Galois_Pn :
    ~~ typeP_Galois ->
  {H1 : {group coset_of H0} |
    [/\ #|H1| = p, U / H0 \subset 'N(H1), [acts U, on H1 | 'Q],
        \big[dprod/1]_(w \in W1 / H0) H1 :^ w = Hbar
      & let a := #|U : 'C_U(H1 | 'Q)| in
        [/\ a > 1, a %| p - 1
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
  have [/= H2 defH1 sH02 sH2H] := inv_quotientS nsH0H sH1Hb.
  have nsH02: H0 <| H2 := normalS sH02 sH2H nsH0H.
  by rewrite defH1 actsQ // -(quotientSGK nH0U) ?normsG ?quotient_normG -?defH1.
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
  have [[z1 Nz1 def_z] nH0x] := (cosetP z, subsetP nH0U x Ux).
  rewrite def_z /= qactE ?morphJ //= -def_z memJ_norm // normJ mem_conjg.
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
split=> //.
  rewrite -(o_phiU 1) // (dvdn_trans (cardSg (subsetT _))) // card_units_Zp //.
  by rewrite subn1 conjg1 o_h (@phi_pfactor p 1) ?muln1.
have cycZhw w: cyclic (units_Zp #[h ^ w]).
  rewrite -(injm_cyclic (inj_Zp_h w)) // im_Zp_unitm Aut_prime_cyclic //=.
  by rewrite -orderE orderJ o_h.
have /cyclicP[z def_z]: cyclic (phi 1 @* U) := cyclicS (subsetT _) (cycZhw 1).
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
  by rewrite !{1}mxE !{1}phi0M // addrCA -addrA -oppr_add addrCA addrA.
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
rewrite -quotient_sub1; last first.
  by rewrite subIset // normsI // (subset_trans _ (astab_norm _ _)) ?actsQ.
have solU: solvable U by rewrite nilpotent_sol; case: MtypeP => _ [].
have [coUW1 regUW1]:= (Frobenius_coprime frobUW1, Frobenius_trivg_cent frobUW1).
rewrite -quotient1 -regUW1 coprime_quotient_cent ?subsetIl //=; last first.
  by rewrite normsI // astabQ norm_quotient_pre // norms_cent ?quotient_norms.
rewrite subsetI quotientS //= quotient_cents2r // subsetI.
rewrite (subset_trans (commSg W1 sKU)) ?commg_subl //= astabQ gen_subG /=.
apply/subsetP=> _ /imset2P[x w1 Kx Ww1 ->].
have:= Kx; rewrite -groupV 2!inE groupV => /andP[Ux /set1P/rowP psi_x'0].
have [nHOx Ux'] := (subsetP nH0U x Ux, groupVr Ux); pose x'b := (coset H0 x)^-1.
rewrite mem_morphpre ?groupR ?morphR //= ?(subsetP nH0W1) //.
have conj_x'b w: w \in W1 / H0 -> (h ^ w) ^ x'b = (h ^ w) ^+ val (phi 1 x^-1).
  move=> Ww; transitivity (Zp_unitm (phi w x^-1) (h ^ w)).
    have /morphpreP[Qx' /morphpreP[Px' Rx']] := dU w Ww x^-1 Ux'.
    rewrite invmK ?restr_permE ?cycle_id //; have [hw Nhw ->] := cosetP (h ^ w).
    by rewrite actpermE /= qactE // morphJ ?groupV ?morphV.
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

End Nine.
