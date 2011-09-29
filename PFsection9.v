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
Let H := M`_\F.
Canonical PFsection9_Hgroup := [group of H].
Let W2 := 'C_H(W1).
Canonical PFsection9_W2group := [group of W2].
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

Let nilH : nilpotent H. Proof. exact: Fcore_nil. Qed.

(* This is Peterfalvi (9.3). *)
Lemma typeII_IV_core (p := #|W2|) :
  if FTtype M == 2 then 'C_H(U) = 1 /\ #|H| = (#|W2| ^ q)%N
  else [/\ prime p, 'C_H(U <*> W1) = 1 & #|H| = (p ^ q * #|'C_H(U)|)%N].
Proof.
have [frobUW1 [_ _ nHUW1 _]] := (Ptype_compl_Frobenius, sdprodP defHUW1).
have solH: solvable H := nilpotent_sol nilH.
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
have [[_ [_ _ nUW1 _] _ _ _] [_ <- nHUW1 _]] := (MtypeP, sdprodP defHUW1).
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
Let solHbar: solvable Hbar. Proof. by rewrite quotient_sol ?nilpotent_sol. Qed.
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
rewrite coprime_quotient_cent ?(subset_trans _ nH0M) ?nilpotent_sol //.
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
  have /joing_sub[sUUW1 sW1UW1] := erefl (U <*> W1).
  rewrite -{2}(setIidPr sW1UW1) -{2}(setIidPr sUUW1) -im_f.
  rewrite /quotient -!(morphim_restrm nH0UW1 (coset_morphism _)) /=.
  apply/Frobenius_semiregularP; rewrite ?morphim_injm_eq1 //.
    exact: injm_sdprod.
  move=> xb /setD1P[ntxb /imsetP[x /setIP[UW1x W1x] def_xb]].
  rewrite def_xb -injm_subcent1 // (Frobenius_reg_ker Ptype_compl_Frobenius).
    exact: morphim1.
  by rewrite !inE W1x andbT -(morph_injm_eq1 inj_f) -?def_xb.
have oHbar: #|Hbar| = (#|W2bar| ^ q)%N.
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
have nUW1: W1 \subset 'N(U) by case: MtypeP=> _ [].
rewrite /typeP_Galois acts_irrQ //= => not_minHbarU.
have [H1 minH1 sH1Hb]: {H1 | minnormal (gval H1) (U / H0) & H1 \subset Hbar}.
  by apply: mingroup_exists; rewrite ntHbar quotient_norms.
exists H1; have [defH1 | ltH1H] := eqVproper sH1Hb.
  by rewrite -defH1 minH1 in not_minHbarU.
have{minH1} [/andP[ntH1 nH1U] minH1] := mingroupP minH1.
have [/= H2 defH1 sH02 sH2H] := inv_quotientS nsH0H sH1Hb.
have nsH02: H0 <| H2 := normalS sH02 sH2H nsH0H.
have actsUH1: [acts U, on H1 | 'Q].
  by rewrite defH1 actsQ // -(quotientSGK nH0U) ?normsG ?quotient_normG -?defH1.
have [nH0H abHbar] := (normal_norm nsH0H, abelem_abelian abelHbar).
have [neqCU _ oHbar] := Ptype_Fcore_factor_facts.
have oW1b: #|W1 / H0| = q.
  rewrite -(card_isog (quotient_isog _ _)) // coprime_TIg //.
  by rewrite (coprimeSg sH0H) // (coprimegS (joing_subr U W1)).
have defHbar: \big[dprod/1]_(w \in W1 / H0) H1 :^ w = Hbar.
  have nHbUW1: U <*> W1 / H0 \subset 'N(Hbar) by exact: quotient_norms.
  pose rUW1 := abelem_repr abelHbar ntHbar nHbUW1.
  have irrUW1: mx_irreducible rUW1.
    apply/abelem_mx_irrP/mingroupP; split=> [|H3]; first by rewrite ntHbar.
    case/andP=> ntH3 nH2UW1 sH3H; case/mingroupP: minHbar => _; apply=> //.
    by rewrite ntH3 -defHUW1 quotientMl // mulG_subG sub_abelian_norm.
  have nsUUW1: U / H0 <| U <*> W1 / H0 by rewrite quotient_normal // normalYl.
  pose rU := subg_repr rUW1 (normal_sub nsUUW1).
  pose V1 := rowg_mx (abelem_rV abelHbar ntHbar @* H1).
  have modV1: mxmodule rU V1.
    rewrite /mxmodule rstabs_subg subsetIidl rstabs_abelem /=.
    by rewrite subsetI normal_sub // rowg_mxK abelem_rV_mK.
  have simV1: mxsimple rU V1.
    split=> // [|V2]; rewrite /mxmodule.
      by rewrite -trivg_rowg rowg_mxK morphim_injm_eq1 ?abelem_rV_injm.
    rewrite rstabs_subg subsetIidl rstabs_abelem subsetI normal_sub //=.
    rewrite -!rowgS -trivg_rowg rowg_mxK -sub_rVabelem_im sub_abelem_rV_im //.
    rewrite -(morphim_injm_eq1 (rVabelem_injm _ _)) ?sub_im_abelem_rV //=.
    by move=> nH3U sH31 ntH3; move/minH1: sH31 => <- //; exact/andP.
  have [W0 sW01 [sumW0 dxW0]] := Clifford_basis irrUW1 simV1.
  have oW0: #|W0| = q.
    have:= eqnP dxW0; rewrite sumW0 mxrank1 /=.
    rewrite {1}(dim_abelemE abelHbar ntHbar) oHbar pfactorK //.
    rewrite (eq_bigr (fun _ => \rank V1)) => [|x W0x]; last first.
      by rewrite mxrankMfree ?row_free_unit ?repr_mx_unit ?(subsetP sW01).
    rewrite sum_nat_const => def_q.
    apply/prime_nt_dvdP=> //; last by rewrite def_q dvdn_mulr.
    apply: contraTneq (proper_card ltH1H) => W0_1.
    rewrite -leqNgt oHbar def_q W0_1 mul1n -{1}(card_Fp p_pr) -card_rowg.
    by rewrite rowg_mxK card_injm ?abelem_rV_injm.
  have defHbar: \big[dprod/1]_(w \in W0) H1 :^ w = Hbar.
    have prodW (W3 : {set _}) :
      W3 \subset U <*> W1 / H0 ->
      (\prod_(w \in W3) H1 :^ w)%G :=:
        rVabelem abelHbar ntHbar @* rowg (\sum_(x \in W3) (V1 *m rUW1 x)%R)%MS.
    - move/subsetP=> sW3UW1; elim/big_rec2: _ => [|w V3 _ /sW3UW1 Ww /= ->].
        by rewrite rowg0 morphim1.
      rewrite (cent_joinEr (sub_abelian_cent2 abHbar _ _)); first 1 last.
      + exact: sub_rVabelem.
      + by rewrite sub_conjg (normP _) ?groupV ?(subsetP nHbUW1).
      rewrite rowgD morphimMl ?sub_im_abelem_rV //= abelem_rowgJ //.
      by rewrite rowg_mxK abelem_rV_mK.
    have defHbar: (\prod_(w \in W0) H1 :^ w)%G :=: Hbar.
      by rewrite prodW // (eq_rowg sumW0) rowg1 im_rVabelem.
    rewrite -defHbar; apply/eqP/bigdprodYP=> w Ww; apply/dprodYP.
    rewrite (bigD1 w) //= in defHbar; have [sHwH sHw'H] := joing_sub defHbar.
    rewrite dprodEY ?(sub_abelian_cent2 abHbar) //; apply/eqP.
    rewrite -(morphim_injm_eq1 (abelem_rV_injm abelHbar ntHbar)); last first.
      rewrite subIset // sub_conjg (normP _) ?sH1Hb // groupV.
      by rewrite (subsetP nHbUW1) ?(subsetP sW01).
    rewrite injmI ?abelem_rV_injm ?(rV_abelem_sJ _ _ nHbUW1) ?(subsetP sW01) //.
    rewrite -/rUW1 -/V1 -[_ @* _]rowg_mxK -rowgI trivg_rowg /=.
    rewrite -(eq_bigl _ _ (in_set _)).
    rewrite prodW; last by rewrite setIdE subIset ?sW01.
    rewrite (eq_bigl _ _ (in_set _)) rVabelem_mK.
    rewrite -mxrank_eq0 (cap_eqmx (eqmx_refl _) (rowgK _)).
    rewrite (mxdirect_sumsP dxW0) ?mxrank0 //.
  rewrite -defHbar -big_filter -[rhs in _ = rhs]big_filter !filter_index_enum.
  rewrite -!(big_map (fun w => H1 :^ w) xpredT id) !mem_mem.
  apply: eq_big_perm; set s1 := map _ _; set s0 := map _ _.
  have ss01: {subset s0 <= s1}.
    move=> _ /imageP[w /(subsetP sW01)/= Ww ->].
    move: Ww; rewrite norm_joinEr // quotientMl // => /mulsgP[x w1 Ux Ww1 ->].
    by rewrite conjsgM (normsP nH1U) // mem_image.
  have Us0: uniq s0.
    apply/dinjectiveP=> x y Wx Wy eq_Hxy; apply: contraNeq ntH1 => neq_xy.
    rewrite -(conjsg_eq1 _ x) -[H1 :^ x]setIid {1}eq_Hxy; apply/eqP.
    rewrite (bigD1 y) // (bigD1 x) /= ?Wx // dprodA in defHbar.
    by case/dprodP: defHbar => [[_ _ /dprodP[_ _ _ ->] _]].
  have [|eq_s12 eq_size12] := leq_size_perm Us0 ss01.
    by rewrite !size_image oW1b oW0.
  by rewrite perm_eq_sym uniq_perm_eq // -(perm_uniq eq_s12).
have oH1: #|H1| = p.
  apply: (expIn (prime_gt0 pr_q)); rewrite -oHbar -(bigdprod_card defHbar).
  by rewrite (eq_bigr _ (fun _ _ => cardJg _ _)) prod_nat_const oW1b.
split=> //; set a := #|_ : _|.
have /cyclicP[h genH1]: cyclic H1 by rewrite prime_cyclic ?oH1.
have inj_Zp_h w := injm_Zp_unitm (h ^ w).
pose ucast eqm zu := eq_rect _ (fun m => {unit 'Z_m}) zu _ eqm.
pose phi w := invm (inj_Zp_h w) \o restr_perm <[h ^ w]> \o actperm 'Q.
have dU w: w \in W1 / H0 -> U \subset 'dom (phi w).
  case/morphimP=> w1 Nw1 Ww1 def_w.
  rewrite -sub_morphim_pre; last by rewrite /= qact_domE ?subsetT // astabsJ.
  apply/subsetP=> _ /morphimP[u1 Nu1 Uu1 ->].
  have:= Nu1; rewrite /= {1}qact_domE ?subsetT // astabsJ => nH0u1.
  rewrite /= im_Zp_unitm; apply/morphpreP; split.
    apply/astabsP=> H0z; have [z Nz def_z] := cosetP H0z.
    rewrite def_z /= /aperm actpermE /= qactE // morphJ //= -def_z.
    rewrite cycleJ -genH1 -mem_conjgV (normP _) // groupV /= normJ mem_conjg.
    rewrite (subsetP nH1U) // def_w -morphV // -morphJ ?groupV //.
    rewrite mem_morphim //; first by rewrite groupJ ?groupV.
    by rewrite -mem_conjg (normsP nUW1).
  apply: Aut_restr_perm (subsetT _) _ _; apply/setIdP; split.
    by apply/subsetP=> ? _; rewrite inE.
  apply/morphicP=> H0z1 H0z2 _ _.
  have [[z1 Nz1 ->] [z2 Nz2 ->]] := (cosetP H0z1, cosetP H0z2).
  by rewrite !actpermE /= -morphM // !qactE ?groupM //= conjMg morphM ?groupJ.
have Mphi w hw x:
    w \in W1 / H0 -> hw \in <[h ^ w]> -> x \in U ->
  hw ^ coset H0 x = hw ^+ val (phi w x).
- move=> Ww Hhw Ux.
  have /morphpreP[Qx /morphpreP[Nx Dx]] := subsetP (dU _ Ww) x Ux.
  transitivity (Zp_unitm (phi w x) hw); last by rewrite autE.
  rewrite invmK // restr_permE // actpermE /=.
  by have [zw Nzw ->] := cosetP hw; rewrite qactE // morphJ // (subsetP nH0U).
have Kphi w: w \in W1 / H0 -> 'ker_U (phi w) = 'C_U(H1 :^ w | 'Q).
  move=> Ww; rewrite genH1 -cycleJ; apply/setP=> x; rewrite 2!in_setI.
  apply/andb_id2l=> Ux.
  have /morphpreP[Qx /morphpreP[Nx Dx]] := subsetP (dU _ Ww) x Ux.
  rewrite astabQ inE (subsetP (dU w Ww)) // cent_cycle 3!inE (subsetP nH0U) //=.
  rewrite inE cent1C (sameP cent1P commgP) (sameP conjg_fixP eqP).
  rewrite (Mphi w) ?cycle_id // (eq_expg_mod_order _ _ 1).
  have hw_gt1: #[h ^ w] > 1 by rewrite orderJ orderE -genH1 oH1 prime_gt1.
  by rewrite -!val_Zp_nat // natr_Zp.
have o_phi w: w \in W1 / H0 -> #|phi w @* U| = a.
  move=> Ww; have [z Nz W1z def_w] := morphimP Ww.
  rewrite card_morphim (setIidPr (dU w Ww)) -indexgI Kphi // /a !astabQ centJ.
  by rewrite def_w morphpreJ // -{1 2}(normsP nUW1 z W1z) -conjIg indexJg.
have cycZu w: cyclic (units_Zp #[h ^ w]).
  rewrite -(injm_cyclic (inj_Zp_h w)) // im_Zp_unitm /= cycleJ -genH1.
  by rewrite Aut_prime_cyclic ?cardJg ?oH1.  
have /cyclicP[zu def_zu]: cyclic (phi 1 @* U) := cyclicS (subsetT _) (cycZu 1).
pose phi_cast w := ucast _ _ (etrans (orderJ h w) (esym (orderJ h 1))).
have Uphi w x: w \in W1 / H0 -> x \in U -> phi_cast w (phi w x) \in <[zu]>%G.
  move=> Ww Ux; have: #|<[zu]>%G| = a by rewrite /= -def_zu o_phi ?group1.
  rewrite /phi_cast; case: _ / (etrans _ _) <[zu]>%G => A oA /=.
  suffices /eqP->: A :==: phi w @* U by rewrite mem_morphim ?(subsetP (dU w _)).
  by rewrite (eq_subG_cyclic (cycZu w)) ?subsetT // oA o_phi.
have a_gt1: a > 1.
  rewrite indexg_gt1 subsetIidl /= astabQ -sub_quotient_pre //. 
  apply: contra neqCU => cH1U; rewrite (sameP eqP setIidPl) astabQ.
  rewrite -sub_quotient_pre // -(bigdprodEY defHbar) cent_gen centsC.
  apply/bigcupsP=> w Ww; rewrite centsC centJ.
  by rewrite -[U / H0](normsP _ w Ww) ?conjSg ?quotient_norms //.
split=> //.
  rewrite -(o_phi 1) ?group1 // (dvdn_trans (cardSg (subsetT _))) // conjg1.
  by rewrite subn1 card_units_Zp // orderE -genH1 oH1 (@phi_pfactor p 1) ?muln1.
have psi_cast: q.-1 = #|(W1 / H0)^#| by rewrite -oW1b (cardsD1 1) ?group1.
have psi0_cast: #[zu] = a by rewrite orderE -def_zu o_phi ?group1.
pose ocast eqm i := eq_rect _ (fun m => 'Z_m) i _ eqm.
pose psi0 w x := ocast _ _ psi0_cast (invm (injm_Zpm _) (phi_cast w (phi w x))).
pose psi x := (\row_(i < q.-1) let w := enum_val (cast_ord psi_cast i) in
              (psi0 w x * (psi0 1 x)^-1)%g)%R.
have psiM: {in U &, {morph psi: x y / x * y}}.
  have psi0M w: w \in W1 / H0 -> {in U &, {morph psi0 w: x y / x * y}}.
    move=> Ww x y Ux Uy; rewrite /psi0; case: (a) / (psi0_cast) => /=.
    rewrite -morphM; first 1 [congr (invm _ _)] || by rewrite im_Zpm Uphi.
    rewrite /phi_cast; case: _ / (etrans _ _) => /=.
    by rewrite -morphM ?(subsetP (dU _ _)).
  move=> x y Ux Uy; apply/rowP=> i; rewrite !{1}mxE; move: (cast_ord _ i) => iw.
  have /setD1P[_ Ww] := enum_valP iw.
  by rewrite /= !{1}psi0M ?group1 // addrCA -addrA -oppr_add addrCA addrA.
suffices Kpsi: 'ker (Morphism psiM) = C.
  by exists [group of Morphism psiM @* U]; rewrite /Ubar -Kpsi first_isog.
apply/setP=> x; rewrite 2!in_setI astabQ 3!inE; apply/esym/andb_id2l=> Ux.
have val_phi_cast w px: val (phi_cast w px) = val px :> nat.
  by rewrite /phi_cast; case: _ / (etrans _ _).
rewrite (subsetP nH0U) //= inE; apply/idP/eqP=> [cHx | /rowP psix0].
  suffices psi0x1 w: w \in W1 / H0 -> psi0 w x = 1.
    apply/rowP=> i; rewrite !mxE; move: {i}(cast_ord _ i) => i.
    by have /setD1P[_ Ww] := enum_valP i; rewrite /= !psi0x1 ?group1 // mulgV.
  move=> Ww; apply: val_inj; rewrite /psi0; case: (a) / (psi0_cast).
  rewrite -(morph1 (invm_morphism (injm_Zpm zu))); congr val; congr (invm _ _).
  do 2!apply: val_inj; rewrite /= val_phi_cast -modZp conjg1 -(orderJ h w).
  rewrite [m in _ = _ %[mod m]]Zp_cast; last first.
    by rewrite orderJ orderE -genH1 oH1 prime_gt1.
  apply/eqP; rewrite -eq_expg_mod_order -Mphi ?cycle_id //.
  rewrite conjgE -(centP cHx) ?mulKg // memJ_norm.
    by rewrite -cycle_subG -genH1.
  by rewrite (subsetP (quotient_norms _ nHW1)).
pose k : nat := val (phi 1 x).
have id_phi w: w \in W1 / H0 -> val (phi w x) = k :> nat.
  move=> Ww; apply/eqP. have [-> // | ntw] := eqVneq w 1.
  have W'w: w \in (W1 / H0)^# by exact/setD1P.
  have /eqP := psix0 (cast_ord (esym psi_cast) (enum_rank_in W'w w)).
  rewrite 2!mxE cast_ordKV enum_rankK_in // -eq_mulgV1 -val_eqE.
  rewrite /psi0; case: (a) / (psi0_cast); rewrite /= val_eqE.
  rewrite (inj_in_eq (injmP _ (injm_invm _))) /= ?im_Zpm ?Uphi ?group1 //.
  by rewrite -2!val_eqE /= !val_phi_cast.
suffices: x \in C by rewrite inE astabQ inE (subsetP nH0U) Ux //= inE.
have nCx: x \in 'N(C).
  apply: subsetP Ux; rewrite normsI ?normG //=.
  by apply: subset_trans (astab_norm _ _); rewrite actsQ //.
have frobUW1: [Frobenius (U <*> W1 / C) = (U / C) ><| (W1 / C)].
  have solU: solvable U by apply: nilpotent_sol; case: MtypeP => _ [].
  apply: (Frobenius_quotient Ptype_compl_Frobenius solU); last first.
    by rewrite proper_subn // properEneq subsetIl neqCU.
  rewrite /normal subIset ?joing_subl //= astabQ.
  apply: normsI; first by rewrite join_subG normG.
  apply: subset_trans (morphpre_norm _ _).
  by rewrite join_subG -!sub_quotient_pre // !norms_cent ?quotient_norms.
have [_ _ /trivgPn[wc Wwc ntwc] _ _] := Frobenius_context frobUW1.
rewrite -groupV coset_idr ?groupV //; apply/set1P; rewrite -set1gE.
rewrite -((Frobenius_reg_ker frobUW1) wc); last exact/setD1P.
rewrite inE /= -/C mem_quotient ?groupV //= (sameP cent1P commgP).
have{Wwc} [w1 Nw1 Ww1 {wc ntwc}->] := morphimP Wwc; rewrite -morphR ?groupV //=.
rewrite coset_id // inE groupMl ?memJ_norm ?groupV ?(subsetP nUW1) // Ux.
have [nH0x' nH0w1] := (subsetP nH0U _ (groupVr Ux), subsetP nH0W1 w1 Ww1).
rewrite astabQ inE groupR //= inE morphR //=; set w := coset H0 w1.
have Ww: w \in W1 / H0 by rewrite mem_quotient.
rewrite -sub_cent1 -(bigdprodEY defHbar) gen_subG.
apply/bigcupsP=> w2 Ww2; rewrite genH1 -cycleJ cycle_subG cent1C inE.
rewrite sub_conjg invg_comm conjg_set1 !conjgM morphV -1?groupV //= invgK.
rewrite -(conjgM h) (Mphi (w2 * w^-1) (h ^ _)) ?cycle_id ?groupM ?groupV //.
rewrite conjXg -(conjgM h) mulgKV id_phi ?groupM ?groupV //.
by rewrite -(id_phi w2) // -Mphi ?cycle_id ?conjgK.
Qed.

(* To check: direct proof, avoiding the detour through Clifford's theorem.
  Impractical for now, due to incomplete theory of iterated direct products
  of groups, but should be compared in the final version.
pose H3 := (\prod_(w \in W1 / H0) H1 :^ w)%G.
have [nH0H abHbar] := (normal_norm nsH0H, abelem_abelian abelHbar).
have defH3: H3 :=: Hbar.
  have sH13: H1 \subset H3.
    by rewrite /H3 (bigD1 1) ?group1 //= conjsg1 joing_subl.
  case/mingroupP: minHbar => _; apply.
    rewrite (subG1_contra sH13 ntH1) /= bigprodGE norms_gen //.
    rewrite -defHUW1 quotientMl ?quotientY //= mulG_subG join_subG /=.
    rewrite -{3}class_supportEr class_support_norm andbT -join_subG.
    rewrite norms_bigcup //; apply/bigcapsP=> w W1w.
    rewrite normJ -sub_conjgV (normsP _ _ (groupVr W1w)).
      by rewrite join_subG sub_abelian_norm.
    by rewrite normsY ?quotient_norms //; case: MtypeP => _ [].
  rewrite bigprodGE -class_supportEr gen_subG /=.
  by rewrite class_support_sub_norm ?quotient_norms.
have {H3 defH3} defHbar: \big[dprod/1]_(w \in W1 / H0) H1 :^ w = Hbar.
  rewrite -defH3; apply/eqP/bigdprodYP=> w W1w.
  rewrite [H3](bigD1 w) //= in defH3; have [sHwH sHw'H] := joing_sub defH3.
  set Hw' := (\prod_(j \in _ | _) _)%G in sHwH sHw'H defH3 *.
  have cHww': Hw' \subset 'C(H1 :^ w) := sub_abelian_cent2 abHbar sHw'H sHwH.
  rewrite subsetD cHww' //= -setI_eq0 setDE setIA -setDE setD_eq0 subG1.
*)

End Nine.
