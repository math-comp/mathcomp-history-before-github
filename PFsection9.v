(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic commutator nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8.

(******************************************************************************)
(* This file covers Peterfalvi, Section 9: Structure of a Minimal Simple      *)
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

Lemma Ptype_Frobenius_compl : [Frobenius U <*> W1 = U ><| W1].
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
have [frobUW1 [_ _ nHUW1 _]] := (Ptype_Frobenius_compl, sdprodP defHUW1).
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
Let p := pdiv #|W2|.
Let p_pr : prime p. Proof. by rewrite pdiv_prime // cardG_gt1. Qed.

Definition Ptype_Fcore_kernel :=
  locked [group of 'Phi('O_p(H)) <*> 'O_p^'(H) <*> 'C_H(U)].
Local Notation H0 := Ptype_Fcore_kernel.
Local Notation Hbar := (H / H0).

(* This is Peterfalvi (9.4), preamble and part (a). *)
Lemma Ptype_Fcore_kernel_facts :
  [/\ H0 <| M, H0 \subset H, p.-abelem Hbar & H0 \proper H].
Proof.
have /dprodP[_ defH cHpp' tiHpp'] := nilpotent_pcoreC p nilH.
have nsHpiM := char_normal_trans (pcore_char _ _) (Fcore_normal M).
have nsPhiHpM := char_normal_trans (Phi_char _) (nsHpiM p).
pose H1 := [group of 'Phi('O_p(H)) <*> 'O_p^'(H)].
have nsH1M: H1 <| M by rewrite normalY ?nsHpiM.
have sH1H: H1 \subset H.
  by rewrite join_subG (subset_trans (Phi_sub _)) ?pcore_sub.
have nH1H: H \subset 'N(H1) := subset_trans (Fcore_sub _) (normal_norm nsH1M).
have nPhiHp': 'O_p^'(H) \subset 'N('Phi('O_p(H))).
  apply: subset_trans (pcore_sub _ _) (normal_norm _).
  exact: char_normal_trans (Phi_char _) (pcore_normal _ _).     
have abelHb: p.-abelem (H / H1).
  rewrite -defH -(mulGSid (Phi_sub 'O_p(_))) /= -mulgA.
  rewrite -(norm_joinEr nPhiHp') //= quotientMidr.
  have isoHp := second_isog (subset_trans (pcore_sub p _) nH1H).
  rewrite -(isog_abelem isoHp) /= norm_joinEr //= -group_modl ?Phi_sub //.
  by rewrite setIC tiHpp' mulg1 Phi_quotient_abelem ?pcore_pgroup.
have sH'H1: H^`(1) \subset H1 by rewrite der1_min // (abelem_abelian abelHb).
have sH0H: H0 \subset H by unlock H0; rewrite join_subG sH1H subsetIl.
have sH10: H1 \subset H0 by unlock H0; exact: joing_subl.
have nH0H: H \subset 'N(H0) by rewrite sub_der1_norm ?(subset_trans _ sH10).
have nsH0M: H0 <| M.
  rewrite /normal (subset_trans sH0H) ?Fcore_sub //=.
  have [_ sUW1M defM nHUW1 _] := sdprod_context defHUW1.
  rewrite -defM mulG_subG nH0H /=; unlock H0.
  rewrite normsY ?(subset_trans _ (normal_norm nsH1M)) //.
  rewrite normsI ?(subset_trans _ (gFnorm _ _)) // join_subG.
  by rewrite cents_norm 1?centsC ?norms_cent //; have [_ []] := MtypeP.
split=> //.
  by have /homgP[f <-] := homg_quotientS nH1H nH0H sH10; exact: morphim_abelem.
rewrite properEcard sH0H /=.
unlock H0; rewrite /= -{3 4}defH /= -subcent_TImulg ?TIpcoreC //; first last.
  have nHU: U \subset 'N(H) by have [_ [_ _ _ /sdprodP[]]] := MtypeP.
  by rewrite subsetI !(char_norm_trans (pcore_char _ _)).
rewrite -(cent_joinEr (centSS _ _ cHpp')) ?subsetIl //.
rewrite -joingA [D in _ <*> D]joingC -joingA (joing_idPr (subsetIl _ _)) joingA.
rewrite (cent_joinEr (centSS _ _ cHpp')) //=; last first.
  by rewrite join_subG Phi_sub subsetIl.
rewrite !TI_cardMg ?ltn_pmul2r //; last first.
  by apply/trivgP; rewrite -tiHpp' setSI ?join_subG ?Phi_sub ?subsetIl.
rewrite proper_card // properEneq join_subG Phi_sub subsetIl /= andbT.
apply/eqP=> /Phi_nongen; rewrite genGid => /setIidPl cUHp.
have sylHp: p.-Sylow(H) 'O_p(H) := nilpotent_pcore_Hall p nilH.
have sylHPC: p.-Sylow('C_H(U)) 'O_p(H).
  by apply: pHall_subl (subsetIl _ _) sylHp; rewrite subsetI pcore_sub.
have:= typeII_IV_core => /=; case: ifP => [_ [C1 _] | _ [W2pr _ oH]].
  case/pHall_sub/idPn: sylHPC; rewrite C1 subG1 -rank_gt0 (rank_Sylow sylHp) /=.
  rewrite p_rank_gt0 (piSg (subsetIl _ 'C(W1))) //= -/W2.
  by rewrite mem_primes p_pr cardG_gt0 pdiv_dvd.
case/negP: not_cHU; rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl /=.
rewrite -[#|H|](partnC p) // {2}oH partn_mul // ?expn_gt0 ?prime_gt0 //.
rewrite -(card_Hall sylHp) (card_Hall sylHPC) mulnCA.
rewrite part_p'nat; last by rewrite pnatNK pnat_exp /p pdiv_id // pnat_id.
by rewrite mul1n partnC.
Qed.
   
(* The first assertion of (9.4)(b). *)
Lemma typeIII_IV_core_prime : FTtype M != 2 -> p = #|W2|.
Proof. by have:= typeII_IV_core => /=; case: ifP => // _ [/pdiv_id]. Qed.

Let sH0H : H0 \subset H. Proof. by case: Ptype_Fcore_kernel_facts. Qed.
Let nsH0M : H0 <| M. Proof. by case: Ptype_Fcore_kernel_facts. Qed.
Let abelHbar : p.-abelem Hbar. Proof. by case: Ptype_Fcore_kernel_facts. Qed.
Let nsH0S : H0 <| H. Proof. exact: normalS sH0H (Fcore_sub _) nsH0M. Qed.
Let ltH0H : H0 \proper H. Proof. by case: Ptype_Fcore_kernel_facts. Qed.
Let ntHbar : Hbar != 1.
Proof. by rewrite -subG1 quotient_sub1 ?normal_norm ?proper_subn. Qed.

Let C := 'C_U(Hbar | 'Q).
Let Ubar := U / C.

Let c := #|C|.
Let u := #|Ubar|.

Let W2bar := 'C_Hbar(U / H0).

End Nine.

