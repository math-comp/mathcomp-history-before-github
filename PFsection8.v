(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup sylow abelian frobenius.
Require Import matrix mxalgebra mxrepresentation vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 (* PFsection3 *) PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 8: Structure of a Minimal Simple      *)
(* Group of Odd Order. Actually, most Section 8 definitions can be found in   *)
(* BGsection16, which holds the conclusions of the Local Analysis part of the *)
(* proof, as the B & G text has been adapted to fit the usage in Section 8.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Eight.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L M N P Q R S T U V W : {group gT}.

(* Peterfalvi, Definition (8.1) is covered by BGsection16.of_typeF. *)

(* This is Peterfalvi (8.2). *)
Lemma typeF_context M U (H := M`_\F) :
  of_typeF M U ->
  [/\ (*a*) exists2 U0 : {group gT}, U0 \subset U /\ #|U0| = exponent U
                & [Frobenius H <*> U0 = H ><| U0],
      (*b*) [Frobenius M = H ><| U] = Zgroup U
    & (*c*) exists2 U1 : {group gT}, U1 <| U /\ abelian U1
                & forall i : Iirr H, i != 0 -> 'I_U['chi_i] \subset U1].
Proof.
case; rewrite -/H => [[ntH ntM defM] exU1 [U0 [sU0U expU0] frobHU0]].
have exponent_Zgroup K: Zgroup K -> exponent K = #|K|.
  move/forall_inP=> ZgK; apply/eqP; rewrite eqn_dvd exponent_dvdn.
  apply/(dvdn_partP _ (cardG_gt0 _)) => p _.
  have [S sylS] := Sylow_exists p K; rewrite -(card_Hall sylS).
  have /cyclicP[x defS]: cyclic S by rewrite ZgK ?(p_Sylow sylS).
  by rewrite defS dvdn_exponent // -cycle_subG -defS (pHall_sub sylS).
have [nsHM sUG mulHU nHU _] := sdprod_context defM.
have oU0: #|U0| = exponent U.
  rewrite -expU0 exponent_Zgroup //.
  apply/forall_inP=> S /SylowP[p _ /and3P[sSU0 pS _]].
  apply: odd_regular_pgroup_cyclic pS (mFT_odd S) ntH _ _.
    by rewrite (subset_trans (subset_trans sSU0 sU0U)).
  move=> x /setD1P[ntx /(subsetP sSU0) U0x].
  by rewrite (Frobenius_reg_ker frobHU0) // !inE ntx.
split; first by exists U0.
  apply/idP/idP=> [frobU | ZgU].
    apply/forall_inP=> S /SylowP[p _ /and3P[sSU pS _]].
    apply: odd_regular_pgroup_cyclic pS (mFT_odd S) ntH _ _.
      by rewrite (subset_trans sSU).
    move=> x /setD1P[ntx /(subsetP sSU) Ux].
    by rewrite (Frobenius_reg_ker frobU) // !inE ntx.
  suffices defU0: U0 :=: U by rewrite defU0 norm_joinEr ?mulHU // in frobHU0.
  by apply/eqP; rewrite eqEcard sU0U /= oU0 exponent_Zgroup.
have itoP: is_action M (fun (j : Iirr H) x => conjg_Iirr j x).
  split=> [x | j x y Mx My].
    apply: can_inj (fun j => conjg_Iirr j x^-1) _ => j.
    by apply: chi_inj; rewrite !conjg_IirrE cfConjgK.
  by apply: chi_inj; rewrite !conjg_IirrE (cfConjgM _ nsHM).
pose ito := Action itoP; pose cto := ('Js \ subsetT M)%act.
have actsMcH: [acts M, on classes H | cto].
  apply/subsetP=> x Mx; rewrite !inE Mx; apply/subsetP=> _ /imsetP[y Hy ->].
  have nHx: x \in 'N(H) by rewrite (subsetP (gFnorm _ _)).
  rewrite !inE /= -class_rcoset norm_rlcoset // class_lcoset mem_classes //.
  by rewrite memJ_norm.
have{exU1} [U1 [nsU1U abU1] s_cUH_U1] := exU1; exists U1 => // i nz_i.
apply/subsetP=> g /setIdP[/setIP[Ug nHg] c_i_g]; have Mg := subsetP sUG g Ug.
apply: contraR nz_i => notU1g; rewrite (sameP eqP set1P).
suffices <-: 'Fix_ito[g] = [set (0 : Iirr H)].
  by rewrite !inE sub1set inE -(inj_eq (@chi_inj _ _)) conjg_IirrE.
apply/eqP; rewrite eq_sym eqEcard cards1 !(inE, sub1set) /=.
rewrite -(inj_eq (@chi_inj _ _)) conjg_IirrE chi0_1 cfConjg_cfun1 eqxx.
rewrite (card_afix_irr_classes Mg actsMcH) => [|j y z Hy /=]; last first.
  case/imsetP=> _ /imsetP[t Ht ->] -> {z}.
  by rewrite conjg_IirrE cfConjgE // conjgK cfunJ.
rewrite -(cards1 [1 gT]) subset_leq_card //= -/H.
apply/subsetP=> _ /setIP[/imsetP[a Ha ->] /afix1P/= c_aH_g].
have /imsetP[x Hx c_a_xg]: a ^ g^-1 \in a ^: H.
  by rewrite -mem_conjg c_aH_g class_refl.
have coHg: coprime #|H| #[g].
  apply: (coprime_dvdr (order_dvdG Ug)).
  by rewrite (coprime_sdprod_Hall defM) (pHall_Hall (Fcore_Hall M)).
have /and3P[/eqP defHg _ _]: partition (('C_H[g] :* g) :^: H) (H :* g).
  by case/partition_cent_rcoset: nHg.
have: (x * g)%g \in H :* g by rewrite mem_rcoset mulgK.
rewrite -{}defHg cover_imset => /bigcupP[y Hy].
case/imsetP=> _ /rcosetP[z /setIP[Hz cgz] ->] def_xg.
rewrite inE classG_eq1 -(can_eq (conjgKV y)) conj1g.
apply: contraR notU1g => nt_ay'; apply: (subsetP (s_cUH_U1 (a ^ y^-1) _)).
  by rewrite !inE nt_ay' groupJ ?groupV.
rewrite inE Ug; have ->: g = (z * g).`_(\pi(H)^').
  rewrite consttM; last exact/cent1P.
  rewrite (constt1P _) ?mul1g ?constt_p_elt //.
    by rewrite /p_elt -coprime_pi' ?cardG_gt0.
  by rewrite (mem_p_elt _ Hz) // pgroupNK pgroup_pi.
rewrite groupX //; rewrite cent1C; apply/cent1P/commgP/conjg_fixP.
by rewrite -conjgM conjgCV invgK -def_xg -mulgA !conjgM -c_a_xg conjgKV.
Qed.

End Eight.
