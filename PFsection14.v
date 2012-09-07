(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime binomial ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct center cyclic commutator gseries nilpotent.
Require Import pgroup sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7.
Require Import BGsection14 BGsection15 BGsection16 BGappendixC.
Require Import ssrnum rat algC cyclotomic algnum.
Require Import classfun character integral_char inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection7 PFsection8 PFsection9.
Require Import PFsection10 PFsection11 PFsection12 PFsection13.

(******************************************************************************)
(* This file covers Peterfalvi, Section 14: Non_existence of G.               *)
(* It completes the proof of the Odd Order theorem.                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.

Section Fourteen.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Local Notation "#1" := (inord 1) (at level 0).

Variables S T U V W W1 W2 : {group gT}.
Hypotheses (defW : W1 \x W2 = W) (defW21 : W2 \x W1 = W).
Hypotheses (pairST : typeP_pair S T defW) (maxS : S \in 'M) (maxT : T \in 'M).
Hypotheses (StypeP : of_typeP S U defW) (TtypeP : of_typeP T V defW21).

Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation "` 'W2'" := (gval W2) (at level 0, only parsing) : group_scope.
Local Notation "` 'W'" := (gval W) (at level 0, only parsing) : group_scope.
Local Notation What := (cyclicTIset defW).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation "` 'PU'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'U'" := (gval U) (at level 0, only parsing) : group_scope.

Local Notation "` 'T'" := (gval T) (at level 0, only parsing) : group_scope.
Local Notation Q := `T`_\F%G.
Local Notation "` 'Q'" := `T`_\F (at level 0) : group_scope.
Local Notation QV := T^`(1)%G.
Local Notation "` 'QV'" := `S^`(1) (at level 0) : group_scope.
Local Notation "` 'V'" := (gval V) (at level 0, only parsing) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.

Let defT : QV ><| W2 = T. Proof. by have [[]] := TtypeP. Qed.
Let defQV : Q ><| V = QV. Proof. by have [_ []] := TtypeP. Qed.

Let notStype1 : FTtype S != 1%N. Proof. exact: FTtypeP_neq1 StypeP. Qed.
Let notStype5 : FTtype S != 5%N. Proof. exact: FTtype5_exclusion maxS. Qed.

Let pddS := FT_prDade_hypF maxS StypeP.
Let ptiWS : primeTI_hypothesis S PU defW := FT_primeTI_hyp StypeP.
Let ctiWG : cyclicTI_hypothesis G defW := pddS.

Let pddT := FT_prDade_hypF maxT TtypeP.
Let ptiWT : primeTI_hypothesis T QV defW21 := FT_primeTI_hyp TtypeP.

Let ntW1 : W1 :!=: 1. Proof. by have [[]] := StypeP. Qed.
Let ntW2 : W2 :!=: 1. Proof. by have [_ _ _ []] := StypeP. Qed.
Let cycW1 : cyclic W1. Proof. by have [[]] := StypeP. Qed.
Let cycW2 : cyclic W2. Proof. by have [_ _ _ []] := StypeP. Qed.

Let p := #|W2|.
Let q := #|W1|.
Let u := #|U|.
Let v := #|V|.
Let nU := (p ^ q).-1 %/ p.-1.
Let nV := (q ^ p).-1 %/ q.-1.

Let pr_p : prime p. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.
Let pr_q : prime q. Proof. by have [] := FTtypeP_primes maxS StypeP. Qed.

Local Open Scope ring_scope.

(* This is Hypothesis (14.1). *)
Hypothesis ltqp: (q < p)%N.

(* This corresponds to Peterfalvi, Theorem (14.2). *)
(* As we import the conclusion of BGappendixC, which covers Appendix C of the *)
(* Bender and Glauberman text, we can state this theorem negatively. This     *)
(* will avoid having to repeat its statement thoughout the proof : we will    *)
(* simply end each nested set of assumptions (corresponding to (14.3) and     *)
(* (14.10)) with a contradiction.                                             *)

Theorem no_full_FT_Galois_structure :
 ~ [/\ (*a*) exists Fpq : finFieldImage P W2 U,
               [/\ #|P| = (p ^ q)%N, #|U| = nU & coprime nU p.-1]
    & (*b*) [/\ q.-abelem Q, W2 \subset 'N(Q)
              & exists2 y, y \in Q & W2 :^ y \subset 'N(U)]].
Proof.
case=> [[Fpq [oP oU coUp1]] [abelQ nQW2 nU_W2Q]].
have /idPn[] := ltqp; rewrite -leqNgt.
exact: (prime_dim_normed_finField _ _ _ defPU) nU_W2Q.
Qed.

Let qgt2 : (q > 2)%N. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.
Let pgt2 : (p > 2)%N. Proof. by rewrite odd_gt2 ?mFT_odd ?cardG_gt1. Qed.

Let coPUq : coprime #|PU| q.
Proof. by rewrite (coprime_sdprod_Hall_r defS); have [[]] := StypeP. Qed.

Let nirrW1 : #|Iirr W1| = q. Proof. by rewrite card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = p. Proof. by rewrite card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = q. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = p. Proof. by rewrite -nirrW2 card_ord. Qed.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).

Local Notation Imu2 := (primeTI_Iirr ptiWS).
Let mu2_ i j := primeTIirr ptiWS i j.
Let mu_ := primeTIred ptiWS.
Local Notation chi_ j := (primeTIres ptiWS j).

Local Notation Inu2 := (primeTI_Iirr ptiWT).
Let nu2_ i j := primeTIirr ptiWT j i.
Let nu_ := primeTIred ptiWT.

Local Notation tauS := (FT_Dade0 maxS).
Local Notation tauT := (FT_Dade0 maxT).

Let calS0 := seqIndD PU S S`_\s 1.
Let rmR_S := FTtypeP_coh_base maxS StypeP.
Let scohS0 : subcoherent calS0 tauS rmR_S.
Proof. exact: FTtypeP_subcoherent StypeP. Qed.

Let calS := seqIndD PU S P 1.
Let sSS0 : cfConjC_subset calS calS0.
Proof. exact/seqInd_conjC_subset1/Fcore_sub_FTcore. Qed.

Let calT := seqIndD QV T Q 1.

(* Justification for Hypothesis (14.3). *)
Fact FTtypeP_max_typeII : FTtype S == 2.
Proof. by have [[_ ->]] := FTtypeP_facts maxS StypeP. Qed.
Local Notation Stype2 := FTtypeP_max_typeII.

(* These correspond to Peterfalvi, Hypothesis (14.3). *)
Variables (L : {group gT}) (tau1L : {additive 'CF(L) -> 'CF(G)}) (phi : 'CF(L)).
Local Notation "` 'L'" := (gval L) (at level 0, only parsing).
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F%g (at level 0, format "` 'H'") : group_scope.

Hypothesis maxNU_L : L \in 'M('N(U)).

(* Consequences of the above. *)
Hypotheses (maxL : L \in 'M) (sNUL : 'N(U) \subset L).
Hypotheses (frobL : [Frobenius L with kernel H]) (Ltype1 : FTtype L == 1%N).

Let calL := seqIndD H L H 1.
Local Notation tauL := (FT_Dade0 maxL).

Hypothesis cohL : coherent_with calL L^# tauL tau1L.
(* Hypothesis irrL : {subset calL <= irr L}. *)
Hypotheses (Lphi : phi \in calL) (phi1 : phi 1%g = #|L : H|%:R).
(* Let irr_phi : phi \in irr L. Proof. exact: irrL. Qed. *)
Let betaS := FTtypeP_bridge StypeP #1.
Let betaT := FTtypeP_bridge TtypeP #1.
Let betaL := 'Ind[L, H] 1 - phi.

(* This is the first assertion of Peterfalvi (14.4). *)
Let galT : typeP_Galois TtypeP.
Proof.
apply: contraLR ltqp => /(FTtypeP_nonGalois_facts maxT)[].
by rewrite -/p -leqNgt => ->.
Qed.

(* This is the second assertion of Peterfalvi (14.4). *)
Let oV : v = nV.
Proof.
rewrite /v (card_FTtypeP_Galois_compl maxT galT) -/nV.
by rewrite !modn_small ?gtn_eqF // ltnW.
Qed.

(* This is Peterfalvi (14.5). *)
Let defL : exists2 y, y \in Q & H ><| (W1 <*> W2 :^ y) = L.
Proof.
have [_ sUH] := FTtypeII_support_facts maxS StypeP Stype2 pairST maxNU_L.
case=> // defL; have [_ _ /negP[]] := compl_of_typeII maxS StypeP Stype2.
have [_ _ _] := FTtypeI_bridge_facts maxS StypeP Ltype1 cohL Lphi phi1.
case=> [[_ ubH] | [_ /idPn[]]]; last by rewrite -(index_sdprod defL) -ltnNge.
have{ubH sUH} /eqP defH: `H == U.
  rewrite eq_sym eqEcard sUH /= -(prednK (cardG_gt0 U)) -add1n -leq_subLR subn1.
  have [_ _ _ _ /divnK <-] := FTtypeP_bridge_facts maxS StypeP.
  by rewrite -leC_nat natrM -ler_pdivr_mulr ?gt0CG // {1}(index_sdprod defL).
rewrite (subset_trans sNUL) // -(sdprodW defL) -(sdprodW defS) mulSg //.
by rewrite -(sdprodW defPU) defH mulG_subr.
Qed.

(* This is Peterfalvi (14.6). *)
Let galS : typeP_Galois StypeP.
Proof.
apply/idPn=> gal'S; have [q3 oU] := FTtypeP_nonGalois_facts maxS gal'S.
have [H1 [_ _ _ _]] := typeP_Galois_Pn maxS (FTtype5_exclusion maxS) gal'S.
rewrite def_Ptype_factor_prime // Ptype_Fcompl_kernel_trivial // -/p q3 /=.
set a := #|U : _| => [] [a_gt1 a_dv_p1 _ [U1 isoU1]].
have{isoU1} isoU: U \isog U1 := isog_trans (quotient1_isog U) isoU1.
have{a_gt1 a_dv_p1} defU1: U1 :=: [set: 'rV_2].
  apply/eqP; rewrite eqEcard subsetT -(card_isog isoU) oU.
  rewrite cardsT card_matrix card_ord Zp_cast // leq_sqr -/p.
  apply: dvdn_leq; first by rewrite -(subnKC pgt2).
  rewrite -divn2 -(@Gauss_dvdl a _ 2) ?divnK //.
    by rewrite dvdn2 -subn1 odd_sub ?odd_gt0 ?mFT_odd.
  by rewrite coprimen2 (dvdn_odd (dvdn_indexg U _)) ?mFT_odd.
have [r pr_r r_r_U] := rank_witness U.
have [R0 sylR0] := Sylow_exists r U; have [sR0U rR0 _] := and3P sylR0.
have [_ sUH _] := FTtypeII_support_facts maxS StypeP Stype2 pairST maxNU_L.
have [R sylR sR0R] := Sylow_superset (subset_trans sR0U sUH) rR0.
have [sRH rR _] := and3P sylR.
have cUU: abelian U by have [[]] := FTtypeP_facts maxS StypeP.
have tiA0: normedTI 'A0(S) G S by have [_ _ _ _ []] := FTtypeP_facts _ StypeP.
have [_ sUPU _ nPU _] := sdprod_context defPU.
have coPU := coprimegS (joing_subl U W1) (Ptype_Fcore_coprime StypeP).
have abR0: abelian R0 := abelianS sR0U cUU.
have{a U1 defU1 isoU r_r_U} rR0_2: 'r(R0) = 2.
  by rewrite (rank_Sylow sylR0) -r_r_U (isog_rank isoU) defU1 rank_mx_group.
have piUr: r \in \pi(U) by rewrite -p_rank_gt0 -(rank_Sylow sylR0) rR0_2.
have /exists_inP[x /setD1P[ntx R0x] ntCPx]: [exists x in R0^#, 'C_P[x] != 1%g].
  have ncycR0: ~~ cyclic R0 by rewrite abelian_rank1_cyclic ?rR0_2.
  have coPR0: coprime #|P| #|R0| := coprimegS sR0U coPU.
  rewrite -negb_forall_in; apply: contra (mmax_Fcore_neq1 maxS) => regR0P.
  rewrite -subG1 -(coprime_abelian_gen_cent1 abR0 _ (subset_trans sR0U nPU)) //.
  by rewrite gen_subG; apply/bigcupsP=> x /(eqfun_inP regR0P)->.
have{x ntx R0x ntCPx} sZR_R0: 'Z(R) \subset R0.
  have A0x: x \in 'A0(S).
    have [z /setIP[Pz cyz] ntz] := trivgPn _ ntCPx. 
    apply/setUP; left; apply/bigcupP; exists z.
      by rewrite !inE ntz (subsetP (Fcore_sub_FTcore maxS)).
    by rewrite (eqP Stype2) 3!inE ntx cent1C (subsetP sUPU) ?(subsetP sR0U).
  have sCxS: 'C[x] \subset S.
    have [memJ_A0 _] := normedTI_memJ_P (FTsupp0_neq0 maxS) tiA0.
    apply/subsetP=> y /cent1P cxy; rewrite -(memJ_A0 x) ?in_setT //.
    by rewrite conjgE -cxy mulKg.
  suffices <-: 'C_R[x] = R0.
    by rewrite -cent_set1 setIS ?centS // sub1set (subsetP sR0R).
  have /Hall_pi hallU: Hall PU U by rewrite -(coprime_sdprod_Hall_r defPU).
  have /Hall_pi hallPU: Hall S PU by rewrite -(coprime_sdprod_Hall_l defS).
  have sylR0_S: r.-Sylow(S) R0.
    by apply: subHall_Sylow piUr sylR0; apply: subHall_Hall (piSg sUPU) hallU.
  rewrite ['C_R[x]](sub_pHall sylR0_S) ?(pgroupS _ rR) ?subsetIl //.
    by rewrite subsetI sR0R sub_cent1 (subsetP abR0).
  by rewrite subIset ?sCxS ?orbT.
pose R1 := 'Ohm_1('Z(R))%G; pose m := logn r #|R1|.
have sR10: R1 \subset R0 by rewrite (subset_trans (Ohm_sub 1 _)).
have oR1: #|R1| = (r ^ m)%N by rewrite -card_pgroup ?(pgroupS sR10).
have{sZR_R0 rR0_2} m12: pred2 1%N 2 m.
  transitivity (0 < m < 1 + 2)%N; first by rewrite -mem_iota !inE.
  rewrite -[m]p_rank_abelian ?center_abelian -?rank_pgroup ?(pgroupS sZR_R0) //.
  rewrite rank_gt0 ltnS -rR0_2 rankS // center_nil_eq1 ?(pgroup_nil rR) //.
  by rewrite (subG1_contra sR0R) // -rank_gt0 rR0_2.
have [y Qy /sdprod_context[_ sW12yL _ /joing_subP[_ nHW2y] tiHW12y]] := defL.
have chR1H: R1 \char H.
  apply: char_trans (char_trans (Ohm_char 1 _) (center_char R)) _.
  by rewrite (nilpotent_Hall_pcore (Fcore_nil L) sylR) gFchar.
have nR1W2y: W2 :^ y \subset 'N(R1) := char_norm_trans chR1H nHW2y.
have regR1W2y: semiregular R1 (W2 :^ y).
  apply: semiregular_sym => x /setD1P[ntx R1x]; apply/trivgP.
  have [_ _ _ regHL] := Frobenius_kerP frobL.
  rewrite /= -(setIidPr (joing_subr W1 (W2 :^ y))) setIAC subIset //.
  rewrite -(setIidPr sW12yL) setIAC -tiHW12y setSI ?regHL // !inE ntx.
  by rewrite (subsetP (char_sub chR1H)).
have /idPn[]: r %| p.-1./2.
  have:= piUr; rewrite mem_primes => /and3P[_ _ /=].
  by rewrite oU Euclid_dvdX ?andbT.
rewrite gtnNdvd //; first by rewrite -(subnKC pgt2).
apply: leq_trans (_ : p.-1 <= r)%N.
  by rewrite -divn2 ltn_divLR // -{1}[p.-1]muln1 -(subnKC pgt2) ltn_pmul2l.
have: p %| (r ^ m).-1.
  by have:= regular_norm_dvd_pred nR1W2y regR1W2y; rewrite cardJg oR1.
rewrite -[p.-1]subn1 leq_subLR  predn_exp Euclid_dvdM // => /orP[]/dvdn_leq.
  by rewrite -(subnKC (prime_gt1 pr_r)) => /implyP/leq_trans->; rewrite 2?ltnW.
move/implyP; case/pred2P: m12 => ->; rewrite !big_ord_recl big_ord0 ?addn0 //=.
by rewrite -(subnKC pgt2).
Qed.

(* This is Peterfalvi (14.7). *)
Let not_charUH : ~~ (U \char H).
Proof.
have [y Qy /sdprod_context[_ sW12yL _ /joing_subP[_ nHW2y] tiHW12y]] := defL.
apply/negP=> chUH; have nUW2y := char_norm_trans chUH nHW2y.
case: no_full_FT_Galois_structure; split; last first.
  split; [by have [_ []] := FTtypeP_facts _ TtypeP | | by exists y].
  by have /sdprodP[_ _ /joing_subP[]] := Ptype_Fcore_sdprod TtypeP.
have <-: #|U| = nU.
  have regUW2y: semiregular U (W2 :^ y).
    apply: semiregular_sym => x /setD1P[ntx R1x]; apply/trivgP.
    have [_ _ _ regHL] := Frobenius_kerP frobL.
    rewrite /= -(setIidPr (joing_subr W1 (W2 :^ y))) setIAC subIset //.
    rewrite -(setIidPr sW12yL) setIAC -tiHW12y setSI ?regHL // !inE ntx.
    by rewrite (subsetP (char_sub chUH)).
  case: ifP (card_FTtypeP_Galois_compl maxS galS) => //.
  rewrite -/p -/q -/nU => p_modq_1 oU.
  have{p_modq_1 oU} oU: (#|U| * q)%N = nU.
    by rewrite oU divnK //; have [|_ ->] := FTtypeP_primes_mod_cases _ StypeP.
  have /eqP Umodp: #|U| == 1 %[mod p].
    have:= regular_norm_dvd_pred nUW2y regUW2y.
    by rewrite cardJg -/p -subn1 eqn_mod_dvd.
  have: nU == 1 %[mod p].
    rewrite /nU predn_exp mulKn; last by rewrite -(subnKC pgt2).
    rewrite -(ltn_predK qgt2) big_ord_recl addnC -modnDml -modn_summ modnDml.
    by rewrite big1 // => i _; rewrite expnS modnMr.
  by rewrite -oU -modnMml Umodp modnMml mul1n !modn_small ?gtn_eqF ?prime_gt1.
have [F []] := typeP_Galois_P maxS (FTtype5_exclusion maxS) galS.
rewrite Ptype_factor_prime ?(group_inj (Ptype_Fcore_kernel_trivial _ _)) //.
rewrite Ptype_Fcompl_kernel_trivial // => psiP [psiU _ [/trivgP inj_psiU psiJ]].
rewrite /= -injm_subcent ?coset1_injm ?norms1 // -morphim_comp -/p.
rewrite (typeP_cent_core_compl StypeP) => [[_ /isomP[inj_psiP im_psiP] psiW2]].
rewrite -(card_isog (quotient1_isog U)) => [[_ coUp1 _]].
suffices FPU: finFieldImage P W2 U.
  by exists FPU; have [_ []] := FTtypeP_facts maxS StypeP.
have /domP[sig [Dsig Ksig _ im_sig]]: 'dom (psiP \o coset 1) = P.
  by apply: injmK; rewrite ?coset1_injm ?norms1.
have{Ksig} inj_sig: 'injm sig by rewrite Ksig injm_comp ?coset1_injm.
exists F sig; first by apply/isomP; rewrite im_sig morphim_comp.
  by rewrite -psiW2 -im_sig injmK // -(typeP_cent_core_compl StypeP) subsetIl.
exists psiU => // z x Pz Ux /=; have inN1 x1: x1 \in 'N(1) by rewrite norm1 inE.
by rewrite !Dsig -psiJ ?mem_morphim //= qactE ?dom_qactJ.
Qed.

(* This is Peterfalvi (14.8)(a). *)
(* In order to avoid the use of real analysis and logarithms we bound the     *)
(* binomial expansion of n.+1 ^ q.+1 directly.                                *)
Let qp1_gt_pq1 : (q ^ p.+1 > p ^ q.+1)%N.
Proof.
have: (4 < p)%N by rewrite odd_geq ?mFT_odd ?(leq_trans _ ltqp).
elim: p ltqp => // n IHn; rewrite !ltnS => ngeq.
rewrite leq_eqVlt => /predU1P[/esym n4 | ngt4].
  suffices /eqP <-: 3 == q by rewrite n4.
  by rewrite eqn_leq qgt2 -ltnS -(odd_ltn 5) ?mFT_odd // -n4.
apply: leq_trans (_ : q * n ^ q.+1 <= _)%N; last first.
  rewrite (expnS q) leq_mul //.
  by move: ngeq; rewrite leq_eqVlt => /predU1P[-> | /IHn/(_ ngt4)/ltnW].
apply: leq_trans (_ : (2 * q.+1 + n) * n ^ q <= _)%N; last first.
  rewrite expnS mulnA leq_mul // addnC.
  move: ngeq; rewrite leq_eqVlt => /predU1P[-> | n_gtq].
    apply: leq_trans (_ : 4 * n <= _)%N; last by rewrite leq_mul // ltnW.
    by rewrite mulnSr addnA -mulSn (mulSnr 3) leq_add2l 3?ltnW.
  by rewrite -{2}(subnKC qgt2) addSn (mulSn _ n) leq_add2l leq_mul.
rewrite mulnDl -expnS -[n.+1]add1n expnDn big_ord_recr binn subnn !mul1n /=.
rewrite ltn_add2r -(@ltn_pmul2l (2 ^ q)) ?expn_gt0 // !mulnA -expnSr.
apply: leq_ltn_trans (_ : (2 ^ q.+1).-1 * q.+1 * n ^ q < _)%N; last first.
  by rewrite -(subnKC ngt4) !ltn_pmul2r ?prednK ?expn_gt0.
rewrite -mulnA predn_exp mul1n big_distrr big_distrl leq_sum // => [[i]] /=.
rewrite ltnS exp1n mul1n => leiq _; rewrite -{1 4}(subnKC leiq) !expnD.
rewrite -mulnA leq_mul // mulnA mulnCA mulnC leq_mul // -bin_sub ?leqW //.
rewrite -(leq_pmul2r (fact_gt0 (q.+1 - i))) -mulnA bin_ffact mulnC subSn //.
rewrite ffactnS /= -!mulnA leq_mul //=; elim: {i leiq}(q - i)%N => //= i IHi.
rewrite ffactnSr expnSr mulnACA expnS factS (mulnACA n) mulnC leq_mul //.
by rewrite leq_mul // (leq_trans (leq_subr _ _)).
Qed.

(* This is Peterfalvi (14.8)(b). *)
Let v1p_gt_u1q : (v.-1 %/ p > u.-1 %/ q)%N.
Proof.
have ub_u: (u.-1 <= nU - 1)%N.
  rewrite -subn1 leq_sub2r //; have [_ _] := FTtypeP_facts maxS StypeP.
  by rewrite (FTtypeP_reg_Fcore maxS StypeP) indexg1.
rewrite ltn_divLR ?prime_gt0 // {ub_u}(leq_ltn_trans ub_u) //.
have p_dv_v1: p %| v.-1 by have [] := FTtypeP_bridge_facts maxT TtypeP.
rewrite divn_mulAC // ltn_divRL ?dvdn_mulr // oV -subn1.
rewrite -(@ltn_pmul2l q.-1) ?(mulnCA q.-1); last by rewrite -(subnKC qgt2).
rewrite !mulnA -(@ltn_pmul2l p.-1); last by rewrite -(subnKC pgt2).
rewrite -mulnA mulnCA mulnA !(mulnBl _ _ _.-1) !divnK ?dvdn_pred_predX //.
rewrite !mul1n mulnCA -!subn1 ltn_mul ?ltn_sub2r ?prime_gt1 //.
rewrite -!subnDA !subnKC ?prime_gt0 // !mulnBl -!expnSr !mulnn.
by rewrite -subSn ?leq_exp2l ?leqW ?prime_gt1 ?leq_sub ?leq_exp2r // ltnW.
Qed.

End Fourteen.

