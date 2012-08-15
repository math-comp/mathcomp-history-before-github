(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7.
Require Import BGsection14 BGsection15 BGsection16.
Require Import ssrnum algC cyclotomic algnum.
Require Import classfun character integral_char inertia vcharacter.
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

Section Thirteen_2_3_5_to_8.

(* These assumptions correspond to Peterfalvi, Hypothesis (13.1); many of     *)
(* them are repeated from above in used to prove (13.2-3) and (13.5-8).       *)
(* Because of the intrinsic limitations of Coq's Section and Module features  *)
(* we will need to be repeat these assumptions twice down this file as we     *)
(* exploit the symmetry between S and T.                                      *)

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
Local Notation PC := 'F(S)%G.
Local Notation "` 'PC'" := 'F(`S) (at level 0) : group_scope.

Let defS : PU ><| W1 = S. Proof. by have [[]] := StypeP. Qed.
Let defPU : P ><| U = PU. Proof. by have [_ []] := StypeP. Qed.
Let defPC : P \x C = PC. Proof. by have [] := typeP_context StypeP. Qed.

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

Lemma Ptype_Fcore_kernel_trivial : H0 :=: 1%g.
Proof.
have [/type2facts[_ oP _]| /type34ker1[]//] := boolP (FTtype S == 2).
have [/and3P[]] := Ptype_Fcore_kernel_exists maxS StypeP notStype5.
case/maxgroupp/andP=> /proper_sub sH0P nH0S /subset_trans/(_ nH0S)nH0P _ _.
apply: card1_trivg; rewrite -(divg_indexS sH0P) -card_quotient //.
have [_ _ ->] := Ptype_Fcore_factor_facts maxS StypeP notStype5.
by rewrite pHbar_p -{}oP divnn ?cardG_gt0.
Qed.
Local Notation H0_1 := Ptype_Fcore_kernel_trivial.

Lemma Ptype_Fcompl_kernel_cent : Ptype_Fcompl_kernel StypeP :=: C.
Proof.
rewrite [Ptype_Fcompl_kernel StypeP]unlock /= (group_inj H0_1).
by rewrite astabQ -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1.
Qed.
Local Notation CHbar_C := Ptype_Fcompl_kernel_cent.

Lemma FTsupp0_neq0 M (maxM : M \in 'M) : 'A0(M : {group gT}) != set0.
Proof.
apply: contraNneq (proper_subn (mmax_proper maxM)) => A0_0.
by rewrite -(norm_FTsupp0 maxM) A0_0 -(setDv [1]) normD1 norms1.
Qed.

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
  exact: Ptype_compl_Frobenius StypeP _.
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
  have [_ [_ /(_ x Dx) defL] /(_ x Dx)[_ _]] := FTsupport_facts maxS.
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

Lemma FTseqInd_TIred j : j != 0 -> mu_ j \in calS.
Proof.
move=> nz_j; rewrite -[mu_ j]cfInd_prTIres mem_seqInd ?gFnormal ?normal1 //=.
by rewrite !inE sub1G (cfker_prTIres (FT_prDade_hypF maxS StypeP)).
Qed.

Lemma FTtypeP_Fitting_abelian : abelian PC.
Proof.
rewrite -(dprodW defPC) abelianM subsetIr.
have [[_ _ _ cUU] [/abelem_abelian-> _] _ _ _] := FTtypeP_facts.
by rewrite (abelianS _ cUU) ?subsetIl.
Qed.
Hint Resolve FTtypeP_Fitting_abelian.

Lemma FTtypeP_Ind_FittingP lambda :
    lambda \in seqIndT PC S ->
  [/\ lambda 1%g = (u * q)%:R
    & exists2 theta, theta \is a linear_char & lambda = 'Ind[S, PC] theta].
Proof.
case/seqIndP=> i _ ->; rewrite cfInd1 -?divgS ?gFsub //; set theta := 'chi_i.
have Ltheta: theta \is a linear_char by apply/char_abelianP.
split; last by [exists theta]; rewrite lin_char1 {i theta Ltheta}// mulr1.
rewrite -(sdprod_card defS) -(sdprod_card defPU) -/q -(dprod_card defPC).
by rewrite -mulnA divnMl // -(LagrangeI U 'C(P)) -indexgI -/u -mulnA mulKn.
Qed.
Local Notation calT_P := FTtypeP_Ind_FittingP.

(* This is Peterfalvi (13.3)(a). *)
Lemma FTprTIred_Ind_Fitting j : j != 0 -> mu_ j \in seqIndT PC S.
Proof.
move=> nz_j; have [//|_ _ _] := typeP_reducible_core_Ind maxS StypeP.
rewrite (group_inj H0_1) CHbar_C -/q /= (dprodWY defPC) -/calS.
case/(_ (mu_ j))=> [|_ _ [_ /lin_char_irr/irrP[r ->] ->]].
  by rewrite mem_filter /= prTIred_not_irr FTseqInd_TIred.
by apply/seqIndP; exists r; rewrite ?inE.
Qed.
Local Notation Tmu := FTprTIred_Ind_Fitting.

Lemma FTprTIred1 j : j != 0 -> mu_ j 1%g = (u * q)%:R.
Proof. by case/Tmu/calT_P. Qed.
Local Notation mu1uq := FTprTIred1.

(* This is the first assertion of Peterfalvi (13.3)(c). *)
Lemma FTprTIsign j : delta_ j = 1.
Proof.
have [[_ _ frobUW1 cUU] _ _ cohS _] := FTtypeP_facts.
have [-> | nz_j] := eqVneq j 0; first exact: prTIsign0.
suffices: (1 == delta_ j %[mod q])%C.
  rewrite signrE /eqCmod addrC opprB subrK dvdC_nat.
  by case: (Idelta j); rewrite ?subr0 // gtnNdvd.
apply: eqCmod_trans (prTIirr1_mod ptiWS 0 j); rewrite -/(mu2_ 0 j) -/q.
have ->: mu2_ 0 j 1%g = u%:R.
  by apply: (mulfI (neq0CG W1)); rewrite -prTIred_1 -/mu_ mu1uq // mulnC natrM.
rewrite eqCmod_sym /eqCmod -(@natrB _ u 1) ?indexg_gt0 // subn1 dvdC_nat.
have nC_UW1: U <*> W1 \subset 'N(C).
  have /sdprodP[_ _ nPUW1 _] := Ptype_Fcore_sdprod StypeP.
  by rewrite normsI ?norms_cent // join_subG normG; have [_ []] := StypeP.
have coUq: coprime #|U| q by have /sdprod_context[_ /coprimeSg->] := defPU.
have /Frobenius_dvd_ker1: [Frobenius U <*> W1 / C = (U / C) ><| (W1 / C)].
  have [defUW1 _ _ _ _] := Frobenius_context frobUW1.
  rewrite Frobenius_coprime_quotient // /normal ?subIset ?joing_subl //.
  split=> [|x /(Frobenius_reg_ker frobUW1)->]; last exact: sub1G.
  rewrite properEneq subsetIl -CHbar_C andbT.
  by have [] := Ptype_Fcore_factor_facts maxS StypeP notStype5.
have [nCU nCW1] := joing_subP nC_UW1; rewrite !card_quotient // -/u.
by rewrite -indexgI setIC setIAC (coprime_TIg coUq) setI1g indexg1.
Qed.
Local Notation delta1 := FTprTIsign.

(* This is Peterfalvi (13.3)(b). *)
Lemma FTtypeP_no_Ind_Fitting_facts :
     ~~ has [predI irr S & seqIndT PC S] calS ->
   [/\ typeP_Galois StypeP, `C = 1%g & u = (p ^ q).-1 %/ p.-1].
Proof.
move=> noIndPC; have [[_ _ _ cUU] _ _ _ _] := FTtypeP_facts.
have [[t []] | [->]] := typeP_reducible_core_cases maxS StypeP notStype5.
  rewrite CHbar_C H0_1 (derG1P (abelianS _ cUU)) ?subsetIl //=.
  rewrite (group_inj (joing1G 1)) -/calS /= (dprodWY defPC) => calSt _.
  case=> _ /lin_char_irr/irrP[r ->] Dt; case/hasP: noIndPC.
  by exists 'chi_t; rewrite //= mem_irr; apply/seqIndP; exists r; rewrite ?inE.
rewrite /= pHbar_p H0_1 oU /c => frobPU _ <- _ /=.
suffices /eqP->: C :==: 1%g by rewrite cards1 muln1.
suffices: 'C_(U / 1)(P / 1) == 1%g.
  by rewrite -injm_subcent ?morphim_injm_eq1 ?norms1 ?ker_coset.
have [_ ntP _ _ _] := Frobenius_context frobPU.
by rewrite (cent_semiregular (Frobenius_reg_compl frobPU)).
Qed.

(* Helper function for (13.3)(c). *)
Let signW2 b j : Iirr W2 := if b then conjC_Iirr j else j.

Let signW2K b : involutive (signW2 b).
Proof. by case: b => //; apply: conjC_IirrK. Qed.

Let signW2_eq0 b : {mono signW2 b: j / j == 0}.
Proof. by case: b => //; apply: conjC_Iirr_eq0. Qed.

(* This is a reformulation of the definition condition part of (13.3)(c) that *)
(* better fits its actual use in (13.7), (13.8) and (13.9) (note however that *)
(* the p = 3 part will in fact not be used).                                  *)
Definition FTtypeP_isoTIred_def tau1 :=
  exists2 b : bool, b -> p = 3
  & forall j, j != 0 -> tau1 (mu_ j) = (-1) ^+ b *: \sum_i eta_ i (signW2 b j).

(* This is the main part of Peterfalvi (13.3)(c), using the definition above. *)
(* Note that the text glosses over the quantifier inversion in the second use *)
(* of (5.8) in the p = 3 case. We must rule out tau1 (mu_ k) = - tau1 (mu_ j) *)
(* by using isometry property of tau1 (alternatively, we could use (4.8) to   *)
(* compute tau1 (mu_ k) = tau (mu_ k - mu_ j) + tau1 (mu_ j) directly.        *)
Lemma FTtypeP_coherence :
   exists2 tau1 : {additive 'CF(S) -> 'CF(G)}, coherent_with calS S^# tau tau1
                & FTtypeP_isoTIred_def tau1.
Proof.
have [redS|] := altP (@allP _ [predC irr S] calS).
  have [k nz_k] := has_nonprincipal_irr ntW2.
  have [_ [tau1 Dtau1]] := uniform_prTIred_coherent pddS nz_k.
  set calT := uniform_prTIred_seq pddS k => cohT.
  exists tau1; last by exists false => // j _; rewrite /= Dtau1 delta1.
  apply: subset_coherent_with cohT => xi Sxi.
  have [_ _ /(_ xi)] := typeP_reducible_core_Ind maxS StypeP notStype5.
  rewrite (group_inj H0_1) mem_filter redS // => /(_ Sxi)/imageP[j nz_j ->] _.
  by rewrite image_f // inE -/mu_ [~~ _]nz_j /= !mu1uq.
rewrite all_predC negbK => /hasP[xi Sxi /irrP[t Dxi]]; rewrite {xi}Dxi in Sxi.
have [_ _ _ [tau1 cohS] _] := FTtypeP_facts; exists tau1 => //.
have [|] := boolP [forall (j | j != 0), tau1 (mu_ j) == \sum_i eta_ i j].
  by move/eqfun_inP=> Dtau1; exists false => // j /Dtau1; rewrite scale1r.
rewrite negb_forall_in => /exists_inP[j nz_j /eqP tau1muj_neq_etaj].
have:= FTtypeP_coherent_TIred sSS0 cohS Sxi (FTseqInd_TIred _).
rewrite -/mu_ -/sigma -/ptiWS => tau1mu; have [dk tau1muj Ddk] := tau1mu j nz_j.
case: Ddk tau1muj => [][-> ->]{dk}; rewrite ?signrN delta1 ?scaleNr scale1r //.
set k := conjC_Iirr j => Dmu tau1muj.
have{Dmu} defIW2 l: l != 0 -> pred2 j k l.
  by move=> nz_l; rewrite Dmu ?FTseqInd_TIred ?mu1uq.
have [nz_k j'k]: k != 0 /\ k != j.
  rewrite conjC_Iirr_eq0 nz_j -(inj_eq irr_inj) conjC_IirrE.
  by rewrite odd_eq_conj_irr1 ?mFT_odd ?irr_eq1.
have /eqP p3: p == 3.
  rewrite -nirrW2 (cardD1 0) (cardD1 j) (cardD1 k) !inE nz_j nz_k j'k !eqSS.
  by apply/pred0Pn=> [[l /and4P[k'l j'l /defIW2/norP[]]]].
exists true => // _ /defIW2/pred2P[]->; first by rewrite scaler_sign.
have [[[Itau1 _] _] [d t1muk Dd]] := (cohS, tau1mu k nz_k); move: Dd t1muk.
case=> [][-> ->] => [|_]; rewrite ?signrN delta1 // scale1r.
case/(congr1 (cfdotr (tau1 (mu_ j)) \o -%R))/eqP/idPn => /=.
rewrite -tau1muj cfdotNl eq_sym !Itau1 ?mem_zchar ?FTseqInd_TIred //.
by rewrite !cfdot_prTIred (negPf j'k) eqxx mul1n oppr0 neq0CG.
Qed.

(* We skip over (13.4), which requires the use of (13.2) and (13.3) on both   *)
(* groups of a type P pair.                                                   *)

Local Notation H := PC.
Local Notation "` 'H'" := `PC (at level 0) : group_scope.

Local Notation calT := (seqIndT H S).
Let calS1 := seqIndD H S P 1.

(* Some facts about calS1 used implicitly throughout (13.5-8). *)
Let S1mu j : j != 0 -> mu_ j \in calS1.
Proof.
move=> nz_j; have /seqIndP[s _ Ds] := Tmu nz_j.
rewrite Ds mem_seqInd ?gFnormal ?normal1 // !inE sub1G andbT.
rewrite -(sub_cfker_Ind_irr s (gFsub _ _) (gFnorm _ _)) -Ds /=.
rewrite -[mu_ j](cfInd_prTIres (FT_prDade_hypF maxS StypeP)).
by rewrite sub_cfker_Ind_irr ?cfker_prTIres ?gFsub ?gFnorm.
Qed.

Let calSirr := [seq phi <- calS | phi \in irr S].

Let S1cases zeta :
  zeta \in calS1 -> {j | j != 0 & zeta = mu_ j} + (zeta \in 'Z[calSirr]).
Proof.
move=> S1zeta; have /sig2_eqW[t /setDP[_ kerP't] Dzeta] := seqIndP S1zeta.
rewrite inE in kerP't; have /mulG_sub[sPH _] := dprodW defPC.
have [/andP[sPPU nPPU] sUPU _ _ _] := sdprod_context defPU.
have sHPU: H \subset PU by rewrite /= -(dprodWC defPC) mulG_subG subIset ?sUPU.
have [/eqfunP mu'zeta|] := boolP [forall j, '['Ind 'chi_t, chi_ j] == 0].
  right; rewrite Dzeta -(cfIndInd _ _ sHPU) ?gFsub //.
  rewrite ['Ind 'chi_t]cfun_sum_constt linear_sum /= rpred_sum // => s tPUs.
  rewrite linearZ rpredZ_Cnat ?Cnat_cfdot_char ?cfInd_char ?irr_char //=.
  have [[j Ds] | [irr_zeta _]] := prTIres_irr_cases ptiWS s.
    by case/eqP: tPUs; rewrite Ds mu'zeta.
  rewrite mem_zchar // mem_filter irr_zeta mem_seqInd ?gFnormal ?normal1 //=.
  by rewrite !inE sub1G andbT -(sub_cfker_constt_Ind_irr tPUs).
rewrite negb_forall => /existsP/sigW[j].
rewrite -irr_consttE constt_Ind_constt_Res => jHt.
have nz_j: j != 0; last do [left; exists j => //].
  apply: contraTneq jHt => ->; rewrite prTIres0 rmorph1 -irr0 constt_irr.
  by apply: contraNneq kerP't => ->; rewrite irr0 cfker_cfun1.
have /pairwise_orthogonalP[_ ooS1]: pairwise_orthogonal calS1.
  by rewrite seqInd_orthogonal ?gFnormal.
rewrite -(cfRes_prTIirr _ 0) cfResRes ?gFsub //= in jHt.
have muj_mu0j: Imu2 (0, j) \in irr_constt (mu_ j).
  by rewrite irr_consttE cfdotC cfdot_prTIirr_red eqxx conjC1 oner_eq0.
apply: contraNeq (constt_Res_trans (prTIred_char _ _) muj_mu0j jHt).
by rewrite cfdot_Res_l /= -Dzeta eq_sym => /ooS1-> //; rewrite S1mu.
Qed.

Let sS1S : {subset calS1 <= 'Z[calS]}.
Proof.
move=> zeta /S1cases[[j nz_j ->]|]; first by rewrite mem_zchar ?FTseqInd_TIred.
by apply: zchar_subset; apply: mem_subseq (filter_subseq _ _).
Qed.

(* This is Peterfalvi (13.5). *)
(* We have adapted the statement to its actual use by replacing the Dade      *)
(* (partial) isometry by a (total) coherent isometry, and strengthening the   *)
(* orthogonality condition. This simplifies the assumptions as zeta0 is no    *)
(* longer needed.                                                             *)
Lemma FTtypeP_seqInd_Fcore_split (tau1 : {additive _}) zeta1 chi :
   coherent_with calS S^# tau tau1 -> zeta1 \in calS1 -> chi \in 'Z[irr G] ->
   {in calS1, forall zeta, zeta != zeta1 -> '[tau1 zeta, chi] = 0} -> 
  let a := '[tau1 zeta1, chi] in
  exists2 alpha,
     alpha \in 'Z[irr H] /\ {subset irr_constt alpha <= Iirr_ker H P} &
  [/\ (*a*) {in H^#, forall x, chi x = a / '[zeta1] * zeta1 x + alpha x}, 
      (*b*)
         \sum_(x in H^#) `|chi x| ^+ 2 =
             a ^+ 2 / '[zeta1] * (#|S|%:R - zeta1 1%g ^+ 2 / '[zeta1])
             - 2%:R * a * (zeta1 1%g * alpha 1%g / '[zeta1])
             + (\sum_(x in H^#) `|alpha x| ^+ 2)              
    & (*c*)
         \sum_(x in H^#) `|alpha x| ^+ 2 >= #|P|.-1%:R * alpha 1%g ^+ 2].
Proof.
case=> _ Dtau1 S1zeta1 Zchi o_tau1S_chi a.
have sW2P: W2 \subset P by have [_ _ _ []] := StypeP.
have /mulG_sub[sPH _] := dprodW defPC.
have ntH: H :!=: 1%g by apply: subG1_contra ntW2; apply: subset_trans sPH.
have ntH1: H^# != set0 by rewrite setD_eq0 subG1.
have sH1S: H^# \subset G^# by rewrite setSD ?subsetT.
have[nsHS nsPS ns1S]: [/\ H <| S, P <| S & 1 <| S] by rewrite !gFnormal normal1.
have [[sHS nHS] [sPS nPS]] := (andP nsHS, andP nsPS).
have tiH: normedTI H^# G S.
  apply/andP; split; first by have [] := compl_of_typeII_IV maxS StypeP.
  by rewrite setTI normD1 (mmax_normal maxS).
have [ddH ddH_1] := Dade_normedTI_P _ sH1S ntH1 tiH; pose tauH := Dade ddH.
have DtauH: {in 'CF(S, H^#), tauH =1 'Ind} := Dade_Ind ddH_1.
have sS1T: {subset calS1 <= calT} by exact: seqInd_subT.
pose zeta0 := zeta1^*%CF.
have S1zeta0: zeta0 \in calS1 by rewrite cfAut_seqInd.
have zeta1'0: zeta0 != zeta1.
  by rewrite (hasPn (seqInd_notReal _ _ _ _) _ S1zeta1) ?gFnormal ?mFT_odd.
have Tzeta0 := sS1T _ S1zeta0.
have calTuq zeta: zeta \in calT -> zeta 1%g = (u * q)%:R by case/calT_P.
have dT_1 zeta: zeta \in calT -> (zeta - zeta0) 1%g == 0.
  by move=> Tzeta; rewrite 2!cfunE !calTuq // subrr eqxx.
have H1dzeta zeta: zeta \in calT -> zeta - zeta0 \in 'CF(S, H^#).
  have TonH: {subset calT <= 'CF(S, H)} by exact: seqInd_on.
  by move=> Tzeta; rewrite cfun_onD1 rpredB ?TonH ?dT_1.
pose calT1 := rem zeta1 (rem zeta0 (filter [mem calS1] calT)).
pose calT2 := filter [predC calS1] calT.
have DcalT: perm_eq calT (zeta0 :: zeta1 :: calT1 ++ calT2).
  rewrite -(perm_filterC [mem calS1]) -!cat_cons perm_cat2r.
  rewrite (perm_eqlP (@perm_to_rem _ zeta0 _ _)) ?mem_filter /= ?S1zeta0 //.
  rewrite perm_cons perm_to_rem // mem_rem_uniq ?filter_uniq ?seqInd_uniq //.
  by rewrite !inE mem_filter /= eq_sym zeta1'0 S1zeta1 sS1T.
have{DcalT} [a_ _ Dchi _] := invDade_seqInd_sum ddH chi DcalT.
have Da_ zeta: zeta \in calT -> a_ zeta = '['Ind (zeta - zeta0), chi].
  move=> Tzeta; rewrite /a_ !calTuq // divff ?scale1r; last first.
    by rewrite pnatr_eq0 -lt0n muln_gt0 indexg_gt0 cardG_gt0.
  by rewrite [Dade _ _]DtauH ?H1dzeta.
have Za_ zeta: zeta \in calT -> a_ zeta \in Cint.
  move=> Tzeta; rewrite Da_ // Cint_cfdot_vchar ?cfInd_vchar //.
  by rewrite rpredB ?char_vchar ?(seqInd_char Tzeta) ?(seqInd_char Tzeta0).
have{Da_} Da_ zeta: zeta \in calS1 -> a_ zeta = '[tau1 zeta, chi].
  move=> S1zeta; have Tzeta := sS1T _ S1zeta; move/(_ _ Tzeta) in H1dzeta.
  rewrite Da_ //; have [_ _ _ _ [_ <-]] := FTtypeP_facts.
    rewrite -Dtau1; last by rewrite zcharD1E rpredB ?sS1S ?dT_1.
    by rewrite raddfB cfdotBl (o_tau1S_chi zeta0) ?subr0.
  apply: cfun_onS H1dzeta; apply: subset_trans (FTsupp_sub0 S).
  have /trivgPn[y Py nty] := subG1_contra sW2P ntW2.
  apply/subsetP=> x H1x; apply/bigcupP; exists y.
    by rewrite !inE nty (subsetP (Fcore_sub_FTcore maxS)).
  rewrite notStype1 (subsetP _ x H1x) ?setSD //= subsetI sub_cent1.
  rewrite (subsetP FTtypeP_Fitting_abelian) -(dprodW defPC).
    by rewrite -(sdprodW defPU) mulgS ?subsetIl.
  by rewrite (subsetP _ y Py) ?mulG_subl.
pose alpha := 'Res[H] (\sum_(zeta <- calT2) (a_ zeta)^* / '[zeta] *: zeta).
have{Dchi} Dchi: {in H^#, forall x, chi x = a / '[zeta1] * zeta1 x + alpha x}.
  move=> x H1x; have [_ Hx] := setD1P H1x.
  transitivity (invDade ddH chi x).
    by rewrite cfunElock ddH_1 // big_set1 H1x mul1g cards1 invr1 mul1r.
  rewrite cfResE ?gFsub ?Dchi // big_cons conj_Cint ?Za_ ?Da_ ?sS1T //= -/a.
  congr (_ + _); rewrite big_cat /= sum_cfunE big1_seq ?add0r //= => [|zeta].
    by apply: eq_bigr => zeta; rewrite cfunE.
  rewrite ?(mem_rem_uniq, inE) ?rem_uniq ?filter_uniq ?seqInd_uniq //=.
  rewrite mem_filter => /and4P[/= zeta1'z _ S1zeta _].
  by rewrite Da_ ?o_tau1S_chi // conjC0 !mul0r.
have kerHalpha: {subset irr_constt alpha <= Iirr_ker H P}.
  move=> s; apply: contraR => kerP's; rewrite [alpha]rmorph_sum cfdot_suml.
  rewrite big1_seq // => psi; rewrite mem_filter /= andbC => /andP[].
  case/seqIndP=> r _ ->; rewrite mem_seqInd // !inE sub1G andbT negbK => kerPr.
  rewrite cfdot_Res_l cfdotZl mulrC cfdot_sum_irr big1 ?mul0r // => t _.
  apply: contraNeq kerP's; rewrite mulf_eq0 fmorph_eq0 inE => /norP[rSt sSt].
  by rewrite (sub_cfker_constt_Ind_irr sSt) -?(sub_cfker_constt_Ind_irr rSt).
have Zalpha: alpha \in 'Z[irr H].
  rewrite [alpha]rmorph_sum big_seq rpred_sum // => zeta; rewrite mem_filter /=.
  case/andP=> S1'zeta Tzeta; rewrite linearZ /= -scalerA.
  rewrite rpredZ_Cint ?conj_Cint ?Za_ //; have [s _ ->] := seqIndP Tzeta.
  rewrite induced_sum_rcosets -?cfclass_sum -?induced_prod_index //=.
  rewrite scalerK ?cfnorm_eq0 ?cfInd_eq0 ?irr_neq0 ?irr_char ?gFsub //.
  by apply: rpred_sum => i _; apply: irr_vchar.
have{Da_ Za_} Za: a \in Cint by rewrite -[a]Da_ ?Za_ ?sS1T. 
exists alpha => //; split=> //.
  set a1 := a / _ in Dchi; pose phi := a1 *: 'Res zeta1 + alpha.
  transitivity (#|H|%:R * '[phi] - `|phi 1%g| ^+ 2).
    rewrite (cfnormE (cfun_onG phi)) mulVKf ?neq0CG // addrC.
    rewrite (big_setD1 _ (group1 H)) addKr; apply: eq_bigr => x H1x.
    by have [_ Hx] := setD1P H1x; rewrite !cfunE cfResE // Dchi.
  have Qa1: a1 \in Creal.
    apply: rpred_div; first by rewrite rpred_Cint.
    by rewrite rpred_Cnat // Cnat_cfdot_char ?(seqInd_char S1zeta1).
  rewrite cfnormDd; last first.
    rewrite [alpha]cfun_sum_constt cfdotZl cfdot_sumr big1 ?mulr0 // => s.
    move/kerHalpha; rewrite inE cfdotZr mulrC cfdot_Res_l => kerPs.
    have [r kerP'r ->] := seqIndP S1zeta1; rewrite cfdot_sum_irr big1 ?mul0r //.
    move=> t _; apply: contraTeq kerP'r; rewrite !inE sub1G andbT negbK.
    rewrite mulf_eq0 fmorph_eq0 => /norP[]; rewrite -!irr_consttE.
    by move=> /sub_cfker_constt_Ind_irr-> // /sub_cfker_constt_Ind_irr <-.
  rewrite cfnormZ 2!cfunE cfRes1 2?real_normK //; last first.
    rewrite rpredD 1?rpredM // Creal_Cint ?Cint_vchar1 // ?char_vchar //.
    by rewrite (seqInd_char S1zeta1).
  rewrite mulrDr mulrCA sqrrD opprD addrACA; congr (_ + _); last first.
    rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG //.
    by rewrite (big_setD1 1%g) // Cint_normK ?Cint_vchar1 // addrC addKr.
  rewrite opprD addrA; congr (_ - _); last first.
    rewrite -[_ * a * _]mulrA -mulr_natl; congr (_ * _).
    by rewrite -[a1 * _]mulrA -(mulrA a); congr (_ * _); rewrite -mulrA mulrC.
  rewrite mulrBr; congr (_ - _); last first.
    by rewrite mulrACA -expr2 -!exprMn mulrAC.
  rewrite -mulrA exprMn -mulrA; congr (_ * _); rewrite expr2 -mulrA.
  congr (_ * _); apply: canLR (mulKf (cfnorm_seqInd_neq0 nsHS S1zeta1)) _.
  rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG // mulrC.
  rewrite (cfnormE (seqInd_on nsHS S1zeta1)) mulVKf ?neq0CG //.
  by apply: eq_bigr => x Hx; rewrite cfResE.
rewrite -subn1 natrB // -Cint_normK ?Cint_vchar1 // mulrBl mul1r ler_subl_addl.
apply: ler_trans (_ : \sum_(x in H) `|alpha x| ^+ 2 <= _); last first.
  by rewrite (big_setD1 1%g).
rewrite (big_setID P) /= (setIidPr sPH) ler_paddr ?sumr_ge0 // => [x _|].
  by rewrite mulr_ge0 ?normr_ge0.
rewrite mulr_natl -sumr_const ler_sum // => y Py.
suffices ->: alpha y = alpha 1%g by apply: lerr.
rewrite [alpha]cfun_sum_constt !sum_cfunE; apply: eq_bigr => i.
by rewrite !cfunE => /kerHalpha; rewrite inE => /subsetP/(_ y Py)/cfker1->.
Qed.

(* Add this to character.v. *)
Lemma Iirr1_neq0 (gT1 : finGroupType) (G1 : {group gT1}) :
  G1 :!=: 1%g -> inord 1 != 0 :> Iirr G1.
Proof. by rewrite -classes_gt1 -NirrE -val_eqE /= => /inordK->. Qed.

Local Notation "#1" := (inord 1) (at level 0).
Local Notation eta10 := (eta_ #1 0).
Local Notation eta01 := (eta_ 0 #1).

Let o_tau1_eta (tau1 : {additive _}) i j:
    coherent_with calS S^# tau tau1 -> 
  {in 'Z[calSirr], forall zeta, '[tau1 zeta, eta_ i j] = 0}.
Proof.
move=> cohS _ /zchar_expansion[|z Zz ->].
  by rewrite filter_uniq ?seqInd_uniq.
rewrite raddf_sum cfdot_suml big1_seq //= => phi; rewrite mem_filter.
case/andP=> irr_phi /(coherent_ortho_cycTIiso StypeP sSS0 cohS) o_phi_eta.
by rewrite raddfZ_Cint {Zz}//= cfdotZl o_phi_eta ?mulr0.
Qed.

(* To move to algC, check for prior use. *)
Lemma Cint_ler_sqr b : b \in Cint -> b <= b ^+ 2.
Proof.
move=> Zb; have [-> | nz_b] := eqVneq b 0; first by rewrite expr0n.
apply: ler_trans (_ : `|b| <= _); first by rewrite real_ler_norm ?Creal_Cint.
by rewrite -Cint_normK // ler_eexpr // norm_Cint_ge1.
Qed.

Let P1_int2_lb b : b \in Cint -> 2%:R * u%:R * b <= #|P|.-1%:R * b ^+ 2.
Proof.
move=> Zb; rewrite -natrM; apply: ler_trans (_ : (2 * u)%:R * b ^+ 2 <= _).
  by rewrite ler_wpmul2l ?ler0n ?Cint_ler_sqr.
rewrite ler_wpmul2r -?realEsqr ?Creal_Cint // leC_nat mulnC -leq_divRL //.
have [_ [_ ->] /leq_trans-> //] := FTtypeP_facts.
by rewrite leq_div2l // -subn1 ltn_subRL.
Qed.

(* This is Peterfalvi (13.6). *)
Lemma FTtypeP_sum_Ind_Fitting_lb (tau1 : {additive _}) lambda :
    coherent_with calS S^# tau tau1 ->
    lambda \in [predI irr S & calT] -> lambda \in calS ->
  \sum_(x in H^#) `|tau1 lambda x| ^+ 2 >= #|S|%:R - lambda 1%g ^+ 2.
Proof.
move=> cohS /andP[irr_lam Tlam] Slam; have [[Itau1 Ztau1] _] := cohS.
have Zlam1: tau1 lambda \in 'Z[irr G] by rewrite Ztau1 ?mem_zchar.
have S1lam: lambda \in calS1.
  have [[s kerP's Ds] [r _ Dr]] := (seqIndP Slam, seqIndP Tlam).
  rewrite Dr mem_seqInd ?gFnormal ?normal1 // !inE !sub1G !andbT in kerP's *.
  rewrite -(sub_cfker_Ind_irr r (gFsub _ _) (gFnorm _ _)) /= -Dr.
  by rewrite Ds sub_cfker_Ind_irr ?gFsub ?gFnorm.
have [|alpha [Zalpha kerPalpha]] := FTtypeP_seqInd_Fcore_split cohS S1lam Zlam1.
  move=> zeta S1zeta lam'zeta; rewrite Itau1 ?sS1S //.
  suffices: pairwise_orthogonal calS1 by case/pairwise_orthogonalP=> _ ->.
  by rewrite seqInd_orthogonal ?gFnormal.
rewrite Itau1 ?mem_zchar // irrWnorm // expr1n !divr1 mul1r => [[Dlam ->]].
rewrite mulr1 -ler_subl_addl addrC opprB subrK; apply: ler_trans.
have /calT_P[-> _] := Tlam.
have [[x W2x ntx] [y W1y nty]] := (trivgPn _ ntW2, trivgPn _ ntW1).
have [_ _ _ [_ _ sW2P _ _] _] := StypeP; have Px := subsetP sW2P x W2x.
have [eps pr_eps] := C_prim_root_exists (prime_gt0 pr_q).
have{y W1y W2x nty} lamAmod: (tau1 lambda x == lambda x %[mod 1 - eps])%A.
  have [_ /mulG_sub[_ sW1S] _ tiPUW1] := sdprodP defS.
  have [_ /mulG_sub[sW1W sW2W] cW12 _] := dprodP defW.
  have /mulG_sub[sPPU _] := sdprodW defPU.
  have [o_y cxy]: #[y] = q /\ x \in 'C[y].
    split; last by apply/cent1P; red; rewrite (centsP cW12).
    by apply: nt_prime_order => //; apply/eqP; rewrite -order_dvdn order_dvdG.
  have lam1yx: (tau1 lambda (y * x)%g == tau1 lambda x %[mod 1 - eps])%A.
    by rewrite (vchar_ker_mod_prim pr_eps) ?in_setT.
  have [Sx Sy] := (subsetP (gFsub _ _) x Px, subsetP sW1S y W1y).
  have PUx := subsetP sPPU x Px.
  have lam_yx: (lambda (y * x)%g == lambda x %[mod 1 - eps])%A.
    by rewrite (vchar_ker_mod_prim pr_eps) ?char_vchar ?(seqInd_char Slam).
  apply: eqAmod_trans lam_yx; rewrite eqAmod_sym; apply: eqAmod_trans lam1yx.
  have PUlam: lambda \in 'CF(S, PU) by rewrite (seqInd_on _ Slam) ?gFnormal.
  have PU'yx: (y * x)%g \notin PU.
    by rewrite groupMr //= -[y \in PU]andbT -W1y -in_setI tiPUW1 !inE.
  rewrite (cfun_on0 PUlam PU'yx) (ortho_cycTIiso_vanish pddS) //.
    apply/orthoPl=> _ /mapP[_ /(cycTIirrP defW)[i [j ->]] ->].
    by rewrite (coherent_ortho_cycTIiso StypeP sSS0).
  rewrite !inE (groupMl x (subsetP sW1W y _)) // (subsetP sW2W) // andbT.
  rewrite groupMl // -[x \in _]andTb -PUx -in_setI tiPUW1 !inE negb_or ntx /=.
  by rewrite (contra _ PU'yx) // => /(subsetP sW2P)/(subsetP sPPU).
have{x ntx Px lamAmod} alphaAmod: (alpha 1%g == 0 %[mod 1 - eps])%A.
  have Hx: x \in H by have/mulG_sub[/subsetP->] := dprodW defPC.
  have:= lamAmod; rewrite -[lambda x]addr0 Dlam ?inE ?ntx // mul1r eqAmodDl.
  rewrite cfker1 // [alpha]cfun_sum_constt (subsetP (cfker_sum _ _ _)) //.
  rewrite !inE Hx (subsetP _ x Px) //; apply/bigcapsP=> i /kerPalpha.
  by rewrite !inE => /subset_trans-> //; apply: cfker_scale.
have /dvdCP[b Zb ->]: (q %| alpha 1%g)%C.
  by rewrite (int_eqAmod_prime_prim pr_eps) // Cint_vchar1.
rewrite natrM mulrACA exprMn !mulrA 2?ler_pmul2r ?gt0CG //.
by rewrite -[_ * b * b]mulrA P1_int2_lb.
Qed.

(* This is Peterfalvi (13.7). *)
Lemma FTtypeP_sum_cycTIiso10_lb : \sum_(x in H^#) `|eta10 x| ^+ 2 >= #|H^#|%:R.
Proof.
pose mu1 := mu_ #1; have S1mu1: mu1 \in calS1 by rewrite S1mu ?Iirr1_neq0.
have Zeta10: eta10 \in 'Z[irr G] by rewrite cycTIiso_vchar.
have [tau1 cohS [b _ Dtau1]] := FTtypeP_coherence.
have{b Dtau1} oS1eta10: {in calS1, forall zeta, '[tau1 zeta, eta10] = 0}.
  move=> zeta /S1cases[[j nz_j ->] | /o_tau1_eta-> //].
  rewrite Dtau1 // cfdotZl cfdot_suml big1 ?mulr0 // => i _.
  by rewrite cfdot_cycTIiso signW2_eq0 (negPf nz_j) andbF.
have [_ /oS1eta10//| alpha []] := FTtypeP_seqInd_Fcore_split cohS S1mu1 Zeta10.
rewrite {}oS1eta10 // expr0n mulr0 !mul0r subrr add0r.
case=> Zalpha kerPalpha [Deta10 -> ub_alpha].
have{Deta10} Deta10: {in H^#, eta10 =1 alpha}.
  by move=> x /Deta10; rewrite !mul0r add0r.
set a1_2 := alpha 1%g ^+ 2 in ub_alpha.
have Dsum_alpha: \sum_(x in H^#) `|alpha x| ^+ 2 = #|H|%:R * '[alpha] - a1_2.
  rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG // (big_setD1 _ (group1 H)) /=.
  by rewrite addrC Cint_normK ?addKr ?Cint_vchar1.
have [/mulG_sub[sPH _] [_ _ _ [_ _ sW2P _ _] _]] := (dprodW defPC, StypeP).
have nz_alpha: alpha != 0.
  have [[x W2x ntx] [y W1y nty]] := (trivgPn _ ntW2, trivgPn _ ntW1).
  have [eps pr_eps] := C_prim_root_exists (prime_gt0 pr_q).
  have [_ mulW12 cW12 tiW12] := dprodP defW.
  have [sW1W sW2W] := mulG_sub mulW12.
  have [o_y cxy]: #[y] = q /\ x \in 'C[y].
    split; last by apply/cent1P; red; rewrite (centsP cW12).
    by apply: nt_prime_order => //; apply/eqP; rewrite -order_dvdn order_dvdG.
  have eta10x: (eta10 x == eta10 (y * x)%g %[mod 1 - eps])%A.
    by rewrite eqAmod_sym (vchar_ker_mod_prim pr_eps) ?in_setT.
  have eta10xy: (eta10 (y * x)%g == 1 %[mod 1 - eps])%A.
    rewrite cycTIiso_restrict; last first.
      rewrite !inE -mulW12 mem_mulg // andbT groupMl ?groupMr // -[_ || _]andTb.
      by rewrite andb_orr -{1}W2x -W1y andbC -!in_setI tiW12 !inE (negPf ntx).
    have {2}<-: w_ #1 0 x = 1.
      rewrite -[x]mul1g /w_ dprod_IirrE cfDprodE // irr0 cfun1E W2x mulr1.
      by rewrite lin_char1 ?irr_cyclic_lin.
    rewrite (vchar_ker_mod_prim pr_eps) ?(subsetP sW1W y) ?(subsetP sW2W) //.
    by rewrite irr_vchar.
  have: (alpha x == 1 %[mod 1 - eps])%A.
    rewrite -Deta10; last by rewrite !inE ntx (subsetP sPH) ?(subsetP sW2P).
    exact: eqAmod_trans eta10x eta10xy.
  apply: contraTneq => ->; rewrite cfunE eqAmod_sym.
  apply/negP=> /(int_eqAmod_prime_prim pr_eps pr_q (rpred1 _))/idPn[].
  by rewrite (dvdC_nat q 1) -(subnKC qgt2).
apply: wlog_neg => suma_lt_H.
suffices{ub_alpha} lb_a1_2: a1_2 >= #|H^#|%:R.
  have Pgt2: (2 < #|P|)%N by apply: leq_trans (subset_leq_card sW2P).
  apply: ler_trans (ler_trans lb_a1_2 _) ub_alpha.
  rewrite ler_pmull ?(ltr_le_trans _ lb_a1_2) ?ler1n ?ltr0n //.
    by rewrite -(subnKC Pgt2).
  have:= leq_trans (ltnW Pgt2) (subset_leq_card sPH).
  by rewrite (cardsD1 1%g) group1.
have /CnatP[n Dn]: '[alpha] \in Cnat by rewrite Cnat_cfnorm_vchar.
have /CnatP[m Dm]: a1_2 \in Cnat by rewrite Cnat_exp_even ?Cint_vchar1.
rewrite Dm leC_nat leqNgt; apply: contra suma_lt_H => a1_2_lt_H.
rewrite {1}Dsum_alpha Dn Dm -natrM ler_subr_addl (cardsD1 1%g H) group1 /=.
case Dn1: n => [|[|n1]]; first by rewrite -cfnorm_eq0 Dn Dn1 eqxx in nz_alpha.
  have /dirrP[b [i Dalpha]]: alpha \in dirr H by rewrite dirrE Zalpha Dn Dn1 /=.
  rewrite -Dm /a1_2 Dalpha cfunE exprMn sqrr_sign mul1r muln1 mulrS ler_add2r.
  by rewrite lin_char1 ?expr1n //; apply/char_abelianP.
rewrite -natrD leC_nat -add2n mulnDr (addnC 1%N) mulnDl -addnA.
by apply: leq_trans (leq_addr _ _); rewrite muln2 -addnn leq_add2r ltnW.
Qed.

(* This is Peterfalvi (13.8). *)
(* We have filled a logical gap in the textbook, which quotes (13.3.c) to get *)
(* a j such that eta_01 is a component of mu_j^tau1, then asserts that the    *)
(* (orthogonality) assumptions of (13.5) have been checked, apparently        *)
(* implying that because for zeta in calS1 \ mu_j, zeta^tau1 is orthogonal to *)
(* mu_j^tau1, as per the proof of (13.6), zeta^tau1 must be orthogonal to     *)
(* eta_01. This is wrong, because zeta^tau1, mu_j^tau1 and eta_01 are not     *)
(* characters, by virtual characters. We need to adopt a more careful line of *)
(* reasoning, using the more precise characterization of calS1 in the lemma   *)
(* S1cases above (which does use the orthogonal-constituent argument, but     *)
(* for chi_j and Res_H zeta), and the decomposition given in (13.3.c) for all *)
(* the mu_k.                                                                  *)
Lemma FTtypeP_sum_cycTIiso01_lb :
  \sum_(x in H^#) `|eta01 x| ^+ 2 >= #|PU|%:R - (u ^ 2)%:R.
Proof.
have [tau1 cohS [b _ Dtau1]] := FTtypeP_coherence.
have Zeta01: eta01 \in 'Z[irr G] by rewrite cycTIiso_vchar.
pose j1 := signW2 b #1; pose d : algC := (-1) ^+ b; pose mu1 := mu_ j1.
have nzj1: j1 != 0 by [rewrite signW2_eq0 ?Iirr1_neq0]; have S1mu1 := S1mu nzj1.
have o_mu_eta01 j: j != 0 -> '[tau1 (mu_ j), eta01] = d *+ (j == j1). 
  move/Dtau1->; rewrite -/d cfdotZl cfdot_suml big_ord_recl /=.
  rewrite cfdot_cycTIiso andTb (inv_eq (signW2K b)).
  by rewrite big1 ?addr0 ?mulr_natr // => i _; rewrite cfdot_cycTIiso.
have [zeta | alpha []] := FTtypeP_seqInd_Fcore_split cohS S1mu1 Zeta01.
  case/S1cases=> [[j nz_j ->] | /o_tau1_eta-> //].
  by rewrite o_mu_eta01 // (inj_eq (prTIred_inj _)) => /negPf->.
rewrite o_mu_eta01 // eqxx mulrb => Zalpha kerPalpha [_ -> lb_alpha].
rewrite -ler_subl_addl cfnorm_prTIred -/q mulrAC sqrr_sign mul1r.
rewrite mu1uq // natrM exprMn (mulrAC _ q%:R) (mulrA _ q%:R) !mulfK ?neq0CG //.
rewrite natrX -(sdprod_card defS) natrM -mulrBl mulfK ?neq0CG //.
rewrite addrC opprB subrK mulrACA; apply: ler_trans lb_alpha.
apply: ler_trans (P1_int2_lb _) _; first by rewrite rpredMsign Cint_vchar1.
by rewrite exprMn sqrr_sign mul1r lerr.
Qed.

End Thirteen_2_3_5_to_8.

End Thirteen.
