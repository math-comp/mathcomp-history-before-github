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

Lemma FTseqInd_TIred j : j != 0 -> mu_ j \in calS.
Proof.
move=> nz_j; rewrite -[mu_ j]cfInd_prTIres mem_seqInd ?gFnormal ?normal1 //=.
by rewrite !inE sub1G (cfker_prTIres (FT_prDade_hypF maxS StypeP)).
Qed.

Definition is_Ind_Fitting lambda := [exists r, lambda == 'Ind[S, PC] 'chi_r].

Lemma FTtypeP_Fitting_abelian : abelian PC.
Proof.
rewrite -(dprodW defPC) abelianM subsetIr.
have [[_ _ _ cUU] [/abelem_abelian-> _] _ _ _] := FTtypeP_facts.
by rewrite (abelianS _ cUU) ?subsetIl.
Qed.
Hint Resolve FTtypeP_Fitting_abelian.

Lemma FTtypeP_Ind_FittingP lambda :
    is_Ind_Fitting lambda ->
  [/\ lambda 1%g = (u * q)%:R
    & exists2 theta : 'CF(PC), theta \is a linear_char & lambda = 'Ind theta].
Proof.
case/exists_eqP=> i ->; rewrite cfInd1 -?divgS ?gFsub //; set theta := 'chi_i.
have Ltheta: theta \is a linear_char by apply/char_abelianP.
split; last by [exists theta]; rewrite lin_char1 {i theta Ltheta}// mulr1.
rewrite -(sdprod_card defS) -(sdprod_card defPU) -/q -(dprod_card defPC).
by rewrite -mulnA divnMl // -(LagrangeI U 'C(P)) -indexgI -/u -mulnA mulKn.
Qed.
Local Notation PCindP := FTtypeP_Ind_FittingP.

(* This is Peterfalvi (13.3). *)
(* Note that the text fails to mention the quantifier inversion from (5.8),   *)
(* which must be handled either by using the isometry property of tau1 to     *)
(* rule out tau1 (mu_ k) = - tau1 (mu_ j), or the coherence property along    *)
(* with (4.8).                                                                *)
Lemma FTtypeP_char_facts :
  [/\ (*a*) forall j, j != 0 -> is_Ind_Fitting (mu_ j),
      (*b*) ~~ has [pred lam in irr S | is_Ind_Fitting lam] calS ->
            [/\ typeP_Galois StypeP, `C = 1%g & u = (p ^ q).-1 %/ p.-1],
      (*c*) forall j, delta_ j = 1
          & exists2 tau1 : {additive 'CF(S) -> 'CF(G)},
              coherent_with calS S^# tau tau1
            & [\/ forall j, j != 0 -> tau1 (mu_ j) = \sum_i eta_ i j
                | [/\ p = 3
                  & forall j, j != 0 -> tau1 (mu_ j) = - \sum_i eta_ i (- j)]]].
Proof.
have indPCmu j: j != 0 -> is_Ind_Fitting (mu_ j).
  move=> nz_j; have [//|_ _ _] := typeP_reducible_core_Ind maxS StypeP.
  rewrite (group_inj H0_1) CHbar_C -/q /= (dprodWY defPC) -/calS.
  case/(_ (mu_ j))=> [|_ _ [_ /lin_char_irr/irrP[r ->] ->]].
    by rewrite mem_filter /= prTIred_not_irr FTseqInd_TIred.
  by apply/exists_eqP; exists r.
have Dmu1 j: j != 0 -> mu_ j 1%g = (u * q)%:R by case/indPCmu/PCindP.
have [[_ _ frobUW1 cUU] _ _ cohS _] := FTtypeP_facts.
have delta1 j: delta_ j = 1.
  have [-> | nz_j] := eqVneq j 0; first exact: prTIsign0.
  suffices: (1 == delta_ j %[mod q])%C.
    rewrite signrE /eqCmod addrC opprB subrK dvdC_nat.
    by case: (Idelta j); rewrite ?subr0 // gtnNdvd.
  apply: eqCmod_trans (prTIirr1_mod ptiWS 0 j); rewrite -/(mu2_ 0 j) -/q.
  have ->: mu2_ 0 j 1%g = u%:R.
    by apply: (mulfI (neq0CG W1)); rewrite -prTIred_1 -/mu_ -natrM mulnC Dmu1.
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
split=> // [notSindPC | ].
  have [[t []] | [->]] := typeP_reducible_core_cases maxS StypeP notStype5.
    rewrite CHbar_C H0_1 (derG1P (abelianS _ cUU)) ?subsetIl //=.
    rewrite (group_inj (joing1G 1)) -/calS /= (dprodWY defPC) => calSt _.
    case=> _ /lin_char_irr/irrP[r ->] Dt; case/hasP: notSindPC.
    by exists 'chi_t; rewrite //= mem_irr; apply/exists_eqP; exists r.
  rewrite /= pHbar_p H0_1 oU /c => frobPU _ <- _.
  suffices: 'C_(U / 1)(P / 1) == 1%g.
    rewrite -injm_subcent ?morphim_injm_eq1 ?norms1 ?ker_coset //=.
    by move/eqP->; rewrite cards1 muln1.
  have [_ ntP _ _ _] := Frobenius_context frobPU.
  by rewrite (cent_semiregular (Frobenius_reg_compl frobPU)).
have [redS|] := altP (@allP _ [predC irr S] calS).
  have [k nz_k] := has_nonprincipal_irr ntW2.
  have [_ [tau1 Dtau1]] := uniform_prTIred_coherent pddS nz_k.
  set calT := uniform_prTIred_seq pddS k => cohT.
  exists tau1; last by left=> j _; rewrite /= Dtau1 delta1 scale1r.
  apply: subset_coherent_with cohT => xi Sxi.
  have [_ _ /(_ xi)] := typeP_reducible_core_Ind maxS StypeP notStype5.
  rewrite (group_inj H0_1) mem_filter redS // => /(_ Sxi)/imageP[j nz_j ->] _.
  by rewrite image_f // inE -/mu_ [~~ _]nz_j /= !Dmu1.
rewrite all_predC negbK => /hasP[xi Sxi /irrP[t Dxi]]; rewrite {xi}Dxi in Sxi.
have{cohS} [tau1 cohS] := cohS; exists tau1 => //.
have [|] := boolP [forall (j | j != 0), tau1 (mu_ j) == \sum_i eta_ i j].
  by move/eqfun_inP; left.
rewrite negb_forall_in => /exists_inP[j nz_j /eqP tau1muj_neq_etaj].
have:= FTtypeP_coherent_TIred sSS0 cohS Sxi (FTseqInd_TIred _).
rewrite -/mu_ -/sigma -/ptiWS => tau1mu; have [dk tau1muj Ddk] := tau1mu j nz_j.
case: Ddk tau1muj => [][-> ->]{dk}; rewrite ?signrN delta1 ?scaleNr scale1r //.
set k := conjC_Iirr j => Dmu tau1muj; right => /=.
have{Dmu} defIW2 l: l != 0 -> pred2 j k l.
  by move=> nz_l; rewrite Dmu ?FTseqInd_TIred ?Dmu1.
have [nz_k j'k]: k != 0 /\ k != j.
  rewrite conjC_Iirr_eq0 nz_j -(inj_eq irr_inj) conjC_IirrE.
  by rewrite odd_eq_conj_irr1 ?mFT_odd ?irr_eq1.
have /eqP p3: p == 3.
  rewrite -nirrW2 (cardD1 0) (cardD1 j) (cardD1 k) !inE nz_j nz_k j'k !eqSS.
  by apply/pred0Pn=> [[l /and4P[k'l j'l /defIW2/norP[]]]].
have Dk: k = - j.
  have [] // := pred2P (defIW2 (- j) _); rewrite ?oppr_eq0 //.
  case/esym/eqP/idPn; rewrite -addr_eq0 -mulr2n Zp_mulrn -val_eqE /=.
  by rewrite [_ == _]Gauss_dvdl /dvdn ?modZp // coprimen2 NirrW2 mFT_odd.
split=> // _ /defIW2/pred2P[]->; first by rewrite -Dk.
have [[[Itau1 _] _] [d t1muk Dd]] := (cohS, tau1mu k nz_k); move: Dd t1muk.
case=> [][-> ->] => [|_]; rewrite ?signrN delta1 ?scaleNr scale1r; last first.
  by rewrite conjC_IirrK Dk opprK.
case/(congr1 (cfdotr (tau1 (mu_ j)) \o -%R))/eqP/idPn => /=.
rewrite -tau1muj cfdotNl eq_sym !Itau1 ?mem_zchar ?FTseqInd_TIred //.
by rewrite !cfdot_prTIred (negPf j'k) eqxx mul1n oppr0 neq0CG.
(* alternative ending
have [_ Dtau] := cohS; rewrite -[mu_ k](subrK (mu_ j)) raddfD Dtau; last first.
  by rewrite zcharD1E !cfunE !Dmu1 ?subrr ?rpredB //= mem_zchar ?FTseqInd_TIred.
rewrite tau1muj addrC; apply: canLR (addKr _) _; rewrite -!sumrB linear_sum /=.
apply: eq_bigr => i _; rewrite -[tau]/(Dade pddS) prDade_sub_TIirr //.
  by rewrite delta1 scale1r Dk opprK.
by apply: (mulfI (neq0CG W1)); rewrite 2!prTIirr_1 -!prTIred_1 !Dmu1.
*)
Qed.

End Thirteen_2_3_5_8.

End Thirteen.
