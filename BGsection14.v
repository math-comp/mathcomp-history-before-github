(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection12 BGsection13.

(******************************************************************************)
(*   This file covers B & G, section 14, starting with the definition of the  *)
(* sigma-decomposition of elements, sigma-supergroups, and basic categories   *)
(* of maximal subgroups:                                                      *)
(* sigma_decomposition x == the set of nontrivial constituents x.`_\sigma(M), *)
(*                          with M ranging over maximal sugroups of G.        *)
(*                          (x is the product of these).                      *)
(*        \ell_\sigma[x] == #|sigma_decomposition x|.                         *)
(*          'M_\sigma(X) == the set of maximal subgroups M such that X is a   *)
(*                          a subset of M`_\sigma.                            *)
(*          'M_\sigma[x] := `M_\sigma([set x])                                *)
(*             \kappa(M) == the set of primes p in \tau1(M) or \tau3(M), such *)
(*                          that 'C_(M`_\sigma)(P) != 1 for some subgroup of  *)
(*                          M of order p, i.e., the primes for which M fails  *)
(*                          to be a Frobenius group.                          *)
(*                 'M_'F == the set of maximal groups M for which \kappa(M)   *)
(*                          is empty, i.e., the maximal groups of Frobenius   *)
(*                          type (in the final classification, this becomes   *)
(*                          Type_I).                                          *)
(*                 'M_'P == the complement to 'M_'F in 'M, i.e., the set of M *)
(*                          for which at least E1 has a proper prime action   *)
(*                          on M`_\sigma.                                     *)
(*                'M_'P1 == the set of maximal subgroups M such that \pi(M)   *)
(*                          is the disjoint union of \sigma(M) and \kappa(M), *)
(*                          i.e., for which the entire complement acts in a   *)
(*                          prime manner (this is a subset of 'M_'P, which    *)
(*                          becomes the troublesome Type_V in the final       *)
(*                          classification).                                  *)
(*                'M_'P2 == the complement to 'M_'P1 in 'M_'P; this subset is *)
(*                          ultimately refined into Types II-IV in the final  *)
(*                          classification.                                   *)
(*                 'N[x] == if x != 1, some element of 'M('C[x]); actually    *)
(*                          if 'M_\sigma[x] > 1, then we will have (Theorem   *)
(*                          14.4), 'M('C[x]) = [set 'N[x]], and otherwise     *)
(*                          we take 'M_\sigma[x] = [set 'N[x]].               *)
(*                 'R[x] == if \ell_\sigma[x] = 1, the normal Hall subgroup   *)
(*                          of 'C[x] that acts sharply transitively by group  *)
(*                          conjugagtion on 'M`_\sigma[x] -- that is, a       *)
(*                          complement in 'C[x] to any M \in 'M`_\sigma[x].   *)
(*                          By Theorem 14.4, we can take 'R[x] is to be       *)
(*                          either 1 or 'C_('N[x]`_\sigma)[x].                *)
(* It seems 'R[x] and 'N[x]`_\sigma play a somewhat the role of a signalizer  *)
(* functor in the FT proof; in particular 'R[x] will be used to construct the *)
(* Dade isometry in the character theory part of the proof.                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Definitons.

Variable gT : minSimpleOddGroupType.
Implicit Type x : gT.
Implicit Type M X : {set gT}.

Definition sigma_decomposition x :=
  [set x.`_\sigma(M : {group gT}) | M <- 'M]^#.
Definition sigma_length x := #|sigma_decomposition x|.

Definition sigma_mmax_of X := [set M \in 'M | X \subset M`_\sigma].

Definition mFT_signalizer_base x :=
  let Ms_x := sigma_mmax_of [set x] in
  let set_of_N := if #|Ms_x| > 1 then 'M('C[x]) else Ms_x in
  odflt (odflt 1%G (pick (mem 'M))) (pick (mem set_of_N)).

Definition mFT_signalizer x :=
  let N := mFT_signalizer_base x in
  if #|sigma_mmax_of [set x]| > 1 then 'C_(N`_\sigma)[x]%G else 1%G.

Definition kappa M  :=
  locked [pred p \in [predU \tau1(M) & \tau3(M)] | 
    existsb P, (P \in 'E_p^1(M)) && ('C_(M`_\sigma)(P) != 1)].

Definition TypeF_maxgroups := [set M \in 'M | (kappa M)^'.-group M].

Definition TypeP_maxgroups := 'M :\: TypeF_maxgroups.

Definition TypeP1_maxgroups :=
  [set M \in TypeP_maxgroups | [predU \sigma(M) & kappa M].-group M].

Definition TypeP2_maxgroups := TypeP_maxgroups :\: TypeP1_maxgroups.

End Definitons.

Notation "\ell_ \sigma ( x )" := (sigma_length x)
  (at level 8, format "\ell_ \sigma ( x )") : group_scope.

Notation "''M_' \sigma ( X )" := (sigma_mmax_of X)
  (at level 8, format "''M_' \sigma ( X )") : group_scope.

Notation "''M_' \sigma [ x ]" := (sigma_mmax_of [set x])
  (at level 8, format "''M_' \sigma [ x ]") : group_scope.

Notation "''N' [ x ]" := (mFT_signalizer_base x)
  (at level 8, format "''N' [ x ]") : group_scope.

Notation "''R' [ x ]" := (mFT_signalizer x)
  (at level 8, format "''R' [ x ]") : group_scope.

Notation "\kappa ( M )" := (kappa M)
  (at level 8, format "\kappa ( M )") : group_scope.

Notation "''M_' ''F'" := (TypeF_maxgroups _)
  (at level 2, format "''M_' ''F'") : group_scope.

Notation "''M_' ''P'" := (TypeP_maxgroups _)
  (at level 2, format "''M_' ''P'") : group_scope.

Notation "''M_' ''P1'" := (TypeP1_maxgroups _)
  (at level 2, format "''M_' ''P1'") : group_scope.

Notation "''M_' ''P2'" := (TypeP2_maxgroups _)
  (at level 2, format "''M_' ''P2'") : group_scope.

Section Section14.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

(* Basic properties of the sigma decomposition. *)
Lemma mem_sigma_decomposition : forall x M (xM := x.`_\sigma(M)),
  M \in 'M -> xM != 1 -> xM \in sigma_decomposition x.
Proof. move=> x M xM maxM nt_xM; rewrite !inE nt_xM; exact: mem_imset. Qed.

Lemma sigma_decomposition_constt' : forall x M (sM := \sigma(M)),
  M \in 'M -> sigma_decomposition x.`_sM^' = sigma_decomposition x :\ x.`_sM.
Proof.
move=> x M sM maxM; apply/setP=> y; rewrite !inE andbCA.
apply: andb_id2l => nty; apply/imsetP/andP=> [[L maxL def_y] | [neq_y_xM]].
  have not_sMy: ~~ sM.-elt y.
    apply: contra nty => sMy; rewrite -order_eq1 (pnat_1 sMy) // def_y.
    apply: p_eltX; exact: p_elt_constt.
  split; first by apply: contraNneq not_sMy => ->; exact: p_elt_constt.
  have notMGL: gval L \notin M :^: G.
    apply: contra not_sMy; rewrite def_y; case/imsetP=> z _ ->.
    by rewrite (eq_constt _ (sigmaJ M z)) p_elt_constt.
  apply/imsetP; exists L; rewrite // def_y sub_in_constt // => p _ sLp.
  by apply: contraFN (sigma_partition maxM maxL notMGL p) => sMp; exact/andP.
case/imsetP=> L maxL def_y; exists L; rewrite ?sub_in_constt // => p _ sLp.
suffices notMGL: gval L \notin M :^: G.
  by apply: contraFN (sigma_partition maxM maxL notMGL p) => sMp; exact/andP.
apply: contra neq_y_xM; rewrite def_y; case/imsetP=> z _ ->.
by rewrite (eq_constt _ (sigmaJ M z)).
Qed.

(* General remarks about the sigma-decomposition, p. 105 of B & G. *)
Remark sigma_mmax_exists : forall p,
  p \in \pi(G) -> {M : {group gT} | M \in 'M & p \in \sigma(M)}.
Proof.
move=> p piGp; have [P sylP] := Sylow_exists p [set: gT].
have ntP: P :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylP) p_rank_gt0.
have ltPG: P \proper G := mFT_pgroup_proper (pHall_pgroup sylP).
have [M maxNM] := mmax_exists (mFT_norm_proper ntP ltPG).
have{maxNM} [maxM sNM] := setIdP maxNM; have sPM := subset_trans (normG P) sNM.
have{sylP} sylP := pHall_subl sPM (subsetT M) sylP.
by exists M => //; apply/exists_inP; exists P.
Qed.

Lemma ell_sigma0P : forall x, reflect (x = 1) (\ell_\sigma(x) == 0).
Proof.
move=> x; rewrite cards_eq0 setD_eq0.
apply: (iffP idP) => [x1 | ->]; last first.
  by apply/subsetP=> y; case/imsetP=> M _ ->; rewrite constt1 inE.
rewrite -(prod_constt x) big1_seq //= => p _; apply: contraTeq x1 => nt_xp.
have piXp: p \in \pi(#[x]) by rewrite -p_part_gt1 -order_constt order_gt1.
have [M maxM sMp] := sigma_mmax_exists (piSg (subsetT _) piXp).
apply/subsetPn; exists (x.`_(\sigma(M))); first exact: mem_imset.
by rewrite (sameP set1P constt1P); apply: contraL sMp; move/pnatPpi; exact.
Qed.

Remark sigma_decomposition_subG : forall x H,
  x \in H -> sigma_decomposition x \subset H.
Proof.
move=> x H Hx; apply/subsetP=> y; case/setD1P=> _; case/imsetP=> M _ ->{y}.
exact: groupX.
Qed.

Remark prod_sigma_decomposition : forall x,
  \prod_(x_sM \in sigma_decomposition x) x_sM = x.
Proof.
move=> x; rewrite -big_filter filter_index_enum; set e := enum _.
have: uniq e := enum_uniq _; have: e =i sigma_decomposition x := mem_enum _.
elim: {x}e (x) => [|y e IHe] x def_e /= Ue.
  by rewrite big_nil (ell_sigma0P x _) //; apply/pred0P; exact: fsym.
have{Ue} [not_e_y Ue] := andP Ue.
have [nty] := setD1P (etrans (fsym def_e y) (mem_head _ _)).
case/imsetP=> M maxM def_y; rewrite big_cons -(consttC \sigma(M) x) -def_y.
congr (y * _); apply: IHe Ue => z; rewrite sigma_decomposition_constt' //.
rewrite -def_y inE -def_e !inE andb_orr andNb.
by symmetry; apply: andb_idl; apply: contraTneq => ->.
Qed.

Remark ell_sigma_le1P : forall x,
  reflect ('M_\sigma[x] != set0) (\ell_\sigma(x) <= 1).
Proof.
move=> x; rewrite -[_ <= 1](mem_iota 0 2) !inE.
case: ell_sigma0P => [-> |].
  have [M] := mmax_exists (mFT_pgroup_proper (@pgroup1 gT 2)).
  by case/setIdP=> maxM _; left; apply/set0Pn; exists M; rewrite inE maxM sub1G.
move/eqP=> ntx; apply: (iffP cards1P) => [[y def_y] | ].
  have{y def_y}: x \in sigma_decomposition x.
    by rewrite -{1}(prod_sigma_decomposition x) def_y big_set1 set11.
  case/setD1P=> _; case/imsetP=> M maxM def_x.
  have [|] := sigma_Jsub maxM (p_elt_constt _ x); rewrite -def_x ?cycle_eq1 //.
  case=> z sXzMs _; apply/set0Pn; exists (M :^ z^-1)%G.
  by rewrite inE mmaxJ maxM MsigmaJ -gen_subG -sub_conjg.
case/set0Pn=> M; case/setIdP=> maxM; rewrite sub1set => Ms_x.
have sMx: \sigma(M).-elt x := mem_p_elt (pcore_pgroup _ _) Ms_x.
have def_xM: x.`_(\sigma(M)) = x := constt_p_elt sMx.
exists x; apply/eqP; rewrite eqEsubset sub1set !inE ntx -setD_eq0 /=.
rewrite -{2 3}def_xM -sigma_decomposition_constt' // (constt1P _) ?p_eltNK //.
by rewrite -cards_eq0 (sameP (ell_sigma0P 1) eqP) eqxx; exact: mem_imset.
Qed.

(* Basic properties of \kappa and the maximal group subclasses. *)
Lemma kappaJ : forall M x, \kappa(M :^ x) =i \kappa(M).
Proof.
move=> M x p; unlock kappa; rewrite 3!{1}inE /= tau1J tau3J.
apply: andb_id2l => _; apply/exists_inP/exists_inP=> [] [P EpP ntCMsP].
  rewrite -(conjsgK x M); exists (P :^ x^-1)%G; first by rewrite pnElemJ.
  by rewrite MsigmaJ centJ -conjIg -subG1 sub_conjg conjs1g subG1.
exists (P :^ x)%G; first by rewrite pnElemJ.
by rewrite MsigmaJ centJ -conjIg -subG1 sub_conjg conjs1g subG1.
Qed.

Lemma kappa_tau13 : forall M p,
  p \in \kappa(M) -> (p \in \tau1(M)) || (p \in \tau3(M)).
Proof. by unlock kappa => M p; case/andP. Qed.

Lemma kappa_sigma' : forall M, {subset \kappa(M) <= \sigma(M)^'}.
Proof. by move=> M p; move/kappa_tau13; case/orP; case/andP. Qed.

Remark rank_kappa : forall M p, p \in \kappa(M) -> 'r_p(M) = 1%N.
Proof. by move=> M p; move/kappa_tau13; case/orP; case/and3P=> _; move/eqP. Qed.

Lemma kappa_pi : forall M, {subset \kappa(M) <= \pi(M)}.
Proof. by move=> M p kMp; rewrite -p_rank_gt0 rank_kappa. Qed.

Remark kappa_nonregular : forall M p P,
  p \in \kappa(M) -> P \in 'E_p^1(M) -> 'C_(M`_\sigma)(P) != 1.
Proof.
move=> M p P kMp EpP; have rpM := rank_kappa kMp.
have [sPM abelP oP] := pnElemPcard EpP; have [pP _] := andP abelP.
have [Q EpQ nregQ]: exists2 Q, Q \in 'E_p^1(M) & 'C_(M`_\sigma)(Q) != 1.
  by apply/exists_inP; unlock kappa in kMp; case/andP: kMp.
have [sQM abelQ oQ] := pnElemPcard EpQ; have [pQ _] := andP abelQ.
have [S sylS sQS] := Sylow_superset sQM pQ; have [_ pS _] := and3P sylS.
have [x Mx sPxS] := Sylow_Jsub sylS sPM pP.
rewrite -(inj_eq (@conjsg_inj _ x)) conjs1g conjIg -centJ.
rewrite (normsP (normal_norm (pcore_normal _ _))) // (subG1_contra _ nregQ) //.
rewrite setIS ?centS // -(cardSg_cyclic _ sPxS sQS) ?cardJg ?oP ?oQ //.
by rewrite (odd_pgroup_rank1_cyclic pS) ?mFT_odd // (p_rank_Sylow sylS) rpM.
Qed.

Lemma mmaxF_P : forall M,
  reflect (M \in 'M /\ \kappa(M) =i pred0) (M \in 'M_'F).
Proof.
move=> M; do [apply: (iffP setIdP) => [] [maxM k'M]; split] => // [p|].
  by apply/idP=> /= kMp; case/negP: (pnatPpi k'M (kappa_pi kMp)).
by apply/pgroupP=> p _ _; rewrite inE /= k'M.
Qed.

Lemma mmaxP_P : forall M,
  reflect (M \in 'M /\ exists p, p \in \kappa(M)) (M \in 'M_'P).
Proof.
move=> M; apply: (iffP setDP) => [[maxM kM] | [maxM [p kMp]]]; split => //.
  rewrite inE maxM !negb_and cardG_gt0 /= all_predC negbK in kM.
  by have [p _ kMp] := hasP kM; exists p.
by apply/mmaxF_P=> [[_ kM0]]; rewrite kM0 in kMp.
Qed.

(* This is B & G, Lemma 14.1. *)
Lemma sigma'_kappa'_facts : forall M p S (A := 'Ohm_1(S)) (Ms := M`_\sigma),
    M \in 'M -> p.-Sylow(M) S ->
   [&& p \in \pi(M), p \notin \sigma(M) & p \notin \kappa(M)] -> 
 [/\ M \in 'M_'F :|: 'M_'P2, logn p #|A| <= 2, 'C_Ms(A) = 1 & nilpotent Ms].
Proof.
move=> M p S A Ms maxM sylS; case/and3P=> piMp sM'p kM'p.
have [sSM pS _] := and3P sylS.
rewrite 8!(maxM, inE) /= !andbT negb_and orb_andr orbN andbT negbK.
rewrite (contra (fun skM => pnatPpi skM piMp)) ?orbT; last exact/norP.
rewrite partition_pi_mmax // (negPf sM'p) orbF orbCA in piMp.
have{piMp} [t2p | t13p] := orP piMp.
  rewrite (tau2_Msigma_nil maxM t2p); have [_ rpM] := andP t2p.
  have{rpM} rS: 2 <= 'r_p(S) by rewrite (p_rank_Sylow sylS) (eqP rpM).
  have [B EpB] := p_rank_geP rS; have{EpB} [sBS abelB dimB] := pnElemP EpB.
  have EpB: B \in 'E_p^2(M) by rewrite !inE abelB dimB (subset_trans sBS).
  have [defB _ regB _ _] := tau2_context maxM t2p EpB.
  by rewrite /A -dimB; have [_ [|->]] := defB S sylS.
have [ntS cycS]: S :!=: 1 /\ cyclic S.
  rewrite (odd_pgroup_rank1_cyclic pS) ?mFT_odd // (p_rank_Sylow sylS).
  apply/andP; rewrite -rank_gt0 (rank_Sylow sylS) -eqn_leq eq_sym.
  by rewrite -2!andb_orr orNb andbT inE /= sM'p in t13p.
have [p_pr _ _] := pgroup_pdiv pS ntS.
have oA: #|A| = p by rewrite (Ohm1_cyclic_pgroup_prime cycS pS).
have sAM: A \subset M := subset_trans (Ohm_sub 1 S) sSM.
have regA: 'C_Ms(A) = 1.
  apply: contraNeq kM'p => nregA; unlock kappa; apply/andP; split=> //.
  by apply/exists_inP; exists [group of A]; rewrite ?p1ElemE // !inE sAM oA /=.
have defMsA: Ms ><| A = Ms <*> A.
  rewrite sdprodEY ?coprime_TIg ?(subset_trans sAM) ?bgFunc_norm // oA.
  by rewrite (pnat_coprime (pcore_pgroup _ _)) ?pnatE.
rewrite (prime_Frobenius_sol_kernel_nil defMsA) ?oA ?(pfactorK 1) //.
by rewrite (solvableS _ (mmax_sol maxM)) // join_subG pcore_sub.
Qed.

(* This is B & G, Proposition 14.2. *)
Proposition Ptype_structure : forall M K (Ms := M`_\sigma) (Kstar := 'C_Ms(K)),
  M \in 'M_'P -> \kappa(M).-Hall(M) K ->
  [/\ (*a*) exists2 U : {group gT},
              [/\ abelian U, [predU \sigma(M) & \kappa(M)]^'.-Hall(M) U
                & (U :==: 1) = (M \in 'M_'P1)]
            & [/\ semiprime Ms K, semiregular U K & Ms ><| (U ><| K) = M],
      (*b*) (*1.2*) K \x Kstar = 'N_M(K)
           /\ {in 'E^1(K), forall X, 
            (*1.1*) 'N_M(X) = 'N_M(K)
           /\ (*2*) {in 'M('N(X)), forall Mstar, X \subset Mstar`_\sigma}},
      (*c*) Kstar != 1 /\ {in 'E^1(Kstar), forall X, 'M('C(X)) = [set M]},
  [/\ (*d*) {in ~: M, forall g, Kstar :&: M :^ g = 1}
         /\ {in M :\: 'N_M(K), forall g, K :&: K :^ g = 1},
      (*e*) {in \pi(Kstar), forall p S,
             p.-Sylow(M) S -> 'M(S) = [set M] /\ ~~ (S \subset Kstar)}
    & (*f*) forall Y, \sigma(M).-group Y -> Y :&: Kstar != 1 -> Y \subset Ms]
    & (*g*) M \in 'M_'P2 ->
            [/\ \sigma(M) =i \beta(M), prime #|K|, nilpotent Ms
                & trivIset (Ms^# :^: G)]].
Proof.
move=> M K Ms Ks PmaxM hallK; have [maxM notFmaxM] := setDP PmaxM.
have{notFmaxM} ntK: K :!=: 1.
  apply: contra notFmaxM; rewrite inE maxM trivg_card1 (card_Hall hallK).
  by rewrite partG_eq1.
have [sKM kK _] := and3P hallK; have s'K := sub_pgroup (@kappa_sigma' M) kK.
have solM := mmax_sol maxM; have [E hallE sKE] := Hall_superset solM sKM s'K.
have [[sEM s'E _] [_ [E3 hallE3]]] := (and3P hallE, ex_tau13_compl hallE).
have [F1 hallF1] := Hall_exists \tau1(M) (solvableS sKM solM).
have [[sF1K t1F1 _] solE] := (and3P hallF1, sigma_compl_sol hallE).
have [E1 hallE1 sFE1] := Hall_superset solE (subset_trans sF1K sKE) t1F1.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [[_ nsE3E] _ [cycE1 _] [defEl defE] _] := sigma_compl_context maxM complEi.
have [sE1E t1E1 _] := and3P hallE1; have sE1M := subset_trans sE1E sEM.
have [sE3E t3E3 _] := and3P hallE3; have sE3M := subset_trans sE3E sEM.
set part_a := exists2 U, _ & _; pose b1_hyp := {in 'E^1(K), forall X, X <| K}.
have [have_a nK1K ntE1 sE1K]: [/\ part_a, b1_hyp, E1 :!=: 1 & E1 \subset K].
  have [t1K | not_t1K] := boolP (\tau1(M).-group K).
    have sKE1: K \subset E1 by rewrite (sub_pHall hallF1 t1K).
    have prE1 := tau1_primact_Msigma maxM hallE hallE1.
    have st1k: {subset \tau1(M) <= \kappa(M)}.
      move=> p t1p; rewrite /kappa -lock 3!inE /= t1p /=.
      have [X]: exists X, X \in 'E_p^1(E1).
        apply/p_rank_geP; rewrite p_rank_gt0 /= (card_Hall hallE1).
        by rewrite pi_of_partn // inE /= (partition_pi_sigma_compl maxM) ?t1p.
      rewrite -(setIidPr sE1M) pnElemI -setIdE; case/setIdP=> EpX sXE1.
      pose q := pdiv #|K|; have piKq: q \in \pi(K) by rewrite pi_pdiv cardG_gt1.
      have [Y]: exists Y, Y \in 'E_q^1(K).
        by apply/p_rank_geP; rewrite p_rank_gt0.
      rewrite -(setIidPr sKM) pnElemI -setIdE; case/setIdP=> EqY sYK.
      have ntCMsY := kappa_nonregular (pnatPpi kK piKq) EqY.
      have [ntY sYE1] := (nt_pnElem EqY isT, subset_trans sYK sKE1).
      apply/exists_inP; exists X; rewrite ?(subG1_contra _ ntCMsY) //=.
      by rewrite (cent_semiprime prE1 sYE1 ntY) ?setIS ?centS.
    have defK := sub_pHall hallK (sub_pgroup st1k t1E1) sKE1 sE1M.
    split=> [|X||]; rewrite ?defK //; last first.
       rewrite -defK; case/nElemP=> p; case/pnElemP=> sXE1 _ _.
       by rewrite char_normal // sub_cyclic_char.
    have [[U _ defU _] _ _ _] := sdprodP defE; rewrite defU in defE.
    have [nsUE _ mulUE1 nUE1 _] := sdprod_context defE.
    have [[_ V _ defV] _] := sdprodP defEl; rewrite defV.
    have [_ <- nE21 _] := sdprodP defV; case/mulGsubP=> nE32 nE31 _.
    have regUK: semiregular U K.
      move=> y; case/setD1P; rewrite -cycle_subG -cent_cycle -order_gt1.
      rewrite -pi_pdiv; move: (pdiv _) => p pi_y_p Ky.
      have piKp := piSg Ky pi_y_p; have t1p := pnatPpi t1K piKp.
      move: pi_y_p; rewrite -p_rank_gt0; case/p_rank_geP=> Y /=.
      rewrite -{1}(setIidPr (subset_trans Ky sKE)) pnElemI -setIdE.
      case/setIdP=> EpY sYy; have EpMY := subsetP (pnElemS _ _ sEM) Y EpY.
      apply: contraNeq (kappa_nonregular (pnatPpi kK piKp) EpMY).
      move/(subG1_contra (setIS U (centS sYy))).
      have{y sYy Ky} sYE1 := subset_trans sYy (subset_trans Ky sKE1).
      have ntY: Y :!=: 1 by exact: (nt_pnElem EpY). 
      rewrite -subG1 /=; have [_ <- _ tiE32] := sdprodP defU.
      rewrite -subcent_TImulg ?subsetI ?(subset_trans sYE1) // mulG_subG.
      rewrite !subG1 /=; case/nandP=> [nregE3Y | nregE2Y].
        have pr13 := (cent_semiprime (tau13_primact_Msigma maxM complEi _)).
        rewrite pr13 ?(subset_trans sYE1) ?joing_subr //; last first.
          by move/cent_semiregular=> regE31; rewrite regE31 ?eqxx in nregE3Y.
        pose q := pdiv #|'C_E3(Y)|.
        have piE3q: q \in \pi(E3).
          by rewrite (piSg (subsetIl E3 'C(Y))) // pi_pdiv cardG_gt1.
        have [X]: exists X, X \in 'E_q^1(M :&: E3).
          by apply/p_rank_geP; rewrite /= (setIidPr sE3M) p_rank_gt0.
        rewrite pnElemI -setIdE; case/setIdP=> EqX sXE3.
        rewrite -subG1 -(_ : 'C_Ms(X) = 1) ?setIS ?centS //.
          by rewrite (subset_trans sXE3) ?joing_subl.
        apply: contraTeq (pnatPpi t3E3 piE3q) => nregMsX; apply: tau3'1.
        suffices kq: q \in \kappa(M).
          rewrite (pnatPpi t1K) //= (card_Hall hallK) pi_of_partn //.
          by rewrite inE /= kappa_pi.
        rewrite /kappa -lock 3!inE /= (pnatPpi t3E3 piE3q) orbT /=.
        by apply/exists_inP; exists X.
      pose q := pdiv #|'C_E2(Y)|; have [sE2E t2E2 _] := and3P hallE2.
      have piCE2Yq: q \in \pi('C_E2(Y)) by rewrite pi_pdiv cardG_gt1.
      have [X]: exists X, X \in 'E_q^1(E :&: 'C_E2(Y)).
        by apply/p_rank_geP; rewrite /= setIA (setIidPr sE2E) p_rank_gt0.
      rewrite pnElemI -setIdE; case/setIdP=> EqX sXcE2Y.
      have t2q:= pnatPpi t2E2 (piSg (subsetIl _ _) piCE2Yq).
      have [A Eq2A _] := ex_tau2Elem hallE t2q.
      have [[_ defEq1] _ _ _] := tau2_compl_context maxM hallE t2q Eq2A.
      rewrite (tau12_regular maxM hallE t1p EpY t2q Eq2A) //.
      rewrite (subG1_contra _ (nt_pnElem EqX _)) // subsetI.
      rewrite defEq1 in EqX; case/pnElemP: EqX => -> _ _.
      by rewrite (subset_trans sXcE2Y) ?subsetIr.
    have [defM [sUE _]] := (sdprod_sigma maxM hallE, andP nsUE).
    exists U; last by rewrite -{1 3}defK defE.
    have hallU: [predU \sigma(M) & \kappa(M)]^'.-Hall(M) U.
      suffices: [predI \sigma(M)^' & \kappa(M)^'].-Hall(M) U.
        by apply: etrans; apply: eq_pHall=> p; rewrite inE /= negb_or.
      apply: subHall_Hall hallE _ _ => [p|]; first by case/andP.
      rewrite pHallE partnI (part_pnat_id s'E) -pHallE.
      apply/(sdprod_normal_pHallP nsUE (pHall_subl sKE sEM hallK)).
      by rewrite -defK.
    split=> //; last first.
      by rewrite inE PmaxM trivg_card1 (card_Hall hallU) partG_eq1 pgroupNK.
    apply: abelianS (der_mmax_compl_abelian maxM hallE).
    rewrite -(coprime_cent_prod nUE1) ?(solvableS sUE) //.
      by rewrite {2}defK (cent_semiregular regUK) // mulg1 commgSS.
    rewrite (coprime_sdprod_Hall defE) (sdprod_Hall defE).
    exact: pHall_Hall hallE1.
  move: not_t1K; rewrite negb_and cardG_gt0 -has_predC; case/hasP=> p piKp t1'p.
  have kp := pnatPpi kK piKp; have t3p := kappa_tau13 kp.
  rewrite [p \in _](negPf t1'p) /= in t3p.
  have [X]: exists X, X \in 'E_p^1(K) by apply/p_rank_geP; rewrite p_rank_gt0.
  rewrite -{1}(setIidPr sKM) pnElemI -setIdE; case/setIdP=> EpX sXK.
  have sXE3: X \subset E3.
    rewrite (sub_normal_Hall hallE3) ?(subset_trans sXK) ?(pi_pgroup _ t3p) //.
    by case/pnElemP: EpX => _; case/andP.
  have [nregX ntX] := (kappa_nonregular kp EpX, nt_pnElem EpX isT).
  have [regE3|ntE1 {defE}defE prE nE1_E] := tau13_nonregular maxM complEi.
    by case/eqP: nregX; rewrite (cent_semiregular regE3).
  have defK: E :=: K.
    apply: (sub_pHall hallK _ sKE sEM); apply/pgroupP=> q q_pr q_dv_E.
    have{q_dv_E} piEq: q \in \pi(E) by rewrite mem_primes q_pr cardG_gt0.
    unlock kappa; apply/andP; split=> /=.
      apply: pnatPpi piEq; rewrite -pgroupE; case/sdprodP: defE => _ <- _ _.
      rewrite pgroupM (sub_pgroup _ t3E3) => [|r t3r]; last by apply/orP; right.
      by rewrite (sub_pgroup _ t1E1) // => r t1r; apply/orP; left.
    have:= piEq; rewrite -p_rank_gt0; case/p_rank_geP=> Y.
    rewrite -{1}(setIidPr sEM) pnElemI -setIdE; case/setIdP=> EqY sYE.
    rewrite (cent_semiprime prE) ?(subset_trans sXK) // in nregX.
    apply/exists_inP; exists Y => //; apply: subG1_contra nregX.
    by rewrite setIS ?centS.
  have defM := sdprod_sigma maxM hallE.
  rewrite /b1_hyp -defK; split=> //; exists 1%G; last first.
    by rewrite -defK sdprod1g //; split=> //; exact: semiregular1l.
  rewrite abelian1 eqxx inE PmaxM pHallE sub1G cards1 eq_sym.
  rewrite partG_eq1 pgroupNK /=; have{defM} [_ defM _ _] := sdprodP defM.
  rewrite -{3 6}defM defK pgroupM.
  rewrite (sub_pgroup _ (pcore_pgroup _ _)) => [|r sr]; last by apply/orP; left.
  by rewrite (sub_pgroup _ kK) // => r kr; apply/orP; right.
set part_b := _ /\ _; set part_c := _ /\ _; set part_d := _ /\ _.
have [U [cUU hallU defP1M] [prMsK regUK defM]] := have_a.
have have_b: part_b.
  set MsU := Ms <*> U; have [sUM sk'U _] := and3P hallU.
  have coMsU: coprime #|Ms| #|U|.
    rewrite (pnat_coprime (pcore_pgroup _ _) (sub_pgroup _ sk'U)) // => p.
    by case/norP.
  have{defM} [[_ F _ defF]] := sdprodP defM; rewrite defF.
  have [_ <- nUK _] := sdprodP defF; rewrite mulgA mulG_subG => defM.
  case/andP=> nMsU nMsK _.
  have coMsU_K: coprime #|MsU| #|K|.
    rewrite [MsU]norm_joinEr // (p'nat_coprime _ kK) // -pgroupE.
    rewrite pgroupM // (sub_pgroup _ (pcore_pgroup _ _)) => [|r]; last first.
      by apply: contraL; exact: kappa_sigma'.
    by apply: sub_pgroup _ sk'U => r; case/norP.
  have defNK: forall X, X <| K -> X :!=: 1 -> 'N_M(X) = Ks * K.
    move=> X; case/andP=> sXK nXK ntX; rewrite -defM -(norm_joinEr nMsU) -/MsU.
    rewrite setIC -group_modr // setIC.
    rewrite coprime_norm_cent ?(subset_trans sXK) ?normsY //; last first.
      by rewrite (coprimegS sXK).
    rewrite /= norm_joinEr -?subcent_TImulg ?(coprime_TIg coMsU) //; last first.
      by rewrite subsetI !(subset_trans sXK).
    by rewrite (cent_semiregular regUK) // mulg1 (cent_semiprime prMsK).
  rewrite /part_b dprodE ?subsetIr //; last first.
    rewrite setICA setIA (coprime_TIg (coprimeSg _ coMsU_K)) ?setI1g //.
    by rewrite joing_subl.
  rewrite -centC ?subsetIr // defNK //; split=> // X Eq1X.
  have [q EqX] := nElemP Eq1X; have ntX := nt_pnElem EqX isT.
  have:= EqX; rewrite -{1}(setIidPr sKE) pnElemI -setIdE.
  case/setIdP=> EqEX sXK; split; first by rewrite defNK ?nK1K.
  have [_ abelX dimX] := pnElemP EqX; have [qX _] := andP abelX.
  have kq: q \in \kappa(M).
    by rewrite (pnatPpi kK (piSg sXK _)) // -p_rank_gt0 p_rank_abelem ?dimX.
  have nregX := kappa_nonregular kq (subsetP (pnElemS _ _ sEM) _ EqEX).
  have sq := tau13_nonregular_sigma maxM hallE EqEX (kappa_tau13 kq) nregX.
  move=> H maxNH; have [maxH sNXH] := setIdP maxNH.
  rewrite (sub_Hall_pcore (Msigma_Hall maxH)) ?(subset_trans (normG X)) //.
  exact: pi_pgroup qX (sq H maxNH).
have have_c: part_c.
  pose p := pdiv #|E1|; have piE1p: p \in \pi(E1) by rewrite pi_pdiv cardG_gt1.
  have:= piE1p; rewrite -p_rank_gt0; case/p_rank_geP=> Y.
  rewrite -(setIidPr sE1M) pnElemI -setIdE; case/setIdP=> EpY sYE1.
  have [sYK ntY] := (subset_trans sYE1 sE1K, nt_pnElem EpY isT).
  split=> [|X].
    rewrite /Ks -(cent_semiprime prMsK sYK) //.
    exact: kappa_nonregular (pnatPpi kK (piSg sE1K piE1p)) EpY.
  case/nElemP=> q; rewrite /= -(cent_semiprime prMsK sYK) // => EqX.
  by have [] := cent_cent_Msigma_tau1_uniq maxM hallE hallE1 sYE1 ntY EqX.
have [[defNK defK1] [_ uniqKs]] := (have_b, have_c).
have have_d: part_d.
  split=> g.
    rewrite inE; apply: contraNeq; rewrite -rank_gt0.
    case/rank_geP=> X; rewrite nElemI -setIdE; case/setIdP=> EpX sXMg.
    have [_ sCXMs] := mem_uniq_mmax (uniqKs _ EpX).
    case/nElemP: EpX => p; case/pnElemP; case/subsetIP=> sXMs _ abelX dimX.
    have [[pX _] sXM] := (andP abelX, subset_trans sXMs (pcore_sub _ _)).
    have piXp: p \in \pi(X) by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
    have sp := pnatPpi (pcore_pgroup _ _) (piSg sXMs piXp).
    have [def_g _ _] := sigma_group_trans maxM sp pX.
    rewrite -groupV; have [|c cXc [m Mm ->]] := def_g g^-1 sXM.
      by rewrite sub_conjgV.
    by rewrite groupM // (subsetP sCXMs).
  case/setDP=> Mg; apply: contraNeq; rewrite -rank_gt0 /=.
  case/rank_geP=> X; rewrite nElemI -setIdE; case/setIdP=> EpX sXKg.
  have [<- _] := defK1 X EpX; rewrite 2!inE Mg /=.
  have{EpX} [p EpX] := nElemP EpX; have [_ abelX dimX] := pnElemP EpX.
  have defKp1: {in 'E_p^1(K), forall Y, 'Ohm_1('O_p(K)) = Y}.
    move=> Y EpY; have E1K_Y: Y \in 'E^1(K) by apply/nElemP; exists p.
    have piKp: p \in \pi(K) by rewrite -p_rank_gt0; apply/p_rank_geP; exists Y.
    have [pKp sKpK] := (pcore_pgroup p K, pcore_sub p K).
    have cycKp: cyclic 'O_p(K).
      rewrite (odd_pgroup_rank1_cyclic pKp) ?mFT_odd //.
      by rewrite -(rank_kappa (pnatPpi kK piKp)) p_rankS ?(subset_trans sKpK).
    have [sYK abelY oY] := pnElemPcard EpY; have [pY _] := andP abelY.
    have sYKp: Y \subset 'O_p(K) by rewrite pcore_max ?nK1K.
    apply/eqP; rewrite eq_sym eqEcard -{1}(Ohm1_id abelY) OhmS //= oY.
    rewrite (Ohm1_cyclic_pgroup_prime cycKp pKp) ?(subG1_contra sYKp) //=.
    exact: nt_pnElem EpY _.
  rewrite sub_conjg -[X :^ _]defKp1 ?defKp1 // !inE sub_conjgV sXKg cardJg dimX.
  by rewrite abelemJ abelX.
split=> {part_a part_b part_c have_a have_b have_c}//; first split=> //.
- move=> q; rewrite /Ks -(cent_semiprime prMsK sE1K ntE1) => picMsE1q.
  have sq := pnatPpi (pcore_pgroup _ M) (piSg (subsetIl _ _) picMsE1q).
  move: picMsE1q; rewrite -p_rank_gt0; case/p_rank_geP=> y EqY S sylS.
  have [sSM qS _] := and3P sylS.
  have sSMs: S \subset M`_\sigma.
    by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup qS).
  have sylS_Ms: q.-Sylow(M`_\sigma) S := pHall_subl sSMs (pcore_sub _ M) sylS.
  have [_]:= cent_cent_Msigma_tau1_uniq maxM hallE hallE1 (subxx _) ntE1 EqY.
  move/(_ S sylS_Ms) => uniqS; split=> //; rewrite subsetI sSMs /=.
  pose p := pdiv #|E1|; have piE1p: p \in \pi(E1) by rewrite pi_pdiv cardG_gt1.
  have [s'p _] := andP (pnatPpi t1E1 piE1p).
  have [P sylP] := Sylow_exists p E1; have [sPE1 pP _] := and3P sylP.
  apply: contra (s'p) => cE1S; apply/exists_inP; exists P.
    exact: subHall_Sylow s'p (subHall_Sylow hallE1 (pnatPpi t1E1 piE1p) sylP).
  apply: (sub_uniq_mmax uniqS); first by rewrite cents_norm // (centsS sPE1).
  apply: mFT_norm_proper (mFT_pgroup_proper pP).
  by rewrite -rank_gt0 (rank_Sylow sylP) p_rank_gt0.
- move=> Y sY ntYKs; have ntY: Y :!=:1 := subG1_contra (subsetIl _ _) ntYKs.
  have [[x sYxMs] _] := sigma_Jsub maxM sY ntY; rewrite sub_conjg in sYxMs.
  suffices Mx': x^-1 \in M by rewrite (normsP _ _ Mx') ?bgFunc_norm in sYxMs.
  rewrite -(setCK M) inE; apply: contra ntYKs => M'x'.
  rewrite setIC -(setIidPr sYxMs) -/Ms -[Ms](setIidPr (pcore_sub _ _)).
  by rewrite conjIg !setIA; have [-> // _] := have_d; rewrite !setI1g.
rewrite inE PmaxM andbT -defP1M => ntU.
have [regMsU nilMs]: 'C_Ms(U) = 1 /\ nilpotent Ms.
  pose p := pdiv #|U|; have piUp: p \in \pi(U) by rewrite pi_pdiv cardG_gt1.
  have [sUM sk'U _] := and3P hallU; have sk'p := pnatPpi sk'U piUp.
  have [S sylS] := Sylow_exists p U; have [sSU _] := andP sylS.
  have sylS_M := subHall_Sylow hallU sk'p sylS.
  rewrite -(setIidPr (centS (subset_trans (Ohm_sub 1 S) sSU))) setIA.
  have [|_ _ -> ->] := sigma'_kappa'_facts maxM sylS_M; last by rewrite setI1g.
  by rewrite -negb_or (piSg sUM).
have [[_ F _ defF] _ _ _] := sdprodP defM; rewrite defF in defM.
have hallMs: \sigma(M).-Hall(M) Ms by exact: Msigma_Hall.
have hallF: \sigma(M)^'.-Hall(M) F by exact/(sdprod_Hall_pcoreP hallMs).
have frF: [Frobenius F = U ><| K] by exact/Frobenius_semiregularP.
have ntMs: Ms != 1 by exact: Msigma_neq1.
have prK: prime #|K|.
  have [solF [_ _ nMsF _]] := (sigma_compl_sol hallF, sdprodP defM).
  have solMs: solvable Ms := solvableS (pcore_sub _ _) (mmax_sol maxM).
  have coMsF: coprime #|Ms| #|F|.
    by rewrite (coprime_sdprod_Hall defM) (pHall_Hall hallMs).
  by have [] := Frobenius_primact frF solF nMsF solMs ntMs coMsF prMsK.
have eq_sb: \sigma(M) =i \beta(M).
  suffices bMs: \beta(M).-group Ms.
    move=> p; apply/idP/idP=> [sp|]; last exact: beta_sub_sigma.
    rewrite (pnatPpi bMs) //= (card_Hall (Msigma_Hall maxM)) pi_of_partn //.
    by rewrite inE /= sigma_sub_pi.
  have [H hallH cHF'] := der_compl_cent_beta' maxM hallF.
  rewrite -pgroupNK -partG_eq1 -(card_Hall hallH) -trivg_card1 -subG1.
  rewrite -regMsU subsetI (pHall_sub hallH) centsC (subset_trans _ cHF') //.
  have [solU [_ mulUK nUK _]] := (abelian_sol cUU, sdprodP defF).
  have coUK: coprime #|U| #|K|.
    rewrite (p'nat_coprime (sub_pgroup _ (pHall_pgroup hallU)) kK) // => p.
    by case/norP.
  rewrite -(coprime_cent_prod nUK) // (cent_semiregular regUK) // mulg1.
  by rewrite -mulUK commgSS ?mulG_subl ?mulG_subr.
split=> //; apply/TIconjP=> x y _ _ /=.
rewrite setTI (mmax_normal maxM (pcore_normal _ M) ntMs).
rewrite -{2}(mulgKV y x) conjsgM -conjIg; move: {x}(x * _) => g.
have [Mg | notMg] := boolP (g \in M); [by left | right].
have [_ _ b'MsMg] := sigma_compl_embedding maxM hallE.
have{b'MsMg notMg} [_ b'MsMg _] := b'MsMg g notMg.
rewrite setIC -pcoreJ -(setIidPr (pcore_sub _ _)) setIA.
rewrite (eq_pcore _ eq_sb) coprime_TIg ?conjs1g //.
exact: p'nat_coprime b'MsMg (pcore_pgroup _ _).
Qed.
                  
(* This is B & G, Corollary 14.3. *)
Corollary pi_of_cent_sigma : forall M x x',
    M \in 'M -> x \in (M`_\sigma)^# ->
    x' \in ('C_M[x])^# -> \sigma(M)^'.-elt x' ->
     (*1*)  \kappa(M).-elt x' /\ 'C[x] \subset M
  \/ (*2*) [/\ \tau2(M).-elt x', \ell_\sigma(x') = 1%N & 'M('C[x']) = [set M]].
Proof.
move=> M x y maxM; case/setD1P=> ntx Ms_x; case/setD1P=> nty cMxy s'y.
have [My cxy] := setIP cMxy.
have [t2y | not_t2y] := boolP (\tau2(M).-elt y); [right | left].
  have uniqCy: 'M('C[y]) = [set M]; last split=> //.
    apply: cent1_nreg_sigma_uniq; rewrite // ?inE ?nty //.
    by apply/trivgPn; exists x; rewrite // inE Ms_x cent1C.
  pose p := pdiv #[y]; have piYp: p \in \pi(#[y]) by rewrite pi_pdiv order_gt1.
  have t2p := pnatPpi t2y piYp; have [E hallE] := ex_sigma_compl maxM.
  have [A Ep2A _] := ex_tau2Elem hallE t2p.
  have pA: p.-group A by case/pnElemP: Ep2A => _; case/andP.
  have ntA: A :!=: 1 by rewrite (nt_pnElem Ep2A).
  have [H maxNH] := mmax_exists (mFT_norm_proper ntA (mFT_pgroup_proper pA)).
  have [st2MsH _ _] := primes_norm_tau2Elem maxM hallE t2p Ep2A maxNH.
  have [maxH _] := setIdP maxNH.
  have sHy: \sigma(H).-elt y.
    by apply: sub_p_elt t2y => q; move/st2MsH; case/andP.
  rewrite /sigma_length (cardsD1 y.`_(\sigma(H))).
  rewrite mem_sigma_decomposition //; last by rewrite constt_p_elt.
  apply/eqP; rewrite eqSS -sigma_decomposition_constt' //.
  by apply/ell_sigma0P; rewrite (constt1P _) ?p_eltNK.
have{not_t2y} [p piYp t2'p]: exists2 p, p \in \pi(#[y]) & p \notin \tau2(M).
  by apply/allPn; rewrite negb_and cardG_gt0 in not_t2y.
have sYM: <[y]> \subset M by rewrite cycle_subG.
have piMp: p \in \pi(M) := piSg sYM piYp.
have t13p: p \in [predU \tau1(M) & \tau3(M)].
  move: piMp; rewrite partition_pi_mmax // (negPf t2'p) /= orbA.
  by case/orP=> // sMy; case/negP: (pnatPpi s'y piYp).
have [X]: exists X, X \in 'E_p^1(<[y]>) by apply/p_rank_geP; rewrite p_rank_gt0.
rewrite -(setIidPr sYM) pnElemI -setIdE; case/setIdP=> EpX sXy.
have kp: p \in \kappa(M).
  unlock kappa; apply/andP; split=> //; apply/exists_inP; exists X => //.
  apply/trivgPn; exists x; rewrite // inE Ms_x (subsetP (centS sXy)) //.
  by rewrite cent_cycle cent1C.
have [sXM abelX dimX] := pnElemP EpX; have [pX _] := andP abelX.
have [K hallK sXK] := Hall_superset (mmax_sol maxM) sXM (pi_pgroup pX kp).
have PmaxM: M \in 'M_'P.
  by rewrite 2!inE maxM andbT; apply: contraL kp => k'M; exact: (pnatPpi k'M).
have [_ [defNK defNX] [_ uniqCKs] _ _] := Ptype_structure PmaxM hallK.
have{defNX} sCMy_nMK: 'C_M[y] \subset 'N_M(K).
  have [|<- _] := defNX X.
    by apply/nElemP; exists p; rewrite !inE sXK abelX dimX.
  by rewrite setIS // cents_norm // -cent_cycle centS.
have [[sMK kK _] [_ mulKKs cKKs _]] := (and3P hallK, dprodP defNK).
have s'K: \sigma(M)^'.-group K := sub_pgroup (@kappa_sigma' M) kK.
have sMs: \sigma(M).-group M`_\sigma := pcore_pgroup _ M.
have sKs: \sigma(M).-group 'C_(M`_\sigma)(K) := pgroupS (subsetIl _ _) sMs.
have{s'K sKs} [hallK_N hallKs] := coprime_mulGp_Hall mulKKs s'K sKs.
split.
  rewrite (mem_p_elt kK) // (mem_normal_Hall hallK_N) ?normal_subnorm //.
  by rewrite (subsetP sCMy_nMK) // inE My cent1id.
have Mx: x \in M := subsetP (pcore_sub _ _) x Ms_x.
have sxKs: <[x]> \subset 'C_(M`_\sigma)(K).
  rewrite cycle_subG (mem_normal_Hall hallKs) ?(mem_p_elt sMs) //=.
    by rewrite -mulKKs /normal mulG_subr mulG_subG normG cents_norm // centsC.
  by rewrite (subsetP sCMy_nMK) // inE Mx cent1C.
have [Z]: exists Z, Z \in 'E^1(<[x]>).
  by apply/rank_geP; rewrite rank_gt0 cycle_eq1.
rewrite -(setIidPr sxKs) nElemI -setIdE; case/setIdP=> E1KsZ sZx.
have [_ sCZM] := mem_uniq_mmax (uniqCKs Z E1KsZ).
by rewrite (subset_trans _ sCZM) // -cent_cycle centS.
Qed.


(* Addendum to Theorem 14.4. *)
Lemma cent1_sub_uniq_sigma_mmax : forall x M,
  #|'M_\sigma[x]| == 1%N -> M \in 'M_\sigma[x] -> 'C[x] \subset M.
Proof.
move=> x M0; case/cards1P=> M defMSx MS_M0; move: MS_M0 (MS_M0).
rewrite {1}defMSx; move/set1P=> ->{M0}; case/setIdP=> maxM Ms_x.
rewrite -(norm_mmax maxM); apply/normsP=> y cxy; apply: congr_group.
by apply/set1P; rewrite -defMSx inE mmaxJ maxM MsigmaJ -(normP cxy) conjSg.
Qed.

(* This is B & G, Theorem 14.4. *)
Theorem mFT_signalizer_context : forall x (N := 'N[x]) (R := 'R[x]),
    \ell_\sigma(x) == 1%N ->
  [/\ [/\ [transitive R, on 'M_\sigma[x] | 'JG],
          #|R| = #|'M_\sigma[x]|,
          R <| 'C[x]
        & Hall 'C[x] R]
   & #|'M_\sigma[x]| > 1 ->
  [/\ 'M('C[x]) = [set N],
    (*a*) 'C_(N`_\sigma)[x] = R /\ R :!=: 1,
    (*c1*) \tau2(N).-elt x,
     (*f*) N \in 'M_'F :|: 'M_'P2
    & {in 'M_\sigma[x], forall M,
  [/\ (*b*) R ><| 'C_(M :&: N)[x] = 'C[x],
     (*c2*) {subset \tau2(N) <= \sigma(M)},
      (*d*) {subset [predI \pi(M) & \sigma(N)] <= \beta(N)}
    & (*e*) \sigma(N)^'.-Hall(N) (M :&: N)]}]].
Proof.
move=> x /= ellx_eq1.
have ntx: x != 1 by rewrite (sameP eqP (ell_sigma0P x)) (eqP ellx_eq1).
have [MSx_gt1 | | ] := ltngtP 1%N #|'M_\sigma[x]|; first 1 last.
- rewrite ltnNge lt0n cards_eq0 (sameP idP (ell_sigma_le1P x)).
  by rewrite (eqP ellx_eq1).
- move/eqP; rewrite eq_sym; case/cards1P=> M defMSx.
  have ->: 'R[x] = 1%G by rewrite /'R[x] defMSx cards1.
  rewrite defMSx /Hall !cards1 sub1G normal1 coprime1n; do 2!split=> //.
  by rewrite atrans_acts_card sub1G imset_set1 cards1.
have [M MSxM]: exists M, M \in 'M_\sigma[x].
  by apply/set0Pn; rewrite -cards_eq0 -lt0n ltnW.
have [maxM Ms_x] := setIdP MSxM; rewrite sub1set in Ms_x.
have Mx: x \in M := subsetP (pcore_sub _ _) x Ms_x.
have [q pi_x_q]: exists q, q \in \pi(#[x]).
  by exists (pdiv #[x]); rewrite pi_pdiv order_gt1.
have sMq: q \in \sigma(M) := pnatPpi (mem_p_elt (pcore_pgroup _ M) Ms_x) pi_x_q.
have [X EqX]: exists X, X \in 'E_q^1(<[x]>).
  by apply/p_rank_geP; rewrite p_rank_gt0.
have [sXx abelX dimX] := pnElemP EqX; have [qX cXX _] := and3P abelX.
have ntX: X :!=: 1 := nt_pnElem EqX isT.
have sXM: X \subset M by rewrite (subset_trans sXx) ?cycle_subG.
have [N maxNX_N] := mmax_exists (mFT_norm_proper ntX (mFT_pgroup_proper qX)).
have [maxN sNX_N] := setIdP maxNX_N; pose R := 'C_(N`_\sigma)[x]%G.
have sCX_N: 'C(X) \subset N := subset_trans (cent_sub X) sNX_N.
have sCx_N: 'C[x] \subset N by rewrite -cent_cycle (subset_trans (centS sXx)).
have sMSx_MSX: 'M_\sigma[x] \subset 'M_\sigma(X).
  apply/subsetP=> M1; case/setIdP=> maxM1 sxM1.
  by rewrite inE maxM1 (subset_trans sXx) ?gen_subG.
have nsRCx: R <| 'C[x] by rewrite /= setIC (normalGI sCx_N) ?pcore_normal.
have hallR: \sigma(N).-Hall('C[x]) R.
  exact: setI_normal_Hall (pcore_normal _ _) (Msigma_Hall maxN) sCx_N.
have transCX: [transitive 'C(X), on 'M_\sigma(X) | 'JG].
  have [_ trCX _ ] := sigma_group_trans maxM sMq qX.
  case/imsetP: trCX => My; case/setIdP; case/imsetP=> y _ ->{My} sXMy trCX.
  have maxMy: (M :^ y)%G \in 'M by rewrite mmaxJ.
  have sXMys: X \subset (M :^ y)`_\sigma.
    by rewrite (sub_Hall_pcore (Msigma_Hall _)) // (pi_pgroup qX) ?sigmaJ.
  apply/imsetP; exists (M :^ y)%G; first exact/setIdP.
  apply/setP=> Mz; apply/setIdP/imsetP=> [[maxMz sXMzs] | [z cXz -> /=]].
    suffices: gval Mz \in orbit 'Js 'C(X) (M :^ y).
      by case/imsetP=> z CXz; move/group_inj->; exists z.
    rewrite -trCX inE andbC (subset_trans sXMzs) ?pcore_sub //=.
    apply/idPn; move/(sigma_partition maxM maxMz); move/(_ q); case/idP.
    rewrite inE /= sMq (pnatPpi (pgroupS sXMzs (pcore_pgroup _ _))) //.
    by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
  by rewrite mmaxJ -(normP (subsetP (cent_sub X) z cXz)) MsigmaJ conjSg.
have MSX_M: M \in 'M_\sigma(X) := subsetP sMSx_MSX M MSxM.
have not_sCX_M: ~~ ('C(X) \subset M).
  apply: contraL MSx_gt1 => sCX_M.
  rewrite -leqNgt (leq_trans (subset_leq_card sMSx_MSX)) //.
  rewrite -(atransP transCX _ MSX_M) card_orbit astab1JG.
  by rewrite (setIidPl (normsG sCX_M)) indexgg.
have neqNM: N :!=: M by apply: contraNneq not_sCX_M => <-.
have maxNX'_N: N \in 'M('N(X)) :\ M by rewrite 2!inE neqNM.
have [notMGN _] := sigma_subgroup_embedding maxM sMq sXM qX ntX maxNX'_N.
have sN'q: q \notin \sigma(N).
  by apply: contraFN (sigma_partition maxM maxN notMGN q) => sNq; exact/andP.
rewrite (negPf sN'q) => [[t2Nq s_piM_bN hallMN]].
have defN: N`_\sigma ><| (M :&: N) = N.
  exact/(sdprod_Hall_pcoreP (Msigma_Hall maxN)).
have Nx: x \in N by rewrite (subsetP sCx_N) ?cent1id.
have MNx: x \in M :&: N by rewrite inE Mx.
have sN'x: \sigma(N)^'.-elt x by rewrite (mem_p_elt (pHall_pgroup hallMN)).
have [sNsN nNsN] := andP (pcore_normal _ _ : N`_\sigma <| N).
have nNs_x: x \in 'N(N`_\sigma) := subsetP nNsN x Nx.
have defCx: R ><| 'C_(M :&: N)[x] = 'C[x].
  rewrite /= -cent_cycle (subcent_sdprod defN) ?cent_cycle.
    exact/setIidPr.
  by rewrite subsetI andbC normsG ?cycle_subG.
have transR: [transitive R, on 'M_\sigma[x] | 'JG].
  apply/imsetP; exists M => //; apply/setP=> L.
  apply/idP/imsetP=> [MSxL | [u Ru ->{L}]]; last first.
    have [_ cxu] := setIP Ru.
    by rewrite inE -(normP cxu) mmaxJ maxM MsigmaJ conjSg sub1set.
  have [u cXu defL] := atransP2 transCX MSX_M (subsetP sMSx_MSX _ MSxL).
  have [_ mulMN nNsMN tiNsMN] := sdprodP defN.
  have:= subsetP sCX_N u cXu; rewrite -mulMN -normC //.
  case/imset2P=> v w; case/setIP=> Mv _ Ns_w def_u; exists w => /=; last first.
    by apply: group_inj; rewrite defL /= def_u conjsgM (conjGid Mv).
  rewrite inE Ns_w -groupV (sameP cent1P commgP) -in_set1 -set1gE -tiNsMN.
  rewrite setICA setIC (setIidPl sNsN) inE groupMl ?groupV //.
  rewrite memJ_norm // groupV Ns_w /= -(norm_mmax maxM) inE sub_conjg.
  rewrite invg_comm -(conjSg _ _ w) -{2}(conjGid Mx) -!conjsgM -conjg_Rmul.
  rewrite -conjgC conjsgM -(conjGid Mv) -(conjsgM M) -def_u.
  rewrite -[M :^ u](congr_group defL) conjGid // -sub1set.
  by have [_ Ls_x] := setIdP MSxL; rewrite (subset_trans Ls_x) ?pcore_sub.
have oR: #|R| = #|'M_\sigma[x]|.
  rewrite -(atransP transR _ MSxM) card_orbit astab1JG (norm_mmax maxM).
  rewrite -setIAC  /= -{3}(setIidPl sNsN) -(setIA _ N) -(setIC M).
  by have [_ _ _ ->] :=  sdprodP defN; rewrite setI1g indexg1.
have ntR: R :!=: 1 by rewrite -cardG_gt1 oR.
have [y Ns_y CNy_x]: exists2 y, y \in (N`_\sigma)^# & x \in ('C_N[y])^#.
  have [y Ry nty] := trivgPn _ ntR; have [Ns_y cxy] := setIP Ry.
  by exists y; rewrite 2!inE ?nty // inE Nx cent1C ntx.
have kN'q: q \notin \kappa(N).
  rewrite (contra (@kappa_tau13 N q)) // negb_or (contraL (@tau2'1 _ _ _)) //.
  exact: tau3'2.
have [[kNx _] | [t2Nx _ uniqN]] := pi_of_cent_sigma maxN Ns_y CNy_x sN'x.
  by case/idPn: (pnatPpi kNx pi_x_q).
have defNx: 'N[x] = N.
  apply/set1P; rewrite -uniqN /'N[x] MSx_gt1; move: (pick _) => ?.
  by case: pickP => //; move/(_ N); rewrite uniqN /= set11.
have ->: 'R[x] = R by rewrite /'R[x] MSx_gt1 defNx.
rewrite (pHall_Hall hallR) {}defNx; split=> // _; split=> // [|L MSxL].
  rewrite !(maxN, inE) /=; case: (pgroup _ _) => //=; rewrite andbT.
  apply: contra kN'q => skN_N; have:= pnatPpi (mem_p_elt skN_N Nx) pi_x_q.
  by case/orP=> //=; rewrite (negPf sN'q).
have [u Ru ->{L MSxL}] := atransP2 transR MSxM MSxL; rewrite /= cardJg.
have [Ns_u cxu] := setIP Ru; have Nu := subsetP sNsN u Ns_u.
rewrite -{1}(conjGid Ru) -(conjGid cxu) -{1 6 7}(conjGid Nu) -!conjIg pHallJ2.
split=> // [|p t2Np].
  rewrite /= -(setTI 'C[x]) -!(setICA setT) -!morphim_conj.
  exact: injm_sdprod (subsetT _) (injm_conj _ _) defCx.
have [A Ep2A _] := ex_tau2Elem hallMN t2Np.
have [[nsAMN _] _ _ _] := tau2_compl_context maxN hallMN t2Np Ep2A.
have{Ep2A} Ep2A: A \in 'E_p^2(M) by move: Ep2A; rewrite pnElemI; case/setIP.
have rpM: 'r_p(M) > 1 by apply/p_rank_geP; exists A.
have: p \in \pi(M) by rewrite -p_rank_gt0 ltnW.
rewrite sigmaJ partition_pi_mmax // !orbA; case/orP=> //.
rewrite orbAC -2!andb_orr -(subnKC rpM) andbF /= => t2Mp.
case/negP: ntX; rewrite -subG1 (subset_trans sXx) //.
have [_ _ <- _ _] := tau2_context maxM t2Mp Ep2A.
have [[sAM abelA _] [_ nAMN]] := (pnElemP Ep2A, andP nsAMN).
rewrite -coprime_norm_cent ?(subset_trans sAM) ?bgFunc_norm //.
  by rewrite cycle_subG inE Ms_x (subsetP nAMN).
have [[sM'p _] [pA _]] := (andP t2Mp, andP abelA).
exact: pnat_coprime (pcore_pgroup _ _) (pi_pgroup pA sM'p).
Qed.

End Section14.
