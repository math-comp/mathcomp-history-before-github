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

End Section14.

