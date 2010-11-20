(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9.

(******************************************************************************)
(*   This file covers B & G, section 10, including with the definitions:      *)
(*   \alpha(M) == the primes p such that M has p-rank at least 3.             *)
(*   \beta(M)  == the primes p in \alpha(M) such that Sylow p-subgroups of M  *)
(*                are not narrow (see BGsection5), i.e., such that M contains *)
(*                no maximal elementary abelian subgroups of rank 2. In a     *)
(*                minimal counter-example G, \beta(M) is the intersection of  *)
(*                \alpha(M) and \beta(G). Note that B & G refers to primes in *)
(*                \beta(G) as ``ideal'' primes, somewhat inconsistently.      *)
(*   \sigma(M) == the primes p such that there exists a p-Sylow subgroup P    *)
(*                of M whose normaliser (in the minimal counter-example) is   *)
(*                contained in M.                                             *)
(*   M`_\alpha == the \alpha(M)-core of M.                                    *)
(*   M`_\beta  == the \beta(M)-core of M.                                     *)
(*   M`_\sigma == the \sigma(M)-core of M.                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Reserved Notation "\alpha ( M )" (at level 2, format "\alpha ( M )").
Reserved Notation "\beta ( M )" (at level 2, format "\beta ( M )").
Reserved Notation "\sigma ( M )" (at level 2, format "\sigma ( M )").

Reserved Notation "M `_ \alpha" (at level 3, format "M `_ \alpha").
Reserved Notation "M `_ \beta" (at level 3, format "M `_ \beta").
Reserved Notation "M `_ \sigma" (at level 3, format "M `_ \sigma").

Section Def.

Variable gT : finGroupType.
Implicit Type p : nat.

Variable M : {set gT}.

Definition alpha := [pred p | 2 < 'r_p(M)].
Definition alpha_core := 'O_alpha(M).
Canonical Structure alpha_core_group := Eval hnf in [group of alpha_core].

Definition beta := [pred p | forallb P, (P \in 'Syl_p(M)) ==> ~~ p.-narrow P].
Definition beta_core := 'O_beta(M).
Canonical Structure beta_core_group := Eval hnf in [group of beta_core].

Definition sigma :=
  [pred p | existsb P, (P \in 'Syl_p(M)) && ('N(P) \subset M)].
Definition sigma_core := 'O_sigma(M).
Canonical Structure sigma_core_group := Eval hnf in [group of sigma_core].

End Def.

Notation "\alpha ( M )" := (alpha M) : group_scope.
Notation "M `_ \alpha" := (alpha_core M) : group_scope.
Notation "M `_ \alpha" := (alpha_core_group M) : subgroup_scope.

Notation "\beta ( M )" := (beta M) : group_scope.
Notation "M `_ \beta" := (beta_core M) : group_scope.
Notation "M `_ \beta" := (beta_core_group M) : subgroup_scope.

Notation "\sigma ( M )" := (sigma M) : group_scope.
Notation "M `_ \sigma" := (sigma_core M) : group_scope.
Notation "M `_ \sigma" := (sigma_core_group M) : subgroup_scope.

Section CoreTheory.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Section GenericCores.

Variables H K : {group gT}.
Implicit Type x : gT.

Lemma sigmaJ : forall x, \sigma(H :^ x) =i \sigma(H).
Proof.
move=> x p; apply/exists_inP/exists_inP=> [[P]|[P]]; rewrite inE => pSyl_P sNH.
  exists (P :^ x^-1)%G; last by rewrite normJ sub_conjg invgK.
  by rewrite -(conjsg1 H) -(mulgV x) conjsgM inE pHallJ2.
by exists (P :^ x)%G; [ by rewrite inE pHallJ2 | by rewrite normJ conjSg ].
Qed.

Lemma MsigmaJ : forall x, (H :^ x)`_\sigma = H`_\sigma :^ x.
Proof. by move=> x; rewrite /sigma_core -(eq_pcore H (sigmaJ x)) pcoreJ. Qed.

Lemma alphaJ : forall x, \alpha(H :^ x) =i \alpha(H).
Proof. by move=> x p; rewrite !inE /= p_rankJ. Qed.

Lemma MalphaJ : forall x, (H :^ x)`_\alpha = H`_\alpha :^ x.
Proof. by move=> x; rewrite /alpha_core -(eq_pcore H (alphaJ x)) pcoreJ. Qed.

Lemma betaJ : forall x, \beta(H :^ x) =i \beta(H).
Proof.  
move=> x p; apply/forall_inP/forall_inP=> Syl_nnar P; rewrite inE => ?.
  by rewrite -(@narrowJ _ _ _ x) Syl_nnar // !inE pHallJ2.
rewrite -(@narrowJ _ _ _ x^-1) Syl_nnar // inE -[_ H]conjsg1 -(mulgV x) conjsgM.
by rewrite pHallJ2.
Qed.

Lemma MbetaJ : forall x, (H :^ x)`_\beta = H`_\beta :^ x.
Proof. by move=> x; rewrite /beta_core -(eq_pcore H (betaJ x)) pcoreJ. Qed.

End GenericCores.

Section MaxCores.

Variables M : {group gT}.
Hypothesis M_max : M \in 'M.
Let M_proper := mmax_proper M_max.

Implicit Type P : {group gT}.

Lemma beta_sub_alpha : {subset \beta(M) <= \alpha(M)}.
Proof. 
move=> p; rewrite !inE /=; move/forall_inP=> Syl_nar.
have [P sylP] := Sylow_exists p M; move: (Syl_nar P).
rewrite -(p_rank_Sylow sylP) inE sylP; move/(_ (erefl _)); apply: contraR.
by rewrite -leqNgt => ?; apply/orP; left.
Qed.

Lemma alpha_sub_sigma : {subset \alpha(M) <= \sigma(M)}.
Proof.
move=> p; rewrite !inE => rM; have [P Syl_P] := Sylow_exists p M.
apply/existsP; exists P; rewrite inE Syl_P.
rewrite uniq_mmax_norm_sub // (def_uniq_mmax _ M_max) ?(pHall_sub Syl_P) //.
have pPG := sub_proper_trans (pHall_sub Syl_P) M_proper.
rewrite -(p_rank_Sylow Syl_P) -(rank_pgroup (pHall_pgroup Syl_P)) in rM.
exact: rank3_Uniqueness pPG rM.
Qed.

Lemma Mbeta_sub_Malpha : M`_\beta \subset M`_\alpha.
Proof. exact: sub_pcore beta_sub_alpha. Qed.

Lemma Malpha_sub_Msigma : M`_\alpha \subset M`_\sigma.
Proof. exact: sub_pcore alpha_sub_sigma. Qed.

Lemma norm_Sylow_sigma : forall p P,
  p \in \sigma(M) -> p.-Sylow(M) P -> 'N(P) \subset M.
Proof.
move=> p P; case/exists_inP=> Q; rewrite inE => pSyl_Q sNPM pSyl_P.
by case: (Sylow_trans pSyl_Q pSyl_P) => m mM ->; rewrite normJ conj_subG.
Qed.

Lemma Sylow_Sylow_sigma : forall p P,
  p \in \sigma(M) -> p.-Sylow(M) P -> p.-Sylow(G) P.
Proof.
move=> p P p_Sig pSyl_P; apply: (mmax_sigma_Sylow M_max) => //.
exact: norm_Sylow_sigma p_Sig pSyl_P.
Qed.

Lemma nt_sigma_Sylow :  forall p P,
  p \in \sigma(M) -> p.-Sylow(M) P -> P :!=: 1.
Proof.
move=> p P sMp; move/(norm_Sylow_sigma sMp); apply: contraTneq => ->.
by rewrite norm1 proper_subn // mmax_proper.
Qed.

Lemma sigma_sub_pi : {subset \sigma(M) <= \pi(M)}.
Proof.
move=> p sMp; have [S sylS]:= Sylow_exists p M.
have [sSM pS _] := and3P sylS.
have{pS} [p_pr p_dv_S _] := pgroup_pdiv pS (nt_sigma_Sylow sMp sylS).
by rewrite mem_primes p_pr cardG_gt0 (dvdn_trans p_dv_S) ?cardSg.
Qed.

Lemma predI_sigma_alpha : [predI \sigma(M) & \alpha(G)] =i \alpha(M).
Proof.
move=> p; rewrite inE /=; case sg_p: (p \in \sigma(M)); last first.
  by symmetry; apply: contraFF sg_p; exact: alpha_sub_sigma.
have [P sylP] := Sylow_exists p M; rewrite !inE -(p_rank_Sylow sylP).
by rewrite -(p_rank_Sylow (Sylow_Sylow_sigma sg_p sylP)).
Qed.

Lemma predI_sigma_beta : [predI \sigma(M) & \beta(G)] =i \beta(M).
Proof.
suff SB: [predI \sigma(M) & \beta(G)] =i [predI \sigma(M) & \beta(M)].
  move=> p; rewrite SB inE /=; apply: andb_idl=> pB.
  exact: alpha_sub_sigma (beta_sub_alpha pB).
move=> p; rewrite !inE /=; apply: andb_id2l; case/exists_inP=> P; rewrite inE.
move=> sylP sNPM; have sylPG := mmax_sigma_Sylow M_max sylP sNPM.
apply/forall_inP/forall_inP=> Syl_nnar Q; rewrite inE; [move=>sylQ|move=>sylQG].
  by have [x _ ->]:= Sylow_trans sylP sylQ; rewrite narrowJ Syl_nnar // inE.
by have [x _ ->]:= Sylow_trans sylPG sylQG; rewrite narrowJ Syl_nnar // inE.
Qed.

End MaxCores.

End CoreTheory.

Section Ten.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Type p : nat.
Implicit Type A E H K M N P Q R S V W X Y : {group gT}.

Let hide T (x : T) := x.
Local Notation "'hide T" := (hide T) (at level 99, only parsing).
Local Notation "...omissis..." := (hide _).

(* This is B & G, Theorem 10.1(d) *)
Theorem sigma_sylow_conjg : forall M p X g, 
  p \in \sigma(M) -> p.-Sylow(M) X -> X :^ g \subset M -> g \in M.
Proof.
move=> M p X g p_Sig pSy_X sXgM; have pX := pHall_pgroup pSy_X. 
case: (Sylow_Jsub pSy_X sXgM _); rewrite ?pgroupJ // => h hM /= sXghX.
by rewrite -(groupMr _ hM) (subsetP (norm_Sylow_sigma _ pSy_X)) ?inE ?conjsgM.
Qed.

(* This is B & G, Theorem 10.1(a,b,c). *)
(* The (e) part is not used  in the rest of the proof, and morover it is      *)
(* obviously stated incorrectly.                                              *)
Theorem mmax_sigma_core_pgroup :
    forall M p X, M \in 'M -> p \in \sigma(M) -> p.-group X ->
  [/\  X \subset M -> forall g, X :^g \subset M -> 
          exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m],
       [transitive 'C(X), on [set Mg \in M :^: G | X \subset Mg] | 'Js ] &
       X \subset M -> 'N(X) = 'N_M(X) * 'C(X) ].
Proof.
pose OO M X := [set Mg \in M :^: G | X \subset Mg].
have BG10_1b_to_a : 'hide forall M p X g, 
    M \in 'M -> p \in \sigma(M) -> p.-group X ->
    [transitive 'C(X), on OO M X| 'Js] -> X \subset M ->  X :^ g \subset M -> 
  exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m].
- move=> M p X g M_max p_Sig pX actT sXM sXgM.
  have sMg'XX : (M :^ g^-1) \in OO M X. 
    by rewrite inE -sub_conjg sXgM mem_orbit ?in_group ?inE.
  have sMXX: M :^ 1 \in OO M X.
    by rewrite inE {2}conjsg1 sXM mem_orbit ?in_group.
  case: (atransP2 actT sMXX sMg'XX) => /= c cC; rewrite conjsg1 => defM.
  exists c^-1; exists (c * g); rewrite in_group cC mulKg; split=> //.
  by rewrite -(norm_mmax M_max) inE conjsgM -defM -conjsgM mulVg conjsg1.
have BG10_1a_to_c : 'hide forall M p X, 
    M \in 'M -> p \in \sigma(M) -> p.-group X -> X \subset M -> 
    (forall g, X :^ g \subset M -> 
      exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m]) ->
  'N(X) = 'N_M(X) * 'C(X). 
- move=> M p X M_max p_Sig pX sXM thmA; apply/eqP; rewrite eqEsubset.
  rewrite mul_subG ?cent_sub ?subsetIr // andbT; apply/subsetP=> x xNX.
  move: (xNX); rewrite inE; move/(fun x => subset_trans x sXM) => sXgM. 
  move: xNX; case/thmA: sXgM => c [m [cC mM ->]] {x}; rewrite inE => cmNX.
  have mNX : m \in 'N(X).
    rewrite inE (subset_trans _ cmNX) // conjsgM conjSg -sub_conjgV.
    by move: cC; rewrite -groupV; move/(subsetP (cent_sub _) _); rewrite inE.
  have cmCX : c ^ m \in 'C(X).
    apply/centP=> x xX; apply: (mulgI m); apply: (mulIg m^-1); rewrite conjgE. 
    gsimpl;rewrite -2!mulgA -{1 3}(invgK m)-(conjgE x) -(mulgA _ x) -(conjgE x).
    by rewrite (centP cC) // memJ_norm // groupV.
  by apply/imset2P; exists m (c^m); rewrite // ?conjgE 1?inE ?mM /=; gsimpl.
have BG10_1b: 'hide forall M p X, 
    M \in 'M -> p \in \sigma(M) -> p.-group X -> 
  [transitive 'C(X), on OO M X | 'Js]; last first.
- by move=> M p *; split; eauto; exact: (BG10_1b _ p).
move=> M p X M_max p_Sig; move: {2}_.+1 (ltnSn (#|M| - #|X|)) => m.
wlog ntX : / X :!=: 1.
  case: eqP => [trX _ _ _|_]; last by apply.
  apply/imsetP; rewrite /OO ?inE trX cent1T /=; exists (gval M); rewrite ?inE.
    by rewrite sub1G andbT; apply/imsetP; exists 1; rewrite ?group1 // conjsg1.
  rewrite orbitJs; apply/setP=> E; rewrite inE; apply/andP/imsetP.
    by case; case/imsetP=> x xG -> s1Mx; exists x; rewrite // xG.
  by case=> x xG ->; rewrite sub1G; split=> //; apply/imsetP; exists x.
elim: m X ntX => // m IH X; rewrite -/(OO M X) /= ltnS => ntX sizeX pX.
have [M1 M1_OO] : exists M1: {group _}, gval M1 \in OO M X.
  have [XX pSyl_XX sXXX] := Sylow_superset (subsetT _) pX.
  move: (p_Sig); case/exists_inP=> P; rewrite inE => pSyl_P sNPM.
  have pSyl_PG := Sylow_Sylow_sigma M_max p_Sig pSyl_P.
  case: (Sylow_trans pSyl_PG pSyl_XX) => x _ defP.
  move: pSyl_P; rewrite -(pHallJ2 _ _ _ x) -defP; case/and3P=> sXXM _ _.
  exists (M :^ x)%G; rewrite inE (subset_trans sXXX sXXM) andbT.
  by apply/imsetP; exists x; rewrite ?inE.
have acts_CX : [acts 'C(X), on OO M X | 'Js].
  apply/subsetP=> x xCX; apply/astabsP=> O /=; rewrite !inE -sub_conjgV.
  rewrite (@normP _ x^-1 _ _) ?in_group ?(subsetP _ _ xCX) ?cent_sub //.
  apply: andb_id2r => sXO; apply/imsetP/imsetP=> [[]|[]] g _ defO; last first.
    by exists (g * x); rewrite ?(groupM,inE) // defO conjsgM.
  exists (g * x^-1); rewrite ?groupM ?inE //.
  by rewrite conjsgM -defO -conjsgM mulgV conjsg1.
apply/imsetP; exists (gval M1) => //; apply/eqP; rewrite eqEsubset andbC.
rewrite acts_sub_orbit // M1_OO; apply/subsetP=> M2' M2'_OO; apply/imsetP. 
have [M2 -> M2_OO {M2' M2'_OO}]: exists2 M2, M2' = gval M2 & gval M2 \in OO M X.
  move: M2'_OO (M2'_OO); rewrite {1}inE; case/andP; case/imsetP=> x ? -> *.
  by exists (M :^ x)%G.
case: (eqsVneq M1 M2) => [->/=|]; first by exists 1; rewrite ?in_group ?conjsg1.
move=> neqM1M2; move: (neqM1M2); rewrite eq_sym => neqM2M1; pose L := 'N(X).
have mk_proper_Syl : forall H K, gval H \in OO M X -> gval K \in OO M X -> 
  H :!=: K -> exists2 X1 : {group _}, p.-Sylow(H :&: L) X1 & X \proper X1.
- move=> H K; rewrite 2!inE; case/andP; case/imsetP=> x2 _ defH sXH.
  case/andP; case/imsetP=> x1 _ defK sXK neqHK; pose g := x1 ^-1 * x2.
  have defH2 : H :=: K :^ g by rewrite defK -!conjsgM mulKVg -defH.
  have sXgH : X :^ g \subset H.
    by rewrite sub_conjg defH2 -!conjsgM mulgV conjsg1.
  have p_Sig1 : p \in \sigma(H) by rewrite defH sigmaJ.
  have [XX pSyl_XX] := Sylow_superset sXH pX.
  rewrite subEproper; case/orP => [defX1|pXXX].
    have := sigma_sylow_conjg p_Sig1 _ sXgH.
    rewrite (eqP defX1); move/(_ pSyl_XX) => gH.
    case/negP: neqHK; rewrite -(inj_eq (@conjsg_inj _ g)) -defH2.
    by rewrite (normP _) // (subsetP (normG _) _ gH).
  case/and3P: pSyl_XX => sXXM1 pXX _; have pLXX := pgroupS (subsetIl _ L) pXX.
  have pXXXL := nilpotent_proper_norm (pgroup_nil pXX) pXXX.
  have [X1 pSyl_X1] := Sylow_superset (setSI L sXXM1) pLXX.
  by move/(proper_sub_trans pXXXL) => ?; exists X1.
have [X1 pSyl_X1 pXX1] := mk_proper_Syl M1 M2 M1_OO M2_OO neqM1M2.
have [X2 pSyl_X2 pXX2] := mk_proper_Syl M2 M1 M2_OO M1_OO neqM2M1.
rewrite /OO in M2_OO M1_OO => {mk_proper_Syl neqM1M2 neqM2M1 acts_CX}.
wlog [P pSyl_P [sX1P sPM]] : M M_max p_Sig IH sizeX M1_OO M2_OO / 
  exists2 P : {group _}, p.-Sylow(L) P & X1 \subset P /\ P \subset M.
- have sX1L : X1 \subset L by case/and3P: pSyl_X1; rewrite subsetI; case/andP.
  have [P pSyl_P sX1P] := Sylow_superset sX1L (pHall_pgroup pSyl_X1).
  move: (p_Sig); case/exists_inP=> Px; rewrite inE => pSyl_Px sNPxM.
  have pSyl_PxG := Sylow_Sylow_sigma M_max p_Sig pSyl_Px.
  have [PG pSyl_PG sPPG] := Sylow_superset (subsetT _) (pHall_pgroup pSyl_P).
  case: (Sylow_trans pSyl_PxG pSyl_PG) => x _ defPG.
  have sPMx : P \subset M :^ x. 
    by rewrite (subset_trans sPPG) // defPG conjSg (pHall_sub pSyl_Px).
  move/(_ (M :^ x)%G); rewrite sigmaJ p_Sig mmaxJ M_max cardJg /OO /=.
  have -> : (M :^ x)%G :^: G = M :^: G; last by apply => //; exists P.
  apply/setP=> Y; apply/imsetP/imsetP=> [[]|[]] z _ ->.
    by exists (x * z); rewrite ?(groupM, inE, conjsgM).
  by exists (x^-1 * z); rewrite ?(groupM, inE) // -conjsgM mulKVg.
have [t tL sX2Pt] : exists2 t, t \in L & X2 \subset P :^ t.
  have sX2L : X2 \subset L by case/and3P: pSyl_X2; rewrite subsetI; case/andP.
  have [Pt pSyl_Pt sX2Pt] := Sylow_superset sX2L (pHall_pgroup pSyl_X2).
  by case: (Sylow_trans pSyl_P pSyl_Pt) sX2Pt => t tL -> *; exists t.
have sX1M := subset_trans sX1P sPM; have pXP := proper_sub_trans pXX1 sX1P.
have ? : #|X| < #|M| by rewrite (proper_card (proper_sub_trans pXX1 sX1M)). 
have use_IH : forall N M1 X1, X \proper X1 -> X1 \subset N -> 
    p.-Sylow(M1 :&: L) X1 -> gval M1 \in M :^: G -> gval N \in M :^: G -> 
  exists2 c, c \in 'C(X) & N :=: M1 :^ c.
- move=> N N1 S1 pXS1 sS1M pSyl_S1 N1inMG NinMG.
  have cardS1 : #|M| - #|S1| < m.
    by rewrite (leq_trans _ sizeX) // ltn_sub2l ?(proper_card pXS1).
  have [N1_OO N_OO] : gval N1 \in OO M S1 /\ gval N \in OO M S1.
    by case/and3P: pSyl_S1; rewrite subsetI /= !inE N1inMG NinMG; case/andP.
  have ntS1 : S1 :!=: 1.
    case: eqP pXS1 => // ->; rewrite properEneq ntX subG1 => /= tX.
    by rewrite tX in ntX.
  move/atransP2: (IH S1 ntS1 cardS1 (pHall_pgroup pSyl_S1)).
  case/(_ N1 N N1_OO N_OO) => /= c cCS1 ->; exists c => //.
  by apply: subsetP (centS (proper_sub _)) _ cCS1.
move: M1_OO M2_OO; rewrite !inE; case/andP=> M1in sXM1; case/andP=> M2in sXM2.
have [|c cCX defM] := use_IH M M1 X1 pXX1 sX1M pSyl_X1 M1in.  
  by apply/imsetP; exists 1; rewrite ?inE // conjsg1.
have [||d dCX /= defMbis] := use_IH (M :^ t)%G M2 X2 pXX2 _ pSyl_X2 M2in.
  by rewrite ?(subset_trans sX2Pt) ?conjSg.
  by apply/imsetP; exists t; rewrite ?inE.
have pP := pHall_pgroup pSyl_P; have oddL: odd #|L| by exact: mFT_odd.
have sPL := pHall_sub pSyl_P; have pMG := mmax_proper M_max => {use_IH}.
have pLG : L \proper G.
  apply: mFT_norm_proper ntX (sub_mmax_proper M_max _).
  by apply: subset_trans (proper_sub pXP) sPM.
have solL : solvable L := mFT_sol pLG. 
case: (leqP 3 'r_p(P)) => [rP|]; last rewrite (p_rank_Sylow pSyl_P).
  have PU : P \in 'U.
    by rewrite rank3_Uniqueness ?(rank_pgroup pP) // (sub_proper_trans sPM pMG).
  have sLM : L \subset M := sub_uniq_mmax (def_uniq_mmax PU M_max sPM) sPL pLG.
  have tM : t \in 'N(M) by apply: subsetP (subset_trans sLM (normG _)) _ tL.
  move: defM defMbis; rewrite (normP tM) => ->; move/eqP.
  rewrite -(inj_eq (@conjsg_inj _ d^-1)) -!conjsgM mulgV conjsg1; move/eqP=> <-.
  by exists (c * d^-1) => //; rewrite !in_group.
case/(rank2_der1_complement solL); rewrite //= -/L => _ _ p'PO.
have defL : L :=: 'N_L(P) * 'O_p^'(L).
  have npsL : L \subset 'N('O_{p^',p}(L)) := char_norm (pseries_char _ _).
  have pSyl_POpp : p.-Sylow('O_{p^',p}(L)) P.
    rewrite (pHall_subl _ (pseries_sub _ _) pSyl_P) //= -/L.
    rewrite -quotient_sub1 /= ?subG1 /=; last by rewrite (subset_trans sPL).
    have pPQ: p.-group (P / 'O_{p^',p}(L)) by rewrite quotient_pgroup ?pP.
    rewrite -[_ / _]setIid coprime_TIg //= (pnat_coprime pPQ) //.
    by rewrite [_.-nat _](pgroupS _ p'PO) // quotientS.
  apply/eqP; rewrite eqEsubset mul_subG ?subsetIl ?pcore_sub ?andbT //.
  rewrite /L -{1}(Frattini_arg (pseries_normal _ _) pSyl_POpp) /= -/L.
  rewrite (subset_trans (_:_ \subset 'N_L(P) * (P * 'O_p^'(L)))) //.
    rewrite -normC ?subIset ?npsL // mulgS //.
    have sPNOL := subset_trans sPL (char_norm (pcore_char p^' _)).
    rewrite normC // -quotientK /pseries //= {1}/pcore_mod /= pcore_mod1 /= -/L.
    by rewrite morphpreS // pcore_sub_Hall ?quotient_pHall.
  by rewrite mulgA mulGSid // subsetI sPL normG.
move: tL; rewrite defL; case/imset2P => u v uNLP vOL deft.
have cop : coprime #|X| #|'O_p^'(L)| := pnat_coprime pX (pcore_pgroup _ _).
have vCX : v \in 'C(X).
  apply: subsetP _ _ vOL; apply/commG1P; apply/trivgP. 
  rewrite -(coprime_TIg cop) setIC /= commg_subI // subsetI subxx ?pcore_sub//=.
  by rewrite (subset_trans (normG _)) // char_norm ?pcore_char.
have ntP : P :!=: 1.
   by rewrite -!proper1G in ntX *; rewrite (proper_trans ntX).
have transP : [transitive 'C(P), on OO M P | 'Js].
  by apply: IH; rewrite ?pP // (leq_trans _ sizeX) // ltn_sub2l // proper_card.
have: u \in 'N(P) by apply: subsetP (subsetIr _ _) _ uNLP.
rewrite (BG10_1a_to_c M p) // => [|g]; last by apply: (BG10_1b_to_a M p P g).
case/imset2P => w x wNMP xCP defu.
exists (c * x * v * d^-1); rewrite ?in_group //=; last move: defM defMbis.  
  by apply: subsetP (centS (proper_sub pXP)) _ xCP.
have wNM : w \in 'N(M) by apply: subsetP (normG _) _ _; case/setIP: wNMP.
rewrite deft defu !conjsgM (normP wNM) -!conjsgM => ->.
move/eqP;  rewrite -(inj_eq (@conjsg_inj _ d^-1)).
by rewrite -!conjsgM mulgV conjsg1 !mulgA; move/eqP=> <-.
Qed.

Section OneMaximal.

Variable M : {group gT}.
Hypothesis M_max : M \in 'M.

Let M_proper := mmax_proper M_max.
Let M_sol := mmax_sol M_max.

Let sub_sigma_Hall_M' : forall (Ms : {group gT}), 
  \sigma(M).-Hall(M) Ms -> Ms \subset M^`(1).
Proof.
move=> Ms sigma_Hall_Ms; have [sMs_M sigma_Ms _] := and3P sigma_Hall_Ms.
rewrite -Sylow_gen gen_subG; apply/bigcupsP=> P.
case/SylowP=> p primep Syl_P_Ms.
case: (eqsVneq P 1)=> [->|neP1]; first by rewrite sub1G.
have [sP_Ms pMs _] := and3P Syl_P_Ms.
have {neP1 pMs} [_ pdvdP _] := pgroup_pdiv pMs neP1.
have {pdvdP} sigma_p : p \in \sigma(M).
  by rewrite -pnatE // (pnat_dvd pdvdP (pgroupS sP_Ms sigma_Ms)).
have {Syl_P_Ms} Syl_P_M : p.-Sylow(M) P.
  rewrite pHallE (subset_trans sP_Ms sMs_M) (card_Hall Syl_P_Ms) /=. 
  rewrite (card_Hall sigma_Hall_Ms) partn_part // => q; rewrite 2!inE. 
  by move/eqP=> ->.
have sPM := subset_trans sP_Ms sMs_M.
have nMP := norm_Sylow_sigma sigma_p Syl_P_M.
have Syl_P_G := Sylow_Sylow_sigma M_max sigma_p Syl_P_M.
have mFT_deriv : G^`(1) = G.
  case/simpleP: (mFT_simple gT)=> _; case/(_ _ (der_normal 1 _))=> //.
  by move/commG1P; move/(negP (mFT_nonAbelian gT)).
rewrite (subset_trans _ (subsetIr P _)) //= -{1}(setIT P) -mFT_deriv.
rewrite (focal_subgroup_gen Syl_P_G) (focal_subgroup_gen Syl_P_M).
rewrite gen_subG; apply/subsetP=> xg; case/imset2P=> x g Px; rewrite inE. 
case/andP=> Gg Pxg ->; case: (eqVneq x 1)=> [->|nex1]. 
  by rewrite comm1g group1.
pose X := <[x]>; have sXM : X \subset M by rewrite cycle_subG (subsetP sPM).
have sXg_M : X :^ g \subset M by rewrite -cycleJ cycle_subG (subsetP sPM).
have neX1 : (X :!=: 1) by apply/trivgPn; exists x; rewrite ?cycle_id.
have pX : p.-group X.
  by rewrite (pgroupS _ (pHall_pgroup Syl_P_M)) // cycle_subG.
have [BG10_1a _ _] := mmax_sigma_core_pgroup M_max sigma_p pX.
case: (BG10_1a sXM _ sXg_M)=> c; rewrite cent_cycle.
case=> m [CXc Mm g_eq]; rewrite mem_gen //.
have xc_eq : x ^ c = x.
  by apply/conjg_fixP; rewrite (sameP commgP cent1P) cent1C.
have xg_eq : x ^ g = x ^ m by rewrite g_eq conjgM xc_eq.
by apply/imset2P; exists x m; rewrite ?inE ?Mm ?commgEl // -xg_eq.
Qed.

Let nsMalpha_M : M`_\alpha <| M.
Proof. by apply: pcore_normal. Qed.

Let F := 'F(M / M`_\alpha).

Let alpha'F : (\alpha(M)^').-group F.
Proof.
have Fitting1 : forall (hT : finGroupType), 'F(1) = (1 : {set hT}).
  by move=> hT; apply/trivgP; rewrite Fitting_sub.
rewrite /F -(nilpotent_pcoreC (\alpha(M)) (Fitting_nil _)) -Fitting_pcore /=.
by rewrite trivg_pcore_quotient /= Fitting1 dprod1g; apply: pcore_pgroup.
Qed.

Let nsF_MMalpha : F <| M / M`_\alpha.
Proof. by apply: Fitting_normal. Qed.

Let alpha_Malpha : \alpha(M).-group (M`_\alpha).
Proof. by exact: pcore_pgroup. Qed.

Let M'Malpha_sub_F : M^`(1) / M`_\alpha \subset F.
Proof.
case: (inv_quotientN nsMalpha_M nsF_MMalpha)=> /= K K_def sMalpha_K nsKM.
have nsMalpha_K : M`_\alpha <| K.
  exact: (normalS sMalpha_K (normal_sub nsKM) nsMalpha_M).
have alpha_Hall_Malpha_K : \alpha(M).-Hall(K) M`_\alpha.
  rewrite -(pquotient_pHall alpha_Malpha nsMalpha_K (normal_refl _)).
  by rewrite trivg_quotient pHallE sub1G cards1 /= part_p'nat // -K_def.
move: (SchurZassenhaus_split (pHall_Hall alpha_Hall_Malpha_K) nsMalpha_K).
case/splitsP=> H; rewrite inE; case/andP=> /= TI_Malpha_H Keq.
have sHK : H \subset K by rewrite -(eqP Keq) mulG_subr.
have isogFH: F \isog H.
  have nMalpha_H : H \subset 'N(M`_\alpha).
    by rewrite (subset_trans _ (normal_norm nsMalpha_K)). 
  rewrite [F]K_def -(eqP Keq) -norm_joinEr // joingC quotientYidr //. 
  rewrite isog_sym (isog_trans _ (second_isog _)) //= (eqP TI_Malpha_H).
  by rewrite quotient1_isog.
have sHM := subset_trans sHK (normal_sub nsKM).
clear K_def sMalpha_K nsKM nsMalpha_K alpha_Hall_Malpha_K Keq sHK K.
have {TI_Malpha_H isogFH sHM H} rF : 'r(F) <= 2.
  case: (rank_witness [group of F])=> p primep -> /=.
  case: (eqVneq 'r_p(F) 0)=> [->|] //; rewrite -lt0n p_rank_gt0 /= -/F.
  rewrite mem_primes; case/and3P=> _ _ pdvdF.
  move: ((pnatP _ (cardG_gt0 _) alpha'F) _ primep pdvdF).
  rewrite /alpha !inE -leqNgt=> rpM.
  by rewrite (isog_p_rank isogFH) (leq_trans (p_rankS _ sHM)).
rewrite quotient_der ?(normal_norm nsMalpha_M) //=.
by rewrite rank2_der1_sub_Fitting // ?mFT_quo_odd // quotient_sol.
Qed.

(* This is B & G, Theorem 10.2(a1). *) 
Theorem Hall_M_Malpha : \alpha(M).-Hall(M) M`_\alpha.
Proof.
have [Ma alpha_Hall_Ma] := Hall_exists \alpha(M) M_sol.
have [sMa_M alpha_Ma _] := and3P alpha_Hall_Ma.
have sigma_Ma : \sigma(M).-group Ma.
  by apply: (sub_in_pnat _ alpha_Ma)=> q _; exact: alpha_sub_sigma.
have [Ms sigma_Hall_Ms sMa_Ms] := Hall_superset M_sol sMa_M sigma_Ma.
have [sMs_M sigma_Ms _] := and3P sigma_Hall_Ms.
have sMs_M' := sub_sigma_Hall_M' sigma_Hall_Ms.
have alpha'Ms_Malpha : ((\alpha(M))^').-group (Ms / M`_\alpha).
  by rewrite (pgroupS (subset_trans _ M'Malpha_sub_F) alpha'F) //= quotientS.
have sMalpha_Ma : M`_\alpha \subset Ma by rewrite pcore_sub_Hall.
have eMa_Malpha : Ma :=: M`_\alpha.
  apply/eqP; rewrite eqEsubset sMalpha_Ma andbT -quotient_sub1; last first.
    by rewrite (subset_trans (subset_trans sMa_Ms _) (normal_norm nsMalpha_M)).
  rewrite subG1 trivg_card1 (@pnat_1 \alpha(M) #|_|) //=.
    by rewrite [_.-nat _]quotient_pgroup.
  by apply: (pgroupS _ alpha'Ms_Malpha); rewrite quotientS.
by rewrite -eMa_Malpha.
Qed.

(* This is B & G, Theorem 10.2(a2). *) 
Theorem Hall_G_Malpha : \alpha(M).-Hall(G) M`_\alpha.
Proof.
rewrite pHallE subsetT /= (card_Hall Hall_M_Malpha) eqn_dvd.
rewrite partn_dvd ?cardG_gt0 ?cardSg ?subsetT //=.
apply/dvdn_partP; rewrite ?part_gt0 // => p.
rewrite inE /= primes_part mem_filter /=; case/andP=> alpha_p primesG_p.
rewrite partn_part=> [|q]; last by rewrite 2!inE; move/eqP=> ->.
have [P Syl_P] := Sylow_exists p M.
have SylGP : p.-Sylow(G) P.
  by rewrite (Sylow_Sylow_sigma _ _ Syl_P) // alpha_sub_sigma.
rewrite -(card_Hall SylGP) (card_Hall Syl_P) sub_in_partn // => q _.
by rewrite 2!inE; move/eqP=> ->.
Qed.

(* This is B & G, Theorem 10.2(b1). *) 
Theorem Hall_M_Msigma : \sigma(M).-Hall(M) M`_\sigma.
Proof. 
have [sMa_M alpha_Ma _] := and3P Hall_M_Malpha.
have sigma_Ma : \sigma(M).-group M`_\alpha.
  by apply: (sub_in_pnat _ alpha_Ma)=> q _; exact: alpha_sub_sigma.
have [Ms sigma_Hall_Ms sMa_Ms] := Hall_superset M_sol sMa_M sigma_Ma.
have [sMs_M sigma_Ms _] := and3P sigma_Hall_Ms.
have sMs_M' := sub_sigma_Hall_M' sigma_Hall_Ms.
have sigma_Hall_F_Ms_Malpha : \sigma(M).-Hall(F) (Ms / M`_\alpha).
  rewrite (pHall_subl _ (normal_sub nsF_MMalpha)) //=.
    by rewrite (subset_trans _ M'Malpha_sub_F) // quotientS.
  by rewrite quotient_pHall // (subset_trans _ (normal_norm nsMalpha_M)).
have : Ms / M`_\alpha <| M / M`_\alpha.
  rewrite (nilpotent_Hall_pcore (Fitting_nil _) sigma_Hall_F_Ms_Malpha) /=.
  exact: (char_normal_trans (pcore_char _ _) (Fitting_normal _)).
rewrite -cosetpre_normal !quotientGK //= => [nsMs_M| ]; last first.
  by rewrite (normalS _ _ nsMalpha_M).
have sMsigma_Ms : M`_\sigma \subset Ms by rewrite pcore_sub_Hall.
have sMsigma_M : M`_\sigma \subset M by apply: pcore_sub.
have sigma_Msigma : \sigma(M).-group M`_\sigma by apply: pcore_pgroup.
have {sMsigma_Ms} eMs_Msigma : Ms :=: M`_\sigma.
  by apply/eqP; rewrite eqEsubset sMsigma_Ms andbT pcore_max.
by rewrite -eMs_Msigma.
Qed.

(* This is B & G, Theorem 10.2(b2). *) 
Theorem Hall_G_Msigma : \sigma(M).-Hall(G) M`_\sigma.
Proof. 
rewrite pHallE subsetT /= (card_Hall Hall_M_Msigma) eqn_dvd.
rewrite partn_dvd ?cardG_gt0 ?cardSg ?subsetT //=.
apply/dvdn_partP; rewrite ?part_gt0 // => p.
rewrite inE /= primes_part mem_filter /=; case/andP=> alpha_p primesG_p.
rewrite partn_part=> [|q]; last by rewrite 2!inE; move/eqP=> ->.
have [P Syl_P] := Sylow_exists p M.
have SylGP : p.-Sylow(G) P.
  by rewrite (Sylow_Sylow_sigma _ _ Syl_P).
rewrite -(card_Hall SylGP) (card_Hall Syl_P) sub_in_partn // => q _.
by rewrite 2!inE; move/eqP=> ->.
Qed.

(* This is B & G, Theorem 10.2(c). *)
Theorem Msigma_sub_M' : M`_\sigma \subset M^`(1).
Proof. exact: sub_sigma_Hall_M' Hall_M_Msigma. Qed.

Let alpha'MMalpha : \alpha(M)^'.-group (M / M`_\alpha).
Proof.
rewrite /pgroup card_quotient ?normal_norm // -divgS ?normal_sub //=.
rewrite (card_Hall Hall_M_Malpha) -{1}(@partnC \alpha(M) #|M|) ?cardG_gt0 //. 
by rewrite mulKn ?cardG_gt0 // part_pnat.
Qed.

(* This is B & G, Theorem 10.2(d1). *)
Theorem rank_MMalpha_le2 : 'r(M / M`_\alpha) <= 2.
Proof.
have [p primep ->] := rank_witness (M / M`_\alpha).
case: (eqVneq 'r_p(M / M`_\alpha) 0)=> [->|] //; rewrite -lt0n p_rank_gt0 /=.
rewrite mem_primes; case/and3P=> _ _ pdvd_MMalpha.
move: ((pnatP _ (cardG_gt0 _) alpha'MMalpha) _ primep pdvd_MMalpha).
rewrite /alpha !inE -leqNgt=> le_rpM2; have [P pSylP] := Sylow_exists p M.
have [sPM pP _] := and3P pSylP.
have nMalpha_P : P \subset 'N(M`_\alpha).
  by rewrite (subset_trans sPM) // normal_norm.
have TI_Malpha_P : M`_\alpha :&: P :=: 1.
  rewrite coprime_TIg // (pnat_coprime alpha_Malpha) //.
  rewrite (sub_in_pnat _ (pHall_pgroup pSylP)) // => q _; rewrite 2!inE.
  by move/eqP=> ->{q}; apply: (pgroupP alpha'MMalpha p primep pdvd_MMalpha).
have pSyl_PMalpha : p.-Sylow(M / M`_\alpha) (P / M`_\alpha).
  by rewrite quotient_pHall.
have isogP : P \isog (P / M`_\alpha).
  by rewrite (isog_trans _ (second_isog _)) // TI_Malpha_P quotient1_isog. 
rewrite -(p_rank_Sylow pSyl_PMalpha) /= -(isog_p_rank isogP).
by rewrite (p_rank_Sylow pSylP).
Qed.

(* This is B & G, Theorem 10.2(d2). *)
Theorem nil_M'Malpha : nilpotent (M^`(1) / M`_\alpha).
Proof. by rewrite (nilpotentS M'Malpha_sub_F) // Fitting_nil. Qed.

(* This is B & G, Theorem 10.2(e). *)
Theorem Msigma_neq1 : M`_\sigma :!=: 1.
Proof. 
case: (eqsVneq M`_\alpha 1)=> [eMalpha1|]; last first.
  by apply: contra; move/eqP=> Ms1; rewrite -subG1 -Ms1 Malpha_sub_Msigma.
have le_rM2 : 'r(M) <= 2.
  have [p primep ->] := rank_witness M.
  rewrite (isog_p_rank (quotient1_isog _)) -eMalpha1 /=.
  case: (eqVneq 'r_p(M / M`_\alpha) 0)=> [->|] //; rewrite -lt0n p_rank_gt0 /=.
  rewrite mem_primes; case/and3P=> _ _ pdvd_MMalpha.
  move: (pgroupP alpha'MMalpha p primep pdvd_MMalpha).
  by rewrite eMalpha1 -(isog_p_rank (quotient1_isog _)) !inE -leqNgt.
have le_rFM2 : 'r('F(M)) <= 2.
  by rewrite (leq_trans _ le_rM2) // rankS // Fitting_sub.
move: (rank2_max_pcore_Sylow (mFT_odd M) (mmax_sol M_max) le_rFM2)=> /= qSyl.
set q := max_pdiv #|M| in qSyl.
have neOqM_1 : 'O_q(M) != 1.
  rewrite -cardG_gt1 (card_Hall qSyl) p_part_gt1 pi_max_pdiv cardG_gt1.
  by rewrite mmax_neq1.
have eNOqM_M : 'N('O_q(M)) = M by apply: mmax_normal; rewrite ?pcore_normal.
apply: contra _ neOqM_1; rewrite -!subG1; apply: subset_trans.
rewrite sub_pcore // => p; rewrite 2!inE; move/eqP=> ->.
rewrite !inE; apply/existsP; exists ('O_q(M))%G; 
by rewrite inE qSyl eNOqM_M subxx.
Qed.

Let nsMaM : M`_\alpha <| M.
Proof. by apply: pcore_normal. Qed.

Let alphaMa : \alpha(M).-group (M`_\alpha).
Proof. by exact: pcore_pgroup. Qed.

(* This is B & G, Lemma 10.3. *)
Theorem cent_alpha'_uniq : forall X, 
     X \subset M -> \alpha(M)^'.-group X -> 'r('C_(M`_\alpha)(X)) >= 2 ->
  ('C_M(X))%G \in 'U.
Proof.
move=> X sXM alpha'X; case: (rank_witness 'C_(M`_\alpha)(X)) => p primep -> rP.
have alpha_p : p \in \alpha(M).
  apply: (pgroupP alphaMa p primep).
  suff : p \in \pi('C_(M`_\alpha)(X)). 
    rewrite !inE mem_primes; case/and3P=> _ _; move/dvdn_trans; apply.
    by rewrite cardSg // subsetIl.
  by rewrite -p_rank_gt0; apply: (leq_trans _ rP).
case/p_rank_geP: rP => /= B; case/pnElemP; rewrite subsetI.
case/andP=> sBMa cXB pabelB lcardB.
have pB := abelem_pgroup pabelB.
have nMaX : X \subset 'N(M`_\alpha).
  exact: (subset_trans _ (normal_norm nsMaM)).
have coMaX : coprime #|M`_\alpha| #|X|.
  by rewrite -(part_pnat_id alphaMa) -(part_pnat_id alpha'X) coprime_partC.
have solMa := solvableS (normal_sub nsMaM) M_sol.
have nBX : X \subset 'N(B) by rewrite cents_norm // centsC.
case: (coprime_Hall_subset nMaX coMaX solMa sBMa pB nBX) => P [pSylP nPX sBP].
case rCPB : ('r('C_P(B)) > 2).
  suff : B \in 'U.
    apply: uniq_mmaxS; rewrite ?(sub_proper_trans _ M_proper) ?subsetIl //.
    by rewrite subsetI cXB andbT (subset_trans sBMa (normal_sub nsMaM)).
  apply: (cent_rank3_Uniqueness _ (leq_trans rCPB (rankS (subsetIr _ _)))).
  by rewrite (rank_pgroup pB) (p_rank_abelem pabelB) lcardB.
have pP := pHall_pgroup pSylP.
have Beq : 'Ohm_1('C_P(B)) = B.
  have sB_CPB : B \subset 'C_P(B). 
    by rewrite subsetI sBP /=; apply: (abelem_abelian pabelB).
  apply/eqP; rewrite eq_sym eqEsubset -{1}(Ohm1_id pabelB) OhmS //=.
  have pCPB : p.-group 'C_P(B) by rewrite (pgroupS _ pP) // subsetIl.
  rewrite (OhmE 1 pCPB) /= gen_subG; apply/subsetP=> g; case/LdivP.
  case/setIP=> Pg CBg gp1; apply: contraFT rCPB => nBg.
  rewrite (rank_pgroup pCPB).
  pose G := <[g]>; suffices: 2 < 'r_p(B <*> G). 
    move/leq_trans; apply; rewrite p_rankS // join_subG sB_CPB /=.
    by rewrite subsetI !cycle_subG Pg.
  have BGeq : B <*> G = B * G.
    by rewrite norm_joinEl // cents_norm // centsC cycle_subG. 
  have cprodBG : B \* G = B <*> G by rewrite cprodE ?BGeq // cycle_subG.
  have pabelBG : p.-abelem (B <*> G).
    rewrite (cprod_abelem _ cprodBG) pabelB cycle_abelem ?primep ?orbT //=.
    by rewrite order_dvdn gp1.
  rewrite p_rank_abelem // -lcardB properG_ltn_log ?abelem_pgroup //.
  apply/properP; split; first by rewrite joing_subl.
  by exists g; rewrite ?nBg //= (subsetP (joing_subr _ _)) // cycle_id.
have cPX : P \subset 'C(X).
  have EpPB : B \in 'E_p(P) by apply/pElemP. 
  have coPX : coprime #|P| #|X|.
    exact: (coprime_dvdl (cardSg (pHall_sub pSylP)) coMaX).
  rewrite centsC; apply: (coprime_odd_faithful_cent_abelem EpPB pP nPX coPX).
    by rewrite mFT_odd.
  rewrite centsC (subset_trans _ cXB) // -{2}Beq. 
  rewrite (OhmE 1 (pgroupS _ pP)) ?subsetIl // sub_gen //= setIdE setIS //.
  by apply/subsetP=> x; rewrite !inE eqn_dvd order_dvdn; case/andP.
have pSylMP : p.-Sylow(M) P.
  rewrite pHallE (subset_trans (pHall_sub pSylP) (normal_sub nsMaM)) /=.
  rewrite (card_Hall pSylP) (card_Hall Hall_M_Malpha) partn_part // =>q.
  by rewrite 2!inE; move/eqP=> ->.
have rP : 'r(P) >= 3.
  rewrite (rank_pgroup (pHall_pgroup pSylP)) (p_rank_Sylow pSylMP).
  by rewrite !inE in alpha_p.
apply: rank3_Uniqueness.
  by rewrite (sub_proper_trans (subsetIl _ _)) // M_proper.
by rewrite (leq_trans rP) // rankS // subsetI cPX andbT (pHall_sub pSylMP).
Qed.

Variable p : nat.
Hypothesis piMp : p \in \pi(M).

(* This is B & G, Lemma 10.4(a). *)
Lemma pdiv_M_M' : p %| #|M / M^`(1)| -> p \in \sigma(M)^'.
Proof.
have primep : prime p by move: piMp; rewrite !inE mem_primes; case/andP.
suff : \sigma(M)^'.-group (M / M^`(1)).
  rewrite /pgroup=> sig'MM' pdvdMM'; move: (pnat_dvd pdvdMM' sig'MM').
  by rewrite (pnatE _ primep) !inE.
suff : \sigma(M)^'.-group (M / M`_\sigma).
  apply: pnat_dvd; rewrite !card_quotient ?der_norm //; last first. 
    by rewrite ?(normal_norm (pcore_normal _ _)). 
  by rewrite indexgS // Msigma_sub_M'.
rewrite /pgroup card_quotient ?normal_norm ?pcore_normal //. 
rewrite -divgS ?pcore_sub // (card_Hall Hall_M_Msigma) //.
rewrite -{1}(@partnC \sigma(M) #|M|) ?cardG_gt0 // mulKn ?cardG_gt0 //. 
by rewrite part_pnat.
Qed.

Variable sigma'p : p \in \sigma(M)^'.

(* This is B & G, Lemma 10.4(b). *)
(* Curiously, the hypothesis M'_\alpha != 1 in the text is not needed. *)
Lemma sigma'_exists_Zgroup : forall P, p.-Sylow(M) P -> 
  exists x, [/\ x \in 'Ohm_1('Z(P))^#, 'M('C_G[x]) != [set M] & 
    Zgroup ('C_(M`_\alpha)[x])].
Proof.
move=> P SylP; move: (sigma'p); rewrite !inE negb_exists_in; move/forallP.
move/(_ P); move/implyP; rewrite inE; move/(_ SylP); case/subsetPn=> u NPu nMu.
have : 'Ohm_1('Z(P)) != 1.
  apply/negP; move/eqP; rewrite -(setIidPr (Ohm_sub 1 'Z(P))) /=.
  move/TI_Ohm1; rewrite setIid; move/(trivg_center_pgroup (pHall_pgroup SylP)).
  by move/eqP; apply/negP; rewrite -cardG_gt1 (card_Hall SylP) p_part_gt1.
case/trivgPn=> /= y OZPy ney1.
have alpha'P : \alpha(M)^'.-group P.
  apply: (sub_in_pnat _ (pHall_pgroup SylP))=> q _; rewrite 2!inE.
  by move/eqP=>->; rewrite 3!inE; apply: contra sigma'p; apply: alpha_sub_sigma.
have key_lemma : forall w, w \in 'Z(P) -> w != 1 -> 'M('C_G[w]) != [set M] -> 
    Zgroup ('C_(M`_\alpha)[w]).
  move=> w ZPw new1 neMCGwM.
  rewrite odd_rank1_Zgroup ?mFT_odd //=; apply: contraR neMCGwM.
  rewrite -ltnNge -cent_cycle; set W := <[w]>; move=> rCMaW.
  have sWP : W \subset P by rewrite cycle_subG (subsetP _ _ ZPw) // subsetIl. 
  have sWM : W \subset M by apply: (subset_trans sWP (pHall_sub SylP)).
  have alpha'W := pgroupS sWP alpha'P.
  have UCMY := cent_alpha'_uniq sWM alpha'W rCMaW.
  have properCGW : 'C_G(W) \proper G.
    rewrite (sub_proper_trans (subset_trans (subsetIr _ _) (cent_sub _))) //.
    by rewrite mFT_norm_proper // ?cycle_eq1 // (sub_proper_trans sWM).
  have MCMWeq : 'M('C_M(W)) = [set M]. 
    by apply: def_uniq_mmax => //; rewrite subsetIl.
  have sCMW_CGW : 'C_M(W) \subset 'C_G(W). 
    by rewrite setSI //= (proper_sub M_proper).
  by rewrite (def_uniq_mmaxS sCMW_CGW properCGW MCMWeq).
case: (eqsVneq 'M('C_G[y]) [set M])=> [eMCGyM | neMCGyM]; last first.
  exists y; rewrite !inE ney1; split=> //; rewrite key_lemma //.
  by rewrite (subsetP (Ohm_sub 1 _)).
case: (eqsVneq 'M('C_G[y^(u^-1)]) [set M])=> [eMCHyuM | neMCGyuM]; last first.
  have neyu1 : y^(u^-1) != 1.
    apply: contra ney1; move/eqP; move/(congr1 (conjg^~ u)).
    by rewrite conjgKV conj1g=> ->.
  have sNP_NZP : 'N(P) \subset 'N('Z(P)) by rewrite char_norms // center_char.
  have sNP_NOZP : 'N(P) \subset 'N('Ohm_1('Z(P))).
    by rewrite (subset_trans sNP_NZP) // char_norms // Ohm_char.
  exists (y^(u^-1)); rewrite !inE neyu1; split=> //=.
    by rewrite memJ_norm // groupV (subsetP _ _ NPu).
  rewrite key_lemma // memJ_norm ?(subsetP _ _ OZPy) ?Ohm_sub // groupV.
  by rewrite (subsetP _ _ NPu).
case/negP: nMu; move: eMCHyuM; rewrite -cent_set1 -conjg_set1 centJ.
have <- : G :^ u^-1 = G.
  by apply/normP; rewrite (subsetP (normG _)) // inE.
rewrite -conjIg cent_set1 (def_uniq_mmaxJ _ eMCGyM) /=; move/set1_inj.
by move/(congr1 val)=> /=; move/normP; rewrite norm_mmax // groupV.
Qed.

(* This is B & G, Lemma 10.4(c), part 1 *)
Lemma sigma'_rank2_max : 'r_p(M) = 2 -> 'E_p^2(M) \subset 'E*_p(G).
Proof.
move=> rpM; apply: contraR sigma'p; case/subsetPn=> A Ep2MA EpGA.
have uniqA : A \in 'U.
  apply: (@nonmaxElem2_Uniqueness _ p); rewrite inE EpGA /=.
  by apply: (subsetP (pnElemS p 2 (subsetT M))).
case/pnElemP: Ep2MA=> sAM; move/abelem_pgroup=> pA _.
have [P pSylMP sAP] := Sylow_superset sAM pA.
apply/existsP; exists P; rewrite inE pSylMP uniq_mmax_norm_sub //.
apply: (def_uniq_mmaxS sAP); last by apply: def_uniq_mmax.
by apply: (sub_proper_trans (pHall_sub pSylMP)).
Qed.

(* This is B & G, Lemma 10.4(c), part 2 *)
Lemma sigma'_rank2_beta' : 'r_p(M) = 2 -> p \notin beta(G).
Proof.
move=> rpM; rewrite negb_forall_in; apply/exists_inP.
have [A Ep2A]: exists A, A \in 'E_p^2(M) by apply/p_rank_geP; rewrite rpM.
have [_ abelA dimA] := pnElemP Ep2A; have [pA _] := andP abelA.
have [P sylP sAP] := Sylow_superset (subsetT _) pA.
exists P; rewrite ?inE // negbK; apply/orP; right; apply/set0Pn.
exists A; rewrite 3!inE abelA dimA eqxx sAP /=.
apply: subsetP (pmaxElemS _ (subsetT P)) _ _.
rewrite inE /= [_ \in subgroups(_)]inE sAP andbT.
exact: subsetP (sigma'_rank2_max rpM) _ _.
Qed.

(* This is B & G, Lemma 10.5, part 1; the condition on X has been weakened,   *)
(* because the proof of Lemma 12.2(a) requires the stronger result.           *)
Lemma sigma'_norm_mmax_rank2 : forall X,
  p.-group X -> 'N(X) \subset M -> 'r_p(M) = 2.
Proof.
move=> X pX sNX_M; have sXM: X \subset M := subset_trans (normG X) sNX_M.
have [P sylP sXP] := Sylow_superset sXM pX.
apply: contraNeq sigma'p; rewrite /= neq_ltn orbC ltnS.
case/orP=> [rMgt2 | rMle1]; first exact: alpha_sub_sigma.
apply/existsP; exists P; rewrite inE sylP (subset_trans _ sNX_M) ?char_norms //.
rewrite sub_cyclic_char //; have [sPM pP ] := and3P sylP.
by rewrite (odd_pgroup_rank1_cyclic pP)  ?mFT_odd ?(leq_trans (p_rankS p sPM)).
Qed.

(* This is B & G, Lemma 10.5, part 2 *)
(* The second claim in B & G 10.5 follows immediately from 10.4c. This is *)
(* the remaining part of the lemma. *)
Lemma sigma'1Elem_sub_p2Elem : forall X,
    X \in 'E_p^1(G) -> 'N(X) \subset M -> 
  exists2 A, A \in 'E_p^2(G) & X \subset A.
Proof.
move=> X EpX sNXM; have p_pr := pnElem_prime EpX.
have [_ abelX dimX] := pnElemP EpX; have pX := abelem_pgroup abelX.
have sXM := subset_trans (normG X) sNXM.
have rpM2 := sigma'_norm_mmax_rank2 pX sNXM.
have [P sylP sXP] := Sylow_superset sXM pX; have [sPM pP _] := and3P sylP.
have chZP1: 'Ohm_1('Z(P)) \char P := char_trans (Ohm_char 1 _) (center_char _).
have neqZP1_X: 'Ohm_1('Z(P)) != X.
  apply: contraNneq sigma'p => defX; rewrite !inE; apply/existsP; exists P. 
  by rewrite inE sylP (subset_trans _ sNXM) // -defX char_norms.
have ntZP1 : 'Ohm_1('Z(P)) != 1.
  have: 'r_p(P) > 0 by rewrite (p_rank_Sylow sylP) rpM2.
  apply: contraTneq; rewrite -(setIidPr (Ohm_sub 1 _)); move/TI_Ohm1.
  by rewrite setIid; move/(trivg_center_pgroup pP)->; rewrite p_rank1.
pose A := X <*> 'Ohm_1('Z(P)).
have defA: X \* 'Ohm_1('Z(P)) = A.
  by rewrite cprodEY // (centSS (Ohm_sub 1 _) sXP) ?subsetIr.
have{defA} abelA : p.-abelem A.
  have pZ: p.-group 'Z(P) := pgroupS (center_sub P) pP.
  by rewrite (cprod_abelem _ defA) abelX /= Ohm1_abelem ?center_abelian.
exists [group of A]; last exact: joing_subl.
rewrite !inE subsetT abelA /= eqn_leq; apply/andP; split.
  rewrite -{1}rpM2 -{1}(p_rank_abelem abelA) p_rankS //=.
  by rewrite join_subG sXM (subset_trans (char_sub chZP1)).
rewrite -dimX (properG_ltn_log (abelem_pgroup abelA)) //.
rewrite properEneq joing_subl andbT eq_sym (sameP eqP joing_idPl).
apply: contra ntZP1 => sZP1_X; rewrite eqEsubset sZP1_X /= in neqZP1_X.
by rewrite -(setIidPr sZP1_X) prime_TIg ?(card_p1Elem EpX).
Qed.

End OneMaximal.

(* This is B & G, Theorem 10.6. *)
Theorem mFT_proper_plength1 : forall p H,
  H \proper G -> p.-length_1 H. 
Proof.
move=> p H pHG; have [M] := mmax_exists pHG; rewrite inE.
case/andP=> maxM sHM {pHG}; suff {H sHM}: p.-length_1 M by apply: plength1S.
case rpM: ('r_p(M) <= 2).
  case: (rank2_der1_complement (mmax_sol maxM) (mFT_odd _) rpM).
  move=> _ _ p'MOp'pM; rewrite /plength_1 eqEsubset pseries_sub /=.
  rewrite lastI pseries_rcons /= /pcore_mod (pcore_pgroup_id p'MOp'pM).
  by rewrite quotientGK // pseries_normal.
have alphap : p \in \alpha(M) by rewrite !inE ltnNge rpM.
pose Ma := M`_\alpha; have nsMaM : Ma <| M by apply: pcore_normal.
have [sMaM nMaM] := andP nsMaM.
have nMaM' : M^`(1) \subset 'N(Ma) by rewrite (subset_trans (der_sub 1 _)).
have sMaM' : Ma \subset M^`(1).
  exact: (subset_trans (Malpha_sub_Msigma maxM) (Msigma_sub_M' maxM)).
have [K hallK] := Hall_exists \alpha(M)^' (mmax_sol maxM).
have hallMa: \alpha(M).-Hall(M) Ma := Hall_M_Malpha maxM.
have sdKMa_M : Ma ><| K = M by exact/sdprod_Hall_pcoreP.
have [_ Meq nMaK IKMa1] := sdprodP sdKMa_M.
have sKM: K \subset M := pHall_sub hallK.
have solMa: solvable Ma := solvableS (normal_sub nsMaM) (mmax_sol maxM).
have {hallMa solMa} MaKeq: [~: Ma, K] = Ma.
  case/solvable_hall_dprod_der_subSset_comm_centr_compl: sdKMa_M => //.
  exact: pHall_Hall hallMa.
have alphaHallMa : \alpha(M).-Hall(M) Ma by apply: Hall_M_Malpha.
have alpha'HallK : \alpha(M)^'.-Hall(M) K.
  rewrite pHallE sKM /= -(@eqn_pmul2l #|Ma|) ?cardG_gt0 //.
  by rewrite (sdprod_card sdKMa_M) (card_Hall alphaHallMa) partnC ?cardG_gt0.
have cardKK' : #|K / K^`(1)| = #|M / M^`(1)|.
  rewrite !card_quotient ?der_norm // -!divgS ?der_sub //.
  have isoKMMa : K \isog M / Ma.
    rewrite -sdKMa_M sdprodEY // joingC quotientYidr //=.
    by rewrite (isog_trans _ (second_isog _)) // IKMa1 quotient1_isog.
  have isoK'M'Ma : K^`(1) \isog M^`(1) / Ma.
    by rewrite quotient_der // bgFunc_isog.
  rewrite (card_isog isoKMMa) (card_isog isoK'M'Ma) ?card_quotient //.
  by rewrite -!divgS // divn_divr ?cardSg // divnK ?cardSg.
have peltgen_eq : p_elt_gen p M = p_elt_gen p Ma.
  rewrite /p_elt_gen; apply: congr1; apply/setP=> g; rewrite !inE.
  apply/andP/andP; case=> [Mg peltg]; split=> //; rewrite ?(subsetP sMaM) //.
  rewrite (mem_normal_Hall (Hall_M_Malpha _) nsMaM Mg) //.
  by apply: (sub_p_elt _ peltg)=> q; rewrite 2!inE; move/eqP=> ->.
have primep : prime p.
  move/negbT : rpM; rewrite -ltnNge; do 2 move/leqW; rewrite !ltnS p_rank_gt0.
  by rewrite mem_primes; case/and3P.
rewrite p_elt_gen_length1 // peltgen_eq -p_elt_gen_length1 //= -/Ma -MaKeq.
have neMa1 : Ma :!=: 1.
  apply: contraL (rank_MMalpha_le2 maxM); rewrite -/Ma; move/eqP=> ->.
  rewrite -(isog_rank (quotient1_isog _)); apply: contra (negbT rpM).
  by apply: leq_trans; apply: p_rank_le_rank.
have : #|K / K^`(1)| > 1.
  rewrite cardG_gt1 -trivg_quotient /=; apply/negP; move/eqP.
  move/(quotient_inj (der_normal _ _) (normal_refl _)); move/eqP; apply/negP.
  rewrite eq_sym proper_neq // (sol_der1_proper (mmax_sol maxM)) //.
  by apply: contra neMa1; rewrite -MaKeq; move/eqP=> ->; rewrite commG1.
case/pdivP=> q primeq qdiv; have [Q SylKQ] := Sylow_exists q K.
have piMq : q \in \pi(M).
  rewrite !inE mem_primes primeq cardG_gt0.
  by rewrite (dvdn_trans qdiv) // (dvdn_trans _ (cardSg sKM)) // dvdn_quotient.
have sigma'q : q \in \sigma(M)^' by rewrite pdiv_M_M' -?cardKK' //.
have SylMQ : q.-Sylow(M) Q.
  rewrite pHallE (subset_trans (pHall_sub SylKQ)) //=.
  rewrite (card_Hall SylKQ) (card_Hall alpha'HallK) partn_part // => r.
  rewrite 3!inE; move/eqP=> ->; apply/negP=> /=; move/(alpha_sub_sigma maxM).
  by move/negP: sigma'q.
case: (sigma'_exists_Zgroup maxM piMq sigma'q SylMQ) => x.
rewrite -cent_cycle !inE; case; case/andP=> nex1.
have qZQ: q.-group 'Z(Q).  
  by rewrite (pgroupS (center_sub _)) // (pHall_pgroup SylMQ).
rewrite (OhmEabelian qZQ) ?(abelianS (Ohm_sub 1 _)) ?center_abelian //.
rewrite -setIdE inE -order_dvdn /=; case/andP=> ZQx xq1 _.
set X := <[x]> => ZgroupCMaX.
have sXK : X \subset K.
  apply: (subset_trans _ (subset_trans (center_sub _) (pHall_sub SylKQ))).
  by rewrite cycle_subG.
have solM := mmax_sol maxM; have oddM := mFT_odd M.
have HMa := pHall_Hall alphaHallMa.
rewrite -(coprime_sdprod_Hall sdKMa_M) in HMa.
apply: (odd_sdprod_Zgroup_cent_prime_plength1 _ _ _ sdKMa_M _ sXK) => //.
case/primeP: (primeq)=> _; move/(_ _ xq1); rewrite order_eq1 (negbTE nex1) /=.
by rewrite -orderE; move/eqP=> ->.
Qed.

Let pSylow_norm_split_sub_norm_der1_commg_norm_sub :
    forall p P, p.-Sylow(G) P -> [/\
  P \subset 'N(P)^`(1),
  forall V, P ><| V :=: 'N(P) -> [~: P, V] :=: P &
  forall Q, Q \subset P -> forall x : gT, 
    Q :^ x \subset P -> exists2 y,y \in 'N(P) & Q :^ x :=: Q :^ y].
Proof.
move=> p P pSyl_P.
wlog ntP: / P :!=: 1.
  case: eqP => [-> _|_]; last apply; split; rewrite ?norm1 ?sub1G //.
    by move=>*; apply: comm1G.
  by move=> Q; move/trivGP=> -> x _; exists 1 => //; rewrite conjs1g conjsg1.
have pP := pHall_pgroup pSyl_P.
have prNP : 'N(P) \proper G := mFT_norm_proper ntP (mFT_pgroup_proper pP).
have [M /= M_MNP] := mmax_exists prNP; have [M_max sNPM] := setIdP M_MNP.
have sPM := subset_trans (normG _) sNPM.
have pSyl_PM := pHall_subl sPM (subsetT _) pSyl_P.
have p_sigM : p \in \sigma(M). 
  by rewrite inE /=; apply/existsP; exists P; rewrite inE pSyl_PM.
have [p_pr _ _] := pgroup_pdiv pP ntP; have pMG := mmax_proper M_max.
have pl1M := mFT_proper_plength1 p pMG; have solM := mmax_sol M_max.
have pHall_P : p.-Sylow('N(P)) P.
  by rewrite -(setIidPr (subsetT 'N(P))) // Sylow_subnorm.
have Hall_P := pHall_Hall pHall_P.
have sPM' : P \subset M^`(1).
  apply: subset_trans _ (Msigma_sub_M' M_max).
  by rewrite (sub_Hall_pcore (Hall_M_Msigma M_max)) ?(pi_pgroup pP).
have sPNP' : P \subset ('N(P))^`(1).
  apply: subset_trans _ (dergS 1 (subsetIr M _)) => /=.
  by apply: sol_Sylow_plength1_sub_norm_der _ pSyl_PM pl1M sPM'.
split=> //.
  move=> V defV; have solP := solvableS sPM solM.
  by case: (solvable_hall_dprod_der_subSset_comm_centr_compl solP _ defV sPNP').
move=> Q sQP x sQxP; have pQ : p.-group Q := pgroupS sQP pP.
have [th101a _ _] := mmax_sigma_core_pgroup M_max p_sigM pQ.
have sQM := subset_trans sQP sPM; have sQxM := subset_trans sQxP sPM.
have [q [u [qCQ uM defx]]] := th101a sQM _ sQxM.
have sQuP: Q :^ u \subset P.
  by rewrite -(normP (subsetP (cent_sub _) _ qCQ)) -conjsgM -defx.
case: (sol_Sylow_plength1_norm_conj _ _ pl1M sQP uM)=>// q' q'CQ [y yNP defu].
exists y; first by rewrite (subsetP (subsetIr _ _) _ yNP).
rewrite defx -defu !conjsgM (normP (subsetP (cent_sub _) _ qCQ)).
by case/setIP: q'CQ => _ q'CQ; rewrite (normP (subsetP (cent_sub _) _ q'CQ)).
Qed.

(* This is B & G, Corollary 10.7(a2). *)
Corollary pSylow_norm_split_sub_norm_der1 : 
  forall p P, p.-Sylow(G) P -> P \subset 'N(P)^`(1).
Proof. 
move=> p P pSyl_P.
by case: (pSylow_norm_split_sub_norm_der1_commg_norm_sub pSyl_P).
Qed.

(* This is B & G, Corollary 10.7(a1). *)
Corollary pSylow_norm_split_commg : forall P p, p.-Sylow(G) P -> 
  forall V, P ><| V :=: 'N(P) -> [~: P, V] :=: P.
Proof.
move=> p P pSyl_P.
by case: (pSylow_norm_split_sub_norm_der1_commg_norm_sub pSyl_P).
Qed.

(* This is B & G, Corollary 10.7(c). *)
Corollary pSylow_conj_sub_in_norm : forall P p, p.-Sylow(G) P -> 
  forall Q, Q \subset P -> forall x : gT, 
    Q :^ x \subset P -> exists2 y,y \in 'N(P) & Q :^ x :=: Q :^ y.
Proof.
move=> P p pSyl_P.
by case: (pSylow_norm_split_sub_norm_der1_commg_norm_sub pSyl_P).
Qed.

(* This is B & G, Corollary 10.7(b). *)
Corollary pSylow_rank3_abelian_or_Ohm_Z_decomp : forall P p, p.-Sylow(G) P ->
  'r(P) < 3 -> abelian P \/ exists P1 : {group gT}, exists P2 : {group gT}, 
     [/\ ~~ (abelian P1) /\ P1 \* P2 :=: P, logn p #|P1| = 3, exponent P1 %| p,
          cyclic P2 & 'Ohm_1(P2) :=: 'Z(P1)].
Proof.
move=> P p pSyl_P rP.
wlog ntP: / P :!=: 1.
  case: eqP => [-> _|_]; rewrite ?abelian1; [ by left | by apply ].
have pP := pHall_pgroup pSyl_P.
have [p_pr _ _] := pgroup_pdiv pP ntP.
have pHall_P : p.-Sylow('N(P)) P.
  by rewrite -(setIidPr (subsetT 'N(P))) // Sylow_subnorm.
have [V] := splitsP (SchurZassenhaus_split (pHall_Hall pHall_P) (normalG _)).
rewrite inE; case/andP; move/eqP=> TI_PV /=; move/eqP=> /= defPV.
have defNP : P ><| V = 'N(P) by rewrite sdprodE // -defPV mulG_subr.
have p'V : p^'.-group V.
  apply/pgroupP=> q pr_q qdV; rewrite /= inE /=. 
  apply: contraL (prime_gt1 p_pr); rewrite inE /=; move/eqP=> defq.
  move: qdV; rewrite defq; case/Cauchy=> // x xV ox; rewrite -ox.
  rewrite (_:x = 1) ?order1 //; apply/set1gP; rewrite -TI_PV inE xV.
  have pcx : p.-group <[x]> by rewrite /pgroup -orderE ox pnat_id.
  have scxNP:  <[x]> \subset 'N(P). 
    by rewrite cycle_subG /= -defPV (subsetP (mulG_subr _ _) _ xV).
  have [y yNP /=] := Sylow_Jsub pHall_P scxNP pcx.
  by rewrite sub_conjg (normP (groupVr yNP)) cycle_subG => ->.
have defP : [~: P, V] = P.
  by case: (pSylow_norm_split_commg pSyl_P defNP).
have [_] := rank2_coprime_comm_cprod pP (mFT_odd _) ntP rP defP p'V (mFT_odd _).
case=> [| [S [not_cSS dimS eS] [C [mulSC cycC defC1]]]]; [by left | right].
exists S; exists C; split; rewrite // defC1.
have sSP: S \subset P by case/cprodP: mulSC => _ <- _; exact: mulG_subl.
by have [||[[]]] := p3group_extraspecial (pgroupS sSP pP); rewrite ?dimS.
Qed.

(* This is B & G, Corollary 10.7(d). *)
Corollary pSylow_sub_norm_pSylow : forall P p, p.-Sylow(G) P -> 
  forall Q, Q \subset P -> p.-Sylow('N(Q)) 'N_P(Q).
Proof.
move=> P p pSyl_P Q sQP; have pP := pHall_pgroup pSyl_P.
have [S /= pSyl_S] := Sylow_exists p 'N(Q).
have [x _ sSxP] := Sylow_Jsub pSyl_P (subsetT _) (pHall_pgroup pSyl_S).
have [t tNQ] := Sylow_Jsub pSyl_S (normG _) (pgroupS sQP pP).
rewrite (normP tNQ) => sQS {t tNQ}.
have sQxP : Q :^ x \subset P by rewrite (subset_trans _ sSxP) // conjSg.
have [y yNP defQy] := pSylow_conj_sub_in_norm pSyl_P sQP sQxP.
have xyNQ : (x * y^-1) \in 'N(Q).
  by apply/normP; rewrite conjsgM defQy -conjsgM mulgV conjsg1.
have sSxyP : S :^ (x * y^-1) \subset P.
  by rewrite conjsgM sub_conjgV (normP yNP).
move: (pSyl_S); rewrite -(pHallJ _ _ xyNQ) /= => pSyl_Sxy.
have:= pHall_subl _ (subsetIr P _) pSyl_Sxy.
rewrite subsetI /= sSxyP (pHall_sub pSyl_Sxy); move/(_ (erefl _)) => pHall_S.
have [t]:= Sylow_Jsub pHall_S (subxx _) (pgroupS (subsetIl _ _) pP).
case/setIP=> xP xNQ XX.
rewrite (('N_P(Q) :=P: (S :^ (x * y^-1)) :^ t^-1) _).
  by rewrite pHallJ ?in_group.
rewrite eqEsubset -sub_conjg XX sub_conjg invgK.
by rewrite conjIg /= (conjGid xP) /= (conjGid xNQ) /= (pHall_sub pHall_S).
Qed.

(* This is B & G, Corollary 10.7(e). *)
Corollary pSylow_psubgroup_normal : forall P p, p.-Sylow(G) P ->
  forall Q R, p.-group R -> Q \subset P :&: R -> Q <| 'N(P) -> Q <| 'N(R).
Proof.
move=> P p pSyl_P Q R pR; rewrite subsetI; case/andP=> sQP sQR.
case/andP=> nQP sNPNQ.
rewrite /normal (subset_trans sQR (normG _)); apply/subsetP=> y yNR.
have [x _ sRxP] := Sylow_Jsub pSyl_P (subsetT _) pR.
move/normP: (yNR) => defRy; move: (sRxP); rewrite -defRy -conjsgM => sRyxP.
have sQxP : Q :^ x \subset P by apply: subset_trans _ sRxP; rewrite conjSg.
have sQyxP: Q :^ (y * x) \subset P by rewrite (subset_trans _ sRyxP) ?conjSg.
have [z zNP defQz] := pSylow_conj_sub_in_norm pSyl_P sQP sQyxP.
have [t tNP defQx] := pSylow_conj_sub_in_norm pSyl_P sQP sQxP.
move/normP: (subsetP sNPNQ _ zNP); move/normP: (subsetP sNPNQ _ tNP).
rewrite -defQx -defQz; move/normP=> xNQ; move/normP=> yxNQ.
by rewrite -(groupMr _ xNQ).
Qed.

Section AnotherMaximal.

Variable M : {group gT}.
Hypothesis M_max : M \in 'M.

Let Hall_G_Mbeta : 
  \beta(M).-Hall(M) M`_\beta -> \beta(M).-Hall(G) M`_\beta.
Proof.
move=> bHall_MB; rewrite pHallE subsetT /= (card_Hall bHall_MB) eqn_dvd.
rewrite partn_dvd ?cardG_gt0 ?cardSg ?subsetT //=.
apply/dvdn_partP; rewrite ?part_gt0 // => p.
rewrite inE /= primes_part mem_filter /=; case/andP=> alpha_p primesG_p.
rewrite partn_part=> [|q]; last by rewrite 2!inE; move/eqP=> ->.
have [P Syl_P] := Sylow_exists p M.
have SylGP : p.-Sylow(G) P.
  rewrite (Sylow_Sylow_sigma _ _ Syl_P) //. 
  by apply: alpha_sub_sigma M_max _ _; apply: beta_sub_alpha _ _.
rewrite -(card_Hall SylGP) (card_Hall Syl_P) sub_in_partn // => q _.
by rewrite 2!inE; move/eqP=> ->.
Qed.

Let all_normal_compl_sub_Fitting : forall (gT : finGroupType) (G : {group gT}), 
  (forall p, prime p -> p %| #|G| -> p^'.-Hall(G) 'O_p^'(G)) -> G \subset 'F(G).
Proof.
move=> rT G allNC; rewrite -{1}Sylow_gen gen_subG; apply/bigcupsP=> /= Q.
move/SylowP=> [q pr_q qHall_Q]; have sQG := pHall_sub qHall_Q.
case : (eqsVneq Q 1) => ntQ; first by rewrite ntQ; apply: sub1G.
have [_ qdQ _]:= pgroup_pdiv (pHall_pgroup qHall_Q) ntQ.
have qd : q %| #|G| := dvdn_trans qdQ (cardSg sQG).
have lt_q : q < #|G|.+1 by rewrite ltnS (dvdn_leq (cardG_gt0 _) qd).
pose P := [pred q | nat_of_ord (q :'I_#|G|.+1) \in \pi(G)].
have Pq : P (Ordinal lt_q) by rewrite /P /= inE /= mem_primes pr_q cardG_gt0 qd.
rewrite FittingEgen sub_gen // (bigcup_max _ Pq) //=.
rewrite -(eq_pcore _ (negnK _)) -bigcap_p'core subsetI sQG /=.
apply/bigcapsP=> [[r /= _]]; rewrite !inE /= => neq_rq.
case piGp: (r \in \pi(G)); last first.
  by rewrite pcore_pgroup_id // /pgroup -partn_eq1 ?cardG_gt0 ?p_part_eq1 ?piGp.
move: piGp; rewrite mem_primes; case/and3P => *.
rewrite (sub_Hall_pcore (allNC _ _ _)) //=.
apply: (sub_in_pnat _ (pHall_pgroup qHall_Q)) => e _; rewrite !inE /=.
by move/eqP=> ->; rewrite eq_sym.
Qed.

(* This is B & G, Lemma 10.8. *)
Lemma mmax_beta_Hall_nil_normal_compl_max_pdiv : 
  [/\ (*a*) \beta(M).-Hall(M) M`_\beta /\ \beta(M).-Hall(G) M`_\beta,
      (*b*) forall H,
               \beta(M)^'.-Hall(M^`(1)) H || \beta(M)^'.-Hall(M`_\sigma) H -> 
            nilpotent H
    & (*c*) forall p, prime p -> p \notin \beta(M) ->
           [/\ p^'.-Hall(M^`(1)) 'O_p^'(M^`(1)), 
               p^'.-Hall(M`_\sigma) 'O_p^'(M`_\sigma)
             & forall q, prime q -> q %| #| M / 'O_p^'(M) | -> q <= p]].
Proof.
have [MB bHall_MB] := Hall_exists \beta(M) (mmax_sol M_max).
have sMBMs : MB \subset M`_\sigma.  
  rewrite (sub_Hall_pcore (Hall_M_Msigma M_max)) ?(pHall_sub bHall_MB) //.
  move: (pHall_pgroup bHall_MB).
  by apply: sub_in_pnat=>? *; apply: (alpha_sub_sigma M_max (beta_sub_alpha _)).
have thmAC: forall p, p \notin \beta(M) -> [/\
    p^'.-Hall(M^`(1)) 'O_p^'(M^`(1)),
    p^'.-Hall(M`_\sigma) 'O_p^'(M`_\sigma),
    MB \subset 'O_p^'(M^`(1)) &
    forall q, prime q -> q %| #| M / 'O_p^'(M) | -> q <= p].
  move=> p n_pB; have [P pSyl_P] := Sylow_exists p M.
  have pl1M := mFT_proper_plength1 p (mmax_proper M_max).
  have solM := mmax_sol M_max; have oddM := mFT_odd M.
  have p'MB : p^'.-group MB.
    apply/pgroupP=> q pr_q qd; have:= pgroupP (pHall_pgroup bHall_MB) _ pr_q qd.
    by apply: contraL; rewrite /= inE /=; move/eqP=> ->; exact: n_pB.
  have ? : (2 < 'r_p(P)) ==> p.-length_1 M by rewrite pl1M implybT.
  case: (odd_narrow_plength1_complement_max_pdiv oddM _ pSyl_P)=> // [|ncM' sp].
    move: (n_pB); rewrite !inE negb_forall_in; case/exists_inP=> Q.
    rewrite inE negbK => sylQ; have [x _ ->]:= Sylow_trans sylQ pSyl_P.
    by rewrite narrowJ.
  have sMBOM' : MB \subset 'O_p^'(M^`(1)).
    rewrite (sub_Hall_pcore ncM') //.
    exact: subset_trans sMBMs (Msigma_sub_M' M_max).
  split=> //; apply: normal_max_pgroup_Hall _ (pcore_normal _ _) => /=.
  apply/maxgroupP; rewrite /psubgroup pcore_pgroup pcore_sub; split=> //= H.
  case/andP=> sHMs p'H sOH; apply/eqP; rewrite eqEsubset sOH andbT.
  have sI: 'O_p^'(M^`(1)) :&: M`_\sigma \subset 'O_p^'(M`_\sigma).
    rewrite pcore_max ?(pgroupS (subsetIl _ _) (pcore_pgroup _ _)) //=.
    rewrite /normal (subsetIr _ _) (subset_trans (pcore_sub _ _)) //.
    rewrite normsI // char_norm ?pcore_char //.
    by rewrite (char_trans _ (der_char 1 M)) // pcore_char.
  rewrite (subset_trans _ sI) // subsetI sHMs andbT.
  rewrite (sub_Hall_pcore ncM') //.
  by rewrite (subset_trans sHMs (Msigma_sub_M' M_max)).
have n_BM: ~~ \beta(M).-group M.
  have: M`_\alpha \proper M.
    rewrite (sub_proper_trans (Malpha_sub_Msigma M_max)) //.
    rewrite (sub_proper_trans (Msigma_sub_M' M_max)) //.
    exact: sol_der1_proper (mmax_sol M_max) (subxx _) (mmax_neq1 M_max).
  apply: contraL=> bM; have A_max := Hall_M_Malpha M_max.
  rewrite {2}(sub_pHall A_max) ?proper_irrefl ?pcore_sub //.
  by apply: sub_in_pnat _ bM => x _; apply: beta_sub_alpha.
have: existsb q, prime (q :'I_#|M|.+1) && ((q : nat) \notin \beta(M)).
  apply: contraR n_BM; rewrite negb_exists_in.
  move/forall_inP=> pr_x_B; apply/pgroupP=> p pr_p pd.
  have := dvdn_leq (cardG_gt0 _) pd; rewrite -ltnS => p_ltM.
  by have := pr_x_B (Ordinal p_ltM); rewrite pr_p negbK; move/(_ (erefl _)).
case/existsP=> q Pq; case/andP: (Pq) => pr_q nb_q.
pose Pr := fun p : 'I_#|M|.+1 => (p : nat) \notin beta(M).
pose SUM :=  \bigcap_(p < _ | Pr p) 'O_p^'(M^`(1)).
have bSUM : \beta(M).-group SUM.
  apply/pgroupP=> r pr_r /= rd.
  have r_ltM : r < #|M|.+1.
    rewrite ltnS (dvdn_leq (cardG_gt0 _) (dvdn_trans rd (cardSg _))) //=.
    by rewrite (@bigcap_min _ _ q) ?(subset_trans (pcore_sub _ _)) ?der_sub.
  apply: contraLR (pcore_pgroup (Ordinal r_ltM)^'(M^`(1))) => /= r_nB.
  have {rd} rd: r %| #|'O_(Ordinal r_ltM)^'(M^`(1))|.
    by apply: dvdn_trans rd (cardSg _); apply: bigcap_inf.
  by apply/pgroupP; move/(_ _ pr_r rd); rewrite !inE /=; case: eqP.
have defMB : MB :=: SUM.
  have sMB_SUM : MB \subset SUM by apply/bigcapsP=> /= i *; case: (thmAC i _).
  apply/eqP; rewrite eqEsubset sMB_SUM /=.
  rewrite -(sub_pHall bHall_MB bSUM) // (subset_trans _ (der_sub 1 _)) //.
  by rewrite (subset_trans _ (pcore_sub q^' _)) //= bigcap_inf.
have sMB_M := pHall_sub bHall_MB; have bMB := pHall_pgroup bHall_MB.
have nMMB : MB <| M.
  rewrite /normal sMB_M defMB norms_bigcap //; apply/bigcapsP=> i _.
  by rewrite char_norm ?(char_trans (pcore_char _ _)) // der_char.
have defMb: MB :=: M`_\beta by rewrite -(normal_Hall_pcore bHall_MB).
have thmA : \beta(M).-Hall(M) M`_\beta by rewrite -defMb.
have ?:= Hall_G_Mbeta thmA; split; [split | | move=> p *; case: (thmAC p)] =>//.
have b'MsMB : (\beta(M))^'.-group (M / MB).
  case/and3P: thmA => _ _; rewrite defMb -card_quotient //.
  by rewrite normal_norm ?pcore_normal.
move=> P pHall_P; have snMMB := normal_norm nMMB.
have b'P : (\beta(M))^'.-group P by case/orP: pHall_P; move/pHall_pgroup.
have sPM : P \subset M.
  case/orP: pHall_P => X; rewrite (subset_trans (pHall_sub X)) // ?der_sub //.
  exact: pcore_sub.
have TI: MB :&: P :=: 1.
  by rewrite (coprime_TIg (pnat_coprime _ b'P)) // defMB [_.-nat _]bSUM.
have nMBP : P \subset 'N(MB) by rewrite (subset_trans sPM).
have ? := subset_trans (pcore_sub \sigma(M) _) snMMB.
rewrite (isog_nil (quotient_isog nMBP TI)) /=.
case/orP: pHall_P => pHall_P; have sPX := pHall_sub pHall_P; last first.
  apply: nilpotentS _ (Fitting_nil (M`_\sigma / _)) => /=.
  apply: subset_trans (quotientS _ sPX) _ => /=.
  apply: all_normal_compl_sub_Fitting => p /= pr_p pd.
  have nb_p : p \notin \beta(M).
    apply: pgroupP b'MsMB _ pr_p (dvdn_trans pd (cardSg (quotientS _ _))) => /=.
    exact: pcore_sub.
  have [_ /= pHallO sMBO _] := thmAC _ nb_p.
  have ? : p^'.-group MB := pgroupS sMBO (pcore_pgroup _ _).
  rewrite pquotient_pcore ?quotient_pHall //; last first.
    by rewrite /normal 1?(subset_trans (pcore_sub _ _)) ?andbT.
  exact: subset_trans (pcore_sub _ _) _.
apply: nilpotentS _ (Fitting_nil (M^`(1) / _)) => /=.
rewrite (subset_trans (quotientS _ sPX)) //.
apply: all_normal_compl_sub_Fitting => p /= pr_p pd.
have nb_p : p \notin \beta(M).
  apply: pgroupP b'MsMB _ pr_p (dvdn_trans pd (cardSg (quotientS _ _))) => /=.
  exact: der_sub.
have [pHallO /= _ sMBO _] := thmAC _ nb_p.
have ? : p^'.-group MB := pgroupS sMBO (pcore_pgroup _ _).
have nMBM' : M^`(1) \subset 'N(MB) by rewrite (subset_trans (der_sub _ _)).
rewrite pquotient_pcore ?quotient_pHall /normal ?mul_subG ?nMBM' ?andbT //=.
  by rewrite (subset_trans (pcore_sub _ _)).
rewrite defMB (subset_trans _ (pcore_sub p^' _)) //=.
have lt_p : p < #|M|.+1.
  rewrite ltnS (leq_trans (dvdn_leq (cardG_gt0 _) pd)) //.
  rewrite (leq_trans (leq_quotient _ _)) //.
  by rewrite (dvdn_leq _ (cardSg (der_sub _ _))) ?cardG_gt0.
exact: (bigcap_inf _ (nb_p : Pr (Ordinal lt_p))).
Qed.

Let pq_group_pq'_core : forall (gT : finGroupType) (G : {group gT}), 
    forall pi qi : nat_pred, {subset pi <= qi^'} -> [predU pi & qi].-group G ->
  'O_pi(G) = 'O_qi^'(G).
Proof.
move=> rT W pi qi neq_pq pqW; apply/eqP.
rewrite eqEsubset !sub_in_pcore //; last by move=> x _; exact: neq_pq x.
move=> r; rewrite mem_primes; case/and3P=> pr_r _ rd.
have:= pgroupP pqW _ pr_r rd; rewrite inE /=; case/orP => //.
by rewrite !inE /= => ->.
Qed.

(* This is B & G, Corollary 10.9(a). *)
Corollary foo_10_9a : 
  forall p q, prime p -> prime q
   -> p != q -> p \notin \beta(M)-> q \notin \beta(M)->
  forall X : {group gT}, q.-subgroup(M) X -> (X \subset M^`(1)) || (p < q) ->
  [/\ (*a1*) exists2 P : {group gT}, p.-Sylow(M`_\sigma) P & X \subset 'C(P),
      (*a2*) p \in \alpha(M) -> 'C_M(X)%G \in 'U
    & (*a3*) q.-Sylow(M^`(1)) X -> 
          exists2 P : {group gT}, p.-Sylow(M^`(1)) P & P \subset 'N_M(X)^`(1)].
Proof.
move=> p q pr_p pr_q neq_pq pB' qB' X; case/andP=> sXM qX XM'.
pose pq := [predU (p : nat_pred) & (q : nat_pred) ].
have solM := mmax_sol M_max.
have sXM'M : (X <*> M^`(1)) \subset M by rewrite join_subG sXM der_sub.
have solXM' : solvable (X <*> M^`(1)) := solvableS sXM'M solM.
have pqX : pq.-group X.
  by apply: sub_in_pnat _ qX => x _ xq; rewrite inE /= xq orbT.
have [W /= pqHall_W sXW {pqX}] := Hall_superset solXM' (joing_subl _ _) pqX.
have b'W : \beta(M)^'.-group W.
  apply/pgroupP=> x pr_x xd; move: (pgroupP (pHall_pgroup pqHall_W) x pr_x xd).
  rewrite inE /=; apply: contraL; rewrite negb_or => /= xB; rewrite !inE /=.
  by case: eqP xB pB'=> [-> -> //|_ xB]; case: eqP xB qB' => // -> ->.
have [Ws/= b'Hall_Ws sWWs {b'W}]:=Hall_superset solXM' (pHall_sub pqHall_W) b'W.
have nilWM' : nilpotent (W :&: M^`(1)).
  apply: nilpotentS (setSI _ sWWs) _.
  have [_ th108 _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
  apply: th108 => /=; rewrite (Hall_setI_normal _ b'Hall_Ws) //=.
  by rewrite /normal joing_subr (subset_trans _ (char_norm (der_char _ _))).
have sWM := subset_trans sWWs (subset_trans (pHall_sub b'Hall_Ws) sXM'M).
have nilW : nilpotent W.
  case/orP: XM' => [sXM'|lt_pq].
    rewrite ((W :=P: W :&: M^`(1)) _) // eqEsubset subsetIl subsetI subxx.
    rewrite -(mulSGid sXM') -norm_joinEl ?(pHall_sub pqHall_W) //=.
    by rewrite (subset_trans sXM) // der_norm.
  have [_ _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
  move/(_ _ pr_p pB')=> [_ _]; move/(_ _ pr_q).
  case E: (_ %| _); first by rewrite leqNgt lt_pq; move/(_ (erefl _)).
  (* bug in equation generation + =>. try to add =>[|_] *)
  have nWOW : W \subset 'N('O_p^'(M) :&: W).
    rewrite normsI ?normG // (subset_trans (pHall_sub pqHall_W)) //. 
    by rewrite (subset_trans sXM'M) // bgFunc_norm.
  have qSyl_WO : q.-Sylow(W) ('O_p^'(M) :&: W).
    rewrite  -max_pgroup_Sylow; apply/maxgroupP; rewrite /psubgroup subsetIr.
    have -> : q.-group('O_p^'(M) :&: W).
      apply/pgroupP=> x pr_x xd.
      have p'x := dvdn_trans xd (cardSg (subsetIl _ _)).
      have qx := dvdn_trans xd (cardSg (subsetIr _ _)).
      have := pgroupP (pcore_pgroup _ _) _ pr_x p'x.
      have := pgroupP (pHall_pgroup pqHall_W) _ pr_x qx.
      by rewrite !inE /=; case/orP=> // => ->.
    split=> // H; case/andP=> sHW qH sOMWH; apply/eqP.
    have sHM := subset_trans sHW sWM.
    have ? : H \subset 'N('O_p^'(M)).
      by rewrite (subset_trans sHM) ?normal_norm ?pcore_normal.
    rewrite eqEsubset subsetI sOMWH sHW !andbT /=.
    rewrite -quotient_sub1 ?subG1 //= -[_ / _]setIid coprime_TIg //=.
    rewrite (pnat_coprime (quotient_pgroup _ qH)) //.
    rewrite [_.-nat _](pgroupS (quotientS _ sHM)) //.
    apply/pgroupP=> r pr_r rd; rewrite inE /=; apply/negP; rewrite /= inE /=.
    by move/eqP=> defq; move: E; rewrite -defq rd.
  have nM'W : W \subset 'N(M^`(1)) by rewrite (subset_trans sWM) ?der_norm.
  have qWWM' : q.-group (W / (M^`(1) :&: W)).
    rewrite /pgroup (card_isog (second_isog _)) //. 
    rewrite [_.-nat _](pgroupS (quotientS _ (pHall_sub pqHall_W))) //=.
    by rewrite (quotientYidr (subset_trans sXW nM'W)) quotient_pgroup // qX.
  have pSyl_OWM' : p.-Sylow(W) 'O_p(M^`(1) :&: W).
    rewrite  -max_pgroup_Sylow;apply/maxgroupP; rewrite /psubgroup pcore_pgroup.
    rewrite (subset_trans (pcore_sub _ _) (subsetIr _ _)); split=> //= P.
    case/andP=> sPW pP sOpMWP.
    have sPM'W : P \subset M^`(1) :&: W.
      have ? : P \subset 'N(W) := subset_trans sPW (normG _).
      have ? : P \subset 'N(M^`(1)).
        rewrite (subset_trans sPW) ?(subset_trans sWM) //.
        by rewrite normal_norm ?der_normal.
      rewrite -quotient_sub1 ?subG1 ?normsI //=.
      rewrite -[_ / _]setIid [_/_ :&: _]coprime_TIg //=.
      rewrite (pnat_coprime (quotient_pgroup _ pP)) //.
      rewrite [_.-nat _](pgroupS (quotientS _ sPW)) //.
      apply/pgroupP=> r pr_r rd; rewrite inE /=; apply/negP; rewrite /= inE /=.
      move/eqP=> defq; have := pgroupP qWWM' _ pr_r rd; rewrite /= inE /= defq.
      by move/eqP => XX; move/negP: neq_pq; rewrite XX eqxx.
    have pHall_OpM'W := nilpotent_pcore_Hall p nilWM'.
    apply/eqP; rewrite eqEsubset sOpMWP andbT //=.
    by rewrite setIC (sub_Hall_pcore pHall_OpM'W) //= setIC.
  move=> _; have pqW := pHall_pgroup pqHall_W.
  have s_pq' : {subset (p : nat_pred) <= q^'}.
    by move=> x; rewrite inE /=; move/eqP=> ->; rewrite !inE.
  have s_qp' : {subset (q:nat_pred) <= p^'}. 
    move=> x qx; rewrite inE /=; apply/negP; move/(s_pq' x).
    by rewrite inE /= qx.
  have nCqW : ('O_p^'(M) :&: W) <| W by rewrite /normal subsetIr.
  have defCq := normal_Hall_pcore qSyl_WO nCqW.
  have nCpW : 'O_p(M^`(1) :&: W) <| W.
    rewrite /normal (subset_trans (pcore_sub _ _) (subsetIr _ _)).
    by rewrite (subset_trans _ (char_norms (pcore_char _ _))) // normsI ?normG.
  have defCp := normal_Hall_pcore pSyl_OWM' nCpW.
  have defqpW : #|W|`_q = #|W|`_p^'.
    apply: eq_in_partn => x; rewrite mem_primes !inE /=; case/and3P=> pr_x _ xd.
    have := pgroupP pqW _ pr_x xd; rewrite !inE /=; do 2 case: eqP => //.
    by move=> -> defq; move: neq_pq; rewrite defq eqxx.
  have defpqW : #|W|`_p = #|W|`_q^'.
    apply: eq_in_partn => x; rewrite mem_primes !inE /=; case/and3P=> pr_x _ xd.
    have := pgroupP pqW _ pr_x xd; rewrite !inE /=; do 2 case: eqP => //.
    by move=> -> defq; move: neq_pq; rewrite defq eqxx.
  apply: nilpotentS _ (Fitting_nil W).
  apply: all_normal_compl_sub_Fitting => r pr_r rd.
  have := pgroupP pqW _ pr_r rd.
  rewrite !inE /=; case/orP; move/eqP=> ->; rewrite pHallE /=; last first.
    by rewrite -(pq_group_pq'_core s_pq') -?defpqW -?pHallE /= ?defCp //=.
  rewrite -(pq_group_pq'_core s_qp') -?defqpW -?pHallE /= ?defCq //.
  by apply: sub_in_pnat _ pqW=> x _; rewrite !inE /= orbC.
have nMsM' : M`_\sigma <| M^`(1).
  rewrite /normal (subset_trans (der_sub _ _)) ?andbT ?char_norm ?pcore_char //.
  exact: Msigma_sub_M' M_max.
have pSyl_OWMs : p.-Hall(M`_\sigma) ('O_p(W) :&: M`_\sigma).
  have nMs : M`_\sigma <| X <*> M^`(1).
    rewrite /normal (subset_trans (normal_sub nMsM')) ?joing_subr //=.
    have nsMsM: M`_\sigma <| M := pcore_normal _ M.
    by rewrite join_subG (subset_trans sXW) ?(subset_trans sWM) ?normal_norm.
  rewrite setIC (Sylow_setI_normal nMs) //=.
  apply: subHall_Sylow pqHall_W _ (nilpotent_pcore_Hall p nilW).
  by rewrite !inE /= eqxx.
have sXCWMs : X \subset 'C('O_p(W) :&: M`_\sigma).
  have sXOp' : X \subset 'O_p^'(W).  
    by rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ _)) ?(pi_p'group qX).
  rewrite (subset_trans sXOp') // (centsS (subsetIl _ _)) //.
  by case/dprodP: (nilpotent_pcoreC p nilW); rewrite centsC.
split; first by exists ('O_p(W) :&: M`_\sigma)%G.
  have prCMG := sub_proper_trans (subsetIl _ 'C(X)) (mmax_proper M_max).
  move=> pA; have pS := alpha_sub_sigma M_max pA; move: (pA).
  rewrite inE => /= rM; apply: rank3_Uniqueness prCMG _ => /=.
  have sPCMX : 'O_p(W) :&: M`_\sigma \subset 'C_M(X).
    by rewrite subsetI (subset_trans (subsetIr _ _) (pcore_sub _ _)) centsC.
  have sOMs : 'O_p(W) \subset M`_\sigma.
    rewrite (sub_Hall_pcore (Hall_M_Msigma M_max)).
      exact: pi_pgroup (pcore_pgroup _ _) pS.
    exact: subset_trans (pcore_sub _ _) sWM.
  have pSyl_O : p.-Sylow(M) 'O_p(W).
    apply: subHall_Sylow (Hall_M_Msigma M_max) pS _ => /=.
    apply: subHall_Sylow pSyl_OWMs _ _; rewrite ?inE //=.
    rewrite -max_pgroup_Sylow; apply/maxgroupP; rewrite /psubgroup subsetI.
    rewrite pcore_pgroup sOMs subxx; split => //= H; rewrite subsetI -andbA.
    by case/and3P=> sHO _ _ sOH; apply/eqP; rewrite eqEsubset sOH sHO.
  rewrite (leq_trans rM) // (leq_trans _ (rankS sPCMX)) //=.
  rewrite (rank_pgroup (pHall_pgroup pSyl_OWMs)) (p_rank_Sylow pSyl_OWMs).
  by rewrite -(p_rank_Sylow pSyl_O) p_rankS.
move=> qSyl_X.
have sWsM' : Ws \subset M^`(1).
  have := pHall_sub b'Hall_Ws.
  rewrite norm_joinEl ?(subset_trans sXM (der_norm _ _)) //.
  by rewrite (mulSGid (pHall_sub qSyl_X)).
have defX : 'O_q(Ws) :=: X.
  have b'Hall_WsM' := pHall_subl sWsM' (joing_subr _ _) b'Hall_Ws.
  have qSyl_XWs := pHall_subl (subset_trans sXW sWWs) sWsM' qSyl_X.
  have [_ th108b _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
  have := th108b Ws; rewrite b'Hall_WsM' /=; move/(_ (erefl _)) => nilWs.
  have [x xWs ->] := Sylow_trans (nilpotent_pcore_Hall q nilWs) qSyl_XWs.
  by rewrite (normP _) // (subsetP _ _ xWs) // char_norm ?pcore_char.
have defM' : M`_\beta <*> Ws :=: M^`(1).
  apply/eqP; rewrite eqEcard join_subG sWsM' andbT //=.
  have ? : M \subset 'N(M`_\beta) by rewrite char_norm ?pcore_char.
  rewrite norm_joinEr ?(subset_trans sWsM') ?(subset_trans (der_sub _ _)) //.
  rewrite -[#|M^`(1)|](partnC \beta(M) (cardG_gt0 _)) /=.
  rewrite coprime_cardMg; last first.
    by rewrite (pnat_coprime (pcore_pgroup _ _) (pHall_pgroup b'Hall_Ws)).
  rewrite -(part_pnat_id (pcore_pgroup _ _)) -/(beta_core M).
  rewrite -(part_pnat_id (pHall_pgroup b'Hall_Ws)).
  rewrite leq_mul ?andbT; last first.
  - rewrite (part_pnat_id (pHall_pgroup b'Hall_Ws)) (card_Hall b'Hall_Ws).
    by rewrite dvdn_leq // partn_dvd ?cardG_gt0 // cardSg // joing_subr.
  - have [[Hall_Mb _] _ _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
    rewrite (part_pnat_id (pHall_pgroup Hall_Mb)) (card_Hall Hall_Mb).
    by rewrite dvdn_leq // partn_dvd ?cardG_gt0 // cardSg // der_sub.
  apply: subset_trans (Mbeta_sub_Malpha _) _.
  apply: subset_trans (Malpha_sub_Msigma M_max) _.
  exact: Msigma_sub_M' M_max. 
have sOM'X := pcore_sub_Hall qSyl_X.
have nMbXM : M`_\beta <*> X <| M.
  have nWsMb : Ws \subset 'N(M`_\beta).
    rewrite (subset_trans sWsM') ?(subset_trans (der_sub 1 _)) //.
    exact: char_norm_trans (pcore_char _ _) (normG _).
  have ? : X \subset 'N(M`_\beta).
    rewrite (subset_trans (pHall_sub qSyl_X)) ?(subset_trans (der_sub _ _)) //.
    exact: char_norm (pcore_char _ _).
  have defXMB : X / M`_\beta = 'O_q(M^`(1) / _). 
    apply/eqP; rewrite -defM' joingC quotientYidr //.
    rewrite eqEcard (subset_trans _ (morphim_pcore _ _ _)) -?defX //=.
    have TI_Ws : M`_\beta :&: Ws = 1.
      apply: coprime_TIg (pnat_coprime (pcore_pgroup _ _) _).
      exact: pHall_pgroup b'Hall_Ws.
    have TI_X : M`_\beta :&: X = 1.
      apply: coprime_TIg (pnat_coprime (pcore_pgroup _ _) _).
      rewrite -defX (sub_in_pnat _ (pcore_pgroup q _)) // => r _.
      by rewrite 3!inE /=; move/eqP=> ->.
    rewrite -(card_isog (bgFunc_isog (bgFunc_pcore q) (quotient_isog _ _))) //=.
    by rewrite -(card_isog (quotient_isog _ _)) //= defX.
  apply: char_normal (char_from_quotient _ (pcore_char  \beta(M) _) _) => /=.
    by rewrite /normal joing_subl join_subG normG.
  rewrite joingC quotientYidr // defXMB.
  apply: char_trans (pcore_char _ _) _. 
  by rewrite /= quotient_der ?der_char // char_norm ?pcore_char.
pose U := 'N_M(X).
have defM : M :=: M`_\beta * U.
  have sXNMX : X \subset U by rewrite subsetI sXM normG.
  rewrite /U -(mulSGid sXNMX) /= -/U mulgA -norm_joinEr; last first.
    by rewrite (subset_trans sXM) // char_norm ?pcore_char.
  have ? : Ws \subset 'N(M`_\beta).
    rewrite (subset_trans sWsM') ?(subset_trans (der_sub _ _)) //.
    by rewrite normal_norm ?pcore_normal.
  rewrite (Frattini_arg _ (pHall_subl _ _ qSyl_X)) ?joing_subr /= -?defM' //.
  rewrite !norm_joinEr ?mulGS ?(subset_trans sXW) ?(subset_trans sWWs) //.
  by rewrite mulg_subr.
have sOWU : 'O_p(W) \subset U.
  rewrite subsetI (subset_trans (pcore_sub _ _)) ?sWM //= -defX.
  rewrite (subset_trans (pcore_sub _ _)) // (subset_trans sWWs) //.
  by rewrite char_norm ?pcore_char.
have pSyl_OW : p.-Sylow(M^`(1)) 'O_p(W).
  have := nilpotent_pcore_Hall p nilW.
  have := pHall_subl (subset_trans sWWs sWsM') (joing_subr _ _) pqHall_W => /=.
  rewrite !pHallE; case/andP=> sWM' cW; case/andP=> _ cOPW.
  rewrite (subset_trans (pcore_sub _ _) sWM') //= (eqP cOPW) (eqP cW) -partnI.
  apply/eqP; apply: eq_partn=> x; rewrite !inE; case: eqP => //.
  by rewrite andbC.
have cop : coprime #|'O_p(W)| #|M`_\beta|.
  apply: pnat_coprime (pcore_pgroup _ _) _; apply/pgroupP=> x pr_x xd.
  rewrite inE /=; apply/negP; move/(@eqP _ x p) => defx.
  rewrite defx in xd pr_x; move: (pgroupP (pcore_pgroup \beta(M) M) _ pr_x xd).
  by move => abs; rewrite abs in pB'.
have:= prod_norm_coprime_subs_derI (sym_eq defM) (pcore_normal _ _) sOWU cop.
rewrite (setIidPl (pHall_sub pSyl_OW)) /= -/U => defOW.
by move/setIidPl: (sym_eq defOW) => sOWU'; exists 'O_p(W)%G.
Qed.

(* This is B & G, Corollary 10.9(b). *)
Corollary foo_10_9b :
  forall H : {group gT}, H :!=: M -> H \in 'M -> 
  forall S : {group gT}, Sylow(G) S -> 'N(S) \subset H :&: M -> 
    M :=: (H :&: M) * M`_\beta /\ \alpha(M) =i \beta(M).
Proof.
move=> H neq_HM H_max S Syl_S sNSHM.
have ntS : S :!=: 1.
  have := (mmax_proper M_max); rewrite properE.
  by case: eqP sNSHM => // ->; rewrite norm1 subsetI subsetT; case/andP=> _ ->.
have [q pr_q qSyl_S] := SylowP _ _ Syl_S; have qS := pHall_pgroup qSyl_S.
move: sNSHM; rewrite subsetI; case/andP=> sNSH sNSM.
have sSM := subset_trans (normG _) sNSM.
have qSyl_SM := pHall_subl sSM (subsetT _) qSyl_S.
have qSig : q \in \sigma(M).
  by rewrite inE /=; apply/existsP; exists S; rewrite sNSM inE qSyl_SM.
have qA' : q \in \alpha(M)^'.
  rewrite inE /=; apply: contra neq_HM; rewrite inE /=.
  rewrite -(p_rank_Sylow qSyl_SM) -(rank_pgroup qS); move/rank3_Uniqueness.
  move/(_ (mFT_pgroup_proper qS)); move/uniq_mmaxP => [X defM].
  have sSH := subset_trans (normG _) sNSH.
  by rewrite (eq_uniq_mmax defM M_max sSM) (eq_uniq_mmax defM H_max sSH).
have qB' : q \notin \beta(M).
  by apply/negP; move/beta_sub_alpha => qA; move: qA'; rewrite inE /= qA.
have sSM' : S \subset M^`(1).
  apply: subset_trans (Msigma_sub_M' M_max).
  by rewrite (sub_Hall_pcore (Hall_M_Msigma M_max)) ?(pi_pgroup qS).
have nMbSM: M`_\beta <*> S <| M.
  have [[bSyl_Ms _] _ th10_8] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
  have ? : S \subset 'N(M`_\beta).
    by rewrite (subset_trans (pHall_sub qSyl_SM)) // normal_norm ?pcore_normal.
  have nMsMb : M`_\sigma / M`_\beta <| M / M`_\beta.
    by rewrite quotient_normal // pcore_normal.
  have defXMB : S / M`_\beta = 'O_q(M`_\sigma / _).
    have nilMs : nilpotent (M`_\sigma / M`_\beta).
      apply: nilpotentS _ (Fitting_nil (M`_\sigma / M`_\beta)).
      apply: all_normal_compl_sub_Fitting => r pr_r /= rd.
      have rB' : r \notin \beta(M).
        apply: contraL (prime_gt1 pr_r); rewrite -leqNgt => rB.
        move: bSyl_Ms; rewrite pHallE pcore_sub /=; move/eqP=> cMb.
        have := dvdn_trans rd (cardSg (quotientS _ (pcore_sub _ _))).
        rewrite card_quotient ?normal_norm ?pcore_normal //=.
        rewrite -divgS ?pcore_sub // cMb /=.
        rewrite -{1}[#|M|](partnC \beta(M)) ?cardG_gt0 //.
        rewrite mulnC mulnK ?part_gt0 // => rd2.
        have B'r:= pnat_dvd rd2 (part_pnat _ _).
        have Br: \beta(M).-nat r.
          apply/(pnatP _ (prime_gt0 pr_r)) => s pr_s.
          by rewrite (dvdn_prime2 pr_s pr_r); move/eqP=> ->.
        by have := pnat_coprime Br B'r; rewrite prime_coprime // dvdnn.
      have [_ rHall_Ms _]:= th10_8 _ pr_r rB'.
      have ? : M`_\sigma \subset 'N(M`_\beta).
        exact: subset_trans (pcore_sub _ _) (normal_norm (pcore_normal _ _)).
      have n1 : 'O_r^'(M`_\sigma) \subset 'N(M`_\beta).
        by rewrite (subset_trans (pcore_sub _ _)).
      have := quotient_pHall n1 rHall_Ms.
      have ? : r^'.-group M`_\beta.
        apply/pgroupP=> s pr_s sd; rewrite !inE /=; apply/negP; move/eqP=> defr.
        have := pgroupP (pcore_pgroup \beta(M) M) _ pr_s sd; rewrite defr => rB.
        by move: rB'; rewrite rB.
      rewrite /= -{3}quotientYidr // pquotient_pcore //= /normal.
        rewrite norm_joinEl //= mulGSid //; apply: sub_pcore => x xB.
        exact: (alpha_sub_sigma M_max (beta_sub_alpha xB)).
      have ? : M \subset 'N(M`_\beta) := normal_norm (pcore_normal _ _).
      by rewrite joing_subr join_subG ?(subset_trans (pcore_sub _ _)).
    have n2 : S \subset 'N(M`_\beta).
      exact: subset_trans sSM (normal_norm (pcore_normal _ _)).
    have qSyl_SQ := quotient_pHall n2 qSyl_S.
    apply: (nilpotent_Hall_pcore nilMs).
    apply: pHall_subl qSyl_SQ; rewrite quotientS ?subsetT //.
    by rewrite (sub_Hall_pcore (Hall_M_Msigma _)) ?(pi_pgroup qS).
  have nSM: S / M`_\beta <| M / M`_\beta.
    by rewrite defXMB (char_normal_trans _ nMsMb) // pcore_char.
  have ? := char_normal_trans (pcore_char q _) nMsMb.
  have n1 : M`_\beta <| M`_\beta <*> S.
    by rewrite /normal joing_subl join_subG normG.
  rewrite -(quotientGK n1) /= -{8}(quotientGK (pcore_normal \beta(M) M)) /=.
  rewrite joingC quotientYidr // morphpre_normal ?defXMB //=.
    rewrite !(subset_trans (pcore_sub _ _), morphimS) //.
    exact: normal_norm (pcore_normal _ _).
  exact: morphimS (normal_norm (pcore_normal _ _)).
have defM : M :=: M`_\beta * 'N_M(S).
  have sXNMX : S \subset 'N_M(S) by rewrite subsetI sSM normG.
  rewrite -(mulSGid sXNMX) /= mulgA -norm_joinEr; last first.
    by rewrite (subset_trans sSM) // char_norm ?pcore_char.
  by rewrite (Frattini_arg _ (pHall_subl _ _ qSyl_S)) ?joing_subr /= ?subsetT.
split.
  apply/eqP; rewrite eqEsubset mul_subG ?subsetIr ?pcore_sub ?andbT //.
  rewrite setIC group_modr ?pcore_sub //.
  apply: subset_trans (setIS _ (mulSg _ sNSH)). 
  have ? : 'N_M(S) \subset 'N(M`_\beta).
    by rewrite (subset_trans _ (char_norm (pcore_char _ _))) // subIset ?subxx.
  rewrite -group_modr ?pcore_sub //.
  by rewrite -norm_joinEl 1?joingC ?norm_joinEr //= -defM.
have nNMSU : 'N_M(S)%G \notin 'U.
  apply: contra neq_HM => nMSU; apply/eqP.
  have sNMSH : 'N_M(S) \subset H := subset_trans (subsetIr _ _) sNSH.
  exact: eq_uniq_mmax (def_uniq_mmax nMSU M_max (subsetIl _ _)) H_max sNMSH.
have qsubgS : q.-subgroup(M) S by rewrite /psubgroup qS sSM.
move=> p; apply/idP/idP => [pA|]; last exact: beta_sub_alpha.
case: (eqVneq p q) => [defp | nqpq].
  by move: pA; rewrite defp => qA; move: qA'; rewrite 2!inE /= qA.
have pr_p: prime p.
  have: p \in \pi(M) by rewrite sigma_sub_pi ?alpha_sub_sigma.
  by rewrite mem_primes; case/and3P.
apply: contraR (nNMSU) => pB'; apply: (uniq_mmaxS (setIS _ (cent_sub _))).
  exact: sub_proper_trans (subsetIl _ _) (mmax_proper M_max). 
by have [|_ -> //] := foo_10_9a pr_p pr_q nqpq pB' qB' qsubgS; rewrite sSM'.
Qed.

(* This is B & G, Proposition 10.10. *)
Lemma max_normed_2Elem_signaliser : forall p q (A Q : {group gT}),
    p != q -> A \in 'E_p^2(G) :&: 'E*_p(G) -> Q \in |/|*(A; q) ->
    q %| #|'C(A)| ->
  exists2 P : {group gT}, p.-Sylow(G) P /\ A \subset P
          & [/\ (*a*) 'O_p^'('C(P)) * ('N(P) :&: 'N(Q)) = 'N(P),
                (*b*) P \subset 'N(Q)^`(1)
              & (*c*) q.-narrow Q -> P \subset 'C(Q)].
Proof.
move=> p q A Q neq_pq; case/setIP=> Ep2A EpmA maxQ piCAq.
have [_ abelA dimA] := pnElemP Ep2A; have [pA cAA _] := and3P abelA.
have [p_pr oA] := (pnElem_prime Ep2A, card_pnElem Ep2A).
have{dimA} rA2: 'r(A) = 2 by rewrite (rank_abelem abelA).
have{EpmA} ncA: normed_constrained A.
  have ntA: A :!=: 1 by rewrite -rank_gt0 rA2.
  exact: plength_1_normed_constrained ntA EpmA (mFT_proper_plength1 _).
pose pi := \pi(A); pose K := 'O_pi^'('C(A)).
have def_pi : pi =i (p : nat_pred).
  by move=> r; rewrite !inE /= oA primes_exp ?primes_prime ?inE.
have pi'q : q \notin pi by rewrite def_pi !inE eq_sym.
have transKA: [transitive K, on |/|*(A; q) | 'JG].
  by rewrite normed_constrained_rank2_trans // (center_idP cAA) rA2.
have [P0 sylP0 sAP0] := Sylow_superset (subsetT _) pA.
have pP0: p.-group P0 := pHall_pgroup sylP0.
have piP0: pi.-group P0 by rewrite (eq_pgroup _ def_pi).
have{pP0} snAP0: A <|<| P0 := nilpotent_subnormal (pgroup_nil pP0) sAP0.
have{pi'q snAP0 ncA piP0} [//|] := normed_trans_superset ncA pi'q snAP0 piP0.
rewrite /= -/pi -/K => -> transKP submaxPA maxPfactoring.
have{transKP} [Q0 maxQ0 _] := imsetP transKP.
have{transKA} [k Kk defQ] := atransP2 transKA (subsetP submaxPA _ maxQ0) maxQ.
set P := P0 :^ k; have{sylP0} sylP: p.-Sylow(G) P by rewrite pHallJ ?in_setT.
have nAK: K \subset 'N(A) by rewrite cents_norm ?pcore_sub.
have{sAP0 nAK K Kk} sAP: A \subset P by rewrite -(normsP nAK k Kk) conjSg.
exists [group of P] => //.
have{maxPfactoring} [sPNQ' defNP] := maxPfactoring _ maxQ0.
move/(congr1 ('Js%act^~ k)): defNP sPNQ'; rewrite -(conjSg _ _ k) /=.
rewrite conjsMg !conjIg !conjsRg -!derg1 -!normJ -pcoreJ -centJ -/P.
rewrite -(congr_group defQ) (eq_pcore _ (eq_negn def_pi)) => defNP sPNQ'.
have{sPNQ'} sPNQ': P \subset 'N(Q)^`(1).
  by rewrite (setIidPl (pSylow_norm_split_sub_norm_der1 sylP)) in sPNQ'.
split=> // narrowQ; have [-> | ntQ] := eqsVneq Q 1; first exact: cents1.
pose AutQ := conj_aut Q @* 'N(Q).
have qQ: q.-group Q by case/mem_max_normed: maxQ.
have ltNG: 'N(Q) \proper G by rewrite mFT_norm_proper // (mFT_pgroup_proper qQ).
have{ltNG} qAutQ': q.-group AutQ^`(1).
  have qAutQq: q.-group 'O_q(AutQ) := pcore_pgroup _ _.
  rewrite (pgroupS _ qAutQq) // der1_min ?bgFunc_norm //.
  have solAutQ: solvable AutQ by rewrite morphim_sol -?mFT_sol_proper.
  have [oddQ oddAutQ]: odd #|Q| /\ odd #|AutQ| by rewrite morphim_odd mFT_odd.
  by case/(narrow_solvable_Aut qQ): (Aut_conj_aut Q 'N(Q)).
have nQP: P \subset 'N(Q) := subset_trans sPNQ' (der_sub 1 _).
rewrite (sameP setIidPl eqP) eqEsubset subsetIl /=.
rewrite -quotient_sub1 ?normsI ?normG ?norms_cent //= -ker_conj_aut subG1.
rewrite trivg_card1 (card_isog (first_isog_loc _ _)) //= -trivg_card1 -subG1.
have q'AutP: q^'.-group (conj_aut Q @* P).
  by rewrite morphim_pgroup //; exact: pi_pnat (pHall_pgroup sylP) _.
rewrite -(coprime_TIg (pnat_coprime qAutQ' q'AutP)) subsetI subxx.
by rewrite /= -morphim_der // morphimS.
Qed.

(* Notation for Proposition 11, which is the last to appear in this segment. *)
Local Notation sigma' := \sigma(gval M)^'.

(* This is B & G, Proposition 10.11(a). *)
Lemma sigma'_not_uniq : forall K, sigma'.-subgroup(M) K -> K \notin 'U.
Proof.
move=> K; case/andP=> sKM sg'K; have solM := mmax_sol M_max.
have [E hallE sKE] := Hall_superset solM sKM sg'K.
have [sEM sg'E _] := and3P hallE.
have rEle2: 'r(E) <= 2.
  have [q _ ->] := rank_witness E; rewrite leqNgt; apply/negP=> rEgt2.
  have: q \in sigma' by rewrite (pnatPpi sg'E) // -p_rank_gt0 -(subnKC rEgt2).
  by rewrite inE /= alpha_sub_sigma //; exact: leq_trans (p_rankS q sEM).
have [E1 | ntE]:= eqsVneq E 1.
  by apply: contraL (@uniq_mmax_neq1 _ K) _; rewrite -subG1 -E1.
pose p := max_pdiv #|E|; pose P := 'O_p(E).
have piEp: p \in \pi(E) by rewrite pi_max_pdiv cardG_gt1.
have sg'p: p \in sigma' by rewrite (pnatPpi sg'E).
have sylP: p.-Sylow(E) P.
  rewrite rank2_max_pcore_Sylow ?mFT_odd ?(solvableS sEM solM) //.
  exact: leq_trans (rankS (Fitting_sub E)) rEle2.
apply: contra (sg'p) => uniqK; apply/existsP; exists [group of P].
have defMK := def_uniq_mmax uniqK M_max (subset_trans sKE sEM).
rewrite inE (subHall_Sylow hallE) // (sub_uniq_mmax defMK) //; last first.
  rewrite mFT_norm_proper ?(mFT_pgroup_proper (pcore_pgroup _ _)) //.
  by rewrite -cardG_gt1 (card_Hall sylP) p_part_gt1.
by rewrite (subset_trans sKE) // bgFunc_norm.
Qed.

(* This is B & G, Proposition 10.11(b). *)
Lemma sub'cent_sigma_rank1 : forall K,
  sigma'.-subgroup(M) K -> 'r('C_K(M`_\sigma)) <= 1.
Proof.
move=> K sg'M_K; have [sKM sg'K] := andP sg'M_K.
rewrite leqNgt; apply/rank_geP=> [[A]]; case/nElemP=> p Ep2A.
have p_pr := pnElem_prime Ep2A.
have [sACKMs abelA dimA] := pnElemP Ep2A; rewrite subsetI centsC in sACKMs.
have{sACKMs} [sAK cAMs]: A \subset K /\ M`_\sigma \subset 'C(A) := andP sACKMs.
have sg'p: p \in sigma'.
  by rewrite (pgroupP (pgroupS sAK sg'K)) // (card_pnElem Ep2A) dvdn_mull.
have [Ms1 | [q q_pr q_dvd_Ms]] := trivgVpdiv M`_\sigma.
  by case/eqP: (Msigma_neq1 M_max).
have sg_q: q \in \sigma(M) := pgroupP (pcore_pgroup _ _) _ q_pr q_dvd_Ms.
have neq_pq: p != q by apply: contraNneq sg'p => ->.
have [Q sylQ] := Sylow_exists q M`_\sigma; have [sQMs qQ _] := and3P sylQ.
have cAQ: Q \subset 'C(A) := subset_trans sQMs cAMs.
have{q_dvd_Ms} q_dv_CA: q %| #|'C(A)|.
  rewrite (dvdn_trans _ (cardSg cAQ)) // -(part_pnat_id (pnat_id q_pr)).
  by rewrite (card_Hall sylQ) partn_dvd.
have{cAQ} maxQ: Q \in |/|*(A; q).
  rewrite inE; apply/maxgroupP; rewrite qQ cents_norm 1?centsC //.
  split=> // Y; case/andP=> qY _ sQY; apply: sub_pHall qY sQY (subsetT Y).
  by rewrite (subHall_Sylow (Hall_G_Msigma M_max)).
have sNQM: 'N(Q) \subset M.
  by rewrite (norm_Sylow_sigma sg_q) // (subHall_Sylow (Hall_M_Msigma _)).
have rCAle2: 'r('C(A)) <= 2.
  apply: contraR (sigma'_not_uniq sg'M_K); rewrite -ltnNge => rCAgt2.
  apply: uniq_mmaxS sAK (sub_mmax_proper M_max sKM) _.
  by apply: cent_rank3_Uniqueness rCAgt2; rewrite (rank_abelem abelA) dimA.
have max2A: A \in 'E_p^2(G) :&: 'E*_p(G).
  rewrite 3!inE subsetT abelA dimA; apply/pmaxElemP; rewrite inE subsetT.
  split=> // Y; case/pElemP=> _ abelY; have [pY cYY _] := and3P abelY.
  case/eqVproper=> // ltAY.
  suffices: 'r_p('C(A)) > 2 by rewrite ltnNge (leq_trans (p_rank_le_rank p _)).
  rewrite -dimA (leq_trans (properG_ltn_log pY ltAY)) //.
  by rewrite logn_le_p_rank // inE centsC (subset_trans (proper_sub ltAY)).
have{rCAle2 cAMs} Ma1: M`_\alpha = 1.
  apply: contraTeq rCAle2; rewrite -rank_gt0 -ltnNge.
  have [r _ ->] := rank_witness M`_\alpha; rewrite p_rank_gt0.
  move/(pnatPpi (pcore_pgroup _ _))=> a_r; apply: (leq_trans a_r).
  have [R sylR] := Sylow_exists r M`_\sigma.
  have sylR_M: r.-Sylow(M) R.
    by rewrite (subHall_Sylow (Hall_M_Msigma M_max)) ?alpha_sub_sigma.
  rewrite -(p_rank_Sylow sylR_M) (p_rank_Sylow sylR).
  by rewrite (leq_trans (p_rank_le_rank r _)) // rankS // centsC.
have{Ma1} nilM': nilpotent M^`(1).
  by rewrite (isog_nil (quotient1_isog _)) -Ma1 nil_M'Malpha.
have{max2A maxQ neq_pq q_dv_CA} [P [sylP sAP] sPNQ']:
  exists2 P : {group gT}, p.-Sylow(G) P /\ A \subsetP & P \subset 'N(Q)^`(1).
- by case/(max_normed_2Elem_signaliser neq_pq): maxQ => // P ? []; exists P.
have{sNQM} defP: 'O_p(M^`(1)) = P.
  rewrite (nilpotent_Hall_pcore nilM' (pHall_subl _ _ sylP)) ?subsetT //.
  by rewrite (subset_trans sPNQ') ?dergS.
have charP: P \char M by rewrite -defP (char_trans (pcore_char p _)) ?der_char.
case/existsP: sg'p; exists P.
rewrite inE (pHall_subl (char_sub charP) (subsetT M) sylP) //=.
rewrite (mmax_normal M_max) ?char_normal // -rank_gt0.
by rewrite (leq_trans _ (rankS sAP)) // (rank_abelem abelA) dimA.
Qed.

(* This is B & G, Proposition 10.11(c). *)
Lemma sub'cent_sigma_cyclic : forall K (Y := 'C_K(M`_\sigma) :&: M^`(1)),
  sigma'.-subgroup(M) K -> cyclic Y /\ Y <| M.
Proof.
move=> K Y sg'M_K; have [sKM sg'K] := andP sg'M_K; pose Z := 'O_sigma'('F(M)).
have nsZM: Z <| M := char_normal_trans (pcore_char _ _) (Fitting_normal M).
have [sZM nZM] := andP nsZM; have Fnil := Fitting_nil M.
have rZle1: 'r(Z) <= 1.
  have sg'Z: sigma'.-subgroup(M) Z by rewrite /psubgroup sZM pcore_pgroup.
  apply: leq_trans (rankS _) (sub'cent_sigma_rank1 sg'Z).
  rewrite subsetI subxx (sameP commG1P trivgP) /=.
  rewrite -(TI_pcoreC \sigma(M) M 'F(M)) subsetI commg_subl commg_subr.
  by rewrite (subset_trans sZM) ?bgFunc_norm ?(subset_trans (pcore_sub _ _)).
have{rZle1} cycZ: cyclic Z.
  have nilZ: nilpotent Z := nilpotentS (pcore_sub _ _) Fnil. 
  by rewrite nil_Zgroup_cyclic // odd_rank1_Zgroup // mFT_odd.
have cZM': M^`(1) \subset 'C_M(Z).
  rewrite der1_min ?normsI ?normG ?norms_cent //= -ker_conj_aut.
  rewrite (isog_abelian (first_isog_loc _ _)) //.
  by rewrite (abelianS (Aut_conj_aut _ _)) // Aut_cyclic_abelian.
have sYF: Y \subset 'F(M).
  apply: subset_trans (cent_sub_Fitting (mmax_sol M_max)).
  have [_ /= <- _ _] := dprodP (nilpotent_pcoreC \sigma(M) Fnil).
  by rewrite centM setICA setISS // setIC subIset ?centS // pcore_Fitting.
have{sYF} sYZ: Y \subset Z.
  rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ Fnil)) //=.
  by rewrite -setIA (pgroupS (subsetIl K _)).
by rewrite (cyclicS sYZ cycZ) (char_normal_trans _ nsZM) // sub_cyclic_char.
Qed.

(* This is B & G, Proposition 10.11(d). *)
Lemma commG_sigma'_1Elem_cyclic : forall p K P (K0 := [~: K, P]),
    sigma'.-subgroup(M) K -> p \in sigma' -> P \in 'E_p^1('N_M(K)) ->
    'C_(M`_\sigma)(P) = 1 -> p^'.-group K -> abelian K ->
  [/\ K0 \subset 'C(M`_\sigma), cyclic K0 & K0 <| M].
Proof.
move=> p K P K0 sg'M_K sg'p EpP regP p'K cKK; have [sKM sg'K]:= andP sg'M_K.
have nK0P: P \subset 'N(K0) := commg_normr P K.
have p_pr := pnElem_prime EpP; have [sPMN _ oP] := pnElemPcard EpP.
have [sPM nKP]: P \subset M /\ P \subset 'N(K) by apply/andP; rewrite -subsetI.
have [sMsM nMsM] := andP (pcore_normal _ _ : M`_\sigma <| M).
have sK0K: K0 \subset K by rewrite commg_subl.
have [sK0M sg'K0]:= (subset_trans sK0K sKM, pgroupS sK0K sg'K).
have [nMsK0 nMsP] := (subset_trans sK0M nMsM, subset_trans sPM nMsM).
have coKP: coprime #|K| #|P| by rewrite oP coprime_sym prime_coprime -?p'natE.
have coK0Ms: coprime #|K0| #|M`_\sigma|.
  by rewrite coprime_sym (pnat_coprime (pcore_pgroup _ _)).
have nilK0Ms: nilpotent (K0 <*> M`_\sigma).
  have mulK0MsP: K0 <*> M`_\sigma ><| P = K0 <*> M`_\sigma <*> P.
    rewrite sdprodEY ?normsY // coprime_TIg //= norm_joinEl //.
    rewrite coprime_cardMg // coprime_mull (coprimeSg sK0K) //.
    by rewrite oP (pnat_coprime (pcore_pgroup _ _)) ?pnatE.
  apply: (prime_Frobenius_sol_kernel_nil mulK0MsP); rewrite ?oP //=.
    by rewrite (solvableS _ (mmax_sol M_max)) // !join_subG sK0M pcore_sub.
  rewrite norm_joinEl // -subcent_TImulg ?subsetI ?nK0P //.
    by rewrite coprime_abel_cent_TI ?mul1g.
  exact: coprime_TIg.
have cMsK0: K0 \subset 'C(M`_\sigma).
  rewrite (sub_nilpotent_cent2 nilK0Ms) ?joing_subl ?joing_subr //.
  exact: pnat_coprime (pcore_pgroup _ _) sg'K0.
have sg'M_K0: sigma'.-subgroup(M) K0 by exact/andP.
have [cycY nsYM] := sub'cent_sigma_cyclic sg'M_K0.
set Y := _ :&: _ in cycY nsYM.
have sK0Y: K0 \subset Y by rewrite !subsetI subxx cMsK0 commgSS.
split=> //; first exact: cyclicS sK0Y cycY.
by apply: char_normal_trans nsYM; rewrite sub_cyclic_char.
Qed.

End AnotherMaximal.

(* This is B & G, Lemma 10.12. *)
Lemma sigma_disjoint : forall M H,
    M \in 'M -> H \in 'M -> gval H \notin M :^: G ->
  [/\ (*a*) M`_\alpha :&: H`_\sigma = 1,
            [predI \alpha(M) & \sigma(H)] =i pred0
    & (*b*) nilpotent M`_\sigma ->
            M`_\sigma :&: H`_\sigma = 1
         /\ [predI \sigma(M) & \sigma(H)] =i pred0].
Proof.
move=> M H maxM maxH notjMH.
suffices sigmaMHnil: forall p, p \in [predI \sigma(M) & \sigma(H)] ->
  p \notin \alpha(M) /\ ~~ nilpotent M`_\sigma.
- have a2: [predI \alpha(M) & \sigma(H)] =i pred0.
    move=> p; apply/andP=> [[/= aMp sHp]].
    by case: (sigmaMHnil p); rewrite /= ?aMp // inE /= alpha_sub_sigma.
  split=> // [|nilMs].
    rewrite coprime_TIg // (pnat_coprime (pcore_pgroup _ _)) //.
    apply: sub_in_pnat (pcore_pgroup _ _) => p _ sHp.
    by apply: contraFN (a2 p); rewrite inE /= sHp andbT.
  have b2: [predI \sigma(M) & \sigma(H)] =i pred0.
    by move=> p; apply/negP; case/sigmaMHnil => _; rewrite nilMs.
  rewrite coprime_TIg // (pnat_coprime (pcore_pgroup _ _)) //.
  apply: sub_in_pnat (pcore_pgroup _ _) => p _ sHp.
  by apply: contraFN (b2 p); rewrite inE /= sHp andbT.
move=> p; case/andP=> sMp sHp; have [S sylS]:= Sylow_exists p M.
have [sSM pS _] := and3P sylS.
have sylS_G: p.-Sylow(G) S := Sylow_Sylow_sigma maxM sMp sylS.
have [g sSHg]: exists g, S \subset H :^ g.
  have [Sg' sylSg']:= Sylow_exists p H.
  have [g _ ->] := Sylow_trans (Sylow_Sylow_sigma maxH sHp sylSg') sylS_G.
  by exists g; rewrite conjSg (pHall_sub sylSg').
have{notjMH} neqHgM: H :^ g != M.
  by apply: contraNneq notjMH => <-; rewrite orbit_sym mem_orbit ?in_setT.
do [split; apply: contra neqHgM] => [|nilMs].
  rewrite !inE -(p_rank_Sylow sylS) -rank_pgroup //= => rS_gt3.
  have uniqS: S \in 'U := rank3_Uniqueness (mFT_pgroup_proper pS) rS_gt3.
  have defUS: 'M(S) = [set M] := def_uniq_mmax uniqS maxM sSM.
  by rewrite (eq_uniq_mmax defUS _ sSHg) ?mmaxJ.
have nsSM: S <| M.
  have nsMsM: M`_\sigma <| M by exact: pcore_normal.
  have{sylS} sylS: p.-Sylow(M`_\sigma) S.
    apply: pHall_subl (pcore_sub _ _) sylS => //.
    by rewrite (sub_Hall_pcore (Hall_M_Msigma maxM)) ?(pi_pgroup pS).
  rewrite (nilpotent_Hall_pcore nilMs sylS).
  by rewrite (char_normal_trans (pcore_char _ _)).
have sNS_Hg: 'N(S) \subset H :^ g.
  rewrite -sub_conjgV -normJ (norm_Sylow_sigma sHp) //.
  by rewrite (pHall_subl _ (subsetT _)) ?sub_conjgV // pHallJ ?in_setT.
have ltHg: H :^ g \proper G by rewrite mmax_proper ?mmaxJ //.
rewrite (mmax_max maxM ltHg) // -(mmax_normal maxM nsSM) //.
by apply: contraTneq sNS_Hg => ->; rewrite norm1 proper_subn.
Qed.

(* This is B & G, Lemma 10.13. *)
Lemma basic_p2maxElem_structure : forall p A P,
    A \in 'E_p^2(G) :&: 'E*_p(G) -> p.-group P -> A \subset P -> ~~ abelian P ->
  let Z0 := ('Ohm_1('Z(P)))%G in
  [/\ (*a*) Z0 \in 'E_p^1(A),
      (*b*) exists Y : {group gT},
            [/\ cyclic Y, Z0 \subset Y
              & forall A0, A0 \in 'E_p^1(A) :\ Z0 -> A0 \x Y = 'C_P(A)]
    & (*c*) [transitive 'N_P(A), on 'E_p^1(A) :\ Z0| 'JG]].
Proof.
move=> p A P; case/setIP=> Ep2A EpmA pP sAP not_cPP Z0; set E1A := 'E_p^1(A).
have p_pr: prime p := pnElem_prime Ep2A; have [_ abelA dimA2] := pnElemP Ep2A.
have [oA [pA cAA _]] := (card_pnElem Ep2A, and3P abelA).
have [p_gt0 p_gt1] := (prime_gt0 p_pr, prime_gt1 p_pr).
have{EpmA} subApG: forall S,
  p.-group S -> A \subset S -> noncyclic_narrow p S /\ 'Ohm_1('C_S(A)) = A.
- move=> S pS sAS; have{EpmA} EpmA: A \in 'E*_p(S).
    by rewrite (subsetP (pmaxElemS p (subsetT S))) // inE EpmA inE.
  split; first by apply/set0Pn; exists A; rewrite 3!inE sAS abelA dimA2.
  by rewrite (Ohm1_cent_max EpmA) // (pgroupS _ pS) subsetIl.
have [S sylS sPS] := Sylow_superset (subsetT P) pP.
pose Z1 := 'Ohm_1('Z(S))%G; have sZ1Z: Z1 \subset 'Z(S) := Ohm_sub 1 _.
have [pS sAS] := (pHall_pgroup sylS, subset_trans sAP sPS).
have [narrowS defC1] := subApG S pS sAS; set C := 'C_S(A) in defC1.
have sZ0A: Z0 \subset A by rewrite -defC1 OhmS // setISS // centS.
have sZ1A: Z1 \subset A by rewrite -defC1 OhmS // setIS // centS.
have [pZ0 pZ1]: p.-group Z0 /\ p.-group Z1 by split; exact: pgroupS pA.
have sZ10: Z1 \subset Z0.
  rewrite -[gval Z1]Ohm_id OhmS // subsetI (subset_trans sZ1A) //=.
  by rewrite (subset_trans sZ1Z) // subIset // centS ?orbT.
have ntZ1: Z1 :!=: 1.
  have: A :!=: 1 by rewrite -cardG_gt1 oA (ltn_exp2l 0).
  apply: contraNneq; rewrite -subG1 -(setIidPr sZ1Z); move/TI_Ohm1.
  by rewrite setIid; move/(trivg_center_pgroup pS) <-.
have EpZ01: abelian C -> Z1 = Z0 /\ Z0 \in E1A.
  move=> cCC; have [eqZ0A | ltZ0A] := eqVproper sZ0A.
    rewrite (abelianS _ cCC) // in not_cPP.
    by rewrite subsetI sPS centsC -eqZ0A (subset_trans (Ohm_sub _ _)) ?subsetIr.
  have leZ0p: #|Z0| <= p ^ 1.
    by rewrite (card_pgroup pZ0) leq_exp2l // -ltnS -dimA2 properG_ltn_log.
  have [_ _ [e oZ1]] := pgroup_pdiv pZ1 ntZ1.
  have{e oZ1}: #|Z1| >= p by rewrite oZ1 (leq_exp2l 1).
  rewrite (geq_leqif (leqif_trans (subset_leqif_card sZ10) (leqif_eq leZ0p))).
  rewrite [E1A]p1ElemE // !inE sZ0A; case/andP=> sZ01 ->.
  by split=> //; apply/eqP; rewrite -val_eqE eqEsubset sZ10.
have [A1 neqA1Z EpA1]: exists2 A1, A1 != Z1 & #|Z1| = p -> A1 \in E1A.
  have [oZ1 |] := #|Z1| =P p; last by exists 1%G; rewrite // eq_sym.
  have [A1 defA]:= abelem_split_dprod abelA sZ1A.
  have{defA} [_ defA _ tiA1Z1] := dprodP defA.
  have EpZ1: Z1 \in E1A by rewrite [E1A]p1ElemE // !inE sZ1A /= oZ1.
  suffices: A1 \in E1A by exists A1; rewrite // eq_sym; exact/(TIp1ElemP EpZ1).
  rewrite [E1A]p1ElemE // !inE -defA mulG_subr /=.
  by rewrite -(mulKn #|A1| p_gt0) -{1}oZ1 -TI_cardMg // defA oA mulKn.
pose cplA1C Y := [/\ cyclic Y, Z0 \subset Y, A1 \x Y = C & abelian C].
have [Y [{cplA1C} cycY sZ0Y defC cCC]]: exists Y, cplA1C Y.
  have [rSgt2 | rSle2] := ltnP 2 'r(S).
    rewrite (rank_pgroup pS) in rSgt2; have oddS := mFT_odd S.
    have oZ1: #|Z1| = p by case: (p_rank_3_maxElem_2_Ohm_ucn pS).
    have{EpA1} EpA1 := EpA1 oZ1; have [sA1A abelA1 oA1] := pnElemPcard EpA1.
    have EpZ1: Z1 \in E1A by rewrite [E1A]p1ElemE // !inE sZ1A /= oZ1.
    have [_ defA cA1Z tiA1Z] := dprodP (p2Elem_dprodP Ep2A EpA1 EpZ1 neqA1Z).
    have defC: 'C_S(A1) = C.
      rewrite /C -defA centM setICA setIC ['C_S(Z1)](setIidPl _) // centsC.
      by rewrite (subset_trans sZ1Z) ?subsetIr.
    have rpCSA1le2: 'r_p('C_S(A1)) <= 2.
      by rewrite defC -p_rank_Ohm1 defC1 (p_rank_abelem abelA) dimA2.
    have sA1S := subset_trans sA1A sAS.
    case: (odd_rank3_narrow pS _ _  _ oA1) => //; set Y := 'C_('C_S(_))(A1).
    rewrite {}defC => cycY _ _; move/esym=> defC; exists [group of Y].
    have cCC: abelian C; last split=> //.
      apply/center_idP; rewrite -(center_dprod defC).
      rewrite (center_idP (abelem_abelian abelA1)).
      by rewrite (center_idP (cyclic_abelian cycY)).
    have{EpZ01} [<- _] := EpZ01 cCC; rewrite subsetI (subset_trans sZ1Z) //.
    by rewrite setIS ?centS // (subset_trans (Ohm_sub 1 _)) ?ucn_sub.
  have:= pSylow_rank3_abelian_or_Ohm_Z_decomp sylS rSle2.
  case=> [cSS | [E [Y [[_ defS] dimE3 eE cycY defY1]]]].
    by rewrite (abelianS sPS) in not_cPP.
  have [[_ mulEY cEY] cYY] := (cprodP defS, cyclic_abelian cycY).
  have defY: 'Z(S) = Y.
    case/cprodP: (center_cprod defS) => _ <- _.
    by rewrite (center_idP cYY) -defY1 mulSGid ?Ohm_sub.
  have pY: p.-group Y by rewrite -defY (pgroupS (center_sub S)).
  have sES: E \subset S by rewrite -mulEY mulG_subl.
  have pE := pgroupS sES pS.
  have defS1: 'Ohm_1(S) = E.
    apply/eqP; rewrite (OhmE 1 pS) eqEsubset gen_subG andbC.
    rewrite sub_gen; last by rewrite subsetI sES sub_LdivT.
    apply/subsetP=> ey; case/LdivP; rewrite -mulEY.
    case/imset2P=> e y Ee Yy -> eyp; rewrite groupM //.
    rewrite (subsetP (center_sub E)) // -defY1 (OhmE 1 pY) mem_gen //.
    rewrite expMgn in eyp; last by red; rewrite -(centsP cEY).
    by rewrite (exponentP eE) // mul1g in eyp; rewrite !inE Yy eyp eqxx.
  have sAE: A \subset E by rewrite -defS1 -(Ohm1_id abelA) OhmS.
  have defC: A * Y = C.
    rewrite /C -mulEY setIC -group_modr; last first.
      by rewrite -defY subIset // orbC centS.
    congr (_ * _); apply/eqP; rewrite /= setIC eqEcard subsetI sAE.
    have pCEA: p.-group 'C_E(A) := pgroupS (subsetIl E _) pE.
    rewrite -abelianE cAA (card_pgroup pCEA) oA leq_exp2l //= leqNgt.
    apply: contraL cycY => dimCEA3.
    have sAZE: A \subset 'Z(E).
      rewrite subsetI sAE // centsC (sameP setIidPl eqP) eqEcard subsetIl /=.
      by rewrite (card_pgroup pE) (card_pgroup pCEA) dimE3 leq_exp2l.
    rewrite abelian_rank1_cyclic // -ltnNge (rank_pgroup pY).
    by rewrite (p_rank_abelian p cYY) defY1 -dimA2 lognSg.
  have cAY: Y \subset 'C(A) by exact: centSS _ _ cEY.
  have cCC: abelian C by rewrite -defC abelianM cAA cYY centsC.
  have{EpZ01} [eqZ10 EpZ1] := EpZ01 cCC; rewrite -eqZ10 in EpZ1.
  have sZ0Y: Z0 \subset Y by rewrite -eqZ10 -defY Ohm_sub.
  have{EpA1} EpA1 := EpA1 (card_pnElem EpZ1).
  have [sA1A _ oA1] := pnElemPcard EpA1.
  have [_ defA _ tiA1Z] := dprodP (p2Elem_dprodP Ep2A EpA1 EpZ1 neqA1Z).
  exists Y; split; rewrite // dprodE ?(centSS _ sA1A cAY) ?prime_TIg ?oA1 //.
    by rewrite -(mulSGid sZ0Y) -eqZ10 mulgA defA.
  apply: contraL cycY => sA1Y; rewrite abelian_rank1_cyclic // -ltnNge.
  by rewrite -dimA2 -rank_abelem ?rankS // -defA eqZ10 mul_subG.
have{EpZ01} [eqZ10 EpZ0] := EpZ01 cCC; have oZ0 := card_pnElem EpZ0.
have{EpA1} EpA1: A1 \in E1A by rewrite EpA1 ?eqZ10.
have [sA1A _ oA1] := pnElemPcard EpA1; rewrite {}eqZ10 in neqA1Z.
have [_ defA _ tiA1Z] := dprodP (p2Elem_dprodP Ep2A EpA1 EpZ0 neqA1Z).
split=> //; first exists (P :&: Y)%G.
  have sPY_Y := subsetIr P Y; rewrite (cyclicS sPY_Y) //.
  rewrite subsetI (subset_trans sZ0A) //= sZ0Y.
  split=> // A0; case/setD1P=> neqA0Z EpA0; have [sA0A _ _] := pnElemP EpA0.
  have [_ mulA0Z _ tiA0Z] := dprodP (p2Elem_dprodP Ep2A EpA0 EpZ0 neqA0Z).
  have{defC} [_ defC cA1Y tiA1Y] := dprodP defC.
  rewrite setIC -{2}(setIidPr sPS) setIAC.
  apply: dprod_modl (subset_trans sA0A sAP); rewrite -defC dprodE /=.
  - by rewrite -(mulSGid sZ0Y) !mulgA mulA0Z defA.
  - rewrite (centSS (subxx Y) sA0A) // -defA centM subsetI cA1Y /=.
    by rewrite sub_abelian_cent ?cyclic_abelian.
  rewrite setIC -(setIidPr sA0A) setIA -defA -group_modr //.
  by rewrite (setIC Y) tiA1Y mul1g setIC.
apply/imsetP; exists A1; first by rewrite 2!inE neqA1Z.
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split.
  apply/subsetP=> A1x; case/imsetP=> x; case/setIP=> Px nAx ->{A1x}.
  rewrite 2!inE /E1A -(normP nAx) pnElemJ EpA1 andbT -val_eqE /=.
  have nZ0P: P \subset 'N(Z0).
    by rewrite (char_norm_trans (Ohm_char 1 _)) // bgFunc_norm.
  by rewrite -(normsP nZ0P x Px) (inj_eq (@conjsg_inj _ x)).
have pN: p.-group 'N_P(_) := pgroupS (subsetIl P _) pP.
have defCPA: 'N_('N_P(A))(A1) = 'C_P(A).
  apply/eqP; rewrite eqEsubset andbC subsetI setIS ?cent_sub //.
  rewrite subIset /=; last by rewrite orbC cents_norm ?centS.
  rewrite setIAC (subset_trans (subsetIl _ _)) //= subsetI subsetIl /=.
  rewrite -defA centM subsetI andbC subIset /=; last first.
    by rewrite centsC (subset_trans (Ohm_sub 1 _)) ?subsetIr.
  have nC_NP: 'N_P(A1) \subset 'N('C(A1)) by rewrite norms_cent ?subsetIr.
  rewrite -quotient_sub1 // subG1 trivg_card1.
  rewrite (pnat_1 (quotient_pgroup _ (pN _))) //.
  rewrite -(card_isog (second_isog nC_NP)) /= (setIC 'C(A1)).
  by apply: p'group_quotient_cent_prime; rewrite ?subsetIr ?oA1.
have sCN: 'C_P(A) \subset 'N_P(A) by rewrite setIS ?cent_sub.
have nA_NCPA: 'N_P('C_P(A)) \subset 'N_P(A).
  have [_ defCPA1] := subApG P pP sAP.
  by rewrite -{2}defCPA1 setIS // (char_norm_trans (Ohm_char 1 _)).
rewrite card_orbit astab1JG /= {}defCPA.
rewrite -(leq_add2l (Z0 \in E1A)) -cardsD1 EpZ0 (card_p1Elem_p2Elem Ep2A) ltnS.
rewrite dvdn_leq ?(pfactor_dvdn 1) ?indexg_gt0 // -divgS // logn_div ?cardSg //.
rewrite subn_gt0  properG_ltn_log ?pN //= (proper_sub_trans _ nA_NCPA) //.
rewrite (nilpotent_proper_norm (pgroup_nil pP)) // properEneq subsetIl andbT.
by apply: contraNneq not_cPP => <-; rewrite (abelianS (setSI _ sPS)).
Qed.

(* This factoid is mentioned very early, in a remark in the introduction of   *)
(* Section 10 (on p. 70). Ironically, this is the converse to 10.14 (a),      *)
(* which only appears at the very end of the Section!                         *)
Lemma beta'_narrow : forall M, M \in 'M -> forall p P,
  p \notin \beta(G) -> p.-Sylow(M) P -> p.-narrow P.
Proof.
move=> M M_max p P b'p sylP; apply: contraR b'p => nnP.
have rPgt2: 'r_p(P) > 2 by rewrite ltnNge; case/norP: nnP.
have a_p: p \in \alpha(M) by rewrite !inE -(p_rank_Sylow sylP).
have sylPG: p.-Sylow(G) P := Sylow_Sylow_sigma M_max (alpha_sub_sigma M_max a_p) sylP.
rewrite !inE /=; apply/forall_inP=> Q; rewrite inE => sylQ.
have [x xM ->]:= Sylow_trans sylPG sylQ.
by rewrite narrowJ.
Qed.

(* This is B & G, Proposition 10.14(a). *)
Lemma beta_not_narrow : forall p, p \in \beta(G) ->
      [disjoint 'E_p^2(G) & 'E*_p(G)]
  /\ (forall P, p.-Sylow(G) P -> [disjoint 'E_p^2(P) & 'E*_p(P)]).
Proof.
move=> p; move/forall_inP=> nnG.
have nnSyl: forall P, p.-Sylow(G) P -> [disjoint 'E_p^2(P) & 'E*_p(P)].
  move=> P sylP; move: (nnG P); rewrite inE -setI_eq0; move/(_ sylP).
  by apply: contraR => ?; apply/orP; right.
split=> //; apply/pred0Pn=> [[E]]; case/andP=> /= Ep2E EpmE.
have [_ abelE dimE]:= pnElemP Ep2E; have pE := abelem_pgroup abelE.
have [P sylP sEP] := Sylow_superset (subsetT E) pE.
case/pred0Pn: (nnSyl P sylP); exists E; rewrite /= 2!inE sEP abelE dimE /=.
by rewrite (subsetP (pmaxElemS p (subsetT P))) // inE EpmE inE.
Qed.

(* This is B & G, Proposition 10.14(b). *)
Lemma beta_noncyclic_uniq : forall p R,
  p \in \beta(G) -> p.-group R -> 'r(R) > 1 -> R \in 'U.
Proof.
move=> p R b_p pR rRgt1; have [P sylP sRP] := Sylow_superset (subsetT R) pR.
rewrite (rank_pgroup pR) in rRgt1; have [A Ep2A] := p_rank_geP rRgt1.
have [sAR abelA dimA] := pnElemP Ep2A; have p_pr := pnElem_prime Ep2A.
case: (pickP [pred F \in 'E_p(P) | A \proper F]) => [F | maxA]; last first.
  have [_ nnSyl] := beta_not_narrow b_p; case/pred0Pn: (nnSyl P sylP).
  exists A; rewrite /= (subsetP (pnElemS p 2 sRP)) //.
  apply/pmaxElemP; split=> [|F EpF]; first by rewrite inE (subset_trans sAR).
  by case/eqVproper=> [// | ltAF]; case/andP: (maxA F).
case/andP; case/pElemP=> _ abelF ltAF; have [pF cFF _] := and3P abelF.
apply: uniq_mmaxS sAR (mFT_pgroup_proper pR) _.
have rCAgt2: 'r('C(A)) > 2.
  rewrite -dimA (leq_trans (properG_ltn_log pF ltAF)) // -(rank_abelem abelF).
  by rewrite rankS // centsC (subset_trans (proper_sub ltAF)).    
by apply: cent_rank3_Uniqueness rCAgt2; rewrite (rank_abelem abelA) dimA.
Qed.

(* This is B & G, Proposition 10.14(c). *)
Lemma beta_subnorm_uniq : forall p P X,
  p \in \beta(G) -> p.-Sylow(G) P -> X \subset P -> 'N_P(X)%G \in 'U.
Proof.
move=> p P X b_p sylP sXP; set Q := 'N_P(X)%G.
have pP := pHall_pgroup sylP; have pQ: p.-group Q := pgroupS (subsetIl _ _) pP.
have [| rQle1] := ltnP 1 'r(Q); first exact: beta_noncyclic_uniq pQ.
have cycQ: cyclic Q.
  by rewrite (odd_pgroup_rank1_cyclic pQ) ?mFT_odd -?rank_pgroup.
have defQ: P :=: Q.
  apply: (nilpotent_sub_norm (pgroup_nil pP) (subsetIl _ _)).
  by rewrite setIS // char_norms // sub_cyclic_char // subsetI sXP normG.
move: b_p; rewrite inE; move/forall_inP; move/(_ P); rewrite inE sylP /narrow.
by rewrite defQ -(rank_pgroup pQ) (leq_trans rQle1) //=; move/(_ (erefl _)).
Qed.

(* This is B & G, Proposition 10.14(d). *)
Lemma beta_norm_sub_mmax : forall M Y,
  M \in 'M -> \beta(M).-subgroup(M) Y -> Y :!=: 1 -> 'N(Y) \subset M.
Proof.
move=> M Y maxM; case/andP=> sYM bY ntY.
have [F1 | [q q_pr q_dv_FY]] := trivgVpdiv 'F(Y).
  by rewrite -(trivg_Fitting (solvableS sYM (mmax_sol maxM))) F1 eqxx in ntY.
pose X := 'O_q(Y); have qX: q.-group X := pcore_pgroup q _.
have ntX: X != 1.
  apply: contraTneq q_dv_FY => X1; rewrite -p'natE // -partn_eq1 //.
  rewrite -(card_Hall (nilpotent_pcore_Hall q (Fitting_nil Y))).
  by rewrite /= p_core_Fitting -/X X1 cards1.
have bMq: q \in \beta(M) by apply: (pgroupP (pgroupS (Fitting_sub Y) bY)).
have b_q: q \in \beta(G) by move: bMq; rewrite -predI_sigma_beta //; case/andP.
have sXM: X \subset M := subset_trans (pcore_sub q Y) sYM.
have [P sylP sXP] := Sylow_superset sXM qX; have [sPM qP _] := and3P sylP.
have sylPG: q.-Sylow(G) P.
  by rewrite (Sylow_Sylow_sigma maxM) // alpha_sub_sigma // beta_sub_alpha.
have uniqNX: 'M('N_P(X)) = [set M].
  apply: def_uniq_mmax => //; last by rewrite subIset ?sPM.
  exact: (beta_subnorm_uniq b_q).
rewrite (subset_trans (char_norms (pcore_char q Y))) //.
rewrite (sub_uniq_mmax uniqNX) ?subsetIr // mFT_norm_proper //.
by rewrite (sub_mmax_proper maxM).
Qed.

End Ten.


