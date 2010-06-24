(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype paths.
Require Import finset prime groups morphisms action automorphism normal cyclic.
Require Import gfunc pgroups gprod center commutators gseries nilpotent.
Require Import sylow abelian maximal hall BGsection1 BGsection4 BGsection5.
Require Import BGsection6 BGsection7 BGsection8 BGsection9.

(******************************************************************************)
(*   This file covers B & G, section 10                                       *)
(*                                                                            *)
(*   \alpha(G) ==                                                             *)
(*                                                                            *)
(*                                                                            *)
(*                                                                            *)
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

Variable gT : minSimpleOddGroupType.
Implicit Type p : nat.

Local Notation G := (TheMinSimpleOddGroup gT).
Local Notation ideal := (fun p =>
  (existsb P : {group _}, p.-Sylow(G) P && ~~ p.-narrow P)).

Implicit Type M : {set gT}.

Definition alpha M := [pred p | (2 < 'r_p(M))].

Notation "\alpha ( M )" := (alpha M) : group_scope.

Definition alpha_core M := 'O_\alpha(M)(M).

Notation "M `_ \alpha" := (alpha_core M) : group_scope.

Canonical Structure alpha_core_group M := Eval hnf in [group of M`_\alpha].

Definition beta M := [pred p \in \alpha(M) | ideal p].

Notation "\beta ( M )" := (beta M) : group_scope.

Definition beta_core M := 'O_\beta(M)(M).

Notation "M `_ \beta" := (beta_core M) : group_scope.

Canonical Structure beta_core_group M := Eval hnf in [group of M`_\beta].

Definition sigma M := 
  [pred p | existsb P : {group gT}, p.-Sylow(M) P && ('N(P) \subset M) ].

Notation "\sigma ( M )" := (sigma M) : group_scope.

Definition sigma_core M := 'O_\sigma(M)(M).

Notation "M `_ \sigma" := (sigma_core M) : group_scope. 

Canonical Structure sigma_core_group M := Eval hnf in [group of M`_\sigma].

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
Variables G H : {group gT}.

Lemma sigma_core_char : G`_\sigma \char G.
Proof. exact: bgFunc_char. Qed.

Lemma sigma_core_pgroup : \sigma(G).-group G`_\sigma.
Proof. exact: pcore_pgroup. Qed.

Lemma sigma_core_sub : G`_\sigma \subset G.
Proof. exact: pcore_sub. Qed.

Lemma sigma_core_max : \sigma(G).-group H -> H <| G -> H \subset G`_\sigma.
Proof. exact: pcore_max. Qed.

Lemma sigma_core_normal : G`_\sigma <| G.
Proof. exact: pcore_normal. Qed. 

Lemma sigmaJ : forall x, \sigma(G :^ x) =i \sigma(G).
Proof.
move=> x p; apply/exists_inP/exists_inP=> [[P pSyl_P sNG]|[P pSyl_P sNG]].
  exists (P :^ x^-1)%G; last by rewrite normJ sub_conjg invgK.
  by rewrite -(conjsg1 G) -(mulgV x) conjsgM pHallJ2.
by exists (P :^ x)%G; [ by rewrite pHallJ2 | by rewrite normJ conjSg ].
Qed.

(* TODO: move to pgroups.v *)
Lemma pcoreJ : forall (gT : finGroupType) (G : {group gT}) x pi,
  'O_pi(G :^ x) = 'O_pi(G) :^ x.
Proof.
move=> rT R x pi; rewrite -{1}(setIid R) -morphim_conj.
rewrite -(bgFunc_ascont _ (injm_conj R x)) //=.
by rewrite morphim_conj (setIidPr _) // pcore_sub.
Qed.

Lemma sigma_coreJ : forall x, (G :^ x)`_\sigma = G`_\sigma :^ x.
Proof. by move=> x; rewrite /sigma_core -(eq_pcore G (sigmaJ x)) pcoreJ. Qed.

Lemma alpha_core_char : G`_\alpha \char G.
Proof. exact: bgFunc_char. Qed.

Lemma alpha_core_pgroup : \alpha(G).-group G`_\alpha.
Proof. exact: pcore_pgroup. Qed.

Lemma alpha_core_sub : G`_\alpha \subset G.
Proof. exact: pcore_sub. Qed.

Lemma alpha_core_max : \alpha(G).-group H -> H <| G -> H \subset G`_\alpha.
Proof. exact: pcore_max. Qed.

Lemma alpha_core_normal : G`_\alpha <| G.
Proof. exact: pcore_normal. Qed. 

Lemma alphaJ : forall x, \alpha(G :^ x) =i \alpha(G).
Proof. by move=> x p; rewrite !inE /= p_rankJ. Qed.

Lemma alpha_coreJ : forall x, (G :^ x)`_\alpha = G`_\alpha :^ x.
Proof. by move=> x; rewrite /alpha_core -(eq_pcore G (alphaJ x)) pcoreJ. Qed.

End CoreTheory.

Section Ten.

Variable gT : minSimpleOddGroupType.
Implicit Type p : nat.

Local Notation G := (TheMinSimpleOddGroup gT).
Local Notation ideal := (fun p =>
  (existsb P : {group _}, p.-Sylow(G) P && ~~ p.-narrow P)).

Implicit Type M : {group gT}.

Variable M : {group gT}.
Hypothesis M_max : M \in 'M.

Let M_proper := mmax_proper M_max.

Lemma beta_sub_alpha : {subset \beta(M) <= \alpha(M)}.
Proof. by move=> p; rewrite !inE; case/andP=> ->. Qed.

Lemma alpha_sub_sigma : {subset \alpha(M) <= \sigma(M)}.
Proof.
move=> p; rewrite !inE => rM; have [P Syl_P] := Sylow_exists p M.
apply/existsP; exists P; rewrite Syl_P.
rewrite uniq_mmax_norm_sub // (def_uniq_mmax _ M_max) ?(pHall_sub Syl_P) //.
have pPG := sub_proper_trans (pHall_sub Syl_P) M_proper.
rewrite (p_rank_Sylow Syl_P) -(rank_pgroup (pHall_pgroup Syl_P)) in rM.
exact: rank3_Uniqueness pPG rM.
Qed.

Lemma Mbeta_sub_Malpha : M`_\beta \subset M`_\alpha.
Proof. exact: sub_pcore beta_sub_alpha. Qed.

Lemma Malpha_sub_Msigma : M`_\alpha \subset M`_\sigma.
Proof. exact: sub_pcore alpha_sub_sigma. Qed.

Implicit Type P X: {group gT}.

Lemma norm_Sylow_sigma : 
  forall p P, p \in \sigma(M) -> p.-Sylow(M) P -> 'N(P) \subset M.
Proof.
move=> p P; case/existsP=> Q; case/andP=> pSyl_Q sNPM pSyl_P.
by case: (Sylow_trans pSyl_Q pSyl_P) => m mM ->; rewrite normJ conj_subG.
Qed.

Lemma Sylow_Sylow_sigma : 
  forall p P, p \in \sigma(M) -> p.-Sylow(M) P -> p.-Sylow(G) P.
Proof.
move=> p P p_Sig pSyl_P; apply: (mmax_sigma_Sylow M_max) => //.
exact: norm_Sylow_sigma p_Sig pSyl_P.
Qed.

Theorem BG10_1d : 
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
  p.-Sylow(M) X -> forall g, X :^ g \subset M -> g \in M.
Proof.
move=> p X p_Sig ntX pX pSyl_X g sXgM.
case: (Sylow_Jsub pSyl_X sXgM _); rewrite ?pgroupJ // => h hM /= sXghX.
rewrite -(groupMr _ hM); apply: subsetP (norm_Sylow_sigma p_Sig pSyl_X) _ _.
by rewrite inE conjsgM.
Qed.

End Ten.

Section Ten1.

Variable gT : minSimpleOddGroupType.
Implicit Type p : nat.

Local Notation G := (TheMinSimpleOddGroup gT).
Local Notation ideal := (fun p =>
  (existsb P : {group _}, p.-Sylow(G) P && ~~ p.-narrow P)).

Implicit Type M X : {group gT}.

Variable M : {group gT}.
Hypothesis M_max : M \in 'M.

Lemma BG10b_to_a :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    [transitive 'C(X), on [set Mg \in M :^: G | X \subset Mg]| 'Js] ->
    X \subset M -> forall g, X :^g \subset M -> 
  exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m].
Proof.
move=> p X p_Sig ntX pX actT sXM g sXgM.
have sMg'XX : (M :^ g^-1) \in [set Mg \in M :^: G | X \subset Mg].
  by rewrite inE -sub_conjg sXgM mem_orbit ?in_group ?in_setT.
have sMXX : M :^ 1 \in [set Mg \in M :^: G | X \subset Mg].
  by rewrite inE {2}conjsg1 sXM mem_orbit ?in_group ?in_setT.
case: (atransP2 actT sMXX sMg'XX) => /= c cC; rewrite conjsg1 => defM.
exists c^-1; exists (c * g); rewrite in_group cC; gsimpl; split => //.
by rewrite -(norm_mmax M_max) inE conjsgM -defM -conjsgM mulVg conjsg1. 
Qed.

Lemma BG10a_to_c :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    X \subset M -> 
    (forall g, X :^g \subset M -> 
      exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m]) ->
  'N(X) = 'N_M(X) * 'C(X). 
Proof.
move=> p X p_Sig ntX pX sXM thmA; apply/eqP; rewrite eqEsubset.
rewrite mul_subG ?cent_sub ?subsetIr // andbT; apply/subsetP=> x xNX.
move: (xNX); rewrite inE; move/(fun x => subset_trans x sXM) => sXgM. 
move: xNX; case/thmA: sXgM => c [m [cC mM ->]] {x}; rewrite inE => cmNX.
have mNX : m \in 'N(X).
  rewrite inE (subset_trans _ cmNX) // conjsgM conjSg -sub_conjgV.
  by move: cC; rewrite -groupV; move/(subsetP (cent_sub _) _); rewrite inE.
have cmCX : c ^ m \in 'C(X).
  apply/centP=> x xX; apply: (mulgI m); apply: (mulIg m^-1); rewrite conjgE. 
  gsimpl; rewrite -2!mulgA -{1 3}(invgK m) -(conjgE x) -(mulgA _ x) -(conjgE x).
  by rewrite (centP cC) // memJ_norm // groupV.
by apply/imset2P; exists m (c^m); rewrite // ?conjgE 1?inE ?mM /=; gsimpl.
Qed.

End Ten1.

Section Ten1b.

Variable gT : minSimpleOddGroupType.
Implicit Type p : nat.

Local Notation G := (TheMinSimpleOddGroup gT).
Local Notation ideal := (fun p =>
  (existsb P : {group _}, p.-Sylow(G) P && ~~ p.-narrow P)).

Implicit Type M X : {group gT}.

Theorem BG10b :
    forall M p X, M \in 'M -> p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    let OO := [set Mg \in M :^: G | X \subset Mg] in
  [transitive 'C(X), on OO | 'Js ].
Proof.
move=> M p X M_max p_Sig.
move: {2}_.+1 (ltnSn (#|M| - #|X|)) => m.
elim: m X => // m IH X sizeX ntX pX; set OO := [set Mg \in _ | _] => /=.
have [M1 M1_OO] : exists M1: {group _}, gval M1 \in OO.
  have [XX pSyl_XX sXXX] := Sylow_superset (subsetT _) pX.
  move: (p_Sig); case/exists_inP=> P pSyl_P sNPM.
  have pSyl_PG := Sylow_Sylow_sigma M_max p_Sig pSyl_P.
  case: (Sylow_trans pSyl_PG pSyl_XX) => x _ defP.
  move: pSyl_P; rewrite -(pHallJ2 _ _ _ x) -defP; case/and3P=> sXXM _ _.
  exists (M :^ x)%G; rewrite inE (subset_trans sXXX sXXM) andbT.
  by apply/imsetP; exists x; rewrite ?inE.
have acts_CX : [acts 'C(X), on OO | 'Js].
  apply/subsetP=> x xCX; apply/astabsP=> O /=; rewrite !inE -sub_conjgV.
  rewrite (@normP _ x^-1 _ _) ?in_group ?(subsetP _ _ xCX) ?cent_sub //.
  apply: andb_id2r => sXO; apply/imsetP/imsetP=> [[]|[]] g _ defO; last first.
    by exists (g * x); rewrite ?(groupM,inE) // defO conjsgM.
  exists (g * x^-1); rewrite ?groupM ?inE //.
  by rewrite conjsgM -defO -conjsgM mulgV conjsg1.
apply/imsetP; exists (gval M1) => //; apply/eqP; rewrite eqEsubset andbC.
rewrite acts_sub_orbit // M1_OO; apply/subsetP=> M2' M2'_OO; apply/imsetP. 
have [M2 -> M2_OO {M2' M2'_OO}] : exists2 M2, M2' = gval M2 & gval M2 \in OO.
  move: M2'_OO (M2'_OO); rewrite {1}inE; case/andP; case/imsetP=> x ? -> *.
  by exists (M :^ x)%G.
case: (eqsVneq M1 M2) => [->/=|]; first by exists 1; rewrite ?in_group ?conjsg1.
move=> neqM1M2; pose L := 'N(X); clear acts_CX.

have [[X1 pSyl_X1 pXX1] [X2 pSyl_X2 pXX2]]: 
  (exists2 X1 : {group _}, p.-Sylow(M1 :&: L) X1 & X \proper X1) /\
   exists2 X2 : {group _}, p.-Sylow(M2 :&: L) X2 & X \proper X2.
- move: (M1_OO); rewrite inE; case/andP; case/imsetP=> x1 _ defM1 sXM1.
  move: (M2_OO); rewrite inE; case/andP; case/imsetP=> x2 _ defM2 sXM2.
  pose g := x2 ^-1 * x1.
  have defM1bis : M1 :=: M2 :^ g.
    by rewrite defM2 -!conjsgM mulKVg -defM1.
  have defM2bis : M2 :=: M1 :^ g^-1.
    by rewrite defM1 -!conjsgM invMg invgK mulKVg defM2. 
  have sXgM1 : X :^ g \subset M1.
    by rewrite sub_conjg defM1bis -!conjsgM mulgV conjsg1 sXM2.
  have p_Sig1 : p \in \sigma(M1) by rewrite defM1 sigmaJ.
  have [XX pSyl_XX] := Sylow_superset sXM1 pX.
  rewrite subEproper; case/orP => [|pXXX].
    move/eqP=> defX1; move: (pSyl_XX); rewrite -defX1.
    move/(BG10_1d p_Sig1 ntX pX); move/(_ _ sXgM1) => gM1.
    case/negP: neqM1M2; rewrite -(inj_eq (@conjsg_inj _ g)) -defM1bis.
    by rewrite eqEsubset -sub_conjgV !conj_subG // groupV.
  case/and3P: pSyl_XX => sXXM1 pXX _; have pLXX := pgroupS (subsetIl _ L) pXX.
  have pXXXL : X \proper XX :&: L. 
    exact: nilpotent_proper_norm (pgroup_nil pXX) pXXX.
  have [X1] := Sylow_superset (setSI L sXXM1) pLXX; rewrite /= -/L => pSyl_X1.
  move/(proper_sub_trans pXXXL) => pXX1; split; first by exists X1.
- have p_Sig2 : p \in \sigma(M2) by rewrite defM2 sigmaJ.
  have sXgM2 : X :^ g^-1 \subset M2.
    by rewrite sub_conjgV -defM1bis sXM1.
  have [YY pSyl_YY] := Sylow_superset sXM2 pX.
  rewrite subEproper; case/orP => [|pXYY].
    move/eqP=> defX2; move: (pSyl_YY); rewrite -defX2.
    move/(BG10_1d p_Sig2 ntX pX); move/(_ _ sXgM2) => gM2.
    case/negP: neqM1M2; rewrite -(inj_eq (@conjsg_inj _ g^-1)) -defM2bis.
    by rewrite eqEsubset -sub_conjgV invgK !conj_subG // -groupV.
  case/and3P: pSyl_YY=> sYYM1 pYY _; have pLYY := pgroupS (subsetIl _ L) pYY.
  have pXYYL : X \proper YY :&: L. 
    exact: nilpotent_proper_norm (pgroup_nil pYY) pXYY.
  have [X2] := Sylow_superset (setSI L sYYM1) pLYY; rewrite /= -/L => pSyl_X2.
  by move/(proper_sub_trans pXYYL) => pXX2; exists X2.

rewrite /OO in M2_OO M1_OO; clear OO.
wlog [P pSyl_P [sX1P sPM]] : M M_max p_Sig IH sizeX M1_OO M2_OO / 
  exists2 P : {group _}, p.-Sylow(L) P & X1 \subset P /\ P \subset M.
- have sX1L : X1 \subset L by case/and3P: pSyl_X1; rewrite subsetI; case/andP.
  have [P pSyl_P sX1P] := Sylow_superset sX1L (pHall_pgroup pSyl_X1).
  move: (p_Sig); case/exists_inP=> Px pSyl_Px sNPxM.
  have pSyl_PxG := Sylow_Sylow_sigma M_max p_Sig pSyl_Px.
  have [PG pSyl_PG sPPG] := Sylow_superset (subsetT _) (pHall_pgroup pSyl_P).
  case: (Sylow_trans pSyl_PxG pSyl_PG) => x _ defPG.
  have sPMx : P \subset M :^ x. 
    by rewrite (subset_trans sPPG) // defPG conjSg (pHall_sub pSyl_Px).
  move/(_ (M :^ x)%G); rewrite sigmaJ p_Sig mmaxJ M_max cardJg.
  have -> : (M :^ x)%G :^: G = M :^: G.
    apply/setP=> Y; apply/imsetP/imsetP=> [[]|[]] z _ ->.
      by exists (x * z); rewrite ?(groupM,inE) // conjsgM.
    by exists (x^-1 * z); rewrite ?(groupM,inE) // -conjsgM mulKVg.
  by apply => //; exists P.

have [t tL sX2Pt] : exists2 t, t \in L & X2 \subset P :^ t.
  have sX2L : X2 \subset L by case/and3P: pSyl_X2; rewrite subsetI; case/andP.
  have [Pt pSyl_Pt sX2Pt] := Sylow_superset sX2L (pHall_pgroup pSyl_X2).
  by case: (Sylow_trans pSyl_P pSyl_Pt) sX2Pt => t tL -> *; exists t.

have [c cCX defM] : exists2 c, c \in 'C(X) & M :=: M1 :^ c.
  have ntX1 : X1 :!=: 1. 
    apply/trivgPn; case/trivgPn: ntX => x *; exists x => //.
    by apply: subsetP (proper_sub pXX1) _ _.
  have cardX1 : #|M| - #|X1| < m.
    rewrite ltnS in sizeX; rewrite (leq_trans _ sizeX) //.
    rewrite ltn_sub2l ?(proper_card pXX1) //.
    by rewrite (proper_card (proper_sub_trans pXX1 (subset_trans sX1P sPM))).
  have M1_OO1 : gval M1 \in [set Mg \in M :^: G | X1 \subset Mg].
    case/and3P: pSyl_X1; rewrite subsetI; case/andP => sX1M1 _ _ _.
    by rewrite inE sX1M1 andbT; rewrite inE in M1_OO; case/andP: M1_OO.
  have M_OO1 : gval M \in [set Mg \in M :^: G | X1 \subset Mg].
    rewrite inE (subset_trans sX1P sPM) andbT; apply/imsetP.
    by exists 1; rewrite ?inE // conjsg1.
  move/atransP2: (IH X1 cardX1 ntX1 (pHall_pgroup pSyl_X1)).
  case/(_ M1 M M1_OO1 M_OO1) => /= c cCX1 ->; exists c => //.
  by apply: subsetP (centS (proper_sub _)) _ cCX1.
have [d dCX defMbis] : exists2 c, c \in 'C(X) & M :^ t :=: M2 :^ c.
  have ntX2 : X2 :!=: 1. 
    apply/trivgPn; case/trivgPn: ntX => x *; exists x => //.
    by apply: subsetP (proper_sub pXX2) _ _.
  have cardX2 : #|M| - #|X2| < m.
    rewrite ltnS in sizeX; rewrite (leq_trans _ sizeX) //.
    rewrite ltn_sub2l ?(proper_card pXX2) // -(cardJg M t).
    rewrite (proper_card (proper_sub_trans pXX2 (subset_trans sX2Pt _))) //.
    by rewrite conjSg.
  have M1_OO1 : gval M2 \in [set Mg \in M :^: G | X2 \subset Mg].
    case/and3P: pSyl_X2; rewrite subsetI; case/andP => sX2M2 _ _ _.
    by rewrite inE sX2M2 andbT; rewrite inE in M2_OO; case/andP: M2_OO.
  have Mt_OO1 : M :^ t \in [set Mg \in M :^: G | X2 \subset Mg].
    rewrite inE (subset_trans sX2Pt) // ?conjSg ?sPM ?andbT //; apply/imsetP.
    by exists t; rewrite ?inE //.
  move/atransP2: (IH X2 cardX2 ntX2 (pHall_pgroup pSyl_X2)).
  case/(_ _ _ M1_OO1 Mt_OO1) => /= d dCX1 ->; exists d => //.
  by apply: subsetP (centS (proper_sub _)) _ dCX1.

have pP := pHall_pgroup pSyl_P; have oddP : odd #|P| by exact: mFT_odd.
case: (leqP 3 'r_p(P)) => [rP|].
  have PU : P \in 'U.
    apply: rank3_Uniqueness; rewrite ?(rank_pgroup (pHall_pgroup pSyl_P)) //.
    by apply: sub_proper_trans sPM (mmax_proper M_max).
  have sLM : L \subset M.
    have sPLM : P \subset L :&: M by rewrite subsetI sPM (pHall_sub pSyl_P).
    admit.
  have tM : t \in 'N(M) by apply: subsetP (subset_trans sLM (normG _)) _ tL.
  move: defM defMbis; rewrite (normP tM) => ->; move/eqP.
  rewrite -(inj_eq (@conjsg_inj _ d^-1)) -!conjsgM mulgV conjsg1; move/eqP=> <-.
  by exists (c * d^-1) => //; rewrite !in_group.
case/(rank2_pdiv_compl_der_abelian_p'group (pgroup_sol pP) oddP) => _ _ p'PO.
have defL : L :=: 'N_L(P) * 'O_p^'(L).
  have pSyl_POpp : p.-Sylow('O_{p^',p}(L)) P.
    apply: pHall_subl _ (pseries_sub _ _) pSyl_P.
    admit.
  rewrite /L -{1}(Frattini_arg (pseries_normal _ _) pSyl_POpp) /= -/L.
  rewrite -normC ?subIset 1?char_norm ?pseries_char //.
  have pl1L : p.-length_1(L).
    rewrite /plength_1 eqEsubset pseries_sub /=. 
    admit.
  have solL : solvable L.
    apply: mFT_sol (mFT_norm_proper ntX (sub_mmax_proper M_max _)).
    by apply: subset_trans (proper_sub pXX1) (subset_trans sX1P sPM).
  have [<- _] := sol_Sylow_plength1_pseries_pcore solL pSyl_P pl1L.
  by rewrite mulgA /= -/L mulGSid // subsetI (pHall_sub pSyl_P) normG.
move: tL; rewrite defL; case/imset2P => u v uNLP vOL deft.
have cop : coprime #|X| #|'O_p^'(L)| := pnat_coprime pX (pcore_pgroup _ _).
have vCX : v \in 'C(X).
  apply: subsetP _ _ vOL.
  admit.
have ntP : P :!=: 1.
  apply/trivgPn; case/trivgPn: ntX => x *; exists x => //.
  by apply: subsetP (subset_trans (proper_sub pXX1) sX1P) _ _.
have : [transitive 'C(P), on [set Mg \in M :^: G | P \subset Mg] | 'Js].
  rewrite ltnS in sizeX; apply: IH; rewrite ?(pHall_pgroup pSyl_P) //.
  rewrite (leq_trans _ sizeX) // ltn_sub2l //.
    by rewrite proper_card ?(proper_sub_trans pXX1 _) ?(subset_trans sX1P sPM).
  by rewrite proper_card // (proper_sub_trans pXX1 sX1P).
move/(BG10b_to_a M_max p_Sig ntP (pHall_pgroup pSyl_P)); move/(_ sPM).
move/(BG10a_to_c p_Sig ntP (pHall_pgroup pSyl_P) sPM) => defNP.
have: u \in 'N(P) by apply: subsetP (subsetIr _ _) _ uNLP.
rewrite defNP; case/imset2P => w x wNMP xCP defu.
have xCX : x \in 'C(X). 
  by apply: subsetP (centS _) _ xCP; apply: subset_trans (proper_sub pXX1) sX1P.
have xwCX : c * x * v * d^-1 \in 'C(X) by rewrite !in_group.
exists (c * x * v * d^-1) => //=; move: defM defMbis. 
have wNM : w \in 'N(M) by apply: subsetP (normG _) _ _; case/setIP: wNMP.
rewrite deft defu !conjsgM (normP wNM) -!conjsgM => ->.
move/eqP;  rewrite -(inj_eq (@conjsg_inj _ d^-1)).
by rewrite -!conjsgM mulgV conjsg1 !mulgA; move/eqP=> <-.
Qed.

Variable M : {group gT}.
Variable M_max : M \in 'M.

Theorem BG10a :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    X \subset M -> forall g, X :^g \subset M -> 
  exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m].
Proof.
move=> p X p_Sig ntX pX sXM g sXgM; apply: (BG10b_to_a _ _ _ pX) => //.
exact: BG10b p_Sig ntX pX.
Qed.

Theorem BG10_c :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    X \subset M -> 'N(X) = 'N_M(X) * 'C(X). 
Proof.
move=> p X p_Sig ntX pX sXM; apply: (BG10a_to_c p_Sig ntX pX) => //.
exact: BG10a p_Sig ntX pX sXM.
Qed.

Theorem BG10_2a : \alpha(M).-Hall(M) M`_\alpha /\ \alpha(M).-Hall(G) M`_\alpha.
Admitted.

Theorem BG10_2b : \sigma(M).-Hall(M) M`_\sigma /\ \sigma(M).-Hall(G) M`_\sigma.
Admitted.

Theorem BG10_2c : M`_\sigma \subset M^`(1).
Admitted.

Theorem BG10_2d1 : 'r(M / M`_\alpha) <= 2. 
Admitted.

Theorem BG10_2d2 : nilpotent (M / M`_\alpha). 
Admitted.

Theorem BG10_2e : M`_\sigma :!=: 1.
Admitted.

End Ten1b.
