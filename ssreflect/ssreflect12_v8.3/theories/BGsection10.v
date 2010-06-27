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

Implicit Type M N X : {group gT}.

Theorem BG10b :
    forall M p X, M \in 'M -> p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    let OO := [set Mg \in M :^: G | X \subset Mg] in
  [transitive 'C(X), on OO | 'Js ].
Proof.
move=> M p X M_max p_Sig; move: {2}_.+1 (ltnSn (#|M| - #|X|)) => m.
elim: m X => // m IH X; rewrite ltnS => sizeX ntX pX.
pose OO M X := [set Mg \in M :^: G | X \subset Mg]; rewrite -/(OO M X) /=.
have [M1 M1_OO] : exists M1: {group _}, gval M1 \in OO M X.
  have [XX pSyl_XX sXXX] := Sylow_superset (subsetT _) pX.
  move: (p_Sig); case/exists_inP=> P pSyl_P sNPM.
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
  have sXgH : X:^g \subset H by rewrite sub_conjg defH2 -!conjsgM mulgV conjsg1.
  have p_Sig1 : p \in \sigma(H) by rewrite defH sigmaJ.
  have [XX pSyl_XX] := Sylow_superset sXH pX.
  rewrite subEproper; case/orP => [defX1|pXXX].
    rewrite -(eqP defX1) in pSyl_XX. 
    have gH := BG10_1d p_Sig1 ntX pX pSyl_XX sXgH.
    case/negP: neqHK; rewrite -(inj_eq (@conjsg_inj _ g)) -defH2.
    by rewrite eqEsubset -sub_conjgV !conj_subG // groupV.
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
  move: (p_Sig); case/exists_inP=> Px pSyl_Px sNPxM.
  have pSyl_PxG := Sylow_Sylow_sigma M_max p_Sig pSyl_Px.
  have [PG pSyl_PG sPPG] := Sylow_superset (subsetT _) (pHall_pgroup pSyl_P).
  case: (Sylow_trans pSyl_PxG pSyl_PG) => x _ defPG.
  have sPMx : P \subset M :^ x. 
    by rewrite (subset_trans sPPG) // defPG conjSg (pHall_sub pSyl_Px).
  move/(_ (M :^ x)%G); rewrite sigmaJ p_Sig mmaxJ M_max cardJg.
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
  have ntS1 : S1 :!=: 1. 
    by apply: contra ntX;rewrite -!subG1; move/(subset_trans (proper_sub pXS1)).
  have cardS1 : #|M| - #|S1| < m.
    by rewrite (leq_trans _ sizeX) // ltn_sub2l ?(proper_card pXS1).
  have [N1_OO N_OO] : gval N1 \in OO M S1 /\ gval N \in OO M S1.
    by case/and3P: pSyl_S1; rewrite subsetI /= !inE N1inMG NinMG; case/andP.
  move/atransP2: (IH S1 cardS1 ntS1 (pHall_pgroup pSyl_S1)).
  case/(_ N1 N N1_OO N_OO) => /= c cCS1 ->; exists c => //.
  by apply: subsetP (centS (proper_sub _)) _ cCS1.
move: M1_OO M2_OO; rewrite !inE; case/andP=> M1in sXM1; case/andP=> M2in sXM2.
have [|c cCX defM] := use_IH M M1 X1 pXX1 sX1M pSyl_X1 M1in.  
  by apply/imsetP; exists 1; rewrite ?inE // conjsg1.
have [||d dCX /= defMbis] := use_IH (M :^ t)%G M2 X2 pXX2 _ pSyl_X2 M2in.
  by rewrite ?(subset_trans sX2Pt) ?conjSg.
  by apply/imsetP; exists t; rewrite ?inE.
have pP := pHall_pgroup pSyl_P; have oddL: odd #|L| by exact: mFT_odd.
have sPL := pHall_sub pSyl_P; have pMG := mmax_proper M_max.
have pLG : L \proper G.
  apply: mFT_norm_proper ntX (sub_mmax_proper M_max _).
  by apply: subset_trans (proper_sub pXP) sPM.
have solL : solvable L := mFT_sol pLG. 
case: (leqP 3 'r_p(P)) => [rP|]; last rewrite -(p_rank_Sylow pSyl_P).
  have PU : P \in 'U.
    by rewrite rank3_Uniqueness ?(rank_pgroup pP) // (sub_proper_trans sPM pMG).
  have sLM : L \subset M := sub_uniq_mmax (def_uniq_mmax PU M_max sPM) sPL pLG.
  have tM : t \in 'N(M) by apply: subsetP (subset_trans sLM (normG _)) _ tL.
  move: defM defMbis; rewrite (normP tM) => ->; move/eqP.
  rewrite -(inj_eq (@conjsg_inj _ d^-1)) -!conjsgM mulgV conjsg1; move/eqP=> <-.
  by exists (c * d^-1) => //; rewrite !in_group.
case/(rank2_pdiv_compl_der_abelian_p'group solL); rewrite //= -/L => _ _ p'PO.
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
  by apply: contra ntX;rewrite -!subG1; move/(subset_trans (proper_sub pXP)).
have transP : [transitive 'C(P), on OO M P | 'Js].
  by apply: IH; rewrite ?pP // (leq_trans _ sizeX) // ltn_sub2l // proper_card.
have: u \in 'N(P) by apply: subsetP (subsetIr _ _) _ uNLP.
rewrite (BG10a_to_c p_Sig _ pP _ (BG10b_to_a M_max _ _ pP transP _)) //.
case/imset2P => w x wNMP xCP defu.
exists (c * x * v * d^-1); rewrite ?in_group //=; last move: defM defMbis.  
  by apply: subsetP (centS (proper_sub pXP)) _ xCP.
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

End Ten1b.

Section Ten2.

Variable gT : minSimpleOddGroupType.
Implicit Type p : nat.

Local Notation G := (TheMinSimpleOddGroup gT).

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
case: (BG10a M_max sigma_p neX1 pX sXM sXg_M)=> c; rewrite cent_cycle.
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

Let sub_M'Malpha_F : M^`(1) / M`_\alpha \subset F.
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
  rewrite [F]K_def -(eqP Keq) -norm_mulgenEr // mulgenC quotient_mulgen //. 
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

Theorem Hall_M_Malpha : \alpha(M).-Hall(M) M`_\alpha.
Proof.
have [Ma alpha_Hall_Ma] := HallExist \alpha(M) M_sol.
have [sMa_M alpha_Ma _] := and3P alpha_Hall_Ma.
have sigma_Ma : \sigma(M).-group Ma.
  by apply: (sub_in_pnat _ alpha_Ma)=> q _; exact: alpha_sub_sigma.
have [Ms sigma_Hall_Ms sMa_Ms] := HallSubset M_sol sMa_M sigma_Ma.
have [sMs_M sigma_Ms _] := and3P sigma_Hall_Ms.
have sMs_M' := sub_sigma_Hall_M' sigma_Hall_Ms.
have alpha'Ms_Malpha : ((\alpha(M))^').-group (Ms / M`_\alpha).
  by rewrite (pgroupS (subset_trans _ sub_M'Malpha_F) alpha'F) //= quotientS.
have sMalpha_Ma : M`_\alpha \subset Ma by rewrite pcore_sub_Hall.
have eMa_Malpha : Ma :=: M`_\alpha.
  apply/eqP; rewrite eqEsubset sMalpha_Ma andbT -quotient_sub1; last first.
    by rewrite (subset_trans (subset_trans sMa_Ms _) (normal_norm nsMalpha_M)).
  rewrite subG1 trivg_card1 (@pnat_1 \alpha(M) #|_|) //=.
    by rewrite [_.-nat _]quotient_pgroup.
  by apply: (pgroupS _ alpha'Ms_Malpha); rewrite quotientS.
by rewrite -eMa_Malpha.
Qed.

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

Theorem Hall_M_Msigma : \sigma(M).-Hall(M) M`_\sigma.
Proof. 
have [sMa_M alpha_Ma _] := and3P Hall_M_Malpha.
have sigma_Ma : \sigma(M).-group M`_\alpha.
  by apply: (sub_in_pnat _ alpha_Ma)=> q _; exact: alpha_sub_sigma.
have [Ms sigma_Hall_Ms sMa_Ms] := HallSubset M_sol sMa_M sigma_Ma.
have [sMs_M sigma_Ms _] := and3P sigma_Hall_Ms.
have sMs_M' := sub_sigma_Hall_M' sigma_Hall_Ms.
have sigma_Hall_F_Ms_Malpha : \sigma(M).-Hall(F) (Ms / M`_\alpha).
  rewrite (pHall_subl _ (normal_sub nsF_MMalpha)) //=.
    by rewrite (subset_trans _ sub_M'Malpha_F) // quotientS.
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

Theorem sub_Msigma_M' : M`_\sigma \subset M^`(1).
Proof. exact: sub_sigma_Hall_M' Hall_M_Msigma. Qed.

Let alpha'MMalpha : \alpha(M)^'.-group (M / M`_\alpha).
Proof.
rewrite /pgroup card_quotient ?normal_norm // -divgS ?normal_sub //=.
rewrite (card_Hall Hall_M_Malpha).
rewrite -{1}(@partnC \alpha(M) #|M|) ?cardG_gt0 // mulKn ?cardG_gt0 //. 
by rewrite part_pnat.
Qed.

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
rewrite (p_rank_Sylow pSyl_PMalpha) /= -(isog_p_rank isogP).
by rewrite -(p_rank_Sylow pSylP).
Qed.

Theorem nil_M'Malpha : nilpotent (M^`(1) / M`_\alpha).
Proof. by rewrite (nilpotentS sub_M'Malpha_F) // Fitting_nil. Qed.

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
move: (rank2_pcore_max_Sylow (mFT_odd M) (mmax_sol M_max) le_rFM2)=> /= qSyl.
set q := max_pdiv #|M| in qSyl.
have neOqM_1 : 'O_q(M) != 1.
  rewrite -cardG_gt1 (card_Hall qSyl) p_part_gt1 pi_max_pdiv cardG_gt1.
  by rewrite mmax_neq1.
have eNOqM_M : 'N('O_q(M)) = M by apply: mmax_normal; rewrite ?pcore_normal.
apply: contra _ neOqM_1; rewrite -!subG1; apply: subset_trans.
rewrite sub_pcore // => p; rewrite 2!inE; move/eqP=> ->.
by rewrite !inE; apply/existsP; exists ('O_q(M))%G; rewrite qSyl eNOqM_M subxx.
Qed.

End Ten2.

