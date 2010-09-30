(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype paths.
Require Import finset prime groups morphisms action automorphism normal cyclic.
Require Import gfunc pgroups gprod center commutators gseries nilpotent.
Require Import sylow abelian maximal hall BGsection1 BGsection4 BGsection5.
Require Import BGsection6 BGsection7 BGsection8 BGsection9 BGtheorem3_6.

(******************************************************************************)
(*   This file covers B & G, section 10                                       *)
(*                                                                            *)
(*   \alpha(M) == the primes p that make the p-rank of M greater than 2       *)
(*   \beta(M)  == ideals primes in \alpha(M). A prime is ideal iff there      *)
(*                exists a p-Sylow subgroup of the group type that is not     *)
(*                narrow.                                                     *)
(*   \sigma(M) == the primes p such that there exists a p-Sylow subgroup P    *)
(*                of M whose normaliser is contained in M                     *)
(*   M`_\alpha == the alpha_core of M, defined as 'O_\alpha(M)(M)             *)
(*   M`_\beta  == the beta_core of M, defined as 'O_\beta(M)(M)               *)
(*   M`_\sigma == the sigma_core of M, defined as 'O_\sigma(M)(M)             *)
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
  (existsb P:{group _}, p.-Sylow(G) P && (~~ p.-narrow P))).

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

Implicit Type P: {group gT}.

Lemma norm_Sylow_sigma : 
  forall p P, p \in \sigma(M) -> p.-Sylow(M) P -> 'N(P) \subset M.
Proof.
move=> p P; case/existsP=> Q; case/andP=> pSyl_Q sNPM pSyl_P.
by case: (Sylow_trans pSyl_Q pSyl_P) => m mM ->; rewrite normJ conj_subG.
Qed.

Lemma Sylow_Sylow_sigma : 
  forall p P, p \in \sigma(M) -> p.-Sylow(M) P -> p.-Sylow([set: gT]) P.
Proof.
move=> p P p_Sig pSyl_P; apply: (mmax_sigma_Sylow M_max) => //.
exact: norm_Sylow_sigma p_Sig pSyl_P.
Qed.

End CoreTheory.

Section Ten.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Type p : nat.
Implicit Type H P Q W M N X : {group gT}.

Let hide T (x : T) := x.
Local Notation "'hide T" := (hide T) (at level 99, only parsing).
Local Notation "...omissis..." := (hide _).

(* This is B & G 10.1(a,b,c,d), the (e) part is unused *)
Theorem mmax_sigma_core_nt_pgroup :
    forall M p X, M \in 'M -> p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
  [/\  X \subset M -> forall g, X :^g \subset M -> 
          exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m],
       [transitive 'C(X), on [set Mg \in M :^: G | X \subset Mg] | 'Js ],
       X \subset M -> 'N(X) = 'N_M(X) * 'C(X) &
       p.-Sylow(M) X -> forall g, X :^ g \subset M -> g \in M ].
Proof.
pose OO M X := [set Mg \in M :^: G | X \subset Mg].
have BG10_1d : 'hide forall M p X g, 
  p \in \sigma(M) -> p.-Sylow(M) X -> X :^ g \subset M -> g \in M.
- move=> M p X g p_Sig pSy_X sXgM; have pX := pHall_pgroup pSy_X. 
  case: (Sylow_Jsub pSy_X sXgM _); rewrite ?pgroupJ // => h hM /= sXghX.
  by rewrite -(groupMr _ hM) (subsetP (norm_Sylow_sigma _ pSy_X)) ?inE ?conjsgM.
have BG10_1b_to_a : 'hide forall M p X g, 
    M \in 'M -> p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    [transitive 'C(X), on OO M X| 'Js] -> X \subset M ->  X :^g \subset M -> 
  exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m].
- move=> M p X g M_max p_Sig ntX pX actT sXM sXgM.
  have sMg'XX : (M :^ g^-1) \in OO M X. 
    by rewrite inE -sub_conjg sXgM mem_orbit ?in_group ?inE.
  have sMXX: M:^1 \in OO M X by rewrite inE {2}conjsg1 sXM mem_orbit ?in_group.
  case: (atransP2 actT sMXX sMg'XX) => /= c cC; rewrite conjsg1 => defM.
  exists c^-1; exists (c * g); rewrite in_group cC; gsimpl; split => //.
  by rewrite -(norm_mmax M_max) inE conjsgM -defM -conjsgM mulVg conjsg1.
have BG10_1a_to_c : 'hide forall M p X, 
    M \in 'M -> p \in \sigma(M) -> X :!=: 1 -> p.-group X -> X \subset M -> 
    (forall g, X :^g \subset M -> 
      exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m]) ->
  'N(X) = 'N_M(X) * 'C(X). 
- move=> M p X M_max p_Sig ntX pX sXM thmA; apply/eqP; rewrite eqEsubset.
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
    M \in 'M -> p \in \sigma(M) -> X :!=: 1 -> p.-group X -> 
  [transitive 'C(X), on OO M X | 'Js]; last first.
- by move=> M p *; split; eauto; exact: (BG10_1b _ p).
move=> M p X M_max p_Sig; move: {2}_.+1 (ltnSn (#|M| - #|X|)) => m.
elim: m X => // m IH X; rewrite -/(OO M X) /= ltnS => sizeX ntX pX.
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
    rewrite -(eqP defX1) in pSyl_XX; have gH: g \in H by exact: (BG10_1d _ p X).
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
  have ntS1 : S1:!=:1 by rewrite -!proper1G in ntX *;rewrite (proper_trans ntX).
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
have sPL := pHall_sub pSyl_P; have pMG := mmax_proper M_max => {use_IH}.
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
have ntP : P :!=: 1 by rewrite -!proper1G in ntX *; rewrite (proper_trans ntX).
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
case: (mmax_sigma_core_nt_pgroup M_max sigma_p neX1 pX) => BG10_1a _ _ _. 
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

(* This is B & G 10.2(a1) *) 
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

(* This is B & G 10.2(a2) *) 
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

(* This is B & G 10.2(b1) *) 
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

(* This is B & G 10.2(b2) *) 
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

(* This is B & G 10.2(c) *)
Theorem Msigma_sub_M' : M`_\sigma \subset M^`(1).
Proof. exact: sub_sigma_Hall_M' Hall_M_Msigma. Qed.

Let alpha'MMalpha : \alpha(M)^'.-group (M / M`_\alpha).
Proof.
rewrite /pgroup card_quotient ?normal_norm // -divgS ?normal_sub //=.
rewrite (card_Hall Hall_M_Malpha) -{1}(@partnC \alpha(M) #|M|) ?cardG_gt0 //. 
by rewrite mulKn ?cardG_gt0 // part_pnat.
Qed.

(* This is B & G 10.2(d1) *)
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

(* This is B & G 10.2(d2) *)
Theorem nil_M'Malpha : nilpotent (M^`(1) / M`_\alpha).
Proof. by rewrite (nilpotentS M'Malpha_sub_F) // Fitting_nil. Qed.

(* This is B & G 10.2(e) *)
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

Let nsMaM : M`_\alpha <| M.
Proof. by apply: pcore_normal. Qed.

Let alphaMa : \alpha(M).-group (M`_\alpha).
Proof. by exact: pcore_pgroup. Qed.

(* This is B & G, 10.3 *)
Theorem centraliser_alpha'_subgroup_unique : forall (X : {group gT}), 
  X \subset M -> \alpha(M)^'.-group X -> 'r('C_(M`_\alpha)(X)) >= 2 ->
    ('C_M(X))%G \in 'U.
Proof.
move=> X sXM alpha'X; case: (rank_witness 'C_(M`_\alpha)(X)) => p primep -> rP.
have alpha_p : p \in \alpha(M).
  apply: (pgroupP alphaMa p primep).
  suff : p \in \pi(#|'C_(M`_\alpha)(X)|). 
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
  rewrite (OhmE 1 pCPB) /= gen_subG; apply/subsetP=> g; rewrite inE.
  case/andP; case/setIP=> Pg CBg gp1; apply: contraR (negbT rCPB)=> nBg.
  rewrite (rank_pgroup pCPB).
  pose G := <[g]>; suff : 2 < 'r_p(B <*> G). 
    move/leq_trans; apply; rewrite p_rankS // mulgen_subG sB_CPB /=.
    by rewrite subsetI !cycle_subG Pg.
  have BGeq : B <*> G = B * G.
    by rewrite norm_mulgenEl // cents_norm // centsC cycle_subG. 
  have cprodBG : B \* G = B <*> G by rewrite cprodE ?BGeq // centsC cycle_subG.
  have pabelBG : p.-abelem (B <*> G).
    rewrite (cprod_abelem _ cprodBG) pabelB cycle_abelem ?primep ?orbT //=.
    by rewrite order_dvdn.
  rewrite p_rank_abelem // -lcardB properG_ltn_log ?abelem_pgroup //.
  apply/properP; split; first by rewrite mulgen_subl.
  by exists g; rewrite ?nBg //= (subsetP (mulgen_subr _ _)) // cycle_id.
have cPX : P \subset 'C(X).
  have EpPB : B \in 'E_p(P) by apply/pElemP. 
  have coPX : coprime #|P| #|X|.
    exact: (coprime_dvdl (cardSg (pHall_sub pSylP)) coMaX).
  rewrite centsC; apply: (coprime_odd_faithful_cent_abelem EpPB pP nPX coPX).
    by rewrite mFT_odd.
  rewrite centsC (subset_trans _ cXB) // -{2}Beq. 
  rewrite (OhmE 1 (pgroupS _ pP)) ?subsetIl // sub_gen //=.
  apply/subsetP=> x; rewrite !inE; case/andP=> ->; move/eqP=> <-.
  by rewrite expg_order /=.
have pSylMP : p.-Sylow(M) P.
  rewrite pHallE (subset_trans (pHall_sub pSylP) (normal_sub nsMaM)) /=.
  rewrite (card_Hall pSylP) (card_Hall Hall_M_Malpha) partn_part // =>q.
  by rewrite 2!inE; move/eqP=> ->.
have rP : 'r(P) >= 3.
  rewrite (rank_pgroup (pHall_pgroup pSylP)) -(p_rank_Sylow pSylMP).
  by rewrite !inE in alpha_p.
apply: rank3_Uniqueness.
  by rewrite (sub_proper_trans (subsetIl _ _)) // M_proper.
by rewrite (leq_trans rP) // rankS // subsetI cPX andbT (pHall_sub pSylMP).
Qed.

Variable p : nat.
Variable piMp : p \in \pi(#|M|).

(* This is B & G, Lemma 10.4a *)
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

(* This is B & G, Lemma 10.4b *)
(* Curiously, the hypothesis M'_\alpha != 1 in the text is not needed. *)
Lemma sigma'_exists_Zgroup : forall P, p.-Sylow(M) P -> 
  exists x, [/\ x \in 'Ohm_1('Z(P))^#, 'M('C_G[x]) != [set M] & 
    Zgroup ('C_(M`_\alpha)[x])].
Proof.
move=> P SylP; move: (sigma'p); rewrite !inE negb_exists_in; move/forallP.
move/(_ P); move/implyP; move/(_ SylP); case/subsetPn=> u NPu nMu.
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
  have UCMY := centraliser_alpha'_subgroup_unique sWM alpha'W rCMaW.
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
have <- : G :^ (u^-1) :=: G.
  by apply/normP; rewrite (subsetP (normG _)) // inE.
rewrite -conjIg cent_set1 (def_uniq_mmaxJ _ eMCGyM) /=; move/set1_inj.
by move/(congr1 val)=> /=; move/normP; rewrite norm_mmax // groupV.
Qed.

(* This is B & G, Lemma 10.4c, part 1 *)
Lemma sigma'_prank2_Ep2_sub : 
  'r_p(M) = 2 -> 'E_p^2(M) \subset 'E*_p(G).
Proof.
move=> rpM; apply: contraR sigma'p; case/subsetPn=> A Ep2MA EpGA.
have uniqA : A \in 'U.
  apply: (@nonmaxElem2_Uniqueness _ p); rewrite inE EpGA /=.
  by apply: (subsetP (pnElemS p 2 (subsetT M))).
case/pnElemP: Ep2MA=> sAM; move/abelem_pgroup=> pA _.
have [P pSylMP sAP] := Sylow_superset sAM pA.
apply/existsP; exists P; rewrite pSylMP uniq_mmax_norm_sub //.
apply: (def_uniq_mmaxS sAP); last by apply: def_uniq_mmax.
by apply: (sub_proper_trans (pHall_sub pSylMP)).
Qed.

(* This is B & G, Lemma 10.4c, part 2; is this the right statement? *)
Lemma sigma'_prank2_Ep2_EpG : 
  'r_p(M) = 2 -> ('E_p^2(M) :&: 'E*_p(G)) != set0.
Proof. 
move=> rpM; apply/set0Pn.
case: (p_rank_geP (_ : 2 <= 'r_p(M)))=> [|A Ep2A]; rewrite ?rpM //=.
by exists A; rewrite inE Ep2A (subsetP (sigma'_prank2_Ep2_sub rpM)).
Qed.

(* This is B & G, Lemma 10.5, part 1 *)
Lemma sigma'_Ep1G_rpM2 : forall X,
  X \in 'E_p^1(G) -> 'N(X) \subset M -> 'r_p(M) = 2.
Proof.
move=> X Ep1GX sNXM; have sXM := subset_trans (normG _) sNXM.
case/pnElemP: Ep1GX => _; move/abelem_pgroup=> pX lcardX.
case primep : (prime p); last by move: lcardX; rewrite lognE primep.
have [P pSylMP sXP] := Sylow_superset sXM pX; have [sPM pP _] := and3P pSylMP.
have : 'r_p(M) <= 2.
  suff : p \notin \alpha(M) by rewrite !inE -leqNgt. 
  by apply/negP; move/(alpha_sub_sigma M_max); move: (negbTE sigma'p)=> /= ->.
have : 'r_p(M) > 0 by rewrite p_rank_gt0.
case erpM1 : 'r_p(M) => [|[|[|]]] //=; case/negP: sigma'p; rewrite !inE.
apply/existsP; exists P; rewrite pSylMP /=; apply: subset_trans sNXM.
suff -> : X :=: 'Ohm_1(P) by rewrite char_norms // Ohm_char.
have cycP : cyclic P. 
  by rewrite (odd_pgroup_rank1_cyclic pP) ?mFT_odd // -erpM1 p_rankS.
have cardX : #|X| = p by rewrite -(part_pnat_id pX) p_part lcardX.
have sXOP : X \subset 'Ohm_1(P).
  rewrite (OhmE 1 pP) sub_gen //; apply/subsetP=> g Xg; rewrite !inE.
  by rewrite (subsetP sXP) //= -order_dvdn -cardX order_dvdG. 
apply/eqP; rewrite eqEcard (Ohm1_cyclic_pgroup_prime cycP pP) ?sXOP -?cardX //=.
rewrite -proper1G (proper_sub_trans _ sXP) // proper1G -cardG_gt1 cardX. 
by rewrite prime_gt1.
Qed.

(* The second claim in B & G 10.5 follows immediately from 10.4c. This is
   the remaining part of the lemma. *)
Lemma sigma'_Ep1G_exists_Ep2G : forall X, X \in 'E_p^1(G) -> 'N(X) \subset M -> 
    exists A, A \in 'E_p^2(G) /\ (X \subset A).
Proof.
move=> X Ep1GX sNXM; have sXM := subset_trans (normG _) sNXM.
have rpM2 := sigma'_Ep1G_rpM2 Ep1GX sNXM.
case/pnElemP: Ep1GX => _ abelX; move/abelem_pgroup: (abelX) => pX lcardX.
case primep : (prime p); last by move: lcardX; rewrite lognE primep.
have [P pSylMP sXP] := Sylow_superset sXM pX; have [sPM pP _] := and3P pSylMP.
have neXOZP : X :!=: 'Ohm_1('Z(P)).
  apply: contra sigma'p=> Xeq; rewrite !inE; apply/existsP; exists P. 
  rewrite pSylMP /= (subset_trans _ sNXM) // char_norms // (eqP Xeq).
  by rewrite (char_trans (Ohm_char 1 _)) // center_char.
have neOZP1 : 'Ohm_1('Z(P)) != 1.
  apply/negP; rewrite -(setIidPr (Ohm_sub 1 'Z(P))) /=; move/eqP; move/TI_Ohm1.
  rewrite setIid; move/(trivg_center_pgroup pP); move/eqP; apply/negP.
  rewrite -proper1G (proper_sub_trans _ sXP) // proper1G -cardG_gt1. 
  by rewrite -(part_pnat_id pX) p_part lcardX prime_gt1.
have pZP : p.-group 'Z(P) by rewrite (pgroupS _ pP) // subsetIl.
have pOZP : p.-group 'Ohm_1('Z(P)) by rewrite (pgroupS (Ohm_sub 1 _) pZP).
pose A := X <*> 'Ohm_1('Z(P)).
have abelA : p.-abelem A.
  have  sX_COZP : X \subset 'C('Ohm_1('Z(P))).
    rewrite centsC (subset_trans (Ohm_sub 1 _)) //.
    by rewrite (subset_trans (subsetIr _ _)) // centS.
  have Aeq : A = X * 'Ohm_1('Z(P)). 
    by rewrite /A norm_mulgenEl // cents_norm.
  have cprodXOZP : X \* 'Ohm_1('Z(P)) = X <*> 'Ohm_1('Z(P)) by rewrite cprodE.
  rewrite (cprod_abelem _ cprodXOZP) abelX /=. 
  by rewrite abelem_Ohm1 /= ?(abelianS (Ohm_sub 1 _)) ?center_abelian.
exists [group of A]; rewrite mulgen_subl; split=> //.
apply/pnElemP; rewrite subsetT abelA; split=> //.
apply/eqP; rewrite eqn_leq -{1}rpM2 -(p_rank_abelem abelA) p_rankS; last first.
  rewrite mulgen_subG sXM (subset_trans (Ohm_sub 1 _)) //.
  by rewrite (subset_trans (subsetIl _ _)). 
rewrite -{1}lcardX (p_rank_abelem abelA).
rewrite (properG_ltn_log (abelem_pgroup abelA)) // /proper (mulgen_subl) /=.
apply: contra neOZP1; move/(subset_trans (mulgen_subr _ _))=> sOZP_X.
have propOZPX : 'Ohm_1('Z(P)) \proper X by rewrite properEneq eq_sym neXOZP.
rewrite trivg_card1 -(part_pnat_id pOZP) p_part.
by move: (properG_ltn_log pX propOZPX); rewrite lcardX ltnS leqn0; move/eqP=>->.
Qed.

End Ten.

Section TenBis.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Type p : nat.
Implicit Type H P Q R V W M N X : {group gT}.

(* This is B & G, Theorem 10.6 *)
Theorem mFT_proper_plength1 : forall p H,
  H \proper G -> p.-length_1 H. 
Proof.
move=> p H pHG; have [M] := mmax_exists pHG; rewrite inE.
case/andP=> maxM sHM {pHG}; suff {H sHM}: p.-length_1 M by apply: plength1S.
case rpM: ('r_p(M) <= 2).
  case: (rank2_pdiv_compl_der_abelian_p'group (mmax_sol maxM) (mFT_odd _) rpM).
  move=> _ _ p'MOp'pM; rewrite /plength_1 eqEsubset pseries_sub /=.
  rewrite lastI pseries_rcons /= /pcore_mod (pcore_pgroup_id p'MOp'pM).
  by rewrite quotientGK // pseries_normal.
have alphap : p \in \alpha(M) by rewrite !inE ltnNge rpM.
pose Ma := M`_\alpha; have nsMaM : Ma <| M by apply: pcore_normal.
have [sMaM nMaM] := andP nsMaM.
have nMaM' : M^`(1) \subset 'N(Ma) by rewrite (subset_trans (der_sub 1 _)).
have sMaM' : Ma \subset M^`(1).
  exact: (subset_trans (Malpha_sub_Msigma maxM) (Msigma_sub_M' maxM)).
move: (SchurZassenhaus_split (pHall_Hall (Hall_M_Malpha maxM)) nsMaM).
case/splitsP=> K complKMa. 
have HMMa := pHall_Hall (Hall_M_Malpha maxM).
have sdKMa_M : Ma ><| K = M.
  by apply: (proj2 (iff_and (sdprod_normal_compl _ _ _))); rewrite complgC.
have [_ Meq nMaK IKMa1] := sdprodP sdKMa_M.
have sKM : K \subset M by rewrite -Meq mulG_subr.
have solMa : solvable Ma.
  exact: (solvableS (normal_sub nsMaM) (mmax_sol maxM)).
have {HMMa solMa} MaKeq: [~: Ma, K] = Ma. 
  exact: (proj1 (solvable_hall_dprod_der_subSset_comm_centr_compl _ HMMa _ _)).
have alphaHallMa : \alpha(M).-Hall(M) Ma by apply: Hall_M_Malpha.
have alpha'HallK : \alpha(M)^'.-Hall(M) K.
  rewrite pHallE sKM /= -(@eqn_pmul2l #|Ma|) ?cardG_gt0 //.
  by rewrite (sdprod_card sdKMa_M) (card_Hall alphaHallMa) partnC ?cardG_gt0.
have cardKK' : #|K / K^`(1)| = #|M / M^`(1)|.
  rewrite !card_quotient ?der_norm // -!divgS ?der_sub //.
  have isoKMMa : K \isog M / Ma.
    rewrite -sdKMa_M sdprodEgen // mulgenC quotient_mulgen //=.
    by rewrite (isog_trans _ (second_isog _)) // IKMa1 quotient1_isog.
  have isoK'M'Ma : K^`(1) \isog M^`(1) / Ma.
    by rewrite quotient_der // bgFunc_isog.
  rewrite (isog_card isoKMMa) (isog_card isoK'M'Ma) ?card_quotient //.
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
have piMq : q \in \pi(#|M|).
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
rewrite inE -order_dvdn /=; case/andP=> ZQx xq1 _.
set X := <[x]> => ZgroupCMaX.
have sXK : X \subset K.
  apply: (subset_trans _ (subset_trans (center_sub _) (pHall_sub SylKQ))).
  by rewrite cycle_subG.
have solM := mmax_sol maxM; have oddM := mFT_odd M.
have HMa := pHall_Hall alphaHallMa.
apply: (odd_sdprod_Zgroup_cent_prime_plength1 _ _ nsMaM _ _ sXK) => //.
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
  by rewrite inE /=; apply/existsP; exists P; rewrite pSyl_PM.
have [p_pr _ _] := pgroup_pdiv pP ntP; have pMG := mmax_proper M_max.
have pl1M := mFT_proper_plength1 p pMG; have solM := mmax_sol M_max.
have pHall_P : p.-Sylow('N(P)) P.
  by rewrite -(setIidPr (subsetT 'N(P))) // Sylow_subnorm.
have Hall_P := pHall_Hall pHall_P.
have sPM' : P \subset M^`(1).
  apply: subset_trans _ (Msigma_sub_M' M_max).
  rewrite (subset_normal_Hall _ (Hall_M_Msigma M_max) (pcore_normal _ _)).
  rewrite /psubgroup sPM.
  by apply: sub_in_pnat pP => q q_piP; rewrite inE /=; move/eqP->.
have sPNP' : P \subset ('N(P))^`(1).
  apply: subset_trans _ (dergS 1 (subsetIr M _)) => /=.
  by apply: sol_Sylow_plength1_sub_norm_der _ pSyl_PM pl1M sPM'.
split=> //.
  move=> V defV; have solP := solvableS sPM solM.
  by case: (solvable_hall_dprod_der_subSset_comm_centr_compl solP _ defV sPNP').
move=> Q sQP x sQxP; have pQ : p.-group Q := pgroupS sQP pP.
wlog ntQ: / Q :!=: 1.
  case: eqP => [->|_]; [ exists 1; rewrite ?in_group // | by apply ].
  by rewrite conjsg1 conjs1g.
have [th101a _ _ _] := mmax_sigma_core_nt_pgroup M_max p_sigM ntQ pQ.
have sQM := subset_trans sQP sPM; have sQxM := subset_trans sQxP sPM.
have [q [u [qCQ uM defx]]] := th101a sQM _ sQxM.
have sQuP: Q :^ u \subset P.
  by rewrite -(normP (subsetP (cent_sub _) _ qCQ)) -conjsgM -defx.
case: (sol_Sylow_plength1_norm_conj _ _ pl1M sQP uM)=>// q' q'CQ [y yNP defu].
exists y; first by rewrite (subsetP (subsetIr _ _) _ yNP).
rewrite defx -defu !conjsgM (normP (subsetP (cent_sub _) _ qCQ)).
by case/setIP: q'CQ => _ q'CQ; rewrite (normP (subsetP (cent_sub _) _ q'CQ)).
Qed.

(* This is B & G 10.7(a2) *)
Corollary pSylow_norm_split_sub_norm_der1 : 
  forall p P, p.-Sylow(G) P -> P \subset 'N(P)^`(1).
Proof. 
move=> p P pSyl_P.
by case: (pSylow_norm_split_sub_norm_der1_commg_norm_sub pSyl_P).
Qed.

(* This is B & G 10.7(a1) *)
Corollary pSylow_norm_split_commg : forall P p, p.-Sylow(G) P -> 
  forall V, P ><| V :=: 'N(P) -> [~: P, V] :=: P.
Proof.
move=> p P pSyl_P.
by case: (pSylow_norm_split_sub_norm_der1_commg_norm_sub pSyl_P).
Qed.

(* This is B & G 10.7(c) *)
Corollary pSylow_conj_sub_in_norm : forall P p, p.-Sylow(G) P -> 
  forall Q, Q \subset P -> forall x : gT, 
    Q :^ x \subset P -> exists2 y,y \in 'N(P) & Q :^ x :=: Q :^ y.
Proof.
move=> P p pSyl_P.
by case: (pSylow_norm_split_sub_norm_der1_commg_norm_sub pSyl_P).
Qed.

(* This is B & G 10.7(b) *)
Corollary pSylow_rank3_abelian_or_Ohm_Z_decomp : forall P p, p.-Sylow(G) P ->
  'r(P) < 3 -> abelian P \/ exists P1, exists P2 : {group gT}, 
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
have [?]:= Blackburn_theorem pP (mFT_odd _) ntP rP defP p'V (mFT_odd _).
case; [ by left | move=>[? [?]]; case/cprodP=> [[P1 P2 -> -> def_P]]].
move=> [? [nAP lcP ? ? defO1]]; right; exists P1; exists P2; split => //.
  by split => //; rewrite -def_P cprodE.
have pP1 : p.-group P1 by rewrite (pgroupS _ pP) // -def_P mulg_subl.
have pr_p : prime p by case: (pgroup_pdiv pP ntP).
have [[_ <- //] _] : extraspecial P1.
apply: (card_p3group_extraspecial pr_p). 
  by rewrite -lcP -p_part (part_pnat_id pP1).
wlog ntZ : / 'Z(P1) :!=: 1.
  case: eqP => [trivZ _|_]; last by apply.
  by rewrite (trivg_center_pgroup pP1 trivZ) cards1 logn1 in lcP.
have [_ _ [[//|/=[cZ|r cZ]]]]:= pgroup_pdiv (pgroupS (subsetIl _ _) pP1) ntZ.
  (* make a lemma *)
  have idxGZ : #|P1 : 'Z(P1)| = p.
    rewrite -divgS ?subsetIl // cZ -(part_pnat_id pP1) p_part lcP !expnS !expn0.
    by rewrite !muln1 !mulnK // -ltn_divl ?div0n ?prime_gt0.
  have cyQ : cyclic (P1 / 'Z(P1)).
    by rewrite prime_cyclic ?card_quotient ?idxGZ // normsI ?norms_cent ?normG.
  by rewrite (center_cyclic_abelian cyQ) center_abelian in nAP.
move: nAP; rewrite ((P1 :=P: 'Z(P1)) _) ?center_abelian // eq_sym eqEcard.
by rewrite subsetIl cZ -(part_pnat_id pP1) p_part lcP leq_pexp2l ?prime_gt0.
Qed.

(* This is B & G 10.7(d) *)
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
  by rewrite hall_conj ?in_group.
rewrite eqEsubset -sub_conjg XX sub_conjg invgK.
by rewrite conjIg /= (conjGid xP) /= (conjGid xNQ) /= (pHall_sub pHall_S).
Qed.

(* This is B & G 10.7(e) *)
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

Variable M : {group gT}.
Variable M_max : M \in 'M.

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
pose P := [pred q | nat_of_ord (q :'I_#|G|.+1) \in \pi(#|G|)].
have Pq : P (Ordinal lt_q) by rewrite /P /= inE /= mem_primes pr_q cardG_gt0 qd.
rewrite FittingEgen sub_gen // (bigcup_max _ Pq) //=.
rewrite -(eq_pcore _ (negnK _)) -bigcap_p'core subsetI sQG /=.
apply/bigcapsP=> [[r /= _]]; rewrite !inE /= => neq_rq.
case piGp: (r \in \pi(#|G|)); last first.
  by rewrite pcore_pgroup_id // /pgroup -partn_eq1 ?cardG_gt0 ?p_part_eq1 ?piGp.
move: piGp; rewrite mem_primes; case/and3P => *.
rewrite (subset_normal_Hall _ (allNC _ _ _)) ?pcore_normal // /psubgroup sQG /=.
apply: (sub_in_pnat _ (pHall_pgroup qHall_Q)) => e _; rewrite !inE /=.
by move/eqP=> ->; rewrite eq_sym.
Qed.

Lemma mmax_beta_Hall_nil_normal_compl_max_pdiv : 
  [/\ \beta(M).-Hall(M) M`_\beta /\ \beta(M).-Hall(G) M`_\beta,
      forall H, \beta(M)^'.-Hall(M^`(1)) H || \beta(M)^'.-Hall(M`_\sigma) H -> 
        nilpotent H &
      forall p, prime p -> p \notin \beta(M) -> [/\
        p^'.-Hall(M^`(1)) 'O_p^'(M^`(1)), 
        p^'.-Hall(M`_\sigma) 'O_p^'(M`_\sigma) &
        forall q, prime q -> q %| #| M / 'O_p^'(M) | -> q <= p]].
Proof.
have [MB bHall_MB] := HallExist \beta(M) (mmax_sol M_max).
have sMBMs : MB \subset M`_\sigma.  
  rewrite (subset_normal_Hall _ (Hall_M_Msigma M_max)) ?pcore_normal //.
  rewrite /psubgroup (pHall_sub bHall_MB); move: (pHall_pgroup bHall_MB).
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
    case: (leqP 3 'r_p(P))=> rP; rewrite /narrow -1?ltnS ?rP //;apply/orP;right.
    move: (n_pB); rewrite !inE; apply: contraR => nnarP.
    rewrite (p_rank_Sylow pSyl_P) rP.
    have pa : p \in \alpha(M) by rewrite inE /= (p_rank_Sylow pSyl_P).
    have := alpha_sub_sigma M_max pa; rewrite inE /= /narrow.
    move/exists_inP => [Q pSyl_Q snQM]; apply/existsP; exists Q. 
    rewrite negb_or leqNgt -(p_rank_Sylow pSyl_Q) (p_rank_Sylow pSyl_P) rP /=.
    rewrite (mmax_sigma_Sylow M_max) //=; apply: contra nnarP => narQ.
    rewrite (@isog_noncyclic_narrow _ _ Q P) //.
    have [x xM ->] := Sylow_trans pSyl_P pSyl_Q.
    by rewrite -{2}(setIid P) -morphim_conj sub_isog // injm_conj.
  have sMBOM' : MB \subset 'O_p^'(M^`(1)).
    rewrite (subset_normal_Hall _ ncM' (pcore_normal _ _)) /psubgroup /=.
    by rewrite (subset_trans sMBMs (Msigma_sub_M' M_max)) p'MB.
  split=> //; apply: normal_max_pgroup_Hall _ (pcore_normal _ _) => /=.
  apply/maxgroupP; rewrite /psubgroup pcore_pgroup pcore_sub; split=> //= H.
  case/andP=> sHMs p'H sOH; apply/eqP; rewrite eqEsubset sOH andbT.
  have sI: 'O_p^'(M^`(1)) :&: M`_\sigma \subset 'O_p^'(M`_\sigma).
    rewrite pcore_max ?(pgroupS (subsetIl _ _) (pcore_pgroup _ _)) //=.
    rewrite /normal (subsetIr _ _) (subset_trans (pcore_sub _ _)) //.
    rewrite normsI // char_norm ?pcore_char //.
    by rewrite (char_trans _ (der_char 1 M)) // pcore_char.
  rewrite (subset_trans _ sI) // subsetI sHMs andbT.
  rewrite (subset_normal_Hall _ ncM' (pcore_normal _ _)) /= /psubgroup p'H.
  by rewrite (subset_trans sHMs (Msigma_sub_M' M_max)).
have n_BM: ~~ \beta(M).-group M.
  have: M`_\alpha \proper M.
    rewrite (sub_proper_trans (Malpha_sub_Msigma M_max)) //.
    rewrite (sub_proper_trans (Msigma_sub_M' M_max)) //.
    exact: sol_der1_proper (mmax_sol M_max) (subxx _) (mmax_neq1 M_max).
  apply: contraL=> bM; have A_max := Hall_M_Malpha M_max.
  rewrite {2}[M](hall_maximal A_max) ?proper_irrefl ?pcore_sub //.
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
  rewrite -(hall_maximal bHall_MB _ bSUM) // (subset_trans _ (der_sub 1 _)) //.
  by rewrite (subset_trans _ (pcore_sub q^' _)) //= bigcap_inf.
have sMB_M := pHall_sub bHall_MB; have bMB := pHall_pgroup bHall_MB.
have nMMB : MB <| M.
  rewrite /normal sMB_M defMB norms_bigcap //; apply/bigcapsP=> i _.
  by rewrite char_norm ?(char_trans (pcore_char _ _)) // der_char.
have defMb : MB :=: M`_\beta.
  apply/eqP; rewrite eqEsubset pcore_max // (subset_normal_Hall _ bHall_MB) //.
  by rewrite /psubgroup pcore_sub pcore_pgroup.
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
have TI : P :&: MB :=: 1.
  by rewrite setIC (coprime_TIg (pnat_coprime _ b'P)) // defMB [_.-nat _]bSUM.
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
  rewrite (leq_trans (BGsection3.leq_quotient _ _)) //.
  by rewrite (dvdn_leq _ (cardSg (der_sub _ _))) ?cardG_gt0.
exact: (bigcap_inf _ (nb_p : Pr (Ordinal lt_p))).
Qed.


Let sub_in_pcore : 
    forall (gT : finGroupType) (pi1 pi2 : nat_pred) (G : {group gT}),
  {in \pi(#|G|), {subset pi1 <= pi2}} -> 'O_pi1(G) \subset 'O_pi2(G).
Proof.
move=> rT pi1 pi2 G sub.
rewrite -(@pcore_pgroup_id \pi(#|G|)) /pgroup ?pnat_pi ?cardG_gt0 //.
rewrite -!pcoreI sub_pcore // => x pi_x; move: pi_x (sub x). 
by rewrite !inE; case/andP => -> -> ->.
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

Corollary foo_10_9a : 
  forall p q, prime p -> prime q
   -> p != q -> p \notin \beta(M)-> q \notin \beta(M)->
  forall X : {group gT}, q.-subgroup(M) X -> (X \subset M^`(1)) || (p < q) ->
    [/\ exists2 P : {group gT}, p.-Sylow(M`_\sigma) P & X \subset 'C(P),
        p \in \alpha(M) -> 'C_M(X)%G \in 'U &
        q.-Sylow(M^`(1)) X -> 
          exists2 P : {group gT}, p.-Sylow(M^`(1)) P  & P \subset 'N_M(X)^`(1)].
Proof.
move=> p q pr_p pr_q neq_pq pB' qB' X; case/andP=> sXM qX XM'.
pose pq := [predU (p : nat_pred) & (q : nat_pred) ].
have solM := mmax_sol M_max.
have sXM'M : (X <*> M^`(1)) \subset M by rewrite mulgen_subG sXM der_sub.
have solXM' : solvable (X <*> M^`(1)) := solvableS sXM'M solM.
have pqX : pq.-group X.
  by apply: sub_in_pnat _ qX => x _ xq; rewrite inE /= xq orbT.
have [W /= pqHall_W sXW {pqX}] := HallSubset solXM' (mulgen_subl _ _) pqX.
have b'W :  \beta(M)^'.-group W.
  apply/pgroupP=> x pr_x xd; move: (pgroupP (pHall_pgroup pqHall_W) x pr_x xd).
  rewrite inE /=; apply: contraL; rewrite negb_or => /= xB; rewrite !inE /=.
  by case: eqP xB pB'=> [-> -> //|_ xB]; case: eqP xB qB' => // -> ->.
have [Ws /= b'Hall_Ws sWWs {b'W}]:=  HallSubset solXM' (pHall_sub pqHall_W) b'W.
have nilWM' : nilpotent (W :&: M^`(1)).
  apply: nilpotentS (setSI _ sWWs) _.
  have [_ th108 _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
  apply: th108 => /=; rewrite (HallSubnormal _ _ b'Hall_Ws) //=.
  by rewrite /normal mulgen_subr (subset_trans _ (char_norm (der_char _ _))).
have sWM := subset_trans sWWs (subset_trans (pHall_sub b'Hall_Ws) sXM'M).
have nilW : nilpotent W.
  case/orP: XM' => [sXM'|lt_pq].
    rewrite ((W :=P: W :&: M^`(1)) _) // eqEsubset subsetIl subsetI subxx.
    rewrite -(mulSGid sXM') -norm_mulgenEl ?(pHall_sub pqHall_W) //=.
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
    rewrite /pgroup (isog_card (second_isog _)) //. 
    rewrite [_.-nat _](pgroupS (quotientS _ (pHall_sub pqHall_W))) //=.
    by rewrite (quotient_mulgen (subset_trans sXW nM'W)) quotient_pgroup // qX.
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
    rewrite setIC (subset_normal_Hall _ pHall_OpM'W) ?pcore_normal //.
    by rewrite /= setIC /psubgroup sPM'W pP.
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
    rewrite /normal (subset_trans (normal_sub nMsM')) ?mulgen_subr //=.
    have ? := sigma_core_normal M.
    by rewrite mulgen_subG (subset_trans sXW) ?(subset_trans sWM) ?normal_norm.
  rewrite setIC (pSylow_normalI nMs) //=.
  apply: BGsection3.pSylow_Hall_Sylow pqHall_W _ (nilpotent_pcore_Hall p nilW).
  by rewrite !inE /= eqxx.
have sXCWMs : X \subset 'C('O_p(W) :&: M`_\sigma).
  have nilOpW : nilpotent 'O_p(W) by apply: nilpotentS (pcore_sub _ _) nilW.
  have sXOp' : X \subset 'O_p^'(W).  
    rewrite (subset_normal_Hall _ (nilpotent_pcore_Hall _ _)) ?pcore_normal //.
    rewrite /psubgroup sXW /pgroup (sub_in_pnat _ qX) // => x _.
    by rewrite !inE /=; move/eqP=> ->; rewrite eq_sym.
  rewrite (subset_trans sXOp') // (centsS (subsetIl _ _)) //.
  by case/dprodP: (nilpotent_pcoreC p nilW); rewrite centsC.
split; first by exists ('O_p(W) :&: M`_\sigma)%G.
  have prCMG := sub_proper_trans (subsetIl _ 'C(X)) (mmax_proper M_max).
  move=> pA; have pS := alpha_sub_sigma M_max pA; move: (pA).
  rewrite inE => /= rM; apply: rank3_Uniqueness prCMG _ => /=.
  have sPCMX : 'O_p(W) :&: M`_\sigma \subset 'C_M(X).
    by rewrite subsetI (subset_trans (subsetIr _ _) (pcore_sub _ _)) centsC.
  have sOMs : 'O_p(W) \subset M`_\sigma.
    rewrite (subset_normal_Hall _ (Hall_M_Msigma M_max)) ?pcore_normal //=.
    rewrite /psubgroup (subset_trans (pcore_sub _ _)) //.
    by apply: sub_in_pnat _ (pcore_pgroup _ _)=>x _; rewrite inE /=; move/eqP->.
  have pSyl_O : p.-Sylow(M) 'O_p(W).
    apply: BGsection3.pSylow_Hall_Sylow (Hall_M_Msigma M_max) pS _ => /=.
    apply: BGsection3.pSylow_Hall_Sylow pSyl_OWMs _ _; rewrite ?inE //=.
    rewrite -max_pgroup_Sylow; apply/maxgroupP; rewrite /psubgroup subsetI.
    rewrite pcore_pgroup sOMs subxx; split => //= H; rewrite subsetI -andbA.
    by case/and3P=> sHO _ _ sOH; apply/eqP; rewrite eqEsubset sOH sHO.
  rewrite (leq_trans rM) // (leq_trans _ (rankS sPCMX)) //=.
  rewrite (rank_pgroup (pHall_pgroup pSyl_OWMs)) -(p_rank_Sylow pSyl_OWMs).
  by rewrite (leq_trans _ (p_rankS _ sOMs)) // (eq_leq (p_rank_Sylow pSyl_O)).
move=> qSyl_X.
have sWsM' : Ws \subset M^`(1).
  have := pHall_sub b'Hall_Ws.
  rewrite norm_mulgenEl ?(subset_trans sXM (der_norm _ _)) //.
  by rewrite (mulSGid (pHall_sub qSyl_X)).
have defX : 'O_q(Ws) :=: X.
  have b'Hall_WsM' := pHall_subl sWsM' (mulgen_subr _ _) b'Hall_Ws.
  have qSyl_XWs := pHall_subl (subset_trans sXW sWWs) sWsM' qSyl_X.
  have [_ th108b _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
  have := th108b Ws; rewrite b'Hall_WsM' /=; move/(_ (erefl _)) => nilWs.
  have [x xWs ->] := Sylow_trans (nilpotent_pcore_Hall q nilWs) qSyl_XWs.
  by rewrite (normP _) // (subsetP _ _ xWs) // char_norm ?pcore_char.
have defM' : M`_\beta <*> Ws :=: M^`(1).
  apply/eqP; rewrite eqEcard mulgen_subG sWsM' andbT //=.
  have ? : M \subset 'N(M`_\beta) by rewrite char_norm ?pcore_char.
  rewrite norm_mulgenEr ?(subset_trans sWsM') ?(subset_trans (der_sub _ _)) //.
  rewrite -[#|M^`(1)|](partnC \beta(M) (cardG_gt0 _)) /=.
  rewrite coprime_cardMg; last first.
    by rewrite (pnat_coprime (pcore_pgroup _ _) (pHall_pgroup b'Hall_Ws)).
  rewrite -(part_pnat_id (pcore_pgroup _ _)) -/(beta_core M).
  rewrite -(part_pnat_id (pHall_pgroup b'Hall_Ws)).
  rewrite leq_mul ?andbT; last first.
    move: b'Hall_Ws; rewrite pHallE; case/andP=> _; move/eqP=> -> /=.
    rewrite (part_pnat_id (part_pnat _ _)) dvdn_leq // partn_dvd ?cardG_gt0 //.
    by apply: cardSg; exact: mulgen_subr.
    have [[Hall_Mb _] _ _] := mmax_beta_Hall_nil_normal_compl_max_pdiv.
    move: Hall_Mb; rewrite pHallE; case/andP=> _; move/eqP=> -> /=.
    rewrite (part_pnat_id (part_pnat _ _)) dvdn_leq // partn_dvd ?cardG_gt0 //.
    exact: cardSg (der_sub _ _).
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
    apply/eqP; rewrite -defM' mulgenC quotient_mulgen //.
    rewrite eqEcard (subset_trans _ (morphim_pcore _ _ _)) -?defX //=.
    have TI_Ws : Ws :&: M`_\beta :=: 1.
      rewrite setIC; apply: coprime_TIg (pnat_coprime (pcore_pgroup _ _) _).
      exact: pHall_pgroup b'Hall_Ws.
    have TI_X : X :&: M`_\beta :=: 1.
      rewrite setIC; apply: coprime_TIg (pnat_coprime (pcore_pgroup _ _) _).
      rewrite -defX (sub_in_pnat _ (pcore_pgroup q _)) // => r _.
      by rewrite 3!inE /=; move/eqP=> ->.
    rewrite -(isog_card (bgFunc_isog (bgFunc_pcore q) (quotient_isog _ _))) //=.
    by rewrite -(isog_card (quotient_isog _ _)) //= defX.
  apply: char_normal (char_from_quotient _ (pcore_char  \beta(M) _) _) => /=.
    by rewrite /normal mulgen_subl mulgen_subG normG.
  rewrite mulgenC quotient_mulgen // defXMB.
  apply: char_trans (pcore_char _ _) _. 
  by rewrite /= quotient_der ?der_char // char_norm ?pcore_char.
pose U := 'N_M(X).
have defM : M :=: M`_\beta * U.
  have sXNMX : X \subset U by rewrite subsetI sXM normG.
  rewrite /U -(mulSGid sXNMX) /= -/U mulgA -norm_mulgenEr; last first.
    by rewrite (subset_trans sXM) // char_norm ?pcore_char.
  have ? : Ws \subset 'N(M`_\beta).
    rewrite (subset_trans sWsM') ?(subset_trans (der_sub _ _)) //.
    by rewrite normal_norm ?pcore_normal.
  rewrite (Frattini_arg _ (pHall_subl _ _ qSyl_X)) ?mulgen_subr /= -?defM' //.
  rewrite !norm_mulgenEr ?mulGS ?(subset_trans sXW) ?(subset_trans sWWs) //.
  by rewrite mulg_subr.
have sOWU : 'O_p(W) \subset U.
  rewrite subsetI (subset_trans (pcore_sub _ _)) ?sWM //= -defX.
  rewrite (subset_trans (pcore_sub _ _)) // (subset_trans sWWs) //.
  by rewrite char_norm ?pcore_char.
have pSyl_OW : p.-Sylow(M^`(1)) 'O_p(W).
  have := nilpotent_pcore_Hall p nilW.
  have := pHall_subl (subset_trans sWWs sWsM') (mulgen_subr _ _) pqHall_W => /=.
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
  by rewrite inE /=; apply/existsP; exists S; rewrite sNSM qSyl_SM.
have qA' : q \in \alpha(M)^'.
  rewrite inE /=; apply: contra neq_HM; rewrite inE /=.
  rewrite (p_rank_Sylow qSyl_SM) -(rank_pgroup qS); move/rank3_Uniqueness.
  move/(_ (mFT_pgroup_proper qS)); move/uniq_mmaxP => [X defM].
  have sSH := subset_trans (normG _) sNSH.
  by rewrite (eq_uniq_mmax defM M_max sSM) (eq_uniq_mmax defM H_max sSH).
have qB' : q \notin \beta(M).
  by apply/negP; move/beta_sub_alpha => qA; move: qA'; rewrite inE /= qA.
have sSM' : S \subset M^`(1).
  apply: subset_trans _ (Msigma_sub_M' M_max).
  rewrite (subset_normal_Hall _ (Hall_M_Msigma M_max)) ?pcore_normal //.
  rewrite /psubgroup sSM.    
  by apply: sub_in_pnat qS => r r_piP; rewrite inE /=; move/eqP->.
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
      rewrite /= -{3}quotient_mulgen // pquotient_pcore //= /normal.
        rewrite norm_mulgenEl //= mulGSid //; apply: sub_pcore => x xB.
        exact: (alpha_sub_sigma M_max (beta_sub_alpha xB)).
      have ? : M \subset 'N(M`_\beta) := normal_norm (pcore_normal _ _).
      by rewrite mulgen_subr mulgen_subG ?(subset_trans (pcore_sub _ _)).
    have n2 : S \subset 'N(M`_\beta).
      exact: subset_trans sSM (normal_norm (pcore_normal _ _)).
    have qSyl_SQ := quotient_pHall n2 qSyl_S.
    symmetry; apply: (f_equal (@gval _) (hall_maximal qSyl_SQ _ _ _)) => //=.
      exact: subset_trans (pcore_sub _ _) (quotientS _ (subsetT _)).
      exact: pcore_pgroup.
    rewrite (subset_normal_Hall _ (nilpotent_pcore_Hall _ _)) ?pcore_normal //.
    rewrite /psubgroup quotient_pgroup ?andbT //=.
    rewrite (subset_normal_Hall _ (quotient_pHall _ (Hall_M_Msigma M_max))) //.
      rewrite /psubgroup quotientS //=.
      apply: sub_in_pnat _ (quotient_pgroup _ qS) => x _.
      by rewrite inE /=; move/eqP=> ->.
    exact: subset_trans (pcore_sub _ _) (normal_norm (pcore_normal _ _)).     
  have nSM: S / M`_\beta <| M / M`_\beta.
    by rewrite defXMB (char_normal_trans _ nMsMb) // pcore_char.
  have ? := char_normal_trans (pcore_char q _) nMsMb.
  have n1 : M`_\beta <| M`_\beta <*> S.
    by rewrite /normal mulgen_subl mulgen_subG normG.
  rewrite -(quotientGK n1) /= -{8}(quotientGK (pcore_normal \beta(M) M)) /=.
  rewrite mulgenC quotient_mulgen // morphpre_normal ?defXMB //=.
    rewrite !(subset_trans (pcore_sub _ _), morphimS) //.
    exact: normal_norm (pcore_normal _ _).
  exact: morphimS (normal_norm (pcore_normal _ _)).
have defM : M :=: M`_\beta * 'N_M(S).
  have sXNMX : S \subset 'N_M(S) by rewrite subsetI sSM normG.
  rewrite -(mulSGid sXNMX) /= mulgA -norm_mulgenEr; last first.
    by rewrite (subset_trans sSM) // char_norm ?pcore_char.
  by rewrite (Frattini_arg _ (pHall_subl _ _ qSyl_S)) ?mulgen_subr /= ?subsetT.
split.
  apply/eqP; rewrite eqEsubset mul_subG ?subsetIr ?pcore_sub ?andbT //.
  rewrite setIC group_modr ?pcore_sub //.
  apply: subset_trans (setIS _ (mulSg _ sNSH)). 
  have ? : 'N_M(S) \subset 'N(M`_\beta).
    by rewrite (subset_trans _ (char_norm (pcore_char _ _))) // subIset ?subxx.
  rewrite -group_modr ?pcore_sub //.
  by rewrite -norm_mulgenEl 1?mulgenC ?norm_mulgenEr //= -defM.
have nNMSU : 'N_M(S)%G \notin 'U.
  apply: contra neq_HM => nMSU; apply/eqP.
  have sNMSH : 'N_M(S) \subset H := subset_trans (subsetIr _ _) sNSH.
  exact: eq_uniq_mmax (def_uniq_mmax nMSU M_max (subsetIl _ _)) H_max sNMSH.
have qsubgS : q.-subgroup(M) S by rewrite /psubgroup qS sSM.
move=> p; apply/idP/idP => [pA|]; last exact: beta_sub_alpha.
case: (eqVneq p q) => [defp | nqpq].
  by move: pA; rewrite defp => qA; move: qA'; rewrite 2!inE /= qA.
have pr_p : prime p.
  move: pA; rewrite inE /=; case/p_rank_pmaxElem_exists => F.
  case/pmaxElemP; case/pElemP=> sFM pabF _.
  case: (eqsVneq F 1) => [->|ntF]; first by rewrite p_rank1.
  by case: (pgroup_pdiv (abelem_pgroup pabF) ntF).
apply: contraR (nNMSU) => pB'.
case: (foo_10_9a _ _ _ pB' _ qsubgS); rewrite ?sSM' // => _ th109a _.
case/negP: nNMSU; apply: uniq_mmaxS (setIS _ (cent_sub _)) _ (th109a pA).
exact: sub_proper_trans (subsetIl _ _) (mmax_proper M_max). 
Qed.

(* This is B & G 10.10 *)
Lemma foo10_10 : 
  forall p q, prime p -> prime q
   -> p != q -> forall A Q : {group gT}, A \in 'E_p^2(G) :&: 'E*_p(G) ->
  Q \in |/|*(A; q) -> q %| #|'C(A)| -> exists2 P, p.-Sylow(G) P & [/\
    A \subset P, 'N(P) = 'O_p^'('C(P)) * ('N(P) :&: 'N(Q)),
    P \subset 'N(Q)^`(1) & 
    cyclic Q || ('E_q^2(Q) :&: 'E*_q(Q) != set0)  -> P \subset 'C(Q) ].
Proof.
move=> p q pr_p pr_q npq A Q; case/setIP; case/pnElemP=> _ abeA clA emA NQ qd.
have ntA : A :!=: 1.
  by case: eqP clA => // ->; rewrite cards1 logn1.
have ncA := plength_1_normed_constrained ntA emA (mFT_proper_plength1 _).
have nq_piA : q \notin \pi(#|A|).
  apply/negP; rewrite mem_primes; case/and3P=> _ _ qdA.
  move: (pgroupP (abelem_pgroup abeA) _ pr_q qdA) npq; rewrite inE /=.
  by rewrite eq_sym => ->.
have rZA : 1 < 'r('Z(A)).
  by admit.
have [P pSyl_P sAP] := Sylow_superset (subsetT _) (abelem_pgroup abeA).
have def_piA : \pi(#|A|) =i (p:nat_pred).
  have [_ pd _] := pgroup_pdiv (abelem_pgroup abeA) ntA.
  move=> x; rewrite !inE /= mem_primes; case: eqP => [|neq].
    by move=> ->; rewrite pr_p cardG_gt0.
  case pr_x : (prime x) => //; case xd: (x %| #|A|); last by rewrite !andbF.
  by move: (pgroupP (abelem_pgroup abeA) _ pr_x xd); rewrite inE /=; move/eqP.
have piA_P : \pi(#|A|).-group P.
  by move: (pHall_pgroup pSyl_P); apply: sub_in_pnat=> x _; rewrite def_piA.
have def_OpiA : forall P, 'O_\pi(#|A|)^'(P) = 'O_p^'(P).
  by move=> S; apply: eq_pcore; apply: eq_negn.
have th73 := normed_constrained_rank2_trans ncA nq_piA qd rZA.
have snAP : A <|<| P.
  rewrite /subnormal sAP /=.
  by admit.
have := normed_trans_superset ncA nq_piA snAP piA_P th73.
rewrite !def_OpiA => /= [[th74a th74b th74c th74d]]; rewrite th74a in th74d.
exists P => //.
Admitted.

End TenBis.


