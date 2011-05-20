(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection2 BGsection3 BGsection4 BGsection5.
Require Import BGsection6 BGsection7 BGsection9 BGsection10 BGsection12.
Require Import BGsection13 BGsection14 BGsection15.

(******************************************************************************)
(*   This file covers B & G, section 16; it summarises all the results of the *)
(* local analysis. Some of the definitions of B & G have been adapted to fit  *)
(* in beter with Peterfalvi, section 8, dropping unused properties and adding *)
(* a few missing ones. This file also defines the following:                  *)
(*   normTIset V W <-> W is the normaliser of all non-empty subsets of V,     *)
(*                    equivalently, V is a TI-subset of G (the full group)    *)
(*                    with normalizer (and centralizer) W if non-empty.       *)
(*    of_typeF M U <-> M = M`_\F ><| U is of type F, in the sense of          *)
(*                     Petervalvi (8.1) rather than B & G section 14.         *)
(* of_typeP M U W1 <-> M = M`_\F ><| U ><| W1 is of type P, in the sense of   *)
(*                     Peterfalvi (8.4) rather than B & G section 14.         *)
(*      of_typeI M <-> M is of type I, in the sense of Peterfalvi (8.3); this *)
(*                     is almost identical to B & G conditions (Ii) - (Iv),   *)
(*                     except that (Iiv) is dropped, as is the condition      *)
(*                     p \in \pi* in (Iv)(c). Also, the condition 'O_p^'(M)   *)
(*                     cyclic, present in both B & G and Peterfalvi, is       *)
(*                     weakened to 'O_p^'(M`_\F) cyclic, because this is the  *)
(*                     statement established in B & G, Theorem 15.7, and we   *)
(*                     could not see how to strengthen it. This seams to be a *)
(*                     typo in B & G that was copied over to Petrfalvi (8.3). *)
(*                     It appears to be of no consequence because (8.3) is    *)
(*                     only used in (12.6) and (12.10) and neither use the    *)
(*                     assumption that 'O_p^'(M) is cyclic, or 'O_p^'(M`_\F)! *)
(* of_typeII_IV M U W1 <-> M = M`_\F ><| U ><| W1 is of type II, III, or IV,  *)
(*                     in the sense of Peterfalvi (8.6)(a). This is almost    *)
(*                     exactly the contents of B & G, (T1)-(T7), except that  *)
(*                     (T6) is dropped, and 'C_(M`_\F)(W1) \subset M^`(2) is  *)
(*                     added (PF, (8.4)(d) and B & G, Theorem C(3)).          *)
(*     of_typeII M <-> M is of type II in the sense of Peterfalvi (8.6); this *)
(*                     differs from B & G by dropping the rank 2 clause in    *)
(*                     IIiii and replacing IIv by B(2)(3) (note that IIv is   *)
(*                     stated incorrectly: M' should be M'^#).                *)
(*    of_typeIII M <-> M is of type III in the sense of Peterfalvi (8.6).     *)
(*     of_typeIV M <-> M is of type IV in the sense of Peterfalvi (8.6).      *)
(*      of_typeV M <-> M is of type V in the sense of Peterfalvi (8.7); this  *)
(*                     differs from B & G (V) by dropping the p \in \pi*      *)
(*                     condition in clauses (V)(b) and (V)(c).                *)
(* FTtype_spec i M <-> M is of type i, for 0 < i <= 5, in the sense of the    *)
(*                     predicates above.                                      *)
(*        FTtype M == the type of M, in the sense above, when M is a maximal  *)
(*                    subgroup of G (this is an iteger i between 1 and 5).    *)
(*           M`_\s == an alternative, combinatorial definition of M`_\sigma   *)
(*                 := M`_\F if M if of type I or II, else M^`(1)              *)
(*          'A1(M) == the "inner Dade kernel" of a maximal group M, as        *)
(*                    defined in Peterfalvi (8.10).                           *)
(*                 := (M`_\s)^#                                               *)
(*           'A(M) == the "Dade kernel" of M, as defined in Peterfalvi (8.10) *)
(*                    (this differs from B & G by excluding 1).               *)
(*          'A0(M) == the "outer Dade kernel" of M, as defined in Peterfalvi  *)
(*                    (8.10) (this differs from B & G by excluding 1).        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section GeneralDefinitions.

Variable gT : finGroupType.
Implicit Types V W X : {set gT}.

End GeneralDefinitions.

Section Definitions.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Types M U V W X : {set gT}.

Definition normTIset V W := forall X, X \subset V -> X != set0 -> 'N(X) = W.

Definition of_typeF M U (H := M`_\F) :=
 [/\ (*a*) [/\ H != 1, U :!=: 1 & H ><| U = M],
     (*b*) exists2 U1 : {group gT}, U1 <| U /\ abelian U1
                & {in H^#, forall x, 'C_U[x] \subset U1}
   & (*c*) exists2 U0 : {group gT}, U0 \subset U /\ exponent U0 = exponent U
                & [Frobenius H <*> U0 = H ><| U0]].

Definition of_typeI M (H := M`_\F) :=
 exists2 U : {group gT}, of_typeF M U
  & [\/ (*a*) trivIset (H^# :^: G),
        (*b*) abelian H /\ 'r(H) = 2
      | (*c*) {in \pi(H), forall p, exponent U %| p.-1}
           /\ (exists2 p, p \in \pi(H) & cyclic 'O_p^'(H))].

Definition of_typeP M U W1 (H := M`_\F) (M' := M^`(1)) (W2 := 'C_H(W1)) :=
  [/\ (*a*) [/\ cyclic W1, Hall M W1, W1 != 1 & M' ><| W1 = M],
      (*b*) [/\ nilpotent U, U \subset M', W1 \subset 'N(U) & H ><| U = M'],
      (*c*) [/\ ~~ cyclic H, M^`(2) \subset 'F(M), H * 'C_M(H) = 'F(M)
              & 'F(M) \subset M'],
      (*d*) [/\ cyclic W2, W2 != 1, W2 \subset H, W2 \subset M^`(2)
              & {in W1^#, forall x, 'C_M'[x] = W2}]
    & (*e*) let W := W1 <*> W2 in let V := W :\: (W1 :|: W2) in normTIset V W].

Definition of_typeII_IV  M U W1 :=
  [/\ of_typeP M U W1, U != 1, prime #|W1| & trivIset ('F(M)^# :^: G)].

Definition of_typeII M (H := M`_\F) (M' := M^`(1)) :=
  exists UW1 : {group gT} * {group gT}, let: (U, W1) := UW1 in
    [/\ of_typeII_IV M U W1, abelian U, ~~ ('N(U) \subset M),
        of_typeF M' U & M'`_\F = H].

Definition of_typeIII M :=
  exists UW1 : {group gT} * {group gT}, let: (U, W1) := UW1 in
    [/\ of_typeII_IV M U W1, abelian U & 'N(U) \subset M].

Definition of_typeIV M :=
  exists UW1 : {group gT} * {group gT}, let: (U, W1) := UW1 in
    [/\ of_typeII_IV M U W1, ~~ abelian U & 'N(U) \subset M].

Definition of_typeV M (H := M`_\F) :=
  exists2 W1 : {group gT}, of_typeP M 1 W1
  & [\/ (*a*) trivIset (H^# :^: G),
        (*b*) exists2 p, p \in \pi(H) & #|W1| %| p.-1 /\ cyclic 'O_p^'(H)
     |  (*c*) exists2 p, p \in \pi(H)
              & [/\ #|'O_p(H)| = (p ^ 3)%N, #|W1| %| p.+1 & cyclic 'O_p^'(H)]].

Definition FTtype_spec i M :=
  match i with
  | 1%N => of_typeI M
  | 2 => of_typeII M
  | 3 => of_typeIII M
  | 4 => of_typeIV M
  | 5 => of_typeV M
  | _ => False
  end.

Definition FTtype M :=
  if \kappa(M)^'.-group M then 1%N else
  if M`_\sigma != M^`(1) then 2 else
  if M`_\F == M`_\sigma then 5 else
  if abelian (M`_\sigma / M`_\F) then 3 else 4.

Lemma FTtype_range : forall M, 0 < FTtype M <= 5.
Proof. by rewrite /FTtype => M; do 4!case: ifP => // _. Qed.

Definition FTcore M := if 0 < FTtype M <= 2 then M`_\F else M^`(1).
Fact FTcore_is_group : forall M, group_set (FTcore M).
Proof. rewrite /FTcore => M; case: ifP => _; exact: groupP. Qed.
Canonical Structure FTcore_group M := Group (FTcore_is_group M).

Definition FTkernel1 M := (FTcore M)^#.

Definition FTkernel M :=
  \bigcup_(x \in FTkernel1 M) 'C_(M^`(FTtype M != 1%N))[x]^#.

Definition FTkernel0 M (su := \pi(M^`(FTtype M != 1%N))) :=
  FTkernel M :|: [set x \in M | ~~ (su.-elt x) && ~~ (su^'.-elt x)].

End Definitions.

Notation "M `_ \s" := (FTcore M) (at level 3, format "M `_ \s") : group_scope.
Notation "M `_ \s" := (FTcore_group M) : subgroup_scope.

Notation "''A1' ( M )" := (FTkernel1 M)
  (at level 8, format "''A1' ( M )") : group_scope.

Notation "''A' ( M )" := (FTkernel M)
  (at level 8, format "''A' ( M )") : group_scope.

Notation "''A0' ( M )" := (FTkernel0 M)
  (at level 8, format "''A0' ( M )") : group_scope.

Section Section16.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

(* This section covers the characterization of the F, P, P1 and P2 types of   *)
(* maximal subgroups summarized at the top of p. 125. in B & G.               *)
Section KappaClassification.

Variables M U K : {group gT}.
Hypotheses (maxM : M \in 'M) (complU : kappa_complement M U K).

Remark trivgFmax : (M \in 'M_'F) = (K :==: 1).
Proof. by rewrite (trivg_kappa maxM); case: complU. Qed.

Remark trivgPmax : (M \in 'M_'P) = (K :!=: 1).
Proof. by rewrite inE trivgFmax maxM andbT. Qed.

Remark FmaxP : reflect (K :==: 1 /\ U :!=: 1) (M \in 'M_'F). 
Proof.
rewrite (trivg_kappa_compl maxM complU) 2!inE.
have [_ hallK _] := complU; rewrite (trivg_kappa maxM hallK).
by apply: (iffP idP) => [-> | []].
Qed.

Remark P1maxP : reflect (K :!=: 1 /\ U :==: 1) (M \in 'M_'P1).
Proof.
rewrite (trivg_kappa_compl maxM complU) inE -trivgPmax.
by apply: (iffP idP) => [|[] //]; case/andP=> ->.
Qed.

Remark P2maxP : reflect (K :!=: 1 /\ U :!=: 1) (M \in 'M_'P2).
Proof.
rewrite (trivg_kappa_compl maxM complU) -trivgPmax.
by apply: (iffP setDP) => [] [].
Qed.

End KappaClassification.

(* This section covers the combinatorial statements of B & G, Lemma 16.1. It  *)
(* needs to appear before summary theorems A-E because we are following       *)
(* Peterfalvi in anticipating the classification in the definition of the     *)
(* kernel sets A1(M), A(M) and A0(M). The actual correspondence between the   *)
(* combinatorial classification and the mathematical description, i.e., the   *)
(* of_typeXX predicates, will be given later.                                 *)
Section FTtypeClassification.

Variable M : {group gT}.
Hypothesis maxM : M \in 'M.

Lemma kappa_witness :
  exists UK : {group gT} * {group gT}, kappa_complement M UK.1 UK.2.
Proof.
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
by have [U complU] := ex_kappa_compl maxM hallK; exists (U, K).
Qed.

(* This is B & G, Lemma 16.1(a). *)
Lemma FTtype_Fmax : (M \in 'M_'F) = (FTtype M == 1%N).
Proof.
by rewrite inE maxM /FTtype; case: (_.-group M) => //; do 3!case: ifP => // _.
Qed.

Lemma FTtype_Pmax : (M \in 'M_'P) = (FTtype M != 1%N).
Proof. by rewrite inE maxM andbT FTtype_Fmax. Qed.

(* This is B & G, Lemma 16.1(b). *)
Lemma FTtype_P2max : (M \in 'M_'P2) = (FTtype M == 2).
Proof.
have [[U K] /= complU] := kappa_witness.
rewrite (sameP (P2maxP maxM complU) andP) -(trivgFmax maxM complU) FTtype_Fmax.
have [-> // | notMtype1] := altP eqP.
have ntK: K :!=: 1 by rewrite -(trivgFmax maxM complU) FTtype_Fmax.
have [_ [//|defM' _] _ _ _] := kappa_structure maxM complU.
do [rewrite /FTtype; case: ifP => // _] in notMtype1 *.
rewrite -cardG_gt1 eqEcard Msigma_der1 //= -(sdprod_card defM') -ltnNge.
rewrite -(@ltn_pmul2l #|M`_\sigma|) ?cardG_gt0 //= muln1.
by case: leqP => // _; do 2!case: ifP=> //.
Qed.

(* This covers the P1 part of B & G, Lemma 16.1 (c) and (d). *)
Lemma FTtype_P1max : (M \in 'M_'P1) = (2 < FTtype M <= 5).
Proof.
rewrite 2!ltn_neqAle -!andbA FTtype_range andbT eq_sym -FTtype_P2max.
rewrite eq_sym -FTtype_Pmax in_setD inE.
by case: (M \in _); rewrite ?andbT ?andbF ?negbK.
Qed.

Lemma Msigma_eq_der1 : M \in 'M_'P1 -> M`_\sigma = M^`(1).
Proof.
have [[U K] /= complU] := kappa_witness.
case/(P1maxP maxM complU)=> ntK; move/eqP=> U1.
by have [_ [//|<- _] _ _ _] := kappa_structure maxM complU; rewrite U1 sdprodg1.
Qed.

Lemma def_FTcore : M`_\s = M`_\sigma.
Proof.
rewrite /FTcore -mem_iota 2!inE -FTtype_Fmax -FTtype_P2max.
have [notP1maxM |] := ifPn.
  by apply/Fcore_eq_Msigma; rewrite ?notP1type_Msigma_nil.
case/norP=> notFmaxM; rewrite inE andbC inE maxM notFmaxM negbK => P1maxM.
by rewrite Msigma_eq_der1.
Qed.

(* This is B & G, Lemma 16.1(f). *)
Lemma Fcore_eq_FTcore : reflect (M`_\F = M`_\s) (FTtype M \in pred3 1%N 2 5).
Proof.
rewrite /FTcore -mem_iota 4!inE orbA; case type12M: (_ || _); first by left.
move: type12M FTtype_P1max; rewrite /FTtype; do 2![case: ifP => // _] => _.
rewrite !(fun_if (leq^~ 5)) !(fun_if (leq 3)) !if_same /= => P1maxM.
rewrite Msigma_eq_der1 // !(fun_if (eq_op^~ 5)) if_same.
by rewrite [if _ then _ else _]andbT; exact: eqP.
Qed.

(* This is the second part of B & G, Lemma 16.1(c). *)
Lemma Fcore_neq_FTcore : (M`_\F != M`_\s) = (FTtype M \in pred2 3 4).
Proof.
have:= FTtype_range M; rewrite -mem_iota (sameP eqP Fcore_eq_FTcore).
by do 5!case/predU1P=> [-> //|].
Qed.

Lemma FTcore_eq_der1 : FTtype M > 2 -> M`_\s = M^`(1).
Proof.
move=> FTtype_gt2; rewrite def_FTcore Msigma_eq_der1 // FTtype_P1max.
by rewrite FTtype_gt2; case/andP: (FTtype_range M).
Qed.

End FTtypeClassification.

Section SingleGroupSummaries.

Variables M U K : {group gT}.
Hypotheses (maxM : M \in 'M) (complU : kappa_complement M U K).

Let Kstar := 'C_(M`_\sigma)(K).

Theorem BGsummaryA :
 [/\ (*1*) [/\ M`_\sigma <| M, \sigma(M).-Hall(M) M`_\sigma &
               \sigma(M).-Hall(G) M`_\sigma],
     (*2*) \kappa(M).-Hall(M) K /\ cyclic K,
     (*3*) [/\ U \in [complements to M`_\sigma <*> K in M],
               K \subset 'N(U),
               M`_\sigma <*> U <| M,
               U <| U <*> K
             & M`_\sigma * U * K = M],
     (*4*) {in K^#, forall k, 'C_U[k] = 1}
  & 
 [/\ (*5*) Kstar != 1 /\ {in K^#, forall k, K \x Kstar = 'C_M[k]},
     (*6*) [/\ M`_\F != 1, M`_\F \subset M`_\sigma, M`_\sigma \subset M^`(1),
               M^`(1) \proper M & nilpotent (M^`(1) / M`_\F)],
     (*7*) [/\ M^`(2) \subset 'F(M), M`_\F * 'C_M(M`_\F) = 'F(M)
             & K :!=: 1 -> 'F(M) \subset M^`(1)]
   & (*8*) M`_\F != M`_\sigma ->
           [/\ U :=: 1, trivIset ('F(M)^# :^: G) & prime #|K| ]]].
Proof.
have [hallU hallK _] := complU; split.
- by rewrite pcore_normal Msigma_Hall // Msigma_Hall_G.
- by have [[]] := kappa_structure maxM complU.
- have [_ defM _ _ _] := kappa_compl_context maxM complU.
  have [[_ UK _ defUK]] := sdprodP defM; rewrite defUK.
  have [nsKUK _ mulUK nUK _] := sdprod_context defUK.
  rewrite -mulUK mulG_subG mulgA => mulMsUK; case/andP=> nMsU nMsK _.
  rewrite (norm_joinEr nUK) mulUK; split=> //.
    rewrite inE coprime_TIg /= norm_joinEr //=.
      by rewrite -mulgA (normC nUK) mulgA mulMsUK !eqxx.
    rewrite (pnat_coprime _ (pHall_pgroup hallU)) // -pgroupE pgroupM.
    rewrite (sub_pgroup _ (pHall_pgroup hallK)) => [|p k_p]; last first.
      by apply/orP; right.
    by rewrite (sub_pgroup _ (pcore_pgroup _ _)) => // p s_p; apply/orP; left.
  have{defM} [[defM _ _] _ _ _ _] := kappa_structure maxM complU.
  have [[MsU _ defMsU] _ _ _ _] := sdprodP defM; rewrite defMsU in defM.
  have [_ mulMsU _ _] := sdprodP defMsU.
  by rewrite norm_joinEr // mulMsU; case/sdprod_context: defM.
- by have [] := kappa_compl_context maxM complU.
split.
- have [K1 | ntK] := eqsVneq K 1.
    rewrite /Kstar K1 cent1T setIT Msigma_neq1 // setDv.
    by split=> // k; rewrite inE.
  have PmaxM: M \in 'M_'P by rewrite inE -(trivg_kappa maxM hallK) ntK.
  have [_ [defNK _] [-> _] _ _] := Ptype_structure PmaxM hallK.
  have [_ _ cKKs tiKKs] := dprodP defNK; rewrite dprodEY //; split=> // k Kk.
  by have [_ _ [_ _ _ [_ _ -> // _ _] _]] := Ptype_embedding PmaxM hallK.
- have [_ _ [_ ->] _] := Fitting_structure maxM.
  by have [[]] := Fcore_structure maxM.
- have [_ [-> defF _] _ sFM'] := Fitting_structure maxM.
  have [_ -> _] := cprodP defF; split=> // ntK.
  by rewrite sFM' // inE -(trivg_kappa maxM hallK) ntK.
move=> not_nilMs; pose q := #|Kstar|.
have solMs: solvable M`_\sigma := solvableS (pcore_sub _ _) (mmax_sol maxM).
have [D hallD] := Hall_exists q^' solMs.
have [_] := Fcore_structure maxM; case/(_ K D)=> //.
case=> P1maxM _ _ [-> _ _ _] _ _ _; split=> //.
  by apply/eqP; rewrite (trivg_kappa_compl maxM complU).
by apply: contraR not_nilMs; case/nonTI_Fitting_facts=> // _ -> _.
Qed.

(* This is a variant of B & G, Lemma 16.1(e) that better fits the Peterfalvi  *)
(* definitions.                                                               *)
Lemma sdprod_FTder : M`_\sigma ><| U = M^`(FTtype M != 1%N).
Proof.
rewrite -FTtype_Fmax // (trivgFmax maxM complU).
have [[defM _ _] defM' _ _ _] := kappa_structure maxM complU.
by case: (altP eqP) defM' defM => [-> _ | _ [] //]; rewrite sdprodg1.
Qed.

Theorem BGsummaryB :
 [/\ (*1*) forall p S, p.-Sylow(U) S -> abelian S /\ 'r(S) <= 2,
     (*2*) abelian <<U :&: 'A(M)>>,
     (*3*) exists U0 : {group gT},
           [/\ U0 \subset U, exponent U0 = exponent U & [disjoint U0 & 'A(M)]]
  &  (*4*) (forall X, X \subset U -> X :!=: 1 -> 'C_(M`_\sigma)(X) != 1 ->
            'M('C(X)) = [set M])
  /\ (*5*) let B := 'A(M) :\: 'A1(M) in trivIset (B :^: G) /\ M \subset 'N(B)].
Proof.
split.
- move=> p S sylS; have [hallU _ _] := complU; have [sUM sk'U _] := and3P hallU.
  have [-> | ntS] := eqsVneq S 1; first by rewrite abelian1 rank1.
  have sk'p: p \in \sigma_kappa(M)^'.
    by rewrite (pnatPpi sk'U) // -p_rank_gt0 -(rank_Sylow sylS) rank_gt0.
  have{sylS} sylS := subHall_Sylow hallU sk'p sylS.
  have [[sSM pS _] [/= s'p _]] := (and3P sylS, norP sk'p).
  rewrite (sigma'_nil_abelian maxM) ?(pi_pgroup pS) ?(pgroup_nil pS) //.
  rewrite (rank_Sylow sylS) leqNgt (contra _ s'p) //; exact: alpha_sub_sigma.
- have [_ _ _ cUA_UA _] := kappa_structure maxM complU.
  apply: abelianS cUA_UA; rewrite genS // -big_distrr ?setIS -?def_FTcore //=.
  by apply/bigcupsP=> x A1x; rewrite (bigcup_max x) // setDE setIAC subsetIr.
- have [-> | ntU] := eqsVneq U 1.
    exists 1%G; split; rewrite // disjoint_sym disjoints_subset.
    by apply/bigcupsP=> x _; rewrite setDE subsetIr.
  have [_ _ _ _ [// | U0 [sU0U expU0 frobU0]]] := kappa_structure maxM complU.
  exists U0; split; rewrite // -setI_eq0 -subset0 big_distrr /=.
  rewrite /'A1(M) def_FTcore //; apply/bigcupsP=> x A1x.
  rewrite setDE setIA -setDE subDset setU0 setICA.
  by rewrite (Frobenius_reg_compl frobU0) ?subsetIr.
set part4 := forall X, _; have part4holds: part4.
  move=> X sXU ntX nregX.
  by have [_ _] := kappa_structure maxM complU; case/(_ X).
have [[nsMsM _ _] _ [_ _ nsMsUM _ _] _ _] := BGsummaryA.
have{nsMsM nsMsUM}[[_ nMsM] [_ nMsUM]] := (andP nsMsM, andP nsMsUM).
split=> // B; have nBM: M \subset 'N(B).
  have nA1M: M \subset 'N('A1(M)) by rewrite normD1 def_FTcore.
  rewrite normsD //; apply/subsetP=> y My; rewrite inE sub_conjg.
  apply/bigcupsP=> x A1x; rewrite -sub_conjg conjDg conjIg -normJ !conjg_set1.
  rewrite conj1g (normsP (der_norm _ M)) // (bigcup_max (x ^ y)) ?memJ_norm //.
  exact: subsetP nA1M y My.
split=> //; apply/trivIsetP=> _ _ /imsetP[a1 _ ->] /imsetP[a2 _ ->].
rewrite -setI_eq0 -(conjsgKV a2 (_ :^ a1)) -(conjsgM _ a1) -conjIg.
rewrite (inj_eq (act_inj _ _)) (sameP eqP normP).
move: {a1}(a1 * a2^-1) => a /(contra (subsetP nBM a)) notMa.
have uniqB: forall y (u := y.`_\sigma(M)^'), y \in B -> 'M('C[u]) = [set M].
  move=> y u; case/setDP; case/bigcupP=> x; case/setD1P=> ntx.
  rewrite def_FTcore // => Ms_x; case/setD1P=> nty; set M' := M^`(_).
  case/setIP=> M'y cxy; rewrite 2!inE (negPf nty) def_FTcore //= => notMs_y.
  have [nsM'M _ _ _ _] := sdprod_context sdprod_FTder.
  have [[sMsM' nMsM'] sM'M]:= (andP nsM'M, der_sub _ M : M' \subset M).
  have hallMs := pHall_subl sMsM' sM'M (Msigma_Hall maxM).
  have hallU: \sigma(M)^'.-Hall(M') U.
    by rewrite -(compl_pHall _ hallMs) sdprod_compl ?sdprod_FTder.
  have suM': <[u]> \subset M' by rewrite cycle_subG groupX.
  have solM': solvable M' := solvableS sM'M (mmax_sol maxM).
  have [z M'z suzU] := Hall_Jsub solM' hallU suM' (p_elt_constt _ _).
  have Mz': z^-1 \in M by rewrite groupV (subsetP sM'M).
  rewrite -(conjgK z u) -(group_inj (conjGid Mz')) -cent_cycle.
  rewrite !cycleJ centJ; apply: def_uniq_mmaxJ (part4holds _ suzU _ _).
    rewrite /= -cycleJ cycle_eq1 -consttJ; apply: contraNneq notMs_y.
    move/constt1P; rewrite p_eltNK p_eltJ => sMy.
    by rewrite (mem_normal_Hall hallMs).
  rewrite -(normsP nMsM' z M'z) centJ -conjIg (isog_eq1 (conj_isog _ _)).
  by apply/trivgPn; exists x; rewrite //= inE Ms_x cent_cycle cent1C groupX.
apply: contraR notMa => /set0Pn[_ /imsetP[x /setIP[Bax /uniqB defM] _]].
move: Bax; rewrite mem_conjg => /uniqB/(def_uniq_mmaxJ a); rewrite consttJ.
rewrite -normJ conjg_set1 conjgKV {}defM => /set1_inj=> defM.
by rewrite -(norm_mmax maxM) inE {2}defM.
Qed.

Let Z := K <*> Kstar.
Let Zhat := Z :\: (K :|: Kstar).

(*    We strengthened the uniqueness condition in part (4) to                 *)
(* 'M_\sigma(K) = [set Mstar].                                                *)
Theorem BGsummaryC : K :!=: 1 ->
 [/\
  [/\ (*1*) abelian U /\ ~~ ('N(U) \subset M),
      (*2*) [/\ cyclic Kstar, Kstar != 1, Kstar \subset M`_\F & ~~ cyclic M`_\F]
    & (*3*) M`_\sigma ><| U = M^`(1) /\ Kstar \subset M^`(2)],
  exists Mstar,
  [/\ (*4*) [/\ Mstar \in 'M_'P, 'C_(Mstar`_\sigma)(Kstar) = K,
                \kappa(Mstar).-Hall(Mstar) Kstar
              & 'M_\sigma(K) = [set Mstar]], (* uniqueness *)
      (*5*) {in 'E^1(Kstar), forall X, 'M('C(X)) = [set M]}
         /\ {in 'E^1(K), forall Y, 'M('C(Y)) = [set Mstar]},
      (*6*) [/\ M :&: Mstar = Z, K \x Kstar = Z & cyclic Z]
    & (*7*) (M \in 'M_'P2 \/ Mstar \in 'M_'P2)
         /\ {in 'M_'P, forall H, gval H \in M :^: G :|: Mstar :^: G}]
& [/\ (*8*) trivIset (Zhat :^: G) /\ 'N(Zhat) = Z,
      (*9*) let B := 'A0(M) :\: 'A(M) in
            [/\ B = class_support Zhat M, trivIset (B :^: G) & 'N(B) = M],
     (*10*) U :!=: 1 ->
            [/\ prime #|K|, trivIset ('F(M)^# :^: G) & M`_\sigma \subset 'F(M)]
   & (*11*) U :==: 1 -> prime #|Kstar| ]].
Proof.
move=> ntK; have [_ hallK _] := complU.
have PmaxM: M \in 'M_'P by rewrite inE -(trivg_kappa maxM hallK) ntK.
split.
- have [_ [//|-> ->] _ _ _] := kappa_structure maxM complU.
  have [-> -> -> -> ->] := Ptype_cyclics PmaxM hallK; do 2!split=> //.
  have [L maxCK_L] := mmax_exists (mFT_cent_proper ntK).
  have [-> | ntU] := eqsVneq U 1.
    by rewrite norm1 proper_subn // mmax_proper.
  have P2maxM: M \in 'M_'P2 by rewrite inE -(trivg_kappa_compl maxM complU) ntU.
  have [r _ rU] := rank_witness U; have [R sylR] := Sylow_exists r U.
  have ntR: R :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylR) -rU rank_gt0.
  have ltRG: R \proper G := mFT_pgroup_proper (pHall_pgroup sylR).
  have [H maxNR_H] := mmax_exists (mFT_norm_proper ntR ltRG).
  apply: contra (subset_trans (subsetIr H _)) _.
  by have [_ _ _ [->]] := P2type_signalizer P2maxM complU maxCK_L sylR maxNR_H.
- have [L [PmaxL _] [uniqL []]] := Ptype_embedding PmaxM hallK.
  rewrite -/Kstar -/Z -/Zhat => hallKstar _ [defK _] [cycZ defML _ _ _].
  case=> [[tiZhat defNZhat _ _] P2_MorL Pmax_conjMorL _]; exists L.
  have uniqMSK: 'M_\sigma(K) = [set L].
    have sKLs: K \subset L`_\sigma by rewrite -defK subsetIl.
    have [X E1X]: exists X, X \in 'E^1(K) by apply/rank_geP; rewrite rank_gt0.
    have sXK: X \subset K by case/nElemP: E1X => ?; case/pnElemP.
    have [maxL sCXL] := mem_uniq_mmax (uniqL X E1X).
    have [x defKx] := cyclicP (cyclicS (joing_subl _ _) cycZ).
    have SMxL: L \in 'M_\sigma[x] by rewrite -defKx inE maxL.
    have ell1x: \ell_\sigma(x) == 1%N.
      by rewrite (Msigma_ell1 maxL) // !inE -cycle_eq1 -cycle_subG -defKx ntK.
    apply/eqP; rewrite eq_sym eqEcard defKx sub1set SMxL cards1 leqNgt.
    apply/negP=> ntSMx; have [_ [//|_ ntR _ _]] := FT_signalizer_context ell1x.
    case/(_ L)=> //; case/sdprodP=> _ _ _ tiRL; case/negP: ntR.
    rewrite -subG1 -tiRL subsetIidl -setIA setICA setISS ?pcore_sub //.
    by rewrite subsetIidr /= -cent_cycle -defKx (subset_trans (centS sXK) sCXL).
  have [_ [defNK _] [_ uniqM] _ _] := Ptype_structure PmaxM hallK.
  do 2!split=> //; last by case: P2_MorL => [] [-> _]; [left | right].
  by have [_ _ cKKs tiKKs] := dprodP defNK; rewrite dprodEY.
split; last 1 first.
- rewrite (trivg_kappa_compl maxM complU) => P1maxM.
  have [L _ [_ _ _ _ [_ [] [] //]]] := Ptype_embedding PmaxM hallK.
  by rewrite inE P1maxM.
- by have [L _ [_ _ _ _ [[]]]] := Ptype_embedding PmaxM hallK.
- have [L _ [_ _ _]] := Ptype_embedding PmaxM hallK.
  case=> cycZ defML defCK defCKs defCZhat [[tiZhat NZhat _] _ _ _ defM].
  have sZM: Z \subset M by rewrite -[Z]defML subsetIl.
  have ->: 'A0(M) :\: 'A(M) = class_support Zhat M.
    rewrite /'A0(M); set M' := M^`(_); set su := \pi(M').
    have defM': M' = M^`(1) by rewrite /M' -FTtype_Pmax ?PmaxM.
    have{hallK} hallM': su.-Hall(M) M'.
      by rewrite Hall_pi //= -/M' defM' (sdprod_Hall defM) (pHall_Hall hallK).
    have{hallM'} hallK: su^'.-Hall(M) K.
      by rewrite -(compl_pHall _ hallM') /= -/M' defM' sdprod_compl.
    have su'K: su^'.-group K := pHall_pgroup hallK.
    have suKs: su.-group Kstar.
      by rewrite (pgroupS _ (pgroup_pi _)) ///= -/M' defM' subIset ?Msigma_der1.
    apply/setP=> x; rewrite !inE; apply/andP/imset2P=> [[]| [y a]]; last first.
      case/setDP=> Zy; rewrite inE; case/norP=> not_Ky notKs_y Ma ->.
      have My := subsetP sZM y Zy; have Mya := groupJ My Ma.
      have [not_suy not_su'y]: ~~ su.-elt y /\ ~~ su^'.-elt y.
        have defZ: K * Kstar = Z by rewrite -cent_joinEr ?subsetIr.
        have [hallK_Z hallKs] := coprime_mulGp_Hall defZ su'K suKs.
        have ns_Z := sub_abelian_normal _ (cyclic_abelian cycZ).
        rewrite -(mem_normal_Hall hallKs) -?ns_Z ?joing_subr // notKs_y.
        by rewrite -(mem_normal_Hall hallK_Z) -?ns_Z ?joing_subl.
      rewrite Mya !p_eltJ not_suy not_su'y orbT; split=> //.
      apply: contra not_suy; case/bigcupP=> x1 _; case/setD1P=> _; case/setIP.
      by move/(mem_p_elt (pgroup_pi _)); rewrite p_eltJ.
    move/negPf->; case/and3P=> Mx not_sux not_su'x; set y := x.`_su^'.
    have syM: <[y]> \subset M by rewrite cycle_subG groupX.
    have [a Ma Kya] := Hall_Jsub (mmax_sol maxM) hallK syM (p_elt_constt _ _).
    have{Kya} K1ya: y ^ a \in K^#.
      rewrite !inE -cycle_subG cycleJ Kya andbT -consttJ.
      by apply: contraNneq not_sux; move/constt1P; rewrite p_eltNK p_eltJ.
    exists (x ^ a) a^-1; rewrite ?groupV ?conjgK // 2!inE andbC negb_or.
    rewrite -[Z](defCK _ K1ya) inE groupJ // cent1C -consttJ groupX ?cent1id //.
    by rewrite (contra (mem_p_elt su'K)) ?(contra (mem_p_elt suKs)) ?p_eltJ.
  split=> //; last first.
    apply: mmax_max (class_support_normG _ _) => //.
    apply: sub_proper_trans (norm_gen _) (mFT_norm_proper _ _).
      have: Zhat != set0.
        apply: contraNneq (proper_subn (sub_mmax_proper maxM sZM)).
        by rewrite /= -NZhat -/Zhat => ->; rewrite -(setDv 1) normD1 norms1.
      case/set0Pn => z Zhat_z; apply/trivgPn; exists (z ^ 1).
        by rewrite mem_gen ?mem_imset2.
      case/setDP: Zhat_z => _; rewrite inE conjg1; case/norP=> notKz _.
      exact: (group1_contra notKz).
    rewrite (sub_mmax_proper maxM) // gen_subG class_support_subG //.
    by rewrite subDset setUC subsetU ?sZM.
  apply/trivIsetP=> _ _ /imsetP[x _ ->] /imsetP[y _ ->].
  rewrite -setI_eq0 -(mulgKV y x) conjsgM -conjIg; move: {x}(x * _) => x.
  have [Mx | notMx _] := boolP (x \in M).
    by rewrite (normsP (class_support_normG _ _) x Mx) eqxx.
  rewrite -subset0 sub_conjg {2}class_supportEr big_distrr /=.
  apply/bigcupsP=> a Ma; rewrite -(mulgKV x a) conjsgM -conjIg sub_conjg.
  rewrite class_supportEr big_distrl /=; apply/bigcupsP=> b Mb.
  rewrite ![set0 :^ _]imset0 subset0 setI_eq0.
  have inZHG: Zhat :^ _ \in Zhat :^: G by move=> c; rewrite mem_imset ?inE.
  apply: (trivIsetP tiZhat) => //; rewrite (canF_eq (conjsgK _)). 
  rewrite -conjsgM eq_sym (sameP eqP normP) NZhat -/Z.
  by rewrite (contra (subsetP sZM _)) // -mulgA -invMg !(groupMl, groupV) //.
rewrite (trivg_kappa_compl maxM complU) => notP1maxM.
have P2maxM: M \in 'M_'P2 by exact/setDP.
split; first by have [_ _ _ _ []] := Ptype_structure PmaxM hallK.
  apply: contraR notP1maxM; case/nonTI_Fitting_facts=> //.
  by case/setUP=> //; case/idPn; case/setDP: PmaxM.
have [<- | neqMF_Ms] := eqVneq M`_\F M`_\sigma; first exact: Fcore_sub_Fitting.
have solMs: solvable M`_\sigma := solvableS (pcore_sub _ _) (mmax_sol maxM).
have [D hallD] := Hall_exists #|Kstar|^' solMs.
by case: (Fcore_structure maxM) notP1maxM => _; case/(_ K D)=> // [[->]].
Qed.

End SingleGroupSummaries.

Theorem BGsummaryD : forall M, M \in 'M ->
 [/\ (*1*) {in M`_\sigma &, forall x y, y \in x ^: G -> y \in x ^: M},
     (*2*) forall g (Ms := M`_\sigma), g \notin M ->
           Ms:&: M :^ g = Ms :&: Ms :^ g /\ cyclic (Ms :&: M :^ g),
     (*3*) {in M`_\sigma^#, forall x,
            [/\ Hall 'C[x] 'C_M[x], 'R[x] ><| 'C_M[x] = 'C[x]
              & let MGx := [set Mg \in M :^: G | x \in Mg] in
                [transitive 'R[x], on MGx | 'Js] /\ #|'R[x]| = #|MGx| ]}
  & (*4*) {in M`_\sigma^#, forall x (N := 'N[x]), ~~ ('C[x] \subset M) ->
           [/\ 'M('C[x]) = [set N] /\ N`_\F = N`_\sigma,
               x \in 'A(N) :\: 'A1(N) /\ N \in 'M_'F :|: 'M_'P2,
               \sigma(N)^'.-Hall(N) (M :&: N)
             & N \in 'M_'P2 ->
               [/\ M \in 'M_'F,
                   exists2 E, [Frobenius M = M`_\sigma ><| gval E] & cyclic E
                 & ~~ trivIset ((M`_\F)^# :^: G)]]}].
Proof.
move=> M maxM; have [[U K] /= complU] := kappa_witness maxM.
have defSM: {in M`_\sigma^#, forall x,
  [set Mg \in M :^: G | x \in Mg] = val @: 'M_\sigma[x]}.
- move=> x; case/setD1P=> ntx Ms_x.
  have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
  apply/setP=> /= Mg; apply/setIdP/imsetP=> [[] | [H]].
    case/imsetP=> g _ -> Mg_x; exists (M :^ g)%G => //=.
    rewrite inE cycle_subG (mem_Hall_pcore (Msigma_Hall _)) ?mmaxJ // maxM.
    by rewrite (eq_p_elt _ (sigmaJ _ _)) (mem_p_elt (pcore_pgroup _ M)).
  case/setIdP=> maxH; rewrite cycle_subG => Hs_x ->.
  split; last exact: subsetP (pcore_sub _ _) x Hs_x.
  pose p := pdiv #[x]; have pixp: p \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
  apply/idPn; move/(sigma_partition maxM maxH); move/(_ p).
  rewrite inE /= (pnatPpi (mem_p_elt (pcore_pgroup _ _) Ms_x)) //.
  by rewrite (pnatPpi (mem_p_elt (pcore_pgroup _ _) Hs_x)).
split.
- have hallMs := pHall_subl (subxx _) (subsetT _) (Msigma_Hall_G maxM).
  move=> x y Ms_x Ms_y /=; case/imsetP=> a _ def_y; rewrite def_y in Ms_y *.
  have [b] := sigma_Hall_tame maxM hallMs Ms_x Ms_y.
  by case/setIP=> Mb _ ->; exact: mem_imset.
- move=> g notMg; split.
    apply/eqP; rewrite eqEsubset andbC setIS ?conjSg ?pcore_sub //=.
    rewrite subsetI subsetIl -MsigmaJ.
    rewrite (sub_Hall_pcore (Msigma_Hall _)) ?mmaxJ ?subsetIr //.
    rewrite (eq_pgroup _ (sigmaJ _ _)).
    exact: pgroupS (subsetIl _ _) (pcore_pgroup _ _).
  have [E hallE] := ex_sigma_compl maxM.
  by have [_ _] := sigma_compl_embedding maxM hallE; case/(_ g).
- move=> x Ms1x /=.
  have [[ntx Ms_x] ell1x] := (setD1P Ms1x, Msigma_ell1 maxM Ms1x).
  have [[trR oR nsRC hallR] defC] := FT_signalizer_context ell1x.
  have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
  suffices defCx: 'R[x] ><| 'C_M[x] = 'C[x].
    split=> //; first by rewrite -(sdprod_Hall defCx).
    rewrite defSM //; split; last by rewrite (card_imset _ val_inj).
    apply/imsetP; exists (gval M); first exact: mem_imset.
    by rewrite -(atransP trR _ SMxM) -imset_comp.
  have [| SMgt1] := leqP #|'M_\sigma[x]| 1.
    rewrite leq_eqVlt {2}(cardD1 M) SMxM orbF => eqSMxM.
    have ->: 'R[x] = 1 by apply/eqP; rewrite trivg_card1 oR.
    by rewrite sdprod1g (setIidPr _) ?cent1_sub_uniq_sigma_mmax.
  have [uniqN _ _ _ defCx] := defC SMgt1.
  have{defCx} [[defCx _ _ _] [_ sCxN]] := (defCx M SMxM, mem_uniq_mmax uniqN).
  by rewrite -setIA (setIidPr sCxN) in defCx.
move=> x Ms1x /= not_sCM.
have [[ntx Ms_x] ell1x] := (setD1P Ms1x, Msigma_ell1 maxM Ms1x).
have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
have SMgt1: #|'M_\sigma[x]| > 1.
  apply: contraR not_sCM; rewrite -leqNgt leq_eqVlt {2}(cardD1 M) SMxM orbF.
  by move/cent1_sub_uniq_sigma_mmax->.
have [_ [//|uniqN ntR t2Nx notP1maxN]] := FT_signalizer_context ell1x.
have [maxN sCxN] := mem_uniq_mmax uniqN.
case/(_ M SMxM)=> _ st2NsM _ ->; split=> //.
- by rewrite (Fcore_eq_Msigma maxN (notP1type_Msigma_nil _)) // -in_setU.
- split=> //; apply/setDP; split.
    have [y Ry nty] := trivgPn _ ntR; have [Nsy cxy] := setIP Ry.
    apply/bigcupP; exists y; first by rewrite 2!inE def_FTcore ?nty.
    rewrite 3!inE ntx cent1C cxy -FTtype_Pmax //= andbT.
    have Nx: x \in 'N[x] by rewrite (subsetP sCxN) ?cent1id.
    case PmaxN: ('N[x] \in 'M_'P) => //.
    have [KN hallKN] := Hall_exists \kappa('N[x]) (mmax_sol maxN).
    have [_ _ [_ _ _ _ [_ _ _ defN]]] := Ptype_embedding PmaxN hallKN.
    have hallN': \kappa('N[x])^'.-Hall('N[x]) 'N[x]^`(1).
      exact/(sdprod_normal_pHallP (der_normal 1 _) hallKN).
    rewrite (mem_normal_Hall hallN') ?der_normal // (sub_p_elt _ t2Nx) // => p.
    by case/andP=> _; apply: contraL; move/rank_kappa->.
  rewrite 2!inE ntx def_FTcore //=; apply: contra ntx => Ns_x.
  rewrite -(constt_p_elt (mem_p_elt (pcore_pgroup _ _) Ns_x)).
  by rewrite (constt1P (sub_p_elt _ t2Nx)) // => p; case/andP.
move=> P2maxN; have [PmaxN _] := setDP P2maxN; have [_ notFmaxN] := setDP PmaxN.
have [FmaxM _ [E _]] := nonFtype_signalizer_base maxM Ms1x not_sCM notFmaxN.
case=> cycE frobM; split=> //; first by exists E.
move: SMgt1; rewrite (cardsD1 M) SMxM ltnS lt0n; case/pred0Pn=> /= My.
case/setD1P=> neqMyM; move/(mem_imset val); rewrite -defSM //=.
case/setIdP; case/imsetP=> y _ defMy My_x.
rewrite (Fcore_eq_Msigma maxM (notP1type_Msigma_nil _)) ?FmaxM //.
apply/TIconjP; case/(_ y 1 (in_setT y) (in_setT 1)).
  rewrite invg1 mulg1 setTI.
  rewrite (mmax_normal maxM (pcore_normal _ _)) ?Msigma_neq1 // => M_y.
  by case/negP: neqMyM; rewrite -val_eqE /= defMy conjGid.
apply/eqP; apply/trivgPn; exists x; rewrite //= conjsg1 inE Ms_x andbT.
rewrite -MsigmaJ (mem_Hall_pcore (Msigma_Hall _)) ?mmaxJ /= -?defMy //.
by rewrite defMy (eq_p_elt _ (sigmaJ _ _)) (mem_p_elt (pcore_pgroup _ _) Ms_x).
Qed.

Theorem BGsummaryE :
  [/\ (*1*) forall M, M \in 'M -> 
            #|class_support M^~~ G| = (#|M`_\sigma|.-1 * #|G : M|)%N,
      (*2*) {in \pi(G), forall p,
             exists2 M : {group gT}, M \in 'M & p \in \sigma(M)}
         /\ {in 'M &, forall M H,
             gval H \notin M :^: G -> [predI \sigma(M) & \sigma(H)] =i pred0}
    & (*3*) let PG := [set class_support (gval M)^~~ G | M <- 'M] in
            [/\ partition PG (cover PG),
                'M_'P = set0 :> {set {group gT}} -> cover PG = G^#
              & forall M K, M \in 'M_'P -> \kappa(M).-Hall(M) K ->
                let Kstar := 'C_(M`_\sigma)(K) in
                let Zhat := (K <*> Kstar) :\: (K :|: Kstar) in
                partition [set class_support Zhat G; cover PG] G^#]].
Proof.
split; first exact: card_class_support_sigma.
  split=> [p|]; first by case/sigma_mmax_exists=> M; exists M.
  exact: sigma_partition.
move=> PG; have [noPmax | ntPmax] := eqVneq 'M_'P (set0 : {set {group gT}}).
  rewrite noPmax; move/eqP: noPmax => noPmax.
  have [partPG _] := mFT_partition gT.
  have [defG1 _ _] := and3P (partPG noPmax); rewrite (eqP defG1) partPG //.
  by split=> // M K; rewrite inE.
have [_ partZPG] := mFT_partition gT.
have partPG: partition PG (cover PG).
  have [M PmaxM] := set0Pn _ ntPmax; have [maxM _] := setDP PmaxM.
  have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
  have{partZPG} [partZPG _] := partZPG M K PmaxM hallK.
  case/and3P: partZPG => _ tiPG; rewrite inE; case/norP=> _ notPGset0.
  apply/and3P; split=> //; apply/trivIsetP.
  by apply: sub_in2 (trivIsetP tiPG) => C; exact: setU1r.
split=> // [noPmax|M K PmaxM hallK]; first by case/eqP: ntPmax.
have [/=] := partZPG M K PmaxM hallK; rewrite -/PG; set Z := class_support _ G.
case/and3P; move/eqP=> defG1 tiZPG; rewrite 2!inE; case/norP=> nzZ _ notPGZ.
have [_ tiPG nzPG] := and3P partPG; have [maxM _] := setDP PmaxM.
rewrite /cover big_setU1 //= -/(cover PG) in defG1.
rewrite /trivIset /cover !big_setU1 //= (eqnP tiPG) -/(cover PG) in tiZPG.
have tiZ_PG: Z :&: cover PG = set0.
  by apply/eqP; rewrite setI_eq0 -leq_card_setU eq_sym.
have notUPGZ: Z \notin [set cover PG].
  by rewrite inE; apply: contraNneq nzZ => defZ; rewrite -tiZ_PG -defZ setIid.
rewrite /partition /trivIset  /(cover _) !big_setU1 // !big_set1 /= -defG1.
rewrite eqxx tiZPG !inE negb_or nzZ /= eq_sym; apply: contraNneq nzPG => PG0.
apply/imsetP; exists M => //; apply/eqP; rewrite eq_sym -subset0 -PG0.
by rewrite (bigcup_max (class_support M^~~ G)) //; exact: mem_imset.
Qed.

(* This should go in PFsection8. *)
Lemma of_typeP_sol : forall M U W1, of_typeP M U W1 -> solvable M.
Proof.
move=> M U K [_ [nilU _ _ defM'] _ _ _].
have [nsHM' _ mulHU _ _] := sdprod_context defM'.
rewrite (series_sol (der_normal 1 M)) (abelian_sol (der_abelian 0 M)) andbT.
rewrite (series_sol nsHM') (nilpotent_sol (Fcore_nil M)).
by rewrite -mulHU quotientMidl quotient_sol ?(nilpotent_sol nilU).
Qed.

(* This should also go in PFsection8. *)
Lemma FTtypePF_exclusion : forall M U1 U W1,
  ~ (of_typeF M U1 /\ of_typeP M U W1).
Proof.
move=> M U1 U W1 [[[ntH ntU1 defM1] _ [U0 [sU01 expU0] frobU0]] typeP_M].
have [[cycW1 hallW1 ntW1 defM] [_ _ _ defM'] _ [_]] := typeP_M; case/negP.
pose p := pdiv #|W1|; set H := M`_\F in defM' frobU0 *.
have piW1p: p \in \pi(W1) by rewrite pi_pdiv cardG_gt1.
have piU0p: p \in \pi(U0).
  rewrite -pi_of_exponent expU0 pi_of_exponent (pi_of_dvd _ _ piW1p) //=.
  rewrite -(@dvdn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defM1).
  rewrite -(sdprod_card defM) dvdn_pmul2r ?cardSg //.
  by case/sdprodP: defM' => _ <- _ _; exact: mulG_subl.
have [|X EpX]:= @p_rank_geP _ p 1 U0 _; first by rewrite p_rank_gt0.
have [ntX [sXU0 abelX _]] := (nt_pnElem EpX isT, pnElemP EpX).
have piW1_X: \pi(W1).-group X by apply: pi_pgroup piW1p; case/andP: abelX.
have sXM: X \subset M.
  apply: subset_trans (subset_trans sXU0 sU01) _.
  by case/sdprodP: defM1 => _ <- _ _; exact: mulG_subr.
have nHM: M \subset 'N(H) by exact: gFnorm.
have [regU0 solM] := (Frobenius_reg_ker frobU0, of_typeP_sol typeP_M).
have [a Ma sXaW1] := Hall_Jsub solM (Hall_pi hallW1) sXM piW1_X.
rewrite -subG1 -(conjs1g a) -(cent_semiregular regU0 sXU0 ntX) conjIg -centJ.
by rewrite (normsP nHM) ?setIS ?centS.
Qed.

Let typePfacts: forall M U W1 (H := M`_\F) (Ms := M`_\sigma),
     M \in 'M -> of_typeP M U W1 ->
  [/\ M \in 'M_'P, \kappa(M).-Hall(M) W1,
     (M \in 'M_'P1) = (U :==: 1) || ('N(U) \subset M)
    & Ms = M^`(1) -> (H == Ms) = (U :==: 1) /\ abelian (Ms / H) = abelian U].
Proof.
move=> M U K H Ms maxM; have [[_ sHMs sMsM' _] _] := Fcore_structure maxM.
move=> [[cycK hallK ntK defM] [nilU sUM' nUK defM'] _ [_ ntKs _ _ _] _].
have [_ sKM mulM'K _ tiM'K] := sdprod_context defM.
have{hallK} kK: \kappa(M).-group K.
  apply: sub_pgroup (pgroup_pi K) => p piKp; unlock kappa.
  rewrite 4!inE -!andb_orr orNb andbT -andbA.
  have [X EpX]: exists X, X \in 'E_p^1(K).
    by apply/p_rank_geP; rewrite p_rank_gt0.
  have [sXK abelX dimX] := pnElemP EpX; have [pX _] := andP abelX.
  have sXM := subset_trans sXK sKM.
  have ->: p \in \sigma(M)^'.
    apply: contra (nt_pnElem EpX isT) => sp.
    rewrite -subG1 -tiM'K subsetI (subset_trans _ sMsM') //.
    by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup pX).
  have ->: 'r_p(M) == 1%N.
    rewrite -(p_rank_Hall (Hall_pi hallK)) // eqn_leq p_rank_gt0 piKp andbT.
    apply: leq_trans (p_rank_le_rank p K) _.
    by rewrite -abelian_rank1_cyclic ?cyclic_abelian.
  apply/existsP; exists X; rewrite 2!inE sXM abelX dimX /=.
  by rewrite (subG1_contra _ ntKs) // setISS ?centS.
have PmaxM : M \in 'M_'P.
  apply/PtypeP; split=> //; exists (pdiv #|K|).
  by rewrite (pnatPpi kK) // pi_pdiv cardG_gt1.
have hallK: \kappa(M).-Hall(M) K.
  rewrite pHallE sKM -(eqn_pmul2l (cardG_gt0 M^`(1))) (sdprod_card defM).
  have [K1 hallK1] := Hall_exists \kappa(M) (mmax_sol maxM).
  have [_ _ [_ _ _ _ [_ _ _ defM1]]] := Ptype_embedding PmaxM hallK1.
  by rewrite -(card_Hall hallK1) /= (sdprod_card defM1).
split=> // [|->]; last first.
  rewrite trivg_card_le1 -(@leq_pmul2l #|H|) ?cardG_gt0 // muln1.
  split; first by rewrite (sdprod_card defM') eqEcard (subset_trans sHMs).
  have [_ mulHU nHU tiHU] := sdprodP defM'.
  by rewrite -mulHU quotientMidl (isog_abelian (quotient_isog nHU tiHU)).
have [U1 | /= ntU] := altP eqP.
  rewrite inE PmaxM -{2}mulM'K /= -defM' U1 sdprodg1 pgroupM.
  have sH: \sigma(M).-group H := pgroupS sHMs (pcore_pgroup _ _).
  rewrite (sub_pgroup _ sH) => [|p sMp]; last by rewrite inE /= sMp.
  by rewrite (sub_pgroup _ kK) // => p kMp; rewrite inE /= kMp orbT.
have [P1maxM | notP1maxM] := boolP (M \in _).
  have defMs: Ms = M^`(1).
    have [U1 complU1] := ex_kappa_compl maxM hallK.
    have [_ [//|<- _] _ _ _] := kappa_structure maxM complU1.
    by case: (P1maxP maxM complU1 P1maxM) => _; move/eqP->; rewrite sdprodg1.
  pose p := pdiv #|U|; have piUp: p \in \pi(U) by rewrite pi_pdiv cardG_gt1.
  have hallU: \pi(H)^'.-Hall(M^`(1)) U.
    have sHM': H \subset M^`(1) by rewrite -defMs.
    have hallH := pHall_subl sHM' (der_sub 1 M) (Fcore_Hall M).
    by rewrite -(compl_pHall _ hallH) ?sdprod_compl.
  have piMs_p: p \in \pi(Ms) by rewrite defMs (piSg sUM').
  have{piMs_p} sMp: p \in \sigma(M) := pnatPpi (pcore_pgroup _ _) piMs_p.
  have sylP: p.-Sylow(M^`(1)) 'O_p(U).
    apply: (subHall_Sylow hallU (pnatPpi (pHall_pgroup hallU) piUp)).
    exact: nilpotent_pcore_Hall nilU.
  rewrite (subset_trans (char_norms (pcore_char p U))) //.
  rewrite (norm_sigma_Sylow sMp) //.
  by rewrite (subHall_Sylow (Msigma_Hall maxM)) //= -/Ms defMs.
suffices complU: kappa_complement M U K.
  by symmetry; apply/idPn; have [[[]]] := BGsummaryC maxM complU ntK.
split=> //; last by rewrite -norm_joinEr ?groupP.
rewrite pHallE (subset_trans _ (der_sub 1 M)) //=.
rewrite -(@eqn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defM').
have [U1 complU1] := ex_kappa_compl maxM hallK.
have [hallU1 _ _] := complU1; rewrite -(card_Hall hallU1).
have [_ [// | defM'1 _] _ _ _] := kappa_structure maxM complU1.
rewrite [H](Fcore_eq_Msigma maxM _) ?(sdprod_card defM'1) //.
by rewrite notP1type_Msigma_nil // in_setD notP1maxM PmaxM orbT.
Qed.

(* This is B & G, Lemma 16.1. *)
Lemma FTtypeP : forall i M,
  M \in 'M -> reflect (FTtype_spec i M) (FTtype M == i).
Proof.
move=> i M maxM; pose Ms := M`_\sigma; pose M' := M^`(1); pose H := M`_\F.
have [[ntH sHMs sMsM' _] _] := Fcore_structure maxM.
apply: (iffP eqP) => [<- | ]; last first.
  case: i => [[] // | [[U [[_ _ defM] _ [U0 [sU0U expU0] frobM]] _] | ]].
    apply/eqP; rewrite -FTtype_Fmax //; apply: wlog_neg => notFmaxM.
    have PmaxM: M \in 'M_'P by exact/setDP.
    apply/FtypeP; split=> // p; apply/idP=> kp.
    have [X EpX]: exists X, X \in 'E_p^1(U0).
      apply/p_rank_geP; rewrite p_rank_gt0 -pi_of_exponent expU0 pi_of_exponent.
      have: p \in \pi(M) by rewrite kappa_pi.
      rewrite /= -(sdprod_card defM) pi_of_muln ?cardG_gt0 //; case/orP=> // Fk.
      have [[_ sMFMs _ _] _] := Fcore_structure maxM.
      case/negP: (kappa_sigma' kp).
      exact: pnatPpi (pcore_pgroup _ _) (piSg sMFMs Fk).
    have [[sXU0 abelX _] ntX] := (pnElemP EpX, nt_pnElem EpX isT).
    have kX := pi_pgroup (abelem_pgroup abelX) kp.
    have [_ sUM _ _ _] := sdprod_context defM.
    have sXM := subset_trans sXU0 (subset_trans sU0U sUM).
    have [K hallK sXK] := Hall_superset (mmax_sol maxM) sXM kX.
    have [ntKs _ _ sKsMF _] := Ptype_cyclics PmaxM hallK; case/negP: ntKs.
    rewrite -subG1 -(cent_semiregular (Frobenius_reg_ker frobM) sXU0 ntX).
    by rewrite subsetI sKsMF subIset // centS ?orbT.
  case=> [[[U K] /= [[PtypeM ntU _ _] _ not_sNUM _ _] ] | ].
    apply/eqP; rewrite -FTtype_P2max // inE.
    by have [-> _ -> _] := typePfacts maxM PtypeM; rewrite negb_or ntU not_sNUM.
  case=> [[[U K] /= [[PtypeM ntU _ _] cUU sNUM] ] | ].
    have [_ _] := typePfacts maxM PtypeM.
    rewrite (negPf ntU) sNUM FTtype_P1max // cUU /FTtype -/Ms -/M' -/H.
    by case: ifP => // _; case: (Ms =P M') => // -> _ [//|-> ->].
  case=> [[[U K] /= [[PtypeM ntU _ _] not_cUU sNUM] ] | ].
    have [_ _] := typePfacts maxM PtypeM.
    rewrite (negPf ntU) (negPf not_cUU) sNUM FTtype_P1max // /FTtype -/Ms -/M'.
    by case: ifP => // _; case: (Ms =P M') => // -> _ [//|-> ->].
  case=> // [[K /= PtypeM _]]; have [_ _] := typePfacts maxM PtypeM.
  rewrite eqxx FTtype_P1max //= /FTtype -/Ms -/M' -/H.
  by case: ifP => // _; case: (Ms =P M') => // -> _ [//|-> _].
have [[U K] /= complU] := kappa_witness maxM; have [hallU hallK _] := complU.
have [K1 | ntK] := eqsVneq K 1.
  have FmaxM: M \in 'M_'F by rewrite -(trivg_kappa maxM hallK) K1.
  have ->: FTtype M = 1%N by apply/eqP; rewrite -FTtype_Fmax.
  have ntU: U :!=: 1 by case/(FmaxP maxM complU): FmaxM.
  have defH: H = Ms. 
    by apply/Fcore_eq_Msigma; rewrite // notP1type_Msigma_nil ?FmaxM.
  have defM: H ><| U = M.
    by have [_] := kappa_compl_context maxM complU; rewrite defH K1 sdprodg1.
  exists U.
    have [_ _ _ cU1U1 exU0] := kappa_structure maxM complU.
    split=> //; last by rewrite -/H defH; case: exU0 => // U0 []; exists U0.
    exists [group of <<\bigcup_(x \in (M`_\sigma)^#) 'C_U[x]>>] => [|x Hx].
      split=> //=; rewrite -big_distrr /= /normal gen_subG subsetIl.
      rewrite norms_gen ?normsI ?normG //; apply/subsetP=> u Uu.
      rewrite inE sub_conjg; apply/bigcupsP=> x Msx.
      rewrite -sub_conjg -normJ conjg_set1 (bigcup_max (x ^ u)) //.
      rewrite memJ_norm // normD1 (subsetP (gFnorm _ _)) //.
      by rewrite (subsetP (pHall_sub hallU)).
    by rewrite sub_gen //= -/Ms -defH (bigcup_max x).
  have [|] := boolP (forallb y, (y \notin M) ==> ('F(M) :&: 'F(M) :^ y == 1)).
    move/forall_inP=> TI_F; constructor 1; apply/TIconjP=> x y _ _.
    rewrite setTI (mmax_normal maxM (Fcore_normal _)) //.
    have [_ | notMxy] := boolP (_ \in M); [by left | right].
    rewrite -(conjsgKV y (_ :^ x)) -conjIg -conjsgM setIC.
    apply/eqP; rewrite -subG1 sub_conjg conjs1g -(eqP (TI_F _ notMxy)).
    by rewrite setISS ?conjSg ?Fcore_sub_Fitting.
  rewrite negb_forall_in; case/exists_inP=> y notMy ntX.
  have [_ _ _ _] := nonTI_Fitting_structure maxM notMy ntX.
  case=> [[] | [_]]; first by constructor 2.
  move: #|_| => p; set P := 'O_p(H); rewrite /= -/H => not_cPP cycHp'.
  case=> [expU | [_]]; [constructor 3 | by rewrite 2!inE FmaxM].
  split=> [q | ].
    move/expU; have [_ <- nHU tiHU] := sdprodP defM.
    by rewrite quotientMidl -(exponent_isog (quotient_isog _ _)).
  have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall _ (Fcore_nil M).
  have ntP: P != 1 by apply: contraNneq not_cPP => ->; exact: abelian1.
  by exists p; rewrite // -p_rank_gt0 -(rank_Sylow sylP) rank_gt0.
have PmaxM: M \in 'M_'P by rewrite inE -(trivg_kappa maxM hallK) ntK.
have [Mstar _ [_ _ _ [cycW _ _ _ _]]] := Ptype_embedding PmaxM hallK.
case=> [[tiV defNV] _ _] _ _ defM {Mstar}.  
have [_ [_ cycK] [_ nUK _ _ _] _] := BGsummaryA maxM complU; rewrite -/H.
case=> [[ntKs defCMK] [_ _ _ _ nilM'H] [sM''F defF]].
move/(_ ntK)=> sFM' types34; have hallK_M := pHall_Hall hallK.
have [/= [[cUU not_sNUM]]] := BGsummaryC maxM complU ntK; rewrite -/H -/M' -/Ms.
case=> cycKs _ sKsH not_cycH [defM' sKsM''] _ [_ _ type2 _].
pose Ks := 'C_H(K); pose W := K <*> Ks; pose V := W :\: (K :|: Ks).
have defKs: 'C_Ms(K) = Ks by rewrite -(setIidPr sKsH) setIA (setIidPl sHMs).
rewrite {}defKs -/W -/V in ntKs tiV defNV cycW cycKs sKsM'' sKsH defCMK.
have{defCMK} prKM': {in K^#, forall k, 'C_M'[k] = Ks}.
  have sKsM': Ks \subset M' := subset_trans sKsM'' (der_sub 1 _).
  move=> k; move/defCMK=> defW; have:= dprod_modr defW sKsM'.
  have [_ _ _ ->] := sdprodP defM; rewrite dprod1g.
  by rewrite setIA (setIidPl (der_sub 1 M)).
have defNsV: forall X : {set gT}, X \subset V -> X != set0 -> 'N(X) = W.
  move=> X sXV neX; apply/eqP; rewrite eqEsubset andbC cents_norm; last first.
    rewrite (centsS sXV) // (sub_abelian_cent (cyclic_abelian cycW)) //.
    exact: subsetDl.
  apply/subsetP=> x nXx; rewrite -defNV inE.
  have VG_V: V \in V :^: G := orbit_refl 'Js _ V.
  have VG_Vx: V :^ x \in V :^: G := mem_orbit 'Js V (in_setT x).
  rewrite -(contraNeq (trivIsetP tiV _ _ VG_V VG_Vx)) // -setI_eq0.
  apply: contra neX => tiVVx; rewrite -subset0 -(eqP tiVVx) subsetI sXV.
  by rewrite-(normP nXx) conjSg. 
have [sHM' nsM'M] := (subset_trans sHMs sMsM', der_normal 1 M : M' <| M).
have hallM': \kappa(M)^'.-Hall(M) M' by exact/(sdprod_normal_pHallP _ hallK).
have [sM'M k'M' _] := and3P hallM'.
have hallH_M': \pi(H).-Hall(M') H := pHall_subl sHM' sM'M (Fcore_Hall M).
have nsHM' := normalS sHM' sM'M (Fcore_normal M).
have [Ueq1 | ntU] := eqsVneq U 1; last first.
  have P2maxM: M \in 'M_'P2 by rewrite inE -(trivg_kappa_compl maxM complU) ntU.
  have ->: FTtype M = 2 by apply/eqP; rewrite -FTtype_P2max.
  have defH: H = Ms.
    by apply/Fcore_eq_Msigma; rewrite // notP1type_Msigma_nil ?P2maxM ?orbT.
  have [//|pr_K tiFM _] := type2; rewrite -defH in defM'.
  have [_ sUM' _ _ _] := sdprod_context defM'.
  have PtypeM: of_typeP M U K by split; rewrite // abelian_nil.
  have defM'F: M'`_\F = H.
    apply/eqP; rewrite eqEsubset (Fcore_max hallH_M') ?Fcore_nil // andbT.
    rewrite (Fcore_max (subHall_Hall hallM' _ (Fcore_Hall _))) ?Fcore_nil //.
      by move=> p piM'Fp; exact: pnatPpi k'M' (piSg (Fcore_sub _) piM'Fp).
    exact: char_normal_trans (Fcore_char _) nsM'M.
  exists (U, K); split=> //; split; first by rewrite defM'F.
    by exists U => // x _; exact: subsetIl.
  have [_ _ _ _ [//|U0 [sU0U expU0 frobU0]]] := kappa_structure maxM complU.
  by rewrite defM'F defH; exists U0.
have P1maxM: M \in 'M_'P1 by rewrite -(trivg_kappa_compl maxM complU) Ueq1.
have: 2 < FTtype M <= 5 by rewrite -FTtype_P1max.
rewrite /FTtype -/H -/Ms; case: ifP => // _; case: eqP => //= defMs _.
have [Y hallY nYK]: exists2 Y, \pi(H)^'.-Hall(M') (gval Y) & K \subset 'N(Y).
  apply: coprime_Hall_exists; first by case/sdprodP: defM.
    by rewrite (coprime_sdprod_Hall defM) (pHall_Hall hallM').
  exact: solvableS sM'M (mmax_sol maxM).
have{defM'} defM': H ><| Y = M' by exact/(sdprod_normal_p'HallP _ hallY).
have PtypeM: of_typeP M Y K.
  have [_ sYM' mulHY nHY tiHY] := sdprod_context defM'.
  do 2!split=> //; rewrite (isog_nil (quotient_isog nHY tiHY)).
  by rewrite /= -quotientMidl mulHY.
have [_ _ sNYG [//| defY1 ->]] := typePfacts maxM PtypeM.
rewrite defY1; have [Y1 | ntY] := altP (Y :=P: 1); last first.
  move/esym: sNYG; rewrite (negPf ntY) P1maxM /= => sNYG.
  have [|_ tiFM prK] := types34; first by rewrite defY1.
  by case: ifPn; exists (Y, K).
exists K; first by rewrite -Y1.
have [|] := boolP (forallb y, (y \notin M) ==> ('F(M) :&: 'F(M) :^ y == 1)).
  move/forall_inP=> TI_F; constructor 1; apply/TIconjP=> x y _ _.
  rewrite setTI (mmax_normal maxM (Fcore_normal _)) //.
  have [_ | notMxy] := boolP (_ \in M); [by left | right].
  rewrite -(conjsgKV y (_ :^ x)) -conjIg -conjsgM setIC.
  apply/eqP; rewrite -subG1 sub_conjg conjs1g -(eqP (TI_F _ notMxy)).
  by rewrite setISS ?conjSg ?Fcore_sub_Fitting.
rewrite negb_forall_in; case/exists_inP=> y notMy ntX.
have [_ _ _ _] := nonTI_Fitting_structure maxM notMy ntX.
case=> [[] | [_]]; first by case/idPn; case/setDP: PmaxM.
move: #|_| => p; set P := 'O_p(H); rewrite /= -/H => not_cPP cycHp'.
have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall _ (Fcore_nil M).
have ntP: P != 1 by apply: contraNneq not_cPP => ->; exact: abelian1.
have piHp: p \in \pi(H) by rewrite -p_rank_gt0 -(rank_Sylow sylP) rank_gt0.
have defH: H = Ms by apply/eqP; rewrite defY1 Y1.
rewrite -defMs -defH in defM; have [_ <- nHU tiHU] := sdprodP defM.
rewrite quotientMidl -(card_isog (quotient_isog _ _)) //.
rewrite -(exponent_isog (quotient_isog _ _)) // exponent_cyclic //=.
case=> [K_dv_H1 | [oP _ K_dv_p1]]; [constructor 2 | constructor 3].
  by exists p; rewrite ?K_dv_H1.
by exists p.
Qed.

(* This is B & G, Theorem I. *)
(* Note that the first assertion is not used in the Perterfalvi revision of   *)
(* the character theory part of the proof.                                    *)
Theorem BGsummaryI :
  [/\ forall H x a, Hall G H -> nilpotent H -> x \in H -> x ^ a \in H ->
      exists2 y, y \in 'N(H) & x ^ a = x ^ y
    & {in 'M, forall M, FTtype M == 1%N}
    \/ exists ST : {group gT} * {group gT}, let (S, T) := ST in
      [/\ S \in 'M /\ T \in 'M,
          exists Wi : {group gT} * {group gT}, let (W1, W2) := Wi in
          let W := W1 <*> W2 in let V := W :\: (W1 :|: W2) in
         (*a*) [/\ cyclic W, trivIset (V :^: G), 'N(V) = W, normTIset V W
                  & W1 :!=: 1 /\ W2 :!=: 1] /\
         (*b*) [/\ S^`(1) ><| W1 = S, T^`(1) ><| W2 = T & S :&: T = W],
     (*c*) {in 'M, forall M, FTtype M != 1%N ->
            exists x, S :^ x = M \/ T :^ x = M},
     (*d*) FTtype S == 2 \/ FTtype T == 2
   & (*e*) 1 < FTtype S <= 5 /\ 1 < FTtype T <= 5]].
Proof.
split=> [H x a hallH nilH Hx|].
  have [M maxM sHMs] := nilpotent_Hall_sigma nilH hallH.
  have{hallH} hallH := pHall_subl sHMs (subsetT _) (Hall_pi hallH).
  by case/(sigma_Hall_tame maxM hallH Hx) => // y; case/setIP; exists y.
have [allFM | ] := boolP (('M : {set {group gT}}) \subset 'M_'F).
  by left=> M maxM; rewrite -FTtype_Fmax // (subsetP allFM).
case/subsetPn=> S maxS notFmaxS; right.
have PmaxS: S \in 'M_'P by exact/setDP.
have [[U W1] /= complU] := kappa_witness maxS; have [_ hallW1 _] := complU.
have ntW1: W1 :!=: 1 by rewrite (trivg_kappa maxS).
have [[_ [_]]] := BGsummaryC maxS complU ntW1; set W2 := 'C_(_)(W1) => ntW2 _.
set W := W1 <*> W2; set V := W :\: _ => _ _ [T [[PmaxT defW1 hallW2 _] _]].
case=> defST _ cycW [P2maxST PmaxST] [[tiV defNV]] _ _ _.
have [maxT _] := setDP PmaxT.
have [_ _ [_ _ _ _ [_ _ _ defS]]] := Ptype_embedding PmaxS hallW1.
have [_ _ [_ _ _ _ [_ _ _ defT]]] := Ptype_embedding PmaxT hallW2.
exists (S, T); split=> //.
- exists (W1, [group of W2]); do 2![split=> //=] => X sXV neX.
  apply/eqP; rewrite eqEsubset andbC cents_norm; last first.
    rewrite (centsS sXV) // (sub_abelian_cent (cyclic_abelian cycW)) //.
    exact: subsetDl.
  apply/subsetP=> x nXx; rewrite -/W -defNV inE.
  have VG_V: V \in V :^: G := orbit_refl 'Js _ V.
  have VG_Vx:  V :^ x \in V :^: G := mem_orbit 'Js V (in_setT x).
  rewrite -(contraNeq (trivIsetP tiV _ _ VG_V VG_Vx)) // -setI_eq0.
  apply: contra neX => /eqP tiVVx; rewrite -subset0 -tiVVx subsetI sXV.
  by rewrite -(normP nXx) conjSg.
- move=> M maxM; rewrite /= -FTtype_Pmax //; move/PmaxST.
  by case/setUP; case/imsetP=> x _ ->; exists x; by [left | right].
- by rewrite -!{1}FTtype_P2max.
rewrite !{1}(ltn_neqAle 1) -!{1}andbA !{1}FTtype_range // !{1}andbT.
by rewrite !{1}(eq_sym 1%N) -!{1}FTtype_Pmax.
Qed.

Lemma ker0_FTtypeI : forall M, M \in 'M -> of_typeI M -> 'A0(M) = 'A(M).
Proof.
move=> M maxM; move/(FTtypeP 1 maxM)=> typeI_M.
apply/setUidPl; apply/subsetP=> x; rewrite typeI_M !inE; case/and3P=> Mx.
by rewrite (mem_p_elt (pgroup_pi M)).
Qed.

Lemma ker0_FTtypeP : forall M U W1 (H := M`_\F) (W2 := 'C_H(W1)),
    M \in 'M -> of_typeP M U W1 ->
    let W := W1 <*> W2 in let V := W :\: (W1 :|: W2) in
  'A0(M) :\: 'A(M) = class_support V M.
Proof.
move=> M U0 K H Ks maxM PtypeM /=; have [[_ _ ntK _] _ _ _ _] := PtypeM.
have [PmaxM hallK _ _] := typePfacts maxM PtypeM.
have [[_ sHMs _ _] _] := Fcore_structure maxM.
have [U complU] := ex_kappa_compl maxM hallK.
have [[_ [_ _ sKsH _] _] _ [_ [-> _ _] _ _]] := BGsummaryC maxM complU ntK.
by rewrite -(setIidPr sKsH) setIA (setIidPl sHMs).
Qed.

(* This is the part of B & G, Theorem II that is relevant to the proof of     *)
(* Peterfalvi (8.7). We drop the considerations on the set of supporting      *)
(* groups, in particular (Tii)(a), but do include additional information on D *)
(* fact that D is included in 'A1(M), not just 'A(M).                         *)
Theorem BGsummaryII : forall M (X : {set gT}),
    M \in 'M -> X \in pred2 'A(M) 'A0(M) ->
    let D := [set x \in X | ~~ ('C[x] \subset M)] in
 [/\       D \subset 'A1(M), (* was 'A(M) in B & G *)
     (*i*) {in X, forall x a, x ^ a \in X -> exists2 y, y \in M & x ^ a = x ^ y}
  &  {in D, forall x (L := 'N[x]),
 [/\ (*ii*) 'M('C[x]) = [set L], FTtype L \in pred2 1%N 2,
     [/\ (*b*) L`_\F ><| (M :&: L) = L,
         (*c*) {in X, forall y, coprime #|L`_\F| #|'C_M[y]| },
         (*d*) x \in 'A(L) :\: 'A1(L)
       & (*e*) 'C_(L`_\F)[x] ><| 'C_M[x] = 'C[x]]
   & (*iii*) FTtype L == 2 ->
             exists2 E, [Frobenius M = M`_\F ><| gval E] & cyclic E]}].
Proof.
move=> M X maxM defX.
have sAM: 'A(M) \subset M.
  by apply/bigcupsP=> x _; rewrite setDE -setIA subIset ?der_sub.
have sA0M: 'A0(M) \subset M by rewrite subUset sAM setIdE subsetIl.
have sAA0: 'A(M) \subset 'A0(M) := subsetUl _ _.
without loss {defX} ->: X / X = 'A0(M).
  case/pred2P: defX => ->; move/(_ _ (erefl _))=> //.
  set D0 := finset _ => [[sD0A1 tameA0 signD0]] D.
  have sDD0: D \subset D0 by rewrite /D /D0 !setIdE setSI.
  split=> [|x Ax a Axa|x Dx]; first exact: subset_trans sDD0 sD0A1.
    by apply: tameA0; exact: (subsetP sAA0).
  have [-> -> [-> coA0L -> -> frobL]] := signD0 x (subsetP sDD0 x Dx).
  by do 2![split=> //] => y Ay; rewrite coA0L // (subsetP sAA0).
move=> {X} D; pose Ms := M`_\sigma.
have tiA0A: forall x a, x \in 'A0(M) :\: 'A(M) -> x ^ a \notin 'A(M).
  move=> x a; rewrite 3!inE; case: (x \in _) => //=; case/and3P=> _ notM'x _.
  apply: contra notM'x; case/bigcupP=> y _; case/setD1P=> _; case/setIP=> Mx _.
  by rewrite -(p_eltJ _ _ a) (mem_p_elt (pgroup_pi _)).
have tiA0: forall x a, x \in 'A0(M) :\: 'A1(M) -> x ^ a \in 'A0(M) -> a \in M. 
  move=> x a; case/setDP=> A0x notA1x A0xa.
  have [Mx Mxa] := (subsetP sA0M x A0x, subsetP sA0M _ A0xa).
  have [[U K] /= complU] := kappa_witness maxM.
  have [Ax | notAx] := boolP (x \in 'A(M)).
    have [_ _ _ [_ []]] := BGsummaryB maxM complU; set B := _ :\: _ => tiB nBM.
    have Bx: x \in B by exact/setDP.
    have ntx: x != 1 by case/bigcupP: Ax => y _; case/setD1P.
    rewrite -(mmax_norm maxM _ _ (norms_gen nBM)); last first.
    - by rewrite (sub_mmax_proper maxM) // gen_subG subDset setUC subsetU ?sAM.
    - by apply/trivgPn; exists x; rewrite ?mem_gen.
    rewrite -sub1set norms_gen // sub1set -groupV inE.
    have BG_B: B \in B :^: G by exact: orbit_refl.
    have BG_Ba: B :^ a^-1 \in B :^: G by exact: mem_orbit (in_setT a^-1).
    rewrite -(contraNeq (trivIsetP tiB _ _ BG_B BG_Ba)) // -setI_eq0.
    apply/set0Pn; exists x; rewrite inE Bx mem_conjgV inE /=; apply/andP; split.
      apply: contra notA1x; case/setD1P=> _; rewrite !inE ntx def_FTcore //.
      move/(mem_p_elt (pcore_pgroup _ _)); rewrite p_eltJ => sMx.
      by rewrite (mem_Hall_pcore (Msigma_Hall maxM)).
    by apply: contraLR Ax => notAxa; rewrite -(conjgK a x) tiA0A // inE notAxa.
  have ntK: K :!=: 1.
    rewrite -(trivgFmax maxM complU) FTtype_Fmax //; apply: contra notAx.
    by move/(FTtypeP 1 maxM); move/ker0_FTtypeI <-.
  have [_ _ [_ [_ tiB <-] _ _]] := BGsummaryC maxM complU ntK.
  set B := _ :\: _ in tiB *; have Bx: x \in B by exact/setDP.
  have BG_B: B \in B :^: G by exact: orbit_refl.
  have BG_Ba: B :^ a^-1 \in B :^: G by exact: mem_orbit (in_setT a^-1).
  rewrite -groupV inE -(contraNeq (trivIsetP tiB _ _ BG_B BG_Ba)) // -setI_eq0.
  by apply/set0Pn; exists x; rewrite inE Bx /= mem_conjgV inE tiA0A.
have sDA1: D \subset 'A1(M).
  apply/subsetPn=> [[x]]; case/setIdP=> A0x not_sCxM notA1x.
  case/negP: not_sCxM; apply/subsetP=> a cxa.
  by apply: (tiA0 x); [exact/setDP | rewrite /conjg -(cent1P cxa) mulKg].
have sDMs1: D \subset Ms^# by rewrite /Ms -def_FTcore.
have [tameMs _ signM PsignM] := BGsummaryD maxM.
split=> // [x A0x a A0xa|x Dx].
  have [A1x | notA1x] := boolP (x \in 'A1(M)); last first.
    by exists a; rewrite // (tiA0 x) // inE notA1x.
  case/setD1P: A1x => _; rewrite def_FTcore // => Ms_x.
  apply/imsetP; rewrite tameMs ?mem_imset ?inE //.
  rewrite (mem_Hall_pcore (Msigma_Hall maxM)) ?(subsetP sA0M) //.
  by rewrite p_eltJ (mem_p_elt (pcore_pgroup _ _) Ms_x).
have [Ms1x [_ not_sCxM]] := (subsetP sDMs1 x Dx, setIdP Dx).
have [[uniqN defNF] [ANx typeN hallMN] type2] := PsignM x Ms1x not_sCxM.
have [maxN _] := mem_uniq_mmax uniqN.
split=> //; last 1 first.
- rewrite -FTtype_P2max //; case/type2=> FmaxM.
  by rewrite (Fcore_eq_Msigma maxM _) // notP1type_Msigma_nil ?FmaxM.
- by rewrite !inE -FTtype_Fmax // -FTtype_P2max // -in_setU.
split=> // [|y A0y|]; rewrite defNF ?sdprod_sigma //=; last by case/signM: Ms1x.
rewrite coprime_pi' ?cardG_gt0 // -pgroupE.
rewrite (eq_p'group _ (pi_Msigma maxN)); apply: wlog_neg => not_sNx'CMy.
have ell1x := Msigma_ell1 maxM Ms1x.
have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG; case/setD1P: Ms1x.
have MSx_gt1: #|'M_\sigma[x]| > 1.
  rewrite ltn_neqAle lt0n {2}(cardD1 M) SMxM andbT eq_sym.
  by apply: contra not_sCxM; move/cent1_sub_uniq_sigma_mmax->.
have [FmaxM t2'M]: M \in 'M_'F /\ \tau2(M)^'.-group M.
  apply: (non_disjoint_signalizer_Frobenius ell1x MSx_gt1 SMxM).
  by apply: contra not_sNx'CMy; exact: pgroupS (subsetIl _ _).
have defA0: 'A0(M) = Ms^#.
  rewrite ker0_FTtypeI //; last by apply/(FTtypeP 1); rewrite -?FTtype_Fmax. 
  rewrite /'A(M) /'A1(M) -FTtype_Fmax // FmaxM def_FTcore //= -/Ms.
  apply/setP => z; apply/bigcupP/idP=> [[t Ms1t] | Ms1z]; last first.
    have [ntz Ms_z] := setD1P Ms1z.
    by exists z; rewrite // 3!inE ntz cent1id (subsetP (pcore_sub _ _) z Ms_z).
  case/setD1P=> ntz; case/setIP=> Mz ctz.
  rewrite 2!inE ntz (mem_Hall_pcore (Msigma_Hall maxM)) //.
  apply: sub_in_pnat (pnat_pi (order_gt0 z)) => p _ pi_z_p.
  have szM: <[z]> \subset M by rewrite cycle_subG.
  have [piMp [_ k'M]] := (piSg szM pi_z_p, setIdP FmaxM).
  apply: contraR (pnatPpi k'M piMp) => s'p /=; unlock kappa; apply/andP; split.
    have:= piMp; rewrite (partition_pi_mmax maxM) (negPf s'p) orbF.
    by rewrite orbCA [p \in _](negPf (pnatPpi t2'M piMp)).
  move: pi_z_p; rewrite -p_rank_gt0 /= -(setIidPr szM).
  case/p_rank_geP=> P; rewrite pnElemI -setIdE; case/setIdP=> EpP sPz.
  apply/exists_inP; exists P => //; apply/trivgPn.
  have [ntt Ms_t] := setD1P Ms1t; exists t => //.
  by rewrite inE Ms_t (subsetP (centS sPz)) // cent_cycle cent1C.
move: A0y; rewrite defA0; case/setD1P=> nty Ms_y.
have sCyMs: 'C_M[y] \subset Ms.
  rewrite -[Ms](setD1K (group1 _)) -subDset /= -defA0 subsetU //.
  rewrite (bigcup_max y) //; first by rewrite 2!inE nty def_FTcore.
  by rewrite -FTtype_Fmax ?FmaxM.
have notMGN: gval 'N[x] \notin M :^: G.
  have [_ [//|_ _ t2Nx _ _]] := FT_signalizer_context ell1x.
  have [ntx Ms_x] := setD1P Ms1x; have sMx := mem_p_elt (pcore_pgroup _ _) Ms_x.
  apply: contra ntx; case/imsetP=> a _ defN.
  rewrite -order_eq1 (pnat_1 sMx (sub_p_elt _ t2Nx)) // => p.
  by rewrite defN tau2J //; case/andP.
apply: sub_pgroup (pgroupS sCyMs (pcore_pgroup _ _)) => p sMp.
by apply: contraFN (sigma_partition maxM maxN notMGN p) => sNp; exact/andP.
Qed.

End Section16.


