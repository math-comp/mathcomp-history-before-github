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
Hypotheses (maxS : S \in 'M) (maxT : T \in 'M).
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
Let nu2_ i j := primeTIirr ptiWT i j.
Let ru_ := primeTIred ptiWT.

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


End Fourteen.

