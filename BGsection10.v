(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype paths.
Require Import finset prime groups action automorphism normal cyclic.
Require Import gfunc pgroups gprod center commutators gseries nilpotent.
Require Import sylow abelian maximal hall BGsection1 BGsection4 BGsection5.
Require Import BGsection6 BGsection7 BGsection8 BGsection9.

(******************************************************************************)
(*   This file covers B & G, section 10                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Ten.

Variable gT : minSimpleOddGroupType.
Implicit Type p : nat.
Local Notation G := (TheMinSimpleOddGroup gT).

Definition ideal p := 
  (3 <= 'r_p(G)) && 
   forallb P, p.-Sylow(G) P && ('E_p^2(P) :&: 'E*_p(P) == set0).

Implicit Type M : {group gT}.

Definition alpha M := [pred p \in \pi(#|M|) | (2 < 'r_p(M))].

Notation "\alpha ( M )" := (alpha M)
  (at level 2, format "\alpha ( M )") : group_scope.

Definition beta M := [pred p \in \alpha(M) | ideal p].

Notation "\beta ( M )" := (beta M)
  (at level 2, format "\beta ( M )") : group_scope.

Definition sigma M := 
  [pred p \in \pi(#|M|) | existsb P, p.-Sylow(M) P && ('N_G(P) \subset M) ].

Notation "\sigma ( M )" := (sigma M)
  (at level 2, format "\sigma ( M )") : group_scope.

Definition sub_alpha M := 'O_\alpha(M)(M).

Notation "M `_ \alpha" := (sub_alpha M)
  (at level 2, format "M `_ \alpha") : group_scope.

Definition sub_beta M := 'O_\beta(M)(M).

Notation "M `_ \beta" := (sub_beta M)
  (at level 2, format "M `_ \beta") : group_scope.

Definition sub_sigma M := 'O_\sigma(M)(M).

Notation "M `_ \sigma" := (sub_sigma M)
  (at level 2, format "M `_ \sigma") : group_scope. 

Variable M : {group gT}.
Hypothesis M_max : M \in 'M.

Let M_proper := mmax_proper M_max.

Lemma beta_sub_alpha : {subset \beta(M) <= \alpha(M)}.
Proof. by move=> p; rewrite !inE; case/andP=> ->. Qed.

Lemma alpha_sub_sigma : {subset \alpha(M) <= \sigma(M)}.
Proof.
move=> p; rewrite !inE; case/andP=> -> rM; have [P Syl_P] := Sylow_exists p M.
apply/existsP; exists (gval P); rewrite Syl_P (subset_trans (subsetIr _ _)) //.
rewrite uniq_mmax_norm_sub // (def_uniq_mmax _ M_max) ?(pHall_sub Syl_P) //.
have pPG := sub_proper_trans (pHall_sub Syl_P) M_proper.
rewrite (p_rank_Sylow Syl_P) -(rank_pgroup (pHall_pgroup Syl_P)) in rM.
exact: rank3_Uniqueness pPG rM.
Qed.

Lemma Mbeta_sub_Malpha : M`_\beta \subset M`_\alpha.
Proof. exact: sub_pcore beta_sub_alpha. Qed.

Lemma Malpha_sub_Msigma : M`_\alpha \subset M`_\sigma.
Proof. exact: sub_pcore alpha_sub_sigma. Qed.


End Ten.