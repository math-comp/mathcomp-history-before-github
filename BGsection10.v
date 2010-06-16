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
  [pred p \in \pi(#|M|) | 
     existsb P : {group gT}, p.-Sylow(M) P && ('N(P) \subset M) ].

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
move=> p P; case/andP=> pdM; case/existsP=> Q; case/andP=> pSyl_Q sNPM pSyl_P.
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
Admitted. 

Let BG10b_to_a :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    [transitive 'C(X), on [set N | N <- orbit 'Js G M, X \subset N] | 'Js] ->
    X \subset M -> forall g, X :^g \subset M -> 
  exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m].
Admitted.

Let BG10a_to_c :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    X \subset M -> 
    (forall g, X :^g \subset M -> 
      exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m]) ->
  'N(X) = 'N_M(X) * 'C(X). 
Proof.
Admitted.

Theorem BG10b :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    [transitive 'C(X), on [set N | N <- orbit 'Js G M, X \subset N] | 'Js].
Proof.
Admitted.

Theorem BG10a :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    X \subset M -> forall g, X :^g \subset M -> 
  exists c, exists m, [/\ c \in 'C(X),  m \in M & g = c * m].
Proof.
move=> p X p_Sig ntX pX sXM g sXgM; apply: (BG10b_to_a _ _ pX) => //.
exact: BG10b p_Sig ntX pX.
Qed.

Theorem BG10_c :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
    X \subset M -> 'N(X) = 'N_M(X) * 'C(X). 
Proof.
move=> p X p_Sig ntX pX sXM; apply: (BG10a_to_c p_Sig ntX pX) => //.
exact: BG10a p_Sig ntX pX sXM.
Qed.

Theorem BG10e :
    forall p X, p \in \sigma(M) -> X :!=: 1 -> p.-group X ->
  'C(X) \subset M -> forall g, X :^ g \subset M -> g \in M.
Proof.
Admitted.

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

End Ten.