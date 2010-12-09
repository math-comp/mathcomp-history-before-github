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
(*                          we have 'M_\sigma[x] = [set 'N[x]].               *)
(*                 'R[x] == if 'M_\sigma[x] is non-empty, a normal Hall       *)
(*                          subgroup of 'C[x] that acts sharply transitively  *)
(*                          on 'M`_\sigma[x]. If 'R[x] != 1 then we must have *)
(*                          'R[x] = 'C_('N[x]`_\sigma)[x].                    *)
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

Definition sigma_mmax_of X := [set M : {group gT} | X \subset M`_\sigma].

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

Definition TypeF_maxgroups :=
  locked [set M \in 'M | ~~ has (kappa M) (primes #|M|)].

Definition TypeP_maxgroups := locked ('M :\: TypeF_maxgroups).

Definition TypeP1_maxgroups :=
  locked [set M \in 'M | all [predU \sigma(M) & kappa M] (primes #|M|)].

Definition TypeP2_maxgroups := locked (TypeP_maxgroups :\: TypeP1_maxgroups).

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
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.


End Section14.

