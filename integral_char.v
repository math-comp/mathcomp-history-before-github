(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import mxpoly mxrepresentation vector algC classfun character.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file should provide the standard results on character integrality,    *)
(* and algebraic integers, including notations and lemmas for reasoning       *)
(* "mod n" in the algebraics, and computing with class sums.                  *)
(*  For now it is a placeholder for the theorem asserting that the degree of  *)
(* an irreducible character of G divides the order of G (Isaacs 3.11).        *)
(******************************************************************************)

Section IntegralChar.

Variables (gT : finGroupType) (G : {group gT}).

Lemma dvd_irr1_cardG i : dvdC ('chi[G]_i 1%g) #|G|%:R. 
Admitted.

End IntegralChar.
