(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection9 PFsection8.

(******************************************************************************)
(* This file covers Peterfalvi, Section 11: Maximal subgroups of Types        *)
(* III and IV.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.

Section Eleven.


Lemma lbound_expn_odd_prime p q : 
   odd p -> odd q -> prime p -> prime q -> p != q -> 4 * q ^ 2 + 1 < p ^ q.
Proof.
case: p=> [|[|[|p]]] //; case: q=> [|[|[|[|[|q]]]]] //.
  case: p=> [|[|p]] // _ _ _ _ _.
  by have /(leq_trans _)-> : 5 ^ 3 <= p.+1.+4 ^ 3 by rewrite leq_exp2r.
set y := p.+3; set x := _.+4; move=> _ _ _ _ _.
have /(leq_trans _)-> //: 3 ^ x <= y ^ x by rewrite leq_exp2r.
rewrite {y}/x; elim: q => [| q IH] //.
rewrite [(3 ^ _)%N]expnS; set x := q.+1.+4 in IH |- *.
rewrite  -(ltn_pmul2l (_ : 0 < 3)) // in IH.
apply: (leq_trans _ IH); rewrite ltnS.
set X := _ + 1; have{X}->: X = 4 * x ^ 2 + (x * (7 * 1).+1 + (2 * 1 + 3))
  by rewrite /X; ring.
set X := (3 * _)%N; have{X}->: X = 4 * x ^ 2 +  (x * (7 * x) + (x * x + 3)) 
  by rewrite /X; ring.
rewrite leq_add2l; apply: leq_add; first by rewrite leq_mul2l ltn_mul2l.
by rewrite leq_add2r leq_mul.
Qed.

End Eleven.
