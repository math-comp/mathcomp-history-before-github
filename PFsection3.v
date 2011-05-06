(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 3: TI-Subsets with Cyclic Normalizers *)
(* Defined here:                                                              *)
(*   cylicTIhypothesis G W W1 W2 == W1 \x W2 = W is a cyclic subgroup of G,   *)
(*                           W1 and W2 are nontrivial of coprime order, and   *)
(*                           W :\: (W1 :|: W2) is a non-empty TI subset of G. *)
(*                           This is Peterfalvi (3.1).                        *)
(* For ccW : cylicTIhypothesis G W W1 W2 we set                               *)
(*        cyclicTIset ccW == W :\: (W1 :|: W2)                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Definitions.

Variables (gT : finGroupType) (G W W1 W2 Wi : {set gT}).

Definition cyclicTIhypothesis :=
  [/\ [/\ W1 \x W2 = W, cyclic W, odd #|W| & W \subset G],
      [/\ W1 != 1, W2 != 1 & coprime #|W1| #|W2| ]
    & trivIset ((W :\: (W1 :|: W2)) :^: G)]%g.


Definition cycTIirr_row :=
  (irr1 W : {cfun gT})
    :: filter [pred xi | (Wi \subset cker W xi) && (xi != irr1 W)]
              (base_irr G).

Definition cyclicTIset of cyclicTIhypothesis := W :\: (W1 :|: W2).

End Definitions.

Section MoreDefinitions.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).

Hypothesis tiW : cyclicTIhypothesis G W W1 W2.

Let w1 := #|W1|.
Let w2 := #|W2|.
Let V := cyclicTIset tiW.

Definition cycTIirr_mx of cyclicTIhypothesis G W W1 W2 :=
  \matrix_(i < (Zp_trunc w1).+2, j < (Zp_trunc w2).+2)
     ((cycTIirr_row G W W2)`_i * (cycTIirr_row G W W1)`_j).

Local Notation ww := (cycTIirr_mx tiW).

Lemma cycTIirr00 : ww 0 0 = irr1 W.
Proof.
by apply/ffunP=> x; rewrite mxE !(irr1E, ffunE) -natr_mul mulnb andbb.
Qed.

End MoreDefinitions.

