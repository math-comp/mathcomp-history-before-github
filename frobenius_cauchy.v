(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
(* Require Import seq. *)
Require Import fintype.
(* Require Import connect. *)
Require Import ssralg.
Require Import bigops.
Require Import finset.
Require Import groups.
Require Import action.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Frob_Cauchy.

Open Scope group_scope.

Variables (aT : finGroupType) (sT : finType) (to : {action aT &-> sT}).
Variable G : {group aT}.

Lemma astab1_to : forall x a,
  a \in 'N(G) -> 'C_(G | to)[to x a] = 'C_(G | to)[x] :^ a.
Proof.
move=> x a nGa; rewrite conjIg (normP nGa); congr (_ :&: _).
apply/setP=> b; rewrite mem_conjg !(sameP astab1P eqP) actCJV.
exact: (inj_eq (act_inj to a)).
Qed.

Lemma card_stab_eq : forall x y,
  y \in orbit to G x -> #|'C_(G | to)[x]| = #|'C_(G | to)[y]|.
Proof.
move=> x y; case/orbitP=> a Ga <- {y}; rewrite astab1_to ?card_conjg //.
exact: (subsetP (normG G)).
Qed.

Theorem Frobenius_Cauchy :
  \sum_(a \in G) #|'C[a | to]| = (#|orbit to G @: setT| * #|G|)%N.
Proof.
transitivity (\sum_(a \in G) \sum_(x \in 'C[a | to]) 1%N).
  by apply: eq_bigr => a _; rewrite sum_nat_const muln1.
rewrite (exchange_big_dep predT) //=; set orbG := orbit to G.
rewrite (partition_big orbG (mem (orbG @: setT))) //= => [|y _]; last first.
  by rewrite mem_imset ?inE.
rewrite -sum_nat_const; apply: eq_bigr => X; case/imsetP=> x _ ->{X}.
rewrite (eq_bigl (mem (orbG x))) => [|y]; last first.
  by apply/eqP/idP=> [<-|]; [exact: orbit_refl | move/orbit_transl].
rewrite -(LaGrange (subset_astab to G [set x])) mulnC.
rewrite -card_orbit -sum_nat_const.
apply: eq_bigr => y Gxy; rewrite sum_nat_const muln1 (card_stab_eq Gxy).
by apply: eq_card => a; rewrite inE /= -(sameP afix1P astab1P).
Qed.

End Frob_Cauchy.

