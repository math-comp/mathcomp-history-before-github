(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of the multplicative group                              *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import seq fintype paths connect.
Require Import groups normal div zp finset bigops group_perm automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Euler.

Definition fp_mul p := {x : I_(p) | coprime p x}.
Canonical Structure fp_mul_subType p := Eval hnf in [subType of fp_mul p].
Canonical Structure fp_mul_eqType p := Eval hnf in [eqType of fp_mul p].
Canonical Structure fp_mul_finType p := Eval hnf in
  [finType of fp_mul_eqType p].

Variable n : pos_nat.

Lemma to_zp_proof : forall i, i %% n < n.
Proof. by move=> i; rewrite ltn_mod. Qed.

Definition to_zp i := Ordinal (to_zp_proof i).
 
Lemma fp_mul_unit_proof : coprime n (to_zp 1).
Proof.
case: (ltngtP n 1) => [|lt1n | n1]; first by rewrite ltnNge (valP n).
  by rewrite /= modn_small // /coprime gcdn1.
by rewrite {1}n1 /coprime gcd1n.
Qed.

Definition fp_mul_unit : fp_mul n := Sub (to_zp 1) fp_mul_unit_proof.

Lemma inv_fp_mul_proof : forall x : fp_mul n,
  coprime n (to_zp (egcdn (val x) n).1).
Proof.
case=> x; rewrite /= /coprime gcdn_modr.
case: (posnP x) => [->|x_pos conx]; first by case: n; do 2?case.
case: egcdnP => //= kx kp; rewrite -(gauss_gcdl _ conx) => -> _.
by rewrite gcdn_addl_mul -(gcdnC n) (eqnP conx) gcdn1.
Qed.

Definition inv_fp_mul x : fp_mul n := Sub (to_zp _) (inv_fp_mul_proof x).

Lemma mul_fp_mul_proof : forall x y : fp_mul n,
  coprime n (to_zp (val x * val y)).
Proof.
case=> [x conx] [y cony]; rewrite /= /coprime gcdn_modr [_ == 1]coprime_mulr.
exact/andP.
Qed.

Definition mul_fp_mul x y : fp_mul n := Sub (to_zp _) (mul_fp_mul_proof x y).

Lemma unit_fp_mul : left_unit fp_mul_unit mul_fp_mul.
Proof.
by move=> x; do 2!apply: val_inj; rewrite /= modn_mulml mul1n modn_small.
Qed.

Lemma invP_fp_mul : left_inverse fp_mul_unit inv_fp_mul mul_fp_mul.
Proof.
case=> x conx; do 2!apply: val_inj; rewrite /= modn_mulml.
case: (posnP x) conx => [->|x_pos conx]; first by case: n; do 2?case.
by case: egcdnP => // _ kp -> _; rewrite gcdnC (eqnP conx) modn_addl_mul.
Qed.

Lemma mulP_fp_mul : associative mul_fp_mul.
Proof.
by move=> x y z; do 2!apply: val_inj; rewrite /= modn_mulmr modn_mulml mulnA.
Qed.

Canonical Structure fp_mul_pre_group := Eval hnf in
  mkFinPreGroupType mulP_fp_mul unit_fp_mul invP_fp_mul.

Canonical Structure fp_mul_group := FinGroupType invP_fp_mul.

(* This introduces an unwanted dependency to cyclic

Lemma cardphi : #|fp_mul_group| = (phi p).
Proof. by rewrite card_sub. Qed.

*)

End Euler.
