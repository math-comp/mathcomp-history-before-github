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
Require Import cyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Euler.

Definition fp_mul p := [subFinType of (sig_eqType (fun x:fzp p => coprime p x))].

Variable n: pos_nat.

Definition fp_mul1 : fp_mul n.
case : n; case; first by case/negP; rewrite ltn0.
case; first by exists (Ordinal (ltn0Sn 0)); rewrite /coprime gcdn0.
move=>n0; have e :(0.+1 < n0.+2)
by move: (ltn0Sn n); rewrite -(leq_add2r 1) 2!addn1.
by exists (Ordinal e); rewrite /coprime gcdn1.
Defined.

Definition inv_fp_mul_val x := if x > 0 then (egcdn x n).1 else 0.

Lemma inv_fp_mul_ltP : forall x : fp_mul n, (inv_fp_mul_val (val x)) < n.
Proof.
rewrite /inv_fp_mul_val => [] [x] /=; move/eqnP.
case: posnP => // x_pos co_p_x; case: egcdnP => //= kx kp.
rewrite gcdnC co_p_x muln1 addn1 => eq_kx_kp lt_kp_x.
rewrite -(ltn_pmul2r x_pos) {}eq_kx_kp.
rewrite -(subnK lt_kp_x) muln_addr  mulnC mulnSr -addnA -addn2 leq_add2l.
apply: leq_trans (leq_addr _ _); exact: leq_trans (ltn_ord x).
Qed.

Lemma inv_fp_mulP : forall x, coprime n (Ordinal (inv_fp_mul_ltP x)).
Proof.
move=> [x co_p_x] /=; rewrite /inv_fp_mul_val; case: posnP => [<- // | x_pos].
case: egcdnP => //= kx kp def_kxx _.
by rewrite /coprime -(gauss_gcdl _ co_p_x) def_kxx (gcdnC x)
  (eqnP co_p_x) gcdn_addl_mul gcdn1.
Qed.

Definition inv_fp_mul x : fp_mul n := exist (fun x : fzp n => coprime n x) _ (inv_fp_mulP x).

Definition mul_fp_mul : fp_mul n -> fp_mul n -> fp_mul n.
move=> [x1 Hx1][y1 Hy1].
have e: ((x1 * y1) %% n < n) by rewrite ltn_mod.
exists (Ordinal e)=>//=; move: Hy1; move/(conj Hx1); move/andP.
by rewrite -coprime_mulr /coprime gcdn_modr.
Defined.

End Euler.

Section EulerProofs.

Variable p:pos_nat.

Lemma unit_fp_mul : forall z, mul_fp_mul (fp_mul1 p)  z = z.
Proof.
move: p; case; case; first by case/negP; rewrite ltn0.
case=>[|n] Hn [y Hy]; apply/val_eqP=>//=.
by move: y Hy; case; case=> //=.
apply/eqP;apply:val_inj=>/=.
by rewrite mul1n; move/eqP: (modn_small (ltn_ord y))=> Hy0; apply/eqP.
Qed.

Lemma invP_fp_mul : forall z,
  mul_fp_mul (inv_fp_mul z) z = (fp_mul1 p).
Proof.
move:p; case; case; first by case/negP; rewrite ltn0.
move=> [|p0] Hp [x co_p_x]; apply/val_eqP =>//=; apply/eqP; apply:val_inj =>/=; first by rewrite modn1.
rewrite /inv_fp_mul_val; move: co_p_x; case: posnP =>[->//|x_pos] co_p_x.
case: (egcdnP _ x_pos) =>/= kx kp -> _; move/eqnP: co_p_x; rewrite gcdnC=>->.
by rewrite modn_addl_mul; move: (ltn0Sn p0); rewrite -(ltn_add2l 1) 2!add1n; move/modn_small=>->.
Qed.

Lemma mulP_fp_mul : forall (x y z: fp_mul p),
  mul_fp_mul x (mul_fp_mul y z) = mul_fp_mul (mul_fp_mul x y) z.
Proof.
move=> [x1 Hx1] [x2 Hx2] [x3 Hx3]; apply/val_eqP=>/=; apply/eqP; apply: val_inj=>/=.
by rewrite modn_mulmr modn_mulml mulnA.
Qed.

Canonical Structure fp_mul_group := FinGroupType unit_fp_mul invP_fp_mul mulP_fp_mul.

Lemma cardphi : #|fp_mul_group| = (phi p).
Proof. by rewrite card_sub. Qed.

End EulerProofs.
