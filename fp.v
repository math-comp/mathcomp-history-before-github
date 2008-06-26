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
Require Import fintype finset groups normal div dirprod.

(* Require Import seq paths connect zp bigops group_perm automorphism  *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Euler.

Definition fp_mul p := {x : 'I_p | coprime p x}.
Canonical Structure fp_mul_subType p := Eval hnf in [subType of fp_mul p].
Canonical Structure fp_mul_eqType p := Eval hnf in [eqType of fp_mul p].
Canonical Structure fp_mul_finType p := Eval hnf in [finType of fp_mul p].
Canonical Structure fp_mul_subFinType p :=
  Eval hnf in [subFinType of fp_mul p].

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

Canonical Structure fp_mul_baseFinGroupType := Eval hnf in
  [baseFinGroupType of fp_mul n by mulP_fp_mul, unit_fp_mul & invP_fp_mul].

Canonical Structure fp_mul_finGroupType := FinGroupType invP_fp_mul.

End Euler.

Section EulerUnit.

(* the unit for the multiplicative group *)

Lemma ltnSSn : forall n, 1 < n.+2.
Proof. by []. Qed.

Definition zp1 (n:pos_nat) : ordinal_finType n.
case; case; first by case/negP; rewrite ltn0.
case; first by exists (Ordinal (ltnSn 0)).
move=> n i; by exists (Ordinal (ltnSSn n)).
Defined.

Lemma zp11 : forall (n:nat) (H: 0 < n.+2),
  (zp1 (PosNat H)) = (Ordinal (ltnSSn n)).
Proof.  by case=> [|n] H; apply: val_inj=> //=. Qed.

Lemma zp10 : forall (H : 0 < 1), (zp1 (PosNat H)) = (Ordinal H).
Proof. trivial. Qed.

Lemma coprime_zp1 : forall n: pos_nat, coprime n (zp1 n).
Proof.
case; case; first by case/negP; rewrite ltn0.
case=> [|n] H; first by rewrite zp10.
by rewrite zp11; apply coprimen1.
Qed.

End EulerUnit.

Section Chinese.

Variables m n : pos_nat.

Lemma coprime_modn_mull : forall p,
    coprime (m * n) p = coprime m (p %% m) && coprime n (p %% n).
Proof.
move=> p; rewrite /coprime (gcdnC m) (gcdnC n); move: (gcdnE m p) (gcdnE n p).
rewrite !eqn0Ngt (valP m) (valP n) /= => <- <-; exact: coprime_mull.
Qed.

Lemma coprime_fp_mul_proof : forall p,
  coprime (m * n) p ->
  coprime m (to_zp m p) && coprime n (to_zp n p).
Proof. by move=> p; rewrite coprime_modn_mull. Qed.


Definition rho : fp_mul (m * n) ->  (fp_mul m) * (fp_mul n):=
  fun x => let Hcop := (andP (coprime_fp_mul_proof (valP x))) in
    (Sub (to_zp m _) (proj1 Hcop), Sub (to_zp n _) (proj2 Hcop)).

Lemma rho_morph : {morph rho : x y / x * y}%g.
Proof.
move=> x y; apply/eqP; rewrite eq_sym; do 3!rewrite /eqd /=.
rewrite !modn_mul2m !eqn_mod_dvd ?leq_modn //.
rewrite {1 3}(divn_eq (sval x * sval y) (m * n)) !addnK.
by rewrite !mulnA {1}mulnAC !dvdn_mull.
Qed.

Canonical Structure rho_morphism := @Morphism _ _ setT rho (in2W rho_morph).

Hypothesis Hcop : coprime m n.

Lemma rho_inj : ('injm rho)%g.
Proof.
apply/injmP=> x y _ _; case=> Hm Hn; do 2!apply: val_inj => /=.
move: (modn_small (valP (sval x))) (modn_small (valP (sval y))) => /= <- <-.
by apply/eqP; rewrite chinese_remainder // Hm Hn !eqxx.
Qed.

Lemma rho_isom : isom setT setT rho.
Proof.
apply/isomP; split; first exact: rho_inj.
apply/setP=> [[x1 x2]]; rewrite !inE /=.
have Hi : chinese m n (sval x1) (sval x2) %% (m * n) < m * n.
  by rewrite ltn_mod pos_natP.
have Hc: coprime (m * n) (Ordinal Hi).
  move: (gcdnE (m * n) (chinese m n (sval x1) (sval x2))).
  rewrite eqn0Ngt pos_natP /coprime /= [gcdn (_ %% _ ) _ ]gcdnC=> <-.
  move: (coprime_modn_mull (chinese m n (sval x1) (sval x2))).
  rewrite /coprime=> ->.
  rewrite chinese_modl ?(valP n) // chinese_modr ?(valP m) //.
  rewrite (modn_small (valP (sval x1))) (modn_small (valP (sval x2))) /=.
  by move: (svalP x1) (svalP x2); rewrite /coprime=> ->->.
pose c : fp_mul (m * n) := Sub (Ordinal _) Hc.
apply/imsetP; exists c; rewrite ?inE //=; apply/eqP; do 3!rewrite /eqd /=.
set e := chinese _ _ _ _; pose e' i j := modn_addl_mul (e %/ (m * n) * i) j _.
rewrite -(e' m n) -{e'}(e' n m) -!mulnA (mulnC n) -divn_eq.
by rewrite chinese_modl ?chinese_modr ?modn_small ?eqxx.
Qed.

End Chinese.