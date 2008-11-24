(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of the additive group and ring Zp, represented as 'I_p  *)
(*                                                                     *)
(***********************************************************************)
(* Definitions:                                                        *)
(* From fintype.v:                                                     *)
(*   'I_p == the subtype of integers less than p, taken here as the    *)
(*           type of integers mod p.                                   *)
(* This file:                                                          *)
(*   inZp p_pos == the natural projection from nat into the integers   *)
(*                 mod p (represented as 'I_p), when p_pos is a proof  *)
(*                 that p > 0.                                         *)
(*  Zp_finGroupType pp == the canonical finGroupType on 'I_pp, when pp *)
(*                        is a pos_nat.                                *)
(*  Zp_ring lt1p == the (commutative) ring structure on 'I_p, given    *)
(*                  lt1p : 1 < p                                       *)
(*  Zp_field pr_p == the field structure on 'I_p, given pr_p : prime p *)
(*     Zp p    == the set (and additive group) of all integers mod p.  *)
(*  Zp_unit p  == the subtype of all units in the ring 'I_p            *)
(*  Zp_units p == the set (and multiplicative group) of all 'I_p units *)
(* We show that Zp and Zp_units are abelian, and compute their orders. *)
(***********************************************************************)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div ssralg.
Require Import fintype bigops poly finset prime groups.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ZpDef.

(***********************************************************************)
(*                                                                     *)
(*  Mod p arithmetic on the finite set {0, 1, 2, ..., p - 1}           *)
(*                                                                     *)
(***********************************************************************)

Variable p : nat.
Hypothesis p_pos : 0 < p.

Definition Zp : {set 'I_p} := setT.

Implicit Types x y z : 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := Ordinal (ltn_pmod i p_pos).
Lemma modZp : forall x, x %% p = x.
Proof. by move=> x; rewrite modn_small ?ltn_ord. Qed.
Lemma valZpK : forall x, inZp x = x.
Proof. by move=> x; apply: val_inj; rewrite /= modZp. Qed.

(* Operations *)
Definition Zp0 := Ordinal p_pos.
Definition Zp1 := inZp 1.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).
Definition Zp_mul x y := inZp (x * y).
Definition Zp_inv x := inZp (egcdn x p).1.

(* Units subtype *)

Inductive Zp_unit : predArgType := ZpUnit x of coprime p x.

Implicit Types u v : Zp_unit.

Coercion Zp_unit_val u := let: ZpUnit x _ := u in x.

Canonical Structure Zp_unit_subType := SubType Zp_unit_val Zp_unit_rect vrefl.
Canonical Structure Zp_unit_eqType := Eval hnf in [subEqType for Zp_unit_val].
Canonical Structure Zp_unit_finType := Eval hnf in [finType of Zp_unit by :>].
Canonical Structure Zp_unit_subFinType := Eval hnf in [subFinType of Zp_unit].

Definition Zp_units : {set Zp_unit} := setT.

(* Additive group structure. *)

Lemma Zp_add0z : left_unit Zp0 Zp_add.
Proof. exact: valZpK. Qed.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Proof.
move=> x; apply: val_inj.
by rewrite /= modn_addml addnC subnK ?modnn // ltnW ?ltn_ord.
Qed.

Lemma Zp_addA : associative Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_addml modn_addmr addnA.
Qed.

Lemma Zp_addC : commutative Zp_add.
Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.

Definition Zp_baseFinGroupType_def := Eval hnf in
  [baseFinGroupType of 'I_p by Zp_addA, Zp_add0z & Zp_addNz].

Definition Zp_additive_group_def :=
  Ring.AdditiveGroup Zp_addA Zp_addC Zp_add0z Zp_addNz.

(* Ring operations *)

Lemma Zp_mul1z : left_unit Zp1 Zp_mul.
Proof. by move=> x; apply: val_inj; rewrite /= modn_mulml mul1n modZp. Qed.

Lemma Zp_mulC : commutative Zp_mul.
Proof. by move=> x y; apply: val_inj; rewrite /= mulnC. Qed.

Lemma Zp_mulz1 : right_unit Zp1 Zp_mul.
Proof. by move=> x; rewrite Zp_mulC Zp_mul1z. Qed.

Lemma Zp_mulA : associative Zp_mul.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_mulml modn_mulmr mulnA.
Qed.

Lemma Zp_mul_addr : right_distributive Zp_mul Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_mulmr modn_add2m muln_addr.
Qed.

Lemma Zp_mul_addl : left_distributive Zp_mul Zp_add.
Proof. by move=> x y z; rewrite -!(Zp_mulC z) Zp_mul_addr. Qed.

Lemma Zp_mulVz : forall x, coprime p x -> Zp_mul (Zp_inv x) x = Zp1.
Proof.
move=> x co_p_x; apply: val_inj; rewrite /= modn_mulml.
by rewrite -(chinese_modl co_p_x 1 0) /chinese addn0 mul1n mulnC.
Qed.

Lemma Zp_mulzV : forall x, coprime p x -> Zp_mul x (Zp_inv x) = Zp1.
Proof. by move=> x Ux; rewrite /= Zp_mulC Zp_mulVz. Qed.

Lemma Zp_mulrn : forall x n,
  ((x : Zp_additive_group_def) *+ n)%R = inZp (x * n).
Proof.
move=> x n; apply: val_inj => /=.
elim: n => [|n IHn] /= ; first by rewrite muln0 modn_small.
by rewrite IHn modn_addmr mulnS.
Qed.

(* Multiplicative (unit) group. *)

Lemma Zp_unit_1_proof : coprime p Zp1.
Proof. by rewrite coprime_modr coprimen1. Qed.

Lemma Zp_unit_mul_proof : forall u v, coprime p (Zp_mul u v).
Proof. by move=> u v; rewrite coprime_modr coprime_mulr (valP u) (valP v). Qed.

Lemma Zp_unit_inv_proof : forall u, coprime p (Zp_inv u).
Proof.
move=> u; have:= Zp_unit_1_proof; rewrite -(Zp_mulVz (valP u)).
by rewrite coprime_modr coprime_mulr; case/andP.
Qed.

Definition Zp_unit_1 := ZpUnit Zp_unit_1_proof.

Definition Zp_unit_inv u := ZpUnit (Zp_unit_inv_proof u).

Definition Zp_unit_mul u v := ZpUnit (Zp_unit_mul_proof u v).

Lemma Zp_unit_mul1g : left_unit Zp_unit_1 Zp_unit_mul.
Proof. move=> u; apply: val_inj; exact: Zp_mul1z. Qed.

Lemma Zp_unit_mulVg : left_inverse Zp_unit_1 Zp_unit_inv Zp_unit_mul.
Proof. move=> u; apply: val_inj; exact: Zp_mulVz (valP u). Qed.

Lemma Zp_unit_mulA : associative Zp_unit_mul.
Proof. move=> u v w; apply: val_inj; exact: Zp_mulA. Qed.

Lemma Zp_unit_mulC : commutative Zp_unit_mul.
Proof. move=> u v; apply: val_inj; exact: Zp_mulC. Qed.

Definition Zp_unit_baseFinGroupType_def := Eval hnf in
  [baseFinGroupType of Zp_unit by Zp_unit_mulA, Zp_unit_mul1g & Zp_unit_mulVg].

Definition Zp_unit_additive_group_def :=
  Ring.AdditiveGroup Zp_unit_mulA Zp_unit_mulC Zp_unit_mul1g Zp_unit_mulVg.

(* Group orders *)

Lemma card_Zp : #|Zp| = p.
Proof. by rewrite cardsT card_ord. Qed.

Lemma card_Zp_units : #|Zp_units| = phi p.
Proof. by rewrite cardsT card_sub phi_count_coprime big_mkord -sum1_card. Qed.

End ZpDef.

Section ZpGroup.

(* Canonical group structures for Zp and Zp_units; we use pos_nat to carry *)
(* the p > 0 assumption, which works fine for group element orders, but    *)
(* doesn't extend very well to the ring and field cases, where one needs   *)
(* stronger constraints (resp., p > 1, prime p) which don't have canonical *)
(* proofs. "Type" classes would work better here.                          *)

Import GroupScope.

Variable p : pos_nat.

Canonical Structure Zp_baseFinGroupType := Zp_baseFinGroupType_def (valP p).
Canonical Structure Zp_finGroupType := FinGroupType (Zp_addNz (valP p)).
Canonical Structure Zp_additive_group := Zp_additive_group_def (valP p).
Canonical Structure Zp_group := Eval hnf in [group of Zp p].

Canonical Structure Zp_unit_baseFinGroupType :=
  Zp_unit_baseFinGroupType_def (valP p).
Canonical Structure Zp_unit_FinGroupType :=
  FinGroupType (Zp_unit_mulVg (valP p)).
Canonical Structure Zp_unit_additive_group :=
  Zp_unit_additive_group_def (valP p).
Canonical Structure Zp_units_group := Eval hnf in [group of Zp_units p].

Implicit Type x : 'I_p.

Definition Zp_gen := Zp1 (valP p).

Lemma Zp_mulgC : @commutative 'I_p mulg.
Proof. exact: Zp_addC. Qed.

Lemma Zp_abelian : abelian (Zp p).
Proof. apply/centsP=> x _ y _; exact: Zp_mulgC. Qed.

Lemma Zp_expgn : forall x n, x ^+ n = inZp (valP p) (x * n).
Proof. exact: Zp_mulrn. Qed.

Lemma Zp_gen_expgz : forall x, Zp_gen ^+ x = x.
Proof. move=> x; rewrite Zp_expgn; exact: Zp_mul1z. Qed.

Lemma Zp_cycle : setT = <[Zp_gen]>.
Proof.
by apply/setP=> x; rewrite -[x]Zp_gen_expgz inE groupX ?mem_gen ?set11.
Qed.

Lemma Zp_unit_mulgC : @commutative (Zp_unit p) mulg.
Proof. exact: Zp_unit_mulC. Qed.

Lemma Zp_units_abelian : abelian (Zp_units p).
Proof. apply/centsP=> x _ y _; exact: Zp_unit_mulgC. Qed.

Lemma Zp_units_expgn : forall (u : Zp_unit p) n,
  u ^+ n = inZp (valP p) (u ^ n) :> 'I_p.
Proof.
move=> u n; apply: val_inj => /=; elim: n => [|n IHn] //.
by rewrite expgS /= IHn modn_mulmr.
Qed.

End ZpGroup.

Implicit Arguments Zp_gen [p].

Section ZpRing.

Open Scope ring_scope.

Variable p : nat.
Hypothesis lt1p : 1 < p.
Let lt0p := ltnW lt1p.

Lemma Zp_nontriv : Zp1 lt0p <> Zp0 lt0p.
Proof. by move/eqP; rewrite /eqd /= modn_small. Qed.

Canonical Structure Zp_basic_ring :=
  @Ring.Basic (Zp_additive_group_def lt0p) _ _
    (Zp_mulA _) (Zp_mul1z _) (Zp_mulz1 _) (Zp_mul_addl _) (Zp_mul_addr _)
    Zp_nontriv.

Canonical Structure Zp_ring := @Ring.Commutative Zp_basic_ring (Zp_mulC _).

Lemma Zp_nat : forall n, n%:Zp_ring = inZp lt0p n.
Proof.
move=> n; rewrite [n%:_]Zp_mulrn; apply: val_inj.
by rewrite /= modn_mulml mul1n.
Qed.

End ZpRing.

(* Field structure for primes. *)

Section PrimeField.

Open Scope ring_scope.

Variable p : nat.
Hypothesis pr_p : prime p.
Let lt1p := prime_gt1 pr_p.

Canonical Structure Fp_ring := Zp_ring lt1p.

Implicit Type x : Fp_ring.

Lemma Fp_coprime : forall x, x != 0 -> coprime p x.
Proof. by move=> x nzx; rewrite prime_coprime // gtnNdvd ?lt0n. Qed.

Lemma Fp_mulVz : forall x,
  x <> 0 -> (Zp_inv (ltnW lt1p) x : Fp_ring) * x = 1.
Proof. move=> x; move/eqP; move/Fp_coprime=> co_p_x; exact: Zp_mulVz. Qed.

Definition Fp_field := @Field.Field Fp_ring _ Fp_mulVz.

End PrimeField.

