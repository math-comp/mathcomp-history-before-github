(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice div.
Require Import fintype bigops finset prime groups ssralg.

(***********************************************************************)
(*  Definition of the additive group and ring Zp, represented as 'I_p  *)
(***********************************************************************)
(* Definitions:                                                        *)
(* From fintype.v:                                                     *)
(*   'I_p == the subtype of integers less than p, taken here as the    *)
(*           type of integers mod p.                                   *)
(* This file:                                                          *)
(*   inZp p_gt0 == the natural projection from nat into the integers   *)
(*                 mod p (represented as 'I_p), when p_gt0 is a proof  *)
(*                 that p > 0.                                         *)
(* the operations:                                                     *)
(*   Zp0 == neutral element for addition                               *)
(*   Zp1 == neutral element for multiplication                         *)
(*   Zp_opp == inverse function for addition                           *)
(*   Zp_add == addition                                                *)
(*   Zp_mul == multiplication                                          *)
(*   Zp_inv == inverse function for multiplication                     *)
(*  Zp_finGroupType pp == the canonical finGroupType on 'I_pp, when pp *)
(*                        is a pos_nat.                                *)
(*  Zp_ring lt1p == the (commutative, unitary) ring structure on 'I_p, *)
(*                  given lt1p : 1 < p                                 *)
(*  Fp_field pr_p == the field structure on 'I_p, given pr_p : prime p *)
(*     Zp p    == the set (and additive group) of all integers mod p.  *)
(*  Zp_unit p  == the subtype of all units in the ring 'I_p            *)
(*  Zp_units p == the set (and multiplicative group) of all 'I_p units *)
(* operations in Zp_units:                                             *)
(* Zp_unit_one == the neutral element for multiplication in Zp_unit    *)
(* Zp_unit_inv u == the inverse function for multiplication in Zp_unit *)
(* Zp_unit_mul u v == multiplication in Zp_unit                        *)
(* We show that Zp and Zp_units are abelian, and compute their orders. *)
(***********************************************************************)

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
Hypothesis p_gt0 : 0 < p.

Definition Zp : {set 'I_p} := setT.

Implicit Types x y z : 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := Ordinal (ltn_pmod i p_gt0).
Lemma modZp : forall x, x %% p = x.
Proof. by move=> x; rewrite modn_small ?ltn_ord. Qed.
Lemma valZpK : forall x, inZp x = x.
Proof. by move=> x; apply: val_inj; rewrite /= modZp. Qed.

(* Operations *)
Definition Zp0 := Ordinal p_gt0.
Definition Zp1 := inZp 1.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).
Definition Zp_mul x y := inZp (x * y).
Definition Zp_inv x := if coprime p x then inZp (egcdn x p).1 else x.

(* Units subtype *)

Inductive Zp_unit : predArgType := ZpUnit x of coprime p x.

Implicit Types u v : Zp_unit.

Coercion Zp_unit_val u := let: ZpUnit x _ := u in x.

Canonical Structure Zp_unit_subType :=
  Eval hnf in [subType for Zp_unit_val by Zp_unit_rect].
Definition Zp_unit_eqMixin := Eval hnf in [eqMixin of Zp_unit by <:].
Canonical Structure Zp_unit_eqType := Eval hnf in EqType Zp_unit_eqMixin.
Definition Zp_unit_choiceMixin := [choiceMixin of Zp_unit by <:].
Canonical Structure Zp_unit_choiceType :=
  Eval hnf in ChoiceType Zp_unit_choiceMixin.
Definition Zp_unit_countMixin := [countMixin of Zp_unit by <:].
Canonical Structure Zp_unit_countType :=
  Eval hnf in CountType Zp_unit_countMixin.
Canonical Structure Zp_unit_subCountType :=
  Eval hnf in [subCountType of Zp_unit].
Definition Zp_unit_finMixin := [finMixin of Zp_unit by <:].
Canonical Structure Zp_unit_finType := Eval hnf in FinType Zp_unit_finMixin.
Canonical Structure Zp_unit_subFinType := Eval hnf in [subFinType of Zp_unit].

Definition Zp_units : {set Zp_unit} := setT.

(* Additive group structure. *)

Lemma Zp_add0z : left_id Zp0 Zp_add.
Proof. exact: valZpK. Qed.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Proof.
by move=> x; apply: val_inj; rewrite /= modn_addml subnK ?modnn // ltnW.
Qed.

Lemma Zp_addA : associative Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_addml modn_addmr addnA.
Qed.

Lemma Zp_addC : commutative Zp_add.
Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.

Definition Zp_groupMixin := FinGroup.Mixin Zp_addA Zp_add0z Zp_addNz.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.

(* Ring operations *)

Lemma Zp_mul1z : left_id Zp1 Zp_mul.
Proof. by move=> x; apply: val_inj; rewrite /= modn_mulml mul1n modZp. Qed.

Lemma Zp_mulC : commutative Zp_mul.
Proof. by move=> x y; apply: val_inj; rewrite /= mulnC. Qed.

Lemma Zp_mulz1 : right_id Zp1 Zp_mul.
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
move=> x co_p_x; apply: val_inj; rewrite /Zp_inv co_p_x /= modn_mulml.
by rewrite -(chinese_modl co_p_x 1 0) /chinese addn0 mul1n mulnC.
Qed.

Lemma Zp_mulzV : forall x, coprime p x -> Zp_mul x (Zp_inv x) = Zp1.
Proof. by move=> x Ux; rewrite /= Zp_mulC Zp_mulVz. Qed.

Lemma Zp_intro_unit : forall x y, Zp_mul y x = Zp1 -> coprime p x.
Proof.
move=> x y [yx1]; have:= coprimen1 p.
by rewrite -coprime_modr -yx1 coprime_modr coprime_mulr; case/andP.
Qed.

Lemma Zp_inv_out : forall x, ~~ coprime p x -> Zp_inv x = x.
Proof. by rewrite /Zp_inv => x; move/negPf->. Qed.

Lemma Zp_mulrn : forall x n,
  ((x : ZmodType Zp_zmodMixin) *+ n)%R = inZp (x * n).
Proof.
move=> x n; apply: val_inj => /=.
elim: n => [|n IHn]; first by rewrite muln0 modn_small.
by rewrite !GRing.mulrS /= IHn modn_addmr mulnS.
Qed.

(* Multiplicative (unit) group. *)

Lemma Zp_unit_one_proof : coprime p Zp1.
Proof. by rewrite coprime_modr coprimen1. Qed.

Lemma Zp_unit_mul_proof : forall u v, coprime p (Zp_mul u v).
Proof. by move=> u v; rewrite coprime_modr coprime_mulr (valP u) (valP v). Qed.

Lemma Zp_unit_inv_proof : forall u, coprime p (Zp_inv u).
Proof.
move=> u; have:= Zp_unit_one_proof; rewrite -(Zp_mulVz (valP u)).
by rewrite coprime_modr coprime_mulr; case/andP.
Qed.

Definition Zp_unit_one := ZpUnit Zp_unit_one_proof.

Definition Zp_unit_inv u := ZpUnit (Zp_unit_inv_proof u).

Definition Zp_unit_mul u v := ZpUnit (Zp_unit_mul_proof u v).

Lemma Zp_unit_mul1g : left_id Zp_unit_one Zp_unit_mul.
Proof. move=> u; apply: val_inj; exact: Zp_mul1z. Qed.

Lemma Zp_unit_mulVg : left_inverse Zp_unit_one Zp_unit_inv Zp_unit_mul.
Proof. move=> u; apply: val_inj; exact: Zp_mulVz (valP u). Qed.

Lemma Zp_unit_mulA : associative Zp_unit_mul.
Proof. move=> u v w; apply: val_inj; exact: Zp_mulA. Qed.

Lemma Zp_unit_mulC : commutative Zp_unit_mul.
Proof. move=> u v; apply: val_inj; exact: Zp_mulC. Qed.

Definition Zp_unit_groupMixin :=
  FinGroup.Mixin Zp_unit_mulA Zp_unit_mul1g Zp_unit_mulVg.

Definition Zp_unit_zmodMixin :=
  ZmodMixin Zp_unit_mulA Zp_unit_mulC Zp_unit_mul1g Zp_unit_mulVg.

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

Canonical Structure Zp_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (Zp_groupMixin (valP p)).
Canonical Structure Zp_finGroupType := FinGroupType (Zp_addNz (valP p)).
Canonical Structure Zp_zmodType :=
  Eval hnf in ZmodType (Zp_zmodMixin (valP p)).
Canonical Structure Zp_group := Eval hnf in [group of Zp p].

Canonical Structure Zp_unit_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (Zp_unit_groupMixin (valP p)).
Canonical Structure Zp_unit_finGroupType :=
  FinGroupType (Zp_unit_mulVg (valP p)).
Canonical Structure Zp_unit_zmodType :=
  Eval hnf in ZmodType (Zp_unit_zmodMixin (valP p)).
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
by rewrite expgS /= IHn expnS modn_mulmr.
Qed.

End ZpGroup.

Implicit Arguments Zp_gen [p].

Section ZpRing.

Open Scope ring_scope.

Variable p : nat.
Hypothesis lt1p : 1 < p.
Let lt0p := ltnW lt1p.

Lemma Zp_nontriv : Zp1 lt0p != Zp0 lt0p.
Proof. by rewrite /eq_op /= modn_small. Qed.

Definition Zp_ringMixin :=
  @ComRingMixin (ZmodType (Zp_zmodMixin lt0p)) _ _
           (Zp_mulA _) (Zp_mulC _) (Zp_mul1z _) (Zp_mul_addl _) Zp_nontriv.

Definition Zp_comRingMixin :
   @commutative (RingType Zp_ringMixin) *%R := Zp_mulC _.

Definition Zp_unitMixin :=
  @ComUnitRingMixin (ComRingType Zp_comRingMixin) (fun i => coprime p i)
   (Zp_inv lt0p) (Zp_mulVz _) (@Zp_intro_unit _ _) (Zp_inv_out _).

Definition Zp_ring := ComUnitRingType Zp_unitMixin.

Lemma Zp_nat : forall n, n%:R = inZp lt0p n :> Zp_ring.
Proof.
by move=> n; apply: val_inj; rewrite [n%:R]Zp_mulrn /= modn_mulml mul1n.
Qed.

End ZpRing.

Lemma ord1 : forall i : 'I_1, i = 0%R.
Proof. case=> [[]] // ?; exact/eqP. Qed.

Lemma lshift_ord1 : forall n (i : 'I_1), lshift n i = 0%R :> 'I_n.+1.
Proof. by move=> n i; apply/eqP; rewrite [i]ord1. Qed.

(* Field structure for primes. *)

Section PrimeField.

Open Scope ring_scope.

Variable p : nat.
Hypothesis pr_p : prime p.
Let lt1p := prime_gt1 pr_p.

Let Fp_ring := ComUnitRingType (Zp_unitMixin lt1p).

Lemma Fp_fieldMixin : GRing.Field.mixin_of Fp_ring.
Proof.
by move=> x nzx; rewrite /GRing.unit /= prime_coprime // gtnNdvd ?lt0n.
Qed.

Definition Fp_idomainMixin := FieldIdomainMixin Fp_fieldMixin.

Definition Fp_field := @FieldType (IdomainType Fp_idomainMixin) Fp_fieldMixin.

End PrimeField.
