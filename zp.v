(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of the additive group and ring Zp                       *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import groups.
Require Import div.
Require Import ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation fzp := ordinal (only parsing).

Section Zp.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the finite set {0, 1, 2, ..., p - 1}                 *)
(*                                                                     *)
(***********************************************************************)

Variable p : pos_nat.
Hypothesis non_trivial_p : 1 < p.

(*--------------------------------------------------------------------*)
(*|                           unit                                   |*)
(*--------------------------------------------------------------------*)

Definition zp0: fzp p := (Ordinal (pos_natP p)).
Definition zp1: fzp p := (Ordinal non_trivial_p).
(* @EqSig _ (fun m => m < p)  _ Hp. *)

(*--------------------------------------------------------------------*)
(*|                           inverse                                |*)
(*--------------------------------------------------------------------*)
Definition inv_zp : fzp p -> fzp p.
intros [x1 Hx1].
exists (modn (p - x1) p).
by rewrite ltn_mod.
Defined.

(*--------------------------------------------------------------------*)
(*|                           addition                               |*)
(*--------------------------------------------------------------------*)
Definition add_zp : fzp p -> fzp p -> fzp p.
intros [x1 Hx1] [y1 Hy1].
exists (modn (x1 + y1) p).
by rewrite ltn_mod.
Defined.

Lemma zp_add0P: forall x, add_zp zp0 x = x.
Proof. case=> x Hx. apply: val_inj. rewrite /=.
exact: modn_small.
Qed.

Lemma zp_oppP : forall x, add_zp (inv_zp x) x = zp0.
Proof.
case=> x Hx; apply: val_inj => /=.
by rewrite -{2}(modn_small Hx) // modn_add2m addnC subnK ?modnn // ltnW.
Qed.

Lemma zp_addA : forall x1 x2 x3, 
  add_zp x1 (add_zp x2 x3) = add_zp (add_zp x1 x2) x3.
Proof.
move => [x1 Hx1] [x2 Hx2] [x3 Hx3]; apply: val_inj => /=.
by rewrite -{1}(modn_small Hx1) // -{2}(modn_small Hx3) // !modn_add2m addnA.
Qed.

Lemma zp_addC : forall x1 x2,
  add_zp x1 x2 = add_zp x2 x1.
Proof.
move => [x1 Hx1] [x2 Hx2].
apply: val_inj => /=.
by rewrite addnC.
Qed.

(*--------------------------------------------------------------------*)
(*|                           Multiplication                         |*)
(*--------------------------------------------------------------------*)

Definition mul_zp : fzp p -> fzp p -> fzp p.
move=>[x1 Hx1] [y1 Hy1] ; exists (modn (x1 * y1) p).
by rewrite ltn_mod.
Defined.

Lemma zp_mul1P: forall x, mul_zp zp1 x = x.
Proof.
case=> x Hx. apply: val_inj ; rewrite /= mul1n.
by apply:(modn_small Hx).
Qed.

Lemma zp_mulC : forall x1 x2,
  mul_zp x1 x2 = mul_zp x2 x1.
Proof.
move=>[x1 Hx1] [x2 Hx2] ; apply: val_inj => /=.
by rewrite mulnC.
Qed.

Lemma zp_mulP1:forall x, mul_zp x zp1 = x.
Proof.
move=>x ; rewrite (zp_mulC x zp1).
by apply:zp_mul1P.
Qed.

Lemma zp_nontriv: zp1 <> zp0.
Proof. by []. Qed.

Lemma zp_mulA : forall x1 x2 x3, 
  mul_zp x1 (mul_zp x2 x3) = mul_zp (mul_zp x1 x2) x3.
Proof.
move=>[x1 Hx1] [x2 Hx2] [x3 Hx3] ; apply: val_inj => /=.
by rewrite -{1}(modn_small Hx1) // -{2}(modn_small Hx3) // !modn_mul2m mulnA.
Qed.

Lemma zp_mul_addr : forall p1 p2 p3, mul_zp p1 ( add_zp p2 p3) = add_zp (mul_zp p1 p2) (mul_zp p1 p3).
Proof.
move=>[p1 Hp1] [p2 Hp2] [p3 Hp3] ; apply: val_inj=> /=.
by rewrite modn_mulmr modn_add2m -muln_addr.
Qed.

Lemma zp_mul_addl : forall p1 p2 p3, mul_zp ( add_zp p1 p2) p3 = add_zp (mul_zp p1 p3) (mul_zp p2 p3).
Proof.
move=>[p1 Hp1] [p2 Hp2] [p3 Hp3] ; apply: val_inj=> /=.
by rewrite modn_mulml modn_add2m -muln_addl.
Qed.

(***********************************************************************)
(*                                                                     *)
(*      Definition of Zp as an additive group                          *)
(*                                                                     *)
(***********************************************************************)

Canonical Structure zp_pre_group := Eval hnf in
  [baseFinGroupType of fzp p by zp_addA, zp_add0P & zp_oppP].

Canonical Structure zp_group := FinGroupType zp_oppP.

Canonical Structure zp_additive_group :=
  Ring.AdditiveGroup zp_addA zp_addC zp_add0P zp_oppP.

Open Scope group_scope.

Lemma mul_zpC : forall x y : zp_group, commute x y.
Proof. by case=> [n ltnp] [m ltmp]; apply: val_inj; rewrite /= addnC. Qed.

Lemma card_zp: #|zp_group| = p.
Proof. exact: card_ord. Qed.

Close Scope group_scope.

(***********************************************************************)
(*                                                                     *)
(*      Definition of Zp as a ring                                     *)
(*                                                                     *)
(***********************************************************************)

Canonical Structure zp_basic_ring :=
  Ring.Basic zp_mulA zp_mul1P zp_mulP1
             zp_mul_addl zp_mul_addr zp_nontriv.

End Zp.

Unset Implicit Arguments.
