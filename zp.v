(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of the additive group Zp                               *)
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

(*--------------------------------------------------------------------*)
(*|                           unit                                   |*)
(*--------------------------------------------------------------------*)

Definition zp0: fzp p := (Ordinal (pos_natP p)).
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
(*|                           addition                                |*)
(*--------------------------------------------------------------------*)
Definition add_zp : fzp p -> fzp p -> fzp p.
intros [x1 Hx1] [y1 Hy1].
exists (modn (x1 + y1) p).
by rewrite ltn_mod.
Defined.

Lemma unit_zp: forall x, add_zp zp0 x = x.
Proof. case=> x Hx; apply: val_inj; exact: modn_small. Qed.

Lemma invP_zp : forall x, add_zp (inv_zp x) x = zp0.
Proof.
case=> x Hx; apply: val_inj => /=.
by rewrite -{2}(modn_small Hx) // modn_add2m addnC subnK ?modnn // ltnW.
Qed.

Lemma mulP_zp : forall x1 x2 x3, 
  add_zp x1 (add_zp x2 x3) = add_zp (add_zp x1 x2) x3.
Proof.
move => [x1 Hx1] [x2 Hx2] [x3 Hx3]; apply: val_inj => /=.
by rewrite -{1}(modn_small Hx1) // -{2}(modn_small Hx3) // !modn_add2m addnA.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the Zp as an additive group                          *)
(*                                                                     *)
(***********************************************************************)

Canonical Structure zp_pre_group := Eval hnf in
  [baseFinGroupType of fzp p by mulP_zp, unit_zp & invP_zp].

Canonical Structure zp_group := FinGroupType invP_zp.

Open Scope group_scope.

Lemma mul_zpC : forall x y : zp_group, commute x y.
Proof. by case=> [n ltnp] [m ltmp]; apply: val_inj; rewrite /= addnC. Qed.

Lemma card_zp: #|zp_group| = p.
Proof. exact: card_ord. Qed.

End Zp.

Unset Implicit Arguments.
