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
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import groups.
Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section Zp.

Variable p: nat.

Hypothesis Hp: 0 < p.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the finite set {0, 1, 2, ..., p - 1}                 *)
(*                                                                     *)
(***********************************************************************)

Definition fzp := ordinal p.

(*--------------------------------------------------------------------*)
(*|                           unit                                   |*)
(*--------------------------------------------------------------------*)

Definition zp0: fzp := @EqSig _ (fun m => m < p)  _ Hp.

(*--------------------------------------------------------------------*)
(*|                           inverse                                |*)
(*--------------------------------------------------------------------*)
Definition inv_zp: fzp -> fzp.
intros [x1 Hx1].
apply: (@EqSig _  _ (modn (p - x1) p) _).
by rewrite ltn_mod.
Defined.

(*--------------------------------------------------------------------*)
(*|                           addition                                |*)
(*--------------------------------------------------------------------*)
Definition add_zp: fzp -> fzp -> fzp.
intros [x1 Hx1] [y1 Hy1].
apply: (@EqSig _  _ (modn (x1 + y1) p) _).
by rewrite ltn_mod.
Defined.

Lemma unit_zp: forall x, add_zp zp0 x = x.
Proof.
move => [x Hx]; rewrite /zp0 /= add0n.
apply/val_eqP => /=.
by rewrite modn_small.
Qed.

Lemma invP_zp : forall x, add_zp (inv_zp x) x = zp0.
Proof.
move => [x Hx]; apply/val_eqP => /=.
rewrite -{2}(modn_small Hx) // modn_add 
        addnC leq_add_sub ?modnn //.
by apply ltnW.
Qed.

Lemma mulP_zp : forall x1 x2 x3, 
  add_zp x1 (add_zp x2 x3) = add_zp (add_zp x1 x2) x3.
move => [x1 Hx1] [x2 Hx2] [x3 Hx3]; apply/val_eqP => /=.
by rewrite -{1}(modn_small Hx1) // -{2}(modn_small Hx3) // 
   !modn_add addnA.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the Zp as an additive group                          *)
(*                                                                     *)
(***********************************************************************)

Definition zp_group := FinGroupType unit_zp invP_zp mulP_zp.

Lemma card_zp: card (setA zp_group) = p.
exact: card_ordinal.
Qed.

End Zp.


Unset Implicit Arguments.
