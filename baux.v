(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.

Lemma eqb_imp: forall P  Q:bool, (P -> Q) -> (Q -> P) -> P = Q.
by case; case => //= Hx1 Hx2; first case Hx1 => //=; case Hx2.
Qed.

Definition wb (a : bool) : {b : bool | a = b} :=
   match a as b return a = b ->  ({b' : bool | a = b'}) with
      true => fun (h : a = true) => exist (fun b' => a = b') true h
     | false => fun (h : a = false) => exist (fun b' => a = b') false h
   end (refl_equal a).
