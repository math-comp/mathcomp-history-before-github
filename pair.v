(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Pair.

Open Scope group_scope.

Variable (V: eqType).

Fixpoint pairn (n: nat): eqType :=
  if n is S n1 then (prod_eqType V (pairn n1)) 
 else V.

End Pair.

Unset Implicit Arguments.
