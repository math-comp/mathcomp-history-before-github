(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import fintype bigop finset prime fingroup ssralg finalg cyclic.

(******************************************************************************)
(*  A few lemmas about finite fields                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.

Section FinField.

Variable (F : finFieldType).

Lemma unit_card : #|[set: {unit F}]| = #|F|.-1.
Proof.
rewrite -(cardC1 0) -(card_imset _ val_inj).
apply: eq_card => x.
rewrite -[_ \in predC1 0]unitfE.
apply/imsetP/idP.
 by case => [[y Hy]] _ -> /=.
move => Hx.
exists (Sub _ Hx); first by rewrite inE.
by rewrite SubK.
Qed.

Lemma unit_cyclic : cyclic [set: {unit F}].
Proof.
have Hf1 : forall x : {unit F}, FinRing.uval x = 1 <-> x = 1%g.
 move => y; split; last by move ->.
 by move => Hy; apply: val_inj.
have HfM : {morph (@FinRing.uval F) : u v  / (u * v)%g >-> u * v} by done.
by apply: field_mul_group_cyclic (fun a b _ _ => HfM a b) (fun a _ => Hf1 a).
Qed.

Lemma unit_finField_expgn (u : {unit F}) n :
  val (u ^+ n)%g = val u ^+ n.
Proof.
elim: n => [//|n IHn].
rewrite expgS exprS -IHn.
by case: {IHn} u (u ^+ n)%g.
Qed.

Lemma expf_card (x : F) : x ^+ #|F| = x.
Proof.
have/prednK <- : (0 < #|F|) by apply/card_gt0P; exists 0.
rewrite -unit_card.
apply/eqP.
rewrite exprS -subr_eq0 -[X in - X]mulr1 -mulr_subr mulf_eq0 -[_ == _]negbK.
case Hx0 : (x != 0); last done.
move/idP : Hx0.
rewrite /= subr_eq0 -unitfE => Hx.
rewrite -[x](SubK [subType of {unit F}] Hx) -unit_finField_expgn.
set x' := (Sub _ Hx).
have/order_dvdG : x' \in [set: {unit F}] by rewrite inE.
rewrite order_dvdn.
by move/eqP ->.
Qed.

End FinField.
