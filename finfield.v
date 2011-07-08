(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import fintype bigop finset prime fingroup ssralg finalg cyclic abelian.

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

Lemma finField_card_gt0 : 0 < #|F|.
Proof. by apply/card_gt0P; exists 0. Qed.

Lemma finField_card_gt1 : 1 < #|F|.
Proof.
rewrite -(prednK finField_card_gt0) ltnS -unit_card.
apply/card_gt0P.
by exists 1%g.
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
rewrite -(prednK finField_card_gt0) -unit_card.
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

Definition char : nat := #[1%R : F]%g.

Lemma finField_char : char \in [char F].
Proof.
have Hchar0 : (char%:R == 0 :> F) by rewrite -order_dvdn dvdnn.
case: (natf0_char (order_gt0 _) Hchar0) => [p Hp].
suff/eqP: (char == p) by move ->.
by rewrite eqn_dvd order_dvdn [(_ ^+ _)%g]charf0 // eqxx (dvdn_charf Hp).
Qed.

Lemma finField_char0 : char%:R = 0 :> F.
Proof. apply: (@charf0 F); apply: finField_char. Qed.

Lemma finField_char_prime : prime char.
Proof. apply: (@charf_prime F); apply: finField_char. Qed.

Lemma finField_order (x : F) : x != 0 -> #[x]%g = char.
Proof.
move => Hx.
apply: (nt_prime_order finField_char_prime) => //.
by rewrite FinRing.zmodXgE -mulr_natl finField_char0 mul0r.
Qed.

Lemma finField_exponent : exponent [set: F] = char.
Proof.
apply/eqP.
rewrite eqn_dvd dvdn_exponent ?inE // andbT.
apply/exponentP.
move => x Hx.
by rewrite FinRing.zmodXgE -mulr_natl finField_char0 mul0r.
Qed.

Lemma finField_card : char.-nat #|F|.
Proof.
rewrite -[#|F|](prednK finField_card_gt0).
apply/allP => x.
rewrite (prednK finField_card_gt0).
move: (primes_exponent [set: F]).
rewrite finField_exponent (primes_prime finField_char_prime) cardsT.
move <-.
by rewrite !inE.
Qed.

End FinField.
