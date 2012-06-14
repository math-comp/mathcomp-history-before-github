(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import fintype bigop finset prime fingroup ssralg finalg cyclic abelian.
Require Import tuple finfun choice matrix vector falgebra fieldext separable.

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
exists (FinRing.unit F Hx); first by rewrite inE.
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

Lemma unit_finField_expg (u : {unit F}) n :
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
rewrite exprS -subr_eq0 -[X in - X]mulr1 -mulrBr mulf_eq0 -[_ == _]negbK.
case Hx0 : (x != 0); last done.
move/idP : Hx0.
rewrite /= subr_eq0 -unitfE => Hx.
rewrite -[x](SubK [subType of {unit F}] Hx) -unit_finField_expg.
pose x' := FinRing.unit F Hx.
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

Section FiniteSeparable.

Variable F : finFieldType.
Variable L : fieldExtType F.

Let pCharL : (char F) \in [char L].
Proof. by rewrite charLF finField_char. Qed.

Lemma FermatLittleTheorem  (x : L) : x ^+ (#|F| ^ \dim {:L}) = x.
Proof.
pose v2rK := @Vector.InternalTheory.v2rK F L.
pose m1 := CanCountMixin v2rK.
pose m2 := CanFinMixin (v2rK : @cancel _ (CountType L m1) _ _).
pose FL := @FinRing.Field.pack L _ _ id (FinType L m2) _ id.
suff -> : #|F| ^ \dim {:L} = #|FL| by apply: (@expf_card FL).
pose f (x : FL) := [ffun i => coord (vbasis fullv) i x].
rewrite -[\dim {:L}]card_ord -card_ffun.
have/card_in_image <- : {in FL &, injective f}.
 move => a b Ha Hb /= /ffunP Hab.
 rewrite (coord_vbasis (memvf a)) (coord_vbasis (memvf b)).
 by apply: eq_bigr => i _; have:= Hab i; rewrite !ffunE => ->.
apply: eq_card => g.
rewrite !inE.
symmetry; apply/idP.
apply/mapP.
exists (\sum_i g i *: (vbasis fullv)`_i); first by rewrite mem_enum.
by apply/ffunP => i; rewrite ffunE coord_sum_free // (basis_free (vbasisP _)).
Qed.

Lemma separableFiniteField (K E : {subfield L}) : separable K E.
Proof.
apply/separableP => y _.
rewrite (separableCharp _ _ 0 pCharL) expn1.
rewrite -{1}[y]FermatLittleTheorem.
 case: (p_natP (finField_card F)) => [[|n ->]].
 move/eqP.
 by rewrite expn0 -{1}(subnK (finField_card_gt1 F)) addnC.
rewrite -expnM.
suff -> : (n.+1 * \dim {:L})%N = (n.+1 * \dim {:L}).-1.+1.
 by rewrite expnS exprM rpredX // memv_adjoin.
by rewrite prednK // muln_gt0 adim_gt0.
Qed.

End FiniteSeparable.
