(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import fintype bigop finset prime fingroup ssralg finalg cyclic abelian.
Require Import tuple finfun choice matrix vector falgebra fieldext separable.
Require Import morphism mxabelem zmodp.

(******************************************************************************)
(*  A few lemmas about finite fields                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.
Import FinRing.Theory.

Section FinRing.

Variable (R : finRingType).

Lemma Zpm_is_rmorph : rmorphism (@Zpm R 1%R).
Proof.
have H1 : 1 < #[1%R:R]%g by rewrite order_gt1 oner_neq0.
repeat split; move => a b /=.
  by rewrite -zmodMgE -zmodVgE morphM ?morphV // mem_Zp.
by rewrite -natrM -zmodXgE -expg_mod_order -[X in _ %% X]Zp_cast.
Qed.

Canonical Zpm_additive := Additive Zpm_is_rmorph.
Canonical Zpm_rmorph := RMorphism Zpm_is_rmorph.

Lemma ZpmMn a n : (@Zpm R a n) = a *+ n.
Proof. by apply: zmodXgE. Qed.

End FinRing.

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
by rewrite zmodXgE -mulr_natl finField_char0 mul0r.
Qed.

Lemma finField_exponent : exponent [set: F] = char.
Proof.
apply/eqP.
rewrite eqn_dvd dvdn_exponent ?inE // andbT.
apply/exponentP.
move => x Hx.
by rewrite zmodXgE -mulr_natl finField_char0 mul0r.
Qed.

Lemma char_abelem_finField : (char.-abelem [set: F])%g.
Proof.
rewrite abelemE; last by apply: finField_char_prime.
by rewrite zmod_abelian finField_exponent dvdnn.
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

Module PrimeFieldExt.

Section PrimeFieldExt.
Variable (F : finFieldType).

Definition primeScale (a : 'F_(char F)) (x : F) := a%:R * x.

Lemma primeScaleA a b x : primeScale a (primeScale b x) = primeScale (a * b) x.
Proof.
move: a b; rewrite /primeScale pdiv_id ?finField_char_prime // => a b.
by rewrite -!ZpmMn rmorphM mulrA.
Qed.

Lemma primeScale1 : left_id 1 primeScale.
Proof. by move => a; rewrite /primeScale mul1r. Qed.

Lemma primeScaleDr : right_distributive primeScale +%R.
Proof. by move => a x y /=; rewrite /primeScale mulrDr. Qed.

Lemma primeScaleDl v : {morph primeScale^~ v: a b / a + b}.
Proof.
rewrite /primeScale pdiv_id ?finField_char_prime //= => a b.
by rewrite -!ZpmMn rmorphD mulrDl.
Qed.

Definition primeScaleLmodMixin :=
  LmodMixin primeScaleA primeScale1 primeScaleDr primeScaleDl.
Canonical finField_ZpmodType :=
  Eval hnf in LmodType 'F_(char F) F primeScaleLmodMixin.
Canonical finField_ZpfinmodType := Eval hnf in [finLmodType 'F_(char F) of F].

Lemma primeScaleAl : GRing.Lalgebra.axiom ( *%R : F -> _).
Proof. by move => a x y; rewrite -[a *: (x * y)]/(a%:R * (x * y)) mulrA. Qed.
Canonical finField_ZplalgType :=
  Eval hnf in LalgType 'F_(char F) F primeScaleAl.
Canonical finField_ZpfinlalgType := Eval hnf in [finLalgType 'F_(char F) of F].

Lemma primeScaleAr : GRing.Algebra.axiom finField_ZplalgType.
Proof.
move => a x y.
rewrite -[a *: (x * y)]/(a%:R * (x * y)).
by rewrite mulrC -mulrA; congr (_ * _); rewrite mulrC.
Qed.
Canonical finField_ZpalgType := Eval hnf in AlgType 'F_(char F) F primeScaleAr.
Canonical finField_ZpfinAlgType := Eval hnf in [finAlgType 'F_(char F) of F].
Canonical finFeild_ZpunitAlgType := Eval hnf in [unitAlgType 'F_(char F) of F].
Canonical finField_ZpfinUnitAlgType :=
  Eval hnf in [finUnitAlgType 'F_(char F) of F].

Fact finField_Zp_vectMixin : Vector.mixin_of finField_ZpmodType.
Proof.
exists ('dim [set: F]).
have nontrivF : [set: F]%G != 1%G.
  apply/trivgPn.
  exists 1; first by rewrite inE.
  by apply: oner_neq0.
have /isog_isom /= [f /isomP [/injmP Hfinj Hfim]] :=
  isog_abelem_rV (char_abelem_finField F) nontrivF.
exists [eta f].
  move => a x y.
  rewrite -zmodMgE morphM ?inE // zmodMgE.
  rewrite -[a *: x]/(a%:R * x) mulr_natl.
  rewrite -zmodXgE morphX ?inE // zmodXgE.
  by rewrite -scaler_nat natr_Zp.
suff HrV y : y \in image f [set : F].
  exists (fun y => iinv (HrV y)) => /= x; last by apply: f_iinv.
  by apply: in_iinv_f.
have /= := in_setT y.
rewrite -Hfim.
case/morphimP => x _ _ ->.
by apply: image_f; apply: in_setT.
Qed.

Canonical finField_ZpvectType :=
  Eval hnf in VectType 'F_(char F) F finField_Zp_vectMixin.
Canonical finField_ZpfalgType := Eval hnf in [FalgType 'F_(char F) of F].

Canonical finField_ZpfieldExtType :=
  Eval hnf in @FieldExt.Pack _ (Phant 'F_(char F)) F
   (let: c := FinRing.Field.class F in
    let: fMixin := 
      (let: GRing.Field.Class _ fm as c' := c : GRing.Field.class_of F return GRing.Field.mixin_of (GRing.UnitRing.Pack c' _) in fm) in
    let: idAxiom :=
      (let: GRing.IntegralDomain.Class _ ida as c' := c : GRing.IntegralDomain.class_of F return GRing.IntegralDomain.axiom (GRing.Ring.Pack c' _)  in ida) in
    let: crAxiom :=
      (let: GRing.ComRing.Class _ cra as c' := c : GRing.ComRing.class_of F return commutative (GRing.Ring.mul c') in cra) in
    (@FieldExt.Class _ F (Falgebra.class finField_ZpfalgType) crAxiom idAxiom fMixin)
   ) F.

End PrimeFieldExt.
End PrimeFieldExt.

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
