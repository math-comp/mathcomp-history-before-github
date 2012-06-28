(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import fintype bigop finset prime fingroup ssralg finalg cyclic abelian.
Require Import tuple finfun choice matrix vector falgebra fieldext separable.
Require Import pgroup poly polydiv galois morphism mxabelem zmodp.

(******************************************************************************)
(*  A few lemmas about finite fields                                          *)
(*                                                                            *)
(*              finChar F == the characteristic of a finFieldType F           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope group_scope.
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
by rewrite -natrM -zmodXgE -expg_mod_order -[X in (_ %% X)%N]Zp_cast.
Qed.

Canonical Zpm_additive := Additive Zpm_is_rmorph.
Canonical Zpm_rmorph := RMorphism Zpm_is_rmorph.

Lemma ZpmMn a n : (@Zpm R a n) = a *+ n.
Proof. by apply: zmodXgE. Qed.

Lemma finRing_nontriv : [set: R]%G != 1%G.
Proof.
apply/trivgPn.
exists 1; first by rewrite inE.
by apply: oner_neq0.
Qed.

Lemma finRing_card_gt1 : 1 < #|R|.
Proof. by rewrite -cardsT (cardG_gt1 [set: R]) finRing_nontriv. Qed.

End FinRing.

Section FinField.

Variable (F : finFieldType).

Definition finChar : nat := pdiv #|F|.

Lemma finChar_prime : prime finChar.
Proof. by apply: pdiv_prime; apply finRing_card_gt1. Qed.

Lemma finField_abelem : (finChar.-abelem [set: F])%g.
Proof.
have : (exponent [set: F])%:R == (0 : F).
  by rewrite -zmodXgE expg_exponent // inE.
case/(natf0_char (exponent_gt0 _)) => p Hp.
have p_prime := charf_prime Hp.
have HpF : p.-abelem [set: F].
  apply/abelemP; first done.
  split => [|x _]; first by apply: zmod_abelian.
  by rewrite zmodXgE mulrn_char.
rewrite /finChar -cardsT -(card_abelem_rV HpF (finRing_nontriv F)) card_matrix.
by rewrite card_Fp // pdiv_pfactor.
Qed.

Lemma finField_unit_card : #|[set: {unit F}]| = #|F|.-1.
Proof.
by rewrite -(cardC1 0) cardsT card_sub; apply: eq_card => x; rewrite unitfE.
Qed.

(* fermat's little theorem *)
Lemma finField_expf_card (x : F) : x ^+ #|F| = x.
Proof.
rewrite -cardsT -(prednK (cardG_gt0 [set: F])) cardsT -finField_unit_card.
apply/eqP.
rewrite exprS -subr_eq0 -[X in - X]mulr1 -mulrBr mulf_eq0.
case: (boolP (x == 0)) => [//|].
rewrite /= subr_eq0 -unitfE => Hx.
rewrite -[x](SubK [subType of {unit F}] Hx).
rewrite -val_unitX -val_unit1 (inj_eq (val_inj)).
by rewrite -order_dvdn order_dvdG ?inE.
Qed.

Lemma finField_genPoly : 'X ^+ #|F| - 'X = \prod_x ('X - x%:P) :> {poly F}.
Proof.
apply/eqP.
rewrite -eqp_monic; last first.
- by apply: monic_prod => i _; apply: monicXsubC.
- rewrite monicE lead_coefDl -?monicE ?monicXn //.
  by rewrite size_opp size_polyXn size_polyX ltnS finRing_card_gt1.
- rewrite eqp_sym -dvdp_size_eqp.
    rewrite size_prod_XsubC /index_enum -enumT -cardT /=.
    rewrite size_addl ?size_polyXn //.
    by rewrite size_opp size_polyX ltnS finRing_card_gt1.
  apply: uniq_roots_dvdp; last first.
    by rewrite uniq_rootsE /index_enum -enumT enum_uniq.
  apply/allP => x _.
  by rewrite rootE !(hornerE, hornerXn) finField_expf_card subrr.
Qed.

Lemma finField_order (x : F) : x != 0 -> #[x]%g = finChar.
Proof. by apply: (abelem_order_p finField_abelem); rewrite inE. Qed.

Lemma finCharP : finChar \in [char F].
Proof.
rewrite inE finChar_prime.
by rewrite -zmodXgE -order_dvdn finField_order ?dvdnn ?oner_neq0.
Qed.

Lemma finField_pgroup : finChar.-group [set: F].
Proof. by apply: abelem_pgroup; apply: finField_abelem. Qed.

Lemma finField_card : #|F| = (finChar ^ 'dim [set: F])%N.
Proof.
rewrite (dim_abelemE finField_abelem) ?finRing_nontriv // -cardsT.
by apply: (card_pgroup finField_pgroup).
Qed.

End FinField.

Module PrimeFieldExt.

Section PrimeFieldExt.
Variable (F : finFieldType).

Definition scale (a : 'F_(finChar F)) (x : F) := a%:R * x.

Lemma scaleA a b x : scale a (scale b x) = scale (a * b) x.
Proof.
move: a b.
rewrite /scale pdiv_id ?finChar_prime // -(finField_order (oner_neq0 _)).
move => a b.
by rewrite -!ZpmMn rmorphM mulrA.
Qed.

Lemma scale1 : left_id 1 scale.
Proof. by move => a; rewrite /scale mul1r. Qed.

Lemma scaleDr : right_distributive scale +%R.
Proof. by move => a x y /=; rewrite /scale mulrDr. Qed.

Lemma scaleDl v : {morph scale^~ v: a b / a + b}.
Proof.
rewrite /scale pdiv_id ?finChar_prime //= -(finField_order (oner_neq0 _)).
move => a b /=.
by rewrite -!ZpmMn -mulrDl -rmorphD.
Qed.

Definition scaleLmodMixin := LmodMixin scaleA scale1 scaleDr scaleDl.

Canonical ZpmodType :=
  Eval hnf in LmodType 'F_(finChar F) F scaleLmodMixin.
Canonical ZpfinmodType := Eval hnf in [finLmodType 'F_(finChar F) of F].

Lemma scaleAl : GRing.Lalgebra.axiom ( *%R : F -> _).
Proof. by move => a x y; rewrite -[a *: (x * y)]/(a%:R * (x * y)) mulrA. Qed.
Canonical ZplalgType := Eval hnf in LalgType 'F_(finChar F) F scaleAl.
Canonical ZpfinlalgType := Eval hnf in [finLalgType 'F_(finChar F) of F].

Lemma scaleAr : GRing.Algebra.axiom ZplalgType.
Proof.
move => a x y.
rewrite -[a *: (x * y)]/(a%:R * (x * y)).
by rewrite mulrC -mulrA; congr (_ * _); rewrite mulrC.
Qed.
Canonical ZpalgType := Eval hnf in AlgType 'F_(finChar F) F scaleAr.
Canonical ZpfinAlgType := Eval hnf in [finAlgType 'F_(finChar F) of F].
Canonical ZpunitAlgType := Eval hnf in [unitAlgType 'F_(finChar F) of F].
Canonical ZpfinUnitAlgType := Eval hnf in [finUnitAlgType 'F_(finChar F) of F].

Lemma Zp_vectAxiom : Vector.axiom ('dim [set: F]) ZpmodType.
Proof.
have /isog_isom /= [f /isomP [/injmP Hfinj Hfim]] :=
  isog_abelem_rV (finField_abelem F) (finRing_nontriv F).
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

Definition Zp_vectMixin : Vector.mixin_of ZpmodType :=
  Vector.Mixin Zp_vectAxiom.
Canonical ZpvectType := Eval hnf in VectType 'F_(finChar F) F Zp_vectMixin.
Canonical ZpfalgType := Eval hnf in [FalgType 'F_(finChar F) of F].
Canonical ZpfieldExtType :=
  @FieldExt.Pack _ (Phant 'F_(finChar F)) F
    (let cF := GRing.Field.class F in
     @FieldExt.Class _ F (Falgebra.class ZpfalgType) cF cF cF) F.

Fact Zp_splittingFieldAxiom : SplittingField.axiom ZpfieldExtType.
Proof.
exists ('X ^+ #|F| - 'X); first by rewrite rpredB ?rpredX // polyOverX.
exists (index_enum F); first by rewrite finField_genPoly eqpxx.
apply:subv_anti; rewrite subvf /=.
apply/subvP => x _.
apply: seqv_sub_adjoin.
rewrite /index_enum -enumT.
by apply: mem_enum.
Qed.

Canonical ZpsplittingFieldType :=
  Eval hnf in SplittingFieldType 'F_(finChar F) F Zp_splittingFieldAxiom.

End PrimeFieldExt.

Module Exports.
Canonical ZpmodType.
Canonical ZpfinmodType.
Canonical ZplalgType.
Canonical ZpfinlalgType.
Canonical ZpalgType.
Canonical ZpfinAlgType.
Canonical ZpunitAlgType.
Canonical ZpfinUnitAlgType.
Canonical ZpvectType.
Canonical ZpfalgType.
Canonical ZpfieldExtType.
Canonical ZpsplittingFieldType.
End Exports.
End PrimeFieldExt.

Section FiniteSeparable.

Variable F : finFieldType.
Variable L : fieldExtType F.

Let pCharL : (finChar F) \in [char L].
Proof. by rewrite charLF finCharP. Qed.

Lemma FermatLittleTheorem  (x : L) : x ^+ (#|F| ^ \dim {:L}) = x.
Proof.
pose v2rK := @Vector.InternalTheory.v2rK F L.
pose m1 := CanCountMixin v2rK.
pose m2 := CanFinMixin (v2rK : @cancel _ (CountType L m1) _ _).
pose FL := @FinRing.Field.pack L _ _ id (FinType L m2) _ id.
suff -> : (#|F| ^ \dim {:L})%N = #|FL| by apply: (@finField_expf_card FL).
pose f (x : FL) := [ffun i => coord (vbasis {:L}) i x].
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
(*
Lemma separableFiniteField (K E : {subfield L}) : separable K E.
Proof.
apply/separableP => y _.
rewrite (separableCharp _ _ 0 pCharL) expn1.
rewrite -{1}[y]FermatLittleTheorem finField_card -expnM.
set n := (_ * _)%N.
have /prednK <- : 0 < n.
  by rewrite muln_gt0 adim_gt0.
by rewrite expnS exprM rpredX // memv_adjoin.
Qed.
*)
End FiniteSeparable.

Import PrimeFieldExt.Exports.
Section PrimeFieldExtTheory.

Variable (F : finFieldType).

Lemma finField_dimv_card (U : {vspace [vectType _ of F]}) :
  #|U| = (finChar F ^ \dim U)%N.
Proof.
rewrite -[\dim _]card_ord -[X in (X ^ _)%N]card_Fp ?finChar_prime //.
rewrite -card_ffun /=.
pose g (x : F) := [ffun i => coord (vbasis U) i x].
have /card_in_imset <- : {in U &, injective g}.
  move => a b Ha Hb /ffunP Hg.
  rewrite (coord_vbasis Ha) (coord_vbasis Hb).
  apply: eq_bigr => i _; congr (_ *: _).
  by move: (Hg i); rewrite !ffunE.
apply: eq_card; move => /= f; rewrite inE; apply/idP.
apply/imsetP; exists (\sum_(i < \dim U) f i *: (vbasis U)`_i).
  apply: rpred_sum => i _.
  by rewrite memvZ // vbasis_mem // -tnth_nth mem_tnth.
apply/ffunP => i.
by rewrite ffunE coord_sum_free // (basis_free (vbasisP U)).
Qed.

Lemma finField_frobenius_generator
  (U : {subfield [splittingFieldType _ of F]}) :
  {x | generator 'Gal(U / 1) x & 
       {in U, x =1 Frobenius_aut (finCharP F)}}.
Proof.
set vF := [splittingFieldType _ of F].
set g := 'Gal(U / 1).
have frob_lin : linear (Frobenius_aut (finCharP F)).
  move => k a b /=.
  by rewrite rmorphD rmorphM  /= Frobenius_autMn rmorph1.
pose f : 'End([vectType _ of F]) :=  linfun (Linear frob_lin).
have Hf : f =1 Frobenius_aut (finCharP F) by apply: lfunE.
have /kAut_gal [x Hx Hfx] : f \is a kAut 1 U.
  rewrite kAutE; apply/andP; split; last first.
    by apply/subvP => _ /memv_imgP [a Ha ->]; rewrite Hf rpredX //.
  apply/kHomP; split.
    move => _ /vlineP [k ->].
    by rewrite Hf rmorphM /= Frobenius_autMn !rmorph1.
  move => a b _ _ /=.
  by rewrite !Hf rmorphM.
exists x; last by move => a Ha; rewrite /= -Hfx ?memvf.
rewrite /generator eq_sym eqEcard cycle_subG Hx.
rewrite dim_fixedField leq_divLR ?field_dimS ?fixedField_bound //.
apply: (@leq_trans (#|<[x]>%g| * (\dim (1%AS : {vspace vF})))); last first.
  by rewrite leq_mul // dimvS // sub1v.
rewrite dimv1 muln1.
rewrite -(leq_exp2l (m:=(finChar F))) ?prime_gt1 ?finChar_prime //.
rewrite -finField_dimv_card.
have HFx0 : (0 < finChar F ^ #[x]%g).
  by rewrite expn_gt0 prime_gt0 // finChar_prime.
have HFx1 : (0 < (finChar F ^ #[x]%g).-1).
  rewrite -ltnS (prednK HFx0) -(exp1n #[x]%g) ltn_exp2r ?order_gt0 //.
  by rewrite prime_gt1 // (finChar_prime F).
have gU : group_set [set x : {unit F} | val x \in U].
  apply/group_setP; split; first by rewrite inE; apply: rpred1.
  by move => a b /=; rewrite !inE => Ha Hb /=; apply: rpredM.
have /cyclicP [a Ha] :=
  cyclicS (subsetT (group gU)) (field_unit_group_cyclic _).
have -> : #|U| = #|group gU|.+1.
  rewrite -(card_imset _ val_inj) (cardD1 0) mem0v add1n; congr _.+1.
  apply: eq_card => b; rewrite inE.
  apply/andP/imsetP.
    rewrite -unitfE; case => Hb HbU.
    exists (Sub b Hb); last done.
    by rewrite inE.
  case => c; rewrite inE => Hc ->.
  by have := valP c; rewrite unitfE.
rewrite -(prednK HFx0) ltnS Ha.
apply/(dvdn_leq HFx1).
rewrite order_dvdn.
apply/eqP/val_inj/(mulrI (valP a)).
rewrite val_unitX -exprS mulr1 prednK //.
suff <- : (x ^+ #[x]%g)%g (val a) = (val a) ^+ ((finChar F) ^ #[x]%g).
  by rewrite expg_order gal_id.
elim: #[x]%g => [|n IH]; first by rewrite gal_id expn0 expr1.
have HaU : val a \in U by have := cycle_id a; rewrite -Ha inE.
by rewrite expgSr galM // comp_lfunE IH -Hfx ?rpredX // Hf expnSr exprM.
Qed.

Lemma galoisFiniteField (K E : {subfield [FalgType _ of F]}) : (K <= E)%VS ->
  galois K E.
Proof.
have Hwlog (M : {subfield [FalgType _ of F]}) : galois M fullv.
  have Hnormf := (normalFieldf M).
  apply/and3P; split => //; first by rewrite subvf.
  apply/separableP => y _.
  rewrite (separableCharp _ _ 0 (finCharP _)) expn1.
  rewrite -{1}[y]finField_expf_card finField_card.
  by rewrite expnS exprM rpredX // memv_adjoin.
move => HKE.
move/galois_fixedField: (Hwlog E) <-.
apply: normal_fixedField_galois; first done.
  by apply: galS.
have [x] := finField_frobenius_generator {: [FalgType _ of F]}.
rewrite /generator => /eqP Hx _.
apply: sub_abelian_norm; last by apply: galS.
apply: (abelianS (galS _ (sub1v _))).
rewrite Hx.
apply cycle_abelian.
Qed.

End PrimeFieldExtTheory.
