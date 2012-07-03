(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
Require Import fintype bigop finset prime fingroup ssralg finalg cyclic abelian.
Require Import tuple finfun choice matrix vector falgebra fieldext separable.
Require Import pgroup poly polydiv galois morphism mxabelem zmodp.

(******************************************************************************)
(*  A few lemmas about finite fields.                                         *)
(*                                                                            *)
(*              finChar F == the characteristic of a finFieldType F           *)
(*     finFieldExtMixin L == a Finite.mixin_of L when L is a fieldExtType     *)
(*                           over a finField.                                 *)
(*      finFieldExtType L == L, but with a finFieldType structure.            *)
(*    primeFieldExtType F == F, but with an fieldExtType structure, over      *)
(*                           'F_(finChar F)                                   *)
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

Section FinFieldExt.

Variable (F : finFieldType).
Variable (L : fieldExtType F).

Definition finFieldExtMixin : Finite.mixin_of L :=
  let v2rK := @Vector.InternalTheory.v2rK F L in
  CanFinMixin (v2rK : @cancel _ (CountType L (CanCountMixin v2rK)) _ _).

Definition finFieldExtType : finFieldType := FinRing.Field.Pack
   (@FinRing.Field.Class L (GRing.Field.class L) finFieldExtMixin) L.

Lemma finField_splittingField_axiom : SplittingField.axiom L.
Proof.
exists ('X ^+ #|finFieldExtType| - 'X).
  by rewrite rpredB ?rpredX // polyOverX.
exists (index_enum finFieldExtType).
  by rewrite (finField_genPoly finFieldExtType) eqpxx.
apply:subv_anti; rewrite subvf /=.
apply/subvP => x _.
apply: seqv_sub_adjoin.
rewrite /index_enum -enumT.
apply: (mem_enum finFieldExtType).
Qed.

End FinFieldExt.

Section PrimeFieldExt.

Variable (F : finFieldType).

Definition primeFieldExt_type of phant F : Type := F.
Notation F0 := (primeFieldExt_type (Phant (GRing.Field.sort F))).

Canonical primeFieldExt_eqType := [eqType of F0].
Canonical primeFieldExt_choiceType := [choiceType of F0].
Canonical primeFieldExt_finType := [finType of F0].
Canonical primeFieldExt_zmodType := [zmodType of F0].
Canonical primeFieldExt_finZmodType := [finZmodType of F0].
Canonical primeFieldExt_ringType := [ringType of F0].
Canonical primeFieldExt_finRingType := [finRingType of F0].
Canonical primeFieldExt_unitRingType := [unitRingType of F0].
Canonical primeFieldExt_finUnitRingType := [finUnitRingType of F0].
Canonical primeFieldExt_comRingType := [comRingType of F0].
Canonical primeFieldExt_finComRingType := [finComRingType of F0].
Canonical primeFieldExt_comUnitRingType := [comUnitRingType of F0].
Canonical primeFieldExt_finComUnitRingType := [finComUnitRingType of F0].
Canonical primeFieldExt_idomainType := [idomainType of F0].
Canonical primeFieldExt_finIdomainType := [finIdomainType of F0].
Canonical primeFieldExt_fieldType := [fieldType of F0].
Canonical primeFieldExt_finFieldType := [finFieldType of F0].

Definition primeFieldExt_scale (a : 'F_(finChar F)) (x : F0) := a%:R * x.
Local Infix "*Fp:" := primeFieldExt_scale (at level 40).

Lemma primeFieldExt_scaleA a b x : a *Fp: (b *Fp: x) = (a * b) *Fp: x.
Proof.
move: a b.
rewrite /primeFieldExt_scale pdiv_id ?finChar_prime //.
rewrite -(finField_order (oner_neq0 _)).
move => a b.
by rewrite -!ZpmMn rmorphM mulrA.
Qed.

Lemma primeFieldExt_scale1 : left_id 1 primeFieldExt_scale.
Proof. by move => a; rewrite /primeFieldExt_scale mul1r. Qed.

Lemma primeFieldExt_scaleDr : right_distributive primeFieldExt_scale +%R.
Proof. by move => a x y /=; rewrite /primeFieldExt_scale mulrDr. Qed.

Lemma primeFieldExt_scaleDl v : {morph primeFieldExt_scale^~ v: a b / a + b}.
Proof.
rewrite /primeFieldExt_scale pdiv_id ?finChar_prime //=.
rewrite -(finField_order (oner_neq0 _)).
move => a b /=.
by rewrite -!ZpmMn -mulrDl -rmorphD.
Qed.

Definition primeFieldExt_lmodMixin :=
  LmodMixin primeFieldExt_scaleA primeFieldExt_scale1
            primeFieldExt_scaleDr primeFieldExt_scaleDl.
Canonical primeFieldExt_lmodType :=
  LmodType 'F_(finChar F) F0 primeFieldExt_lmodMixin.
Canonical primeFieldExt_finLmodType := [finLmodType 'F_(finChar F) of F0].

Lemma primeFieldExt_scaleAl : GRing.Lalgebra.axiom ( *%R : F0 -> _).
Proof. by move => a x y; rewrite -[a *: (x * y)]/(a%:R * (x * y)) mulrA. Qed.
Canonical primeFieldExt_LalgType :=
  LalgType 'F_(finChar F) F0 primeFieldExt_scaleAl.
Canonical primeFieldExt_finLalgType := [finLalgType 'F_(finChar F) of F0].

Lemma primeFieldExt_scaleAr : GRing.Algebra.axiom primeFieldExt_LalgType.
Proof.
move => a x y.
rewrite -[a *: (x * y)]/(a%:R * (x * y)).
by rewrite mulrC -mulrA; congr (_ * _); rewrite mulrC.
Qed.
Canonical primeFieldExt_algType := 
  AlgType 'F_(finChar F) F0 primeFieldExt_scaleAr.
Canonical primeFieldExt_finAlgType := [finAlgType 'F_(finChar F) of F0].
Canonical primeFieldExt_unitAlgType := [unitAlgType 'F_(finChar F) of F0].
Canonical primeFieldExt_finUnitAlgType := [finUnitAlgType 'F_(finChar F) of F0].

Lemma primeFieldExt_vectAxiom :
  Vector.axiom ('dim [set: F]) primeFieldExt_lmodType.
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

Definition primeFieldExt_vectMixin : Vector.mixin_of primeFieldExt_lmodType :=
  Vector.Mixin primeFieldExt_vectAxiom.
Canonical primeFieldExt_vectType :=
  VectType 'F_(finChar F) F0 primeFieldExt_vectMixin.
Canonical primeFieldExt_falgType := [FalgType 'F_(finChar F) of F0].
Canonical primeFieldExt_fieldExtType :=
  @FieldExt.Pack _ (Phant 'F_(finChar F)) F0
    (let cF := GRing.Field.class F in
     @FieldExt.Class _ F0 (Falgebra.class primeFieldExt_falgType) cF cF cF) F0.

Canonical primeFieldExt_splittingFieldType :=
  SplittingFieldType 'F_(finChar F) F0 (finField_splittingField_axiom _).

Lemma primeFieldExt_dimf : \dim {:[vectType _ of F0]} = 'dim [set: F].
Proof. by rewrite dimvf. Qed.

End PrimeFieldExt.

Notation primeFieldExtType F := (primeFieldExt_type (Phant F)).

Section FinSplittingField.

Variable (F : finFieldType).
Variable (L : splittingFieldType F).
Implicit Types (K E : {subfield L}).

Lemma finField_memv1_subproof (a : L) : (a \in 1%VS) = (a ^+ #|F| == a).
Proof.
apply/vlineP/eqP.
  move => [k ->].
  by rewrite -[k%:A]/(in_alg L k) -rmorphX finField_expf_card.
move => Ha.
have : root (map_poly (in_alg L) ('X ^+ #|F| - 'X)) a.
  rewrite rmorphB /= map_polyXn map_polyX.
  by rewrite rootE !(hornerE, hornerXn) Ha subrr.
have -> : map_poly (in_alg L) ('X ^+ #|F| - 'X) =
          \prod_(c <- [seq b%:A | b <- index_enum F]) ('X - c%:P).
  rewrite finField_genPoly rmorph_prod big_map.
  apply: eq_bigr => b _.
  by rewrite rmorphB /= map_polyX map_polyC.
rewrite root_prod_XsubC.
case/mapP => k _ Hk.
by exists k.
Qed.

Lemma finField_galois_subproof K : galois K {:L}.
Proof.
wlog: K / K = 1%AS.
  move/(_ _ (refl_equal 1%AS)) => Hgal.
  apply: (galoisS _ Hgal).
  by rewrite sub1v subvf.
move => {K} ->.
apply/splitting_galoisField.
exists ('X ^+ #|finFieldExtType L| - 'X); split.
- by rewrite rpredB ?rpredX // polyOverX.
exists (index_enum (finFieldExtType L)).
  by rewrite (finField_genPoly (finFieldExtType L)) eqpxx.
apply: subv_anti; rewrite subvf.
apply/subvP => a _.
apply: seqv_sub_adjoin.
rewrite /index_enum -enumT.
apply: (@mem_enum (finFieldExtType L)).
rewrite (finField_genPoly (finFieldExtType L)).
rewrite separable_prod_XsubC /index_enum -enumT.
apply: (@enum_uniq (finFieldExtType L)).
Qed.

Lemma finField_galois_generator_subproof K :
  {x | generator 'Gal({:L} / K) x & 
       forall a, x a = a ^+ (#|F| ^ \dim K)}.
Proof.
wlog: K / K = 1%AS.
  case/(_ _ (refl_equal 1%AS)) => x.
  rewrite /generator => /eqP HKEx.
  rewrite dimv1 expn1 => Hx.
  exists (x ^+ \dim K)%g; last first.
    move => a.
    elim: (\dim K) => [|n IH]; first by rewrite expg0 gal_id expn0 expr1.
    by rewrite expgSr galM ?memvf // comp_lfunE IH Hx ?rpredX // expnSr exprM.
  rewrite (eq_subG_cyclic (cycle_cyclic x)) ?cycleX //=; last first.
    by rewrite -HKEx galS // sub1v.
  rewrite [X in _ == X]orderXgcd /order -HKEx.
  rewrite -{1}(galois_dim (finField_galois_subproof _)).
  rewrite -{1 2}(galois_dim (finField_galois_subproof _)).
  by rewrite !dimv1 !divn1 (gcdn_idPr _) // field_dimS // subvf.
move ->; rewrite dimv1 expn1.
pose f (a : L) := a ^+ #|F|.
have HfZ k : f (k%:A) = k%:A.
  by apply/eqP; rewrite -finField_memv1_subproof memvZ // memv_line.
have Hf_rmorph : rmorphism f.
  have := finCharP F.
  rewrite -(charLF L) => Hchar.
  rewrite /f finField_card.
  elim: ('dim _) => [|n IH]; first by rewrite expn0.
  rewrite expnSr.
  repeat split; last by rewrite expr1n.
    move => a b /=.
    rewrite !exprM [(_ - _) ^+ _](rmorphB (RMorphism IH)).
    by rewrite [(_ - _) ^+ _](rmorphB [rmorphism of Frobenius_aut Hchar]).
  move => a b /=.
  by rewrite exprMn.
have Hf_linear : linear f.
  move => k a b; rewrite -mulr_algl.
  rewrite [f _](rmorphD (RMorphism Hf_rmorph)) (rmorphM (RMorphism Hf_rmorph)).
  by rewrite /= HfZ mulr_algl.
have /kAut_gal [x Hx Hfx] : linfun (Linear Hf_linear) \is a kAut 1 {:L}.
  rewrite kAutE; apply/andP; split; last first.
    by apply/subvP => _ /memv_imgP [a Ha ->]; rewrite lfunE rpredX //.
  apply/kHomP; split.
    move => _ /vlineP [k ->].
    by rewrite lfunE /= HfZ.
  move => a b _ _ /=.
  rewrite !(lfunE (Linear Hf_linear)) /=.
  by rewrite [f _](rmorphM (RMorphism Hf_rmorph)).
exists x; last by move => a; rewrite -Hfx ?memvf // lfunE.
apply/eqP.
suff <- : fixedField [set x] = 1%AS by rewrite -[<[x]>]gal_generated.
apply/vspaceP => a.
apply/fixedFieldP/idP.
  case => HaE /(_ _ (set11 x)).
  by rewrite -Hfx // lfunE finField_memv1_subproof /= /f => ->.
case/vlineP => k ->; split => [|_ /set1P ->]; first by rewrite memvZ // mem1v.
by rewrite -Hfx ?memvZ ?mem1v // lfunE /= HfZ.
Qed.

Lemma finField_galois K E : (K <= E)%VS -> galois K E.
Proof.
move => HKE.
move/galois_fixedField: (finField_galois_subproof E) <-.
apply: normal_fixedField_galois; first by apply: finField_galois_subproof.
  by apply: galS.
have [x] := finField_galois_generator_subproof 1.
rewrite /generator => /eqP Hx _.
apply: sub_abelian_norm; last by apply: galS.
apply: (abelianS (galS _ (sub1v _))).
rewrite Hx.
apply cycle_abelian.
Qed.

Lemma finField_galois_generator K E : (K <= E)%VS ->
  {x | generator 'Gal(E / K) x & 
       {in E, forall a, x a = a ^+ (#|F| ^ \dim K)}}.
Proof.
move => HKE.
have [x Hx Hxa] := finField_galois_generator_subproof K.
have HKEL : (K <= E <= fullv)%VS by rewrite HKE subvf.
have Hnorm : normalField K E.
  by case/and3P: (finField_galois HKE).
have Hx_gal : x \in 'Gal({:L} / K).
  by move: Hx; rewrite /generator => /eqP ->; apply: cycle_id.
exists (normalField_cast _ x); last first.
  by move => a HaE /=; rewrite (normalField_cast_eq HKEL).
move: Hx.
rewrite /generator -(morphim_cycle (normalField_cast_morphism HKEL Hnorm)) //.
move/eqP <-.
rewrite normalField_img //.
by apply: finField_galois; apply: subvf.
Qed.

End FinSplittingField.

Lemma fermat's_little_theorem (F : finFieldType) (L : fieldExtType F) 
  (K : {subfield L}) a : (a \in K) = (a ^+ (#|F| ^ \dim K) == a).
Proof.
suff : forall (L : splittingFieldType F) (K : {subfield L}) a,
  (a \in K) = (a ^+ (#|F| ^ \dim K) == a).
  pose L0 := SplittingFieldType F _ (finField_splittingField_axiom L).
  by move/(_ L0 K); apply.
move => {L K a} L K a.
have /galois_fixedField Hgalois := finField_galois (subvf K).
have [x Hx Hxa] := finField_galois_generator (subvf K).
rewrite -Hxa ?memvf // -{1}Hgalois.
move: Hx; rewrite /generator; move /eqP ->.
rewrite /cycle -gal_generated.
have /galois_fixedField -> := fixedField_galois [set x].
apply/fixedFieldP/eqP.
  by case => _; apply; rewrite set11.
move => Hx; split => [|_ /set1P ->]; last done.
by rewrite memvf.
Qed.
