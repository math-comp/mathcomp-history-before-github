(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice tuple.
Require Import bigop ssralg poly polydiv.

Require Import generic_quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.
Open Local Scope quotient_scope.

Reserved Notation "{ 'ratio' T }" (at level 0, format "{ 'ratio'  T }").
Reserved Notation "{ 'fraction' T }" (at level 0, format "{ 'fraction'  T }").
Reserved Notation "x %:F" (at level 2, format "x %:F").

CoInductive fractionDomain (T : Type) := FractionDomain { numer : T; denom : T}.

Section FractionDomainTheory.

Variable R : zmodType.

Definition fractionDomain_encode f : seq R := [:: numer f; denom f].
Definition fractionDomain_decode s : fractionDomain R := FractionDomain s`_0 s`_1.
Lemma fractionDomain_codeK : cancel fractionDomain_encode fractionDomain_decode.
Proof. by case. Qed.

Definition FractionDomain_EqMixin := CanEqMixin fractionDomain_codeK.
Canonical fractionDomain_EqType := EqType (fractionDomain R) FractionDomain_EqMixin.
Definition FractionDomain_ChoiceMixin := CanChoiceMixin fractionDomain_codeK.
Canonical fractionDomain_ChoiceType := ChoiceType (fractionDomain R) FractionDomain_ChoiceMixin.

End FractionDomainTheory.

Section FracDomain.
Variable R : ringType.

Inductive ratio := mkRatio { frac :> fractionDomain R; _ : denom frac != 0 }.
Definition ratio_of of phant R := ratio.
Local Notation "{ 'ratio' T }" := (ratio_of (Phant T)).

Canonical ratio_subType := Eval hnf in [subType for frac].
Canonical ratio_of_subType := Eval hnf in [subType of {ratio R}].
Definition ratio_EqMixin := [eqMixin of ratio by <:].
Canonical ratio_eqType := EqType ratio ratio_EqMixin.
Canonical ratio_of_eqType := Eval hnf in [eqType of {ratio R}].
Definition ratio_ChoiceMixin := [choiceMixin of ratio by <:].
Canonical ratio_choiceType := ChoiceType ratio ratio_ChoiceMixin.
Canonical ratio_of_choiceType := Eval hnf in [choiceType of {ratio R}].

Lemma denom_ratioP : forall f : ratio, denom f != 0. Proof. by case. Qed.

Definition ratio0 := (@mkRatio (FractionDomain 0 1) (oner_neq0 _)).
Definition Ratio x y : {ratio R} := insubd ratio0 (FractionDomain x y).

Lemma numer_Ratio x y : y != 0 -> numer (Ratio x y) = x.
Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed.

Lemma denom_Ratio x y : y != 0 -> denom (Ratio x y) = y.
Proof. by move=> ny0; rewrite /Ratio /insubd insubT. Qed.

Definition numden_Ratio := (numer_Ratio, denom_Ratio).

CoInductive Ratio_spec (n d : R) : {ratio R} -> R -> R -> Type :=
  | RatioNull of d = 0 : Ratio_spec n d ratio0 n 0
  | RatioNonNull (d_neq0 : d != 0) : 
    Ratio_spec n d (@mkRatio (FractionDomain n d) d_neq0) n d.

Lemma RatioP n d : Ratio_spec n d (Ratio n d) n d.
Proof.
rewrite /Ratio /insubd; case: insubP=> /= [x /= d_neq0 hx|].
  have ->: x = @mkRatio (FractionDomain n d) d_neq0 by apply: val_inj.
  by constructor.
by rewrite negbK=> /eqP hx; rewrite {2}hx; constructor.
Qed.

Lemma Ratio0 x : Ratio x 0 = ratio0.
Proof. by rewrite /Ratio /insubd; case: insubP; rewrite //= eqxx. Qed.

End FracDomain.

Notation "{ 'ratio' T }" := (ratio_of (Phant T)).
Identity Coercion type_fracdomain_of : ratio_of >-> ratio.

Notation "'\n_' x"  := (numer x)
  (at level 8, x at level 2, format "'\n_' x").
Notation "'\d_' x"  := (denom x)
  (at level 8, x at level 2, format "'\d_' x").

Module FracField.
Section FracField.

Variable R : idomainType.

Local Notation frac := (fractionDomain R).
Local Notation dom := (ratio R).
Local Notation domP := denom_ratioP.

Implicit Types x y z : dom.

Definition equivf x y := \n_x * \d_y == \d_x * \n_y.

Lemma equivfE x y : equivf x y = (\n_x * \d_y == \d_x * \n_y).
Proof. by []. Qed.

Lemma equivf_refl : reflexive equivf.
Proof. by move=> x; rewrite /equivf mulrC. Qed.

Lemma equivf_sym : symmetric equivf.
Proof. by move=> x y; rewrite /equivf eq_sym; congr (_==_); rewrite mulrC. Qed.

Lemma equivf_trans : transitive equivf.
Proof.
move=> [x Px] [y Py] [z Pz]; rewrite /equivf /= mulrC => /eqP xy /eqP yz.
by rewrite -(inj_eq (mulfI Px)) mulrA xy -mulrA yz mulrCA.
Qed.

Canonical equivf_equiv := EquivRel equivf equivf_refl equivf_sym equivf_trans.
Canonical equivf_encModRel := defaultEncModRel equivf.

Definition type := {eq_quot equivf}.
Definition type_of of phant R := type.
Notation "{ 'fraction' T }" := (type_of (Phant T)).

Canonical frac_quotType := [quotType of type].
Canonical frac_eqType := [eqType of type].
Canonical frac_choiceType := [choiceType of type].
Canonical frac_eqQuotType := [eqQuotType equivf of type].

Canonical frac_of_quotType := [quotType of {fraction R}].
Canonical frac_of_eqType := [eqType of {fraction R}].
Canonical frac_of_choiceType := [choiceType of {fraction R}].
Canonical frac_of_eqQuotType := [eqQuotType equivf of {fraction R}].

Lemma equivf_def (x y : ratio R) : x == y %[mod type]
                                    = (\n_x * \d_y == \d_x * \n_y).
Proof. by rewrite eqmodE. Qed.

Lemma equivf_r x : \n_x * \d_(repr (\pi_type x)) = \d_x * \n_(repr (\pi_type x)).
Proof. by apply/eqP; rewrite -equivf_def reprK. Qed.

Lemma equivf_l x : \n_(repr (\pi_type x)) * \d_x = \d_(repr (\pi_type x)) * \n_x.
Proof. by apply/eqP; rewrite -equivf_def reprK. Qed.

Lemma numer0 x : (\n_x == 0) = (x == (ratio0 R) %[mod_eq equivf]).
Proof. by rewrite eqmodE /= !equivfE // mulr1 mulr0. Qed.

Lemma Ratio_numden : forall x, Ratio \n_x \d_x = x.
Proof.
case=> [[n d] /= nd]; rewrite /Ratio /insubd; apply: val_inj=> /=.
by case: insubP=> //=; rewrite nd.
Qed.

Definition tofrac := lift_embed {fraction R} (fun x : R => Ratio x 1).
Canonical tofrac_pi_morph := PiEmbed tofrac.

Notation "x %:F"  := (@tofrac x).

Implicit Types a b c : type.

Definition addf x y : dom := Ratio (\n_x * \d_y + \n_y * \d_x) (\d_x * \d_y).
Definition add := lift_op2 {fraction R} addf.

Lemma pi_add : {morph \pi : x y / addf x y >-> add x y}.
Proof.
move=> x y; unlock add; apply/eqmodP; rewrite /= equivfE.
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP //.
rewrite mulrDr mulrDl eq_sym; apply/eqP.
rewrite !mulrA ![_ * \n__]mulrC !mulrA equivf_l.
congr (_ + _); first by rewrite -mulrA mulrCA !mulrA.
rewrite -!mulrA [X in _ * X]mulrCA !mulrA equivf_l.
by rewrite mulrC !mulrA -mulrA mulrC mulrA.
Qed.
Canonical pi_add_morph := PiMorph2 pi_add.

Definition oppf x : dom := Ratio (- \n_x) \d_x.
Definition opp := lift_op1 {fraction R} oppf.
Lemma pi_opp : {morph \pi : x / oppf x >-> opp x}.
Proof.
move=> x; unlock opp; apply/eqmodP; rewrite /= /equivf /oppf /=.
by rewrite !numden_Ratio ?(domP,mulf_neq0) // mulNr mulrN -equivf_r.
Qed.
Canonical pi_opp_morph := PiMorph1 pi_opp.

Definition mulf x y : dom := Ratio (\n_x * \n_y) (\d_x * \d_y).
Definition mul := lift_op2 {fraction R} mulf.

Lemma pi_mul : {morph \pi : x y / mulf x y >-> mul x y}.
Proof.
move=> x y; unlock mul; apply/eqmodP=> /=.
rewrite equivfE /= /addf /= !numden_Ratio ?mulf_neq0 ?domP //.
rewrite mulrAC !mulrA -mulrA equivf_r -equivf_l.
by rewrite mulrA ![_ * \d_y]mulrC !mulrA.
Qed.
Canonical pi_mul_morph := PiMorph2 pi_mul.

Definition invf x : dom := Ratio \d_x \n_x.
Definition inv := lift_op1 {fraction R} invf.

Lemma pi_inv : {morph \pi : x / invf x >-> inv x}.
Proof.
move=> x; unlock inv; apply/eqmodP=> /=; rewrite equivfE /invf eq_sym.
do 2?case: RatioP=> /= [/eqP|];
  rewrite ?mul0r ?mul1r -?equivf_def ?numer0 ?reprK //.
  by move=> hx /eqP hx'; rewrite hx' eqxx in hx.
by move=> /eqP ->; rewrite eqxx.
Qed.
Canonical pi_inv_morph := PiMorph1 pi_inv.

Lemma addA : associative add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
rewrite /addf /= !numden_Ratio ?mulf_neq0 ?domP // !mulrDl !mulrA !addrA.
by congr (\pi (Ratio (_ + _ + _) _)); rewrite mulrAC.
Qed.

Lemma addC : commutative add.
Proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !piE /addf addrC [\d__ * _]mulrC.
Qed.

Lemma add0_l : left_id 0%:F add.
Proof.
elim/quotW=> x; rewrite !piE /addf !numden_Ratio ?oner_eq0 //.
by rewrite mul0r mul1r mulr1 add0r Ratio_numden.
Qed.

Lemma addN_l : left_inverse 0%:F opp add.
Proof.
elim/quotW=> x; apply/eqP; rewrite piE /equivf.
rewrite /addf /oppf !numden_Ratio ?(oner_eq0, mulf_neq0, domP) //.
by rewrite mulr1 mulr0 mulNr addNr.
Qed.

Definition frac_zmodMixin :=  ZmodMixin addA addC add0_l addN_l.
Canonical frac_zmodType := Eval hnf in ZmodType type frac_zmodMixin.

Lemma mulA : associative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE.
by rewrite /mulf !numden_Ratio ?mulf_neq0 ?domP // !mulrA.
Qed.

Lemma mulC : commutative mul.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE /mulf.
by rewrite [_ * (\d_x)]mulrC [_ * (\n_x)]mulrC.
Qed.

Lemma mul1_l : left_id 1%:F mul.
Proof.
elim/quotW=> x; rewrite !piE /mulf.
by rewrite !numden_Ratio ?oner_eq0 // !mul1r Ratio_numden.
Qed.

Lemma mul_addl : left_distributive mul add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
rewrite !piE /equivf /mulf /addf !numden_Ratio ?mulf_neq0 ?domP //; apply/eqP.
rewrite !(mulrDr, mulrDl) !mulrA; congr (_ * _ + _ * _).
  rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
  rewrite ![\d_y * _]mulrC !mulrA; congr (_ * _ * _).
  by rewrite [X in _ = X]mulrC mulrA.
rewrite ![_ * \n_z]mulrC -!mulrA; congr (_ * _).
rewrite ![\d_x * _]mulrC !mulrA; congr (_ * _ * _).
by rewrite -mulrA mulrC [X in X * _] mulrC.
Qed.

Lemma nonzero1 : 1%:F != 0%:F :> type.
Proof. by rewrite piE equivfE !numden_Ratio ?mul1r ?oner_eq0. Qed.

Definition frac_comRingMixin := ComRingMixin mulA mulC mul1_l mul_addl nonzero1.
Canonical frac_ringType := Eval hnf in RingType type frac_comRingMixin.
Canonical frac_comRingType := Eval hnf in ComRingType type mulC.

Lemma mulV_l : forall a, a != 0%:F -> mul (inv a) a = 1%:F.
Proof.
elim/quotW=> x /=; rewrite !piE.
rewrite /equivf !numden_Ratio ?oner_eq0 // mulr1 mulr0=> nx0.
apply/eqmodP; rewrite /= equivfE.
by rewrite !numden_Ratio ?(oner_eq0, mulf_neq0, domP) // !mulr1 mulrC.
Qed.

Lemma inv0 : inv 0%:F = 0%:F.
Proof.
rewrite !piE /invf !numden_Ratio ?oner_eq0 // /Ratio /insubd.
do 2?case: insubP; rewrite //= ?eqxx ?oner_eq0 // => u _ hu _.
by congr \pi; apply: val_inj; rewrite /= hu.
Qed.

Definition RatFieldUnitMixin := FieldUnitMixin mulV_l inv0.
Canonical frac_unitRingType := Eval hnf in UnitRingType type RatFieldUnitMixin.
Canonical frac_comUnitRingType := [comUnitRingType of type].

Lemma field_axiom : GRing.Field.mixin_of frac_unitRingType.
Proof. exact. Qed.

Definition RatFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical frac_idomainType :=
  Eval hnf in IdomainType type (FieldIdomainMixin field_axiom).
Canonical frac_fieldType := FieldType type field_axiom.

End FracField.
End FracField.

Notation "{ 'fraction' T }" := (FracField.type_of (Phant T)).
Notation equivf := (@FracField.equivf _).
Hint Resolve denom_ratioP.

Section Canonicals.

Variable R : idomainType.

Canonical FracField.frac_quotType.
Canonical FracField.frac_eqType.
Canonical FracField.frac_choiceType.
Canonical FracField.frac_zmodType.
Canonical FracField.frac_ringType.
Canonical FracField.frac_comRingType.
Canonical FracField.frac_unitRingType.
Canonical FracField.frac_comUnitRingType.
Canonical FracField.frac_idomainType.
Canonical FracField.frac_fieldType.
Canonical FracField.tofrac_pi_morph.
Canonical frac_of_quotType := Eval hnf in [quotType of {fraction R}].
Canonical frac_of_eqType := Eval hnf  in [eqType of {fraction R}].
Canonical frac_of_choiceType := Eval hnf in [choiceType of {fraction R}].
Canonical frac_of_zmodType := Eval hnf in [zmodType of {fraction R}].
Canonical frac_of_ringType := Eval hnf in [ringType of {fraction R}].
Canonical frac_of_comRingType := Eval hnf in [comRingType of {fraction R}].
Canonical frac_of_unitRingType := Eval hnf in [unitRingType of {fraction R}].
Canonical frac_of_comUnitRingType := Eval hnf in [comUnitRingType of {fraction R}].
Canonical frac_of_idomainType := Eval hnf in [idomainType of {fraction R}].
Canonical frac_of_fieldType := Eval hnf in [fieldType of {fraction R}].

End Canonicals.

Reserved Notation "{ 'polyfrac' T }" (at level 0, format "{ 'polyfrac'  T }").

Section FracFieldTheory.

Import FracField.

Variable R : idomainType.

Lemma Ratio_numden (x : {ratio R}) : Ratio \n_x \d_x = x.
Proof. exact: FracField.Ratio_numden. Qed.

(* CoInductive ratio_spec (x : {ratio R}) : R -> R -> {ratio R} -> Type := *)
(*   RatioSpec n d of x = Ratio n d & d != 0 : ratio_spec x n d (Ratio n d). *)

(* Lemma ratioP x : ratio_spec x \n_x \d_x (Ratio \n_x \d_x). *)
(* Proof. by constructor; rewrite ?Ratio_numden. Qed. *)

Local Notation tofrac := (@FracField.tofrac R).
Local Notation "x %:F" := (tofrac x).

Lemma tofrac_is_additive: additive tofrac.
Proof.
move=> p q /=; unlock tofrac.
rewrite -[X in _ = _ + X]pi_opp -[X in _ = X]pi_add.
by rewrite /addf /oppf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

Canonical tofrac_additive := Additive tofrac_is_additive.

Lemma tofrac_is_multiplicative: multiplicative tofrac.
Proof.
split=> [p q|//]; unlock tofrac; rewrite -[X in _ = X]pi_mul.
by rewrite /mulf /= !numden_Ratio ?(oner_neq0, mul1r, mulr1).
Qed.

Canonical tofrac_rmorphism := AddRMorphism tofrac_is_multiplicative.

Lemma tofrac0 : 0%:F = 0. Proof. exact: rmorph0. Qed.
Lemma tofracN : {morph tofrac: x / - x}. Proof. exact: rmorphN. Qed.
Lemma tofracD : {morph tofrac: x y / x + y}. Proof. exact: rmorphD. Qed.
Lemma tofracB : {morph tofrac: x y / x - y}. Proof. exact: rmorphB. Qed.
Lemma tofracMn n : {morph tofrac: x / x *+ n}. Proof. exact: rmorphMn. Qed.
Lemma tofracMNn n : {morph tofrac: x / x *- n}. Proof. exact: rmorphMNn. Qed.
Lemma tofrac1 : 1%:F = 1. Proof. exact: rmorph1. Qed.
Lemma tofracM : {morph tofrac: x y  / x * y}. Proof. exact: rmorphM. Qed.
Lemma tofracX n : {morph tofrac: x / x ^+ n}. Proof. exact: rmorphX. Qed.

Lemma tofrac_eq (p q : R): (p%:F == q%:F) = (p == q).
Proof.
apply/eqP/eqP=> [|->//]; unlock tofrac=> /eqmodP /eqP /=.
by rewrite !numden_Ratio ?(oner_eq0, mul1r, mulr1).
Qed.

Lemma tofrac_eq0 (p : R): (p%:F == 0) = (p == 0).
Proof. by rewrite tofrac_eq. Qed.
End FracFieldTheory.

(* Section PolyFracDef. *)

(* Variable R : fieldType. *)

(* Definition polyfrac_axiom (x : {ratio {poly R}}) := *)
(*   (coprimep \n_x \d_x) && (monic \d_x). *)

(* Record polynomialfrac := PolyFrac { *)
(*   polyfrac :> {ratio {poly R}}; *)
(*   _ : polyfrac_axiom polyfrac *)
(* }. *)
(* Definition polyfrac_of of phant R := polynomialfrac. *)
(* Local Notation pfrac := (polyfrac_of (Phant R)). *)
(* Identity Coercion type_pfrac_of : polyfrac_of >-> polynomialfrac. *)

(* Lemma coprime_polyfrac (x : pfrac) : coprimep \n_x \d_x. *)
(* Proof. by case: x=> pf /= /andP []. Qed. *)

(* Lemma monic_polyfrac (x : pfrac) : monic \d_x. *)
(* Proof. by case: x=> pf /= /andP []. Qed. *)

(* End PolyFracDef. *)
(* Notation "{ 'polyfrac' T }" := (polyfrac_of (Phant T)). *)

(* Module PolyFraction. *)
(* Section PolyFraction. *)

(* Variable R : fieldType. *)

(* Canonical polyfrac_subType := Eval hnf in *)
(*   [subType for (@polyfrac R)]. *)
(* Canonical poly_frac_of_subType := [subType of {polyfrac R}]. *)
(* Definition polyfrac_EqMixin := Eval hnf in [eqMixin of polynomialfrac R by <:]. *)
(* Canonical polyfrac_eqType := EqType (polynomialfrac R) polyfrac_EqMixin. *)
(* Canonical poly_frac_of_eqType := [eqType of {polyfrac R}]. *)
(* Definition polyfrac_ChoiceMixin := Eval hnf in [choiceMixin of polynomialfrac R by <:]. *)
(* Canonical polyfrac_choiceType := ChoiceType (polynomialfrac R) polyfrac_ChoiceMixin. *)
(* Canonical polyfrac_of_choiceType := [choiceType of {polyfrac R}]. *)

(* Definition reduce (x : {ratio {poly R}}) : {ratio {poly R}} := *)
(*   let g := gcdp \n_x \d_x in let lg := lead_coef g in *)
(*     Ratio (\n_x %/ (lg^-1 *: g)) (\d_x %/ (lg^-1 *: g)). *)

(* Definition normalize (x : {ratio {poly R}}) : {ratio {poly R}} := *)
(*   Ratio ((lead_coef \d_x) *: \n_x) ((lead_coef \d_x)^-1 *: \d_x). *)

(* Lemma canon0 : @polyfrac_axiom R (ratio0 _). *)
(* Proof. by rewrite /polyfrac_axiom coprime0p eqpxx monic1. Qed. *)

(* Definition canonize (x : {ratio {poly R}}) : {polyfrac R} := *)
(*   insubd (PolyFrac canon0) (normalize (reduce x)). *)

(* Lemma polyvalK : cancel (@polyfrac R) canonize. *)
(* Proof. *)
(* case=> [[[n d] /= hd]] /=; rewrite /polyfrac_axiom /= => hx. *)
(* case/andP: (hx)=> cnd md. *)
(* rewrite /canonize /normalize /reduce /=. *)
(* set g := gcdp n d; set lg := lead_coef g. *)
(* have hdng : d %/ (lg^-1 *: g) != 0. *)
(*   suff: (lg^-1 *: g) %| d. *)
(*     by rewrite dvdp_eq; apply: contraTneq=> ->; rewrite mul0r. *)
(*   rewrite (eqp_dvdl _ (eqp_scale _ _)) ?dvdp_gcdr //. *)
(*   by rewrite invr_eq0 lead_coef_eq0 gcdp_eq0 (negPf hd) andbF. *)
(* rewrite !numden_Ratio //= /insubd. *)
(* set n' : {poly R} := _ *: (_ %/ _); set d' : {poly R} := _ *: (_ %/ _). *)
(* have hg : lg^-1 *: g = 1. *)
(*   rewrite /lg /g; move: cnd; rewrite coprimep_def=> /size_poly1P [c hc ->]. *)
(*   by rewrite lead_coefC -mul_polyC -rmorphM mulVr // unitfE. *)
(* have -> : n' = n by rewrite /n' hg !divp1 (eqP md) scale1r. *)
(* have -> : d' = d by rewrite /d' hg !divp1 (eqP md) invr1 scale1r. *)
(* do 2! apply: val_inj => /=. *)
(* by rewrite insubT /= /polyfrac_axiom !numden_Ratio // /Ratio /insubd insubT. *)
(* Qed. *)


(* Definition polyfrac_quotClass := QuotClass polyvalK. *)
(* Canonical polyfrac_quotType := QuotType polyfrac_quotClass. *)
(* Canonical pfrac_quotType := Eval hnf in [quotType of {polyfrac R}]. *)

(* Lemma polyfrac_same_equivf (x y : {ratio {poly R}}) : *)
(*   (x == y %[m {fraction {poly R}}]) = (x == y %[m {polyfrac R}]). *)
(* Proof. *)
(* rewrite eqmodE /=. *)
(* move: x y => [[nx dx] /= hdx] [[ny dy] /= hdy]. *)
(* rewrite /FracField.equivf //=. *)
(* rewrite unlock /pi_of /= /canonize /normalize /reduce /=. *)
(* rewrite !numden_Ratio. *)
(* Admitted. *)

(* Local Notation sequiv := polyfrac_same_equivf. *)

(* Definition add : {polyfrac R} -> {polyfrac R} -> {polyfrac R} := *)
(*   chgQuotOp2 (mop2_morph (@FracField.add_compat _)). *)
(* Definition opp : {polyfrac R} -> {polyfrac R} := *)
(*   chgQuotOp1 (mop1_morph (@FracField.opp_compat _)). *)
(* Definition mul : {polyfrac R} -> {polyfrac R} -> {polyfrac R} := *)
(*   chgQuotOp2 (mop2_morph (@FracField.mul_compat _)). *)
(* Definition inv : {polyfrac R} -> {polyfrac R} := *)
(*   chgQuotOp1 (mop1_morph (@FracField.inv_compat _)). *)

(* Canonical add_morph := @MorphOp2 _ _ _ _ _ _ _ add (chgQuotOp2P _ sequiv). *)
(* Canonical opp_morph := @MorphOp1 _ _ _ _ _ opp (chgQuotOp1P _ sequiv). *)
(* Canonical mul_morph := @MorphOp2 _ _ _ _ _ _ _ mul (chgQuotOp2P _ sequiv). *)
(* Canonical inv_morph := @MorphOp1 _ _ _ _ _ inv (chgQuotOp1P _ sequiv). *)

(* (* To be continued *) *)

(* End PolyFraction. *)
(* End PolyFraction. *)

