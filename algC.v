(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice div fintype.
Require Import bigop finset prime ssralg poly polydiv ssrint rat ssrnum.

(******************************************************************************)
(* This file provides a temporary partial axiomatic presentation of the       *)
(* algebraic numbers.                                                         *)
(*       algC == the closed field of algebraic numbers.                       *)
(*        z^* == the complex conjugate of z.                                  *)
(*     0 <= x <=> x is a nonnegative real.                                    *)
(*     x <= y <=> (y - x) is a nonnegative real                               *)
(*      x < y <=> (y - x) is a (strictly) positive real                       *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x. *)
(*       `|z| == the complex norm of z, i.e., sqrtC (z * z^* ).               *)
(*  isNatC z <=> z is a natural number.                                       *)
(*  getNatC x == the n such that x = n%:R if isNatC x, else 0.                *)
(*  isRealC x == x is a real number, i.e., x^* == x.                          *)
(*     isIntC x == x is an integer.                                           *)
(*    getIntC x == a pair (n, b) such that x = (-1) ^+ b * n%:R, if isIntC x. *)
(*     dvdC x y == x divides y, i.e., y = z * x for some integer z.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition algebraic (R : ringType) :=
 forall x : R, exists2 p, map_poly intr p != 0 :> {poly R}
                        & root (map_poly intr p) x.
  
Module Type AlgSig.

Parameter type : Type.

Parameter eqMixin : Equality.class_of type.
Canonical type_eqType := EqType type eqMixin.

Parameter choiceMixin : Choice.mixin_of type.
Canonical type_choiceType := ChoiceType type choiceMixin.

Parameter zmodMixin : GRing.Zmodule.mixin_of type.
Canonical type_zmodType := ZmodType type zmodMixin.

Parameter ringMixin : GRing.Ring.mixin_of [zmodType of type].
Canonical type_ringType := RingType type ringMixin.

Parameter mulC : commutative (@GRing.mul [ringType of type]).
Canonical type_comRingType := ComRingType type mulC.

Parameter unitRingMixin : GRing.UnitRing.mixin_of [ringType of type].
Canonical type_unitRingType := UnitRingType type unitRingMixin.

Canonical type_comUnitRingType := Eval hnf in [comUnitRingType of type].

Parameter idomain_axiom : GRing.IntegralDomain.axiom [ringType of type].
Canonical type_idomainType := IdomainType type idomain_axiom.

Parameter fieldMixin : GRing.Field.mixin_of [unitRingType of type].
Canonical type_fieldType := FieldType type fieldMixin.

Parameter numMixin : Num.mixin_of [ringType of type].
Canonical type_numIdomainType := NumIdomainType type numMixin.
Canonical type_numFieldType := NumFieldType type numMixin.

Parameter decFieldMixin : GRing.DecidableField.mixin_of [unitRingType of type].
Canonical type_decFieldType := DecFieldType type decFieldMixin.

Parameter closed_axiom : GRing.ClosedField.axiom [ringType of type].
Canonical type_closedFieldType := ClosedFieldType type closed_axiom.

Parameter conj : {rmorphism type -> type}.

Axiom conjK : involutive conj.
Axiom normCK : forall x : type, `|x| ^+ 2 = x * conj x.
Axiom type_algebraic : algebraic [ringType of type].

End AlgSig.

Section AlgIsArchi.

(* :TODO: update theory for archimedeanity in ssrnum to reflect this axiom *)
Definition archimedean (R : numIdomainType) := 
  forall x : R, 0 <= x -> exists n, n%:R <= x < n.+1%:R.

Variable R : numIdomainType.
Hypothesis R_alg : algebraic R.
Implicit Type x : R.

Local Hint Resolve (@intr_inj [numIdomainType of R]).

(* :TODO: this result should be moved to the archimedean theory in ssrnum *)
Lemma alg_archimedean : archimedean R.
Proof.
move=> x x_ge0; have x_real := ger0_real x_ge0.
suffices /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R.
  exists n; rewrite lt_x_n1 andbT; case Dn: n => // [n1]; rewrite -Dn.
  have [||//|] := @real_lerP _ n%:R x; rewrite ?rpred_nat //.
  by rewrite Dn => /min_n; rewrite Dn ltnn.
suffices [n x_le_n]: exists n, x <= n%:R.
  by exists n; rewrite (ler_lt_trans x_le_n) ?ltr_nat.
have [||x_le1 | x_ge1] := @real_lerP _ x 1; rewrite ?rpred1 //.
  by exists 1%N.
have [p nz_p px0] := R_alg x; pose n := (size p).-2.
have {nz_p} nz_p : p != 0 by apply: contraNneq nz_p => ->; rewrite map_poly0.
have Dn: n.+2 = size p.
  rewrite /n -subn2 -addn2 subnK // ltnNge.
  apply: contra (nz_p) => /size1_polyC Dp; rewrite Dp polyC_eq0.
  by rewrite Dp /root map_polyC hornerC intr_eq0 in px0.
have xk_gt0 k: 0 < x ^+ k by rewrite exprn_gt0 // (ltr_trans ltr01).
exists (\sum_(i < n.+1) `|(p`_i)%R|)%N.
apply: ler_trans (_ : x <= `|lead_coef p|%:R * x) _.
  rewrite -{1}[x]mul1r ler_pmul2r ?(xk_gt0 1%N) // ler1n lt0n.
  by rewrite absz_eq0 lead_coef_eq0.
rewrite -[_ * x]subr0 -(ler_pmul2r (xk_gt0 n)) mulrBl mul0r -mulrA.
rewrite -exprS -(mulr0 ((-1) ^+ (lead_coef p < 0)%R)) -(eqP px0).
rewrite horner_coef size_map_inj_poly // lead_coefE -Dn big_ord_recr coef_map.
move: p`_n.+1 => a /=; rewrite addrC {2}[a]intEsign mulrDr.
rewrite !rmorphM rmorph_sign -mulrA signrMK opprD addrNK mulr_sumr.
rewrite -subr_ge0 opprK natr_sum mulr_suml -big_split /= sumr_ge0 // => i _.
rewrite coef_map {2}[p`_i]intEsign /= rmorphM rmorph_sign !mulrA -signr_addb.
rewrite -mulrA mulrCA -mulrDr mulr_ge0 ?ler0n // mulr_sign.
case: ifP => _; last by rewrite addr_ge0 ?ltrW.
rewrite subr_ge0 -{2}(subnK (leq_ord i)) -[x ^+ i]mul1r exprD.
by case: (n - i)%N => [|k]; rewrite ?lerr // ler_pmul2r // expr_ge1 // ?ltrW.
Qed.

End AlgIsArchi.

Section AlgIsCountable.

Variable R : closedFieldType.
Hypothesis R_alg : algebraic R.
Implicit Type x : R.

Local Notation ZtoR := (intr : int -> R).
Local Notation pZtoR := (map_poly ZtoR).

(* Countability. *)
Lemma alg_countMixin : Countable.mixin_of R.
Proof.
pose code x :=
  let p := s2val (sig2_eqW (R_alg x)) in
  (p : seq int, index x (sval (closed_field_poly_normal (pZtoR p)))).
pose decode pi :=
  (sval (closed_field_poly_normal (Poly (map ZtoR pi.1))))`_(pi.2).
apply: CanCountMixin (code) (decode) _ => x; rewrite {}/decode {code}/=.
rewrite -map_polyE; case: (sig2_eqW _) => p /= nz_p px0.
case: (closed_field_poly_normal _) => r /= Dp; apply: nth_index.
have nz_a: lead_coef (pZtoR p) != 0 by rewrite lead_coef_eq0.
by rewrite -root_prod_XsubC -(rootZ _ _ nz_a) -Dp.
Qed.

End AlgIsCountable.

Module AlgebraicsTheory (Alg : AlgSig).

Delimit Scope C_scope with C.
Open Scope C_scope.

Notation algC := Alg.type.
Notation conjC := Alg.conj.
Notation "x ^*" := (conjC x) (at level 2, format "x ^*") : C_scope.

Canonical Alg.type_eqType.
Canonical Alg.type_choiceType.
Canonical Alg.type_zmodType.
Canonical Alg.type_ringType.
Canonical Alg.type_comRingType.
Canonical Alg.type_unitRingType.
Canonical Alg.type_comUnitRingType.
Canonical Alg.type_idomainType.
Canonical Alg.type_fieldType.
Canonical Alg.type_numIdomainType.
Canonical Alg.type_numFieldType.
Canonical Alg.type_decFieldType.
Canonical Alg.type_closedFieldType.

Local Notation real := Num.real.

(* Against all logic, Implicit Types declarations are Local. *)
Implicit Types (x y z : algC) (m n : nat) (b : bool).

(* Note and caveat: Q-automorphisms of algC do not necessarily commute with   *)
(* conjugation. However, they necessarily do so on the subfield of algC       *)
(* generated by roots of unity, hence on all character values. We should      *)
(* therefore always ensure we only consider dot products of automorphisms of  *)
(* character on (virtual) characters.                                         *)
(*  Further note: by a theorem of Brauer, all non-modular representation      *)
(* theory can be done in the subfield generated by all nth roots of unity; on *)
(* this subfield commutation would be automatic. However, it would be rather  *)
(* inconvenient to work with because we would not be abe to use the complex   *)
(* norm du tp the lack of square roots. Unfortunately adding square roots     *)
(* implies that an automorphism that commutes conjugation must preserve the   *)
(* order on real algebraics, hence be trivial.                                *)

Definition conjCK : involutive conjC := Alg.conjK.
Definition normCK x : `|x| ^+ 2 = x * x^* := Alg.normCK x.
Definition algC_algebraic x := @Alg.type_algebraic x.

Definition eqC_nat := @eqr_nat [numFieldType of algC].
Definition leC_nat := ler_nat [numFieldType of algC].
Definition ltC_nat := ltr_nat [numFieldType of algC].
Definition Cchar := @char_num [numFieldType of algC].

Definition algC_archimedean := alg_archimedean algC_algebraic.
Definition algC_countMixin := alg_countMixin algC_algebraic.
Canonical algC_countType := CountType algC algC_countMixin.

Lemma mulCJ x : x * x^* = `|x| ^+ 2. Proof. by rewrite normCK. Qed.

Lemma mulCJ_ge0 x : 0 <= x * x^*.
Proof. by rewrite mulCJ exprn_ge0 ?normr_ge0. Qed.

Lemma mulJC_ge0 x : 0 <= x^* * x. Proof. by rewrite mulrC mulCJ_ge0. Qed.

Lemma mulCJ_gt0 x : (0 < x * x^*) = (x != 0).
Proof. 
have [->|x_neq0] := altP eqP; first by rewrite rmorph0 mulr0.
by rewrite mulCJ exprn_gt0 ?normr_gt0.
Qed.

Lemma mulJC_gt0 x : (0 < x^* * x) = (x != 0).
Proof. by rewrite mulrC mulCJ_gt0. Qed.

Lemma mulCJ_eq0 x : (x * x^* == 0) = (x == 0).
Proof. by rewrite mulCJ expf_eq0 normr_eq0. Qed.

Lemma mulJC_eq0 x : (x^* * x == 0) = (x == 0).
Proof. by rewrite mulrC mulCJ_eq0. Qed.

Lemma conjC_ge0 x : (0 <= x^*) = (0 <= x).
Proof.
wlog suffices: x / 0 <= x -> 0 <= x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
rewrite le0r => /orP [/eqP -> | x_gt0]; first by rewrite rmorph0.
by rewrite -(pmulr_rge0 _ x_gt0) mulCJ_ge0.
Qed.

(* Cyril : Is it useful ? *)
Lemma conjC_nat n : (n%:R)^* = n%:R. Proof. exact: rmorph_nat. Qed.
Lemma conjC0 : 0^* = 0. Proof. exact: (conjC_nat 0). Qed.
Lemma conjC1 : 1^* = 1. Proof. exact: (conjC_nat 1). Qed.
Lemma conjC_eq0 x : (x^* == 0) = (x == 0). Proof. exact: fmorph_eq0. Qed.
Lemma conjC_inv x : (x^-1)^* = (x^*)^-1. Proof. exact: fmorphV. Qed.

Lemma signC_inj : injective (fun b => (-1) ^+ b : algC).
Proof.
apply: can_inj (fun x => ~~ (0 <= x)) _ => [[]]; rewrite ?ler01 //.
by rewrite oppr_ge0 // ltr_geF ?ltr01.
Qed.

Fact sqrtC_subproof x : exists y : algC, y ^+ 2 == x.
Proof.
have [// | y def_y2] := @solve_monicpoly _ 2 [fun i => 0 with 0%N |-> x].
by exists y; rewrite def_y2 !big_ord_recl big_ord0 /= mulr1 mul0r !addr0.
Qed.

Definition sqrtC := locked (fun x =>
  let y := xchoose (sqrtC_subproof x) in if 0 <= y then y else - y).

Lemma sqrtCK x : sqrtC x ^+ 2 = x.
Proof.
unlock sqrtC; rewrite (fun_if (fun y => y ^+ 2)) sqrrN if_same.
exact/eqP/(xchooseP (sqrtC_subproof x)).
Qed.

Lemma sqrtC_sqr c : (sqrtC (c ^+ 2) == c) || (sqrtC (c ^+ 2) == - c).
Proof. by rewrite -subr_eq0 -addr_eq0 -mulf_eq0 -subr_sqr sqrtCK subrr. Qed.

Lemma sqrtC_lt0 c : (sqrtC c < 0) = false.
Proof.
unlock sqrtC; case: ifPn => [/ler_gtF //|].
by apply: contraNF; rewrite oppr_lt0 => /ltrW.
Qed.

Lemma geC0_sqrt_sqr c : 0 <= c -> sqrtC (c ^+ 2) = c.
Proof.
move=> c_ge0; case/pred2P: (sqrtC_sqr c) => //; unlock sqrtC.
case: ifPn => le0rc def_c; move: le0rc; last by rewrite (oppr_inj def_c) c_ge0.
by rewrite def_c oppr_ge0 -[_ <= _]andbT -c_ge0 => /ler_anti ->; rewrite oppr0.
Qed.

Lemma sqrtC0 : sqrtC 0 = 0. Proof. by rewrite -{1}(mulr0 0) geC0_sqrt_sqr. Qed.

Lemma sqrtC_eq0 c : (sqrtC c == 0) = (c == 0).
Proof.
apply/eqP/eqP=> [|->]; last exact: sqrtC0.
by rewrite -{2}[c]sqrtCK => ->; rewrite exprS mul0r.
Qed.

Lemma sqrtC_le0 c : (sqrtC c <= 0) = (c == 0).
Proof.
have [-> | c_neq0] := altP eqP; first by rewrite sqrtC0 lerr.
by rewrite ler_eqVlt sqrtC_lt0 orbF sqrtC_eq0 (negPf c_neq0).
Qed.

Lemma sqrtC1 : sqrtC 1 = 1.
Proof. by rewrite -{2}(geC0_sqrt_sqr ler01) expr1n. Qed.

Fact conj_id_real x : x^* = x -> x \is real.
Proof.
move=> Rx; pose y := sqrtC x; rewrite realE.
have: x ^+ 2 - (y * y^*) ^+ 2 == 0 by rewrite exprMn -rmorphX sqrtCK Rx subrr.
rewrite subr_sqr mulf_eq0 subr_eq0 addr_eq0.
by case/pred2P=> ->; rewrite ?oppr_le0 ?mulCJ_ge0 ?orbT.
Qed.

Lemma sqrtC_ge0 c : (0 <= sqrtC c) = (0 <= c).
Proof.
apply/idP/idP => c_ge0; first by rewrite -[c]sqrtCK exprn_ge0.
rewrite real_lerNgt ?real0 ?sqrtC_lt0 ?conj_id_real //.
move: c_ge0; rewrite le0r => /predU1P [-> | ]; first by rewrite sqrtC0 conjC0.
move=> c_gt0; apply: (@mulfI _ (sqrtC c)); first by rewrite sqrtC_eq0 gtr_eqF.
by rewrite mulCJ -normrX sqrtCK [_ * _]sqrtCK (normr_idP _) ?ltrW.
Qed.

Lemma normC_def x : `|x| = sqrtC (x * x^*).
Proof.
by apply/eqP; rewrite -(@eqr_expn2 _ 2) ?sqrtCK ?normCK ?sqrtC_ge0 ?mulCJ_ge0.
Qed.

Lemma normCJ z : `|z|^* = `|z|.
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) ?conjC_ge0 //.
by rewrite -rmorphX normCK rmorphM conjCK mulrC.
Qed.

Lemma realC_conjP x : reflect (x^* = x) (x \is real).
Proof.
apply: (iffP idP); last exact: conj_id_real.
case/orP => [x_ge0|x_le0]; first by rewrite -[x](normr_idP _) ?normCJ.
apply: (can_inj (@opprK _)); rewrite -rmorphN.
by rewrite -[-x](normr_idP _) ?oppr_ge0 ?normCJ.
Qed.

Definition eqrJC x := sameP eqP (@realC_conjP x).

Lemma invC_norm x : x^-1 = `|x| ^- 2 * x^*.
Proof.
have [-> | nx_x] := eqVneq x 0; first by rewrite conjC0 mulr0 invr0.
by rewrite normC_def sqrtCK invfM divfK ?conjC_eq0.
Qed.

Lemma geC0_conj x : 0 <= x -> x^* = x.
Proof. by move=> /ger0_real /realC_conjP. Qed.

Lemma geC0_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x_ge0; rewrite pexpr_eq1. Qed.

Lemma normC_add_eq x y : `|x + y| = `|x| + `|y| -> 
  exists2 k, `|k| = 1 & ((x == `|x| * k) && (y == `|y| * k)).
Proof.
move=> hxy; pose s z := z / `|z|; have congr_sqr := congr1 (fun z => z ^+ 2).
have norm1 z: z != 0 -> (`|s z| = 1) * (`|z| * s z = z).
  move=> z_neq0; rewrite mulrC divfK ?normr_eq0 //; split => //.
  by rewrite /s normrM normfV normr_id divff ?normr_eq0.
have [-> | ntx] := eqVneq x 0.
  have [-> | nty] := eqVneq y 0.
    by exists 1; rewrite ?mulr1 ?normr1 ?normr0 ?eqxx.
  by exists (s y); rewrite !norm1 // normr0 mul0r !eqxx.
exists (s x); rewrite ?norm1 ?eqxx //=.
have [-> | nty] := eqVneq y 0; first by rewrite normr0 mul0r.
(* rewrite -{1}[x]norm1 // -{1}[y]norm1 //. *)
move/congr_sqr: hxy; rewrite sqrrD normCK rmorphD mulrDl !mulrDr !mulCJ.
rewrite addrA => /addIr; rewrite -addrA -normrM -mulr_natr => /addrI def2xy.
have eq_xy: x * y^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -mulCJ_eq0 rmorphB !rmorphM !conjCK.
  rewrite -(mulrC x) -(mulrC y) [_ * _]mulrC -[_ - _]opprB mulNr -expr2.
  move/congr_sqr/esym/eqP: def2xy; rewrite exprMn normCK -natrX.
  rewrite mulr_natr rmorphM mulrA [_ * _]mulrC -mulrA mulrCA mulrA.
  by rewrite -subr_sqrDB addrC -[_ == _]subr_eq0 addrK.
have{eq_xy def2xy} def_xy: y * x^* = `|x * y|.
  move: def2xy; rewrite eq_xy -mulr2n -mulr_natr => /mulIf -> //.
  by rewrite pnatr_eq0.
apply/eqP/(@mulfI _ (`|x| ^+ 2)); first by rewrite expf_eq0 normr_eq0.
rewrite {1}normCK mulrAC -mulrA def_xy normrM mulrC -!mulrA; congr (_ * _).
by rewrite mulrCA; congr (_ * _); rewrite mulrC divfK ?normr_eq0.
Qed.

Lemma normC_sum_eq (I : finType) (P : pred I) (F : I -> algC) :
     `|\sum_(i | P i) F i| = \sum_(i | P i) `|F i| ->
   exists2 k, `|k| = 1 & forall i, P i -> F i = `|F i| * k.
Proof.
have [i /andP[Pi nzFi] | F0] := pickP [pred i | P i && (F i != 0)]; last first.
  exists 1 => [|i Pi]; first exact: normr1.
  by case/nandP: (F0 i) => [/negP[]// | /negbNE/eqP->]; rewrite normr0 mul0r.
rewrite !(bigD1 i Pi) /=; set Q := fun _ => _ : bool => norm_sumF.
rewrite -normr_eq0 in nzFi; set c := F i / `|F i|; exists c => [|j Pj].
  by rewrite normrM normfV normr_id divff.
have [Qj | /nandP[/negP[]// | /negbNE/eqP->]] := boolP (Q j); last first.
  by rewrite mulrC divfK.
have: `|F i + F j| = `|F i| + `|F j|.
  do [rewrite !(bigD1 j Qj) /=; set z := \sum_(k | _) `|_|] in norm_sumF.
  apply/eqP; rewrite eqr_le ler_norm_add -(ler_add2r z) -addrA -norm_sumF addrA.
  by rewrite (ler_trans (ler_norm_add _ _)) // ler_add2l ler_norm_sum.
case/normC_add_eq=> k _ /andP[/eqP/(canLR (mulKf nzFi)) <- /eqP].
by rewrite -(mulrC (F i)).
Qed.

Lemma normC_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
    `|\sum_(i | P i) F i| = (\sum_(i | P i) `|F i|) ->
     (forall i, P i -> `|F i| = 1) ->
   exists2 k, `|k| = 1 & forall i, P i -> F i = k.
Proof.
case/normC_sum_eq=> k k1 defF normF.
by  exists k => // i Pi; rewrite defF // normF // mul1r.
Qed.

Lemma normC_sum_upper (I : finType) (P : pred I) (F G : I -> algC) :
     (forall i, P i -> `|F i| <= G i) ->
     \sum_(i | P i) F i = \sum_(i | P i) G i ->
   forall i, P i -> F i = G i.
Proof.
set sumF := \sum_(i | _) _; set sumG := \sum_(i | _) _ => leFG eq_sumFG.
have posG i: P i -> 0 <= G i by move/leFG; apply: ler_trans; exact: normr_ge0.
have norm_sumG: `|sumG| = sumG by rewrite ger0_norm ?sumr_ge0.
have norm_sumF: `|sumF| = \sum_(i | P i) `|F i|.
  apply/eqP; rewrite eqr_le ler_norm_sum eq_sumFG norm_sumG -subr_ge0 -sumrB.
  by rewrite sumr_ge0 // => i Pi; rewrite subr_ge0 ?leFG.
have [k _ defF] := normC_sum_eq norm_sumF.
have [/(psumr_eq0P posG) G0 i Pi | nz_sumG] := eqVneq sumG 0.
  by apply/eqP; rewrite G0 // -normr_eq0 eqr_le normr_ge0 -(G0 i Pi) leFG.
have k1: k = 1.
  apply: (mulfI nz_sumG); rewrite mulr1 -{1}norm_sumG -eq_sumFG norm_sumF.
  by rewrite mulr_suml -(eq_bigr _ defF).
have /psumr_eq0P eqFG i : P i -> 0 <= G i - F i.
  by move=> Pi; rewrite subr_ge0 defF // k1 mulr1 leFG.
move=> i /eqFG/(canRL (subrK _))->; rewrite ?add0r //.
by rewrite sumrB -/sumF eq_sumFG subrr.
Qed.

Definition getNatC x :=
  if insub x : {? c | 0 <= c} is Some c then
    val (sigW (algC_archimedean (valP c)))
  else 0%N.

Lemma getNatC_def x (n := getNatC x) :
  if 0 <= x then (n%:R <= x < n.+1%:R) else n == 0%N.
Proof.
rewrite /n /getNatC; case: ifPn => [le0x | not_le0x]; last by rewrite insubN.
by rewrite insubT //=; case: sigW.
Qed.

Lemma getNatC_nat n : getNatC (n%:R) = n.
Proof.
have:= getNatC_def n%:R; rewrite /= ler0n ler_nat ltr_nat.
case/andP=> H1 H2; apply: anti_leq => //.
by rewrite H1 // -ltnS -[(getNatC _).+1]addn1.
Qed.

Definition isNatC c := c == (getNatC c)%:R.

Lemma isNatCP c : reflect (exists n, c = n%:R) (isNatC c).
Proof.
apply: (iffP idP)=> [H | [n H]]; first by exists (getNatC c); apply/eqP.
by rewrite H /isNatC getNatC_nat.
Qed.

Lemma isNatC_nat n : isNatC (n%:R).
Proof. by apply/isNatCP; exists n. Qed.
Lemma isNatC_0 : isNatC 0. Proof. exact: (isNatC_nat 0). Qed.
Lemma isNatC_1 : isNatC 1. Proof. exact: (isNatC_nat 1). Qed.
Hint Resolve isNatC_0 isNatC_1.

Lemma isNatC_add c1 c2 : isNatC c1 -> isNatC c2 -> isNatC (c1 + c2).
Proof.
by case/isNatCP=> n1 ->; case/isNatCP=> n2 ->; rewrite -natrD isNatC_nat.
Qed.

Lemma isNatC_mul c1 c2 : isNatC c1 -> isNatC c2 -> isNatC (c1 * c2).
Proof.
by case/isNatCP=> n1 ->; case/isNatCP=> n2 ->; rewrite -natrM isNatC_nat.
Qed.

Lemma isNatC_exp x n : isNatC x -> isNatC (x ^+ n).
Proof. by move=> Nx; elim: n => // n IHn; rewrite exprS isNatC_mul. Qed.

Lemma isNatC_sum (I : Type) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, P i -> isNatC (F i)) -> isNatC (\sum_(j <- r | P j) F j).
Proof. by move=> H; apply big_ind=> //; exact: isNatC_add. Qed.

Lemma isNatC_muln x n : isNatC x -> isNatC (x *+ n).
Proof. by elim: n => // n IH Hx; rewrite mulrSr isNatC_add // IH. Qed.

Lemma posC_Nat c : isNatC c -> 0 <= c.
Proof. by case/isNatCP=> n ->; exact: ler0n. Qed.

Lemma isNatC_conj c : isNatC c -> c^* = c.
Proof. by case/isNatCP=> n ->; exact: conjC_nat. Qed.

Lemma isNatC_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
     (forall i, P i -> isNatC (F i)) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := getNatC (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF/eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -eqC_nat natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

Lemma real_normCK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Proof. by move=> xR; rewrite normCK (realC_conjP _ _). Qed.

(* We mimic Z by a sign and a natural number *)
Definition getIntC x :=
  if 0 <= x then (false, getNatC x) else (true, getNatC (- x)).

Definition isIntC x := x == (let: (b, n) := getIntC x in (-1) ^+ b * n%:R).

Lemma isIntCP x : isIntC x -> {e : bool & {n | x = (-1) ^+ e * n%:R}}.
Proof. by move/(x =P _); case: (getIntC x) => e n; exists e, n. Qed.

Lemma isIntCE x : isIntC x = isNatC x || isNatC (- x).
Proof.
apply/idP/idP=> [/isIntCP[b [n ->]] | ].
  by rewrite mulr_sign; case: b; rewrite ?opprK ?isNatC_nat ?orbT.
rewrite /isIntC /getIntC => /orP[] /isNatCP[n def_x].
  by rewrite def_x /= ler0n mul1r getNatC_nat.
rewrite -{-4}[x]opprK {x}def_x getNatC_nat oppr_ge0 lern0.
by case: n => [|n]; rewrite /= ?mulN1r // mul1r oppr0 (getNatC_nat 0).
Qed.

Lemma isIntC_Nat x : isNatC x -> isIntC x.
Proof. by rewrite isIntCE => ->. Qed.

Lemma isIntC_nat n : isIntC (n%:R).
Proof. by rewrite isIntCE isNatC_nat. Qed.
Lemma isIntC_0 : isIntC 0. Proof. exact: (isIntC_nat 0). Qed.
Lemma isIntC_1 : isIntC 1. Proof. exact: (isIntC_nat 1). Qed.
Hint Resolve isIntC_0 isIntC_1.

Lemma isIntC_opp x : isIntC (- x) = isIntC x.
Proof. by rewrite !isIntCE opprK orbC. Qed.

Lemma isIntC_mul_sign n x : isIntC ((-1) ^+ n * x) = isIntC x.
Proof. by rewrite -signr_odd mulr_sign fun_if isIntC_opp if_same. Qed.

Lemma isIntC_sign n : isIntC ((-1) ^+ n).
Proof. by rewrite -[_ ^+ _]mulr1 isIntC_mul_sign (isIntC_nat 1). Qed.

Lemma isIntC_add x y : isIntC x -> isIntC y -> isIntC (x + y).
Proof.
move=> /isIntCP[e [m ->]] /isIntCP[b [n ->]].
without loss le_nm: e b m n / (n <= m)%N.
  by move=> IH; case/orP: (leq_total n m) => /IH //; rewrite addrC.
rewrite -(addKb e b) signr_addb -mulrA -mulrDr isIntC_mul_sign mulr_sign.
by case: ifP => _; rewrite -(natrD, natrB) // isIntC_nat.
Qed.

Lemma isIntC_sub x y : isIntC x -> isIntC y -> isIntC (x - y).
Proof. by move=> Zx Zy; rewrite isIntC_add ?isIntC_opp. Qed.

Lemma isIntC_mul x y : isIntC x -> isIntC y -> isIntC (x * y).
Proof.
move=> /isIntCP[e [m ->]] /isIntCP[b [n ->]].
by rewrite -mulrA isIntC_mul_sign mulrCA isIntC_mul_sign -natrM isIntC_nat.
Qed.

Lemma isIntC_exp x n : isIntC x -> isIntC (x ^+ n).
Proof. by move=> Zx; elim: n => // n IHn; rewrite exprS isIntC_mul. Qed.

Lemma isIntC_sum (I : Type) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, P i -> isIntC (F i)) -> isIntC (\sum_(j <- r | P j) F j).
Proof. by move=> Z_F; apply big_ind=> //; exact: isIntC_add. Qed.

Lemma isIntC_conj c : isIntC c -> c^* = c.
Proof. by case/isIntCP=> b [n ->]; rewrite rmorphM rmorph_sign rmorph_nat. Qed.

Lemma isIntC_Real x : isIntC x -> x \is real.
Proof. by move/isIntC_conj/realC_conjP. Qed.

Lemma int_normCK x : isIntC x -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/isIntC_Real/real_normCK. Qed.

Lemma isIntC_signE x : isIntC x -> x = (-1) ^+ (x < 0)%C * `|x|.
Proof. by move/isIntC_Real/realEsign. Qed.

Lemma normIntC_Nat x : isIntC x -> isNatC `|x|.
Proof.
case/isIntCP=> b [n ->].
by rewrite normrM normr_sign mul1r normr_nat isNatC_nat.
Qed.

Lemma isIntC_pos x : 0 <= x -> isIntC x = isNatC x.
Proof. by rewrite /isIntC /getIntC => ->; rewrite mul1r. Qed.

Lemma isNatC_posInt x : isNatC x = isIntC x && (0 <= x).
Proof.
by rewrite -(andb_idr (@posC_Nat x)); apply: andb_id2r => /isIntC_pos.
Qed.

Lemma isNatC_exp_even x n : ~~ odd n -> isIntC x -> isNatC (x ^+ n).
Proof.
rewrite -dvdn2 => /dvdnP[m ->] Zx; rewrite isNatC_posInt isIntC_exp //.
by rewrite exprM -int_normCK ?isIntC_exp // exprn_ge0 ?posC_norm.
Qed.

Lemma isIntC_normC_ge1 x : isIntC x -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0; case/normIntC_Nat/isNatCP=> n ->.
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma isIntC_expr2_ge1 x : isIntC x -> x != 0 -> 1 <= x ^+ 2.
Proof.
move=> Zx nz_x; rewrite -int_normCK //.
by rewrite expr_ge1 ?normr_ge0 ?isIntC_normC_ge1.
Qed.

Definition dvdC x y := if x == 0 then y == 0 else isIntC (y / x).
Notation dvdNC n y := (dvdC n%:R y).

Lemma dvdCP x y : reflect (exists2 z, isIntC z & y = z * x) (dvdC x y).
Proof.
rewrite /dvdC; have [-> | nz_x] := altP eqP.
  by apply: (iffP eqP) => [-> | [z _ ->]]; first exists 0; rewrite ?mulr0.
apply: (iffP idP) => [Zxp | [z Zz ->]]; last by rewrite mulfK.
by exists (y / x); rewrite ?divfK.
Qed.

Lemma dvdCP_nat x y : 0 <= x -> 0 <= y -> dvdC x y -> {n | y = n%:R * x}.
Proof.
move=> x_ge0 y_ge0 x_dv_y; apply: sig_eqW.
case/dvdCP: x_dv_y => z Zz -> in y_ge0 *; move: x_ge0 y_ge0 Zz.
rewrite ler_eqVlt => /predU1P[<- | ]; first by exists 22; rewrite !mulr0.
by move=> /pmulr_lge0-> /isIntC_pos-> /isNatCP[n ->]; exists n.
Qed.

Lemma dvdC0 x : dvdC x 0.
Proof. by rewrite /dvdC mul0r isIntC_0 eqxx if_same. Qed.

Lemma dvd0C x : dvdC 0 x = (x == 0).
Proof. by rewrite /dvdC eqxx. Qed.

Lemma dvdC_opp x y : dvdC x (- y) = dvdC x y.
Proof. by rewrite /dvdC mulNr isIntC_opp oppr_eq0. Qed.

Lemma dvdC_mulrn p x : isIntC x -> dvdNC p (x *+ p).
Proof. by move=> Zx; apply/dvdCP; exists x; rewrite ?mulr_natr ?IsIntC_nat. Qed.

Lemma dvdC_mul_sign x e y : dvdC x ((-1) ^+ e * y) = dvdC x y.
Proof. by rewrite -signr_odd mulr_sign fun_if dvdC_opp if_same. Qed.

Lemma dvdC_nat p n : dvdNC p (n%:R) = (p %| n)%N.
Proof.
rewrite /dvdC isIntC_pos ?mulr_ge0 ?invr_ge0 ?ler0n // !pnatr_eq0.
have [/eqP ->|nz_p] := ifPn; first by rewrite dvd0n.
apply/isNatCP/dvdnP=> [[q def_q] | [q ->]]; exists q.
  by apply/eqP; rewrite -eqC_nat natrM -def_q divfK ?pnatr_eq0. 
by rewrite natrM mulfK ?pnatr_eq0.
Qed.

Lemma dvdC_int p x : isIntC x -> dvdNC p x = (p %| getNatC `|x|%R)%N.
Proof.
case/isIntCP=> e [n ->{x}]; rewrite dvdC_mul_sign normrM normr_sign mul1r.
by rewrite normr_nat getNatC_nat dvdC_nat.
Qed.

Lemma dvdC_add x y z : dvdC x y -> dvdC x z -> dvdC x (y + z).
Proof.
rewrite /dvdC; case: ifP => [_ /eqP-> | _ p_x p_y]; first by rewrite add0r.
by rewrite mulrDl isIntC_add.
Qed.

Lemma dvdC_addl x y z : dvdC x y -> dvdC x (y + z) = dvdC x z.
Proof.
move=> x_dv_y; apply/idP/idP; last exact: dvdC_add.
by rewrite -{2}(addKr y z); apply: dvdC_add; rewrite dvdC_opp.
Qed.

Lemma dvdC_mull x y z : isIntC y -> dvdC x z -> dvdC x (y * z).
Proof.
move=> Zy /dvdCP[m Zm ->]; apply/dvdCP.
by exists (y * m); rewrite ?mulrA ?isIntC_mul.
Qed.

Lemma dvdC_mulr x y z : isIntC y -> dvdC x z -> dvdC x (z * y).
Proof. by rewrite mulrC; exact: dvdC_mull. Qed.

Lemma dvdC_trans x y z : dvdC x y -> dvdC y z -> dvdC x z.
Proof. by move=> x_dv_y /dvdCP[m Zm ->]; exact: dvdC_mull. Qed.

Lemma dvdC_refl x : dvdC x x.
Proof. by apply/dvdCP; exists 1; rewrite ?mul1r. Qed.
Hint Resolve dvdC_refl.

Section AutC.

Variable u : {rmorphism algC -> algC}.

Lemma rmorph_NatC z : isNatC z -> u z = z.
Proof. by case/isNatCP=> n ->; exact: rmorph_nat. Qed.

Lemma rmorph_IntC z : isIntC z -> u z = z.
Proof.
by rewrite isIntCE => /orP[]/rmorph_NatC //; rewrite rmorphN => /oppr_inj.
Qed.

End AutC.

Section AutLmodC.

Variables (U V : lmodType algC) (f : {additive U -> V}).

Lemma raddfZ_NatC a u : isNatC a -> f (a *: u) = a *: f u. 
Proof. by case/isNatCP=> n ->; exact: raddfZnat. Qed.

Lemma raddfZ_IntC a u : isIntC a -> f (a *: u) = a *: f u. 
Proof.
by move/eqP->; case: (getIntC a) => e n; rewrite -!scalerA raddfZsign raddfZnat.
Qed.

End AutLmodC.

Section AlgCRect.
(* Imaginary numbers and rectangular coordinates. This is proof-of-concept    *)
(* only, and not currently used in the rest of the formalization (it was part *)
(* of a failed early automorphism construction attempt).                      *)
Definition algCi : algC := sqrtC (- 1).
Definition alg_Re x := (x + x^*) / 2%:R.
Definition alg_Im x := (x - x^*) / (algCi *+ 2).

Lemma sqr_algCi : algCi ^+ 2 = -1. Proof. exact: sqrtCK. Qed.

Lemma algCi_nonReal : algCi \isn't real.
Proof.
(* :BUG: hidden evar here in v8.4 ! *)
(* apply: contraFN (ltr_geF ltr01) => /real_normCK norm_i. *)
have /ltr_geF : 0 < 1 :> algC by exact ltr01.
apply: contraFN  => /real_normCK norm_i.
by rewrite -oppr_ge0 -sqr_algCi -norm_i exprn_ge0.
Qed.

Lemma algCi_neq0 : algCi != 0.
Proof. by apply: contraNneq algCi_nonReal => ->; exact: isIntC_Real. Qed.

Lemma normCi : `|algCi| = 1.
Proof.
apply/eqP.
by rewrite -(@pexpr_eq1 _ _ 2) ?normr_ge0 // -normrX sqr_algCi normrN1.
Qed.

Lemma conjCi : algCi^* = - algCi.
Proof.
have: root (\prod_(z <- [:: algCi; -algCi]) ('X - z%:P)) algCi^*.
  rewrite big_cons big_seq1 raddfN opprK -subr_sqr -rmorphX sqr_algCi.
  by rewrite /root !hornerE -expr2 -rmorphX sqr_algCi rmorphN rmorph1 subrr.
by rewrite root_prod_XsubC !inE eqrJC (negPf algCi_nonReal) => /eqP.
Qed.

Lemma invCi : algCi^-1 = - algCi.
Proof. by rewrite invC_norm normCi conjCi expr1n invr1 mul1r. Qed.

Lemma algCrect x : x = alg_Re x + algCi * alg_Im x.
Proof. 
rewrite mulrCA -mulr_natr invfM mulVKf ?algCi_neq0 // -mulrDl.
by rewrite addrCA !addrA addrK -mulr2n -mulr_natr mulfK ?pnatr_eq0.
Qed.

Lemma alg_Re_Real x : alg_Re x \is real.
Proof. by rewrite -eqrJC fmorph_div rmorph_nat rmorphD conjCK addrC. Qed.

Lemma alg_Im_Real x : alg_Im x \is real.
Proof.
rewrite -eqrJC fmorph_div rmorphMn conjCi mulNrn invrN mulrN -mulNr.
by rewrite rmorphB conjCK opprB.
Qed.

Lemma alg_Re_rect x y : x \is real -> y \is real -> alg_Re (x + algCi * y) = x.
Proof.
move=> Rx Ry; rewrite /alg_Re rmorphD addrCA !addrA rmorphM conjCi mulNr.
by rewrite !(realC_conjP _ _) // addrK -mulr2n -(mulr_natr x) mulfK ?pnatr_eq0.
Qed.

Lemma alg_Im_rect x y : x \is real -> y \is real -> alg_Im (x + algCi * y) = y.
Proof.
move=> Rx Ry; rewrite /alg_Im rmorphD opprD addrAC -!addrA rmorphM conjCi.
rewrite mulNr opprK !(realC_conjP _ _) // addNKr -(mulrC y) -mulr2n -mulrnAr.
by rewrite mulfK // -mulr_natr mulf_neq0 ?algCi_neq0 ?pnatr_eq0.
Qed.

End AlgCRect.


Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).

Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).

Local Hint Resolve (@intr_inj [numIdomainType of algC]).
Local Notation QtoC_M := (ratr_rmorphism [numFieldType of algC]).

(* Integer subring; this should replace isIntC / getIntC. *)
Lemma isIntC_int (m : int) : isIntC m%:~R.
Proof.
by rewrite [m]intEsign rmorphM rmorph_sign isIntC_mul_sign isIntC_nat.
Qed.

Definition getCint z := (-1) ^+ (z < 0)%R * (getNatC `|z|)%:Z.
Local Notation CtoZ := getCint.

Lemma getCintK z : isIntC z -> {for z, cancel CtoZ ZtoC}.
Proof.
rewrite /{for z, _} /= => Zz; rewrite rmorphM rmorph_sign /= -pmulrn.
by rewrite -(eqP (normIntC_Nat Zz)) -isIntC_signE.
Qed.

Lemma CintrK : cancel ZtoC CtoZ. 
Proof.
move=> z; rewrite [z]intEsign rmorphM rmorph_sign /= /getCint.
rewrite normrM normr_sign mul1r normr_nat getNatC_nat; congr (_ ^+ _ * _).
case: z => n; first by rewrite mul1r ler_gtF ?ler0n.
by rewrite -oppr_gt0 mulN1r opprK ltr0n.
Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  isNatC x -> x \in kS.
Proof. by case/isNatCP=> n ->; apply: rpred_nat. Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  isIntC x -> x \in kS.
Proof. by move/getCintK <-; apply: rpred_int. Qed.

Lemma getCint0 : CtoZ 0 = 0. Proof. exact: (CintrK 0). Qed.
Hint Resolve getCint0.

Lemma getCintpK (p : {poly algC}) :
  all isIntC p -> pZtoC (map_poly CtoZ p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/getCintK// | _]; rewrite getCint0.
Qed.

Lemma getCintpP (p : {poly algC}) : all isIntC p -> {q | p = pZtoC q}.
Proof. by exists (map_poly CtoZ p); rewrite getCintpK. Qed.

(* Reconstructed rational subring. *)
(* Note that this proof is tweaked so that it depends only on the fact that *)
(* QtoC is a field embedding, and not on the order structure assumed for C. *)
(* Thus, it could be used in (and moved to) the construction of C.          *)
Fact getCrat_subproof : {CtoQ | cancel QtoC CtoQ}.
Proof.
have QtoCinj: injective QtoC by exact: fmorph_inj.
have ZtoQinj: injective ZtoQ by exact: intr_inj.
have defZtoC: ZtoC =1 QtoC \o ZtoQ by move=> m; rewrite /= rmorph_int.
suffices CtoQ x: {xa : seq rat | forall a, x = QtoC a -> a \in xa}.
  exists (fun x => let: exist xa _ := CtoQ x in xa`_(index x (map QtoC xa))).
  move=> a /=; case: (CtoQ _) => xa /= /(_ a (erefl _)) xa_a; apply: QtoCinj.
  by rewrite -(nth_map _ 0) ?nth_index -?(size_map QtoC) ?index_mem ?map_f.
have [-> | nz_x] := eqVneq x 0.
  by exists [:: 0] => a; rewrite inE -(inj_eq QtoCinj) rmorph0 => <-.
have /sig2_eqW[p nz_p px0] := algC_algebraic x.
have {nz_p} nz_p : p != 0 by apply: contraNneq nz_p => ->; rewrite map_polyC.
without loss{nz_x} nz_p0: p nz_p px0 / p`_0 != 0.
  move=> IH; elim/poly_ind: p nz_p => [/eqP// | p a IHp nz_p] in px0.
  have [a0 | nz_a] := eqVneq a 0; last first.
    by apply: IH nz_p px0 _; rewrite coefD coefC coefMX add0r.
  rewrite a0 addr0 mulrC mulf_eq0 -size_poly_eq0 size_polyX in nz_p px0.
  apply: IHp nz_p _; rewrite rmorphM rootM /= map_polyX in px0.
  by rewrite {1}/root hornerX (negPf nz_x) in px0.
pose p_n := lead_coef p; pose q e m : rat := (-1) ^+ e * m%:R / `|p_n|%:R.
exists [seq q e m | e <- iota 0 2, m <- divisors `|p_n * p`_0|] => a Dx.
rewrite {x}Dx (eq_map_poly defZtoC) map_poly_comp fmorph_root /root in px0.
have [n Dn]: {n | size p = n.+2}.
  exists (size p - 2)%N; rewrite -addn2 subnK // ltnNge. 
  apply: contra nz_p => /size1_polyC Dp; rewrite Dp polyC_eq0.
  by rewrite Dp map_polyC hornerC intr_eq0 in px0.
pose qn (c : int) m := c * (m ^ n.+1)%N.
pose Eqn (c0 c1 c2 : int) d m := qn c0 d + qn c1 m = c2 * d * m.
have Eqn_div c1 c2 d m c0: coprime m d -> Eqn c0 c1 c2 d m -> (m %| `|c0|)%N.
  move=> co_m_d /(canRL (addrK _))/(congr1 (dvdn m \o absz))/=.
  rewrite abszM mulnC Gauss_dvdr ?coprime_expr // => ->.
  by rewrite -mulNr expnSr PoszM mulrA -mulrDl abszM dvdn_mull.
pose m := numq a; pose d := `|denq a|%N.
have co_md: coprime `|m| d by exact: coprime_num_den.
have Dd: denq a = d by rewrite /d; case: (denq a) (denq_gt0 a).
have{px0} [c Dc1 Emd]: {c | `|c.1|%N = `|p_n|%N & Eqn p`_0 c.1 c.2 d `|m|%N}.
  pose e : int := (-1) ^+ (m < 0)%R.
  pose r := \sum_(i < n) p`_i.+1 * m ^+ i * (d ^ (n - i.+1))%N.
  exists (e ^+ n.+1 * p_n, - (r * e)); first by rewrite -exprM abszMsign.
  apply/eqP; rewrite !mulNr -addr_eq0 (mulrAC r) -!mulrA -intEsign addrAC.
  apply/eqP; transitivity (\sum_(i < n.+2) p`_i * m ^+ i * (d ^ (n.+1 - i))%N).
    rewrite big_ord_recr big_ord_recl subnn !mulr1; congr (_ + _ + _).
      rewrite mulr_suml; apply: eq_bigr => i _; rewrite -!mulrA; congr (_ * _).
      by rewrite /= mulrC -!mulrA -exprS mulrA -PoszM -expnSr mulrC -subSn.
    rewrite /qn /p_n lead_coefE Dn mulrAC mulrC; congr (_ * _).
    rewrite -[Posz (_ ^ _)]intz -pmulrn natrX pmulrn intz.
    by rewrite -exprMn -intEsign.
  apply: (ZtoQinj); rewrite rmorph0 -(mul0r (ZtoQ (d ^ n.+1)%N)) -(eqP px0).
  rewrite rmorph_sum horner_coef (size_map_inj_poly ZtoQinj) // Dn mulr_suml.
  apply: eq_bigr => i _; rewrite coef_map !rmorphM !rmorphX /= numqE Dd.
  by rewrite -!pmulrn !natrX exprMn -!mulrA -exprD subnKC ?leq_ord.
have{Dc1} /dvdnP[d1 Dp_n]: (d %| `|p_n|)%N.
  rewrite -Dc1 (Eqn_div p`_0 c.2 `|m|%N) 1?coprime_sym //.
  by rewrite /Eqn mulrAC addrC //.
have [d1_gt0 _]: (0 < d1 /\ 0 < d)%N.
  by apply/andP; rewrite -muln_gt0 -Dp_n absz_gt0 lead_coef_eq0. 
have dv_md1_p0n: (`|m| * d1 %| `|p_n| * `|(p`_0)%R|)%N.
  by rewrite Dp_n mulnC -mulnA dvdn_pmul2l ?dvdn_mull // (Eqn_div c.1 c.2 d).
apply/allpairsP; exists ((m < 0)%R : nat, `|m| * d1)%N.
rewrite mem_iota ltnS leq_b1; split=> //.
  by rewrite abszM -dvdn_divisors // muln_gt0 !absz_gt0 lead_coef_eq0 nz_p.
rewrite /q Dp_n !natrM invfM !mulrA !pmulrn -rmorphMsign -intEsign /=.
by rewrite -Dd mulfK ?divq_num_den // intr_eq0 -lt0n.
Qed.

Definition getCrat := sval getCrat_subproof.
Local Notation CtoQ := getCrat.
Definition Crat : pred algC := (fun x => x == QtoC (CtoQ x)).
Fact Crat_key : pred_key Crat. Proof. by []. Qed.
Canonical Crat_keyed := KeyedPred Crat_key.

Lemma CratrK : cancel QtoC CtoQ.
Proof. by rewrite /getCrat; case: getCrat_subproof. Qed.

Lemma getCratK : {in Crat, cancel CtoQ QtoC}.
Proof. by move=> x /eqP. Qed.

Lemma ratr_Crat (a : rat) : QtoC a \in Crat.
Proof. by rewrite unfold_in /Crat CratrK. Qed.

Lemma CratP x : reflect (exists a, x = QtoC a) (x \in Crat).
Proof.
by apply: (iffP eqP) => [-> | [a ->]]; [exists (CtoQ x) | rewrite CratrK].
Qed.

Lemma Crat0 : 0 \in Crat. Proof. by apply/CratP; exists 0; rewrite rmorph0. Qed.
Lemma Crat1 : 1 \in Crat. Proof. by apply/CratP; exists 1; rewrite rmorph1. Qed.
Hint Resolve Crat0 Crat1.

Fact Crat_divring_closed : divring_closed Crat.
Proof.
split=> // _ _ /CratP[x ->] /CratP[y ->].
  by rewrite -rmorphB ratr_Crat.
by rewrite -fmorph_div ratr_Crat.
Qed.
Canonical Crat_opprPred := OpprPred Crat_divring_closed.
Canonical Crat_addrPred := AddrPred Crat_divring_closed.
Canonical Crat_mulrPred := MulrPred Crat_divring_closed.
Canonical Crat_zmodPred := ZmodPred Crat_divring_closed.
Canonical Crat_semiringPred := SemiringPred Crat_divring_closed.
Canonical Crat_smulrPred := SmulrPred Crat_divring_closed.
Canonical Crat_divrPred := DivrPred Crat_divring_closed.
Canonical Crat_subringPred := SubringPred Crat_divring_closed.
Canonical Crat_sdivrPred := SdivrPred Crat_divring_closed.
Canonical Crat_divringPred := DivringPred Crat_divring_closed.

Lemma rpred_Crat S (ringS : divringPred S) (kS : keyed_pred ringS) :
  {subset Crat <= kS}.
Proof. by move=> _ /CratP[a ->]; apply: rpred_rat. Qed.

Lemma CratV x : (x^-1 \in Crat) = (x \in Crat).
Proof. exact: rpredV. Qed.

Lemma CratXz m : {in Crat, forall x, x ^ m \in Crat}.
Proof. exact: rpredXint. Qed.

Lemma Crat_div : {in Crat &, forall x y, x / y \in Crat}.
Proof. exact: rpred_div. Qed.

Lemma conj_Crat z : z \in Crat -> z^* = z.
Proof. by move/getCratK <-; rewrite fmorph_div !rmorph_int. Qed.

Lemma Creal_Rat z : z \in Crat -> z \is real.
Proof. by move/conj_Crat/realC_conjP. Qed.

Lemma Cint_ratr a : isIntC (QtoC a) = (a \in Qint).
Proof.
apply/idP/idP=> [Za | /numqK <-]; last by rewrite rmorph_int isIntC_int.
apply/QintP; exists (CtoZ (QtoC a)); apply: (can_inj CratrK).
by rewrite rmorph_int getCintK.
Qed.

(* Minimal polynomial. *)
Fact minCpoly_subproof (x : algC) :
  {p | p \is monic & forall q, root (pQtoC q) x = (p %| q)%R}.
Proof.
have /sig2_eqW[p0 nz_p0 p0x] := algC_algebraic x.
have {nz_p0} nz_p0 : p0 != 0.
   by apply: contraNneq nz_p0 => ->; rewrite map_polyC.
have [r Dp0] := closed_field_poly_normal (pZtoC p0).
do [rewrite lead_coef_map_inj //; set d0 := _%:~R] in Dp0.
have{nz_p0} nz_d0: d0 != 0; first by rewrite intr_eq0 lead_coef_eq0.
have r_x: x \in r by rewrite Dp0 rootZ // root_prod_XsubC in p0x.
pose p_ (I : {set 'I_(size r)}) := \prod_(i <- enum I) ('X - (r`_i)%:P).
pose Qpx I := root (p_ I) x && all (mem Crat) (p_ I).
have{d0 p0 nz_d0 p0x Dp0} /minset_exists[I /minsetP[]]: Qpx setT.
  rewrite /Qpx; have ->: p_ setT = d0^-1 *: intrp p0.
     rewrite Dp0 scalerK // (big_nth 0) big_mkord /p_ big_filter /=.
     by apply: eq_bigl => i; rewrite inE.
   rewrite rootZ ?invr_eq0 // p0x; apply/(all_nthP 0)=> i _ /=.
   by rewrite coefZ mulrC coef_map Crat_div ?rpred_int.
case/andP=> pIx QpI minI _; pose p := map_poly CtoQ (p_ I).
have DpI: p_ I = pQtoC p.
  rewrite -[p_ I]coefK; apply/polyP=> i; rewrite -map_poly_comp !coef_poly.
  by case: ifP => //= lti_pI; rewrite getCratK //; exact: (all_nthP 0 QpI).
exists p; first by rewrite -(map_monic QtoC_M) -DpI monic_prod_XsubC.
move=> q; rewrite -(dvdp_map QtoC_M) -DpI.
apply/idP/idP=> [qx0 | /dvdpP[{q} q ->]]; last by rewrite rootM pIx orbT.
pose q1 := gcdp p q; have /dvdp_prod_XsubC[m Dq1]: pQtoC q1 %| p_ I.
  by rewrite gcdp_map DpI dvdp_gcdl.
pose B := [set i \in mask m (enum I)].
have{Dq1} Dq1: pQtoC q1 %= p_ B.
  congr (_ %= _): Dq1; apply: eq_big_perm.
  by rewrite uniq_perm_eq ?mask_uniq ?enum_uniq // => i; rewrite mem_enum inE.
rewrite -(minI B); first by rewrite -(eqp_dvdl _ Dq1) gcdp_map dvdp_gcdr.
  rewrite /Qpx -(eqp_root Dq1) gcdp_map root_gcd qx0 -DpI pIx.
  have{Dq1} /eqpP[[d1 d2] /= /andP[nz_d1 nz_d2] Dq1] := Dq1.
  rewrite -[p_ B](scalerK nz_d2) -Dq1 scalerA mulrC.
  have ->: d1 / d2 = (QtoC (lead_coef q1))^-1.
    have:= congr1 lead_coef Dq1; rewrite !lead_coefZ lead_coef_map.
    rewrite (monicP (monic_prod_XsubC _ _ _)) mulr1 => <-.
    by rewrite invfM mulVKf.
  apply/(all_nthP 0)=> i _; rewrite coefZ coef_map mulrC /=.
  by rewrite Crat_div ?ratr_Crat.
by apply/subsetP=> i; rewrite inE => /mem_mask; rewrite mem_enum.
Qed.

Definition minCpoly x : {poly algC} :=
  locked (pQtoC (s2val (minCpoly_subproof x))).

Lemma minCpolyP x :
   {p | minCpoly x = pQtoC p /\ p \is monic
      & forall q, root (pQtoC q) x = (p %| q)}.
Proof. by unlock minCpoly; case: (minCpoly_subproof x) => p /=; exists p. Qed.

Lemma minCpoly_monic x : minCpoly x \is monic.
Proof. by have [p [-> mon_p] _] := minCpolyP x; rewrite map_monic. Qed.

Lemma minCpoly_eq0 x : (minCpoly x == 0) = false.
Proof. exact/negbTE/monic_neq0/minCpoly_monic. Qed.

Lemma root_minCpoly x : root (minCpoly x) x.
Proof. by have [p [-> _] ->] := minCpolyP x. Qed.

Lemma size_minCpoly x : (1 < size (minCpoly x))%N.
Proof.
apply: contraFT (minCpoly_eq0 x); rewrite -leqNgt => /size1_polyC Dp.
by have /eqP := root_minCpoly x; rewrite Dp hornerC => ->.
Qed.

Section MoreAlgCaut.

Implicit Type nu : {rmorphism algC -> algC}.

Lemma Crat_aut nu x : (nu x \in Crat) = (x \in Crat).
Proof.
apply/idP/idP=> /CratP[a] => [|->]; last by rewrite fmorph_rat ratr_Crat.
by rewrite -(fmorph_rat nu) => /fmorph_inj->; apply: ratr_Crat.
Qed.

Lemma aut_Crat nu : {in Crat, nu =1 id}.
Proof. by move=> _ /CratP[a ->]; apply: fmorph_rat. Qed.

Lemma algC_invaut_subproof nu x : {y | nu y = x}.
Proof.
have [r Dp] := closed_field_poly_normal (minCpoly x).
suffices /mapP/sig2_eqW[y _ ->]: x \in map nu r by exists y.
rewrite -root_prod_XsubC; congr (root _ x): (root_minCpoly x).
have [q [Dq _] _] := minCpolyP x; rewrite Dq -(eq_map_poly (fmorph_rat nu)).
rewrite (map_poly_comp nu) -{q}Dq Dp (monicP (minCpoly_monic x)) scale1r.
rewrite rmorph_prod big_map; apply: eq_bigr => z _.
by rewrite rmorphB /= map_polyX map_polyC.
Qed.
Definition algC_invaut nu x := sval (algC_invaut_subproof nu x).

Lemma algC_invautK nu : cancel (algC_invaut nu) nu.
Proof. by move=> x; rewrite /algC_invaut; case: algC_invaut_subproof. Qed.

Lemma algC_autK nu : cancel nu (algC_invaut nu).
Proof. exact: inj_can_sym (algC_invautK nu) (fmorph_inj nu). Qed.

Fact algC_invaut_is_rmorphism nu : rmorphism (algC_invaut nu).
Proof. exact: can2_rmorphism (algC_autK nu) (algC_invautK nu). Qed.
Canonical algC_invaut_additive nu := Additive (algC_invaut_is_rmorphism nu).
Canonical algC_invaut_rmorphism nu := RMorphism (algC_invaut_is_rmorphism nu).

Lemma isNatC_rmorph nu x : isNatC (nu x) = isNatC x.
Proof.
by do [apply/idP/idP=> Nx; have:= rmorph_NatC nu Nx] => [/fmorph_inj <- | ->].
Qed.

Lemma isIntC_rmorph nu x : isIntC (nu x) = isIntC x.
Proof. by rewrite !isIntCE -rmorphN !isNatC_rmorph. Qed.

Lemma minCpoly_aut nu x : minCpoly (nu x) = minCpoly x.
Proof.
wlog suffices dvd_nu: nu x / minCpoly x %| minCpoly (nu x).
  apply/eqP; rewrite -eqp_monic ?minCpoly_monic //; apply/andP; split=> //.
  by rewrite -{2}(algC_autK nu x) dvd_nu.
have [[q [Dq _] min_q] [q1 [Dq1 _] _]] := (minCpolyP x, minCpolyP (nu x)).
rewrite Dq Dq1 dvdp_map -min_q -(fmorph_root nu) -map_poly_comp.
by rewrite (eq_map_poly (fmorph_rat nu)) -Dq1 root_minCpoly.
Qed.

End MoreAlgCaut.

End AlgebraicsTheory.


(* Fake algebraics *)

Module FakeAlg : AlgSig.

Parameter type : Type.

Parameter eqMixin : Equality.class_of type.
Canonical type_eqType := EqType type eqMixin.

Parameter choiceMixin : Choice.mixin_of type.
Canonical type_choiceType := ChoiceType type choiceMixin.

Parameter zmodMixin : GRing.Zmodule.mixin_of type.
Canonical type_zmodType := ZmodType type zmodMixin.

Parameter ringMixin : GRing.Ring.mixin_of [zmodType of type].
Canonical type_ringType := RingType type ringMixin.

Parameter mulC : commutative (@GRing.mul [ringType of type]).
Canonical type_comRingType := ComRingType type mulC.

Parameter unitRingMixin : GRing.UnitRing.mixin_of [ringType of type].
Canonical type_unitRingType := UnitRingType type unitRingMixin.

Canonical type_comUnitRingType := Eval hnf in [comUnitRingType of type].

Parameter idomain_axiom : GRing.IntegralDomain.axiom [ringType of type].
Canonical type_idomainType := IdomainType type idomain_axiom.

Parameter fieldMixin : GRing.Field.mixin_of [unitRingType of type].
Canonical type_fieldType := FieldType type fieldMixin.

Parameter numMixin : Num.mixin_of [ringType of type].
Canonical type_numIdomainType := NumIdomainType type numMixin.
Canonical type_numFieldType := NumFieldType type numMixin.

Parameter decFieldMixin : GRing.DecidableField.mixin_of [unitRingType of type].
Canonical type_decFieldType := DecFieldType type decFieldMixin.

Parameter closed_axiom : GRing.ClosedField.axiom [ringType of type].
Canonical type_closedFieldType := ClosedFieldType type closed_axiom.

Parameter conj : {rmorphism type -> type}.

Axiom conjK : involutive conj.
Axiom normCK : forall x : type, `|x| ^+ 2 = x * conj x.
Axiom type_algebraic : algebraic [ringType of type].

End FakeAlg.

Module FakeAlgTh := AlgebraicsTheory FakeAlg.
Export FakeAlgTh.
