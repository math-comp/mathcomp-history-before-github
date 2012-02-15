Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint div orderedalg qnum poly.

Import GRing.Theory ORing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section MoreRcf.

Variable R : rcfType.

Lemma sqrtr_subproof (x : R) : 
  {y | (0 <= y) && if 0 <= x then (y ^ 2 == x) else y == 0}.
Proof.
have [x_ge0|] := ger0P x; last by exists 0; rewrite lerr eqxx.
have [] := @poly_ivt _ ('X^2 - x%:P) 0 (x + 1).
* by rewrite ler_paddr ?ler01.
* rewrite !hornerD !hornerN !horner_exp !hornerC !hornerX.
  rewrite exprS mul0r sub0r oppr_le0 x_ge0 /= sqrrD1 -!addrA.
  by rewrite addr_ge0 ?mulr_ge0 // addrCA subrr addr0 addr_ge0 ?ler01.
move=> y /andP[y_ge0 _]; rewrite /root !hornerE subr_eq0.
by move/eqP <-; exists y; rewrite y_ge0 eqxx.
Qed.

Definition sqrtr (a : R) : R := projT1 (sqrtr_subproof a).

Lemma sqrtr_ge0 a : 0 <= sqrtr a.
Proof. by rewrite /sqrtr; case: sqrtr_subproof => x /= /andP []. Qed.
Hint Resolve sqrtr_ge0.

Lemma sqr_sqrtr a : 0 <= a -> (sqrtr a)^+2 = a.
Proof. 
move=> a_ge0; rewrite /sqrtr; case: sqrtr_subproof.
by move=> x /= /andP [_]; rewrite a_ge0 => /eqP.
Qed.

Lemma ler0_sqrtr a : a <= 0 -> sqrtr a = 0.
Proof. 
rewrite /sqrtr; case: sqrtr_subproof => x /=.
have [//|_ /andP [_ /eqP] //|->] := ltrgt0P a.
by rewrite mulf_eq0 orbb => /andP [_ /eqP].
Qed.

Lemma ltr0_sqrtr a : a < 0 -> sqrtr a = 0.
Proof. by move=> /ltrW; apply: ler0_sqrtr. Qed.

CoInductive sqrtr_spec (a : R) : R -> bool -> bool -> R -> Type :=
| IsNoSqrtr of a < 0 : sqrtr_spec a a false true 0
| IsSqrtr b of 0 <= b : sqrtr_spec a (b ^+ 2) true false b.

Lemma sqrtrP a : sqrtr_spec a a (0 <= a) (a < 0) (sqrtr a).
Proof.
have [a_ge0|a_lt0] := ger0P a.
  by rewrite -{1 2}[a]sqr_sqrtr //; constructor.
by rewrite ltr0_sqrtr //; constructor.
Qed.

(* move to orderedalg for any oIdomainType of with precondition a \in Rreal *)
Lemma sqr_ge0 (a : R) : 0 <= a ^+ 2.
Proof. by case: (ger0P a) => ?; [rewrite mulr_ge0|rewrite mulr_le0 ?ltrW]. Qed.

Lemma sqr_eq0 (a : R) : (a ^+ 2 == 0) = (a == 0).
Proof. by rewrite mulf_eq0 orbb. Qed.

Lemma sqrtr_sqr a : sqrtr (a ^+ 2) = `|a|.
Proof.
have /eqP : sqrtr (a ^+ 2) ^+2 = `|a| ^+ 2.
  by rewrite -normrX ger0_norm ?sqr_sqrtr ?sqr_ge0.
rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0 => /orP [/eqP-> //|ha].
have := sqrtr_ge0 (a ^+ 2); rewrite (eqP ha) oppr_ge0 normr_le0 => /eqP ->.
by rewrite normr0 oppr0.
Qed.

Lemma sqrtrM a b : 0 <= a -> 0 <= b ->
  sqrtr (a * b) = sqrtr a * sqrtr b.
Proof.
case: (sqrtrP a) => // {a} a a_ge0; case: (sqrtrP b) => // {b} b b_ge0 _ _.
by rewrite mulrMM sqrtr_sqr ger0_norm ?mulr_ge0.
Qed.

Lemma sqrtr0 : sqrtr 0 = 0.
Proof. by move: (sqrtr_sqr 0); rewrite exprS mul0r => ->; rewrite normr0. Qed.

Lemma sqrtr1 : sqrtr 1 = 1.
Proof. by move: (sqrtr_sqr 1); rewrite expr1n => ->; rewrite normr1. Qed.

Lemma sqrtr_eq0 a : (sqrtr a == 0) = (a <= 0).
Proof.
case: sqrtrP => [/ltrW ->|b]; first by rewrite eqxx.
case: ltrgt0P => [b_gt0|//|->]; last by rewrite exprS mul0r lerr.
by rewrite ltr_geF ?pmulr_rgt0.
Qed.

Lemma sqrtr_gt0 a : (0 < sqrtr a) = (0 < a).
Proof. by rewrite lt0r sqrtr_ge0 sqrtr_eq0 -ltrNge andbT. Qed.

Lemma eqr_sqrt (a b : R) : 0 <= a -> 0 <= b ->
  (sqrtr a == sqrtr b) = (a == b).
Proof.
move=> a_ge0 b_ge0; apply/eqP/eqP=> [HS|->] //.
by move: (sqr_sqrtr a_ge0); rewrite HS (sqr_sqrtr b_ge0).
Qed.

Lemma ler_wsqrtr : {homo sqrtr : a b / a <= b}.
Proof.
move=> a b /= le_ab; case: (boolP (0 <= a))=> [pa|]; last first.
  by rewrite -ltrNge; move/ltrW; rewrite -sqrtr_eq0; move/eqP->.
rewrite -(@ler_pexpn2r R 2) -?topredE /= ?sqrtr_ge0 //.
by rewrite !sqr_sqrtr // (ler_trans pa).
Qed.

Lemma ler_psqrt : {in >%R 0 &, {mono sqrtr : a b / a <= b}}.
Proof.
apply: homo_mono_in => x y; rewrite -!topredE /= => x_gt0 y_gt0.
rewrite !ltr_neqAle => /andP [neq_xy le_xy].
by rewrite ler_wsqrtr // eqr_sqrt ?ltrW // neq_xy.
Qed.

Lemma ler_sqrt a b : 0 < b -> (sqrtr a <= sqrtr b) = (a <= b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last by rewrite ler_psqrt.
by rewrite ler0_sqrtr // sqrtr_ge0 (ler_trans a_le0) ?ltrW.
Qed.

Lemma ltr_sqrt a b : 0 < b -> (sqrtr a < sqrtr b) = (a < b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite (lerW_mono_in ler_psqrt).
by rewrite ler0_sqrtr // sqrtr_gt0 b_gt0 (ler_lt_trans a_le0).
Qed.

End MoreRcf.


Reserved Notation "x +i* y" (at level 40, left associativity, format "x  +i*  y").
Reserved Notation "x -i* y" (at level 40, left associativity, format "x  -i*  y").

CoInductive cplx (R : Type) : Type := Cplx { Re : R; Im : R }.

(* Definition cplx_of(R : oFieldType) of (phant R) := cplx R. *)
(* Identity Coercion type_cplx_of : cplx_of >-> cplx. *)
(* Notation "{ 'cplx'  R }" := (cplx_of (Phant R)). *)

Definition to_cplx (F : ringType) (x : F) := Cplx x 0.
Notation "x %:C" := (to_cplx x)
  (at level 2, left associativity, format "x %:C")  : ring_scope.
Notation "x +i* y" := (Cplx x y) : ring_scope.
Notation "x -i* y" := (Cplx x (- y)) : ring_scope.
Notation "x *i " := (Cplx 0 x) (at level 8, format "x *i") : ring_scope.
Notation "''i'" := (Cplx 0 1) : ring_scope.

Module CplxEqChoice.
Section CplxEqChoice.

Variable R : Type.
Notation C := (cplx R).

Definition sqR_of_cplx (x : C) := let: a +i* b := x in [::a;  b].
Definition cplx_of_sqR (x : seq R) :=
  if x is [:: a; b] then Some (a +i* b) else None.

Lemma cplx_of_sqRK : pcancel sqR_of_cplx cplx_of_sqR.
Proof. by case. Qed.

End CplxEqChoice.
End CplxEqChoice.

Definition cplx_eqMixin (R : eqType) :=
  PcanEqMixin (@CplxEqChoice.cplx_of_sqRK R).
Definition cplx_choiceMixin  (R : choiceType) :=
  PcanChoiceMixin (@CplxEqChoice.cplx_of_sqRK R).

Canonical Structure cplx_eqType (R : eqType) :=
  EqType (cplx R) (cplx_eqMixin R).
Canonical Structure cplx_choiceType (R : choiceType) :=
  ChoiceType (cplx R) (cplx_choiceMixin R).

Lemma eq_cplx : forall (R : eqType) (x y : cplx R),
  (x == y) = (Re x == Re y) && (Im x == Im y).
Proof.
move=> R [a b] [c d] /=.
apply/eqP/andP; first by move=> [-> ->]; split.
by case; move/eqP->; move/eqP->.
Qed.

Lemma cplxr0 : forall (R : ringType) (x : R), x +i* 0 = x%:C. Proof. by []. Qed.

Module CplxField.
Section CplxField.

Variable R : rcfType.
Local Notation C := (cplx R).
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Definition addc (x y : C) := let: a +i* b := x in let: c +i* d := y in
  (a + c) +i* (b + d).
Definition oppc (x : C) := let: a +i* b := x in (- a) +i* (- b).

Lemma addcC : commutative addc.
Proof. by move=> [a b] [c d] /=; congr (_ +i* _); rewrite addrC. Qed.
Lemma addcA : associative addc.
Proof. by move=> [a b] [c d] [e f] /=; rewrite !addrA. Qed.

Lemma add0c : left_id C0 addc.
Proof. by move=> [a b] /=; rewrite !add0r. Qed.

Lemma addNc : left_inverse C0 oppc addc.
Proof. by move=> [a b] /=; rewrite !addNr. Qed.

Definition cplx_ZmodMixin := ZmodMixin addcA addcC add0c addNc.
Canonical Structure cplx_ZmodType := ZmodType C cplx_ZmodMixin.

Definition mulc (x y : C) := let: a +i* b := x in let: c +i* d := y in
  ((a * c) - (b * d)) +i* ((a * d) + (b * c)).

Lemma mulcC : commutative mulc.
Proof.
move=> [a b] [c d] /=.
by rewrite [c * b + _]addrC ![_ * c]mulrC ![_ * d]mulrC.
Qed.

Lemma mulcA : associative mulc.
Proof.
move=> [a b] [c d] [e f] /=.
rewrite !mulrDr !mulrDl !mulrN !mulNr !mulrA !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite !addrA addrAC;
  congr (_ + _); rewrite addrC.
Qed.

Definition invc (x : C) := let: a +i* b := x in let n2 := (a ^+ 2 + b ^+ 2) in
  (a / n2) -i* (b / n2).

Lemma mul1c : left_id C1 mulc.
Proof. by move=> [a b] /=; rewrite !mul1r !mul0r subr0 addr0. Qed.

Lemma mulc_addl : left_distributive mulc addc.
Proof.
move=> [a b] [c d] [e f] /=; rewrite !mulrDl !opprD -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite addrCA.
Qed.

Lemma nonzero1c : C1 != C0. Proof. by rewrite eq_cplx /= oner_eq0. Qed.

Definition cplx_comRingMixin :=
  ComRingMixin mulcA mulcC mul1c mulc_addl nonzero1c.
Canonical Structure  cplx_Ring := Eval hnf in RingType C cplx_comRingMixin.
Canonical Structure cplx_comRing := Eval hnf in ComRingType C mulcC.

Lemma mulVc : forall x, x != C0 -> mulc (invc x) x = C1.
Proof.
move=> [a b]; rewrite eq_cplx => /= hab; rewrite !mulNr opprK.
rewrite ![_ / _ * _]mulrAC [b * a]mulrC subrr cplxr0 -mulrDl mulfV //.
by rewrite paddr_eq0 ?sqr_eq0 // -expr2 exprn_even_ge0.
Qed.

Lemma invc0 : invc C0 = C0. Proof. by rewrite /= !mul0r oppr0. Qed.

Definition CplxFieldUnitMixin := FieldUnitMixin mulVc invc0.
Canonical Structure cplx_unitRing :=
  Eval hnf in UnitRingType C CplxFieldUnitMixin.
Canonical Structure cplx_comUnitRing := Eval hnf in [comUnitRingType of C].

Lemma field_axiom : GRing.Field.mixin_of cplx_unitRing.
Proof. by []. Qed.

Definition CplxFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical Structure cplx_iDomain :=
  Eval hnf in IdomainType C (FieldIdomainMixin field_axiom).
Canonical Structure cplx_fieldMixin := FieldType C field_axiom.

Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)].

Lemma cplx_is_rmorphism : rmorphism (@to_cplx R).
Proof.
split; [|split=> //] => a b /=; simpc; first by rewrite subrr.
by rewrite !mulr0 !mul0r addr0 subr0.
Qed.

Canonical Structure cplx_rmorphism := RMorphism cplx_is_rmorphism.
Canonical Structure cplx_additive := Additive cplx_is_rmorphism.

Lemma Re_is_additive : additive (@Re R).
Proof. by case=> a1 b1; case=> a2 b2. Qed.

Canonical Structure Re_additive := Additive Re_is_additive.

Lemma Im_is_additive : additive (@Im R).
Proof. by case=> a1 b1; case=> a2 b2. Qed.

Canonical Structure Im_additive := Additive Im_is_additive.

Definition lec (x y : C) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a <= c).

Definition ltc (x y : C) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a < c).

Definition normc (x : C) : R := 
  let: a +i* b := x in sqrtr (a ^+ 2 + b ^+ 2).

Notation normC x := (normc x)%:C.

Lemma ltc0_add : forall x y, ltc 0 x -> ltc 0 y -> ltc 0 (x + y).
Proof.
move=> [a b] [c d] /= /andP [/eqP-> ha] /andP [/eqP-> hc].
by rewrite addr0 eqxx addr_gt0.
Qed.

Lemma normc1 : normc 1 = 1.
Proof. by rewrite /= expr1n exprS mul0r addr0 sqrtr1. Qed.

Lemma normC1_neq0 : normC 1 != 0. Proof. by rewrite normc1 oner_eq0. Qed.

Lemma eq0_normc x : normc x = 0 -> x = 0.
Proof.
case: x => a b /= /eqP; rewrite sqrtr_eq0 ler_eqVlt => /orP [|]; last first.
  by rewrite ltrNge addr_ge0 ?sqr_ge0.
by rewrite paddr_eq0 ?sqr_ge0 // ?sqr_eq0 => /andP [/eqP -> /eqP ->].
Qed.

Lemma eq0_normC x : normC x = 0 -> x = 0. Proof. by case=> /eq0_normc. Qed.

Lemma ge0_lec_total x y : lec 0 x -> lec 0 y -> lec x y || lec y x.
Proof.
move: x y => [a b] [c d] /= /andP[/eqP -> a_ge0] /andP[/eqP -> c_ge0].
by rewrite eqxx ler_total.
Qed.

Lemma sqrM (a b : R) : (a * b) ^+ 2 = a ^+ 2 * b ^+ 2.
Proof. by rewrite mulrMM. Qed.

Lemma normcM x y : normc (x * y) = normc x * normc y.
Proof.
move: x y => [a b] [c d] /=; rewrite -sqrtrM ?addr_ge0 ?sqr_ge0 //.
rewrite sqrrB sqrrD mulrDl !mulrDr -!sqrM.
rewrite mulrAC [b * d]mulrC !mulrA.
suff -> : forall (u v w z t : R), (u - v + w) + (z + v + t) = u + w + (z + t).
  by rewrite addrAC !addrA.
by move=> u v w z t; rewrite [_ - _ + _]addrAC [z + v]addrC !addrA addrNK.
Qed.

Lemma normCM x y : normC (x * y) = normC x * normC y.
Proof. by rewrite -rmorphM normcM. Qed.

Lemma subc_ge0 x y : lec 0 (y - x) = lec x y.
Proof. by move: x y => [a b] [c d] /=; simpc; rewrite subr_ge0 subr_eq0. Qed.

Lemma lec_def x y : lec x y = (normC (y - x) == y - x).
Proof.
rewrite -subc_ge0; move: (_ - _) => [a b]; rewrite eq_cplx /= eq_sym.
have [<- /=|_] := altP eqP; last by rewrite andbF.
by rewrite [0 ^+ _]mul0r addr0 andbT sqrtr_sqr ger0_def.
Qed.

Lemma ltc_def x y : ltc x y = (y != x) && lec x y.
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite eq_cplx /=.
by have [] := altP eqP; rewrite ?(andbF, andbT) //= ltr_def.
Qed.

Lemma lec_normD x y : lec (normC (x + y)) (normC x + normC y).
Proof.
move: x y => [a b] [c d] /=; simpc; rewrite addr0 eqxx /=.
rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?(ler_paddr, sqrtr_ge0) //.
rewrite [X in _ <= X] sqrrD ?sqr_sqrtr;
   do ?by rewrite ?(ler_paddr, sqrtr_ge0, sqr_ge0, mulr_ge0) //.
rewrite -addrA addrCA (monoRL (addrNK _) (ler_add2r _)) !sqrrD.
set u := _ *+ 2; set v := _ *+ 2.
rewrite [a ^+ _ + _ + _]addrAC [b ^+ _ + _ + _]addrAC -addrA.
rewrite [u + _] addrC [X in _ - X]addrAC [b ^+ _ + _]addrC.
rewrite [u]lock [v]lock !addrA; set x := (a ^+ 2 + _ + _ + _).
rewrite -addrA addrC addKr -!lock addrC.
have [huv|] := ger0P (u + v); last first.
  by move=> /ltrW /ler_trans -> //; rewrite pmulrn_lge0 // mulr_ge0 ?sqrtr_ge0.
rewrite -(@ler_pexpn2r _ 2) -?topredE //=; last first.
  by rewrite ?(pmulrn_lge0, mulr_ge0, sqrtr_ge0) //.
rewrite -mulr_natl !sqrM !sqr_sqrtr ?(ler_paddr, sqr_ge0) //.
rewrite -mulrnDl -mulr_natl !sqrM ler_pmul2l ?exprn_gt0 ?ltr0n //.
rewrite sqrrD mulrDl !mulrDr -!sqrM addrAC.
rewrite [_ + (b * d) ^+ 2]addrC [X in _ <= X]addrAC -!addrA !ler_add2l.
rewrite mulrAC mulrA -mulrA mulrMM mulrC.
by rewrite -subr_ge0 addrAC -sqrrB sqr_ge0.
Qed.

Definition cplx_POrderedMixin := PartialOrderMixin lec_normD ltc0_add eq0_normC
  normC1_neq0 ge0_lec_total normCM lec_def ltc_def.
Canonical Structure cplx_poIdomainType := POIdomainType C cplx_POrderedMixin.

End CplxField.
End CplxField.

Canonical Structure cplx_ZmodType (R : rcfType) :=
  ZmodType (cplx R) (CplxField.cplx_ZmodMixin R).
Canonical Structure cplx_Ring (R : rcfType) :=
  Eval hnf in RingType (cplx R) (CplxField.cplx_comRingMixin R).
Canonical Structure cplx_comRing (R : rcfType) :=
  Eval hnf in ComRingType (cplx R) (@CplxField.mulcC R).
Canonical Structure cplx_unitRing (R : rcfType) :=
  Eval hnf in UnitRingType (cplx R) (CplxField.CplxFieldUnitMixin R).
Canonical Structure cplx_comUnitRing (R : rcfType) :=
  Eval hnf in [comUnitRingType of (cplx R)].
Canonical Structure cplx_iDomain (R : rcfType) :=
  Eval hnf in IdomainType (cplx R) (FieldIdomainMixin (@CplxField.field_axiom R)).
Canonical Structure cplx_fieldType (R : rcfType) :=
  FieldType (cplx R) (@CplxField.field_axiom R).
Canonical Structure cplx_poIdomainType (R : rcfType) :=
  POIdomainType (cplx R) (CplxField.cplx_POrderedMixin R).
Canonical Structure cplx_poFieldType (R : rcfType) :=
  POFieldType (cplx R) (CplxField.cplx_POrderedMixin R).

Definition conjc (R : ringType) (x : cplx R) := let: a +i* b := x in a -i* b.
Notation "x ^*" := (conjc x) (at level 2, format "x ^*").

Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) <= (_ +i* _)]/((_ == _) && (_ <= _))
  | rewrite -[(_ +i* _) < (_ +i* _)]/((_ == _) && (_ < _))
  | rewrite -[`|_ +i* _|]/(sqrtr (_ + _))%:C
  | rewrite (mulrNN, mulrN, mulNr, opprB, opprD, mulr0, mul0r,
    subr0, sub0r, addr0, add0r, mulr1, mul1r, subrr, opprK, oppr0,
    eqxx) ].


Section CplxTheory.

Variable R : rcfType.
Notation C := (cplx R).

Lemma ReiNIm : forall x : C, Re (x * 'i) = - Im x.
Proof. by case=> a b; simpc. Qed.

Lemma ImiRe : forall x : C, Im (x * 'i) = Re x.
Proof. by case=> a b; simpc. Qed.

Lemma cplxI : injective (@to_cplx R). Proof. by move=> x y []. Qed.

Lemma ler0c (x : R) : (0 <= x%:C) = (0 <= x). Proof. by simpc. Qed.

Lemma lecE : forall x y : C, (x <= y) = (Im y == Im x) && (Re x <= Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma ltcE : forall x y : C, (x < y) = (Im y == Im x) && (Re x < Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma lecR : forall x y : R, (x%:C <= y%:C) = (x <= y).
Proof. by move=> x y; simpc. Qed.

Lemma ltcR : forall x y : R, (x%:C < y%:C) = (x < y).
Proof. by move=> x y; simpc. Qed.

Lemma conjc_is_rmorphism : rmorphism (@conjc R).
Proof.
split=> [[a b] [c d]|] /=; first by simpc; rewrite [d - _]addrC.
by split=> [[a b] [c d]|] /=; simpc.
Qed.

Canonical Structure conjc_rmorphism := RMorphism conjc_is_rmorphism.
Canonical Structure conjc_additive := Additive conjc_is_rmorphism.

Lemma conjcK : involutive (@conjc R).
Proof. by move=> [a b] /=; rewrite opprK. Qed.

Lemma mulcJ_ge0 (x : C) : 0 <= x * x ^*.
Proof.
by move: x=> [a b]; simpc; rewrite mulrC addNr eqxx addr_ge0 ?sqr_ge0.
Qed.

Lemma conjc_real (x : R) : x%:C^* = x%:C.
Proof. by rewrite /= oppr0. Qed.

Lemma ReJ_add (x : C) : (Re x)%:C =  (x + x^*) / 2%:R.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 // -natrM pnatr_eq0.
Qed.

Lemma ImJ_sub (x : C) : (Im x)%:C =  (x^* - x) / 2%:R * 'i.
Proof.
case: x => a b; simpc; rewrite [0 ^+ 2]mul0r addr0 /=.
rewrite -!mulr2n -mulr_natr -mulrA [_ * (_ / _)]mulrA.
by rewrite divff ?mulr1 ?opprK // -natrM pnatr_eq0.
Qed.

Lemma ger0_Im (x : C) : 0 <= x -> Im x = 0.
Proof. by move: x=> [a b] /=; simpc => /andP [/eqP]. Qed.

(* Todo : extend theory of : *)
(*   - exprn_even_gt *)
(*   - signed exponents *)


Lemma conj_ge0 : forall x : C, (0 <= x ^*) = (0 <= x).
Proof. by move=> [a b] /=; simpc; rewrite oppr_eq0. Qed.

Lemma conjc_nat : forall n, (n%:R : C)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjc0 : (0 : C) ^* = 0.
Proof. exact: (conjc_nat 0). Qed.

Lemma conjc1 : (1 : C) ^* = 1.
Proof. exact: (conjc_nat 1). Qed.

Lemma conjc_eq0 : forall x : C, (x ^* == 0) = (x == 0).
Proof. by move=> [a b]; rewrite !eq_cplx /= eqr_oppC oppr0. Qed.

Lemma conjc_inv: forall x : C, (x^-1)^* = (x^* )^-1.
Proof. exact: fmorphV. Qed.

Lemma cplx_root_conj : forall (p : {poly C}) (x : C),
  root (map_poly (@conjc _) p) x = root p (x^*).
Proof.
move=> p x; rewrite /root.
by rewrite -{1}[x]conjcK horner_map /= conjc_eq0.
Qed.

End CplxTheory.

(* Section RcfDef. *)

(* Variable R : oFieldType. *)
(* Notation C := (cplx R). *)

(* Definition rcf_even := forall (p : {poly R}), *)
(*   ~~odd (size p) -> {x | p.[x] = 0}. *)
(* Definition rcf_square := forall x : R, *)
(*   {y | (0 <= y) && if 0 <= x then (y ^ 2 == x) else y == 0}. *)

(* Lemma rcf_even_sqr_from_ivt : rcf_axiom R -> rcf_even * rcf_square. *)
(* Proof. *)
(* move=> ivt. *)
(* split. *)
(*   move=> p sp. *)
(*   move: (ivt p). *)
(*   admit. *)
(* move=> x. *)
(* case: (boolP (0 <= x)) (@ivt ('X^2 - x%:P) 0 (1 + x))=> px; last first. *)
(*   by move=> _; exists 0; rewrite lerr eqxx. *)
(* case. *)
(* * by rewrite ler_paddr ?ler01. *)
(* * rewrite !horner_lin oppr_le0 px /=. *)
(*   rewrite subr_ge0 (@ler_trans _ (1 + x)) //. *)
(*     by rewrite ler_paddl ?ler01 ?lerr. *)
(*   by rewrite ler_pemulr // addrC -subr_ge0 ?addrK // subr0 ler_paddl ?ler01. *)
(* * move=> y hy; rewrite /root !horner_lin; move/eqP. *)
(*   move/(canRL (@addrNK _ _)); rewrite add0r=> <-. *)
(* by exists y; case/andP: hy=> -> _; rewrite eqxx. *)
(* Qed. *)

(* Lemma ivt_from_closed : GRing.ClosedField.axiom [ringType of C] -> rcf_axiom R. *)
(* Proof. *)
(* rewrite /GRing.ClosedField.axiom /= => hclosed. *)
(* move=> p a b hab. *)
(* Admitted. *)

(* Lemma closed_form_rcf_even_sqr : rcf_even -> rcf_square *)
(*   -> GRing.ClosedField.axiom [ringType of C]. *)
(* Proof. *)
(* Admitted. *)

(* Lemma closed_form_ivt : rcf_axiom R -> GRing.ClosedField.axiom [ringType of C]. *)
(* Proof. *)
(* move/rcf_even_sqr_from_ivt; case. *)
(* exact: closed_form_rcf_even_sqr. *)
(* Qed. *)

(* End RcfDef. *)

Require Import closed_field fintype.

Import ORing.Theory.

Section CplxClosed.

Variable R : rcfType.
Local Notation C := (cplx R).


(* Definition C_closedFieldAxiom := closed_form_ivt (@poly_ivt R). *)
(* Definition C_decFieldMixin := closed_fields_QEMixin C_closedFieldAxiom. *)
(* Canonical Structure C_decField := DecFieldType C C_decFieldMixin. *)
(* Canonical Structure C_closedField := ClosedFieldType C C_closedFieldAxiom. *)



Definition sqrtc (x : C) : C :=
  let: a +i* b := x in
  let sgr1 b := if b == 0 then 1 else sgr b in
  let r := sqrtr (a^+2 + b^+2) in
  (sqrtr ((r + a)/2%:R)) +i* (sgr1 b * sqrtr ((r - a)/2%:R)).

Lemma sqr_sqrtc : forall x, (sqrtc x) ^+ 2 = x.
Proof.
have sqr: forall x : R, x ^+ 2 = x * x.
  by move=> x; rewrite exprS expr1.
case=> a b; rewrite exprS expr1; simpc.
have F0: 2%:R != 0 :> R by rewrite pnatr_eq0.
have F1: 0 <= 2%:R^-1 :> R by rewrite invr_ge0 ler0n.
have F2: `|a| <= sqrtr (a^+2 + b^+2).
  rewrite -sqrtr_sqr ler_wsqrtr //.
  by rewrite addrC -subr_ge0 addrK exprn_even_ge0.
have F3: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) - a) / 2%:R.
  rewrite mulr_ge0 // subr_ge0 (ler_trans _ F2) //.
  by rewrite -(maxrN a) ler_maxr lerr.
have F4: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) + a) / 2%:R.
  rewrite mulr_ge0 // -{2}[a]opprK subr_ge0 (ler_trans _ F2) //.
  by rewrite -(maxrN a) ler_maxr lerr orbT.
congr (_ +i* _);  set u := if _ then _ else _.
  rewrite mulrCA !mulrA.
  have->: (u * u) = 1.
    rewrite /u; case: (altP (_ =P _)); rewrite ?mul1r //.
    by rewrite mulr_sg=> ->.
  rewrite mul1r -!sqr !sqr_sqrtr //.
  rewrite [_+a]addrC -mulrBl opprD addrA addrK.
  by rewrite opprK -mulr2n -mulr_natl [_*a]mulrC mulfK.
rewrite mulrCA -mulrA -mulrDr [sqrtr _ * _]mulrC.
rewrite -mulr2n -sqrtrM // mulrAC !mulrA ?[_ * (_ - _)]mulrC -subr_sqr.
rewrite sqr_sqrtr; last first.
  by rewrite ler_paddr // exprn_even_ge0.
rewrite [_^+2 + _]addrC addrK -mulrA -expr2 sqrtrM ?exprn_even_ge0 //.
rewrite !sqrtr_sqr -mulr_natr.
rewrite [`|_^-1|]ger0_norm // -mulrA [_ * _%:R]mulrC divff //.
rewrite mulr1 /u; case: (_ =P _)=>[->|].
  by rewrite  normr0 mulr0.
by rewrite mulr_sg_norm.
Qed.

Lemma sqrtc_sqrtr :
  forall (x : C), 0 <= x -> sqrtc x = (sqrtr (Re x))%:C.
Proof.
move=> [a b] /andP [/eqP->] /= a_ge0.
rewrite eqxx mul1r [0 ^+ _]exprS mul0r addr0 sqrtr_sqr.
rewrite ger0_norm // subrr mul0r sqrtr0 -mulr2n.
by rewrite -[_*+2]mulr_natr mulfK // pnatr_eq0.
Qed.

Lemma sqrtc0 : sqrtc 0 = 0.
Proof. by rewrite sqrtc_sqrtr ?lerr // sqrtr0. Qed.

Lemma sqrtc1 : sqrtc 1 = 1.
Proof. by rewrite sqrtc_sqrtr ?ler01 // sqrtr1. Qed.

Lemma sqrtN1 : sqrtc (-1) = 'i.
Proof.
rewrite /sqrtc /= oppr0 eqxx [0^+_]exprS mulr0 addr0.
rewrite exprS expr1 mulN1r opprK sqrtr1 subrr mul0r sqrtr0.
by rewrite mul1r -mulr2n divff ?sqrtr1 // pnatr_eq0.
Qed.

Lemma sqrtc_ge0 (x : C) : (0 <= sqrtc x) = (0 <= x).
Proof.
apply/idP/idP=> [psx|px]; last first.
  by rewrite sqrtc_sqrtr // lecR sqrtr_ge0.
by rewrite -[x]sqr_sqrtc exprS expr1 mulr_ge0.
Qed.

Lemma sqrtc_eq0 (x : C) : (sqrtc x == 0) = (x == 0).
Proof.
apply/eqP/eqP=> [eqs|->]; last by rewrite sqrtc0.
by rewrite -[x]sqr_sqrtc eqs exprS mul0r.
Qed.

Lemma normcE x : `|x| = sqrtc (x * x^*).
Proof.
case: x=> a b; simpc; rewrite [b * a]mulrC addNr sqrtc_sqrtr //.
by simpc; rewrite /= addr_ge0 ?sqr_ge0.
Qed.

Lemma sqr_normc (x : C) : (`|x| ^+ 2) = x * x^*.
Proof. by rewrite normcE sqr_sqrtc. Qed.

Lemma normc_ge_Re (x : C) : `|Re x|%:C <= `|x|.
Proof.
by case: x => a b; simpc; rewrite -sqrtr_sqr ler_wsqrtr // ler_addl sqr_ge0.
Qed.

Lemma normcJ (x : C) :  `|x^*| = `|x|.
Proof. by case: x => a b; simpc; rewrite /= sqrrN. Qed.

Lemma invc_norm (x : C) : x^-1 = `|x|^-2 * x^*.
Proof.
case: (altP (x =P 0)) => [->|dx]; first by rewrite rmorph0 mulr0 invr0.
apply: (mulIf dx); rewrite mulrC divff // -mulrA [_^* * _]mulrC -(sqr_normc x).
by rewrite mulVf // expf_neq0 ?normr_eq0.
Qed.

End CplxClosed.

