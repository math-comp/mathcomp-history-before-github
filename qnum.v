Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg div orderedalg zint.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record qnum : Set := Qnum {
  valq : (zint * zint) ;
  _ : (0 < valq.2) && (coprime (absz valq.1) (absz (valq.2)))
}.

Bind Scope ring_scope with qnum.

Definition qnumz (n : zint) := @Qnum (n, 1) (coprimen1 _).
(* Coercion qnumz (n : zint) := @Qnum (n, 1) (coprimen1 _). *)

Canonical qnum_subType := Eval hnf in [subType for valq by qnum_rect].
Definition qnum_eqMixin := [eqMixin of qnum by <:].
Canonical qnum_eqType := EqType qnum qnum_eqMixin.
Definition qnum_countMixin := [countMixin of qnum by <:].
Definition qnum_choiceMixin := CountChoiceMixin qnum_countMixin.
Canonical qnum_choiceType := ChoiceType qnum qnum_choiceMixin.
Canonical qnum_countType := CountType qnum qnum_countMixin.

Notation numq x := ((valq x).1).
Notation denq x := ((valq x).2).

Lemma denq_gt0  x : 0 < denq x. Proof. by case: x=> [[a b] /= /andP []]. Qed.

Lemma denq_neq0 x : denq x != 0. Proof. by rewrite ltrNW ?denq_gt0. Qed.

Lemma denq_eq0 x : (denq x == 0) = false.
Proof. exact: negPf (denq_neq0 _). Qed.

Lemma coprime_num_den x : coprime (absz (numq x)) (absz (denq x)).
Proof. by case: x=> [[a b] /= /andP []]. Qed.

Lemma QnumK x P : @Qnum (numq x, denq x) P = x.
Proof. by move:x P => [[a b] P'] P; apply: val_inj. Qed.

Lemma fracq_subproof : forall x : zint * zint,
  let n := if x.2 == 0 then 0 else
    (sgr x.1 * sgr x.2) * ((absz x.1) %/ gcdn (absz x.1) (absz x.2))%:Z in
    let d := if x.2 == 0 then 1 else
      (absz x.2 %/ gcdn (absz (x.1)) (absz x.2))%:Z in
        (0 < d) && (coprime (absz n) (absz d)).
Proof.
move=> [m n] /=; case: (altP (n =P 0))=> [//|n0].
rewrite ltz_nat divn_gt0 ?gcdn_gt0 ?absz_gt0 ?n0 ?orbT //.
rewrite dvdn_leq ?absz_gt0 ?dvdn_gcdr //= !abszM ?absz_sg n0.
case: (altP (m =P 0))=> [->|m0].
  by rewrite mul0n absz0 gcd0n divnn absz_gt0 n0.
move: n0 m0; rewrite -!absz_gt0.
move: (absz _) (absz _)=> {n m} m n n0 m0.
rewrite !mul1n absz_nat /coprime -(@eqn_pmul2l (gcdn m n)) ?gcdn_gt0 ?m0 //.
rewrite -gcdn_mul2l; do 2!rewrite divn_mulCA ?(dvdn_gcdl, dvdn_gcdr) ?divnn //.
by rewrite ?gcdn_gt0 ?n0 ?m0 ?muln1.
Qed.

Definition fracq (x : zint * zint) := nosimpl (@Qnum (_, _) (fracq_subproof x)).

Lemma qnumzE n : qnumz n = fracq (n, 1).
Proof. by apply: val_inj; rewrite /= mulr1 gcdn1 !divn1 abszE mulr_sg_abs. Qed.

Lemma fracqK x : fracq (valq x) = x.
Proof.
move:x => [[n d] /= Pnd]; apply: val_inj=> /=.
move: Pnd; rewrite /coprime /fracq /=; case/andP=> hd; move/eqP=> hnd.
rewrite ltrNW // hnd !divn1 mulrAC !abszE mulr_sg_abs.
by rewrite gtr0_abs // gtr0_sg // mulr1.
Qed.

Lemma valq_frac x (k := sgr x.2 * gcdn (absz x.1) (absz x.2)) : x.2 != 0 ->
  x = (k * numq (fracq x), k *  denq (fracq x)).
Proof.
move: x @k=> [n d] /=; case d0: (d == 0)=> // _.
rewrite !mulrA [_ * sgr d]mulrC !mulrA mulr_sg d0 mul1r mulrC -!mulrA.
rewrite -!PoszM ![(gcdn _ _ * _)%N]divn_mulCA ?(dvdn_gcdl, dvdn_gcdr) //.
rewrite !PoszM !mulrA !abszE !mulr_sg_abs.
by rewrite divnn gcdn_gt0 !lt0n !absz_eq0 d0 orbT !mulr1.
Qed.

CoInductive fracq_spec (x : zint * zint) : zint * zint -> qnum -> Type :=
| FracqSpecN of x.2 = 0 : fracq_spec x (x.1, 0) (@Qnum (0, 1) isT)
| FracqSpecP k fx of k != 0 : fracq_spec x (k * numq fx, k * denq fx) (fx).

Lemma fracqP x : fracq_spec x x (fracq x).
Proof.
case dx0: (x.2 == 0).
  have hx: x = (x.1, 0) by rewrite [x]surjective_pairing (eqP dx0).
  rewrite {2}hx; rewrite /fracq.
  have ->: @Qnum (_, _) (fracq_subproof x) = @Qnum (0, 1) isT.
    by apply: val_inj=> /=; rewrite dx0.
  by constructor; rewrite (eqP dx0).
rewrite {2}[x]valq_frac ?dx0 //; constructor; rewrite ?dx0 //.
by rewrite mulf_neq0 ?sgr_eq0 ?dx0 // -lt0n gcdn_gt0 !absz_gt0 dx0 orbT.
Qed.

Lemma fracq_eq x y : x.2 != 0 -> y.2 != 0 ->
  (fracq x == fracq y) = (x.1 * y.2 == y.1 * x.2).
Proof.
case: fracqP=> {x} //= k fx k0 _; case: fracqP=> {y} //= k' fy k'0 _.
rewrite !mulrA ![_ * k]mulrC !mulrA ![_ * k']mulrC -!mulrA.
rewrite !(inj_eq (mulfI _)) //; apply/idP/idP; first by move/eqP->.
move=> hxy; rewrite -val_eqE /=.
rewrite [valq fx]surjective_pairing [valq fy]surjective_pairing.
rewrite xpair_eqE; suff hnfx : (denq fx = denq fy).
  by move: hxy; rewrite hnfx eqxx andbT (inj_eq (mulIf _)) ?denq_eq0.
rewrite -[X in X = _]gtz0_abs ?denq_gt0 // -[X in _ = X]gtz0_abs ?denq_gt0 //.
apply/eqP; rewrite eqz_nat /= eqn_dvd.
rewrite -(@gauss _ (absz (numq fx))) 1?coprime_sym ?coprime_num_den // andbC.
rewrite -(@gauss _ (absz (numq fy))) 1?coprime_sym ?coprime_num_den //.
by rewrite -!abszM (eqP hxy) -{1}(eqP hxy) !abszM !dvdn_mull ?dvdnn.
Qed.


Lemma frac0q x : fracq (0, x) = fracq (0, 1).
Proof.
rewrite /fracq; apply: val_inj=> //=.
by case: ifP=> x0; rewrite ?x0 //= sgr0 !mul0r !gcd0n !divnn lt0n absz_eq0 x0.
Qed.

Lemma fracq0  x : fracq (x, 0) = fracq (0, 1). Proof. exact/eqP. Qed.

Lemma fracq_eq0 x : (fracq x == fracq (0, 1)) = (x.1 == 0) || (x.2 == 0).
Proof.
move: x=> [n d] /=; case: (altP (d =P 0))=> [->|d0].
  by rewrite fracq0 eqxx orbT.
by rewrite orbF fracq_eq ?d0 //= mulr1 mul0r.
Qed.

Module QnumField.

Definition add (x y : zint * zint) := nosimpl (x.1 * y.2 + y.1 * x.2, x.2 * y.2).
Definition addq (x y : qnum) := nosimpl fracq (add (valq x) (valq y)).

Definition opp (x : zint * zint) := nosimpl (- x.1, x.2).
Definition oppq (x : qnum) := nosimpl fracq (opp (valq x)).

Lemma addC : commutative add.
Proof. by move=> x y; rewrite /add addrC [_.2 * _.2]mulrC. Qed.
Lemma addA : associative add.
Proof.
by move=> x y z; rewrite /add !mulrA !mulr_addl addrA ![_ * x.2]mulrC !mulrA.
Qed.

Lemma addq_frac x y : x.2 != 0 -> y.2 != 0 -> (addq (fracq x) (fracq y)) = fracq (add x y).
Proof.
rewrite /add; case: fracqP=> // {x} k x k0 _; case: fracqP=> // {y} k' y k'0 _.
apply/eqP; rewrite fracq_eq /= ?mulf_neq0 ?denq_neq0 //; apply/eqP.
by rewrite !mulr_addl !mulrA ![_ * k]mulrC !mulrA ![_ * k']mulrC !mulrA.
Qed.

Lemma qnumzD : {morph qnumz : x y / x + y >-> addq x y}.
Proof. by move=> x y /=; rewrite !qnumzE addq_frac // /add /= !mulr1. Qed.

Lemma oppq_frac x : oppq (fracq x) = fracq (opp x).
Proof.
rewrite /opp; case: fracqP=> /=; first by rewrite fracq0.
move=> k {x} x k0; apply/eqP; rewrite fracq_eq /= ?mulf_neq0 ?denq_neq0 //.
by rewrite !(mulrA, mulNr) [_ * k]mulrC.
Qed.

Lemma qnumzN : {morph qnumz : x / - x >-> oppq x}.
Proof. by move=> x /=; rewrite !qnumzE oppq_frac // /add /= !mulr1. Qed.

Lemma addqC : commutative addq.
Proof. by move=> x y; rewrite /addq /=; rewrite addC. Qed.

Lemma addqA : associative addq.
Proof.
move=> x y z; rewrite -[x]fracqK -[y]fracqK -[z]fracqK.
by rewrite !addq_frac ?mulf_neq0 ?denq_neq0 // addA.
Qed.

Lemma add0q : left_id (fracq (0, 1)) addq.
Proof.
move=> x; rewrite -[x]fracqK addq_frac ?denq_neq0 // /add /=.
by rewrite mul0r add0r mulr1 mul1r -surjective_pairing.
Qed.

Lemma addNq : left_inverse (fracq (0, 1)) oppq addq.
Proof.
move=> x; rewrite -[x]fracqK !(addq_frac, oppq_frac) ?denq_neq0 /add /opp //=.
rewrite mulNr addNr; apply/eqP.
by rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mul0r.
Qed.

Definition qnum_ZmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical qnum_ZmodType := ZmodType qnum qnum_ZmodMixin.

Definition mul (x y : zint * zint) := nosimpl (x.1 * y.1, x.2 * y.2).
Definition mulq (x y : qnum) := nosimpl fracq (mul (valq x) (valq y)).

Lemma mulC : commutative mul.
Proof. by move=> x y; rewrite /mul mulrC [_ * x.2]mulrC. Qed.

Lemma mulA : associative mul. Proof. by move=> x y z; rewrite /mul !mulrA. Qed.

Definition inv (x : zint * zint) := nosimpl (x.2, x.1).
Definition invq (x : qnum) := nosimpl fracq (inv (valq x)).

Lemma mulq_frac x y : (mulq (fracq x) (fracq y)) = fracq (mul x y).
Proof.
rewrite /mul; case: fracqP=> /= [|k {x} x k0].
 by rewrite mul0r fracq0 /mulq /mul /= mul0r frac0q.
case: fracqP=> /= [|k' {y} y k'0].
 by rewrite mulr0 fracq0 /mulq /mul /= mulr0 frac0q.
apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //=.
by rewrite !mulrA ![_ * k]mulrC !mulrA ![_ * k']mulrC !mulrA.
Qed.

Lemma qnumzM : {morph qnumz : x y / x * y >-> mulq x y}.
Proof. by move=> x y /=; rewrite !qnumzE mulq_frac // /mul /= !mulr1. Qed.

Lemma invq_frac x : x.1 != 0 -> x.2 != 0 -> invq (fracq x) = fracq (inv x).
Proof.
rewrite /inv; case: fracqP=> // k {x} x k0; rewrite mulf_eq0=> /norP [_ nx0] _.
by apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= mulrCA mulrA.
Qed.

Lemma mulqC : commutative mulq. Proof. by move=> x y; rewrite /mulq mulC. Qed.

Lemma mulqA : associative mulq.
Proof.
by move=> x y z; rewrite -[x]fracqK -[y]fracqK -[z]fracqK !mulq_frac mulA.
Qed.

Lemma mul1q : left_id (fracq (1,1)) mulq.
Proof.
move=> x; rewrite -[x]fracqK; rewrite mulq_frac /mul.
by rewrite !mul1r -surjective_pairing.
Qed.

Lemma mulq_addl : left_distributive mulq addq.
Proof.
move=> x y z; rewrite -[x]fracqK -[y]fracqK -[z]fracqK /=.
rewrite !(mulq_frac, addq_frac) ?mulf_neq0 ?denq_neq0 //=.
apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mulr_addl; apply/eqP.
by rewrite !mulrA ![_ * numq z]mulrC !mulrA ![_ * denq x]mulrC !mulrA.
Qed.

Lemma nonzero1q : (fracq (1, 1)) != (fracq (0, 1)). Proof. by []. Qed.

Definition qnum_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.
Canonical  qnum_Ring := Eval hnf in RingType qnum qnum_comRingMixin.
Canonical qnum_comRing := Eval hnf in ComRingType qnum mulqC.


Lemma mulVq x : x != (fracq (0, 1)) -> mulq (invq x) x = (fracq (1, 1)).
Proof.
rewrite -[x]fracqK fracq_eq ?denq_neq0 //= mulr1 mul0r=> nx0.
rewrite !(mulq_frac, invq_frac) ?denq_neq0 //.
by apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= mulr1 mul1r mulrC.
Qed.

Lemma invq0 : invq (fracq (0, 1)) = (fracq (0, 1)). Proof. by apply/eqP. Qed.

Definition QnumFieldUnitMixin := FieldUnitMixin mulVq invq0.
Canonical qnum_unitRing :=
  Eval hnf in UnitRingType qnum QnumFieldUnitMixin.
Canonical qnum_comUnitRing := Eval hnf in [comUnitRingType of qnum].

Lemma field_axiom : GRing.Field.mixin_of qnum_unitRing.
Proof. exact. Qed.

Definition QnumFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical qnum_iDomain :=
  Eval hnf in IdomainType qnum (FieldIdomainMixin field_axiom).
Canonical qnum_fieldType := FieldType qnum field_axiom.

Lemma numq_eq0 x : (numq x == 0) = (x == 0).
Proof.
rewrite -[x]fracqK fracq_eq0; case: fracqP=> /= [|k {x} x k0].
  by rewrite eqxx orbT.
by rewrite !mulf_eq0 (negPf k0) /= denq_eq0 orbF.
Qed.

Definition posq (x : qnum) := nosimpl (0 <= numq x).

Lemma posq_frac x : posq (fracq x) = (0 <= x.1 * x.2).
Proof.
rewrite /posq; case: fracqP=> /= [|k {x} x k0]; first by rewrite mulr0.
rewrite mulrAC mulrA -{2}(mulr0 (k * k * denq x)) ler_pmul2l //.
by rewrite mulr_gt0 ?denq_gt0 // -sgr_cp0 sgrM mulr_sg k0.
Qed.

Lemma posq_add x y : posq x -> posq y -> posq (addq x y).
Proof.
rewrite /posq /= => hnx hny; rewrite ltrNW ?mulr_gt0 ?denq_gt0 //.
by rewrite !mulr_ge0 // sgr_ge0 ?addr_ge0 ?mulr_ge0 // ltrW ?denq_gt0.
Qed.

Lemma posq_mul x y : posq x -> posq y -> posq (mulq x y).
Proof.
rewrite /posq /= => hnx hny; rewrite ltrNW ?mulr_gt0 ?denq_gt0 //.
by rewrite !mulr_ge0 // sgr_ge0 mulr_ge0 // ltrW ?denq_gt0.
Qed.

Lemma posq_anti x : posq x -> posq (oppq x) -> x = 0.
Proof.
rewrite -[x]fracqK !(oppq_frac, posq_frac) ?denq_neq0 //=.
rewrite mulNr oppr_cp0=> px pNx.
by apply/eqP; rewrite fracq_eq0 -mulf_eq0 eqr_le px pNx.
Qed.

Lemma posq_total : forall x, (posq x || posq (oppq x)).
Proof.
move=> x; rewrite -[x]fracqK !(oppq_frac, posq_frac) ?denq_neq0 //.
by rewrite mulNr oppr_cp0 ler_total.
Qed.

Definition le_q_total := TotalOrderPosMixin posq_total.

Definition qnum_POrderedMixin := TotalOrder_PartialPosMixin posq_add posq_mul posq_anti  posq_total.
Canonical qnum_poIdomainType := POIdomainType qnum qnum_POrderedMixin.
Canonical qnum_oIdomainType := OIdomainType qnum le_q_total.
Canonical qnum_poFieldType := POFieldType qnum qnum_POrderedMixin.
Canonical qnum_oFieldType := OFieldType qnum  le_q_total.

End QnumField.

Canonical QnumField.qnum_ZmodType.
Canonical QnumField.qnum_Ring.
Canonical QnumField.qnum_comRing.
Canonical QnumField.qnum_unitRing.
Canonical QnumField.qnum_comUnitRing.
Canonical QnumField.qnum_iDomain.
Canonical QnumField.qnum_fieldType.
Canonical QnumField.qnum_poIdomainType.
Canonical QnumField.qnum_oIdomainType.
Canonical QnumField.qnum_poFieldType.
Canonical QnumField.qnum_oFieldType.

Notation "n %:Q" := ((n : zint)%:~R : qnum)
  (at level 2, left associativity, format "n %:Q")  : ring_scope.

(* Eval compute in (8%:Q / 15%:Q >= 1 / 2%:Q :> qnum). (* OK *) *)

Lemma zintqE n : n%:Q = qnumz n.
Proof.
elim: n=> [|n ihn|n ihn]; first by rewrite mulr0z qnumzE.
  by rewrite zintS mulrz_addl QnumField.qnumzD ihn.
by rewrite zintS oppr_add mulrz_addl QnumField.qnumzD ihn.
Qed.

Lemma numq_zint n : numq n%:Q = n. Proof. by rewrite zintqE. Qed.
Lemma denq_zint n : denq n%:Q = 1. Proof. by rewrite zintqE. Qed.

Lemma qnum0 : 0%:Q = 0. Proof. by []. Qed.
Lemma qnum1 : 1%:Q = 1. Proof. by []. Qed.

(* Todo : prove morphism/compatibility lemmas for _%:zR  and/or %:Q *)

Lemma numq_eq0 x : (numq x == 0) = (x == 0).
Proof. exact: QnumField.numq_eq0. Qed.

Lemma numq_ge0 x : (0 <= numq x) = (0 <= x).
Proof. by rewrite -[_ <= x]/(0 <= numq (_ + _)) oppr0 add0r. Qed.

Lemma numqN x : numq (- x) = - numq x.
Proof.
case: x=> [[a b] /= /andP [hb]]; rewrite /coprime=> /eqP hab.
rewrite ltrNW // (gtr0_sg hb) mulr1 sgrN abszN hab divn1.
by rewrite abszE mulNr mulr_sg_abs.
Qed.

Lemma numq_le0 x : (numq x <= 0) = (x <= 0).
Proof. by rewrite -oppr_ge0 -numqN numq_ge0 oppr_ge0. Qed.

Lemma numq_gt0 x : (0 < numq x) = (0 < x).
Proof. by rewrite !ltrNge numq_le0. Qed.

Lemma numq_lt0 x : (numq x < 0) = (x < 0).
Proof. by rewrite !ltrNge numq_ge0. Qed.

Lemma sgr_numq x : sgz (numq x) = sgz x.
Proof.
apply/eqP; case: (sgzP x); rewrite sgz_cp0 ?(numq_gt0, numq_lt0) //.
by move->.
Qed.

Lemma fracqE x : fracq x = x.1%:Q / x.2%:Q.
Proof.
move:x => [m n] /=.
case n0: (n == 0); first by rewrite (eqP n0) fracq0 qnum0 invr0 mulr0.
rewrite -[m%:Q]fracqK -[n%:Q]fracqK.
rewrite [_^-1]QnumField.invq_frac ?(denq_neq0, numq_eq0, eqr_zint, zintr_eq0, n0) //.
rewrite [_ / _]QnumField.mulq_frac /= /QnumField.inv /QnumField.mul /=.
by rewrite !numq_zint !denq_zint mul1r mulr1.
Qed.

Lemma divq_num_den x : (numq x)%:Q / (denq x)%:Q = x.
Proof. by rewrite -{3}[x]fracqK [valq _]surjective_pairing /= fracqE. Qed.

CoInductive qnum_spec (x : qnum) : qnum -> zint -> zint -> Type :=
  Qnum_spec (n : zint) (d : nat) & x = n%:Q / d%:Q & coprime (absz n) d
  : qnum_spec x (n%:Q / d%:Q) n d.

Lemma qnumP : forall x : qnum, qnum_spec x x (numq x) (denq x).
Proof.
move=> x; rewrite -{2}[x]fracqK /= [valq _]surjective_pairing fracqE /=.
case hd: (denq x)=> [p|n].
  constructor; rewrite -?hd ?divq_num_den //.
  by rewrite -[p]/(absz p) -hd coprime_num_den.
by move: (denq_gt0 x); rewrite hd.
Qed.
