Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg div orderedalg zint.

Import GRing.Theory.
Import ORing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Notation sgr := ORing.sg.

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

Definition numq x := nosimpl ((valq x).1).
Definition denq x := nosimpl ((valq x).2).

Lemma denq_gt0  x : 0 < denq x.
Proof. by rewrite /denq; case: x=> [[a b] /= /andP []]. Qed.
Hint Resolve denq_gt0.

Definition denq_ge0 x := ltrW (denq_gt0 x).

Lemma denq_lt0  x : (denq x < 0) = false. Proof. by rewrite ltr_gtF. Qed.

Lemma denq_neq0 x : denq x != 0.
Proof. by rewrite /denq gtr_eqF ?denq_gt0. Qed.
Hint Resolve denq_neq0.

Lemma denq_eq0 x : (denq x == 0) = false.
Proof. exact: negPf (denq_neq0 _). Qed.

Lemma coprime_num_den x : coprime (absz (numq x)) (absz (denq x)).
Proof. by rewrite /numq /denq; case: x=> [[a b] /= /andP []]. Qed.

Lemma QnumK x P : @Qnum (numq x, denq x) P = x.
Proof. by move:x P => [[a b] P'] P; apply: val_inj. Qed.

Lemma fracq_subproof : forall x : zint * zint,
  let n := if x.2 == 0 then 0 else
    (-1) ^ ((x.2 < 0) (+) (x.1 < 0)) 
         * ((absz x.1) %/ gcdn (absz x.1) (absz x.2))%:Z in
    let d := if x.2 == 0 then 1 else
      (absz x.2 %/ gcdn (absz (x.1)) (absz x.2))%:Z in
        (0 < d) && (coprime (absz n) (absz d)).
Proof.
move=> [m n] /=; case: (altP (n =P 0))=> [//|n0].
rewrite ltz_nat divn_gt0 ?gcdn_gt0 ?absz_gt0 ?n0 ?orbT //.
rewrite dvdn_leq ?absz_gt0 ?dvdn_gcdr //= !abszM absz_sign mul1n.
have [->|m0] := altP (m =P 0); first by rewrite div0n gcd0n divnn absz_gt0 n0.
move: n0 m0; rewrite -!absz_gt0 absz_nat.
move: (absz _) (absz _)=> {m n} [|m] [|n] // _ _.
rewrite /coprime -(@eqn_pmul2l (gcdn m.+1 n.+1)) ?gcdn_gt0 //.
rewrite -gcdn_mul2l; do 2!rewrite divn_mulCA ?(dvdn_gcdl, dvdn_gcdr) ?divnn //.
by rewrite ?gcdn_gt0 ?muln1.
Qed.

Definition fracq (x : zint * zint) := nosimpl (@Qnum (_, _) (fracq_subproof x)).

Lemma qnumzE n : qnumz n = fracq (n, 1).
Proof. by apply: val_inj; rewrite /= gcdn1 !divn1 abszE mulr_sign_norm. Qed.

Lemma valqK x : fracq (valq x) = x.
Proof.
move:x => [[n d] /= Pnd]; apply: val_inj=> /=.
move: Pnd; rewrite /coprime /fracq /=; case/andP=> hd; move/eqP=> hnd.
by rewrite ltr_gtF ?gtr_eqF //= hnd !divn1 mulz_sign_abs abszE gtr0_norm.
Qed.

Definition scalq := locked (fun x =>
           sgr x.2 * (gcdn (absz x.1) (absz x.2))%:Z).

Lemma scalq_eq0 x : (scalq x == 0) = (x.2 == 0).
Proof.
case: x => n d; rewrite /scalq -lock /= mulf_eq0 sgr_eq0 /= eqz_nat.
rewrite -[gcdn _ _ == 0%N]negbK -lt0n gcdn_gt0 ?absz_gt0 [X in ~~ X]orbC.
by case: sgrP.
Qed.

Lemma sgr_scalq x : sgr (scalq x) = sgr x.2.
Proof.
unlock scalq; rewrite sgrM sgr_id -[(gcdn _ _)%:Z]zintz sgr_nat.
by rewrite -lt0n gcdn_gt0 ?absz_gt0 orbC; case: sgrP; rewrite // mul0r.
Qed.

Lemma signr_scalq x : (scalq x < 0) = (x.2 < 0).
Proof. by rewrite -!sgr_cp0 sgr_scalq. Qed.

Lemma scalqE x : x.2 != 0 -> scalq x =
          (-1) ^+ (x.2 < 0)%R * (gcdn (absz x.1) (absz x.2))%:Z.
Proof. by unlock scalq; case: sgrP. Qed.

Lemma valq_frac x : x.2 != 0 ->
 x = (scalq x * numq (fracq x), scalq x * denq (fracq x)).
Proof.
case: x => [n d] /= d_neq0; rewrite /denq /numq scalqE //= (negPf d_neq0).
rewrite mulrM_sign -mulrA -!PoszM addKb.
do 2!rewrite divn_mulCA ?(dvdn_gcdl, dvdn_gcdr) // divnn.
by rewrite gcdn_gt0 !absz_gt0 d_neq0 orbT !muln1 !mulz_sign_abs.
Qed.

Local Notation zeroq := (fracq (0, 1)).
Local Notation oneq := (fracq (1, 1)).

Lemma frac0q x : fracq (0, x) = zeroq.
Proof.
apply: val_inj; rewrite //= div0n !gcd0n !mulr0 !divnn.
by have [//|x_neq0] := altP eqP; rewrite absz_gt0 x_neq0.
Qed.

Lemma fracq0  x : fracq (x, 0) = zeroq. Proof. exact/eqP. Qed.

CoInductive fracq_spec (x : zint * zint) : zint * zint -> qnum -> Type :=
| FracqSpecN of x.2 = 0 : fracq_spec x (x.1, 0) zeroq
| FracqSpecP k fx of k != 0 :
  fracq_spec x (k * numq fx, k * denq fx) fx.

Lemma fracqP x : fracq_spec x x (fracq x).
Proof.
case: x => n d /=; have [d_eq0|d_neq0] := eqVneq d 0.
  by rewrite d_eq0 fracq0; constructor.
by rewrite {2}[(_, _)]valq_frac //; constructor; rewrite scalq_eq0.
Qed.

Lemma qnum_eqE x y : (x == y) = (numq x == numq y) && (denq x == denq y).
Proof.
rewrite -val_eqE [val x]surjective_pairing [val y]surjective_pairing /=.
by rewrite xpair_eqE.
Qed.

Lemma sgr_denq x : sgr (denq x) = 1. Proof. by apply/eqP; rewrite sgr_cp0. Qed.
Lemma normr_denq x : `|denq x| = denq x. Proof. by rewrite gtr0_norm. Qed.
Lemma absz_denq x : absz (denq x) = denq x :> zint.
Proof. by rewrite abszE normr_denq. Qed.

Lemma qnum_eq x y : (x == y) = (numq x * denq y == numq y * denq x).
Proof.
symmetry; rewrite qnum_eqE andbC.
have [->|] /= := altP (denq _ =P _); first by rewrite (inj_eq (mulIf _)).
apply: contraNF => /eqP hxy; rewrite -absz_denq -[X in _ == X]absz_denq.
rewrite eqz_nat /= eqn_dvd.
rewrite -(@gauss _ (absz (numq x))) 1?coprime_sym ?coprime_num_den // andbC.
rewrite -(@gauss _ (absz (numq y))) 1?coprime_sym ?coprime_num_den //.
by rewrite -!abszM hxy -{1}hxy !abszM !dvdn_mull ?dvdnn.
Qed.

Lemma fracq_eq x y : x.2 != 0 -> y.2 != 0 ->
  (fracq x == fracq y) = (x.1 * y.2 == y.1 * x.2).
Proof.
case: fracqP=> //= u fx u_neq0 _; case: fracqP=> //= v fy v_neq0 _; symmetry.
rewrite [X in (_ == X)]mulrC mulrMM [X in (_ == X)]mulrMM.
by rewrite [denq _ * _]mulrC (inj_eq (mulfI _)) ?mulf_neq0 // qnum_eq.
Qed.

Lemma fracq_eq0 x : (fracq x == fracq (0, 1)) = (x.1 == 0) || (x.2 == 0).
Proof.
move: x=> [n d] /=; have [->|d0] := altP (d =P 0).
  by rewrite fracq0 eqxx orbT.
by rewrite orbF fracq_eq ?d0 //= mulr1 mul0r.
Qed.

Lemma fracqMM x n d : x != 0 -> fracq (x * n, x * d) = fracq (n, d).
Proof.
move=> x_neq0; apply/eqP.
have [->|d_neq0] := eqVneq d 0; first by rewrite mulr0 !fracq0.
by rewrite fracq_eq ?mulf_neq0 //= mulrCA mulrA.
Qed.

Module QnumField.

Definition add (x y : zint * zint) := (x.1 * y.2 + y.1 * x.2, x.2 * y.2).
Definition addq (x y : qnum) := nosimpl fracq (add (valq x) (valq y)).

Definition opp (x : zint * zint) := (- x.1, x.2).
Definition oppq (x : qnum) := nosimpl fracq (opp (valq x)).

Lemma addC : commutative add.
Proof. by move=> x y; rewrite /add addrC [_.2 * _]mulrC. Qed.

Lemma addA : associative add.
Proof.
by move=> x y z; rewrite /add !mulrA !mulrDl addrA ![_ * x.2]mulrC !mulrA.
Qed.

Lemma addq_frac x y : x.2 != 0 -> y.2 != 0 ->
  (addq (fracq x) (fracq y)) = fracq (add x y).
Proof.
case: fracqP => // u fx u_neq0 _; case: fracqP => // v fy v_neq0 _.
rewrite /add /= ![(_ * numq _) * _]mulrMM [(_ * denq _) * _]mulrMM.
by rewrite [v * _]mulrC -mulrDr fracqMM ?mulf_neq0.
Qed.

Lemma qnumzD : {morph qnumz : x y / x + y >-> addq x y}.
Proof. by move=> x y /=; rewrite !qnumzE addq_frac // /add /= !mulr1. Qed.

Lemma oppq_frac x : oppq (fracq x) = fracq (opp x).
Proof.
rewrite /opp; case: fracqP=> /= [|u fx u_neq0]; first by rewrite fracq0.
by rewrite -mulrN fracqMM.
Qed.

Lemma qnumzN : {morph qnumz : x / - x >-> oppq x}.
Proof. by move=> x /=; rewrite !qnumzE oppq_frac // /add /= !mulr1. Qed.

Lemma addqC : commutative addq.
Proof. by move=> x y; rewrite /addq /=; rewrite addC. Qed.

Lemma addqA : associative addq.
Proof.
move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK.
by rewrite !addq_frac ?mulf_neq0 ?denq_neq0 // addA.
Qed.

Lemma add0q : left_id (fracq (0, 1)) addq.
Proof.
move=> x; rewrite -[x]valqK addq_frac ?denq_neq0 // /add /=.
by rewrite mul0r add0r mulr1 mul1r -surjective_pairing.
Qed.

Lemma addNq : left_inverse (fracq (0, 1)) oppq addq.
Proof.
move=> x; rewrite -[x]valqK !(addq_frac, oppq_frac) ?denq_neq0 /add /opp //=.
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
rewrite /mul; case: fracqP => /= [|u fx u_neq0].
  by rewrite mul0r fracq0 /mulq /mul /= mul0r frac0q.
case: fracqP=> /= [|v fy v_neq0].
  by rewrite mulr0 fracq0 /mulq /mul /= mulr0 frac0q.
by rewrite ![_ * (v * _)]mulrMM fracqMM ?mulf_neq0.
Qed.

Lemma qnumzM : {morph qnumz : x y / x * y >-> mulq x y}.
Proof. by move=> x y /=; rewrite !qnumzE mulq_frac // /mul /= !mulr1. Qed.

Lemma invq_frac x : x.1 != 0 -> x.2 != 0 -> invq (fracq x) = fracq (inv x).
Proof. by rewrite /inv; case: fracqP => // k {x} x k0; rewrite fracqMM. Qed.

Lemma mulqC : commutative mulq. Proof. by move=> x y; rewrite /mulq mulC. Qed.

Lemma mulqA : associative mulq.
Proof.
by move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK !mulq_frac mulA.
Qed.

Lemma mul1q : left_id (fracq (1,1)) mulq.
Proof.
move=> x; rewrite -[x]valqK; rewrite mulq_frac /mul.
by rewrite !mul1r -surjective_pairing.
Qed.

Lemma mulq_addl : left_distributive mulq addq.
Proof.
move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK /=.
rewrite !(mulq_frac, addq_frac) ?mulf_neq0 ?denq_neq0 //=.
apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mulrDl; apply/eqP.
by rewrite !mulrA ![_ * (valq z).1]mulrC !mulrA ![_ * (valq x).2]mulrC !mulrA.
Qed.

Lemma nonzero1q : (fracq (1, 1)) != (fracq (0, 1)). Proof. by []. Qed.

Definition qnum_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.
Canonical  qnum_Ring := Eval hnf in RingType qnum qnum_comRingMixin.
Canonical qnum_comRing := Eval hnf in ComRingType qnum mulqC.


Lemma mulVq x : x != (fracq (0, 1)) -> mulq (invq x) x = (fracq (1, 1)).
Proof.
rewrite -[x]valqK fracq_eq ?denq_neq0 //= mulr1 mul0r=> nx0.
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
rewrite -[x]valqK fracq_eq0; case: fracqP=> /= [|k {x} x k0].
  by rewrite eqxx orbT.
by rewrite !mulf_eq0 (negPf k0) /= denq_eq0 orbF.
Qed.

End QnumField.

Canonical QnumField.qnum_ZmodType.
Canonical QnumField.qnum_Ring.
Canonical QnumField.qnum_comRing.
Canonical QnumField.qnum_unitRing.
Canonical QnumField.qnum_comUnitRing.
Canonical QnumField.qnum_iDomain.
Canonical QnumField.qnum_fieldType.

Hint Resolve denq_neq0 denq_gt0 denq_ge0.

Notation "n %:Q" := ((n : zint)%:~R : qnum)
  (at level 2, left associativity, format "n %:Q")  : ring_scope.

(* Eval compute in (8%:Q / 15%:Q >= 1 / 2%:Q :> qnum). (* OK *) *)

Lemma zintqE n : n%:Q = qnumz n.
Proof.
elim: n=> [|n ihn|n ihn]; first by rewrite mulr0z qnumzE.
  by rewrite zintS mulrzDl QnumField.qnumzD ihn.
by rewrite zintS opprD mulrzDl QnumField.qnumzD ihn.
Qed.

Lemma numq_zint n : numq n%:Q = n. Proof. by rewrite zintqE. Qed.
Lemma denq_zint n : denq n%:Q = 1. Proof. by rewrite zintqE. Qed.

Lemma qnum0 : 0%:Q = 0. Proof. by []. Qed.
Lemma qnum1 : 1%:Q = 1. Proof. by []. Qed.

(* Todo : prove morphism/compatibility lemmas for _%:zR  and/or %:Q *)

Lemma numq_eq0 x : (numq x == 0) = (x == 0).
Proof. exact: QnumField.numq_eq0. Qed.

Lemma numqN x : numq (- x) = - numq x.
Proof.
rewrite /numq; case: x=> [[a b] /= /andP [hb]]; rewrite /coprime=> /eqP hab.
by rewrite ltr_gtF ?gtr_eqF // {2}abszN hab divn1 mulz_sign_abs.
Qed.

Lemma denqN x : denq (- x) = denq x.
Proof.
rewrite /denq; case: x=> [[a b] /= /andP [hb]]; rewrite /coprime=> /eqP hab.
by rewrite gtr_eqF // abszN hab divn1 gtz0_abs.
Qed.

Lemma zintq_eq0 n : (n%:~R == 0 :> qnum) = (n == 0)%N.
Proof. by rewrite zintqE /qnumz qnum_eqE /numq /denq /= mulr0 eqxx andbT. Qed.

(* fracq should never apear, its canonical form is _%:Q / _%:Q *)
Lemma fracqE x : fracq x = x.1%:Q / x.2%:Q.
Proof.
move:x => [m n] /=.
case n0: (n == 0); first by rewrite (eqP n0) fracq0 qnum0 invr0 mulr0.
rewrite -[m%:Q]valqK -[n%:Q]valqK.
rewrite [_^-1]QnumField.invq_frac ?(denq_neq0, numq_eq0, n0, zintq_eq0) //.
rewrite [_ / _]QnumField.mulq_frac /= /QnumField.inv /QnumField.mul /=.
by rewrite -!/(numq _) -!/(denq _) !numq_zint !denq_zint mul1r mulr1.
Qed.

Lemma divq_num_den x : (numq x)%:Q / (denq x)%:Q = x.
Proof. by rewrite -{3}[x]valqK [valq _]surjective_pairing /= fracqE. Qed.

CoInductive divq_spec (n d : zint) : zint -> zint -> qnum -> Type :=
| DivqSpecN of d = 0 : divq_spec n d n 0 0
| DivqSpecP k x of k != 0 : divq_spec n d (k * numq x) (k * denq x) x.

Lemma  divqP n d : divq_spec n d n d (n%:Q / d%:Q).
Proof.
set x := (n, d); rewrite -[n]/x.1 -[d]/x.2 -fracqE.
by case: fracqP => [_|k fx k_neq0] /=; constructor. 
Qed.

Lemma divq_eq (nx dx ny dy : qnum) : dx != 0 -> dy != 0 ->
  (nx / dx == ny / dy) = (nx * dy == ny * dx).
Proof.
move=> dx_neq0 dy_neq0; rewrite -(inj_eq (@mulIf _ (dx * dy) _)) ?mulf_neq0 //.
by rewrite mulrA divfK // mulrCA divfK // [dx * _ ]mulrC.
Qed.

CoInductive qnum_spec (* (x : qnum) *) : qnum -> zint -> zint -> Type :=
  Qnum_spec (n : zint) (d : nat)  & coprime (absz n) d.+1
  : qnum_spec (* x  *) (n%:Q / d.+1%:Q) n d.+1.

Lemma qnumP x : qnum_spec x (numq x) (denq x).
Proof.
rewrite -{1}[x](divq_num_den); case hd: denq => [p|n].
  have: 0 < p%:Z by rewrite -hd denq_gt0.
  case: p hd=> //= n hd; constructor; rewrite -?hd ?divq_num_den //.
  by rewrite -[n.+1]/(absz n.+1) -hd coprime_num_den.
by move: (denq_gt0 x); rewrite hd.
Qed.

Lemma coprimeq_num n d : coprime (absz n) (absz d) ->
  numq (n%:~R / d%:~R) = sgr d * n.
Proof.
move=> cnd /=; have <- := fracqE (n, d%:Z).
rewrite /numq /= (eqP (cnd : _ == 1%N)) divn1.
have [|d_gt0|d_lt0] := sgrP d;
by rewrite (mul0r, mul1r, mulN1r) //= ?[_ ^ _]signrN ?mulNr mulz_sign_abs.
Qed.

Lemma coprimeq_den n d : coprime (absz n) (absz d) ->
  denq (n%:~R / d%:~R) = if d == 0 then 1 else `|d|.
Proof.
move=> cnd; have <- := fracqE (n, d%:Z).
by rewrite /denq /= (eqP (cnd : _ == 1%N)) divn1; case: d {cnd}.
Qed.

Lemma numqE x : (numq x)%:~R = x * (denq x)%:~R.
Proof. by rewrite -{2}[x]divq_num_den divfK // zintq_eq0 denq_eq0. Qed.

Lemma denqP x : {d | denq x = d.+1}.
Proof. by rewrite /denq; case: x => [[_ [[|d]|]] //= _]; exists d. Qed.

Definition normq (x : qnum) : qnum :=  `|numq x|%:~R / (denq x)%:~R.
Definition le_qnum (x y : qnum) := numq x * denq y <= numq y * denq x.
Definition lt_qnum (x y : qnum) := numq x * denq y < numq y * denq x.

Lemma gt_qnum0 x : lt_qnum 0 x = (0 < numq x).
Proof. by rewrite /lt_qnum mul0r mulr1. Qed.

Lemma lt_qnum0 x : lt_qnum x 0 = (numq x < 0).
Proof. by rewrite /lt_qnum mul0r mulr1. Qed.

Lemma ge_qnum0 x : le_qnum 0 x = (0 <= numq x).
Proof. by rewrite /le_qnum mul0r mulr1. Qed.

Lemma le_qnum0 x : le_qnum x 0 = (numq x <= 0).
Proof. by rewrite /le_qnum mul0r mulr1. Qed.

Lemma le_qnum0D x y : le_qnum 0 x -> le_qnum 0 y -> le_qnum 0 (x + y).
Proof.
rewrite !ge_qnum0 => hnx hny.
have hxy: (0 <= numq x * denq y + numq y * denq x).
  by rewrite addr_ge0 ?mulr_ge0.
by rewrite /numq /= -!/(denq _) ?mulf_eq0 ?denq_eq0 !ler_gtF ?mulr_ge0.
Qed.

Lemma le_qnum0M x y : le_qnum 0 x -> le_qnum 0 y -> le_qnum 0 (x * y).
Proof.
rewrite !ge_qnum0 => hnx hny.
have hxy: (0 <= numq x * denq y + numq y * denq x).
  by rewrite addr_ge0 ?mulr_ge0.
by rewrite /numq /= -!/(denq _) ?mulf_eq0 ?denq_eq0 !ler_gtF ?mulr_ge0.
Qed.

Lemma le_qnum0_anti x : le_qnum 0 x -> le_qnum x 0 -> x = 0.
Proof.
by move=> hx hy; apply/eqP; rewrite -numq_eq0 eqr_le -ge_qnum0 -le_qnum0 hx hy.
Qed.

Lemma sgr_numq_div (n d : zint) : sgr (numq (n%:Q / d%:Q)) = sgr n * sgr d.
Proof.
set x := (n, d); rewrite -/x.1 -/x.2 -fracqE.
case: fracqP => [|k fx k_neq0] /=; first by rewrite mulr0.
by rewrite !sgrM mulrMM mulr_sg k_neq0 sgr_denq mulr1 mul1r.
Qed.

Lemma subq_ge0 x y : le_qnum 0 (y - x) = le_qnum x y.
Proof.
symmetry; rewrite ge_qnum0 /le_qnum -subr_ge0.
case: qnumP => nx dx cndx; case: qnumP => ny dy cndy.
rewrite -!mulNr addf_div2 ?zintq_eq0 // !mulNr -!rmorphM -rmorphB /=.
symmetry; rewrite !lerNgt -sgr_cp0 sgr_numq_div mulrC gtr0_sg //.
by rewrite mul1r sgr_cp0.
Qed.

Lemma le_qnum_total : total le_qnum.
Proof. by move=> x y; apply: ler_total. Qed.

Lemma numq_sign_mul (b : bool) x : numq ((-1) ^+ b * x) = (-1) ^+ b * numq x.
Proof. by case: b; rewrite ?(mul1r, mulN1r) // numqN. Qed.

Lemma numq_div_lt0 n d : n != 0 -> d != 0 ->
  (numq (n%:~R / d%:~R) < 0)%R = (n < 0)%R (+) (d < 0)%R.
Proof.
move=> n0 d0; rewrite -sgr_cp0 sgr_numq_div !sgr_def n0 d0.
by rewrite !mulr1n -signr_addb; case: (_ (+) _).
Qed.

Lemma normr_num_div n d : `|numq (n%:~R / d%:~R)| = numq (`|n|%:~R / `|d|%:~R).
Proof.
rewrite (normr_dec n) (normr_dec d) !rmorphM /= invfM mulrMM !sgr_def.
have [->|n_neq0] := altP eqP; first by rewrite mul0r mulr0.
have [->|d_neq0] := altP eqP; first by rewrite invr0 !mulr0.
rewrite !zintr_sign invr_sign -signr_addb numq_sign_mul -numq_div_lt0 //.
by apply: (canRL (signrMK _)); rewrite mulz_sign_abs.
Qed.

Lemma norm_qnumN x : normq (- x) = normq x.
Proof. by rewrite /normq numqN denqN normrN. Qed.

Lemma ge_qnum0_norm x : le_qnum 0 x -> normq x = x.
Proof.
rewrite ge_qnum0; case: qnumP=> [] // n d cnd n_ge0.
by rewrite /normq /= normr_num_div ?ger0_norm // divq_num_den.
Qed.

Lemma lt_qnum_def x y : (lt_qnum x y) = (y != x) && (le_qnum x y).
Proof. by rewrite /lt_qnum ltr_def qnum_eq. Qed.

Definition qnumLeMixin := TotalPartialLeMixin le_qnum0D le_qnum0M le_qnum0_anti
  subq_ge0 (@le_qnum_total 0) norm_qnumN ge_qnum0_norm lt_qnum_def.

Canonical qnum_poIdomainType := POIdomainType qnum qnumLeMixin.
Canonical qnum_poFieldType := POFieldType qnum qnumLeMixin.

Canonical qnum_oIdomainType :=  OIdomainType qnum (@le_qnum_total 0).
Canonical qnum_oFieldType :=  OFieldType qnum (@le_qnum_total 0).


Lemma numq_ge0 x : (0 <= numq x) = (0 <= x).
Proof.
by case: qnumP => n d cnd; rewrite ?pmulr_lge0 ?invr_gt0 (ler0z, ltr0z).
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

Lemma denq_mulr_sign (b : bool) x : denq ((-1) ^+ b * x) = denq x.
Proof. by case: b; rewrite ?(mul1r, mulN1r) // denqN. Qed.

Lemma denq_norm x : denq `|x| = denq x.
Proof. by rewrite normr_dec_sign denq_mulr_sign. Qed.

Definition qnum_archi_bound (x : qnum) := (absz (numq x)).+1.

Lemma qnum_archi_boundP (x : qnum) : 0 <= x -> x < (qnum_archi_bound x)%:R.
Proof.
rewrite -numq_ge0 /qnum_archi_bound; case: qnumP=> [] [] // n d cnd _.
rewrite absz_nat ltr_pdivr_mulr ?ltr0z // natmulP -rmorphM /=.
by rewrite ltr_nat mulnS leq_addr.
Qed.

Definition archiMixin := ArchimedianMixin qnum_archi_boundP.
Canonical archiType := ArchiFieldType qnum archiMixin.
