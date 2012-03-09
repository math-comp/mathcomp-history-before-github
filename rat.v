Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg div orderedalg int.

Import GRing.Theory.
Import ORing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Notation sgr := ORing.sg.

Record rat : Set := Rat {
  valq : (int * int) ;
  _ : (0 < valq.2) && coprime `|valq.1| `|valq.2|
}.

Bind Scope ring_scope with rat.

Definition ratz (n : int) := @Rat (n, 1) (coprimen1 _).
(* Coercion ratz (n : int) := @Rat (n, 1) (coprimen1 _). *)

Canonical rat_subType := Eval hnf in [subType for valq by rat_rect].
Definition rat_eqMixin := [eqMixin of rat by <:].
Canonical rat_eqType := EqType rat rat_eqMixin.
Definition rat_countMixin := [countMixin of rat by <:].
Definition rat_choiceMixin := CountChoiceMixin rat_countMixin.
Canonical rat_choiceType := ChoiceType rat rat_choiceMixin.
Canonical rat_countType := CountType rat rat_countMixin.

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

Lemma coprime_num_den x : coprime `|numq x| `|denq x|.
Proof. by rewrite /numq /denq; case: x=> [[a b] /= /andP []]. Qed.

Fact RatK x P : @Rat (numq x, denq x) P = x.
Proof. by move:x P => [[a b] P'] P; apply: val_inj. Qed.

Fact fracq_subproof : forall x : int * int,
  let n := if x.2 == 0 then 0 else
    (-1) ^ ((x.2 < 0) (+) (x.1 < 0)) 
         * (`|x.1| %/ gcdn `|x.1| `|x.2|)%:Z in
    let d := if x.2 == 0 then 1 else
      (`|x.2| %/ gcdn `|x.1| `|x.2|)%:Z in
        (0 < d) && (coprime `|n| `|d|).
Proof.
move=> [m n] /=; case: (altP (n =P 0))=> [//|n0].
rewrite ltz_nat divn_gt0 ?gcdn_gt0 ?absz_gt0 ?n0 ?orbT //.
rewrite dvdn_leq ?absz_gt0 ?dvdn_gcdr //= !abszM absz_sign mul1n.
have [->|m0] := altP (m =P 0); first by rewrite div0n gcd0n divnn absz_gt0 n0.
move: n0 m0; rewrite -!absz_gt0 absz_nat.
move: `|_|%N `|_|%N => {m n} [|m] [|n] // _ _.
rewrite /coprime -(@eqn_pmul2l (gcdn m.+1 n.+1)) ?gcdn_gt0 //.
rewrite muln_gcdr; do 2!rewrite muln_divCA ?(dvdn_gcdl, dvdn_gcdr) ?divnn //.
by rewrite ?gcdn_gt0 ?muln1.
Qed.

Definition fracq (x : int * int) := nosimpl (@Rat (_, _) (fracq_subproof x)).

Fact ratz_frac n : ratz n = fracq (n, 1).
Proof. by apply: val_inj; rewrite /= gcdn1 !divn1 abszE mulr_sign_norm. Qed.

Fact valqK x : fracq (valq x) = x.
Proof.
move:x => [[n d] /= Pnd]; apply: val_inj=> /=.
move: Pnd; rewrite /coprime /fracq /=; case/andP=> hd; move/eqP=> hnd.
by rewrite ltr_gtF ?gtr_eqF //= hnd !divn1 mulz_sign_abs abszE gtr0_norm.
Qed.

Definition scalq := locked (fun x => sgr x.2 * (gcdn `|x.1| `|x.2|)%:Z).

Fact scalq_eq0 x : (scalq x == 0) = (x.2 == 0).
Proof.
case: x => n d; rewrite /scalq -lock /= mulf_eq0 sgr_eq0 /= eqz_nat.
rewrite -[gcdn _ _ == 0%N]negbK -lt0n gcdn_gt0 ?absz_gt0 [X in ~~ X]orbC.
by case: sgrP.
Qed.

Lemma sgr_scalq x : sgr (scalq x) = sgr x.2.
Proof.
unlock scalq; rewrite sgrM sgr_id -[(gcdn _ _)%:Z]intz sgr_nat.
by rewrite -lt0n gcdn_gt0 ?absz_gt0 orbC; case: sgrP; rewrite // mul0r.
Qed.

Lemma signr_scalq x : (scalq x < 0) = (x.2 < 0).
Proof. by rewrite -!sgr_cp0 sgr_scalq. Qed.

Lemma scalqE x : x.2 != 0 -> scalq x =
          (-1) ^+ (x.2 < 0)%R * (gcdn `|x.1| `|x.2|)%:Z.
Proof. by unlock scalq; case: sgrP. Qed.

Fact valq_frac x : x.2 != 0 ->
 x = (scalq x * numq (fracq x), scalq x * denq (fracq x)).
Proof.
case: x => [n d] /= d_neq0; rewrite /denq /numq scalqE //= (negPf d_neq0).
rewrite mulr_signM -mulrA -!PoszM addKb.
do 2!rewrite muln_divCA ?(dvdn_gcdl, dvdn_gcdr) // divnn.
by rewrite gcdn_gt0 !absz_gt0 d_neq0 orbT !muln1 !mulz_sign_abs.
Qed.

Local Notation zeroq := (fracq (0, 1)).
Local Notation oneq := (fracq (1, 1)).

Fact frac0q x : fracq (0, x) = zeroq.
Proof.
apply: val_inj; rewrite //= div0n !gcd0n !mulr0 !divnn.
by have [//|x_neq0] := altP eqP; rewrite absz_gt0 x_neq0.
Qed.

Fact fracq0  x : fracq (x, 0) = zeroq. Proof. exact/eqP. Qed.

CoInductive fracq_spec (x : int * int) : int * int -> rat -> Type :=
| FracqSpecN of x.2 = 0 : fracq_spec x (x.1, 0) zeroq
| FracqSpecP k fx of k != 0 :
  fracq_spec x (k * numq fx, k * denq fx) fx.

Fact fracqP x : fracq_spec x x (fracq x).
Proof.
case: x => n d /=; have [d_eq0|d_neq0] := eqVneq d 0.
  by rewrite d_eq0 fracq0; constructor.
by rewrite {2}[(_, _)]valq_frac //; constructor; rewrite scalq_eq0.
Qed.

Lemma rat_eqE x y : (x == y) = (numq x == numq y) && (denq x == denq y).
Proof.
rewrite -val_eqE [val x]surjective_pairing [val y]surjective_pairing /=.
by rewrite xpair_eqE.
Qed.

Lemma sgr_denq x : sgr (denq x) = 1. Proof. by apply/eqP; rewrite sgr_cp0. Qed.

Lemma normr_denq x : `|denq x| = denq x. Proof. by rewrite gtr0_norm. Qed.

Lemma absz_denq x : `|denq x|%N = denq x :> int.
Proof. by rewrite abszE normr_denq. Qed.

Lemma rat_eq x y : (x == y) = (numq x * denq y == numq y * denq x).
Proof.
symmetry; rewrite rat_eqE andbC.
have [->|] /= := altP (denq _ =P _); first by rewrite (inj_eq (mulIf _)).
apply: contraNF => /eqP hxy; rewrite -absz_denq -[X in _ == X]absz_denq.
rewrite eqz_nat /= eqn_dvd.
rewrite -(@Gauss_dvdr _ `|numq x|) 1?coprime_sym ?coprime_num_den //.
rewrite andbC.
rewrite -(@Gauss_dvdr _ `|numq y|) 1?coprime_sym ?coprime_num_den //.
by rewrite -!abszM hxy -{1}hxy !abszM !dvdn_mull ?dvdnn.
Qed.

Fact fracq_eq x y : x.2 != 0 -> y.2 != 0 ->
  (fracq x == fracq y) = (x.1 * y.2 == y.1 * x.2).
Proof.
case: fracqP=> //= u fx u_neq0 _; case: fracqP=> //= v fy v_neq0 _; symmetry.
rewrite [X in (_ == X)]mulrC mulrACA [X in (_ == X)]mulrACA.
by rewrite [denq _ * _]mulrC (inj_eq (mulfI _)) ?mulf_neq0 // rat_eq.
Qed.

Fact fracq_eq0 x : (fracq x == fracq (0, 1)) = (x.1 == 0) || (x.2 == 0).
Proof.
move: x=> [n d] /=; have [->|d0] := altP (d =P 0).
  by rewrite fracq0 eqxx orbT.
by rewrite orbF fracq_eq ?d0 //= mulr1 mul0r.
Qed.

Fact fracqMM x n d : x != 0 -> fracq (x * n, x * d) = fracq (n, d).
Proof.
move=> x_neq0; apply/eqP.
have [->|d_neq0] := eqVneq d 0; first by rewrite mulr0 !fracq0.
by rewrite fracq_eq ?mulf_neq0 //= mulrCA mulrA.
Qed.

Module RatField.

Definition add (x y : int * int) := (x.1 * y.2 + y.1 * x.2, x.2 * y.2).
Definition addq (x y : rat) := nosimpl fracq (add (valq x) (valq y)).

Definition opp (x : int * int) := (- x.1, x.2).
Definition oppq (x : rat) := nosimpl fracq (opp (valq x)).

Fact addC : commutative add.
Proof. by move=> x y; rewrite /add addrC [_.2 * _]mulrC. Qed.

Fact addA : associative add.
Proof.
by move=> x y z; rewrite /add !mulrA !mulrDl addrA ![_ * x.2]mulrC !mulrA.
Qed.

Fact addq_frac x y : x.2 != 0 -> y.2 != 0 ->
  (addq (fracq x) (fracq y)) = fracq (add x y).
Proof.
case: fracqP => // u fx u_neq0 _; case: fracqP => // v fy v_neq0 _.
rewrite /add /= ![(_ * numq _) * _]mulrACA [(_ * denq _) * _]mulrACA.
by rewrite [v * _]mulrC -mulrDr fracqMM ?mulf_neq0.
Qed.

Fact ratzD : {morph ratz : x y / x + y >-> addq x y}.
Proof. by move=> x y /=; rewrite !ratz_frac addq_frac // /add /= !mulr1. Qed.

Fact oppq_frac x : oppq (fracq x) = fracq (opp x).
Proof.
rewrite /opp; case: fracqP=> /= [|u fx u_neq0]; first by rewrite fracq0.
by rewrite -mulrN fracqMM.
Qed.

Fact ratzN : {morph ratz : x / - x >-> oppq x}.
Proof. by move=> x /=; rewrite !ratz_frac oppq_frac // /add /= !mulr1. Qed.

Fact addqC : commutative addq.
Proof. by move=> x y; rewrite /addq /=; rewrite addC. Qed.

Fact addqA : associative addq.
Proof.
move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK.
by rewrite !addq_frac ?mulf_neq0 ?denq_neq0 // addA.
Qed.

Fact add0q : left_id (fracq (0, 1)) addq.
Proof.
move=> x; rewrite -[x]valqK addq_frac ?denq_neq0 // /add /=.
by rewrite mul0r add0r mulr1 mul1r -surjective_pairing.
Qed.

Fact addNq : left_inverse (fracq (0, 1)) oppq addq.
Proof.
move=> x; rewrite -[x]valqK !(addq_frac, oppq_frac) ?denq_neq0 /add /opp //=.
rewrite mulNr addNr; apply/eqP.
by rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mul0r.
Qed.

Definition rat_ZmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical rat_ZmodType := ZmodType rat rat_ZmodMixin.

Definition mul (x y : int * int) := nosimpl (x.1 * y.1, x.2 * y.2).
Definition mulq (x y : rat) := nosimpl fracq (mul (valq x) (valq y)).

Fact mulC : commutative mul.
Proof. by move=> x y; rewrite /mul mulrC [_ * x.2]mulrC. Qed.

Fact mulA : associative mul. Proof. by move=> x y z; rewrite /mul !mulrA. Qed.

Definition inv (x : int * int) := nosimpl (x.2, x.1).
Definition invq (x : rat) := nosimpl fracq (inv (valq x)).

Fact mulq_frac x y : (mulq (fracq x) (fracq y)) = fracq (mul x y).
Proof.
rewrite /mul; case: fracqP => /= [|u fx u_neq0].
  by rewrite mul0r fracq0 /mulq /mul /= mul0r frac0q.
case: fracqP=> /= [|v fy v_neq0].
  by rewrite mulr0 fracq0 /mulq /mul /= mulr0 frac0q.
by rewrite ![_ * (v * _)]mulrACA fracqMM ?mulf_neq0.
Qed.

Fact ratzM : {morph ratz : x y / x * y >-> mulq x y}.
Proof. by move=> x y /=; rewrite !ratz_frac mulq_frac // /mul /= !mulr1. Qed.

Fact invq_frac x : x.1 != 0 -> x.2 != 0 -> invq (fracq x) = fracq (inv x).
Proof. by rewrite /inv; case: fracqP => // k {x} x k0; rewrite fracqMM. Qed.

Fact mulqC : commutative mulq. Proof. by move=> x y; rewrite /mulq mulC. Qed.

Fact mulqA : associative mulq.
Proof.
by move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK !mulq_frac mulA.
Qed.

Fact mul1q : left_id (fracq (1,1)) mulq.
Proof.
move=> x; rewrite -[x]valqK; rewrite mulq_frac /mul.
by rewrite !mul1r -surjective_pairing.
Qed.

Fact mulq_addl : left_distributive mulq addq.
Proof.
move=> x y z; rewrite -[x]valqK -[y]valqK -[z]valqK /=.
rewrite !(mulq_frac, addq_frac) ?mulf_neq0 ?denq_neq0 //=.
apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= !mulrDl; apply/eqP.
by rewrite !mulrA ![_ * (valq z).1]mulrC !mulrA ![_ * (valq x).2]mulrC !mulrA.
Qed.

Fact nonzero1q : (fracq (1, 1)) != (fracq (0, 1)). Proof. by []. Qed.

Definition rat_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.
Canonical  rat_Ring := Eval hnf in RingType rat rat_comRingMixin.
Canonical rat_comRing := Eval hnf in ComRingType rat mulqC.


Fact mulVq x : x != (fracq (0, 1)) -> mulq (invq x) x = (fracq (1, 1)).
Proof.
rewrite -[x]valqK fracq_eq ?denq_neq0 //= mulr1 mul0r=> nx0.
rewrite !(mulq_frac, invq_frac) ?denq_neq0 //.
by apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= mulr1 mul1r mulrC.
Qed.

Fact invq0 : invq (fracq (0, 1)) = (fracq (0, 1)). Proof. by apply/eqP. Qed.

Definition RatFieldUnitMixin := FieldUnitMixin mulVq invq0.
Canonical rat_unitRing :=
  Eval hnf in UnitRingType rat RatFieldUnitMixin.
Canonical rat_comUnitRing := Eval hnf in [comUnitRingType of rat].

Fact field_axiom : GRing.Field.mixin_of rat_unitRing.
Proof. exact. Qed.

Definition RatFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical rat_iDomain :=
  Eval hnf in IdomainType rat (FieldIdomainMixin field_axiom).
Canonical rat_fieldType := FieldType rat field_axiom.

Lemma numq_eq0 x : (numq x == 0) = (x == 0).
Proof.
rewrite -[x]valqK fracq_eq0; case: fracqP=> /= [|k {x} x k0].
  by rewrite eqxx orbT.
by rewrite !mulf_eq0 (negPf k0) /= denq_eq0 orbF.
Qed.

End RatField.

Canonical RatField.rat_ZmodType.
Canonical RatField.rat_Ring.
Canonical RatField.rat_comRing.
Canonical RatField.rat_unitRing.
Canonical RatField.rat_comUnitRing.
Canonical RatField.rat_iDomain.
Canonical RatField.rat_fieldType.

Hint Resolve denq_neq0 denq_gt0 denq_ge0.

Notation "n %:Q" := ((n : int)%:~R : rat)
  (at level 2, left associativity, format "n %:Q")  : ring_scope.

(* ratz should not be used, %:Q should be used instead *)
Lemma ratzE n : ratz n = n%:Q.
Proof.
elim: n=> [|n ihn|n ihn]; first by rewrite mulr0z ratz_frac.
  by rewrite intS mulrzDl RatField.ratzD ihn.
by rewrite intS opprD mulrzDl RatField.ratzD ihn.
Qed.

Lemma numq_int n : numq n%:Q = n. Proof. by rewrite -ratzE. Qed.
Lemma denq_int n : denq n%:Q = 1. Proof. by rewrite -ratzE. Qed.

Lemma rat0 : 0%:Q = 0. Proof. by []. Qed.
Lemma rat1 : 1%:Q = 1. Proof. by []. Qed.

Lemma numq_eq0 x : (numq x == 0) = (x == 0).
Proof. exact: RatField.numq_eq0. Qed.

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

(* Will be subsumed by pnatr_eq0 *)
Fact intq_eq0 n : (n%:~R == 0 :> rat) = (n == 0)%N.
Proof. by rewrite -ratzE /ratz rat_eqE /numq /denq /= mulr0 eqxx andbT. Qed.

(* fracq should never apear, its canonical form is _%:Q / _%:Q *)
Lemma fracqE x : fracq x = x.1%:Q / x.2%:Q.
Proof.
move:x => [m n] /=.
case n0: (n == 0); first by rewrite (eqP n0) fracq0 rat0 invr0 mulr0.
rewrite -[m%:Q]valqK -[n%:Q]valqK.
rewrite [_^-1]RatField.invq_frac ?(denq_neq0, numq_eq0, n0, intq_eq0) //.
rewrite [_ / _]RatField.mulq_frac /= /RatField.inv /RatField.mul /=.
by rewrite -!/(numq _) -!/(denq _) !numq_int !denq_int mul1r mulr1.
Qed.

Lemma divq_num_den x : (numq x)%:Q / (denq x)%:Q = x.
Proof. by rewrite -{3}[x]valqK [valq _]surjective_pairing /= fracqE. Qed.

CoInductive divq_spec (n d : int) : int -> int -> rat -> Type :=
| DivqSpecN of d = 0 : divq_spec n d n 0 0
| DivqSpecP k x of k != 0 : divq_spec n d (k * numq x) (k * denq x) x.

(* replaces fracqP *)
Lemma divqP n d : divq_spec n d n d (n%:Q / d%:Q).
Proof.
set x := (n, d); rewrite -[n]/x.1 -[d]/x.2 -fracqE.
by case: fracqP => [_|k fx k_neq0] /=; constructor. 
Qed.

Lemma divq_eq (nx dx ny dy : rat) : dx != 0 -> dy != 0 ->
  (nx / dx == ny / dy) = (nx * dy == ny * dx).
Proof.
move=> dx_neq0 dy_neq0; rewrite -(inj_eq (@mulIf _ (dx * dy) _)) ?mulf_neq0 //.
by rewrite mulrA divfK // mulrCA divfK // [dx * _ ]mulrC.
Qed.

CoInductive rat_spec (* (x : rat) *) : rat -> int -> int -> Type :=
  Rat_spec (n : int) (d : nat)  & coprime `|n| d.+1
  : rat_spec (* x  *) (n%:Q / d.+1%:Q) n d.+1.

Lemma ratP x : rat_spec x (numq x) (denq x).
Proof.
rewrite -{1}[x](divq_num_den); case hd: denq => [p|n].
  have: 0 < p%:Z by rewrite -hd denq_gt0.
  case: p hd=> //= n hd; constructor; rewrite -?hd ?divq_num_den //.
  by rewrite -[n.+1]/`|n.+1|%N -hd coprime_num_den.
by move: (denq_gt0 x); rewrite hd.
Qed.

Lemma coprimeq_num n d : coprime `|n| `|d| -> numq (n%:~R / d%:~R) = sgr d * n.
Proof.
move=> cnd /=; have <- := fracqE (n, d).
rewrite /numq /= (eqP (cnd : _ == 1%N)) divn1.
have [|d_gt0|d_lt0] := sgrP d;
by rewrite (mul0r, mul1r, mulN1r) //= ?[_ ^ _]signrN ?mulNr mulz_sign_abs.
Qed.

Lemma coprimeq_den n d :
  coprime `|n| `|d| -> denq (n%:~R / d%:~R) = (if d == 0 then 1 else `|d|).
Proof.
move=> cnd; have <- := fracqE (n, d).
by rewrite /denq /= (eqP (cnd : _ == 1%N)) divn1; case: d {cnd}.
Qed.

Lemma numqE x : (numq x)%:~R = x * (denq x)%:~R.
Proof. by rewrite -{2}[x]divq_num_den divfK // intq_eq0 denq_eq0. Qed.

Lemma denqP x : {d | denq x = d.+1}.
Proof. by rewrite /denq; case: x => [[_ [[|d]|]] //= _]; exists d. Qed.

Definition normq (x : rat) : rat :=  `|numq x|%:~R / (denq x)%:~R.
Definition le_rat (x y : rat) := numq x * denq y <= numq y * denq x.
Definition lt_rat (x y : rat) := numq x * denq y < numq y * denq x.

Lemma gt_rat0 x : lt_rat 0 x = (0 < numq x).
Proof. by rewrite /lt_rat mul0r mulr1. Qed.

Lemma lt_rat0 x : lt_rat x 0 = (numq x < 0).
Proof. by rewrite /lt_rat mul0r mulr1. Qed.

Lemma ge_rat0 x : le_rat 0 x = (0 <= numq x).
Proof. by rewrite /le_rat mul0r mulr1. Qed.

Lemma le_rat0 x : le_rat x 0 = (numq x <= 0).
Proof. by rewrite /le_rat mul0r mulr1. Qed.

Fact le_rat0D x y : le_rat 0 x -> le_rat 0 y -> le_rat 0 (x + y).
Proof.
rewrite !ge_rat0 => hnx hny.
have hxy: (0 <= numq x * denq y + numq y * denq x).
  by rewrite addr_ge0 ?mulr_ge0.
by rewrite /numq /= -!/(denq _) ?mulf_eq0 ?denq_eq0 !ler_gtF ?mulr_ge0.
Qed.

Fact le_rat0M x y : le_rat 0 x -> le_rat 0 y -> le_rat 0 (x * y).
Proof.
rewrite !ge_rat0 => hnx hny.
have hxy: (0 <= numq x * denq y + numq y * denq x).
  by rewrite addr_ge0 ?mulr_ge0.
by rewrite /numq /= -!/(denq _) ?mulf_eq0 ?denq_eq0 !ler_gtF ?mulr_ge0.
Qed.

Fact le_rat0_anti x : le_rat 0 x -> le_rat x 0 -> x = 0.
Proof.
by move=> hx hy; apply/eqP; rewrite -numq_eq0 eqr_le -ge_rat0 -le_rat0 hx hy.
Qed.

Lemma sgr_numq_div (n d : int) : sgr (numq (n%:Q / d%:Q)) = sgr n * sgr d.
Proof.
set x := (n, d); rewrite -/x.1 -/x.2 -fracqE.
case: fracqP => [|k fx k_neq0] /=; first by rewrite mulr0.
by rewrite !sgrM mulrACA mulr_sg k_neq0 sgr_denq mulr1 mul1r.
Qed.

Fact subq_ge0 x y : le_rat 0 (y - x) = le_rat x y.
Proof.
symmetry; rewrite ge_rat0 /le_rat -subr_ge0.
case: ratP => nx dx cndx; case: ratP => ny dy cndy.
rewrite -!mulNr addf_div ?intq_eq0 // !mulNr -!rmorphM -rmorphB /=.
symmetry; rewrite !lerNgt -sgr_cp0 sgr_numq_div mulrC gtr0_sg //.
by rewrite mul1r sgr_cp0.
Qed.

Fact le_rat_total : total le_rat.
Proof. by move=> x y; apply: ler_total. Qed.

Fact numq_sign_mul (b : bool) x : numq ((-1) ^+ b * x) = (-1) ^+ b * numq x.
Proof. by case: b; rewrite ?(mul1r, mulN1r) // numqN. Qed.

Fact numq_div_lt0 n d : n != 0 -> d != 0 ->
  (numq (n%:~R / d%:~R) < 0)%R = (n < 0)%R (+) (d < 0)%R.
Proof.
move=> n0 d0; rewrite -sgr_cp0 sgr_numq_div !sgr_def n0 d0.
by rewrite !mulr1n -signr_addb; case: (_ (+) _).
Qed.

Lemma normr_num_div n d : `|numq (n%:~R / d%:~R)| = numq (`|n|%:~R / `|d|%:~R).
Proof.
rewrite (normr_dec n) (normr_dec d) !rmorphM /= invfM mulrACA !sgr_def.
have [->|n_neq0] := altP eqP; first by rewrite mul0r mulr0.
have [->|d_neq0] := altP eqP; first by rewrite invr0 !mulr0.
rewrite !intr_sign invr_sign -signr_addb numq_sign_mul -numq_div_lt0 //.
by apply: (canRL (signrMK _)); rewrite mulz_sign_abs.
Qed.

Fact norm_ratN x : normq (- x) = normq x.
Proof. by rewrite /normq numqN denqN normrN. Qed.

Fact ge_rat0_norm x : le_rat 0 x -> normq x = x.
Proof.
rewrite ge_rat0; case: ratP=> [] // n d cnd n_ge0.
by rewrite /normq /= normr_num_div ?ger0_norm // divq_num_den.
Qed.

Fact lt_rat_def x y : (lt_rat x y) = (y != x) && (le_rat x y).
Proof. by rewrite /lt_rat ltr_def rat_eq. Qed.

Definition ratLeMixin := TotalPartialLeMixin le_rat0D le_rat0M le_rat0_anti
  subq_ge0 (@le_rat_total 0) norm_ratN ge_rat0_norm lt_rat_def.

Canonical rat_poIdomainType := POIdomainType rat ratLeMixin.
Canonical rat_poFieldType := POFieldType rat ratLeMixin.

Canonical rat_oIdomainType :=  OIdomainType rat (@le_rat_total 0).
Canonical rat_oFieldType :=  OFieldType rat (@le_rat_total 0).


Lemma numq_ge0 x : (0 <= numq x) = (0 <= x).
Proof.
by case: ratP => n d cnd; rewrite ?pmulr_lge0 ?invr_gt0 (ler0z, ltr0z).
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

Definition rat_archi_bound (x : rat) := `|numq x|.+1.

Fact rat_archi_boundP (x : rat) : 0 <= x -> x < (rat_archi_bound x)%:R.
Proof.
rewrite -numq_ge0 /rat_archi_bound; case: ratP=> [] [] // n d cnd _.
rewrite absz_nat ltr_pdivr_mulr ?ltr0z // pmulrn -rmorphM /=.
by rewrite ltr_nat mulnS leq_addr.
Qed.

Definition archiMixin := ArchimedianMixin rat_archi_boundP.
Canonical archiType := ArchiFieldType rat archiMixin.

Section QintPred.

Definition Qint := [qualify a x : rat | denq x == 1].
Fact Qint_key : pred_key Qint. Proof. by []. Qed.
Canonical Qint_keyed := KeyedQualifier Qint_key.

Lemma Qint_def x : (x \is a Qint) = (denq x == 1). Proof. by []. Qed.

Lemma numqK : {in Qint, cancel (fun x => numq x) intr}.
Proof. by move=> x /(_ =P 1 :> int) Zx; rewrite numqE Zx rmorph1 mulr1. Qed.

Lemma QintP x : reflect (exists z, x = z%:~R) (x \in Qint).
Proof.
apply: (iffP idP) => [/numqK <- | [z ->]]; first by exists (numq x).
by rewrite Qint_def denq_int.
Qed.

Fact Qint_subring_closed : subring_closed Qint.
Proof.
split=> // _ _ /QintP[x ->] /QintP[y ->]; apply/QintP.
  by exists (x - y); rewrite -rmorphB.
by exists (x * y); rewrite -rmorphM.
Qed.

Canonical Qint_opprPred := OpprPred Qint_subring_closed.
Canonical Qint_addrPred := AddrPred Qint_subring_closed.
Canonical Qint_mulrPred := MulrPred Qint_subring_closed.
Canonical Qint_zmodPred := ZmodPred Qint_subring_closed.
Canonical Qint_semiringPred := SemiringPred Qint_subring_closed.
Canonical Qint_smulrPred := SmulrPred Qint_subring_closed.
Canonical Qint_subringPred := SubringPred Qint_subring_closed.

End QintPred.

Section QnatPred.

Definition Qnat := [qualify a x : rat | (x \is a Qint) && (0 <= x)].
Fact Qnat_key : pred_key Qnat. Proof. by []. Qed.
Canonical Qnat_keyed := KeyedQualifier Qnat_key.

Lemma Qnat_def x : (x \is a Qnat) = (x \is a Qint) && (0 <= x). Proof. by []. Qed.

Lemma QnatP x : reflect (exists n : nat, x = n%:R) (x \in Qnat).
Proof.
rewrite Qnat_def; apply: (iffP idP) => [/andP []|[n ->]]; last first.
  by rewrite Qint_def pmulrn denq_int eqxx ler0z.
by move=> /QintP [] [] n ->; rewrite ?ler0z // => _; exists n.
Qed.

Fact Qnat_semiring_closed : semiring_closed Qnat.
Proof.
do 2?split; move => // x y; rewrite !Qnat_def => /andP[xQ hx] /andP[yQ hy].
  by rewrite rpredD // addr_ge0.
by rewrite rpredM // mulr_ge0.
Qed.

Canonical Qnat_addrPred := AddrPred Qnat_semiring_closed.
Canonical Qnat_mulrPred := MulrPred Qnat_semiring_closed.
Canonical Qnat_semiringPred := SemiringPred Qnat_semiring_closed.

End QnatPred.

Lemma natq_div m n : n %| m -> (m %/ n)%:R = m%:R / n%:R :> rat.
Proof. by apply: char0_natf_div; apply: char_po. Qed.

Section InRing.

Variable R : unitRingType.

Definition ratr x : R := (numq x)%:~R / (denq x)%:~R.

Lemma ratr_int z : ratr z%:~R = z%:~R.
Proof. by rewrite /ratr numq_int denq_int divr1. Qed.

Lemma ratr_nat n : ratr n%:R = n%:R.
Proof. exact: (ratr_int n). Qed.

Lemma rpred_rat S (ringS : @divringPred R S) (kS : keyed_pred ringS) a :
  ratr a \in kS.
Proof. by rewrite rpred_div ?rpred_int. Qed.

End InRing.

Section Fmorph.

Implicit Type rR : unitRingType.

Lemma fmorph_rat (aR : fieldType) rR (f : {rmorphism aR -> rR}) a :
  f (ratr _ a) = ratr _ a.
Proof. by rewrite fmorph_div !rmorph_int. Qed.

Lemma fmorph_eq_rat rR (f : {rmorphism rat -> rR}) : f =1 ratr _.
Proof. by move=> a; rewrite -{1}[a]divq_num_den fmorph_div !rmorph_int. Qed.

End Fmorph.

Section InPoField.

Import orderedalg.
Variable F : poFieldType.

Fact ratr_is_rmorphism : rmorphism (@ratr F).
Proof.
have injZtoQ: @injective rat int intr by exact: intr_inj.
have nz_den x: (denq x)%:~R != 0 :> F by rewrite intr_eq0 denq_eq0.
do 2?split; rewrite /ratr ?divr1 // => x y; last first.
  rewrite mulrC mulrAC; apply: canLR (mulKf (nz_den _)) _; rewrite !mulrA.
  do 2!apply: canRL (mulfK (nz_den _)) _; rewrite -!rmorphM; congr _%:~R.
  apply: injZtoQ; rewrite !rmorphM [x * y]lock /= !numqE -lock.
  by rewrite -!mulrA mulrA mulrCA -!mulrA (mulrCA y).
apply: (canLR (mulfK (nz_den _))); apply: (mulIf (nz_den x)).
rewrite mulrAC mulrBl divfK ?nz_den // mulrAC -!rmorphM.
apply: (mulIf (nz_den y)); rewrite mulrAC mulrBl divfK ?nz_den //.
rewrite -!(rmorphM, rmorphB); congr _%:~R; apply: injZtoQ.
rewrite !(rmorphM, rmorphB) [_ - _]lock /= -lock !numqE.
by rewrite (mulrAC y) -!mulrBl -mulrA mulrAC !mulrA.
Qed.

Canonical ratr_additive := Additive ratr_is_rmorphism.
Canonical ratr_rmorphism := RMorphism ratr_is_rmorphism.

Lemma ler_rat : {mono (@ratr F) : x y / x <= y}.
Proof.
move=> x y /=; case: (ratP x) => nx dx cndx; case: (ratP y) => ny dy cndy.
rewrite !fmorph_div /= !ratr_int !ler_pdivl_mulr ?ltr0z //.
by rewrite ![_ / _ * _]mulrAC !ler_pdivr_mulr ?ltr0z // -!rmorphM /= !ler_int.
Qed.

Lemma ltr_rat : {mono (@ratr F) : x y / x < y}.
Proof. exact: lerW_mono ler_rat. Qed.

Lemma ler0q x : (0 <= ratr F x) = (0 <= x).
Proof. by rewrite (_ : 0 = ratr F 0) ?ler_rat ?rmorph0. Qed.

Lemma lerq0 x : (ratr F x <= 0) = (x <= 0).
Proof. by rewrite (_ : 0 = ratr F 0) ?ler_rat ?rmorph0. Qed.

Lemma ltr0q x : (0 < ratr F x) = (0 < x).
Proof. by rewrite (_ : 0 = ratr F 0) ?ltr_rat ?rmorph0. Qed.

Lemma ltrq0 x : (ratr F x < 0) = (x < 0).
Proof. by rewrite (_ : 0 = ratr F 0) ?ltr_rat ?rmorph0. Qed.

End InPoField.

Implicit Arguments ratr [[R]].