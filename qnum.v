Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint div orderedalg orderedzint.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Record qnum : Set := Qnum {
  valq : (zint * zint) ;
  _ : (0 < valq.2) && (coprime (absz valq.1) (absz (valq.2))) 
}.

Definition zint_qnum (n : zint) := @Qnum (n, 1) (coprimen1 _).
(* Coercion zint_qnum (n : zint) := @Qnum (n, 1) (coprimen1 _). *)

Canonical Structure qnum_subType := Eval hnf in [subType for valq by qnum_rect].
Definition qnum_eqMixin := [eqMixin of qnum by <:].
Canonical Structure qnum_eqType := EqType qnum qnum_eqMixin.
Definition qnum_countMixin := [countMixin of qnum by <:].
Definition qnum_choiceMixin := CountChoiceMixin qnum_countMixin.
Canonical Structure qnum_choiceType := ChoiceType qnum qnum_choiceMixin.
Canonical Structure qnum_countType := CountType qnum qnum_countMixin.

Notation numq x := ((valq x).1).
Notation denq x := ((valq x).2).

Lemma denq_gt0 : forall x, 0 < denq x.
Proof. by case=> [[a b] /= i]; case/andP:(i). Qed.

Lemma denq_neq0 : forall x, denq x != 0.
Proof. by move=> x; rewrite ltrNW ?denq_gt0. Qed.

Lemma denq_eq0 : forall x, denq x == 0 = false.
Proof. by move=> x; rewrite (negPf (denq_neq0 _)). Qed.

Lemma coprime_num_den : forall x, coprime (absz (numq x)) (absz (denq x)).
Proof. by case=> [[a b] /= i]; case/andP:(i). Qed.

Lemma QnumK : forall x P, @Qnum (numq x, denq x) P = x.
Proof. by move=> [[a b] P'] P; apply: val_inj. Qed.

Lemma abszr : forall x, absz `|x| = absz x. Proof. by case. Qed.

Lemma fracq_subproof : forall x : zint * zint,
  let n := if x.2 == 0 then 0 else
    sgr x.2 * sgr x.1 *~ ((absz x.1) %/ gcdn (absz x.1) (absz x.2))%:Z in
    let d := if x.2 == 0 then 1 else 
      (absz x.2 %/ gcdn (absz (x.1)) (absz x.2))%:Z in
        (0 < d) && (coprime (absz n) (absz d)).
Proof. 
move=> [m n] /=; case: ifP=> n0; rewrite ?n0 // ltz_nat lt0n eq_sym.
rewrite eqn_div ?dvdn_gcdr 1?eq_sym ?gcdn_gt0 ?mul0n
  1?orbC ?lt0n ?absz_eq0 ?n0 //=.
rewrite -abszr absr_mulz absr_mul !absr_sg n0 mul1r.
case m0: (_ == 0)=> /=.
  by rewrite !(eqP m0) gcd0n divnn /= lt0n absz_eq0 n0.
move: m0 n0; rewrite -!absz_eq0.
move: (absz _) (absz _) => {n m} m n n0 m0; rewrite /coprime.
rewrite -(@eqn_pmul2l (gcdn n m)) ?muln1 ?gcdn_gt0 ?lt0n ?n0 // -gcdn_mul2l.
do 2!rewrite divn_mulCA ?(dvdn_gcdl, dvdn_gcdr) ?divnn //.
by rewrite ?gcdn_gt0 ?lt0n ?n0 ?muln1.
Qed.

Definition fracq (x : zint * zint) := nosimpl @Qnum (_, _) (fracq_subproof x).

Lemma zint_qnumE : forall n, zint_qnum n = fracq (n, 1).
Proof.
by move=> n; apply: val_inj; rewrite /= mul1r gcdn1 !divn1 -absrz -absr_sgP. 
Qed.

Lemma fracqK : forall x : qnum, fracq (valq x) = x.
Proof. 
move=> [[n d] /= Pnd]; apply: val_inj=> /=.
move: Pnd; rewrite /coprime /fracq /=; case/andP=> hd; move/eqP=> hnd.
rewrite ltrNW // hnd !divn1 -!absrz mulzrA -[sgr n *~ _]absr_sgP.
by rewrite ger0_abs ?ltrW // gtr0_sg //.
Qed.

Lemma valq_frac : forall x (k := sgr x.2 * gcdn (absz x.1) (absz x.2)), x.2 != 0 ->
  x = (k * numq (fracq x), k *  denq (fracq x)).
Proof.
move=> [n d] /=; case d0: (d == 0)=> // _.
rewrite !mulzzr mulrCA -!mulrA -!mulzM divn_mulCA ?dvdn_gcdl //.
congr (_, _).
  rewrite divnn gcdn_gt0 orbC lt0n absz_eq0 d0 muln1.
  rewrite mulrA mulrAC mulrA mulss d0 mul1r -absrz mulrC.
  by rewrite {1}[n]absr_sgP mulzzr.
rewrite divn_mulCA ?dvdn_gcdr // divnn gcdn_gt0 orbC lt0n absz_eq0 d0 muln1.
by rewrite -absrz {1}[d]absr_sgP mulzzr.
Qed.

CoInductive valq_spec (x : zint * zint) : zint * zint -> qnum -> Type := 
| ValqSpecN of x.2 = 0 : valq_spec x (x.1, 0) (@Qnum (0, 1) isT)
| ValqSpecP k fx of x.2 != 0 & k != 0 & k = sgr x.2 * gcdn (absz x.1) (absz x.2) 
  & fx = fracq x & x = (k * numq fx, k * denq fx) : 
  valq_spec x (k * numq fx, k * denq fx) (fx).

Lemma valqP : forall x : zint * zint, valq_spec x x (fracq x).
Proof.
move=> x; case dx0: (x.2 == 0).
  have hx: x = (x.1, 0) by  rewrite [x]surjective_pairing (eqP dx0).
  rewrite {2}hx; rewrite /fracq.
  have ->: @Qnum (_, _) (fracq_subproof x) = @Qnum (0, 1) isT.
    by apply: val_inj=> /=; rewrite dx0.
  by constructor; rewrite (eqP dx0).
rewrite {2}[x]valq_frac ?dx0 //; constructor; rewrite ?dx0 //.
  rewrite mulf_neq0 ?sgr_eq0 ?dx0 //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 dx0.
by rewrite -valq_frac // dx0.
Qed.  

Lemma fracq_eq : forall x y, x.2 != 0 -> y.2 != 0 ->
  (fracq x == fracq y) = (x.1 * y.2 == y.1 * x.2).
Proof.
move=> x y hdx hdy; case: valqP hdx=> //=; do ?by move->.
move => // k fx hdx k0 hk hfx hx _; rewrite ?hx /=.
(* Note this : *)
rewrite {-1}[y]valq_frac //.
rewrite [sgr _ * _]lock; set k' := locked _.
rewrite [fracq y]lock; set fy := locked _=> /=.
have k'0: k' != 0. 
  rewrite /k'; unlock; rewrite mulf_neq0 ?sgr_cp0 //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdy.
(* could be replaced in ssr > 1.2 by a case: valqP hdy *)
rewrite !mulrA ![_ * k]mulrC !mulrA ![_ * k']mulrC -!mulrA.
rewrite !(inj_eq (mulfI _)) //; apply/idP/idP; first by move/eqP->.
move=> hxy; rewrite -val_eqE /=.
rewrite [valq fx]surjective_pairing [valq fy]surjective_pairing.
rewrite xpair_eqE; suff hnfx : (denq fx = denq fy).
  by move: hxy; rewrite hnfx eqxx andbT (inj_eq (mulIf _)) ?denq_eq0.
rewrite -[denq fx]gtr0_abs ?denq_gt0 // -[denq fy]gtr0_abs ?denq_gt0 //.
(* Todo : a bit theory about dvdz, comming later *)
apply/eqP; rewrite !absrz eqz_nat eqn_dvd.
rewrite -(@gauss _ (absz (numq fx))) 1?coprime_sym ?coprime_num_den // andbC.
rewrite -(@gauss _ (absz (numq fy))) 1?coprime_sym ?coprime_num_den //.
have h: (absz (numq fy) * absz (denq fx) = absz (numq fx) * absz (denq fy))%N.
  by apply/eqP; rewrite -eqz_nat !mulzM -!absrz -!absr_mul (eqP hxy).
by rewrite h dvdn_mull // -h dvdn_mull.
Qed.

Lemma frac0q : forall x, fracq (0, x) = fracq (0, 1).
Proof.
move=> x; rewrite /fracq; apply: val_inj=> //= (* Warning : without //= Qed fails) *).
case: ifP=> x0; rewrite ?x0 //=.
by rewrite !mulr0 !mul0zr !gcd0n !divnn lt0n absz_eq0 x0.
Qed.

Lemma fracq0 : forall x, fracq (x, 0) = fracq (0, 1). 
Proof. by move=> x; apply/eqP. Qed.

Lemma fracq_eq0 : forall x, (fracq x == fracq (0, 1)) = (x.1 == 0) || (x.2 == 0).
Proof.
move=> [n d] /=; case d0: (d == 0); first by rewrite (eqP d0) orbC fracq0 eqxx.
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

Lemma addq_frac : forall x y, x.2 != 0 -> y.2 != 0 -> (addq (fracq x) (fracq y)) = fracq (add x y).
Proof.
move=> x y hdx hdy; rewrite /add.
(* Note this : *)
rewrite {-1}[x]valq_frac //.
rewrite [sgr _ * _]lock; set k := locked _.
rewrite [fracq x]lock; set fx := locked _=> /=.
have k0: k != 0. 
  rewrite /k; unlock; rewrite mulf_neq0 ?sgr_cp0 //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdx.
(* could be replaced in ssr > 1.2 by a case: valqP hdx *)
(* Note this : *)
rewrite {-1}[y]valq_frac //.
rewrite [sgr _ * _]lock; set k' := locked _.
rewrite [fracq y]lock; set fy := locked _=> /=.
have k'0: k' != 0. 
  rewrite /k'; unlock; rewrite mulf_neq0 ?sgr_cp0 //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdy.
(* could be replaced in ssr > 1.2 by a case: valqP hdy *)
apply/eqP; rewrite fracq_eq /= ?mulf_neq0 ?denq_neq0 //; apply/eqP.
by rewrite !mulr_addl !mulrA ![_ * k]mulrC !mulrA ![_ * k']mulrC !mulrA.
Qed.

Lemma addqM : {morph zint_qnum : x y / x + y >-> addq x y}.
Proof. by move=> x y /=; rewrite !zint_qnumE addq_frac // /add /= !mulr1. Qed.

Lemma oppq_frac : forall x, oppq (fracq x) = fracq (opp x).
Proof.
move=> x; rewrite /opp; case hdx: (x.2 == 0).
  by case: x hdx=> m n /= hn; rewrite (eqP hn) ?fracq0.
(* Note this : *)
rewrite {-1}[x]valq_frac ?hdx //.
rewrite [sgr _ * _]lock; set k := locked _.
rewrite [fracq x]lock; set fx := locked _=> /=.
have k0: k != 0. 
  rewrite /k; unlock; rewrite mulf_neq0 ?sgr_cp0 ?hdx //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdx.
(* could be replaced in ssr > 1.2 by a case: valqP hdx *)
apply/eqP; rewrite fracq_eq /= ?mulf_neq0 ?denq_neq0 //.
by rewrite !(mulrA, mulNr) [_ * k]mulrC.
Qed.

Lemma oppqM : {morph zint_qnum : x / - x >-> oppq x}.
Proof. by move=> x /=; rewrite !zint_qnumE oppq_frac // /add /= !mulr1. Qed.

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
Canonical Structure qnum_ZmodType := ZmodType qnum qnum_ZmodMixin.

Definition mul (x y : zint * zint) := nosimpl (x.1 * y.1, x.2 * y.2).
Definition mulq (x y : qnum) := nosimpl fracq (mul (valq x) (valq y)).

Lemma mulC : commutative mul.
Proof. by move=> x y; rewrite /mul mulrC [_ * x.2]mulrC. Qed.

Lemma mulA : associative mul. Proof. by move=> x y z; rewrite /mul !mulrA. Qed.

Definition inv (x : zint * zint) := nosimpl (x.2, x.1).
Definition invq (x : qnum) := nosimpl fracq (inv (valq x)).

Lemma mulq_frac: forall x y, (mulq (fracq x) (fracq y)) = fracq (mul x y).
Proof.
move=> x y; rewrite /mul.
(* Note this : *)
case hdx: (x.2 == 0).
  by case: x hdx=> m n /= hn; rewrite /mulq /mul (eqP hn) ?mul0r ?fracq0 ?frac0q.
rewrite {-1}[x]valq_frac ?hdx //.
rewrite [sgr _ * _]lock; set k := locked _.
rewrite [fracq x]lock; set fx := locked _=> /=.
have k0: k != 0. 
  rewrite /k; unlock; rewrite mulf_neq0 ?sgr_cp0 ?hdx //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdx.
(* could be replaced in ssr > 1.2 by a case: valqP hdx *)
(* Note this : *)
case hdy: (y.2 == 0).
  by case: y hdy=> m n /= hn; rewrite /mulq /mul (eqP hn) ?mulr0 ?fracq0 ?frac0q.
rewrite {-1}[y]valq_frac ?hdy //.
rewrite [sgr _ * _]lock; set k' := locked _.
rewrite [fracq y]lock; set fy := locked _=> /=.
have k'0: k' != 0. 
  rewrite /k'; unlock; rewrite mulf_neq0 ?sgr_cp0 ?hdy //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdy.
(* could be replaced in ssr > 1.2 by a case: valqP hdy *)
apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //=.
by rewrite !mulrA ![_ * k]mulrC !mulrA ![_ * k']mulrC !mulrA.
Qed.

Lemma mulqM : {morph zint_qnum : x y / x * y >-> mulq x y}.
Proof. by move=> x y /=; rewrite !zint_qnumE mulq_frac // /mul /= !mulr1. Qed.

Lemma invq_frac : forall x, x.1 != 0 -> x.2 != 0 -> invq (fracq x) = fracq (inv x).
Proof.
move=> x hnx hdx; rewrite /inv; move: hnx.
(* Note this : *)
rewrite {-2}[x]valq_frac //.
rewrite [sgr _ * _]lock; set k := locked _.
rewrite [fracq x]lock; set fx := locked _=> /=.
have k0: k != 0. 
  rewrite /k; unlock; rewrite mulf_neq0 ?sgr_cp0 //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdx.
(* could be replaced in ssr > 1.2 by a case: valqP hdx *)
rewrite !(mulf_eq0, negb_or, k0) /= => nfx0.
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
Canonical Structure  qnum_Ring := Eval hnf in RingType qnum qnum_comRingMixin.
Canonical Structure qnum_comRing := Eval hnf in ComRingType qnum mulqC.


Lemma mulVq : forall x, x != (fracq (0, 1)) -> mulq (invq x) x = (fracq (1, 1)).
Proof.
move=> x; rewrite -[x]fracqK fracq_eq ?denq_neq0 //= mulr1 mul0r=> nx0.
rewrite !(mulq_frac, invq_frac) ?denq_neq0 //.
by apply/eqP; rewrite fracq_eq ?mulf_neq0 ?denq_neq0 //= mulr1 mul1r mulrC.
Qed.

Lemma invq0 : invq (fracq (0, 1)) = (fracq (0, 1)). Proof. by apply/eqP. Qed.

Definition QnumFieldUnitMixin := FieldUnitMixin mulVq invq0.
Canonical Structure qnum_unitRing :=
  Eval hnf in UnitRingType qnum QnumFieldUnitMixin.
Canonical Structure qnum_comUnitRing := Eval hnf in [comUnitRingType of qnum].

Lemma field_axiom : GRing.Field.mixin_of qnum_unitRing.
Proof. exact. Qed.

Definition QnumFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical Structure qnum_iDomain :=
  Eval hnf in IdomainType qnum (FieldIdomainMixin field_axiom).
Canonical Structure qnum_fieldMixin := FieldType qnum field_axiom.

Lemma numq_eq0 : forall x, (numq x == 0) = (x == 0).
Proof.
move=> x; rewrite -[x]fracqK fracq_eq0.
case: valqP=> //= [hx|k fx dx k0 hk hfx hx]; first by rewrite ?hx eqxx orbT.
by rewrite ?hx !mulf_eq0 (negPf k0) ?denq_eq0 /= orbF.
Qed.

(* Lemma fracqE : forall x, fracq x = mulq x.1%:zR (invq x.2%:zR). *)
(* Proof. *)
(* move=> x. *)
(* rewrite -[x.1%:zR]fracqK /=. *)

(* rewrite !(invq_frac, mulq_frac) /= ?(denq_eq0, numq_eq0) //. *)
(*   apply/eqP; rewrite fracq_eq /=. *)
(* rewrite /mulq /invq /mul /inv /=. *)

(* case: valqP=> //=. *)

Definition pos (x : zint * zint) := posr (x.1 * x.2).
Definition posq (x : qnum) := nosimpl (pos (valq x)).

Lemma posq_frac : forall x, posq (fracq x) = pos x.
Proof.
move=> x; rewrite /pos.
(* Note this : *)
case hdx: (x.2 == 0).
  by case: x hdx=> m n /= hn; rewrite ?(eqP hn) /posq /pos mulr0.
rewrite {-1}[x]valq_frac ?hdx //.
rewrite [sgr _ * _]lock; set k := locked _.
rewrite [fracq x]lock; set fx := locked _=> /=.
have k0: k != 0. 
  rewrite /k; unlock; rewrite mulf_neq0 ?sgr_cp0 ?hdx //.
  by rewrite eqz_nat -lt0n gcdn_gt0 orbC lt0n absz_eq0 hdx.
(* could be replaced in ssr > 1.2 by a case: valqP hdx *)
rewrite /pos /= mulrCA !mulrA -mulrA; symmetry.
rewrite posr_ge0 -(mulr0 (k * k)) ler_pmul2r -?posr_ge0 //.
by rewrite -sgr_cp0 sgr_mul mulss k0.
Qed.

Lemma posq0 : posq 0. Proof. done. Qed.

Lemma posq_add : forall x y, posq x -> posq y -> posq (addq x y).
Proof. 
move=> x y; rewrite -[x]fracqK -[y]fracqK.
rewrite !(addq_frac, posq_frac) ?denq_neq0 //.
rewrite /pos /add /= => px py; rewrite mulr_addl posr_add //.
  rewrite mulrCA !mulrA [_ * numq x]mulrC -mulrA posr_mul //.
  by rewrite posr_ge0 ltrW // -sgr_cp0 sgr_mul mulss denq_neq0.
rewrite !mulrA mulrC !mulrA [_ * numq y]mulrC -mulrA posr_mul //.
by rewrite posr_ge0 ltrW // -sgr_cp0 sgr_mul mulss denq_neq0.
Qed.

Lemma posq_mul : forall x y, posq x -> posq y -> posq (mulq x y).
Proof.
move=> x y; rewrite -[x]fracqK -[y]fracqK.
rewrite !(mulq_frac, posq_frac) ?denq_neq0 //.
rewrite /pos /mul /= => px py. 
by rewrite mulrAC !mulrA -mulrA [_ * numq _]mulrC posr_mul.
Qed.

Lemma posq_anti : forall x, posq x -> posq (oppq x) -> x = 0.
Proof.
move=> x; rewrite -[x]fracqK !(oppq_frac, posq_frac) ?denq_neq0 //.
rewrite /pos /opp /= mulNr !posr_ge0 oppr_cp0=> px pNx.
by apply/eqP; rewrite fracq_eq0 -mulf_eq0 eqr_le px pNx.
Qed.

Lemma posq_total : forall x, (posq (oppq x) || posq x).
Proof.
move=> x; rewrite -[x]fracqK !(oppq_frac, posq_frac) ?denq_neq0 //.
by rewrite /pos /opp /= mulNr !posr_ge0 oppr_cp0 ler_total.
Qed.

Definition qnum_POrderedMixin := PartialOrderMixin posq0
  posq_add posq_mul posq_anti.
Canonical Structure qnum_poIdomainType := POIdomainType qnum qnum_POrderedMixin.

Lemma le_q_total : (@total qnum) (<=%R).
Proof. by move=> x y; rewrite !ler_pos -oppr_sub posq_total. Qed.

Canonical Structure qnum_oIdomainType := OIdomainType qnum le_q_total.

End QnumField.

Canonical Structure qnum_ZmodType := ZmodType qnum QnumField.qnum_ZmodMixin.
Canonical Structure qnum_Ring := Eval hnf in RingType qnum QnumField.qnum_comRingMixin.
Canonical Structure qnum_comRing := Eval hnf in ComRingType qnum QnumField.mulqC.
Canonical Structure qnum_unitRing := Eval hnf in UnitRingType qnum QnumField.QnumFieldUnitMixin.
Canonical Structure qnum_comUnitRing := Eval hnf in [comUnitRingType of qnum].
Canonical Structure qnum_iDomain :=
  Eval hnf in IdomainType qnum (FieldIdomainMixin QnumField.field_axiom).
Canonical Structure qnum_fieldType := FieldType qnum QnumField.field_axiom.
Canonical Structure qnum_poIdomainType := POIdomainType qnum QnumField.qnum_POrderedMixin.
Canonical Structure qnum_oIdomainType := OIdomainType qnum QnumField.le_q_total.
Canonical Structure qnum_poFieldType := POFieldType qnum QnumField.qnum_POrderedMixin.
Canonical Structure qnum_oFieldType := OFieldType qnum QnumField.le_q_total.


Notation "n %:Q" := (zint_qnum n)
  (at level 2, left associativity, format "n %:Q")  : ring_scope.

(* Eval compute in (8%:Q / 15%:Q >= 1 / 2%:Q :> qnum). (* OK *) *)

Lemma numq_zint : forall (n : zint), numq n%:Q = n. Proof. by move=> n; apply/eqP. Qed.
Lemma denq_zint : forall (n : zint), denq n%:Q = 1. Proof. by []. Qed.

Lemma qnum0 : 0%:Q = 0. Proof. by apply/eqP. Qed.
Lemma qnum1 : 1%:Q = 1. Proof. by apply/eqP. Qed.

(* Todo : prove morphism/compatibility lemmas for _%:zR  and/or %:Q *)

Lemma addqM : {morph zint_qnum : x y / x + y}.
Proof. exact: QnumField.addqM. Qed.

Lemma oppqM : {morph zint_qnum : x / - x}.
Proof. exact: QnumField.oppqM. Qed.

Lemma mulqM : {morph zint_qnum : x y / x * y}.
Proof. exact: QnumField.mulqM. Qed.

Lemma mulz1q : forall n, n%:zR = n%:Q.
Proof. 
elim=> //=; first by rewrite mul0zr qnum0.
  by move=> n hn; rewrite zintS mulzr_addl addqM hn.
by move=> n hn; rewrite zintS oppr_add mulzr_addl addqM hn !mulNzr oppqM.
Qed.

Lemma eqq_zint : forall x y, (x%:Q == y%:Q) = (x == y).
Proof.
by move=> x y; rewrite -[x%:Q]fracqK -[y%:Q]fracqK fracq_eq //= !mulr1.
Qed.

Lemma numq_eq0 : forall x, (numq x == 0) = (x == 0).
Proof. exact QnumField.numq_eq0. Qed.

Lemma qnumz_eq0 : forall x, (x%:Q == 0) = (x == 0).
Proof. by move=> x; rewrite -qnum0 eqq_zint. Qed.

Lemma fracqE : forall x, fracq x = x.1%:Q / x.2%:Q.
Proof.
move=> [m n] /=.
case n0: (n == 0); first by rewrite (eqP n0) fracq0 qnum0 invr0 mulr0.
rewrite -[m%:Q]fracqK -[n%:Q]fracqK. 
rewrite [_^-1]QnumField.invq_frac ?(denq_neq0, numq_eq0, eqq_zint, n0) //.
  rewrite [_ / _]QnumField.mulq_frac /= /QnumField.inv /QnumField.mul /=.
  by rewrite mulr1 mul1r.
by rewrite -qnum0 eqq_zint n0.
Qed.

Lemma divq_num_den : forall x, (numq x)%:Q / (denq x)%:Q = x.
Proof.
by move=> x; rewrite -{3}[x]fracqK [valq _]surjective_pairing /= fracqE.
Qed.

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
