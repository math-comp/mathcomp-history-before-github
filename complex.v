Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint div orderedalg qnum poly.

Import GRing.Theory ORing.Theory AbsrNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Reserved Notation "x +i* y" (at level 40, left associativity, format "x  +i*  y").
Reserved Notation "x -i* y" (at level 40, left associativity, format "x  -i*  y").

CoInductive cplx (R : oFieldType) : Type := Cplx { Re : R; Im : R }.
Coercion cplx_of_R (F : oFieldType) (x : F) := Cplx x 0.
Notation "x %:C" := (x : cplx _)
  (at level 2, left associativity, format "x %:C")  : ring_scope.
Notation "x +i* y" := (Cplx x y) : ring_scope.
Notation "x -i* y" := (Cplx x (- y)) : ring_scope.
Notation "x *i " := (Cplx 0 x) (at level 8, format "x *i") : ring_scope.
Notation "''i'" := (Cplx 0 1) : ring_scope.

Module CplxEqChoice.
Section CplxEqChoice.

Variable R : oFieldType.
Notation C := (cplx R).

Definition sqR_of_cplx (x : C) := let: a +i* b := x in [::a;  b].
Definition cplx_of_sqR (x : seq R) :=
  if x is [:: a; b] then Some (a +i* b) else None.

Lemma cplx_of_sqRK : pcancel sqR_of_cplx cplx_of_sqR.
Proof. by case. Qed.

Definition cplx_eqMixin := PcanEqMixin cplx_of_sqRK.
Definition cplx_choiceMixin := PcanChoiceMixin cplx_of_sqRK.

End CplxEqChoice.
End CplxEqChoice.

Canonical Structure cplx_eqType R :=
  EqType (cplx R) (CplxEqChoice.cplx_eqMixin R).
Canonical Structure cplx_choiceType R :=
  ChoiceType (cplx R) (CplxEqChoice.cplx_choiceMixin R).

Lemma eq_cplx : forall (R : oFieldType) (x y : cplx R),
  (x == y) = (Re x == Re y) && (Im x == Im y).
Proof.
move=> R [a b] [c d] /=.
apply/eqP/andP; first by move=> [-> ->]; split.
by case; move/eqP->; move/eqP->.
Qed.

Lemma cplxr0 : forall (R : oFieldType) (x : R), x +i* 0 = x. Proof. by []. Qed.

Module CplxField.
Section CplxField.

Variable R : oFieldType.
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
rewrite !mulr_addr !mulr_addl !mulrN !mulNr !mulrA !oppr_add -!addrA.
by congr ((_ + _) +i* (_ + _)); rewrite !addrA addrAC;
  congr (_ + _); rewrite addrC.
Qed.

Definition invc (x : C) := let: a +i* b := x in let n2 := (a ^+ 2 + b ^+ 2) in
  (a / n2) -i* (b / n2).

Lemma mul1c : left_id C1 mulc.
Proof. by move=> [a b] /=; rewrite !mul1r !mul0r subr0 addr0. Qed.

Lemma mulc_addl : left_distributive mulc addc.
Proof.
move=> [a b] [c d] [e f] /=; rewrite !mulr_addl !oppr_add -!addrA.
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
rewrite ![_ / _ * _]mulrAC [b * a]mulrC subrr cplxr0 -mulr_addl mulfV //.
by rewrite paddr_eq0 ?mulf_eq0 ?orbb // -expr2 exprn_even_ge0.
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

Definition lec (x y : C) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a <= c).

Definition ltc (x y : C) :=
  let: a +i* b := x in let: c +i* d := y in
    (d == b) && (a < c).

Lemma ltc01 : ltc 0 1. Proof. by rewrite /= eqxx ltr01. Qed.

Lemma ltc0_add : forall x y, ltc 0 x -> ltc 0 y -> ltc 0 (x + y).
Proof.
move=> [a b] [c d] /= /andP [/eqP-> ha] /andP [/eqP-> hc].
by rewrite addr0 eqxx addr_gt0.
Qed.

Lemma ltc0_mul : forall x y, ltc 0 x -> ltc 0 (x * y) = ltc 0 y.
Proof.
move=> [a b] [c d] /= => /andP [/eqP-> a_gt0].
by rewrite !mul0r addr0 subr0 mulf_eq0 gtr_eqF //= pmulr_rgt0.
Qed.

Lemma ltc0_anti : forall x,  ltc 0 x -> ~~ ltc 0 (-x).
Proof.
move=> [a b] /= /andP [/eqP-> ha]; rewrite oppr0 eqxx /= oppr_cp0.
by case: ltrgtP ha.
Qed.

Lemma subc_gt0  : forall x y, ltc 0 (y - x) = ltc x y.
Proof. by move=> [a b] [c d] /=; rewrite subr_gt0 subr_eq0. Qed.

Lemma lec_eqVlt : forall x y, lec x y = ((y == x) || ltc x y).
Proof.
by move=> [a b] [c d]; rewrite eq_cplx andbC -andb_orr /= ler_eqVlt.
Qed.

Definition cplx_POrderedMixin := PartialOrderMixin ltc01 ltc0_add ltc0_mul ltc0_anti subc_gt0 lec_eqVlt.
Canonical Structure cplx_poIdomainType := POIdomainType C cplx_POrderedMixin.

End CplxField.
End CplxField.

Canonical Structure cplx_ZmodType R :=
  ZmodType (cplx R) (CplxField.cplx_ZmodMixin R).
Canonical Structure cplx_Ring R :=
  Eval hnf in RingType (cplx R) (CplxField.cplx_comRingMixin R).
Canonical Structure cplx_comRing R :=
  Eval hnf in ComRingType (cplx R) (@CplxField.mulcC R).
Canonical Structure cplx_unitRing R :=
  Eval hnf in UnitRingType (cplx R) (CplxField.CplxFieldUnitMixin R).
Canonical Structure cplx_comUnitRing R :=
  Eval hnf in [comUnitRingType of (cplx R)].
Canonical Structure cplx_iDomain R :=
  Eval hnf in IdomainType (cplx R) (FieldIdomainMixin (@CplxField.field_axiom R)).
Canonical Structure cplx_fieldType R :=
  FieldType (cplx R) (@CplxField.field_axiom R).
Canonical Structure cplx_poIdomainType R :=
  POIdomainType (cplx R) (CplxField.cplx_POrderedMixin R).
Canonical Structure cplx_poFieldType R :=
  POFieldType (cplx R) (CplxField.cplx_POrderedMixin R).

Definition conjc (R : oFieldType) (x : cplx R) := let: a +i* b := x in a -i* b.
Notation "x ^*" := (conjc x) (at level 2, format "x ^*").

Ltac simpc := do ?
  [ rewrite -[(_ +i* _) - (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) + (_ +i* _)]/(_ +i* _)
  | rewrite -[(_ +i* _) * (_ +i* _)]/(_ +i* _)
  | rewrite -[(posr (_ +i* _))]/(_ && _)].

Section CplxTheory.

Variable R : oFieldType.
Notation C := (cplx R).

Lemma cplx_is_morphism : rmorphism (@cplx_of_R R).
Proof.
split; [|split=> //] => a b; simpc; first by rewrite subrr.
by rewrite !mulr0 !mul0r addr0 subr0.
Qed.

Canonical Structure cplx_morphism := RMorphism cplx_is_morphism.

Lemma Re_is_additive : additive (@Re R).
Proof. by case=> a1 b1; case=> a2 b2. Qed.

Canonical Structure Re_additive := Additive Re_is_additive.

Lemma Im_is_additive : additive (@Im R).
Proof. by case=> a1 b1; case=> a2 b2. Qed.

Canonical Structure Im_additive := Additive Im_is_additive.

Lemma ReiNIm : forall x : C, Re (x * 'i) = - Im x.
Proof.
by case=> a b; simpc; rewrite mulr0 mulr1 sub0r.
Qed.

Lemma ImiRe : forall x : C, Im (x * 'i) = Re x.
Proof.
by case=> a b; simpc; rewrite !mulr0 !mulr1 addr0.
Qed.

Lemma cplxI : injective (@cplx_of_R R). Proof. by move=> x y []. Qed.

Lemma poscR (x : R) : (0 <= x%:C) = (0 <= x).
Proof. by rewrite -[_ <= _]/(_ && _) eqxx. Qed.

Lemma lecE : forall x y : C, (x <= y) = (Im y == Im x) && (Re x <= Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma ltcE : forall x y : C, (x < y) = (Im y == Im x) && (Re x < Re y).
Proof. by move=> [a b] [c d]. Qed.

Lemma lecR : forall x y : R, (x%:C <= y%:C) = (x <= y).
Proof. by move=> x y; rewrite lecE /= eqxx. Qed.

Lemma ltcR : forall x y : R, (x%:C < y%:C) = (x < y).
Proof. by move=> x y; rewrite ltcE /= eqxx. Qed.

Lemma conjc_is_morphism : rmorphism (@conjc R).
Proof.
split=> [[a b] [c d]|] /=; first by simpc; rewrite opprK oppr_sub [d - _]addrC.
split=> [[a b] [c d]|] /=; first by simpc; rewrite mulrNN mulrN mulNr -oppr_add.
by rewrite oppr0 cplxr0.
Qed.

Canonical Structure conjc_morphism := RMorphism conjc_is_morphism.

Lemma conjcK : involutive (@conjc R).
Proof. by move=> [a b] /=; rewrite opprK. Qed.

Lemma mulc_conj_ge0 : forall x : C, 0 <= x * x ^*.
Proof.
move=> [a b]; simpc; rewrite !mulrN opprK [a * b]mulrC addNr cplxr0.
by rewrite lecR ler_paddr // -expr2 exprn_even_ge0.
Qed.

Lemma conjc_real : forall x : R, x^* = x.
Proof. by move=> x /=; rewrite oppr0. Qed.

Lemma Re_conj_add : forall x : C, Re x =  (x + x^*) / 2%:R :> C.
Proof.
case=> a b; simpc.
rewrite subrr !mul0r !add0r !mul0r mulrN mulr0 addr0 subr0 oppr0.
rewrite [0^+_]exprS mul0r addr0 -mulr2n -mulr_natr -mulrA.
have<-: 2%:R = 1 + 1 :> R by [].
rewrite [_ * (_ / _)]mulrA divff ?mulr1 //=.
by rewrite mulf_neq0 ?pnatr_eq0.
Qed.

Lemma Im_conj_sub : forall x : C, Im x =  (x^* - x) / 2%:R * 'i  :> C.
Proof.
case=> a b; simpc.
rewrite !(subrr,add0r,addr0,mul0r,mulr0,mulr1,mulrN,opprK,oppr0).
rewrite -oppr_add !mulNr opprK.
rewrite [0^+_]exprS mul0r addr0 -mulr2n -mulr_natr -mulrA.
have<-: 2%:R = 1 + 1 :> R by [].
rewrite [_ * (_ / _)]mulrA divff ?mulr1 //=.
by rewrite mulf_neq0 ?pnatr_eq0.
Qed.

Lemma posc_is_real : forall x : C, 0 <= x -> Im x = 0.
Proof. by move=> [a b]; rewrite lecE /=; case/andP; move/eqP<-. Qed.

(* Todo : extend theory of : *)
(*   - exprn_even_gt *)
(*   - signed exponents *)


Lemma conj_ge0 : forall x : C, (0 <= x ^*) = (0 <= x).
Proof. by move=> [a b] /=; simpc; rewrite !lecE /= oppr_eq0. Qed.

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

Section RcfDef.

Variable R : oFieldType.
Notation C := (cplx R).

Definition rcf_even := forall (p : {poly R}),
  ~~odd (size p) -> {x | p.[x] = 0}.
Definition rcf_square := forall x : R,
  {y | (0 <= y) && if 0 <= x then (y ^ 2 == x) else y == 0}.

Lemma rcf_even_sqr_from_ivt : rcf_axiom R -> rcf_even * rcf_square.
Proof.
move=> ivt.
split.
  move=> p sp.
  move: (ivt p).
  admit.
move=> x.
case: (boolP (0 <= x)) (@ivt ('X^2 - x%:P) 0 (1 + x))=> px; last first.
  by move=> _; exists 0; rewrite lerr eqxx.
case.
* by rewrite ler_paddr ?ler01.
* rewrite !horner_lin oppr_le0 px /=.
  rewrite subr_ge0 (@ler_trans _ (1 + x)) //.
    by rewrite ler_paddl ?ler01 ?lerr.
  by rewrite ler_pemulr // addrC -subr_ge0 ?addrK // subr0 ler_paddl ?ler01.
* move=> y hy; rewrite /root !horner_lin; move/eqP.
  move/(canRL (@addrNK _ _)); rewrite add0r=> <-.
by exists y; case/andP: hy=> -> _; rewrite eqxx.
Qed.

Lemma ivt_from_closed : GRing.ClosedField.axiom [ringType of C] -> rcf_axiom R.
Proof.
rewrite /GRing.ClosedField.axiom /= => hclosed.
move=> p a b hab.
Admitted.

Lemma closed_form_rcf_even_sqr : rcf_even -> rcf_square
  -> GRing.ClosedField.axiom [ringType of C].
Proof.
Admitted.

Lemma closed_form_ivt : rcf_axiom R -> GRing.ClosedField.axiom [ringType of C].
Proof.
move/rcf_even_sqr_from_ivt; case.
exact: closed_form_rcf_even_sqr.
Qed.

End RcfDef.

Require Import closed_field fintype.

Import ORing.Theory.

Section CplxClosed.

Variable R : rcfType.
Local Notation C := (cplx R).

Definition C_closedFieldAxiom := closed_form_ivt (@poly_ivt R).
Definition C_decFieldMixin := closed_fields_QEMixin C_closedFieldAxiom.
Canonical Structure C_decField := DecFieldType C C_decFieldMixin.
Canonical Structure C_closedField := ClosedFieldType C C_closedFieldAxiom.


(* This should be moved to orderedalg *)
Definition sqrtr (a : R) : R :=
  projT1 ((rcf_even_sqr_from_ivt (@poly_ivt R)).2 a).

Lemma sqrtr_ge0 : forall a : R, 0 <= sqrtr a.
Proof.
by move=> a; rewrite /sqrtr; case: (_.2 _)=> x /=; case/andP.
Qed.

Lemma sqr_sqrtr : forall a : R, 0 <= a -> (sqrtr a)^+2 = a.
Proof.
move=> a; rewrite /sqrtr; case: (_.2 _)=> x /=; case/andP=> _ HH H1.
by move: HH; rewrite H1; move/eqP.
Qed.

Lemma sqrtr_sqr : forall a : R, sqrtr (a^+2) = `|a|.
Proof.
move=> a.
have F1: 0 <= a * a.
  case: (boolP (0 <= a))=> pa; first by rewrite mulr_ge0.
  by rewrite -mulrNN mulr_ge0 // oppr_ge0 ltrW // ltrNge.
have: sqrtr (a ^+ 2) ^+2 == (`|a|) ^+ 2.
  by rewrite sqr_sqrtr exprS expr1 // exprS expr1 -absrM ger0_abs.
rewrite -subr_eq0 subr_sqr mulf_eq0; case/orP.
  by rewrite subr_eq0; move/eqP.
rewrite (paddr_eq0 (sqrtr_ge0 _) (absr_ge0 _)).
by case/andP; do 2 move/eqP->.
Qed.

Lemma sqrtr0 : sqrtr 0 = 0.
Proof.
by move: (sqrtr_sqr 0); rewrite exprS mul0r => ->; rewrite absr0.
Qed.

Lemma sqrtr1 : sqrtr 1 = 1.
Proof.
move: (sqrtr_sqr 1); rewrite exp1rn => ->.
by rewrite absr1.
Qed.

Lemma sqrtr_eq0 : forall a : R, (sqrtr a == 0) = (a <= 0).
Proof.
move=> a; rewrite /sqrtr; case: (_.2 _)=> x /=.
case/andP=> px Hp; apply/eqP/idP; last first.
  case: (0 <= a) Hp; move/eqP=> // <- HH.
  suff: x ^+ 2 == 0 by rewrite expf_eq0 /=; move/eqP.
  apply/eqP; apply: ler_anti.
  by rewrite exprn_even_ge0 // exprnP HH.
case E1: (0 <= a) Hp; last by rewrite ltrW // ltrNge E1.
by move/eqP=> <- ->; rewrite -exprnP exprS mul0r lerr.
Qed.

Lemma sqrtrM : forall a b : R, 0 <= a -> 0 <= b ->
  sqrtr (a * b) = sqrtr a * sqrtr b.
Proof.
move=> a b pa pb.
have->: a * b = (sqrtr a * sqrtr b)^+2.
  rewrite exprS expr1 mulrCA !mulrA -expr2 sqr_sqrtr //.
  by rewrite -mulrA -expr2 sqr_sqrtr.
by rewrite sqrtr_sqr ger0_abs // mulr_ge0 // sqrtr_ge0.
Qed.

Lemma eqr_sqrt : forall a b : R, 0 <= a -> 0 <= b ->
  (sqrtr a == sqrtr b) = (a == b).
Proof.
move=> a b pa pb;apply/eqP/eqP=> [HS|->] //.
by move: (sqr_sqrtr pa); rewrite HS (sqr_sqrtr pb).
Qed.

Lemma sqrtr_monotone : forall a b,
  a <= b -> sqrtr a <= sqrtr b.
Proof.
move=> a b aLb.
case: (boolP (0 <= a))=> [pa|]; last first.
  rewrite -ltrNge; move/ltrW; rewrite -sqrtr_eq0; move/eqP->.
  exact: sqrtr_ge0.
rewrite -(@ler_pexpn2r R 2) -?topredE /= ?sqrtr_ge0 //.
by rewrite !sqr_sqrtr // (ler_trans pa).
Qed.

Lemma ler_sqrt : forall a b : R, 0 <= b ->
  (sqrtr a <= sqrtr b) = (a <= b).
Proof.
move=> a b pb;apply/idP/idP=> HH; last first.
  case: (boolP (0 <= a))=> [pa|]; first by apply: sqrtr_monotone.
  rewrite -ltrNge; move/ltrW; rewrite -sqrtr_eq0; move/eqP->.
  exact: sqrtr_ge0.
case: (boolP (0 <= a))=> pa; last first.
   by apply: ler_trans pb; apply: ltrW; rewrite ltrNge.
rewrite -(sqr_sqrtr pa) -(sqr_sqrtr pb) -subr_ge0.
by rewrite subr_sqr mulr_ge0 ?subr_ge0 // ler_paddr ?sqrtr_ge0.
Qed.

Lemma ltr_sqrt : forall a b : R, 0 < b ->
  (sqrtr a < sqrtr b) = (a < b).
Proof.
move=> a b pb;apply/idP/idP=> HH; last first.
  rewrite ltr_neqAle ler_sqrt ?ltrW // andbT.
  case: (boolP (0 <= a))=> [pa|].
    by rewrite eqr_sqrt // ?ltrW // gtr_eqF //.
  rewrite -ltrNge; move/ltrW; rewrite -sqrtr_eq0; move/eqP->.
  apply/eqP=> HH1; move: (pb).
  by rewrite -(sqr_sqrtr (ltrW pb)) HH1 exprS mul0r ltrr.
move: HH; rewrite !ltrNge=> HH; apply/negP=> HH1.
by case/negP: HH; apply: sqrtr_monotone.
Qed.

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
  rewrite -sqrtr_sqr sqrtr_monotone //.
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
  rewrite [_+a]addrC -mulr_subl oppr_add addrA addrK.
  by rewrite opprK -mulr2n -mulr_natl [_*a]mulrC mulfK.
rewrite mulrCA -mulrA -mulr_addr [sqrtr _ * _]mulrC.
rewrite -mulr2n -sqrtrM // mulrAC !mulrA -subr_sqr.
rewrite sqr_sqrtr; last first.
  by rewrite ler_paddr // exprn_even_ge0.
rewrite [_^+2 + _]addrC addrK -mulrA -expr2 sqrtrM ?exprn_even_ge0 //.
rewrite !sqrtr_sqr -mulr_natr.
rewrite [`|_^-1|]ger0_abs // -mulrA [_ * _%:R]mulrC divff //.
rewrite mulr1 /u; case: (_ =P _)=>[->|].
  by rewrite  absr0 mulr0.
by rewrite mulr_sg_abs.
Qed.

Lemma sqrtc_sqrtr :
  forall (x : C), 0 <= x -> sqrtc x = cplx_of_R (sqrtr (Re x)).
Proof.
move=> [a b] /andP [/eqP->] /= a_ge0.
rewrite eqxx mul1r [0 ^+ _]exprS mul0r addr0 sqrtr_sqr.
rewrite ger0_abs // subrr mul0r sqrtr0 -mulr2n.
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

Lemma sqrtc_ge0 :  forall (x : C), (0 <= sqrtc x) = (0 <= x).
Proof.
move=> x; apply/idP/idP=> [psx|px]; last first.
  by rewrite sqrtc_sqrtr // lecR sqrtr_ge0.
by rewrite -[x]sqr_sqrtc exprS expr1 mulr_ge0.
Qed.

Lemma sqrtc_eq0 :  forall (x : C), (sqrtc x == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> [eqs|->]; last by rewrite sqrtc0.
by rewrite -[x]sqr_sqrtc eqs exprS mul0r.
Qed.

Notation R1 := (ORing.TField.sort R).

Definition normc (x : C) : R :=
  let: a +i* b := x in sqrtr (a^+2 + b^+2).

Lemma normc_ge0 : forall x, 0 <= normc x.
Proof. by case=> a b; apply: sqrtr_ge0. Qed.

Lemma normc0 : normc 0 = 0.
Proof. by rewrite /= exprS mul0r add0r sqrtr0. Qed.

Lemma normc1 : normc 1 = 1.
Proof. by rewrite /= !(mul0r,mul1r,exprS) addr0 expr0 sqrtr1. Qed.

Lemma normcE : forall x : C, (normc x: R1) = sqrtc (x * x^*) :> C.
Proof.
case=> a b; rewrite /normc; simpc.
rewrite !mulrN opprK [b * a]mulrC addNr sqrtc_sqrtr //.
by rewrite -!expr2 lecR ler_paddr // exprn_even_ge0.
Qed.

Lemma sqr_normc : forall x : C, ((normc x) ^+ 2 : R1) = x * x^* :> C.
Proof.
move=> x; move: (mulc_conj_ge0 x)=> Hx.
by rewrite !rmorphM /= normcE -expr2 sqr_sqrtc.
Qed.

Lemma normcM : multiplicative normc.
Proof.
split; last by exact: normc1.
case=> a1 b1; case=> a2 b2; simpc.
rewrite /normc -sqrtrM ?(ler_paddr,exprn_even_ge0) //.
congr sqrtr; rewrite !expr2 !(mulr_addr,mulr_addl).
rewrite -!addrA; congr (_ + _); first by rewrite mulrCA !mulrA.
do 6 rewrite addrC -!addrA; congr (_ + _).
  by rewrite mulrCA !mulrA.
do 3 rewrite addrC -!addrA; congr (_ + _).
  by rewrite mulrCA !mulrA.
rewrite !mulrN !mulNr opprK.
have->: b1 * a2 * (a1 * b2)  = a1 * a2 * (b1 * b2).
  by rewrite [b1 * _]mulrC mulrCA !mulrA.
have->: a1 * b2 * (b1 * a2)  = b1 * b2 * (a1 * a2).
  by rewrite [a1 * _]mulrC mulrCA !mulrA.
by rewrite !addrA addrK addrN add0r mulrCA !mulrA.
Qed.

Lemma normcX : forall x n, normc (x^+n) = normc x ^+ n.
Proof.
by move=> x; elim=> [|n IH]; rewrite ?(exprS,expr0) // normcM // IH.
Qed.

Lemma normc_eq0: forall x, (normc x == 0) = (x == 0).
Proof.
case=> a b /=; rewrite sqrtr_eq0.
apply/idP/and3P=>[HH|[]]; last first.
  by move/eqP->; move/eqP->; rewrite exprS mul0r add0r lerr.
split=> //.
  suff: a ^+ 2 = 0.
    by move/eqP; rewrite expf_eq0; case/andP.
  apply: ler_anti; rewrite ?(andbT,exprn_even_ge0) //.
  apply: ler_trans HH.
  by rewrite -{1}[a ^+ 2]addr0 ler_add2l exprn_even_ge0.
suff: b ^+ 2 = 0.
  by move/eqP; rewrite expf_eq0; case/andP.
apply: ler_anti; rewrite ?(andbT,exprn_even_ge0) //.
apply: ler_trans HH.
by rewrite -{1}[b ^+ 2]add0r ler_add2r exprn_even_ge0.
Qed.

Lemma normc_ge_Re : forall (x : C), `|Re x| <= normc x.
Proof.
case=> a b; rewrite -sqrtr_sqr sqrtr_monotone //.
by rewrite -{1}[a^+2]addr0 ler_add2l exprn_even_ge0.
Qed.

Lemma normcJ : forall x, normc (x^* ) = normc x.
Proof. by case=> a b; rewrite /= sqrrN. Qed.

Lemma normC_add_le : forall x y : C,  normc (x + y) <= normc x + normc y.
Proof.
move=> x y; rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?(ler_paddr,normc_ge0) //.
rewrite -lecR sqr_normc rmorphD /= mulr_addr !mulr_addl.
rewrite sqrr_add -!sqr_normc !rmorphD -!addrA /=.
rewrite ler_add2l !addrA ler_add2r -mulr2n.
suff->: y * x^* + x * y^* = cplx_of_R (Re(x * y^*)) *+2.
  rewrite ler_wmuln2r // -[normc y]normcJ -normcM.
  by rewrite lecR (ler_trans _ (normc_ge_Re _)) // -maxrN ler_maxr lerr.
rewrite addrC [y*_]mulrC Re_conj_add rmorphM /= conjcK -[_ *+ 2]mulr_natr.
by rewrite divfK // pnatr_eq0.
Qed.

Lemma invc_norm : forall x : C, x^-1 = (cplx_of_R (normc x))^-2 * x^*.
Proof.
move=> x; case: (altP (x =P 0)) => [->|dx].
  by rewrite rmorph0 mulr0 invr0.
apply: (mulIf dx).
rewrite mulrC divff // -mulrA [_^* * _]mulrC -(sqr_normc x) mulrC.
rewrite !rmorphX /= divff // expf_neq0 //.
by apply/negP; case/andP; rewrite normc_eq0 (negPf dx).
Qed.

End CplxClosed.
