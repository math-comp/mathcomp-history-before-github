Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint div orderedalg orderedzint qnum poly.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Reserved Notation "x +i y" (at level 40, left associativity, format "x  +i  y").
Reserved Notation "x -i y" (at level 40, left associativity, format "x  -i  y").

CoInductive cplx (R : oFieldType) : Type := Cplx { Re : R; Im : R }.
Coercion cplx_of_R (F : oFieldType) (x : F) := Cplx x 0.
Notation "x %:C" := (x : cplx _) 
  (at level 2, left associativity, format "x %:C")  : ring_scope.
Notation "x +i y" := (Cplx x y) : ring_scope.
Notation "x -i y" := (Cplx x (- y)) : ring_scope.
Notation "x *i" := (Cplx 0 x) (at level 8, format "x *i") : ring_scope.
Notation "''i'" := (Cplx 0 1) : ring_scope.

Module CplxEqChoice.
Section CplxEqChoice.

Variable R : oFieldType.
Notation C := (cplx R).

Definition sqR_of_cplx (x : C) := let: a +i b := x in [::a;  b].
Definition cplx_of_sqR (x : seq R) := 
  if x is [:: a; b] then Some (a +i b) else None.

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

Lemma cplxr0 : forall (R : oFieldType) (x : R), x +i 0 = x. Proof. by []. Qed.

Module CplxField.
Section CplxField.

Variable R : oFieldType.
Local Notation C := (cplx R).
Local Notation C0 := ((0 : R)%:C).
Local Notation C1 := ((1 : R)%:C).

Definition addc (x y : C) := let: a +i b := x in let: c +i d := y in 
  (a + c) +i (b + d).
Definition oppc (x : C) := let: a +i b := x in (- a) +i (- b).

Lemma addcC : commutative addc.
Proof. by move=> [a b] [c d] /=; congr (_ +i _); rewrite addrC. Qed.
Lemma addcA : associative addc.
Proof. by move=> [a b] [c d] [e f] /=; rewrite !addrA. Qed.

Lemma add0c : left_id C0 addc.
Proof. by move=> [a b] /=; rewrite !add0r. Qed.

Lemma addNc : left_inverse C0 oppc addc.
Proof. by move=> [a b] /=; rewrite !addNr. Qed.

Definition cplx_ZmodMixin := ZmodMixin addcA addcC add0c addNc.
Canonical Structure cplx_ZmodType := ZmodType C cplx_ZmodMixin.

Definition mulc (x y : C) := let: a +i b := x in let: c +i d := y in 
  ((a * c) - (b * d)) +i ((a * d) + (b * c)).

Lemma mulcC : commutative mulc.
Proof. 
move=> [a b] [c d] /=.
by rewrite [c * b + _]addrC ![_ * c]mulrC ![_ * d]mulrC.
Qed.

Lemma mulcA : associative mulc.
Proof.
move=> [a b] [c d] [e f] /=.
rewrite !mulr_addr !mulr_addl !mulrN !mulNr !mulrA !oppr_add -!addrA.
by congr ((_ + _) +i (_ + _)); rewrite !addrA addrAC;
  congr (_ + _); rewrite addrC.
Qed.

Definition invc (x : C) := let: a +i b := x in let n2 := (a ^+ 2 + b ^+ 2) in
  (a / n2) -i (b / n2).

Lemma mul1c : left_id C1 mulc.
Proof. by move=> [a b] /=; rewrite !mul1r !mul0r subr0 addr0. Qed.

Lemma mulc_addl : left_distributive mulc addc.
Proof.
move=> [a b] [c d] [e f] /=; rewrite !mulr_addl !oppr_add -!addrA.
by congr ((_ + _) +i (_ + _)); rewrite addrCA.
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
by rewrite addr_eq0 ?mulf_eq0 ?orbb // -expr2 exprn_even_ge0.
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

Definition posc (x : C) := let: a +i b := x in (b == 0) && (posr a).

Lemma posc0 : posc 0. Proof. by rewrite /= eqxx /= posr0. Qed.

Lemma posc_add : forall x y, posc x -> posc y -> posc (addc x y).
Proof.
move=> [a b] [c d]; case/andP; move/eqP=> -> pa; case/andP; move/eqP=> -> pc.
by rewrite /= addr0 eqxx posr_add.
Qed.

Lemma posc_mul : forall x y, posc x -> posc y -> posc (mulc x y).
Proof.
move=> [a b] [c d]; case/andP; move/eqP=> -> pa; case/andP; move/eqP=> -> pc.
by rewrite /= !mulr0 mul0r addr0 subr0 eqxx posr_mul.
Qed.

Lemma posc_anti : forall x, posc x -> posc (oppc x) -> x = 0.
Proof.
move=> [a b]; case/andP; move/eqP=> -> pa /=; rewrite oppr0 eqxx /= cplxr0.
move=> pNa; apply/eqP; rewrite eq_cplx /= eqxx andbT.
by rewrite eqr_le !lter_pos subr0 sub0r; apply/andP.
Qed.

Lemma posc1 : posc C1. Proof. by rewrite /= eqxx posr_ge0 ler01. Qed.

Lemma poscM : forall x : R, posc x = posr x.
Proof. by move=> x; rewrite /= eqxx. Qed.

Definition cplx_POrderedMixin := PartialOrderMixin posc0
  posc_add posc_mul posc_anti.
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

Definition conjc (R : oFieldType) (x : cplx R) := let: a +i b := x in a -i b.
Notation "x ^*" := (conjc x) (at level 2, format "x ^*").

Ltac simpc := do ?
  [ rewrite -[(_ +i _) - (_ +i _)]/(_ +i _)
  | rewrite -[(_ +i _) + (_ +i _)]/(_ +i _)
  | rewrite -[(_ +i _) * (_ +i _)]/(_ +i _)
  | rewrite -[(posr (_ +i _))]/(_ && _)].

Section CplxTheory.

Variable R : oFieldType.
Notation C := (cplx R).

Lemma cplxI : injective (@cplx_of_R R). Proof. by move=> x y []. Qed.

Lemma poscM : forall x : R, posr (x%:C) = posr x.
Proof. exact: CplxField.poscM. Qed.

Lemma lecE : forall x y : C, (x <= y) = (Im x == Im y) && (Re x <= Re y).
Proof. 
by move=> [a b] [c d] /=; rewrite !lter_pos; simpc; rewrite subr_eq0 eq_sym.
Qed.

Lemma ltcE : forall x y : C, (x < y) = (Im x == Im y) && (Re x < Re y).
Proof.
move=> [a b] [c d] /=; rewrite !lter_pos eq_cplx /=; simpc.
by rewrite subr_eq0 [d == _]eq_sym; case: (b == d); rewrite !(andbT, andbF).
Qed.

Lemma lecM : forall x y : R, (x%:C <= y%:C) = (x <= y).
Proof. by move=> x y; rewrite lecE /= eqxx. Qed.

Lemma ltcM : forall x y : R, (x%:C < y%:C) = (x < y).
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
by rewrite lecM addr_ge0 // -expr2 exprn_even_ge0.
Qed.

Lemma conjc_real : forall x : R, x^* = x.
Proof. by move=> x /=; rewrite oppr0. Qed.

Lemma posc1 : posr (1 : C).
Proof. exact: CplxField.posc1. Qed.

Lemma lec01 : 0 <= 1 :> C.
Proof. by rewrite -posr_ge0 posc1. Qed.

Lemma ltc01 : 0 < 1 :> C.
Proof. by rewrite ltr_neqAle lec01 eq_sym oner_eq0. Qed.

Lemma posc_is_real : forall x : C, 0 <= x -> Im x = 0.
Proof. by move=> [a b]; rewrite lecE /=; case/andP; move/eqP<-. Qed.

Lemma invc_ge0 : forall x : C, (0 <= x^-1) = (0 <= x).
Proof.
move=> [a b]; rewrite !lecE /= ![0 == _]eq_sym.
rewrite -mulNr mulf_eq0 invr_eq0 addr_eq0 ?exprn_even_ge0 //.
rewrite !expf_eq0 /= eqr_oppC oppr0 andKb; apply: andb_id2l.
move/eqP->; rewrite [0 ^+ _]mulr0 addr0.
case: (0 <= a) (a < 0) / (lerP 0 a) => ha.
  by rewrite mulr_ge0 // invr_ge0 exprSn_ge0.
by rewrite lerNgt mulr_lt0_gt0 // invr_gt0 mulr_lt0.
Qed.
(* Todo : extend theory of : *)
(*   - exprn_even_gt *)
(*   - signed exponents *)

Definition ltec01 := (lec01, ltc01).

Lemma ltc0Sn : forall n, 0 < (n.+1)%:~R :> C.
Proof.
elim=> [|n ihn]; first by rewrite ltc01.
by rewrite (ltr_le_trans ihn) // [n.+2%:Z]zintS mulrz_addl cpr_add lec01.
Qed.

Lemma lec0n : forall n : nat, 0 <= n%:~R :> C.
Proof. by move=> [|n]; rewrite ?mul0zr ?lerr // ltrW // ltc0Sn. Qed.

Lemma mulSn1c_eq0 : forall n, n.+1%:~R == 0 :> C = false.
Proof. by move=> n; rewrite eq_sym ltrE ?ltc0Sn. Qed.

Lemma ltc0n : forall n : nat, (0 < n%:~R :> C) = (n%:~R != 0 :> C).
Proof. by case=> *; rewrite ?(mulr0z, ltrr, eqxx, ltc0Sn, mulSn1c_eq0). Qed.

Definition ltec0n := (ltc0Sn, lec0n, mulSn1c_eq0, ltc0n).

Lemma Cchar : [char C] =i pred0.
Proof. by case=> // p; rewrite !inE mulSn1c_eq0 andbF. Qed.

Lemma mulz1c_eq0 : forall n, (n%:~R == 0 :> C) = (n == 0).
Proof. 
by elim=> [|n _|n _]; rewrite ?mulr0z ?eqxx// ?oppr_eq0 mulSn1c_eq0.
Qed.

Lemma mulz1cI : injective ( *~%R (1 : C)).
Proof.
move=> m n; move/eqP; rewrite -subr_eq0 -mulrz_subr.
by rewrite mulz1c_eq0 subr_eq0; move/eqP.
Qed.

Lemma mulzc_eq0 : forall (x : C) n, x *~ n == 0 = ((x == 0) || (n == 0)).
Proof. by move=> x n; rewrite -mulrzr mulf_eq0 mulz1c_eq0. Qed.

Lemma mulzc_neq0 : forall (x : C) n, x *~ n != 0 = ((x != 0) && (n != 0)).
Proof. by move=> x n; rewrite mulzc_eq0 negb_or. Qed.

Lemma expcn_eq1 : forall (x : C) n, 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof.
move=> x n hx; rewrite expfS_eq1; case: (x == 1)=> //=.
rewrite eq_sym ltrWN // (@ltr_le_trans _ 1) ?ltc01 //.
elim: n=> [|n ihn]; first by rewrite big_ord_recl big_ord0 addr0 lerr.
by rewrite big_ord_recr /= addrC ger0_ler_add // exprSn_ge0.
Qed.

Lemma posr_conj : forall x : C, posr (x ^*) = posr x.
Proof. by move=> [a b] /=; simpc; rewrite eqr_oppC oppr0. Qed.

Lemma conj_ge0 : forall x : C, (0 <= x ^*) = (0 <= x).
Proof. by move=> x; rewrite -!posr_ge0 posr_conj. Qed.

Lemma conjc_nat : forall n, (n%:R : C)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjc0 : (0 : C) ^* = 0.
Proof. exact: (conjc_nat 0). Qed.

Lemma conjc1 : (1 : C) ^* = 1.
Proof. exact: (conjc_nat 1). Qed.

Lemma conjc_eq0 : forall x : C, (x ^* == 0) = (x == 0).
Proof. by move=> [a b]; rewrite !eq_cplx /= eqr_oppC oppr0. Qed.

Lemma lec_pmull: forall x y : C, 0 < x -> 0 <= x * y = (0 <= y).
move=> [a b] [c d] /=; simpc; rewrite !lecE !ltcE /=.
case/andP; move/eqP<-=> ha; rewrite !mul0r addr0 subr0.
rewrite eq_sym mulf_eq0 ltrNW //= [0 == _]eq_sym; apply: andb_id2l=> _.
(* Todo : add this kind of lemma to orderedalg *)
case: (0 <= c) (c < 0) / (lerP 0 c) => hc; first by rewrite mulr_ge0 // ltrW.
by rewrite lerNgt mulr_gt0_lt0.
Qed.

Lemma posc_sum_eq0: 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> 0 <= F i) ->
   \sum_(j <- r | P j) F j = 0 ->
   (forall i, i \in r -> P i -> F i = 0).
Proof.
move=> I r P F HN; elim: r=> [|y r Hrec] //.
rewrite big_cons; case HP: (P _)=> Hs; last first.
  move=> i Hi Hp; apply: Hrec=> //.
  move: Hi; rewrite in_cons; case/orP=> //.
  by move/eqP=>Hi; case/negP: HP; rewrite -Hi.
move=> i Hi HP1.
move/eqP: Hs; rewrite addr_eq0 ?HN //.
  case/andP; move: Hi; rewrite in_cons; case/orP; first by do 2 move/eqP->.
  by move=> Hin _; move/eqP=> Hs; exact: Hrec.
rewrite big_mkcond /= sumr_ge0 //.
move=> j; case: ifP; first exact: HN.
by rewrite lerr.
Qed.
(* by apply: sumr_ge0. <= Todo : modify sumr_ge0, it's too weak for now *)

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
* by rewrite ger0_ler_add ?ler01.
* rewrite !horner_lin oppr_le0 px /=.
  rewrite subr_ge0 (@ler_trans _ (1 + x)) //.
    by rewrite ger0_ler_add ?ler01 ?lerr.
  rewrite ler_epmulr //.
    by rewrite addrC ger0_ler_add ?lerr.
  by rewrite ger0_ler_add ?ler01.
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

Import OrderedRing.Theory.

Section CplxClosed.

Variable R : rcfType.
Local Notation C := (cplx R).

Definition C_closedFieldAxiom := closed_form_ivt (@poly_ivt R).
Definition C_QEmixin := closed_fields_QEMixin C_closedFieldAxiom.
Canonical Structure C_QE :=  @GRing.QE.pack C _ C_QEmixin _ _ id _ id.
Definition C_DecFieldMixin := (GRing.QEDecidableFieldMixin C_QE).
Canonical Structure C_DecField := DecFieldType C C_DecFieldMixin.
Canonical Structure C_closedField := ClosedFieldType C C_closedFieldAxiom.


(* This should be moved to orderedalg *)
Definition sqrtr (a : R) : R := 
  projT1 ((rcf_even_sqr_from_ivt (@poly_ivt R)).2 a).

Lemma sqrtr_ge0: forall a : R, 0 <= sqrtr a.
Proof.
by move=> a; rewrite /sqrtr; case: (_.2 _)=> x /=; case/andP.
Qed.

Lemma sqr_sqrtrE: forall a : R, 0 <= a -> (sqrtr a)^+2 = a.
Proof.
move=> a; rewrite /sqrtr; case: (_.2 _)=> x /=; case/andP=> _ HH H1.
by move: HH; rewrite H1; move/eqP.
Qed.

Lemma sqrtr_sqr: forall a : R, sqrtr (a^+2) = `|a|.
Proof.
move=> a.
have F1: 0 <= a * a.
  case: (boolP (0 <= a))=> pa; first by rewrite mulr_ge0.
  by rewrite -mulrNN mulr_ge0 // oppr_ge0 ltrW // ltrNge.
have: sqrtr (a ^+ 2) ^+2 == (`|a|) ^+ 2.
  by rewrite sqr_sqrtrE exprS expr1 // exprS expr1 -absr_mul ger0_abs.
rewrite -subr_eq0 subr_sqr mulf_eq0; case/orP.
  by rewrite subr_eq0; move/eqP.
rewrite (addr_eq0 (sqrtr_ge0 _) (absr_ge0 _)).
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

Lemma sqrtr_negE: forall a : R, a < 0 -> sqrtr a = 0.
Proof.
move=> a; rewrite /sqrtr; case: (_.2 _)=> x /=; case/andP=> _ HH H1.
by move: HH; rewrite lerNgt H1; move/eqP.
Qed.

Lemma sqrtrM: forall a b : R, 0 <= a -> 0 <= b ->
  sqrtr (a * b) = sqrtr a * sqrtr b.
Proof.
move=> a b pa pb.
have->: a * b = (sqrtr a * sqrtr b)^+2.
  rewrite exprS expr1 mulrCA !mulrA -expr2 sqr_sqrtrE //.
  by rewrite -mulrA -expr2 sqr_sqrtrE.
by rewrite sqrtr_sqr ger0_abs // mulr_ge0 // sqrtr_ge0.
Qed.

Lemma sqrtr_monotone: forall a b : R, 
  a <= b -> sqrtr a <= sqrtr b.
Proof.
move=> a b aLb.
case: (boolP (0 <= a))=> pa; last first.
  by rewrite sqrtr_negE ?ltrNge // sqrtr_ge0.
by rewrite -(ler_pexp2 1) ?sqrtr_ge0 // !sqr_sqrtrE // (ler_trans pa).
Qed.

Definition sqrtc (x : C) : C := 
  let: a +i b := x in
  let sgr1 b := if b == 0 then 1 else sgr b in
  let r := sqrtr (a^+2 + b^+2) in
  (sqrtr ((r + a)/2%:R)) +i (sqrtr ((r - a)/2%:R) *~ sgr1 b).

Lemma sqr_sqrtc : forall x, (sqrtc x) ^+ 2 = x.
Proof.
have sqr: forall x : R, x ^+ 2 = x * x.
  by move=> x; rewrite exprS expr1.
case=> a b; rewrite exprS expr1; simpc.
have F0: 2%:R != 0 :> R.
  by rewrite (mulSn1r_eq0 _ 1%N).
have F1: 0 <= 2%:R^-1 :> R.
  by rewrite invr_ge0 (@ler_nat _ 0%N).
have F2: `|a| <= sqrtr (a^+2 + b^+2).
  rewrite -sqrtr_sqr sqrtr_monotone //.
  by rewrite addrC -subr_ge0 addrK exprn_even_ge0.
have F3: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) - a) / 2%:R.
  rewrite mulr_ge0 // subr_ge0 (ler_trans _ F2) //.
  by rewrite -(maxrN a) ler_maxr lerr.
have F4: 0 <= (sqrtr (a ^+ 2 + b ^+ 2) + a) / 2%:R.
  rewrite mulr_ge0 // -{2}[a]opprK subr_ge0 (ler_trans _ F2) //.
  by rewrite -(maxrN a) ler_maxr lerr orbT.
congr (_ +i _);  set u := if _ then _ else _.
  rewrite mulrzAl mulrzAr -mulrzA.
  have->: (u * u) = 1.
    rewrite /u; case: (_ =P _); rewrite ?mul1r //.
    by move/eqP=> HH; rewrite mul_neq0ss. 
  rewrite mulr1z -!sqr !sqr_sqrtrE //.
  rewrite [_+a]addrC -mulr_subl oppr_add addrA addrK.
  by rewrite opprK -mulr2n -mulr_natl [_*a]mulrC mulfK.
rewrite mulrzAl mulrzAr -mulrz_addr [sqrtr _ * _]mulrC.
rewrite -mulr2n -sqrtrM // mulrAC !mulrA -subr_sqr.
rewrite sqr_sqrtrE; last first.
  by rewrite addr_ge0 // exprn_even_ge0.
rewrite [_^+2 + _]addrC addrK -mulrA -expr2 sqrtrM ?exprn_even_ge0 //.
rewrite !sqrtr_sqr -mulr_natr.
rewrite [`|_^-1|]ger0_abs // -mulrA [_ * _%:R]mulrC divff //.
rewrite mulr1 /u; case: (_ =P _)=>[->|].
  by rewrite  absr0 mul0rz.
by rewrite -absr_sgP.
Qed.

Lemma sqrtc_sqrtr : 
  forall (x : C), 0 <= x -> sqrtc x = (cplx_of_R (sqrtr (Re x))).
Proof.
move=> [a b]; case/andP; rewrite !subr0 posr_ge0 /sqrtc.
move/eqP=> -> zLa.
rewrite eqxx mulr1z [0^+_]exprS mul0r addr0 sqrtr_sqr ger0_abs //.
rewrite subrr mul0r sqrtr0 -mulr2n -[_*+2]mulr_natr mulfK //.
by rewrite (mulSn1r_eq0 _ 1%N).
Qed.

Lemma sqrtc0 : sqrtc 0 = 0.
Proof. by rewrite sqrtc_sqrtr ?lerr // sqrtr0. Qed.

Lemma sqrtc1 : sqrtc 1 = 1.
Proof. by rewrite sqrtc_sqrtr ?lec01 // sqrtr1. Qed.

Lemma sqrtN1 : sqrtc (-1) = 'i.
Proof. 
rewrite /sqrtc /= oppr0 eqxx [0^+_]exprS mulr0 addr0.
rewrite exprS expr1 mulN1r opprK sqrtr1 subrr mul0r sqrtr0.
rewrite mulr1z -mulr2n divff ?sqrtr1 //.
by rewrite (mulSn1r_eq0 _ 1%N).
Qed.

(* we should do better and get the equivalence *)
Lemma sqrtc_ge0 :  forall (x : C), 0 <= x -> 0 <= sqrtc x.
Proof. by move=> x px; rewrite sqrtc_sqrtr // lecM sqrtr_ge0. Qed.

(* Which one will be good ? *)
(* Definition normc (x : C) := Re (sqrt (x * x^* )). *)
(* Definition normc (x : C) : R := sqrt (Re (x * x^* )). *)

(* Lemma normcE : forall x, (normc x) ^+ 2 = x * x^* :> C. *)
(* Proof.  *)
(* by move=> [a b]; rewrite /normc /=; simpc; rewrite !mulrN [a * b]mulrC addNr. *)
(* Qed. *)
(* (* *)
(* Hypothesis normC_add: forall x y, *)
(*   normC (x + y) <= normC x + normC y +  2%:R * (normC x * normC y). *)
(* *) *)

(* Lemma normc_ge0 : forall x, 0 <= normc x. *)
(* Proof. by move=> x; rewrite -lecM normcE mulc_conj_ge0. Qed. *)

(* Lemma normc0 : normc 0 = 0. Proof. by rewrite /normc mul0r. Qed. *)

(* Lemma normc1 : normc 1 = 1. Proof. by rewrite /normc mul1r. Qed. *)


(* Lemma normc_mul :  {morph normc: x y / x * y}. *)
(* Proof. *)
(* move=> x y /=; apply: cplxI; rewrite !normcE. *)
(* rewrite rmorphM -!mulrA /=. congr (_ * _)). *)
(* by rewrite mulrc -!mulrA [y * _]mulrC. *)
(* Qed. *)

(* Lemma normc_exp : forall x n, normc (x^+n) = normc x ^+ n. *)
(* Proof. *)
(* move=> x; elim=> [|n IH]; first by rewrite !expr0 normc1. *)
(* by rewrite exprS normc_mul IH exprS. *)
(* Qed. *)

(* Lemma normc_conj: forall x, normc (x^* ) = normc x. *)
(* Proof. by move=> x; rewrite /normc conjcK mulrC. Qed. *)

(* Lemma normc_inv : forall x, x^-1 = (normc x)^-1 * x^*. *)
(* Proof. *)
(* move=> x; case: (x =P 0)=> [->|]. *)
(*   by rewrite conjc0 mulr0 invr0. *)
(* move/eqP=> Hx. *)
(* rewrite /normc invr_mul ?(GRing.unitfE,conjC_eq0) //. *)
(* by rewrite mulrC mulrA GRing.mulrV ?(GRing.unitfE,conjc_eq0) // div1r. *)
(* Qed. *)

(* Lemma normc_eq0: forall x, (normc x == 0) = (x == 0). *)
(* Proof. *)
(* move=> x; apply/eqP/eqP=> Hp; last first. *)
(*   by rewrite Hp normc0. *)
(* by apply/eqP; rewrite -invr_eq0 normc_inv Hp invr0 mul0r. *)
(* Qed. *)

End CplxClosed.
