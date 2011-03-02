Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint div orderedalg orderedzint qnum.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Defensive.

Open Scope ring_scope.

(* Some axioms to start with *)
Parameter C : Type. 

Parameter C_eqMixin : Equality.mixin_of C.
Canonical Structure C_eqType := EqType C C_eqMixin.
Parameter C_choiceMixin : Choice.mixin_of (seq (seq C)).
Canonical Structure C_choiceType := ChoiceType C C_choiceMixin.
Parameter C_ZmodMixin : GRing.Zmodule.mixin_of C.
Canonical Structure C_ZmodType := ZmodType C C_ZmodMixin.
Parameter C_ringMixin : GRing.Ring.mixin_of [zmodType of C].
Canonical Structure C_Ring := Eval hnf in RingType C C_ringMixin.
Parameter C_mulC : @commutative C _ ( *%R).
Canonical Structure C_comRing := Eval hnf in ComRingType C C_mulC.
Parameter C_UnitMixin : GRing.UnitRing.mixin_of [ringType of C].
Canonical Structure C_unitRing := Eval hnf in UnitRingType C C_UnitMixin.
Canonical Structure C_comUnitRing := Eval hnf in [comUnitRingType of C].
Parameter C_field_axiom : GRing.Field.mixin_of [unitRingType of C].
Canonical Structure C_iDomain :=
  Eval hnf in IdomainType C (FieldIdomainMixin C_field_axiom).
Canonical Structure C_fieldType := FieldType C C_field_axiom.
Parameter C_POrderedMixin : OrderedRing.PartialOrder.mixin_of [ringType of C].
Canonical Structure C_poIdomainType := POIdomainType C C_POrderedMixin.
Canonical Structure C_poFieldType := POFieldType C C_POrderedMixin.
Parameter C_DecidableField : GRing.DecidableField.mixin_of [unitRingType of C].
Canonical Structure C_DecidableType := DecFieldType C C_DecidableField.
Parameter C_ClosedFieldMixin : GRing.ClosedField.axiom [ringType of C].
Canonical Structure C_ClosedField :=  ClosedFieldType C C_ClosedFieldMixin.

Variable conjC : {rmorphism C -> C}.
Notation "x ^*" := (conjC x) (at level 2, format "x ^*").
Hypothesis conjCK : involutive conjC.

Hypothesis posr_pconj : forall x, posr (x * x ^*).
Hypothesis posr_conjI : forall x, posr x -> x^* = x.

Hypothesis posC1 : posr (1 : C).
Hypothesis posr_inv : forall x : C, posr x^-1 = posr x.

Section C_Theory.

Implicit Types x y z : C.

Lemma leC01 : 0 <= 1 :> C.
Proof. by rewrite ler_pos subr0 posC1. Qed.

Lemma ltC01 : 0 < 1 :> C.
Proof. by rewrite ltr_neqAle eq_sym oner_eq0 leC01. Qed.

Definition lteC01 := (leC01, ltC01).

Lemma ltC0Sn : forall n, 0 < (n.+1)%:zR :> C.
Proof.
elim=> [|n ihn]; first by rewrite ltC01.
by rewrite (ltr_le_trans ihn) // [n.+2%:Z]zintS mulzr_addl cpr_add leC01.
Qed.

Lemma leC0n : forall n : nat, 0 <= n%:zR :> C.
Proof. by move=> [|n]; rewrite ?mul0zr ?lerr // ltrW // ltC0Sn. Qed.

Lemma mulSn1C_eq0 : forall n, n.+1%:zR == 0 :> C = false.
Proof. by move=> n; rewrite eq_sym ltrE ?ltC0Sn. Qed.

Lemma ltC0n : forall n : nat, (0 < n%:zR :> C) = (n%:zR != 0 :> C).
Proof. by case=> *; rewrite ?(mul0zr, ltrr, eqxx, ltC0Sn, mulSn1C_eq0). Qed.

Definition lteC0n := (ltC0Sn, leC0n, mulSn1C_eq0, ltC0n).

Lemma Cchar : [char C] =i pred0.
Proof. by case=> // p; rewrite !inE mulSn1C_eq0 andbF. Qed.

Lemma mulz1C_eq0 : forall n, (n%:zR == 0 :> C) = (n == 0).
Proof. 
by elim=> [|n _|n _]; rewrite ?mulr0z ?eqxx// ?mulNzr ?oppr_eq0 mulSn1C_eq0.
Qed.

Lemma mulz1CI : injective ( *~%R (1 : C)).
Proof.
move=> m n; move/eqP; rewrite -subr_eq0 -mulzr_subl.
by rewrite mulz1C_eq0 subr_eq0; move/eqP.
Qed.

Lemma mulzC_eq0 : forall x n, n *~ x == 0 = ((x == 0) || (n == 0)).
Proof. by move=> x n; rewrite -mulzrr mulf_eq0 mulz1C_eq0. Qed.

Lemma mulzC_neq0 : forall x n, n *~ x != 0 = ((x != 0) && (n != 0)).
Proof. by move=> x n; rewrite mulzC_eq0 negb_or. Qed.

Lemma expCn_eq1 : forall x n, 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof.
move=> x n hx; rewrite expfS_eq1; case: (x == 1)=> //=.
rewrite eq_sym ltrWN // (@ltr_le_trans _ 1) ?ltC01 //.
elim: n=> [|n ihn]; first by rewrite big_ord_recl big_ord0 addr0 lerr.
by rewrite big_ord_recr /= addrC ger0_ler_add // exprSn_ge0.
Qed.

Lemma pconj_gt0 : forall x, 0 <= (x * x ^*).
Proof. by move=> x; rewrite -posr_ge0 posr_pconj. Qed.

Lemma conjIE : forall x, 0 <= x -> x^* = x.
Proof. by move=> x px; rewrite posr_conjI ?posr_ge0. Qed.

Lemma invr_ge0 : forall x, (0 <= x^-1) = (0 <= x).
Proof. by move=> x; rewrite -!posr_ge0 posr_inv. Qed.

Lemma posr_conj : forall x, posr (x ^*) = posr x.
Proof.
by move=>x; apply/idP/idP=>Hp; first rewrite -[x]conjCK; 
   rewrite (posr_conjI Hp).
Qed.

Lemma conj_ge0 : forall x, (0 <= x ^*) = (0 <= x).
Proof. by move=> x; rewrite -!posr_ge0 posr_conj. Qed.

Lemma conjC_nat : forall n, (n%:R)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjC0 : 0 ^* = 0.
Proof. exact: (conjC_nat 0). Qed.

Lemma conjC1 : 1 ^* = 1.
Proof. exact: (conjC_nat 1). Qed.

Lemma conjC_eq0 : forall x, (x ^* == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> H; last by rewrite H (conjC_nat 0).
by rewrite -[x]conjCK H (conjC_nat 0).
Qed.

Lemma leC_pmull: forall x y, 0 < x -> 0 <= x * y = (0 <= y).
Proof. Admitted.

Lemma posC_sum_eq0: 
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
admit.
(* by apply: sumr_ge0. <= Todo : modify sumr_ge0, it's too weak for now *)
Qed.

Definition normC x := x * x^*.

(*
Hypothesis normC_add: forall x y,
  normC (x + y) <= normC x + normC y +  2%:R * (normC x * normC y).
*)

Lemma normC_ge0 : forall x, 0 <= normC x.
Proof. by move=> x; rewrite pconj_gt0. Qed.

Lemma normC0 : normC 0 = 0.
Proof.  exact: mul0r. Qed.

Lemma normC1 : normC 1 = 1.
Proof.  by rewrite /normC mul1r conjC1. Qed.

Lemma normC_mul :  {morph normC: x y / x * y}.
Proof.
move=> x y; rewrite /normC rmorphM -!mulrA; congr (_ * _).
by rewrite mulrC -!mulrA [y * _]mulrC.
Qed.

Lemma normC_exp : forall x n, normC (x^+n) = normC x ^+ n.
Proof.
move=> x; elim=> [|n IH]; first by rewrite !expr0 normC1.
by rewrite exprS normC_mul IH exprS.
Qed.

Lemma normC_conj: forall x, normC (x^*) = normC x.
Proof. by move=> x; rewrite /normC conjCK mulrC. Qed.

Lemma normC_inv : forall x, x^-1 = (normC x)^-1 * x^*.
Proof.
move=> x; case: (x =P 0)=> [->|].
  by rewrite conjC0 mulr0 invr0.
move/eqP=> Hx.
rewrite /normC invr_mul ?(GRing.unitfE,conjC_eq0) //.
by rewrite mulrC mulrA GRing.mulrV ?(GRing.unitfE,conjC_eq0) // div1r.
Qed.

Lemma normC_eq0: forall x, (normC x == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp normC0.
by apply/eqP; rewrite -invr_eq0 normC_inv Hp invr0 mul0r.
Qed.

Lemma conjC_inv: forall x, (x^-1)^* = (x^*)^-1.
Proof.
move=> x; rewrite normC_inv rmorphM conjCK.
rewrite (normC_inv x^*) conjCK; congr (_ * _).
rewrite normC_conj; apply: conjIE.
rewrite invr_ge0; exact: normC_ge0.
Qed.

(* to ne continued ... *)

End C_Theory.