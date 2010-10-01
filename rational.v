(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice tuple.
Require Import bigop ssralg.

Require Import generic_quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section EquivProps.

Lemma left_trans : forall T0 (e:rel T0),
  symmetric e -> transitive e -> left_transitive e.
Proof.
move=> T0 e sym tr x y exy z; apply/idP/idP; last do [move/tr:exy; exact].
move:exy; rewrite sym; move/tr; exact.
Qed.

End EquivProps.


Section ChoiceTheoryExt.

Variable T : choiceType.
Implicit Types P Q : pred T.

Lemma choosePn : forall P x0, P x0 = false -> choose P x0 = x0.
Proof. by move=> P x0 Px0; rewrite /choose insubF. Qed.

Check eq_choose.
Check choose_id.

Lemma eq_choose_id : forall P Q x y,
  P =1 Q -> P x -> Q y -> choose P x = choose Q y.
Proof.
move=> P Q x y eQP; rewrite eQP => Qx Qy;
have ->: choose P x = choose Q x; [exact: eq_choose | exact: choose_id].
Qed.


End ChoiceTheoryExt.

Import GRing.Theory.
Open Local Scope ring_scope.

Module Rational.
Variable R : idomainType.

Definition indom (x : {csquare R}) := (x.2 != 0).
Definition dom := { x | indom x }.
Definition Dom := @Sub _ _ [subType of dom].
Definition Domd := @insubd _ _ [subType of dom].
Definition domP := @valP _ _ [subType of dom].
Definition DomdP := @insubP _ _ [subType of dom].

Notation "'\n_' x"  := (sval x).1
  (at level 8, x at level 2, format "'\n_' x").
Notation "'\d_' x"  :=
  (sval x).2 (at level 8, x at level 2, format "'\d_' x").

Lemma PDom_prop : forall x y, y != 0 -> indom (x, y).
Proof. exact. Qed.
Definition PDom x y (Py : y != 0) := Dom (PDom_prop x Py).

Definition equivq (x y : dom) := \n_x * \d_y == \d_x * \n_y.

Lemma equivq_refl : reflexive equivq.
Proof. by move=> x; rewrite /equivq mulrC. Qed.

Lemma equivq_sym : symmetric equivq.
Proof. by move=> x y; rewrite /equivq eq_sym; congr (_==_); rewrite mulrC. Qed.

Lemma equivq_trans : transitive equivq.
Proof.
move=> [x Px] [y Py] [z Pz]. rewrite /equivq /=.
rewrite mulrC. move/eqP=>exy. move/eqP=>eyz.
rewrite -(inj_eq (mulfI Px)) mulrA exy -mulrA eyz.
by rewrite !mulrA [_.2 * _]mulrC.
Qed.

Definition equivq_ltrans := left_trans equivq_sym equivq_trans.

Definition canon x := choose (equivq x) x.
Lemma canon_id : forall x, canon (canon x) = canon x.
Proof.
move=> x. rewrite /canon; apply: eq_choose_id; rewrite ?equivq_refl //.
by apply: equivq_ltrans; rewrite equivq_sym chooseP // equivq_refl.
Qed.


Definition axiom (x : dom) := canon x == x.
Definition rational := { x | axiom x }.
Definition Rational := @Sub _ _ [subType of rational].


Lemma canon_rat_axiom : forall x:dom, axiom (canon x).
Proof. by move=> x; rewrite /axiom canon_id. Qed.

Definition canon_rat (x:dom) := @Rational (canon x) (canon_rat_axiom x).


Lemma canon_rat_valK : forall x:rational, canon_rat (val x)  = x.
Proof.
by move=> [x /=]; rewrite /axiom=> Px; apply:val_inj=>/=; rewrite (eqP Px).
Qed.

Canonical Structure rational_quotType := Eval hnf in
  @QuotType _ rational [eta val] [eta canon_rat] canon_rat_valK.


Definition ratW := @quotW _ rational_quotType.
Definition ratP := @quotP _ rational_quotType.
Definition inRatP := insubP [subType of rational].

Notation zeroq := (\pi_rational (PDom 0 (nonzero1r _))).
Notation oneq := (\pi_rational (PDom 1 (nonzero1r _))).
Notation rat x := (\pi_rational (PDom x (nonzero1r _))).
Notation rat_inv px := (\pi_rational (PDom 1 px)).


Lemma equivqP : forall x y, x == y mod rational = equivq x y.
Proof.
move=> x y. rewrite -(inj_eq val_inj) /= /canon.
apply/eqP/idP => Hxy.
   apply: (@equivq_trans (choose (equivq x) x));
   last rewrite Hxy equivq_sym; by rewrite chooseP // equivq_refl.
apply: eq_choose_id; rewrite ?equivq_refl //.
exact: equivq_ltrans.
Qed.

Lemma mul_dom : forall x y : dom, \d_x * \d_y != 0.
Proof. move=> x y. rewrite mulf_neq0 //; apply:domP. Qed.

Lemma addq_compat : \compat2_rational _
  (fun x y => \pi_rational
    (PDom (\n_x*\d_y + \n_y*\d_x) (mul_dom x y) )
  ).
Proof.
apply:compat2Epi=> x y x' y'.
rewrite !equivqP /equivq /=. move/eqP=>Px. move/eqP=>Py.
apply/eqP. rewrite mulr_addl mulr_addr. congr (_+_).
   by rewrite !mulrA (mulrAC \n_x) Px (mulrAC \d_x).
symmetry. rewrite mulrA -(mulrA \d_x) -Py mulrA -mulrA.
by congr (_*_); rewrite mulrC.
Qed.
Notation addq := (qT_op2 addq_compat).

Lemma oppq_compat : \compat1_rational _
  (fun x => \pi_rational (PDom (- \n_x) (domP x )) ).
Proof.
apply:compat1Epi=> x y. rewrite !equivqP /equivq /=.
by rewrite mulNr mulrN; move/eqP->.
Qed.
Notation oppq := (qT_op1 oppq_compat).

Lemma mulq_compat : \compat2_rational _
  (fun x y => \pi_rational (PDom (\n_x*\n_y) (mul_dom x y) )  ).
Proof.
apply:compat2Epi=> x y x' y'.
rewrite !equivqP /equivq /=. move/eqP=>Px. move/eqP=>Py.
by rewrite !mulrA (mulrAC \n_x) Px -!mulrA Py !mulrA (mulrAC \d_x).
Qed.
Notation mulq := (qT_op2 mulq_compat).

Lemma invq_compat : \compat1_rational _
  (fun x => \pi_rational (Domd x (\d_x ,\n_x)) ).
Proof.
apply: compat1Epi=> x y.
rewrite !equivqP /equivq /=. move/eqP=>Px.
case nx: (\n_x != 0).
   case ny : (\n_y != 0).
      by rewrite !val_insubd /indom nx ny /= -Px.
   move:Px. move/eqP:ny->. rewrite mulr0. move/eqP.
   by rewrite mulf_eq0  (negPf (domP _)); move/negPf:nx->.
move:Px. move/eqP:nx=>nx. rewrite nx mul0r. move/eqP.
rewrite eq_sym mulf_eq0 (negPf (domP _)) /=. move/eqP=> ny.
by rewrite ny !val_insubd /indom /= !eqxx /= nx ny mulr0 mul0r.
Qed.
Notation invq := (qT_op1 invq_compat).






Lemma addqA : associative addq.
Proof.
elim/ratW=> x. elim/ratW=> y. elim/ratW=> z.
rewrite !qTE. congr pi. apply: val_inj=> /=.
congr (_,_); last by rewrite mulrA.
rewrite !mulr_addl addrA -!mulrA.
by congr (_+_+_); congr (_*_); rewrite mulrC.
Qed.


Lemma addqC : commutative addq.
Proof.
elim/ratW=> x. elim/ratW=> y. rewrite !qTE. congr pi. apply: val_inj=> /=.
by congr (_,_); [rewrite addrC; congr (_+_)|rewrite mulrC].
Qed.

Lemma add0q : left_id zeroq addq.
Proof.
elim/ratW=> x. rewrite !qTE. congr pi. apply: val_inj=> /=.
rewrite mul0r mulr1 mul1r add0r. by rewrite -surjective_pairing.
Qed.


Lemma addqN : left_inverse zeroq oppq addq.
Proof.
elim/ratW=> x. rewrite !qTE. apply/eqP. rewrite -equivP.
by rewrite equivqP /equivq /= mulr0 mulr1 mulNr addNr.
Qed.


Definition rat_zmodMixin :=  ZmodMixin addqA addqC add0q addqN.
Canonical Structure rat_zmodType := Eval hnf in ZmodType rat_zmodMixin.


Lemma mulqA : associative mulq.
Proof.
elim/ratW=> x. elim/ratW=> y. elim/ratW=> z.
rewrite !qTE. congr pi. apply: val_inj=> /=.
by rewrite !mulrA.
Qed.

Lemma mulqC : commutative mulq.
Proof.
elim/ratW=> x. elim/ratW=> y. rewrite !qTE. congr pi. apply: val_inj=> /=.
by congr (_,_); rewrite mulrC.
Qed.

Lemma mul1q : left_id oneq mulq.
Proof.
elim/ratW=> x. rewrite !qTE. congr pi. apply: val_inj=> /=.
by rewrite !mul1r -surjective_pairing.
Qed.

Lemma mulq_addl : left_distributive mulq addq.
Proof.
elim/ratW=> x. elim/ratW=> y. elim/ratW=> z.
rewrite !qTE. apply/eqP. rewrite -equivP equivqP /equivq /=.
rewrite !(mulr_addl, mulr_addr) !mulrA. apply/eqP. congr (_+_).
   congr (_*_*_). rewrite (mulrC _ \d_x) (mulrC _ \d_y) -!mulrA.
   by do 2!congr (_*_); rewrite mulrA mulrC.
congr (_*_). rewrite (mulrC _ \d_z) (mulrC _ \d_y) !mulrA.
by rewrite (mulrC _ \d_x) -!mulrA; do 4!congr (_*_); rewrite mulrC.
Qed.

Lemma nonzero1q : oneq != zeroq.
Proof. by rewrite -equivP equivqP /equivq /= !mul1r GRing.nonzero1r. Qed.

Definition rat_comRingMixin :=
  ComRingMixin mulqA mulqC mul1q mulq_addl nonzero1q.
Canonical Structure  rat_Ring := Eval hnf in RingType rat_comRingMixin.
Canonical Structure rat_comRing := Eval hnf in ComRingType mulqC.


Lemma mulVq : forall x, x != zeroq -> mulq (invq x) x = oneq.
Proof.
elim/ratW=> x. rewrite !qTE. move=> Px; apply/eqP. move:Px.
rewrite -!equivP !equivqP /equivq /= !mulr1 mulr0 => Px.
by rewrite val_insubd /indom /= Px /= mulrC.
Qed.

Lemma invq0 : invq zeroq = zeroq.
Proof.
apply/eqP. rewrite !qTE -equivP equivqP /equivq /=.
by rewrite mulr1 mulr0 val_insubd /indom eqxx /=.
Qed.


Definition RatFieldUnitMixin := FieldUnitMixin mulVq invq0.
Canonical Structure rat_unitRing :=
  Eval hnf in UnitRingType RatFieldUnitMixin.
Canonical Structure rat_comUnitRing :=
  Eval hnf in ComUnitRingType RatFieldUnitMixin.

Lemma field_axiom : GRing.Field.mixin_of rat_unitRing.
Proof. exact. Qed.

Definition RatFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical Structure rat_iDomain :=
  Eval hnf in IdomainType (FieldIdomainMixin field_axiom).
Canonical Structure rat_fieldMixin := FieldType field_axiom.

End Rational.

