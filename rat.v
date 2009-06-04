Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice tuple.
Require Import bigops ssralg.

Require Import quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Import GRing.Theory.
Open Local Scope ring_scope.

Section cartesianSquare.
Variable R : choiceType.

Definition cartesianSquare := (R * R)%type.

Notation "'\numer' x"  := x.1 (at level 8, x at level 2, format "'\numer' x").
Notation "'\denom' x"  := x.2 (at level 8, x at level 2, format "'\denom' x").

Definition csquare_to_tuple (x : cartesianSquare) := [tuple (\numer x); (\denom x)].
Definition tuple_to_csquare (t: 2.-tuple R) :=  ([tnth t 0], [tnth t 1]).

Lemma csquare_tupleK : cancel csquare_to_tuple tuple_to_csquare.
Proof. by elim. Qed.

Definition csquareEqMixin := CanEqMixin csquare_tupleK.
(* Canonical Structure csquareEqType := Eval hnf in EqType csquareEqMixin. *)
Canonical Structure csquareEqType := Eval hnf in [eqType of cartesianSquare].
Definition csquareChoiceMixin := CanChoiceMixin csquare_tupleK.
Canonical Structure csquareChoiceType := Eval hnf in ChoiceType csquareChoiceMixin.

Identity Coercion csquareToProd : cartesianSquare >-> prod.

End cartesianSquare.

Notation "'\numer' x"  := x.1 (at level 8, x at level 2, format "'\numer'  x").
Notation "'\denom' x"  := x.2 (at level 8, x at level 2, format "'\denom'  x").

Section RatChoice.

Variable R : idomainType.

Record ratChoice : Type := RatChoice {
  pi :> cartesianSquare R -> option (cartesianSquare R);
  _ : forall x, obind pi (pi x) = pi x;
  _ : forall x y, [&& x.1*y.2 == y.1*x.2, x.2!=0 & y.2 !=0] = (pi x == pi y) && (pi x != None)
}.

Lemma pi_id : forall p:ratChoice, forall x, obind p (p x) = p x.
Proof. by case. Qed.

Lemma pi_equiv : forall p:ratChoice, 
  (fun x y=> [&& x.1*y.2 == y.1*x.2, x.2!=0 & y.2 !=0]) =2 (fun x y =>(p x == p y) && (p x != None)).
Proof. by case=> p bp ep x y; rewrite -ep. Qed.

Definition mkReprRatChoice (p : ratChoice) :=
  @ReprChoice _ (pi p)  (pi_id p).

End RatChoice.


Section Rat. (* Rational Fractions *)

Variable R : idomainType.
Variable r : ratChoice R.


Definition reprChoiceRat := Eval hnf in (mkReprRatChoice r).
Definition rat := quotient reprChoiceRat.
Notation canon_rat := (canon reprChoiceRat).
Notation dom_rat := (dom reprChoiceRat).
Notation rew_rat := (rew reprChoiceRat).


Canonical Structure rat_eqType := Eval hnf in [eqType of rat].
Canonical Structure rat_subType := Eval hnf in [subType of rat].
Canonical Structure rat_choiceType := Eval hnf in
  [choiceType of rat for (quotient_choiceType reprChoiceRat)].


Reserved Notation "x === y" (at level 70, no associativity).
Local Notation "x === y" := (@equiv _ reprChoiceRat x y).

Reserved Notation "\dom x" (at level 2, format "\dom  x").
Local Notation "\dom x" :=  (x === x).

Lemma equivS : forall x y, x === y = [&& x.1*y.2 == y.1*x.2, x.2!=0 & y.2 !=0].
Proof. by move=> x y; rewrite (pi_equiv r) /equiv /reprChoiceRat /=. Qed.


Lemma domS : forall x : cartesianSquare R, \dom x = (\denom x != 0).
Proof. by move=> x; rewrite equivS eqxx andTb andbb. Qed.



Program Definition cst_rat_dom x :=  @Dom _ reprChoiceRat (x,1) _.
Next Obligation. by rewrite equivS GRing.nonzero1r eqxx. Qed.

Definition zero_rat : rat := @Quotient _ _ (canon _ (cst_rat_dom 0)) (canon_axiomq _).
Definition one_rat : rat := @Quotient _ _ (canon _ (cst_rat_dom 1)) (canon_axiomq _).


Lemma denom_non_nul : forall x:dom_rat, \denom (dom_elt x) != 0.
Proof. by move=>[[nx dx]] /=; rewrite equivS eqxx andTb andbb. Qed.

Lemma equiv_rat : forall x y :dom_rat, (x === y) = 
  ((dom_elt x).1*(dom_elt y).2 == (dom_elt y).1*(dom_elt x).2).
Proof. by move=> x y; rewrite equivS /= !denom_non_nul !andbT. Qed.

Definition add_rapport (x y : cartesianSquare R):= 
   (\numer x*\denom y + \numer y*\denom x,\denom x * \denom y). 

Lemma add_rapport_dom_lemma : 
  forall x y : dom_rat, \dom (add_rapport (dom_elt x) (dom_elt y)).
Proof. by move=> x y; rewrite equivS /= eqxx; rewrite mulf_neq0 ?denom_non_nul. Qed. 
Canonical Structure add_rapport_dom x y := Dom (@add_rapport_dom_lemma x y).

Definition add_rat (x y : rat) : rat :=   
  @Quotient _ _ (canon _ (add_rapport (repr x) (repr y))) (canon_axiomq _).

Lemma add_rat_compat : compat2 reprChoiceRat add_rapport.
Proof.
move=> x y xf yf. rewrite !equiv_rat /=. move/eqP=>Ry. move/eqP=>Rx. apply/eqP.
rewrite !mulr_addl; congr (_+_); last rewrite ![\numer _*_]mulrC;
rewrite ![_*_*(_*_)]mulrAC !mulrA -![_*_*_*_]mulrA; congr (_*_);
by rewrite 1?[(\denom _)*_]mulrC // Rx mulrC.
Qed.
Canonical Structure add_rat_rew x y := Rew (compat_mod_op2 add_rat_compat x y).



Definition mul_rapport (x y : cartesianSquare R):= 
   (\numer x*\numer y, \denom x * \denom y). 

Lemma mul_rapport_dom_lemma: forall x y : dom_rat, \dom (mul_rapport (dom_elt x) (dom_elt y)).
Proof. by move=> x y; rewrite equivS /= eqxx mulf_neq0 ?denom_non_nul. Qed. 
Canonical Structure mul_rapport_dom x y := Dom (@mul_rapport_dom_lemma x y).

Definition mul_rat (x y : rat) : rat :=   
  @Quotient _ _ (canon _ (mul_rapport (repr x) (repr y))) (canon_axiomq _).

Lemma mul_rat_compat : compat2 reprChoiceRat mul_rapport.
Proof.
move=> x y xf yf. rewrite !equiv_rat /=. move/eqP=>Ry. move/eqP=>Rx. apply/eqP.
rewrite ![_*_*(_*_)]mulrAC !mulrA -![_*_*_*_]mulrA Ry; congr(_*_).
by rewrite mulrC Rx mulrC.
Qed. 
Canonical Structure mul_rat_rew x y := Rew (compat_mod_op2 mul_rat_compat x y).

Definition opp_rapport (x : cartesianSquare R):= (-\numer x, \denom x). 

Lemma opp_rapport_dom_lemma: forall x : dom_rat, \dom (opp_rapport (dom_elt x)).
Proof. by move=> x; rewrite equivS /= eqxx ?denom_non_nul. Qed. 
Canonical Structure opp_rapport_dom x := Dom (@opp_rapport_dom_lemma x).

Definition opp_rat (x : rat) : rat :=   
  @Quotient _ _ (canon _ (opp_rapport (repr x))) (canon_axiomq _).

Lemma opp_rat_compat : compat1 reprChoiceRat opp_rapport.
Proof.
by move=> x xf;  rewrite !equiv_rat /= !mulNr; move/eqP->. 
Qed.
Canonical Structure opp_rat_rew x := Rew (compat_mod_op1 opp_rat_compat x).


Lemma add_ratA : associative add_rat.
Proof.
move=> x y z. apply/equivP=>/=. apply: quot_inj=>/=.
congr (_,_); last by rewrite mulrA.
by rewrite /= !mulr_addl !mulrA addrA; congr (_+_+_); rewrite mulrAC.
Qed.

Lemma add_ratC : commutative add_rat.
Proof.
move=> x y. apply:val_inj=> /=;
congr (canon _ (_, _)); last by rewrite mulrC.
by rewrite addrC.
Qed.

Lemma cst_dom_lemma: forall x:R, \dom (x,1).
Proof. by move=>x; rewrite equivS /= eqxx GRing.nonzero1r.  Qed.
Canonical Structure cst_dom x := Dom (@cst_dom_lemma x).

Lemma add_0rat: left_id zero_rat add_rat.
Proof.
move=>x. apply/equivP=>/=. apply: quot_inj=>/=.
by case:x=>[[]] /= *; rewrite /add_rapport mul0r mulr1 mul1r add0r.
Qed.

Lemma add_ratN : left_inverse zero_rat opp_rat add_rat.
Proof.
move=> x. apply/equivP=>/=. rewrite rew_equiv /=.
by rewrite !equiv_rat /= mul0r mulr1 mulNr addrC subrr eqxx.
Qed.



Definition rat_zmodMixin :=  ZmodMixin add_ratA add_ratC add_0rat add_ratN.
Canonical Structure rat_zmodType := Eval hnf in ZmodType rat_zmodMixin.


Lemma mul_ratA : associative mul_rat.
Proof.
move=> x y z. apply/equivP=>/=.  apply: quot_inj=>/=.
by congr(_,_)=>/=; rewrite mulrA.
Qed.

Lemma mul_ratC : commutative mul_rat.
Proof.
by move=> x y; apply:val_inj=>/=; congr(canon _); congr(_,_); rewrite mulrC.
Qed.

Lemma mul_1rat : left_id one_rat mul_rat.
Proof.
move=> x. apply/equivP=>/=. apply: quot_inj=>/=.
by rewrite /mul_rapport /= !mul1r; move:x=>[[??]/=?].
Qed.

Lemma mul_rat_addl : left_distributive mul_rat add_rat.
Proof.
move=> x y z. apply/equivP=>/=. rewrite rew_equiv /=.
rewrite equiv_rat /= !mulr_addl. apply/eqP.
by congr(_+_); rewrite -!mulrA; congr(_*_); rewrite !mulrA; congr(_*_*_);
rewrite -mulrA; symmetry; rewrite -mulrA; congr (_*_); rewrite mulrC.
Qed.

Lemma nonzero_1rat : one_rat != 0.
Proof.
rewrite -quotientP /= rew_equiv /= !equiv_rat /=.
by rewrite !mulr1 GRing.nonzero1r.
Qed.

Definition rat_comRingMixin := 
  ComRingMixin mul_ratA mul_ratC mul_1rat mul_rat_addl nonzero_1rat.
Canonical Structure  rat_Ring := Eval hnf in RingType rat_comRingMixin.
Canonical Structure rat_comRing := Eval hnf in ComRingType mul_ratC.


Definition inv_rapport (x:cartesianSquare R)  := 
 if @insub _ _ (dom_subType reprChoiceRat) (x.2,x.1) 
   is Some y then (dom_elt y)  else x.

Lemma inv_rapport_dom_lemma: forall x:dom_rat, \dom (inv_rapport (dom_elt x)).
Proof. 
rewrite /inv_rapport=>x. case:insubP; first by move=>[[??]??]/=->.
by move=> _; apply: in_dom.
Qed.
Canonical Structure inv_rapport_dom x := Dom (@inv_rapport_dom_lemma x).

Definition inv_rat (x:rat) : rat :=
  @Quotient _ _ (canon_rat (inv_rapport (repr x))) (canon_axiomq _).

Lemma numer0 : (\numer (repr zero_rat)) = 0.
Proof. 
have:((repr zero_rat)===(0,1)); first by rewrite canon_eliml /= domS GRing.nonzero1r.
by rewrite equivS /= mulr1 mul0r; case/and3P; move/eqP.
Qed.

Lemma numer_eq0 : forall (x:rat), (x == 0) = (\numer (repr x) == 0).
Proof.
move=> x; apply/eqP/eqP=> Hx; first by rewrite Hx numer0.
by apply/equivP=>/=; rewrite rew_equiv /= equiv_rat /= Hx !mul0r eqxx.
Qed.

Lemma numer_equiv_eq0 : forall x y, x === y
  -> (\numer x == 0)  = (\numer y == 0).
Proof.
move=> x y. rewrite equivS. case/and3P=> exy dx dy.
apply/eqP/eqP=>N; move:exy; rewrite N mul0r ?[0 == _]eq_sym mulf_eq0.
   by case/orP; move/eqP=>// Hx; move: Hx dx->; rewrite eqxx.
by case/orP; move/eqP=>// Hy; move: Hy dy->; rewrite eqxx.
Qed.

Lemma numer_equiv_neq0 : forall x y, x === y
  -> (\numer x != 0)  = (\numer y != 0).
Proof.
move=> x y exy. apply:eqP. rewrite (inj_eq negb_inj).
by apply/eqP; apply: numer_equiv_eq0.
Qed.

Lemma inv_rapport_compat : compat1 reprChoiceRat inv_rapport.
Proof.
move=> x xf exxf. move:(exxf). rewrite !equiv_rat. move/eqP=> Rx /=. 
rewrite /inv_rapport /=. case:insubP. 
   case:insubP; first by move=>/= u dmx -> v dx -> /=; rewrite mulrC -Rx mulrC.
   rewrite domS /= negb_involutive -(numer_equiv_eq0 (exxf)) /=.
   by move/eqP->; rewrite domS /= eqxx.
rewrite domS /= negb_involutive (numer_equiv_eq0 exxf).
move/eqP->=>/=. case: insubP; last by rewrite Rx eqxx.
by rewrite domS /= eqxx.
Qed.
Canonical Structure inv_rapport_rew x := Rew (compat_mod_op1 inv_rapport_compat x).


Lemma mulV_rat : forall x, x != 0 -> inv_rat x * x = 1.
Proof.
move=> x Ux /=. apply/equivP=>/=. rewrite rew_equiv /= equiv_rat /=.
rewrite mul1r mulr1 /inv_rapport /=. case:insubP.
   by move=> u Dx /= -> /=; rewrite mulrC eqxx.
by case/negP; rewrite domS /= -numer_eq0.
Qed.

Lemma inv_rat0 : inv_rat 0 = 0.
Proof.
apply/equivP=>/=. rewrite rew_equiv /= equiv_rat /= mulr1 mul0r.
by rewrite /inv_rapport; case:insubP; first by rewrite domS /= eqxx.
Qed.


Definition RatFieldUnitMixin := FieldUnitMixin mulV_rat inv_rat0.
Canonical Structure rat_unitRing := 
  Eval hnf in UnitRingType RatFieldUnitMixin.
Canonical Structure rat_comUnitRing :=  
  Eval hnf in ComUnitRingType RatFieldUnitMixin.

Notation unit := (GRing.unitDef rat_unitRing).
Lemma field_axiom : GRing.Field.mixin_of rat_unitRing.
Proof. exact. Qed.

Definition RatFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical Structure rat_iDomain := Eval hnf in IdomainType (FieldIdomainMixin field_axiom).
Canonical Structure rat_fieldMixin := FieldType field_axiom.

End Rat.