Add LoadPath "../".
Require Import ssreflect.
Require Import ssrbool.
Require Import eqtype.
Require Import fintype.
Require Import ssrnat.
Require Import seq.
Require Import funs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Rings.

Structure rings : Type := Rings {
  R :> eqType;
  zero :R;
  one :R;
  plus :R->R->R;
  mult :R->R->R;
  opp :R->R;
  zeroP : forall x, plus zero x = x;
  oppP : forall x, plus (opp x) x = zero;
  plusA : forall x1 x2 x3, plus x1 (plus x2 x3) = plus (plus x1 x2) x3;
  plusC : forall x1 x2, plus x1 x2 = plus x2 x1;
  onePl : forall x, mult one x = x;
  onePr : forall x, mult x one = x;
  multA : forall x1 x2 x3, mult x1 (mult x2 x3) = mult (mult x1 x2) x3;
  plus_multl : forall x1 x2 x3, mult x1 (plus x2 x3) = plus (mult x1 x2) (mult x1 x3);
  plus_multr : forall x1 x2 x3, mult (plus x1 x2) x3 = plus (mult x1 x3) (mult x2 x3);
  one_diff_zero : one <> zero (* Non trivial ring *)
}.

End Rings.

Implicit Arguments Rings.one [].
Implicit Arguments Rings.zero [].

Delimit Scope rings_scope with R.
Bind Scope rings_scope with Rings.R.
Arguments Scope Rings.plus [_ rings_scope rings_scope].
Arguments Scope Rings.opp [_ rings_scope].
Arguments Scope Rings.mult [_ rings_scope rings_scope].

Notation ringsType := Rings.rings.
Notation RingsType := Rings.Rings.

Definition mult := nosimpl Rings.mult.
Definition plus := nosimpl Rings.plus.
Definition opp := nosimpl Rings.opp.
Definition zero := nosimpl Rings.zero.
Definition one := nosimpl Rings.one.
Prenex Implicits mult plus opp.

Infix "+" := plus: rings_scope.
Notation "- x" := (opp x): rings_scope.
Infix "*" := mult: rings_scope.
Notation "1" := (one _) (at level 0) : rings_scope.
Notation "0" := (zero _) (at level 0): rings_scope.

Section RingsProp.
Open Scope rings_scope.

Variable elt : ringsType.

Lemma plusA : forall x1 x2 x3 : elt, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. exact: Rings.plusA. Qed.

Lemma plusC : forall x1 x2 : elt, x1 + x2 = x2 + x1.
Proof. exact: Rings.plusC. Qed.

Lemma plus0l: forall x : elt, 0 + x = x.
Proof. exact: Rings.zeroP. Qed.

Lemma plus0r: forall x : elt, x + 0 = x.
Proof. move=> *; rewrite plusC; exact: plus0l. Qed.

Lemma plus_opl : forall x : elt, - x + x = 0.
Proof.  exact: Rings.oppP. Qed.

Lemma plus_opr : forall x : elt, x + - x = 0.
Proof. move=> *; rewrite plusC; exact: plus_opl. Qed.

Lemma plusK : forall x : elt, cancel (plus x) (plus (- x)).
Proof. by move=> x y; rewrite plusA plus_opl plus0l. Qed.

Lemma plusInj : forall x : elt, injective (plus x).
Proof. move=> x; exact: can_inj (plusK x). Qed.

Implicit Arguments plusInj [].

Lemma opp0 : -0 = 0 :> elt.
Proof. by rewrite -{2}(plus_opl 0) plusC plus0l. Qed.

Lemma oppK : cancel (@opp elt) opp.
Proof. by move=> x; rewrite -{2}(plusK (- x) x) plusC -plusA plusK. Qed.

Lemma oppInj : injective (@opp elt).
Proof. exact: can_inj oppK. Qed.

Lemma opp_plus : forall x1 x2 : elt, - (x1 + x2) = - x1 + - x2. 
Proof.
move=> x1 x2; apply: (plusInj (x1 + x2)); symmetry.
by rewrite -plusA [x2 + (_ + _)]plusC -plusA plus_opl plusC -plusA
   plus0l plus_opl plusC plus_opl.
Qed.

(* Multiplication *)
Lemma multA: 
  forall x1 x2 x3 :elt, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. exact: Rings.multA. Qed.

Lemma mult1l: forall x :elt, 1 * x = x.
Proof. exact: Rings.onePl. Qed.

Lemma mult1r : forall x : elt, x * 1 = x.
Proof. exact: Rings.onePr. Qed.

Lemma plus_multl:
  forall x1 x2 x3 :elt, x3 * (x1 + x2) = (x3 * x1) + (x3 * x2).
Proof. move => *; exact: Rings.plus_multl. Qed.

Lemma plus_multr:
  forall x1 x2 x3 :elt, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
Proof. exact: Rings.plus_multr. Qed.

Lemma mult0r: forall x :elt, x * 0 = 0.
Proof.
move => x; move: (@plusInj x (x*0) 0) => ->//.
by rewrite -{1}[x]mult1r  -plus_multl  plusC plus0l mult1r plusC plus0l.
Qed.

Lemma mult0l: forall x :elt, 0 * x = 0.
Proof.
move => x; move: (@plusInj x (0*x) 0) => ->//.
by rewrite -{1}[x]mult1l  -plus_multr plusC plus0l mult1l plusC plus0l.
Qed.

Lemma mult_oppl: forall x y :elt, (- (x * y)) = (- x) * y.
Proof.
move => x y.
by rewrite -[-x*y]plus0l -(plus_opl (x*y)) -plusA -plus_multr [x+_]plusC 
   plus_opl mult0l plusC plus0l.
Qed.

Lemma mult_oppr: forall x y :elt, (-(x * y)) = x * (- y).
Proof.
move => x y.
by rewrite -[x*-y]plus0l -(plus_opl (x*y)) -plusA -plus_multl [y+_]plusC
   plus_opl mult0r plusC plus0l.
Qed.

Lemma one_diff_0 : (one elt) <> 0.
Proof. exact: Rings.one_diff_zero. Qed.

End RingsProp.

Section CommutativeRings.
Open Scope rings_scope.

Record comRings : Type := ComRings {
  elt :> ringsType;
  multCP : forall x y :elt, x * y = y * x
}.

Variable elt : comRings.

Lemma multC : forall x y :elt, x * y = y * x.
Proof. exact: multCP. Qed.

End CommutativeRings.



