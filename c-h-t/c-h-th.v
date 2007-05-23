Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple.
Require Import div groups group_perm zp signperm indexed_products determinant.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Section RingTheory.

Record isRings (R :Type) (plus mult : R->R->R) (opp : R->R) (zero one : R) : Prop := {
  mult1x : forall x, mult one x = x;
  mult0x : forall x : R, mult zero x = zero;
  plus0x : forall x : R, plus zero x = x;
  minusxx : forall x : R, plus x (opp x) = zero;
  plusA : forall x1 x2 x3 : R, plus x1 (plus x2 x3) = plus (plus x1 x2) x3;
  plusC : forall x1 x2 : R, plus x1 x2 = plus x2 x1;
  multA : forall x1 x2 x3 : R, mult x1 (mult x2 x3) = mult (mult x1 x2) x3;
  distrR : forall x1 x2 x3 : R, mult (plus x1 x2) x3 = plus (mult x1 x3) (mult x2 x3)
}.

Record isComRings (R :Type) (plus mult : R->R->R) (opp : R->R) (zero one : R) : Prop := {
  isRingsP : isRings plus mult opp zero one;
  multC : forall x1 x2 :R, (mult x1 x2) = (mult x2 x1)
}.

End RingTheory.
*)


Section Polynomials.

Variable R : eqType.
Variables plus mult : R -> R -> R.
Variable opp : R -> R.
Variables zero one : R.

Notation "x1 + x2" := (plus x1 x2): local_scope.
Notation "- x" := (opp x): local_scope.
Notation "x1 * x2" := (mult x1 x2): local_scope.
Notation "1" := one (at level 0) : local_scope.
Notation "0" := zero (at level 0): local_scope.
Notation "- 1" := (- 1) (at level 0) : local_scope.
Notation "x - y" := (x + (- y)) : local_scope.

Section Polynomial.

Definition polynomial := seq R.

(*
Notation "'PR_' ( n )" := (polynomial n)
  (at level 9, n at level 50, format "'PR_' ( n )") : local_scope.

Notation "'\poly_' ( i ) E" := (Polynomial (fun i => E))
  (at level 35, E at level 35, i at level 50,
   format "'\poly_' ( i )  E") : local_scope.
*)

Notation "00" := (@Seq0 R: polynomial) (at level 0): local_scope.

Fixpoint plusP (p q: polynomial) {struct p}: polynomial :=
  if p is (Adds a p') then
    if q is (Adds b q') then Adds (a + b) (plusP p' q') 
   else p 
  else q.

Notation "x1 '++' x2" := (plusP x1 x2) (at level 50) : local_scope.


Definition eqP0 (p: polynomial) : bool :=
  all (set1 0) p.

Fixpoint eqP (p q: polynomial) {struct p}: bool :=
  if p is (Adds a p') then
    if q is (Adds b q') then (a == b) && (eqP p' q') 
   else eqP0 p 
  else eqP0 q.

Notation "x1 '==' x2" := (eqP x1 x2) (at level 70) : local_scope.


Definition opP (p : polynomial) : polynomial :=
  maps opp p.

Notation "'--' x" := (opP x) (at level 10) : local_scope.

(* 
Multiplication by X
*)

Definition multPX (p : polynomial) := (Adds 0 p).

Notation "'Xp' x" := (multPX x) (at level 40) : local_scope.


(* 
Multiplication by a coefficient: 
*)

Definition multRP (c : R) (p : polynomial): polynomial :=
  maps (mult c) p.

Notation "c 'sp' x" := (multRP c x) (at level 40) : local_scope.

(* 
Multiplication
*)

Fixpoint multP (p q : polynomial) {struct p} : polynomial :=
  if p is (Adds a p') then a sp q ++ Xp (multP p' q) 
  else p.

Notation "x1 '**' x2" := (multP x1 x2) : local_scope.

End Polynomial.

Notation "00" := (@Seq0 R: polynomial) (at level 0): local_scope.Notation "x1 '++' x2" := (plusP x1 x2) (at level 50) : local_scope.
Notation "x1 '==' x2" := (eqP x1 x2) (at level 70) : local_scope.
Notation "'--' x" := (opP x) (at level 10) : local_scope.
Notation "'Xp' x" := (multPX x) (at level 40) : local_scope.
Notation "c 'sp' x" := (multRP c x) (at level 40) : local_scope.
Notation "x1 '**' x2" := (multP x1 x2) : local_scope.

Section PolynomialProp.

(* Commute *)
Variable plusC: forall a b, a + b = b + a.

Lemma plusPC: forall p q, p ++ q = q ++ p.
Proof.
by elim => [| a p1 Hrec] [| b q1] //; rewrite /= plusC Hrec.
Qed.

(* Zero Left *)
Variable plus0l: forall a, 0 + a = a.

Lemma plusP0l: forall p, 00 ++ p = p.
Proof. by done. Qed.

(* Zero Right *)
Variable plus0r: forall a, a + 0 = a.

Lemma plusP0r: forall p, p ++ 00 = p.
Proof. by move => [|a p1] //. Qed.

(* Associativity *)
Variable plusA: forall a b c, (a + b) + c = a + (b + c).

Lemma plusPA: forall p q r, (p ++ q) ++ r = p ++ (q ++ r).
Proof.
elim => [| a p Hrec] // [| b q] // [| c r] //.
by rewrite /= plusA Hrec.
Qed.

Lemma eqP0_eqP: forall p, eqP0 p -> p == 00.
Proof.
elim => [|a p Hrec] //.
Qed.

Lemma eqP_refl: forall p, p == p.
Proof.
by elim => [|a p Hrec] //=; rewrite eq_refl.
Qed.

Lemma eqP_sym: forall p q, p == q -> q == p.
Proof.
elim => [|a p Hrec] // [|b q] //=.
by case/andP => H1 H2; rewrite eq_sym H1 Hrec.
Qed.

Lemma eqP0_trans: forall p q, eqP0 p -> p == q -> eqP0 q.
Proof.
elim => [|a p Hrec] // [|b q] //=.
case/andP => H1 H2; case/andP => H3 H4.
by rewrite -(eqtype.eqP H3) H1 Hrec.
Qed.

Lemma eqP_trans: forall p q r, p == q -> q == r -> p == r.
Proof.
elim => [|a p Hrec] //=; first exact: eqP0_trans.
move => [|b q] // [|c r] //=; case/andP => H1 H2; 
                              case/andP => H3 H4.
  by rewrite -(eqtype.eqP H1) H3 (Hrec 00) // eqP0_eqP.
 -by rewrite (eqtype.eqP H1) H3 (eqP0_trans H4) // eqP_sym.
by rewrite (eqtype.eqP H1) H3 (Hrec _ _ H2).
Qed.

Lemma eqP0_plus: forall p q, eqP0 p -> eqP0 q -> eqP0 (p ++ q).
Proof.
elim => [|a p Hrec] // [|b q] //=.
case/andP => H1 H2; case/andP => H3 H4.
by rewrite -(eqtype.eqP H1) plus0l H3 Hrec.
Qed.

Lemma eqP0_eqP_plusl: forall p q, eqP0 p -> q == p ++ q.
Proof.
elim => [|a p Hrec] // [|b q] //=.
  by rewrite eq_refl eqP_refl.
case/andP => H1 H2.
by rewrite -(eqtype.eqP H1) plus0l eq_refl Hrec.
Qed.

Lemma eqP0_eqP_plusr: forall p q, eqP0 p -> q == q ++ p.
Proof.
elim => [|a p Hrec] // [|b q] //=.
  by rewrite eq_refl eqP_refl.
case/andP => H1 H2.
by rewrite -(eqtype.eqP H1) plus0r eq_refl Hrec.
Qed.

Lemma eqpP_plus: forall p1 p2 q1 q2, 
  p1 == p2 -> q1 == q2 -> (p1 ++ q1) == (p2 ++ q2).
Proof.
elim => [|a1 p1 Hrec] //.
  move => p2 q1 q2 H1 H2.
  by rewrite /= (eqP_trans H2) // eqP0_eqP_plusl.
move =>  [|a2 p2] //.
  move => q1 q2 H1 H2.
  by rewrite (@eqP_trans _ q1) // eqP_sym // eqP0_eqP_plusl.
move => [|b1 q1] //.
  move => q2 H1 H2.
  rewrite (@eqP_trans _ (Adds a1 p1)) //;
     first by rewrite /= eq_refl eqP_refl.
  by rewrite (eqP_trans H1) // eqP0_eqP_plusr.
move => [|b2 q2] //.
  move => H1 H2.
  rewrite (@eqP_trans _ (Adds a2 p2)) //;
     last by rewrite /= eq_refl eqP_refl.
  by rewrite (eqP_trans _ H1) // eqP_sym // eqP0_eqP_plusr.
rewrite /=; case/andP => H1 H2; case/andP => H3 H4.
by rewrite (eqtype.eqP H1) (eqtype.eqP H3) Hrec // eq_refl.
Qed.

(* Opposite left *)
Variable plus0pr: forall a, a + (-a) = 0.

Lemma plusP0pr: forall p, p ++ (-- p) == 00.
Proof.
move => p; apply: eqP0_eqP. 
elim  p => [| a p1 Hrec] //.
by rewrite /= plus0pr Hrec eq_refl.
Qed.

(* Opposite right *)
Variable plus0pl: forall a, (-a) + a = 0.

Lemma plusP0pl: forall p, (--p) ++ p == 00.
Proof.
move => p; apply: eqP0_eqP. 
elim  p => [| a p1 Hrec] //.
by rewrite /= plus0pl Hrec eq_refl.
Qed.

Let opp_zero: -0 = 0.
by rewrite -{2}(plus0pr 0) plus0l.
Qed.

Lemma eqP0_opp: forall p, eqP0 p -> eqP0 (-- p).
Proof.
elim => [|a p] //=.
move => H1; case/andP => H2 H3; rewrite H1 //.
by rewrite -(eqtype.eqP H2) opp_zero eq_refl.
Qed.

Lemma eqP_opp: forall p q, p == q -> -- p == -- q.
elim => [|a p Hrec] //.
  exact: eqP0_opp.
move => [|b q] //=.
  by exact: (@eqP0_opp (Adds a p)).
by case/andP => H1 H2; rewrite (eqtype.eqP H1) eq_refl Hrec.
Qed.

Lemma multPx_plus: forall p q, Xp (p ++ q) = (Xp p) ++ (Xp q).
Proof.
by elim => [|a p] //=; rewrite plus0l.
Qed.

Lemma multPx_opp: forall p, Xp (--p) = --(Xp p).
Proof.
by move => [| a p ] /=; rewrite opp_zero.
Qed.

Lemma eqP0_multPx: forall p, eqP0 p -> eqP0 (Xp p).
Proof.
by move => p Hp; rewrite /= eq_refl.
Qed.

Lemma eqP_multPx: forall p q, p == q -> Xp p == Xp q.
Proof.
by move => p Hp; rewrite /= eq_refl.
Qed.



(* zero right *)
Variable mult0r: forall a, a * 0 = 0.

Lemma eqP0_multRP: forall c p, eqP0 p -> eqP0 (c sp p).
Proof.
move => c; elim => [|a p Hrec] //=.
by case/andP => H1 H2; rewrite -(eqtype.eqP H1) mult0r eq_refl Hrec.
Qed.

(* zero left *)
Variable mult0l: forall a, 0 * a = 0.
 
Lemma eqP0_multRP0: forall p, eqP0 (0 sp p).
Proof.
elim => [|a p Hrec] //=.
by rewrite mult0l eq_refl Hrec.
Qed.

Lemma eqP_multRP: forall c p q, p == q -> c sp p == c sp q.
Proof.
move => c; elim => [| a p Hrec] //=.
  exact: eqP0_multRP.
move => [|b q] /=; case/andP => H1 H2; rewrite -(eqtype.eqP H1).
  by rewrite mult0r eq_refl eqP0_multRP.
by rewrite eq_refl Hrec.
Qed.

(* Distributivity r *)
Variable plus_mult_r: forall a b c, (a + b) * c = (a * c) + (b * c).

Lemma multRPl: forall c1 c2 p, (c1 + c2) sp p = (c1 sp p) ++ (c2 sp p).
move => c1 c2; elim => [|a p Hrec] //=.
by rewrite plus_mult_r Hrec.
Qed.

(* Distributivity l *)
Variable plus_mult_l: forall a b c, c * (a + b) = (c * a) + (c * b).

Lemma multRPr: forall c p q, c sp (p ++ q) = (c sp p) ++ (c sp q).
move => c; elim => [|a p Hrec] //= [|b q] //=.
by rewrite plus_mult_l Hrec.
Qed.

End PolynomialProp.

End Polynomials.

Section MatrixOfPoly.

End MatrixOfPoly.

Section PolyOfMatrix.

End PolyOfMatrix.
