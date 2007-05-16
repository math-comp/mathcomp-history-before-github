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

Notation "0p" := (Seq0: polynomial) (at level 0): local_scope.

Fixpoint plusP (p q: polynomial) {struct p}: polynomial :=
  if p is (Adds a p') then
    if q is (Adds b q') then Adds (a + b) (plusP p' q') 
   else p 
  else q.

Notation "x1 '+p' x2" := (plusP x1 x2) (at level 50) : local_scope.

Definition eqP0 (p: polynomial) : bool :=
  all (set1 0) p.

Fixpoint eqP (p q: polynomial) {struct p}: bool :=
  if p is (Adds a p') then
    if q is (Adds b q') then (a == b) && (eqP p' q') 
   else eqP0 p 
  else eqP0 q.

Notation "x1 '=p' x2" := (eqP x1 x2) (at level 70) : local_scope.

Definition opP (p : polynomial) : polynomial :=
  maps opp p.

Notation "'-p' x" := (opP x) (at level 10) : local_scope.

(* 
Multiplication by X
*)

Definition multPX (p : polynomial) := (Adds one p).

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
  if p is (Adds a p') then a sp q +p Xp (multP p' q) 
  else p.

Notation "x1 '*p' x2" := (multP x1 x2) (at level 40) : local_scope.

End Polynomial.

Section PolynomialProp.

Lemma PlusPCom : forall p q : polynomial,  p +p q =p q +p p.

End PolynomialProp.

End Polynomials.

Section MatrixOfPoly.

End MatrixOfPoly.

Section PolyOfMatrix.

End PolyOfMatrix.
