Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple.
Require Import div groups.
Require Import determinantET rings.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope local_scope with loc.
Open Scope local_scope.
Open Scope rings_scope.

Section Polynomials.

Variable R : ringsType.
(*
Variables plus mult : R -> R -> R.
Variable opp : R -> R.
Variables zero one : R.

Infix "+" := plus: local_scope.
Notation "- x" := (opp x): local_scope.
Infix "*" := mult: local_scope.
Notation "1" := one (at level 0) : local_scope.
Notation "0" := zero (at level 0): local_scope.
*)

(*
(* Zero Right *)
Variable plus0r: forall a, a + 0 = a.
(* Zero Left *)
Variable plus0l: forall a, 0 + a = a.
(* Commute *)
Variable plusC: forall a b, a + b = b + a.
(* Associative *)
Variable plusA: forall a b c, (a + b) + c = a + (b + c).(* Opposite left *)
Variable plus_opr: forall a, a + (-a) = 0.
(* Opposite right *)
Variable plus_opl: forall a, (-a) + a = 0.
(* zero right *)
Variable mult0r: forall a, a * 0 = 0.
(* zero left *)
Variable mult0l: forall a, 0 * a = 0.
(* Distributivity r *)
Variable plus_multr: forall a b c, (a + b) * c = (a * c) + (b * c).
(* Distributivity l *)
Variable plus_multl: forall a b c, c * (a + b) = (c * a) + (c * b).
(* Commutative *)
Variable multC: forall a b, a * b = b * a.
(* Associative *)
Variable multA: forall a b c, (a * b) * c = a * (b * c).
(* one left *)
Variable mult1l: forall a, 1 * a = a.
(* one right *)
Variable mult1r: forall a, a * 1 = a.
(* one diff zero *)
Variable one_diff_0: 1 <> 0.

Let opp_zero: -0 = 0.
by rewrite -{2}(plus_opr 0) plus0l.
Qed.
*)

Section Polynomial.


(* A polynomial is sequence, the firts element of the sequence is monome of low degree*)
Definition polynomial := seq R.


(*
Fixpoint plusPnn (p q: polynomial) {struct p}: polynomial :=
  if p is (Adds a p') then
    if q is (Adds b q') then Adds (a + b) (plusPnn p' q') 
   else p 
  else q.
*)

Fixpoint plusP (p q: polynomial) {struct p}: polynomial := 
  if p is (Adds a p') then 
    if q is (Adds b q') then Adds (a + b) (plusP p' q') (* (plusPnn p' q')  *)
    else p
  else q.

Definition eqP0 (p: polynomial) : bool :=
  all (set1 0) p.

Fixpoint eqP (p q: polynomial) {struct p}: bool :=
  if p is (Adds a p') then
    if q is (Adds b q') then (a == b) && (eqP p' q') 
   else eqP0 p 
  else eqP0 q.

(* ---------------------------------  coef  --------------------------------- *)

Fixpoint coeff_poly (p : polynomial) (i : nat) {struct i} : R := 
  match p, i with
    | seq0, _ => 0
    | Adds a s, O => a
    | Adds a s, S i' => coeff_poly s i'
  end.

Definition opP (p : polynomial) : polynomial :=
  maps opp p.

(* 
Multiplication by X
*)


Definition multPX (p : polynomial) : polynomial := if p is (Adds _ _) then (Adds 0 p) else p.

(* 
Multiplication by a coefficient: 
*)

Definition multRPl (c : R) (p : polynomial): polynomial :=
  maps (mult c) p.

Definition multRPr (c : R) (p : polynomial): polynomial :=
  maps (fun x => mult x c) p.


Open Scope local_scope.


Notation "'11'" :=  (Adds 1 seq0) (at level 0): local_scope.
Notation "00" := (@Seq0 R: polynomial) (at level 0): local_scope.Notation "x1 '++' x2" := (plusP x1 x2) (at level 50) : local_scope.
Notation "x1 '==' x2" := (eqP x1 x2) (at level 70) : local_scope.
Notation "'--' x" := (opP x) (at level 10) : local_scope.
Notation "'Xp' x" := (multPX x) (at level 40) : local_scope.
Notation "c 'sp' x" := (multRPl c x) (at level 40) : local_scope.
Notation "x 'ps' c" := (multRPr c x) (at level 40) : local_scope.
(* 
Multiplication
*)

Fixpoint multP (p q : polynomial) {struct p} : polynomial :=
  if p is (Adds a p') then 
    if q is (Adds b q') then 
       Adds (mult a b) ((a sp q') ++ (p' ps b) ++ Xp (multP p' q'))
    else 00 
  else 00.
Notation "x1 '**' x2" := (multP x1 x2) : local_scope.



Section PolynomialProp.


Lemma multP0 : forall p : polynomial, 00 ** p = 00.
Proof. move => p; elim: p => [|x s Hrec] //=. Qed.

Lemma plusP0l : forall p: polynomial, 00 ++ p = p.
Proof. move => p; elim: p => [|x s Hrec] //=. Qed.

Lemma plusP0r: forall p, p ++ 00 = p.
Proof. by move => [|a p1] //. Qed.

Lemma plusPC : forall p q : polynomial,  p ++ q = q ++ p.
Proof. by elim => [| a p1 Hrec] [| b q1] //; rewrite /= plusC Hrec. Qed.

Lemma plusPA: forall p q r, (p ++ q) ++ r = p ++ (q ++ r).
Proof.
elim => [| a p Hrec] // [| b q] // [| c r] //.
by rewrite /= plusA Hrec.
Qed.

Lemma eqP0_eqP: forall p, eqP0 p -> (p == 00).
Proof. elim => //= [a p Hrec H]. Qed.

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
by rewrite -(eqtype.eqP H1) plusC plus0l eq_refl Hrec.
Qed.

Lemma eqP_plus0l: forall p, 00 ++ p = p.
Proof. done. Qed.

Lemma eqP_plus0r: forall p, p ++ 00 = p.
Proof. by case. Qed.

Lemma eqP_plus: forall p1 p2 q1 q2, 
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

Lemma plusP0pr: forall p, p ++ (-- p) == 00.
Proof.
move => p; apply: eqP0_eqP. 
elim  p => [| a p1 Hrec] //.
by rewrite /=  Hrec plus_opr eq_refl.
Qed.

Lemma plusP0pl: forall p, (--p) ++ p == 00.
Proof.
move => p; apply: eqP0_eqP. 
elim  p => [| a p1 Hrec] //.
by rewrite plusPC /= plusPC plus_opr Hrec eq_refl.
Qed.

Lemma eqP0_opp: forall p, eqP0 p -> eqP0 (-- p).
Proof.
elim => [|a p] //=.
move => H1; case/andP => H2 H3; rewrite H1 //.
by rewrite -(eqtype.eqP H2) opp0 eq_refl.
Qed.

Lemma eqP_opp: forall p q, p == q -> -- p == -- q.
elim => [|a p Hrec] //.
  exact: eqP0_opp.
move => [|b q] //=.
  by exact: (@eqP0_opp (Adds a p)).
by case/andP => H1 H2; rewrite (eqtype.eqP H1) eq_refl Hrec.
Qed.

Lemma multPX_plus: forall p q, Xp (p ++ q) = (Xp p) ++ (Xp q).
Proof.
by case => [|a p] // [|b q] //=; rewrite plus0l.
Qed.

Lemma multPX_opp: forall p, Xp (--p) = --(Xp p).
Proof.
by move => [| a p ] //=; rewrite opp0.
Qed.

Lemma eqP0_multPX: forall p, eqP0 p -> eqP0 (Xp p).
Proof.
by move => [| a p] Hp; rewrite //= eq_refl.
Qed.

Lemma eqP_multPX: forall p q, p == q -> Xp p == Xp q.
Proof.
by move => [| a p] [|b q] Hp; rewrite //= eq_refl.
Qed.

Lemma eqP0_multRPl: forall c p, eqP0 p -> eqP0 (c sp p).
Proof.
move => c; elim => [|a p Hrec] //=.
case/andP => H1 H2; rewrite -(eqtype.eqP H1) mult0r eq_refl Hrec //=.
Qed.

Lemma eqP0_multRPl0: forall p, eqP0 (0 sp p).
Proof.
elim => [|a p Hrec] //=.
by rewrite mult0l eq_refl Hrec.
Qed.

Lemma eqP_multRPl: forall c p q, p == q -> c sp p == c sp q.
Proof.
move => c; elim => [| a p Hrec] //=.
  exact: eqP0_multRPl.
move => [|b q] /=; case/andP => H1 H2; rewrite -(eqtype.eqP H1).
  by rewrite mult0r eq_refl eqP0_multRPl.
by rewrite eq_refl Hrec.
Qed.

Lemma multRPl_multPX: forall c p, Xp (c sp p) = c sp (Xp p).
Proof.
by move => c [| a p] //=; rewrite mult0r.
Qed.

Lemma multRPl_plusl: forall c1 c2 p, (c1 + c2) sp p = (c1 sp p) ++ (c2 sp p).
move => c1 c2; elim => [|a p Hrec] //=.
by rewrite plus_multr Hrec.
Qed.

Lemma multRPl_plusr: forall c p q, c sp (p ++ q) = (c sp p) ++ (c sp q).
move => c; elim => [|a p Hrec] //= [|b q] //=.
by rewrite plus_multl Hrec.
Qed.

Lemma eqP0_multRPr: forall c p, eqP0 p -> eqP0 (p ps c).
Proof.
move => c; elim => [|a p Hrec] //=.
by case/andP => H1 H2; rewrite -(eqtype.eqP H1) mult0l eq_refl Hrec.
Qed.
 
Lemma eqP0_multRPr0: forall p, eqP0 (p ps 0).
Proof.
elim => [|a p Hrec] //=.
by rewrite mult0r eq_refl Hrec.
Qed.

Lemma eqP_multRPr: forall c p q, p == q -> p ps c == q ps c.
Proof.
move => c; elim => [| a p Hrec] //=.
  exact: eqP0_multRPr.
move => [|b q] /=; case/andP => H1 H2; rewrite -(eqtype.eqP H1).
  by rewrite mult0l eq_refl eqP0_multRPr.
by rewrite eq_refl Hrec.
Qed.

Lemma multRPr_multPX: forall c p, Xp (p ps c) = (Xp p) ps c.
Proof.
by move => c [| a p] //=; rewrite mult0l.
Qed.

Lemma multRPr_plusl: forall c1 c2 p, p ps (c1 + c2) = (p ps c1) ++ (p ps c2).
move => c1 c2; elim => [|a p Hrec] //=.
by rewrite plus_multl Hrec.
Qed.

Lemma multRPr_plusr: forall c p q, (p ++ q) ps c = (p ps c) ++ (q ps c).
move => c; elim => [|a p Hrec] //= [|b q] //=.
by rewrite plus_multr Hrec.
Qed.

Lemma eqP0_multPl: forall (p q: polynomial), eqP0 p -> eqP0 (p ** q).
Proof.
elim => [|a p Hrec] //= [|b q] //=.
case/andP => H1 H2.
rewrite -(eqtype.eqP H1) mult0l eq_refl !eqP0_plus //=.
  by exact: eqP0_multRPl0.
  by exact: eqP0_multRPr.
by rewrite eqP0_multPX // Hrec.
Qed.

Lemma eqP0_multPr: forall (p q: polynomial), eqP0 p -> eqP0 (q ** p).
Proof.
elim => [|a p Hrec] [|b q] //=.
case/andP => H1 H2; rewrite -(eqtype.eqP H1) mult0r eq_refl !eqP0_plus //=.
  by exact: eqP0_multRPl.
  by exact: eqP0_multRPr0.
by rewrite eqP0_multPX // Hrec.
Qed.

Lemma eqpP_mult: forall p1 p2 q1 q2, 
  p1 == p2 -> q1 == q2 -> (p1 ** q1) == (p2 ** q2).
Proof.
elim => [|a1 p1 Hrec].
  move => p1 q1 q2 H1 H2.
  by rewrite /= eqP0_multPl.
move => [|a2 p2].
  move => q1 q2 H1 H2.
  by rewrite (@eqP_trans _ 00) ?eqP0_multPl // eqP_sym 
             // /eqP eqP0_multPl.
move => [|b1 q1].
  move => q2 H1 H2.
  by rewrite (@eqP_trans _ 00) // /eqP eqP0_multPr.
move => [|b2 q2].
  move => H1 H2.
  by rewrite (@eqP_trans _ 00) // eqP_sym // /eqP eqP0_multPr.
rewrite /=; case/andP => H1 H2; case/andP => H3 H4.
rewrite (eqtype.eqP H1) (eqtype.eqP H3) eq_refl !eqP_plus //=
           ?eqP_multPX // ?Hrec // ?eqP_multRPr ?eqP_multRPl // eq_refl.
Qed.

Lemma multP0l: forall p, 00 ** p = 00.
Proof. done. Qed.

Lemma multP0r: forall p, p ** 00 = 00.
Proof. by case. Qed.

Lemma multRPrlC: forall a b p, a sp (p ps b) = (a sp p) ps b.
move => a b; elim => [|c  p Hrec] //=.
by rewrite multA Hrec.
Qed.

(* commutative proprety *)

Fixpoint com_coeff (p :polynomial) (x :R) {struct p} : bool := 
  (if p is (Adds a p') then (a * x == x * a)%EQ && (com_coeff p' x) else true).

Lemma com_coeffP : forall p x, 
  reflect (forall y, (mem p) y -> x * y = y * x) (com_coeff p x).
Proof. 
move => p x.
apply: (iffP idP) => H; first (elim: p H => //=).
  move=> x0 s Hrec H y Hy.
  case Hx: (x0==y)%EQ; elim: (andP H) => //=; first (move/eqtype.eqP: Hx => <-; 
                                         move=> HH _; by move/eqtype.eqP: HH => HH).
  move => _ HH; apply: Hrec => //=.
  elim: (orP Hy) => HT //=; by rewrite Hx in HT.
elim: p H => //= [a s Hrec H].
rewrite / setU1 in H.
move: (H a) => Ha; rewrite eq_refl //= in Ha; rewrite Ha //= eq_refl; apply Hrec.
move=> y Hy; apply H; apply/orP; right; exact Hy.
Qed.

(*
Lemma com_coeff_plusP: forall p q x,
  com_coeff p x -> com_coeff q x -> com_coeff (p ++ q) x.
Proof.
elim => //.
move => x s H1 q x0 H2 H3.
apply/com_coeffP => //.
*)

(* ____ *)

Lemma multRPrl: forall a p, com_coeff p a -> p ps a = a sp p.
move => b; elim => //= [a  p Hrec H].
elim: (andP H) => H1 H2; move/eqtype.eqP: H1 => ->; congr Adds.
by apply: Hrec.
Qed.

Lemma multPC: forall p q, (forall x, (mem p) x -> com_coeff q x) -> p ** q = q ** p.
Proof.
elim => //= [|a p Hrec] //= [|b q H] //=.
move: (H a) => //= ; rewrite / setU1 eq_refl //=.
move=> H1; move: (H1 is_true_true); clear H1; move=> H1.
rewrite Hrec; first last.
  move=> x Hx; move: (H x) => //=; rewrite /setU1 Hx orbT => H2.
  move: (H2 is_true_true); clear H2; move=> H2; elim: (andP H2) => //=.
rewrite !multRPrl; first (elim: (andP H1) => HH _; rewrite (eqtype.eqP HH)
    ; congr Adds; congr plusP; by rewrite plusPC).
  by elim: (andP H1).
clear H1 Hrec; rewrite //= in H.
elim: p H => //= [s p0 Hrec H].
apply/andP; split; last (apply: Hrec).
  move: (H s) => //=; rewrite / setU1 //= eq_refl orbT eq_sym => H1;
      move: (H1 is_true_true); move/andP => H2; by elim: H2.
move=> x Hx; apply: H; move: Hx; rewrite / setU1 //=.
move=> H; elim: (orP H) => ->; rewrite ?orbT //=.
Qed.


Lemma multRPl_multl: forall c1 c2 p, (c1 * c2) sp p = c1 sp (c2 sp p).
Proof.
move => c1 c2; elim => [|a p Hrec] //=.
by rewrite multA Hrec.
Qed.

Lemma multRPl_multr: forall c p q, c sp (p ** q) = (c sp p) ** q.
Proof.
move => c; elim => [|a p Hrec] //= [|b q] //=.
rewrite multA; congr Adds.
by rewrite !multRPl_plusr multRPl_multl multRPrlC -Hrec multRPl_multPX.
Qed.

Lemma multRPr_multl: forall c1 c2 p, p ps (c1 * c2) = (p ps c1) ps c2.
Proof.
move => c1 c2; elim => [|a p Hrec] //=.
by rewrite multA Hrec.
Qed.

Lemma multRPr_multr: forall c p q, (p ** q) ps c = p ** (q ps c).
Proof.
move => c; elim => [|a p Hrec] //= [|b q] //=.
rewrite multA; congr Adds.
by rewrite !multRPr_plusr multRPr_multl multRPrlC -Hrec multRPr_multPX.
Qed.

Lemma plusP_multr: forall p q r, 
  (p ++ q) ** r = (p ** r) ++ (q ** r).
Proof.
elim => [|a p Hrec] // [|b q] //.
  by move => r; rewrite multP0l !plusP0r.
move => [|c r] //=.
congr Adds.
  by rewrite plus_multr.
rewrite Hrec multPX_plus multRPl_plusl multRPr_plusr !plusPA.
repeat (congr plusP; rewrite plusPC !plusPA).
Qed.

Lemma plusP_multl: forall p q r, 
  r ** (p ++ q) = (r ** p) ++ (r ** q).
Proof.
elim => [|a p Hrec] //.
 by move => q r; rewrite multP0r !plusP0l.
move => [|b q] //.
 by move => r; rewrite multP0r !plusP0r.
move => [|c r] //=.
congr Adds.
  by rewrite plus_multl.
rewrite Hrec multPX_plus multRPr_plusl multRPl_plusr !plusPA.
repeat (congr plusP; rewrite plusPC !plusPA).
Qed.

Lemma adds_multl: forall a (p q: polynomial), 
  (Adds a p) ** q = (a sp q) ++ Xp (p ** q).
Proof.
move => a p q; elim: q a p => [|b q Hrec] a.
  by move => p;  rewrite !multP0r. 
case => [|a1 p].
  by rewrite multP0l /= !plusP0r.
rewrite {1}[Adds a1 p]lock /=; unlock.
congr Adds; first by rewrite plus0r.
rewrite !plusPA; congr plusP.
rewrite Hrec.
rewrite (plusPC (p ps b)) -plusPA.
case: (a1 sp _ ++ _) => // [a2 p1].
rewrite {2}[Adds a2 _]lock /= plus0r plusPC.
by unlock.
Qed.


Lemma multPX_multl: forall p q, (Xp p) ** q = Xp (p ** q).
Proof.
move => [|a p] // [|b q] //.
change (Xp Adds a p) with (Adds 0 (Adds a p)).
rewrite adds_multl /=.
rewrite plus0r mult0l; congr Adds.
rewrite plusPA.
elim: q (p ps b ++ _) (a * b) => // c r Hrec [| c1 r1] // d.
  rewrite /= mult0l plus0l.
  by generalize (Hrec 00 (a * c)); rewrite !plusP0r => ->.
by rewrite /= ?Hrec mult0l plus0l.
Qed.


Lemma adds_multr: forall a (p q: polynomial), 
  q ** (Adds a p) = (q ps a) ++ Xp (q ** p).
Proof.
move => a p q; elim: q a p => [|b q Hrec] a.
  by move => p;  rewrite !multP0l. 
case => [|a1 p].
  by rewrite multP0r /= multP0r /= !plusP0r.
rewrite {1}[Adds a1 p]lock /=; unlock.
congr Adds; first by rewrite plus0r.
rewrite !plusPA plusPC plusPA; congr plusP.
rewrite Hrec.
case: (q ps _ ++ _) => [| a2 p1].
  by rewrite /= plusP0r.
rewrite /multPX.
rewrite [Adds a2 p1]lock [b sp p ++ _]lock /=; unlock.
by rewrite plus0l plusPC.
Qed.

Lemma multPX_multr: forall p q, q ** (Xp p) = Xp (q ** p).
Proof.
move => [|a p] // [|b q] //.
change (Xp Adds a p) with (Adds 0 (Adds a p)).
rewrite adds_multr /=.
rewrite plus0r mult0r; congr Adds.
rewrite plusPA.
rewrite [b sp p ++ _]plusPC !plusPA.
elim: q (Xp _ ++ _) (b * a) => // c r Hrec [| c1 r1] // d.
  rewrite /= mult0r plus0l.
  by generalize (Hrec 00 (c * a)); rewrite !plusP0r => ->.
by rewrite /= ?Hrec mult0r plus0l.
Qed.

Lemma multP_sp_ps: forall a p q,
  (p ps a) ** q = p ** (a sp q).
Proof.
move => c; elim => [|a p Hrec] // [|b q] //=.
by rewrite multA Hrec multRPl_multl multRPr_multl.
Qed.

Lemma multPA: forall p q r, 
  multP (multP p q) r = multP p (multP q r).
Proof.
elim => [|a p Hrec] // [|b q] // [|c r] //=.
congr Adds => //; first (by rewrite multA).
rewrite -!multPX_multl !multPX_plus.
rewrite !plusP_multl !plusP_multr.
rewrite !multRPl_plusr !multRPr_plusr.
rewrite !plusPA.
congr plusP; first by rewrite multRPl_multl.
congr plusP; first by rewrite multRPrlC.
apply sym_equal; rewrite plusPC !plusPA.
congr plusP; first by rewrite multRPr_multl.
rewrite -!multP_sp_ps.
apply sym_equal; rewrite plusPC !plusPA plusPC !plusPA.
congr plusP.
  by rewrite multRPr_multPX.
apply sym_equal; rewrite plusPC !plusPA.
congr plusP.
 by rewrite !multPX_multl !multPX_multr Hrec.
rewrite plusPC; congr plusP.
  by rewrite multRPr_multr.
by rewrite multRPl_multr multRPl_multPX.
Qed.

Lemma multRP1 : forall p, 1 sp p = p.
Proof.
elim => [|a p Hrec] //=.
by rewrite mult1l Hrec.
Qed.

Lemma multPR1 : forall p, p ps 1 = p.
Proof.
elim => [|a p Hrec] //=.
by rewrite mult1r Hrec.
Qed.

Lemma multP1 : forall p : polynomial, 11 ** p = p.
Proof.
case => [|a p] //=.
by rewrite !plusP0r mult1l multRP1.
Qed.

Lemma multP1r : forall p : polynomial, p ** 11 = p.
Proof.
case => [|a p] //=.
by rewrite mult1r multP0r //= plusP0r multPR1.
Qed.


(* A pol is normal if its last element is <> 0 *)
Definition normal (p: polynomial) :=
  last 1 p != 0.

Fixpoint norm3 (p q r: polynomial) {struct p}: polynomial :=
  if p is (Adds a p') then
    if (a == 0)%EQ then norm3 p' q (Adds a r) 
              else norm3 p' (Adds a r) (Adds a r)
  else rev q.

(* Normalizer *)
Definition norm p := norm3 p (Seq0 _) (Seq0 _).


(* 00 is normal *)
Lemma normal0: normal 00.
Proof.
rewrite /normal /=.
by apply/negP => H1; case (@one_diff_0 R); apply/eqtype.eqP.
Qed.

(* 1 is normal *)
Lemma normal1: normal 11.
Proof.
rewrite /normal /=.
by apply/negP => H1; case (@one_diff_0 R); apply/eqtype.eqP.
Qed.

Lemma normal_inv: forall a p, normal (Adds a p) -> normal p.
Proof.
move => a [|b p] // _; exact: normal0.
Qed.

(* Equality on normal polynomials is structural *)
Lemma normal_eq:
  forall p q, normal p -> normal q -> p == q -> p = q.
Proof.
have F1: forall p, eqP0 p -> last 0 p = 0.
  elim => [|a p] //= H.
  by case/andP; move/eqtype.eqP => <-.
elim => [|a p Hrec].
  elim => [|b q Hrec] //=.
  move => _ H; case/andP; move/eqtype.eqP => H1 H2.
  case/negP: H; rewrite -H1 /=.
  apply/eqtype.eqP; apply F1 => //.
case => [|b q H1 H2] //=.
  move => H _; case/andP; move/eqtype.eqP => H1 H2.
  case/negP: H; rewrite -H1 /=.
  apply/eqtype.eqP; apply F1 => //.
case/andP; move/eqtype.eqP => -> H3.
by rewrite (Hrec q)  ?(normal_inv H1) ?(normal_inv H2).
Qed.

Lemma norm3_eq:
  forall p q r, 
    (rev q) == (rev r) -> norm3 p q r == cat (rev r) p.
Proof.
elim => [|a p Hrec] q r H1 //=.
  by rewrite cats0.
case E1: (a == 0)%EQ.
  rewrite (eqP_trans (Hrec q (Adds a r) _)) //=.
    rewrite rev_adds.
    rewrite {H1}(eqP_trans H1) //.
    elim: (rev r) => [|b r1 Hrec1] //=.
      by rewrite eq_sym E1.
    by rewrite Hrec1 eq_refl.
  by rewrite rev_adds cat_add_last eqP_refl.
rewrite (eqP_trans (Hrec (Adds a r) (Adds a r) _)) //=.
  by rewrite eqP_refl.
by rewrite rev_adds cat_add_last eqP_refl.
Qed.

(* Normalizing returns an equal polynomial *)
Lemma norm_eq: forall p, norm p == p.
Proof.
move => p; rewrite /norm.
by rewrite (eqP_trans (norm3_eq _ _)) //= eqP_refl.
Qed.

Lemma norm3_normal:
  forall p q r, 
    normal (rev q) -> normal (norm3 p q r).
Proof.
elim => [|a p Hrec] q r H1 //=.
case E1: (a == 0)%EQ; rewrite Hrec //.
by rewrite /normal rev_adds last_add_last E1.
Qed.

(* Normalizing normalises *)
Lemma norm_normal: forall p, normal (norm p).
Proof.
move => p; rewrite /norm.
rewrite norm3_normal //; exact: normal0.
Qed.

Lemma norm_plusP : forall p q, p ++ (norm q) == norm (p ++ q).
Proof.
move => p q.
apply: eqP_sym.
apply: (eqP_trans (norm_eq (p ++ q))).
apply: eqP_plus; first (exact: eqP_refl).
apply: eqP_sym; apply: norm_eq.
Qed.


(* Injection from polynomial to R *)
Definition R_to_poly (x :R) : polynomial := if x!=0 then (Adds x seq0) else seq0.

Lemma inj_R_to_poly : injective R_to_poly.
move => x.
case HT:(x==0%R)%EQ; rewrite / R_to_poly HT => //= y;
  case HTT:(y==0%R)%EQ=> //= H; last (move/eqseqP: H=> //=).
  by move/eqtype.eqP: HT=> ->; move/eqtype.eqP: HTT => ->.
rewrite andbT => H; by apply/eqtype.eqP.
Qed.

Lemma R_to_poly_normal: forall x, normal (R_to_poly x).
Proof.
move=> x; case H:(x==0%R)%EQ; rewrite / R_to_poly H //= / normal //=;
    first (apply/eqtype.eqP; apply: one_diff_0).
apply/eqtype.eqP; move/eqtype.eqP: H => //=.
Qed.

End PolynomialProp.

Section MorphismEvaluation.

Fixpoint evalP (p :polynomial) (x :R) {struct p} : R :=
  (if p is (Adds a p') then a + x * (evalP p' x) else 0).

Lemma evalP_com_coeff: forall p x, com_coeff p x ->
  x * (evalP p x) = (evalP p x) * x.
Proof.
elim => //=; first (by move=> *; rewrite mult0r mult0l).
move=> a s Hrec x H.
move/andP: H => H; elim: H => H1 H2.
rewrite plus_multl plus_multr -multA.
move/eqtype.eqP: H1 => ->; congr plus; congr mult.
by rewrite Hrec. 
Qed.

(* Proof that eval is morphisme *)

Lemma evalP_plusP : forall p q x, evalP (p ++ q) x = (evalP p x) + (evalP q x).
Proof.
move => p q x.
elim: p q => // [q |a s Hrec q].
  elim: q => // [|a s _]; (by rewrite plus0l).
elim: q Hrec => // [Hrec |b u Hrec2 Hrec] /=; first (by rewrite plus0r).
move: (Hrec u) => ->.
by rewrite plus_multl plusA -!plusA ![b + _]plusC -plusA.
Qed.

Lemma evalP_multPX : forall p x, evalP (Xp p) x = x * (evalP p x).
Proof. elim => //= * ; [by rewrite mult0r| by rewrite plus0l]. Qed.

Lemma evalP_multPR : forall p c x, (x * c = c * x) -> 
  evalP (c sp p) x = c * (evalP p x).
Proof. 
elim => //= [|a p1 Hrec c x H]; first (by move=> *; rewrite mult0r).
by rewrite Hrec //= multA H plus_multl multA.
Qed.

Lemma evalP_multRP : forall p c x, evalP (p ps c) x = (evalP p x) * c.
Proof. 
elim => //= [|a p1 Hrec c x]; first (by move=> *; rewrite mult0l).
by rewrite Hrec //= multA plus_multr.
Qed.

Lemma evalP_multP : forall p q x, (com_coeff p x) ->
  evalP (p ** q) x = (evalP p x) * (evalP q x).
Proof.
move => p q x Hp.
elim: p q Hp => //[|a p1 Hrec q Hp];
  first (by move=> *; rewrite //= mult0l).
elim: q p1 Hp Hrec => //[|b q1 Hrec2 p1 Hp Hrec]; 
  first (by move=> *; rewrite //= mult0r).
rewrite adds_multr // evalP_plusP evalP_multPX.
move: (Hrec2 p1) => -> //=.
rewrite evalP_multRP.
rewrite !plus_multl !plus_multr plus_multl !multA; congr plus.
congr plus; rewrite //= in Hp; 
  first (by elim: (andP Hp) => H1 _; move/eqtype.eqP: H1 => ->).
congr mult; rewrite -!multA; congr mult.
by apply: evalP_com_coeff; elim: (andP Hp).
Qed.

Lemma evalP_11 : forall x, evalP 11 x = 1.
Proof. by rewrite //= => *; rewrite mult0r plus0r. Qed.

Lemma evalP_eqP0 : forall p x, eqP0 p -> evalP p x = 0.
Proof.
move => p x H.
elim: p H => //= [a p1 Hrec H].
move/andP: H => H; elim: H => H1 H2; move/eqtype.eqP: H1 => <-.
move: (Hrec H2) => ->.
by rewrite mult0r plus0l.
Qed.

Lemma evalP_eqP : forall p q x, (p == q) -> evalP p x = evalP q x.
Proof.
move => p q x H.
elim: p q H => // [q H| a p1 Hrec q H].
by move: (evalP_eqP0 x H) => ->.
elim: q p1 Hrec H => //= [p1 Hrec H|b q1 _ p1 Hrec H];
  move/andP: H => H; elim: H => H1 H2; move/eqtype.eqP: H1 => <-.
  move: (evalP_eqP0 x H2) => ->; by rewrite mult0r plus0l.
by move: (Hrec q1 H2) => ->.
Qed.

(*
Lemma com_coeff_multP_rev : forall p p1 p2 x,
  (com_coeff p x) -> (com_coeff p1 x) -> (p == p1 ** p2) -> ~~ eqP0 p1 -> 
     (com_coeff p2 x).
Proof.
move => p p1 p2.
elim: p1 p p2 => // [a1 s1 Hrec].
elim: s1 Hrec => // [Hrec| a2 s2 Hrec2 Hrec].
move => p p2 x Hp H1 H2 H3.
move/com_coeffP: Hp => Hp.
move/com_coeffP: H1 => H1.
rewrite //= andbT in H3.
rewrite adds_multl //= in H2.
apply/com_coeffP => y Hy.
move: (Hp (a1*y)) => H4.

rewrite // in H2.

move => a1 s1 Hrec p p2 x Hp Hp1 H1 H2.
elim: s1 Hrec
elim: p Hp H1 => // [Hp H1| a s Hrec1 Hp H1].


rewrite //= in Hp1; elim: (andP Hp1) => H3 H4.
clear Hp1.
rewrite //= in H2.
move: (nandP H2) => H5; clear H2.
elim: H5 => H5.
apply: Hrec => //=.

apply: Hrec => //.

  move=> p1; elim: p1 => // [a1 s1 Hrec1].
  move=> p2 x H1 H2 H3 H4 .

  apply: Hrec1 => //.
  rewrite //= in H4.
  
  move=> p2; elim: p2 s1 Hrec1 => // [a2 s2 Hrec2 s1 Hrec1].
  move=> x H1 H2 H3 H4.
  apply: Hrec1 => //=.
  Focus 2.
  rewrite adds_multl in H3.


  move/com_coeffP: H2 => H2.
  apply/com_coeff

  rewrite //= in H3; rewrite //= in H4.

move => p p1 p2 x Hp Hp1 H1 H2.
move/com_coeffP: Hp => Hp; move/com_coeffP: Hp1 => Hp1.
apply/com_coeffP.
elim: p p1 p2 Hp H1 H2 => //= [Hp H1 H2| a1 s1 Hrec1 Hp H1 H2].
elim: p1 Hp1 H1 H2 => // [a1 s1 Hrec2 Hp1 H1 H2] //=.
elim: p2 Hrec2 H1 => //.
move=> x0 s Hrec3 H1 H3 y Hy.
rewrite //= in H3.
rewrite //= in H2.
apply: Hrec3 => //.
apply: Hp => //=.
elim: p2 p1 Hrec1 Hp Hp1 H => // [p1 Hrec1 Hp Hp1 H| a2 s2 Hrec2 p1 Hrec1 Hp Hp1 H] //=.


elim: p2 H => // [a2 s2 Hrec2 H] //=.
elim: p2 p1 Hrec1 Hp Hp1 H => // [p1 Hrec1 Hp Hp1 H| a2 s2 Hrec2 p1 Hrec1 Hp Hp1 H] //=.

elim: p2 H => //= [a2 s2  Hrec2]; rewrite adds_multr.
rewrite eqP0_plus //=.



Qed.
*)

Lemma factor_th : forall p p1 x,
  (com_coeff p x) -> p == (Adds (- x) (Adds 1 seq0)) ** p1 -> evalP p x = 0.
Proof.
move => p p1 x Hp.
set Xx :polynomial := (Seq (- x) 1); move => H.
have HXx : com_coeff Xx x.
  rewrite //=.
  apply/and3P; split => //=; last (by rewrite mult1l mult1r).
  apply/eqtype.eqP.
  by rewrite -(plus0r (- x * x)) -(plus0r (x * - x)) -(plus_opr (x * x)) 
      !plusA -plus_multr -plus_multl !plus_opl mult0r mult0l !plus0l.
move: (evalP_eqP x H) => ->.
move: (evalP_multP p1 HXx) => ->.
by rewrite //= mult0r plus0r mult1r plus_opl mult0l.
Qed.


End MorphismEvaluation.

End Polynomial.

End Polynomials.

Section PolyNorm.
Open Scope rings_scope.
Variable R : ringsType.

Notation "00" := (@Seq0 R: (polynomial R)) (at level 0): local_scope.

Record polyNorm: Type := PolyNorm {
  poly :> (polynomial R);
  normP : normal poly
}.

(*
Lemma can_poly : forall m n, cancel poly PolyNorm.
Proof. move => m n; by rewrite /cancel; case => /=. Qed.

Lemma mval_inj : forall m n, injective (@mval m n). 
Proof. move => m n; exact: can_inj (@can_mval m n). Qed.
*)
Lemma toto : forall p: (polynomial R), p <> 00 -> (eqP0 p) -> ~ normal p.
Proof.
move=> p H1 H2.
elim: p H1 H2 => //= [a s Hrec H1 H2].
rewrite / normal //=; apply/idP; apply/eqtype.eqP; clear Hrec H1.
elim: s H2 => //= [|a1 s1 Hrec1 H2]; first (by rewrite andbT=> H1; rewrite -(eqtype.eqP H1)).
move/and3P: H2 => H2; elim: H2=> H2 H3 H4; move/eqtype.eqP: H2 => H2; move/eqtype.eqP: H3 => H3.
rewrite -H2 in Hrec1; rewrite -H3; apply: Hrec1; apply/andP; split=> //=.
Qed.

Lemma eqPP : reflect_eq (fun (p1 p2 : polyNorm) => (eqP p1 p2)).
Proof.
move; elim=> //= [[|x1 s1] N1] [[|x2 s2] N2] //=; apply: (iffP idP) => //=.
(* 1 *) by move=> _ //=; rewrite /= (eq_irrelevance N1 N2).
(* 2 *) move=> H1; have H2: eqP0 (Adds x2 s2) by rewrite //=.
          have H3: (Adds x2 s2) <> 00 by rewrite //=. 
          by move: (toto H3 H2) => *.
(* 3 *) move=> H1; have H2: eqP0 (Adds x1 s1) by rewrite //=.
          have H3: (Adds x1 s1) <> 00 by rewrite //=. 
          by move: (toto H3 H2) => *.
(* 4 *) move=> H1 //=; elim: (andP H1); clear H1=> H1 H2; move: (normal_inv N1) (normal_inv N2)=> H3 H4.
          move: (normal_eq H3 H4 H2) => H5; move/eqtype.eqP: H1 => H1.
          move: N1 N2; rewrite H5 H1 => N1 N2; by rewrite /= (eq_irrelevance N1 N2).
(* 5 *) move=> H1; have H2: (eqP (PolyNorm N1) (PolyNorm N2)) by rewrite H1 eqP_refl.
          move: (normal_eq N1 N2 H2)=> //=.
Qed.

Canonical Structure polyNormET := EqType eqPP.

Definition plusPn (p1 p2 :polyNorm) : polyNorm := (PolyNorm (norm_normal (plusP p1 p2))).

Definition multPn (p1 p2 :polyNorm) : polyNorm := (PolyNorm (norm_normal (multP p1 p2))).

Definition opPn (p1 :polyNorm) : polyNorm := (PolyNorm (norm_normal (opP p1))).

Notation "\00n" := (PolyNorm (normal0 R)) (at level 0): local_scope.

Notation "\11n" := (PolyNorm (normal1 R)) (at level 0): local_scope.

Lemma multPn0 : forall p : polyNorm, multPn \00n p = \00n.
Proof. move=> p //=.
rewrite / multPn //=.
(* Set Printing All. *)
congr PolyNorm; apply: eq_irrelevance.
Qed.

Lemma plusPn0l : forall p:  polyNorm, plusPn \00n p = p.
Proof. by move=> p //=; apply/eqPP => //=; apply: norm_eq. Qed.

(* 
Lemma plusPn0r: forall p:  polyNorm, plusPn p \00n = p.
Proof. by move=> p //=; apply/eqPP => //=; rewrite plusP0r; apply: norm_eq. Qed.
*)

Lemma plusPnC : forall p q : polyNorm,  plusPn p q = plusPn q p.
Proof.
move=> p q //=.
by apply/eqPP => //=; rewrite plusPC eqP_refl.
Qed.

Lemma plusPnA: forall p q r :polyNorm,
  plusPn p (plusPn q r) = plusPn (plusPn p q) r.
Proof.
move=> p q r //=.
apply/eqPP => //=.
have H1: (eqP (norm (plusP p (norm (plusP q r)))) (plusP p (norm (plusP q r))) ).
  apply: norm_eq.
rewrite (eqP_trans H1) //=.
have H2: (eqP (norm (plusP (norm (plusP p q)) r)) (plusP (norm (plusP p q)) r) ).
  apply: norm_eq.
rewrite eqP_sym //= (eqP_trans H2) //=.
have H3: eqP (plusP p (norm (plusP q r))) (norm (plusP p (plusP q r))). 
apply: norm_plusP.
rewrite eqP_sym // (eqP_trans H3) //= -plusPA eqP_sym //.
rewrite [plusP (plusP p q) r]plusPC plusPC.
apply: norm_plusP.
Qed.

Lemma plusPn0p: forall p :polyNorm, plusPn p (opPn p) = \00n.
Proof.
move => p; apply/eqPP => //=. 
rewrite (eqP_trans (norm_eq _)) // (eqP_trans (norm_plusP _ _)) //
  (eqP_trans (norm_eq _)) // (eqP_trans (plusP0pr _)) //.
Qed.

Lemma multPn1l : forall p : polyNorm, multPn \11n p = p.
Proof.
move=> p //=.
rewrite / multPn // multP1.
apply/eqPP => //=.
apply: norm_eq.
Qed.

Lemma multPn1r : forall p : polyNorm, multPn p \11n = p.
Proof.
move=> p //=.
apply/eqPP => //=.
rewrite multP1r; apply: norm_eq.
Qed.

Lemma multPnA: forall p q r :polyNorm, 
  multPn p (multPn q r) = multPn (multPn p q) r.
Proof.
Admitted.

Lemma plusPn_multPnr: forall p q r :polyNorm, 
  multPn (plusPn p q) r = plusPn (multPn p r) (multPn q r).
Proof.
Admitted.

Lemma plusPn_multPnl: forall p q r :polyNorm, 
  multPn p (plusPn q r) = plusPn (multPn p q) (multPn p r).
Proof.
Admitted.

Definition polyNormRings : ringsType.
exists polyNormET \00n \11n plusPn multPn opPn.
(* 1 *) move=> x; apply: plusPn0l.
(* 2 *) move=> x; rewrite plusPnC; apply: plusPn0p.
(* 3 *) apply: (plusPnA).
(* 4 *) apply: plusPnC.
(* 5 *) apply: multPn1l.
(* 6 *) apply: multPn1r.
(* 7 *) apply: multPnA.
(* 8 *) apply: plusPn_multPnl.
(* 9 *) apply: plusPn_multPnr.
rewrite //=.
Defined.

End PolyNorm.

Section Cayley.

Variable R : comRings.

Open Scope rings_scope.

Notation "\P[x]" := (polynomial R) : local_scope.

Notation "'M_' ( n )" := (matrix R n n)
  (at level 9, m, n at level 50, format "'M_' ( n )") : local_scope.


Section MatrixPoly.

Section MatrixOfPoly.

Open Scope local_scope.

Definition matrix_of_polynomial (n :nat) := (matrix (polyNormRings R) n n).

Notation "'\M_(x)_' ( n )" := (matrix_of_polynomial n)
  (at level 9, m, n at level 50, format "'\M_(x)_' ( n )") : local_scope.

(* ---- STOP ---- *)

Definition mx_to_mx_of_poly (n :nat) (A :M_(n)): \M_(x)_( n ) := 
   matrix_of_fun (fun i j => (PolyNorm (R_to_poly_normal (A i j)))).

Lemma inj_mx_to_mx_of_poly : forall n, injective (@mx_to_mx_of_poly n).
Proof.
Admitted.

(* Operation for Matrix of Poly *)
Notation "'11'" :=  ((Adds 1 seq0) : \P[x] ) (at level 0): local_scope.
Notation "00" := (@Seq0 R: \P[x] ) (at level 0): local_scope.
Notation "x1 '++' x2" := (plusP plus x1 x2) (at level 50) : local_scope.
Notation "x1 '=p' x2" := (eqP zero x1 x2) (at level 70) : local_scope.
Notation "'--' x" := (opP opp x) (at level 10) : local_scope.
Notation "'Xp' x" := (multPX zero x) (at level 40) : local_scope.
Notation "c 'sp' x" := (multRPl mult c x) (at level 40) : local_scope.
Notation "x 'ps' c" := (multRPr mult c x) (at level 40) : local_scope.

Definition plusMP := matrix_plus (@plusP R ).
Notation "x1 '+mp' x2" := (plusMP x1 x2) (at level 50) : local_scope.

Definition multMP := (matrix_mul (@multP R) (@plusP R) 00).
Notation "x1 '*mp' x2" := (multMP x1 x2) (at level 50) : local_scope.

Definition unitMP (n :nat) : \M_(x)_(n) := (unit_matrix 00 11 n).
Notation "'\1mp_' ( n )" := (unitMP n)
  (at level 0, format "'\1mp_' ( n )") : local_scope.

Definition scaleMP := (matrix_scale (@multP R)).
Notation "x '*smp' A" := (scaleMP x A) (at level 40) : local_scope.

Definition adjugateMP := (adjugate (@plusP R) (@multP R) (@opP R) 00 11).

(* ---- *)

Notation "'X'" := ((Adds 1 00) : \P[x] ) (at level 0): local_scope.

Definition x_I n : \M_(x)_(n) := 
  (@matrix_of_fun \P[x] n n (fun i j => (if i == j then X else 00 ))).

Definition det_MP := determinant (@plusP R) (@multP R) (@opP R) 00 11.

Definition poly_car (n :nat) (A :M_(n)) : \P[x] :=
  det_MP ((x_I n) +mp (mx_to_mx_of_poly (matrix_scale mult (-1) A))).


Lemma mult_adugateR_MP : forall n (A : \M_(x)_(n)), A *mp adjugateMP A = det_MP A *smp \1mp_(n).
Proof.

Admitted.

End MatrixOfPoly.

Section PolyOfMatrix.
Open Scope local_scope.

Definition mx_n_type n := (matrix_eqType R n n).
Notation "'\M_' ( n )" := (mx_n_type n) 
  (at level 9, m, n at level 50, format "'\M_' ( n )") : local_scope.

Definition polynomial_of_matrix (n :nat) := (@polynomial \M_(n)).

Notation "'\M_[x]_' ( n )" := (polynomial_of_matrix n)
  (at level 9, m, n at level 50, format "'\M_[x]_' ( n )") : local_scope.

(* Operation for Poly of Matrix *)
Notation "'\1m_' ( n )" := (unit_matrix 0 1 n)
  (at level 0, format "'\1m_' ( n )") : local_scope.
Notation "'\0m_' ( n )" := (null_matrix 0 n n)
  (at level 0, format "'\0m_' ( n )") : local_scope.
Notation "A '+m' B" := (matrix_plus plus A B) (at level 50) : local_scope.
Notation "x '*sm' A" := (matrix_scale mult x A) (at level 40) : local_scope.
Notation "A '*m' B" := (matrix_mul plus mult 0 A B) (at level 40) : local_scope.

Definition plusPM (n :nat) : \M_[x]_(n) -> \M_[x]_(n) -> \M_[x]_(n) := plusP (@matrix_plus _ plus n n).
Notation "x1 '+pm' x2" := (plusPM x1 x2) (at level 50) : local_scope.

Definition multPM (n :nat) : \M_[x]_(n) -> \M_[x]_(n) -> \M_[x]_(n) :=
  multP (@matrix_plus _ plus n n) (@matrix_mul _ plus mult 0 n n n) \0m_(n).
Notation "x1 '*pm' x2" := (multPM x1 x2) (at level 50) : local_scope.

Definition unitPM (n: nat) : \M_[x]_(n) := (Adds (@unit_matrix _ 0 1 n) seq0).
Notation "'\1pm_' ( n )" := (unitPM n)
  (at level 0, format "'\1pm_' ( n )") : local_scope.

Definition zeroPM (n: nat) : \M_[x]_(n) := (@Seq0 \M_(n)).
Notation "'\0pm_' ( n )" := (zeroPM n)
  (at level 0, format "'\0pm_' ( n )") : local_scope.

Definition multXPM (n :nat) : \M_[x]_(n) -> \M_[x]_(n) :=(multPX \0m_(n)).
Notation "'Xpm' x" := (multXPM x) (at level 40) : local_scope.

(* --- *)

Definition R_to_mx (n :nat) (x :R) : M_(n) := (x *sm \1m_(n)).

Definition poly_to_poly_of_mx (n :nat) (p : \P[x]) : \M_[x]_(n):= 
  maps (R_to_mx n) p .

Lemma inj_poly_to_poly_of_mx : forall n, injective (poly_to_poly_of_mx n).
Proof.

Admitted.

End PolyOfMatrix.

Notation "'\M_' ( n )" := (mx_n_type n) 
  (at level 9, m, n at level 50, format "'\M_' ( n )") : local_scope.

Notation "'\M_(x)_' ( n )" := (matrix_of_polynomial n)
  (at level 9, m, n at level 50, format "'\M_(x)_' ( n )") : local_scope.
Notation "'\M_[x]_' ( n )" := (polynomial_of_matrix n)
  (at level 9, m, n at level 50, format "'\M_[x]_' ( n )") : local_scope.

Notation "x1 '+mp' x2" := (plusMP x1 x2) (at level 50) : local_scope.
Notation "x1 '*mp' x2" := (multMP x1 x2) (at level 50) : local_scope.
Notation "'\1mp_' ( n )" := (unitMP n)
  (at level 0, format "'\1mp_' ( n )") : local_scope.
Notation "x '*smp' A" := (scaleMP x A) (at level 40) : local_scope.
Notation "x1 '+pm' x2" := (plusPM x1 x2) (at level 50) : local_scope.
Notation "x1 '*pm' x2" := (multPM x1 x2) (at level 50) : local_scope.
Notation "'\1pm_' ( n )" := (unitPM n)
  (at level 0, format "'\1pm_' ( n )") : local_scope.
Notation "'\0pm_' ( n )" := (zeroPM n)
  (at level 0, format "'\0pm_' ( n )") : local_scope.

Notation "'\0m_' ( n )" := (null_matrix 0 n n)
  (at level 0, format "'\0m_' ( n )") : local_scope.

Notation "'\1m_' ( n )" := (unit_matrix 0 1 n)
  (at level 0, format "'\1m_' ( n )") : local_scope.

Notation "'Xpm' x" := (multXPM x) (at level 40) : local_scope.

(* Definition plusPM : *)


Variable (n :nat) (phi : \M_(x)_(n) -> \M_[x]_(n)).
Hypothesis phi_iso : bijective phi.
Hypothesis phi_plus : forall Ax Bx, phi (Ax +mp Bx) = (phi Ax) +pm (phi Bx).
Hypothesis phi_mult : forall Ax Bx, phi (Ax *mp Bx) = (phi Ax) *pm (phi Bx).
Hypothesis phi_one : (phi \1mp_(n)) = \1pm_(n).

Definition evalPM : \M_[x]_(n) -> (mx_n_type n) -> (mx_n_type n) :=
  evalP (@matrix_plus R plus n n) (@matrix_mul R plus mult 0 n n n) \0m_(n).

Lemma factor_th_PM : forall (p p1 :polynomial (matrix_eqType R n n)) A,
  (com_coeff (@matrix_mul R plus mult 0 n n n) p A) -> 
    (@eqP _ \0m_(n) p ((Adds (@matrix_scale R mult n n (-1) A) (Adds \1m_(n) seq0)) *pm p1)) ->
        evalPM p A = \0m_(n).
Proof.
(* Check (@matrix_plus R plus n n).
Check (@matrix_mul R plus mult 0 n n n). *)
pose oppM := (@matrix_scale R mult n n (-1)).
(* Check \0m_(n).
Check \1m_(n). *)
pose HF := (@factor_th (matrix_eqType R n n) (@matrix_plus R plus n n) 
(@matrix_mul R plus mult 0 n n n) oppM \0m_(n) \1m_(n)).
rewrite / evalPM / mx_n_type.
move => p p1 A Hp H.
apply: (HF _ _ _ _ _ _ _ _ _ _ _ _ _ _ p p1 A _ H); rewrite //=.
move=> a; rewrite matrix_plusC; last (exact: plusC); apply: matrix_plus0x; exact: plus0l.
move => a; apply: matrix_plus0x; exact: plus0l.
apply: matrix_plusC; exact: plusC.
symmetry; apply: matrix_plusA; symmetry; exact: plusA.
apply: matrix_scale_oppr => //=.
apply: matrix_scale_oppl => //=.
apply: matrix_mult0rx => //=.
apply: matrix_mult0lx => //=.
apply: matrix_distrR => //=.
move => a b c; apply: matrix_distrL => //=.




(* 
move => a; rewrite / oppM //= / matrix_plus / matrix_scale / null_matrix.
apply/matrix_eqP.
unlock matrix_of_fun.
rewrite / matrix_eq.
move => i j.

apply: (@matrix_plusA R plus n n n a b c). exact: plusC. *)

Admitted.


Theorem Cayley_Hamilton : forall A : M_(n), 
  evalPM (poly_to_poly_of_mx n ( poly_car A)) A = \0m_(n).
Proof.

Admitted.


End MatrixPoly.


