Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple
 indexed_products div groups determinantET rings.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope local_scope with loc.
Open Scope local_scope.
Open Scope rings_scope.

Section Polynomial.

Variable R : ringsType.

(* A polynomial is a sequence, the first element of the sequence is the monome 
  of degree 0*)
Definition polynomial := seq R.

Section PolynomialOp.

Fixpoint plusP (p q: polynomial) {struct p}: polynomial := 
  if p is (Adds a p') then 
    if q is (Adds b q') then Adds (a + b) (plusP p' q') (* (plusPnn p' q')  *)
    else p
  else q.

Definition eqP0 (p: polynomial) : bool :=
  all (set1 0) p.

Fixpoint eq_P (p q: polynomial) {struct p}: bool :=
  if p is (Adds a p') then
    if q is (Adds b q') then (a == b) && (eq_P p' q') 
   else eqP0 p 
  else eqP0 q.

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


(* 
Multiplication
*)
Fixpoint multP (p q : polynomial) {struct p} : polynomial :=
  if p is (Adds a p') then 
    if q is (Adds b q') then 
       Adds (a * b) (plusP (multRPl a q') (plusP (multRPr b p') (multPX (multP p' q'))))
    else (@Seq0 R: polynomial) 
  else (@Seq0 R: polynomial).

End PolynomialOp.

(* 
Work on notations.
*)

Delimit Scope poly_scope with P.
Bind Scope poly_scope with polynomial.

Notation "'11'" :=  (Adds 1 seq0) (at level 0): poly_scope.
Notation "00" := (@Seq0 R: polynomial) (at level 0): poly_scope.
Notation "x1 '++' x2" := (plusP x1 x2) (at level 50) : poly_scope.
Notation "x1 '==' x2" := (eq_P x1 x2) (at level 70) : poly_scope.
Notation "'--' x" := (opP x) (at level 10) : poly_scope.
Notation "'Xp' x" := (multPX x) (at level 40) : poly_scope.
Notation "c 'sp' x" := (multRPl c x) (at level 40) : poly_scope.
Notation "x 'ps' c" := (multRPr c x) (at level 40) : poly_scope.
Notation "x1 '**' x2" := (multP x1 x2) : poly_scope.

Section PolynomialProp.
Open Scope poly_scope.

Lemma multP0 : forall p : polynomial, 00 ** p = 00.
Proof. move => p; elim: p => [|x s Hrec] //=. Qed.

Lemma plusP0l : forall p: polynomial, 00 ++ p = p.
Proof. move => p; elim: p => [|x s Hrec] //=. Qed.

Lemma plusP0r: forall p, p ++ 00 = p.
Proof. by move => [|a p1] //. Qed.

Lemma plusPC : forall p q : polynomial,  p ++ q = q ++ p.
Proof. by elim => [| a p1 Hrec] [| b q1] //; rewrite /= plusC Hrec. Qed.

Lemma plusPA: forall p q r, p ++ (q ++ r) = (p ++ q) ++ r.
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
by rewrite -(eqP H3) H1 Hrec.
Qed.

Lemma eqP_trans: forall p q r, p == q -> q == r -> p == r.
Proof.
elim => [|a p Hrec] //=; first exact: eqP0_trans.
move => [|b q] // [|c r] //=; case/andP => H1 H2; 
                              case/andP => H3 H4.
  by rewrite -(eqP H1) H3 (Hrec 00) // eqP0_eqP.
 -by rewrite (eqP H1) H3 (eqP0_trans H4) // eqP_sym.
by rewrite (eqP H1) H3 (Hrec _ _ H2).
Qed.

Lemma eqP0_plus: forall p q, eqP0 p -> eqP0 q -> eqP0 (p ++ q).
Proof.
elim => [|a p Hrec] // [|b q] //=.
case/andP => H1 H2; case/andP => H3 H4.
by rewrite -(eqP H1) plus0l H3 Hrec.
Qed.

Lemma eqP0_eqP_plusl: forall p q, eqP0 p -> q == p ++ q.
Proof.
elim => [|a p Hrec] // [|b q] //=.
  by rewrite eq_refl eqP_refl.
case/andP => H1 H2.
by rewrite -(eqP H1) plus0l eq_refl Hrec.
Qed.

Lemma eqP0_eqP_plusr: forall p q, eqP0 p -> q == q ++ p.
Proof.
elim => [|a p Hrec] // [|b q] //=.
  by rewrite eq_refl eqP_refl.
case/andP => H1 H2.
by rewrite -(eqP H1) plusC plus0l eq_refl Hrec.
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
  rewrite (@eqP_trans _ (Adds a2 p2)) //; last by rewrite /= eq_refl eqP_refl.
  by rewrite (eqP_trans _ H1) // eqP_sym // eqP0_eqP_plusr.
rewrite /=; case/andP => H1 H2; case/andP => H3 H4.
by rewrite (eqP H1) (eqP H3) Hrec // eq_refl.
Qed.

Lemma plusP0pr: forall p, p ++ (-- p) == 00.
Proof.
move => p; apply: eqP0_eqP. 
by elim p => [| a p1 Hrec] //; rewrite /= Hrec plus_opr eq_refl.
Qed.

Lemma plusP0pl: forall p, (--p) ++ p == 00.
Proof.
by move => p; rewrite plusPC; apply: plusP0pr.
Qed.

Lemma eqP0_opp: forall p, eqP0 p -> eqP0 (-- p).
Proof.
elim => [|a p] //=.
by move => H; case/andP => H1 H2; rewrite H // -(eqP H1) opp0 eq_refl.
Qed.

Lemma eqP_opp: forall p q, p == q -> -- p == -- q.
Proof.
elim => [|a p Hrec] //.
  exact: eqP0_opp.
move => [|b q] //=.
  by exact: (@eqP0_opp (Adds a p)).
by case/andP => H1 H2; rewrite (eqP H1) eq_refl Hrec.
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
by case/andP => H1 H2; rewrite -(eqP H1) mult0r eq_refl Hrec.
Qed.

Lemma eqP0_multRPl0: forall p, eqP0 (0 sp p).
Proof.
by elim => [|a p Hrec] //=; rewrite mult0l eq_refl Hrec.
Qed.

Lemma eqP_multRPl: forall c p q, p == q -> c sp p == c sp q.
Proof.
move => c; elim => [| a p Hrec] //=.
  exact: eqP0_multRPl.
move => [|b q] /=; case/andP => H1 H2; rewrite -(eqP H1).
  by rewrite mult0r eq_refl eqP0_multRPl.
by rewrite eq_refl Hrec.
Qed.

Lemma multRPl_multPX: forall c p, Xp (c sp p) = c sp (Xp p).
Proof.
by move => c [| a p] //=; rewrite mult0r.
Qed.

Lemma multRPl_plusl: forall c1 c2 p, (c1 + c2) sp p = (c1 sp p) ++ (c2 sp p).
Proof. 
by move => c1 c2; elim => [|a p Hrec] //=; rewrite plus_multr Hrec.
Qed.

Lemma multRPl_plusr: forall c p q, c sp (p ++ q) = (c sp p) ++ (c sp q).
Proof.
by move => c; elim => [|a p Hrec] //= [|b q] //=; rewrite plus_multl Hrec.
Qed.

Lemma eqP0_multRPr: forall c p, eqP0 p -> eqP0 (p ps c).
Proof.
move => c; elim => [|a p Hrec] //=.
by case/andP => H1 H2; rewrite -(eqP H1) mult0l eq_refl Hrec.
Qed.
 
Lemma eqP0_multRPr0: forall p, eqP0 (p ps 0).
Proof.
by elim => [|a p Hrec] //=; rewrite mult0r eq_refl Hrec.
Qed.

Lemma eqP_multRPr: forall c p q, p == q -> p ps c == q ps c.
Proof.
move => c; elim => [| a p Hrec] //=.
  exact: eqP0_multRPr.
move => [|b q] /=; case/andP => H1 H2; rewrite -(eqP H1).
  by rewrite mult0l eq_refl eqP0_multRPr.
by rewrite eq_refl Hrec.
Qed.

Lemma multRPr_multPX: forall c p, Xp (p ps c) = (Xp p) ps c.
Proof.
by move => c [| a p] //=; rewrite mult0l.
Qed.

Lemma multRPr_plusl: forall c1 c2 p, p ps (c1 + c2) = (p ps c1) ++ (p ps c2).
Proof.
move => c1 c2; elim => [|a p Hrec] //=.
by rewrite plus_multl Hrec.
Qed.

Lemma multRPr_plusr: forall c p q, (p ++ q) ps c = (p ps c) ++ (q ps c).
Proof.
by move => c; elim => [|a p Hrec] //= [|b q] //=; rewrite plus_multr Hrec.
Qed.

Lemma eqP0_multPl: forall (p q: polynomial), eqP0 p -> eqP0 (p ** q).
Proof.
elim => [|a p Hrec] //= [|b q] //=; case/andP => H1 H2.
rewrite -(eqP H1) mult0l eq_refl !eqP0_plus ?eqP0_multRPl0 ?eqP0_multRPr //=.
by rewrite eqP0_multPX // Hrec.
Qed.

Lemma eqP0_multPr: forall (p q: polynomial), eqP0 p -> eqP0 (q ** p).
Proof.
elim => [|a p Hrec] [|b q] //=; case/andP => H1 H2.
 rewrite -(eqP H1) mult0r eq_refl !eqP0_plus ?eqP0_multRPl ?eqP0_multRPr0 //=.
by rewrite eqP0_multPX // Hrec.
Qed.

Lemma eqpP_mult: forall p1 p2 q1 q2, 
  p1 == p2 -> q1 == q2 -> (p1 ** q1) == (p2 ** q2).
Proof.
elim => [|a1 p1 Hrec].
  by move => p1 q1 q2 H1 H2; rewrite /= eqP0_multPl.
move => [|a2 p2].
  move => q1 q2 H1 H2.
  by rewrite (@eqP_trans _ 00) ?eqP0_multPl // eqP_sym // /eq_P eqP0_multPl.
move => [|b1 q1].
  by move => q2 H1 H2; rewrite (@eqP_trans _ 00) // /eq_P eqP0_multPr.
move => [|b2 q2].
  by move => H1 H2; rewrite (@eqP_trans _ 00) // eqP_sym // /eq_P eqP0_multPr.
case/andP => H1 H2; case/andP => H3 H4.
by rewrite /= (eqP H1) (eqP H3) eq_refl !eqP_plus
           ?eqP_multPX ?Hrec ?eqP_multRPr ?eqP_multRPl // eq_refl.
Qed.

Lemma multP0l: forall p, 00 ** p = 00.
Proof. done. Qed.

Lemma multP0r: forall p, p ** 00 = 00.
Proof. by case. Qed.

Lemma multRPrlC: forall a b p, a sp (p ps b) = (a sp p) ps b.
move => a b; elim => [|c  p Hrec] //=.
by rewrite multA Hrec.
Qed.

(* commutation property *)

Fixpoint com_coeff (p :polynomial) (x :R) {struct p} : bool := 
  (if p is (Adds a p') then (a * x == x * a)%EQ && (com_coeff p' x) else true).

Lemma com_coeffP : forall p x, 
  reflect (forall y, (mem p) y -> x * y = y * x) (com_coeff p x).
Proof. 
move => p x.
apply: (iffP idP) => H; first (elim: p H => //= x0 s Hrec H y Hy).
  case Hx: (x0==y)%EQ; case/andP: H => //=.
    by move/eqP: Hx => <-; move=> HH _; move/eqP: HH => HH.
  by move => _ HH; apply: Hrec => //; case/orP: Hy => HT //; rewrite Hx in HT.
elim: p H => //= [a s Hrec H]; rewrite /setU1 in H.
by rewrite (H a) eq_refl // Hrec //= => y Hy; apply H; rewrite Hy orbT.
Qed.

Lemma multRPrl: forall a p, com_coeff p a -> p ps a = a sp p.
Proof.
move => b; elim => //= [a  p Hrec H].
by case/andP: H => H1 H2; move/eqP: H1 => ->; congr Adds; apply: Hrec.
Qed.

Lemma multPC:
  forall p q, (forall x, mem p x -> com_coeff q x) -> p ** q = q ** p.
Proof.
elim => //= [|a p Hrec] //= [|b q H] //=.
move: (H a); rewrite // / setU1 eq_refl //= => H1.
move: (H1 is_true_true); move: H1 => _ H1.
rewrite Hrec; first last.
  move=> x Hx; move: (H x) => //=; rewrite /setU1 Hx orbT => H2.
  case/andP: (H2 is_true_true) => //=.
rewrite !multRPrl; first(case/andP: H1 => HH _; rewrite (eqP HH);
congr Adds; rewrite plusPC -plusPA; congr plusP; by rewrite plusPC).
  by case/andP: H1.
clear H1 Hrec; rewrite //= in H.
elim: p H => //= [s p0 Hrec H].
apply/andP; split; last (apply: Hrec).
  move: (H s) => //=; rewrite / setU1 //= eq_refl orbT eq_sym => H1;
      move: (H1 is_true_true); move/andP => H2; by elim: H2.
move=> x Hx; apply: H; move: Hx; rewrite / setU1 //=.
by case/orP => -> //=; rewrite ?orbT.
Qed.


Lemma multRPl_multl: forall c1 c2 p, (c1 * c2) sp p = c1 sp (c2 sp p).
Proof.
by move => c1 c2; elim => [|a p Hrec] //=; rewrite multA Hrec.
Qed.

Lemma multRPl_multr: forall c p q, c sp (p ** q) = (c sp p) ** q.
Proof.
move => c; elim => [|a p Hrec] //= [|b q] //=; rewrite multA; congr Adds.
by rewrite !multRPl_plusr multRPl_multl multRPrlC -Hrec multRPl_multPX.
Qed.

Lemma multRPr_multl: forall c1 c2 p, p ps (c1 * c2) = (p ps c1) ps c2.
Proof.
by move => c1 c2; elim => [|a p Hrec] //=; rewrite multA Hrec.
Qed.

Lemma multRPr_multr: forall c p q, (p ** q) ps c = p ** (q ps c).
Proof.
move => c; elim => [|a p Hrec] //= [|b q] //=; rewrite multA; congr Adds.
by rewrite !multRPr_plusr multRPr_multl multRPrlC -Hrec multRPr_multPX.
Qed.

Lemma plusP_multr: forall p q r, (p ++ q) ** r = (p ** r) ++ (q ** r).
Proof.
elim => [|a p Hrec] // [|b q] //.
  by move => r; rewrite multP0l !plusP0r.
move => [|c r] //=; congr Adds.
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
congr plusP; rewrite Hrec (plusPC (p ps b)) plusPA.
case: (a1 sp _ ++ _) => // [a2 p1].
by rewrite {2}[Adds a2 _]lock /= plus0r plusPC; unlock.
Qed.

Lemma multPX_multl: forall p q, (Xp p) ** q = Xp (p ** q).
Proof.
move => [|a p] // [|b q] //.
change (Xp Adds a p) with (Adds 0 (Adds a p)).
rewrite adds_multl /= plus0r mult0l; congr Adds. 
elim: q (p ps b ++ _) (a * b) => // c r Hrec [| c1 r1] // d.
  by move: (Hrec 00 (a * c)); rewrite /= mult0l plus0l !plusP0r => ->.
by rewrite /= ?Hrec mult0l plus0l.
Qed.

Lemma adds_multr: forall a p q, q ** (Adds a p) = (q ps a) ++ Xp (q ** p).
Proof.
move => a p q; elim: q a p => [|b q Hrec] a.
  by move => p; rewrite !multP0l. 
case => [|a1 p]; first by rewrite multP0r /= multP0r /= !plusP0r.
rewrite {1}[Adds a1 p]lock /=; unlock.
congr Adds; first by rewrite plus0r.
rewrite Hrec plusPC -!plusPA /=; congr plusP.
case: (q ps _ ++ _) => [| a2 p1]; first by rewrite /= plusP0r.
rewrite /multPX [Adds a2 p1]lock [b sp p ++ _]lock /=; unlock.
by rewrite plus0l plusPC.
Qed.

Lemma multPX_multr: forall p q, q ** (Xp p) = Xp (q ** p).
Proof.
move => [|a p] // [|b q] //.
change (Xp Adds a p) with (Adds 0 (Adds a p)).
rewrite adds_multr /= plus0r mult0r; congr Adds; rewrite
  [b sp p ++ _]plusPC -!plusPA.
elim: q (Xp _ ++ _) (b * a) => // c r Hrec [| c1 r1] // d.
  by move: (Hrec 00 (c * a)); rewrite /= mult0r plus0l !plusP0r => ->.
by rewrite /= ?Hrec mult0r plus0l.
Qed.

Lemma multP_sp_ps: forall a p q, (p ps a) ** q = p ** (a sp q).
Proof.
move => c; elim => [|a p Hrec] // [|b q] //=.
by rewrite multA Hrec multRPl_multl multRPr_multl.
Qed.

Lemma multPA: forall p q r, p ** (q ** r) = (p ** q) ** r.
Proof.
elim => [|a p Hrec] // [|b q] // [|c r] //=.
congr Adds => //; first (by rewrite multA).
rewrite -!multPX_multl !multPX_plus !plusP_multl !plusP_multr
  !multRPl_plusr !multRPr_plusr -!plusPA.
congr plusP; first by rewrite multRPl_multl.
congr plusP; first by rewrite multRPrlC.
rewrite plusPC -!plusPA.
congr plusP; first by rewrite multRPr_multl.
rewrite -!multP_sp_ps plusPC -!plusPA.
congr plusP; first  by rewrite multRPr_multr.
rewrite plusPC -!plusPA.
congr plusP; first by rewrite multRPl_multr multRPl_multPX.
congr plusP; first by rewrite -multRPr_multPX.
by rewrite !multPX_multl !multPX_multr Hrec.
Qed.

Lemma multRP1 : forall p, 1 sp p = p.
Proof.
by elim => [|a p Hrec] //=; rewrite mult1l Hrec.
Qed.

Lemma multPR1 : forall p, p ps 1 = p.
Proof.
by elim => [|a p Hrec] //=; rewrite mult1r Hrec.
Qed.

Lemma multP1 : forall p : polynomial, 11 ** p = p.
Proof.
by case => [|a p] //=; rewrite !plusP0r mult1l multRP1.
Qed.

Lemma multP1r : forall p : polynomial, p ** 11 = p.
Proof.
by case => [|a p] //=; rewrite mult1r multP0r //= plusP0r multPR1.
Qed.

Lemma eqP_simpl_plus : forall p q r, p ++ q == p ++ r -> q == r.
Proof.
move=> p q r.
rewrite plusPC => H1.
move: (eqP_plus H1 (eqP_refl (-- p))) => H2.
rewrite -!plusPA in H2.
move: (eqP_sym (eqP_plus (eqP_refl q) (@plusP0pr p))).
clear H1 => H1.
move: (@plusP0pr p) => H3.
move: (eqP_trans H1 H2); clear H1 H2 H3 => H1.
rewrite [r ++ _]plusPC plusPA plusP0r in H1.
move: (eqP_plus (@plusP0pr p) (eqP_refl r)); rewrite plusP0l => H2.
by move: (eqP_trans H1 H2).
Qed.

Lemma eqP_simpl_multPX : forall p q, Xp p == Xp q -> p == q.
Proof.
elim=> //[|a p Hrec].
  elim=> //=[b q Hrec H1];
    by elim: (andP H1) => _.
elim=>//[H1|b q Hrec2 ]; first (by elim: (andP H1) => _).
  rewrite //= => H1; by elim: (andP H1) => _.
Qed.

Lemma multPX_mult : forall p q, (Xp p) ** (Xp q) = Xp (Xp (p ** q)).
Proof.
move=> p q.
by rewrite -multPX_multl -multPX_multr.
Qed.

End PolynomialProp.

Section InjPolynomial.
Open Scope poly_scope.

(* Injection from R to polynomial *)
Definition R_to_poly (x :R) : polynomial := 
  if x!=0 then (Adds x seq0) else seq0.

Lemma inj_R_to_poly : injective R_to_poly.
Proof.
move => x.
case HT:(x==0%R)%EQ; rewrite / R_to_poly HT => //= y;
  case HTT:(y==0%R)%EQ=> //= H; last (move/eqseqP: H=> //=).
  by move/eqP: HT=> ->; move/eqP: HTT => ->.
rewrite andbT => H; by apply/eqP.
Qed.

Lemma R_to_poly_plus: forall x y, 
  R_to_poly (x + y) == (R_to_poly x) ++ (R_to_poly y).
Proof.
move=> x y; rewrite /R_to_poly; case H1:(x==0)%EQ; move/eqP: (H1) => H4.
  by rewrite H4 plus0l //= eqP_refl.
case H2:(y==0)%EQ; move/eqP: (H2) => H3.
  by rewrite H3 plus0r H1 //= eq_refl.
case H5:(x+y==0)%EQ; move/eqP: H5=>H;  by rewrite //= ?H eq_refl.
Qed.

Lemma R_to_poly_mult: forall x y, 
  R_to_poly (x * y) == (R_to_poly x) ** (R_to_poly y).
Proof.
move=> x y; rewrite /R_to_poly; case H1:(x==0)%EQ; move/eqP: (H1) => H3.
  by rewrite H3 mult0l eq_refl //=.
case H2:(y==0)%EQ; move/eqP: (H2) => H4.
  by rewrite H4 mult0r eq_refl //= H1 //=.
case H5:(x*y==0)%EQ; move/eqP: (H5) => H6; by rewrite //= ?H6 eq_refl.
Qed.

(* R_to_poly_iprod *)
Lemma R_to_poly_iprod :
  forall n (f : I_(n) -> R),
    R_to_poly (@iprod R plus 0 I_(n) (setA I_(n)) f) ==
    (@iprod polynomial plusP 00 I_(n) (setA I_(n)) 
               (fun j : I_(n) => R_to_poly (f j))).
Proof.
elim=> // [f|n Hrec].
  by rewrite / R_to_poly // eq_refl.
rewrite -addn1 => f.
move: (iprod_rec R plus 0 (@plusA R) (@plusC R) (@plus0l R) n f) => ->.
move: (iprod_rec _ plusP 00 plusPA plusPC plusP0l n 
           (fun j : I_(n + 1) => R_to_poly (f j))) => ->.
move: (R_to_poly_plus (iprod R plus 0 I_(n) (setA I_(n)) 
         (fun x : I_(n) => f (inj_ord n 1 x))) 
 (f (make_ord (n:=n + 1) (m:=n) (ltn_addn1 n)))) => H1.
rewrite (eqP_trans H1) //; by apply: eqP_plus => //=; apply: eqP_refl.
Qed.

End InjPolynomial.

Section PolynomialDecomposition.
Open Scope poly_scope.
(* Definition of the head and tail of a polynomial *)

Definition head_poly : polynomial -> R :=
  fun p => if p is Adds a p' then a else 0.

Definition tail_poly : polynomial -> polynomial :=
  fun p => if p is Adds a p' then p' else seq0.

Lemma head_tail_prop : forall p,
   p == (R_to_poly (head_poly p)) ++ (Xp tail_poly p).
Proof.
case=> // [|x s]; first by rewrite //= /R_to_poly eq_refl //.
rewrite / head_poly // / tail_poly // /R_to_poly //.
case: s => [|xx ss].
  case H:(x==0)%EQ=> //=; last by rewrite eq_refl.
  by rewrite eq_sym H.
case H:(x==0)%EQ=> //=; by rewrite ?plus0r ?H !eq_refl eqP_refl.
Qed.

Lemma head_poly_plus: 
  forall p q, head_poly (p ++ q) = (head_poly p) + (head_poly q).
Proof.
case=> //[|a p]; first (rewrite //= => q; by rewrite plus0l).
case=> //=; by rewrite plus0r.
Qed.

Lemma tail_poly_plus:
  forall p q, tail_poly (p ++ q) == (tail_poly p) ++ (tail_poly q).
Proof.
case=>//[|a p]; first (rewrite //= => q; by rewrite eqP_refl).
case=> //=[|b q];[rewrite plusP0r|]; by rewrite eqP_refl.
Qed.

Lemma head_poly_multX :
  forall p, head_poly (Xp p) = 0.
Proof. case=>//=; by rewrite eq_refl. Qed.

Lemma tail_poly_multX :
  forall p, tail_poly (Xp p) == p.
Proof. case=> //= *; by rewrite eq_refl eqP_refl. Qed.

Lemma head_poly_multRP :
  forall p c, head_poly (c sp p) = c * (head_poly p).
Proof. case=>//= *; by rewrite mult0r. Qed.

Lemma tail_poly_multRP :
  forall p c, tail_poly (c sp p) == c sp (tail_poly p).
Proof. case=> //= *; by rewrite  eqP_refl. Qed.

Lemma head_poly_multPR :
  forall p c, head_poly (p ps c) = (head_poly p) * c.
Proof. case=>//= *; by rewrite mult0l. Qed.

Lemma tail_poly_multPR :
  forall p c, tail_poly (p ps c) == (tail_poly p) ps c.
Proof. case=> //= *; by rewrite  eqP_refl. Qed.

Lemma head_poly_mult : 
  forall p q, head_poly (p ** q) = (head_poly p) * (head_poly q).
Proof.
case=> //[*|a p]; first by rewrite //= mult0l.
by case=>//=; rewrite mult0r.
Qed.

Lemma head_poly_eqP :
  forall p q, p==q -> head_poly p = head_poly q.
Proof.
case=>//[|x s].
  by case=>//= [xx ss H]; move/andP: H=> H; elim: H => H  _; exact: (eqP H).
case=>//= [H|xx ss H];
  move/andP: H=> H; elim: H => H  _; [symmetry|]; exact: (eqP H).
Qed.

Lemma tail_poly_eqP :
  forall p q, p==q -> tail_poly p == tail_poly q.
Proof.
case=>//[|x s].
  case=>//= [xx ss H]; move/andP: H=> H; elim: H => _ H; exact: H.
case=>//= [H|xx ss H];
  move/andP: H=> H; elim: H => _ H; [by apply: eqP0_eqP| exact: H].
Qed.

Lemma head_poly_iprod :
  forall n (f : I_(n) -> polynomial),
  head_poly (iprod _ plusP 00 I_(n) (setA I_(n)) f) =
  (iprod _ plus 0 I_(n) (setA I_(n)) (fun j : I_(n) => head_poly (f j))).
Proof.
elim=> // [n Hrec].
rewrite -addn1 => f.
move: (iprod_rec _ _ _ plusPA plusPC plusP0l n f) => ->.
move: (iprod_rec _ _ _ (@plusA R) (@plusC R) (@plus0l R) n
          (fun j : I_(n + 1) => head_poly (f j))) => ->.
by rewrite head_poly_plus; congr plus; rewrite
      (Hrec (fun x : I_(n) => f (inj_ord n 1 x))).
Qed.

Lemma R_to_poly_mult_l : forall a p, R_to_poly a ** p == a sp p.
move => a p; rewrite /R_to_poly; case H:(a==0)%EQ. 
  by move/eqP: H=> H; rewrite /= H eqP0_multRPl0.
by case: p => [|b p]; rewrite //= eq_refl plusP0r eqP_refl.
Qed.

Lemma R_to_poly_mult_r : forall a p, p ** R_to_poly a == p ps a.
move => a p; rewrite /R_to_poly; case H:(a==0)%EQ. 
  move/eqP: H=> H; rewrite /= H .
  by elim: p => // [b p Hp]; rewrite /= mult0r eq_refl eqP0_multRPr0.
by elim:p => // [b p Hp]; rewrite /= eq_refl multP0r /multPX plusP0r eqP_refl.
Qed.

Lemma tail_poly_mult : 
  forall p q, tail_poly (p ** q) == ((head_poly p) sp (tail_poly q)) ++ 
    ((tail_poly p) ps (head_poly q)) ++ Xp ((tail_poly p) ** (tail_poly q)).
Proof.
move=> p q.
move: (@head_tail_prop (p ** q)) => H1.
move: (@head_tail_prop p) (@head_tail_prop q)=> Hp Hq.
move: {Hp Hq}(eqpP_mult Hp Hq) =>H2.
move: {H1} (eqP_sym H1) => H1.
move: {H1 H2} (eqP_trans H1 H2) => H3.
rewrite plusP_multr !plusP_multl in H3.
move: (head_poly_mult p q) => H1; rewrite H1 in H3.
move: (R_to_poly_mult (head_poly p) (head_poly q)) => H2.
rewrite -!plusPA  in H3.
move: (eqP_sym (eqP_plus H2 (eqP_refl (Xp (tail_poly (p**q)))))); clear H2=> H2.
move: {H1 H2 H3}(eqP_trans H2 H3) => H1.
move: {H1} (eqP_simpl_plus H1) => H1.
rewrite multPX_mult multPX_multr multPX_multl -!multPX_plus in H1.
apply: {H1}(eqP_trans (eqP_simpl_multPX H1)).
rewrite plusPA.
apply: eqP_plus.
  apply: eqP_plus.
    apply R_to_poly_mult_l.
  apply R_to_poly_mult_r.
apply eqP_refl.
Qed.

End PolynomialDecomposition.

Section Normalization.
Open Scope poly_scope.

(* A pol is normal if its last element is <> 0 *)
Definition normal (p: polynomial) := last 1 p != 0.

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
by apply/negP => H1; case (@one_diff_0 R); apply/eqP.
Qed.

(* 1 is normal *)
Lemma normal1: normal 11.
Proof.
rewrite /normal /=.
by apply/negP => H1; case (@one_diff_0 R); apply/eqP.
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
  elim => [|a p] //= H; first by case/andP; move/eqP => <-.
elim => [|a p Hrec].
  elim => [|b q Hrec] //=.
  move => _ H; case/andP; move/eqP => H1 H2.
  by case/negP: H; rewrite -H1 /=; apply/eqP; apply F1.
case => [|b q H1 H2] //=.
  move => H _; case/andP; move/eqP => H1 H2.
  by case/negP: H; rewrite -H1 /=; apply/eqP; apply F1.
case/andP; move/eqP => -> H3.
by rewrite (Hrec q)  ?(normal_inv H1) ?(normal_inv H2).
Qed.

Lemma norm3_eq:
  forall p q r, (rev q) == (rev r) -> norm3 p q r == cat (rev r) p.
Proof.
elim => [|a p Hrec] q r H1 //=; first by rewrite cats0.
case E1: (a == 0)%EQ.
  rewrite (eqP_trans (Hrec q (Adds a r) _)) //=.
    rewrite rev_adds {H1}(eqP_trans H1) //.
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
by move => p; rewrite /norm (eqP_trans (norm3_eq _ _)) //= eqP_refl.
Qed.

Lemma norm3_normal: forall p q r, normal (rev q) -> normal (norm3 p q r).
Proof.
elim => [|a p Hrec] q r H1 //=.
by case E1: (a == 0)%EQ; rewrite Hrec // /normal rev_adds last_add_last E1.
Qed.

(* Normalizing normalises *)
Lemma norm_normal: forall p, normal (norm p).
Proof.
by move => p; rewrite /norm norm3_normal //; exact: normal0.
Qed.

Lemma normal_norm_eq : forall p, normal p -> norm p = p.
Proof.
move=> p Hp; apply: normal_eq=> //; last (by apply: norm_eq).
apply: norm_normal.
Qed.


Lemma norm_plusP : forall p q, p ++ (norm q) == norm (p ++ q).
Proof.
move => p q; apply: eqP_sym; apply: (eqP_trans (norm_eq (p ++ q))).
apply: eqP_plus; first (exact: eqP_refl).
apply: eqP_sym; apply: norm_eq.
Qed.

Lemma norm_seq0 : norm (Seq0 R) = seq0.
Proof. done. Qed.

Lemma norm_seq1 : forall a, (a <> 0) -> norm (Seq a) = (Seq a).
Proof.
by move=> a Ha; apply: normal_norm_eq; rewrite /normal //=; apply/eqP.
Qed.

Lemma normal_seq1 : forall a, (a <> 0) -> normal (Seq a).
Proof. by move=> a Ha; rewrite / normal //=; apply/eqP. Qed.

Lemma norm_seq0R : norm (Seq 0) = seq0.
Proof. by rewrite / norm //= eq_refl. Qed.

Lemma eqP_eq_norm : forall p q, p == q -> norm p = norm q.
Proof.
move=> p q H; apply: normal_eq; try apply: norm_normal.
move: (norm_eq p)(norm_eq q) => Hp Hq.
by rewrite (eqP_trans Hp) // eqP_sym // (eqP_trans Hq) // eqP_sym.
Qed.

Lemma norm_adds : 
  forall (p :polynomial) a, (a <> 0) -> norm (Adds a p) = Adds a (norm p).
Proof.
have HT1 : forall p a, (Adds a (norm p)) == Adds a p.
  by move=>  p a; rewrite //= eq_refl norm_eq.
have HT3: forall p a, (a != 0) -> normal p -> normal (Adds a p) by elim => //=.
move=> p a Ha; move: (eqP_eq_norm (HT1 p a)) => <-.
apply: normal_norm_eq; apply: HT3; first by apply/eqP.
by apply: norm_normal.
Qed.

Lemma norm_multPX : forall (p :polynomial), norm (Adds 0 p) = multPX (norm p).
Proof.
have HT: (forall p, normal p -> normal (Xp p)) by elim=>//.
move=> p; apply: normal_eq; first (apply: norm_normal).
  by apply: HT; apply: norm_normal.
move: (norm_eq (Adds 0 p)) => H1.
rewrite (eqP_trans H1) //; clear H1.
move: (norm_eq p) => H1; move: (eqP_multPX H1) => H2.
rewrite eqP_sym // (eqP_trans H2) //.
by clear H1 H2; elim: p => //= [|x p Hrec]; rewrite !eq_refl //= eqP_refl.
Qed.

Lemma normal_tail_poly: forall p, normal p -> normal (tail_poly p).
Proof. case=>//=[x s]; exact: normal_inv. Qed.


Lemma R_to_poly_normal: forall x, normal (R_to_poly x).
Proof.
rewrite /R_to_poly /normal; move=> x; case H:(x==0%R)%EQ; rewrite //= //=;
    first (apply/eqP; apply: one_diff_0).
by rewrite H.
Qed.

End Normalization.

Section EvaluationMorphism.
Open Scope poly_scope.

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


