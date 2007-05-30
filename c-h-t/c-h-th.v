Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple.
Require Import div groups.
Require Import determinantET.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope local_scope with loc.
Open Scope local_scope.


Section Polynomials.

Variable R : eqType.
Variables plus mult : R -> R -> R.
Variable opp : R -> R.
Variables zero one : R.

Infix "+" := plus: local_scope.
Notation "- x" := (opp x): local_scope.
Infix "*" := mult: local_scope.
Notation "1" := one (at level 0) : local_scope.
Notation "0" := zero (at level 0): local_scope.


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
(* one diff zero *)
Variable one_diff_0: 1 <> 0.

Let opp_zero: -0 = 0.
by rewrite -{2}(plus_opr 0) plus0l.
Qed.

Section Polynomial.


(* A polynomial is sequence, the firts element of the sequence is monome of low degree*)
Definition polynomial := seq_eqType R.

(* Injection from polynomial to R *)
Definition R_to_poly (x :R) : polynomial := (Adds x seq0).

Lemma inj_R_to_poly : injective R_to_poly.
move => x y; rewrite / R_to_poly => H.
move/eqseqP: H => //= H; move/andP: H => H; elim: H => H _.
by apply/eqP.
Qed.

Fixpoint plusP (p q: polynomial) {struct p}: polynomial :=
  if p is (Adds a p') then
    if q is (Adds b q') then Adds (a + b) (plusP p' q') 
   else p 
  else q.

Definition eqP0 (p: polynomial) : bool :=
  all (set1 0) p.

Fixpoint eqP (p q: polynomial) {struct p}: bool :=
  if p is (Adds a p') then
    if q is (Adds b q') then (a == b) && (eqP p' q') 
   else eqP0 p 
  else eqP0 q.
(*
Lemma eqPP : reflect_eq eqP.
Proof.
move; elim=> [|x1 s1 Hrec] [|x2 s2]; first [ by constructor | simpl ].
apply: (iffP idP).
*)

Definition opP (p : polynomial) : polynomial :=
  maps opp p.

(* 
Multiplication by X
*)


Definition multPX (p : polynomial) := if p is (Adds _ _) then (Adds 0 p) else p.

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
by rewrite -(eqtype.eqP H2) opp_zero eq_refl.
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
by move => [| a p ] //=; rewrite opp_zero.
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
by case/andP => H1 H2; rewrite -(eqtype.eqP H1) multC mult0l eq_refl Hrec.
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

Lemma multRPrl: forall a p, p ps a = a sp p.
move => b; elim => [|a  p Hrec] //=.
by rewrite multC Hrec.
Qed.

Lemma multPC: forall p q, p ** q = q ** p.
Proof.
elim => [|a p Hrec] // [|b q] //=.
rewrite !multRPrl multC; congr Adds; congr plusP.
  exact: plusPC.
by rewrite Hrec.
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
congr Adds => //.
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

Lemma multP1 : forall p : polynomial, 11 ** p = p.
Proof.
case => [|a p] //=.
by rewrite !plusP0r mult1l multRP1.
Qed.

(* 00 is normal *)
Lemma normal0: normal 00.
Proof.
rewrite /normal /=.
by apply/negP => H1; case one_diff_0; apply/eqtype.eqP.
Qed.

(* 1 is normal *)
Lemma normal1: normal 11.
Proof.
rewrite /normal /=.
by apply/negP => H1; case one_diff_0; apply/eqtype.eqP.
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

End PolynomialProp.

Section MorphismEvaluation.

Fixpoint evalP (p :polynomial) (x :R) {struct p} : R :=
  (if p is (Adds a p') then a + x * (evalP p' x) else 0).

(* Proof that eval is morphisme *)

Lemma evalP_plusP : forall p q x, evalP (p ++ q) x = (evalP p x) + (evalP q x).
Proof.
move => p q x.
elim: p q => // [a s Hrec q].
elim: q Hrec => // [b u Hrec2 Hrec] /=.
  move: (Hrec u) => ->.
  by rewrite !plusA; congr plus; rewrite ![b + x *_]plusC -plusA -plus_multl.
Qed.

Lemma evalP_multPX : forall p x, evalP (Xp p) x = x * (evalP p x).
Proof. by elim => //= *; rewrite multC mult0x. Qed.

Lemma evalP_multPR : forall p c x, (x * c = c * x) -> evalP (c sp p) x = c * (evalP p x).
Proof. 
elim => //= [a p1 Hrec c x H].
rewrite plus_multl; congr plus; move: (Hrec c x H) => ->;
  rewrite -multA H multA; congr mult.
Qed.

Fixpoint com_coeff (p :polynomial) (x :R) {struct p} : bool := 
  (if p is (Adds a p') then (a * x == x * a)%EQ && (com_coeff p' x) else true).

Lemma com_coeffP : forall p x, 
  reflect (forall y, (mem p) y -> x * y = y * x) (com_coeff p x).
Proof. 
move => p x.
apply: (iffP idP) => H; first (elim: p H => //=).
elim: p H => //= [a s Hrec H].
rewrite / setU1 in H.
move: (H a) => Ha; rewrite eq_refl //= in Ha; rewrite Ha //= eq_refl; apply Hrec.
move=> y Hy; apply H; apply/orP; right; exact Hy.
Qed.

Lemma evalP_multP : forall p q x, (com_coeff p x) -> (com_coeff q x) ->
  evalP (p ** q) x = (evalP p x) * (evalP q x).
Proof.
move => p q x Hp Hq.
move/com_coeffP: Hp => Hp; move/com_coeffP: Hq => Hq.
elim: p q Hp Hq => // [a p1 Hrec q Hp Hq].
elim: q p1 Hrec Hp Hq => // [b q1 Hrec2 p1 Hrec Hp Hq].
rewrite adds_multl // evalP_plusP evalP_multPX.
move: (Hrec (Adds b q1)) => -> //=.
move: (Hp a) => Ha; move: (Hq b) => Hb.
rewrite -multA plus_multr !plus_multl evalP_multPR;
  last (rewrite Ha //= / setU1 eq_refl //=).
rewrite !plusA; congr plus; congr plus.
rewrite -multA Ha //= / setU1 eq_refl //=.
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

Lemma com_coeff_multP_rev : forall p p1 p2 x,
  (com_coeff p x) -> (com_coeff p1 x) -> (p == p1 ** p2) -> (com_coeff p2 x).
Proof.
move => p p1 p2 x Hp Hp1 H.
move/com_coeffP: Hp => Hp; move/com_coeffP: Hp1 => Hp1.
apply/com_coeffP.
elim: p p1 p2 Hp Hp1 H => // [p1 p2 Hp Hp1 H| a1 s1 Hrec1 p1 p2 Hp Hp1 H].
Qed.

End MorphismEvaluation.

End Polynomial.

End Polynomials.

Section Cayley.

Variable R : eqType.
Variables plus mult : R -> R -> R.
Variable opp : R -> R.
Variables zero one : R.

Infix "+" := plus: local_scope.
Notation "- x" := (opp x): local_scope.
Infix "*" := mult: local_scope.
Notation "1" := one (at level 0) : local_scope.
Notation "0" := zero (at level 0): local_scope.


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
(* one diff zero *)
Variable one_diff_0: 1 <> 0.

Let opp_zero: -0 = 0.
by rewrite -{2}(plus_opr 0) plus0l.
Qed.


Notation "\P[x]" := (polynomial R) : local_scope.

Notation "'M_' ( n )" := (matrix R n n)
  (at level 9, m, n at level 50, format "'M_' ( n )") : local_scope.


Section MatrixPoly.

Section MatrixOfPoly.

Open Scope local_scope.

Definition matrix_of_polynomial (n :nat) := (matrix (polynomial R) n n).

Notation "'\M_(x)_' ( n )" := (matrix_of_polynomial n)
  (at level 9, m, n at level 50, format "'\M_(x)_' ( n )") : local_scope.

Definition mx_to_mx_of_poly (n :nat) (A :M_(n)): \M_(x)_( n ) := 
   matrix_of_fun (fun i j => (R_to_poly (A i j))).

Lemma inj_mx_to_mx_of_poly : forall n, injective (@mx_to_mx_of_poly n).
Proof.
Admitted.

Definition poly_x : \P[x] := (Adds 1 (Adds 0 seq0)).

Definition x_I n : \M_(x)_(n) := 
  (@matrix_of_fun \P[x] n n (fun i j => (if i == j then poly_x else (@Seq0 R: (\P[x])) ))).

Definition determinant_poly := determinant (plusP plus) (multP mult plus zero) (opP opp) (@Seq0 R: \P[x]) (Adds 1 seq0).

Definition poly_car (n :nat) (A :M_(n)) : \P[x] :=
  determinant_poly (matrix_plus (plusP plus) (x_I n) (mx_to_mx_of_poly (matrix_scale mult (-1) A))).

End MatrixOfPoly.

Section PolyOfMatrix.
Open Scope local_scope.

Definition polynomial_of_matrix (n :nat) := (@polynomial (matrix_eqType R n n)).

Notation "'\M_[x]_' ( n )" := (polynomial_of_matrix n)
  (at level 9, m, n at level 50, format "'\M_[x]_' ( n )") : local_scope.

Definition R_to_mx (n :nat) (x :R) : M_(n) := (matrix_scale mult x (unit_matrix one zero n)).

Definition poly_to_poly_of_mx (n :nat) (p : \P[x]) : \M_[x]_(n):= 
  maps (R_to_mx n) p .

End PolyOfMatrix.

Notation "'\M_(x)_' ( n )" := (matrix_of_polynomial n)
  (at level 9, m, n at level 50, format "'\M_(x)_' ( n )") : local_scope.
Notation "'\M_[x]_' ( n )" := (polynomial_of_matrix n)
  (at level 9, m, n at level 50, format "'\M_[x]_' ( n )") : local_scope.

Variable (n :nat) (phi : \M_(x)_(n) -> \M_[x]_(n)).
Hypothesis phi_iso : bijective phi.
(* Hypothesis phi_plus : *)


End MatrixPoly.


