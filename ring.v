Require Import ssreflect eqtype funs ssrnat ssrbool.
Require Import groups group_perm signperm.
Require Import algebraic_struct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module RingClass.

Structure ring_class : Type := RingClass {
  element :> eqType;
  zero : element;
  one : element;
  opp : element -> element;
  plus : element -> element -> element;
  mult : element -> element -> element
}.
End RingClass.
Notation ring_class := RingClass.ring_class.
Notation RingClass := RingClass.RingClass.

Coercion ring2groups_plus_cls (r : ring_class) :=
  (GroupsClass (@RingClass.zero r) (@RingClass.opp r)
  (@RingClass.plus r)).

Coercion ring2monoid_mult_cls (r : ring_class) :=
  (MonoidClass (@RingClass.one r) (@RingClass.mult r)).

Section RingAxioms.
(* Ring *)
Notation zero' := RingClass.zero.
Notation one := RingClass.one.
Notation plus' := RingClass.plus.
Notation mult := RingClass.mult.

Structure is_ring (R : ring_class)
  : Prop := {
  ring_is_groups_plusP_ :> (is_abelian_groups R);
  ring_is_monoid_multP_ :> (is_monoid (ring2monoid_mult_cls R));
  plus_mult_l_ : forall x1 x2 x3 : R, 
    mult x1 (plus' x2 x3) = plus' (mult x1 x2) (mult x1 x3);
  plus_mult_r_ : forall x1 x2 x3 : R, 
    mult (plus' x1 x2) x3 = plus' (mult x1 x3) (mult x2 x3);
  one_diff_zero_ : (@one R) <> (@zero' R)  (* Non trivial ring *)
}.

Structure is_commutative_ring (R : ring_class)
  : Prop := {
  com_is_ringP_ :> (is_ring R);
  multC_ : opC (@mult R)
}.
(* --- *)

End RingAxioms.

Section RingSimpl.

Variable R : ring_class.

Lemma is_ring_cr :
  is_commutative_ring R -> is_ring R.
Proof. by case. Qed.

Lemma is_groups_ring :
  is_ring R -> is_abelian_groups R.
Proof. by case. Qed.

Lemma is_monoid_ring_mult :
  is_ring R -> is_monoid (ring2monoid_mult_cls R).
Proof. by case. Qed.

Lemma is_abelian_monoid_cr_mult :
  is_commutative_ring R -> is_abelian_monoid (ring2monoid_mult_cls R).
Proof. by case=> H1 H2; split=>//; case H1; auto. Qed.

End RingSimpl.

Hint Resolve is_monoid_am is_groups_ag is_monoid_grp is_abelian_monoid_ag
 is_ring_cr is_groups_ring is_monoid_ring_mult is_abelian_monoid_cr_mult.

Module Ring.

Structure ring : Type := Ring {
  element :> ring_class;
  ringP : is_ring element
}.
End Ring.
Notation ring := Ring.ring.
Notation Ring := Ring.Ring.
Coercion Ring : is_ring >-> ring.

Module CommutativeRing.

Structure commutative_ring : Type := CommutativeRing {
  element : ring_class;
  commutative_ringP : is_commutative_ring element
}.
End CommutativeRing.
Notation com_ring := CommutativeRing.commutative_ring.
Notation ComRing := CommutativeRing.CommutativeRing.
Coercion ComRing : is_commutative_ring >-> com_ring.

Definition ring2groups_plus : ring -> ab_groups.
case=>// elt H.
exists elt; auto.
Defined.

Coercion ring2groups_plus : ring >-> ab_groups.

Definition ring2monoid_mult : ring -> monoid.
case=>// elt H.
exists (ring2monoid_mult_cls elt); auto.
Defined.

Coercion ring2monoid_mult : ring >-> monoid.

Coercion com_ring2ring (R : com_ring) :=
  let: ComRing _ H := R in Ring H.

Delimit Scope ring_scope with R.
Bind Scope ring_scope with Ring.element.

Notation "0" := (RingClass.zero _) (at level 0): ring_scope.
Notation "1" := (RingClass.one _) (at level 0): ring_scope.
Notation "- x" := (RingClass.opp x): ring_scope.
Infix "+" := RingClass.plus: ring_scope.
Infix "*" := RingClass.mult: ring_scope.

Section RingsProp.
Open Scope ring_scope.

Variable (R : ring).

Lemma plus_rA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. by case: R=> elt H; apply: (@plus_gA H). Qed.

Lemma plus_rC : forall x1 x2 : R, x1 + x2 = x2 + x1.
Proof. by case: R=> elt H; apply: (@plus_gC H). Qed.

Lemma plus_r0l: forall x : R, 0 + x = x.
Proof. by case: R=> elt H; apply: (@plus_g0l H). Qed.

Lemma plus_r0r: forall x : R, x + 0 = x.
Proof. by case: R=> elt H; apply: (@plus_g0r H). Qed.

Lemma plus_opp_rl : forall x : R, - x + x = 0.
Proof. by case: R=> elt H; apply: (@plus_opp_gl H). Qed.

Lemma plus_opp_rr : forall x : R, x + - x = 0.
Proof. by case: R=> elt H; apply: (@plus_opp_gr H). Qed.

Notation plus_r := RingClass.plus.
Lemma plus_rK : forall x : R, cancel (plus_r x) (plus_r (- x)).
Proof. by case: R=> elt H; apply: (@plus_gKl H). Qed.

Lemma plus_r_inj : forall x : R, injective (plus_r x).
Proof. move=> x; exact: can_inj (plus_rK x). Qed.

Implicit Arguments plus_r_inj [].

Lemma opp_r0 : -0 = 0 :> R.
Proof. by case: R=> elt H; apply: (@opp_g0 H). Qed.

Notation opp_r := RingClass.opp.
Lemma opp_rK : cancel (@opp_r R) (@opp_r R).
Proof. by case: R=> elt H; apply: (@opp_gK H). Qed.

Lemma opp_r_inj : injective (@opp_r R).
Proof. exact: can_inj opp_rK. Qed.

Lemma opp_plus_r : forall x1 x2 : R, - (x1 + x2) = - x1 + - x2. 
Proof.
move=> x1 x2; rewrite plus_rC.
by case: R x1 x2 => //= elt H; apply: (@opp_plus_g H).
Qed.

Lemma opp_plus_r_eq : forall (x1 x2 : R), x1 + x2 = 0 -> x1 = -x2.
Proof. 
by move=> x1 x2 H; apply: (plus_r_inj x2); rewrite plus_opp_rr plus_rC.
Qed.

(* Multiplication *)
Lemma mult_rA: 
  forall x1 x2 x3 : R, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. 
by case: R=> //= elt H; apply (@m_op_A (is_monoid_ring_mult H)).
Qed.

Lemma mult_r1l: forall x : R, 1 * x = x.
Proof. 
by case: R=> //= elt H; apply: (@m_op_unitl (is_monoid_ring_mult H)).
Qed.

Lemma mult_r1r : forall x : R, x * 1 = x.
Proof.
by case: R=> //= elt H; apply: (@m_op_unitr (is_monoid_ring_mult H)).
Qed.

Lemma plus_mult_l:
  forall x1 x2 x3 : R, x3 * (x1 + x2) = (x3 * x1) + (x3 * x2).
Proof. by case: R=> elt; case. Qed.

Lemma plus_mult_r:
  forall x1 x2 x3 : R, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
Proof. by case: R=> elt; case. Qed.

Lemma one_diff_0 : 1 <> 0 :> R.
Proof. by case: R=>elt; case. Qed.

Lemma mult_r0r: forall x : R, x * 0 = 0.
Proof.
move => x; move: (@plus_r_inj x (x*0) 0) => ->//.
by rewrite -{1}[x]mult_r1r  -plus_mult_l 
  plus_rC plus_r0l mult_r1r plus_rC plus_r0l.
Qed.

Lemma mult_r0l: forall x : R, 0 * x = 0.
Proof.
move => x; move: (@plus_r_inj x (0*x) 0) => ->//.
by rewrite -{1}[x]mult_r1l 
 -plus_mult_r plus_rC plus_r0l mult_r1l plus_rC plus_r0l.
Qed.

Lemma mult_opp_rl: forall x y : R, (- (x * y)) = (- x) * y.
Proof.
move => x y.
by rewrite -[-x*y]plus_r0l -(plus_opp_rl (x*y))
  -plus_rA -plus_mult_r [x+_]plus_rC 
   plus_opp_rl mult_r0l plus_rC plus_r0l.
Qed.

Lemma mult_opp_rr: forall x y : R, (-(x * y)) = x * (- y).
Proof.
move => x y.
by rewrite -[x*-y]plus_r0l -(plus_opp_rl (x*y))
  -plus_rA -plus_mult_l [y+_]plus_rC
   plus_opp_rl mult_r0r plus_rC plus_r0l.
Qed.

Lemma plus_rCA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x2 + (x1 + x3).
Proof. move=> *; rewrite !plus_rA; congr (_ + _); exact: plus_rC. Qed.

Variable cR : com_ring.

Lemma mult_rC : forall x1 x2 : cR, x1 * x2 = x2 * x1.
Proof. by case: cR=>elt; case. Qed.

Lemma mult_rCA : forall x1 x2 x3 : cR, x1 * (x2 * x3) = x2 * (x1 * x3).
Proof.
case: cR mult_rC => //=elt H Hc x1 x2 x3.
rewrite !(@m_op_A (is_monoid_ring_mult H))//; congr (_ * _).
by exact: Hc.
Qed.

End RingsProp.

Section InjectingNat.
Open Scope ring_scope.

Variable (R : ring).

(* Injecting natural integers. *)

Definition RofSn n := iter n (fun x : R => x + 1) 1.

Coercion Local R_of_nat n := if n is S n' then RofSn n' else 0.

Notation n2r := R_of_nat.

Lemma RofSnE : forall n, RofSn n = n + 1 :> R.
Proof. by elim=> /= [|_ -> //]; rewrite plus_r0l. Qed.

Lemma Raddn : forall m n, (m + n)%N = m + n :> R.
Proof.
move=> m n; elim: m => /= [|m IHm]; first by rewrite plus_r0l.
by rewrite !RofSnE IHm plus_rC plus_rCA plus_rA.
Qed.

Lemma Rsubn : forall m n, m >= n -> (m - n)%N = m + - n :> R.
Proof.
move=> m n; move/leq_add_sub=> Dm.
by rewrite -{2}Dm Raddn -plus_rA plus_rCA plus_opp_rr plus_rC plus_r0l.
Qed.

Lemma Rmuln : forall m n, (m * n)%N = m * n :> R.
Proof.
move=> m n; elim: m => /= [|m IHm]; first by rewrite mult_r0l.
by rewrite Raddn RofSnE IHm plus_mult_r mult_r1l plus_rC.
Qed.

End InjectingNat.

Section IntPow.
Open Scope ring_scope.

Variable (R : ring).

(* Integer powers. *)

Definition RexpSn x n := iter n (fun y : R => y * x) x.

Definition Rexp_nat x n := if n is S n' then RexpSn x n' else 1.

End IntPow.
Notation "x ^ n" := (Rexp_nat x n).

Section IntPowProp.
Open Scope ring_scope.

Lemma RexpSnE : forall (R : ring) x n, RexpSn x n = x ^ n * x :> R.
Proof. by move=> R x; elim=> /= [|_ -> //]; rewrite mult_r1l. Qed.

Lemma exp1n : forall (R : ring) n, 1 ^ n = 1 :> R.
Proof. by move=> R; elim=> //= n IHn; rewrite RexpSnE IHn mult_r1l. Qed.

Lemma exp0n : forall (R : ring) n, 0 < n -> 0 ^ n = 0 :> R.
Proof. by move=> R [|[|n]] //= _; rewrite mult_r0r. Qed.

Lemma Rexpn : forall (R : ring) m n, (m ^ n)%N = m ^ n :> R.
Proof. by move=> R m; elim=> //= n IHn; rewrite Rmuln RexpSnE IHn. Qed.

Lemma sign_addb : forall (R : ring) b1 b2,
  (-1) ^ (b1 (+) b2) = (-1) ^ b1 * (-1) ^ b2 :> R.
Proof.
move=> R.
do 2!case; rewrite //= ?(@mult_opp_rl (-1) _) ?mult_r1l ?mult_r1r//.
by rewrite -mult_opp_rl -mult_opp_rr opp_rK mult_r1l.
Qed.

Lemma sign_permM : forall (R : ring) d (s t : permType d),
  (-1) ^ (s * t)%G = (-1) ^ s * (-1) ^ t :> R.
Proof. by move=> *; rewrite odd_permM sign_addb. Qed.

Variable cR : com_ring.

Lemma mult_exp : forall x1 x2 n, (x1 * x2) ^ n = x1 ^ n * x2 ^ n :> cR.
Proof.
move=> x1 x2; elim=> //= [|n IHn]; first by rewrite mult_r1l.
by rewrite !RexpSnE IHn -!mult_rA (mult_rCA x1).
Qed.

Lemma exp_addn : forall x n1 n2, x ^ (n1 + n2) = x ^ n1 * x ^ n2 :> cR.
Proof.
move=> x n1 n2; elim: n1 => /= [|n1 IHn]; first by rewrite mult_r1l.
by rewrite !RexpSnE IHn mult_rC mult_rCA mult_rA.
Qed.

Lemma exp_muln : forall x n1 n2, x ^ (n1 * n2) = (x ^ n1) ^ n2 :> cR.
Proof.
move=> x n1 n2; rewrite mulnC; elim: n2 => //= n2 IHn.
by rewrite !RexpSnE exp_addn IHn mult_rC.
Qed.

Lemma sign_odd : forall n, (-1) ^ odd n = (-1) ^ n :> cR.
Proof.
move=> n; rewrite -{2}[n]odd_double_half addnC double_mul2 exp_addn exp_muln.
rewrite //= ?(@mult_opp_rl (-1) _) ?mult_r1l ?mult_r1r//.
by rewrite -mult_opp_rl -mult_opp_rr opp_rK mult_r1l exp1n mult_r1l.
Qed.

End IntPowProp.



Unset Implicit Arguments.
