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

(* Some usefull definition *)

Section OperationProp.
Variable (T: Type) (op op' : T -> T -> T).

Definition opA := forall x1 x2 x3, op x1 (op x2 x3) = op (op x1 x2) x3.

Definition opC := forall x1 x2, op x1 x2 = op x2 x1.

Definition op_distl := 
  forall x1 x2 x3, op' x1 (op x2 x3) = op (op' x1 x2) (op' x1 x3).

Definition op_distr :=
  forall x1 x2 x3, op' (op x1 x2) x3 = op (op' x1 x3) (op' x2 x3).

End OperationProp.

Module Monoid.

Structure monoid : Type := Monoid {
  element :> eqType;
  unit : element;
  op : element -> element -> element
}.

End Monoid.

Notation monoid_class := Monoid.monoid.
Notation Monoid := Monoid.Monoid.
Notation op := Monoid.op.
Notation unit := Monoid.unit.

Structure is_monoid (M : monoid_class) : Prop := {
  opA_ : opA (@op M);
  op_unitl_ : forall x, op (@unit M) x = x;
  op_unitr_ : forall x, op x (@unit M) = x 
}.

Structure is_abelian_monoid (M : monoid_class) : Prop := {
  ab_monoidP_ : (is_monoid M);
  opC_ : opC (@op M)
}.

Lemma is_monoid_am : forall (M : monoid_class),
  is_abelian_monoid M -> is_monoid M.
Proof. by move=> M; case. Qed.

Hint Resolve is_monoid_am.

Section MonoidProp.
Variable (M : monoid_class) (Mm : is_monoid M)
 (Mam : is_abelian_monoid M).

Lemma m_op_A : forall x1 x2 x3 : M,
  op x1 (op x2 x3) = op (op x1 x2) x3.
Proof. case: Mm =>//. Qed.

Lemma m_op_unitl : forall x : M, op (@unit M) x = x.
Proof. case: Mm =>//. Qed.

Lemma m_op_unitr : forall x, op x (@unit M) = x.
Proof. case: Mm =>//. Qed.

Lemma m_op_C : forall x1 x2 : M, op x1 x2 = op x2 x1.
Proof. case: Mam => //. Qed.

End MonoidProp.


Module Groups.

Structure groups : Type := Groups {
  element :> eqType;
  zero : element;
  opp : element -> element;
  plus : element -> element -> element
}.
End Groups.

(* groups notation *)
Notation groups_class := Groups.groups.
Notation Groups := Groups.Groups.

Implicit Arguments Groups.zero [].

Delimit Scope groups_scope with Gs.
Bind Scope groups_scope with Groups.element.
Arguments Scope Groups.opp [_ groups_scope].
Arguments Scope Groups.plus [_ groups_scope groups_scope].

Definition zero_g := nosimpl Groups.zero.
Definition opp_g := nosimpl Groups.opp.
Definition plus_g := nosimpl Groups.plus.
Prenex Implicits opp_g plus_g.

Notation "0" := (zero_g _) (at level 0): groups_scope.
Notation "- x" := (opp_g x): groups_scope.
Infix "+" := plus_g: groups_scope.

Coercion groups_to_monoid (g : groups_class) :=
  (Monoid (@zero_g g) (@plus_g g)).

Structure is_groups (G : groups_class) : Prop := {
  monoidP_ : (is_monoid G);
  oppP_ : forall x, plus_g (opp_g x) x = @zero_g G
}.

Structure is_abelian_groups (G : groups_class) : Prop := {
  groupsP_ : (is_groups G);
  plusC_ : opC (@plus_g G)
}.

Section GroupsCoercion.

Variable (G : groups_class).

Lemma is_groups_ag : is_abelian_groups G -> is_groups G.
Proof. by case. Qed.

Lemma is_monoid_grp : is_groups G -> is_monoid G.
Proof. by case. Qed.

Lemma is_abelian_monoid_ag : is_abelian_groups G -> is_abelian_monoid G.
Proof. by case=> H1 H2; split=>//; case: H1. Qed.

End GroupsCoercion.

Hint Resolve is_groups_ag is_monoid_grp is_abelian_monoid_ag.

Section GroupsProp.
Open Scope groups_scope.

Variable (G : groups_class) 
  (Gg : is_groups G) (Gag : is_abelian_groups G).

Lemma plus_gA : forall x1 x2 x3 : G, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. by apply: (@m_op_A G) => //=; auto. Qed.

Lemma plus_g0l : forall x : G, 0 + x = x.
Proof. by apply: (@m_op_unitl G); auto. Qed.

Lemma plus_opp_gl : forall x : G, - x + x = 0.
Proof. by case: Gg. Qed.

Lemma plus_gKl : forall x : G, cancel (plus_g x) (plus_g (- x)).
Proof.
by move=> x y; rewrite plus_gA plus_opp_gl plus_g0l.
Qed.

Lemma plus_g_injl : forall x : G, injective (plus_g x).
Proof. move=> x; exact: can_inj (plus_gKl x). Qed.

Implicit Arguments plus_g_injl [].

Lemma plus_g0r : forall x : G, x + 0 = x.
Proof. by apply: (@m_op_unitr G); case: Gg. Qed.

Lemma plus_opp_gr : forall x : G, x + (- x) = 0.
Proof.
by move=> x; rewrite -{1}(plus_gKl (- x) x) plus_opp_gl -plus_gA
  plus_g0l plus_opp_gl.
Qed.

Lemma plus_gKr : forall x : G, cancel (plus_g (- x)) (plus_g x).
Proof.
by move=> x y; rewrite plus_gA plus_opp_gr plus_g0l.
Qed.

Notation plus_gr := (fun x y => y + x).

Lemma plus_grKl : forall x : G, cancel (plus_gr x) (plus_gr (- x)).
Proof.
by move=> x y; rewrite -plus_gA plus_opp_gr plus_g0r.
Qed.

Lemma plus_g_injr : forall x : G, injective (plus_gr x).
Proof. move=> x; exact: can_inj (plus_grKl x). Qed.

Lemma plus_grKr : forall x : G, cancel (plus_gr (- x)) (plus_gr x).
Proof. by move=> x y; rewrite -plus_gA plus_opp_gl plus_g0r. Qed.

Lemma opp_g0 : - 0 = 0 :> G.
Proof. by rewrite -{2}(plus_opp_gl 0) plus_g0r. Qed.

Lemma opp_gK : cancel (@opp_g G) opp_g.
Proof.
by move=> x; rewrite -{2}(plus_grKl (- x) x) -plus_gA plus_gKr.
Qed.

Lemma opp_g_inj : injective (@opp_g G).
Proof. exact: can_inj opp_gK. Qed.

Lemma opp_plus_g : forall x1 x2 : G, - (x2 + x1) = - x1 + - x2. 
Proof.
by move=> x1 x2; apply: (plus_g_injl (x2 + x1));
  rewrite plus_gA plus_grKl !plus_opp_gr.
Qed.

Lemma plus_gC : forall x1 x2 : G, x1 + x2 = x2 + x1.
Proof. by case: Gag. Qed.

End GroupsProp.

Implicit Arguments plus_g_injl [G].
Implicit Arguments plus_g_injr [G].


Module Ring.

Structure ring : Type := Ring {
  element :> eqType;
  zero : element;
  one : element;
  opp : element -> element;
  plus : element -> element -> element;
  mult : element -> element -> element
}.
End Ring.

(* ring notation *)
Notation ring_class := Ring.ring.
Notation Ring := Ring.Ring.

Implicit Arguments Ring.zero [].
Implicit Arguments Ring.one [].

Delimit Scope ring_scope with R.
Bind Scope ring_scope with Ring.element.
Arguments Scope Ring.opp [_ ring_scope].
Arguments Scope Ring.plus [_ ring_scope ring_scope].
Arguments Scope Ring.mult [_ ring_scope ring_scope].

Definition zero_r := nosimpl Ring.zero.
Definition one_r := nosimpl Ring.one.
Definition opp_r := nosimpl Ring.opp.
Definition plus_r := nosimpl Ring.plus.
Definition mult_r := nosimpl Ring.mult.
Prenex Implicits opp_r plus_r mult_r.

Notation "0" := (zero_r _) (at level 0): ring_scope.
Notation "1" := (one_r _) (at level 0): ring_scope.
Notation "- x" := (opp_r x): ring_scope.
Infix "+" := plus_r: ring_scope.
Infix "*" := mult_r: ring_scope.

Coercion ring_to_groups_plus (r : ring_class) :=
  (Groups (@zero_r r) (@opp_r r) (@plus_r r)).

Coercion ring_to_monoid_mult (r : ring_class) :=
  (Monoid (@one_r r) (@mult_r r)).

Notation r2m_m := ring_to_monoid_mult.

Structure is_ring (R : ring_class) : Prop := {
  groups_plusP_ : (is_abelian_groups R);
  monoid_multP_ : (is_monoid (r2m_m R));
  plus_mult_l_ : forall x1 x2 x3 : R, 
    mult_r x1 (plus_r x2 x3) = plus_r (mult_r x1 x2) (mult_r x1 x3);
  plus_mult_r_ : forall x1 x2 x3 : R, 
    mult_r (plus_r x1 x2) x3 = plus_r (mult_r x1 x3) (mult_r x2 x3);
  one_diff_zero_ : (one_r R) <> (zero_r R)  (* Non trivial ring *)
}.

Structure is_commutative_ring (R : ring_class) : Prop := {
  ringP_ : (is_ring R);
  multC_ : opC (@mult_r R)
}.


Section RingCoercion.
Variable (R : ring_class).

Lemma is_ring_cr : is_commutative_ring R -> is_ring R.
Proof. by case. Qed.

Lemma is_groups_ring : is_ring R -> is_abelian_groups R.
Proof. by case. Qed.

Lemma is_monoid_ring_mult : is_ring R -> is_monoid (r2m_m R).
Proof. by case. Qed.

Lemma is_abelian_monoid_cr_mult : is_commutative_ring R -> is_abelian_monoid (r2m_m R).
Proof. by case=> H1 H2; split=>//; case H1; auto. Qed.

End RingCoercion.

Hint Resolve is_ring_cr is_groups_ring is_monoid_ring_mult is_abelian_monoid_cr_mult.

Section RingsProp.
Open Scope ring_scope.

Variable (R : ring_class) 
  (Rr : is_ring R) (Rcr : is_commutative_ring R).

Lemma plus_rA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. apply: (@plus_gA R); auto. Qed.

Lemma plus_rC : forall x1 x2 : R, x1 + x2 = x2 + x1.
Proof. apply: (@plus_gC R); auto. Qed.

Lemma plus_r0l: forall x : R, 0 + x = x.
Proof. apply: (@plus_g0l R); auto. Qed.

Lemma plus_r0r: forall x : R, x + 0 = x.
Proof. apply: (@plus_g0r R); auto. Qed.

Lemma plus_opp_rl : forall x : R, - x + x = 0.
Proof. apply: (@plus_opp_gl R); auto. Qed.

Lemma plus_opp_rr : forall x : R, x + - x = 0.
Proof. apply: (@plus_opp_gr R); auto. Qed.

Lemma plus_rK : forall x : R, cancel (plus_r x) (plus_r (- x)).
Proof. apply: (@plus_gKl R); auto. Qed.

Lemma plus_r_inj : forall x : R, injective (plus_r x).
Proof. move=> x; exact: can_inj (plus_rK x). Qed.

Implicit Arguments plus_r_inj [].

Lemma opp_r0 : -0 = 0 :> R.
Proof. apply: (@opp_g0 R); auto. Qed.

Lemma opp_rK : cancel (@opp_r R) opp_r.
Proof. apply: (@opp_gK R); auto. Qed.

Lemma opp_r_inj : injective (@opp_r R).
Proof. exact: can_inj opp_rK. Qed.

Lemma opp_plus_r : forall x1 x2 : R, - (x1 + x2) = - x1 + - x2. 
Proof.
move=> x1 x2; rewrite plus_rC.
apply: (@opp_plus_g R); auto.
Qed.

Lemma opp_plus_r_eq : forall (x1 x2 : R), x1 + x2 = 0 -> x1 = -x2.
Proof. 
by move=> x1 x2 H; apply: (plus_r_inj x2); rewrite plus_opp_rr plus_rC.
Qed.

(* Multiplication *)
Lemma mult_rA: 
  forall x1 x2 x3 : R, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. apply (@m_op_A (r2m_m R)); auto. Qed.

Lemma mult_r1l: forall x : R, 1 * x = x.
Proof. apply: (@m_op_unitl (r2m_m R)); auto. Qed.

Lemma mult_r1r : forall x : R, x * 1 = x.
Proof. apply: (@m_op_unitr (r2m_m R)); auto. Qed.

Lemma plus_mult_l:
  forall x1 x2 x3 : R, x3 * (x1 + x2) = (x3 * x1) + (x3 * x2).
Proof. by case: Rr. Qed.

Lemma plus_mult_r:
  forall x1 x2 x3 : R, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
Proof. by case: Rr. Qed.

Lemma one_diff_0 : 1 <> 0 :> R.
Proof. by case: Rr. Qed.

Lemma mult_r0r: forall x : R, x * 0 = 0.
Proof.
move => x; move: (@plus_r_inj x (x*0) 0) => ->//.
by rewrite -{1}[x]mult_r1r  -plus_mult_l  plus_rC plus_r0l mult_r1r plus_rC plus_r0l.
Qed.

Lemma mult_r0l: forall x : R, 0 * x = 0.
Proof.
move => x; move: (@plus_r_inj x (0*x) 0) => ->//.
by rewrite -{1}[x]mult_r1l  -plus_mult_r plus_rC plus_r0l mult_r1l plus_rC plus_r0l.
Qed.

Lemma mult_opp_rl: forall x y : R, (- (x * y)) = (- x) * y.
Proof.
move => x y.
by rewrite -[-x*y]plus_r0l -(plus_opp_rl (x*y)) -plus_rA -plus_mult_r [x+_]plus_rC 
   plus_opp_rl mult_r0l plus_rC plus_r0l.
Qed.

Lemma mult_opp_rr: forall x y : R, (-(x * y)) = x * (- y).
Proof.
move => x y.
by rewrite -[x*-y]plus_r0l -(plus_opp_rl (x*y)) -plus_rA -plus_mult_l [y+_]plus_rC
   plus_opp_rl mult_r0r plus_rC plus_r0l.
Qed.

Lemma plus_rCA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x2 + (x1 + x3).
Proof. move=> *; rewrite !plus_rA; congr (_ + _); exact: plus_rC. Qed.

Lemma mult_rC : forall x1 x2 : R, x1 * x2 = x2 * x1.
Proof. by case: Rcr. Qed.

Lemma mult_rCA : forall x1 x2 x3 : R, x1 * (x2 * x3) = x2 * (x1 * x3).
Proof.
clear Rr; move=> *.
rewrite !(@m_op_A (r2m_m R)); auto; congr (_ * _); exact: mult_rC.
Qed.

End RingsProp.


Unset Implicit Arguments.