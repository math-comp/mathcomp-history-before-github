Require Import ssreflect.
Require Import eqtype.
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

Module MonoidClass.

Structure monoid_class : Type := MonoidClass {
  element :> Type;
  unit : element;
  op : element -> element -> element
}.
End MonoidClass.
Notation monoid_class := MonoidClass.monoid_class.
Notation MonoidClass := MonoidClass.MonoidClass.

Module GroupsClass.

Structure groups_class : Type := GroupsClass {
  element :> Type;
  zero : element;
  opp : element -> element;
  plus : element -> element -> element
}.
End GroupsClass.
Notation groups_class := GroupsClass.groups_class.
Notation GroupsClass := GroupsClass.GroupsClass.

Coercion groups2monoid_cls (g : groups_class) :=
  (MonoidClass (@GroupsClass.zero g) (@GroupsClass.plus g)).

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

Print Graph.


Section StructAxioms.

(* Monoid *)
Notation op := MonoidClass.op.
Notation unit := MonoidClass.unit.

Structure is_monoid (M : monoid_class)
  : Prop := {
  opA_ : opA (@op M);
  op_unitl_ : forall x : M, op (@unit M) x = x;
  op_unitr_ : forall x : M, op x (@unit M) = x 
}.

Structure is_abelian_monoid (M : monoid_class)
  : Prop := {
  ab_is_monoidP_ : (is_monoid M);
  opC_ : opC (@op M)
}.
(* --- *)

(* Groups *)
Notation zero := GroupsClass.zero.
Notation opp := GroupsClass.opp.
Notation plus := GroupsClass.plus.

Structure is_groups (G : groups_class)
  : Prop := {
  is_monoidP_ :> (is_monoid G);
  oppP_ : forall x : G, plus (opp x) x = (@zero G)
}.

Structure is_abelian_groups (G : groups_class)
  : Prop := {
  ab_is_groupsP_ :> (is_groups G);
  plusC_ : opC (@plus G)
}.
(* --- *)

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

End StructAxioms.

Section StructSimpl.

Lemma is_monoid_am : forall M : monoid_class,
  is_abelian_monoid M -> is_monoid M.
Proof. by move=>M; case. Qed.

(* --- *)

Variable G : groups_class.

Lemma is_groups_ag :
  is_abelian_groups G -> is_groups G.
Proof. by case. Qed.

Lemma is_monoid_grp : is_groups G -> is_monoid G.
Proof. by case. Qed.

Lemma is_abelian_monoid_ag :
  is_abelian_groups G -> is_abelian_monoid G.
Proof. by case=> H1 H2; split=>//; case: H1. Qed.

(* --- *)

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

End StructSimpl.

Hint Resolve is_monoid_am is_groups_ag is_monoid_grp is_abelian_monoid_ag
 is_ring_cr is_groups_ring is_monoid_ring_mult is_abelian_monoid_cr_mult.

Module Monoid.

Structure monoid : Type := Monoid {
  element :> monoid_class;
  monoidP : is_monoid element
}.
End Monoid.
Notation monoid := Monoid.monoid.
Notation Monoid := Monoid.Monoid.
Coercion Monoid : is_monoid >-> monoid.

Module AbelianMonoid.

Structure abelian_monoid : Type := AbelianMonoid {
  element :> monoid_class;
  abelian_monoidP : is_abelian_monoid element
}.
End AbelianMonoid.
Notation ab_monoid := AbelianMonoid.abelian_monoid.
Notation AbMonoid := AbelianMonoid.AbelianMonoid.
Coercion AbMonoid : is_abelian_monoid >-> ab_monoid.

Coercion ab_mono2mono (M : ab_monoid) :=
  let: AbMonoid _ H := M in Monoid (is_monoid_am H).

Print Graph.

Delimit Scope monoid_scope with Mo.
Bind Scope monoid_scope with Monoid.element.

Notation "1" := (MonoidClass.unit _) (at level 0): monoid_scope.
Infix "*" := MonoidClass.op : monoid_scope.

Section MonoidProp.
Open Scope monoid_scope.
Variable (M : monoid).

Lemma m_op_A : forall x1 x2 x3 : M,
  x1 * (x2 * x3) = x1 * x2 * x3.
Proof. case: M=> elt; case=>//. Qed.

Lemma m_op_unitl : forall x : M, 1 * x = x.
Proof. case: M=> elt; case=>//. Qed.

Lemma m_op_unitr : forall x : M, x * 1 = x.
Proof. case: M=> elt; case=>//. Qed.

Variable (aM: ab_monoid).

Lemma m_op_C : forall x1 x2 : aM, x1 * x2 = x2 * x1.
Proof. case: aM => elt; case=> //. Qed.

End MonoidProp.

Module Groups.

Structure groups : Type := Groups {
  element :> groups_class;
  groupsP : is_groups element
}.
End Groups.
Notation groups := Groups.groups.
Notation Groups := Groups.Groups.
Coercion Groups : is_groups >-> groups.

Module AbelianGroups.

Structure abelian_groups : Type := AbelianGroups {
  element :> groups_class;
  abelian_groupsP : is_abelian_groups element
}.
End AbelianGroups.
Notation ab_groups := AbelianGroups.abelian_groups.
Notation AbGroups := AbelianGroups.AbelianGroups.
Coercion AbGroups : is_abelian_groups >-> ab_groups.

Coercion groups2monoid (G : groups) :=
  let: Groups _ H := G in Monoid H.

Coercion ab_groups2groups (G : ab_groups) :=
  let: AbGroups _ H := G in Groups H.

Delimit Scope groups_scope with Gs.
Bind Scope groups_scope with Groups.element.

Notation "0" := (GroupsClass.zero _) (at level 0): groups_scope.
Notation "- x" := (GroupsClass.opp x): groups_scope.
Infix "+" := GroupsClass.plus: groups_scope.

Section GroupsProp.
Open Scope groups_scope.

Variable (G : groups).

Lemma plus_gA : forall x1 x2 x3 : G, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. by case: G => //= elt H; apply: (@m_op_A H). Qed.

Lemma plus_g0l : forall x : G, 0 + x = x.
Proof. by case: G => //= elt H; apply: (@m_op_unitl H). Qed.

Lemma plus_opp_gl : forall x : G, - x + x = 0.
Proof. by case: G=> elt; case. Qed.

Notation plus_g := GroupsClass.plus.

Lemma plus_gKl : forall x : G, cancel (plus_g x) (plus_g (- x)).
Proof.
by move=> x y; rewrite plus_gA plus_opp_gl plus_g0l.
Qed.

Lemma plus_g_injl : forall x : G, injective (plus_g x).
Proof. move=> x; exact: can_inj (plus_gKl x). Qed.

Implicit Arguments plus_g_injl [].

Lemma plus_g0r : forall x : G, x + 0 = x.
Proof. by case: G => //= elt H; apply: (@m_op_unitr H). Qed.

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

Notation opp_g := GroupsClass.opp.

Lemma opp_gK : cancel (@opp_g G) (@opp_g G).
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

Variable aG : ab_groups.

Lemma plus_gC : forall x1 x2 : aG, x1 + x2 = x2 + x1.
Proof. by case: aG=> elt; case. Qed.

End GroupsProp.

Implicit Arguments plus_g_injl [G].
Implicit Arguments plus_g_injr [G].

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
  element :> ring_class;
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


Unset Implicit Arguments.