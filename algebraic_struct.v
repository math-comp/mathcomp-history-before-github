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


Section MonoidProp.
Variable (M : monoid_class) (Mm : is_monoid M).

Lemma m_op_A : forall x1 x2 x3 : M,
  op x1 (op x2 x3) = op (op x1 x2) x3.
Proof. case: Mm =>//. Qed.

Lemma m_op_unitl : forall x : M, op (@unit M) x = x.
Proof. case: Mm =>//. Qed.

Lemma m_op_unitr : forall x, op x (@unit M) = x.
Proof. case: Mm =>//. Qed.

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
Arguments Scope Groups.plus [_ groups_scope groups_scope].
Arguments Scope Groups.opp [_ groups_scope].

Definition plus_g := nosimpl Groups.plus.
Definition opp_g := nosimpl Groups.opp.
Definition zero_g := nosimpl Groups.zero.
Prenex Implicits plus_g opp_g.

Infix "+" := plus_g: groups_scope.
Notation "- x" := (opp_g x): groups_scope.
Notation "0" := (zero_g _) (at level 0): groups_scope.

Coercion groups_to_monoid (g : groups_class) :=
  (Monoid (@zero_g g) (@plus_g g)).

Structure is_groups (elt : groups_class) : Prop := {
  monoidP_ : (is_monoid elt);
  oppP_ : forall x, plus_g (opp_g x) x = @zero_g elt
}.

Structure is_abelian_groups (elt : groups_class) : Prop := {
  groupsP_ : (is_groups elt);
  plusC_ : opC (@plus_g elt)
}.

Section GroupsProp.
Open Scope groups_scope.

Variable (G : groups_class) (Gg : is_groups G) 
(Gag : is_abelian_groups G).

Lemma plus_gA : forall x1 x2 x3 : G, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. by apply: (@m_op_A G) => //=; case: Gg. Qed.

Lemma plus_g0l : forall x : G, 0 + x = x.
Proof. by apply: (@m_op_unitl G); case: Gg. Qed.

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

Lemma is_groups_ag : forall (G : groups_class),
  is_abelian_groups G -> is_groups G.
Proof. by move=> G; case. Qed.

Hint Resolve is_groups_ag.
(*
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
(* Notation "x '--' y" := (x + (- y)%R) : rings_scope. *)

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

Lemma opp_plus_eqr : forall (x1 x2 : elt), x1 + x2 = 0 -> x1 = -x2.
Proof. 
by move=> x1 x2 H; apply: (plusInj x2); rewrite plus_opr plusC.
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

Lemma multm1x : forall x :elt, -1 * x = - x.
Proof.
by move => x; rewrite -mult_oppl mult1l.
Qed.

Lemma plusCA : forall x1 x2 x3 : elt, x1 + (x2 + x3) = x2 + (x1 + x3).
Proof. move=> *; rewrite !plusA; congr (_ + _); exact: plusC. Qed.

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

Lemma multCA : forall x1 x2 x3 : elt, x1 * (x2 * x3) = x2 * (x1 * x3).
Proof. move=> *; rewrite !multA; congr (_ * _); exact: multC. Qed.

End CommutativeRings.
*)

Unset Implicit Arguments.