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

End StructSimpl.

Hint Resolve is_monoid_am is_groups_ag is_monoid_grp
 is_abelian_monoid_ag.

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
  element : monoid_class;
  abelian_monoidP : is_abelian_monoid element
}.
End AbelianMonoid.
Notation ab_monoid := AbelianMonoid.abelian_monoid.
Notation AbMonoid := AbelianMonoid.AbelianMonoid.
Coercion AbMonoid : is_abelian_monoid >-> ab_monoid.

Coercion ab_mono2mono (M : ab_monoid) :=
  let: AbMonoid _ H := M in Monoid (is_monoid_am H).

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
  element : groups_class;
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

Unset Implicit Arguments.