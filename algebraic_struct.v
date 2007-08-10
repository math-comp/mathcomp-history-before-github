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

Section StructAxioms.

(* Monoid *)

Structure is_monoid (M : Type) (u : M) (op : M->M->M)
  : Prop := {
  opA_ : opA op;
  op_unitl_ : forall x, op u x = x;
  op_unitr_ : forall x, op x u = x 
}.

Structure is_abelian_monoid (M : Type) (u : M) (op : M->M->M)
  : Prop := {
  ab_is_monoidP_ :> (is_monoid u op);
  opC_ : opC op
}.
(* --- *)

(* Groups *)

Structure is_groups (G : Type) (z : G) (opp : G->G) (plus : G->G->G)
  : Prop := {
  is_monoidP_ :> (is_monoid z plus);
  oppP_ : forall x, plus (opp x) x = z
}.

Structure is_abelian_groups (G : Type) (z : G) (opp : G->G)
  (plus : G->G->G) : Prop := {
  ab_is_groupsP_ :> (is_groups z opp plus);
  plusC_ : opC plus
}.
(* --- *)

End StructAxioms.

Module Monoid.

Structure monoid : Type := Monoid {
  element :> Type;
  unit : element;
  op : element -> element -> element;
  monoidP :> is_monoid unit op
}.
End Monoid.
Notation monoid := Monoid.monoid.
Notation Monoid := Monoid.Monoid.
Coercion Monoid : is_monoid >-> monoid.

Module AbelianMonoid.

Structure abelian_monoid : Type := AbelianMonoid {
  element :> monoid;
  opC_ : opC (@Monoid.op element)
}.
End AbelianMonoid.
Notation ab_monoid := AbelianMonoid.abelian_monoid.
Notation AbMonoid := AbelianMonoid.AbelianMonoid.

Delimit Scope monoid_scope with Mo.
Bind Scope monoid_scope with Monoid.element.

Notation "1" := (Monoid.unit _) (at level 0): monoid_scope.
Infix "*" := Monoid.op : monoid_scope.

Section MonoidProp.
Open Scope monoid_scope.
Variable (M : monoid).

Lemma m_op_A : forall x1 x2 x3 : M,
  x1 * (x2 * x3) = x1 * x2 * x3.
Proof. case: M=> elt u o; case=>//=. Qed.

Lemma m_op_unitl : forall x : M, 1 * x = x.
Proof. case: M=> elt u o; case=>//. Qed.

Lemma m_op_unitr : forall x : M, x * 1 = x.
Proof. case: M=> elt u o; case=>//. Qed.

Variable (aM: ab_monoid).

Lemma m_op_C : forall x1 x2 : aM, x1 * x2 = x2 * x1.
Proof. case: aM => elt//. Qed.

End MonoidProp.

Module Groups.

Structure groups : Type := Groups {
  element :> Type;
  zero : element;
  opp : element -> element;
  plus : element -> element -> element;
  groupsP :> is_groups zero opp plus
}.
End Groups.
Notation groups := Groups.groups.
Notation Groups := Groups.Groups.
Coercion Groups : is_groups >-> groups.

Module AbelianGroups.

Structure abelian_groups : Type := AbelianGroups {
  element :> groups;
  plusC_ : opC (@Groups.plus element)
}.
End AbelianGroups.
Notation ab_groups := AbelianGroups.abelian_groups.
Notation AbGroups := AbelianGroups.AbelianGroups.

(*
Definition g2m (G :groups) : (Groups.element G) -> (Monoid.element G).
move=> G x; exact x.
Defined.

Coercion g2m : Groups.element >-> Monoid.element.
*)

Definition ag2am (G : ab_groups) : ab_monoid := 
@AbMonoid (@AbelianGroups.element G) (@AbelianGroups.plusC_ G).

Coercion ag2am : ab_groups >-> ab_monoid.

Delimit Scope groups_scope with Gs.
Bind Scope groups_scope with Groups.element.

Notation "0" := (Groups.zero _) (at level 0): groups_scope.
Notation "- x" := (Groups.opp x): groups_scope.
Infix "+" := Groups.plus: groups_scope.

Section GroupsProp.
Open Scope groups_scope.

Variable (G : groups).

Lemma plus_gA : forall x1 x2 x3 : G, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. by apply: (@m_op_A G). Qed.

Lemma plus_g0l : forall x : G, 0 + x = x.
Proof. by apply: (@m_op_unitl G). Qed.

Lemma plus_opp_gl : forall x : G, - x + x = 0.
Proof. by case: G=> elt z o p; case. Qed.

Notation plus_g := Groups.plus.

Lemma plus_gKl : forall x : G, cancel (plus_g x) (plus_g (- x)).
Proof.
by move=> x y; rewrite plus_gA plus_opp_gl plus_g0l.
Qed.

Lemma plus_g_injl : forall x : G, injective (plus_g x).
Proof. move=> x; exact: can_inj (plus_gKl x). Qed.

Implicit Arguments plus_g_injl [].

Lemma plus_g0r : forall x : G, x + 0 = x.
Proof. by apply: (@m_op_unitr G). Qed.

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

Notation opp_g := Groups.opp.

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
Proof. by case: aG. Qed.

End GroupsProp.

Implicit Arguments plus_g_injl [G].
Implicit Arguments plus_g_injr [G].

Unset Implicit Arguments.