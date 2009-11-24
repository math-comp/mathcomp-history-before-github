Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype finfun tuple.
Require Import bigops ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\pi_ T" (at level 0, format "\pi_ T").
Reserved Notation "x == y 'mod' T"
  (at level 70, y at next level, no associativity, format "x  ==  y  'mod'  T").
Reserved Notation "\equiv_ T x y" (at level 2, format "\equiv_ T  x  y").
Reserved Notation "\compat1_ T" (at level 0, format "\compat1_ T").
Reserved Notation "\compat2_ T" (at level 0, format "\compat2_ T").


Section Quotient.

Variable T : eqType.

Record quotType := QuotType {
  quot_sort :> Type;
  repr : quot_sort -> T;
  pi : T -> quot_sort;
  _ : forall x : quot_sort, pi (repr x) = x
}.

Variable qT : quotType.
Definition pi_of of phant qT := pi qT.
Notation "\pi_ T" := (@pi_of (Phant T)).

Lemma pi_repr : forall x : qT, pi qT (repr x) = x.
Proof. by case:qT. Qed.

Definition quot_Sub x (px : repr (pi qT x) == x) := pi qT x.

Lemma reprK : forall x Px, repr (@quot_Sub x Px) = x.
Proof. by move=> x Px; rewrite /quot_Sub (eqP Px). Qed.

Lemma quot_sortPx : forall x:qT, repr (pi qT (repr x)) == repr x.
Proof. by move=> x; rewrite pi_repr eqxx. Qed.

Lemma quot_sortquot_Sub : forall x:qT, x = quot_Sub (quot_sortPx x).
Proof. by move=> x; apply: (can_inj pi_repr); rewrite reprK. Qed.

Lemma reprP : forall K (_ : forall x Px, K (@quot_Sub x Px)) u, K u.
Proof. by move=> K PK u; rewrite (quot_sortquot_Sub u); apply:PK. Qed.

Canonical Structure quot_subType := SubType _ _ _ reprP reprK.
Definition quot_eqMixin := Eval hnf in [eqMixin of qT by <:].
Canonical Structure quot_eqType := Eval hnf in EqType qT quot_eqMixin.

Definition repack_quot qT :=
  let: QuotType _ repr' pi' can := qT
  return {type of @QuotType for qT } -> _ in
  fun k => k repr' pi' can.

Notation "[ 'quotType' 'of' T ]" :=
   (repack_quot (fun r p can => @QuotType T r p can))
 (at level 0, format "[ 'quotType'  'of'  T ]") : form_scope.

Lemma Sub_pi : forall x Px, @Sub T _ _ x Px = pi qT x.
Proof. by move=> x Px; rewrite /= /quot_Sub. Qed.


Notation "\pi_ T" := (@pi_of (Phant T)).
Notation "x == y 'mod' T" := (\pi_T x == \pi_T y).
Lemma equivP : forall x y, x == y mod qT = (pi qT x == pi qT y).
Proof. by []. Qed.

Canonical Structure equivPred :=  @mkPredType T qT (fun x y => pi _ y == x).

Lemma in_qTE : forall (x:qT) (y:T), y \in x = (pi _ y == x).
Proof. by move=> x y; rewrite -topredE. Qed.
Lemma in_equiv : forall (x:qT) (y:T), y \in x = ((repr x) == y mod qT).
Proof. by move=> x y; rewrite in_qTE equivP pi_repr eq_sym. Qed.

End Quotient.

Notation "\pi_ T" := (@pi_of _ _ (Phant T)).
Notation "x == y 'mod' T" := (\pi_T x == \pi_T y).


Notation "[ 'quotType' 'of' T ]" :=
   (repack_quot (fun r p can => @QuotType T r p can))
 (at level 0, format "[ 'quotType'  'of'  T ]") : form_scope.


Section Congruence.

Variable T : eqType.
Variable qT : quotType T.

CoInductive compat1 S (op : T -> S) : Type :=
  Compat1 : (forall x:qT, {in x, forall x', op (repr x) = op x'}) -> compat1 op.
Definition compat1_of of phant qT := compat1.
Definition qT_op1 S op (cop : @compat1 S op) x :=  op (@repr T qT x).

Lemma compat1E : forall S (op:T -> S),
  (forall x y,  x == y mod qT -> op x = op y) -> compat1 op.
Proof.
by move=> ?? Px; constructor; move=> x x'; rewrite in_equiv; move/Px.
Qed.

Lemma compat1Epi : forall (op:T -> T),
  (forall x y,  (x == y mod qT) -> (op x == op y mod qT))
  -> compat1 (\pi_qT \o op).
Proof. move=> op Hyp. apply:compat1E=> x y exy. apply/eqP. exact: Hyp. Qed.


CoInductive compat2 S (op : T -> T -> S) : Type :=
  Compat2 : (forall x y:qT, {in x & y, forall x' y',
    op (repr x) (repr y) = op x' y'}) -> compat2 op.
Definition compat2_of of phant qT := compat2.
Definition qT_op2 S op (cop : @compat2 S op) x y :=
  op (@repr T qT x) (@repr T qT y) .

Lemma compat2E : forall S (op : T -> T -> S),
  (forall x x' y y',  x == x' mod qT -> y == y' mod qT
    -> op x y = op x' y') -> compat2 op.
Proof.
move=> S op Pxy; constructor; move=> x x' y y'.
rewrite !in_equiv => ??; exact: Pxy.
Qed.

Lemma compat2Epi : forall (op : T -> T -> T),
  (forall x x' y y',  x == x' mod qT -> y == y' mod qT
    -> op x y == op x' y' mod qT ) -> compat2 (fun x y => \pi_qT (op x y)).
Proof.
move=> op Hyp. apply:compat2E=> x y x' y' exy exy'.
apply/eqP. exact: Hyp.
Qed.

Lemma qT_op1E : forall S op cop x,
  @qT_op1 S op cop (\pi_qT x) = op x.
Proof. by move=> S f [cf] x /=; rewrite -(cf (\pi_qT x)) // in_qTE. Qed.

Lemma qT_op2E : forall S op cop x y,
  @qT_op2 S op cop (\pi_qT x) (\pi_qT y) = op x y.
Proof.
by move=> S f [cf] x y /=; rewrite -(cf (\pi_qT x) (\pi_qT y)) // in_qTE.
Qed.

Definition qTE := (qT_op1E, qT_op2E).

Lemma quotW : forall P, (forall y:T, P (\pi_qT y)) -> forall x:qT, P x.
Proof.
move=> P Py x. set y := repr x. have -> : x = pi qT y; last exact: Py.
by rewrite /y /=; rewrite pi_repr.
Qed.

Lemma quotP : forall P,
  (forall y:T, (repr (\pi_qT y) = y)
  -> P (\pi_qT y)) -> forall x:qT, P x.
Proof.
move=> P Py x. set y := repr x. have -> : x = pi qT y.
   by rewrite /y /= pi_repr.
by apply: Py; rewrite /y /= /pi_of pi_repr.
Qed.


End Congruence.
Notation "\compat1_ T" := (compat1_of (Phant T)).
Notation "\compat2_ T" := (compat2_of (Phant T)).


Section cartesianSquare.
Variable R : choiceType.

Definition cartesianSquare := (R * R)%type.

Definition csquare_to_tuple (x : cartesianSquare) := [tuple x.1; x.2].
Definition tuple_to_csquare (t: 2.-tuple R) :=  ([tnth t 0], [tnth t 1]).

Lemma csquare_tupleK : cancel csquare_to_tuple tuple_to_csquare.
Proof. by elim. Qed.

Definition csquareEqMixin := CanEqMixin csquare_tupleK.
(* Canonical Structure csquareEqType := Eval hnf in EqType csquareEqMixin. *)
Canonical Structure csquareEqType := Eval hnf in [eqType of cartesianSquare].
Definition csquareChoiceMixin := CanChoiceMixin csquare_tupleK.
Canonical Structure csquareChoiceType :=
  Eval hnf in ChoiceType cartesianSquare csquareChoiceMixin.

Identity Coercion csquareToProd : cartesianSquare >-> prod.

Definition csquare_of of phant R := cartesianSquare.
Identity Coercion type_csquare_of : csquare_of >-> cartesianSquare.

Notation "{ 'csquare' T }" := (csquare_of (Phant T)) (at level 0, format "{ 'csquare'  T }").
Canonical Structure csquareEqType' := Eval hnf in [eqType of {csquare R}].
Canonical Structure csquareChoiceType' := Eval hnf in [choiceType of {csquare R}].

End cartesianSquare.
Notation "{ 'csquare' T }" := (csquare_of (Phant T)) (at level 0, format "{ 'csquare'  T }").





