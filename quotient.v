(* -*- coding : utf-8 -*- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\pi_ Q" (at level 0, format "\pi_ Q").
Reserved Notation "x == y 'mod' Q" (at level 70, y at next level, 
  no associativity, format "x  ==  y  'mod'  Q").
Reserved Notation "\compat1_ Q" (at level 0, format "\compat1_ Q").
Reserved Notation "\compat2_ Q" (at level 0, format "\compat2_ Q").

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
Canonical Structure quot_eqType := Eval hnf in EqType _ quot_eqMixin.

Definition clone_quot (Q:Type) qT of phant_id (quot_sort qT) Q := qT.

Notation "\pi_ qT" := (@pi_of (Phant qT)).
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

Notation "[ 'quotType' 'of' Q ]" := (@clone_quot _ Q _ id)
 (at level 0, format "[ 'quotType'  'of'  Q ]") : form_scope.


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
Proof. 
move=> op Hyp. apply:compat1E=> x y exy. apply/eqP. exact: Hyp. 
Qed.


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
move=> op Hyp; apply:compat2E=> x y x' y' exy exy'. 
apply/eqP; exact: Hyp. 
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
move=> P Py x; set y := repr x; have -> : x = pi qT y; last exact: Py.
by rewrite /y /=; rewrite pi_repr.
Qed.

Lemma quotP : forall P,
  (forall y:T, (repr (\pi_qT y) = y)
  -> P (\pi_qT y)) -> forall x:qT, P x.
Proof.
move=> P Py x. set y := repr x; have -> : x = pi qT y.
   by rewrite /y /= pi_repr.
by apply: Py; rewrite /y /= /pi_of pi_repr.
Qed.

End Congruence.
Notation "\compat1_ T" := (compat1_of (Phant T)).
Notation "\compat2_ T" := (compat2_of (Phant T)).




