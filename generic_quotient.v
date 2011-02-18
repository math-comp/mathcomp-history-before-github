(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(* -*- coding : utf-8 -*- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\pi_ Q" (at level 0, format "\pi_ Q").
Reserved Notation "\pi" (at level 0, format "\pi").
Reserved Notation "x == y %{m Q }" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  ==  y '/'  %{m  Q } ']'").
Reserved Notation "x = y %{m Q }" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %{m  Q } ']'").
Reserved Notation "x == y %{mod r }" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  ==  y '/'  %{mod  r } ']'").
Reserved Notation "x = y %{mod r }" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %{mod  r } ']'").
Reserved Notation "{ T %/ e }" (at level 0, T at level 0,
  format "{  T  %/  e }", only parsing).
Reserved Notation "{mod e }" (at level 0, T at level 0,
  format "{mod  e }").
(* Reserved Notation "\compat1_ Q" (at level 0, format "\compat1_ Q"). *)
(* Reserved Notation "\compat2_ Q" (at level 0, format "\compat2_ Q"). *)

Section QuotientDef.

Variable T : eqType.

Record quotClass qT := QuotClass {
  quot_repr : qT -> T;
  pi : T -> qT;
  _ : forall x : qT, pi (quot_repr x) = x
}.

Record quotType := QuotType {
  quot_sort :> Type;
  quot_class :> quotClass quot_sort
}.

Variable qT : quotType.
Definition pi_of of phant qT := pi qT.
Notation "\pi_ T" := (@pi_of (Phant T)).

Definition repr := quot_repr qT.

Lemma reprK : forall x : qT, \pi_qT (repr x) = x.
Proof. by rewrite /pi_of /repr; case:qT=> [? []]. Qed.

Definition quot_Sub x (px : repr (\pi_qT x) == x) := \pi_qT x.

Lemma quot_reprK : forall x Px, repr (@quot_Sub x Px) = x.
Proof. by move=> x Px; rewrite /quot_Sub (eqP Px). Qed.

Lemma quot_sortPx : forall x:qT, repr (\pi_qT (repr x)) == repr x.
Proof. by move=> x; rewrite reprK eqxx. Qed.

Lemma quot_sortquot_Sub : forall x:qT, x = quot_Sub (quot_sortPx x).
Proof. by move=> x; apply: (can_inj reprK); rewrite quot_reprK. Qed.

Lemma quot_reprP : forall K (_ : forall x Px, K (@quot_Sub x Px)) u, K u.
Proof. by move=> K PK u; rewrite (quot_sortquot_Sub u); apply:PK. Qed.

Canonical Structure quot_subType := SubType _ _ _ quot_reprP quot_reprK.
Definition quot_eqMixin := Eval hnf in [eqMixin of qT by <:].
Canonical Structure quot_eqType := Eval hnf in EqType _ quot_eqMixin.

Definition clone_quot (Q:Type) qT of phant_id (quot_sort qT) Q := qT.

Notation "\pi_ qT" := (@pi_of (Phant qT)).
Notation "\pi" := (@pi_of (Phant _)).
Notation "x == y %{m Q }" := (\pi_Q x == \pi_Q y).
Notation "x = y %{m Q }" := (\pi_Q x = \pi_Q y).

Lemma pi_val : forall x : qT, \pi_qT (val x) = x.
Proof. exact: reprK. Qed.

Lemma repr_val : val =1 repr. Proof. by []. Qed.

(* Lemma eqq_def : forall x y, x == y mod qT = (\pi_qT x == \pi_qT y). *)
(* Proof. by []. Qed. *)

Lemma eqqP : forall x y, reflect (\pi_qT x = \pi_qT y) (x == y %{m qT}).
Proof. by move=> x y; apply: (iffP eqP). Qed.

Implicit Arguments eqqP [x y].

Canonical Structure eq_qTPred :=
  @mkPredType T qT (fun x y => \pi_qT y == x).

Lemma inqE : forall (x : qT) (y : T), y \in x = (\pi_qT y == x).
Proof. by move=> x y; rewrite -topredE. Qed.

Lemma inq_eq : forall (x : qT) (y : T), y \in x -> \pi_qT y = x.
Proof. by move=> x y; rewrite inqE; move/eqP. Qed.

Lemma in_eqqE : forall (x:qT) (y:T), y \in x = (y == (repr x) %{m qT}).
Proof. by move=> x y; rewrite inqE reprK. Qed.

Lemma quotW : forall P, (forall y : T, P (\pi_qT y)) -> forall x : qT, P x.
Proof. by move=> P Py x; rewrite -[x]reprK; apply: Py. Qed.

Lemma quotP : forall P, (forall y : T, repr (\pi_qT y) = y -> P (\pi_qT y))
  -> forall x : qT, P x.
Proof. by move=> P Py x; rewrite -[x]reprK; apply: Py; rewrite reprK. Qed.

End QuotientDef.

Notation "\pi_ qT" := (@pi_of _ _ (Phant qT)) (only parsing).
Notation "\pi" := \pi_(_).
Notation "x == y %{m Q }" := (\pi_Q x == \pi_Q y).
Notation "x = y %{m Q }" := (\pi_Q x = \pi_Q y).

Notation "[ 'quotType' 'of' Q ]" := (@clone_quot _ Q _ id)
 (at level 0, format "[ 'quotType'  'of'  Q ]") : form_scope.

Implicit Arguments eqqP [T qT x y].

Section EquivRel.

Variable T : choiceType.

Record equiv_rel := EquivRel {
  equiv :> rel T;
  _ : reflexive equiv;
  _ : symmetric equiv;
  _ : transitive equiv
}.

Lemma eq_op_trans : forall T : eqType, transitive (@eq_op T).
Proof. by move=> T' x y z; move/eqP->; move/eqP->. Qed.

Canonical Structure eq_op_Equiv :=
  @EquivRel _ (@eqxx _) (@eq_sym _) (@eq_op_trans _).

Variable e : equiv_rel.

Lemma equiv_refl : forall x, e x x. Proof. by case: e. Qed.
Lemma equiv_sym : symmetric e. Proof. by case: e. Qed.
Lemma equiv_trans : transitive e. Proof. by case: e. Qed.

Lemma equiv_ltrans: left_transitive e.
Proof.
move=> x y exy z; apply/idP/idP=> hz; last by rewrite (equiv_trans exy).
by rewrite (equiv_trans _ hz) // equiv_sym.
Qed.

Definition equiv_canon x : T := choose (e x) x.

Record equivQuotient := EquivQuotient {
  equiv_repr : T;
  _ : equiv_canon equiv_repr == equiv_repr
}.

Definition equivQuot_of of (phant T) & (phantom (rel _) e) := equivQuotient.

Lemma equiv_canon_id : forall x, equiv_canon (equiv_canon x) == (equiv_canon x).
Proof.
move=> x; rewrite /equiv_canon (@eq_choose _ _ (e x)).
  by rewrite (@choose_id _ (e x) _ x) ?chooseP ?equiv_refl.
by move=> y; apply: equiv_ltrans; rewrite equiv_sym chooseP // equiv_refl.
Qed.

Definition equiv_pi (x : T) := EquivQuotient (equiv_canon_id x).

Lemma equivQTP: forall x, equiv_pi (equiv_repr x) = x.
Proof.
case=> x hx; move/eqP:(hx)=> hx'.
exact: (@val_inj _ _ [subType for equiv_repr by equivQuotient_rect]).
Qed.

Definition EquivQuotClass := QuotClass equivQTP.
Canonical Structure EquivQT :=
  @QuotType _ (equivQuot_of (Phant _) (Phantom (rel _) e)) EquivQuotClass.

Local Notation qT := (equivQuot_of (Phant T) (Phantom (rel T) e)).

Lemma equivE : forall x y, e x y = (x == y %{m qT}).
Proof.
move=> x y; rewrite -(inj_eq (val_inj)) /= /repr /= /equiv_canon.
apply/idP/eqP=> hxy.
  rewrite -(@eq_choose _ (e x) (e y)); last by move=> z; apply: equiv_ltrans.
  by apply: choose_id; rewrite ?equiv_refl.
rewrite (equiv_trans (chooseP (equiv_refl _))) //.
by rewrite hxy equiv_sym chooseP ?equiv_refl.
Qed.

Lemma equivP : forall x y, reflect (x = y %{m qT}) (e x y).
Proof. by move=> x y; rewrite equivE; apply: (iffP eqP). Qed.

End EquivRel.

Notation "{ T %/ e }" := (equivQuot_of (Phant T) (Phantom (rel T) e)) (only parsing).
Notation "{mod e }" := (equivQuot_of (Phant _) (Phantom (rel _) e)).
Notation "x == y %{mod r }" := (x == y %{m {mod r}}).
Notation "x = y %{mod r }" := (x = y %{m {mod r}}).

Hint Resolve equiv_refl.

Implicit Arguments equivP [T e x y].

(* Section Test. *)

(* Check { nat %/ eq_op}. *)

(* Goal forall x y : nat, reflect (x = y) (x == y %{m { nat %/ eq_op}}). *)
(* Proof. *)
(* move=> x y /=. *)
(* move=> x y; apply: (iffP idP); last by move->. *)
(* by rewrite -equivE; move/eqP->. *)
(* Qed. *)

(* Variable T : choiceType. *)
(* Variable e : rel T. *)
(* Hypothesis exx : reflexive e. *)
(* Hypothesis e_sym : symmetric e. *)
(* Hypothesis e_trans : transitive e. *)

(* Notation "===" := e. *)
(* Notation "x === y" := (e x y) (at level 70, no associativity). *)
(* Canonical Structure e_equivRel := EquivRel exx e_sym e_trans. *)
(* Check {T T / e}. *)

(* Goal forall x y : T, e x y -> (x = y mod %{m T/e}). *)
(* Proof. *)
(* move=> x y /=. *)
(* rewrite equiv_eqqT. *)
(* move/eqqTP. *)
(* move/equivP=> /=. *)
(* by move/equivP. *)
(* Qed. *)

(* End Test. *)

(* Todo : restate and refresh *)
(* Section Congruence. *)

(* Variable T : eqType. *)
(* Variable qT : quotType T. *)

(* (* Record compat := Compat { *) *)
(* (*   compatl :> T; *) *)
(* (*   compatr : T; *) *)
(* (*   _ : compatl = compatr *) *)
(* (* }. *) *)

(* (* Lemma compatP : forall c : compat, compatl c = compatr c. *) *)
(* (* Proof. by case. Qed. *) *)

(* (* Inductive types_of_types : seq Type -> Type := *) *)
(* (* | ToTNil : types_of_types [::] *) *)
(* (* | ToTCons T (A : T) sT (sA : types_of_types sT) : types_of_types (T :: sT). *) *)

(* (* Fixpoint op_type aTs rT :=  *) *)
(* (*   if aTs is aT :: aTs' then aT -> op_type aTs' rT else rT. *) *)

(* (* Eval compute in op_type [::nat : Type; bool : Type] nat. *) *)

(* (* Fixpoint apply_args (aTs : seq Type) (rT : Type) (xs : types_of_types aTs):= *) *)
(* (*   match xs in types_of_types aTs return op_type aTs rT -> rT with *) *)
(* (*     | ToTNil => fun f => f *) *)
(* (*     | ToTCons T x aTs xs => fun f => apply_args _ xs (f x) *) *)
(* (*   end. *) *)

(* (* Definition compat (aTs : seq eqType) (aQs : types_of_types (map quotType aTs))  *) *)
(* (*   (rT : eqType) (rQ  : quotType rT) (f : op_type (map Equality.sort aTs) rT) := *) *)
(* (*   let fix aux (aTs' : seq eqType) (aQs' : types_of_types (map quotType aTs'))  *) *)
(* (*     (aTs'' : seq Type) (xs ys : types_of_types aTs'') :=  *) *)
(* (*     match aQs' in types_of_types aTs' *) *)
(* (*       return op_type (map Equality.sort aTs) rT -> rT with *) *)
(* (*       | ToTNil => apply_args xs f = apply_args ys f *) *)
(* (*       | ToTCons T Q aTs' aQs' =>  *) *)
(* (*         forall x y : T, x = y mod Q -> aux aTs' aQs' _ (rcons xs x) (rcons ys y) *) *)
(* (*     end in aux aTs aQs [::] [::] [::]. *) *)



(*   (rT : Type) (rQ : quotType rT) (f : op_type sT rT)  *)
(*   (xs ys : types_of_types sQ) : Prop := *)
(*   match sQ with *)
(*     | ToTNil => @apply_args xs f = apply_args ys f *)
(*     | ToTCons T Q sT' sQ' => forall x : T,  *)
(*       @compat sT sQ rT rQ f  *)
(*   end. *)





(* Lemma compatlE : forall c: compat, \pi_qT c = c. *)
(* Proof. by move=> c; apply: inqT_eq; apply: compatP. Qed. *)

(* Lemma compatrE : forall c: compat, (c : qT) = \pi_qT c. *)
(* Proof. by move=> c; rewrite compatlE. Qed. *)



(* Lemma compatE : cop x = op (val x) *)
(* cop (\pi_qT x) = op x. *)

(* CoInductive compat1 S (op : T -> S) : Type := *)
(*   Compat1 : (forall x:qT, {in x, forall x', op (repr x) = op x'}) -> compat1 op. *)
(* Definition compat1_of of phant qT := compat1. *)
(* Definition qT_op1 S op (cop : @compat1 S op) x :=  op (@repr T qT x). *)

(* Lemma compat1E : forall S (op:T -> S), *)
(*   (forall x y,  x == y mod qT -> op x = op y) -> compat1 op. *)
(* Proof. *)
(* by move=> ?? Px; constructor; move=> x x'; rewrite in_equiv; move/Px. *)
(* Qed. *)

(* Lemma compat1Epi : forall (op:T -> T), *)
(*   (forall x y,  (x == y mod qT) -> (op x == op y mod qT)) *)
(*   -> compat1 (\pi_qT \o op). *)
(* Proof.  *)
(* move=> op Hyp. apply:compat1E=> x y exy. apply/eqP. exact: Hyp.  *)
(* Qed. *)


(* CoInductive compat2 S (op : T -> T -> S) : Type := *)
(*   Compat2 : (forall x y:qT, {in x & y, forall x' y', *)
(*     op (repr x) (repr y) = op x' y'}) -> compat2 op. *)
(* Definition compat2_of of phant qT := compat2. *)
(* Definition qT_op2 S op (cop : @compat2 S op) x y := *)
(*   op (@repr T qT x) (@repr T qT y) . *)

(* Lemma compat2E : forall S (op : T -> T -> S), *)
(*   (forall x x' y y',  x == x' mod qT -> y == y' mod qT *)
(*     -> op x y = op x' y') -> compat2 op. *)
(* Proof. *)
(* move=> S op Pxy; constructor; move=> x x' y y'. *)
(* rewrite !in_equiv => ??; exact: Pxy. *)
(* Qed. *)

(* Lemma compat2Epi : forall (op : T -> T -> T), *)
(*   (forall x x' y y',  x == x' mod qT -> y == y' mod qT *)
(*     -> op x y == op x' y' mod qT ) -> compat2 (fun x y => \pi_qT (op x y)). *)
(* Proof. *)
(* move=> op Hyp; apply:compat2E=> x y x' y' exy exy'.  *)
(* apply/eqP; exact: Hyp.  *)
(* Qed. *)

(* Lemma qT_op1E : forall S op cop x, *)
(*   @qT_op1 S op cop (\pi_qT x) = op x. *)
(* Proof. by move=> S f [cf] x /=; rewrite -(cf (\pi_qT x)) // in_qTE. Qed. *)

(* Lemma qT_op2E : forall S op cop x y, *)
(*   @qT_op2 S op cop (\pi_qT x) (\pi_qT y) = op x y. *)
(* Proof. *)
(* by move=> S f [cf] x y /=; rewrite -(cf (\pi_qT x) (\pi_qT y)) // in_qTE. *)
(* Qed. *)

(* Definition qTE := (qT_op1E, qT_op2E). *)

(* End Congruence. *)

(* Notation "\compat1_ T" := (compat1_of (Phant T)). *)
(* Notation "\compat2_ T" := (compat2_of (Phant T)). *)
