(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(* -*- coding : utf-8 -*- *)



(************************************************************************)
(* This is the next version of generic_quotient, with several           *)
(* generalizations and simplificatations. It is not compatible with the *)
(* previous version, but it should ultimatley replace it                *)
(************************************************************************)


Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\pi_ Q" (at level 0, format "\pi_ Q").
Reserved Notation "\pi" (at level 0, format "\pi").
Reserved Notation "x == y %[m Q ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  ==  y '/'  %[m  Q ] ']'").
Reserved Notation "x = y %[m Q ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  =  y '/'  %[m  Q ] ']'").
Reserved Notation "x != y %[m Q ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  !=  y '/'  %[m  Q ] ']'").
Reserved Notation "x <> y %[m Q ]" (at level 70, y at next level,
  no associativity,   format "'[hv ' x '/'  <>  y '/'  %[m  Q ] ']'").
(* Reserved Notation "x == y %[mod r ]" (at level 70, y at next level, *)
(*   no associativity,   format "'[hv ' x '/'  ==  y '/'  %[mod  r ] ']'"). *)
(* Reserved Notation "x = y %[mod r ]" (at level 70, y at next level, *)
(*   no associativity,   format "'[hv ' x '/'  =  y '/'  %[mod  r ] ']'"). *)
(* Reserved Notation "x != y %[mod r ]" (at level 70, y at next level, *)
(*   no associativity,   format "'[hv ' x '/'  !=  y '/'  %[mod  r ] ']'"). *)
(* Reserved Notation "x <> y %[mod r ]" (at level 70, y at next level, *)
(*   no associativity,   format "'[hv ' x '/'  <>  y '/'  %[mod  r ] ']'"). *)
Reserved Notation "[qT T %/ e ]" (at level 0, T at level 0,
  format "[qT T  %/  e ]", only parsing).
Reserved Notation "[mod e ]" (at level 0, format "[mod  e ]").

Delimit Scope quotient_scope with qT.
Local Open Scope quotient_scope.

Section QuotientDef.

Variable T : Type.

Record quot_class_of qT := QuotClass {
(* Record quot_mixin_of qT := QuotMixin { *)
  quot_repr : qT -> T;
  quot_pi : T -> qT;
  _ : cancel quot_repr quot_pi
}.

(* Record quot_class_of qT := QuotClass { *)
(*   quot_base :> Equality.class_of qT; *)
(*   quot_mixin :> quot_mixin_of qT *)
(* }. *)

Record quotType := QuotType {
  quot_sort :> Type;
  quot_class :> quot_class_of quot_sort
}.

Variable qT : quotType.
Definition pi_of of phant qT := quot_pi qT.
Local Notation "\pi" := (pi_of (Phant qT)).
Definition repr_of := quot_repr qT.

Lemma repr_ofK : cancel repr_of \pi.
Proof. by rewrite /pi_of /repr_of /=; case:qT=> [? []]. Qed.

(* Todo : when the previous modif are made, make this a helper to
   build the subtype mixin from the quotient axiom + do packaging
   stuff *)

(* Definition quot_eqType := EqType qT qT. *)
(* Canonical quot_eqType. *)

Definition clone_quot (Q : Type) qT cT of phant_id (quot_sort qT) Q
  & phant_id (quot_class qT) cT := @QuotType Q cT.

End QuotientDef.

Module Type PiSig.
Parameter f : forall (T : Type) (qT : quotType T), phant qT -> T -> qT.
Axiom E : f = pi_of.
End PiSig.

Module Pi : PiSig.
Definition f := pi_of.
Definition E := erefl f.
End Pi.

Module MPi : PiSig.
Definition f := pi_of.
Definition E := erefl f.
End MPi.

Module Type ReprSig.
Parameter f : forall (T : Type) (qT : quotType T), qT -> T.
Axiom E : f = repr_of.
End ReprSig.

Module Repr : ReprSig.
Definition f := repr_of.
Definition E := erefl f.
End Repr.

Notation repr := Repr.f.
Notation "\pi_ Q" := (@Pi.f _ _ (Phant Q)) : quotient_scope.
Notation "\pi" := (@Pi.f _ _ (Phant _))  (only parsing) : quotient_scope.
Notation "x == y %[m Q ]" := (\pi_Q x == \pi_Q y) : quotient_scope.
Notation "x = y %[m Q ]" := (\pi_Q x = \pi_Q y) : quotient_scope.
Notation "x != y %[m Q ]" := (\pi_Q x != \pi_Q y) : quotient_scope.
Notation "x <> y %[m Q ]" := (\pi_Q x <> \pi_Q y) : quotient_scope.

Local Notation "\mpi" := (@MPi.f _ _ (Phant _)).
Canonical mpi_unlock := Unlockable MPi.E.
Canonical pi_unlock := Unlockable Pi.E.
Canonical repr_unlock := Unlockable Repr.E.

Notation "[ 'quotType' 'of' Q ]" := (@clone_quot _ Q _ _ id id)
 (at level 0, format "[ 'quotType'  'of'  Q ]") : form_scope.

Implicit Arguments repr [T qT].
Prenex Implicits repr.

Section QuotTypeTheory.

Variable T : Type.
Variable qT : quotType T.

Lemma reprK : cancel repr \pi_qT.
Proof. by move=> x; rewrite !unlock repr_ofK. Qed.

Lemma mpiE : \mpi =1 \pi_qT.
Proof. by move=> x; rewrite !unlock. Qed.

Lemma quotW P : (forall y : T, P (\pi_qT y)) -> forall x : qT, P x.
Proof. by move=> Py x; rewrite -[x]reprK; apply: Py. Qed.

Lemma quotP P : (forall y : T, repr (\pi_qT y) = y -> P (\pi_qT y))
  -> forall x : qT, P x.
Proof. by move=> Py x; rewrite -[x]reprK; apply: Py; rewrite reprK. Qed.

End QuotTypeTheory.

Section SubTypeMixin.
Variable T : eqType.
Variable qT : quotType T.

Definition quot_Sub x (px : repr (\pi_qT x) == x) := \pi_qT x.

Lemma quot_reprK x Px : repr (@quot_Sub x Px) = x.
Proof. by rewrite /quot_Sub (eqP Px). Qed.

Lemma quot_sortPx (x : qT) : repr (\pi_qT (repr x)) == repr x.
Proof. by rewrite reprK eqxx. Qed.

Lemma quot_sortquot_Sub (x : qT) : x = quot_Sub (quot_sortPx x).
Proof. by rewrite /quot_Sub reprK. Qed.

Lemma quot_reprP K (PK : forall x Px, K (@quot_Sub x Px)) u : K u.
Proof. by rewrite (quot_sortquot_Sub u); apply: PK. Qed.
End SubTypeMixin.

(* Canonical quot_subType (T : eqType) (qT : quotType T) := *)
(*   SubType _ _ _ (@quot_reprP _ qT) (@quot_reprK _ qT). *)
(* Definition quot_eqMixin T (qT : quotType T) := Eval hnf in [eqMixin of qT by <:]. *)
(* Canonical quot_eqType T qT  := Eval hnf in EqType _ quot_eqMixin. *)

(* Lemma repr_val (T : eqType) (qT : quotType T) : val =1 (@repr T qT). *)
(* Proof. by []. Qed. *)


Section EquivRel.

Variable T : Type.

Lemma left_trans (e : rel T) :
  symmetric e -> transitive e -> left_transitive e.
Proof. by move=> s t ? * ?; apply/idP/idP; apply: t; rewrite // s. Qed.

Lemma right_trans (e : rel T) :
  symmetric e -> transitive e -> right_transitive e.
Proof. by move=> s t ? * x; rewrite ![e x _]s; apply: left_trans. Qed.

Record equiv_rel := EquivRel {
  equiv :> rel T;
  _ : reflexive equiv;
  _ : symmetric equiv;
  _ : transitive equiv
}.

Variable e : equiv_rel.

Lemma equiv_refl x : e x x. Proof. by case: e. Qed.
Lemma equiv_sym : symmetric e. Proof. by case: e. Qed.
Lemma equiv_trans : transitive e. Proof. by case: e. Qed.

Lemma eq_op_trans (T' : eqType) : transitive (@eq_op T').
Proof. by move=> x y z;  move/eqP->; move/eqP->. Qed.

Lemma equiv_ltrans: left_transitive e.
Proof. by apply: left_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

Lemma equiv_rtrans: right_transitive e.
Proof. by apply: right_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

End EquivRel.

Section EquivQuot.
(*
Canonical eq_op_Equiv :=
  @EquivRel _ (@eqxx _) (@eq_sym _) (@eq_op_trans _).
*)

Variable D : Type.
Variable T : choiceType.

Variable TD : T -> D.
Variable DT : D -> T.

Local Notation cancelTD e := (forall x, e (TD (DT x)) x).

Record equiv_rel_indirect := EquivRelIndirect {
  equiv_indirect :> rel D;
  _ : reflexive equiv_indirect;
  _ : symmetric equiv_indirect;
  _ : transitive equiv_indirect;
  _ : cancelTD equiv_indirect
}.

Implicit Type e : equiv_rel_indirect.

Definition equiv_indirect_refl e : reflexive e. Proof. by case: e. Qed.
Definition equiv_indirect_sym e : symmetric e. Proof. by case: e. Qed.
Definition equiv_indirect_trans e : transitive e. Proof. by case: e. Qed.
Definition equiv_indirect_TDK e : cancelTD e. Proof. by case: e. Qed.

Canonical equiv_rel_indirect_equivRel e :=
  @EquivRel _ e (equiv_indirect_refl e)
  (equiv_indirect_sym e) (@equiv_indirect_trans e).

Variable e : equiv_rel_indirect.
Local Notation TDK := (@equiv_indirect_TDK e).

Definition equivQuotEquiv : rel T := [rel x y | e (TD x) (TD y)].
Local Notation eT := equivQuotEquiv.

Lemma quotEquiv_refl x : eT x x. Proof. by rewrite /eT /= equiv_refl. Qed.
Lemma quotEquiv_sym : symmetric eT.
Proof. by move=> *; rewrite /eT /= equiv_sym. Qed.
Lemma quotEquiv_trans : transitive eT.
Proof. by rewrite /eT=> y x z /= exy eyz; rewrite (equiv_trans exy). Qed.

Canonical quotEquiv_equivRel :=
  EquivRel quotEquiv_refl quotEquiv_sym quotEquiv_trans.

Definition equiv_canon x : T := choose (eT x) (x).

Record equivQuotient := EquivQuotient {
  equiv_repr : T;
  _ : (frel equiv_canon) equiv_repr equiv_repr
}.

Definition equivQuot_of of (phantom (rel _) e) := equivQuotient.

Lemma equiv_canon_id : forall x, (invariant equiv_canon equiv_canon) x.
Proof.
move=> x /=; rewrite /equiv_canon (@eq_choose _ _ (eT x)).
  by rewrite (@choose_id _ (eT x) _ x) ?chooseP ?equiv_refl.
by move=> y; apply: equiv_ltrans; rewrite equiv_sym /= chooseP // equiv_refl.
Qed.

Definition equiv_pi (x : T) := EquivQuotient (equiv_canon_id x).

Lemma equiv_reprK : cancel equiv_repr equiv_pi.
Proof.
case=> x hx; move/eqP:(hx)=> hx'.
exact: (@val_inj _ _ [subType for equiv_repr by equivQuotient_rect]).
Qed.

Lemma equiv_pi_TD (x y : T) : reflect (equiv_pi x = equiv_pi y) (eT x y).
Proof.
apply: (iffP idP)=> hxy.
  apply: (can_inj equiv_reprK); rewrite /= /equiv_canon.
  rewrite -(@eq_choose _ (eT x) (eT y)); last first.
    by move=> z; rewrite /eT /=; apply: equiv_ltrans.
  by apply: choose_id; rewrite ?equiv_refl //.
rewrite (equiv_trans (chooseP (equiv_refl _ _))) //=.
move: hxy=> /(f_equal equiv_repr) /=; rewrite /equiv_canon=> ->.
by rewrite equiv_sym /= chooseP ?equiv_refl.
Qed.

Lemma equiv_pi_DT (x y : D) : reflect (equiv_pi (DT x) = equiv_pi (DT y)) (e x y).
Proof.
apply: (iffP idP)=> hxy.
  apply/equiv_pi_TD; rewrite /eT /=.
  by rewrite (equiv_ltrans (TDK _)) (equiv_rtrans (TDK _)).
rewrite -(equiv_ltrans (TDK _)) -(equiv_rtrans (TDK _)) /= -[e _ _]/(eT _ _).
by apply/equiv_pi_TD.
Qed.

Lemma equivQTP : cancel (TD \o equiv_repr) (equiv_pi \o DT).
Proof.
move=> x /=.
by rewrite (equiv_pi_TD _ (equiv_repr x) _) ?equiv_reprK /eT /= ?TDK.
Qed.

Local Notation qT := (equivQuot_of (Phantom (rel D) e)).
Definition EquivQuotClass := QuotClass equivQTP.
Canonical EquivQT := @QuotType D qT EquivQuotClass.

Lemma equivP : forall x y, reflect (x = y %[m qT]) (e x y).
Proof. by move=> x y; apply: (iffP (equiv_pi_DT _ _)); rewrite !unlock. Qed.

Definition equivEqMixin := CanEqMixin equiv_reprK.
Canonical equivEqType := EqType qT equivEqMixin.
Definition equivChoiceMixin := CanChoiceMixin equiv_reprK.
Canonical equivChoiceType := ChoiceType qT equivChoiceMixin.

Lemma equivE : forall x y, (x == y %[m qT]) = e x y.
Proof. by move=> x y; apply/idP/equivP=> /eqP. Qed.

End EquivQuot.

Notation "[qT D %/ e ]" :=
  (@equivQuot_of D _ _ _ _ (Phantom (rel D) e))
  (only parsing) : quotient_scope.

Notation "[mod e ]" := ([qT _ %/ e ]) : quotient_scope.
Notation "x == y %[mod r ]" := (x == y %[m [mod r]]) : quotient_scope.
Notation "x = y %[mod r ]" := (x = y %[m [mod r]]) : quotient_scope.
Notation "x != y %[mod r ]" := (x != y %[m [mod r]]) : quotient_scope.
Notation "x <> y %[mod r ]" := (x <> y %[m [mod r]]) : quotient_scope.

Hint Resolve equiv_refl.


(*******************)
(* About morphisms *)
(*******************)

Structure pi_morph T (x : T) := PiMorph {pi_op : T; _ : pi_op = x}.
Implicit Arguments PiMorph [T x].
Prenex Implicits PiMorph.

Section Morphism.

Variable T : Type.
Variable (qT : quotType T).

Canonical pi_morph_pi (x : T) := @PiMorph _ (\pi_qT x) (\pi x) (erefl _).
Lemma piE x (m : pi_morph (\pi_qT x)) : pi_op m = \pi x. Proof. by case: m. Qed.

Variable (f : T -> T) (g : T -> T -> T) (p : pred T) (r : rel T).
Variable (fq : qT -> qT) (gq : qT -> qT -> qT) (pq : pred qT) (rq : rel qT).
Hypothesis pi_f : {morph \pi : x / f x >-> fq x}.
Hypothesis pi_g : {morph \pi : x y / g x y >-> gq x y}.
Hypothesis pi_p : {mono \pi : x / p x >-> pq x}.
Hypothesis pi_r : {mono \pi : x y / r x y >-> rq x y}.
Variables (a b : T) (x : pi_morph (\pi_qT a)) (y : pi_morph (\pi_qT b)).

Lemma pi_morph1 : fq (pi_op x) = \pi (f a). Proof. by rewrite !piE. Qed.
Lemma pi_morph2 : gq (pi_op x) (pi_op y) = \pi (g a b). Proof. by rewrite !piE. Qed.
Lemma pi_mono1 : pq (pi_op x) = p a. Proof. by rewrite !piE. Qed.
Lemma pi_mono2 : rq (pi_op x) (pi_op y) = r a b. Proof. by rewrite !piE. Qed.

End Morphism.
Implicit Arguments pi_morph1 [T qT f fq].
Implicit Arguments pi_morph2 [T qT g gq].
Implicit Arguments pi_mono1 [T qT p pq].
Implicit Arguments pi_mono2 [T qT r rq].
Prenex Implicits pi_morph1 pi_morph2 pi_mono1 pi_mono2.

Notation PiMorph1 fq pi_f :=
  (fun a (x : pi_morph (\pi a)) => PiMorph (fq _) (pi_morph1 pi_f a x)).
Notation PiMorph2 gq pi_g :=
  (fun a b (x : pi_morph (\pi a)) (y : pi_morph (\pi b))
    => PiMorph (gq _ _) (pi_morph2 pi_g a b x y)).
Notation PiMono1 pq pi_p :=
  (fun a (x : pi_morph (\pi a)) => PiMorph (pq _) (pi_mono1 pi_p a x)).
Notation PiMono2 rq pi_r :=
  (fun a b (x : pi_morph (\pi a)) (y : pi_morph (\pi b))
    => PiMorph (rq _ _) (pi_mono2 pi_r a b x y)).

(* Module MonoidQuotient. *)

(* Section Theory. *)

(* Variables (T : eqType) (idm : T). *)
(* Variables (qT : quotType T) (idq : pi_morph (\pi_qT idm)). *)

(* Import Monoid. *)

(* Section OperatorStructure. *)
(* Variable op : law idm. *)

(* Structure pi_operator_morph := PiOperatorMorph { *)
(*   pi_operator :> law (pi_op idq); *)
(*   _ : {morph \pi : x y / op x y >-> pi_operator x y} *)
(* }. *)
(* Lemma pi_operatorP (opq : pi_operator_morph) : *)
(*   {morph \pi : x y / op x y >-> opq x y}. *)
(* Proof. by case: opq. Qed. *)

(* Canonical operator_pi_morph (opq : pi_operator_morph) := PiMorph2 opq (pi_operatorP opq). *)

(* End OperatorStructure. *)

(* Section Plain. *)
(* Variable mul : law idm. *)
(* Variable mulq : pi_operator_morph mul. *)

(* Lemma mulqA : associative mulq. *)
(* Proof. *)
(* by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK ![mulq _ _]piE mulmA. *)
(* Qed. *)

(* Lemma mul1q : left_id idq (pi_operator mulq). *)
(* Proof. by elim/quotW=> x; rewrite !mop2P mul1m. Qed. *)

(* Lemma mulq1 : right_id idq mulq. *)
(* Proof. by elim/quotW=> x; rewrite !mop2P mulm1. Qed. *)

(* Canonical mulq_law := Law mulqA mul1q mulq1. *)
(* End Plain. *)

(* Section Commutative. *)
(* Variable mul : com_law idm. *)
(* Hypothesis mul_mop : mop2_spec mul qT. *)
(* Local Notation mulq := (mop2 mul_mop). *)

(* Lemma mulqC : commutative mulq. *)
(* Proof. by elim/quotW=> x; elim/quotW=> y; rewrite !mopP mulmC. Qed. *)

(* Canonical mulq_com_law := ComLaw mulqC. *)
(* End Commutative. *)

(* Section Mul. *)
(* Variable mul : mul_law idm. *)
(* Hypothesis mul_mop : mop2_spec mul qT. *)
(* Local Notation mulq := (mop2 mul_mop). *)

(* Lemma mul0q : left_zero idq mulq. *)
(* Proof. by elim/quotW=> x; rewrite !mopP mul0m. Qed. *)

(* Lemma mulq0 : right_zero idq mulq. *)
(* Proof. by elim/quotW=> x; rewrite !mopP mulm0. Qed. *)

(* Canonical mulq_mul_law := MulLaw mul0q mulq0. *)
(* End Mul. *)

(* Section Add. *)
(* Variables (mul : T -> T -> T) (add : add_law idm mul). *)
(* Hypothesis mul_mop : mop2_spec mul qT. *)
(* Hypothesis add_mop : mop2_spec add qT. *)
(* Local Notation mulq := (mop2 mul_mop). *)
(* Local Notation addq := (mop2 add_mop). *)

(* Lemma mulq_addl : left_distributive mulq addq. *)
(* Proof. *)
(* by elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !mopP mulm_addl. *)
(* Qed. *)

(* Lemma mulq_addr : right_distributive mulq addq. *)
(* Proof. *)
(* by elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !mopP mulm_addr. *)
(* Qed. *)

(* Canonical addq_add_law := AddLaw mulq_addl mulq_addr. *)
(* End Add. *)

(* End Theory. *)
(* End MonoidQuotient. *)

(* Canonical MonoidQuotient.mulq_law. *)
(* Canonical MonoidQuotient.mulq_com_law. *)
(* Canonical MonoidQuotient.mulq_mul_law. *)
(* Canonical MonoidQuotient.addq_add_law. *)

