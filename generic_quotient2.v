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

(***************************)
(* This will soon change : *)
(***************************)
Section MFun.

Variable aT1 aT2 rT : Type.
Variable (qT1 : quotType aT1) (qT2 : quotType aT2) (qTr : quotType rT).
Variable f1 : aT1 -> rT.
Variable f2 : aT1 -> aT2 -> rT.
Local Notation ph1 := (phant qT1).
Local Notation ph2 := (phant qT2).
Local Notation phr := (phant qTr).
Local Notation Ph1 := (Phant qT1).
Local Notation Ph2 := (Phant qT2).
Local Notation Phr := (Phant qTr).

Definition mfun1_spec_of of ph1 := forall a, f1 (repr (\pi_qT1 a)) = f1 a.
Notation mf1_spec := (mfun1_spec_of Ph1).

Definition mfun2_spec_of of ph1 & ph2 := forall a b,
  f2 (repr (\pi_qT1 a)) (repr (\pi_qT2 b)) = f2 a b.
Notation mf2_spec := (mfun2_spec_of Ph1 Ph2).

Definition mfun1 of mf1_spec := fun (a : qT1) => f1 (repr a).

Definition mfun2 of mf2_spec :=
  fun (a : qT1) (b : qT2) => f2 (repr a) (repr b).

Lemma mfun1P : forall m a, mfun1 m (\pi a) = f1 a. Proof. by []. Qed.

Lemma mfun2P : forall m a b, mfun2 m (\pi a) (\pi b) = f2 a b.
Proof. by []. Qed.

Definition mop1_spec_of of ph1 & phr :=
  forall a, f1 (repr (\pi_qT1 a)) = f1 a %[m qTr].
Notation mop1_spec := (mop1_spec_of Ph1 Phr).

Definition mop2_spec_of of ph1 & ph2 & phr := forall a b,
  f2 (repr (\pi_qT1 a)) (repr (\pi_qT2 b)) = f2 a b %[m qTr].
Notation mop2_spec := (mop2_spec_of Ph1 Ph2 Phr).

Definition mop1 of mop1_spec := fun (a : qT1) => \mpi (f1 (repr a)) : qTr.

Definition mop2 of mop2_spec :=
  fun (a : qT1) (b : qT2) => \mpi (f2 (repr a) (repr b)) : qTr.

Lemma mop1P m a : mop1 m (\pi a) = \pi (f1 a).
Proof. by rewrite /mop1 mpiE. Qed.

Lemma mop2P m a b : mop2 m (\pi a) (\pi b) = \pi (f2 a b).
Proof. by rewrite /mop2 mpiE. Qed.

Definition mopP := (mop1P, mop2P, mfun1P, mfun2P).

(* Small generalization *)
Structure morph_fun1 := MorphFun1 {
  proj_mfun1 :> qT1 -> rT;
  _ a : proj_mfun1 (\pi a) = f1 a
}.
Lemma morph_fun1P (m : morph_fun1) a : m (\pi a) = f1 a.
Proof. by case: m. Qed.

Structure morph_fun2 := MorphFun2 {
  proj_mfun2 :> qT1 -> qT2 -> rT;
  _ a b : proj_mfun2 (\pi a) (\pi b) = f2 a b
}.
Lemma morph_fun2P (m : morph_fun2) a b : m (\pi a) (\pi b) = f2 a b.
Proof. by case: m. Qed.

Structure morph_op1 := MorphOp1 {
  proj_mop1 :> qT1 -> qTr;
  _ a : proj_mop1 (\pi a) = \pi (f1 a)
}.
Lemma morph_op1P (m : morph_op1) a : m (\pi a) = \pi (f1 a).
Proof. by case: m. Qed.

Structure morph_op2 := MorphOp2 {
  proj_mop2 :> qT1 -> qT2 -> qTr;
  _ a b : proj_mop2 (\pi a) (\pi b) = \pi (f2 a b)
}.
Lemma morph_op2P (m : morph_op2) a b : m (\pi a) (\pi b) = \pi (f2 a b).
Proof. by case: m. Qed.

Definition morph_opP := (morph_op1P, morph_op2P, morph_fun1P, morph_fun2P).

Canonical mfun1_morph m := MorphFun1 (mfun1P m).
Canonical mfun2_morph m := MorphFun2 (mfun2P m).
Canonical mop1_morph m := MorphOp1 (mop1P m).
Canonical mop2_morph m := MorphOp2 (mop2P m).

End MFun.

Notation mfun1_spec f qT := (@mfun1_spec_of _ _ _ f (Phant qT)).
Notation mfun11_spec f qT1 qT2 :=
  (@mfun2_spec_of _ _ _ _ _ f (Phant qT1) (Phant qT2)).
Notation mfun2_spec f qT := (mfun11_spec f qT qT).

Notation mop1_spec op qT := (@mop1_spec_of _ _ _ _ op (Phant qT) (Phant qT)).
Notation mop2_spec op qT :=
  (@mop2_spec_of _ _ _ _ _ _ op (Phant qT) (Phant qT) (Phant qT)).


Module MonoidQuotient.

Section Theory.
Variables (T : eqType) (idm : T).
Variable (qT : quotType T).
Notation idq := (\pi_qT idm).

Import Monoid.

Section Plain.
Variable mul : law idm.
Hypothesis mul_mop : mop2_spec mul qT.
Local Notation mulq := (mop2 mul_mop).

Lemma mulqA : associative mulq.
Proof.
by elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !mopP mulmA.
Qed.

Lemma mul1q : left_id idq mulq.
Proof. by elim/quotW=> x; rewrite !mop2P mul1m. Qed.

Lemma mulq1 : right_id idq mulq.
Proof. by elim/quotW=> x; rewrite !mop2P mulm1. Qed.

Canonical mulq_law := Law mulqA mul1q mulq1.
End Plain.

Section Commutative.
Variable mul : com_law idm.
Hypothesis mul_mop : mop2_spec mul qT.
Local Notation mulq := (mop2 mul_mop).

Lemma mulqC : commutative mulq.
Proof. by elim/quotW=> x; elim/quotW=> y; rewrite !mopP mulmC. Qed.

Canonical mulq_com_law := ComLaw mulqC.
End Commutative.

Section Mul.
Variable mul : mul_law idm.
Hypothesis mul_mop : mop2_spec mul qT.
Local Notation mulq := (mop2 mul_mop).

Lemma mul0q : left_zero idq mulq.
Proof. by elim/quotW=> x; rewrite !mopP mul0m. Qed.

Lemma mulq0 : right_zero idq mulq.
Proof. by elim/quotW=> x; rewrite !mopP mulm0. Qed.

Canonical mulq_mul_law := MulLaw mul0q mulq0.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Hypothesis mul_mop : mop2_spec mul qT.
Hypothesis add_mop : mop2_spec add qT.
Local Notation mulq := (mop2 mul_mop).
Local Notation addq := (mop2 add_mop).

Lemma mulq_addl : left_distributive mulq addq.
Proof.
by elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !mopP mulm_addl.
Qed.

Lemma mulq_addr : right_distributive mulq addq.
Proof.
by elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !mopP mulm_addr.
Qed.

Canonical addq_add_law := AddLaw mulq_addl mulq_addr.
End Add.

End Theory.
End MonoidQuotient.

Canonical MonoidQuotient.mulq_law.
Canonical MonoidQuotient.mulq_com_law.
Canonical MonoidQuotient.mulq_mul_law.
Canonical MonoidQuotient.addq_add_law.

