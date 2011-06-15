(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(* -*- coding : utf-8 -*- *)
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
(* Reserved Notation "\compat1_ Q" (at level 0, format "\compat1_ Q"). *)
(* Reserved Notation "\compat2_ Q" (at level 0, format "\compat2_ Q"). *)

Delimit Scope quotient_scope with qT.
Local Open Scope quotient_scope.

Section QuotientDef.

Variable T : eqType.

Record quotClass qT := QuotClass {
  quot_repr : qT -> T;
  pi : T -> qT;
  _ : cancel quot_repr pi
}.

Record quotType := QuotType {
  quot_sort :> Type; (* Todo : insert here the fact it's a subType,
                        and remove quot_repr in quotClass *)
  quot_class :> quotClass quot_sort
  (* Todo : add here the Equivalence.class_of *)
}.

Variable qT : quotType.
Definition pi_of of phant qT := pi qT.
Notation "\pi_ T" := (@pi_of (Phant T)).

Definition repr := quot_repr qT.

Lemma pi_repr : cancel repr \pi_qT.
Proof. by rewrite /pi_of /repr /=; case:qT=> [? []]. Qed.

(* Todo : when the previous modif are made, make this a helper to
   build the subtype mixin from the quotient axiom + do packaging
   stuff *)

Section SubTypeMixin.
Definition quot_Sub x (px : repr (\pi_qT x) == x) := \pi_qT x.

Lemma quot_reprK x Px : repr (@quot_Sub x Px) = x.
Proof. by rewrite /quot_Sub (eqP Px). Qed.

Lemma quot_sortPx (x : qT) : repr (\pi_qT (repr x)) == repr x.
Proof. by rewrite pi_repr eqxx. Qed.

Lemma quot_sortquot_Sub (x : qT) : x = quot_Sub (quot_sortPx x).
Proof. by apply: (can_inj pi_repr); rewrite quot_reprK. Qed.

Lemma quot_reprP K (PK : forall x Px, K (@quot_Sub x Px)) u : K u.
Proof. by rewrite (quot_sortquot_Sub u); apply: PK. Qed.
End SubTypeMixin.

Canonical quot_subType := SubType _ _ _ quot_reprP quot_reprK.
Definition quot_eqMixin := Eval hnf in [eqMixin of qT by <:].
Canonical quot_eqType := Eval hnf in EqType _ quot_eqMixin.

Definition clone_quot (Q:Type) qT of phant_id (quot_sort qT) Q := qT.

Lemma repr_val : val =1 repr. Proof. by []. Qed.

End QuotientDef.

Module Type MorphOpSig.
Parameter morphop : forall (T : eqType) (qT : quotType T), phant qT -> T -> qT.
Axiom morphopE : morphop = pi_of.
End MorphOpSig.

Module PiOp : MorphOpSig.
Definition morphop := pi_of.
Lemma morphopE : morphop = pi_of. Proof. by []. Qed.
End PiOp.

Module MorphOp : MorphOpSig.
Definition morphop := pi_of.
Lemma morphopE : morphop = pi_of. Proof. by []. Qed.
End MorphOp.

Notation "\pi_ qT" := (@PiOp.morphop _ _ (Phant qT)) (only parsing) : quotient_scope.
Notation "\pi" := \pi_(_) : quotient_scope.
Notation "x == y %[m Q ]" := (\pi_Q x == \pi_Q y) : quotient_scope.
Notation "x = y %[m Q ]" := (\pi_Q x = \pi_Q y) : quotient_scope.
Notation "x != y %[m Q ]" := (\pi_Q x != \pi_Q y) : quotient_scope.
Notation "x <> y %[m Q ]" := (\pi_Q x <> \pi_Q y) : quotient_scope.

Notation "\mpi" := (@MorphOp.morphop _ _ (Phant _)) (only parsing).
Canonical morphop_mpi_unlock := Unlockable MorphOp.morphopE.
Canonical morphop_pi_unlock := Unlockable PiOp.morphopE.

Notation "[ 'quotType' 'of' Q ]" := (@clone_quot _ Q _ id)
 (at level 0, format "[ 'quotType'  'of'  Q ]") : form_scope.

Section QuotTypeTheory.

Variable T : eqType.
Variable qT : quotType T.

Lemma reprK : cancel (@repr _ _) \pi_qT.
Proof. by move=> x; rewrite unlock pi_repr. Qed.

Lemma repr_mpi : cancel (@repr T qT) \mpi.
Proof. by move=> x; rewrite unlock pi_repr. Qed.

Lemma mpiE : \mpi =1 \pi_qT.
Proof. by move=> x; rewrite !unlock. Qed.

Lemma quotW P : (forall y : T, P (\pi_qT y)) -> forall x : qT, P x.
Proof. by move=> Py x; rewrite -[x]reprK; apply: Py. Qed.

Lemma quotP P : (forall y : T, repr (\pi_qT y) = y -> P (\pi_qT y))
  -> forall x : qT, P x.
Proof. by move=> Py x; rewrite -[x]reprK; apply: Py; rewrite reprK. Qed.

End QuotTypeTheory.

Implicit Arguments repr [T qT].
Prenex Implicits repr.

Section EquivRel.

Lemma left_trans T (e : rel T) :
  symmetric e -> transitive e -> left_transitive e.
Proof. by move=> s t ? * ?; apply/idP/idP; apply: t; rewrite // s. Qed.

Lemma right_trans T0 (e : rel T0) :
  symmetric e -> transitive e -> right_transitive e.
Proof. by move=> s t ? * x; rewrite ![e x _]s; apply: left_trans. Qed.

Variable T : choiceType.

Record equiv_rel := EquivRel {
  equiv :> rel T;
  _ : reflexive equiv;
  _ : symmetric equiv;
  _ : transitive equiv
}.

Lemma eq_op_trans (T' : eqType) : transitive (@eq_op T').
Proof. by move=> x y z;  move/eqP->; move/eqP->. Qed.

(*
Canonical eq_op_Equiv :=
  @EquivRel _ (@eqxx _) (@eq_sym _) (@eq_op_trans _).
*)

Variable e : equiv_rel.

Lemma equiv_refl x : e x x. Proof. by case: e. Qed.
Lemma equiv_sym : symmetric e. Proof. by case: e. Qed.
Lemma equiv_trans : transitive e. Proof. by case: e. Qed.

Lemma equiv_ltrans: left_transitive e.
Proof. by apply: left_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

Lemma equiv_rtrans: right_transitive e.
Proof. by apply: right_trans; [apply: equiv_sym|apply: equiv_trans]. Qed.

Definition equiv_canon x : T := choose (e x) x.

Record equivQuotient := EquivQuotient {
  equiv_repr : T;
  _ : (frel equiv_canon) equiv_repr equiv_repr
}.

Definition equivQuot_of of (phant T) & (phantom (rel _) e) := equivQuotient.

Lemma equiv_canon_id : forall x, (invariant equiv_canon equiv_canon) x.
Proof.
move=> x /=; rewrite /equiv_canon (@eq_choose _ _ (e x)).
  by rewrite (@choose_id _ (e x) _ x) ?chooseP ?equiv_refl.
by move=> y; apply: equiv_ltrans; rewrite equiv_sym chooseP // equiv_refl.
Qed.

Definition equiv_pi (x : T) := EquivQuotient (equiv_canon_id x).

Lemma equivQTP : cancel equiv_repr equiv_pi.
Proof.
case=> x hx; move/eqP:(hx)=> hx'.
exact: (@val_inj _ _ [subType for equiv_repr by equivQuotient_rect]).
Qed.

Local Notation qT := (equivQuot_of (Phant T) (Phantom (rel T) e)).
Definition EquivQuotClass := QuotClass equivQTP.
Canonical EquivQT := @QuotType T qT EquivQuotClass.
Definition EquiveqMixin := [eqMixin of [quotType of qT] by <:].
Canonical EquiveqType := EqType qT EquiveqMixin.
Definition EquivchoiceMixin := [choiceMixin of [quotType of qT] by <:].
Canonical EquivchoiceType := ChoiceType qT EquivchoiceMixin.

Lemma equivE x y : e x y = (x == y %[m qT]).
Proof.
rewrite -(inj_eq (val_inj)) unlock /= /repr /= /equiv_canon.
apply/idP/eqP=> hxy.
  rewrite -(@eq_choose _ (e x) (e y)); last by move=> z; apply: equiv_ltrans.
  by apply: choose_id; rewrite ?equiv_refl.
rewrite (equiv_trans (chooseP (equiv_refl _))) //.
by rewrite hxy equiv_sym chooseP ?equiv_refl.
Qed.

Lemma equivP : forall x y, reflect (x = y %[m qT]) (e x y).
Proof. by move=> x y; rewrite equivE; apply: (iffP eqP). Qed.

End EquivRel.

Notation "[qT T %/ e ]" := (equivQuot_of (Phant T) (Phantom (rel T) e)) (only parsing) : quotient_scope.
Notation "[mod e ]" := (equivQuot_of (Phant _) (Phantom (rel _) e)) : quotient_scope.
Notation "x == y %[mod r ]" := (x == y %[m [mod r]]) : quotient_scope.
Notation "x = y %[mod r ]" := (x = y %[m [mod r]]) : quotient_scope.
Notation "x != y %[mod r ]" := (x != y %[m [mod r]]) : quotient_scope.
Notation "x <> y %[mod r ]" := (x <> y %[m [mod r]]) : quotient_scope.

Hint Resolve equiv_refl.

Implicit Arguments equivP [T e x y].

(* Section Test. *)

(* Check [qT nat %/ eq_op]. *)

(* Goal forall x y : nat, reflect (x = y) (x == y %[m [qT nat %/ eq_op]]). *)
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
(* Canonical e_equivRel := EquivRel exx e_sym e_trans. *)
(* Check [mT T / e]. *)

(* Goal forall x y : T, e x y -> (x = y mod %[m T/e]). *)
(* Proof. *)
(* move=> x y /=. *)
(* rewrite equiv_eqqT. *)
(* move/eqqTP. *)
(* move/equivP=> /=. *)
(* by move/equivP. *)
(* Qed. *)

(* End Test. *)

Section MFun.

Variable aT1 aT2 rT : eqType.
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
(* Todo : commutation of mopP with big and map and others *)

End MFun.

Notation mfun1_spec f qT := (@mfun1_spec_of _ _ _ f (Phant qT)).
Notation mfun11_spec f qT1 qT2 :=
  (@mfun2_spec_of _ _ _ _ _ f (Phant qT1) (Phant qT2)).
Notation mfun2_spec f qT := (mfun11_spec f qT qT).

Notation mop1_spec op qT := (@mop1_spec_of _ _ _ _ op (Phant qT) (Phant qT)).
Notation mop2_spec op qT :=
  (@mop2_spec_of _ _ _ _ _ _ op (Phant qT) (Phant qT) (Phant qT)).

Definition chgQuot (T : eqType) (qT qT' : quotType T) : qT -> qT' := \pi \o repr.
Implicit Arguments chgQuot [T qT qT'].

Lemma chgQuotE  (T : eqType) (qT : quotType T) (x : qT) : chgQuot x = x.
Proof. exact: reprK. Qed.

Section QuotientMorphism.

Variable T : eqType.
Variable (qT : quotType T) (qT' : quotType T).
Variable op1 : T -> T.
Variable op2 : T -> T -> T.
Variable m1 : morph_op1 qT qT op1.
Variable m2 : morph_op2 qT qT qT op2.
Variable m1' : morph_op1 qT' qT' op1.
Variable m2' : morph_op2 qT' qT' qT' op2.

Definition chgQuotOp1 (x : qT') : qT' := chgQuot (m1 (chgQuot x)).
Definition chgQuotOp2 (x y : qT') : qT' := chgQuot (m2 (chgQuot x) (chgQuot y)).

Hypothesis equiv_qT_qT' : forall x y, (x == y %[m qT]) = (x == y %[m qT']).

Fact same_qT_qT' x y : (x = y %[m qT]) <-> (x = y %[m qT']).
Proof. by split=> /eqP; rewrite (equiv_qT_qT', =^~ equiv_qT_qT')=> /eqP. Qed.

Lemma chgQuot_pi (x : T) : chgQuot (\pi_qT x) = \pi_qT' x.
Proof. by rewrite /chgQuot /= -same_qT_qT' reprK. Qed.

Fact chgQuot_pi' (x : T) : chgQuot (\pi_qT' x) = \pi_qT x.
Proof. by rewrite /chgQuot /= same_qT_qT' reprK. Qed.

Lemma chgQuotK (x : qT) : chgQuot (chgQuot x : qT') = x.
Proof. by rewrite {2}/chgQuot /= chgQuot_pi' /chgQuot !reprK. Qed.

Lemma chgQuot_bij : bijective (@chgQuot _ qT qT').
Proof.
by apply: (@Bijective _ _ _ (@chgQuot _ _ qT))=> x;
  rewrite /chgQuot /= -[x]reprK (same_qT_qT', =^~ same_qT_qT') !reprK.
Qed.

Lemma sameQuotMorphOp1 x : chgQuot (m1 (chgQuot x)) = m1' x.
Proof. by rewrite morph_opP chgQuot_pi -(morph_op1P m1') reprK. Qed.

Lemma sameQuotMorphOp2 x y : chgQuot (m2 (chgQuot x) (chgQuot y)) = m2' x y.
Proof. by rewrite morph_opP chgQuot_pi -(morph_op2P m2') !reprK. Qed.

Lemma chgQuotOp1P x : chgQuotOp1 (\pi x) = \pi (op1 x).
Proof. by rewrite /chgQuotOp1 chgQuot_pi' morph_opP chgQuot_pi. Qed.
Definition chgQuotOp1_morph := MorphOp1 chgQuotOp1P.

Lemma chgQuotOp2P x y : chgQuotOp2 (\pi x) (\pi y) = \pi (op2 x y).
Proof. by rewrite /chgQuotOp2 !chgQuot_pi' morph_opP chgQuot_pi. Qed.
Definition chgQuotOp2_morph := MorphOp2 chgQuotOp2P.

End QuotientMorphism.


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



(* Todo : generalize morphisms *)
(* Section Congruence. *)
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



