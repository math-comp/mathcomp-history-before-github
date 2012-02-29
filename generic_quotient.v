(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(* -*- coding : utf-8 -*- *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq bigop.

(*******)
(* Doc *)
(*******)

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
Reserved Notation "{mod e }" (at level 0, T at level 0,
  format "{mod  e }", only parsing).

Delimit Scope quotient_scope with qT.
Local Open Scope quotient_scope.

Section QuotientDef.

Variable T : Type.

Record quot_mixin_of qT := QuotClass {
  quot_repr : qT -> T;
  quot_pi : T -> qT;
  _ : cancel quot_repr quot_pi
}.

Notation quot_class_of := quot_mixin_of.

Record quotType := QuotTypePack {
  quot_sort :> Type;
  quot_class :> quot_class_of quot_sort;
  _ : Type
}.

Definition QuotType_pack qT m := @QuotTypePack qT m qT.

Variable qT : quotType.
Definition pi_of of phant qT := quot_pi qT.
Local Notation "\pi" := (pi_of (Phant qT)).
Definition repr_of := quot_repr qT.

Lemma repr_ofK : cancel repr_of \pi.
Proof. by rewrite /pi_of /repr_of /=; case:qT=> [? []]. Qed.

Definition QuotType_clone (Q : Type) qT cT 
  of phant_id (quot_class qT) cT := @QuotTypePack Q cT Q.

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

Notation quot_class_of := quot_mixin_of.
Notation QuotType Q m := (@QuotType_pack _ Q m).
Notation "[ 'quotType' 'of' Q ]" := (@QuotType_clone _ Q _ _ id)
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

(*******************)
(* About morphisms *)
(*******************)

Structure pi_morph T (x : T) := PiMorph {pi_op : T; _ : x = pi_op}.
Lemma piE (T : Type) (x : T) (m : pi_morph x) : pi_op m = x. Proof. by case: m. Qed.

Canonical pi_morph_pi T (qT : quotType T) (x : T) :=
  @PiMorph _ (\pi_qT x) (\pi x) (erefl _).

Implicit Arguments PiMorph [T x pi_op].
Prenex Implicits PiMorph.

Section Morphism.

Variables T U : Type.
Variable (qT : quotType T).

Variable (f : T -> T) (g : T -> T -> T) (p : T -> U) (r : T -> T -> U).
Variable (fq : qT -> qT) (gq : qT -> qT -> qT) (pq : qT -> U) (rq : qT -> qT -> U).
Hypothesis pi_f : {morph \pi : x / f x >-> fq x}.
Hypothesis pi_g : {morph \pi : x y / g x y >-> gq x y}.
Hypothesis pi_p : {mono \pi : x / p x >-> pq x}.
Hypothesis pi_r : {mono \pi : x y / r x y >-> rq x y}.
Variables (a b : T) (x : pi_morph (\pi_qT a)) (y : pi_morph (\pi_qT b)).

(* Internal Lemmmas : do not use directly *)
Lemma pi_morph1 : \pi (f a) = fq (pi_op x). Proof. by rewrite !piE. Qed.
Lemma pi_morph2 : \pi (g a b) = gq (pi_op x) (pi_op y). Proof. by rewrite !piE. Qed.
Lemma pi_mono1 : p a = pq (pi_op x). Proof. by rewrite !piE. Qed.
Lemma pi_mono2 : r a b = rq (pi_op x) (pi_op y). Proof. by rewrite !piE. Qed.

End Morphism.

Implicit Arguments pi_morph1 [T qT f fq].
Implicit Arguments pi_morph2 [T qT g gq].
Implicit Arguments pi_mono1 [T U qT p pq].
Implicit Arguments pi_mono2 [T U qT r rq].
Prenex Implicits pi_morph1 pi_morph2 pi_mono1 pi_mono2.


Notation mk_embed qT e := (locked (fun x => \pi_qT (e x) : qT)).
Notation mk_mconst qT x := (locked (\pi_qT x : qT)).
Notation mk_mop1 qT f := (locked (fun x : qT => \pi_qT (f (repr x)) : qT)).
Notation mk_mop2 qT g := 
  (locked (fun x y : qT => \pi_qT (g (repr x) (repr y)) : qT)).
Notation mk_mfun1 qT f := (locked (fun x : qT => f (repr x))).
Notation mk_mfun2 qT g := (locked (fun x y : qT => g (repr x) (repr y))).

Notation PiConst a := (@PiMorph _ _ a (lock _)).
Notation PiMorph1 pi_f :=
  (fun a (x : pi_morph (\pi a)) => PiMorph (pi_morph1 pi_f a x)).
Notation PiMorph2 pi_g :=
  (fun a b (x : pi_morph (\pi a)) (y : pi_morph (\pi b))
    => PiMorph (pi_morph2 pi_g a b x y)).
Notation PiMono1 pi_p :=
  (fun a (x : pi_morph (\pi a)) => PiMorph (pi_mono1 pi_p a x)).
Notation PiMono2 pi_r :=
  (fun a b (x : pi_morph (\pi a)) (y : pi_morph (\pi b))
    => PiMorph (pi_mono2 pi_r a b x y)).

Lemma eq_lock T T' e : e =1 (@locked (T -> T') (fun x : T => e x)).
Proof. by rewrite -lock. Qed.
Prenex Implicits eq_lock.

Notation PiEmbed e := 
  (fun x => @PiMorph _ _ (e x) (eq_lock (fun _ => \pi _) _)).

Section EqQuotTypeStructure.

Variable T : Type.
Variable eq_quot_op : rel T.

Definition eq_quot_mixin_of (Q : Type) (qc : quot_class_of T Q)
  (ec : Equality.class_of Q) :=
  {mono \pi_(QuotTypePack qc Q) : x y /
   eq_quot_op x y >-> @eq_op (Equality.Pack ec Q) x y}.

Record eq_quot_class_of (Q : Type) : Type := EqQuotClass {
  eq_quot_quot_class :> quot_class_of T Q;
  eq_quot_eq_mixin :> Equality.class_of Q;
  pi_eq_quot_mixin :> eq_quot_mixin_of eq_quot_quot_class eq_quot_eq_mixin
}.

Record eqQuotType : Type := EqQuotTypePack {
  eq_quot_sort :> Type;
  _ : eq_quot_class_of eq_quot_sort;
  _ : Type
}.

Implicit Type eqT : eqQuotType.

Definition eq_quot_class eqT : eq_quot_class_of eqT :=
  let: EqQuotTypePack _ cT _ as qT' := eqT return eq_quot_class_of qT' in cT.

Canonical eqQuotType_eqType eqT := EqType eqT (eq_quot_class eqT).
Canonical eqQuotType_quotType eqT := QuotType eqT (eq_quot_class eqT).

Coercion eqQuotType_eqType : eqQuotType >-> eqType.
Coercion eqQuotType_quotType : eqQuotType >-> quotType.

Definition EqQuotType_pack Q :=
  fun (qT : quotType T) (eT : eqType) qc ec 
  of phant_id (quot_class qT) qc & phant_id (Equality.class eT) ec => 
    fun m => EqQuotTypePack (@EqQuotClass Q qc ec m) Q.

Definition EqQuotType_clone (Q : Type) eqT cT 
  of phant_id (eq_quot_class eqT) cT := @EqQuotTypePack Q cT Q.

Lemma pi_eq_quot eqT : {mono \pi_eqT : x y / eq_quot_op x y >-> x == y}.
Proof. by case: eqT => [] ? []. Qed.

Canonical pi_eq_quot_mono eqT := PiMono2 (pi_eq_quot eqT).

End EqQuotTypeStructure.

Notation EqQuotType e Q m := (@EqQuotType_pack _ e Q _ _ _ _ id id m).
Notation "[ 'eqQuotType' e 'of' Q ]" := (@EqQuotType_clone _ e Q _ _ id)
 (at level 0, format "[ 'eqQuotType'  e  'of'  Q ]") : form_scope.

Module QuotSubType.
Section SubTypeMixin.

Variable T : eqType.
Variable qT : quotType T.

Definition Sub x (px : repr (\pi_qT x) == x) := \pi_qT x.

Lemma qreprK x Px : repr (@Sub x Px) = x.
Proof. by rewrite /Sub (eqP Px). Qed.

Lemma sortPx (x : qT) : repr (\pi_qT (repr x)) == repr x.
Proof. by rewrite !reprK eqxx. Qed.

Lemma sort_Sub (x : qT) : x = Sub (sortPx x).
Proof. by rewrite /Sub reprK. Qed.

Lemma reprP K (PK : forall x Px, K (@Sub x Px)) u : K u.
Proof. by rewrite (sort_Sub u); apply: PK. Qed.

Canonical subType  := SubType _ _ _ reprP qreprK.
Definition eqMixin := Eval hnf in [eqMixin of qT by <:].

End SubTypeMixin.

Definition choiceMixin (T : choiceType) (qT : quotType T) :=
  Eval hnf in [choiceMixin of qT by <:].

End QuotSubType.

Notation "[ 'subType' 'of' Q 'by' %/ ]" :=
  (SubType Q _ _ QuotSubType.reprP QuotSubType.qreprK)
  (at level 0, format "[ 'subType'  'of'  Q  'by'  %/ ]") : form_scope.

Notation "[ 'eqMixin' 'of' Q 'by' <:%/ ]" := 
  (@QuotSubType.eqMixin _ _: Equality.class_of Q)
  (at level 0, format "[ 'eqMixin'  'of'  Q  'by'  <:%/ ]") : form_scope.

Notation "[ 'choiceMixin' 'of' Q 'by' <:%/ ]" := 
  (@QuotSubType.choiceMixin _ _: Choice.mixin_of (seq (seq Q)))
  (at level 0, format "[ 'choiceMixin'  'of'  Q  'by'  <:%/ ]") : form_scope.

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

Hint Resolve equiv_refl.

Module EquivQuot.
Section EquivQuot.

Variable D : Type.
Variable T : choiceType.

Variable TD : T -> D.
Variable DT : D -> T.

Local Notation cancelTD e := (forall x, e (TD (DT x)) x).

Record indirect := Indirect {
  equiv_indirect :> rel D;
  _ : cancelTD equiv_indirect;
  _ : reflexive equiv_indirect;
  _ : symmetric equiv_indirect;
  _ : transitive equiv_indirect
}.

Implicit Type e : indirect.

Definition indirect_refl e : reflexive e. Proof. by case: e. Qed.
Definition indirect_sym e : symmetric e. Proof. by case: e. Qed.
Definition indirect_trans e : transitive e. Proof. by case: e. Qed.
Definition indirect_TDK e : cancelTD e. Proof. by case: e. Qed.

Canonical indirect_equivRel e :=
  @EquivRel _ e (indirect_refl e)
  (indirect_sym e) (@indirect_trans e).

Coercion indirect_equivRel : indirect >-> equiv_rel.

Variable e : indirect.
Local Notation TDK := (@indirect_TDK e).

Definition equivQuotEquiv : rel T := [rel x y | e (TD x) (TD y)].
Local Notation eT := equivQuotEquiv.

Lemma quotEquiv_refl x : eT x x. Proof. by rewrite /eT /=. Qed.
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

Definition type_of of (phantom (rel _) e) := equivQuotient.

Lemma equiv_canon_id : forall x, (invariant equiv_canon equiv_canon) x.
Proof.
move=> x /=; rewrite /equiv_canon (@eq_choose _ _ (eT x)).
  by rewrite (@choose_id _ (eT x) _ x) ?chooseP ?equiv_refl.
by move=> y; apply: equiv_ltrans; rewrite equiv_sym /= chooseP.
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
by rewrite equiv_sym /= chooseP.
Qed.

Lemma equiv_pi_DT (x y : D) :
  reflect (equiv_pi (DT x) = equiv_pi (DT y)) (e x y).
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

Local Notation qT := (type_of (Phantom (rel D) e)).
Definition quotClass := QuotClass equivQTP.
Canonical quotType := QuotType qT quotClass.

Lemma eqmodP x y : reflect (x = y %[m qT]) (e x y).
Proof. by apply: (iffP (equiv_pi_DT _ _)); rewrite !unlock. Qed.

Definition eqMixin := CanEqMixin equiv_reprK.
Canonical eqType := EqType qT eqMixin.
Definition choiceMixin := CanChoiceMixin equiv_reprK.
Canonical choiceType := ChoiceType qT choiceMixin.

Lemma eqmodE x y : x == y %[m qT] = e x y.
Proof. exact: sameP eqP (@eqmodP _ _). Qed.

Canonical eqQuotType := EqQuotType e qT eqmodE.

End EquivQuot.
End EquivQuot.

Canonical EquivQuot.indirect_equivRel.
Coercion EquivQuot.indirect_equivRel : EquivQuot.indirect >-> equiv_rel.

Definition eqmodE := EquivQuot.eqmodE.
Implicit Arguments eqmodE [D T DT TD e].
Prenex Implicits eqmodE.

Definition eqmodP := EquivQuot.eqmodP.
Implicit Arguments eqmodP [D T TD DT e x y].
Prenex Implicits eqmodP.

(* begin hide *)
(* Notation "[ 'eqMixin' 'of' Q 'by' %/ ]" :=  *)
(*   (@EquivQuot.eqMixin _ _ _ _ _ : Equality.class_of Q) *)
(*   (at level 0, format "[ 'eqMixin'  'of'  Q  'by'  %/ ]") : form_scope. *)

(* Notation "[ 'choiceMixin' 'of' Q 'by' %/ ]" :=  *)
(*   (@EquivQuot.choiceMixin _ _ _ _ _ : Choice.mixin_of (seq (seq Q))) *)
(*   (at level 0, format "[ 'choiceMixin'  'of'  Q  'by'  %/ ]") : form_scope. *)

(* Notation "[ 'eqType' 'of' Q 'by' %/ ]" := (EqType Q [eqMixin of Q by %/]) *)
(*   (at level 0, format "[ 'eqType'  'of'  Q  'by'  %/ ]") : form_scope. *)

(* Notation "[ 'choiceType' 'of' Q 'by' %/ ]" := *)
(*   (ChoiceType Q [choiceMixin of Q by %/]) *)
(*   (at level 0, format "[ 'choiceType'  'of'  Q  'by'  %/ ]") : form_scope. *)

(* Notation "[ 'eqQuotType' e 'of' Q 'by' %/ ]" := (EqQuotType e Q eqmodE) *)
(*   (at level 0, format "[ 'eqQuotType'  e  'of'  Q  'by'  %/ ]") : form_scope. *)
(* end hide *)

Canonical EquivQuot.quotType.
Canonical EquivQuot.eqType.
Canonical EquivQuot.choiceType.
Canonical EquivQuot.eqQuotType.

Notation "{mod e }" := (@EquivQuot.type_of _ _ _ _ _ (Phantom (rel _) e)) : quotient_scope.
Notation "x == y %[mod r ]" := (x == y %[m {mod r}]) : quotient_scope.
Notation "x = y %[mod r ]" := (x = y %[m {mod r}]) : quotient_scope.
Notation "x != y %[mod r ]" := (x != y %[m {mod r}]) : quotient_scope.
Notation "x <> y %[mod r ]" := (x <> y %[m {mod r}]) : quotient_scope.

Notation EquivQuotIndirect := EquivQuot.Indirect.

Section EquivQuotDirect.

Variable T : choiceType.
Variable R : rel T.
Variable e : equiv_rel T.

Definition MkEquivQuotDirect (er : reflexive R)
  (es : symmetric R) (et : transitive R) of phant_id R (equiv e) &
  phant_id er (@equiv_refl _ e) &
  phant_id es (@equiv_sym _ e) &
  phant_id et (@equiv_trans _ e) :=
  @EquivQuotIndirect T T id id R (fun _ => er _) er es et.

End EquivQuotDirect.

Notation EquivQuotDirect R := (@MkEquivQuotDirect _ R _ _ _ _ id id id id).


(* begin hide *)
(* Section MonoidQuotient. *)

(* Variables (T : Type) (idm : T). *)
(* Variables (qT : quotType T). *)

(* Import Monoid. *)

(* Section QuotOp2Structure. *)
(* Variable op : T -> T -> T. *)

(* Structure quot_op2 := QuotOp2 { *)
(*   quot_op2_op :> qT -> qT -> qT; *)
(*   _ : {morph \pi : x y / op x y >-> quot_op2_op x y} *)
(* }. *)

(* Lemma pi_quot_op2 (q_op : quot_op2) : *)
(*   {morph \pi : x y / op x y >-> q_op x y}. *)
(* Proof. by case: q_op. Qed. *)

(* Canonical pi_quot_op2_morph (q_op : quot_op2) := *)
(*   PiMorph2 (pi_quot_op2 q_op). *)

(* Structure quot_law := QuotLaw { *)
(*   quot_law_op :> quot_op2; *)
(*   idq :> pi_morph (\pi_qT idm) *)
(* }. *)

(* End QuotOp2Structure. *)

(* Section Plain. *)
(* Variable mul : law idm. *)
(* Variable mulq : quot_law mul. *)

(* Lemma mulqA : associative mulq. *)
(* Proof. by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE mulmA. Qed. *)

(* Lemma mul1q : left_id (pi_op mulq) mulq. *)
(* Proof. by move=> x; rewrite -[x]reprK !piE mul1m. Qed. *)

(* Lemma mulq1 : right_id (pi_op mulq) mulq. *)
(* Proof. by move=> x; rewrite -[x]reprK !piE mulm1. Qed. *)

(* Canonical mulq_law := Law mulqA mul1q mulq1. *)
(* End Plain. *)

(* Section Commutative. *)
(* Variable mul : com_law idm. *)
(* Variable mulq : quot_law mul. *)

(* Lemma mulqC : commutative mulq. *)
(* Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE mulmC. Qed. *)

(* Canonical mulq_com_law := ComLaw mulqC. *)
(* End Commutative. *)

(* Section Mul. *)
(* Variable mul : mul_law idm. *)
(* Variable mulq : quot_law mul. *)

(* Lemma mul0q : left_zero (pi_op mulq) mulq. *)
(* Proof. by move=> x; rewrite -[x]reprK !piE mul0m. Qed. *)

(* Lemma mulq0 : right_zero (pi_op mulq) mulq. *)
(* Proof. by move=> x; rewrite -[x]reprK !piE mulm0. Qed. *)

(* Canonical mulq_mul_law := MulLaw mul0q mulq0. *)
(* End Mul. *)

(* Section Add. *)
(* Variables (mul : T -> T -> T) (add : add_law idm mul). *)
(* Variables (mulq : quot_op2 mul) (addq : quot_law add). *)

(* Lemma mulq_addl : left_distributive mulq addq. *)
(* Proof. *)
(* by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE mulm_addl. *)
(* Qed. *)

(* Lemma mulq_addr : right_distributive mulq addq. *)
(* Proof. *)
(* by move=> x y z; rewrite -[x]reprK -[y]reprK -[z]reprK !piE mulm_addr. *)
(* Qed. *)

(* Canonical addq_add_law := AddLaw mulq_addl mulq_addr. *)
(* End Add. *)

(* End MonoidQuotient. *)
(* end hide *)