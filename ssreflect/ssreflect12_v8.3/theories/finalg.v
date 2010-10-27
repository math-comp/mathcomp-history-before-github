(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import ssralg finset fingroup morphism perm action.

(*****************************************************************************)
(* This file clones the entire ssralg hierachy for finite types; this allows *)
(* type inference to function properly on expressions that mix combinatorial *)
(* and algebraic operators (e.g., [set x + y | x, y <- A]).                  *)
(*   finZmodType, finRingType, finComRingType, finUnitRingType,              *)
(*   finComUnitRingType, finIdomType, finFieldType finLmodType,              *)
(*   finLalgType finAlgType finUnitAlgType                                  *)
(*      == the finite counterparts of zmodType, etc.                         *)
(* Note that a finFieldType is canonically decidable. All these structures   *)
(* can be derived using [xxxType of T] forms, e.g., if R has both canonical  *)
(* finType and ringType structures, then                                     *)
(*     Canonical Structure R_finRingType := Eval hnf in [finRingType of R].  *)
(* declares the derived finRingType structure for R. As the implementation   *)
(* of the derivation is somewhat involved, the Eval hnf normalization is     *)
(* strongly recommended.                                                     *)
(*   This file also provides direct tie-ins with finite group theory:        *)
(*  [baseFinGroupType of R for +%R] == the (canonical) additive group        *)
(*      [finGroupType of R for +%R]    structures for R                      *)
(*                         {unit R} == the type of units of R, which has a   *)
(*                                     canonical group structure.            *)
(*                           'U%act == the action by right multiplication of *)
(*                                     {unit R} on R, via FinRing.unit_act.  *)
(*                                     (This is also a group action.)        *)
(*****************************************************************************)

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module FinRing.

Local Notation mixin_of T b := (Finite.mixin_of (EqType T b)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later 
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_choice : forall T, base_of T -> Choice.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, mixin_of T (to_choice b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T :=
  fun bT b & phant_id (base_class bT) b =>
  fun fT m & phant_id (Finite.class fT) (Finite.Class m) =>
  Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_choice base_sort].
Local Notation fin_ class cT := (@Finite.Class _ (class cT) (class cT)).

Module Zmodule.

Section ClassDef.

Record class_of M :=
  Class { base : GRing.Zmodule.class_of M; mixin : mixin_of M base }.
Local Coercion base : class_of >-> GRing.Zmodule.class_of.
Local Coercion mixin : class_of >-> mixin_of.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.Zmodule.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (zmodType cT) (fin_ class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Canonical Structure join_finType.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Section AdditiveGroup.

Variable M : Zmodule.type.

Definition zmod_GroupMixin : FinGroup.mixin_of M :=
  FinGroup.Mixin (@GRing.addrA _) (@GRing.add0r _) (@GRing.addNr _).

Canonical Structure zmod_baseFinGroupType := BaseFinGroupType M zmod_GroupMixin.
Canonical Structure zmod_finGroupType := FinGroupType (@GRing.addNr M).

Lemma zmod1gE : 1%g = 0 :> M.                          Proof. by []. Qed.
Lemma zmodVgE : forall x : M, x^-1%g = - x.            Proof. by []. Qed.
Lemma zmodMgE : forall x y : M, (x * y)%g = x + y.     Proof. by []. Qed.
Lemma zmodXgE : forall n (x : M), (x ^+ n)%g = x *+ n. Proof. by []. Qed.

Lemma zmod_mulgC : forall x y : M, commute x y.
Proof. exact: GRing.addrC. Qed.

Lemma zmod_abelian : forall A : {set M}, abelian A.
Proof. move=> A; apply/centsP=> x _ y _; exact: zmod_mulgC. Qed.

End AdditiveGroup.

Module Import AdditiveGroupExports.
Coercion zmod_baseFinGroupType : Zmodule.type >-> baseFinGroupType.
Canonical Structure zmod_baseFinGroupType.
Coercion zmod_finGroupType : Zmodule.type >-> finGroupType.
Canonical Structure zmod_finGroupType.
End AdditiveGroupExports.

Module Ring.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Ring.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Zmodule.Class (mixin c).
Local Coercion base : class_of >-> GRing.Ring.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.Ring.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition finZmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (ringType cT) (fin_ class cT) cT.
Definition join_finZmodType cT := @Zmodule.Pack (ringType cT) (class cT) cT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Ring.class_of.
Coercion base2 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
End Exports.

Section Unit.

Variable R : type.

Definition is_inv (x y : R) := (x * y == 1) && (y * x == 1).
Definition unit : pred R := fun x => existsb y, is_inv x y.
Definition inv x := odflt x (pick (is_inv x)).

Lemma mulVr : {in unit, left_inverse 1 inv *%R}.
Proof.
rewrite /inv => x Ux; case: pickP => [y | no_y]; last by case/pred0P: Ux.
by case/andP=> _; move/eqP.
Qed.

Lemma mulrV : {in unit, right_inverse 1 inv *%R}.
Proof.
rewrite /inv => x Ux; case: pickP => [y | no_y]; last by case/pred0P: Ux.
by case/andP; move/eqP.
Qed.

Lemma intro_unit : forall x y, y * x = 1 /\ x * y = 1 -> unit x.
Proof.
by move=> x y [yx1 xy1]; apply/existsP; exists y; rewrite /is_inv xy1 yx1 !eqxx.
Qed.

Lemma invr_out : {in predC unit, inv =1 id}.
Proof.
rewrite /inv => x nUx; case: pickP => // y invxy.
by case/existsP: nUx; exists y.
Qed.

Definition UnitMixin := GRing.UnitRing.Mixin mulVr mulrV intro_unit invr_out.

End Unit.

End Ring.
Import Ring.Exports.

Module ComRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Ring.Class (mixin c).
Local Coercion base : class_of >-> GRing.ComRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.ComRing.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition finZmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition finRingType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (comRingType cT) (fin_ class cT) cT.
Definition join_finZmodType cT := @Zmodule.Pack (comRingType cT) (class cT) cT.
Definition join_finRingType cT := @Ring.Pack (comRingType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.UnitRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := Ring.Class (mixin c).
Local Coercion base : class_of >-> GRing.UnitRing.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.UnitRing.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition finZmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition finRingType cT := Ring.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (unitRingType cT) (fin_ class cT) cT.
Definition join_finZmodType cT := @Zmodule.Pack (unitRingType cT) (class cT) cT.
Definition join_finRingType cT := @Ring.Pack (unitRingType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.UnitRing.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Section UnitsGroup.

Variable R : UnitRing.type.

Inductive unit_of (phR : phant R) := Unit (x : R) of GRing.unit x.
Bind Scope group_scope with unit_of.

Let phR := Phant R.
Local Notation uT := (unit_of phR).
Definition uval (u : uT) := let: Unit x _ := u in x.

Canonical Structure unit_subType := [subType for uval by @unit_of_rect phR].
Definition unit_eqMixin := Eval hnf in [eqMixin of uT by <:].
Canonical Structure unit_eqType := Eval hnf in EqType uT unit_eqMixin.
Definition unit_choiceMixin := [choiceMixin of uT by <:].
Canonical Structure unit_choiceType :=
  Eval hnf in ChoiceType uT unit_choiceMixin.
Definition unit_countMixin := [countMixin of uT by <:].
Canonical Structure unit_countType := Eval hnf in CountType uT unit_countMixin.
Canonical Structure unit_subCountType := Eval hnf in [subCountType of uT].
Definition unit_finMixin := [finMixin of uT by <:].
Canonical Structure unit_finType := Eval hnf in FinType uT unit_finMixin.
Canonical Structure unit_subFinType := Eval hnf in [subFinType of uT].

Definition unit1 := Unit phR (@GRing.unitr1 _).
Lemma unit_inv_proof : forall u : uT, GRing.unit (val u)^-1.
Proof. by move=> u; rewrite GRing.unitr_inv ?(valP u). Qed.
Definition unit_inv u := Unit phR (unit_inv_proof u).
Lemma unit_mul_proof : forall u v : uT, GRing.unit (val u * val v).
Proof. by move=> u v; rewrite (GRing.unitr_mulr _ (valP u)) ?(valP v). Qed.
Definition unit_mul u v := Unit phR (unit_mul_proof u v).
Lemma unit_muluA : associative unit_mul.
Proof. move=> u v w; apply: val_inj; exact: GRing.mulrA. Qed.
Lemma unit_mul1u : left_id unit1 unit_mul.
Proof. move=> u; apply: val_inj; exact: GRing.mul1r. Qed.
Lemma unit_mulVu : left_inverse unit1 unit_inv unit_mul.
Proof. move=> u; apply: val_inj; exact: GRing.mulVr (valP u). Qed.

Definition unit_GroupMixin := FinGroup.Mixin unit_muluA unit_mul1u unit_mulVu.
Canonical Structure unit_baseFinGroupType :=
  Eval hnf in BaseFinGroupType uT unit_GroupMixin.
Canonical Structure unit_finGroupType := Eval hnf in FinGroupType unit_mulVu.

Definition unit_act x (u : uT) := x * val u.
Lemma unit_actE : forall x u, unit_act x u = x * val u. Proof. by []. Qed.

Canonical Structure unit_action :=
  @TotalAction _ _ unit_act (@GRing.mulr1 _) (fun _ _ _ => GRing.mulrA _ _ _).
Lemma unit_is_groupAction : @is_groupAction _ R setT setT unit_action.
Proof.
move=> u _ /=; rewrite inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= [_ u]GRing.mulr_addl.
Qed.
Canonical Structure unit_groupAction := GroupAction unit_is_groupAction.

End UnitsGroup.

Module Import UnitsGroupExports.
Bind Scope group_scope with unit_of.
Canonical Structure unit_subType.
Canonical Structure unit_eqType.
Canonical Structure unit_choiceType.
Canonical Structure unit_countType.
Canonical Structure unit_subCountType.
Canonical Structure unit_finType.
Canonical Structure unit_subFinType.
Canonical Structure unit_baseFinGroupType.
Canonical Structure unit_finGroupType.
Canonical Structure unit_action.
Canonical Structure unit_groupAction.
End UnitsGroupExports.

Module ComUnitRing.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ComUnitRing.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := ComRing.Class (mixin c).
Definition base3 R (c : class_of R) := @UnitRing.Class R (base c) (mixin c).
Local Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.ComUnitRing.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition finZmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition finRingType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition finComRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition finUnitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.

Section Joins.
Variable cT : type.
Let clT := class cT.
Let cT' := comUnitRingType cT.
Definition join_finType := @Finite.Pack cT' (fin_ class cT) cT.
Definition join_finZmodType := @Zmodule.Pack cT' clT cT.
Definition join_finRingType := @Ring.Pack cT' clT cT.
Definition join_finComRingType := @ComRing.Pack cT' clT cT.
Definition join_finUnitRingType := @UnitRing.Pack cT' clT cT.
Definition ujoin_finComRingType := @ComRing.Pack (unitRingType cT) clT cT.
Definition cjoin_finUnitRingType := @UnitRing.Pack (comRingType cT) clT cT.
Definition fcjoin_finUnitRingType := @UnitRing.Pack (finComRingType cT) clT cT.
End Joins.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ComUnitRing.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion base3 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical Structure finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finComRingType.
Canonical Structure join_finUnitRingType.
Canonical Structure ujoin_finComRingType.
Canonical Structure cjoin_finUnitRingType.
Canonical Structure fcjoin_finUnitRingType.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module IntegralDomain.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.IntegralDomain.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := ComUnitRing.Class (mixin c).
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition finZmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition finRingType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition finComRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition finUnitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition finComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.

Section Joins.
Variable cT : type.
Let clT := class cT.
Let cT' := idomainType cT.
Definition join_finType := @Finite.Pack cT' (fin_ class cT) cT.
Definition join_finZmodType := @Zmodule.Pack cT' clT cT.
Definition join_finRingType := @Ring.Pack cT' clT cT.
Definition join_finUnitRingType := @UnitRing.Pack cT' clT cT.
Definition join_finComRingType := @ComRing.Pack cT' clT cT.
Definition join_finComUnitRingType := @ComUnitRing.Pack cT' clT cT.
End Joins.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion base2 : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical Structure finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical Structure finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finComRingType.
Canonical Structure join_finUnitRingType.
Canonical Structure join_finComUnitRingType.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.Field.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition countType cT := Countable.Pack (fin_ class cT) cT.
Definition finType cT := Finite.Pack (fin_ class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition finZmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition finRingType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition finComRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition finUnitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition finComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition finIdomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.

Section Joins.
Variable cT : type.
Let clT := class cT.
Let cT' := fieldType cT.
Definition join_finType := @Finite.Pack cT' (fin_ class cT) cT.
Definition join_finZmodType := @Zmodule.Pack cT' clT cT.
Definition join_finRingType := @Ring.Pack cT' clT cT.
Definition join_finUnitRingType := @UnitRing.Pack cT' clT cT.
Definition join_finComRingType := @ComRing.Pack cT' clT cT.
Definition join_finComUnitRingType := @ComUnitRing.Pack cT' clT cT.
Definition join_finIdomainType := @IntegralDomain.Pack cT' clT cT.
End Joins.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion finComRingType : type >-> ComRing.type.
Canonical Structure finComRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion finComUnitRingType : type >-> ComUnitRing.type.
Canonical Structure finComUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion finIdomainType : type >-> IntegralDomain.type.
Canonical Structure finIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical Structure fieldType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finComRingType.
Canonical Structure join_finUnitRingType.
Canonical Structure join_finComUnitRingType.
Canonical Structure join_finIdomainType.
End Exports.

End Field.
Import Field.Exports.

Section DecideField.

Variable F : Field.type.

Fixpoint sat e f :=
  match f with
  | GRing.Bool b => b
  | t1 == t2 => (GRing.eval e t1 == GRing.eval e t2)%bool
  | GRing.Unit t => GRing.unit (GRing.eval e t)
  | f1 /\ f2 => sat e f1 && sat e f2
  | f1 \/ f2 => sat e f1 || sat e f2
  | f1 ==> f2 => (sat e f1 ==> sat e f2)%bool
  | ~ f1 => ~~ sat e f1
  | ('exists 'X_k, f1) => (existsb x : F, sat (set_nth 0%R e k x) f1)
  | ('forall 'X_k, f1) => (forallb x : F, sat (set_nth 0%R e k x) f1)
  end%T.

Lemma decidable : GRing.DecidableField.axiom sat.
Proof.
move=> e f; elim: f e;
  try by move=> f1 IH1 f2 IH2 e /=; case IH1; case IH2; constructor; tauto.
- by move=> b e; exact: idP.
- by move=> t1 t2 e; exact: eqP.
- by move=> t e; exact: idP.
- by move=> f IH e /=; case: IH; constructor.
- by move=> i f IH e; apply: (iffP existsP) => [] [x fx]; exists x; exact/IH.
by move=> i f IH e; apply: (iffP forallP) => f_ x; exact/IH.
Qed.

Definition DecidableFieldMixin := DecFieldMixin decidable.

End DecideField.

Module DecField.

Section Joins.
Variable cT : Field.type.
Let clT := Field.class cT.
Definition type := Eval hnf in DecFieldType cT (DecidableFieldMixin cT).
Definition finType := @Finite.Pack type (fin_ Field.class cT) type.
Definition finZmodType := @Zmodule.Pack type clT type.
Definition finRingType := @Ring.Pack type clT type.
Definition finUnitRingType := @UnitRing.Pack type clT type.
Definition finComRingType := @ComRing.Pack type clT type.
Definition finComUnitRingType := @ComUnitRing.Pack type clT type.
Definition finIdomainType := @IntegralDomain.Pack type clT type.
End Joins.

Module Exports.
Coercion type : Field.type >-> GRing.DecidableField.type.
Canonical Structure type.
Canonical Structure finType.
Canonical Structure finZmodType.
Canonical Structure finRingType.
Canonical Structure finUnitRingType.
Canonical Structure finComRingType.
Canonical Structure finComUnitRingType.
Canonical Structure finIdomainType.
End Exports.

End DecField.

Module Lmodule.

Section ClassDef.

Variable R : ringType.
Implicit Type phR : phant R.

Record class_of M :=
  Class { base : GRing.Lmodule.class_of R M ; mixin : mixin_of M base }.
Definition base2 R (c : class_of R) := Zmodule.Class (mixin c).
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Local Coercion base2 : class_of >-> Zmodule.class_of.

Structure type phR := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class phR (cT : type phR) :=
  let: Pack _ c _ := cT return class_of cT in c.
Definition pack phR := gen_pack (Pack phR) Class (@GRing.Lmodule.class R phR).

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition countType phR cT := Countable.Pack (fin_ (@class phR) cT) cT.
Definition finType phR cT := Finite.Pack (fin_ (@class phR) cT) cT.
Definition zmodType phR (cT : type phR) := GRing.Zmodule.Pack (@class phR cT) cT.
Definition finZmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Definition lmodType phR cT := GRing.Lmodule.Pack phR (@class phR cT) cT.
Definition join_finType phR cT := 
  @Finite.Pack (lmodType cT) (fin_ (@class phR) cT) cT.
Definition join_finZmodType phR cT := 
  @Zmodule.Pack (lmodType cT) (@class phR cT) cT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion base2 : class_of >-> Zmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Module Lalgebra.

Section ClassDef.

Variable R : ringType.
Implicit Type phR : phant R.

Record class_of M :=
  Class { base : GRing.Lalgebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Ring.Class (mixin c).
Definition base3 M (c : class_of M) := @Lmodule.Class _ _ (base c) (mixin c).
Local Coercion base : class_of >-> GRing.Lalgebra.class_of.
Local Coercion base2 : class_of >-> Ring.class_of.
Local Coercion base3 : class_of >-> Lmodule.class_of.

Structure type phR := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class phR (cT : type phR) :=
  let: Pack _ c _ := cT return class_of cT in c.
Definition pack phR := gen_pack (Pack phR) Class (@GRing.Lalgebra.class R phR).

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition countType phR cT := Countable.Pack (fin_ (@class phR) cT) cT.
Definition finType phR cT := Finite.Pack (fin_ (@class phR) cT) cT.
Definition zmodType phR (cT : type phR) :=
  GRing.Zmodule.Pack (@class phR cT) cT.
Definition finZmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Definition ringType phR (cT : type phR) := GRing.Ring.Pack (@class phR cT) cT.
Definition finRingType phR cT := Ring.Pack (@class phR cT) cT.
Definition lmodType phR (cT : type phR) := 
  GRing.Lmodule.Pack phR (@class phR cT) cT.
Definition finLmodType phR cT := Lmodule.Pack phR (@class phR cT) cT.
Definition lalgType phR (cT : type phR) :=
  GRing.Lalgebra.Pack phR (@class phR cT) cT.

Section Joins.
Variable phR: phant R.
Variable cT : type phR.
Let clT := class cT.
Let cT' := lalgType cT.
Definition join_finType := @Finite.Pack cT' (fin_ (@class phR) cT) cT.
Definition join_finZmodType := @Zmodule.Pack cT' clT cT.
Definition join_finLmodType := @Lmodule.Pack _ phR cT' clT cT.
Definition join_finRingType := @Ring.Pack cT' clT cT.
Definition rjoin_finLmodType := @Lmodule.Pack _ phR (ringType cT) clT cT.
Definition ljoin_finRingType := @Ring.Pack (lmodType cT) clT cT.
Definition fljoin_finRingType := @Ring.Pack (finLmodType cT) clT cT.
End Joins.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Lalgebra.class_of.
Coercion base2 : class_of >-> Ring.class_of.
Coercion base3 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical Structure finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finLmodType.
Canonical Structure join_finRingType.
Canonical Structure rjoin_finLmodType.
Canonical Structure ljoin_finRingType.
Canonical Structure fljoin_finRingType.
End Exports.

End Lalgebra.
Import Lalgebra.Exports.

Module Algebra.

Section ClassDef.

Variable R : ringType.
Implicit Type phR : phant R.

Record class_of M :=
  Class { base : GRing.Algebra.class_of R M; mixin : mixin_of M base }.
Definition base2 M (c : class_of M) := Lalgebra.Class (mixin c).
Local Coercion base : class_of >-> GRing.Algebra.class_of.
Local Coercion base2 : class_of >->Lalgebra.class_of.

Structure type phR := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class phR (cT : type phR) :=
  let: Pack _ c _ := cT return class_of cT in c.
Definition pack phR := gen_pack (Pack phR) Class (@GRing.Algebra.class R phR).

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition countType phR cT := Countable.Pack (fin_ (@class phR) cT) cT.
Definition finType phR cT := Finite.Pack (fin_ (@class phR) cT) cT.
Definition zmodType phR (cT : type phR) :=
  GRing.Zmodule.Pack (@class phR cT) cT.
Definition finZmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Definition ringType phR (cT : type phR) := GRing.Ring.Pack (@class phR cT) cT.
Definition finRingType phR cT := Ring.Pack (@class phR cT) cT.
Definition lmodType phR (cT : type phR) :=
   GRing.Lmodule.Pack phR (@class phR cT) cT.
Definition finLmodType phR cT := Lmodule.Pack phR (@class phR cT) cT.
Definition lalgType phR (cT : type phR) := 
  GRing.Lalgebra.Pack phR (@class phR cT) cT.
Definition finLalgType phR cT := Lalgebra.Pack phR (@class phR cT) cT.
Definition algType phR (cT : type phR) :=
 GRing.Algebra.Pack phR (@class phR cT) cT.

Section Joins.

Variable phR: phant R.
Variable cT : type phR.
Let clT := class cT.
Let cT' := algType cT.

Definition join_finType :=  @Finite.Pack cT' (fin_ (@class phR) cT) cT'.
Definition join_finZmodType := @Zmodule.Pack cT' (@class phR cT) cT'.
Definition join_finRingType := @Ring.Pack cT' (@class phR cT) cT'.
Definition join_finLmodType :=  @Lmodule.Pack _ phR cT' (@class phR cT) cT'.
Definition join_finLalgType := @Lalgebra.Pack _ phR cT' (@class phR cT) cT'.

End Joins.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Algebra.class_of.
Coercion base2 : class_of >-> Lalgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical Structure finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Coercion finLalgType : type >-> Lalgebra.type.
Canonical Structure finLalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical Structure algType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finLmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finLalgType.
End Exports.

End Algebra.
Import Algebra.Exports.

Module UnitAlgebra.
 
Section ClassDef.

Variable R : unitRingType.
Implicit Type phR : phant R.
 
Record class_of M := 
  Class { base : GRing.UnitAlgebra.class_of R M ; mixin : mixin_of M base }. 
Definition base2 M (c : class_of M) := Algebra.Class (mixin c).
Definition base3 M (c : class_of M) := @UnitRing.Class _ (base c) (mixin c).

Local Coercion base : class_of >-> GRing.UnitAlgebra.class_of.
Local Coercion base2 : class_of >-> Algebra.class_of.
Local Coercion base3 : class_of >-> UnitRing.class_of.

Structure type phR := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class phR (cT : type phR) := 
  let: Pack _ c _ := cT return class_of cT in c. 
Definition pack phR :=
  gen_pack (Pack phR) Class (@GRing.UnitAlgebra.class R phR). 

Definition eqType phR cT := Equality.Pack (@class phR cT) cT. 
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT. 
Definition countType phR cT := Countable.Pack (fin_ (@class phR) cT) cT. 
Definition finType phR cT := Finite.Pack (fin_ (@class phR) cT) cT. 
Definition zmodType phR (cT : type phR) :=
  GRing.Zmodule.Pack (@class phR cT) cT. 
Definition finZmodType phR cT := Zmodule.Pack (@class phR cT) cT. 
Definition ringType phR (cT : type phR) := GRing.Ring.Pack (@class phR cT) cT. 
Definition finRingType phR cT := Ring.Pack (@class phR cT) cT. 
Definition unitRingType phR (cT : type phR) := 
  GRing.UnitRing.Pack (@class phR cT) cT.
Definition finUnitRingType phR cT := UnitRing.Pack (@class phR cT) cT. 
Definition lmodType phR (cT : type phR) := 
  GRing.Lmodule.Pack phR (@class phR cT) cT. 
Definition finLmodType phR cT := Lmodule.Pack phR (@class phR cT) cT. 
Definition lalgType phR (cT : type phR) := 
  GRing.Lalgebra.Pack phR (@class phR cT) cT. 
Definition finLalgType phR cT := Lalgebra.Pack phR (@class phR cT) cT. 
Definition algType phR (cT : type phR) := 
  GRing.Algebra.Pack phR (@class phR cT) cT. 
Definition finAlgType phR cT := Algebra.Pack phR (@class phR cT) cT. 
Definition unitAlgType phR (cT : type phR) := 
  GRing.UnitAlgebra.Pack phR (@class phR cT) cT.

Section Joins.

Variable phR: phant R.
Variable cT : type phR.
Let clT := class cT.
Let cT' := unitAlgType cT.

Definition join_finType := @Finite.Pack cT' (fin_ (@class phR) cT) cT.
Definition join_finZmodType := @Zmodule.Pack cT' (@class phR cT) cT.
Definition join_finRingType := @Ring.Pack cT' (@class phR cT) cT.
Definition join_finUnitRingType := @UnitRing.Pack cT' (@class phR cT) cT.
Definition join_finLmodType := @Lmodule.Pack _ phR cT' (@class phR cT) cT.
Definition join_finLalgType := @Lalgebra.Pack _ phR cT' (@class phR cT) cT.
Definition join_finAlgType := @Algebra.Pack _ phR cT' (@class phR cT) cT.
Definition  ljoin_finUnitRingType := @UnitRing.Pack (lmodType cT) clT cT.
Definition fljoin_finUnitRingType := @UnitRing.Pack (finLmodType cT) clT cT.
Definition  njoin_finUnitRingType := @UnitRing.Pack (lalgType cT) clT cT.
Definition fnjoin_finUnitRingType := @UnitRing.Pack (finLalgType cT) clT cT.
Definition  ajoin_finUnitRingType := @UnitRing.Pack (algType cT) clT cT.
Definition fajoin_finUnitRingType := @UnitRing.Pack (finAlgType cT) clT cT.
Definition ujoin_finLmodType := @Lmodule.Pack _ phR (unitRingType cT) clT cT.
Definition ujoin_finLalgType := @Lalgebra.Pack _ phR (unitRingType cT) clT cT.
Definition ujoin_finAlgType := @Algebra.Pack _ phR (unitRingType cT) clT cT.

End Joins.
 
End ClassDef. 

Module Exports.
Coercion base : class_of >-> GRing.UnitAlgebra.class_of.
Coercion base2 : class_of >-> Algebra.class_of.
Coercion base3 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion countType : type >-> Countable.type.
Canonical Structure countType.
Coercion finType : type >-> Finite.type.
Canonical Structure finType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion finZmodType : type >-> Zmodule.type.
Canonical Structure finZmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion finRingType : type >-> Ring.type.
Canonical Structure finRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion finUnitRingType : type >-> UnitRing.type.
Canonical Structure finUnitRingType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion finLmodType : type >-> Lmodule.type.
Canonical Structure finLmodType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Coercion finLalgType : type >-> Lalgebra.type.
Canonical Structure finLalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical Structure algType.
Coercion finAlgType : type >-> Algebra.type.
Canonical Structure finAlgType.
Coercion unitAlgType : type >-> GRing.UnitAlgebra.type.
Canonical Structure unitAlgType.
Canonical Structure join_finType.
Canonical Structure join_finZmodType.
Canonical Structure join_finLmodType.
Canonical Structure join_finRingType.
Canonical Structure join_finLalgType.
Canonical Structure join_finAlgType.
Canonical Structure ljoin_finUnitRingType.
Canonical Structure fljoin_finUnitRingType.
Canonical Structure njoin_finUnitRingType.
Canonical Structure fnjoin_finUnitRingType.
Canonical Structure ajoin_finUnitRingType.
Canonical Structure fajoin_finUnitRingType.
Canonical Structure ujoin_finLmodType.
Canonical Structure ujoin_finLalgType.
Canonical Structure ujoin_finAlgType.
End Exports.

End UnitAlgebra.
Import UnitAlgebra.Exports.

Module Theory.

Definition zmod1gE := zmod1gE.
Definition zmodVgE := zmodVgE.
Definition zmodMgE := zmodMgE.
Definition zmodXgE := zmodXgE.
Definition zmod_mulgC := zmod_mulgC.
Definition zmod_abelian := zmod_abelian.
Definition unit_actE := unit_actE.

End Theory.

End FinRing.

Export FinRing.Zmodule.Exports.
Export FinRing.AdditiveGroupExports.
Export FinRing.Ring.Exports.
Export FinRing.ComRing.Exports.
Export FinRing.UnitRing.Exports.
Export FinRing.UnitsGroupExports.
Export FinRing.ComUnitRing.Exports.
Export FinRing.IntegralDomain.Exports.
Export FinRing.Field.Exports.
Export FinRing.DecField.Exports.
Export FinRing.Lmodule.Exports.
Export FinRing.Lalgebra.Exports.
Export FinRing.Algebra.Exports.
Export FinRing.UnitAlgebra.Exports.

Notation finZmodType := FinRing.Zmodule.type.
Notation finRingType := FinRing.Ring.type.
Notation finComRingType := FinRing.ComRing.type.
Notation finUnitRingType := FinRing.UnitRing.type.
Notation finComUnitRingType := FinRing.ComUnitRing.type.
Notation finIdomainType := FinRing.IntegralDomain.type.
Notation finFieldType := FinRing.Field.type.
Notation finLmodType R := (FinRing.Lmodule.type (Phant R)).
Notation finLalgType R := (FinRing.Lalgebra.type (Phant R)).
Notation finAlgType R := (FinRing.Algebra.type (Phant R)).
Notation finUnitAlgType R := (FinRing.UnitAlgebra.type (Phant R)).

Local Notation do_pack pack T := (pack T _ _ id _ _ id).
Notation "[ 'finZmodType' 'of' T ]" := (do_pack FinRing.Zmodule.pack T)
  (at level 0, format "[ 'finZmodType'  'of'  T ]") : form_scope.
Notation "[ 'finRingType' 'of' T ]" := (do_pack FinRing.Ring.pack T)
  (at level 0, format "[ 'finRingType'  'of'  T ]") : form_scope.
Notation "[ 'finComRingType' 'of' T ]" := (do_pack FinRing.ComRing.pack T)
  (at level 0, format "[ 'finComRingType'  'of'  T ]") : form_scope.
Notation "[ 'finUnitRingType' 'of' T ]" := (do_pack FinRing.UnitRing.pack T)
  (at level 0, format "[ 'finUnitRingType'  'of'  T ]") : form_scope.
Notation "[ 'finComUnitRingType' 'of' T ]" :=
    (do_pack FinRing.ComUnitRing.pack T)
  (at level 0, format "[ 'finComUnitRingType'  'of'  T ]") : form_scope.
Notation "[ 'finIdomainType' 'of' T ]" :=
    (do_pack FinRing.IntegralDomain.pack T)
  (at level 0, format "[ 'finIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'finFieldType' 'of' T ]" := (do_pack FinRing.Field.pack T)
  (at level 0, format "[ 'finFieldType'  'of'  T ]") : form_scope.
Notation "[ 'finLmodType' [ R ] 'of' T ]" :=
    (do_pack (@FinRing.Lmodule.pack _ (Phant R)) T)
  (at level 0, format "[ 'finLmodType' [ R ] 'of'  T ]") : form_scope.
Notation "[ 'finLalgType' [ R ] 'of' T ]" :=
    (do_pack (@FinRing.Lalgebra.pack _ (Phant R)) T)
  (at level 0, format "[ 'finLalgType' [ R ] 'of'  T ]") : form_scope.
Notation "[ 'finAlgType' [ R ] 'of' T ]" :=
    (do_pack (@FinRing.Algebra.pack _ (Phant R)) T)
  (at level 0, format "[ 'finAlgType' [ R ] 'of'  T ]") : form_scope.
Notation "[ 'finUnitAlgType' [ R ] 'of' T ]" :=
    (do_pack (@FinRing.UnitAlgebra.pack _ (Phant R)) T) 
  (at level 0, format "[ 'finUnitAlgType' [ R ] 'of'  T ]") : form_scope.

Notation "{ 'unit' R }" := (FinRing.unit_of (Phant R))
  (at level 0, format "{ 'unit'  R }") : type_scope.
Notation "''U'" := (FinRing.unit_action _)
  (at level 0) : action_scope.
Notation "''U'" := (FinRing.unit_groupAction _)
  (at level 0) : groupAction_scope.

Notation "[ 'baseFinGroupType' 'of' R 'for' +%R ]" :=
    (BaseFinGroupType R (FinRing.zmod_GroupMixin _))
  (at level 0, format "[ 'baseFinGroupType'  'of'  R  'for'  +%R ]")
    : form_scope.
Notation "[ 'finGroupType' 'of' R 'for' +%R ]" :=
    (@FinGroup.clone R _ (FinRing.zmod_finGroupType _) id _ id)
  (at level 0, format "[ 'finGroupType'  'of'  R  'for'  +%R ]") : form_scope.

Canonical Structure finRing_baseFinGroupType (R : finRingType) :=
  Eval hnf in [baseFinGroupType of R for +%R].
Canonical Structure finRing_finGroupType (R : finRingType) :=
  Eval hnf in [finGroupType of R for +%R].
Canonical Structure finComRing_baseFinGroupType (R : finComRingType) :=
  Eval hnf in [baseFinGroupType of R for +%R].
Canonical Structure finComRing_finGroupType (R : finComRingType) :=
  Eval hnf in [finGroupType of R for +%R].
Canonical Structure finUnitRing_baseFinGroupType (R : finUnitRingType) :=
  Eval hnf in [baseFinGroupType of R for +%R].
Canonical Structure finUnitRing_finGroupType (R : finUnitRingType) :=
  Eval hnf in [finGroupType of R for +%R].
Canonical Structure finComUnitRing_baseFinGroupType (R : finComUnitRingType) :=
  Eval hnf in [baseFinGroupType of R for +%R].
Canonical Structure finComUnitRing_finGroupType (R : finComUnitRingType) :=
  Eval hnf in [finGroupType of R for +%R].
Canonical Structure finIdomain_baseFinGroupType (R : finIdomainType) :=
  Eval hnf in [baseFinGroupType of R for +%R].
Canonical Structure finIdomain_finGroupType (R : finIdomainType) :=
  Eval hnf in [finGroupType of R for +%R].
Canonical Structure finField_baseFinGroupType (F : finFieldType) :=
  Eval hnf in [baseFinGroupType of F for +%R].
Canonical Structure finField_finGroupType (F : finFieldType) :=
  Eval hnf in [finGroupType of F for +%R].
Canonical Structure finLmod_baseFinGroupType
                      (R : ringType) (M : finLmodType R) :=
  Eval hnf in [baseFinGroupType of M for +%R].
Canonical Structure finLalg_baseFinGroupType
                      (R : ringType) (M : finLalgType R) :=
  Eval hnf in [baseFinGroupType of M for +%R].
Canonical Structure finAlg_baseFinGroupType
                      (R : ringType) (M : finAlgType R) :=
  Eval hnf in [baseFinGroupType of M for +%R].
Canonical Structure finUnitAlg_baseFinGroupType
                      (R : unitRingType) (M : finUnitAlgType R) :=
  Eval hnf in [baseFinGroupType of M for +%R].

Canonical Structure zmod_baseFinGroupType (M : finZmodType) :=
  Eval hnf in [baseFinGroupType of M : zmodType for +%R].
Canonical Structure zmod_finGroupType (M : finZmodType) :=
  Eval hnf in [finGroupType of M : zmodType for +%R].
Canonical Structure ring_baseFinGroupType (R : finRingType) :=
  Eval hnf in [baseFinGroupType of R : ringType for +%R].
Canonical Structure ring_finGroupType (R : finRingType) :=
  Eval hnf in [finGroupType of R : ringType for +%R].
Canonical Structure comRing_baseFinGroupType (R : finComRingType) :=
  Eval hnf in [baseFinGroupType of R : comRingType for +%R].
Canonical Structure comRing_finGroupType (R : finComRingType) :=
  Eval hnf in [finGroupType of R : comRingType for +%R].
Canonical Structure unitRing_baseFinGroupType (R : finUnitRingType) :=
  Eval hnf in [baseFinGroupType of R : unitRingType for +%R].
Canonical Structure unitRing_finGroupType (R : finUnitRingType) :=
  Eval hnf in [finGroupType of R : unitRingType for +%R].
Canonical Structure comUnitRing_baseFinGroupType (R : finComUnitRingType) :=
  Eval hnf in [baseFinGroupType of R : comUnitRingType for +%R].
Canonical Structure comUnitRing_finGroupType (R : finComUnitRingType) :=
  Eval hnf in [finGroupType of R : comUnitRingType for +%R].
Canonical Structure idomain_baseFinGroupType (R : finIdomainType) :=
  Eval hnf in [baseFinGroupType of R : idomainType for +%R].
Canonical Structure idomain_finGroupType (R : finIdomainType) :=
  Eval hnf in [finGroupType of R : idomainType for +%R].
Canonical Structure field_baseFinGroupType (F : finFieldType) :=
  Eval hnf in [baseFinGroupType of F : fieldType for +%R].
Canonical Structure field_finGroupType (F : finFieldType) :=
  Eval hnf in [finGroupType of F : fieldType for +%R].
Canonical Structure decField_baseFinGroupType (F : finFieldType) :=
  Eval hnf in [baseFinGroupType of F : decFieldType for +%R].
Canonical Structure decField_finGroupType (F : finFieldType) :=
  Eval hnf in [finGroupType of F : decFieldType for +%R].
Canonical Structure lmod_baseFinGroupType
                      (R : ringType) (M : finLmodType R) :=
  Eval hnf in [baseFinGroupType of M : lmodType R  for +%R].
Canonical Structure lmod_finGroupType
                      (R : ringType) (M : finLmodType R) :=
  Eval hnf in [finGroupType of M : lmodType R for +%R].
Canonical Structure lalg_baseFinGroupType
                      (R : ringType) (M : finLalgType R) :=
  Eval hnf in [baseFinGroupType of M : lalgType R  for +%R].
Canonical Structure lalg_finGroupType
                      (R : ringType) (M : finLalgType R) :=
  Eval hnf in [finGroupType of M : lalgType R for +%R].
Canonical Structure alg_finGroupType
                      (R : ringType) (M : finAlgType R) :=
  Eval hnf in [finGroupType of M : algType R for +%R].
Canonical Structure unitAlg_finGroupType
                      (R : unitRingType) (M : finUnitAlgType R) :=
  Eval hnf in [finGroupType of M : unitAlgType R for +%R].
