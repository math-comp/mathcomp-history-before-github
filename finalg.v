(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import ssralg finset groups morphisms perm action.

(*****************************************************************************)
(* This file clones the entire ssralg hierachy for finite types; this allows *)
(* type inference to function properly on expressions that mix combinatorial *)
(* and algebraic operators (e.g., [set x + y | x, y <- A]).                  *)
(*   finZmodType, finRingType, finComRingType, finUnitRingType,              *)
(*   finComUnitRingType, finIdomType, finFieldType                           *)
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

Record class_of M :=
  Class { base :> GRing.Zmodule.class_of M; ext :> mixin_of M base }.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.Zmodule.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (zmodType cT) (fin_ class cT) cT.

End Zmodule.

Section AdditiveGroup.

Variable M : Zmodule.type.
Canonical Structure Zmodule.finType.
Canonical Structure Zmodule.zmodType.

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

Coercion zmod_baseFinGroupType : Zmodule.type >-> baseFinGroupType.
Coercion zmod_finGroupType : Zmodule.type >-> finGroupType.

Module Ring.

Record class_of R :=
  Class { base1 :> GRing.Ring.class_of R; ext :> mixin_of R base1 }.
Coercion base2 R (c : class_of R) := Zmodule.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.Ring.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion finZmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (ringType cT) (fin_ class cT) cT.
Definition join_finZmodType cT := @Zmodule.Pack (ringType cT) (class cT) cT.

Section Unit.

Variable R : type.
Canonical Structure ringType.
Canonical Structure finType.

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

Module ComRing.

Record class_of R :=
  Class { base1 :> GRing.ComRing.class_of R; ext :> mixin_of R base1 }.
Coercion base2 R (c : class_of R) := Ring.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.ComRing.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion finZmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion finRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (comRingType cT) (fin_ class cT) cT.
Definition join_finZmodType cT := @Zmodule.Pack (comRingType cT) (class cT) cT.
Definition join_finRingType cT := @Ring.Pack (comRingType cT) (class cT) cT.

End ComRing.

Module UnitRing.

Record class_of R :=
  Class { base1 :> GRing.UnitRing.class_of R; ext :> mixin_of R base1 }.
Coercion base2 R (c : class_of R) := Ring.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.UnitRing.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion finZmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion finRingType cT := Ring.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition join_finType cT := @Finite.Pack (unitRingType cT) (fin_ class cT) cT.
Definition join_finZmodType cT := @Zmodule.Pack (unitRingType cT) (class cT) cT.
Definition join_finRingType cT := @Ring.Pack (unitRingType cT) (class cT) cT.

End UnitRing.

Section UnitsGroup.

Variable R : UnitRing.type.
Canonical Structure UnitRing.eqType.
Canonical Structure UnitRing.choiceType.
Canonical Structure UnitRing.countType.
Canonical Structure UnitRing.finType.
Canonical Structure UnitRing.ringType.
Canonical Structure UnitRing.unitRingType.

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

Module ComUnitRing.

Record class_of R :=
  Class { base1 :> GRing.ComUnitRing.class_of R; ext :> mixin_of R base1 }.
Coercion base2 R (c : class_of R) := ComRing.Class c.
Coercion base3 R (c : class_of R) := @UnitRing.Class R c c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.ComUnitRing.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion finZmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion finRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion finComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion finUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.

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

End ComUnitRing.

Module IntegralDomain.

Record class_of R :=
  Class { base1 :> GRing.IntegralDomain.class_of R; ext :> mixin_of R base1 }.
Coercion base2 R (c : class_of R) := ComUnitRing.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion finZmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion finRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion finComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion finUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion finComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.

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

End IntegralDomain.

Module Field.

Record class_of R :=
  Class { base1 :> GRing.Field.class_of R; ext :> mixin_of R base1 }.
Coercion base2 R (c : class_of R) := IntegralDomain.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition pack := gen_pack Pack Class GRing.Field.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (fin_ class cT) cT.
Coercion finType cT := Finite.Pack (fin_ class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion finZmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion finRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion finComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion finUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion finComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Coercion finIdomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := GRing.Field.Pack (class cT) cT.

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

End Field.

Section DecideField.

Variable F : Field.type.
Canonical Structure Field.finType.
Canonical Structure Field.unitRingType.

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

Canonical Structure Field.fieldType.
Coercion decFieldType (F : Field.type) :=
  Eval hnf in DecFieldType F (DecidableFieldMixin F).

Section DecFieldJoins.
Variable cT : Field.type.
Let clT := Field.class cT.
Let cT' := decFieldType cT.
Definition decField_finType := @Finite.Pack cT' (fin_ Field.class cT) cT.
Definition decField_finZmodType := @Zmodule.Pack cT' clT cT.
Definition decField_finRingType := @Ring.Pack cT' clT cT.
Definition decField_finUnitRingType := @UnitRing.Pack cT' clT cT.
Definition decField_finComRingType := @ComRing.Pack cT' clT cT.
Definition decField_finComUnitRingType := @ComUnitRing.Pack cT' clT cT.
Definition decField_finIdomainType := @IntegralDomain.Pack cT' clT cT.
End DecFieldJoins.

Module Lmodule.
Section Lmodule.
Variable R : ringType.
Implicit Type phR : phant R.

Record class_of M :=
  Class { base1 :> GRing.Lmodule.class_of R M ; ext :> mixin_of M base1 }.
Coercion base2 M (c : class_of M) := Zmodule.Class c.
Structure type phR : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class phR (cT : type phR) :=
  let: Pack _ c _ := cT return class_of cT in c.
Definition pack phR := gen_pack (Pack phR) Class (@GRing.Lmodule.class R phR).

Coercion eqType phR cT := Equality.Pack (@class phR cT) cT.
Coercion choiceType phR cT := Choice.Pack (@class phR cT) cT.
Coercion countType phR cT := Countable.Pack (fin_ (@class phR) cT) cT.
Coercion finType phR cT := Finite.Pack (fin_ (@class phR) cT) cT.
Coercion zmodType phR (cT : type phR) := GRing.Zmodule.Pack (@class phR cT) cT.
Coercion finZmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Coercion lmodType phR cT := GRing.Lmodule.Pack phR (@class phR cT) cT.
Definition join_finType phR cT := 
  @Finite.Pack (lmodType cT) (fin_ (@class phR) cT) cT.
Definition join_finZmodType phR cT := 
  @Zmodule.Pack (lmodType cT) (@class phR cT) cT.

End Lmodule.
End Lmodule.

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

Canonical Structure FinRing.Zmodule.eqType.
Canonical Structure FinRing.Zmodule.choiceType.
Canonical Structure FinRing.Zmodule.countType.
Canonical Structure FinRing.Zmodule.finType.
Canonical Structure FinRing.Zmodule.zmodType.
Canonical Structure FinRing.Zmodule.join_finType.
Canonical Structure FinRing.zmod_baseFinGroupType.
Canonical Structure FinRing.zmod_finGroupType.

Canonical Structure FinRing.Ring.eqType.
Canonical Structure FinRing.Ring.choiceType.
Canonical Structure FinRing.Ring.countType.
Canonical Structure FinRing.Ring.finType.
Canonical Structure FinRing.Ring.zmodType.
Canonical Structure FinRing.Ring.finZmodType.
Canonical Structure FinRing.Ring.ringType.
Canonical Structure FinRing.Ring.join_finType.
Canonical Structure FinRing.Ring.join_finZmodType.

Canonical Structure FinRing.ComRing.eqType.
Canonical Structure FinRing.ComRing.choiceType.
Canonical Structure FinRing.ComRing.countType.
Canonical Structure FinRing.ComRing.finType.
Canonical Structure FinRing.ComRing.zmodType.
Canonical Structure FinRing.ComRing.finZmodType.
Canonical Structure FinRing.ComRing.ringType.
Canonical Structure FinRing.ComRing.finRingType.
Canonical Structure FinRing.ComRing.comRingType.
Canonical Structure FinRing.ComRing.join_finType.
Canonical Structure FinRing.ComRing.join_finZmodType.
Canonical Structure FinRing.ComRing.join_finRingType.

Canonical Structure FinRing.UnitRing.eqType.
Canonical Structure FinRing.UnitRing.choiceType.
Canonical Structure FinRing.UnitRing.countType.
Canonical Structure FinRing.UnitRing.finType.
Canonical Structure FinRing.UnitRing.zmodType.
Canonical Structure FinRing.UnitRing.finZmodType.
Canonical Structure FinRing.UnitRing.ringType.
Canonical Structure FinRing.UnitRing.finRingType.
Canonical Structure FinRing.UnitRing.unitRingType.
Canonical Structure FinRing.UnitRing.join_finType.
Canonical Structure FinRing.UnitRing.join_finZmodType.
Canonical Structure FinRing.UnitRing.join_finRingType.

Canonical Structure FinRing.unit_subType.
Canonical Structure FinRing.unit_eqType.
Canonical Structure FinRing.unit_choiceType.
Canonical Structure FinRing.unit_countType.
Canonical Structure FinRing.unit_subCountType.
Canonical Structure FinRing.unit_finType.
Canonical Structure FinRing.unit_subFinType.
Canonical Structure FinRing.unit_baseFinGroupType.
Canonical Structure FinRing.unit_finGroupType.
Canonical Structure FinRing.unit_action.
Canonical Structure FinRing.unit_groupAction.

Canonical Structure FinRing.ComUnitRing.eqType.
Canonical Structure FinRing.ComUnitRing.choiceType.
Canonical Structure FinRing.ComUnitRing.countType.
Canonical Structure FinRing.ComUnitRing.finType.
Canonical Structure FinRing.ComUnitRing.zmodType.
Canonical Structure FinRing.ComUnitRing.finZmodType.
Canonical Structure FinRing.ComUnitRing.ringType.
Canonical Structure FinRing.ComUnitRing.finRingType.
Canonical Structure FinRing.ComUnitRing.comRingType.
Canonical Structure FinRing.ComUnitRing.finComRingType.
Canonical Structure FinRing.ComUnitRing.unitRingType.
Canonical Structure FinRing.ComUnitRing.finUnitRingType.
Canonical Structure FinRing.ComUnitRing.comUnitRingType.
Canonical Structure FinRing.ComUnitRing.join_finType.
Canonical Structure FinRing.ComUnitRing.join_finZmodType.
Canonical Structure FinRing.ComUnitRing.join_finRingType.
Canonical Structure FinRing.ComUnitRing.join_finComRingType.
Canonical Structure FinRing.ComUnitRing.join_finUnitRingType.
Canonical Structure FinRing.ComUnitRing.ujoin_finComRingType.
Canonical Structure FinRing.ComUnitRing.cjoin_finUnitRingType.
Canonical Structure FinRing.ComUnitRing.fcjoin_finUnitRingType.

Canonical Structure FinRing.IntegralDomain.eqType.
Canonical Structure FinRing.IntegralDomain.choiceType.
Canonical Structure FinRing.IntegralDomain.countType.
Canonical Structure FinRing.IntegralDomain.finType.
Canonical Structure FinRing.IntegralDomain.zmodType.
Canonical Structure FinRing.IntegralDomain.finZmodType.
Canonical Structure FinRing.IntegralDomain.ringType.
Canonical Structure FinRing.IntegralDomain.finRingType.
Canonical Structure FinRing.IntegralDomain.comRingType.
Canonical Structure FinRing.IntegralDomain.finComRingType.
Canonical Structure FinRing.IntegralDomain.unitRingType.
Canonical Structure FinRing.IntegralDomain.finUnitRingType.
Canonical Structure FinRing.IntegralDomain.comUnitRingType.
Canonical Structure FinRing.IntegralDomain.finComUnitRingType.
Canonical Structure FinRing.IntegralDomain.idomainType.
Canonical Structure FinRing.IntegralDomain.join_finType.
Canonical Structure FinRing.IntegralDomain.join_finZmodType.
Canonical Structure FinRing.IntegralDomain.join_finRingType.
Canonical Structure FinRing.IntegralDomain.join_finComRingType.
Canonical Structure FinRing.IntegralDomain.join_finUnitRingType.
Canonical Structure FinRing.IntegralDomain.join_finComUnitRingType.

Canonical Structure FinRing.Field.eqType.
Canonical Structure FinRing.Field.choiceType.
Canonical Structure FinRing.Field.countType.
Canonical Structure FinRing.Field.finType.
Canonical Structure FinRing.Field.zmodType.
Canonical Structure FinRing.Field.finZmodType.
Canonical Structure FinRing.Field.ringType.
Canonical Structure FinRing.Field.finRingType.
Canonical Structure FinRing.Field.comRingType.
Canonical Structure FinRing.Field.finComRingType.
Canonical Structure FinRing.Field.unitRingType.
Canonical Structure FinRing.Field.finUnitRingType.
Canonical Structure FinRing.Field.comUnitRingType.
Canonical Structure FinRing.Field.finComUnitRingType.
Canonical Structure FinRing.Field.idomainType.
Canonical Structure FinRing.Field.finIdomainType.
Canonical Structure FinRing.Field.fieldType.
Canonical Structure FinRing.decFieldType.
Canonical Structure FinRing.Field.join_finType.
Canonical Structure FinRing.Field.join_finZmodType.
Canonical Structure FinRing.Field.join_finRingType.
Canonical Structure FinRing.Field.join_finComRingType.
Canonical Structure FinRing.Field.join_finUnitRingType.
Canonical Structure FinRing.Field.join_finComUnitRingType.
Canonical Structure FinRing.Field.join_finIdomainType.

Canonical Structure FinRing.decField_finType.
Canonical Structure FinRing.decField_finZmodType.
Canonical Structure FinRing.decField_finRingType.
Canonical Structure FinRing.decField_finComRingType.
Canonical Structure FinRing.decField_finUnitRingType.
Canonical Structure FinRing.decField_finComUnitRingType.
Canonical Structure FinRing.decField_finIdomainType.

Canonical Structure FinRing.Lmodule.eqType.
Canonical Structure FinRing.Lmodule.choiceType.
Canonical Structure FinRing.Lmodule.countType.
Canonical Structure FinRing.Lmodule.finType.
Canonical Structure FinRing.Lmodule.zmodType.
Canonical Structure FinRing.Lmodule.finZmodType.
Canonical Structure FinRing.Lmodule.lmodType.

Bind Scope ring_scope with FinRing.Zmodule.sort.
Bind Scope ring_scope with FinRing.Ring.sort.
Bind Scope ring_scope with FinRing.ComRing.sort.
Bind Scope ring_scope with FinRing.UnitRing.sort.
Bind Scope ring_scope with FinRing.ComUnitRing.sort.
Bind Scope ring_scope with FinRing.IntegralDomain.sort.
Bind Scope ring_scope with FinRing.Field.sort.
Bind Scope ring_scope with FinRing.Lmodule.sort.
Bind Scope group_scope with FinRing.unit_of.

Notation finZmodType := FinRing.Zmodule.type.
Notation finRingType := FinRing.Ring.type.
Notation finComRingType := FinRing.ComRing.type.
Notation finUnitRingType := FinRing.UnitRing.type.
Notation finComUnitRingType := FinRing.ComUnitRing.type.
Notation finIdomainType := FinRing.IntegralDomain.type.
Notation finFieldType := FinRing.Field.type.
Notation finLmoduleType R := (FinRing.Lmodule.type (Phant R)).

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
Notation "[ 'finLmoduleType' [ R ] 'of' T ]" :=
    (do_pack (@FinRing.Lmodule.pack _ (Phant R)) T)
  (at level 0, format "[ 'finLmoduleType' [ R ] 'of'  T ]") : form_scope.

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
Canonical Structure finLmodule_baseFinGroupType
                      (R : ringType) (M : finLmoduleType R) :=
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
                      (R : ringType) (M : finLmoduleType R) :=
  Eval hnf in [baseFinGroupType of M : lmodType R  for +%R].
Canonical Structure lmod_finGroupType
                      (R : ringType) (M : finLmoduleType R) :=
  Eval hnf in [finGroupType of M : lmodType R for +%R].

