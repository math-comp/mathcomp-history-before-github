(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun ssralg matrix zmodp vector algebra.

(*****************************************************************************)
(*  * Finite dimensional Field Extentions                                    *)
(*     fieldExt F      == type for finite dimensional field extension.       *)
(*     FieldExt F E    == packs a field E to build a field extension over    *)
(*                         F. The field E should have a canonical structure  *)
(*                         as a algFType over F.                             *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Open Local Scope ring_scope.

Import GRing.Theory.

(* Finite Dimensional Field Extension *)

Module FieldExt.

Import GRing.

Section FieldExt.

Variable R : Ring.type.
Implicit Type phR : phant R.

Record class_of (T : Type) : Type := Class {
  base1 :> Field.class_of T;
  lmod_ext :> Lmodule.mixin_of R (Zmodule.Pack base1 T);
  lalg_ext :> @Lalgebra.axiom R (Lmodule.Pack _ (Lmodule.Class lmod_ext) T) 
                                (Ring.mul base1);
  alg_ext :> Algebra.axiom (Lalgebra.Pack (Phant R) (Lalgebra.Class lalg_ext) T); (* Do I really need this since it can be derived? *)
  vec_ext :> VectorType.mixin_of (Lmodule.Pack _ (Lmodule.Class lmod_ext) T)
}.

Coercion base2 T (m:class_of T) := @AlgFType.Class R T (Algebra.Class m) (vec_ext m).
Coercion base3 T (m:class_of T) := @UnitAlgebra.Class R T m m.

Structure type phR := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class phR (cT : type phR) :=
  let: Pack _ c _ :=  cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T :=
  fun bT b & phant_id (Field.class bT) (b : Field.class_of T) =>
  fun mT lm lam am vm & phant_id (@AlgFType.class _ phR mT) 
   (@AlgFType.Class R T 
    (@Algebra.Class R T (@Lalgebra.Class R T b lm lam) am)
    vm) =>
  Pack (Phant R) (@Class T b lm lam am vm) T.

Lemma AlgebraAxiom : forall T
  (base : Field.class_of T)
  (lmod_ext : Lmodule.mixin_of R (Zmodule.Pack base T))
  (lalg_ext : @Lalgebra.axiom R (Lmodule.Pack _ (Lmodule.Class lmod_ext) T) 
                                (Ring.mul base)),
  Algebra.axiom (Lalgebra.Pack (Phant R) (Lalgebra.Class lalg_ext) T).
Proof.
move=> T b lm lam c /= x y.
have Hcom: (commutative (Ring.mul b)) by case: (ComUnitRing.base b).
rewrite /mul /= !(Hcom x).
by rewrite scaler_mull.
Qed.

Coercion eqType phR cT := Equality.Pack (@class phR cT) cT.
Coercion choiceType phR cT := Choice.Pack (@class phR cT) cT.
Coercion zmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Coercion ringType phR cT := Ring.Pack (@class phR cT) cT.
Coercion unitRingType phR cT := UnitRing.Pack (@class phR cT) cT.
Coercion comRingType phR cT := ComRing.Pack (@class phR cT) cT.
Coercion comUnitRingType phR cT := ComUnitRing.Pack (@class phR cT) cT.
Coercion idomainType phR cT := IntegralDomain.Pack (@class phR cT) cT.
Coercion fieldType phR cT := Field.Pack (@class phR cT) cT.
Coercion lmodType phR cT := Lmodule.Pack phR (@class phR cT) cT.
Coercion lalgType phR cT := Lalgebra.Pack phR (@class phR cT) cT.
Coercion algType phR cT := Algebra.Pack phR (@class phR cT) cT.
Coercion unitAlgType phR cT := UnitAlgebra.Pack phR (@class phR cT) cT.
Coercion vectorType phR cT := VectorType.Pack phR (@class phR cT) cT.
Coercion algfType phR cT := AlgFType.Pack phR (@class phR cT) cT.

Definition unitRing_algfType phR  cT :=
  @UnitRing.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition comRing_algfType phR  cT :=
  @ComRing.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition comUnitRing_algfType phR  cT :=
  @ComUnitRing.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition idomain_algfType phR  cT :=
  @IntegralDomain.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition field_algfType phR  cT :=
  @Field.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition unitAlg_algfType phR  cT :=
  @UnitAlgebra.Pack R phR (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).

Definition unitRing_unitAlgType phR  cT :=
  @UnitRing.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition comRing_unitAlgType phR  cT :=
  @ComRing.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition comUnitRing_unitAlgType phR  cT :=
  @ComUnitRing.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition idomain_unitAlgType phR  cT :=
  @IntegralDomain.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition field_unitAlgType phR  cT :=
  @Field.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition lmodRing_unitAlgType phR  cT :=
  @Lmodule.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition lalgRing_unitAlgType phR  cT :=
  @Lalgebra.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition algRing_unitAlgType phR  cT :=
  @Algebra.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition vectorRing_unitAlgType phR  cT :=
  @VectorType.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition algfRing_unitAlgType phR  cT :=
  @AlgFType.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).

End FieldExt.

End FieldExt.

Canonical Structure FieldExt.eqType.
Canonical Structure FieldExt.choiceType.
Canonical Structure FieldExt.zmodType.
Canonical Structure FieldExt.ringType.
Canonical Structure FieldExt.unitRingType.
Canonical Structure FieldExt.comRingType.
Canonical Structure FieldExt.comUnitRingType.
Canonical Structure FieldExt.idomainType.
Canonical Structure FieldExt.fieldType.
Canonical Structure FieldExt.lmodType.
Canonical Structure FieldExt.lalgType.
Canonical Structure FieldExt.algType.
Canonical Structure FieldExt.unitAlgType.
Canonical Structure FieldExt.vectorType.
Canonical Structure FieldExt.algfType.
Canonical Structure FieldExt.unitRing_algfType.
Canonical Structure FieldExt.comRing_algfType.
Canonical Structure FieldExt.comUnitRing_algfType.
Canonical Structure FieldExt.idomain_algfType.
Canonical Structure FieldExt.field_algfType.
Canonical Structure FieldExt.unitAlg_algfType.
Canonical Structure FieldExt.unitRing_unitAlgType.
Canonical Structure FieldExt.comRing_unitAlgType.
Canonical Structure FieldExt.comUnitRing_unitAlgType.
Canonical Structure FieldExt.idomain_unitAlgType.
Canonical Structure FieldExt.field_unitAlgType.
Canonical Structure FieldExt.lmodRing_unitAlgType.
Canonical Structure FieldExt.lalgRing_unitAlgType.
Canonical Structure FieldExt.algRing_unitAlgType.
Canonical Structure FieldExt.vectorRing_unitAlgType.
Canonical Structure FieldExt.algfRing_unitAlgType.

Bind Scope ring_scope with FieldExt.sort.

Notation fieldExtType R := (@FieldExt.type _ (Phant R)).
Notation FieldExtType R T :=
    (@FieldExt.pack _ (Phant R) T _ _ id _ _ _ _ _ id).
