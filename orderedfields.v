Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
Require Import bigops ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.

Module OrderedField.

Record mixin_of (R : ringType) := Mixin {
  leq : rel R;
  _ : antisymmetric leq;
  _ : transitive leq;
  _ : total leq;
  _ : forall z x y, leq x y -> leq (x + z) (y + z);
  _ : forall x y, leq 0%R x -> leq 0%R y -> leq 0%R (x * y)%R
}.

Record class_of (R : Type) : Type := Class {
  base :> GRing.Field.class_of R;
  ext :> mixin_of (GRing.Ring.Pack base R)
}.

Record type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type }.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@GRing.Ring.Pack T b0 T)) :=
  fun bT b & phant_id (GRing.Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.


Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := GRing.Field.Pack (class cT) cT.

End OrderedField.

Bind Scope ring_scope with OrderedField.sort.
Canonical Structure OrderedField.eqType.
Canonical Structure OrderedField.choiceType.
Canonical Structure OrderedField.zmodType.
Canonical Structure OrderedField.ringType.
Canonical Structure OrderedField.comRingType.
Canonical Structure OrderedField.unitRingType.
Canonical Structure OrderedField.comUnitRingType.
Canonical Structure OrderedField.idomainType.
Canonical Structure OrderedField.fieldType.


Notation oFieldType := OrderedField.type.
Notation OFieldType T m := (OrderedField.pack T _ m _ _ id _ id).
Notation OFieldMixin := OrderedField.Mixin.
Notation "[ 'oFieldType' 'of' T 'for' cT ]" := (OrderedField.clone T cT _ idfun)
  (at level 0, format "[ 'oFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'oFieldType' 'of' T ]" := (OrderedField.clone T _ _ id)
  (at level 0, format "[ 'oFieldType'  'of'  T ]") : form_scope.

Open Scope ring_scope.

Definition leqr (F : oFieldType) : rel F := 
  OrderedField.leq (OrderedField.class F).
Notation "<=%R" := (@leqr _) : ring_scope.
Notation "x <= y" := (leqr x y) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x < y"  := (~~(y <= x)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Section OrderedFieldTheory.

Variable F : oFieldType.
Implicit Types x y z t : F.

Lemma leqr_anti : antisymmetric (@leqr F). Proof. by case F => T [? []]. Qed.
Lemma leqr_trans : transitive (@leqr F). Proof. by case F => T [? []]. Qed.
Lemma leqr_total : total (@leqr F). Proof. by case F => T [? []]. Qed.
Lemma leqrr : reflexive (@leqr F).
Proof. by move=> x; rewrite -[_<=_]orbb; apply: leqr_total. Qed.
Hint Resolve leqrr.

Lemma ltrNge : forall x y, ~~(x < y) = (x >= y).
Proof. by move=> x y; rewrite negbK. Qed.

Lemma leqr_add2l : forall z x y, ((x + z) <= (y + z)) = (x <= y).
Proof. 
have w : forall z x y, x <= y -> (x + z) <= (y + z).
  by case F => T [? []].
move=> z x y; apply/idP/idP; last exact: w.
by move/(w (-z)); rewrite -!addrA subrr !addr0.
Qed.

Lemma leqr_add2r : forall z x y, ((z + x) <= (z + y)) = (x <= y).
Proof. move=> z x y; rewrite ![z+_]addrC; exact: leqr_add2l. Qed.

Lemma leq0r_mul : forall x y, 0 <= x -> 0 <= y -> 0 <= (x * y).
Proof. by case F => T [? []]. Qed.

Lemma leqr_sub : forall x y,  (x <= y) = (0 <= y - x).
Proof. by move=> x y; symmetry; rewrite -(leqr_add2l x) add0r subrK. Qed.

Lemma leqr_opp : forall x y, (y <= x) = (-x <= -y).
Proof. by move=> x y; symmetry; rewrite leqr_sub opprK addrC -leqr_sub. Qed.

Lemma ltrW : forall x y, x < y -> x <= y.
Proof. by move=> x y; case/orP:(leqr_total x y)=> ->. Qed.
Hint Resolve ltrW.

Lemma eqr_leq : forall x y, (x == y) = (x <= y <= x).
Proof.
move=> x y; apply/idP/idP; last by move/leqr_anti->.
by move/eqP->; rewrite leqrr.
Qed.

Lemma leqr_lt : forall x y, x != y -> x <= y = (x < y).
Proof.
move=> x y xy; apply/idP/idP; last exact: ltrW.
case lyx : (y<=x)=> // lxy. apply: contra xy=> _.
by rewrite eqr_leq lxy lyx.
Qed.

Lemma leqr_nlt : forall x y, x <= y = ~~(y < x).
Proof. by move=> x y; apply: negbRL. Qed.

Lemma ltr_neqAle : forall x y, (x < y) = (x != y) && (x <= y).
Proof. 
move=> x y; case exy: (_==_)=> /=.
  by rewrite (eqP exy) leqrr.
by symmetry; rewrite leqr_lt ?exy.
Qed.

CoInductive leq_xor_gtr (x y : F) : bool -> bool -> Set :=
  | LeqNotGtr of x <= y : leq_xor_gtr x y true false
  | GtrNotLeq of y < x  : leq_xor_gtr x y false true.

Lemma leqrP : forall x y, leq_xor_gtr x y (x <= y) (y < x).
Proof. by move=> x y; case hxy: (_<=_); constructor; rewrite ?hxy //. Qed.

CoInductive ltr_xor_geq (x y : F) : bool -> bool -> Set :=
  | LtrNotGeq of x < y  : ltr_xor_geq x y false true
  | GeqNotLtr of y <= x : ltr_xor_geq x y true false.

Lemma ltrP : forall x y, ltr_xor_geq x y (y <= x) (x < y).
Proof. by move=> x y; case: (leqrP y x); constructor. Qed.

CoInductive comparer x y : bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y true false false
  | ComparerGt of x > y : comparer x y false true false
  | ComparerEq of x = y : comparer x y false false true.

Lemma ltrgtP : forall m n, comparer m n (m < n) (n < m) (m == n).
Proof.
move=> x y; case exy: (_==_); first by rewrite (eqP exy) leqrr; constructor.
case: (ltrP y x); rewrite leqr_lt ?exy //; last first.
  by move=> lxy; rewrite lxy; constructor.
rewrite negbK; move=> lyx; rewrite lyx; constructor.
by rewrite ltr_neqAle lyx eq_sym exy.
Qed.

Lemma leqr01 : @leqr F 0 1.
Proof. 
case/orP:(leqr_total 0 1); first done.
rewrite leqr_opp oppr0=> l0m.
by move: (leq0r_mul l0m l0m); rewrite mulrN mulr1 opprK.
Qed.

Lemma ltr01 : ~~ (@leqr F 1  0).
Proof. by rewrite -leqr_lt ?leqr01 // eq_sym oner_eq0. Qed.

Lemma leqr_add : forall x y z t, x <= y -> z <= t -> x + z <= y + t.
Proof.
move=> x y z t lxy.
rewrite -(leqr_add2r y)=> lyzyt; apply: leqr_trans lyzyt.
by rewrite leqr_add2l.
Qed.

Lemma leqr_mulP : forall z x y, 0 <= z -> (x <= y) -> (x * z <= y * z).
Proof.
move=> z x t zp lxy; rewrite leqr_sub -mulr_subl.
by apply: leq0r_mul; rewrite -?leqr_sub.
Qed.

Lemma leqr_mulN : forall z x y, 0 >= z -> (x <= y) -> (x * z >= y * z).
Proof.
move=> z x t zn lxy; rewrite leqr_opp -!mulrN.
by apply: leqr_mulP=> //; rewrite leqr_opp opprK oppr0.
Qed.

Lemma leq0r_inv : forall x, (0 <= x) = (0 <= x^-1).
Proof.
move=> x; case x0: (x == 0); first by rewrite (eqP x0) invr0.
case leqrP=> l0x; case leqrP=> l0i //; apply/eqP.
  move: (leqr_mulN (ltrW l0i) l0x); rewrite divff ?x0 //.
  by rewrite mul0r leqr_nlt ltr01.
move: (leqr_mulP l0i (ltrW l0x)); rewrite divff ?x0 //.
by rewrite mul0r leqr_nlt ltr01.
Qed.

Lemma ltr_mulP : forall z x y, 0 < z ->  (x * z <= y * z) = (x <= y).
Proof.
move=> z x t; rewrite ltr_neqAle; case/andP; rewrite eq_sym=> zn0 zp. 
apply/idP/idP; last exact: leqr_mulP.
move:zp; rewrite leq0r_inv=> zp; move/(leqr_mulP zp).
by rewrite -!mulrA divff // !mulr1.
Qed.

Lemma ltr_mulN : forall z x y, 0 > z -> (x * z >= y * z) = (x <= y).
Proof.
move=> z x t zn; rewrite leqr_opp -!mulrN ltr_mulP //.
by rewrite leqr_opp opprK oppr0.
Qed.

Lemma neq_ltr : forall x y, (x != y) = (x < y) || (y < x).
Proof. by move=> *; rewrite eqr_leq negb_and orbC. Qed.

Lemma leqr_eqVlt : forall x y, (x <= y) = (x == y) || (x < y).
Proof. 
move=> x y. rewrite ltr_neqAle. 
by case exy: (_==_); rewrite ?(andbT,andbF) // (eqP exy) leqrr.
Qed.

Lemma leq_ltr_trans : forall y x z, x <= y -> y < z -> x < z.
Proof. move=> y x z lxy; apply: contra=> lzx; exact: leqr_trans lxy. Qed.

Lemma ltr_trans : forall y x z, x < y -> y < z -> x < z.
Proof. move=> y x z; move/ltrW; exact: leq_ltr_trans. Qed.

End OrderedFieldTheory.

Require Import poly.

Module RealClosedField.

Record mixin_of (F : oFieldType) := Mixin {
  _ : forall x : F, 0 <= x -> exists y, x = y ^+ 2;
  _ : forall (p : {poly F}), ~~ odd (size p) -> exists x : F, root p x
(* Should we replace it by a poly independant version, as in ClosedField ? *)
}.

Record class_of (R : Type) : Type := Class {
  base :> OrderedField.class_of R; 
   (* In fact, this should be a new kind of Decidable Field 
      including the Leq constructor ... *)
  ext :> mixin_of (OrderedField.Pack base R)
}.

Record type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type }.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@OrderedField.Pack T b0 T)) :=
  fun bT b & phant_id (OrderedField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.


Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := GRing.Field.Pack (class cT) cT.
Coercion oFieldType cT := OrderedField.Pack (class cT) cT.

End RealClosedField.

Bind Scope ring_scope with RealClosedField.sort.
Canonical Structure RealClosedField.eqType.
Canonical Structure RealClosedField.choiceType.
Canonical Structure RealClosedField.zmodType.
Canonical Structure RealClosedField.ringType.
Canonical Structure RealClosedField.comRingType.
Canonical Structure RealClosedField.unitRingType.
Canonical Structure RealClosedField.comUnitRingType.
Canonical Structure RealClosedField.idomainType.
Canonical Structure RealClosedField.fieldType.
Canonical Structure RealClosedField.oFieldType.


Notation rFieldType := RealClosedField.type.
Notation RFieldType T m := (RealClosedField.pack T _ m _ _ id _ id).
Notation RFieldMixin := RealClosedField.Mixin.
Notation "[ 'rFieldType' 'of' T 'for' cT ]" := (RealClosedField.clone T cT _ idfun)
  (at level 0, format "[ 'rFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'rFieldType' 'of' T ]" := (RealClosedField.clone T _ _ id)
  (at level 0, format "[ 'rFieldType'  'of'  T ]") : form_scope.

