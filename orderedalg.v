(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg finset fingroup zmodp zint.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Import GRing.Theory.

Reserved Notation  "`| x |" (at level 0, x at level 99, format "`| x |").
Reserved Notation "x <= y :> T" (at level 70, y at next level).
Reserved Notation "x >= y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x < y :> T" (at level 70, y at next level).
Reserved Notation "x > y :> T" (at level 70, y at next level, only parsing).

Module OrderedRing.

Module PartialOrder.

Record mixin_of (R : ringType) := Mixin {
  pos : pred R;
  _ : pos 0;
  _ : forall x y, pos x -> pos y -> pos (x + y);
  _ : forall x y, pos x -> pos y -> pos (x * y);
  _  : forall x, pos x -> pos (-x) -> x = 0
}.

Local Notation ring_mixin_of T b := (mixin_of (@GRing.Ring.Pack T b T)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later 
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_ring : forall T, base_of T -> GRing.Ring.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, ring_mixin_of T (to_ring b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T b0 (m0 : ring_mixin_of T b0) :=
  fun bT b & phant_id (base_class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_ring base_sort].

Module IntegralDomain.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : GRing.IntegralDomain.class_of R;
  mixin : mixin_of (GRing.Ring.Pack base R)
}.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Open Scope ring_scope.

Module OrderDef.

Definition posr (R : IntegralDomain.type) : pred R := pos (IntegralDomain.class R).
Definition ler (R : IntegralDomain.type) : rel R := fun (x y : R) => posr (y - x).
Notation "<=%R" := (@ler _) : ring_scope.
Notation "x <= y" := (ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Definition ltr (R : IntegralDomain.type) : rel R := 
  fun x y => (x != y) && (x <= y :> R).
Notation "<%R" := (@ltr _) : ring_scope.
Notation "x < y"  := (ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "`[ a , b ]" := [pred x | a <= x <= b]
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : ring_scope.
Notation "`] a , b ]" := [pred x | a < x <= b]
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : ring_scope.
Notation "`[ a , b [" := [pred x | a <= x < b]
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : ring_scope.
Notation "`] a , b [" := [pred x | a < x < b]
  (at level 0, a, b at level 9 , format "`] a ,  b [") : ring_scope.
Notation "`] '-oo' , b ]" := [pred x | x <= b]
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : ring_scope.
Notation "`] '-oo' , b [" := [pred x | x < b]
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : ring_scope.
Notation "`[ a , '+oo' [" := [pred x | a <= x]
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : ring_scope.
Notation "`] a , '+oo' [" := [pred x | a < x]
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : ring_scope.

Definition sgr (R : IntegralDomain.type) (x : R) : zint := 
  if x == 0 then 0 else if 0 <= x then 1 else -1.
Definition absr (R : IntegralDomain.type) (x : R) := 
  if 0 <= x then x else - x.
Notation "`| x |" := (@absr _ x) : ring_scope.

Definition minr (R : IntegralDomain.type) (x y : R) :=
  if x <= y then x else y.
Definition maxr (R : IntegralDomain.type) (x y : R) :=
  if y <= x then x else y.

End OrderDef.

Import OrderDef.

Module IntegralDomainTheory.

Section IntegralDomainTheory.

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

Lemma posr0 : @posr R 0.
Proof. by case R => T [? []]. Qed.
Lemma posr_add : forall x y, posr x -> posr y -> posr (x + y).
Proof. by case R => T [? []]. Qed.
Lemma posr_mul : forall x y, posr x -> posr y -> posr (x * y).
Proof. by case R => T [? []]. Qed.
Lemma posr_eq0 : forall x, posr x -> posr (-x) -> x = 0.
Proof. by case R => T [? []]. Qed.

Hint Resolve posr0.

Lemma ler_pos : forall x y, (x <= y) = posr (y - x).
Proof. done. Qed.
Lemma ltr_pos : forall x y, (x < y) = (x != y) && posr (y - x).
Proof. done. Qed.
Definition lter_pos := (ler_pos, ltr_pos).

Lemma posr_ge0 : forall x, posr x = (0 <= x).
Proof. by move=> x; rewrite ler_pos subr0. Qed.

Lemma ler_anti : antisymmetric (@ler R).
Proof.
move=> x y; rewrite !ler_pos; case/andP=> pxy pyx.
by apply/eqP; rewrite -subr_eq0 [_ - _]posr_eq0 ?oppr_sub.
Qed.

Lemma ler_trans : transitive (@ler R).
Proof. 
move=> x y z; rewrite !ler_pos => pyx pzy.
by move: (posr_add pzy pyx); rewrite addrA addrNK.
Qed.

Lemma lerr : forall x, x <= x.
Proof. by move=> x; rewrite /ler subrr. Qed.
Hint Resolve lerr.

Lemma ltr_neqAle : forall x y, (x < y) = (x != y) && (x <= y). 
Proof. done. Qed.

Lemma ler_eqVlt : forall x y, (x <= y) = (x == y) || (x < y).
Proof.
move=> x y; rewrite ltr_neqAle.
by case xy: (x == y)=> //=; rewrite (eqP xy) lerr.
Qed.

Lemma ltrr : irreflexive (@ltr R).
Proof. by move=> x; rewrite /ltr lerr eqxx. Qed.
Hint Resolve ltrr.

Definition lterr := (lerr, ltrr).

Lemma ler_add2l : forall z x y, ((x + z) <= (y + z)) = (x <= y).
Proof. by move=> z x y; rewrite lter_pos oppr_add addrA addrAC addrK. Qed.

Lemma ltr_add2l : forall z x y, ((x + z) < (y + z)) = (x < y).
Proof.
move=> z x y; by rewrite !ltr_neqAle (inj_eq (@addIr _ _)) ler_add2l.
Qed.

Definition lter_add2l := (ler_add2l, ltr_add2l).

Lemma ler_add2r : forall z x y, ((z + x) <= (z + y)) = (x <= y).
Proof. by move=> z x y; rewrite ![z + _]addrC lter_add2l. Qed.

Lemma ltr_add2r : forall z x y, ((z + x) < (z + y)) = (x < y).
Proof. by move=> z x y; rewrite ![z + _]addrC lter_add2l. Qed.

Definition lter_add2r := (ler_add2r, ltr_add2r).
Definition lter_add2 := (lter_add2l, lter_add2r).

Lemma subr_ge0 : forall  x y, (0 <= (y - x)) = (x <= y).
Proof. by move=> x y; rewrite !ler_pos subr0. Qed.

Lemma subr_le0 : forall  x y, ((y - x) <= 0) = (y <= x).
Proof. by move=> x y; rewrite ler_pos sub0r oppr_sub. Qed.

Lemma subr_gt0 : forall  x y, (0 < (y - x)) = (x < y).
Proof. by move=> x y; rewrite ltr_neqAle subr_ge0 eq_sym subr_eq0 eq_sym. Qed.

Lemma subr_lt0 : forall  x y, ((y - x) < 0) = (y < x).
Proof. by move=> x y; rewrite ltr_neqAle subr_le0 subr_eq0. Qed.

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

Lemma ler_opp2 : forall x y, (-x <= -y) = (y <= x).
Proof. by move=> x y; rewrite !lter_pos opprK addrC. Qed.

Lemma ltr_opp2 : forall x y, (-x < -y) = (y < x).
Proof. by move=> x y; rewrite ltr_neqAle ler_opp2 eqr_opp eq_sym. Qed.

Definition lter_opp2 := (ler_opp2, ltr_opp2).

Lemma ler_oppr : forall x y, (x <= -y) = (y <= -x).
Proof. by move=> x y; rewrite -lter_opp2 opprK. Qed.

Lemma ltr_oppr : forall x y, (x < -y) = (y < -x).
Proof. by move=> x y; rewrite -lter_opp2 opprK. Qed.

Definition lter_oppr := (ler_oppr, ltr_oppr).
Lemma ler_oppl : forall x y, (-x <= y) = (-y <= x).
Proof. by move=> x y; rewrite -lter_opp2 opprK. Qed.

Lemma ltr_oppl : forall x y, (-x < y) = (-y < x).
Proof. by move=> x y; rewrite -lter_opp2 opprK. Qed.

Definition lter_oppl := (ler_oppl, ltr_oppl).

Lemma oppr_ge0 : forall x, (0 <= -x) = (x <= 0).
Proof. by move=> x; rewrite lter_oppr oppr0. Qed.

Lemma oppr_gt0 : forall x, (0 < -x) = (x < 0).
Proof. by move=> x; rewrite lter_oppr oppr0. Qed.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).
Lemma oppr_le0 : forall x, (-x <= 0) = (0 <= x).
Proof. by move=> x; rewrite lter_oppl oppr0. Qed.

Lemma oppr_lt0 : forall x, (-x < 0) = (0 < x).
Proof. by move=> x; rewrite lter_oppl oppr0. Qed.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lter_oppE := (oppr_cp0, lter_opp2).

Lemma ltrW : forall x y, x < y -> x <= y.
Proof. by move=> x y; rewrite ler_eqVlt=> ->; rewrite orbT. Qed.
Hint Resolve ltrW.

Lemma eqr_le : forall x y, (x == y) = (x <= y <= x).
Proof.
move=> x y; apply/idP/idP; last by move/ler_anti->.
by move/eqP->; rewrite lerr.
Qed.

Lemma ltr_asym : forall x y, x < y < x = false.
Proof.
by move=> x y; rewrite !ltr_neqAle andbCA -andbA -eqr_le eq_sym; case: (x == y).
Qed.

Lemma ltr_le_asym : forall x y, x < y <= x = false.
Proof. by move=> x y; rewrite ltr_neqAle -andbA -eqr_le; case: (x == y). Qed.

Lemma ler_lt_asym : forall x y, x <= y < x = false.
Proof. by move=> x y; rewrite andbC ltr_le_asym. Qed.

Lemma ler_lt : forall x y, x != y -> x <= y = (x < y).
Proof. by move=> x y; rewrite ltr_neqAle=> ->. Qed.

Lemma ltrWN : forall x y, x < y -> x == y = false.
Proof. by move=> x y; rewrite ltr_neqAle; case/andP; move/negPf=> ->. Qed.
Hint Resolve ltrWN.

Lemma ltrNW : forall x y, y < x -> x == y = false.
Proof. by move=> x y hyx; rewrite eq_sym ltrWN. Qed.

Definition ltrE x y (hxy : x < y) := (hxy, (ltrWN hxy), (ltrW hxy)).

Lemma ler_lt_trans : forall y x z, x <= y -> y < z -> x < z.
Proof.
move=> y x z lxy; rewrite !ltr_neqAle; case/andP=> nyz lyz.
rewrite (ler_trans lxy lyz) andbT; apply: contra nyz.
by move/eqP=> eyz; rewrite eqr_le lyz -eyz.
Qed.

Lemma ltr_le_trans : forall y x z, x < y -> y <= z -> x < z.
Proof.
move=> y x z; rewrite !ltr_neqAle; case/andP=> nxy lxy lyz.
rewrite (ler_trans lxy lyz) andbT; apply: contra nxy.
by move/eqP=> eyz; rewrite eqr_le lxy eyz lyz.
Qed.

Lemma ltr_trans : transitive (@ltr R).
Proof. by move=> x y z lxy lyz; apply: (@ler_lt_trans x); rewrite // ltrW. Qed.

Definition lter_trans y := (ler_trans, ltr_trans).
Definition lter_le_trans y x z lyz := (ler_trans^~ lyz, ltr_le_trans^~ lyz). 
Definition ler_lte_trans y x z (lxy : x <= y) := 
  (@ler_trans y x z lxy, @ler_lt_trans  y x z lxy). 
Definition ltr_lte_trans y x z (lxy : x < y) := 
  (@ltr_trans y x z lxy, @ltr_le_trans  y x z lxy). 

Lemma ge0_cp : forall x, 0 <= x -> (-x <= 0) * (-x <= x).
Proof. by move=> x hx; rewrite oppr_cp0 hx (@ler_trans 0) ?oppr_cp0. Qed.

Lemma gt0_cp : forall x, 0 < x -> 
 (0 <= x) * (-x <= 0) * (-x <= x) * (-x < 0) * (-x < x).
Proof. 
move=> x hx; move: (ltrW hx)=> hx'; rewrite !ge0_cp // hx'.
by rewrite oppr_cp0 hx // (@ltr_trans 0) ?oppr_cp0.
Qed.

Lemma mem0_intcc_xNx : forall x, 0 \in `[-x, x] = (0 <= x).
Proof. 
by move=> x; rewrite !inE; case hx: (0 <= _); rewrite (andbT, andbF) ?ge0_cp.
Qed.

Lemma mem0_intoo_xNx : forall x, 0 \in `](-x), x[ = (0 < x).
Proof. 
by move=> x; rewrite !inE; case hx: (0 < _); rewrite (andbT, andbF) ?gt0_cp.
Qed.

Lemma le0_cp : forall x, x <= 0 -> (0 <= -x) * (x <= -x).
Proof. by move=> x hx; rewrite oppr_cp0 hx (@ler_trans 0) ?oppr_cp0. Qed.

Lemma lt0_cp : forall x, x < 0 -> 
  (x <= 0) * (0 <= -x) * (x <= -x) * (0 < -x) * (x < -x).
Proof. 
Proof. 
move=> x hx; move: (ltrW hx)=> hx'; rewrite !le0_cp // hx'.
by rewrite oppr_cp0 hx // (@ltr_trans 0) ?oppr_cp0.
Qed.

Lemma ler_add : forall x y z t, x <= y -> z <= t -> x + z <= y + t.
Proof. by move=> x y z t lxy lzt; rewrite (@ler_trans (y + z)) ?lter_add2. Qed.

Lemma ler_lt_add : forall x y z t, x <= y -> z < t -> x + z < y + t.
Proof.
move=> x y z t lxy lzt.
by rewrite (@ler_lt_trans (y + z)) ?lter_add2.
Qed.

Lemma ltr_le_add : forall x y z t, x < y -> z <= t -> x + z < y + t.
Proof.
move=> x y z t lxy lzt.
by rewrite (@ltr_le_trans (y + z)) ?lter_add2.
Qed.

Lemma ltr_add : forall x y z t, x < y -> z < t -> x + z < y + t.
Proof. by move=> x y z t lxy lzt; rewrite ltr_le_add // ltrW. Qed.

Lemma ler_sub : forall x y z t, x <= y -> t <= z -> x - z <= y - t.
Proof. by move=> x y z t lxy ltz; rewrite ler_add // lter_opp2. Qed.

Lemma ler_lt_sub : forall x y z t, x <= y -> t < z -> x - z < y - t.
Proof. by move=> x y z t lxy lzt; rewrite ler_lt_add // lter_opp2. Qed.

Lemma ltr_le_sub : forall x y z t, x < y -> t <= z -> x - z < y - t.
Proof. by move=> x y z t lxy lzt; rewrite ltr_le_add // lter_opp2. Qed.

Lemma ltr_add2 : forall x y z t, x < y -> t < z -> x - z < y - t.
Proof. by move=> x y z t lxy lzt; rewrite ltr_add // lter_opp2. Qed.

Lemma ler_subl_addl : forall x y z, (x - y <= z) = (x <= z + y).
Proof. by move=> x y z; rewrite !ler_pos oppr_sub addrA. Qed.

Lemma ltr_subl_addl : forall x y z, (x - y < z) = (x < z + y).
Proof. by move=> x y z; rewrite !ltr_neqAle ler_subl_addl subr_eq. Qed.

Lemma ler_subr_addl : forall x y z, (x <= y - z) = (x + z <= y).
Proof. by move=> x y z; rewrite !ler_pos oppr_add addrAC addrA. Qed.

Lemma ltr_subr_addl : forall x y z, (x < y - z) = (x + z < y).
Proof. 
by move=> x y z; rewrite !ltr_neqAle ler_subr_addl eq_sym subr_eq eq_sym.
Qed.

Definition lter_subl_addl := (ler_subl_addl, ltr_subl_addl).
Definition lter_subr_addl := (ler_subr_addl, ltr_subr_addl).
Definition lter_sub_addl := (lter_subr_addl, lter_subl_addl).

Lemma ler_subl_addr : forall x y z, (x - y <= z) = (x <= y + z).
Proof. by move=> x y z; rewrite lter_sub_addl addrC. Qed.

Lemma ltr_subl_addr : forall x y z, (x - y < z) = (x < y + z).
Proof. by move=> x y z; rewrite lter_sub_addl addrC. Qed.

Lemma ler_subr_addr : forall x y z, (x <= y - z) = (z + x <= y).
Proof. by move=> x y z; rewrite lter_sub_addl addrC. Qed.

Lemma ltr_subr_addr : forall x y z, (x < y - z) = (z + x < y).
Proof. by move=> x y z; rewrite lter_sub_addl addrC. Qed.

Definition lter_subl_addr := (ler_subl_addr, ltr_subl_addr).
Definition lter_subr_addr := (ler_subr_addr, ltr_subr_addr).
Definition lter_sub_addr := (lter_subr_addr, lter_subl_addr).

Lemma ler_addr : forall x y, (x <= x + y) = (0 <= y).
Proof. by move=> x y; rewrite -{1}[x]addr0 lter_add2r. Qed.

Lemma ltr_addr : forall x y, (x < x + y) = (0 < y).
Proof. by move=> x y; rewrite -{1}[x]addr0 lter_add2r. Qed.

Lemma ler_addl : forall x y, (x <= y + x) = (0 <= y).
Proof. by move=> x y; rewrite -{1}[x]add0r lter_add2l. Qed.

Lemma ltr_addl : forall x y, (x < y + x) = (0 < y).
Proof. by move=> x y; rewrite -{1}[x]add0r lter_add2l. Qed.

Definition lter_addr := (ler_addr, ltr_addr).
Definition lter_addl := (ler_addl, ltr_addl).
Definition lter_add := (lter_addr, lter_addl).

Lemma ger_addr : forall x y, (x + y <= x) = (y <= 0).
Proof. by move=> x y; rewrite -{2}[x]addr0 lter_add2r. Qed.

Lemma gtr_addr : forall x y, (x + y < x) = (y < 0).
Proof. by move=> x y; rewrite -{2}[x]addr0 lter_add2r. Qed.

Lemma ger_addl : forall x y, (y + x <= x) = (y <= 0).
Proof. by move=> x y; rewrite -{2}[x]add0r lter_add2l. Qed.

Lemma gtr_addl : forall x y, (y + x < x) = (y < 0).
Proof. by move=> x y; rewrite -{2}[x]add0r lter_add2l. Qed.

Definition gter_addr := (ger_addr, gtr_addr).
Definition gter_addl := (ger_addl, gtr_addl).
Definition gter_add := (gter_addr, gter_addl).
Definition cpr_add := (gter_add, lter_add).

Lemma ger0_ler_add : forall x y z, 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> x y z *; rewrite -[y]add0r ler_add. Qed.

Lemma gtr0_ler_add : forall x y z, 0 < x -> y <= z -> y < x + z.
Proof. by move=> x y z *; rewrite -[y]add0r ltr_le_add. Qed.

Lemma ger0_ltr_add : forall x y z, 0 <= x -> y < z -> y < x + z.
Proof. by move=> x y z *; rewrite -[y]add0r ler_lt_add. Qed.

Lemma gtr0_ltr_add : forall x y z, 0 < x -> y < z -> y < x + z.
Proof. by move=> x y z *; rewrite -[y]add0r ltr_add. Qed.

Lemma ler0_ler_add : forall x y z, x <= 0 -> y <= z -> x + y <= z.
Proof. by move=> x y z *; rewrite -[z]add0r ler_add. Qed.

Lemma ltr0_ler_add : forall x y z, x < 0 -> y <= z -> x + y < z.
Proof. by move=> x y z *; rewrite -[z]add0r ltr_le_add. Qed.

Lemma ler0_ltr_add : forall x y z, x <= 0 -> y < z -> x + y < z.
Proof. by move=> x y z *; rewrite -[z]add0r ler_lt_add. Qed.

Lemma ltr0_ltr_add : forall x y z, x < 0 -> y < z -> x + y < z.
Proof. by move=> x y z *; rewrite -[z]add0r ltr_add. Qed.

Lemma addr_ge0 : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by move=> *; exact: ger0_ler_add. Qed.

Lemma addr_ge0_gt0 : forall x y, 0 <= x -> 0 < y -> 0 < x + y.
Proof. by move=> *; exact: ger0_ltr_add. Qed.

Lemma addr_gt0_ge0 : forall x y, 0 < x -> 0 <= y -> 0 < x + y.
Proof. by move=> *; exact: gtr0_ler_add. Qed.

Lemma addr_gt0 : forall x y, 0 < x -> 0 < y -> 0 < x + y.
Proof. by move=> *; exact: gtr0_ltr_add. Qed.

Lemma ler_addr_transl : forall y x z t, x <= y -> (z + y) <= t -> (z + x) <= t.
Proof. by move=> y x z t hxy hzyt; rewrite (ler_trans _ hzyt) ?lter_add2. Qed.

Lemma ltr_le_addr_transl : forall y x z t, x < y -> (z + y) <= t -> (z + x) < t.
Proof. by move=> y x z t hxy hzyt; rewrite (ltr_le_trans _ hzyt) ?lter_add2. Qed.

Lemma ler_lt_addr_transl : forall y x z t, x <= y -> (z + y) < t -> (z + x) < t.
Proof. by move=> y x z t hxy hzyt; rewrite (ler_lt_trans _ hzyt) ?lter_add2. Qed.

Lemma ltr_addr_transl : forall y x z t, x < y -> (z + y) < t -> (z + x) < t.
Proof. by move=> y x z t hxy hzyt; rewrite (ltr_trans _ hzyt) ?lter_add2. Qed.

Lemma ler_addr_transr : forall x y z t, x <= y -> t <= (z + x) -> t <= (z + y).
Proof. by move=> x y z t hxy hzyt; rewrite (ler_trans hzyt) ?lter_add2. Qed.

Lemma ltr_le_addr_transr : forall x y z t, x < y -> t <= (z + x) -> t < (z + y).
Proof. by move=> x y z t hxy hzyt; rewrite (ler_lt_trans hzyt) ?lter_add2. Qed.

Lemma ler_lt_addr_transr : forall x y z t, x <= y -> t < (z + x) -> t < (z + y).
Proof. by move=> x y z t hxy hzyt; rewrite (ltr_le_trans hzyt) ?lter_add2. Qed.

Lemma ltr_addr_transr : forall x y z t, x < y -> t < (z + x) -> t < (z + y).
Proof. by move=> x y z t hxy hzyt; rewrite (ltr_trans hzyt) ?lter_add2. Qed.

Lemma ler_addl_transl : forall y x z t, x <= y -> (y + z) <= t -> (x + z) <= t.
Proof. by move=> y *; rewrite addrC (@ler_addr_transl y) 1?addrC. Qed.

Lemma ltr_le_addl_transl : forall y x z t, x < y -> (y + z) <= t -> (x + z) < t.
Proof. by move=> y *; rewrite addrC (@ltr_le_addr_transl y) 1?addrC. Qed.

Lemma ler_lt_addl_transl : forall y x z t, x <= y -> (y + z) < t -> (x + z) < t.
Proof. by move=> y *; rewrite addrC (@ler_lt_addr_transl y) 1?addrC. Qed.

Lemma ltr_addl_transl : forall y x z t, x < y -> (y + z) < t -> (x + z) < t.
Proof. by move=> y *; rewrite addrC (@ltr_addr_transl y) 1?addrC. Qed.

Lemma ler_addl_transr : forall x y z t, x <= y -> t <= (x + z) -> t <= (y + z).
Proof. by move=> y *; rewrite addrC (@ler_addr_transr y) 1?addrC. Qed.

Lemma ltr_le_addl_transr : forall x y z t, x < y -> t <= (x + z) -> t < (y + z).
Proof. by move=> y *; rewrite addrC (@ltr_le_addr_transr y) 1?addrC. Qed.

Lemma ler_lt_addl_transr : forall x y z t, x <= y -> t < (x + z) -> t < (y + z).
Proof. by move=> y *; rewrite addrC (@ler_lt_addr_transr y) 1?addrC. Qed.

Lemma ltr_addl_transr : forall x y z t, x < y -> t < (x + z) -> t < (y + z).
Proof. by move=> y *; rewrite addrC (@ltr_addr_transr y) 1?addrC. Qed.


Lemma addr_eq0 : forall (x y : R), 0 <= x -> 0 <= y -> 
  (x + y == 0) = (x == 0) && (y == 0).
Proof.
move=> x y; rewrite ler_eqVlt; case/orP=> hx; rewrite [x == 0]eq_sym.
  by rewrite hx -(eqP hx) add0r.
rewrite (ltrWN hx) /= => hy; rewrite eq_sym; apply: ltrWN.
exact: addr_gt0_ge0.
Qed.

Lemma sumr_ge0 : forall I r (F : I -> R),
  (forall i, (0 <=  F i)) -> 0 <= \sum_(i <- r) (F i).
Proof.
move=> I; elim=> [|a r ihr] //= F arP; first by rewrite big_nil lerr.
rewrite big_cons addr_ge0 //=; exact: ihr.
Qed.

Lemma ler_sum : forall I r (P : pred I) (F G : I -> R),
  (forall i, P i -> F i <= G i) ->
  (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) G i.
Proof.
move=> I; elim=> [|i r ihr] // P F G hFG; first by rewrite !big_nil.
rewrite !big_cons; case Pi: (P i); last exact: ihr.
by rewrite ler_add ?hFG ?ihr.
Qed.

Lemma sumr_eq0 :  forall I r (F : I -> R), 
  (forall i, 0 <= F i) ->
  (\sum_(i <- r) (F i) == 0) =  (all (fun i => (F i == 0)) r).
Proof.
move=> I; elim=> [|a r ihr] //= F arP; first by rewrite big_nil eqxx.
by rewrite big_cons addr_eq0 ?ihr // sumr_ge0.
Qed.

Lemma mulr_ge0 : forall x y, 0 <= x -> 0 <= y -> 0 <= (x * y).
Proof. by move=> x y; rewrite -!posr_ge0=> px py; rewrite posr_mul. Qed.

Lemma mulr_gt0 : forall x y, 0 < x -> 0 < y -> 0 < (x * y).
Proof.
move=> x y px py; rewrite ltr_neqAle mulr_ge0 ?ltrW // eq_sym andbT.
by rewrite mulf_neq0 // eq_sym ltrWN.
Qed.

Definition mulr_gte0 := (mulr_ge0, mulr_gt0).

Lemma mulr_le0 : forall x y, x <= 0 -> y <= 0 -> 0 <= (x * y).
Proof. by move=> x y hx hy; rewrite -mulrNN mulr_gte0 ?oppr_gte0. Qed.

Lemma mulr_lt0 : forall x y, x < 0 -> y < 0 -> 0 < (x * y).
Proof. by move=> x y hx hy; rewrite -mulrNN mulr_gte0 ?oppr_gte0. Qed.

Definition mulr_lte0 := (mulr_le0, mulr_lt0).

Lemma mulr_ge0_le0 : forall x y, 0 <= x -> y <= 0 -> (x * y) <= 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulrN mulr_gte0 ?oppr_gte0. Qed.

Lemma mulr_gt0_lt0 : forall x y, 0 < x -> y < 0 -> (x * y) < 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulrN mulr_gte0 ?oppr_gte0. Qed.

Definition mulr_gte0_lte0 := (mulr_ge0_le0, mulr_gt0_lt0).

Lemma mulr_le0_ge0 : forall x y, x <= 0 -> 0 <= y -> (x * y) <= 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulNr mulr_gte0 ?oppr_gte0. Qed.

Lemma mulr_lt0_gt0 : forall x y, x < 0 -> 0 < y -> (x * y) < 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulNr mulr_gte0 ?oppr_gte0. Qed.

Definition mulr_lte0_gte0 := (mulr_le0_ge0, mulr_lt0_gt0).

Definition mulr_gte0_cp0 := (mulr_gte0, mulr_gte0_lte0).
Definition mulr_lte0_cp0 := (mulr_lte0, mulr_lte0_gte0).

Lemma ler_pmul2rW : forall x y z, 0 <= x -> y <= z -> x * y <= x * z.
Proof. by move=> *; rewrite ler_pos -mulr_subr posr_mul // posr_ge0. Qed.

Lemma ltr_pmul2rW : forall x y z, 0 < x -> y < z -> x * y < x * z.
Proof.
move=> x y z hx hyz; rewrite ltr_neqAle ler_pmul2rW 1?ltrW //.
by rewrite -subr_eq0 -mulr_subr mulf_neq0 // ?subr_eq0 ?[_ == 0]eq_sym ltrWN.
Qed.

Definition lter_pmul2rW := (ler_pmul2rW, ltr_pmul2rW).

Lemma ler_pmul2lW : forall x y z, 0 <= x -> y <= z -> y * x <= z * x.
Proof. by move=> x y z *; rewrite ![_ * x]mulrC lter_pmul2rW. Qed.

Lemma ltr_pmul2lW : forall x y z, 0 < x -> y < z -> y * x < z * x.
Proof. by move=> x y z *; rewrite ![_ * x]mulrC lter_pmul2rW. Qed.

Definition lter_pmul2lW := (ler_pmul2lW, ltr_pmul2lW).
Definition lter_pmulW := (lter_pmul2rW, lter_pmul2lW).

Lemma ler_nmul2rW : forall x y z, x <= 0 -> y <= z -> x * z <= x * y.
Proof. by move=> x y z *; rewrite -![x * _]mulrNN lter_pmulW ?lter_oppE. Qed.

Lemma ltr_nmul2rW : forall x y z, x < 0 -> y < z -> x * z < x * y.
Proof. by move=> x y z *; rewrite -![x * _]mulrNN lter_pmulW ?lter_oppE. Qed.

Definition lter_nmul2rW := (ler_nmul2rW, ltr_nmul2rW).

Lemma ler_nmul2lW : forall x y z, x <= 0 -> y <= z -> z * x <= y * x.
Proof. by move=> x y z *; rewrite -![_ * x]mulrNN lter_pmulW ?lter_oppE. Qed.

Lemma ltr_nmul2lW : forall x y z, x < 0 -> y < z -> z * x < y * x.
Proof. by move=> x y z *; rewrite -![_ * x]mulrNN lter_pmulW ?lter_oppE. Qed.

Definition lter_nmul2lW := (ler_nmul2lW, ltr_nmul2lW).
Definition lter_nmulW := (lter_nmul2rW, lter_nmul2lW).

Lemma exprSn_ge0 : forall n x, 0 <= x -> 0 <= x ^+ n.+1.
Proof. by elim=> [|n ihn] x hx //; rewrite [_ ^+ _.+2]exprS mulr_ge0 ?ihn. Qed.

Lemma exprSn_gt0 : forall n x, 0 < x -> 0 < x ^+ n.+1.
Proof. by elim=> [|n ihn] x hx //; rewrite [_ ^+ _.+2]exprS mulr_gt0 ?ihn. Qed.

Definition exprSn_gte0 := (exprSn_ge0, exprSn_gt0).

Section Interval.

Lemma intccP : forall x a b, reflect ((a <= x) * (x <= b)) (x \in `[a, b]).
Proof. by move=> x a b; apply: (iffP andP); case. Qed.

Lemma intcoP : forall x a b, reflect ((a <= x) * (x < b)) (x \in `[a, b[).
Proof. by move=> x a b; apply: (iffP andP); case. Qed.

Lemma intocP : forall x a b, reflect ((a < x) * (x <= b)) (x \in `]a, b]).
Proof. by move=> x a b; apply: (iffP andP); case. Qed.

Lemma intooP : forall x a b, reflect ((a < x) * (x < b)) (x \in `]a, b[).
Proof. by move=> x a b; apply: (iffP andP); case. Qed.

Lemma inticP : forall x b, reflect (x <= b) (x \in `]-oo, b]).
Proof. by move=> x b; apply: (iffP idP). Qed.

Lemma intioP : forall x b, reflect (x < b) (x \in `]-oo, b[).
Proof. by move=> x b; apply: (iffP idP). Qed.

Lemma intciP : forall x a, reflect (a <= x) (x \in `[a, +oo[).
Proof. by move=> x a; apply: (iffP idP). Qed.

Lemma intoiP : forall x a, reflect (a < x) (x \in `]a, +oo[).
Proof. by move=> x a; apply: (iffP idP). Qed.

Implicit Arguments intccP [x a b].
Implicit Arguments intcoP [x a b].
Implicit Arguments intocP [x a b].
Implicit Arguments intooP [x a b].
Implicit Arguments inticP [x b].
Implicit Arguments intioP [x b].
Implicit Arguments intciP [x a].
Implicit Arguments intoiP [x a].

Lemma intcc_rr : forall x, `[x, x] =i pred1 x.
Proof. by move=> x y; rewrite !inE -eqr_le eq_sym. Qed.

Lemma intoc_rr : forall x, `[x, x[ =i pred0.
Proof. by move=> x y; rewrite !inE ler_lt_asym. Qed.

Lemma intco_rr : forall x, `]x, x] =i pred0.
Proof. by move=> x y; rewrite !inE ltr_le_asym. Qed.

Lemma intoo_rr : forall x, `]x, x[ =i pred0.
Proof. by move=> x y; rewrite !inE ltr_asym. Qed.

Lemma intcc_gt : forall a b : R, b < a -> `[a, b] =i pred0.
Proof.
move=> a b hba x; rewrite !inE; apply/negP; case/andP=> hax hxb.
by move:(ltr_le_trans hba hax); move/(ler_lt_trans hxb); rewrite ltrr.
Qed.

Lemma intoc_ge : forall a b : R, b <= a -> `]a, b] =i pred0.
Proof.
move=> a b hba x; rewrite !inE; apply/negP; case/andP=> hax hxb.
by move:(ler_lt_trans hba hax); move/(ler_lt_trans hxb); rewrite ltrr.
Qed.

Lemma intco_ge : forall a b : R, b <= a -> `[a, b[ =i pred0.
Proof.
move=> a b hba x; rewrite !inE; apply/negP; case/andP=> hax hxb.
by move:(ler_trans hba hax); move/(ltr_le_trans hxb); rewrite ltrr.
Qed.

Lemma intoo_ge : forall a b : R, b <= a -> `]a, b[ =i pred0.
Proof.
move=> a b hba x; rewrite !inE; apply/negP; case/andP=> hax hxb.
by move:(ler_lt_trans hba hax); move/(ltr_trans hxb); rewrite ltrr.
Qed.

Lemma intoc_cc : forall a b : R, {subset `]a, b] <= `[a, b]}.
Proof. by move=> a b x; case/intocP; rewrite !inE; move/ltrW=> ->. Qed.

Lemma intco_cc : forall a b : R, {subset `[a, b[ <= `[a, b]}.
Proof. by move=> a b x; case/intcoP; rewrite !inE=> ->; move/ltrW. Qed.

Lemma intoo_co : forall a b : R, {subset `]a, b[ <= `[a, b[}.
Proof. by move=> a b x; case/intooP; rewrite !inE; move/ltrW=> ->. Qed.

Lemma intoo_oc : forall a b : R, {subset `]a, b[ <= `]a, b]}.
Proof. by move=> a b x; case/intooP; rewrite !inE=> ->; move/ltrW. Qed.

Lemma intoo_cc : forall a b : R, {subset `]a, b[ <= `[a, b]}.
Proof. by move=> a b x; move/intoo_co; move/intco_cc. Qed.

Lemma intcc_ic : forall a b : R, {subset `[a, b] <= `]-oo, b]}.
Proof. by move=> a b x; case/intccP. Qed.

Lemma intcc_ci : forall a b : R, {subset `[a, b] <= `[a, +oo[}.
Proof. by move=> a b x; case/intccP. Qed.

Lemma intco_io : forall a b : R, {subset `[a, b[ <= `]-oo, b[}.
Proof. by move=> a b x; case/intcoP. Qed.

Lemma intoc_oi : forall a b : R, {subset `]a, b] <= `]a, +oo[}.
Proof. by move=> a b x; case/intocP. Qed.

Lemma intoi_ci : forall a : R, {subset `]a, +oo[ <= `[a, +oo[}.
Proof. by move=> a x; rewrite !inE; move/ltrW. Qed.

Lemma intio_ic : forall b : R, {subset `]-oo, b[ <= `]-oo, b]}.
Proof. by move=> b x; rewrite !inE; move/ltrW. Qed.

Lemma intcc_cc : forall (a b a' b' : R), a' <= a -> b <= b' 
  -> {subset `[a, b] <= `[a', b']}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ler_trans ha) ?(ler_trans _ hb) ?(intccP hx).
Qed.

Lemma intco_co : forall (a b a' b' : R), a' <= a -> b <= b' 
  -> {subset `[a, b[ <= `[a', b'[}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ler_trans ha) ?(ltr_le_trans _ hb) ?(intcoP hx).
Qed.

Lemma intoc_oc : forall (a b a' b' : R), a' <= a -> b <= b' 
  -> {subset `]a, b] <= `]a', b']}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ler_lt_trans ha) ?(ler_trans _ hb) ?(intocP hx).
Qed.

Lemma intoo_oo : forall (a b a' b' : R), a' <= a -> b <= b' 
  -> {subset `]a, b[ <= `]a', b'[}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ler_lt_trans ha) ?(ltr_le_trans _ hb) ?(intooP hx).
Qed.

Lemma intcc_oc : forall (a b a' b' : R), a' < a -> b <= b' 
  -> {subset `[a, b] <= `]a', b']}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ltr_le_trans ha) ?(ler_trans _ hb) ?(intccP hx).
Qed.

Lemma intco_oo : forall (a b a' b' : R), a' < a -> b <= b' 
  -> {subset `[a, b[ <= `]a', b'[}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ltr_le_trans ha) ?(ltr_le_trans _ hb) ?(intcoP hx).
Qed.

Lemma intcc_co : forall (a b a' b' : R), a' <= a -> b < b' 
  -> {subset `[a, b] <= `[a', b'[}.
Proof.
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ler_trans ha) ?(ler_lt_trans _ hb) ?(intccP hx).
Qed.

Lemma intoc_oo : forall (a b a' b' : R), a' <= a -> b < b' 
  -> {subset `]a, b] <= `]a', b'[}.
Proof. 
move=> a b a' b' ha hb x hx; rewrite !inE.
by rewrite (ler_lt_trans ha) ?(ler_lt_trans _ hb) ?(intocP hx).
Qed.

Lemma intci_ci : forall (a a' : R), a' <= a
  -> {subset `[a, +oo[ <= `[a', +oo[}.
Proof. by move=> a a' ha x; rewrite !inE; move/(ler_trans _); apply. Qed.

Lemma intic_ic : forall (b b' : R), b <= b' 
  -> {subset `]-oo, b] <= `]-oo, b']}.
Proof. by move=> a a' ha x; rewrite !inE; move/ler_trans; apply. Qed.

Lemma intoi_oi : forall (a a' : R), a' <= a
  -> {subset `]a, +oo[ <= `]a', +oo[}.
Proof. by move=> a a' ha x; rewrite !inE; move/(ler_lt_trans _); apply. Qed.

Lemma intio_io : forall (b b' : R), b <= b' 
  -> {subset `]-oo, b[ <= `]-oo, b'[}.
Proof. by move=> a a' ha x; rewrite !inE; move/ltr_le_trans; apply. Qed.

Lemma intci_oi : forall (a a' : R), a' < a
  -> {subset `[a, +oo[ <= `]a', +oo[}.
Proof. by move=> a a' ha x; rewrite !inE; move/(ltr_le_trans _); apply. Qed.

Lemma intic_io : forall (b b' : R), b < b' 
  -> {subset `]-oo, b] <= `]-oo, b'[}.
Proof. by move=> a a' ha x; rewrite !inE; move/ler_lt_trans; apply. Qed.

End Interval.

End IntegralDomainTheory.
End IntegralDomainTheory.

Module Field.

Include IntegralDomainTheory.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : ring_mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.Field.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @IntegralDomain.Pack (fieldType cT) (class cT) cT.

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
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion poIdomainType : type >-> IntegralDomain.type.
Canonical Structure poIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical Structure fieldType.

End Exports.

End Field.
Import Field.Exports.

(* Module FieldTheory. *)
(* Section FieldTheory. *)

(* Variable F : Field.type. *)
(* Implicit Types x y z t : F. *)

(* End FieldTheory. *)
(* End FieldTheory. *)

End PartialOrder.

Module TotalOrder.

Import PartialOrder.OrderDef.

Definition mixin_of (R : PartialOrder.IntegralDomain.type) :=
  total (@ler R).

Local Notation oidom_mixin_of T b := 
  (mixin_of (@PartialOrder.IntegralDomain.Pack T b T)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later 
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_oidom : forall T, base_of T -> PartialOrder.IntegralDomain.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, oidom_mixin_of T (to_oidom b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T b0 (m0 : oidom_mixin_of T b0) :=
  fun bT b & phant_id (base_class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_oidom base_sort].

Import PartialOrder.IntegralDomain.Exports.

Module IntegralDomain.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : PartialOrder.IntegralDomain.class_of R;
  mixin : mixin_of (PartialOrder.IntegralDomain.Pack base R)
}.
Local Coercion base : class_of >-> PartialOrder.IntegralDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class PartialOrder.IntegralDomain.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poidomainType cT := PartialOrder.IntegralDomain.Pack (class cT) cT.
Definition join_idomainType cT :=
  @GRing.IntegralDomain.Pack (poidomainType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PartialOrder.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion poidomainType : type >-> PartialOrder.IntegralDomain.type.
Canonical Structure poidomainType.
End Exports.

End IntegralDomain.
Import PartialOrder.IntegralDomain.Exports.
Import PartialOrder.Field.Exports.
Import IntegralDomain.Exports.

Module IntegralDomainTheory.

Import PartialOrder.IntegralDomainTheory.

Section IntegralDomainTheory.

Hint Resolve lerr.

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

Lemma ler_total : total (@ler R). Proof. by case: R => T []. Qed.

Lemma ltrNge : forall x y, (x < y) = ~~ (y <= x).
Proof.
have aux: forall x y, x <= y -> (y < x) = false.
  move=> x y lxy.
  by rewrite -(ltr_asym x y) !ltr_neqAle lxy andbT eq_sym andbA andbb.
move=> x y; case/orP: (ler_total x y)=> hxy; rewrite ?hxy /=.
  by rewrite ler_eqVlt [y < x]aux // orbF ltr_neqAle hxy andbT eq_sym.
by apply/negP; rewrite aux.
Qed.

Lemma lerNgt : forall x y, (x <= y) = ~~ (y < x).
Proof. by move=> *; rewrite ltrNge negbK. Qed.

CoInductive le_xor_gtr (x y : R) : bool -> bool -> Set :=
  | LeNotGtr of x <= y : le_xor_gtr x y true false
  | GtrNotLe of y < x  : le_xor_gtr x y false true.

Lemma lerP : forall x y, le_xor_gtr x y (x <= y) (y < x).
Proof.
move=> x y; rewrite ltrNge.
by case hy: (_ <= _); constructor; rewrite // ltrNge hy.
Qed.

CoInductive ltr_xor_geq (x y : R) : bool -> bool -> Set :=
  | LtrNotGeq of x < y  : ltr_xor_geq x y false true
  | GeqNotLtr of y <= x : ltr_xor_geq x y true false.

Lemma ltrP : forall x y, ltr_xor_geq x y (y <= x) (x < y).
Proof. by move=> x y; case: (lerP y x); constructor. Qed.

CoInductive cparer x y : bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CparerLt of x < y : cparer x y false false true false true false
  | CparerGt of x > y : cparer x y false false false true false true
  | CparerEq of x = y : cparer x y true true true true false false.

Lemma ltrgtP : forall x y, cparer x y (y == x) (x == y) 
  (x <= y) (y <= x) (x < y) (x > y) .
Proof.
move=> x y; case exy: (_ == _); rewrite ?exy eq_sym exy.
  by rewrite (eqP exy) !lterr; constructor.
case: ltrP=> hxy; first by rewrite ltrNge ltrW //; constructor.
by move: hxy; rewrite ler_eqVlt exy /= lerNgt => hxy; rewrite hxy; constructor.
Qed.

Lemma neq_ltr : forall x y, (x != y) = (x < y) || (y < x).
Proof. by move=> *; rewrite eqr_le negb_and orbC !ltrNge. Qed.

Lemma ler01 : 0 <= 1 :> R.
Proof. 
by case/orP:(ler_total 0 1)=> // ler10; rewrite -[1]mulr1 mulr_le0.
 Qed.

Lemma ltr01 : 0 < 1 :> R.
Proof. by rewrite -ler_lt ?ler01 // eq_sym oner_eq0. Qed.

Definition lter01 := (ler01, ltr01).

Lemma ltr0Sn : forall n, 0 < (n.+1)%:~R :> R.
Proof.
elim=> [|n ihn]; first by rewrite ltr01.
by rewrite (ltr_le_trans ihn) // [n.+2%:Z]zintS mulrz_addl cpr_add ler01.
Qed.

Lemma ler0n : forall n : nat, 0 <= n%:~R :> R.
Proof. by move=> [|n]; rewrite ?mulr0z ?lerr // ltrW // ltr0Sn. Qed.

Lemma mulSn1r_eq0 : forall n, n.+1%:~R == 0 :> R = false.
Proof. by move=> n; rewrite eq_sym ltrE ?ltr0Sn. Qed.

Lemma ltr0n : forall n : nat, (0 < n%:~R :> R) = (n%:~R != 0 :> R).
Proof. by case=> *; rewrite ?(mulr0z, ltrr, eqxx, ltr0Sn, mulSn1r_eq0). Qed.

Definition lter0n := (ltr0Sn, ler0n, mulSn1r_eq0, ltr0n).

Lemma charor : [char R] =i pred0.
Proof. by case=> // p; rewrite !inE mulSn1r_eq0 andbF. Qed.

Lemma mul1rz_eq0 : forall n, (n%:~R == 0 :> R) = (n == 0).
Proof. 
by elim=> [|n _|n _]; rewrite ?mulr0z ?eqxx// ?mulrNz ?oppr_eq0 mulSn1r_eq0.
Qed.

Lemma mul1rzI : injective ( *~%R (1 : R)).
Proof.
move=> m n; move/eqP; rewrite -subr_eq0 -mulrz_subr.
by rewrite mul1rz_eq0 subr_eq0; move/eqP.
Qed.

Lemma mulrz_eq0 : forall x n, x *~ n == 0 = ((x == 0) || (n == 0)).
Proof. by move=> x n; rewrite -mulrzr mulf_eq0 mul1rz_eq0. Qed.

Lemma mulrz_neq0 : forall x n, x *~ n != 0 = ((x != 0) && (n != 0)).
Proof. by move=> x n; rewrite mulrz_eq0 negb_or. Qed.

Lemma ler_nat : forall m n : nat, (m%:R <= n%:R :> R) = (m <= n)%N.
Proof.
move=> m n; case: leqP => [lemn | gtnm].
  by rewrite -subr_ge0 -natr_sub ?ler0n.
by rewrite lerNgt -(subnKC gtnm) addSnnS natr_add ltr_addr ltr0Sn.
Qed.

Lemma ltr_nat : forall m n : nat, (m%:R < n%:R :> R) = (m < n)%N.
Proof. by move=> m n; rewrite ltrNge ltnNge ler_nat. Qed.

Lemma natr_gt0 : forall n : nat, (0 < n%:R :> R) = (0 < n)%N.
Proof. exact: (ltr_nat 0). Qed.

Section FinGroup.

Import GroupScope.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma natrG_gt0 : forall G, #|G|%:R > 0 :> R.
Proof. by move=> G; rewrite natr_gt0 cardG_gt0. Qed.

Lemma natrG_neq0 : forall G, #|G|%:R != 0 :> R.
Proof. by move=> G; rewrite -ltr0n natrG_gt0. Qed.

Lemma natr_indexg_gt0 : forall G H, #|G : H|%:R > 0 :> R.
Proof. by move=> G H; rewrite natr_gt0 indexg_gt0. Qed.

Lemma natr_indexg_neq0 : forall G H, #|G : H|%:R != 0 :> R.
Proof. by move=> G H; rewrite -ltr0n natr_indexg_gt0. Qed.

End FinGroup.

(* sgr section *)

Lemma sgr_cp0 : forall x,
  ((sgr x == 1) = (0 < x)) *
  ((sgr x == -1) = (x < 0)) *
  ((sgr x == 0) = (x == 0)).
Proof.
by move=> x; rewrite /sgr; case: ltrgtP=> // hx;
(* only for ssr <= 1.2 *)
rewrite ?hx ?(ltrWN hx) ?(ltrNW hx) ?eqxx.
Qed.

Lemma gtr0_sg : forall x, 0 < x -> sgr x = 1.
Proof. by move=> x hx; apply/eqP; rewrite sgr_cp0. Qed.

Lemma ltr0_sg : forall x, x < 0 -> sgr x = -1.
Proof. by move=> x hx; apply/eqP; rewrite sgr_cp0. Qed.

Lemma sgr0 : sgr (0 : R) = 0. Proof. by rewrite /sgr eqxx. Qed.

Lemma sgr1 : sgr (1 : R) = 1. Proof. by rewrite /sgr oner_eq0 ler01. Qed.

CoInductive sgr_val x : bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> zint -> Set :=
  | SgrNull of x = 0 : sgr_val x true true true true false false 
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x false false true false false true 
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x false true false false true false
    false true false false true false (-1).

Lemma sgrP : forall x,
  sgr_val x (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x) 
  (0 == sgr x) (-1 == sgr x) (1 == sgr x)
  (sgr x == 0)  (sgr x == -1) (sgr x == 1) (sgr x).
Proof.
move=> x; case: (ltrgtP x 0)=> hx; move: (hx); rewrite -?sgr_cp0.
* by move/eqP=> hsx; rewrite ?ler_eqVlt -?sgr_cp0 ?hsx ?(ltrNW hx); constructor.
* by move/eqP=> hsx; rewrite ?ler_eqVlt -?sgr_cp0 ?hsx ?(ltrWN hx); constructor.
* by move=> _; rewrite ?hx ?sgr0 ?eqxx ?lerr; constructor.
(* for ssreflect > 1.2, replace by this : *)
(* move=> x; case: (ltrgtP x 0)=> hx; move: (hx); rewrite -?sgr_cp0; *)
(*   do ?[by move/eqP=> hsgr; rewrite hsgr; constructor]. *)
(* by move->; rewrite sgr0; constructor; rewrite // sgr0. *)
Qed.

Lemma sgr_opp : forall x, sgr (-x) = -sgr x.
Proof.
move=> x; case (ltrgtP x 0)=> hx; last by rewrite hx !(oppr0, sgr0).
  by rewrite gtr0_sg ?oppr_cp0// ltr0_sg// opprK.
by rewrite ltr0_sg ?oppr_cp0// gtr0_sg.
Qed.

Lemma sgrN1 : sgr (-1 : R) = -1. Proof. by rewrite sgr_opp sgr1. Qed.

Lemma mulss : forall x, sgr x * sgr x = (x != 0)%:~R.
Proof. by move=> x; rewrite -sgr_cp0; case: sgrP. Qed.

Lemma muls_eqA : forall x y z, sgr x != 0 ->
  (sgr y * sgr z == sgr x) = ((sgr y * sgr x == sgr z) && (sgr z != 0)).
Proof. by move=> x y z; do 3!case: sgrP=> _. Qed.

Lemma sgr_mul : forall x y, sgr (x * y) = sgr x  * sgr y.
Proof. 
move=> x y; case: (sgrP x)=> hx; first by rewrite hx !mul0r sgr0.
  case: (sgrP y)=> hy; first by rewrite hy mulr0 sgr0.
    by apply/eqP; rewrite mul1r sgr_cp0 mulr_gt0.
  by apply/eqP; rewrite mul1r sgr_cp0 mulr_gt0_lt0.
case: (sgrP y)=> hy; first by rewrite hy mulr0 sgr0.
  by apply/eqP; rewrite mulr1 sgr_cp0 mulr_lt0_gt0.
by apply/eqP; rewrite mulN1r opprK sgr_cp0 mulr_lt0.
Qed. 

Lemma sgr_exp : forall n x, sgr (x ^+ n) = (sgr x) ^+ n.
Proof. by elim=> [|n ihn] x; rewrite ?sgr1 // !exprS sgr_mul ihn. Qed.

Lemma sgr_eq0 : forall x, (sgr x == 0) = (x == 0).
Proof. by move=> x; case: sgrP. Qed.

Lemma mul_neq0ss : forall x, x != 0 -> sgr x * sgr x = 1.
Proof. by move=> x hx; rewrite mulss hx. Qed.

Lemma sgr_odd : forall n x, x != 0 -> (sgr x) ^+ n = (sgr x) ^+ (odd n).
Proof. by move=> n x; case: sgrP=> //=; rewrite ?exp1rn // signr_odd. Qed.

(* smul section *)

Lemma sgr_smul : forall x y, sgr (x *~ (sgr y)) = (sgr x) * (sgr y).
Proof.
move=> x y; case: (sgrP y); rewrite ?(mulr0z, mulr0, sgr0, mulr1z, mulr1) //.
by rewrite sgr_opp mulrN mulr1.
Qed.

Lemma smul_exp : forall x y n,
  (x *~ sgr y) ^+ n.+1 = (x ^+ n.+1) *~ (sgr y ^+ n.+1).
Proof.
move=> s x n; case: (sgrP x); first by rewrite ![0 ^+ _.+1]exprS !mul0r.
  by rewrite exp1rn.
rewrite [_ ^+ _]exprN -![(-1) ^+ n.+1]signr_odd.
by case: (odd n.+1); rewrite !(expr0, expr1) !(mulNr, mul1r).
Qed.

(* absr section *)

Lemma absr_dec : forall x, `|x| = x *~ sgr x.
Proof.
rewrite /absr=> x; case: lerP; last by move/ltr0_sg->; rewrite mulrN1z.
rewrite ler_eqVlt; case/orP; first by move/eqP<-; rewrite sgr0.
by move/gtr0_sg->.
Qed.

Lemma absr0 : `|0 : R| = 0 :> R.
Proof. by rewrite /absr lerr. Qed.

Lemma absr_opp : forall x, `| -x | = `|x|.
Proof. by move=> x; rewrite !absr_dec sgr_opp mulNrNz. Qed.

Lemma ger0_abs : forall x, (0 <= x) -> `|x| = x.
Proof. by rewrite /absr=> x ->. Qed.

Definition gtr0_abs x (hx : 0 < x) := ger0_abs (ltrW hx).

Lemma ler0_abs : forall x, (x <= 0) -> `|x| = -x.
Proof.
move=> x hx; rewrite -{1}[x]opprK absr_opp //.
by apply:ger0_abs; rewrite oppr_cp0.
Qed.

Definition ltr0_abs x (hx : x < 0) := ler0_abs (ltrW hx).

CoInductive absr_val x : R -> bool -> bool -> bool 
  -> bool -> bool -> bool -> R -> Set :=
  | AbsNull of x = 0 : absr_val x 0 true true true true false false 0
  | AbsrPos of x > 0 : 
    absr_val x x false false false true false true x
  | AbsrNeg of x < 0 : 
    absr_val x x false false true false true false (-x).

Lemma absrP : forall x, absr_val x 
  x (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (0 < x) `|x|.
Proof.
move=> x; case: ltrgtP=> hx.
* by rewrite gtr0_abs //; constructor; rewrite // gtr0_abs.
* by rewrite ltr0_abs //; constructor; rewrite // ltr0_abs.
* by rewrite -hx absr0; constructor; rewrite // absr0.
Qed.

Lemma absr_idVN : forall x, (`|x| = x) \/ (`|x| = -x).
Proof. by move=> x; rewrite /absr; case: ltrgtP=> _; [right|left|left]. Qed.

Lemma absr_ge0 : forall x, 0 <= `|x|.
Proof. by move=> x; case: absrP=> //; rewrite ?oppr_cp0; move/ltrW. Qed.
Hint Resolve absr_ge0.

Lemma absr_sgP : forall x, x = `|x| *~ (sgr x).
Proof. by move=> x; rewrite absr_dec -mulrzA mulss; case: ltrgtP. Qed.

Lemma absr_eq0 : forall x, (`|x| == 0) = (x == 0).
Proof. by rewrite /absr=> x; case: lerP; rewrite ?oppr_eq0. Qed.

Lemma absr_lt0 : forall x, `|x| < 0 = false.
Proof. by move=> x; apply: negbTE; rewrite -lerNgt. Qed.

Lemma absr_le0 : forall x, (`|x| <= 0) = (x == 0).
Proof.
by move=> x; case: absrP; rewrite ?lerr ?oppr_cp0 // ?ltrNge; move/negPf.
Qed.

Lemma absr_gt0 : forall x, (`|x| > 0) = (x != 0).
Proof. by move=> x; rewrite ltrNge absr_le0. Qed.

Lemma absr1 : `|1| = 1 :> R.
Proof. by rewrite ger0_abs// ler01. Qed.

Lemma absr_id : forall x, `| `|x| | = `|x|.
Proof. by move=> x; rewrite ger0_abs // absr_ge0. Qed.

Definition absrE x := (absr_id, absr0, absr1, absr_ge0, absr_eq0, 
  absr_lt0, absr_le0, absr_gt0).

Lemma absr_subC : forall x y, `|x - y| = `|y - x|.
Proof. by move=> x y; rewrite -oppr_sub absr_opp. Qed.

Lemma absr_mul : forall x y, `|x * y| = `|x| * `|y|.
Proof. by move=> x y; rewrite !absr_dec sgr_mul mulrzAr mulrzAl mulrzA. Qed.

Lemma absr_exp : forall n x, `|x ^+ n| = `|x| ^+ n.
Proof. by elim=> [|n ihn] x; rewrite ?absr1 // !exprS absr_mul ihn. Qed.

(* Todo : rename *r_*_le in ler_*_* *)
Lemma absr_add_le : forall x y, `| x + y | <= `|x| + `|y|.
Proof.
move=> x; wlog : x / (x > 0)=> [hxp | xp] y.
  case: (ltrgtP x 0)=> [xn|xp|->]; last 2 first; do ?exact: hxp.
    by rewrite absr0 !add0r lterr.
  by rewrite -absr_opp oppr_add (ler_trans (hxp _ _ _)) ?absr_opp ?oppr_cp0.
case: (ltrgtP y 0)=> hy; last by rewrite hy absr0 !addr0.
  rewrite (@ger0_abs x) ?(ltrW xp) // (@ler0_abs y) ?(ltrW hy) //.
  by case: (lerP 0 (x + y))=> lnyx; [rewrite ger0_abs | rewrite ler0_abs];
    rewrite // ?ltrW // ?oppr_add lter_add2 ?(lt0_cp, gt0_cp).
by rewrite !ger0_abs // ?ltrW // addr_gt0.
Qed.

Lemma absr_sum_le : forall I r (G : I -> R),
  `|\sum_(i <- r) G i| <= \sum_(i <- r) `|G i|.
Proof.
move=> I; elim=> [|a r ihr] //= G; first by rewrite !big_nil absr0 lerr.
by rewrite !big_cons /= (ler_trans (absr_add_le _ _)) //= ler_add2r /= ihr.
Qed.

Lemma absr_sub_le : forall x y, `| x - y | <= `|x| + `|y|.
Proof. by move=> x y; rewrite (ler_trans (absr_add_le _ _)) ?absr_opp. Qed.

Lemma subr_abs_le : forall x y, `|x| - `|y| <= `| x + y |.
Proof.
move=> x y; rewrite -{1}[x](addrK y).
by rewrite (ler_addl_transl (absr_sub_le _ _)) // addrK.
Qed.

Lemma subr_abs_le_sub : forall x y, `|x| - `|y| <= `| x - y |.
Proof. by move=> x y; rewrite -[`|y|]absr_opp subr_abs_le. Qed.

Lemma absr_le_mem : forall x y, (`|x| <= y) = (x \in `[-y, y]).
Proof.
move=> x y; case: absrP=> hx; first by rewrite ?hx mem0_intcc_xNx.
  rewrite !inE; case: lerP=> hxy; rewrite andbC //=.
  by symmetry; rewrite ler_oppl (@ler_trans _ x) // ge0_cp // ltrW.
rewrite !inE; case: (lerP x y)=> hxy; rewrite andbC; first by rewrite ler_oppl.
by apply: negbTE; rewrite -ltrNge (@ler_lt_trans _ x) ?lt0_cp // ltrW.
Qed.

Lemma absr_le : forall x y, reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof.
by move=> x y; rewrite absr_le_mem !inE ler_oppl; apply: (iffP (intccP _ _ _)).
Qed.

Implicit Arguments absr_le [x y].

Lemma absr_ge0_eq : forall x y, 0 <= y -> (`|x| == y) = (x == y) || (x == -y).
Proof.
move=> x y hy; case: absrP=> hx; rewrite ?hx ?[0 == _]eq_sym ?oppr_eq0 ?orbb //.
  case: ltrgtP=> //= hxy;
    (* specific to ssr <= 1.2 *)
    rewrite ?(ltrNW hxy) ?(ltrWN hxy) ?hxy ?eqxx //;
    (* resume here *)
    symmetry; apply/negP; move/eqP=> exNy.
    by move: hxy; rewrite -[y]opprK -exNy ltrNge ge0_cp // ltrW.
  by move: hxy; rewrite exNy ltrNge ge0_cp.
rewrite eqr_oppC; case: (ltrgtP x y)=> //= hxy; rewrite hxy in hx.
by suff: false by []; rewrite -(ler_lt_asym 0 y) hx hy.
Qed.

Lemma absr_eq : forall x y, (`|x| == `|y|) = (x == y) || (x == -y).
Proof.
by move=> x y; rewrite absr_ge0_eq //; case: absrP=> hy; rewrite ?hy // opprK orbC.
Qed.

Lemma absr_lt_mem : forall x y, (`|x| < y) = (x \in `](-y), y[).
Proof.
move=> x y; case: (lerP 0 y)=> hy.
  rewrite !inE !ltr_neqAle absr_le_mem // !inE absr_ge0_eq // negb_or.
  by rewrite !andbA [-_ == _]eq_sym; congr andb; rewrite -andbA andbC.
rewrite intoo_ge ?lt0_cp // !inE; apply/negP=> hxy.
by move:(ltr_trans hxy hy); rewrite absrE.
Qed.

Definition absr_lte_mem := (absr_le_mem, absr_lt_mem).

Lemma absr_lt : forall x y, reflect ((-x < y) * (x < y)) (`|x| < y).
Proof.
by move=> x y; rewrite absr_lt_mem !inE ltr_oppl; apply: (iffP (intooP _ _ _)).
Qed.

Implicit Arguments absr_lt [x y].

Lemma absr_le_lt0: forall x y, y < 0 -> (`|x| <= y = false).
Proof. by move=> x y hy; rewrite absr_le_mem intcc_gt ?lt0_cp. Qed.

Lemma absr_lt_le0: forall x y, y <= 0 -> (`|x| < y = false).
Proof. by move=> x y hy; rewrite absr_lt_mem intoo_ge ?le0_cp. Qed.

Lemma distr_intcc : forall x y e, (`|x - y| <= e) = (x \in `[y - e, y + e]).
Proof.
by move=> x y e; rewrite absr_lte_mem !inE lter_subl_addr lter_subr_addr.
Qed. 

Lemma distr_intoo : forall x y e, (`|x - y| < e) = (x \in `]y - e, (y + e)[).
Proof.
by move=> x y e; rewrite absr_lte_mem // !inE lter_subl_addr lter_subr_addr.
Qed.

Definition distr_int := (distr_intcc, distr_intoo).

Lemma absr_abs_le : forall x y, `| `|x| - `|y| | <= `| x + y |.
Proof.
by move=> x y; apply/absr_le; rewrite oppr_sub {1}[_ + y]addrC !subr_abs_le.
Qed.

Lemma absr_smul : forall x y, y != 0 -> `|x *~ sgr y| = `|x|.
Proof. by move=> x y; case: sgrP; rewrite // mulrN1z absr_opp. Qed.

Lemma absr_eqr : forall x, (`|x| == x) = (0 <= x).
Proof.
move=> x; case: absrP=> hx; rewrite ?hx ?eqxx //; move/ltrWN: hx=> hx.
by rewrite eq_sym -subr_eq0 opprK (mulrz_eq0 _ 2) hx.
Qed.

Lemma absr_eqNr : forall x, (`|x| == -x) = (x <= 0).
Proof. move=> x; rewrite -oppr_cp0 -absr_opp; exact: absr_eqr. Qed.

Definition absr_eqrVNr := (absr_eqr, absr_eqNr).

Lemma ler_pmul2r : forall x y z : R, 0 < x -> (x * y <= x * z) = (y <= z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ler_pmul2rW; rewrite ltrW.
by rewrite !lerNgt; apply: contra; apply: ltr_pmul2rW.
Qed.

Lemma ltr_pmul2r : forall x y z : R, 0 < x -> (x * y < x * z) = (y < z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ltr_pmul2rW.
by rewrite !ltrNge; apply: contra; apply: ler_pmul2rW; rewrite ltrW.
Qed.

Definition lter_pmul2r := (ler_pmul2r, ltr_pmul2r).

Lemma ler_pmul2l : forall x y z : R, 0 < x -> (y * x <= z * x) = (y <= z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ler_pmul2lW; rewrite ltrW.
by rewrite !lerNgt; apply: contra; apply: ltr_pmul2lW.
Qed.

Lemma ltr_pmul2l : forall x y z : R, 0 < x -> (y * x < z * x) = (y < z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ltr_pmul2lW.
by rewrite !ltrNge; apply: contra; apply: ler_pmul2lW; rewrite ltrW.
Qed.

Definition lter_pmul2l := (ler_pmul2l, ltr_pmul2l).

Lemma ler_nmul2r : forall x y z : R, x < 0 -> (x * z <= x * y) = (y <= z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ler_nmul2rW; rewrite ltrW.
by rewrite !lerNgt; apply: contra; apply: ltr_nmul2rW.
Qed.

Lemma ltr_nmul2r : forall x y z : R, x < 0 -> (x * z < x * y) = (y < z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ltr_nmul2rW.
by rewrite !ltrNge; apply: contra; apply: ler_nmul2rW; rewrite ltrW.
Qed.

Definition lter_nmul2r := (ler_nmul2r, ltr_nmul2r).

Lemma ler_nmul2l : forall x y z : R, x < 0 -> (z * x <= y * x) = (y <= z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ler_nmul2lW; rewrite ltrW.
by rewrite !lerNgt; apply: contra; apply: ltr_nmul2lW.
Qed.

Lemma ltr_nmul2l : forall x y z : R, x < 0 -> (z * x < y * x) = (y < z).
Proof.
move=> x y z hx; apply/idP/idP; last by apply: ltr_nmul2lW.
by rewrite !ltrNge; apply: contra; apply: ler_nmul2lW; rewrite ltrW.
Qed.

Definition lter_nmul2l := (ler_nmul2l, ltr_nmul2l).

Lemma ler_epmull : forall x y, 1 <= x -> 0 <= y -> y <= x * y.
Proof. by move=> x y hx hy; rewrite -{1}[y]mul1r ler_pmul2lW. Qed.

Lemma ltr_epmull : forall x y, 1 < x -> 0 < y -> y < x * y.
Proof. by move=> x y hx hy; rewrite -{1}[y]mul1r ltr_pmul2lW. Qed.

Definition lter_epmull := (ler_epmull, ltr_epmull).

Lemma ler_enmull : forall x y, 1 <= x -> y <= 0 -> x * y <= y.
Proof. by move=> x y hx hy; rewrite -{2}[y]mul1r ler_nmul2lW. Qed.

Lemma ltr_enmull : forall x y, 1 < x -> y < 0 -> x * y < y.
Proof. by move=> x y hx hy; rewrite -{2}[y]mul1r ltr_nmul2lW. Qed.

Definition lter_enmull := (ler_enmull, ltr_enmull).
Definition lter_emull := (lter_epmull, lter_enmull).

Lemma ler_epmulr : forall x y, 1 <= x -> 0 <= y -> y <= y * x.
Proof. by move=> x y hx hy; rewrite -{1}[y]mulr1 ler_pmul2rW. Qed.

Lemma ltr_epmulr : forall x y, 1 < x -> 0 < y -> y < y * x.
Proof. by move=> x y hx hy; rewrite -{1}[y]mulr1 ltr_pmul2rW. Qed.

Definition lter_epmulr := (ler_epmulr, ltr_epmulr).

Lemma ler_enmulr : forall x y, 1 <= x -> y <= 0 -> y * x <= y.
Proof. by move=> x y hx hy; rewrite -{2}[y]mulr1 ler_nmul2rW. Qed.

Lemma ltr_enmulr : forall x y, 1 < x -> y < 0 -> y * x < y.
Proof. by move=> x y hx hy; rewrite -{2}[y]mulr1 ltr_nmul2rW. Qed.

Definition lter_enmulr := (ler_enmulr, ltr_enmulr).
Definition lter_emulr := (lter_epmulr, lter_enmulr).

Lemma ler_ipmull : forall x y, x <= 1 -> 0 <= y -> x * y <= y.
Proof. by move=> x y hx hy; rewrite -{2}[y]mul1r ler_pmul2lW. Qed.

Lemma ltr_ipmull : forall x y, x < 1 -> 0 < y -> x * y < y.
Proof. by move=> x y hx hy; rewrite -{2}[y]mul1r ltr_pmul2lW. Qed.

Definition lter_ipmull := (ler_ipmull, ltr_ipmull).

Lemma ler_inmull : forall x y, x <= 1 -> y <= 0 -> y <= x * y.
Proof. 
move=> x y hx hy; rewrite -mulrNN -{1}[y]mul1r -mulrNN.
by rewrite ler_pmul2lW ?oppr_ge0 ?ler_opp2.
Qed.

Lemma ltr_inmull : forall x y, x < 1 -> y < 0 -> y < x * y.
Proof.
move=> x y hx hy; rewrite -mulrNN -{1}[y]mul1r -mulrNN.
by rewrite ltr_pmul2lW ?oppr_gt0 ?ltr_opp2.
Qed.

Definition lter_inmull := (ler_inmull, ltr_inmull).
Definition lter_imull := (lter_inmull, lter_ipmull).

Lemma ler_ipmulr : forall x y, x <= 1 -> 0 <= y -> y * x <= y.
Proof.
move=> x y hx hy; rewrite -mulrNN -{2}[y]mulr1 -[_ * 1]mulrNN.
by rewrite ler_nmul2rW ?oppr_le0 ?ler_opp2.
Qed.

Lemma ltr_ipmulr : forall x y, x < 1 -> 0 < y -> y * x < y.
Proof.
move=> x y hx hy; rewrite -mulrNN -{2}[y]mulr1 -[_ * 1]mulrNN.
by rewrite ltr_nmul2rW ?oppr_lt0 ?ltr_opp2.
Qed.

Definition lter_ipmulr := (ler_ipmulr, ltr_ipmulr).

Lemma ler_inmulr : forall x y, x <= 1 -> y <= 0 -> y <= y * x.
Proof. by move=> x y hx hy; rewrite -{1}[y]mulr1 ler_nmul2rW. Qed.

Lemma ltr_inmulr : forall x y, x < 1 -> y < 0 -> y < y * x.
Proof. by move=> x y hx hy; rewrite -{1}[y]mulr1 ltr_nmul2rW. Qed.

Definition lter_inmulr := (ler_inmulr, ltr_inmulr).
Definition lter_imulr := (lter_ipmulr, lter_inmulr).

Lemma exprn_ge0 : forall n x, (0 <= x) -> (0 <= x ^+ n).
Proof. by elim=> [|n ihn] x hx; rewrite ?ler01 // exprS mulr_ge0 ?ihn. Qed.

Lemma exprn_gt0 : forall n x, (0 < x) -> (0 < x ^+ n).
Proof. by elim=> [|n ihn] x hx; rewrite ?ltr01 // exprS mulr_gt0 ?ihn. Qed.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_even_ge0 : forall n x, ~~ odd n -> 0 <= x ^+ n.
Proof.
case=> [|n] x; rewrite ?ler01 //= negbK=> hx.
rewrite ler_eqVlt eq_sym expf_eq0 -sgr_cp0 sgr_exp /=.
by case x0: (x == 0)=> //=; rewrite sgr_odd ?x0 //= hx expr0.
Qed.

(* Lemma mulN1sr : forall (R' : PartialOrder.IntegralDomain.type) (x : R), *)
(*   sgr (-1 : R') *~ x = -x. *)

Lemma sqr_abs_eq1 : forall x, (x ^+ 2 == 1) = (`|x| == 1).
Proof. by move=> x; rewrite sqrf_eq1 -absr_eq absr1. Qed.

Lemma sqr_ge0_eq1 : forall x, 0 <= x -> (x ^+ 2 == 1) = (x == 1).
Proof. by move=> x hx; rewrite sqr_abs_eq1 ger0_abs. Qed.

Lemma mulr_le1 : forall x y, 0 <= x -> 0 <= y 
  -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> x y *; rewrite (@ler_trans _ y) ?ler_ipmull. Qed.

Lemma mulr_lt1 : forall x y, 0 <= x -> 0 <= y 
  -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> x y *; rewrite (@ler_lt_trans _ y) ?ler_ipmull // ltrW. Qed.

Lemma mulr_ge1 : forall x y, 1 <= x -> 1 <= y -> 1 <= x * y.
Proof. 
by move=> x y *; rewrite (@ler_trans _ y) ?ler_epmull // (ler_trans ler01).
Qed.

Lemma mulr_gt1 : forall x y, 1 < x -> 1 < y -> 1 < x * y.
Proof. 
by move=> x y *; rewrite (@ltr_trans _ y) ?ltr_epmull // (ltr_trans ltr01).
Qed.

Lemma exprn_ile1 : forall n x, `|x| <= 1 -> x ^+ n <= 1.
Proof.
move=> n x; wlog hx0: x / x >= 0=> [hpos|] hx1; last first.
  elim: n=> [|n ihn] //;  rewrite exprS (ler_trans _ ihn) //.
  by rewrite ?lter_imull ?exprn_ge0 // (absr_le _).
case: (lerP 0 x)=> hx; first exact: hpos.
rewrite -[x]opprK -mulN1r exprn_mull -signr_odd.
case hn: (odd n); last by rewrite mul1r hpos ?absr_opp ?oppr_ge0 ?(ltrW hx).
rewrite mulN1r (@ler_trans _ 0) ?ler01 ?oppr_le0 //.
by rewrite exprn_ge0 // oppr_ge0 ltrW.
Qed.
 
Lemma exprn_ilt1 : forall n x, `|x| < 1 -> x ^+ n.+1 < 1.
Proof.
move=> n x; wlog hx0: x / x >= 0=> [hpos|] hx1; last first.
  elim: n=> [|n ihn]; move: (hx1); rewrite ger0_abs // => hx.
  by rewrite exprS (ler_lt_trans _ ihn) ?lter_imull ?exprn_ge0 // ltrW.
case: (lerP 0 x)=> hx; first exact: hpos.
rewrite -[x]opprK -mulN1r exprn_mull -signr_odd /=.
case hn: (odd n); first by rewrite mul1r hpos ?absr_opp ?oppr_ge0 ?(ltrW hx).
by rewrite mulN1r (@ltr_le_trans _ 0) ?ler01 ?oppr_lt0 ?exprn_gt0 ?oppr_gt0.
Qed.

Definition exprn_ilte1:= (exprn_ile1, exprn_ilt1).

Lemma exprn_le1 : forall n x, 0 <= x -> (x ^+ n.+1 <= 1) = (x <= 1).
Proof.
move=> n x hx0; elim: n=> [|n ihn] //.
apply/idP/idP; last by move=> hx; rewrite exprn_ile1 // ger0_abs.
case: (lerP x 1)=> hx1 //; rewrite exprS; move/(ler_lt_trans); move/(_ _ hx1).
rewrite ?lerNgt ?hx1 ltrNge /=; move/negPf <-; rewrite ler_epmulr //.
by rewrite ltrW // ltrNge ihn -ltrNge.
Qed.

Lemma exprn_lt1 : forall n x, 0 <= x -> (x ^+ n.+1 < 1) = (x < 1).
Proof.
move=> n x hx0; elim: n=> [|n ihn] //.
apply/idP/idP; last by move=> hx; rewrite exprn_ilt1 // ger0_abs.
case: (ltrP x 1)=> hx1 //; rewrite exprS; move/ltr_le_trans; move/(_ _ hx1).
by rewrite !ltrNge ?hx1 /=; move/negPf<-; rewrite ler_epmulr // lerNgt ihn -lerNgt.
Qed.

Definition exprn_lte1 := (exprn_le1, exprn_lt1).

Lemma exprSn_ge0_eq1 : forall x n, 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. 
move=> x n hx; rewrite expfS_eq1; case: (x == 1)=> //=.
rewrite eq_sym ltrWN // (@ltr_le_trans _ 1) ?ltr01 //.
elim: n=> [|n ihn]; first by rewrite big_ord_recl big_ord0 addr0 lerr.
by rewrite big_ord_recr /= addrC ger0_ler_add // exprn_ge0.
Qed.

Lemma exprn_ege1 : forall n x, 1 <= x -> 1 <= x ^+ n.
Proof.
case=> [|n] x hx1 //; move: (ler_trans ler01 hx1)=> hx0.
by move: hx1; rewrite !lerNgt; apply: contra; rewrite exprn_lt1.
Qed.

Lemma exprn_egt1 : forall n x, 1 < x -> 1 < x ^+ n.+1.
Proof.
move=> n x hx1 //; move: (ltr_trans ltr01 hx1)=> hx0.
by move: hx1; rewrite !ltrNge; apply: contra; rewrite exprn_le1 // ltrW.
Qed.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).


Lemma exprn_ge1 : forall n x, 0 <= x -> (1 <= x ^+ n.+1) = (1 <= x).
Proof.
move=> n x hx0; apply/idP/idP; last exact: exprn_ege1.
by rewrite !lerNgt; apply: contra=> hx1; rewrite exprn_lt1.
Qed.

Lemma exprn_gt1 : forall n x, 0 <= x -> (1 < x ^+ n.+1) = (1 < x).
Proof.
move=> n x hx0; apply/idP/idP; last exact: exprn_egt1.
by rewrite !ltrNge; apply: contra=> hx1; rewrite exprn_le1.
Qed.

Lemma ler_iexprS : forall x n, 0 <= x -> x <= 1 -> x ^+ n.+1 <= x.
Proof.
by move=> x n hx0 hx1; rewrite exprS lter_imulr // exprn_ile1 // ger0_abs.
Qed.

Lemma ltr_iexprSS : forall x n, 0 < x -> x < 1 -> x ^+ n.+2 < x.
Proof.
by move=> x n hx0 hx1; rewrite exprS lter_imulr ?exprn_ilt1 ?ger0_abs // ltrW.
Qed.

Lemma ler_eexprS : forall x n, 1 <= x -> x <= x ^+ n.+1.
Proof.
move=> x n hx1; move: (ler_trans ler01 hx1)=> hx0. 
by rewrite exprS lter_emulr // exprn_ege1.
Qed.

Lemma ltr_eexprSS : forall x n, 1 < x -> x < x ^+ n.+2.
Proof.
move=> x n hx1; move: (ler_lt_trans ler01 hx1)=> hx0. 
by rewrite exprS lter_emulr // exprn_egt1.
Qed.

Lemma ler_iexpr2 : forall x m n, (n <= m)%N 
  -> 0 <= x -> x <= 1 -> x ^+ m <= x ^+ n.
Proof.
move=> x m n; move/subnK=> <- hx0 hx1; rewrite exprn_addr.
by rewrite lter_imull ?exprn_ge0 // exprn_ile1 // ger0_abs. 
Qed.

Lemma ltr_iexpr2 : forall x m n, (n < m)%N
 -> 0 < x -> x < 1 -> x ^+ m < x ^+ n.
Proof.
move=> x m n; move/subnKC=> <- hx0 hx1; rewrite addSn -addnS exprn_addr.
by rewrite lter_imulr ?exprn_gt0 ?exprn_ilt1 ?ger0_abs // ltrW.
Qed.

Lemma ler_eexpr2 : forall x m n, (m <= n)%N
  -> 1 <= x -> x ^+ m <= x ^+ n.
Proof.
move=> x m n; move/subnK=> <- hx1; rewrite exprn_addr.
by rewrite lter_emull ?exprn_ge0 ?exprn_ege1 // (ler_trans ler01).
Qed.

Lemma ltr_eexpr2 : forall x m n, (m < n)%N
  -> 1 < x -> x ^+ m < x ^+ n.
Proof.
move=> x m n; move/subnK=> <- hx1; rewrite addnS -addSn exprn_addr.
by rewrite lter_emull ?exprn_egt1 ?exprn_gt0 // (ltr_trans ltr01).
Qed.

Definition lter_iexpr2 := (ler_iexpr2, ltr_iexpr2).
Definition lter_eexpr2 := (ler_eexpr2, ltr_eexpr2).

Lemma ler_le_pexp2 : forall n x y,  0 <= x -> x <= y -> (x ^+ n.+1 <= y ^+ n.+1).
Proof.
move=> n x y; case: ltrgtP=> hx _ //; last first.
  by rewrite hx => hy; rewrite exprS mul0r exprn_ge0.
move=> hxy; elim: n => [|n ihn] //.
rewrite ![_ ^+ _.+2]exprS (@ler_trans _ (x * y ^+ n.+1)) //.
  by rewrite ler_pmul2r ?exprn_gt0.
by rewrite ler_pmul2l ?exprn_gt0 ?(ltr_le_trans hx).
Qed.

Lemma ltr_lt_pexp2 : forall n x y,  0 <= x -> x < y -> (x ^+ n.+1 < y ^+ n.+1).
Proof.
move=> n x y; rewrite ler_eqVlt; case/orP=> hx.
  by rewrite -(eqP hx) => hy; rewrite exprS mul0r exprn_gt0.
move=> hxy; elim: n => [|n ihn] //.
rewrite ![_ ^+ _.+2]exprS (@ltr_trans _ (x * y ^+ n.+1)) //.
  by rewrite ltr_pmul2r ?exprn_gt0.
by rewrite ltr_pmul2l ?exprn_gt0 ?(ltr_trans hx).
Qed.

Definition lter_lte_pexp2 := (ler_le_pexp2, ltr_lt_pexp2).

Lemma ler_pexp2 : forall n x y,  0 <= x -> 0 <= y 
  -> (x ^+ n.+1 <= y ^+ n.+1) = (x <= y).
Proof.
move=> n x y hx hy; apply/idP/idP; last by move=> hxy; rewrite lter_lte_pexp2.
by apply: contraLR; rewrite -!ltrNge => hxy; rewrite lter_lte_pexp2.
Qed.

Lemma ltr_pexp2 : forall n x y,  0 <= x -> 0 <= y 
  -> (x ^+ n.+1 < y ^+ n.+1) = (x < y).
Proof.
move=> n x y hx hy; apply/idP/idP; last by move=> hxy; rewrite lter_lte_pexp2.
by apply: contraLR; rewrite -!lerNgt => hxy; rewrite lter_lte_pexp2.
Qed.

Definition lter_pexp2 := (ler_pexp2, ltr_pexp2).

Lemma eqr_exp2 : forall n x y, 0 <= x -> 0 <= y -> 
  (x ^+ n.+1 == y ^+ n.+1) = (x == y).
Proof. by move=> *; rewrite !eqr_le !ler_pexp2. Qed.

Section MinMax.

Lemma minrC : commutative (@minr R).
Proof. by move=> x y; rewrite /minr; case: ltrgtP. Qed.

Lemma minrr : idempotent (@minr R).
Proof. by move=> x; rewrite /minr lerr. Qed.

Lemma minr_l : forall x y, x <= y -> minr x y = x.
Proof. by move=> x y; rewrite /minr => ->. Qed.

Lemma minr_r : forall x y, y <= x -> minr x y = y.
Proof. by move=> x y hyx; rewrite minrC minr_l. Qed.

Lemma maxrC : commutative (@maxr R).
Proof. by move=> x y; rewrite /maxr; case: ltrgtP. Qed.

Lemma maxrr : idempotent (@maxr R).
Proof. by move=> x; rewrite /maxr lerr. Qed.

Lemma maxr_l : forall x y, y <= x -> maxr x y = x.
Proof. by move=> x y hxy; rewrite /maxr hxy. Qed.

Lemma maxr_r : forall x y, x <= y -> maxr x y = y.
Proof. by move=> x y hxy; rewrite maxrC maxr_l. Qed.

Lemma addr_min_max : forall x y, minr x y + maxr x y = x + y.
Proof.
move=> x y; case: (lerP x y)=> hxy; first by rewrite maxr_r ?minr_l.
by rewrite maxr_l ?minr_r ?ltrW // addrC.
Qed.

Lemma addr_max_min : forall x y, maxr x y + minr x y = x + y.
Proof. by move=> x y; rewrite addrC addr_min_max. Qed.

Lemma minr_to_max : forall x y, minr x y = x + y - maxr x y.
Proof. by move=> x y; rewrite -[x + y]addr_min_max addrK. Qed.

Lemma maxr_to_min : forall x y, maxr x y = x + y - minr x y.
Proof. by move=> x y; rewrite -[x + y]addr_max_min addrK. Qed.

Lemma minrA : forall x y z, minr x (minr y z) = minr (minr x y) z.
Proof.
rewrite /minr => x y z; case: (lerP y z)=> hyz; last move/ltrW:hyz=> hyz.
  by case: lerP=> hxy; rewrite ?hyz // (@ler_trans _ y).
case: lerP=> hxz; first by rewrite !(ler_trans hxz).
case: (lerP x y)=> hxy; first by rewrite lerNgt hxz.
by case: ltrgtP hyz.
Qed.

Lemma minrCA : left_commutative (@minr R).
Proof. by move=> x y z; rewrite !minrA [minr x y]minrC. Qed.

Lemma minrAC :  right_commutative (@minr R).
Proof. by move=> x y z; rewrite -!minrA [minr y z]minrC. Qed.

CoInductive minr_spec (x y :R) : bool -> bool -> R -> Type :=
| Minr_r of x <= y : minr_spec x y true false x
| Minr_l of y < x : minr_spec x y false true y.

Lemma minrP : forall x y, minr_spec x y (x <= y) (y < x) (minr x y).
Proof.
move=> x y; case: lerP=> hxy; first by rewrite minr_l //; constructor.
by rewrite minr_r 1?ltrW //; constructor.
Qed.

Lemma oppr_max : forall x y, - (maxr x y) = minr (- x) (- y).
Proof. 
move=> x y; case: minrP; rewrite lter_opp2 => hxy; first by rewrite maxr_l.
by rewrite maxr_r // ltrW.
Qed.

Lemma oppr_min : forall x y, - (minr x y) = maxr (- x) (- y).
Proof. by move=> x y; rewrite -[maxr _ _]opprK oppr_max !opprK. Qed.

Lemma maxrA : forall x y z, maxr x (maxr y z) = maxr (maxr x y) z.
Proof. by move=> x y z; apply/eqP; rewrite -eqr_opp !oppr_max minrA. Qed.

Lemma maxrCA : left_commutative (@maxr R).
Proof. by move=> x y z; rewrite !maxrA [maxr x y]maxrC. Qed.

Lemma maxrAC :  right_commutative (@maxr R).
Proof. by move=> x y z; rewrite -!maxrA [maxr y z]maxrC. Qed.

CoInductive maxr_spec (x y :R) : bool -> bool -> R -> Type :=
| Maxr_r of y <= x : maxr_spec x y true false x
| Maxr_l of x < y : maxr_spec x y false true y.

Lemma maxrP : forall x y, maxr_spec x y (y <= x) (x < y) (maxr x y).
Proof.
move=> x y; case: lerP=> hxy; first by rewrite maxr_l //; constructor.
by rewrite maxr_r 1?ltrW //; constructor.
Qed.

Lemma eqr_minl : forall x y, (minr x y == x) = (x <= y).
Proof. by move=> x y; case: minrP=> hxy; rewrite ?eqxx // ltrWN. Qed.

Lemma eqr_minr : forall x y, (minr x y == y) = (y <= x).
Proof. by move=> x y; rewrite minrC eqr_minl. Qed.

Lemma eqr_maxl : forall x y, (maxr x y == x) = (y <= x).
Proof. by move=> x y; case: maxrP=> hxy; rewrite ?eqxx // eq_sym ltrWN. Qed.

Lemma eqr_maxr : forall x y, (maxr x y == y) = (x <= y).
Proof. by move=> x y; rewrite maxrC eqr_maxl. Qed.

Lemma ler_minr : forall x y z, (x <= minr y z) = (x <= y) && (x <= z).
Proof.
move=> x y z; case: minrP=> hyz.
  by case: lerP=> hxy //; rewrite (ler_trans _ hyz).
by case: lerP=> hxz; rewrite andbC // (ler_trans hxz) // ltrW.
Qed.

Lemma ler_minl : forall x y z, (minr y z <= x) = (y <= x) || (z <= x).
Proof.
move=> x y z; case minrP=> hyz.
  case: lerP=> hyx //=; symmetry; apply: negbTE.
  by rewrite -ltrNge (@ltr_le_trans _ y).
case: lerP=> hzx; rewrite orbC //=; symmetry; apply: negbTE.
by rewrite -ltrNge (@ltr_trans _ z).
Qed.

Lemma ler_maxr : forall x y z, (x <= maxr y z) = (x <= y) || (x <= z).
Proof. by move=> x y z; rewrite -lter_opp2 oppr_max ler_minl !ler_opp2. Qed.

Lemma ler_maxl : forall x y z, (maxr y z <= x) = (y <= x) && (z <= x).
Proof. by move=> x y z; rewrite -lter_opp2 oppr_max ler_minr !ler_opp2. Qed.

Lemma ltr_minr : forall x y z, (x < minr y z) = (x < y) && (x < z).
Proof. by move=> x y z; rewrite !ltrNge ler_minl negb_or. Qed.

Lemma ltr_minl : forall x y z, (minr y z < x) = (y < x) || (z < x).
Proof. by move=> x y z; rewrite !ltrNge ler_minr negb_and. Qed.

Lemma ltr_maxr : forall x y z, (x < maxr y z) = (x < y) || (x < z).
Proof. by move=> x y z; rewrite !ltrNge ler_maxl negb_and. Qed.

Lemma ltr_maxl : forall x y z, (maxr y z < x) = (y < x) && (z < x).
Proof. by move=> x y z; rewrite !ltrNge ler_maxr negb_or. Qed.

Definition lter_minr := (ler_minr, ltr_minr).
Definition lter_minl := (ler_minl, ltr_minl).
Definition lter_maxr := (ler_maxr, ltr_maxr).
Definition lter_maxl := (ler_maxl, ltr_maxl).

Lemma addr_minl : left_distributive +%R (@minr R).
Proof.
move=> x y z; case: minrP=> hxy; first by rewrite minr_l // ler_add2l.
by rewrite minr_r // ltrW // ltr_add2l.
Qed.

Lemma addr_minr : right_distributive +%R (@minr R).
Proof.
move=> x y z; case: minrP=> hxy; first by rewrite minr_l // ler_add2r.
by rewrite minr_r // ltrW // ltr_add2r.
Qed.

Lemma addr_maxl : left_distributive +%R (@maxr R).
Proof. 
move=> x y z; rewrite -[_ + _]opprK oppr_add oppr_max.
by rewrite addr_minl -!oppr_add oppr_min !opprK.
Qed.

Lemma addr_maxr : right_distributive +%R (@maxr R).
Proof. 
move=> x y z; rewrite -[_ + _]opprK oppr_add oppr_max.
by rewrite addr_minr -!oppr_add oppr_min !opprK.
Qed.

Lemma minrK : forall x y, maxr (minr x y) x = x.
Proof. by move=> x y; case: minrP=> hxy; rewrite ?maxrr ?maxr_r // ltrW. Qed.

Lemma minKr : forall x y, minr y (maxr x y) = y.
Proof. by move=> x y; case: maxrP=> hxy; rewrite ?minrr ?minr_l. Qed.

Lemma maxr_minl : left_distributive (@maxr R) (@minr R).
Proof.
move=> x y z; case: minrP=> hxy.
  by case: maxrP=> hm; rewrite minr_l // ler_maxr (hxy, lerr) ?orbT.
by case: maxrP=> hyz; rewrite minr_r // ler_maxr (ltrW hxy, lerr) ?orbT.
Qed.

Lemma maxr_minr : right_distributive (@maxr R) (@minr R).
Proof. by move=> x y z; rewrite maxrC maxr_minl ![_ _ x]maxrC. Qed.

Lemma minr_maxl : left_distributive (@minr R) (@maxr R).
Proof.
move=> x y z; rewrite -[minr _ _]opprK !oppr_min [- maxr x y]oppr_max.
by rewrite maxr_minl !(oppr_max, oppr_min, opprK).
Qed.

Lemma minr_maxr : right_distributive (@minr R) (@maxr R).
Proof. by move=> x y z; rewrite minrC minr_maxl ![_ _ x]minrC. Qed.


Lemma minr_pmulr : forall x y z : R, 0 <= x
  -> x * minr y z = minr (x * y) (x * z).
Proof.
move=> x y z; case: sgrP=> // hx _; first by rewrite hx !mul0r minrr.
case: minrP=> hyz; first by rewrite minr_l // ler_pmul2r.
by rewrite minr_r // ltrW // ltr_pmul2r.
Qed.

Lemma minr_nmulr : forall x y z : R, x <= 0
  -> x * minr y z = maxr (x * y) (x * z).
Proof.
move=> x y z hx; rewrite -[_ * _]opprK -mulNr minr_pmulr ?oppr_cp0 //.
by rewrite oppr_min !mulNr !opprK.
Qed.

Lemma maxr_pmulr : forall x y z : R, 0 <= x
  -> x * maxr y z = maxr (x * y) (x * z).
Proof.
move=> x y z hx; rewrite -[_ * _]opprK -mulrN oppr_max minr_pmulr //.
by rewrite oppr_min !mulrN !opprK.
Qed.

Lemma maxr_nmulr : forall x y z : R, x <= 0
  -> x * maxr y z = minr (x * y) (x * z).
Proof.
move=> x y z hx; rewrite -[_ * _]opprK -mulrN oppr_max minr_nmulr //.
by rewrite oppr_max !mulrN !opprK.
Qed.

Lemma minr_pmull : forall x y z : R, 0 <= x
  -> minr y z * x = minr (y * x) (z * x).
Proof. by move=> x *; rewrite mulrC minr_pmulr // ![_ * x]mulrC. Qed.

Lemma minr_nmull : forall x y z : R, x <= 0
  -> minr y z * x = maxr (y * x) (z * x).
Proof. by move=> x *; rewrite mulrC minr_nmulr // ![_ * x]mulrC. Qed.

Lemma maxr_pmull : forall x y z : R, 0 <= x
  -> maxr y z * x = maxr (y * x) (z * x).
Proof. by move=> x *; rewrite mulrC maxr_pmulr // ![_ * x]mulrC. Qed.

Lemma maxr_nmull : forall x y z : R, x <= 0
  -> maxr y z * x = minr (y * x) (z * x).
Proof. by move=> x *; rewrite mulrC maxr_nmulr // ![_ * x]mulrC. Qed.

Lemma maxrN : forall x, maxr x (- x) = `|x|.
Proof.
move=> x; case: absrP=> hx; first by rewrite ?hx oppr0 maxrr.
  by rewrite maxr_l // ge0_cp // ltrW.
by rewrite maxr_r // le0_cp // ltrW.
Qed.

Lemma maxNr : forall x, maxr (- x) x = `|x|.
Proof. by move=> x; rewrite maxrC maxrN. Qed.

Lemma minrN : forall x, minr x (- x) = - `|x|.
Proof. by move=> x; rewrite -[minr _ _]opprK oppr_min opprK maxNr. Qed.

Lemma minNr : forall x, minr (- x) x = - `|x|.
Proof. by move=> x; rewrite -[minr _ _]opprK oppr_min opprK maxrN. Qed.

End MinMax.

End IntegralDomainTheory.
End IntegralDomainTheory.

Include IntegralDomainTheory.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : PartialOrder.Field.class_of R; mixin : oidom_mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (@mixin _ c).
Local Coercion base : class_of >-> PartialOrder.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class PartialOrder.Field.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PartialOrder.IntegralDomain.Pack (class cT) cT.
Definition oIdomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition poFieldType cT := PartialOrder.Field.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @PartialOrder.IntegralDomain.Pack (poFieldType cT) (class cT) cT.
Definition join_oIdomainType cT :=
  @IntegralDomain.Pack (poFieldType cT) (class cT) cT.
Definition join_fieldType cT :=
  @GRing.Field.Pack (poFieldType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PartialOrder.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical Structure comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical Structure unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical Structure comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical Structure idomainType.
Coercion poIdomainType : type >-> PartialOrder.IntegralDomain.type.
Canonical Structure poIdomainType.
Coercion oIdomainType : type >-> IntegralDomain.type.
Canonical Structure oIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical Structure fieldType.
Coercion poFieldType : type >-> PartialOrder.Field.type.
Canonical Structure poFieldType.

Canonical Structure join_poIdomainType.
Canonical Structure join_oIdomainType.
Canonical Structure join_fieldType.

End Exports.

End Field.

Import PartialOrder.IntegralDomain.Exports.
Import PartialOrder.Field.Exports.
Import IntegralDomain.Exports.
Import Field.Exports.

Module FieldTheory.

Import PartialOrder.IntegralDomainTheory.
Import IntegralDomainTheory.

Section FieldTheory.

Variable F : Field.type.
Implicit Types x y z t : F.

Hint Resolve lerr.

Lemma unitf_gt0 : forall x, 0 < x -> GRing.unit x.
Proof. by move=> x hx; rewrite unitfE eq_sym ltrWN. Qed.

Lemma unitf_lt0 : forall x, x < 0 -> GRing.unit x.
Proof. by move=> x hx; rewrite unitfE ltrWN. Qed.

Lemma invr_ge0 : forall x, (0 <= x^-1) = (0 <= x).
Proof.
move=> x; case: (ltrgtP x)=> hx; last by rewrite hx invr0 lerr.
  apply/negP; move: hx; rewrite ltr_neqAle -oppr_ge0; case/andP=> nx0 hx hVx.
  by move: (mulr_ge0 hx hVx); rewrite mulNr divff // oppr_cp0 lerNgt ltr01.
move: hx; rewrite lerNgt ltr_neqAle eq_sym; case/andP=> x0 hx.
apply/negP; rewrite -oppr_cp0; move/ltrW=> hVx.
by move: (mulr_ge0 hx hVx); rewrite mulrN divff // oppr_cp0 lerNgt ltr01.
Qed.  

Lemma invr_gt0 : forall x, (0 < x^-1) = (0 < x).
Proof. by move=> x; rewrite !ltr_neqAle invr_ge0 eq_sym invr_eq0 eq_sym. Qed.

Definition invr_gte0 := (invr_ge0, invr_gt0).

Lemma invr_le0 : forall x, (x^-1 <= 0) = (x <= 0).
Proof. by move=> x; rewrite !lerNgt invr_gte0. Qed.

Lemma invr_lt0 : forall x, (x^-1 < 0) = (x < 0).
Proof. by move=> x; rewrite !ltrNge invr_gte0. Qed.

Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma invr_eq1 : forall x, (x^-1 == 1) = (x == 1).
Proof. by move=> x; rewrite (can2_eq (@invrK _) (@invrK _)) invr1. Qed.

Lemma invr_gt1 : forall x, 0 < x -> (1 < x^-1) = (x < 1).
Proof.
move=> x hx; case: (ltrgtP x 1)=> hx1; last by rewrite hx1 invr1 ltrr.
  rewrite -{1}[1](@divff _ x); last by rewrite eq_sym ltrWN.
  by rewrite ltr_ipmull // invr_gt0.
(* specific to ssr <= 1.2 *)
rewrite ?[x < 1]ltrNge ?(ltrW hx1) /=.
(* resume here *)
apply/negP=> hVx1; move: (mulr_gt1 hx1 hVx1).
by rewrite divff ?ltrr // eq_sym ltrWN.
Qed.

Lemma invr_ge1 : forall x, 0 < x -> (1 <= x^-1) = (x <= 1).
Proof. by move=> x hx; rewrite !ler_eqVlt eq_sym invr_eq1 eq_sym invr_gt1. Qed.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 : forall x, 0 < x -> (x^-1 <= 1) = (1 <= x).
Proof. by move=> x hx; rewrite -invr_ge1 ?invr_gt0 // invrK. Qed.

Lemma invr_lt1 : forall x, 0 < x -> (x^-1 < 1) = (1 < x).
Proof. by move=> x hx; rewrite -invr_gt1 ?invr_gt0 // invrK. Qed.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

Lemma invr_sg : forall x, (sgr x)^-1 = sgr x.
Proof.
(* (* if ssr > 1.2, this suffices : *) by move=> x; case: (sgrP x). *)
move=> x; case: (ltrgtP x 0); do ?by rewrite -?sgr_cp0; move/eqP->.
by move->; rewrite sgr0. 
Qed.

Lemma sgr_inv : forall x, sgr (x^-1) = sgr x.
Proof.
move=> x; case: (ltrgtP x 0)=> hx; move: (hx); rewrite -?sgr_cp0=> hsx;
  rewrite ?hsx ?(eqP hsx) ?(sgr0, invr0) //.
  by apply/eqP; rewrite sgr_cp0 invr_lt0.
by apply/eqP; rewrite sgr_cp0 invr_gt0.
(* if ssr > 1.2, this suffices : *)
(* move=> x; case: (sgrP x)=> hx; first by rewrite hx invr0 sgr0. *)
(*   by apply/eqP; rewrite sgr_cp0 invr_gt0. *)
(* by apply/eqP; rewrite sgr_cp0 invr_lt0. *)
Qed.

Lemma absr_inv : {morph (@absr F) : x / x ^-1}.
Proof.
move=> x /=; case x0: (x == 0); first by rewrite (eqP x0) !(absr0, invr0).
apply/eqP; rewrite -[`|_|^-1]mul1r.
rewrite -(can2_eq (mulrK _) (mulrVK _)) ?unitfE ?absrE ?x0 //.
by rewrite -absr_mul mulVr ?unitfE ?x0 ?absr1.
Qed.

(* Lemma lef_divr_gt0_mull : forall z x y, 0 < z -> (x <= y / z) = (x * z <= y). *)
(* Proof. *)
(* move=> z x y hz; have nz0: z != 0 by rewrite eq_sym ltrWN. *)
(* apply/idP/idP=> hxyz. *)
(* (* rename like leq_pmul *) *)
(*   by rewrite -[y](@mulfVK _ z) // ler_pmullW // ltrW. *)
(* rewrite -[x](@mulfK _ z) // ler_pmullW //. *)

Lemma ler_pdivl_mulr : forall z x y, 0 < z -> (x <= y / z) = (x * z <= y).
Proof. by move=> z *; rewrite -(@ler_pmul2l _ z) ?mulrVK ?unitf_gt0. Qed.

Lemma ltr_pdivl_mulr : forall z x y, 0 < z -> (x < y / z) = (x * z < y).
Proof. by move=> z *; rewrite -(@ltr_pmul2l _ z) ?mulrVK ?unitf_gt0. Qed.

Definition lter_pdivl_mulr := (ler_pdivl_mulr, ltr_pdivl_mulr).

Lemma ler_pdivr_mulr : forall z x y, 0 < z -> (y / z <= x) = (y <= x * z).
Proof. by move=> z *; rewrite -(@ler_pmul2l _ z) ?mulrVK ?unitf_gt0. Qed.

Lemma ltr_pdivr_mulr : forall z x y, 0 < z -> (y / z < x) = (y < x * z).
Proof. by move=> z *; rewrite -(@ltr_pmul2l _ z) ?mulrVK ?unitf_gt0. Qed.

Definition lter_pdivr_mulr := (ler_pdivr_mulr, ltr_pdivr_mulr).

Lemma ler_pdivl_mull : forall z x y, 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Proof. by move=> z *; rewrite mulrC ler_pdivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivl_mull : forall z x y, 0 < z -> (x < z^-1 * y) = (z * x < y).
Proof. by move=> z *; rewrite mulrC ltr_pdivl_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivl_mull := (ler_pdivl_mull, ltr_pdivl_mull).

Lemma ler_pdivr_mull : forall z x y, 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Proof. by move=> z *; rewrite mulrC ler_pdivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivr_mull : forall z x y, 0 < z -> (z^-1 * y < x) = (y < z * x).
Proof. by move=> z *; rewrite mulrC ltr_pdivr_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivr_mull := (ler_pdivr_mull, ltr_pdivr_mull).

Lemma ler_ndivl_mulr : forall z x y, z < 0 -> (x <= y / z) = (y <= x * z).
Proof. by move=> z *; rewrite -(@ler_nmul2l _ z) ?mulrVK  ?unitf_lt0. Qed.

Lemma ltr_ndivl_mulr : forall z x y, z < 0 -> (x < y / z) = (y < x * z).
Proof. by move=> z *; rewrite -(@ltr_nmul2l _ z) ?mulrVK ?unitf_lt0. Qed.

Definition lter_ndivl_mulr := (ler_ndivl_mulr, ltr_ndivl_mulr).

Lemma ler_ndivr_mulr : forall z x y, z < 0 -> (y / z <= x) = (x * z <= y).
Proof. by move=> z *; rewrite -(@ler_nmul2l _ z) ?mulrVK ?unitf_lt0. Qed.

Lemma ltr_ndivr_mulr : forall z x y, z < 0 -> (y / z < x) = (x * z < y).
Proof. by move=> z *; rewrite -(@ltr_nmul2l _ z) ?mulrVK ?unitf_lt0. Qed.

Definition lter_ndivr_mulr := (ler_ndivr_mulr, ltr_ndivr_mulr).

Lemma ler_ndivl_mull : forall z x y, z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Proof. by move=> z *; rewrite mulrC ler_ndivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivl_mull : forall z x y, z < 0 -> (x < z^-1 * y) = (y < z * x).
Proof. by move=> z *; rewrite mulrC ltr_ndivl_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivl_mull := (ler_ndivl_mull, ltr_ndivl_mull).

Lemma ler_ndivr_mull : forall z x y, z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Proof. by move=> z *; rewrite mulrC ler_ndivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivr_mull : forall z x y, z < 0 -> (z^-1 * y < x) = (z * x < y).
Proof. by move=> z *; rewrite mulrC ltr_ndivr_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivr_mull := (ler_ndivr_mull, ltr_ndivr_mull).

Lemma ler_pinv : forall x y, 0 < x -> 0 < y -> (x <= y) = (y^-1 <= x^-1).
Proof.
move=> x y hx hy.
by rewrite -[x^-1]mul1r ler_pdivl_mulr // ler_pdivr_mull // mulr1.
Qed.

Lemma ler_ninv : forall x y, x < 0 -> y < 0 -> (x <= y) = (y^-1 <= x^-1).
Proof.
move=> x y hx hy.
by rewrite -[x^-1]mul1r ler_ndivl_mulr // ler_ndivl_mull // mulr1.
Qed.

Lemma ltr_pinv : forall x y, 0 < x -> 0 < y -> (x < y) = (y^-1 < x^-1).
Proof.
move=> x y hx hy.
by rewrite -[x^-1]mul1r ltr_pdivl_mulr // ltr_pdivr_mull // mulr1.
Qed.

Lemma ltr_ninv : forall x y, x < 0 -> y < 0 -> (x < y) = (y^-1 < x^-1).
Proof.
move=> x y hx hy.
by rewrite -[x^-1]mul1r ltr_ndivl_mulr // ltr_ndivl_mull // mulr1.
Qed.

Definition lter_pinv := (ler_pinv, ltr_pinv).
Definition lter_ninv := (ler_ninv, ltr_ninv).

Lemma sgr_mulrz : forall x n, sgr (x *~ n.+1) = sgr x.
Proof.
move=> x n; rewrite -natmulP -mulr_natr sgr_mul -{2}[sgr _]mulr1.
by congr (_*_); apply/eqP; rewrite sgr_cp0 ltr0Sn.
Qed.

Lemma midf_le : forall x y, x <= y -> 
  (x <= (x + y) / 2%:~R) * ((x + y) / 2%:~R  <= y).
Proof.
move=> x y lxy; rewrite ler_pdivl_mulr ?ler_pdivr_mulr ?ltr0Sn //.
by rewrite !mulrzr ler_add2r ler_add2l.
Qed.

Lemma midf_lt : forall x y, x < y -> 
  (x < (x + y) / 2%:~R) * ((x + y) / 2%:~R  < y).
Proof.
move=> x y lxy; rewrite ltr_pdivl_mulr ?ltr_pdivr_mulr ?ltr0Sn //.
by rewrite !mulrzr ltr_add2r ltr_add2l.
Qed.

Definition midf_lte := (midf_le, midf_lt).

Lemma natf_div : forall m d : nat, d %| m -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof. exact: char0_natf_div (@charor F). Qed.

Section FinGroup.

Import GroupScope.

Variable gT : finGroupType.

Lemma natf_indexg : forall G H : {group gT},
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Proof. by move=> G H sHG; rewrite -divgS // natf_div ?cardSg. Qed.

End FinGroup.

End FieldTheory.
End FieldTheory.
Include FieldTheory.

(* Module RealClosedField. *)

(* Section ClassDef. *)

(* Definition axiom (F : Field.type) := forall (p : {poly F}) (a b : F), a <= b  *)
(*     -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x. *)

(* Record mixin_of (F : Field.type) := Mixin { *)
(*   _ : axiom F *)
(* }. *)

(* Record class_of (R : Type) : Type := Class { *)
(*   base : Field.class_of R; *)
(*   mixin : mixin_of (Field.Pack base R) *)
(* }. *)
(* Local Coercion base : class_of >-> Field.class_of. *)

(* Structure type := Pack {sort; _ : class_of sort; _ : Type}. *)
(* Local Coercion sort : type >-> Sortclass. *)
(* Definition class cT := let: Pack _ c _ := cT return class_of cT in c. *)
(* Definition clone T cT c of phant_id (class cT) c := @Pack T c T. *)
(* Definition pack T b0 (m0 : mixin_of (@Field.Pack T b0 T)) := *)
(*   fun bT b & phant_id (Field.class bT) b => *)
(*   fun    m & phant_id m0 m => Pack (@Class T b m) T. *)

(* Definition eqType cT := Equality.Pack (class cT) cT. *)
(* Definition choiceType cT := Choice.Pack (class cT) cT. *)
(* Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT. *)
(* Definition ringType cT := GRing.Ring.Pack (class cT) cT. *)
(* Definition comRingType cT := GRing.ComRing.Pack (class cT) cT. *)
(* Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT. *)
(* Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT. *)
(* Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT. *)
(* Definition poIdomainType cT := PartialOrder.IntegralDomain.Pack (class cT) cT. *)
(* Definition oIdomainType cT := IntegralDomain.Pack (class cT) cT. *)
(* Definition fieldType cT := GRing.Field.Pack (class cT) cT. *)
(* Definition poFieldType cT := PartialOrder.Field.Pack (class cT) cT. *)
(* Definition oFieldType cT := Field.Pack (class cT) cT. *)

(* End ClassDef. *)

(* Module Exports. *)
(* Coercion base : class_of >-> Field.class_of. *)
(* Coercion sort : type >-> Sortclass. *)
(* Bind Scope ring_scope with sort. *)
(* Coercion eqType : type >-> Equality.type. *)
(* Canonical Structure eqType. *)
(* Coercion choiceType : type >-> Choice.type. *)
(* Canonical Structure choiceType. *)
(* Coercion zmodType : type >-> GRing.Zmodule.type. *)
(* Canonical Structure zmodType. *)
(* Coercion ringType : type >-> GRing.Ring.type. *)
(* Canonical Structure ringType. *)
(* Coercion comRingType : type >-> GRing.ComRing.type. *)
(* Canonical Structure comRingType. *)
(* Coercion unitRingType : type >-> GRing.UnitRing.type. *)
(* Canonical Structure unitRingType. *)
(* Coercion comUnitRingType : type >-> GRing.ComUnitRing.type. *)
(* Canonical Structure comUnitRingType. *)
(* Coercion idomainType : type >-> GRing.IntegralDomain.type. *)
(* Canonical Structure idomainType. *)
(* Coercion poIdomainType : type >-> PartialOrder.IntegralDomain.type. *)
(* Canonical Structure oIdomainType. *)
(* Coercion oIdomainType : type >-> IntegralDomain.type. *)
(* Canonical Structure oIdomainType. *)
(* Coercion fieldType : type >-> GRing.Field.type. *)
(* Canonical Structure fieldType. *)
(* Coercion poFieldType : type >-> PartialOrder.Field.type. *)
(* Canonical Structure oFieldType. *)
(* Coercion oFieldType : type >-> Field.type. *)
(* Canonical Structure oFieldType. *)
(* End Exports. *)

(* End RealClosedField. *)
(* Import RealClosedField.Exports. *)

(* Module RealClosedFieldTheory. *)
(* Definition poly_ivt := RealClosedField.axiom. *)
(* End RealClosedFieldTheory. *)
(* Include RealClosedFieldTheory. *)

End TotalOrder.

Module Theory.
Export PartialOrder.IntegralDomainTheory.
(* Export PartialOrder.FieldTheory. *)
Export TotalOrder.IntegralDomainTheory.
Export TotalOrder.FieldTheory.
(* Export TotalOrder.RealClosedFieldTheory. *)

End Theory.

End OrderedRing.

Export OrderedRing.PartialOrder.IntegralDomain.Exports.
Export OrderedRing.PartialOrder.Field.Exports.
Export OrderedRing.TotalOrder.IntegralDomain.Exports.
Export OrderedRing.TotalOrder.Field.Exports.
(* Export OrderedRing.TotalOrder.RealClosedField.Exports. *)

Notation PartialOrderMixin := OrderedRing.PartialOrder.Mixin.

Notation poIdomainType := OrderedRing.PartialOrder.IntegralDomain.type.
Notation poFieldType := OrderedRing.PartialOrder.Field.type.
Notation oIdomainType := OrderedRing.TotalOrder.IntegralDomain.type.
Notation oFieldType := OrderedRing.TotalOrder.Field.type.
(* Notation rFieldType := OrderedRing.TotalOrder.RealClosedField.type. *)

Notation POIdomainType T m :=
  (@OrderedRing.PartialOrder.IntegralDomain.pack T _ m _ _ id _ id).
Notation POFieldType T m :=
  (@OrderedRing.PartialOrder.Field.pack T _ m _ _ id _ id).
Notation OIdomainType T m :=
  (@OrderedRing.TotalOrder.IntegralDomain.pack T _ m _ _ id _ id).
Notation OFieldType T m :=
  (@OrderedRing.TotalOrder.Field.pack T _ m _ _ id _ id).
(* Notation RFieldType T m := *)
(*   (@OrderedRing.TotalOrder.RealClosedField.pack T _ m _ _ id _ id). *)

Notation "[ 'poIdomainType' 'of' T ]" :=
    (@OrderedRing.PartialOrder.IntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'poIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'poFieldType' 'of' T ]" :=
  (@OrderedRing.PartialOrder.Field.clone T _ _ id)
  (at level 0, format "[ 'poFieldType'  'of'  T ]") : form_scope.
Notation "[ 'oIdomainType' 'of' T ]" :=
    (@OrderedRing.TotalOrder.IntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'oIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'oFieldType' 'of' T ]" :=
  (@OrderedRing.TotalOrder.Field.clone T _ _ id)
  (at level 0, format "[ 'oFieldType'  'of'  T ]") : form_scope.
(* Notation "[ 'rFieldType' 'of' T ]" := *)
(*   (@OrderedRing.TotalOrder.RealClosedField.clone T _ _ id) *)
(*   (at level 0, format "[ 'rFieldType'  'of'  T ]") : form_scope. *)

Notation posr := (@OrderedRing.PartialOrder.OrderDef.posr _).

Notation "<=%R" := (@OrderedRing.PartialOrder.OrderDef.ler _) : ring_scope.
Notation "x <= y" := (OrderedRing.PartialOrder.OrderDef.ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T))
  (at level 70, y at next level, only parsing) : ring_scope.


Notation "<%R" := (@OrderedRing.PartialOrder.OrderDef.ltr _) : ring_scope.
Notation "x < y"  := (OrderedRing.PartialOrder.OrderDef.ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T))
  (at level 70, y at next level, only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.
Notation "`| x |" := (OrderedRing.PartialOrder.OrderDef.absr x) : ring_scope.
Notation sgr := (@OrderedRing.PartialOrder.OrderDef.sgr _).
Notation maxr := (@OrderedRing.PartialOrder.OrderDef.maxr _).
Notation minr := (@OrderedRing.PartialOrder.OrderDef.minr _).

(* Notation "`[ a , b ]" := [pred x | a <= x <= b] *)
(*   (at level 0, a, b at level 9 , format "`[ a ,  b ]") : ring_scope. *)
(* Notation "`] a , b ]" := [pred x | a < x <= b] *)
(*   (at level 0, a, b at level 9 , format "`] a ,  b ]") : ring_scope. *)
(* Notation "`[ a , b [" := [pred x | a <= x < b] *)
(*   (at level 0, a, b at level 9 , format "`[ a ,  b [") : ring_scope. *)
(* Notation "`] a , b [" := [pred x | a < x < b] *)
(*   (at level 0, a, b at level 9 , format "`] a ,  b [") : ring_scope. *)
(* Notation "`] '-oo' , b ]" := [pred x | x <= b] *)
(*   (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : ring_scope. *)
(* Notation "`] '-oo' , b [" := [pred x | x < b] *)
(*   (at level 0, b at level 9 , format "`] '-oo' ,  b [") : ring_scope. *)
(* Notation "`[ a , '+oo' [" := [pred x | a <= x] *)
(*   (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : ring_scope. *)
(* Notation "`] a , '+oo' [" := [pred x | a < x] *)
(*   (at level 0, a at level 9 , format "`] a ,  '+oo' [") : ring_scope. *)
