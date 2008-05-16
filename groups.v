(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import div.
Require Import ssralg.
Require Import bigops.
Require Import finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope group_scope with g.
Delimit Scope subgroup_scope with G.

(* This module can be imported to open the scope for group element *)
(* operations locally to a file, without exporing the Open to      *)
(* clients of that file (as Open would do).                        *)
Module GroupScope.
Open Scope group_scope.
End GroupScope.
Import GroupScope.

Module FinGroup.

(* We split the group axiomatisation in two. We define a  *)
(* class of "base groups", which are basically monoids    *)
(* with an involutive antimorphism, from which we derive  *)
(* the class of groups proper. This allows use to reuse   *)
(* much of the group notation and algebraic axioms for    *)
(* group subsets, by defining a base group class on them. *)
(*   We use class/mixins here rather than telescopes to   *)
(* be able to interoperate with the type coercions.       *)
(* Another potential benefit (not exploited here) would   *)
(* be to define a class for infinite groups, which could  *)
(* share all of the algebraic laws.                       *)
Record mixin (T : Type) : Type := Mixin {
  mul : T -> T -> T;
  unit : T;
  inv : T -> T;
  _ : associative mul;
  _ : left_unit unit mul;
  _ : involutive inv;
  _ : {morph inv : x y / mul x y >-> mul y x}
}.

Structure base_class : Type := BaseClass {
  sort : Type;
   _ : mixin sort;
   _ : FinType.mixin sort
}.

(* We want to use sort as a coercion class, both to infer         *)
(* argument scopes properly, and to allow groups and cosets to    *)
(* coerce to the base group of group subsets.                     *)
(*   However, the return type of group operations should NOT be a *)
(* coercion class, since this would trump the real (head-normal)  *)
(* coercion class for concrete group types, thus spoiling the     *)
(* coercion of A * B to pred_sort in x \in A * B, or rho * tau to *)
(* ffun and Funclass in (rho * tau) x, when rho tau : perm T.     *)
(*   Therefore we define an alias of sort for argument types, and *)
(* make it the default coercion FinGroup.base_class >-> Sortclass *)
(* so that arguments of a functions whose parameters are of type, *)
(* say, gT : finGroupType, can be coerced to the coercion class   *)
(* of arg_sort. Care should be taken, however, to declare the     *)
(* return type of functions and operators as FinGroup.sort gT     *)
(* rather than gT, e.g., mulg : gT -> gT -> FinGroup.sort gT.     *)
(* Note that since we do this here and in normal.v for all the    *)
(* basic functions, the inferred return type should generally be  *)
(* correct.                                                       *)
Coercion arg_sort := sort.
(* Declaring sort as a Coercion is clearly redundant; it only     *)
(* serves the purpose of eliding FinGroup.sort in the display of  *)
(* return types. The warning could be eliminated by using the     *)
(* functor trick to replace Sortclass by a dummy target.          *)
Coercion sort : base_class >-> Sortclass.

Coercion mixin_of T :=
  let: BaseClass _ m _ := T return mixin T in m.

Definition finmixin_of T :=
  let: BaseClass _ _ m := T return FinType.mixin T in m.

Structure class : Type := Class {
  base :> base_class;
  _ : left_inverse base.(unit) base.(inv) base.(mul)
}.

(* We only need three axioms to make a true group. *)

Section Make.

Variables (T : Type) (unit : T) (mul : T -> T -> T) (inv : T -> T).

Hypothesis mulA : associative mul.
Hypothesis mul1 : left_unit unit mul.
Hypothesis mulV : left_inverse unit inv mul.
Notation "1" := unit.
Infix "*" := mul.
Notation "x ^-1" := (inv x).

Lemma mk_invgK : involutive inv.
Proof.
have mulV21: forall x, x^-1^-1 * 1 = x.
  by move=> x; rewrite -(mulV x) mulA mulV mul1.
by move=> x; rewrite -[_ ^-1]mulV21 -(mul1 1) mulA !mulV21.
Qed.

Lemma mk_invMg : {morph inv : x y / x * y >-> y * x}.
Proof.
have mulxV: forall x, x * x^-1 = 1 by move=> x; rewrite -{1}[x]mk_invgK mulV.
move=> x y /=; rewrite -[y^-1 * _]mul1 -(mulV (x * y)) -2!mulA (mulA y).
by rewrite mulxV mul1 mulxV -(mulxV (x * y)) mulA mulV mul1.
Qed.

Definition mkMixin := Mixin mulA mul1 mk_invgK mk_invMg.

End Make.

End FinGroup.

Bind Scope group_scope with FinGroup.sort.
Bind Scope group_scope with FinGroup.arg_sort.

Notation baseFinGroupType := FinGroup.base_class.
Notation BaseFinGroupType := FinGroup.BaseClass.

Section InheritedClasses.

Variable T : baseFinGroupType.
Let mT := FinGroup.finmixin_of T.

Canonical Structure finGroup_arg_eqType := @EqClass T mT.
Canonical Structure finGroup_eqType := @EqClass (FinGroup.sort T) mT.
Canonical Structure finGroup_arg_finType := @FinClass T mT.
Canonical Structure finGroup_finType := @FinClass (FinGroup.sort T) mT.

End InheritedClasses.

Coercion finGroup_arg_finType : baseFinGroupType >-> finType.

Notation "[ 'baseFinGroupType' 'of' T ]" :=
  (match {T : as baseFinGroupType} as s
   return [type of BaseFinGroupType for s] -> _ with
  | BaseFinGroupType _ mixG mixF => fun k => k mixG mixF end
  (@BaseFinGroupType T)) (at level 0, only parsing) : form_scope.

Notation Local FinMix := (FinType.mkMixin _).
Notation "[ 'baseFinGroupType' 'of' T 'by' mulA , mul1 , invK & invM ]" :=
  (@BaseFinGroupType T (FinGroup.Mixin mulA mul1 invK invM) FinMix)
  (at level 0, only parsing) : form_scope.
Notation "[ 'baseFinGroupType' 'of' T 'by' mulA , mul1 & mulV ]" :=
  (@BaseFinGroupType T (FinGroup.mkMixin mulA mul1 mulV) FinMix)
  (at level 0, only parsing) : form_scope.

Notation finGroupType := FinGroup.class.
Notation FinGroupType := FinGroup.Class.

Notation "[ 'finGroupType' 'of' T ]" :=
  (match {T : baseFinGroupType as finGroupType} as s
   return [type of FinGroupType for s] -> _ with
  | FinGroupType _ mulV => fun k => k mulV end
  (@FinGroupType T)) (at level 0, only parsing) : form_scope.

Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (FinGroup.sort T).

Definition unitg : rT := FinGroup.unit T.
Definition mulg : T -> T -> rT := FinGroup.mul T.
Definition invg : T -> rT := FinGroup.inv T.
Definition expgn_rec (x : T) n : rT := iter n (mulg x) unitg.

End ElementOps.

Definition expgn := nosimpl expgn_rec.

Notation "1" := (unitg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.
Notation "x ^-1" := (invg x) : group_scope.
Notation "x ^+ n" := (expgn x n) : group_scope.
Notation "x ^- n" := (x ^+ n)^-1 : group_scope.

(* Arguments of conjg are restricted to true groups to avoid an *)
(* improper interpretation of A ^ B with A and B sets, namely:  *)
(*       {x^-1 * (y * z) | y \in A, x, z \in B}                 *)
Definition conjg (T : finGroupType) (x y : T) := y^-1 * (x * y).
Notation "x1 ^ x2" := (conjg x1 x2) : group_scope.

Definition commg (T : finGroupType) (x y : T) := x^-1 * x ^ y.
Notation "[ ~ x1 , x2 , .. , xn ]" := (commg .. (commg x1 x2) .. xn)
  (at level 0,
   format  "'[ ' [ ~  x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'") : group_scope.

Prenex Implicits mulg invg expgn conjg commg.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[mulg/1]_(<- r | P%B) F%g) : group_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[mulg/1]_(i <- r | P%B) F%g) : group_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[mulg/1]_(i <- r) F%g) : group_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[mulg/1]_(m <= i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[mulg/1]_(m <= i < n) F%g) : group_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[mulg/1]_(i | P%B) F%g) : group_scope.
Notation "\prod_ ( i ) F" :=
  (\big[mulg/1]_(i) F%g) : group_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[mulg/1]_(i : t | P%B) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[mulg/1]_(i : t) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[mulg/1]_(i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[mulg/1]_(i < n) F%g) : group_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[mulg/1]_(i \in A | P%B) F%g) : group_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[mulg/1]_(i \in A) F%g) : group_scope.

Section PreGroupIdentities.

Variable T : baseFinGroupType.
Implicit Types x y z : T.

Lemma mulgA : @associative T mulg.  Proof. by case: T => ? []. Qed.
Lemma mul1g : @left_unit T 1 mulg.  Proof. by case: T => ? []. Qed.
Lemma invgK : @involutive T invg.   Proof. by case: T => ? []. Qed.
Lemma invMg : forall x y, (x * y)^-1 = y^-1 * x^-1.
Proof. by case: T => ? []. Qed.

Lemma invg_inj : @injective T T invg. Proof. exact: can_inj invgK. Qed.

Lemma eq_invg_sym : forall x y, (x^-1 == y :> T) = (x == y^-1).
Proof. by move=> x y; exact: (inv_eq invgK). Qed.

Lemma invg1 : 1^-1 = 1 :> T.
Proof. by apply: invg_inj; rewrite -{1}[1^-1]mul1g invMg invgK mul1g. Qed.

Lemma eq_invg1 : forall x, (x^-1 == 1 :> T) = (x == 1).
Proof. by move=> x; rewrite eq_invg_sym invg1. Qed.

Lemma mulg1 : @right_unit T 1 mulg.
Proof. by move=> x; apply: invg_inj; rewrite invMg invg1 mul1g. Qed.

Canonical Structure finGroup_law := Monoid.Law mulgA mul1g mulg1.

Lemma expgnE : forall x n, x ^+ n = expgn_rec x n. Proof. by []. Qed.

Lemma expg0 : forall x, x ^+ 0 = 1. Proof. by []. Qed.

Lemma expgS : forall x n, x ^+ n.+1 = x * x ^+ n. Proof. by []. Qed.

Lemma expg1 : forall x, x ^+ 1 = x. Proof. exact: mulg1. Qed.

Lemma exp1gn : forall n, 1 ^+ n = 1 :> T.
Proof. by elim=> // n IHn; rewrite expgS mul1g. Qed.

Lemma expgn_add : forall x n m, x ^+ (n + m) = x ^+ n * x ^+ m.
Proof. by move=> x; elim=> [|n IHn] m; rewrite ?mul1g // -mulgA -IHn. Qed.

Lemma expgSr : forall x n, x ^+ n.+1 = x ^+ n * x.
Proof. by move=> x n; rewrite -addn1 expgn_add expg1. Qed.

Lemma expgn_mul : forall x n m, x ^+ (n * m) = x ^+ n ^+ m.
Proof.
move=> x n; elim=> [|m IHm]; first by rewrite muln0 expg0.
by rewrite mulnS expgn_add IHm.
Qed.

Definition commute x y := x * y = y * x.

Lemma commute_refl : forall x, commute x x.
Proof. by []. Qed.

Lemma commute_sym : forall x y, commute x y -> commute y x.
Proof. by []. Qed.

Lemma commute1 : forall x, commute x 1.
Proof. by move=> x; rewrite /commute mulg1 mul1g. Qed.

Lemma commuteM : forall x y z,
  commute x y ->  commute x z ->  commute x (y * z).
Proof. by move=> x y z cxy cxz; rewrite /commute -mulgA -cxz !mulgA cxy. Qed.

Lemma commuteX : forall x y n, commute x y ->  commute x (y ^+ n).
Proof.
move=> x y n cxy; elim: n => [|n IHn]; [exact: commute1 | exact: commuteM].
Qed.

Lemma expVgn : forall x n, x^-1 ^+ n = x ^- n.
Proof.
by move=> x; elim=> [|n IHn]; rewrite ?invg1 // invMg -IHn expgSr.
Qed.

Lemma expMgn : forall x y n, commute x y -> (x * y) ^+ n  = x ^+ n * y ^+ n.
Proof.
move=> x y n cxy; elim: n => [| n IHn]; first by rewrite mulg1.
by rewrite !expgS IHn -mulgA (mulgA y) (commuteX _ (commute_sym cxy)) !mulgA.
Qed.

End PreGroupIdentities.

Hint Resolve commute1.
Implicit Arguments invg_inj [T].
Prenex Implicits commute invgK invg_inj.

Section GroupIdentities.

Variable T : finGroupType.
Implicit Types x y z : T.

Lemma mulVg : @left_inverse T 1 invg mulg.
Proof. by case T. Qed.

Lemma mulgV : @right_inverse T 1 invg mulg.
Proof. by move=> x; rewrite -{1}(invgK x) mulVg. Qed.

Lemma mulKg : forall x, cancel (mulg x) (mulg x^-1).
Proof. by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulKVg : forall x, cancel (mulg x^-1) (mulg x).
Proof. by move=> x y; rewrite mulgA mulgV mul1g. Qed.

Lemma mulg_injl : forall x, injective (mulg x).
Proof. move=> x; exact: can_inj (mulKg x). Qed.

Lemma mulgK : forall x, cancel (mulg^~ x) (mulg^~ x^-1).
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulgKV : forall x, cancel (mulg^~ x^-1) (mulg^~ x).
Proof. by move=> x y; rewrite -mulgA mulVg mulg1. Qed.

Lemma mulg_injr : forall x, injective (mulg^~ x).
Proof. move=> x; exact: can_inj (mulgK x). Qed.

Lemma eq_invg_mul : forall x y, (x^-1 == y :> T) = (x * y == 1 :> T).
Proof. by move=> x y; rewrite (canF_eq (mulKg _)) mulg1. Qed.

Lemma eq_mulgV1 : forall x y, (x == y) = (x * y^-1 == 1 :> T).
Proof. by move=> x y; rewrite -(inj_eq invg_inj) eq_invg_mul. Qed.

Lemma eq_mulVg1 : forall x y, (x == y) = (x^-1 * y == 1 :> T).
Proof. by move=> x y; rewrite -eq_invg_mul invgK. Qed.

Lemma commuteV : forall x y, commute x y -> commute x y^-1.
Proof.
by move=> x y cxy; apply/eqP; rewrite (canF_eq (mulgKV _)) -mulgA cxy mulKg.
Qed.

(* A connect-based alternative to orderg
Definition order (x : T) := connect.order (mulg x) 1.

Lemma expgn_order : forall x, x ^+ (order x) = 1.
Proof. move=> x; apply: iter_order; exact: mulg_injl. Qed.

Lemma order_pos : forall x, order x > 0.
Proof. by move=> x; rewrite -[order x]orderSpred. Qed.

Canonical Structure order_pos_nat x := PosNat (order_pos x).

Lemma invg_order : forall x, x^-1 = x ^+ (order x).-1.
Proof.
by move=> x; apply/eqP; rewrite eq_invMg -expgS orderSpred expgn_order.
Qed.

*)

Lemma conjgE : forall x y, x ^ y = y^-1 * (x * y). Proof. by []. Qed.

Lemma conjgC : forall x y, x * y = y * x ^ y.
Proof. by move=> x y; rewrite mulKVg. Qed.

Lemma conjgCV : forall x y, x * y = y ^ x^-1 * x.
Proof. by move=> x y; rewrite -mulgA mulgKV invgK. Qed.

Lemma conjg1 : forall x, x ^ 1 = x.
Proof. by move=> x; rewrite conjgE commute1 mulKg. Qed.

Lemma conj1g : forall x, 1 ^ x = 1.
Proof. by move=> x; rewrite conjgE mul1g mulVg. Qed.

Lemma conjMg : forall x y z, (x * y) ^ z = x ^ z * y ^ z.
Proof. by move=> x y z; rewrite !conjgE !mulgA mulgK. Qed.

Lemma conjgM : forall x y z, x ^ (y * z) = (x ^ y) ^ z.
Proof. by move=> x y z; rewrite !conjgE invMg !mulgA. Qed.

Lemma conjVg : forall x y, x^-1 ^ y = (x ^ y)^-1.
Proof. by move=> x y; rewrite !conjgE !invMg invgK mulgA. Qed.

Lemma conjJg : forall x y z, (x ^ y) ^ z = (x ^ z) ^ y ^ z.
Proof. by move=> x y z; rewrite 2!conjMg conjVg. Qed.

Lemma conjXg : forall x y n, (x ^+ n) ^ y = (x ^ y) ^+ n.
Proof. by move=> x y; elim=> [| n IHn]; rewrite ?conj1g // conjMg IHn. Qed.

Lemma conjgK : forall y, cancel (conjg^~ y) (conjg^~ y^-1).
Proof. by move=> y x; rewrite -conjgM mulgV conjg1. Qed.

Lemma conjgKV : forall y, cancel (conjg^~ y^-1) (conjg^~ y).
Proof. by move=> y x; rewrite -conjgM mulVg conjg1. Qed.

Lemma conjg_inj : forall y, injective (conjg^~ y).
Proof. move=> y; exact: can_inj (conjgK y). Qed.

Lemma commgEl : forall x y, [~ x, y] = x^-1 * x ^ y. Proof. by []. Qed.

Lemma commgEr : forall x y, [~ x, y] = y^-1 ^ x * y.
Proof. by move=> x y; rewrite -!mulgA. Qed.

Lemma commgC : forall x y, x * y = y * x * [~ x, y].
Proof. by move=> x y; rewrite -mulgA !mulKVg. Qed.

Lemma commgCV : forall x y, x * y = [~ x^-1, y^-1] * (y * x).
Proof. by move=> x y; rewrite commgEl !mulgA !invgK !mulgKV. Qed.

Lemma conjRg : forall x y z, [~ x, y] ^ z = [~ x ^ z, y ^ z].
Proof. by move=> x y z; rewrite !conjMg !conjVg. Qed.

Lemma invg_comm : forall x y, [~ x, y]^-1 = [~ y, x].
Proof. by move=> x y; rewrite commgEr conjVg invMg invgK. Qed.

Lemma commgP : forall x y, reflect (commute x y) ([~ x, y] == 1 :> T).
Proof. move=> x y; rewrite 2!(canF_eq (mulKVg _)) mulg1; exact: eqP. Qed.

Lemma conjg_fixP : forall x y, reflect (x ^ y = x) ([~ x, y] == 1 :> T).
Proof. move=> x y; rewrite (canF_eq (mulKVg _)) mulg1; exact: eqP. Qed.

Lemma commg1_sym : forall x y, ([~ x, y] == 1 :> T) = ([~ y, x] == 1 :> T).
Proof. by move=> x y; rewrite -invg_comm (inv_eq invgK) invg1. Qed.

Lemma commg1 : forall x, [~ x, 1] = 1.
Proof. by move=> x; apply/eqP; apply/commgP. Qed.

Lemma comm1g : forall x, [~ 1, x] = 1.
Proof. by move=> x; rewrite -invg_comm commg1 invg1. Qed.

Lemma commgg : forall x, [~ x, x] = 1.
Proof. by move=> x; apply/eqP; apply/commgP. Qed.

Lemma commgXg : forall x n, [~ x, x ^+ n] = 1.
Proof. by move=> x n; apply/eqP; apply/commgP; exact: commuteX. Qed.

Lemma commgVg : forall x, [~ x, x^-1] = 1.
Proof. by move=> x; apply/eqP; apply/commgP; exact: commuteV. Qed.

Lemma commgXVg : forall x n, [~ x, x ^- n] = 1.
Proof.
move=> x n;  apply/eqP; apply/commgP; apply: commuteV; exact: commuteX.
Qed.

(* Other commg identities should slot in here. *)

End GroupIdentities.

Hint Rewrite mulg1 mul1g invg1 mulVg mulgV (@invgK) mulgK mulgKV
             invMg mulgA : gsimpl.

Ltac gsimpl := autorewrite with gsimpl; try done.

Definition gsimp := (mulg1 , mul1g, (invg1, @invgK), (mulgV, mulVg)).
Definition gnorm := (gsimp, (mulgK, mulgKV, (mulgA, invMg))).

Implicit Arguments mulg_injl [T].
Implicit Arguments mulg_injr [T].
Implicit Arguments conjg_inj [T].
Implicit Arguments commgP [T x y].
Implicit Arguments conjg_fixP [T x y].
Prenex Implicits conjg_fixP commgP.

Section SetMulDef.

Variable gT : finGroupType.
Notation Local sT := {set gT}.
Implicit Types A B : sT.
Implicit Type x y : gT.

(* Plucking a set representative. *)

Definition repr A := if [pick x \in A] is Some x then x else 1.

Lemma mem_repr : forall x A, x \in A -> repr A \in A.
Proof.
by rewrite /repr => x A; case: pickP => [//|A0]; rewrite [x \in A]A0.
Qed.

Lemma card_mem_repr : forall A, #|A| > 0 -> repr A \in A.
Proof. by move=> A; rewrite lt0n; case/existsP=> x; exact: mem_repr. Qed.

(* Set-lifted group operations. *)

Definition set_mulg A B := mulg @2: (A, B).
Definition set_invg A := invg @^-1: A.

Definition lcoset_of A x := mulg x @: A.
Definition rcoset_of A x := mulg^~ x @: A.
Definition lcosets A B := lcoset_of A @: B.
Definition rcosets A B := rcoset_of A @: B.
Definition indexg A B := #|rcosets A B|.

Definition conjugate_of A x := conjg^~ x @: A.
Definition conjugates A B := conjugate_of A @: B.
Definition class_of x B := conjg x @: B.
Definition classes A := class_of^~ A @: A.
Definition class_support A B := conjg @2: (A, B).

Definition commg_set A B := commg @2: (A, B).

(* These will only be used later, but are defined here so that we can *)
(* keep all the Notation together.                                    *)
Definition normaliser A := [set x | conjugate_of A x \subset A].
Definition centraliser A := \bigcap_(x \in A) normaliser [set x].

(* "normal" and "central" are intended to be use in conjunction with *)
(* the {in ...} form, as in abelian below.                           *)
Definition normal A := forall x, conjugate_of A x = A.
Definition normal_subset A B := (A \subset B) && (B \subset normaliser A).
Definition centralises x A := forall y, y \in A -> commute x y.
Definition central A := forall x, centralises x A.
Definition abelian A := {in A, central A}.

(* The pre-group structure of group subsets. *)

Lemma set_mul1g : left_unit [set 1] set_mulg.
Proof.
move=> A; apply/setP=> y; apply/imset2P/idP=> [[x1 x] | Ay].
  by move/set1P=> -> Ax ->; rewrite mul1g.
by exists (1 : gT) y; rewrite ?(set11, mul1g).
Qed.

Lemma set_mulgA : associative set_mulg.
Proof.
move=> A B C; apply/setP=> y; apply/imset2P/imset2P=> [[x1 z Ax1] | [z x3]].
  case/imset2P=> x2 x3 Bx2 Cx3 -> ->.
  by exists (x1 * x2) x3; rewrite ?mulgA //; apply/imset2P; exists x1 x2.
case/imset2P=> x1 x2 Ax1 Bx2 -> Cx3 ->.
by exists x1 (x2 * x3); rewrite ?mulgA //; apply/imset2P; exists x2 x3.
Qed.

Lemma set_invgK : involutive set_invg.
Proof. by move=> A; apply/setP=> x; rewrite !inE invgK. Qed.

Lemma set_invgM : {morph set_invg : A B / set_mulg A B >-> set_mulg B A}.
Proof.
move=> A B; apply/setP=> z; rewrite inE.
apply/imset2P/imset2P=> [[x y Ax By] | [y x]]; last first.
  by rewrite !inE => By1 Ax1 ->; exists x^-1 y^-1; rewrite ?invMg.
by move/(canRL invgK)->; exists y^-1 x^-1; rewrite ?invMg // inE invgK.
Qed.

Canonical Structure group_set_baseGroupType :=
  [baseFinGroupType of set gT by set_mulgA, set_mul1g, set_invgK & set_invgM].

Canonical Structure group_set_for_baseGroupType := Eval hnf in
  [baseFinGroupType of {set gT}].

End SetMulDef.

(* Time to open the bag of dirty tricks. When we define groups down below *)
(* as a subtype of set gT, we need them to be able to coerce to sets in   *)
(* both set-style contexts (x \in G) and monoid-style contexts (G * H),   *)
(* and we need the coercion function to be EXACTLY the structure          *)
(* projection in BOTH cases -- otherwise the canonical unification breaks.*)
(*   Alas, Coq doesn't let us use the same coercion function twice, even  *)
(* when the targets are convertible. Our workaround (ab)uses the module   *)
(* system to declare two different identity coercions on an alias class.  *)

Module GroupSet.
Definition sort (gT : finGroupType) := {set gT}.
Identity Coercion of_sort : sort >-> set_for.
End GroupSet.

Module Type GroupSetBaseGroupSig.
Definition sort gT := group_set_for_baseGroupType gT : Type.
End GroupSetBaseGroupSig.

Module MakeGroupSetBaseGroup (Gset_base : GroupSetBaseGroupSig).
Identity Coercion of_sort : Gset_base.sort >-> FinGroup.arg_sort.
End MakeGroupSetBaseGroup.

Module GroupSetBaseGroup := MakeGroupSetBaseGroup GroupSet.

Canonical Structure group_set_eqType gT := Eval hnf in
  [eqType of GroupSet.sort gT].
Canonical Structure group_set_finType gT := Eval hnf in
  [finType of GroupSet.sort gT].

Arguments Scope conjugate_of [_ group_scope group_scope].
Arguments Scope class_of [_ group_scope group_scope].
Arguments Scope conjugates [_ group_scope group_scope].
Arguments Scope rcosets [_ group_scope group_scope].
Arguments Scope rcoset_of [_ group_scope group_scope].
Arguments Scope lcosets [_ group_scope group_scope].
Arguments Scope lcoset_of [_ group_scope group_scope].
Arguments Scope class_support [_ group_scope group_scope].
Arguments Scope normal [_ group_scope].
Arguments Scope normaliser [_ group_scope].
Arguments Scope normal_subset [_ group_scope group_scope].
Arguments Scope central [_ group_scope].
Arguments Scope centraliser [_ group_scope].
Arguments Scope centralises [_ group_scope group_scope].
Arguments Scope abelian [_ group_scope].

Notation "x *: A" := ([set x%g] * A) (at level 40) : group_scope.
Notation "A :* x" := (A * [set x%g]) (at level 40) : group_scope.
Notation "A :^ x" := (conjugate_of A x) (at level 35) : group_scope.
Notation "x ^: B" := (class_of x B) (at level 35) : group_scope.
Notation "A :^: B" := (conjugates A B) (at level 35) : group_scope.

(* No notation for lcoset_of and rcoset_of, which are to be used   *)
(* only in curried form; thus we can use mulgA, mulg1, etc, freely *)
(* on, e.g., A :* 1 * B :* x.                                      *)
(* No notation for the set commutator generator set set_commg.     *)

Notation "''N' ( A )" := (normaliser A)
  (at level 9, format "''N' ( A )") : group_scope.
Notation "'N_' ( G ) ( A )" := (G%g :&: 'N(A))
  (at level 9, format "'N_' ( G ) ( A )") : group_scope.
Notation "A <| B" := (normal_subset A B)
  (at level 70) : group_scope.
Notation "''C' ( A )" := (centraliser A%g)
  (at level 9, format "''C' ( A )") : group_scope.
Notation "'C_' ( G ) ( A )" := (G%g :&: 'C(A))
  (at level 9, format "'C_' ( G ) ( A )") : group_scope.
Notation "''C' [ x ]" := 'N([set x%g])
  (at level 9, format "''C' [ x ]") : group_scope.
Notation "'C_' ( G ) [ x ]" := N_(G)([set x%g])
  (at level 9, format "'C_' ( G ) [ x ]") : group_scope.

Notation "{ 'for' x , 'normal' A }" := (A :^ x = A%g)
   (at level 0, A at level 9,
    format "{ 'for'  x ,  'normal'  A }") : type_scope.
Notation "{ 'for' x , 'central' A }" := (centralises x A%g)
   (at level 0, A at level 9,
    format "{ 'for'  x ,  'central'  A }") : type_scope.

Prenex Implicits repr lcoset_of rcoset_of lcosets rcosets indexg.
Prenex Implicits conjugate_of conjugates class_of classes class_support.
Prenex Implicits commg_set normal central abelian.

Implicit Arguments mem_repr [gT A].

Section SmulProp.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types A B C D : sT.
Implicit Type x y z : gT.

(* Set product. We already have all the pregroup identities, so we *)
(* only need to add the monotonicity rules.                        *)

Lemma mulsgP : forall A B x,
  reflect (imset2_spec mulg (mem A) (mem B) x) (x \in A * B).
Proof. move=> A B x; exact: imset2P. Qed.

Lemma mem_mulg : forall A B x y, x \in A -> y \in B -> x * y \in A * B.
Proof. by move=> A B x y Ax By; apply/mulsgP; exists x y. Qed.

Lemma mulSg : forall A B C, A \subset B -> A * C \subset B * C.
Proof. move=> A B C; exact: imset2Sl. Qed.

Lemma mulgS : forall A B C, B \subset C -> A * B \subset A * C.
Proof. move=> A B C; exact: imset2Sr. Qed.

Lemma mulgSS : forall A B C D,
  A \subset B -> C \subset D -> A * C \subset B * D.
Proof. move=> A B C D; exact: imset2S. Qed.

Lemma mulg_subl : forall A B, 1 \in B -> A \subset A * B.
Proof. by move=> A B B1; rewrite -{1}(mulg1 A) mulgS ?sub1set. Qed.

Lemma mulg_subr : forall A B, 1 \in A -> B \subset A * B.
Proof. by move=> A B A1; rewrite -{1}(mul1g B) mulSg ?sub1set. Qed.

Lemma mulUg : forall A B C, (A :|: B) * C = (A * C) :|: (B * C).
Proof. move=> A B C; exact: imset2Ul. Qed.

Lemma mulgU : forall A B C, A * (B :|: C) = (A * B) :|: (A * C).
Proof. move=> A B C; exact: imset2Ur. Qed.

(* Set (pointwise) inverse. *)

Lemma invUg : forall A B, (A :|: B)^-1 = A^-1 :|: B^-1.
Proof. by move=> A B; exact: preimsetU. Qed.

Lemma invIg : forall A B, (A :&: B)^-1 = A^-1 :&: B^-1.
Proof. by move=> A B; exact: preimsetI. Qed.

Lemma invDg : forall A B, (A :\: B)^-1 = A^-1 :\: B^-1.
Proof. by move=> A B; exact: preimsetD. Qed.

Lemma invCg : forall A, (~: A)^-1 = ~: A^-1.
Proof. by move=> A; exact: preimsetC. Qed.

Lemma invSg : forall A B, (A^-1 \subset B^-1) = (A \subset B).
Proof. by move=> A B; rewrite -!eqsetIl -invIg (inj_eq invg_inj). Qed.

Lemma mem_invg : forall x A, (x \in A^-1) = (x^-1 \in A).
Proof. by move=> x A; rewrite inE. Qed.

Lemma memV_invg : forall x A, (x^-1 \in A^-1) = (x \in A).
Proof. by move=> x A; rewrite inE invgK. Qed.

Lemma card_invg : forall A, #|A^-1| = #|A|.
Proof. move=> A; apply: card_preimset; exact: invg_inj. Qed.

(* Product with singletons. *)

Lemma unitsgE : 1 = [set 1] :> sT. Proof. by []. Qed.

Lemma mulg_set1 : forall x y, [set x] :* y = [set x * y].
Proof. by move=> x y; rewrite [_ * _]imset2_set1l imset_set1. Qed.

Lemma invg_set1 : forall x, [set x]^-1 = [set x^-1].
Proof. move=> x; apply/setP=> y; rewrite !inE inv_eq //; exact: invgK. Qed.

(* Cosets, left and right. *)

Lemma lcosetE : forall A x, lcoset_of A x = x *: A.
Proof. by move=> A x; rewrite [_ * _]imset2_set1l. Qed.

Lemma card_lcoset : forall A x, #|x *: A| = #|A|.
Proof. by move=> A x; rewrite -lcosetE (card_imset _ (mulg_injl _)). Qed.

Lemma mem_lcoset : forall A x y, (y \in x *: A) = (x^-1 * y \in A).
Proof.
by move=> A x y; rewrite -lcosetE [_ x](can_imset_pre _ (mulKg _)) inE.
Qed.

Lemma lcosetP : forall A x y,
  reflect (exists2 a, a \in A & y = x * a) (y \in x *: A).
Proof. move=> A x y; rewrite -lcosetE; exact: imsetP. Qed.

Lemma lcosetsP : forall A B C,
  reflect (exists2 x, x \in B & C = x *: A) (C \in lcosets A B).
Proof.
move=> A B C.
by apply: (iffP imsetP) => [] [x Bx ->]; exists x; rewrite ?lcosetE.
Qed.

Lemma lcosetM : forall A x y, (x * y) *: A = x *: (y *: A).
Proof. by move=> A x y; rewrite -mulg_set1 mulgA. Qed.

(* On to the right, adding some algebraic lemmas *)

Lemma rcosetE : forall A x, rcoset_of A x = A :* x.
Proof. by move=> A x; rewrite [_ * _]imset2_set1r. Qed.

Lemma card_rcoset : forall A x, #|A :* x| = #|A|.
Proof. by move=> A x; rewrite -rcosetE (card_imset _ (mulg_injr _)). Qed.

Lemma mem_rcoset : forall A x y, (y \in A :* x) = (y * x^-1 \in A).
Proof.
by move=> A x y; rewrite -rcosetE  [_ x](can_imset_pre A (mulgK _)) inE.
Qed.

Lemma rcosetP : forall A x y,
  reflect (exists2 a, a \in A & y = a * x) (y \in A :* x).
Proof. move=> A x y; rewrite -rcosetE; exact: imsetP. Qed.

Lemma rcosetsP : forall A B C,
  reflect (exists2 x, x \in B & C = A :* x) (C \in rcosets A B).
Proof.
move=> A B C.
by apply: (iffP imsetP) => [] [x Bx ->]; exists x; rewrite ?rcosetE.
Qed.

Lemma rcosetM : forall A x y, A :* (x * y) = A :* x :* y.
Proof. by move=> A x y; rewrite -mulg_set1 mulgA. Qed.

(* Probably redundant *)
Lemma rcoset1 : forall A, A :* 1 = A.
Proof. exact: mulg1. Qed.

Lemma rcosetK : forall x, cancel (fun A => A :* x) (fun A => A :* x^-1).
Proof. by move=> x A; rewrite -rcosetM mulgV mulg1. Qed.

Lemma rcosetKV : forall x, cancel (fun A => A :* x^-1) (fun A => A :* x).
Proof. by move=> x A; rewrite -rcosetM mulVg mulg1. Qed.

Lemma rcoset_inj : forall x, injective (fun A => A :* x).
Proof. by move=> x; exact: can_inj (rcosetK x). Qed.

(* Inverse maps lcosets to rcosets *)

Lemma lcosets_invg : forall A B, lcosets A^-1 B^-1 = invg @^-1: rcosets A B. 
Proof.
move=> A B; apply/setP=> C; rewrite inE.
apply/imsetP/imsetP=> [] [a]; rewrite -memV_invg ?invgK => Aa;
  try move/(canRL invgK); move->; exists a^-1;
  by rewrite // lcosetE rcosetE invMg invg_set1 ?invgK.
Qed.

(* Conjugates. *)

Lemma conjg_preim : forall A x, A :^ x = (conjg^~ x^-1) @^-1: A.
Proof. move=> A x; exact: can_imset_pre (conjgK _). Qed.

Lemma conjIg : forall A B x, (A :&: B) :^ x = A :^ x :&: B :^ x.
Proof. by move=> A B x; rewrite !conjg_preim preimsetI. Qed.

Lemma conjUg : forall A B x, (A :|: B) :^ x = A :^ x :|: B :^ x.
Proof. by move=> A B x; rewrite !conjg_preim preimsetU. Qed.

Lemma card_conjg : forall A x, #|A :^ x| = #|A|.
Proof. by move=> A x; rewrite (card_imset _ (conjg_inj x)). Qed.

Lemma mem_conjg : forall A x y, (y \in A :^ x) = (y ^ x^-1 \in A).
Proof. by move=> A x y; rewrite conjg_preim inE. Qed.

Lemma mem_conjgV : forall A x y, (y \in A :^ x^-1) = (y ^ x \in A).
Proof. by move=> A x y; rewrite mem_conjg invgK. Qed.

Lemma memJ_conjg : forall A x y, (y ^ x \in A :^ x) = (y \in A).
Proof. by move=> A x y; rewrite mem_conjg conjgK. Qed.

Lemma conjsgE : forall A x, A :^ x = x^-1 *: (A :* x).
Proof.
by move=> A x; apply/setP=> y; rewrite mem_lcoset mem_rcoset -mulgA mem_conjg.
Qed.

Lemma conjsg1 : forall A, A :^ 1 = A.
Proof. by move=> A; rewrite conjsgE invg1 mul1g mulg1. Qed.

Lemma conjsgM : forall A x y, A :^ (x * y) = (A :^ x) :^ y.
Proof. by move=> A x y; rewrite !conjsgE invMg -!mulg_set1 !mulgA. Qed.

Lemma conjsgK : forall x, cancel (fun A => A :^ x) (fun A => A :^ x^-1).
Proof. by move=> x A; rewrite -conjsgM mulgV conjsg1. Qed.

Lemma conjsgKV : forall x, cancel (fun A => A :^ x^-1) (fun A => A :^ x).
Proof. by move=> x A; rewrite -conjsgM mulVg conjsg1. Qed.

Lemma conjsg_inj : forall x, injective (fun A => A :^ x).
Proof. by move=> x; exact: can_inj (conjsgK x). Qed.

Lemma conjSg : forall A B x, (A :^ x \subset B :^ x) = (A \subset B).
Proof.
by move=> A B x; rewrite -!eqsetIl -conjIg (inj_eq (@conjsg_inj x)).
Qed.

Lemma conjg_set1 : forall x y, [set x] :^ y = [set x ^ y].
Proof. by move=> x y; rewrite [_ :^ _]imset_set1. Qed.

Lemma conjs1g : forall x, 1 :^ x = 1.
Proof. by move=> x; rewrite conjg_set1 conj1g. Qed.

Lemma conjsMg : forall A B x, (A * B) :^ x = A :^ x * B :^ x.
Proof. by move=> A B x; rewrite !conjsgE !mulgA rcosetK. Qed.

(* Classes; not much for now. *)

Lemma classgS : forall x A B, A \subset B -> x ^: A \subset x ^: B.
Proof. move=> x A B; exact: imsetS. Qed.

Lemma classg_set1 : forall x y,  x ^: [set y] = [set x ^ y].
Proof. by move=> x y; exact: imset_set1. Qed.

Lemma class1g : forall x A, x \in A -> 1 ^: A = 1.
Proof.
move=> x A Ax; apply/setP=> y.
by apply/imsetP/set1P=> [[a Aa]|] ->; last exists x; rewrite ?conj1g.
Qed.

Lemma class_supportM : forall A B C,
  class_support A (B * C) = class_support (class_support A B) C.
Proof.
move=> A B C; apply/setP=> x; apply/imset2P/imset2P=> [[a y Aa] | [y c]].
  case/mulsgP=> b c Bb Cc -> ->{x y}.
  by exists (a ^ b) c; rewrite ?(imset2_f_imp, conjgM).
case/imset2P=> a b Aa Bb -> Cc ->{x y}.
by exists a (b * c); rewrite ?(mem_mulg, conjgM).
Qed.

Lemma class_support_set1l : forall A x, class_support [set x] A = x ^: A.
Proof. move=> A x; exact: imset2_set1l. Qed.

Lemma class_support_set1r : forall A x, class_support A [set x] = A :^ x.
Proof. move=> A x; exact: imset2_set1r. Qed.

Lemma classgM : forall x A B, x ^: (A * B) = class_support (x ^: A) B.
Proof. by move=> x A B; rewrite -!class_support_set1l class_supportM. Qed.

Lemma classg_lcoset : forall x y A, x ^: (y *: A) = (x ^ y) ^: A.
Proof. by move=> x y A; rewrite classgM classg_set1 class_support_set1l. Qed.

Lemma classg_rcoset : forall x A y, x ^: (A :* y) = (x ^: A) :^ y.
Proof. by move=> x A y; rewrite -class_support_set1r classgM. Qed.

(* Conjugate set. *)

Lemma conjugatesS : forall A B C, B \subset C -> A :^: B \subset A :^: C.
Proof. by move=> A B C; exact: imsetS. Qed.

Lemma conjugates_set1 : forall A x, A :^: [set x] = [set A :^ x].
Proof. by move=> A x; exact: imset_set1. Qed.

Lemma class_supportEl : forall A B,
  class_support A B = \bigcup_(x \in A) x ^: B.
Proof. move=> A B; exact: curry_imset2l. Qed.

Lemma class_supportEr : forall A B,
  class_support A B = \bigcup_(x \in B) A :^ x.
Proof. move=> A B; exact: curry_imset2r. Qed.

(* Commutator sets. *)

Lemma commg_setSS : forall A B C D,
   A \subset B -> C \subset D -> commg_set A C \subset commg_set B D.
Proof. by move=> A B C D; exact: imset2S. Qed.

(* Groups (at last!) *)

Definition group_set A := (1 \in A) && (A * A \subset A).

Lemma group_setP : forall A,
  reflect (1 \in A /\ {in A & A, forall x y, x * y \in A}) (group_set A).
Proof.
move=> A; apply: (iffP andP) => [] [A1 AM]; split=> {A1}//.
  by move=> x y Ax Ay; apply: (subsetP AM); rewrite mem_mulg.
apply/subsetP=> z; case/mulsgP=> [x y Ax Ay ->]; exact: AM.
Qed.

Structure group : Type := Group {
  set_of_group :> GroupSet.sort gT;
  _ : group_set set_of_group
}.

Definition group_for of phant gT : predArgType := group.
Notation Local groupT := (group_for (Phant gT)).
Identity Coercion group_for_group : group_for >-> group.

Canonical Structure group_subType := SubType set_of_group group_rect vrefl.
Canonical Structure group_eqType := Eval hnf in [subEqType for set_of_group].
Canonical Structure group_finType := Eval hnf in [finType of group by :>].
Canonical Structure group_subFinType := Eval hnf in [subFinType of group].

(* No predType or baseFinGroupType structures, as these would hide the *)
(* group-to-set coercion and thus spoil unification.                  *)

Canonical Structure group_for_subType := Eval hnf in [subType of groupT].
Canonical Structure group_for_eqType := Eval hnf in [eqType of groupT].
Canonical Structure group_for_finType := Eval hnf in [finType of groupT].
Canonical Structure group_for_subFinType := Eval hnf in [subFinType of groupT].

Lemma group_inj : injective set_of_group. Proof. exact: val_inj. Qed.
Lemma groupP : forall G : groupT, group_set G. Proof. by case. Qed.

Lemma group_set_unit : group_set 1.
Proof. by rewrite /group_set set11 mulg1 subset_refl. Qed.

Canonical Structure unit_group := Group group_set_unit.
Canonical Structure set1_group := @Group [set 1] group_set_unit.

Lemma group_setT : group_set setT.
Proof. apply/group_setP; split=> [|x y _ _]; exact: in_setT. Qed.

Canonical Structure setT_group := Group group_setT.

Definition setT_group_for of phant gT := setT_group.

(* Trivial group predicate and product remainder functions *)

Definition trivg A := A \subset unit_group.
Definition remgl A B x := repr (A :&: x *: B).
Definition remgr A B x := repr (A :&: B :* x).

(* These definition come early so we can establish the Notation. *)
Definition generated A := \bigcap_(G : groupT | A \subset G) G.
Definition cycle_of x := generated [set x].
Definition mulgen A B := generated (A :|: B).
Definition commutator A B := generated (commg_set A B).

End SmulProp.

Implicit Arguments mulsgP [gT A B x].
Implicit Arguments lcosetP [gT A x y].
Implicit Arguments lcosetsP [gT A B C].
Implicit Arguments rcosetP [gT A x y].
Implicit Arguments rcosetsP [gT A B C].
Implicit Arguments group_setP [gT A].
Prenex Implicits group_set trivg remgl remgr.
Prenex Implicits mulsgP lcosetP lcosetsP rcosetP rcosetsP group_setP.

Arguments Scope commutator [_ group_scope group_scope].
Arguments Scope mulgen [_ group_scope group_scope].
Arguments Scope generated [_ group_scope].

Notation "{ 'group' gT }" := (group_for (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.

Notation "[ 'group' 'of' G ]" :=
  (match {G%g as group _} as s return [type of @Group _ for s] -> _ with
  | Group _ gP => fun k => k gP end
  (@Group _ G%g)) (at level 0, only parsing) : form_scope.

Bind Scope subgroup_scope with group.
Bind Scope subgroup_scope with group_for.
Notation "1" := (unit_group _) : subgroup_scope.
Notation "[ 'setT' ]" := (setT_group _)
  (at level 0, format "[ 'setT' ]") : subgroup_scope.
Notation "[ 'setT' gT ]" := (setT_group_for (Phant gT))
  (at level 0, format "[ 'setT'  gT ]") : subgroup_scope.

Notation "<< A >>"  := (generated A)
 (at level 0, format "<< A >>") : group_scope.

Notation "A <*> B" := (mulgen A B) (at level 40) : group_scope.

Notation "[ ~: A1 , A2 , .. , An ]" := (commutator .. (commutator A1 A2) .. An)
  (at level 0,
  format "[ ~: '['  A1 , '/'  A2 , '/'  .. , '/'  An ']' ]") : group_scope.

Section GroupProp.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types A B C D : sT.
Implicit Types x y z : gT.
Implicit Types G H K : {group gT}.

Section OneGroup.

Variable G : {group gT}.

Lemma valG : val G = G. Proof. by []. Qed.

(* Non-triviality. *)

Lemma group1 : 1 \in G. Proof. by case/group_setP: (valP G). Qed.
Hint Resolve group1.

(* Loads of silly variants to placate the incompleteness of trivial. *)
(* An alternative would be to upgrade done, pending better support   *)
(* in the ssreflect ML code.                                         *)
Notation gTr := (FinGroup.sort gT).
Notation Gcl := (pred_of_set G : pred gTr).
Lemma group1_class1 : (1 : gTr) \in G. Proof. by []. Qed.
Lemma group1_class2 : 1 \in Gcl. Proof. by []. Qed.
Lemma group1_class12 : (1 : gTr) \in Gcl. Proof. by []. Qed.
Lemma group1_eqType : (1 : gT : eqType) \in G. Proof. by []. Qed.
Lemma group1_finType : (1 : gT : finType) \in G. Proof. by []. Qed.

Lemma sub1G : 1%G \subset G. Proof. by rewrite sub1set. Qed.

Lemma mem_repr_group : repr G \in G. Proof. exact: mem_repr group1. Qed.

Lemma pos_card_group : 0 < #|G|.
Proof. by rewrite lt0n; apply/existsP; exists (1 : gT). Qed.

Lemma trivgP : reflect (G = 1%G) (trivg G).
Proof. by rewrite -[trivg G]andbT -sub1G -eqset_sub; exact: eqP. Qed.

Lemma trivg_card : trivg G = (#|G| <= 1).
Proof.
by rewrite (sameP trivgP eqP) eq_sym [_ == _]eqset_sub_card cards1 sub1G.
Qed.

(* Inclusion and product. *)

Lemma mulG_subl : forall A, A \subset A * G.
Proof. move=> A; exact: mulg_subl group1. Qed.

Lemma mulG_subr : forall A, A \subset G * A.
Proof. move=> A; exact: mulg_subr group1. Qed.

Lemma mulGid : G * G = G.
Proof.
by apply/eqP; rewrite eqset_sub mulG_subr andbT; case/andP: (valP G).
Qed.

Lemma mulGS : forall A B, (G * A \subset G * B) = (A \subset G * B).
Proof.
move=> A B; apply/idP/idP; first exact: subset_trans (mulG_subr A).
by move/(mulgS G); rewrite mulgA mulGid.
Qed.

Lemma mulSG : forall A B, (A * G \subset B * G) = (A \subset B * G).
Proof.
move=> A B; apply/idP/idP; first exact: subset_trans (mulG_subl A).
by move/(mulSg G); rewrite -mulgA mulGid.
Qed.

(* Membership lemmas *)

Lemma groupM : forall x y, x \in G -> y \in G -> x * y \in G.
Proof. by case/group_setP: (valP G). Qed.

Lemma groupX : forall x n, x \in G -> x ^+ n \in G.
Proof. by move => x n Gx; elim: n => [|n IHn]; rewrite (group1, groupM). Qed.

Lemma groupVr : forall x, x \in G -> x^-1 \in G.
Proof. by move=> x Gx; rewrite -(finv_f (mulg_injl x) x^-1) mulgV groupX. Qed.

Lemma groupVl : forall x, x^-1 \in G -> x \in G.
Proof. by move=> x; move/groupVr; rewrite invgK. Qed.

Lemma groupV : forall x, (x^-1 \in G) = (x \in G).
Proof. by move=> x; apply/idP/idP; [exact: groupVl | exact: groupVr]. Qed.

Lemma groupMl : forall x y, x \in G -> (x * y \in G) = (y \in G).
Proof.
move=> x y Gx; apply/idP/idP=> Gy; last exact: groupM.
rewrite -(mulKg x y); exact: groupM (groupVr _) _.
Qed.

Lemma groupMr : forall x y, x \in G -> (y * x \in G) = (y \in G).
Proof. by move=> x y Gx; rewrite -[_ \in G]groupV invMg groupMl groupV. Qed.

Definition in_group := (group1, groupV, (groupMl, groupX)).

Lemma groupJ : forall x y, x \in G -> y \in G -> x ^ y \in G.
Proof. by move=> x y Gx Gy; rewrite !in_group. Qed.

Lemma groupJr : forall x y, y \in G -> (x ^ y \in G) = (x \in G).
Proof. by move=> x y Gy; rewrite groupMl (groupMr, groupV). Qed.

Lemma groupR : forall x y, x \in G -> y \in G -> [~ x, y] \in G.
Proof. by move=> x y Gx Gy; rewrite !in_group. Qed.

(* Inverse is an anti-morphism. *)

Lemma invGid : G^-1 = G. Proof. by apply/setP=> x; rewrite inE groupV. Qed.

Lemma invg_lcoset : forall x, (x *: G)^-1 = G :* x^-1.
Proof. by move=> x; rewrite invMg invGid invg_set1. Qed.

Lemma invg_rcoset : forall x, (G :* x)^-1 = x^-1 *: G.
Proof. by move=> x; rewrite invMg invGid invg_set1. Qed.

Lemma memV_lcosetV : forall x y, (y^-1 \in x^-1 *: G) = (y \in G :* x).
Proof. by move=> x y; rewrite -invg_rcoset memV_invg. Qed.

Lemma memV_rcosetV : forall x y, (y^-1 \in G :* x^-1) = (y \in x *: G).
Proof. by move=> x y; rewrite -invg_lcoset memV_invg. Qed.

(* Product idempotence *)

Lemma mulSgGid : forall A x, x \in A -> A \subset G -> A * G = G.
Proof.
move=> A x Ax sAG; apply/eqP; rewrite eqset_sub -{2}mulGid mulSg //=.
apply/subsetP=> y Gy; rewrite -(mulKVg x y) mem_mulg // groupMr // groupV.
exact: (subsetP sAG).
Qed.

Lemma mulGSgid : forall A x, x \in A -> A \subset G -> G * A = G.
Proof.
move=> A x; rewrite -memV_invg -invSg invGid => Ax sAG.
by apply: invg_inj; rewrite invMg invGid (mulSgGid Ax).
Qed.

(* Left cosets *)

Lemma lcoset_refl : forall x, x \in x *: G.
Proof. by move=> x; rewrite mem_lcoset mulVg group1. Qed.

Lemma lcoset_sym : forall x y, (x \in y *: G) = (y \in x *: G).
Proof. by move=> x y; rewrite !mem_lcoset -groupV invMg invgK. Qed.

Lemma lcoset_trans1 : forall x y, x \in y *: G -> x *: G = y *: G.
Proof.
move=> x y Gyx; apply/setP=> u; rewrite !mem_lcoset in Gyx *.
by rewrite -{2}(mulKVg x u) mulgA (groupMl _ Gyx).
Qed.

Lemma lcoset_trans1r : forall x y z, 
  x \in y *: G -> (x \in z *: G) = (y \in z *: G).
Proof. by move=> x y z Gyx; rewrite -2!(lcoset_sym z) (lcoset_trans1 Gyx). Qed.

Lemma lcoset_trans : forall x y z,
  x \in y *: G -> y \in z *: G -> x \in z *: G.
Proof. by move=> x y z; move/lcoset_trans1r->. Qed.

Lemma lcoset_id : forall x, x \in G -> x *: G = G.
Proof. move=> x; rewrite -{-2}(mul1g G); exact: lcoset_trans1. Qed.

(* Right cosets, with an elimination form for repr. *)

Lemma rcoset_refl : forall x, x \in G :* x.
Proof. by move=> x; rewrite mem_rcoset mulgV group1. Qed.

Lemma rcoset_sym : forall x y, (x \in G :* y) = (y \in G :* x).
Proof. by move=> x y; rewrite -!memV_lcosetV lcoset_sym. Qed.

Lemma rcoset_trans1 : forall x y, x \in G :* y -> G :* x = G :* y.
Proof.
move=> x y Gyx; apply: invg_inj; rewrite !invg_rcoset.
by apply: lcoset_trans1; rewrite memV_lcosetV.
Qed.

Lemma rcoset_trans1r : forall x y z, 
  x \in G :* y -> (x \in G :* z) = (y \in G :* z).
Proof. by move=> x y z Gyx; rewrite -2!(rcoset_sym z) (rcoset_trans1 Gyx). Qed.

Lemma rcoset_trans : forall x y z,
  y \in G :* x -> z \in G :* y -> z \in G :* x.
Proof. by move=> x y z; move/rcoset_trans1->. Qed.

Lemma rcoset_id : forall x, x \in G -> G :* x = G.
Proof. move=> x; rewrite -{-2}(mulg1 G); exact: rcoset_trans1. Qed.

(* Elimination form. *)

CoInductive rcoset_repr_spec x : gT -> Type :=
  RcosetReprSpec g : g \in G -> rcoset_repr_spec x (g * x).

Lemma mem_repr_rcoset : forall x, repr (G :* x) \in G :* x.
Proof. move=> x; exact: mem_repr (rcoset_refl x). Qed.

(* This form sometimes fails because ssreflect 1.1 delegates matching to the *)
(* (weaker) primitive Coq algorithm for general (co)inductive type families. *)
Lemma repr_rcosetP : forall x, rcoset_repr_spec x (repr (G :* x)).
Proof.
move=> x; rewrite -[repr _](mulgKV x).
by split; rewrite -mem_rcoset mem_repr_rcoset.
Qed.

Lemma rcoset_repr : forall x, G :* (repr (G :* x)) = G :* x.
Proof.
move=> x; apply: rcoset_trans1; exact: mem_repr (rcoset_refl x).
Qed.

(* Coset spaces. *)

Lemma mem_lcosets : forall A x, (x *: G \in lcosets G A) = (x \in A * G).
Proof.
move=> A x; apply/imsetP/mulsgP=> [[a Aa eqxaG] | [a g Aa Gg ->{x}]].
  exists a (a^-1 * x); rewrite ?mulKVg //.
  by rewrite -mem_lcoset -lcosetE -eqxaG lcoset_refl.
by exists a; rewrite // lcosetM lcosetE lcoset_id.
Qed.

Lemma mem_rcosets : forall A x, (G :* x \in rcosets G A) = (x \in G * A).
Proof.
move=> A x; rewrite -memV_invg invMg invGid -mem_lcosets.
by rewrite -{4}invGid lcosets_invg inE invg_lcoset invgK.
Qed.

(* Conjugates. *)

Lemma group_set_conjG : forall x, group_set (G :^ x).
Proof.
move=> x; apply/group_setP; split=> [|y z]; rewrite !mem_conjg.
  by rewrite conj1g group1.
rewrite conjMg; exact: groupM.
Qed.

Canonical Structure conjG_group x := Group (group_set_conjG x).

Lemma conjGid : {in G, normal G}.
Proof. by move=> x Gx; apply/setP=> y; rewrite mem_conjg groupJr ?groupV. Qed.

(* Classes *)

Lemma class1G : 1 ^: G = 1. Proof. exact: class1g group1. Qed.

Lemma classGidl : forall x y, y \in G -> (x ^ y) ^: G = x ^: G.
Proof. by move=> x y Gy; rewrite -classg_lcoset lcoset_id. Qed.

Lemma classGidr : forall x, {in G, normal (x ^: G)}.
Proof. by move=> x y Gy; rewrite -classg_rcoset rcoset_id. Qed.

Lemma class_supportGidl : forall A x,
  x \in G -> class_support (A :^ x) G = class_support A G.
Proof.
by move=> A x Gx; rewrite -class_support_set1r -class_supportM lcoset_id.
Qed.

Lemma class_supportGidr : forall A, {in G, normal (class_support A G)}.
Proof.
by move=> A x Gx; rewrite -class_support_set1r -class_supportM rcoset_id.
Qed.

(* Subgroup Type construction. *)

Notation Local subgT := {x | x \in G}.
Definition subgroup_unit : subgT := Sub 1 group1.
Definition subgroup_inv (u : subgT) : subgT := Sub _^-1 (groupVr (valP u)).
Definition subgroup_mul (u v : subgT) : subgT :=
  Sub (_ * _) (groupM (valP u) (valP v)).
Lemma subgroup_unitP : left_unit subgroup_unit subgroup_mul.
Proof. move=> u; apply: val_inj; exact: mul1g. Qed.
Lemma subgroup_invP : left_inverse subgroup_unit subgroup_inv subgroup_mul.
Proof. move=> u; apply: val_inj; exact: mulVg. Qed.
Lemma subgroup_mulP : associative subgroup_mul.
Proof. move=> u v w; apply: val_inj; exact: mulgA. Qed.

Canonical Structure subBaseFinGroupType :=
  [baseFinGroupType of subgT by subgroup_mulP, subgroup_unitP & subgroup_invP].
Canonical Structure subFinGroupType := FinGroupType subgroup_invP.

End OneGroup.

Hint Resolve group1.

Lemma invMG : forall G H, (G * H)^-1 = H * G.
Proof. by move=> G H; rewrite invMg !invGid. Qed.

Lemma mulSGid : forall G H, H \subset G -> H * G = G.
Proof. move=> G H; exact: mulSgGid (group1 H). Qed.

Lemma mulGSid : forall G H, H \subset G -> G * H = G.
Proof. move=> G H; exact: mulGSgid (group1 H). Qed.

Lemma comm_group_setP : forall G H, reflect (commute G H) (group_set (G * H)).
Proof.
move=> G H; rewrite /group_set (subsetP (mulG_subl _ _)) ?group1 // andbC.
have <-: #|G * H| <= #|H * G| by rewrite -invMG card_invg.
rewrite -mulgA mulGS mulgA mulSG -eqset_sub_card eq_sym; exact: eqP.
Qed.

Lemma card_lcosets : forall G H, #|lcosets H G| = indexg H G.
Proof.
move=> G H; rewrite -[indexg H G](card_preimset _ invg_inj).
by rewrite -lcosets_invg !invGid.
Qed.

(* Group Modularity equations *)

Lemma group_modl : forall A B G, A \subset G -> A * (B :&: G) = A * B :&: G.
Proof.
move=> A B G sAG; apply/eqP; rewrite eqset_sub subsetI mulgS ?subsetIl //.
rewrite -{2}mulGid mulgSS ?subsetIr //; apply/subsetP => x.
case/setIP; case/mulsgP=> a b Aa Bb ->{x} Gab; rewrite mem_mulg // inE Bb.
by rewrite -(groupMl _ (subsetP sAG _ Aa)).
Qed.

Lemma group_modr : forall A B G, B \subset G -> (G :&: A) * B = G :&: A * B.
Proof.
move=> A B G sBG; apply: invg_inj; rewrite !(invMg, invIg) invGid !(setIC G).
by rewrite group_modl // -invGid invSg.
Qed.

(* Properties of the remainders *)

Lemma remGl_id : forall A G x y, y \in G -> remgl A G (x * y) = remgl A G x.
Proof. by move=> A G x y Gy; rewrite {1}/remgl lcosetM lcoset_id. Qed.

Lemma mem_remGl : forall A G x, (remgl A G x \in A :&: x *: G) = (x \in A * G).
Proof.
move=> A G x; set y := remgl A G x; apply/idP/mulsgP=> [|[a g Aa Gg x_ag]].
  rewrite inE lcoset_sym mem_lcoset; case/andP=> Ay Gy'x.
  by exists y (y^-1 * x); rewrite ?mulKVg.
by apply: (mem_repr a); rewrite inE Aa lcoset_sym mem_lcoset x_ag mulKg.
Qed.

Lemma remGr_id : forall A G x y, y \in G -> remgr A G (y * x) = remgr A G x.
Proof. by move=> A G x y Gy; rewrite {1}/remgr rcosetM rcoset_id. Qed.

Lemma mem_remGr : forall A G x, (remgr A G x \in A :&: G :* x) = (x \in G * A).
Proof.
move=> A G x; set y := _ x; apply/idP/mulsgP=> [|[g a Gg Aa x_ga]].
  rewrite inE rcoset_sym mem_rcoset; case/andP=> Ay Gxy'.
  by exists (x * y^-1) y; rewrite ?mulgKV.
by apply: (mem_repr a); rewrite inE Aa rcoset_sym mem_rcoset x_ga mulgK.
Qed.

End GroupProp.

Hint Resolve group1 group1_class1 group1_class12 group1_class12.
Hint Resolve group1_eqType group1_finType pos_card_group.

Notation "G :^ x" := (conjG_group G x) : subgroup_scope.

Section LaGrange.

Variables (gT : finGroupType) (H G : {group gT}).
Notation sT := {set gT}.

Hypothesis sHG : H \subset G.

Theorem LaGrange : (#|H| * indexg H G)%N = #|G|.
Proof.
pose f x := (x * (repr (H :* x))^-1, H :* x).
rewrite -cardX -(@on_card_preimset _ _ f); first apply: eq_card => x.
  rewrite !inE /= -mem_rcoset rcoset_sym (mem_repr x) ?rcoset_refl //=.
  by rewrite mem_rcosets mulSGid.
exists (fun hHx => hHx.1 * repr hHx.2 : gT) => [x _ | ]; first exact: mulgKV.
case=> h A; case/andP=> /= Hh; case/imsetP=> x _ ->{A}.
by rewrite rcosetE /f rcosetM (rcoset_id Hh) rcoset_repr mulgK.
Qed.

Lemma group_dvdn : #|H| %| #|G|.
Proof. by apply/dvdnP; exists (indexg H G); rewrite mulnC LaGrange. Qed.

Lemma group_divn : #|G| %/ #|H| = indexg H G.
Proof. by rewrite -LaGrange // divn_mulr. Qed.

End LaGrange.

Section GroupInter.

Open Scope group_scope.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Section Binary.

Variables G H : {group gT}.

Lemma group_setI : group_set (G :&: H).
Proof.
apply/group_setP; split=> [|x y]; rewrite !inE ?group1 //.
by case/andP=> Gx Hx; rewrite !groupMl.
Qed.

Canonical Structure setI_group := Group group_setI.

Lemma card_mulG : (#|G * H|%g * #|G :&: H| = #|G| * #|H|)%N.
Proof.
pose f u := let: (g, h) := u in let m := g * h in (m, remgr H G m * h^-1).
rewrite -!cardX -(@on_card_preimset _ _ f); last first.
  pose f' md := let h := md.2^-1 * remgr H G md.1 in (md.1 * h^-1, h).
  by exists f'; case=> *; rewrite /f' /= !gnorm.
apply: eq_card => [] [g h]; rewrite !inE /=; symmetry.
case GHgh: (g * h \in G * H); last first.
  by apply/andP=> [] [Gg Hh]; rewrite mem_mulg in GHgh.
rewrite -mem_remGr in GHgh; case/setIP: GHgh; move: (remgr H G _) => z Hz Gghz.
rewrite /= inE (groupMl _ Hz) groupV -{1}(mulgKV g (z * _)) groupMl //.
by rewrite -mulgA -invMg -mem_rcoset.
Qed.

Lemma card_mulG_trivP :
  reflect (#|G * H| = (#|G| * #|H|)%N) (trivg (G :&: H)).
Proof.
rewrite trivg_card leq_eqVlt ltnNge pos_card_group orbF eq_sym /=.
suff: #|G * H| > 0 by move/eqn_pmul2l <-; rewrite muln1 card_mulG; exact: eqP.
apply: leq_trans (pos_card_group H) (subset_leq_card _); exact: mulG_subr.
Qed.

Lemma coprime_trivg : coprime #|G| #|H| -> trivg (G :&: H).
Proof.
move/eqnP=> coGH; rewrite trivg_card dvdn_leq // -{}coGH.
by rewrite dvdn_gcd ?group_dvdn ?(subsetIl, subsetIr).
Qed.

Lemma coprime_card_mulG : coprime #|G| #|H| -> #|G * H| = (#|G| * #|H|)%N.
Proof. by move/coprime_trivg; move/card_mulG_trivP. Qed.

End Binary.

Section Nary.

Variables (I : finType) (P : pred I) (F : I -> {group gT}).

Lemma group_set_bigcap : group_set (\bigcap_(i | P i) F i).
Proof.
apply: (@big_prop _ [eta group_set])=> [|G H gG gH|G _]; try exact: groupP.
exact: (@group_setI (Group gG) (Group gH)).
Qed.

Canonical Structure bigcap_group := Group group_set_bigcap.

End Nary.

Canonical Structure generated_group A := Eval hnf in [group of <<A>>].

Canonical Structure commutator_group A B := Eval hnf in [group of [~: A, B]].

Canonical Structure mulgen_group A B := Eval hnf in [group of A <*> B].

End GroupInter.

Definition mulGen (gT : finGroupType) (G H : {group gT}) :=
  nosimpl (mulgen_group G H).

Arguments Scope generated_group [_ group_scope].

Notation "G :&: H" := (setI_group G H) : subgroup_scope.
Notation "<< A >>"  := (generated_group A) : subgroup_scope.
Notation "[ ~: A1 , A2 , .. , An ]" :=
  (commutator_group .. (commutator_group A1 A2) .. An) : subgroup_scope.
Notation "G <*> H" := (mulGen G H) : subgroup_scope.
Prenex Implicits mulGen.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[mulGen/1%G]_(<- r | P%B) F%G) : subgroup_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[mulGen/1%G]_(i <- r | P%B) F%G) : subgroup_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[mulGen/1%G]_(i <- r) F%G) : subgroup_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[mulGen/1%G]_(m <= i < n | P%B) F%G) : subgroup_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[mulGen/1%G]_(m <= i < n) F%G) : subgroup_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[mulGen/1%G]_(i | P%B) F%G) : subgroup_scope.
Notation "\prod_ ( i ) F" :=
  (\big[mulGen/1%G]_(i) F%G) : subgroup_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[mulGen/1%G]_(i : t | P%B) F%G) (only parsing) : subgroup_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[mulGen/1%G]_(i : t) F%G) (only parsing) : subgroup_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[mulGen/1%G]_(i < n | P%B) F%G) : subgroup_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[mulGen/1%G]_(i < n) F%G) : subgroup_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[mulGen/1%G]_(i \in A | P%B) F%G) : subgroup_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[mulGen/1%G]_(i \in A) F%G) : subgroup_scope.

Section GeneratedGroup.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types x y z : gT.
Implicit Types A B C : sT.
Implicit Types G H K : {group gT}.

Lemma sub_geng : forall A, A \subset <<A>>.
Proof. move=> A; exact/bigcap_inP. Qed.

Lemma mem_geng : forall x A, x \in A -> x \in <<A>>.
Proof. move=> x A; exact: subsetP (sub_geng A) x. Qed.

Lemma generatedP : forall x A,
  reflect (forall G, A \subset G -> x \in G) (x \in <<A>>).
Proof. move=> x A; exact: bigcapP. Qed.

Lemma gen_subG : forall A G, (<<A>> \subset G) = (A \subset G).
Proof.
move=> A G; apply/idP/idP=> [|sAG]; first exact: subset_trans (sub_geng A).
by apply/subsetP=> x; move/generatedP; apply.
Qed.

Lemma genGid : forall G, <<G>> = G.
Proof.
by move=> G; apply/eqP; rewrite eqset_sub gen_subG sub_geng andbT. 
Qed.

Lemma genSg : forall A B, A \subset B -> <<A>> \subset <<B>>.
Proof.
by move=> A B sAB; rewrite gen_subG (subset_trans _ (sub_geng B)).
Qed.

Lemma gengg : forall A, << <<A>> >> = <<A>>.
Proof. move=> A; exact: genGid. Qed.

Lemma genUgen : forall A B, <<A :|: <<B>> >> = <<A :|: B>>.
Proof.
move=> A B; apply/eqP; rewrite eqset_sub gen_subG subUset gen_subG /=.
by rewrite -subUset sub_geng genSg // setUS // sub_geng.
Qed.

Lemma gen_genU : forall A B, << <<A>> :|: B>> = <<A :|: B>>.
Proof. by move=> A B; rewrite -!(setUC B) genUgen. Qed.

Lemma gen0 : <<@set0 gT>> = 1.
Proof. by apply/eqP; rewrite eqset_sub sub1G gen_subG sub0set. Qed.

Lemma genD : forall A B, A \subset <<A :\: B>> -> <<A :\: B>> = <<A>>.
Proof.
by move=> A B sAB; apply/eqP; rewrite eqset_sub genSg (subsetDl, gen_subG).
Qed.

Lemma genDU : forall A B C,
  A \subset C -> <<C :\: A>> = <<B>> -> <<A :|: B>> = <<C>>.
Proof.
move=> A B C sAC; rewrite -genUgen => <- {B}; rewrite genUgen; congr <<_>>.
by apply/eqP; rewrite setDE setUIr setUCr setIT eqsetUr.
Qed.

Lemma genD1 : forall A x, x \in <<A :\ x>> -> <<A :\ x>> = <<A>>.
Proof.
move=> A x gA'x; apply/eqP; rewrite eqset_sub genSg; last first.
  by rewrite setD1E subsetIl.
rewrite gen_subG; apply/subsetP=> y Ay.
by case: (y =P x) => [-> //|]; move/eqP=> nyx; rewrite mem_geng // inE nyx.
Qed.

Lemma mulgenE : forall A B, A <*> B = <<A :|: B>>. Proof. by []. Qed.

Lemma mulGenE : forall G H, (G <*> H)%G = G <*> H :> sT. Proof. by []. Qed.

Lemma mulgen_idl : forall A B, <<A>> <*> B = A <*> B.
Proof. exact: gen_genU. Qed.

Lemma mulgen_idr : forall A B, A <*> <<B>> = A <*> B.
Proof. exact: genUgen. Qed.

Notation mulgenT := (@mulgen gT).
Notation mulGenT := (@mulGen gT).

Lemma mulgenC : commutative mulgenT.
Proof. by move=> A B; rewrite /mulgen setUC. Qed.

Lemma mulgenA : associative mulgenT.
Proof. by move=> A B C; rewrite mulgen_idl mulgen_idr /mulgen setUA. Qed.

Lemma mulgen1G : forall G, 1 <*> G = G.
Proof. by move=> G; rewrite -gen0 mulgen_idl /mulgen set0U genGid. Qed.

Lemma mulgenG1 : forall G, G <*> 1 = G.
Proof. by move=> G; rewrite mulgenC mulgen1G. Qed.

Lemma genM_mulgen : forall G H, <<G * H>> = G <*> H.
Proof.
move=> G H; apply/eqP; rewrite eqset_sub gen_subG /= -{1}[G <*> H]mulGid.
rewrite genSg; last by rewrite subUset mulG_subl mulG_subr.
by rewrite mulgSS ?(subset_trans _ (sub_geng _), subsetUl, subsetUr).
Qed.

Lemma comm_mulgenE : forall G H, commute G H -> G <*> H = G * H.
Proof.
move=> G H; move/comm_group_setP=> gGH; rewrite -genM_mulgen.
exact: (genGid (Group gGH)).
Qed.

Lemma mulGenC : commutative mulGenT.
Proof. by move=> G H; apply: val_inj; exact: mulgenC. Qed.

Lemma mulGenA : associative mulGenT.
Proof. by move=> G H K; apply: val_inj; exact: mulgenA. Qed.

Lemma mulGen1G : left_unit 1%G mulGenT.
Proof. by move=> G; apply: val_inj; exact: mulgen1G. Qed.

Lemma mulGenG1 : right_unit 1%G mulGenT.
Proof. by move=> G; apply: val_inj; exact: mulgenG1. Qed.

Canonical Structure mulGen_law := Monoid.Law mulGenA mulGen1G mulGenG1.
Canonical Structure mulGen_abelaw := Monoid.AbelianLaw mulGenC.

Lemma commG1P : forall A B, reflect {in A, central B} (trivg [~: A, B]).
Proof.
move=> A B; rewrite [trivg _]gen_subG.
apply: (iffP subsetP) => [cAB1 x Ax y By | cAB z].
  by apply/commgP; rewrite -in_set1 cAB1 // imset2_f_imp.
case/imset2P=> x y Ax Ay ->{z}; rewrite inE; apply/commgP; exact: cAB.
Qed.

End GeneratedGroup.

Implicit Arguments commG1P [gT A B].
Prenex Implicits commG1P.

Section Normaliser.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types x y z : gT.
Implicit Types A B C : sT.
Implicit Type G H K : {group gT}.

Lemma normgP : forall x A, reflect {for x, normal A} (x \in 'N(A)).
Proof.
move=> x A; suff ->: (x \in 'N(A)) = (A :^ x == A) by exact: eqP.
by rewrite eqset_sub_card card_conjg leqnn andbT inE.
Qed.

Implicit Arguments normgP [x A].

Lemma normg_conj : forall x A, x \in 'N(A) -> {for x, normal A}.
Proof. by move=> x A; move/normgP. Qed.

Lemma memJ_normg : forall x y A, x \in 'N(A) -> (y ^ x \in A) = (y \in A).
Proof. by move=> x y A Nx; rewrite -{1}(normgP Nx) memJ_conjg. Qed.

Lemma group_set_normaliser : forall A, group_set 'N(A).
Proof.
move=> A; apply/group_setP; split=> [|x y Nx Ny]; rewrite inE ?conjsg1 //.
by rewrite conjsgM !(normgP _).
Qed.

Canonical Structure normaliser_group A := Group (group_set_normaliser A).

Lemma normalP : forall A B, reflect {in A, normal B} (A \subset 'N(B)).
Proof.
move=> A B; apply: (iffP subsetP) => nBA x Ax; last by rewrite inE nBA //.
by apply/normgP; exact: nBA.
Qed.

Lemma normC : forall A B, A \subset 'N(B) -> commute A B.
Proof.
move=> A B; move/subsetP=> nBA; apply/setP => u.
apply/mulsgP/mulsgP=> [[x y Ax By] | [y x By Ax]] -> {u}.
  by exists (y ^ x^-1) x; rewrite -?conjgCV // memJ_normg // groupV nBA.
by exists x (y ^ x); rewrite -?conjgC // memJ_normg // nBA.
Qed.

Lemma normalC : forall A B, {in A, normal B} -> commute A B.
Proof. move=> A B; move/normalP; exact: normC. Qed.

Lemma normG : forall G, G \subset 'N(G).
Proof. move=> G; apply/normalP; exact: conjGid. Qed.

Lemma norm_mulgenE : forall G H, G \subset 'N(H) -> G <*> H = G * H.
Proof. by move=> G H; move/normC; move/comm_mulgenE. Qed.

Lemma normal_mulgenE : forall G H, {in G, normal H} -> G <*> H = G * H.
Proof. by move=> G H; move/normalC; move/comm_mulgenE. Qed.

Lemma norm_rlcoset : forall G x, x \in 'N(G) -> G :* x = x *: G.
Proof. by move=> G x; rewrite -sub1set; move/normC. Qed.

Lemma rcoset_mul : forall G x y,
  x \in 'N(G) -> (G :* x) * (G :* y) = G :* (x * y).
Proof.
move=> G x y; move/norm_rlcoset=> GxxG.
by rewrite mulgA -(mulgA _ _ G) -GxxG mulgA mulGid -mulgA mulg_set1.
Qed.

Lemma normalsubP : forall A B,
  reflect (A \subset B /\ {in B, normal A}) (A <| B).
Proof. by move=> A B; apply: (iffP andP)=> [] [sAB]; move/normalP. Qed.

Lemma centg1P : forall x y, reflect (commute x y) (x \in 'C[y]).
Proof.
move=> x y; rewrite inE conjg_set1 sub1set inE (sameP eqP conjg_fixP).
rewrite commg1_sym; exact: commgP.
Qed.

Canonical Structure centraliser_group A := Eval hnf in [group of 'C(A)].

Lemma centg_set1 : forall x, 'C([set x]) = 'C[x].
Proof. by move=> x; apply: big_pred1 => y /=; rewrite inE. Qed.

Lemma centgP : forall A x, reflect {for x, central A} (x \in 'C(A)).
Proof.
by move=> A x; apply: (iffP (bigcapP _ _ _)) => cxA y; move/cxA; move/centg1P.
Qed.

Lemma centralP : forall A B, reflect {in A, central B} (A \subset 'C(B)).
Proof.
by move=> A B; apply: (iffP subsetP) => cAB x; move/cAB; move/centgP.
Qed.

Lemma central_normal : forall x A, {for x, central A} -> {for x, normal A}.
Proof.
move=> x A Cx; apply/normgP; rewrite inE; apply/subsetP=> yx.
case/imsetP=> y Ay ->{yx}; rewrite (conjg_fixP _) // commg1_sym.
apply/commgP; exact: Cx.
Qed.

Lemma in_central_normal : forall A B, {in A, central B} -> {in A, normal B}.
Proof. move=> A B cAB x; move/cAB; exact: central_normal. Qed.

Lemma sub_centg : forall A, 'C(A) \subset 'N(A).
Proof.
by move=> A; apply/subsetP=> x; move/centgP; move/central_normal; move/normgP.
Qed.

Lemma norm_centg : forall A, 'N(A) \subset 'N('C(A)).
Proof.
move=> A; apply/subsetP=> x; move/normgP=> nxA; rewrite inE.
apply/subsetP=> zx; case/imsetP=> z; move/centgP=> czA ->{zx}.
apply/centgP=> y Ay; apply/commgP; apply/conjg_fixP.
rewrite -conjgM (conjgCV x y) conjgM (@conjg_fixP _ z _ _) //.
by apply/commgP; apply: czA; rewrite -mem_conjg nxA.
Qed.

Lemma normsub_centg : forall A, 'C(A) <| 'N(A).
Proof. by move=> A; rewrite /(_ <| _) sub_centg norm_centg. Qed.

Lemma central_mulgenE : forall H1 H2,
  {in H1, central H2} -> H1 <*> H2 = H1 * H2.
Proof. move=> H1 H2; move/in_central_normal; exact: normal_mulgenE. Qed.

Lemma centralC : forall A B, (A \subset 'C(B)) = (B \subset 'C(A)).
Proof.
by move=> A B; apply/centralP/centralP=> cAB x ? y ?; rewrite /commute -cAB.
Qed.

Lemma central_sym : forall A B, {in A, central B} -> {in B, central A}.
Proof. by move=> A B; move/centralP; rewrite centralC; move/centralP. Qed.

End Normaliser.

Implicit Arguments normgP [gT x A].
Implicit Arguments centgP [gT x A].
Implicit Arguments normalP [gT A B].
Implicit Arguments centg1P [gT x y].
Implicit Arguments normalsubP [gT A B].
Implicit Arguments centralP [gT A B].
Prenex Implicits normgP normalP centg1P normalsubP centgP centralP.

Arguments Scope normaliser_group [_ group_scope].
Arguments Scope centraliser_group [_ group_scope].

Notation "''N' ( A )" := (normaliser_group A) : subgroup_scope.
Notation "''C' ( A )" := (centraliser_group A) : subgroup_scope.
Notation "''C' [ x ]" := ('N([set x%g]))%G : subgroup_scope.
Notation "'N_' ( G ) ( A )" := (G :&: 'N(A))%G : subgroup_scope.
Notation "'C_' ( G ) ( A )" := (G :&: 'C(A))%G : subgroup_scope.
Notation "'C_' ( H ) [ x ]" := (N_(H)([set x%g]))%G : subgroup_scope.

Section Maximal.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types A B : sT.

Definition maximal A B :=
  (A \subset B) &&
  (forallb K : {group gT},
    (A \subset K) && (K \subset B) ==> (A == K) || (K == B :> sT)).

Lemma maximalP : forall A B,
  reflect (A \subset B  /\ 
           forall K : {group gT},
             A \subset K -> K \subset B -> A = K \/ K = B :> sT) 
  (maximal A B).
Proof.
move=> A B; (apply: (iffP andP); case=> sHG maxH; split) => // [K sHK sKG|].
  by have:= (forallP maxH K); rewrite sHK sKG; case/orP; move/eqP; auto.
apply/forallP => K; apply/implyP; case/andP=> sHK sKG.
by case (maxH K) => // ->; rewrite eqxx ?orbT.
Qed.

End Maximal.

Section FrattiniDefs.

Variable gT : finGroupType.

Variable G : {group gT}.

Lemma maximal_existence : forall H : {group gT}, H \subset G -> 
  H = G \/ exists K : {group gT}, [/\ maximal K G , H \subset K & K != G].
Proof.
move=> H sHG; elim: {2}#|G| H sHG (leq_addr #|H| #|G|) => [|n IHn] H sHG.
  rewrite add0n leq_eqVlt ltnNge subset_leq_card // orbF; move/eqP=> eqHG.
  by left; apply: val_inj; apply/setP; exact/subset_cardP.
rewrite addSnnS => leGnH; case maxH: (maximal H G).
  by case: (H =P G); [left | move/eqP=> nHG; right; exists H].
move/idPn: maxH; rewrite negb_and sHG; case/existsP=> L.
rewrite negb_imply -andbA negb_orb; case/and4P=> sHL sLG nHL nLG; right.
case: {IHn}(IHn L sLG) => [|eqLG|[K [maxK sLK nKG]]]; first 1 last.
- by rewrite eqLG eqxx in nLG.
- exists K; split=> //; exact: subset_trans sLK.
apply: (leq_trans leGnH); rewrite leq_add2l ltn_neqAle subset_leq_card //.
rewrite andbT; apply: contra nHL; move/eqP=> eqHL.
by apply/eqP; apply/setP; exact/subset_cardP.
Qed.

Definition Frattini (A : {set gT}) := \bigcap_(H : {group gT} | maximal H A) H.

Canonical Structure Frattini_group A := Eval hnf in [group of Frattini A].

Lemma Frattini_sub : Frattini G \subset G.
Proof. 
rewrite [Frattini G](bigD1 G) ?subsetIl ?eqxx //. 
rewrite /maximal subset_refl andTb; apply/forallP=>x; apply/implyP.
by move/subset_eqP; move/setP->; rewrite eqxx.
Qed.

Lemma Frattini_strict_sub :  G = 1 :> {set gT} \/ Frattini G != G.
Proof.
case: (G =P 1 :> {set _}) => nG1; [by left | right].
rewrite eqset_sub Frattini_sub; apply/bigcap_inP=> sGmax.
have: [set 1] \subset G by rewrite sub1set group1.
case/maximal_existence=> [G1 | [K [Kmax _]]]; first by case nG1; rewrite -G1.
by rewrite -val_eqE eqset_sub sGmax //=; case/andP: Kmax => ->.
Qed.

End FrattiniDefs.

Section FrattiniProps.

Variable gT : finGroupType.

Lemma Frattini_not_gen : forall (G : {group gT}) (X : {set gT}),
  X \subset G -> (G \subset <<X>>) = (G  \subset << X :|: Frattini G >>).
Proof.
move=> G X sXG; apply/idP/idP=> [|sGXF].
  move/subset_trans; apply.
  apply/subsetP=>x; move/bigcapP=>Hx; apply/bigcapP=> i Hi.
  apply Hx; apply: (subset_trans _ Hi); exact: subsetUl.
have sXFG: X :|: Frattini G \subset G.
  by rewrite subUset sXG andTb Frattini_sub.
rewrite -gen_subG in sXG.
have [<- //=| [K [Kmax sHK nKG]]] := maximal_existence sXG.
rewrite gen_subG in sHK.
have: Frattini G \subset K by exact: bigcap_inf.
move/(conj sHK); move/andP; rewrite -subUset -gen_subG.
move/(subset_trans sGXF)=> sGK; case/maximalP: Kmax => sKG _.
by case/eqP: nKG; apply: val_inj; apply/setP; apply/subset_eqP; apply/andP.
Qed.

End FrattiniProps.
