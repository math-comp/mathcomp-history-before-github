(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import bigops.

(*****************************************************************************)
(*   The algebraic part of the Algebraic Hierarchy, as described in          *)
(*           "Packaging mathematical structures", TPHOLs09, by               *)
(*   Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence Rideau    *)
(*                                                                           *)
(* This file defines for each Structure (Zmodule, Ring, etc ...) its type,   *)
(* its packers and its canonical properties :                                *)
(*                                                                           *)
(*  * Zmodule                                                                *)
(*      zmodType        == type for Zmodule structure                        *)
(*      ZmodMixin       == builds the mixin containing the definition        *)
(*                         of a Zmodule                                      *)
(*      ZmodType M      == packs the mixin M to build a Zmodule of type      *)
(*                         zmodType. (The underlying type should have a      *)
(*                         choiceType canonical structure)                   *)
(*      0               == the additive identity element of a Zmodule        *)
(*      x + y           == the addition operation of a Zmodule               *)
(*      - x             == the opposite operation of a Zmodule               *)
(*      x - y           == the substraction operation of a Zmodule           *)
(*                      := x + - y                                           *)
(*      x +* n , x -* n == the generic multiplication by a nat               *)
(*      \sum_<range> e  == iterated sum for a Zmodule (cf bigops.v)          *)
(*      e`_i            == nth 0 e i, when e : seq M and M is a zmodType     *)
(*      ... and a many classical Lemmas on these Zmodule laws                *)
(*                                                                           *)
(*  * Ring                                                                   *)
(*      ringType      == type for ring structure                             *)
(*      RingMixin     == builds the mixin containing the definitions of a    *)
(*                       ring (the underlying type should have a zmodType    *)
(*                       structure)                                          *)
(*      RingType M    == packs the ring mixin M to build a ring              *)
(*      RevRingType T == repacks T to build the ring where the               *)
(*                       multiplicative law is reversed ( x *' y = y * x )   *)
(*      1             == the multiplicative identity element of a Ring       *)
(*      n%:R          == the ring image of a nat n (e.g., 1%:R := 1%R)       *)
(*      x * y         == the multiplication operation of a ring              *)
(*    \prod_<range> e == iterated product for a ring (cf bigops.v)           *)
(*      x ^+ y        == the exponentiation operation of a ring              *)
(*      GRing.comm x y <=> x and y commute, i.e., x * y = y * x              *)
(*                                                                           *)
(*  * Commutative Ring                                                       *)
(*      comRingType      == type for commutative ring structure              *)
(*      ComRingMixin     == builds the mixin containing the definitions of a *)
(*                          *non commutative* ring, but using                *)
(*                         commutative ring mixin mulC. (The underlying type *)
(*                         should have a Zmodule canonical structure)        *)
(*      ComRingType mulC == packs mulC to build a commutative ring.          *)
(*                          (The underlying type should have a ring          *)
(*                          canonical structure)                             *)
(*                                                                           *)
(*  * Unit Ring                                                              *)
(*      unitRingType   == type for unit ring structure                       *)
(*      UnitRingMixin  == builds the mixin containing the definitions        *)
(*                        of a unit ring. (The underlying type should        *)
(*                        have a ring canonical structure)                   *)
(*      UnitRingType M == packs the unit ring mixin M to build a unit ring   *)
(*      GRing.unit x   == x is a unit (i.e., has an inverse)                 *)
(*      x^-1           == the inversion operation element of a unit ring     *)
(*                        (returns x if is x is not an unit)                 *)
(*      x / y          := x * y^-1                                           *)
(*      x ^- n         := (x ^+ n)^-1                                        *)
(*                                                                           *)
(*  * Commutative Unit Ring                                                  *)
(*      comUnitRingType   == type for unit ring structure                    *)
(*      ComUnitRingMixin  == builds the mixin containing the definitions     *)
(*                           of a *non commutative unit ring*, but using     *)
(*                           the commutative property. (The underlying type  *)
(*                           should have a ring canonical structure)         *)
(*      ComUnitRingType M == packs the *unit ring mixin* M to build a unit   *)
(*                           ring. (The underlying type should have a        *)
(*                           commutative ring canonical structure)           *)
(*                                                                           *)
(*  * Integral Domain (integral, commutative, unit ring)                     *)
(*      idomainType       == type for integral domain structure              *)
(*      IdomainType M     == packs the idomain mixin M to build a integral   *)
(*                           domain. (The underlying type should have a      *)
(*                           commutative unit ring canonical structure)      *)
(*                                                                           *)
(*  * Field                                                                  *)
(*      fieldType         == type for field structure                        *)
(*      FieldUnitMixin    == builds a *non commutative unit ring* mixin,     *)
(*                           using some field properties. (The underlying    *)
(*                           type should have a *commutative ring* canonical *)
(*                           structure)                                      *)
(*      FieldMixin        == builds the field mixin. (The underlying type    *)
(*                           should have a *commutative ring* canonical      *)
(*                           structure)                                      *)
(*      FieldIdomainMixin == builds an *idomain* mixin, using a field mixin  *)
(*      FieldType M       == packs the field mixin M to build a field        *)
(*                           (The underlying type should have a              *)
(*                           integral domain canonical structure)            *)
(*                                                                           *)
(*  * Decidable Field                                                        *)
(*      decFieldType      == type for decidable field structure              *)
(*      DecFieldMixin     == builds the mixin containing the definitions of  *)
(*                           a decidable Field. (The underlying type should  *)
(*                           have a unit ring canonical structure)           *)
(*      DecFieldType M    == packs the decidable field mixin M to build a    *)
(*                           decidable field. (The underlying type should    *)
(*                           have a field canonical structure)               *)
(*      GRing.term R      == the type of formal expressions in a unit ring R *)
(*                           with formal variables 'X_i, i : nat             *)
(*      GRing.formula R   == the type of first order formulas over R         *)
(*      GRing.eval t e    == the value of term t with valuation e : seq R    *)
(*                           (e maps 'X_i to e`_i)                           *)
(*      GRing.holds f e   == the intuitionistic CiC interpretation of the    *)
(*                           formula f holds with valuation e                *)
(*      GRing.sat f e     == valuation e satisfies f                         *)
(*      GRing.sol f n     == a sequence e of size n such that e satisfies f, *)
(*                           if one exists, or nil if there is no such e     *)
(*                                                                           *)
(*  * Closed Field                                                           *)
(*      closedFieldType   == type for closed field structure                 *)
(*      ClosedFieldType M == packs the closed field mixin M to build a       *)
(*                           closed field. (The underlying type should have  *)
(*                           a decidable field canonical structure)          *)
(*                                                                           *)
(* The Lemmas about theses structures are all contained in GRing.Theory.     *)
(* Notations are defined in scope ring_scope (delimiter %R), except term and *)
(* formula notations, which are in term_scope (delimiter %T).                *)
(*                                                                           *)
(* NB: The module GRing should not be imported, only the main module and     *)
(*     GRing.Theory should be.                                               *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Abstract algebra framework for ssreflect.                        *)
(* We define a number of structures that "package" common algebraic *)
(* properties of operations. These extend the combinatorial classes *)
(* with notation and theory for classical algebraic structures.     *)

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "*%R" (at level 0).
Reserved Notation "n %:R"
  (at level 2, R at level 1, left associativity, format "n %:R").

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.

Module GRing.

Import Monoid.Theory.

Module Zmodule.

Record mixin_of (M : Type) : Type := Mixin {
  zero : M;
  opp : M -> M;
  add : M -> M -> M;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
}.

Record class_of (M : Type) : Type :=
  Class { base :> Choice.class_of M; ext :> mixin_of M }.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Choice.unpack k.

Definition eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.

End Zmodule.

Canonical Structure Zmodule.eqType.
Canonical Structure Zmodule.choiceType.
Bind Scope ring_scope with Zmodule.sort.

Definition zero M := Zmodule.zero (Zmodule.class M).
Definition opp M := Zmodule.opp (Zmodule.class M).
Definition add M := Zmodule.add (Zmodule.class M).

Notation Local "0" := (zero _).
Notation Local "-%R" := (@opp _).
Notation Local "- x" := (opp x).
Notation Local "+%R" := (@add _).
Notation Local "x + y" := (add x y).
Notation Local "x - y" := (x + - y).

Definition natmul M x n := nosimpl iterop _ n +%R x (zero M).

Notation Local "x *+ n" := (natmul x n).
Notation Local "x *- n" := ((- x) *+ n).

Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Notation "\sum_ ( i \in A ) F" := (\big[+%R/0]_(i \in A) F).

Section ZmoduleTheory.

Variable M : Zmodule.type.
Implicit Types x y : M.

Lemma addrA : @associative M +%R. Proof. by case M => T [? []]. Qed.
Lemma addrC : @commutative M +%R. Proof. by case M => T [? []]. Qed.
Lemma add0r : @left_id M 0 +%R. Proof. by case M => T [? []]. Qed.
Lemma addNr : @left_inverse M 0 -%R +%R. Proof. by case M => T [? []]. Qed.

Lemma addr0 : @right_id M 0 +%R.
Proof. by move=> x; rewrite addrC add0r. Qed.
Lemma addrN : @right_inverse M 0 -%R +%R.
Proof. by move=> x; rewrite addrC addNr. Qed.
Definition subrr := addrN.

Canonical Structure add_monoid := Monoid.Law addrA add0r addr0.
Canonical Structure add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative M +%R. Proof. exact: mulmCA. Qed.
Lemma addrAC : @right_commutative M +%R. Proof. exact: mulmAC. Qed.

Lemma addKr : forall x, cancel ( +%R x) ( +%R (- x)).
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.
Lemma addNKr : forall x, cancel ( +%R (- x)) ( +%R x).
Proof. by move=> x y; rewrite addrA addrN add0r. Qed.
Lemma addrK : forall x, cancel ( +%R^~ x) ( +%R^~ (- x)).
Proof. by move=> x y; rewrite -addrA addrN addr0. Qed.
Lemma addrNK : forall x, cancel ( +%R^~ (- x)) ( +%R^~ x).
Proof. by move=> x y; rewrite -addrA addNr addr0. Qed.
Definition subrK := addrNK.
Lemma addrI : forall y, injective (add y).
Proof. move=> x; exact: can_inj (addKr x). Qed.
Lemma addIr : forall y, injective ( +%R^~ y).
Proof. move=> y; exact: can_inj (addrK y). Qed.
Lemma opprK : @involutive M -%R.
Proof. by move=> x; apply: (@addIr (- x)); rewrite addNr addrN. Qed.
Lemma oppr0 : -0 = 0 :> M.
Proof. by rewrite -[-0]add0r subrr. Qed.
Lemma oppr_eq0 : forall x, (- x == 0) = (x == 0).
Proof. by move=> x; rewrite (inv_eq opprK) oppr0. Qed.

Lemma oppr_add : {morph -%R: x y / x + y : M}.
Proof.
by move=> x y; apply: (@addrI (x + y)); rewrite addrA subrr addrAC addrK subrr.
Qed.

Lemma oppr_sub : forall x y, - (x - y) = y - x.
Proof. by move=> x y; rewrite oppr_add addrC opprK. Qed.

Lemma subr_eq : forall x y z, (x - z == y) = (x == y + z).
Proof. by move=> x y z; rewrite (can2_eq (subrK _) (addrK _)). Qed.

Lemma subr_eq0 : forall x y, (x - y == 0) = (x == y).
Proof. by move=> x y; rewrite subr_eq add0r. Qed.

Lemma mulr0n : forall x, x *+ 0 = 0. Proof. by []. Qed.
Lemma mulr1n : forall x, x *+ 1 = x. Proof. by []. Qed.

Lemma mulrS : forall x n, x *+ n.+1 = x + x *+ n.
Proof. by move=> x [|n] //=; rewrite addr0. Qed.

Lemma mulrSr : forall x n, x *+ n.+1 = x *+ n + x.
Proof. by move=> x n; rewrite addrC mulrS. Qed.

Lemma mul0rn : forall n, 0 *+ n = 0 :> M.
Proof. by elim=> // n IHn; rewrite mulrS add0r. Qed.

Lemma oppr_muln : forall x n, - (x *+ n) = x *- n :> M.
Proof.
by move=> x; elim=> [|n IHn]; rewrite ?oppr0 // !mulrS oppr_add IHn.
Qed.

Lemma mulrn_addl : forall n, {morph (fun x => x *+ n) : x y / x + y}.
Proof.
move=> n x y; elim: n => [|n IHn]; rewrite ?addr0 // !mulrS. 
by rewrite addrCA -!addrA -IHn -addrCA.
Qed.

Lemma mulrn_addr : forall x m n, x *+ (m + n) = x *+ m + x *+ n.
Proof.
move=> x n m; elim: n => [|n IHn]; first by rewrite add0r.
by rewrite !mulrS IHn addrA.
Qed.

Lemma mulrnA : forall x m n, x *+ (m * n) = x *+ m *+ n.
Proof.
move=> x m n; rewrite mulnC.
by elim: n => //= n IHn; rewrite mulrS mulrn_addr IHn.
Qed.

Lemma mulrnAC : forall x m n, x *+ m *+ n = x *+ n *+ m.
Proof. by move=> x m n; rewrite -!mulrnA mulnC. Qed.

Lemma sumr_opp : forall I r P (F : I -> M),
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Proof. by move=> I r P F; rewrite (big_morph _ oppr_add oppr0). Qed.

Lemma sumr_sub : forall I r (P : pred I) (F1 F2 : I -> M),
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. by move=> *; rewrite -sumr_opp -big_split /=. Qed.

Lemma sumr_muln :  forall I r P (F : I -> M) n,
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Proof.
by move=> I r P F n; rewrite (big_morph _ (mulrn_addl n) (mul0rn _)).
Qed.

Lemma sumr_const : forall (I : finType) (A : pred I) (x : M),
  \sum_(i \in A) x = x *+ #|A|.
Proof. by move=> I A x; rewrite big_const -iteropE. Qed.

End ZmoduleTheory.

Module Ring.

Record mixin_of (R : Zmodule.type) : Type := Mixin {
  one : R;
  mul : R -> R -> R;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul +%R;
  _ : right_distributive mul +%R;
  _ : one != 0
}.

Definition EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 :=
  let _ := @Mixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 in
  @Mixin (Zmodule.Pack (Zmodule.class R) R) _ _
     mulA mul1x mulx1 mul_addl mul_addr nz1.

Record class_of (R : Type) : Type := Class {
  base :> Zmodule.class_of R;
  ext :> mixin_of (Zmodule.Pack base R)
}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Zmodule.unpack k.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.

End Ring.

Bind Scope ring_scope with Ring.sort.
Canonical Structure Ring.eqType.
Canonical Structure Ring.choiceType.
Canonical Structure Ring.zmodType.

Definition one (R : Ring.type) : R := Ring.one (Ring.class R).
Definition mul (R : Ring.type) : R -> R -> R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).

Notation Local "1" := (one _).
Notation Local "- 1" := (- (1)).
Notation Local "n %:R" := (1 *+ n).
Notation Local "*%R" := (@mul _).
Notation Local "x * y" := (mul x y).
Notation Local "x ^+ n" := (exp x n).

Notation "\prod_ ( i <- r | P ) F" := (\big[*%R/1]_(i <- r | P) F).
Notation "\prod_ ( i \in A ) F" := (\big[*%R/1]_(i \in A) F).
 
Section RingTheory.

Variable R : Ring.type.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R. Proof. by case R => T [? []]. Qed.
Lemma mul1r : @left_id R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr1 : @right_id R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr_addl : @left_distributive R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma mulr_addr : @right_distributive R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma nonzero1r : 1 != 0 :> R. Proof. by case R => T [? []]. Qed.
Lemma oner_eq0 : (1 == 0 :> R) = false. Proof. exact: negbTE nonzero1r. Qed.

Lemma mul0r : @left_zero R 0 *%R.
Proof.
by move=> x; apply: (@addIr _ (1 * x)); rewrite -mulr_addl !add0r mul1r.
Qed.
Lemma mulr0 : @right_zero R 0 *%R.
Proof.
by move=> x; apply: (@addIr _ (x * 1)); rewrite -mulr_addr !add0r mulr1.
Qed.
Lemma mulrN : forall x y, x * (- y) = - (x * y).
Proof.
by move=> x y; apply: (@addrI _ (x * y)); rewrite -mulr_addr !subrr mulr0.
Qed.
Lemma mulNr : forall x y, (- x) * y = - (x * y).
Proof.
by move=> x y; apply: (@addrI _ (x * y)); rewrite -mulr_addl !subrr mul0r.
Qed.
Lemma mulrNN : forall x y, (- x) * (- y) = x * y.
Proof. by move=> x y; rewrite mulrN mulNr opprK. Qed.
Lemma mulN1r : forall x, -1 * x = - x.
Proof. by move=> x; rewrite mulNr mul1r. Qed.
Lemma mulrN1 : forall x, x * -1 = - x.
Proof. by move=> x; rewrite mulrN mulr1. Qed.

Canonical Structure mul_monoid := Monoid.Law mulrA mul1r mulr1.
Canonical Structure muloid := Monoid.MulLaw mul0r mulr0.
Canonical Structure addoid := Monoid.AddLaw mulr_addl mulr_addr.

Lemma mulr_natr : forall x n, x * n%:R = x *+ n.
Proof.
by move=> x; elim=> [|n IHn]; rewrite ?mulr0 // !mulrS mulr_addr IHn mulr1.
Qed.

Lemma mulr_natl : forall n x, n%:R * x = x *+ n.
Proof.
move=> n x; elim: n => [|n IHn]; first exact: mul0r.
by rewrite !mulrS mulr_addl mul1r IHn.
Qed.

Lemma natr_add : forall m n, (m + n)%:R = m%:R + n%:R :> R.
Proof. by move=> m n; exact: mulrn_addr. Qed.

Lemma natr_mul : forall m n, (m * n)%:R = m%:R * n%:R :> R.
Proof. by move=> m n; rewrite mulrnA -mulr_natr. Qed.

Lemma expr0 : forall x, x ^+ 0 = 1. Proof. by []. Qed.
Lemma expr1 : forall x, x ^+ 1 = x. Proof. by []. Qed.

Lemma exprS : forall x n, x ^+ n.+1 = x * x ^+ n.
Proof. by move=> x [] //; rewrite mulr1. Qed.

Lemma exp1rn : forall n, 1 ^+ n = 1 :> R.
Proof. by elim=> // n IHn; rewrite exprS mul1r. Qed.

Lemma exprn_addr : forall x m n, x ^+ (m + n) = x ^+ m * x ^+ n.
Proof.
by move=> x m n; elim: m => [|m IHm]; rewrite ?mul1r // !exprS -mulrA -IHm.
Qed.

Lemma exprSr : forall x n, x ^+ n.+1 = x ^+ n * x.
Proof. by move=> x n; rewrite -addn1 exprn_addr expr1. Qed.

Definition commDef x y := x * y = y * x.
Notation comm := commDef.

Lemma commr_sym : forall x y, comm x y -> comm y x. Proof. done. Qed.
Lemma commr_refl : forall x, comm x x. Proof. done. Qed.

Lemma commr0 : forall x, comm x 0.
Proof. by move=> x; rewrite /comm mulr0 mul0r. Qed.

Lemma commr1 : forall x, comm x 1.
Proof. by move=> x; rewrite /comm mulr1 mul1r. Qed.

Lemma commr_opp : forall x y, comm x y -> comm x (- y).
Proof. by move=> x y com_xy; rewrite /comm mulrN com_xy mulNr. Qed.

Lemma commrN1 : forall x, comm x (-1).
Proof. move=> x; apply: commr_opp; exact: commr1. Qed.

Lemma commr_add : forall x y z,
  comm x y -> comm x z -> comm x (y + z).
Proof. by move=> x y z; rewrite /comm mulr_addl mulr_addr => -> ->. Qed.

Lemma commr_muln : forall x y n, comm x y -> comm x (y *+ n).
Proof.
rewrite /comm => x y n com_xy.
by elim: n => [|n IHn]; rewrite ?commr0 // mulrS commr_add.
Qed.

Lemma commr_mul : forall x y z,
  comm x y -> comm x z -> comm x (y * z).
Proof.
by move=> x y z com_xy; rewrite /comm mulrA com_xy -!mulrA => ->.
Qed.

Lemma commr_nat : forall x n, comm x n%:R.
Proof. move=> x n; apply: commr_muln; exact: commr1. Qed.

Lemma commr_exp : forall x y n, comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => x y n com_xy.
by elim: n => [|n IHn]; rewrite ?commr1 // exprS commr_mul.
Qed.

Lemma commr_exp_mull : forall x y n,
  comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> x y n com_xy; elim: n => /= [|n IHn]; first by rewrite mulr1.
by rewrite !exprS IHn !mulrA; congr (_ * _); rewrite -!mulrA -commr_exp.
Qed.

Lemma exprn_mulnl : forall x m n, (x *+ m) ^+ n = x ^+ n *+ (m ^ n) :> R.
Proof.
move=> x m; elim=> [|n IHn]; first by rewrite mulr1n.
rewrite exprS IHn -mulr_natr -mulrA -commr_nat mulr_natr -mulrnA -expnSr.
by rewrite -mulr_natr mulrA -exprS mulr_natr.
Qed.

Lemma exprn_mulr : forall x m n, x ^+ (m * n) = x ^+ m ^+ n.
Proof.
move=> x m n; elim: m => [|m IHm]; first by rewrite exp1rn.
by rewrite mulSn exprn_addr IHm exprS commr_exp_mull //; exact: commr_exp.
Qed.

Lemma signr_odd : forall n, (-1) ^+ (odd n) = (-1) ^+ n :> R.
Proof.
elim=> //= n IHn; rewrite exprS -{}IHn.
by case/odd: n; rewrite !mulN1r ?opprK.
Qed.

Lemma signr_eq0 :  forall n, ((-1) ^+ n == 0 :> R) = false.
Proof.
by move=> n; rewrite -signr_odd; case: odd; rewrite ?oppr_eq0 oner_eq0.
Qed.

Lemma signr_addb : forall b1 b2,
  (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Proof. by do 2!case; rewrite ?expr1 ?mulN1r ?mul1r ?opprK. Qed.

Lemma exprN : forall x n, (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Proof.
by move=> x n; rewrite -mulN1r commr_exp_mull // /comm mulN1r mulrN mulr1.
Qed.

Lemma prodr_const : forall (I : finType) (A : pred I) (x : R),
  \prod_(i \in A) x = x ^+ #|A|.
Proof. by move=> I A x; rewrite big_const -iteropE. Qed.

Definition RevRingMixin :=
  let mul' x y := y * x in
  let mulrA' x y z := esym (mulrA z y x) in
  let mulr_addl' x y z := mulr_addr z x y in
  let mulr_addr' x y z := mulr_addl y z x in
  @Ring.Mixin R 1 mul' mulrA' mulr1 mul1r mulr_addl' mulr_addr' nonzero1r.

Definition RevRingType := Ring.Pack (Ring.Class RevRingMixin) R.


End RingTheory.

Notation comm := (@commDef _).

Notation rev :=
  (let R := _ in fun (x : Ring.sort R) => x : Ring.sort (RevRingType R)).

Definition ring_morphism (aR rR : Ring.type) (f : aR -> rR) :=
  [/\ {morph f : x y / x - y}, {morph f : x y / x * y} & f 1 = 1].

Section RingMorphTheory.

Variables aR' aR rR : Ring.type.
Variables (f : aR -> rR) (g : aR' -> aR).
Hypotheses (fM : ring_morphism f) (gM : ring_morphism g).

Lemma ringM_sub : {morph f : x y / x - y}.
Proof. by case fM. Qed.

Lemma ringM_0 : f 0 = 0.
Proof. by rewrite -(subrr 0) ringM_sub subrr. Qed.

Lemma ringM_1 : f 1 = 1.
Proof. by case fM. Qed.

Lemma ringM_opp : {morph f : x / - x}.
Proof. by move=> x /=; rewrite -[-x]add0r ringM_sub ringM_0 add0r. Qed.

Lemma ringM_add : {morph f : x y / x + y}.
Proof. by move=> x y /=; rewrite -(opprK y) ringM_opp ringM_sub. Qed.

Definition ringM_sum := big_morph f ringM_add ringM_0.

Lemma ringM_mul : {morph f : x y / x * y}.
Proof. by case fM. Qed.

Definition ringM_prod := big_morph f ringM_mul ringM_1.

Lemma ringM_nat : forall n, f n%:R = n %:R.
Proof.
by elim=> [|n IHn]; rewrite ?ringM_0 // !mulrS ringM_add IHn ringM_1.
Qed.

Lemma ringM_exp : forall n, {morph f : x / x ^+ n}.
Proof.  by elim=> [|n IHn] x; rewrite ?ringM_1 //  !exprS ringM_mul IHn. Qed.

Lemma comp_ringM : ring_morphism (f \o g).
Proof.
case: fM gM => [fsub fmul f1] [gsub gmul g1].
by split=> [x y | x y |] /=; rewrite ?g1 ?gsub ?gmul.
Qed.


End RingMorphTheory.



Module ComRing.

Record class_of (R : Type) : Type :=
  Class {base :> Ring.class_of R; _ : commutative (Ring.mul base)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack : forall R, commutative *%R -> type :=
  let k T c m := Pack (@Class T c m) T in Ring.unpack k.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.

End ComRing.

Canonical Structure ComRing.eqType.
Canonical Structure ComRing.choiceType.
Canonical Structure ComRing.zmodType.
Canonical Structure ComRing.ringType.
Bind Scope ring_scope with ComRing.sort.

Section ComRingTheory.

Variable R : ComRing.type.
Implicit Types x y : R.

Lemma mulrC : @commutative R *%R. Proof. by case: R => T []. Qed.
Canonical Structure mul_comoid := Monoid.ComLaw mulrC.
Lemma mulrCA : @left_commutative R *%R. Proof. exact: mulmCA. Qed.
Lemma mulrAC : @right_commutative R *%R. Proof. exact: mulmAC. Qed.

Lemma exprn_mull : forall n, {morph (fun x => x ^+ n) : x y / x * y}.
Proof. move=> n x y; apply: commr_exp_mull; exact: mulrC. Qed.

Lemma prodr_exp : forall n I r (P : pred I) (F : I -> R),
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
Proof.
by move=> n I r P F; rewrite (big_morph _ (exprn_mull n) (exp1rn _ n)).
Qed.

End ComRingTheory.

Module UnitRing.

Record mixin_of (R : Ring.type) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in predC unit, inv =1 id}
}.

Definition EtaMixin R unit inv mulVr mulrV unitP inv_out :=
  let _ := @Mixin R unit inv mulVr mulrV unitP inv_out in
  @Mixin (Ring.Pack (Ring.class R) R) unit inv mulVr mulrV unitP inv_out.

Record class_of (R : Type) : Type := Class {
  base :> Ring.class_of R;
  mixin :> mixin_of (Ring.Pack base R)
}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Ring.unpack k.
Definition comPack := (* pack ComUnitRing mixin *)
  let k T cc :=
    let: ComRing.Class c _ := cc return mixin_of (Ring.Pack cc T) -> type
    in fun m => Pack (Class m) T
  in ComRing.unpack k. 

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.

End UnitRing.

Canonical Structure UnitRing.eqType.
Canonical Structure UnitRing.zmodType.
Canonical Structure UnitRing.ringType.
Bind Scope ring_scope with UnitRing.sort.

Definition unitDef (R : UnitRing.type) : pred R :=
  UnitRing.unit (UnitRing.class R).
Notation unit := (@unitDef _).
Definition inv (R : UnitRing.type) : R -> R := UnitRing.inv (UnitRing.class R).

Notation Local "x ^-1" := (inv x).
Notation Local "x / y" := (x * y^-1).
Notation Local "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : UnitRing.type.
Implicit Types x y : R.

Lemma divrr : forall x, unit x -> x / x = 1.
Proof. by case: R => T [? []]. Qed.
Definition mulrV := divrr.
 
Lemma mulVr : forall x, unit x -> x^-1 * x = 1.
Proof. by case: R => T [? []]. Qed.

Lemma invr_out : forall x, ~~ unit x -> x^-1 = x.
Proof. by case: R => T [? []]. Qed.

Lemma unitrP : forall x, reflect (exists y, y * x = 1 /\ x * y = 1) (unit x).
Proof. 
move=> x; apply: (iffP idP) => [Ux | []]; last by case: R x => T [? []].
by exists x^-1; rewrite divrr ?mulVr.
Qed.

Lemma mulKr : forall x, unit x -> cancel (mul x) (mul x^-1).
Proof. by move=> x Ux y; rewrite mulrA mulVr ?mul1r. Qed.

Lemma mulVKr : forall x, unit x -> cancel (mul x^-1) (mul x).
Proof. by move=> x Ux y; rewrite mulrA mulrV ?mul1r. Qed.

Lemma mulrK : forall x, unit x -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by move=> x Ux y; rewrite -mulrA divrr ?mulr1. Qed.

Lemma mulrVK : forall x, unit x -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by move=> x Ux y; rewrite -mulrA mulVr ?mulr1. Qed.
Definition divrK := mulrVK.

Lemma mulrI : forall x, unit x -> injective (mul x).
Proof. move=> x Ux; exact: can_inj (mulKr Ux). Qed.

Lemma mulIr : forall x, unit x -> injective ( *%R^~ x).
Proof. move=> x Ux; exact: can_inj (mulrK Ux). Qed.

Lemma commr_inv : forall x, comm x x^-1.
Proof.
move=> x; case Ux: (unit x); last by rewrite invr_out ?Ux.
by rewrite /comm mulVr ?divrr.
Qed.

Lemma unitrE : forall x, unit x = (x / x == 1).
Proof.
move=> x; apply/idP/eqP=> [Ux | xx1]; first exact: divrr.
by apply/unitrP; exists x^-1; rewrite -commr_inv.
Qed.

Lemma invrK : involutive (@inv R).
Proof.
move=> x; case Ux: (unit x); last by rewrite !invr_out ?Ux.
rewrite -(mulrK Ux _^-1) -mulrA commr_inv mulKr //.
by apply/unitrP; exists x; rewrite divrr ?mulVr.
Qed.

Lemma invr_inj : injective (@inv R).
Proof. exact: inv_inj invrK. Qed.

Lemma unitr_inv : forall x, unit x^-1 = unit x.
Proof. by move=> x; rewrite !unitrE invrK commr_inv. Qed.

Lemma unitr1 : unit (1 : R).
Proof. by apply/unitrP; exists (1 : R); rewrite mulr1. Qed.

Lemma invr1 : 1^-1 = 1 :> R.
Proof. by rewrite -{2}(mulVr unitr1) mulr1. Qed.

Lemma unitr0 : unit (0 : R) = false.
Proof.
by apply/unitrP=> [[x [_]]]; apply/eqP; rewrite mul0r eq_sym nonzero1r.
Qed.

Lemma invr0 : 0^-1 = 0 :> R.
Proof. by rewrite invr_out ?unitr0. Qed.

Lemma unitr_opp : forall x, unit (- x) = unit x.
Proof.
move=> x; wlog Ux: x / unit x.
  by move=> WHx; apply/idP/idP=> Ux; first rewrite -(opprK x); rewrite WHx.
by rewrite Ux; apply/unitrP; exists (- x^-1); rewrite !mulrNN mulVr ?divrr.
Qed.

Lemma invrN : forall x, (- x)^-1 = - x^-1.
Proof.
move=> x; case Ux: (unit x) (unitr_opp x) => [] Unx.
  by apply: (mulrI Unx); rewrite mulrNN !divrr.
by rewrite !invr_out ?Ux ?Unx.
Qed.

Lemma unitr_mull : forall x y, unit y -> unit (x * y) = unit x.
Proof.
move=> x y Uy; wlog Ux: x y Uy / unit x => [WHxy|].
  by apply/idP/idP=> Ux; first rewrite -(mulrK Uy x); rewrite WHxy ?unitr_inv.
rewrite Ux; apply/unitrP; exists (y^-1 * x^-1).
by rewrite -!mulrA mulKr ?mulrA ?mulrK ?divrr ?mulVr.
Qed.

Lemma unitr_mulr : forall x y, unit x -> unit (x * y) = unit y.
Proof.
move=> x y Ux; apply/idP/idP=> [Uxy | Uy]; last by rewrite unitr_mull.
by rewrite -(mulKr Ux y) unitr_mull ?unitr_inv.
Qed.

Lemma invr_mul : forall x y, unit x -> unit y -> (x * y)^-1 = y^-1 * x^-1.
Proof.
move=> x y Ux Uy; have Uxy: unit (x * y) by rewrite unitr_mull.
by apply: (mulrI Uxy); rewrite divrr ?mulrA ?mulrK ?divrr.
Qed.

Lemma commr_unit_mul : forall x y, comm x y -> unit (x * y) = unit x && unit y.
Proof.
move=> x y cxy; apply/idP/andP=> [Uxy | [Ux Uy]]; last by rewrite unitr_mull.
suffices Ux: unit x by rewrite unitr_mulr in Uxy.
apply/unitrP; case/unitrP: Uxy => z [zxy xyz]; exists (y * z).
rewrite mulrA xyz -{1}[y]mul1r -{1}zxy cxy -!mulrA (mulrA x) (mulrA _ z) xyz.
by rewrite mul1r -cxy.
Qed.

Lemma unitr_exp : forall x n, unit x -> unit (x ^+ n).
Proof.
by move=> x n Ux; elim: n => [|n IHn]; rewrite ?unitr1 // exprS unitr_mull.
Qed.

Lemma unitr_pexp : forall x n, n > 0 -> unit (x ^+ n) = unit x.
Proof.
move=> x [//|n] _; rewrite exprS commr_unit_mul; last exact: commr_exp.
by case Ux: (unit x); rewrite // unitr_exp.
Qed.

Lemma expr_inv : forall x n, x^-1 ^+ n = x ^- n.
Proof.
move=> x; elim=> [|n IHn]; first by rewrite !expr0 ?invr1.
case Ux: (unit x); first by rewrite exprSr exprS IHn -invr_mul // unitr_exp.
by rewrite !invr_out ?unitr_pexp ?Ux.
Qed.

Lemma invr_neq0 : forall x, x != 0 -> x^-1 != 0.
Proof.
move=> x nx0; case Ux: (unit x); last by rewrite invr_out ?Ux.
by apply/eqP=> x'0; rewrite -unitr_inv x'0 unitr0 in Ux.
Qed.

Lemma invr_eq0 : forall x, (x^-1 == 0) = (x == 0).
Proof.
by move=> x; apply: negb_inj; apply/idP/idP; move/invr_neq0; rewrite ?invrK.
Qed.

End UnitRingTheory.

(* Reification of the theory of rings with units, in named style  *)
Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

Fixpoint tsubst (t : term) (s : nat * term) {struct t} :=
  match t with
  | Var i => if i == s.1 then s.2 else t
  | Const _ | NatConst _ => t
  | Add t1 t2 => Add (tsubst t1 s) (tsubst t2 s)
  | Opp t1 => Opp (tsubst t1 s)
  | NatMul t1 n => NatMul (tsubst t1 s) n
  | Mul t1 t2 => Mul (tsubst t1 s) (tsubst t2 s)
  | Inv t1 => Inv (tsubst t1 s)
  | Exp t1 n => Exp (tsubst t1 s) n
  end.

Fixpoint fsubst (f : formula) (s : nat * term) {struct f} :=
  match f with
  | Equal t1 t2 => Equal (tsubst t1 s) (tsubst t2 s)
  | Unit t1 => Unit (tsubst t1 s)
  | And f1 f2 => And (fsubst f1 s) (fsubst f2 s)
  | Or f1 f2 => Or (fsubst f1 s) (fsubst f2 s)
  | Implies f1 f2 => Implies (fsubst f1 s) (fsubst f2 s)
  | Not f1 => Not (fsubst f1 s)
  | Exists i f1 => Exists i (if i == s.1 then f1 else fsubst f1 s)
  | Forall i f1 => Forall i (if i == s.1 then f1 else fsubst f1 s)
  end.

End TermDef.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Scope Add [_ term_scope term_scope].
Arguments Scope Opp [_ term_scope].
Arguments Scope NatMul [_ term_scope nat_scope].
Arguments Scope Mul [_ term_scope term_scope].
Arguments Scope Mul [_ term_scope term_scope].
Arguments Scope Inv [_ term_scope].
Arguments Scope Exp [_ term_scope nat_scope].
Arguments Scope Equal [_ term_scope term_scope].
Arguments Scope Unit [_ term_scope].
Arguments Scope And [_ term_scope term_scope].
Arguments Scope Or [_ term_scope term_scope].
Arguments Scope Implies [_ term_scope term_scope].
Arguments Scope Not [_ term_scope].
Arguments Scope Exists [_ nat_scope term_scope].
Arguments Scope Forall [_ nat_scope term_scope].
Arguments Scope tsubst [_ term_scope _].
Arguments Scope fsubst [_ term_scope _].

Notation Local "s `_ i" := (nth 0 s i).

Notation "''X_' i" := (Var _ i)
  (at level 8, i at level 2, format "''X_' i") : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "'exists' ''X_' i , f" := (Exists i f)
  (at level 200, i at level 2, right associativity,
   format "'[hv' 'exists'  ''X_' i , '/ '  f ']'") : term_scope.
Notation "'forall' ''X_' i , f" := (Forall i f)
  (at level 200, i at level 2,
   format "'[hv' 'forall'  ''X_' i , '/ '  f ']'") : term_scope.


Section EvalTerm.

Variable R : UnitRing.type.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (t : term R) (e : seq R) {struct t} : R :=
  match t with
  | Var i => e`_i
  | Const x => x
  | NatConst n => n%:R
  | Add t1 t2 => eval t1 e + eval t2 e
  | Opp t1 => - eval t1 e
  | NatMul t1 n => eval t1 e *+ n
  | Mul t1 t2 => eval t1 e * eval t2 e
  | Inv t1 => (eval t1 e)^-1
  | Exp t1 n => eval t1 e ^+ n
  end.

Lemma eq_eval : forall t e e', nth 0 e =1 nth 0 e' -> eval t e = eval t e'.
Proof. by move=> t e e' eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst : forall t e s,
  eval (tsubst t s) e = eval t (set_nth 0 e s.1 (eval s.2 e)).
Proof.
move=> t e [i u]; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: eq_op.
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (f : formula R) (e : seq R) {struct f} : Prop :=
  match f with
  | Equal t1 t2 => eval t1 e = eval t2 e
  | Unit t1 => unit (eval t1 e)
  | And f1 f2 => holds f1 e /\ holds f2 e
  | Or f1 f2 => holds f1 e \/ holds f2 e
  | Implies f1 f2 => holds f1 e -> holds f2 e
  | Not f1 => ~ holds f1 e
  | Exists i f1 => exists x, holds f1 (set_nth 0 e i x)
  | Forall i f1 => forall x, holds f1 (set_nth 0 e i x)
  end.

(* Extensionality of formula evaluation *)
Lemma eq_holds : forall f e e',
  nth 0 e =1 nth 0 e' -> (holds f e <-> holds f e').
Proof.
pose es1 e e' := @nth R 0 e =1 nth 0 e'.
have eq_i: forall i v, let sv e := set_nth 0 e i v in
           forall e e', es1 e e' -> es1 (sv e) (sv e').
  by move=> i v /= e e' eq_e j; rewrite !nth_set_nth /= eq_e.
elim=> /=.
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- move=> ? IH ? IH' ? ? E; move: (IH _ _ E) (IH' _ _ E); tauto.
- move=> ? IH ? IH' ? ? E; move: (IH _ _ E) (IH' _ _ E); tauto.
- move=> ? IH ? IH' ? ? E; move: (IH _ _ E) (IH' _ _ E); tauto.
- move=> ? IH ? ? E; move: (IH _ _ E); tauto.
- move=> i f IHf e e' E; have{IHf} IHf := IHf _ _ (eq_i i _ _ _ E).
  split=> [] [x]; exists x; move: (IHf x); tauto.
- move=> i f IHf e e' E; have{IHf} IHf := IHf _ _ (eq_i i _ _ _ E).
  split=> [] f_e x; move: (f_e x) (IHf x); tauto.
Qed.

(* Evaluation and substitution by a constant *)
Lemma holds_fsubst : forall f e i v,
  holds (fsubst f (i, Const v)) e <-> holds f (set_nth 0 e i v).
Proof.
move=> f e i v; elim: f e => /=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
- case eq_ji: (j == i); first rewrite (eqP eq_ji).
    by split=> [] [x f_x]; exists x; rewrite set_set_nth eqxx in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
case eq_ji: (j == i); first rewrite (eqP eq_ji).
  by split=> [] f_ x; move: (f_ x); rewrite set_set_nth eqxx.
split=> [] f_ x; move: (f_ x); rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
Qed.

(* Boolean test selecting terms in the language of rings *)
Fixpoint rterm (t : term R) := 
  match t with
  | Inv _ => false
  | Add t1 t2 | Mul t1 t2 => rterm t1 && rterm t2
  | Opp t1 | NatMul t1 _ | Exp t1 _ => rterm t1
  | _ => true
  end.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Equal t1 t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | And f1 f2 | Or f1 f2 | Implies f1 f2 => rformula f1 && rformula f2
  | Not f1 | Exists _ f1 | Forall _ f1 => rformula f1
  end.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | Var i => i.+1
  | Add t1 t2 | Mul t1 t2 => maxn (ub_var t1) (ub_var t2)
  | Opp t1 | NatMul t1 _ | Exp t1 _ | Inv t1 => ub_var t1
  | _ => 0%N
  end.

(* Replaces inverses in the term t  by fresh variables *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | Inv t1 =>
    let: (t1', r1) := to_rterm t1 r n in
      (Var _ (n + size r1), rcons r1 t1')
  | Add t1 t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Add t1' t2', r2)
  | Opp t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (Opp t1', r1)
  | NatMul t1 m =>
   let: (t1', r1) := to_rterm t1 r n in
     (NatMul t1' m, r1)
  | Mul t1 t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | Exp t1 m =>
       let: (t1', r1) := to_rterm t1 r n in
     (Exp t1' m, r1)
  | _ => (t, r)
  end.

(* A ring formula stating that t1 is equal to 0 in the ring *)
(*theory. Also applies to non commutative rings *)
Definition eq0_rformula t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop (r : seq (term R)) (i : nat) {struct r}:=
    (match r with 
      | [::] => Equal t1' (NatConst _ 0)
      | t :: r' => 
        let f := 'X_i * t == 1%:R /\ t * 'X_i == 1%:R in
          forall 'X_i, (f \/ 'X_i == t /\ ~ (exists 'X_i,  f)) ==> loop r' i.+1
    end)%T
    in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(*  equivalent formula in the sub-theory of rings : *)
Fixpoint to_rformula f := 
  match f with
  | t1 == t2 => 
      eq0_rformula (t1 - t2)
  | Unit t1 => eq0_rformula (t1 * t1^-1 - 1%:R)
  | f1 /\ f2 => to_rformula f1 /\ to_rformula f2
  | f1 \/ f2 =>  to_rformula f1 \/ to_rformula f2
  | f1 ==> f2 => to_rformula f1 ==> to_rformula f2
  | ~ f1 => ~ to_rformula f1
  | Exists i f1 => exists 'X_i, to_rformula f1
  | Forall i f1 => forall 'X_i, to_rformula f1
  end%T.

(* The transformation gives a ring formula.*)
Lemma rformula_to_rformula : forall f, rformula (to_rformula f).
Proof.
suff eq0_ring : rformula (eq0_rformula _) by elim=> //= => f1 ->.
move=> t1; rewrite /eq0_rformula; move: (ub_var t1) => m.
set tr := _ m.
suff : all rterm (tr.1 :: tr.2).
  case: tr => {t1} t1 r /=; case/andP=> t1_r.
  elim: r m => [| t r IHr] m; rewrite /= ?andbT //.
  case/andP=> ->; exact: IHr.
have : all rterm [::] by [].
rewrite {}/tr; elim: t1 [::] => //=.
- move=> t1 IHt1 t2 IHt2 r. 
  move/IHt1; case: to_rterm=> {t1 r IHt1} t1 r /=; case/andP=> t1_r.
  move/IHt2; case: to_rterm=> {t2 r IHt2} t2 r /=; case/andP=> t2_r.
  by rewrite t1_r t2_r.
- by move=> t1 IHt1 r; move/IHt1; case: to_rterm. 
- by move=> t1 IHt1 n r; move/IHt1; case: to_rterm. 
- move=> t1 IHt1 t2 IHt2 r. 
  move/IHt1; case: to_rterm=> {t1 r IHt1} t1 r /=; case/andP=> t1_r.
  move/IHt2; case: to_rterm=> {t2 r IHt2} t2 r /=; case/andP=> t2_r.
  by rewrite t1_r t2_r.
- move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm=> {t1 r IHt1} t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r; move/IHt1; case: to_rterm. 
Qed.

(* Correctness of the transformation. *)
Lemma to_rformula_equiv : forall f e,
  holds (to_rformula f) e <-> holds f e.
Proof.
suff equal0_equiv : forall t1 t2 e, 
  holds (eq0_rformula (t1 - t2)) e <-> (eval t1 e == eval t2 e).
- elim => /= ; try tauto.
  + move => t1 t2 e.
    by split; [move/equal0_equiv; move/eqP | move/eqP; move/equal0_equiv].
  + move=> t1 e; rewrite unitrE; exact: equal0_equiv.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x]; move/IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
move=> t1 t2 e; rewrite -(add0r (eval t2 e)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval (t1 - t2) e); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst : forall s t, s.1 >= ub_var t -> tsubst t s = t.
  move=> s; elim=> //=.
  - by move=> n; case: ltngtP.
  - move=> t1 IHt1 t2 IHt2; rewrite leq_maxl.
    by case/andP; move/IHt1->; move/IHt2->.
  - by move=> t1 IHt1; move/IHt1->.
  - by move=> t1 IHt1 n; move/IHt1->.
  - move=> t1 IHt1 t2 IHt2; rewrite leq_maxl.
    by case/andP; move/IHt1->; move/IHt2->.
  - by move=> t1 IHt1; move/IHt1->.
  - by move=> t1 IHt1 n; move/IHt1->.
pose rsub  t' := fix rsub m (r : seq (term R))  :=
  if r is u :: r' then tsubst (rsub m.+1 r') (m, u^-1)%T else t'.
pose ub_sub := fix ub_sub m (r : seq (term R))  :=
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else True.
suff rsub_to_r : forall t0 r0 m, m >= ub_var t0 -> ub_sub m r0 ->
  let: (t', r) := to_rterm t0 r0 m in
  [/\ take (size r0) r = r0, 
    ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t0].
- have:= rsub_to_r t [::] _ (leqnn _).
  rewrite /eq0_rformula.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split; move/eqP.
  rewrite eval_tsubst /=; set y := eval u e; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst u e (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (unit y); [left | right]; first by rewrite mulVr ?divrr.
    split; first by rewrite invr_out ?Uy.
    case=> z; rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst u e (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  by rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, Const _))
     !sub_var_tsubst.
have rsub_id : forall r t n, (ub_var t)<= n -> rsub t n r = t.
  elim=> //= t0 r IHr t1 n hn; rewrite IHr ?sub_var_tsubst  ?(ltnW hn) //.
  by  rewrite (leq_trans hn).
have rsub_acc : forall r s t1 m, 
  ub_var t1 <= m + size r -> rsub t1 m (r ++ s) = rsub t1 m r.
  elim=> [|t1 r IHr] s t2 m /=; first by rewrite addn0; apply: rsub_id.
  by move=> hleq; rewrite IHr // addSnnS.
elim=> /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite leq_maxl; case/andP=> hub1 hub2 hmr;
  case: to_rterm {IHt1 hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite leq_maxl; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //; 
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take leq_minl leqnn orbT];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move/IHt1=> {IHt1}IHt1
     | move=> t1 IHt1 n r m; do 2!move/IHt1=> {IHt1}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IHt1 r m; do 2!move/IHt1=> {IHt1}IHt1.
case: to_rterm IHt1 => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take leq_minl leqnn orbT.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS; move/IHr1=> IH; case/IH=> _ _ ub_r1 ->.
Qed. 

(* Boolean test selecting formulas which describe a constructable set, *)
(* i.e. formulas without quantifiers. Here we also require that zero be the *)
(* rhs in equalities. *)

(* The job of qfree is to check that all the terms in the dnf are rterms..*)
(* May be should we separate this check from bare quantifier elimination *)
Fixpoint qfree (f : formula R) :=
  match f with
  | Equal t1 (NatConst 0) => rterm t1
  | And f1 f2 | Or f1 f2 => qfree f1 && qfree f2 
  | Not f1 => qfree f1
  | _ => false
  end.

(* Boolean holds predicate for quantifier free formulas *)
Definition qfree_eval e := fix loop (f : formula R) : bool :=
  match f with 
    | Equal t1 (NatConst 0) => (eval t1 e == 0)
    | And f1 f2 => loop f1 && loop f2
    | Or f1 f2 => loop f1 || loop f2
    | Not f1 => ~~ loop f1
    |_ => false
  end.

(* qfree_eval is equivalent to holds *)
Lemma qfree_eval_holds : forall f e,
  qfree f -> reflect (holds f e) (qfree_eval e f).
Proof.
elim=> //.
- move=> t1 t2 e cet12; case: t2 cet12=> //= [[|n]] // _; exact: eqP.
- move=> f1 IHf1 f2 IHf2 e /=; case/andP => cf1 cf2.
  by apply: (iffP andP); case; move/(IHf1 _ cf1)=> r1; move/(IHf2 _ cf2); split.
- move=> f1 IHf1 f2 IHf2 e /=; case/andP => cf1 cf2.
  by apply: (iffP orP); 
    (case; [move/(IHf1 _ cf1)=> H1; left | move/(IHf2 _ cf2); right]).
- by move=> f IHf e /= cf; apply: (iffP negP)=> H; move/(IHf _ cf).
Qed.

(* The T truth formula *)
Definition tt_form : formula R := (0%:R == 0%:R)%T.

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qfree formula *)
Fixpoint qfree_to_dnf (f : formula R) (neg : bool) {struct f} := 
  match f with
    | Equal t1 _ => [:: if neg then ([::], [:: t1]) else ([:: t1], [::])]
    | And f1 f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
    | Or f1 f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
    | Not f1 => [rec f1, (~~ neg)]
    |_ =>  [:: ([::], [::])]
  end where "[ 'rec' f , neg ]" := (qfree_to_dnf f neg).


(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_formula :=
  foldr (fun bc =>
         Or (foldr (fun t => And (t == 0%:R)) tt_form bc.1
             /\ foldr (fun t => And (~ (t == 0%:R))) tt_form bc.2))
        (Not tt_form).


(* Catenation of dnf is the Or of formulas *)
Lemma dnf_to_formula_cat : forall bcs1 bcs2 e, 
  qfree_eval e (dnf_to_formula (bcs1 ++ bcs2))
 = qfree_eval e ((dnf_to_formula bcs1) \/ (dnf_to_formula bcs2)).
Proof.
elim=> [|bc1 bcs1 IH1] bcs2 e /=; first by rewrite eqxx.
by rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnf_correct : forall bcs1 bcs2 e, 
  qfree_eval e (dnf_to_formula (and_dnf bcs1 bcs2))
  = qfree_eval e ((dnf_to_formula bcs1) /\ (dnf_to_formula bcs2)).
Proof.
elim=>[|bc1 bcs1 IH1] bcs2 /= e; first by rewrite /and_dnf big_nil /= eqxx.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) dnf_to_formula_cat  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [| bc2 bcs2 IH] bc1 /=; first by rewrite eqxx andbF.
rewrite {}IH /= andb_orr; congr orb; rewrite {bcs2}. 
suff aux : forall (l1 l2 : seq (term R)) g, 
  qfree_eval e (foldr (fun t => And (g t)) tt_form (l1 ++ l2)) =
  qfree_eval e (And (foldr (fun t => And (g t)) tt_form l1)
                    (foldr (fun t => And (g t)) tt_form l2)).
  by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim=> [| ? ? IHl1] * /=; [rewrite eqxx | rewrite -andbA IHl1 /=].
Qed.


Lemma qfree_to_dnf_correct : forall f, (qfree f) -> 
  (forall e, qfree_eval e f =
    qfree_eval e (dnf_to_formula (qfree_to_dnf f false))).
Proof.
elim => //=.
- by move=> t1 t2; case: t2 => //= [[|n]] // _ e; rewrite eqxx /= orbF !andbT.
- move=> f1 IHf1 f2 IHf2; case/andP=> cf1 cf2 e; rewrite IHf1 // IHf2 //=.
  by rewrite and_dnf_correct.
- move=> f1 IHf1 f2 IHf2; case/andP=> cf1 cf2 e; rewrite IHf1 // IHf2 //=.
  by rewrite dnf_to_formula_cat.
- move=> f IHf cf e; rewrite {}IHf //; elim: f cf => //.
  + by move=> t1 [] ? //=; rewrite eqxx /= 2!orbF !andbT.
  + move=> f1 IHf1 f2 IHf2 /=; case/andP=> cf1 cf2.
    by rewrite and_dnf_correct /= dnf_to_formula_cat /= -IHf1 // negb_and IHf2.
  + move=> f1 IHf1 f2 IHf2 /=; case/andP=> cf1 cf2.
    by rewrite and_dnf_correct /= dnf_to_formula_cat /= -IHf1 // negb_or -IHf2.
  + by move=> f IHf /= cf; rewrite -IHf // negbK.
Qed.

Lemma qfree_dnf_to_formula : forall f,
  qfree f -> qfree (dnf_to_formula (qfree_to_dnf f false)).
Proof.
have aux1 : forall bcs1 bcs2,
  qfree (dnf_to_formula (bcs1 ++ bcs2))
  = qfree (dnf_to_formula bcs1) && (qfree (dnf_to_formula bcs2)).
  by elim=> [|bc1 bcs1 IH1] bcs2 //=; rewrite IH1 andbA.
have aux2 : forall bcs1 bcs2, 
  qfree (dnf_to_formula bcs1) -> 
  qfree (dnf_to_formula bcs2) ->
  qfree (dnf_to_formula (and_dnf bcs1 bcs2)).
- elim=>[|bc1 bcs1 IH1] bcs2 /=; first by rewrite /and_dnf big_nil.
  rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) aux1.
  do 2![case/andP] => cf1 cf2 cbf1 cbf2; rewrite {}IH1 //= andbT. 
  elim: bcs2 cbf2 {cbf1} => [| bsc2 bcf2 IH] //=.
  do 2![case/andP] => h1 h2; move/IH->.
  elim: bc1.1 cf1 => /= [_|t bc ?]; last by case/andP=> -> /=.
  elim: bc1.2 cf2 => /= [_|t bc ?]; last by case/andP=> -> /=.
  by rewrite h1 h2.
move=> f; elim: f false => //; last by move=> f IHf b; exact: IHf.
- by move=> t1 [] // [] [] //= ->.
- move=> f1 IHf1 f2 IHf2 [] /=; case/andP; auto; rewrite aux1; move/IHf1->.
  exact: IHf2.
move=> f1 IHf1 f2 IHf2 [] /=; case/andP; auto; rewrite aux1; move/IHf1->.
exact: IHf2.
Qed.


Lemma to_rterm_rterm : forall t r n, rterm t -> to_rterm t r n = (t, r).
Proof.
elim=> //. 
- by move=> t1 IHt1 t2 IHt2 r n /=; case/andP=> rt1 rt2; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /=; case/andP=> rt1 rt2; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.


End EvalTerm.

Module ComUnitRing.

Record class_of (R : Type) : Type := Class {
  base1 :> ComRing.class_of R;
  ext :> UnitRing.mixin_of (Ring.Pack base1 R)
}.

Coercion base2 R m := UnitRing.Class (@ext R m).

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Section Mixin.

Variables (R : ComRing.type) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Lemma mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Proof. by move=> x Ux /=; rewrite mulrC mulVx. Qed.

Lemma mulC_unitP : forall x y, y * x = 1 /\ x * y = 1 -> unit x.
Proof. move=> x y [yx _]; exact: unitPl yx. Qed.

Definition Mixin := UnitRing.EtaMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Definition pack := let k T c m := Pack (@Class T c m) T in ComRing.unpack k.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
Definition com_unitRingType cT :=
  @UnitRing.Pack (comRingType cT) (class cT) cT.

End ComUnitRing.

Canonical Structure ComUnitRing.eqType.
Canonical Structure ComUnitRing.choiceType.
Canonical Structure ComUnitRing.zmodType.
Canonical Structure ComUnitRing.ringType.
Canonical Structure ComUnitRing.unitRingType.
Canonical Structure ComUnitRing.comRingType.
Bind Scope ring_scope with ComUnitRing.sort.

Section ComUnitRingTheory.

Variable R : ComUnitRing.type.
Implicit Types x y : R.

Lemma unitr_mul : forall x y, unit (x * y) = unit x && unit y.
Proof. move=> x y; apply: commr_unit_mul; exact: mulrC. Qed.

End ComUnitRingTheory.

Module IntegralDomain.

Definition axiom (R : Ring.type) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Record class_of (R : Type) : Type :=
  Class {base :> ComUnitRing.class_of R; ext : axiom (Ring.Pack base R)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack : forall R : ComUnitRing.type, axiom R -> type :=
  let k T c ax := Pack (@Class T c ax) T in ComUnitRing.unpack k.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := ComUnitRing.Pack (class cT) cT.

End IntegralDomain.

Canonical Structure IntegralDomain.eqType.
Canonical Structure IntegralDomain.choiceType.
Canonical Structure IntegralDomain.zmodType.
Canonical Structure IntegralDomain.ringType.
Canonical Structure IntegralDomain.unitRingType.
Canonical Structure IntegralDomain.comRingType.
Canonical Structure IntegralDomain.comUnitRingType.
Bind Scope ring_scope with IntegralDomain.sort.

Section IntegralDomainTheory.

Variable R : IntegralDomain.type.
Implicit Types x y : R.

Lemma mulf_eq0 : forall x y, (x * y == 0) = (x == 0) || (y == 0).
Proof.
move=> x y; apply/eqP/idP; first by case: R x y => T [].
by case/pred2P=> ->; rewrite (mulr0, mul0r).
Qed.

Lemma mulf_neq0 : forall x y, x != 0 -> y != 0 -> x * y != 0.
Proof. move=> x y x0 y0; rewrite mulf_eq0; exact/norP. Qed.

Lemma expf_eq0 : forall x n, (x ^+ n == 0) = (n > 0) && (x == 0).
Proof.
move=> x; elim=> [|n IHn]; first by rewrite oner_eq0.
by rewrite exprS mulf_eq0 IHn andKb.
Qed.

Lemma expf_neq0 : forall x m, x != 0 -> x ^+ m != 0.
Proof. by move=> x n x_nz; rewrite expf_eq0; apply/nandP; right. Qed.

Lemma mulfI : forall x, x != 0 -> injective ( *%R x).
Proof.
move=> x nz_x y z; rewrite -[x * z]add0r; move/(canLR (addrK _)).
move/eqP; rewrite -mulrN -mulr_addr mulf_eq0 (negbTE nz_x) /=; move/eqP.
by move/(canRL (subrK _)); rewrite add0r.
Qed.

Lemma mulIf : forall x, x != 0 -> injective ( *%R^~ x).
Proof. move=> x nz_x y z; rewrite -!(mulrC x); exact: mulfI. Qed.

End IntegralDomainTheory.

Module Field.

Definition mixin_of (F : UnitRing.type) := forall x : F, x != 0 -> unit x.

Record class_of (F : Type) : Type := Class {
  base :> IntegralDomain.class_of F;
  ext: mixin_of (UnitRing.Pack base F)
}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack : forall F : IntegralDomain.type, mixin_of F -> type :=
  let k T c m := Pack (@Class T c m) T in IntegralDomain.unpack k.

Lemma IdomainMixin : forall R, mixin_of R -> IntegralDomain.axiom R.
Proof.
move=> R m x y xy0; apply/norP=> [[]]; move/m=> Ux; move/m.
by rewrite -(unitr_mulr _ Ux) xy0 unitr0.
Qed.

Section Mixins.

Variables (R : ComRing.type) (inv : R -> R).

Definition axiom := forall x, x != 0 -> inv x * x = 1.
Hypothesis mulVx : axiom.
Hypothesis inv0 : inv 0 = 0.

Lemma intro_unit : forall x y : R, y * x = 1 -> x != 0.
Proof.
move=> x y yx1; apply: contra (nonzero1r R); move/eqP=> x0.
by rewrite -yx1 x0 mulr0.
Qed.

Lemma inv_out : {in predC (predC1 0), inv =1 id}.
Proof. by move=> x; move/negbNE; move/eqP->. Qed.

Definition UnitMixin := ComUnitRing.Mixin mulVx intro_unit inv_out.

Lemma Mixin : mixin_of (UnitRing.Pack (UnitRing.Class UnitMixin) R).
Proof. by []. Qed.

End Mixins.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := IntegralDomain.Pack (class cT) cT.

End Field.

Canonical Structure Field.eqType.
Canonical Structure Field.choiceType.
Canonical Structure Field.zmodType.
Canonical Structure Field.ringType.
Canonical Structure Field.unitRingType.
Canonical Structure Field.comRingType.
Canonical Structure Field.comUnitRingType.
Canonical Structure Field.idomainType.
Bind Scope ring_scope with Field.sort.

Section FieldTheory.

Variable F : Field.type.
Implicit Types x y : F.

Lemma unitfE : forall x, unit x = (x != 0).
Proof.
move=> x; apply/idP/idP=> [Ux |]; last by case: F x => T [].
by apply/eqP=> x0; rewrite x0 unitr0 in Ux.
Qed.

Lemma mulVf: forall x, x != 0 -> x^-1 * x = 1.
Proof. by move=> x; rewrite -unitfE; exact: mulVr. Qed.
Lemma divff: forall x, x != 0 -> x / x = 1.
Proof. by move=> x; rewrite -unitfE; exact: divrr. Qed.
Definition mulfV := divff.
Lemma mulKf : forall x, x != 0 -> cancel ( *%R x) ( *%R x^-1).
Proof. by move=> x; rewrite -unitfE; exact: mulKr. Qed.
Lemma mulVKf : forall x, x != 0 -> cancel ( *%R x^-1) ( *%R x).
Proof. by move=> x; rewrite -unitfE; exact: mulVKr. Qed.
Lemma mulfK : forall x, x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by move=> x; rewrite -unitfE; exact: mulrK. Qed.
Lemma mulfVK : forall x, x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by move=> x; rewrite -unitfE; exact: divrK. Qed.
Definition divfK := mulfVK.

Lemma invf_mul : {morph (fun x => x^-1) : x y / x * y}.
Proof.
move=> x y; case: (eqVneq x 0) => [-> |nzx]; first by rewrite !(mul0r, invr0).
case: (eqVneq y 0) => [-> |nzy]; first by rewrite !(mulr0, invr0).
by rewrite mulrC invr_mul ?unitfE.
Qed.

Lemma prodf_inv : forall I r (P : pred I) (E : I -> F),
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof. by move=> I r P E; rewrite (big_morph _ invf_mul (invr1 _)). Qed.

End FieldTheory.

Module DecidableField.

Definition axiom (R : UnitRing.type) (s : formula R -> pred (seq R)) :=
  forall f e, reflect (holds f e) (s f e).

Record mixin_of (R : UnitRing.type) : Type :=
  Mixin { sat : formula R -> pred (seq R); satP : axiom sat}.

Record class_of (F : Type) : Type :=
  Class {base :> Field.class_of F; mixin:> mixin_of (UnitRing.Pack base F)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Field.unpack k.

(* Ultimately, there should be a QE Mixin constructor *)

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := Field.Pack (class cT) cT.

End DecidableField.

Canonical Structure DecidableField.eqType.
Canonical Structure DecidableField.choiceType.
Canonical Structure DecidableField.zmodType.
Canonical Structure DecidableField.ringType.
Canonical Structure DecidableField.unitRingType.
Canonical Structure DecidableField.comRingType.
Canonical Structure DecidableField.comUnitRingType.
Canonical Structure DecidableField.idomainType.
Canonical Structure DecidableField.fieldType.
Bind Scope ring_scope with DecidableField.sort.

Section DecidableFieldTheory.

Variable F : DecidableField.type.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
Proof. exact: DecidableField.satP. Qed.

Definition nExists R n f : formula R := iteri n (fun i => Exists i) f.

Lemma nExistsP : forall f n e,
  reflect (exists s, (size s == n) && (sat f (s ++ drop n e)))
          (sat (nExists n f) e).
Proof.
have drop_set_nth:
  forall e n x, @drop F n (set_nth 0 e n x) = x :: drop n.+1 e.
- move=> /= e n x; apply: (@eq_from_nth _ 0) => [|i _].
    by rewrite /= !size_drop size_set_nth -add_sub_maxn addSnnS addKn.
  rewrite nth_drop nth_set_nth /= -{2}[n]addn0 eqn_addl. 
  by case: i => //= i; rewrite nth_drop addSnnS.
move=> f n e; elim: n e => [|n IHn] e /=.
  by rewrite drop0; apply: (iffP idP) => [f_e | [[|] //]]; exists (Nil F).
case: satP => [sol | no_sol]; constructor.
  case: sol => x; move/satP; case/IHn=> /= s; case/andP=> sz_s.
  rewrite drop_set_nth -cat_rcons => f_s; exists (rcons s x).
  by rewrite size_rcons eqSS sz_s.
case; case/lastP=> // s x; rewrite size_rcons eqSS cat_rcons => f_sx.
case: no_sol; exists x; apply/satP; apply/IHn.
by exists s; rewrite drop_set_nth.
Qed.

Definition sol f n :=
  if insub [::] : {? e | sat (nExists n f) e} is Some u then
    @xchoose _ (fun x => _) (nExistsP _ _ _ (valP u))
  else nseq n 0.

Lemma solP : forall f n,
  reflect (exists2 s, size s = n & holds f s) (sat f (sol f n)).
Proof.
rewrite /sol => f n; case: insubP=> [u /= _ val_u | no_sol].
  set uP := nExistsP _ _ _ _; case/andP: (xchooseP uP).
  move: {uP}(xchoose _) => s; rewrite {u}val_u cats0.
  move/eqP=> s_n f_s; rewrite f_s; left; exists s => //; exact/satP.
apply: (iffP idP) => [f0 | [s s_n f_s]]; case/nExistsP: no_sol.
  by exists (@nseq F n 0); rewrite cats0 size_nseq eqxx.
exists s; rewrite cats0 s_n eqxx; exact/satP.
Qed.

Lemma size_sol : forall f n, size (sol f n) = n.
Proof.
rewrite /sol => f n; case: insubP=> [u /= _ _ | _]; last exact: size_nseq.
by set uP := nExistsP _ _ _ _; case/andP: (xchooseP uP); move/eqP.
Qed.

Lemma eq_sat : forall f1 f2,
  (forall e, holds f1 e <-> holds f2 e) -> sat f1 =1 sat f2.
Proof. by move=> f1 f2 eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.
 
Lemma eq_sol : forall f1 f2,
  (forall e, holds f1 e <-> holds f2 e) -> sol f1 =1 sol f2.
Proof.
rewrite /sol => f1 f2; move/eq_sat=> eqf12 n.
case: insubP=> [u /= _ val_u | no_sol].
  have u2P: sat (nExists n f2) [::].
    apply/nExistsP; case/nExistsP: (valP u) => s.
    by rewrite eqf12 /= val_u; exists s.
  rewrite (insubT (sat _) u2P); apply: eq_xchoose => s.
  by rewrite /= val_u eqf12.
rewrite insubN //; apply: contra no_sol; case/nExistsP=> s f2_s.
by apply/nExistsP; exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Implicit Arguments satP [F f e].
Implicit Arguments solP [F f n].

(* Structure of field with quantifier elimination *)
Module QE.

(* p is the elimination of a single existential quantifier *)
Definition qfree_proj_axiom (R : UnitRing.type)
  (p : nat -> (seq (term R) * seq (term R)) -> formula R) :=
  forall i dnf, qfree (p i dnf).

(* The elimination operator p preserves  validity *)
Definition holds_proj_axiom (R : UnitRing.type)
  (p : nat -> (seq (term R) * seq (term R)) -> formula R) :=
  forall i bc e,  qfree (dnf_to_formula [:: bc]) ->
    reflect  (holds (Exists i (dnf_to_formula [:: bc])) e)
             (qfree_eval e (p i bc)).

Record mixin_of (R : UnitRing.type) : Type := Mixin {
  proj : nat -> (seq (term R) * seq (term R)) -> formula R;  
  qfree_proj : qfree_proj_axiom proj;
  holds_proj : holds_proj_axiom proj
}.

Record class_of (F : Type) : Type :=
  Class {base :> Field.class_of F; mixin:> mixin_of (UnitRing.Pack base F)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Field.unpack k.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := Field.Pack (class cT) cT.

End QE.

Canonical Structure QE.eqType.
Canonical Structure QE.choiceType.
Canonical Structure QE.zmodType.
Canonical Structure QE.ringType.
Canonical Structure QE.unitRingType.
Canonical Structure QE.comRingType.
Canonical Structure QE.comUnitRingType.
Canonical Structure QE.idomainType.
Canonical Structure QE.fieldType.
Bind Scope ring_scope with QE.sort.

Section QE_theory.

Variable F : QE.type.

Definition proj := QE.proj (QE.class F).

Lemma qfree_proj : QE.qfree_proj_axiom proj.
Proof. exact: QE.qfree_proj. Qed.

Lemma holds_proj : QE.holds_proj_axiom proj.
Proof. exact: QE.holds_proj. Qed.

Notation Local true_f := (tt_form F).

Implicit Type f : (formula F).

Definition elim_aux f n := foldr (@Or F) (Not true_f) 
      (map (proj n) 
      (qfree_to_dnf f false)).

Fixpoint quantifier_elim (f : formula F) : formula F :=
  match f with
    | t1 == t2 => t1 - t2 == 0%:R
    | Unit _ => f
    | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
    | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
    | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
    | ~ f => ~ (quantifier_elim f)
    | Exists n f => elim_aux (quantifier_elim f) n
    | Forall n f => ~ elim_aux (~ quantifier_elim f) n
  end%T.

Lemma qfree_quantifier_elim : forall f, 
  rformula f -> qfree (quantifier_elim f).
Proof.
have aux : forall f n, qfree (elim_aux f n).
  move=> f n; rewrite /elim_aux; elim: qfree_to_dnf => //= x l ->.
  by rewrite qfree_proj.
by elim=> //= f1 IHf1 f2 IHf2 /=; case/andP=> rf1 rf2; rewrite IHf1 // IHf2.
Qed.


Lemma quantifier_elim_ringf : forall f e, rformula f ->
  reflect (holds f e) (qfree_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qfree_eval (set_nth 0 e n x) f.
have aux : forall f e n, qfree f ->
  reflect  (rc e n f) (qfree_eval e (elim_aux f n)).
  rewrite /elim_aux => f e n cf.
  apply: (@iffP (rc e n (dnf_to_formula (qfree_to_dnf f false)))); last first.
  - by case=> x; rewrite qfree_to_dnf_correct //; exists x.
  - by case=> x; rewrite -qfree_to_dnf_correct //; exists x.
  have := (qfree_dnf_to_formula cf).
  elim: {f cf} (qfree_to_dnf f false) => [| bc l IHl] /=.
    by rewrite eqxx; right; case; rewrite /= eqxx.
  case/andP=> hc.
  have {hc} hc : qfree (dnf_to_formula [:: bc]) by rewrite /= hc.
  move/IHl=> {IHl} IHl /=; case: holds_proj; rewrite // ?orTb ?orFb.
    move=> hx; left; case: hx => x; move/(qfree_eval_holds _ hc).
    by rewrite /= eqxx orbF; exists x; apply/orP; left.
  move=> hbf; apply: (iffP IHl).
    by case=> x hx; exists x; apply/orP; right.
  case=> x /=; case/orP=> hx; last by exists x.
  by case: hbf; exists x; apply/(qfree_eval_holds _ hc); rewrite /= hx.
elim=> //.
- move=> ? ? //= e _; rewrite (can2_eq (subrK _) (addrK _)) add0r; exact: eqP.
- move=> ? IHf1 ? IHf2 e /=; case/andP; case/(IHf1 e) => ?; last by right; case.
  by case/(IHf2 e); constructor; tauto.
- move=> ? IHf1 ? IHf2 e /=; case/andP; case/(IHf1 e) => ?; first by left; left.
  by case/(IHf2 e); constructor; tauto.
- move=> ? IHf1 ? IHf2 e /=; case/andP; case/(IHf1 e) => ?; last by left.
  by case/(IHf2 e); constructor; tauto.
- by move=> f IHf e /=; case/(IHf e); constructor; tauto.
- move=> n f IHf e /= rf.
  by apply: (iffP (aux _ _ _ (qfree_quantifier_elim rf)));
    case=> x hx; exists x; apply/IHf.
- move=> n f IHf e /= rf; case: (aux (~_)%T e n (qfree_quantifier_elim rf)).
    by move=> hf; right; case : hf => x hx; move/(_ x)=> hx'; case/IHf: hx.
by move=> hf; left=> x; apply/IHf=> //; apply/idPn=> hx; case: hf; exists x.
Qed.

Definition proj_sat f e := qfree_eval e (quantifier_elim (to_rformula f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof. 
rewrite /DecidableField.axiom /proj_sat; move=> f e.
by apply: (iffP (quantifier_elim_ringf _ ( rformula_to_rformula _))); 
move/to_rformula_equiv.
Qed.

Definition QEDecidableFieldMixin := DecidableField.Mixin proj_satP.

Canonical Structure QEDecidableField := 
  Eval hnf in DecidableField.pack QEDecidableFieldMixin.

End QE_theory.


Module ClosedField.

(* Axiom == all non-constant monic polynomials have a root *)
Definition axiom (R : Ring.type) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Record class_of (F : Type) : Type :=
  Class {base :> DecidableField.class_of F; _ : axiom (Ring.Pack base F)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack :=
  let k T c ax := Pack (@Class T c ax) T in DecidableField.unpack k.

(* There should eventually be a constructor from polynomial resolution *)
(* that builds the DecidableField mixin using QE.                      *)

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := Zmodule.Pack (class cT) cT.
Definition ringType cT := Ring.Pack (class cT) cT.
Definition comRingType cT := ComRing.Pack (class cT) cT.
Definition unitRingType cT := UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := Field.Pack (class cT) cT.
Coercion decFieldType cT := DecidableField.Pack (class cT) cT.

End ClosedField.

Canonical Structure ClosedField.eqType.
Canonical Structure ClosedField.choiceType.
Canonical Structure ClosedField.zmodType.
Canonical Structure ClosedField.ringType.
Canonical Structure ClosedField.unitRingType.
Canonical Structure ClosedField.comRingType.
Canonical Structure ClosedField.comUnitRingType.
Canonical Structure ClosedField.idomainType.
Canonical Structure ClosedField.fieldType.
Canonical Structure ClosedField.decFieldType.

Bind Scope ring_scope with ClosedField.sort.

Section ClosedFieldTheory.

Variable F : ClosedField.type.

Lemma solve_monicpoly : ClosedField.axiom F.
Proof. by case: F => ? []. Qed.

End ClosedFieldTheory.

Module Theory.

Definition addrA := addrA.
Definition addrC := addrC.
Definition add0r := add0r.
Definition addNr := addNr.
Definition addr0 := addr0.
Definition addrN := addrN.
Definition subrr := subrr.
Definition addrCA := addrCA.
Definition addrAC := addrAC.
Definition addKr := addKr.
Definition addNKr := addNKr.
Definition addrK := addrK.
Definition addrNK := addrNK.
Definition subrK := subrK.
Definition addrI := addrI.
Definition addIr := addIr.
Definition opprK := opprK.
Definition oppr0 := oppr0.
Definition oppr_eq0 := oppr_eq0.
Definition oppr_add := oppr_add.
Definition oppr_sub := oppr_sub.
Definition subr_eq := subr_eq.
Definition subr_eq0 := subr_eq0.
Definition sumr_opp := sumr_opp.
Definition sumr_sub := sumr_sub.
Definition sumr_muln := sumr_muln.
Definition sumr_const := sumr_const.
Definition mulr0n := mulr0n.
Definition mulrS := mulrS.
Definition mulr1n := mulr1n.
Definition mulrSr := mulrSr.
Definition mul0rn := mul0rn.
Definition oppr_muln := oppr_muln.
Definition mulrn_addl := mulrn_addl.
Definition mulrn_addr := mulrn_addr.
Definition mulrnA := mulrnA.
Definition mulrnAC := mulrnAC.
Definition mulrA := mulrA.
Definition mul1r := mul1r.
Definition mulr1 := mulr1.
Definition mulr_addl := mulr_addl.
Definition mulr_addr := mulr_addr.
Definition nonzero1r := nonzero1r.
Definition oner_eq0 := oner_eq0.
Definition mul0r := mul0r.
Definition mulr0 := mulr0.
Definition mulrN := mulrN.
Definition mulNr := mulNr.
Definition mulrNN := mulrNN.
Definition mulN1r := mulN1r.
Definition mulrN1 := mulrN1.
Definition mulr_natr := mulr_natr.
Definition mulr_natl := mulr_natl.
Definition natr_add := natr_add.
Definition natr_mul := natr_mul.
Definition expr0 := expr0.
Definition exprS := exprS.
Definition expr1 := expr1.
Definition exp1rn := exp1rn.
Definition exprn_addr := exprn_addr.
Definition exprSr := exprSr.
Definition commr_sym := commr_sym.
Definition commr_refl := commr_refl.
Definition commr0 := commr0.
Definition commr1 := commr1.
Definition commr_opp := commr_opp.
Definition commrN1 := commrN1.
Definition commr_add := commr_add.
Definition commr_muln := commr_muln.
Definition commr_mul := commr_mul.
Definition commr_nat := commr_nat.
Definition commr_exp := commr_exp.
Definition commr_exp_mull := commr_exp_mull.
Definition exprn_mulnl := exprn_mulnl.
Definition exprn_mulr := exprn_mulr.
Definition signr_odd := signr_odd.
Definition signr_eq0 := signr_eq0.
Definition signr_addb := signr_addb.
Definition exprN := exprN.
Definition prodr_const := prodr_const.
Definition mulrC := mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition exprn_mull := exprn_mull.
Definition prodr_exp := prodr_exp.
Definition mulrV := mulrV.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP := unitrP.
Definition mulKr := mulKr.
Definition mulVKr := mulVKr.
Definition mulrK := mulrK.
Definition mulrVK := mulrVK.
Definition divrK := divrK.
Definition mulrI := mulrI.
Definition mulIr := mulIr.
Definition commr_inv := commr_inv.
Definition unitrE := unitrE.
Definition invrK := invrK.
Definition invr_inj := invr_inj.
Definition unitr_inv := unitr_inv.
Definition unitr1 := unitr1.
Definition invr1 := invr1.
Definition unitr0 := unitr0.
Definition invr0 := invr0.
Definition unitr_opp := unitr_opp.
Definition invrN := invrN.
Definition unitr_mull := unitr_mull.
Definition unitr_mulr := unitr_mulr.
Definition invr_mul := invr_mul.
Definition invr_eq0 := invr_eq0.
Definition invr_neq0 := invr_neq0.
Definition commr_unit_mul := commr_unit_mul.
Definition unitr_exp := unitr_exp.
Definition unitr_pexp := unitr_pexp.
Definition expr_inv := expr_inv.
Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition unitr_mul := unitr_mul.
Definition mulf_eq0 := mulf_eq0.
Definition mulf_neq0 := mulf_neq0.
Definition expf_eq0 := expf_eq0.
Definition expf_neq0 := expf_neq0.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition mulfV := mulfV.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulVKf := mulVKf.
Definition mulfK := mulfK.
Definition mulfVK := mulfVK.
Definition divfK := divfK.
Definition invf_mul := invf_mul.
Definition prodf_inv := prodf_inv.
Definition satP := @satP.
Definition eq_sat := eq_sat.
Definition solP := @solP.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition ring_morphism := ring_morphism.
Definition solve_monicpoly := solve_monicpoly.

Lemma ringM_sub : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> {morph f : x y / x - y >-> x - y}.
Proof. exact: ringM_sub. Qed.

Lemma ringM_0 : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> f 0 = 0.
Proof. exact: ringM_0. Qed.

Lemma ringM_1 : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> f 1 = 1.
Proof. exact: ringM_1. Qed.

Lemma ringM_opp : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> {morph f : x / - x >-> - x}.
Proof. exact: ringM_opp. Qed.

Lemma ringM_add : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> {morph f : x y / x + y >-> x + y}.
Proof. exact: ringM_add. Qed.

Lemma ringM_sum : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f ->
       forall (I : Type) (r : seq I) (P : pred I) (F : I -> aR),
       f (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) f (F i).
Proof. exact: ringM_sum. Qed.

Lemma ringM_mul : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> {morph f : x y / x * y >-> x * y}.
Proof. exact: ringM_mul. Qed.

Lemma ringM_prod : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f ->
       forall (I : Type) (r : seq I) (P : pred I) (F : I -> aR),
       f (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) f (F i).
Proof. exact: ringM_prod. Qed.

Lemma ringM_nat : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f -> forall n : nat, f n%:R = n%:R.
Proof. exact: ringM_nat. Qed.

Lemma ringM_exp : forall (aR rR : Ring.type) (f : aR -> rR),
       ring_morphism f ->
       forall n : nat, {morph f : x / x ^+ n >-> x ^+ n}.
Proof. exact: ringM_exp. Qed.

Lemma comp_ringM :
 forall (aR' aR rR : Ring.type) (f : aR -> rR) (g : aR' -> aR),
       ring_morphism f -> ring_morphism g -> ring_morphism (f \o g).
Proof. exact: comp_ringM. Qed.


Implicit Arguments satP [F f e].
Implicit Arguments solP [F f n].
Prenex Implicits satP solP.

End Theory.

End GRing.

Canonical Structure GRing.Zmodule.eqType.
Canonical Structure GRing.Zmodule.choiceType.
Canonical Structure GRing.Ring.eqType.
Canonical Structure GRing.Ring.choiceType.
Canonical Structure GRing.Ring.zmodType.
Canonical Structure GRing.UnitRing.eqType.
Canonical Structure GRing.UnitRing.choiceType.
Canonical Structure GRing.UnitRing.zmodType.
Canonical Structure GRing.UnitRing.ringType.
Canonical Structure GRing.ComRing.eqType.
Canonical Structure GRing.ComRing.choiceType.
Canonical Structure GRing.ComRing.zmodType.
Canonical Structure GRing.ComRing.ringType.
Canonical Structure GRing.ComUnitRing.eqType.
Canonical Structure GRing.ComUnitRing.choiceType.
Canonical Structure GRing.ComUnitRing.zmodType.
Canonical Structure GRing.ComUnitRing.ringType.
Canonical Structure GRing.ComUnitRing.unitRingType.
Canonical Structure GRing.ComUnitRing.comRingType.
Canonical Structure GRing.ComUnitRing.com_unitRingType.
Canonical Structure GRing.IntegralDomain.eqType.
Canonical Structure GRing.IntegralDomain.choiceType.
Canonical Structure GRing.IntegralDomain.zmodType.
Canonical Structure GRing.IntegralDomain.ringType.
Canonical Structure GRing.IntegralDomain.unitRingType.
Canonical Structure GRing.IntegralDomain.comRingType.
Canonical Structure GRing.IntegralDomain.comUnitRingType.
Canonical Structure GRing.Field.eqType.
Canonical Structure GRing.Field.choiceType.
Canonical Structure GRing.Field.zmodType.
Canonical Structure GRing.Field.ringType.
Canonical Structure GRing.Field.unitRingType.
Canonical Structure GRing.Field.comRingType.
Canonical Structure GRing.Field.comUnitRingType.
Canonical Structure GRing.Field.idomainType.
Canonical Structure GRing.DecidableField.eqType.
Canonical Structure GRing.DecidableField.choiceType.
Canonical Structure GRing.DecidableField.zmodType.
Canonical Structure GRing.DecidableField.ringType.
Canonical Structure GRing.DecidableField.unitRingType.
Canonical Structure GRing.DecidableField.comRingType.
Canonical Structure GRing.DecidableField.comUnitRingType.
Canonical Structure GRing.DecidableField.idomainType.
Canonical Structure GRing.DecidableField.fieldType.
Canonical Structure GRing.ClosedField.eqType.
Canonical Structure GRing.ClosedField.choiceType.
Canonical Structure GRing.ClosedField.zmodType.
Canonical Structure GRing.ClosedField.ringType.
Canonical Structure GRing.ClosedField.unitRingType.
Canonical Structure GRing.ClosedField.comRingType.
Canonical Structure GRing.ClosedField.comUnitRingType.
Canonical Structure GRing.ClosedField.idomainType.
Canonical Structure GRing.ClosedField.fieldType.
Canonical Structure GRing.ClosedField.decFieldType.

Canonical Structure GRing.add_monoid.
Canonical Structure GRing.add_comoid.
Canonical Structure GRing.mul_monoid.
Canonical Structure GRing.mul_comoid.
Canonical Structure GRing.muloid.
Canonical Structure GRing.addoid.

Bind Scope ring_scope with GRing.Zmodule.sort.
Bind Scope ring_scope with GRing.Ring.sort.
Bind Scope ring_scope with GRing.ComRing.sort.
Bind Scope ring_scope with GRing.UnitRing.sort.
Bind Scope ring_scope with GRing.ComUnitRing.sort.
Bind Scope ring_scope with GRing.IntegralDomain.sort.
Bind Scope ring_scope with GRing.Field.sort.
Bind Scope ring_scope with GRing.DecidableField.sort.
Bind Scope ring_scope with GRing.ClosedField.sort.

Notation "0" := (GRing.zero _) : ring_scope.
Notation "-%R" := (@GRing.opp _) : ring_scope.
Notation "- x" := (GRing.opp x) : ring_scope.
Notation "+%R" := (@GRing.add _).
Notation "x + y" := (GRing.add x y) : ring_scope.
Notation "x - y" := (GRing.add x (- y)) : ring_scope.
Notation "x *+ n" := (GRing.natmul x n) : ring_scope.
Notation "x *- n" := (GRing.natmul (- x) n) : ring_scope.

Notation "1" := (GRing.one _) : ring_scope.
Notation "- 1" := (- (1))%R : ring_scope.

Notation "n %:R" := (GRing.natmul 1 n) : ring_scope.
Notation "*%R" := (@GRing.mul _).
Notation "x * y" := (GRing.mul x y) : ring_scope.
Notation "x ^+ n" := (GRing.exp x n) : ring_scope.
Notation "x ^-1" := (GRing.inv x) : ring_scope.
Notation "x ^- n" := (x ^+ n)^-1%R : ring_scope.
Notation "x / y" := (GRing.mul x y^-1) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.

Implicit Arguments GRing.unitDef [].

Bind Scope term_scope with GRing.term.
Bind Scope term_scope with GRing.formula.

Notation "''X_' i" := (GRing.Var _ i)
  (at level 8, i at level 2, format "''X_' i") : term_scope.
Notation "n %:R" := (GRing.NatConst _ n) : term_scope.
Infix "+" := GRing.Add : term_scope.
Notation "- t" := (GRing.Opp t) : term_scope.
Notation "t - u" := (GRing.Add t (- u)) : term_scope.
Infix "*" := GRing.Mul : term_scope.
Infix "*+" := GRing.NatMul : term_scope.
Notation "t ^-1" := (GRing.Inv t) : term_scope.
Notation "t / u" := (GRing.Mul t u^-1) : term_scope.
Infix "^+" := GRing.Exp : term_scope.
Infix "==" := GRing.Equal : term_scope.
Infix "/\" := GRing.And : term_scope.
Infix "\/" := GRing.Or : term_scope.
Infix "==>" := GRing.Implies : term_scope.
Notation "~ f" := (GRing.Not f) : term_scope.
Notation "'exists' ''X_' i , f" := (GRing.Exists i f)
  (at level 200, i at level 2,
   format "'[hv' 'exists'  ''X_' i , '/ '  f ']'") : term_scope.
Notation "'forall' ''X_' i , f" := (GRing.Forall i f)
  (at level 200, i at level 2,
   format "'[hv' 'forall'  ''X_' i , '/ '  f ']'") : term_scope.

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%R/0%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i \in A | P ) F" :=
  (\big[+%R/0%R]_(i \in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i \in A ) F" :=
  (\big[+%R/0%R]_(i \in A) F%R) : ring_scope.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%R/1%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[*%R/1%R]_(i \in A | P%B) F%R) : ring_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[*%R/1%R]_(i \in A) F%R) : ring_scope.

Notation zmodType := GRing.Zmodule.type.
Notation ZmodType := GRing.Zmodule.pack.
Notation ZmodMixin := GRing.Zmodule.Mixin.
Notation "[ 'zmodType' 'of' T 'for' cT ]" :=
    (@GRing.Zmodule.repack cT (@GRing.Zmodule.Pack T) T)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'zmodType' 'of' T ]" :=
    (GRing.Zmodule.repack (fun c => @GRing.Zmodule.Pack T c) T)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.

Notation ringType := GRing.Ring.type.
Notation RingType := GRing.Ring.pack.
Notation RingMixin := GRing.Ring.Mixin.
Notation RevRingType := GRing.RevRingType.
Notation "[ 'ringType' 'of' T 'for' cT ]" :=
    (@GRing.Ring.repack cT (@GRing.Ring.Pack T) T)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" :=
    (GRing.Ring.repack (fun c => @GRing.Ring.Pack T c) T)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.

Notation comRingType := GRing.ComRing.type.
Notation ComRingType := GRing.ComRing.pack.
Notation ComRingMixin := GRing.ComRing.RingMixin.
Notation "[ 'comRingType' 'of' T 'for' cT ]" :=
    (@GRing.ComRing.repack cT (@GRing.ComRing.Pack T) T)
  (at level 0, format "[ 'comRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comRingType' 'of' T ]" :=
    (GRing.ComRing.repack (fun c => @GRing.ComRing.Pack T c) T)
  (at level 0, format "[ 'comRingType'  'of'  T ]") : form_scope.

Notation unitRingType := GRing.UnitRing.type.
Notation UnitRingType := GRing.UnitRing.pack.
Notation UnitRingMixin := GRing.UnitRing.EtaMixin.
Notation Com_UnitRingType := GRing.UnitRing.comPack.
Notation "[ 'unitRingType' 'of' T 'for' cT ]" :=
    (@GRing.UnitRing.repack cT (@GRing.UnitRing.Pack T) T)
  (at level 0, format "[ 'unitRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'unitRingType' 'of' T ]" :=
    (GRing.UnitRing.repack (fun c => @GRing.UnitRing.Pack T c) T)
  (at level 0, format "[ 'unitRingType'  'of'  T ]") : form_scope.

Notation comUnitRingType := GRing.ComUnitRing.type.
Notation ComUnitRingType := GRing.ComUnitRing.pack.
Notation ComUnitRingMixin := GRing.ComUnitRing.Mixin.
Notation "[ 'comUnitRingType' 'of' T 'for' cT ]" :=
    (@GRing.ComUnitRing.repack cT (@GRing.ComUnitRing.Pack T) T)
  (at level 0,
   format "[ 'comUnitRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comUnitRingType' 'of' T ]" :=
    (GRing.ComUnitRing.repack (fun c => @GRing.ComUnitRing.Pack T c) T)
  (at level 0, format "[ 'comUnitRingType'  'of'  T ]") : form_scope.

Notation idomainType := GRing.IntegralDomain.type.
Notation IdomainType := GRing.IntegralDomain.pack.
Notation "[ 'idomainType' 'of' T 'for' cT ]" :=
    (@GRing.IntegralDomain.repack cT (@GRing.IntegralDomain.Pack T) T)
  (at level 0, format "[ 'idomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'idomainType' 'of' T ]" :=
    (GRing.IntegralDomain.repack (fun c => @GRing.IntegralDomain.Pack T c) T)
  (at level 0, format "[ 'idomainType'  'of'  T ]") : form_scope.

Notation fieldType := GRing.Field.type.
Notation FieldType := GRing.Field.pack.
Notation FieldUnitMixin := GRing.Field.UnitMixin.
Notation FieldIdomainMixin := GRing.Field.IdomainMixin.
Notation FieldMixin := GRing.Field.Mixin.
Notation "[ 'fieldType' 'of' T 'for' cT ]" :=
    (@GRing.Field.repack cT (@GRing.Field.Pack T) T)
  (at level 0, format "[ 'fieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'fieldType' 'of' T ]" :=
    (GRing.Field.repack (fun c => @GRing.Field.Pack T c) T)
  (at level 0, format "[ 'fieldType'  'of'  T ]") : form_scope.

Notation decFieldType := GRing.DecidableField.type.
Notation DecFieldType := GRing.DecidableField.pack.
Notation DecFieldMixin := GRing.DecidableField.Mixin.
Notation "[ 'decFieldType' 'of' T 'for' cT ]" :=
    (@GRing.DecidableField.repack cT (@GRing.DecidableField.Pack T) T)
  (at level 0, format "[ 'decFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'decFieldType' 'of' T ]" :=
    (GRing.DecidableField.repack (fun c => @GRing.DecidableField.Pack T c) T)
  (at level 0, format "[ 'decFieldType'  'of'  T ]") : form_scope.

Notation closedFieldType := GRing.ClosedField.type.
Notation ClosedFieldType := GRing.ClosedField.pack.
Notation "[ 'closedFieldType' 'of' T 'for' cT ]" :=
    (@GRing.ClosedField.repack cT (@GRing.ClosedField.Pack T) T)
  (at level 0,
   format "[ 'closedFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'closedFieldType' 'of' T ]" :=
    (GRing.ClosedField.repack (fun c => @GRing.ClosedField.Pack T c) T)
  (at level 0, format "[ 'closedFieldType'  'of'  T ]") : form_scope.
