(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigops prime binomial.

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
(*      ZmodType R M    == packs the mixin M to build a Zmodule of type      *)
(*                         zmodType. (The underlying type R should have a    *)
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
(*      RingType R M  == packs the ring mixin M to build a ring on type R    *)
(*      RevRingType T == repacks T to build the ring where the               *)
(*                       multiplicative law is reversed ( x *' y = y * x )   *)
(*      1             == the multiplicative identity element of a Ring       *)
(*      n%:R          == the ring image of a nat n (e.g., 1%:R := 1%R)       *)
(*      x * y         == the multiplication operation of a ring              *)
(*    \prod_<range> e == iterated product for a ring (cf bigops.v)           *)
(*      x ^+ y        == the exponentiation operation of a ring              *)
(*     GRing.comm x y <=> x and y commute, i.e., x * y = y * x               *)
(*      [char R]      == the characteristic of R, i.e., the set of prime     *)
(*                       numbers p such that p%:R = 0 in R. The set [char p] *)
(*                       has a most one element, and is represented as a     *)
(*                       pred_nat collective predicate (see prime.v); thus   *)
(*                       the statement p \in [char R] can be read as "R has  *)
(*                       characteristic p", while [char R] =i pred0 means    *)
(*                       "R has characteristic 0" when R is a field.         *)
(* Frobenius_aut chRp == the Frobenius automorphism mapping x : R to x ^+ p, *)
(*                       where chRp : p \in [char R] is a proof that R has   *)
(*                       indeed (non-zero) characteristic p.                 *)
(*                                                                           *)
(*  * Commutative Ring                                                       *)
(*      comRingType      == type for commutative ring structure              *)
(*    ComRingType R mulC == packs mulC to build a commutative ring.          *)
(*                          (The underlying type R should have a ring        *)
(*                          canonical structure)                             *)
(*      ComRingMixin     == builds the mixin containing the definitions of a *)
(*                          *non commutative* ring, using the commutativity  *)
(*                          to decrease the number of axioms.                *)
(*                                                                           *)
(*  * Unit Ring                                                              *)
(*      unitRingType   == type for unit ring structure                       *)
(*      UnitRingMixin  == builds the mixin containing the definitions        *)
(*                        of a unit ring. (The underlying type should        *)
(*                        have a ring canonical structure)                   *)
(*    UnitRingType R M == packs the unit ring mixin M to build a unit ring.  *)
(*                        WARNING: while it is possible to omit R for most   *)
(*                        of the xxxType functions, R MUST be explicitly     *)
(*                        given when UnitRingType is used with a mixin       *)
(*                        produced by ComUnitRingMixin, otherwise the        *)
(*                        resulting structure will have the WRONG sort and   *)
(*                        will not be used by type inference.                *)
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
(*                           the commutative property. The underlying type   *)
(*                           should have a commutative ring canonical        *)
(*                           structure. WARNING: ALWAYS give an explicit     *)
(*                           type argument to UnitRingType along with a      *)
(*                           mixin produced by ComUnitRingMixin (see above). *)
(*                                                                           *)
(*  * Integral Domain (integral, commutative, unit ring)                     *)
(*      idomainType       == type for integral domain structure              *)
(*      IdomainType R M   == packs the idomain mixin M to build a integral   *)
(*                           domain. (The underlying type R should have a    *)
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
(*      FieldType R M     == packs the field mixin M to build a field        *)
(*                           (The underlying type R should have a            *)
(*                           integral domain canonical structure)            *)
(*                                                                           *)
(*  * Decidable Field                                                        *)
(*      decFieldType      == type for decidable field structure              *)
(*      DecFieldMixin     == builds the mixin containing the definitions of  *)
(*                           a decidable Field. (The underlying type should  *)
(*                           have a unit ring canonical structure)           *)
(*      DecFieldType R M  == packs the decidable field mixin M to build a    *)
(*                           decidable field. (The underlying type R should  *)
(*                           have a field canonical structure)               *)
(*      GRing.term R      == the type of formal expressions in a unit ring R *)
(*                           with formal variables 'X_k, k : nat, and        *)
(*                           manifest constants x%:T, x : R. The notation of *)
(*                           all the ring operations is redefined for terms, *)
(*                           in scope %T.                                    *)
(*      GRing.formula R   == the type of first order formulas over R; the %T *)
(*                           scope binds the logical connectives /\, \/, ~,  *)
(*                           ==>, ==, and != to formulae; GRing.True/False   *)
(*                           and GRing.Bool b denote constant formulae, and  *)
(*                           quantifiers are written 'forall/'exists 'X_k, f *)
(*                           GRing.Unit x tests for ring units, and the      *)
(*                           the construct Pick p_f t_f e_f can be used to   *)
(*                           emulate the pick function defined in fintype.v. *)
(*      GRing.eval e t    == the value of term t with valuation e : seq R    *)
(*                           (e maps 'X_i to e`_i)                           *)
(*  GRing.same_env e1 e2 <=> environments e1 and e2 are extensionally equal  *)
(*    GRing.qf_eval e f   == the value (in bool) of a quantifier-free f.     *)
(*      GRing.qf_form f   == f is quantifier-free.                           *)
(*      GRing.holds e f   == the intuitionistic CiC interpretation of the    *)
(*                           formula f holds with valuation e                *)
(*      GRing.sat e f     == valuation e satisfies f (only in a decField)    *)
(*      GRing.sol n f     == a sequence e of size n such that e satisfies f, *)
(*                           if one exists, or [::] if there is no such e    *)
(*                                                                           *)
(*  * Closed Field                                                           *)
(*      closedFieldType   == type for closed field structure                 *)
(*    ClosedFieldType R M == packs the closed field mixin M to build a       *)
(*                           closed field. (The underlying type R should     *)
(*                           have a decidable field canonical structure.)    *)
(*                                                                           *)
(* * Morphism                                                                *)
(*     GRing.morphism f <=> f is a ring morphism: f commutes with 0, +, -,   *)
(*                          *, 1, and with ^-1 and / in integral domains.    *)
(*                   x^f == the image of x under some morphism. This         *)
(*                          notation is only reserved (not defined) here;    *)
(*                          it is bound locally in sections where some       *)
(*                          morphism is used heavily (e.g., the container    *)
(*                          morphism in the parametricity sections of poly   *)
(*                          and matrix, or the Frobenius section here).      *)
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
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "[ 'char' F ]" (at level 0, format "[ 'char'  F ]").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").
(* Patch for recurring Coq parser bug: Coq seg faults when a level 200 *)
(* notation is used as a pattern.                                      *)
Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Reserved Notation "x ^f" (at level 2, left associativity, format "x ^f").

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

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
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.

End Zmodule.

Canonical Structure Zmodule.eqType.
Canonical Structure Zmodule.choiceType.
Bind Scope ring_scope with Zmodule.sort.

Definition zero M := Zmodule.zero (Zmodule.class M).
Definition opp M := Zmodule.opp (Zmodule.class M).
Definition add M := Zmodule.add (Zmodule.class M).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Definition natmul M x n := nosimpl iterop _ n +%R x (zero M).

Local Notation "x *+ n" := (natmul x n) : ring_scope.
Local Notation "x *- n" := ((- x) *+ n) : ring_scope.

Local Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Local Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Local Notation "\sum_ ( i \in A ) F" := (\big[+%R/0]_(i \in A) F).

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section ZmoduleTheory.

Variable M : Zmodule.type.
Implicit Types x y : M.

Lemma addrA : @associative M +%R. Proof. by case M => T [? []]. Qed.
Lemma addrC : @commutative M M +%R. Proof. by case M => T [? []]. Qed.
Lemma add0r : @left_id M M 0 +%R. Proof. by case M => T [? []]. Qed.
Lemma addNr : @left_inverse M M M 0 -%R +%R. Proof. by case M => T [? []]. Qed.

Lemma addr0 : @right_id M M 0 +%R.
Proof. by move=> x; rewrite addrC add0r. Qed.
Lemma addrN : @right_inverse M M M 0 -%R +%R.
Proof. by move=> x; rewrite addrC addNr. Qed.
Definition subrr := addrN.

Canonical Structure add_monoid := Monoid.Law addrA add0r addr0.
Canonical Structure add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative M M +%R. Proof. exact: mulmCA. Qed.
Lemma addrAC : @right_commutative M M +%R. Proof. exact: mulmAC. Qed.

Lemma addKr : @left_loop M M -%R +%R.
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.
Lemma addNKr : @rev_left_loop M M -%R +%R.
Proof. by move=> x y; rewrite addrA addrN add0r. Qed.
Lemma addrK : @right_loop M M -%R +%R.
Proof. by move=> x y; rewrite -addrA addrN addr0. Qed.
Lemma addrNK : @rev_right_loop M M -%R +%R.
Proof. by move=> x y; rewrite -addrA addNr addr0. Qed.
Definition subrK := addrNK.
Lemma addrI : @right_injective M M M +%R.
Proof. move=> x; exact: can_inj (addKr x). Qed.
Lemma addIr : @left_injective M M M +%R.
Proof. move=> y; exact: can_inj (addrK y). Qed.
Lemma opprK : @involutive M -%R.
Proof. by move=> x; apply: (@addIr (- x)); rewrite addNr addrN. Qed.
Lemma oppr0 : -0 = 0 :> M.
Proof. by rewrite -[-0]add0r subrr. Qed.
Lemma oppr_eq0 : forall x, (- x == 0) = (x == 0).
Proof. by move=> x; rewrite (inv_eq opprK) oppr0. Qed.

Lemma subr0 : forall x, x - 0 = x. Proof. by move=> x; rewrite oppr0 addr0. Qed.
Lemma sub0r : forall x, 0 - x = - x. Proof. by move=> x; rewrite add0r. Qed.

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

Lemma mulrb : forall x (b : bool), x *+ b = (if b then x else 0).
Proof. by move=> x []. Qed.

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

Lemma sumr_muln_r :  forall x I r P (F : I -> nat),
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Proof. by move=> x I r P F; rewrite (big_morph _ (mulrn_addr x) (erefl _)). Qed.

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
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.

End Ring.

Bind Scope ring_scope with Ring.sort.
Canonical Structure Ring.eqType.
Canonical Structure Ring.choiceType.
Canonical Structure Ring.zmodType.

Definition one (R : Ring.type) : R := Ring.one (Ring.class R).
Definition mul (R : Ring.type) : R -> R -> R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).

Local Notation "1" := (one _).
Local Notation "- 1" := (- (1)).
Local Notation "n %:R" := (1 *+ n).
Local Notation "*%R" := (@mul _).
Local Notation "x * y" := (mul x y).
Local Notation "x ^+ n" := (exp x n).

Local Notation "\prod_ ( i <- r | P ) F" := (\big[*%R/1]_(i <- r | P) F).
Local Notation "\prod_ ( i \in A ) F" := (\big[*%R/1]_(i \in A) F).

(* The "field" characteristic; the definition, and many of the theorems,     *)
(* has to apply to rings as well; indeed, we need the Frobenius automorphism *)
(* results for a non commutative ring in the proof of Gorenstein 2.6.3.      *)
Definition char (R : Ring.type) of phant R : nat_pred :=
  [pred p | prime p && (p%:R == 0 :> R)].

Local Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.

Section RingTheory.

Variable R : Ring.type.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R. Proof. by case R => T [? []]. Qed.
Lemma mul1r : @left_id R R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr1 : @right_id R R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr_addl : @left_distributive R R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma mulr_addr : @right_distributive R R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma nonzero1r : 1 != 0 :> R. Proof. by case R => T [? []]. Qed.
Lemma oner_eq0 : (1 == 0 :> R) = false. Proof. exact: negbTE nonzero1r. Qed.

Lemma mul0r : @left_zero R R 0 *%R.
Proof.
by move=> x; apply: (@addIr _ (1 * x)); rewrite -mulr_addl !add0r mul1r.
Qed.
Lemma mulr0 : @right_zero R R 0 *%R.
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

Lemma mulr_subl : forall x y z, (y - z) * x = y * x - z * x.
Proof. by move=> x y z; rewrite mulr_addl mulNr. Qed.

Lemma mulr_subr : forall x y z, x * (y - z) = x * y - x * z.
Proof. by move=> x y z; rewrite mulr_addr mulrN. Qed.

Lemma mulrnAl : forall x y n, (x *+ n) * y = (x * y) *+ n.
Proof.
by move=> x y; elim=> [|n IHn]; rewrite ?mul0r // !mulrS mulr_addl IHn.
Qed.

Lemma mulrnAr : forall x y n, x * (y *+ n) = (x * y) *+ n.
Proof.
by move=> x y; elim=> [|n IHn]; rewrite ?mulr0 // !mulrS mulr_addr IHn.
Qed.

Lemma mulr_natl : forall x n, n%:R * x = x *+ n.
Proof. by move=> x n; rewrite mulrnAl mul1r. Qed.

Lemma mulr_natr : forall x n, x * n%:R = x *+ n.
Proof. by move=> x n; rewrite mulrnAr mulr1. Qed.

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

Lemma commr_sign : forall x n, comm x ((-1) ^+ n).
Proof. move=> x n; exact: (commr_exp n (commrN1 x)). Qed.

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

Lemma prodr_exp_r : forall x I r P (F : I -> nat),
  \prod_(i <- r | P i) x ^+ F i = x ^+ (\sum_(i <- r | P i) F i).
Proof. by move=> x I r P F; rewrite (big_morph _ (exprn_addr _) (erefl _)). Qed.

Lemma prodr_opp : forall (I : finType) (A : pred I) (F : I -> R),
  \prod_(i \in A) - F i = (- 1) ^+ #|A| * \prod_(i \in A) F i.
Proof.
move=> I A F; rewrite -sum1_card /= -!(big_filter _ A) !unlock.
elim: {A}(filter _ _) => /= [|i r ->]; first by rewrite mul1r.
by rewrite mulrA -mulN1r (commr_exp _ (commrN1 _)) exprSr !mulrA.
Qed.

Lemma exprn_addl_comm : forall x y n, comm x y ->
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ bin n i.
Proof.
move=> x y n cxy.
elim: n => [|n IHn]; rewrite big_ord_recl mulr1 ?big_ord0 ?addr0 //=.
rewrite exprS {}IHn /= mulr_addl !big_distrr /= big_ord_recl mulr1 subn0.
rewrite !big_ord_recr /= !binn !subnn !mul1r !subn0 bin0 !exprS -addrA.
congr (_ + _); rewrite addrA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite !mulrnAr !mulrA -exprS -leq_subS ?(valP i) //.
by rewrite  subSS (commr_exp _ (commr_sym cxy)) -mulrA -exprS -mulrn_addr.
Qed.

Lemma exprn_subl_comm : forall x y n, comm x y ->
  (x - y) ^+ n = \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ bin n i.
Proof.
move=> x y n cxy; rewrite exprn_addl_comm; last exact: commr_opp.
by apply: eq_bigr => i _; congr (_ *+ _); rewrite -commr_sign -mulrA -exprN.
Qed.

Lemma subr_expn_comm : forall x y n, comm x y ->
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof.
move=> x y [|n] cxy; first by rewrite big_ord0 mulr0 subrr.
rewrite mulr_subl !big_distrr big_ord_recl big_ord_recr /= subnn mulr1 mul1r.
rewrite subn0 -!exprS oppr_add -!addrA; congr (_ + _); rewrite addrA -sumr_sub.
rewrite big1 ?add0r // => i _; rewrite !mulrA -exprS -leq_subS ?(valP i) //.
by rewrite subSS (commr_exp _ (commr_sym cxy)) -mulrA -exprS subrr.
Qed.

Lemma subr_expn_1 : forall x n, x ^+ n - 1 = (x - 1) * (\sum_(i < n) x ^+ i).
Proof.
move=> x n; rewrite -!(oppr_sub 1) mulNr -{1}(exp1rn n).
rewrite (subr_expn_comm _ (commr_sym (commr1 x))); congr (- (_ * _)).
by apply: eq_bigr => i _; rewrite exp1rn mul1r.
Qed.

Definition Frobenius_aut p of p \in [char R] := fun x => x ^+ p.

Section Frobenius.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Lemma charf0 : p%:R = 0 :> R. Proof. by apply/eqP; case/andP: charFp. Qed.
Lemma charf_prime : prime p. Proof. by case/andP: charFp. Qed.
Hint Resolve charf_prime.

Lemma dvdn_charf : forall n, (p %| n)%N = (n%:R == 0 :> R).
Proof.
move=> n; apply/idP/eqP=> [|n0].
  by case/dvdnP=> n' ->; rewrite natr_mul charf0 mulr0.
apply/idPn; rewrite -prime_coprime //; move/eqnP=> pn1.
have [a _] := bezoutl n (prime_gt0 charf_prime); case/dvdnP=> b.
move/(congr1 (fun m => m%:R : R)); move/eqP.
by rewrite natr_add !natr_mul charf0 n0 !mulr0 pn1 addr0 oner_eq0.
Qed.

Lemma charf_eq : [char R] =i (p : nat_pred).
Proof.
move=> q; apply/andP/eqP=> [[q_pr q0] | ->]; last by rewrite charf0.
by apply/eqP; rewrite eq_sym -dvdn_prime2 // dvdn_charf.
Qed.

Lemma bin_lt_charf_0 : forall k, 0 < k < p -> (bin p k)%:R = 0 :> R.
Proof. by move=> k lt0kp; apply/eqP; rewrite -dvdn_charf prime_dvd_bin. Qed.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autE : forall x, x^f = x ^+ p. Proof. by []. Qed.
Local Notation fE := Frobenius_autE.

Lemma Frobenius_aut_0 : 0^f = 0.
Proof. by rewrite fE -(prednK (prime_gt0 charf_prime)) exprS mul0r. Qed.

Lemma Frobenius_aut_1 : 1^f = 1.
Proof. by rewrite fE exp1rn. Qed.

Lemma Frobenius_aut_add_comm : forall x y, comm x y -> (x + y)^f = x^f + y^f.
Proof.
move=> x y cxy; have defp := prednK (prime_gt0 charf_prime).
rewrite !fE exprn_addl_comm // big_ord_recr subnn -defp big_ord_recl /= defp.
rewrite subn0 mulr1 mul1r bin0 binn big1 ?addr0 // => i _.
by rewrite -mulr_natl bin_lt_charf_0 ?mul0r //= -{2}defp ltnS (valP i).
Qed.

Lemma Frobenius_aut_muln : forall x n, (x *+ n)^f = x^f *+ n.
Proof.
move=> x; elim=> [|n IHn]; first exact: Frobenius_aut_0.
rewrite !mulrS Frobenius_aut_add_comm ?IHn //; exact: commr_muln.
Qed.

Lemma Frobenius_aut_nat : forall n, (n%:R)^f = n%:R.
Proof. by move=> n; rewrite Frobenius_aut_muln Frobenius_aut_1. Qed.

Lemma Frobenius_aut_mul_comm : forall x y, comm x y -> (x * y)^f = x^f * y^f.
Proof. by move=> x y; exact: commr_exp_mull. Qed.

Lemma Frobenius_aut_exp : forall x n, (x ^+ n)^f = x^f ^+ n.
Proof. by move=> x n; rewrite !fE -!exprn_mulr mulnC. Qed.

Lemma Frobenius_aut_opp : forall x, (- x)^f = - x^f.
Proof.
move=> x; apply/eqP; rewrite -subr_eq0 opprK addrC.
by rewrite -(Frobenius_aut_add_comm (commr_opp _)) // subrr Frobenius_aut_0.
Qed.

Lemma Frobenius_aut_sub_comm : forall x y, comm x y -> (x - y)^f = x^f - y^f.
Proof.
move=> x y; move/commr_opp; move/Frobenius_aut_add_comm->.
by rewrite Frobenius_aut_opp.
Qed.

End Frobenius.

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

Definition morphism (aR rR : Ring.type) (f : aR -> rR) :=
  [/\ {morph f : x y / x - y}, {morph f : x y / x * y} & f 1 = 1].

Section RingMorphTheory.

Variables aR' aR rR : Ring.type.
Variables (f : aR -> rR) (g : aR' -> aR).
Hypotheses (fM : morphism f) (gM : morphism g).

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

Lemma ringM_natmul : forall n, {morph f : x / x *+ n}.
Proof. by elim=> [|n IHn] x; rewrite ?ringM_0 // !mulrS ringM_add IHn. Qed.

Lemma ringM_nat : forall n, f n%:R = n %:R.
Proof. by move=> n; rewrite ringM_natmul ringM_1. Qed.

Lemma ringM_exp : forall n, {morph f : x / x ^+ n}.
Proof. by elim=> [|n IHn] x; rewrite ?ringM_1 //  !exprS ringM_mul IHn. Qed.

Lemma ringM_sign : forall k, f ((- 1) ^+ k) = (- 1) ^+ k.
Proof. by move=> k; rewrite ringM_exp ringM_opp ringM_1. Qed.

Lemma ringM_char : forall p, p \in [char aR] -> p \in [char rR].
Proof.
move=> p; rewrite !inE -ringM_nat.
by case/andP=> -> /=; move/eqP->; rewrite ringM_0.
Qed.

Lemma comp_ringM : morphism (f \o g).
Proof.
case: fM gM => [fsub fmul f1] [gsub gmul g1].
by split=> [x y | x y |] /=; rewrite ?g1 ?gsub ?gmul.
Qed.

Lemma ringM_isom :
  bijective f -> exists f', [/\ cancel f f', cancel f' f & morphism f'].
Proof.
case=> f' fK f'K; exists f'; split=> //.
split=> [x y|x y|]; apply: (canLR fK);
 by rewrite (ringM_sub, ringM_mul, ringM_1) ?f'K.
Qed.

End RingMorphTheory.

Module ComRing.

Record class_of (R : Type) : Type :=
  Class {base :> Ring.class_of R; _ : commutative (Ring.mul base)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
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

Lemma mulrC : @commutative R R *%R. Proof. by case: R => T []. Qed.
Canonical Structure mul_comoid := Monoid.ComLaw mulrC.
Lemma mulrCA : @left_commutative R R *%R. Proof. exact: mulmCA. Qed.
Lemma mulrAC : @right_commutative R R *%R. Proof. exact: mulmAC. Qed.

Lemma exprn_mull : forall n, {morph (fun x => x ^+ n) : x y / x * y}.
Proof. move=> n x y; apply: commr_exp_mull; exact: mulrC. Qed.

Lemma prodr_exp : forall n I r (P : pred I) (F : I -> R),
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
Proof.
by move=> n I r P F; rewrite (big_morph _ (exprn_mull n) (exp1rn _ n)).
Qed.

Lemma exprn_addl : forall x y n,
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ bin n i.
Proof. by move=> x y n; rewrite exprn_addl_comm //; exact: mulrC. Qed.

Lemma exprn_subl : forall x y n,
  (x - y) ^+ n = \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ bin n i.
Proof. by move=> x y n; rewrite exprn_subl_comm //; exact: mulrC. Qed.

Lemma subr_expn : forall x y n,
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof. by move=> x y n; rewrite -subr_expn_comm //; exact: mulrC. Qed.

Lemma ringM_comm : forall (rR : Ring.type) (f : R -> rR), 
  morphism f -> forall x y, comm (f x) (f y).
Proof. by move=> rR f fRM x y; red; rewrite -!ringM_mul // mulrC. Qed.

Lemma Frobenius_aut_RM : forall p (charRp : p \in [char R]),
  morphism (Frobenius_aut charRp).
Proof.
move=> p charRp; split=> [x y|x y|]; last exact: Frobenius_aut_1.
  exact: Frobenius_aut_sub_comm (mulrC _ _).
exact: Frobenius_aut_mul_comm (mulrC _ _).
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
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
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

Section UnitRingMorphism.

Variables (aR rR : UnitRing.type) (f : aR -> rR).
Hypothesis fM : morphism f.

Lemma ringM_unit : forall x, unit x -> unit (f x).
Proof.
move=> x; case/unitrP=> y [yx1 xy1]; apply/unitrP.
by exists (f y); rewrite -!ringM_mul // yx1 xy1 ringM_1.
Qed.

Lemma ringM_inv : forall x, unit x -> f x^-1 = (f x)^-1.
Proof.
move=> x Ux; rewrite -[(f x)^-1]mul1r; apply: (canRL (mulrK (ringM_unit Ux))).
by rewrite -ringM_mul // mulVr ?ringM_1.
Qed.

Lemma ringM_div : forall x y, unit y -> f (x / y) = f x / f y.
Proof. by move=> x y Uy; rewrite ringM_mul ?ringM_inv. Qed.

End UnitRingMorphism.

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
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

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

Implicit Arguments Bool [R].
Prenex Implicits Const Add Opp NatMul Mul Exp Bool Unit And Or Implies Not.
Prenex Implicits Exists Forall.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : UnitRing.type.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval : forall e e' t, same_env e e' -> eval e t = eval e' t.
Proof. by move=> e e' t eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst : forall e t s,
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
Proof.
move=> e t [i u]; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: (_ == _).
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => unit (eval e t1)
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym : forall e e', same_env e e' -> same_env e' e.
Proof. by move=> e e'; exact: fsym. Qed.

(* Extensionality of formula evaluation *)
Lemma eq_holds : forall e e' f, same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i: forall i v e e', same_env e e' -> same_env (sv e i v) (sv e' i v).
  by move=> i v /= e e' eq_e j; rewrite !nth_set_nth /= eq_e.
move=> e e' t; elim: t e e' => //=.
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e).
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e f12; move/IH1: (same_env_sym eq_e); eauto.
- by move=> f1 IH1 e e'; move/same_env_sym; move/IH1; tauto.
- by move=> i f1 IH1 e e'; move/(eq_i i)=> eq_e [x f_ex]; exists x; eauto.
by move=> i f1 IH1 e e'; move/(eq_i i); eauto.
Qed.

(* Evaluation and substitution by a constant *)
Lemma holds_fsubst : forall e f i v,
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
Proof.
move=> e f i v; elim: f e => //=; do [
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
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

(* Replaces inverses in the term t by fresh variables, accumulating the *)
(* substitution. *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id : forall t r n, rterm t -> to_rterm t r n = (t, r).
Proof.
elim=> //.
- by move=> t1 IHt1 t2 IHt2 r n /=; case/andP=> rt1 rt2; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /=; case/andP=> rt1 rt2; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.

(* A ring formula stating that t1 is equal to 0 in the ring theory. *)
(* Also applies to non commutative rings.                           *)
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

(* The transformation gives a ring formula. *)
Lemma to_rform_rformula : forall f, rformula (to_rform f).
Proof.
suffices eq0_ring : rformula (eq0_rform _) by elim=> //= => f1 ->.
move=> t1; rewrite /eq0_rform; move: (ub_var t1) => m; set tr := _ m.
suffices: all rterm (tr.1 :: tr.2).
  case: tr => {t1} t1 r /=; case/andP=> t1_r.
  elim: r m => [| t r IHr] m; rewrite /= ?andbT //.
  case/andP=> ->; exact: IHr.
have: all rterm [::] by [].
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
  by move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r; move/IHt1; case: to_rterm.
Qed.

(* Correctness of the transformation. *)
Lemma to_rformP : forall e f, holds e (to_rform f) <-> holds e f.
Proof.
suffices equal0_equiv : forall e t1 t2,
  holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2).
- move=> e f; elim: f e => /=; try tauto.
  + move => t1 t2 e.
    by split; [move/equal0_equiv; move/eqP | move/eqP; move/equal0_equiv].
  + move=> t1 e; rewrite unitrE; exact: equal0_equiv.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x]; move/IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
move=> e t1 t2; rewrite -(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval e (t1 - t2)); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst: forall s t, s.1 >= ub_var t -> tsubst t s = t.
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
pose fix rsub t' m r : term R :=
  if r is u :: r' then tsubst (rsub t' m.+1 r') (m, u^-1)%T else t'.
pose fix ub_sub m r : Prop :=
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else true.
suffices rsub_to_r: forall t0 r0 m, m >= ub_var t0 -> ub_sub m r0 ->
  let: (t', r) := to_rterm t0 r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t0].
- have:= rsub_to_r t [::] _ (leqnn _).
  rewrite /eq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split; move/eqP.
  rewrite eval_tsubst /=; set y := eval e u; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (unit y); [left | right]; first by rewrite mulVr ?divrr.
    split; first by rewrite invr_out ?Uy.
    case=> z; rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
  by rewrite !sub_var_tsubst.
have rsub_id : forall r t n, ub_var t <= n -> rsub t n r = t.
  by elim=> //= t0 r IHr t1 n hn; rewrite IHr ?sub_var_tsubst ?leqW.
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
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => unit (eval e t1)
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

(* qf_eval is equivalent to holds *)
Lemma qf_evalP : forall e f, qf_form f -> reflect (holds e f) (qf_eval e f).
Proof.
move=> e; elim=> //=; try by move=> *; exact: idP.
- move=> t1 t2 _; exact: eqP.
- move=> f1 IHf1 f2 IHf2 /=; case/andP; case/IHf1=> f1T; last by right; case.
  by case/IHf2; [left | right; case].
- move=> f1 IHf1 f2 IHf2 /=; case/andP; case/IHf1=> f1F; first by do 2 left.
  by case/IHf2; [left; right | right; case].
- move=> f1 IHf1 f2 IHf2 /=; case/andP; case/IHf1=> f1T; last by left.
  by case/IHf2; [left | right; move/(_ f1T)].
by move=> f1 IHf1; case/IHf1; [right | left].
Qed.

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in 
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP : forall e bcs1 bcs2,
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
Proof.
move=> e.
by elim=> //= bc1 bcs1 IH1 bcs2; rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnfP : forall e bcs1 bcs2,
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
Proof.
move=> e; elim=> [|bc1 bcs1 IH1] bcs2 /=; first by rewrite /and_dnf big_nil.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [| bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux: forall (l1 l2 : seq (term R)) g (redg := foldr (And \o g) True),
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%T.
+ by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim=> [| ? ? IHl1] * //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP : forall e,
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> e qev; have qevT: forall f, qev f true = ~~ qev f false.
  rewrite {}/qev; elim=> //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by rewrite and_dnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_dnfP /=; move/IH1->; move/IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /=; move/IH1->; move/IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE; move/IH1 <-; move/IH2->.
by move=> f1 IH1; move/IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf : forall bcs, qf_form (dnf_to_form bcs).
Proof. by elim=> //= [[clT clF] _ ->] /=; elim: clT => //=; elim: clF. Qed.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm : forall f b, rformula f -> all dnf_rterm (qf_to_dnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok: forall bcs1 bcs2, ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> bcs1 bcs2 ok1 ok2; rewrite [ok _]all_cat; exact/andP.
have and_ok: forall bcs1 bcs2, ok bcs1 -> ok bcs2 -> ok (and_dnf bcs1 bcs2).
  rewrite /and_dnf unlock; elim=> //= cl1 bcs1 IH1 bcs2; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2; case/andP=> ok2; move/IH2->.
  by rewrite /dnf_rterm !all_cat ok11 ok12 /= !andbT.
elim=> //=; try by [move=> _ ? ? [] | move=> ? ? ? ? [] /=; case/andP; auto].
- by do 2!case.
- by rewrite /dnf_rterm => ? ? [] /= ->.
by auto.
Qed.

Lemma dnf_to_rform : forall bcs, rformula (dnf_to_form bcs) = all dnf_rterm bcs.
Proof.
elim=> //= [[cl1 cl2] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
by congr andb; [elim: cl1 | elim: cl2] => //= t cl ->; rewrite andbT.
Qed.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := @big_morph _ _ _ true _ andb qf_form.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick : forall e (qev := qf_eval e),
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> e qev P; rewrite (@big_morph _ _ _ false _ orb qev) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite (@big_morph _ _ _ true _ andb qev) //= big_andE /=.
  case/andP; move/forallP=> eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //=; move/negbTE.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite (@big_morph _ _ _ true _ andb qev) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Type I : seq nat.
Implicit Type e : seq R.

Lemma foldExistsP : forall I e,
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
Proof.
elim=> /= [|i I IHi] e.
  by split=> [[e' eq_e] |]; [apply: eq_holds => i; rewrite eq_e | exists e].
split=> [[e' eq_e f_e'] | [x]]; last set e_x := set_nth 0 e i x.
  exists e'`_i; apply/IHi; exists e' => // j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
case/IHi=> e' eq_e f_e'; exists e' => // j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma foldForallP : forall I e,
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
Proof.
elim=> /= [|i I IHi] e.
  by split=> [|f_e e' eq_e]; [exact | apply: eq_holds f_e => i; rewrite eq_e].
split=> [f_e' x | f_e e' eq_e]; first set e_x := set_nth 0 e i x.
  apply/IHi=> e' eq_e; apply: f_e' => j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
move/IHi: (f_e e'`_i); apply=> j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
Qed.

End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Module ComUnitRing.

Record class_of (R : Type) : Type := Class {
  base1 :> ComRing.class_of R;
  ext :> UnitRing.mixin_of (Ring.Pack base1 R)
}.

Coercion base2 R m := UnitRing.Class (@ext R m).

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.

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

Definition pack T :=
  fun bT b & phant_id (ComRing.class bT) (b : ComRing.class_of T) =>
  fun mT m & phant_id (UnitRing.class mT) (@UnitRing.Class T b m) =>
  Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
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
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (ComUnitRing.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
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
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (IntegralDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

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

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
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

Lemma mulVf : forall x, x != 0 -> x^-1 * x = 1.
Proof. by move=> x; rewrite -unitfE; exact: mulVr. Qed.
Lemma divff : forall x, x != 0 -> x / x = 1.
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

Lemma natf0_char : forall n,
  n > 0 -> n%:R == 0 :> F -> exists p, p \in [char F].
Proof.
move=> n; elim: {n}_.+1 {-2}n (ltnSn n) => // m IHm n; rewrite ltnS => le_n_m.
rewrite leq_eqVlt -primes_pdiv mem_primes; move: (pdiv n) => p.
case/predU1P=> [<-|]; [by rewrite oner_eq0 | case/and3P=> p_pr n_gt0].
case/dvdnP=> n' def_n; rewrite def_n muln_gt0 andbC prime_gt0 // in n_gt0 *.
rewrite natr_mul mulf_eq0 orbC; case/orP; first by exists p; exact/andP.
by apply: IHm (leq_trans _ le_n_m) _; rewrite // def_n ltn_Pmulr // prime_gt1.
Qed.

Lemma charf'_nat : forall n, [char F]^'.-nat n = (n%:R != 0 :> F).
Proof.
move=> n; case: (posnP n) => [-> | n_gt0]; first by rewrite eqxx.
apply/idP/idP => [|nz_n]; last first.
  by apply/pnatP=> // p p_pr p_dvd_n; apply: contra nz_n; move/dvdn_charf <-.
apply: contraL => n0; have [// | p charFp] := natf0_char _ n0.
have [p_pr _] := andP charFp; rewrite (eq_pnat _ (eq_negn (charf_eq charFp))).
by rewrite p'natE // (dvdn_charf charFp) n0.
Qed.

Lemma charf0P : [char F] =i pred0 <-> (forall n, (n%:R == 0 :> F) = (n == 0)%N).
Proof.
split=> charF0 n; last by rewrite !inE charF0 andbC; case: eqP => // ->.
case: posnP => [-> | n_gt0]; first exact: eqxx.
by apply/negP; case/natf0_char=> // p; rewrite charF0.
Qed.

Section FieldMorphismInj.

Variables (R : Ring.type) (f : F -> R).
Hypothesis fRM : morphism f.

Lemma fieldM_eq0 : forall x, (f x == 0) = (x == 0).
Proof.
move=> x; case: (eqVneq x 0) => [-> | nz_x]; first by rewrite ringM_0 ?eqxx.
rewrite (negbTE nz_x); apply/eqP; move/(congr1 ( *%R (f x^-1))); move/eqP.
by rewrite -ringM_mul // mulVf // mulr0 ringM_1 ?oner_eq0.
Qed.

Lemma fieldM_inj : injective f.
Proof.
move=> x y eqfxy; apply/eqP; rewrite -subr_eq0 -fieldM_eq0 ringM_sub //.
by rewrite eqfxy subrr.
Qed.

Lemma fieldM_char : [char R] =i [char F].
Proof. by move=> p; rewrite !inE -fieldM_eq0 ringM_nat. Qed.

End FieldMorphismInj.

Section FieldMorphismInv.

Variables (R : UnitRing.type) (f : F -> R).
Hypothesis fRM : morphism f.

Lemma fieldM_unit : forall x, unit (f x) = (x != 0).
Proof.
move=> x; case: eqP => [-> |]; first by rewrite ringM_0 ?unitr0.
by move/eqP; rewrite -unitfE; exact: ringM_unit.
Qed.

Lemma fieldM_inv : {morph f: x / x^-1}.
Proof.
move=> x; case (eqVneq x 0) => [-> | nzx]; last by rewrite ringM_inv ?unitfE.
by rewrite !(invr0, ringM_0 fRM).
Qed.

Lemma fieldM_div : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite ringM_mul ?fieldM_inv. Qed.

End FieldMorphismInv.

End FieldTheory.

Module DecidableField.

Definition axiom (R : UnitRing.type) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : UnitRing.type) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Record class_of (F : Type) : Type :=
  Class {base :> Field.class_of F; mixin:> mixin_of (UnitRing.Pack base F)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* Ultimately, there should be a QE Mixin constructor *)

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := IntegralDomain.Pack (class cT) cT.
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

Lemma sol_subproof : forall n f,
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
Proof.
move=> n f; apply: (iffP (satP _ _)) => [|[s]]; last first.
  case/andP; move/eqP=> sz_s; move/satP=> f_s; apply/foldExistsP.
  exists s => // i; rewrite !inE mem_iota -leqNgt add0n => le_n_i.
  by rewrite !nth_default ?sz_s.
case/foldExistsP=> e e0 f_e; set s := take n (set_nth 0 e n 0).
have sz_s: size s = n by rewrite size_take size_set_nth leq_maxr leqnn.
exists s; rewrite sz_s eqxx; apply/satP; apply: eq_holds f_e => i.
case: (leqP n i) => [le_n_i | lt_i_n].
  by rewrite -e0 ?nth_default ?sz_s // !inE mem_iota -leqNgt.
by rewrite nth_take // nth_set_nth /= eq_sym eqn_leq leqNgt lt_i_n.
Qed.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol : forall n f, size (sol n f) = n.
Proof.
rewrite /sol => n f; case: sol_subproof => [sP | _]; last exact: size_nseq.
by case/andP: (xchooseP sP); move/eqP.
Qed.

Lemma solP : forall n f,
  reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
Proof.
rewrite /sol => n f; case: sol_subproof => [sP | sPn].
  case/andP: (xchooseP sP) => _ ->; left.
  by case: sP => s; case/andP; move/eqP=> <-; move/satP; exists s.
apply: (iffP (satP _ _)); first by exists (nseq n 0); rewrite ?size_nseq.
by case=> s sz_s; move/satP=> f_s; case: sPn; exists s; rewrite sz_s eqxx.
Qed.

Lemma eq_sat : forall f1 f2,
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
Proof. by move=> f1 f2 eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.

Lemma eq_sol : forall f1 f2,
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
Proof.
rewrite /sol => f1 f2; move/eq_sat=> eqf12 n.
do 2![case: sol_subproof] => //= [f1s f2s | ns1 [s f2s] | [s f1s] []].
- by apply: eq_xchoose => s; rewrite eqf12.
- by case: ns1; exists s; rewrite -eqf12.
by exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Implicit Arguments satP [F e f].
Implicit Arguments solP [F n f].

(* Structure of field with quantifier elimination *)
Module QE.

Section Axioms.

Variable R : UnitRing.type.
Variable proj : nat -> seq (term R) * seq (term R) -> formula R.
(* proj is the elimination of a single existential quantifier *)

Definition wf_proj_axiom :=
  forall i bc (bc_i := proj i bc), qf_form bc_i && rformula bc_i : Prop.

(* The elimination operator p preserves  validity *)
Definition holds_proj_axiom :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

End Axioms.

Record mixin_of (R : UnitRing.type) : Type := Mixin {
  proj : nat -> (seq (term R) * seq (term R)) -> formula R;
  wf_proj : wf_proj_axiom proj;
  holds_proj : holds_proj_axiom proj
}.

Record class_of (F : Type) : Type :=
  Class {base :> Field.class_of F; mixin:> mixin_of (UnitRing.Pack base F)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := IntegralDomain.Pack (class cT) cT.
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

Lemma wf_proj : QE.wf_proj_axiom proj.
Proof. exact: QE.wf_proj. Qed.

Lemma holds_proj : QE.holds_proj_axiom proj.
Proof. exact: QE.holds_proj. Qed.

Implicit Type f : formula F.

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim (f : formula F) : formula F :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

Lemma quantifier_elim_wf : forall f (qf := quantifier_elim f),
  rformula f -> qf_form qf && rformula qf.
Proof.
suffices aux_wf: forall f n (qf := elim_aux f n), qf_form qf && rformula qf.
  by elim=> //= f1 IH1 f2 IH2; case/andP; move/IH1; case/andP=> -> -> /=.
rewrite /elim_aux => f n; elim: (_ f _) => //= bc bcs.
by rewrite andbC andbAC andbA wf_proj.
Qed.

Lemma quantifier_elim_rformP : forall e f,
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP: forall f e n, qf_form f && rformula f ->
  reflect (rc e n f) (qf_eval e (elim_aux f n)).
+ rewrite /elim_aux => f e n cf; set bcs := qf_to_dnf f false.
  apply: (@iffP (rc e n (dnf_to_form bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; exact: qf_to_dnf_rterm.
  elim: {f cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc; move/IHbcs=> {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: holds_proj => //= [ex_x|no_x].
    left; case: ex_x => x; move/(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
move=> e f; elim: f e => //.
- move=> b e _; exact: idP.
- move=> t1 t2 e _; exact: eqP.
- move=> f1 IH1 f2 IH2 e /=; case/andP; case/IH1=> f1e; last by right; case.
  by case/IH2; [left | right; case].
- move=> f1 IH1 f2 IH2 e /=; case/andP; case/IH1=> f1e; first by do 2!left.
  by case/IH2; [left; right | right; case].
- move=> f1 IH1 f2 IH2 e /=; case/andP; case/IH1=> f1e; last by left.
  by case/IH2; [left | right; move/(_ f1e)].
- by move=> f IHf e /=; case/IHf; [right | left].
- move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
  by apply: (iffP (auxP _ _ _ rqf)) => [] [x]; exists x; exact/IHf.
move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
case: auxP => // [f_x|no_x]; first by right=> no_x; case: f_x => x; case/IHf.
by left=> x; apply/IHf=> //; apply/idPn=> f_x; case: no_x; exists x.
Qed.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

Definition QEDecidableFieldMixin := DecidableField.Mixin proj_satP.

Canonical Structure QEDecidableField :=
  DecidableField.Pack (DecidableField.Class QEDecidableFieldMixin) F.

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
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (DecidableField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* There should eventually be a constructor from polynomial resolution *)
(* that builds the DecidableField mixin using QE.                      *)

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := Field.Pack (class cT) cT.
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
Definition subr0 := subr0.
Definition sub0r := sub0r.
Definition subr_eq := subr_eq.
Definition subr_eq0 := subr_eq0.
Definition sumr_opp := sumr_opp.
Definition sumr_sub := sumr_sub.
Definition sumr_muln := sumr_muln.
Definition sumr_muln_r := sumr_muln_r.
Definition sumr_const := sumr_const.
Definition mulr0n := mulr0n.
Definition mulrS := mulrS.
Definition mulr1n := mulr1n.
Definition mulrSr := mulrSr.
Definition mulrb := mulrb.
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
Definition mulr_subl := mulr_subl.
Definition mulr_subr := mulr_subr.
Definition mulrnAl := mulrnAl.
Definition mulrnAr := mulrnAr.
Definition mulr_natl := mulr_natl.
Definition mulr_natr := mulr_natr.
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
Definition commr_sign := commr_sign.
Definition exprn_mulnl := exprn_mulnl.
Definition exprn_mulr := exprn_mulr.
Definition signr_odd := signr_odd.
Definition signr_eq0 := signr_eq0.
Definition signr_addb := signr_addb.
Definition exprN := exprN.
Definition exprn_addl_comm := exprn_addl_comm.
Definition exprn_subl_comm := exprn_subl_comm.
Definition subr_expn_comm := subr_expn_comm.
Definition subr_expn_1 := subr_expn_1.
Definition charf0 := charf0.
Definition charf_prime := charf_prime.
Definition dvdn_charf := dvdn_charf.
Definition charf_eq := charf_eq.
Definition bin_lt_charf_0 := bin_lt_charf_0.
Definition Frobenius_autE := Frobenius_autE.
Definition Frobenius_aut_0 := Frobenius_aut_0.
Definition Frobenius_aut_1 := Frobenius_aut_1.
Definition Frobenius_aut_add_comm := Frobenius_aut_add_comm.
Definition Frobenius_aut_muln := Frobenius_aut_muln.
Definition Frobenius_aut_nat := Frobenius_aut_nat.
Definition Frobenius_aut_mul_comm := Frobenius_aut_mul_comm.
Definition Frobenius_aut_exp := Frobenius_aut_exp.
Definition Frobenius_aut_opp := Frobenius_aut_opp.
Definition Frobenius_aut_sub_comm := Frobenius_aut_sub_comm.
Definition prodr_const := prodr_const.
Definition mulrC := mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition exprn_mull := exprn_mull.
Definition prodr_exp := prodr_exp.
Definition prodr_exp_r := prodr_exp_r.
Definition prodr_opp := prodr_opp.
Definition exprn_addl := exprn_addl.
Definition exprn_subl := exprn_subl.
Definition subr_expn := subr_expn.
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
Definition natf0_char := natf0_char.
Definition charf'_nat := charf'_nat.
Definition charf0P := charf0P.
Definition satP := @satP.
Definition eq_sat := eq_sat.
Definition solP := @solP.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := solve_monicpoly.
Definition ringM_sub := ringM_sub.
Definition ringM_0 := ringM_0.
Definition ringM_1 := ringM_1.
Definition ringM_opp := ringM_opp.
Definition ringM_add := ringM_add.
Definition ringM_sum := ringM_sum.
Definition ringM_mul := ringM_mul.
Definition ringM_prod := ringM_prod.
Definition ringM_natmul := ringM_natmul.
Definition ringM_nat := ringM_nat.
Definition ringM_exp := ringM_exp.
Definition ringM_sign := ringM_sign.
Definition ringM_char := ringM_char.
Definition comp_ringM := comp_ringM.
Definition ringM_isom := ringM_isom.
Definition ringM_comm := ringM_comm.
Definition ringM_unit := ringM_unit.
Definition Frobenius_aut_RM := Frobenius_aut_RM.
Definition fieldM_eq0 := fieldM_eq0.
Definition fieldM_inj := fieldM_inj.
Definition ringM_inv := ringM_inv.
Definition fieldM_char := fieldM_char.
Definition ringM_div := ringM_div.
Definition fieldM_unit := fieldM_unit.
Definition fieldM_inv := fieldM_inv.
Definition fieldM_div := fieldM_div.

Implicit Arguments satP [F e f].
Implicit Arguments solP [F n f].
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
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.

Notation "1" := (GRing.one _) : ring_scope.
Notation "- 1" := (- (1))%R : ring_scope.

Notation "n %:R" := (GRing.natmul 1 n) : ring_scope.
Notation "[ 'char' R ]" := (GRing.char (Phant R)) : ring_scope.
Notation Frobenius_aut chRp := (GRing.Frobenius_aut chRp).
Notation "*%R" := (@GRing.mul _).
Notation "x * y" := (GRing.mul x y) : ring_scope.
Notation "x ^+ n" := (GRing.exp x n) : ring_scope.
Notation "x ^-1" := (GRing.inv x) : ring_scope.
Notation "x ^- n" := (x ^+ n)^-1%R : ring_scope.
Notation "x / y" := (GRing.mul x y^-1) : ring_scope.

Implicit Arguments GRing.unitDef [].

Bind Scope term_scope with GRing.term.
Bind Scope term_scope with GRing.formula.

Notation "''X_' i" := (GRing.Var _ i) : term_scope.
Notation "n %:R" := (GRing.NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (GRing.Const x) : term_scope.
Infix "+" := GRing.Add : term_scope.
Notation "- t" := (GRing.Opp t) : term_scope.
Notation "t - u" := (GRing.Add t (- u)) : term_scope.
Infix "*" := GRing.Mul : term_scope.
Infix "*+" := GRing.NatMul : term_scope.
Notation "t ^-1" := (GRing.Inv t) : term_scope.
Notation "t / u" := (GRing.Mul t u^-1) : term_scope.
Infix "^+" := GRing.Exp : term_scope.
Infix "==" := GRing.Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := GRing.And : term_scope.
Infix "\/" := GRing.Or : term_scope.
Infix "==>" := GRing.Implies : term_scope.
Notation "~ f" := (GRing.Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (GRing.Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (GRing.Forall i f) : term_scope.

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
Notation ZmodType T m := (@GRing.Zmodule.pack T m _ _ id).
Notation ZmodMixin := GRing.Zmodule.Mixin.
Notation "[ 'zmodType' 'of' T 'for' cT ]" := (@GRing.Zmodule.clone T cT _ idfun)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'zmodType' 'of' T ]" := (@GRing.Zmodule.clone T _ _ id)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.

Notation ringType := GRing.Ring.type.
Notation RingType T m := (@GRing.Ring.pack T _ m _ _ id _ id).
Notation RingMixin := GRing.Ring.Mixin.
Notation RevRingType := GRing.RevRingType.
Notation "[ 'ringType' 'of' T 'for' cT ]" := (@GRing.Ring.clone T cT _ idfun)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" := (@GRing.Ring.clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.

Notation comRingType := GRing.ComRing.type.
Notation ComRingType T m := (@GRing.ComRing.pack T _ m _ _ id _ id).
Notation ComRingMixin := GRing.ComRing.RingMixin.
Notation "[ 'comRingType' 'of' T 'for' cT ]" :=
    (@GRing.ComRing.clone T cT _ idfun)
  (at level 0, format "[ 'comRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comRingType' 'of' T ]" := (@GRing.ComRing.clone T _ _ id)
  (at level 0, format "[ 'comRingType'  'of'  T ]") : form_scope.

Notation unitRingType := GRing.UnitRing.type.
Notation UnitRingType T m := (@GRing.UnitRing.pack T _ m _ _ id _ id).
Notation UnitRingMixin := GRing.UnitRing.EtaMixin.
Notation "[ 'unitRingType' 'of' T 'for' cT ]" :=
    (@GRing.UnitRing.clone T cT _ idfun)
  (at level 0, format "[ 'unitRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'unitRingType' 'of' T ]" := (@GRing.UnitRing.clone T _ _ id)
  (at level 0, format "[ 'unitRingType'  'of'  T ]") : form_scope.

Notation comUnitRingType := GRing.ComUnitRing.type.
Notation ComUnitRingMixin := GRing.ComUnitRing.Mixin.
Notation "[ 'comUnitRingType' 'of' T ]" :=
    (@GRing.ComUnitRing.pack T _ _ id _ _ id)
  (at level 0, format "[ 'comUnitRingType'  'of'  T ]") : form_scope.

Notation idomainType := GRing.IntegralDomain.type.
Notation IdomainType T m := (@GRing.IntegralDomain.pack T _ m _ _ id _ id).
Notation "[ 'idomainType' 'of' T 'for' cT ]" :=
    (@GRing.IntegralDomain.clone T cT _ idfun)
  (at level 0, format "[ 'idomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'idomainType' 'of' T ]" := (@GRing.IntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'idomainType'  'of'  T ]") : form_scope.

Notation fieldType := GRing.Field.type.
Notation FieldType T m := (@GRing.Field.pack T _ m _ _ id _ id).
Notation FieldUnitMixin := GRing.Field.UnitMixin.
Notation FieldIdomainMixin := GRing.Field.IdomainMixin.
Notation FieldMixin := GRing.Field.Mixin.
Notation "[ 'fieldType' 'of' T 'for' cT ]" := (@GRing.Field.clone T cT _ idfun)
  (at level 0, format "[ 'fieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'fieldType' 'of' T ]" := (@GRing.Field.clone T _ _ id)
  (at level 0, format "[ 'fieldType'  'of'  T ]") : form_scope.

Notation decFieldType := GRing.DecidableField.type.
Notation DecFieldType T m := (@GRing.DecidableField.pack T _ m _ _ id _ id).
Notation DecFieldMixin := GRing.DecidableField.Mixin.
Notation "[ 'decFieldType' 'of' T 'for' cT ]" :=
    (@GRing.DecidableField.clone T cT _ idfun)
  (at level 0, format "[ 'decFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'decFieldType' 'of' T ]" := (@GRing.DecidableField.clone T _ _ id)
  (at level 0, format "[ 'decFieldType'  'of'  T ]") : form_scope.

Notation closedFieldType := GRing.ClosedField.type.
Notation ClosedFieldType T m := (GRing.ClosedField.pack T _ m _ _ id _ id).
Notation "[ 'closedFieldType' 'of' T 'for' cT ]" :=
    (@GRing.ClosedField.clone T cT _ idfun)
  (at level 0,
   format "[ 'closedFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'closedFieldType' 'of' T ]" := (@GRing.ClosedField.clone T _ _ id)
  (at level 0, format "[ 'closedFieldType'  'of'  T ]") : form_scope.
