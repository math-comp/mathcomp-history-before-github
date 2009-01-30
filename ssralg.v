(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Abstract algebra framework for ssreflect. *)
(* We define a number of structures that "package" common algebraic *)
(* properties of operations. The purpose of this packaging is NOT   *)
(* to make generic definitions shorter, but to make proofs shorter, *)
(* by providing canonical structures that automatically supply      *)
(* canonical properties of operators required by generic lemmas.    *)
(*   Therefore, as a rule, the "carrier" of such structures will    *)
(* be the binary operation, rather than the data type or its        *)
(* identity element.  *)
(*   The primary application of these structures are the generic    *)
(* indexed products and summations in bigops.v.                     *)
(*   We then define a second class of structures that provide       *)
(* generic notation in addition to generic algebraic properties.    *)
(* For these the carrier is the data type.                          *)

Reserved Notation "+%R" (at level 0).
Reserved Notation "x *+ n" (at level 40, n at level 9, left associativity).
Reserved Notation "x *- n" (at level 40, n at level 9, left associativity).

Reserved Notation "*%R" (at level 0).
Reserved Notation "n %: R"
  (at level 2, R at level 1, left associativity, format "n %: R").
Reserved Notation "x ^+ n" (at level 29, n at level 9, left associativity).
Reserved Notation "x ^- n" (at level 29, n at level 9, left associativity).

Module Monoid.

Section Definitions.
Variables (T : Type) (idm : T).

Structure law : Type := Law {
  operator :> T -> T -> T;
  _ : associative operator;
  _ : left_id idm operator;
  _ : right_id idm operator
}.

Structure com_law : Type := ComLaw {
   com_operator :> law;
   _ : commutative com_operator
}.

Structure mul_law : Type := MulLaw {
  mul_operator :> T -> T -> T;
  _ : left_zero idm mul_operator;
  _ : right_zero idm mul_operator
}.

Structure add_law (mul : T -> T -> T) : Type := AddLaw {
  add_operator :> com_law;
  _ : left_distributive mul add_operator;
  _ : right_distributive mul add_operator
}.

Definition repack_law opL :=
  let: Law _ opmA op1m opm1 := opL
    return {type of Law for opL} -> law in
  fun k => k opmA op1m opm1.

Definition repack_mul_law opM :=
  let: MulLaw _ op0m opm0 := opM
    return {type of MulLaw for opM} -> mul_law in
  fun k => k op0m opm0.

Definition op_phant := phantom (T -> T -> T).
Definition op_uni op1 op2 := op_phant op1 -> op_phant op2.

Definition repack_com_law op (opL : law) (opC : com_law) :=
  fun (_ : op_uni opL op) (_ : op_uni opC op) opEq =>
  (let: ComLaw _ opmC := opC
     return {type of ComLaw for opC} -> com_law in
   fun k => k opmC)
  (let: erefl in _ = opC := opEq
     return {type of ComLaw for opC}
   in @ComLaw opL).

Definition repack_add_law mop aop (opC : com_law) (opA : add_law mop) :=
  fun (_ : op_uni opC aop) (_ : op_uni opA aop) opEq =>
  (let: AddLaw _ mopAm mopmA  := opA
     return {type of @AddLaw mop for opA} -> add_law mop in
   fun k => k mopAm mopmA)
  (let: erefl in _ = opA := opEq
     return {type of @AddLaw mop for opA}
   in @AddLaw mop opC).

End Definitions.

Definition morphism T1 T2 id1 id2 op1 op2 (phi : T1 -> T2) :=
  phi id1 = id2 /\ {morph phi : x y / op1 x y >-> op2 x y}.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T) (inv : T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof. by move=>  mul1x x; rewrite mulC. Qed.

Lemma mulC_zero : left_zero zero mul -> right_zero zero mul.
Proof. by move=> mul0x x; rewrite mulC. Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof. by move=> mul_addl x y z; rewrite !(mulC x). Qed.

End CommutativeAxioms.

Module Theory.

Section Theory.
Variables (T : Type) (idm : T).

Section Plain.
Variable mul : law idm.
Lemma mul1m : left_id idm mul. Proof. by case mul. Qed.
Lemma mulm1 : right_id idm mul. Proof. by case mul. Qed.
Lemma mulmA : associative mul. Proof. by case mul. Qed.
End Plain.

Section Commutative.
Variable mul : com_law idm.
Lemma mulmC : commutative mul. Proof. by case mul. Qed.
Lemma mulmCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulmA (mulmC x). Qed.
Lemma mulmAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulmA (mulmC y). Qed.
End Commutative.

Section Mul.
Variable mul : mul_law idm.
Lemma mul0m : left_zero idm mul. Proof. by case mul. Qed.
Lemma mulm0 : right_zero idm mul. Proof. by case mul. Qed.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Lemma addmA : associative add. Proof. exact: mulmA. Qed.
Lemma addmC : commutative add. Proof. exact: mulmC. Qed.
Lemma addmCA : left_commutative add. Proof. exact: mulmCA. Qed.
Lemma addmAC : right_commutative add. Proof. exact: mulmAC. Qed.
Lemma add0m : left_id idm add. Proof. exact: mul1m. Qed.
Lemma addm0 : right_id idm add. Proof. exact: mulm1. Qed.
Lemma mulm_addl : left_distributive mul add. Proof. by case add. Qed.
Lemma mulm_addr : right_distributive mul add. Proof. by case add. Qed.
End Add.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Theory.

End Theory.

Import Theory. (* Will become Include Theory. in Coq 8.2 *)
Definition mul1m :=  mul1m.
Definition mulm1 := mulm1.
Definition mulmA := mulmA.
Definition mulmC := mulmC.
Definition mulmCA := mulmCA.
Definition mulmAC := mulmAC.
Definition mul0m := mul0m.
Definition mulm0 := mulm0.
Definition addmA := addmA.
Definition addmC := addmC.
Definition addmCA := addmCA.
Definition addmAC := addmAC.
Definition add0m := add0m.
Definition addm0 := addm0.
Definition mulm_addl := mulm_addl.
Definition mulm_addr := mulm_addr.
Definition simpm := simpm.

End Monoid.

Notation "[ 'law' 'of' f ]" :=
    (Monoid.repack_law (fun fA => @Monoid.Law _ _ f fA))
  (at level 0, format"[ 'law'  'of'  f ]") : form_scope.

Notation "[ 'com_law' 'of' f ]" :=
    (@Monoid.repack_com_law _ _ f _ _ id id (erefl _))
  (at level 0, format "[ 'com_law'  'of'  f ]") : form_scope.

Notation "[ 'mul_law' 'of' f ]" :=
    (Monoid.repack_mul_law (fun f0m => @Monoid.MulLaw _ _ f f0m))
  (at level 0, format"[ 'mul_law'  'of'  f ]") : form_scope.

Notation "[ 'add_law' m 'of' a ]" :=
    (@Monoid.repack_add_law _ _ m a _ _ id id (erefl _))
  (at level 0, format "[ 'add_law'  m  'of'  a ]") : form_scope.

Section PervasiveMonoids.

Import Monoid.

Canonical Structure andb_monoid := Law andbA andTb andbT.
Canonical Structure andb_comoid := ComLaw andbC.

Canonical Structure andb_muloid := MulLaw andFb andbF.
Canonical Structure orb_monoid := Law orbA orFb orbF.
Canonical Structure orb_comoid := ComLaw orbC.
Canonical Structure orb_muloid := MulLaw orTb orbT.
Canonical Structure addb_monoid := Law addbA addFb addbF.
Canonical Structure addb_comoid := ComLaw addbC.
Canonical Structure orb_addoid := AddLaw andb_orl andb_orr.
Canonical Structure andb_addoid := AddLaw orb_andl orb_andr.
Canonical Structure addb_addoid := AddLaw andb_addl andb_addr.

Canonical Structure addn_monoid := Law addnA add0n addn0.
Canonical Structure addn_comoid := ComLaw addnC.
Canonical Structure muln_monoid := Law mulnA mul1n muln1.
Canonical Structure muln_comoid := ComLaw mulnC.
Canonical Structure muln_muloid := MulLaw mul0n muln0.
Canonical Structure addn_addoid := AddLaw muln_addl muln_addr.

Canonical Structure maxn_monoid := Law maxnA max0n maxn0.
Canonical Structure maxn_comoid := ComLaw maxnC.
Canonical Structure maxn_addoid := AddLaw maxn_mull maxn_mulr.

Canonical Structure gcdn_monoid := Law gcdnA gcd0n gcdn0.
Canonical Structure gcdn_comoid := ComLaw gcdnC.
Canonical Structure gcdn_addoid := AddLaw muln_gcdl muln_gcdr.

Canonical Structure lcmn_monoid := Law lcmnA lcm1n lcmn1.
Canonical Structure lcmn_comoid := ComLaw lcmnC.
Canonical Structure lcmn_addoid := AddLaw muln_lcml muln_lcmr.

Canonical Structure cat_monoid T := Law (@catA T) (@cat0s T) (@cats0 T).

End PervasiveMonoids.

(* Unit test for the [...law of ...] Notations
Definition myp := addn. Definition mym := muln.
Canonical Structure myp_mon := [law of myp].
Canonical Structure myp_cmon := [com_law of myp].
Canonical Structure mym_mul := [mul_law of mym].
Canonical Structure myp_add := [add_law _ of myp].
Print myp_add.
Print Canonical Projections.
*)

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
Definition natmul M x n := nosimpl iter _ n (add x) (zero M).

Notation Local "0" := (zero _).
Notation Local "- x" := (opp x).
Notation Local "+%R" := (@add _).
Notation Local "x + y" := (add x y).
Notation Local "x - y" := (x + - y).
Notation Local "x *+ n" := (natmul x n).
Notation Local "x *- n" := ((- x) *+ n).

Section ZmoduleTheory.

Variable M : Zmodule.type.
Implicit Types x y : M.

Lemma addrA : @associative M +%R. Proof. by case M => T [? []]. Qed.
Lemma addrC : @commutative M +%R. Proof. by case M => T [? []]. Qed.
Lemma add0r : @left_id M 0 +%R. Proof. by case M => T [? []]. Qed.
Lemma addNr : left_inverse 0 (@opp M) +%R. Proof. by case M => T [? []]. Qed.

Lemma addr0 : @right_id M 0 +%R.
Proof. by move=> x; rewrite addrC add0r. Qed.
Lemma addrN : right_inverse 0 (@opp M) +%R.
Proof. by move=> x; rewrite addrC addNr. Qed.
Definition subrr := addrN.

Canonical Structure add_monoid := Monoid.Law addrA add0r addr0.
Canonical Structure add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative M +%R. Proof. exact: mulmCA. Qed.
Lemma addrAC : @right_commutative M +%R. Proof. exact: mulmAC. Qed.

Lemma addKr : forall x, cancel ( +%R x) ( +%R (- x)).
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.
Lemma addrK : forall x, cancel ( +%R^~ x) ( +%R^~ (- x)).
Proof. by move=> x y; rewrite -addrA addrN addr0. Qed.
Lemma subrK : forall x, cancel ( +%R^~ (- x)) ( +%R^~ x).
Proof. by move=> x y; rewrite -addrA addNr addr0. Qed.
Lemma addrI : forall y, injective (add y).
Proof. move=> x; exact: can_inj (addKr x). Qed.
Lemma addIr : forall y, injective ( +%R^~ y).
Proof. move=> y; exact: can_inj (addrK y). Qed.
Lemma opprK : involutive (@opp M).
Proof. by move=> x; apply: (@addIr (- x)); rewrite addNr addrN. Qed.
Lemma oppr0 : -0 = 0 :> M.
Proof. by rewrite -[-0]add0r subrr. Qed.
Lemma oppr_eq0 : forall x, (- x == 0) = (x == 0).
Proof. by move=> x; rewrite (inv_eq opprK) oppr0. Qed.

Lemma oppr_add : forall x y, -(x + y) = - x - y.
Proof.
move=> x y; apply: (@addrI (x + y)).
by rewrite addrA subrr addrAC addrK subrr.
Qed.

Lemma mulr0n : forall x, x *+ 0 = 0. Proof. by []. Qed.
Lemma mulrS : forall x n, x *+ n.+1 = x + x *+ n. Proof. by []. Qed.

Lemma mulr1n : forall x, x *+ 1 = x. Proof. exact: addr0. Qed.

Lemma mulrSr : forall x n, x *+ n.+1 = x *+ n + x.
Proof. by move=> x n; rewrite addrC. Qed.

Lemma mul0rn : forall n, 0 *+ n = 0 :> M.
Proof. by elim=> // n IHn; rewrite mulrS add0r. Qed.

Lemma oppr_muln : forall x n, - (x *+ n) = x *- n :> M.
Proof. by move=> x; elim=> [|n IHn]; rewrite (oppr0, oppr_add) ?IHn. Qed.

Lemma mulrn_addl : forall x y n, (x + y) *+ n = x *+ n + y *+ n.
Proof.
move=> x y; elim=> [|n IHn]; rewrite ?addr0 // !mulrS. 
by rewrite addrCA -!addrA -IHn -addrCA.
Qed.

Lemma mulrn_addr : forall x m n, x *+ (m + n) = x *+ m + x *+ n.
Proof.
move=> x n m; elim: n => [|n IHn]; first by rewrite add0r.
by rewrite !mulrS IHn addrA.
Qed.

Lemma mulrnA : forall x m n, x *+ (m * n) = x *+ m *+ n.
Proof.
by move=> x m n; rewrite mulnC; elim: n => //= n IHn; rewrite mulrn_addr IHn.
Qed.

Lemma mulrnAC : forall x m n, x *+ m *+ n = x *+ n *+ m.
Proof. by move=> x m n; rewrite -!mulrnA mulnC. Qed.

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
Definition zmodType cT := Zmodule.Pack (class cT) cT.

End Ring.

Bind Scope ring_scope with Ring.sort.
Canonical Structure Ring.eqType.
Canonical Structure Ring.choiceType.
Canonical Structure Ring.zmodType.

Definition one R := Ring.one (Ring.class R).
Definition mul R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iter _ n (mul x) (one R).
Definition idr R x : R := x.

Notation Local "1" := (one _).
Notation Local "- 1" := (- (1)).
Notation Local "n %: R" := (@idr R 1 *+ n).
Notation Local "*%R" := (@mul _).
Notation Local "x * y" := (mul x y).
Notation Local "x ^+ n" := (exp x n).

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

Lemma natr_cst : forall n, n%:R = (if n is m.+1 then iter m (add 1) 1 else 0).
Proof. by case=> // n; rewrite /natmul -iter_f addr0. Qed.

Lemma mulr_natr : forall x n, x * n%:R = x *+ n.
Proof.
by move=> x; elim=> [|n IHn]; rewrite (mulr0, mulr_addr) ?IHn ?mulr1.
Qed.

Lemma mulr_natl : forall n x, n%:R * x = x *+ n.
Proof.
by move=> n x; elim: n => [|n IHn]; rewrite (mul0r, mulr_addl) ?mul1r ?IHn.
Qed.

Lemma natr_add : forall m n, (m + n)%:R = m%:R + n%:R.
Proof. by move=> m n; exact: mulrn_addr. Qed.

Lemma natr_mul : forall m n, (m * n)%:R = m%:R * n%:R.
Proof. by move=> m n; rewrite mulrnA -mulr_natr. Qed.

Lemma expr0 : forall x, x ^+ 0 = 1. Proof. by []. Qed.

Lemma exprS : forall x n, x ^+ n.+1 = x * x ^+ n. Proof. by []. Qed.

Lemma expr1 : forall x, x ^+ 1 = x. Proof. exact: mulr1. Qed.

Lemma exp1rn : forall n, 1 ^+ n = 1 :> R.
Proof. by elim=> // n IHn; rewrite exprS mul1r. Qed.

Lemma exprn_addr : forall x m n, x ^+ (m + n) = x ^+ m * x ^+ n.
Proof.
by move=> x m n; elim: m => [|m IHm]; rewrite ?mul1r // -mulrA -IHm.
Qed.

Lemma exprSr : forall x n, x ^+ n.+1 = x ^+ n * x.
Proof. by move=> x n; rewrite -addn1 exprn_addr expr1. Qed.

Definition comm x y := x * y = y * x.

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
move=> x y n com_xy; elim: n => [|n IHn]; [exact: commr0 | exact: commr_add].
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
move=> x y n com_xy; elim: n => [|n IHn]; [exact: commr1 | exact: commr_mul].
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
by rewrite mulSn exprn_addr IHm commr_exp_mull //; exact: commr_exp.
Qed.

Lemma signr_odd : forall n, (-1) ^+ (odd n) = (-1) ^+ n :> R.
Proof.
elim=> //= n IHn; rewrite exprS -{}IHn.
by case/odd: n; rewrite //= !mulN1r expr1 opprK.
Qed.

Lemma signr_addb : forall b1 b2,
  (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Proof. by do 2!case; rewrite ?expr1 ?mulN1r ?mul1r ?opprK. Qed.

Lemma exprN : forall x n, (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Proof.
by move=> x n; rewrite -mulN1r commr_exp_mull // /comm mulN1r mulrN mulr1.
Qed.

End RingTheory.

Prenex Implicits comm.

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

Lemma exprn_mull : forall x y n, (x * y) ^+ n = x ^+ n * y ^+ n.
Proof. move=> x y n; apply: commr_exp_mull; exact: mulrC. Qed.

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
Definition inv R := UnitRing.inv (UnitRing.class R).

Notation Local "x ^-1" := (inv x).
Notation Local "x / y" := (x * y^-1).
Notation Local "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : UnitRing.type.
Implicit Types x y : R.

Lemma divrr : forall x, unit x -> x / x = 1.
Proof. by case: R => T [? []]. Qed.

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

Lemma mulrK : forall x, unit x -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by move=> x Ux y; rewrite -mulrA divrr ?mulr1. Qed.

Lemma divrK : forall x, unit x -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by move=> x Ux y; rewrite -mulrA mulVr ?mulr1. Qed.

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
by move=> x n Ux; elim: n => [|n IHn]; rewrite ?unitr1 ?unitr_mull.
Qed.

Lemma unitr_pexp : forall x n, n > 0 -> unit (x ^+ n) = unit x.
Proof.
move=> x [//|n] _; rewrite exprS commr_unit_mul; last exact: commr_exp.
by case Ux: (unit x); rewrite // unitr_exp.
Qed.

Lemma expr_inv : forall x n, x^-1 ^+ n = x ^- n.
Proof.
move=> x; elim=> [|n IHn]; first by rewrite !expr0 ?invr1.
case Ux: (unit x); first by rewrite exprSr IHn -invr_mul // ?unitr_exp.
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

Notation Local "s `_ i" := (sub 0 s i).

Section EvalTerm.

Variable R : UnitRing.type.

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

Canonical Structure term_exprType := ExprType eval.

Lemma eq_eval : forall (t : term R) e e',
  sub 0 e =1 sub 0 e' -> t.[e] = t.[e'].
Proof.
by move=> t e e' eq_e; rewrite !evalE /=; elim: t => //= t1 -> // t2 ->.
Qed.

Definition set_nth s i v : seq R :=
  take i (s ++ seqn i 0) ++ v :: drop i.+1 s.

Lemma size_set_nth : forall s i v, size (set_nth s i v) = maxn i.+1 (size s).
Proof.
move=> s i v; rewrite size_cat size_takel ?size_cat ?size_seqn ?leq_addl //=.
by rewrite -addSnnS size_drop add_sub_maxn.
Qed.

Lemma sub_set_nth : forall s i v,
  sub 0 (set_nth s i v) =1 [fun j => s`_j with i |-> v].
Proof.
move=> s i v j; rewrite sub_cat size_takel ?size_cat ?size_seqn ?leq_addl //=.
case: ltngtP => [ltji | ltij | ->]; last by [rewrite subnn]; last first.
  by rewrite -subSS leq_subS //= sub_drop subnK.
rewrite sub_take // sub_cat; case: ltnP => [// | lesj].
rewrite (sub_default _ lesj); apply/eqP.
have: all (pred1 0) (@seqn R i 0) by rewrite all_pred1_seqn eqxx orbT.
move/allP; apply; rewrite mem_sub // size_seqn (leq_ltn_trans _ ltji) //.
exact: leq_subr.
Qed.

Lemma eval_tsubst : forall t e s, (tsubst t s).[e] = t.[set_nth e s.1 s.2.[e]].
Proof.
move=> t e [i u]; rewrite !evalE /=.
elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite sub_set_nth /=; case: eq_op.
Qed.

Fixpoint holds (f : formula R) (e : seq R) {struct f} : Prop :=
  match f with
  | Equal t1 t2 => t1.[e] = t2.[e]
  | Unit t1 => unit t1.[e]
  | And f1 f2 => holds f1 e /\ holds f2 e
  | Or f1 f2 => holds f1 e \/ holds f2 e
  | Implies f1 f2 => holds f1 e -> holds f2 e
  | Not f1 => ~ holds f1 e
  | Exists i f1 => exists x, holds f1 (set_nth e i x)
  | Forall i f1 => forall x, holds f1 (set_nth e i x)
  end.

Canonical Structure formula_exprType := ExprType holds.

Lemma eq_holds : forall (f : formula R) e e',
  sub 0 e =1 sub 0 e' -> (f.[e] <-> f.[e']).
Proof.
pose es1 e e' := @sub R 0 e =1 sub 0 e'.
have eq_i: forall i v, let sv e := set_nth e i v in
           forall e e', es1 e e' -> es1 (sv e) (sv e').
  by move=> i v /= e e' eq_e j; rewrite !sub_set_nth /= eq_e.
move=> f e e'; rewrite !evalE /=.
elim: f e e' => /=.
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

Lemma holds_fsubst : forall f e i v,
  (fsubst f (i, Const v)).[e] <-> f.[set_nth e i v].
Proof.
have setii: forall i e (v v' : R),
  set_nth (set_nth e i v') i v = set_nth e i v.
- move=> i e v v'; apply: (@eq_from_sub _ 0) => [|j _].
    by rewrite !size_set_nth maxnA maxnn.
  by do 2!rewrite !sub_set_nth /=; case: eqP.
have setij: forall i j e (v v' : R), i != j ->
  set_nth (set_nth e j v') i v = set_nth (set_nth e i v) j v'.
- move=> i j e v v' ne_ij; apply: (@eq_from_sub _ 0) => [|k _].
    by rewrite !size_set_nth maxnCA.
  by do 2!rewrite !sub_set_nth /=; case: eqP => // ->; rewrite -if_neg ne_ij.
move=> f e i v; rewrite !evalE /=.
elim: f e => /=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
  case: eqP => [->|] /=; last move/eqP=> ne_ji.
    by split=> [] [x f_x]; exists x; rewrite setii in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite setij //;
     move: (IHf (set_nth e j x)); tauto.
case: eqP => [->|] /=; last move/eqP=> ne_ji.
  by split=> [] f_ x; move: (f_ x); rewrite setii.
split=> [] f_ x; move: (f_ x); rewrite setij //;
     move: (IHf (set_nth e j x)); tauto.
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

Lemma unitrC_mul : forall x y, unit (x * y) = unit x && unit y.
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

Lemma mulr_eq0 : forall x y, (x * y == 0) = (x == 0) || (y == 0).
Proof.
move=> x y; apply/eqP/idP; first by case: R x y => T [].
by case/pred2P=> ->; rewrite (mulr0, mul0r).
Qed.

Lemma mulr_neq0 : forall x y, x != 0 -> y != 0 -> x * y != 0.
Proof. move=> x y x0 y0; rewrite mulr_eq0; exact/norP. Qed.

Lemma expr_eq0 : forall x n, (x ^+ n == 0) = (n > 0) && (x == 0).
Proof.
move=> x; elim=> [|n IHn]; first by rewrite oner_eq0.
by rewrite exprS mulr_eq0 IHn andKb.
Qed.

Lemma expr_neq0 : forall x m, x != 0 -> x ^+ m != 0.
Proof. by move=> x n x_nz; rewrite expr_eq0; apply/nandP; right. Qed.

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
Lemma mulKf : forall x, x != 0 -> cancel ( *%R x) ( *%R x^-1).
Proof. by move=> x; rewrite -unitfE; exact: mulKr. Qed.
Lemma mulfK : forall x, x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by move=> x; rewrite -unitfE; exact: mulrK. Qed.
Lemma divfK : forall x, x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by move=> x; rewrite -unitfE; exact: divrK. Qed.
Lemma mulfI : forall x, x != 0 -> injective ( *%R x).
Proof. by move=> x; rewrite -unitfE; exact: mulrI. Qed.
Lemma mulIf : forall x : F, x != 0 -> injective ( *%R^~ x).
Proof. by move=> x; rewrite -unitfE; exact: mulIr. Qed.

Lemma invf_mul : forall x y, (x * y)^-1 = x^-1 * y^-1.
Proof.
move=> x y; case: (eqVneq x 0) => [-> |nzx]; first by rewrite !(mul0r, invr0).
case: (eqVneq y 0) => [-> |nzy]; first by rewrite !(mulr0, invr0).
by rewrite mulrC invr_mul ?unitfE.
Qed.

End FieldTheory.

Module DecidableField.

Definition axiom (R : UnitRing.type) (s : formula R -> pred (seq R)) :=
  forall f e, reflect f.[e] (s f e).

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

(* Ultimately, there should be a QE Mixin comstrucutor *)

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

Definition Exists_n R n f : formula R := iter_n n (fun i => Exists i) f.

Lemma Exists_nP : forall f n e,
  reflect (exists s, (size s == n) && (sat f (s ++ drop n e)))
          (sat (Exists_n n f) e).
Proof.
have drop_set_nth: forall e n x, @drop F n (set_nth e n x) = x :: drop n.+1 e.
  move=> e n x; rewrite drop_cat size_takel ?size_cat ?size_seqn ?leq_addl //.
  by rewrite ltnn subnn drop0.  
move=> f n e; elim: n e => [|n IHn] e /=.
  by rewrite drop0; apply: (iffP idP) => [f_e | [[|] //]]; exists (Seq0 F).
case: satP => [sol | no_sol]; constructor.
  case: sol => x; move/satP; case/IHn=> /= s; case/andP=> sz_s.
  rewrite drop_set_nth -cat_add_last => f_s; exists (add_last s x).
  by rewrite size_add_last eqSS sz_s.
case; case/lastP=> // s x; rewrite size_add_last eqSS cat_add_last => f_sx.
case: no_sol; exists x; apply/satP; apply/IHn.
by exists s; rewrite drop_set_nth.
Qed.

Definition sol f n :=
  if insub [::] : {? e | sat (Exists_n n f) e} is Some u then
    @xchoose _ (fun x => _) (Exists_nP _ _ _ (valP u))
  else seqn n 0.

Lemma solP : forall f n,
  reflect (exists2 s, size s = n & f.[s]) (sat f (sol f n)).
Proof.
rewrite /sol => f n; case: insubP=> [u /= _ val_u | no_sol].
  set uP := Exists_nP _ _ _ _; case/andP: (xchooseP uP).
  move: {uP}(xchoose _) => s; rewrite {u}val_u cats0.
  move/eqP=> s_n f_s; rewrite f_s; left; exists s => //; exact/satP.
apply: (iffP idP) => [f0 | [s s_n f_s]]; case/Exists_nP: no_sol.
  by exists (@seqn F n 0); rewrite cats0 size_seqn eqxx.
exists s; rewrite cats0 s_n eqxx; exact/satP.
Qed.

Lemma size_sol : forall f n, size (sol f n) = n.
Proof.
rewrite /sol => f n; case: insubP=> [u /= _ _ | _]; last exact: size_seqn.
by set uP := Exists_nP _ _ _ _; case/andP: (xchooseP uP); move/eqP.
Qed.

Lemma eq_sat : forall f1 f2, (forall e, f1.[e] <-> f2.[e]) -> sat f1 =1 sat f2.
Proof. by move=> f1 f2 eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.
 
Lemma eq_sol : forall f1 f2, (forall e, f1.[e] <-> f2.[e]) -> sol f1 =1 sol f2.
Proof.
rewrite /sol => f1 f2; move/eq_sat=> eqf12 n.
case: insubP=> [u /= _ val_u | no_sol].
  have u2P: sat (Exists_n n f2) [::].
    apply/Exists_nP; case/Exists_nP: (valP u) => s.
    by rewrite eqf12 /= val_u; exists s.
  rewrite (insubT (sat _) u2P); apply: eq_xchoose => s.
  by rewrite /= val_u eqf12.
rewrite insubN //; apply: contra no_sol; case/Exists_nP=> s f2_s.
by apply/Exists_nP; exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Implicit Arguments satP [F f e].
Implicit Arguments solP [F f n].

Module ClosedField.

(* Axiom == all non-constant monic polynomials have a root *)
Definition axiom (R : Ring.type) :=
  forall p, p != [::] -> exists x, @foldr R R (fun c z => z * x + c) 1 p == 0.

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

Lemma solve_monicseq : ClosedField.axiom F.
Proof. by case: F => ? []. Qed.

End ClosedFieldTheory.

Module Theory.

Definition addrA := addrA.
Definition addrC := addrC.
Definition add0r := add0r.
Definition addNr := addNr.
Definition addr0 := addr0.
Definition addrN := addrN.
Definition addrCA := addrCA.
Definition addrAC := addrAC.
Definition addKr := addKr.
Definition addrK := addrK.
Definition subrK := subrK.
Definition addrI := addrI.
Definition addIr := addIr.
Definition opprK := opprK.
Definition oppr0 := oppr0.
Definition oppr_eq0 := oppr_eq0.
Definition oppr_add := oppr_add.
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
Definition natr_cst := natr_cst.
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
Definition signr_addb := signr_addb.
Definition exprN := exprN.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP := unitrP.
Definition mulKr := mulKr.
Definition mulrK := mulrK.
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
Definition mulrC := mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition exprn_mull := exprn_mull.
Definition unitrC_mul := unitrC_mul.
Definition mulr_eq0 := mulr_eq0.
Definition mulr_neq0 := mulr_neq0.
Definition expr_eq0 := expr_eq0.
Definition expr_neq0 := expr_neq0.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulfK := mulfK.
Definition divfK := divfK.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition invf_mul := invf_mul.
Definition satP := @satP.
Definition eq_sat := eq_sat.
Definition solP := @solP.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicseq := solve_monicseq.
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

Canonical Structure GRing.term_exprType.
Canonical Structure GRing.formula_exprType.

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
Notation "- x" := (GRing.opp x) : ring_scope.
Notation "+%R" := (@GRing.add _).
Notation "x + y" := (GRing.add x y) : ring_scope.
Notation "x - y" := (GRing.add x (- y)) : ring_scope.
Notation "x *+ n" := (GRing.natmul x n) : ring_scope.
Notation "x *- n" := (GRing.natmul (- x) n) : ring_scope.

Notation "1" := (GRing.one _) : ring_scope.
Notation "- 1" := (- (1))%R : ring_scope.

Notation "n %: R" := (GRing.natmul (@GRing.idr R 1%R) n) : ring_scope.
Notation "*%R" := (@GRing.mul _).
Notation "x * y" := (GRing.mul x y) : ring_scope.
Notation "x ^+ n" := (GRing.exp x n) : ring_scope.
Notation "x ^-1" := (GRing.inv x) : ring_scope.
Notation "x ^- n" := (x ^+ n)^-1%R : ring_scope.
Notation "x / y" := (GRing.mul x y^-1) : ring_scope.
Notation "s `_ i" := (sub 0%R s%R i) : ring_scope.

Implicit Arguments GRing.unitDef [].

Bind Scope term_scope with GRing.term.
Bind Scope term_scope with GRing.formula.

Notation "''X_' i" := (GRing.Var _ i)
  (at level 8, i at level 2, format "''X_' i") : term_scope.
Notation "n %: R" := (GRing.NatConst R n) : term_scope.
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
