Require Import ssreflect ssrfun ssrbool eqtype.
Require Import ssrnat div seq.

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
(* be the binary operation, rather than the data type or its unit.  *)
(*   The primary application of these structures are the generic    *)
(* indexed products and summations (see bigops.v).                  *)
(*   We then define a second class of structures that provide       *)
(* generic notation in addition to generic algebraic properties.    *)
(* For these the carrier is the data type.                          *)

Reserved Notation "x *+ n" (at level 40, n at level 9, left associativity).
Reserved Notation "x *- n" (at level 40, n at level 9, left associativity).
Reserved Notation "n %: R" (at level 2, R at level 1, left associativity,
           format "n %: R").

Reserved Notation "x ^+ n" (at level 29, n at level 9, left associativity).
Reserved Notation "x ^- n" (at level 29, n at level 9, left associativity).

Reserved Notation "f .[ x ]"
  (at level 2, left associativity, format "f .[ x ]").

Module Monoid.

Section Monoid.

Variable T : Type.
Variable unit : T.

Structure law : Type := Law {
  operator : T -> T -> T;
  _ : associative operator;
  _ : left_unit unit operator;
  _ : right_unit unit operator
}.

Structure abelian_law : Type := AbelianLaw {
   law_of_abelian :> law;
   _ : commutative (operator law_of_abelian)
}.

Structure mul_law : Type := MulLaw {
  mul_operator : T -> T -> T;
  _ : left_zero unit mul_operator;
  _ : right_zero unit mul_operator
}.

Structure add_law (mul_op : mul_law) : Type := AddLaw {
  law_of_additive :> abelian_law;
  _ : left_distributive (mul_operator mul_op) (operator law_of_additive);
  _ : right_distributive (mul_operator mul_op) (operator law_of_additive)
}.

End Monoid.

Module Equations.

Section Equations.

Variable T : Type.
Variable unit : T.
Coercion Local operator : law >-> Funclass.
Coercion Local mul_operator : mul_law >-> Funclass.

Section Plain.
Variable mul : law unit.
Lemma mul1m : left_unit unit mul. Proof. by case mul. Qed.
Lemma mulm1 : right_unit unit mul. Proof. by case mul. Qed.
Lemma mulmA : associative mul. Proof. by case mul. Qed.
End Plain.

Section Abelian.
Variable mul : abelian_law unit.
Lemma mulmC : commutative mul. Proof. by case mul. Qed.
Lemma mulmCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulmA (mulmC x). Qed.
Lemma mulmAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulmA (mulmC y). Qed.
End Abelian.

Section Ring.
Variables (mul : mul_law unit) (add : add_law mul).
Lemma mul0m : left_zero unit mul. Proof. by case mul. Qed.
Lemma mulm0 : right_zero unit mul. Proof. by case mul. Qed.
Lemma addmA : associative add. Proof. exact: mulmA. Qed.
Lemma addmC : commutative add. Proof. exact: mulmC. Qed.
Lemma addmCA : left_commutative add. Proof. exact: mulmCA. Qed.
Lemma addmAC : right_commutative add. Proof. exact: mulmAC. Qed.
Lemma add0m : left_unit unit add. Proof. exact: mul1m. Qed.
Lemma addm0 : right_unit unit add. Proof. exact: mulm1. Qed.
Lemma mulm_addl : left_distributive mul add. Proof. by case add. Qed.
Lemma mulm_addr : right_distributive mul add. Proof. by case add. Qed.
End Ring.

End Equations.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Equations.

Export Equations.

Definition morphism T T' unit unit' mul mul' (phi : T -> T') :=
  phi unit = unit' /\ {morph phi : x y / mul x y >-> mul' x y}.

End Monoid.

Notation "[ 'law' 'of' f ]" :=
  (match [is f : _ -> _ <: Monoid.law _] as s
   return {type of @Monoid.Law _ for s} -> _ with
  | Monoid.Law _ a ul ur => fun k => k a ul ur end
  (@Monoid.Law _ f)) (at level 0, only parsing) : form_scope.

Notation "[ 'abelian_law' 'of' f ]" :=
  (match [is f : _ -> _ <: Monoid.abelian_law _] as s
   return {type of @Monoid.AbelianLaw _ for s} with
  | Monoid.AbelianLaw _ c => fun k => k c end
  (@Monoid.AbelianLaw _ _ f)) (at level 0, only parsing) : form_scope.

Notation "[ 'mul_law' 'of' f ]" :=
  (match [is f : _ -> _ <: Monoid.mul_law _] as s
   return {type of @Monoid.MulLaw _ for s} -> _ with
  | Monoid.AddLaw _ zl zr => fun k => k zl zr end
  (@Monoid.AddLaw _ f)) (at level 0, only parsing) : form_scope.

Notation "[ 'add_law' 'of' f ]" :=
  (match [is f : _ -> _ <: Monoid.add_law _] as s
   return {type of @Monoid.AddLaw _ for s} -> _ with
  | Monoid.AddLaw _ dl dr => fun k => k dl dr end
  (@Monoid.AddLaw _ f)) (at level 0, only parsing) : form_scope.

Delimit Scope ring_scope with R.

Module Ring.

Structure additive_group : Type := AdditiveGroup {
  sort_ :> eqType;
  zero_ : sort_;
  opp_ : sort_ -> sort_;
  add_ : sort_ -> sort_ -> sort_;
  _ : associative add_;
  _ : commutative add_;
  _ : left_unit zero_ add_;
  _ : left_inverse zero_ opp_ add_
}.

Definition zero := nosimpl zero_.
Definition opp := nosimpl opp_.
Definition add := nosimpl add_.
Definition natmul R x n := iter n (add x) (zero R).

Bind Scope ring_scope with sort_.

Open Scope ring_scope.
Notation Local "0" := (zero _) : ring_scope.
Notation Local "- x" := (opp x) : ring_scope.
Notation Local "x + y" := (add x y) : ring_scope.
Notation Local "x - y" := (x + - y) : ring_scope.
Notation Local "x *+ n" := (natmul x n) : ring_scope.
Notation Local "x *- n" := ((- x) *+n) : ring_scope.

Section AdditiveEquations.
Variable R : additive_group.
Notation Local add := (@add R) (only parsing).
Notation Local opp := (@opp R) (only parsing).

Lemma addrA : associative add. Proof. by case R. Qed.
Lemma addrC : commutative add. Proof. by case R. Qed.
Lemma add0r : left_unit 0 add. Proof. by case R. Qed.
Lemma addNr : left_inverse 0 opp add. Proof. by case R. Qed.

Lemma addr0 : right_unit 0 add.
Proof. by move=> x; rewrite addrC add0r. Qed.
Lemma addrN : right_inverse 0 opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.
Definition subrr := addrN.
Lemma addrCA : left_commutative add.
Proof. by move=> x y z; rewrite !addrA (addrC x). Qed.
Lemma addrAC : right_commutative add.
Proof. by move=> x y z; rewrite -!addrA (addrC y). Qed.

Lemma addKr : forall x, cancel (add x) (add (- x)).
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.
Lemma addrK : forall x, cancel (add^~ x) (add^~ (- x)).
Proof. by move=> x y; rewrite -addrA addrN addr0. Qed.
Lemma addIr : forall y, injective (add y).
Proof. move=> x; exact: can_inj (addKr x). Qed.
Lemma addrI : forall y, injective (add^~ y).
Proof. move=> x; exact: can_inj (addrK x). Qed.
Lemma opprK : involutive opp.
Proof. by move=> x; apply: (@addrI (- x)); rewrite addNr addrN. Qed.
Lemma oppr0 : -0 = 0 :> R.
Proof. by rewrite -[-0]add0r subrr. Qed.
Lemma oppr_add : forall x y : R, -(x + y) = - x - y.
Proof.
by move=> x y; apply: (@addIr (x + y)); rewrite addrA subrr addrAC addrK subrr.
Qed.

Canonical Structure ring_add_monoid := Monoid.Law addrA add0r addr0.
Canonical Structure ring_add_abeloid := Monoid.AbelianLaw addrC.

Lemma mulr0n : forall n, 0 *+ n = 0 :> R.
Proof. by elim=> //= n ->; rewrite add0r. Qed.

Lemma oppr_muln : forall x n, - (x *+n) = x *-n :> R.
Proof. by move=> x; elim=> /= [|n <-]; rewrite (oppr0, oppr_add). Qed.

Lemma mulrn_addl : forall (x y : R) n, (x + y) *+n = x *+n + y *+n.
Proof. 
by move=> x y; elim=> /= [|n ->]; rewrite ?addrA (addr0, addrAC _ y).
Qed.

Lemma mulrnS : forall (x : R) n, x *+(n.+1) = x *+n + x.
Proof. by move=> x n /=; rewrite addrC. Qed.

Lemma mulrn_addr : forall (x : R) m n, x *+(m + n) = x *+m + x *+n.
Proof. by move=> x n m; elim: n => /= [|n ->]; rewrite (add0r, addrA). Qed.

Lemma mulrnA : forall (x : R) m n, x *+(m * n) = x *+m *+n.
Proof.
move=> x m n; rewrite mulnC; elim: n => //= n <-; exact: mulrn_addr.
Qed.

Lemma mulrnAC : forall (x : R) m n, x *+m *+n = x *+n *+m.
Proof. by move=> x m n; rewrite -!mulrnA mulnC. Qed.

End AdditiveEquations.

Structure basic : Type := Basic {
  base_ :> additive_group;
  one_ : base_;
  mul_ : base_ -> base_ -> base_;
  _ : associative mul_;
  _ : left_unit one_ mul_;
  _ : right_unit one_ mul_;
  _ : left_distributive mul_ (@add_ base_);
  _ : right_distributive mul_ (@add_ base_);
  _ : one_ <> 0
}.

Definition one := nosimpl one_.
Definition mul := nosimpl mul_.
Definition exp R x n := iter n (mul x) (one R).
Notation Local "1" := (one _) : ring_scope.
Notation Local "- 1" := (- (1)) : ring_scope.
(*
Notation "2" := (1 + 1) : ring_scope.
Notation "3" := (1 + 2) : ring_scope.
Notation "4" := (1 + 3) : ring_scope.
Notation "5" := (1 + 4) : ring_scope.
*)
Notation Local "n %: R" := ((one R) *+ n) : ring_scope.
Notation Local "x * y" := (mul x y) : ring_scope.
Notation Local "x ^+ n" := (exp x n) : ring_scope.

Section BasicRingEquations.

Variable R : basic.
Notation mul := (@mul R) (only parsing).
Notation add := (@add R) (only parsing).

Lemma mulrA : associative mul. Proof. by case R. Qed.
Lemma mul1r : left_unit 1 mul. Proof. by case R. Qed.
Lemma mulr1 : right_unit 1 mul. Proof. by case R. Qed.
Lemma mulr_addl : left_distributive mul add. Proof. by case R. Qed.
Lemma mulr_addr : right_distributive mul add. Proof. by case R. Qed.
Lemma nonzero1r : 1 <> 0 :> R. Proof. by case R. Qed.
Lemma nonzeroN1r : -1 <> 0 :> R.
Proof. rewrite -oppr0; move/(can_inj (@opprK _)); exact: nonzero1r. Qed.

Lemma mul0r : left_zero 0 mul.
Proof.
by move=> x; apply: (@addrI _ (1 * x)); rewrite -mulr_addl !add0r mul1r.
Qed.
Lemma mulr0 : right_zero 0 mul.
Proof.
by move=> x; apply: (@addrI _ (x * 1)); rewrite -mulr_addr !add0r mulr1.
Qed.
Lemma mulrN : forall x y : R, x * (- y) = - (x * y).
Proof.
by move=> x y; apply: (@addIr _ (x * y)); rewrite -mulr_addr !subrr mulr0.
Qed.
Lemma mulNr : forall x y : R, (- x) * y = - (x * y).
Proof.
by move=> x y; apply: (@addIr _ (x * y)); rewrite -mulr_addl !subrr mul0r.
Qed.
Lemma mulrNN : forall x y : R, (- x) * (- y) = x * y.
Proof. by move=> x y; rewrite mulrN mulNr opprK. Qed.
Lemma mulN1r : forall x, -1 * x = - x :> R.
Proof. by move=> x; rewrite mulNr mul1r. Qed.
Lemma mulrN1 : forall x, x * -1 = - x :> R.
Proof. by move=> x; rewrite mulrN mulr1. Qed.

Canonical Structure ring_monoid := Monoid.Law mulrA mul1r mulr1.
Canonical Structure ring_muloid := Monoid.MulLaw mul0r mulr0.
Canonical Structure ring_addoid := Monoid.AddLaw mulr_addl mulr_addr.

Lemma natr_cst : forall n, n%:R = (if n is m.+1 then iter m (add 1) 1 else 0).
Proof. by case=> // n; rewrite /natmul -iter_f addr0. Qed.

Lemma mulr_natr : forall x n, x * n%:R = x *+n.
Proof. by move=> x; elim=> /= [|n <-]; rewrite (mulr0, mulr_addr) ?mulr1. Qed.

Lemma mulr_natl : forall n x, n%:R * x = x *+n.
Proof.
by move=> n x; elim: n => /= [|n <-]; rewrite (mul0r, mulr_addl) ?mul1r.
Qed.

Lemma natr_add : forall m n, (m + n)%:R = m%:R + n%:R.
Proof. by move=> m n; exact: mulrn_addr. Qed.

Lemma natr_mul : forall m n, (m * n)%:R = m%:R * n%:R.
Proof.
by move=> m n; rewrite mulr_natl; elim: m => //= m <-; rewrite natr_add.
Qed.

Lemma exp1rn : forall n, 1 ^+ n = 1 :> R.
Proof. by elim=> //= n ->; rewrite mul1r. Qed.

Lemma expr0n : forall x : R, x ^+0 = 1. Proof. done. Qed.

Lemma expr1n : forall x : R, x ^+1 = x. Proof. exact: mulr1. Qed.

Lemma exprn_addr : forall x m n, x ^+(m + n) = x ^+m * x ^+n :> R.
Proof. by move=> x m n; elim: m => /= [|m ->]; rewrite (mul1r, mulrA). Qed.

Definition commb (x y : R) := x * y = y * x.

Lemma commr_sym : forall x y, commb x y -> commb y x. Proof. done. Qed.
Lemma commr_refl : forall x, commb x x. Proof. done. Qed.

Lemma commr0 : forall x, commb x 0.
Proof. by move=> x; rewrite /commb mulr0 mul0r. Qed.

Lemma commr1 : forall x, commb x 1.
Proof. by move=> x; rewrite /commb mulr1 mul1r. Qed.

Lemma commr_opp : forall x y, commb x y -> commb x (- y).
Proof. by move=> x y com_xy; rewrite /commb mulrN com_xy mulNr. Qed.

Lemma commrN1 : forall x, commb x (-1).
Proof. move=> x; apply: commr_opp; exact: commr1. Qed.

Lemma commr_add : forall x y z,
  commb x y -> commb x z -> commb x (y + z).
Proof. by move=> x y z; rewrite /commb mulr_addl mulr_addr => -> ->. Qed.

Lemma commr_muln : forall x y n, commb x y -> commb x (y *+n).
Proof.
move=> x y n com_xy; elim: n => [|n IHn]; [exact: commr0 | exact: commr_add].
Qed.

Lemma commr_mul : forall x y z,
  commb x y -> commb x z -> commb x (y * z).
Proof.
by move=> x y z com_xy; rewrite /commb mulrA com_xy -!mulrA => ->.
Qed.

Lemma commr_nat : forall x n, commb x n%:R.
Proof. move=> x n; apply: commr_muln; exact: commr1. Qed.

Lemma commr_exp : forall x y n, commb x y -> commb x (y ^+n).
Proof.
move=> x y n com_xy; elim: n => [|n IHn]; [exact: commr1 | exact: commr_mul].
Qed.

Lemma commr_exp_mull : forall x y n,
  commb x y -> (x * y) ^+n = x ^+n * y ^+n.
Proof.
move=> x y n com_xy; elim: n => /= [|n ->]; first by rewrite mulr1.
by rewrite !mulrA; congr (_ * _); rewrite -!mulrA -commr_exp.
Qed.

Lemma exprn_mulnl : forall x m n, (x *+m) ^+n = x ^+n *+(m ^ n) :> R.
Proof.
move=> x m n; elim: n => /= [|n ->]; first by rewrite addr0.
rewrite -mulr_natr -!mulrA mulr_natl -mulrnA mulnC.
by rewrite -mulr_natr mulrA mulr_natr.
Qed.

Lemma exprn_mulr : forall x m n, x ^+ (m * n) = x ^+m ^+n :> R.
Proof.
move=> x m n; elim: m => /= [|m IHm]; first by rewrite exp1rn.
rewrite exprn_addr IHm commr_exp_mull //; exact: commr_exp.
Qed.

Lemma signr_odd : forall n, (-1) ^+(odd n) = (-1) ^+n :> R.
Proof. by elim=> //= n <-; case/odd: n; rewrite //= !mulN1r opprK. Qed.

Lemma signr_addb : forall b1 b2, (-1)^+(b1 (+) b2) = (-1)^+b1 * (-1)^+b2 :> R.
Proof. by do 2!case; rewrite /= ?mulN1r ?mul1r ?opprK. Qed.

Lemma exprN : forall x n, (- x) ^+n = (-1) ^+n * x ^+ n :> R.
Proof.
by move=> x n; rewrite -mulN1r commr_exp_mull // /commb mulN1r mulrN mulr1.
Qed.

End BasicRingEquations.

Structure commutative_ : Type := Commutative {
  ring_ :> basic;
  _ : commutative (@mul_ ring_)
}.

Section CommutativeRingEquations.
Variable R : commutative_.
Notation Local mul := (@mul R) (only parsing).

Lemma mulrC : commutative mul. Proof. by case R. Qed.
Lemma mulrCA : left_commutative mul.
Proof. by move=> x y z; rewrite !mulrA (mulrC x). Qed.
Lemma mulrAC : right_commutative mul.
Proof. by move=> x y z; rewrite -!mulrA (mulrC y). Qed.
Canonical Structure ring_abeloid := Monoid.AbelianLaw mulrC.

Lemma exprn_mull : forall x y n, (x * y) ^+n = x ^+n * y ^+n :> R.
Proof. move=> x y n; apply: commr_exp_mull; exact: mulrC. Qed.

End CommutativeRingEquations.

End Ring.

Canonical Structure Ring.ring_add_abeloid.
Canonical Structure Ring.ring_add_monoid.
Canonical Structure Ring.ring_monoid.
Canonical Structure Ring.ring_abeloid.
Canonical Structure Ring.ring_muloid.
Canonical Structure Ring.ring_addoid.

Implicit Arguments Ring.addrI [R x1 x2].
Implicit Arguments Ring.addIr [R x1 x2].

Notation "0" := (Ring.zero _) : ring_scope.
Notation "- x" := (Ring.opp x) : ring_scope.
Notation "x + y" := (Ring.add x y) : ring_scope.
Notation "x - y" := (x + - y)%R : ring_scope.
Notation "x *+ n" := (Ring.natmul x n) : ring_scope.
Notation "x *- n" := ((- x) *+n)%R : ring_scope.

Notation "1" := (Ring.one _) : ring_scope.
Notation "- 1" := (- (1))%R : ring_scope.
(*
Notation "2" := (1 + 1) : ring_scope.
Notation "3" := (1 + 2) : ring_scope.
Notation "4" := (1 + 3) : ring_scope.
Notation "5" := (1 + 4) : ring_scope.
*)
Notation "n %: R" := ((Ring.one R) *+ n)%R : ring_scope.
Notation "x * y" := (Ring.mul x y) : ring_scope.
Notation "x ^+ n" := (Ring.exp x n) : ring_scope.
Notation "s .[ i ]" :=  (sub 0%R s i) : ring_scope.

Import Ring.
(* Fields *)
Module Field.

Delimit Scope field_scope with F.

Structure field : Type := Field {
  field_ :> commutative_;
  inv_ : field_ -> field_;
  _ : forall x, x != 0 -> (inv_ x) * x = 1
}.

Definition inv := nosimpl inv_.

Bind Scope field_scope with field_.
Open Scope field_scope.
Notation Local "x ^-1" := (inv x) : field_scope.

Section FieldEquations.
Variable F : field.
Notation Local mul := (@mul F) (only parsing).
Notation Local inv := (@inv F) (only parsing).

Lemma mulfV: forall x : F, (x != 0) -> x^-1 * x = 1.
Proof. by case: F. Qed.
Lemma mulVf: forall x : F, (x != 0) -> x * x^-1 = 1.
Proof. by move=>*; rewrite mulrC mulfV. Qed.
Lemma mulKf : forall x : F, (x != 0) -> cancel (mul x) (mul x^-1).
Proof. by move=> x Hx y; rewrite mulrA mulfV// mul1r. Qed.
Lemma mulfK : forall x : F, (x != 0) -> cancel (mul^~ x) (mul^~ x^-1).
Proof. by move=> x Hx y; rewrite -mulrA mulVf// mulr1. Qed.
Lemma mulIf : forall x : F, (x != 0) -> injective (mul x).
Proof. move=> x Hx; exact: can_inj (mulKf Hx). Qed.
Lemma mulfI : forall x : F, (x != 0) -> injective (mul^~ x).
Proof. move=> x Hx; exact: can_inj (mulfK Hx). Qed.
Lemma neq0I: forall x : F, x != 0 -> (x^-1) != 0.
Proof.
move=> x Hx; apply/eqP; move/(congr1 (mul x)).
by rewrite mulVf// mulr0; move: (@nonzero1r F).
Qed.
Lemma neq0_mul : forall x y : F, x != 0 -> y != 0 -> (x * y != 0).
Proof.
move=> x y Hx Hy; apply/eqP; move/(congr1 (mul (x^-1))).
by rewrite mulr0 mulrA mulfV// mul1r; apply/eqP.
Qed.
Lemma invfK : forall x : F, (x != 0) -> (x^-1)^-1 = x.
Proof.
move=> x Hx; apply: (mulfI (neq0I Hx)).
rewrite mulfV ?mulVf//.
by apply: neq0I.
Qed.
Lemma invf1 : 1^-1 = 1 :> F.
Proof. by rewrite -[1^-1]mul1r mulVf; [|apply/eqP; exact: nonzero1r]. Qed.
Lemma invfI : forall x1 x2 : F,
 (x1 != 0) -> (x2 != 0) -> (x1^-1 = x2^-1) -> x1 = x2.
Proof.
by move => x1 x2 H1 H2 Heq; rewrite -(invfK H1) -(invfK H2) Heq.
Qed.
Lemma invf_mul : forall x y : F,
 x != 0 -> y != 0 -> (x * y)^-1 = x^-1 * y^-1.
Proof.
move=> x y Hx Hy.
apply: (mulfI (neq0_mul Hx Hy)); rewrite mulfV; last (by apply: neq0_mul).
by rewrite mulrA mulrAC mulrC -mulrA mulfV// mulr1 mulVf.
Qed.

End FieldEquations.
End Field.

Notation "x ^-1" := (Field.inv x) : field_scope.

Notation "[ 'agroupType' 'of' t ]" :=
  (match [is t : Type <: additive_group] as s
   return {type of AdditiveGroup for s} -> _ with
  | AdditiveGroup _ _ _ _ a c u i => fun k => k _ _ _ a c u i end
  (@AdditiveGroup t)) (at level 0, only parsing) : form_scope.

Notation "[ 'ringType' 'of' t ]" :=
  (match [is t : Type <: basic] as s return {type of Basic for s} -> _ with
  | Basic _ _ _ a ul ur dl dr nz => fun k => k _ _ a ul ur dl dr nz end
  (@Basic t)) (at level 0, only parsing) : form_scope.

Notation "[ 'cringType' 'of' t ]" :=
  (match [is t : Type <: commutative_] as s
   return {type of Commutative for s} -> _ with
  | Commutative _ c => fun k => k c end
  (@Commutative t)) (at level 0, only parsing) : form_scope.

Notation "[ 'fieldType' 'of' t ]" :=
  (match [is t : Type <: Field.field] as s
   return {type of Field.Field for s} -> _ with
  | Field.Field _ _ nzi => fun k => k _ nzi end
  (@Field.Field t)) (at level 0, only parsing) : form_scope.

Require Import ssrbool.

Section BoolMonoids.

Import Monoid.

Canonical Structure andb_monoid := Law andbA andTb andbT.
Canonical Structure andb_abeloid := AbelianLaw andbC.
Canonical Structure andb_muloid := MulLaw andFb andbF.
Canonical Structure orb_monoid := Law orbA orFb orbF.
Canonical Structure orb_abeloid := AbelianLaw orbC.
Canonical Structure orb_muloid := MulLaw orTb orbT.
Canonical Structure addb_monoid := Law addbA addFb addbF.
Canonical Structure addb_abeloid := AbelianLaw addbC.
Canonical Structure orb_addoid := AddLaw andb_orl andb_orr.
Canonical Structure andb_addoid := AddLaw orb_andl orb_andr.
Canonical Structure addb_addoid := AddLaw andb_addl andb_addr.

End BoolMonoids.

Require Import ssrnat div.

Section NatMonoids.

Import Monoid.

Canonical Structure addn_monoid := Law addnA add0n addn0.
Canonical Structure addn_abeloid := AbelianLaw addnC.
Canonical Structure muln_monoid := Law mulnA mul1n muln1.
Canonical Structure muln_abeloid := AbelianLaw mulnC.
Canonical Structure muln_muloid := MulLaw mul0n muln0.
Canonical Structure addn_addoid := AddLaw muln_addl muln_addr.

Canonical Structure maxn_monoid := Law maxnA max0n maxn0.
Canonical Structure maxn_abeloid := AbelianLaw maxnC.

Canonical Structure maxn_addoid := AddLaw maxn_mull maxn_mulr.

Canonical Structure gcdn_monoid := Law gcdnA gcd0n gcdn0.
Canonical Structure gcdn_abeloid := AbelianLaw gcdnC.
Canonical Structure gcdn_addoid := AddLaw muln_gcdl muln_gcdr.

Canonical Structure lcmn_monoid := Law lcmnA lcm0n lcmn0.
Canonical Structure lcmn_abeloid := AbelianLaw lcmnC.

End NatMonoids.

Unset Implicit Arguments.