Require Import ssreflect funs ssrbool eqtype.
Require Import ssrnat div.

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
(* indexed products and summations (see ssrbig.v).                  *)
(*   We then define a second class of structures that provide       *)
(* generic notation in addition to generic algebraic properties.    *)
(* For these the carrier is the data type.                          *)

Reserved Notation "x *+ n" (at level 40, n at level 9, left associativity,
           format "x *+ n").
Reserved Notation "x *- n" (at level 40, n at level 9, left associativity,
           format "x  *- n").
Reserved Notation "n `:` R" (at level 100, no associativity,
           format "n `:` R").
Reserved Notation "0" (at level 0).
Reserved Notation "1" (at level 0).
(*
Reserved Notation "2".
Reserved Notation "3".
Reserved Notation "4".
Reserved Notation "5".
*)
Reserved Notation "- 1" (at level 0).
Reserved Notation "x ^-1" (at level 9,
           format "x ^-1").
   (* Should be at level 2 -- need to patch groups.v*)
Reserved Notation "x ^2" (at level 2,
           format "x ^2").
Reserved Notation "x ^+ n" (at level 30, n at level 9, right associativity,
           format "x  ^+ n").
Reserved Notation "x ^- n" (at level 30, n at level 9, right associativity,
           format "x  ^- n").

(* Notation complement for functions and pairs (should move to funs.v). *)

Notation "f '^~' y" := (fun x => f x y)
  (at level 10, y at level 9, only parsing) : fun_scope.
Notation "p '.1'" := (fst p) (at level 2, format "p '.1'") : fun_scope.
Notation "p '.2'" := (snd p) (at level 2, format "p '.2'") : fun_scope.

(* End of complements. *)

Section OperationProperties.

Variable T : Type.
Variables zero one: T.
Variable inv : T -> T.
Variables mul add : T -> T -> T.

Notation Local "1"  := one.
Notation Local "x ^-1" := (inv x).
Notation Local "x * y"  := (mul x y).
Notation Local "0"  := zero.
Notation Local "x + y"  := (add x y).

Definition left_unit          := forall x,     1 * x = x.
Definition right_unit         := forall x,     x * 1 = x.
Definition left_inverse       := forall x,     x^-1 * x = 1.
Definition right_inverse      := forall x,     x * x^-1 = 1.
Definition associative        := forall x y z, x * (y * z) = x * y * z.
Definition commutative        := forall x y,   x * y = y * x.
Definition idempotent         := forall x,     x * x = x.
Definition left_commutative   := forall x y z, x * (y * z) = y * (x * z).
Definition right_commutative  := forall x y z, x * y * z = x * z * y.
Definition left_zero          := forall x,     0 * x = 0.
Definition right_zero         := forall x,     x * 0 = 0.
Definition left_distributive  := forall x y z, (x + y) * z = x * z + y * z.
Definition right_distributive := forall x y z, x * (y + z) = x * y + x * z.

End OperationProperties.

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
  phi unit = unit' /\ forall x y, phi (mul x y) = mul' (phi x) (phi y).

End Monoid.

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
Notation Local "- 1" := (- 1) : ring_scope.
(*
Notation "2" := (1 + 1) : ring_scope.
Notation "3" := (1 + 2) : ring_scope.
Notation "4" := (1 + 3) : ring_scope.
Notation "5" := (1 + 4) : ring_scope.
*)
Notation Local "n `:` R" := ((one R) *+ n) : ring_scope.
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

Lemma natr_cst : forall n, (n`:`R) = if n is m.+1 then iter m (add 1) 1 else 0.
Proof. by case=> // n; rewrite /natmul -iter_f addr0. Qed.

Lemma mulr_natr : forall x n, x * (n`:`R) = x *+n.
Proof. by move=> x; elim=> /= [|n <-]; rewrite (mulr0, mulr_addr) ?mulr1. Qed.

Lemma mulr_natl : forall n x, (n`:`R) * x = x *+n.
Proof.
by move=> n x; elim: n => /= [|n <-]; rewrite (mul0r, mulr_addl) ?mul1r.
Qed.

Lemma natr_add : forall m n, (m + n `:` R) = (m`:`R) + (n`:`R).
Proof. by move=> m n; exact: mulrn_addr. Qed.

Lemma natr_mul : forall m n, (m * n `:` R) = (m`:`R) * (n`:`R).
Proof.
by move=> m n; rewrite mulr_natl; elim: m => //= m <-; rewrite natr_add.
Qed.

Lemma exp1rn : forall n, 1 ^+ n = 1 :> R.
Proof. by elim=> //= n ->; rewrite mul1r. Qed.

Lemma expr0n : forall x : R, x ^+0 = 1. Proof. done. Qed.

Lemma expr1n : forall x : R, x ^+1 = x. Proof. exact: mulr1. Qed.

Lemma exprn_addr : forall x m n, x ^+(m + n) = x ^+m * x ^+n :> R.
Proof. by move=> x m n; elim: m => /= [|m ->]; rewrite (mul1r, mulrA). Qed.

Definition commute (x y : R) := x * y = y * x.

Lemma commr_sym : forall x y, commute x y -> commute y x. Proof. done. Qed.
Lemma commr_refl : forall x, commute x x. Proof. done. Qed.

Lemma commr0 : forall x, commute x 0.
Proof. by move=> x; rewrite /commute mulr0 mul0r. Qed.

Lemma commr1 : forall x, commute x 1.
Proof. by move=> x; rewrite /commute mulr1 mul1r. Qed.

Lemma commr_opp : forall x y, commute x y -> commute x (- y).
Proof. by move=> x y com_xy; rewrite /commute mulrN com_xy mulNr. Qed.

Lemma commrN1 : forall x, commute x -1.
Proof. move=> x; apply: commr_opp; exact: commr1. Qed.

Lemma commr_add : forall x y z,
  commute x y -> commute x z -> commute x (y + z).
Proof. by move=> x y z; rewrite /commute mulr_addl mulr_addr => -> ->. Qed.

Lemma commr_muln : forall x y n, commute x y -> commute x (y *+n).
Proof.
move=> x y n com_xy; elim: n => [|n IHn]; [exact: commr0 | exact: commr_add].
Qed.

Lemma commr_mul : forall x y z,
  commute x y -> commute x z -> commute x (y * z).
Proof.
by move=> x y z com_xy; rewrite /commute mulrA com_xy -!mulrA => ->.
Qed.

Lemma commr_nat : forall x n, commute x (n`:`R).
Proof. move=> x n; apply: commr_muln; exact: commr1. Qed.

Lemma commr_exp : forall x y n, commute x y -> commute x (y ^+n).
Proof.
move=> x y n com_xy; elim: n => [|n IHn]; [exact: commr1 | exact: commr_mul].
Qed.

Lemma commr_exp_mull : forall x y n,
  commute x y -> (x * y) ^+n = x ^+n * y ^+n.
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
by move=> x n; rewrite -mulN1r commr_exp_mull // /commute mulN1r mulrN mulr1.
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

Implicit Arguments Ring.addrI [R x x'].
Implicit Arguments Ring.addIr [R x x'].

Notation "0" := (Ring.zero _) : ring_scope.
Notation "- x" := (Ring.opp x) : ring_scope.
Notation "x + y" := (Ring.add x y) : ring_scope.
Notation "x - y" := (x + - y)%R : ring_scope.
Notation "x *+ n" := (Ring.natmul x n) : ring_scope.
Notation "x *- n" := ((- x) *+n)%R : ring_scope.

Notation "1" := (Ring.one _) : ring_scope.
Notation "- 1" := (- 1)%R : ring_scope.
(*
Notation "2" := (1 + 1) : ring_scope.
Notation "3" := (1 + 2) : ring_scope.
Notation "4" := (1 + 3) : ring_scope.
Notation "5" := (1 + 4) : ring_scope.
*)
Notation "n `:` R" := ((Ring.one R) *+ n)%R : ring_scope.
Notation "x * y" := (Ring.mul x y) : ring_scope.
Notation "x ^+ n" := (Ring.exp x n) : ring_scope.

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
Canonical Structure orb_addoid := AddLaw andb_orb_distrib_l andb_orb_distrib_r.
Canonical Structure andb_addoid := AddLaw orb_andb_distrib_l orb_andb_distrib_r.
Lemma andb_addl : left_distributive andb addb. Proof. by do 3!case. Qed.
Lemma andb_addr : right_distributive andb addb. Proof. by do 3!case. Qed.
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
Lemma max0n : left_unit 0 maxn. Proof. by case. Qed.
Lemma maxn0 : right_unit 0 maxn. Proof. done. Qed.
Lemma maxnC : commutative maxn.
Proof. by move=> m n; rewrite /maxn; case ltngtP. Qed.

Lemma add_sub_maxn : forall m n, m + (n - m) = maxn m n.
Proof.
move=> m n; rewrite /maxn; case: leqP; last by move/ltnW; move/leq_add_sub.
by move/eqnP->; rewrite addn0.
Qed.

Lemma maxnAC : right_commutative maxn.
Proof.
by move=> m n p; rewrite -!add_sub_maxn -!addnA -!subn_sub !add_sub_maxn maxnC.
Qed.

Lemma maxnA : associative maxn.
Proof. by move=> m n p; rewrite !(maxnC m) maxnAC. Qed.

Lemma maxnCA : left_commutative maxn.
Proof. by move=> m n p; rewrite !maxnA (maxnC m). Qed.

Canonical Structure maxn_monoid := Law maxnA max0n maxn0.
Canonical Structure maxn_abeloid := AbelianLaw maxnC.

Lemma maxn_leq : forall m n, (maxn m n == n) = (m <= n).
Proof. by move=> m n; rewrite maxnC -{2}[n]addn0 -add_sub_maxn eqn_addl. Qed.

Lemma maxn_geq : forall m n, (maxn m n == m) = (m >= n).
Proof. by move=> m n; rewrite -{2}[m]addn0 -add_sub_maxn eqn_addl. Qed.

Lemma maxnn : idempotent maxn.
Proof. by move=> n; apply/eqP; rewrite maxn_geq. Qed.

Lemma maxn_addl : left_distributive addn maxn.
Proof. by move=> m n p; rewrite -!add_sub_maxn subn_add2r mulmAC. Qed.

Lemma maxn_addr : right_distributive addn maxn.
Proof. by move=> m n p; rewrite !(addnC m) maxn_addl. Qed.

Lemma maxn_mulr : right_distributive muln maxn.
Proof. by case=> // m n p; rewrite /maxn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma maxn_mull : left_distributive muln maxn.
Proof. by move=> m n p; rewrite -!(mulnC p) maxn_mulr. Qed.

Canonical Structure maxn_addoid := AddLaw maxn_mull maxn_mulr.

Lemma gcd0n : left_unit 0 gcdn. Proof. by move=> n; rewrite gcdnC gcdn0. Qed.
Lemma gcdnAC : right_commutative gcdn.
Proof.
suff dvd: forall m n p, dvdn (gcdn (gcdn m n) p) (gcdn (gcdn m p) n).
  by move=> m n p; apply/eqP; rewrite eqn_dvd !dvd.
move: dvdn_gcdl dvdn_gcdr => dvdl dvdr m n p.
do ![apply dvdn_gcd]; by [|exact: (dvdn_trans (dvdn_gcdl _ _))].
Qed.
Lemma gcdnA : associative gcdn.
Proof. by move=> m n p; rewrite !(gcdnC m) gcdnAC. Qed.
Lemma gcdnCA : left_commutative gcdn.
Proof. by move=> m n p; rewrite !gcdnA (gcdnC m). Qed.
Lemma muln_gcdl : left_distributive muln gcdn.
Proof. by move=> m n p; rewrite -!(mulnC p) gcdn_mul2l. Qed.
Lemma muln_gcdr : right_distributive muln gcdn.
Proof. by move=> m n p; rewrite gcdn_mul2l. Qed.

Canonical Structure gcdn_monoid := Law gcdnA gcd0n gcdn0.
Canonical Structure gcdn_abeloid := AbelianLaw gcdnC.
Canonical Structure gcdn_addoid := AddLaw muln_gcdl muln_gcdr.

Definition lcmn m n := if m * n == 0 then m + n else divn (m * n) (gcdn m n).

Lemma lcmnC : commutative lcmn.
Proof. by move=> m n; rewrite /lcmn mulnC addnC gcdnC. Qed.

Lemma lcm0n : left_unit 0 lcmn. Proof. done. Qed.
Lemma lcmn0 : right_unit 0 lcmn. Proof. by move=> n; rewrite lcmnC. Qed.

Lemma muln_lcm_gcd : forall m n, m > 0 -> n > 0 -> lcmn m n * gcdn m n = m * n.
Proof.
move=> m n pos_m pos_n; rewrite /lcmn -if_neg -lt0n ltn_0mul pos_m pos_n /=.
apply/eqP; rewrite -dvdn_eq; apply dvdn_mull; exact: dvdn_gcdr.
Qed.

Lemma ltn_0lcm : forall m n, (lcmn m n > 0) = (m > 0) || (n > 0).
Proof.
move=> m n; case: (ltngtP 0 m) => [pos_m||<-] //.
case: (ltngtP 0 n) => // [pos_n|<-]; last by rewrite lcmn0.
have pos_dmn : gcdn m n > 0 by rewrite ltn_0gcd pos_m.
by rewrite -(ltn_pmul2r pos_dmn) muln_lcm_gcd // ltn_0mul pos_m.
Qed.

Lemma muln_lcmr : right_distributive muln lcmn.
Proof.
move=> m n p; case: (ltngtP 0 m) => [pos_m||<-] //.
case: (ltngtP 0 n) => // [pos_n|<-]; last by rewrite muln0.
case: (ltngtP 0 p) => // [pos_p|<-]; last by rewrite muln0 !lcmn0.
have posd_np : gcdn n p > 0 by rewrite ltn_0gcd pos_n.
apply/eqP; rewrite -(eqn_pmul2r posd_np) -mulnA muln_lcm_gcd //.
rewrite -(eqn_pmul2r pos_m) -!mulnA muln_gcdl mulnA -!(mulnC m).
by rewrite muln_lcm_gcd // !ltn_0mul pos_m.
Qed.

Lemma muln_lcml : left_distributive muln lcmn.
Proof. by move=> m n p; rewrite -!(mulnC p) muln_lcmr. Qed.

Lemma lcmnA : associative lcmn.
Proof.
move=> m n p; case: (ltngtP 0 m) => [pos_m||<-] //.
case: (ltngtP 0 n) => // [pos_n|<-]; last by rewrite lcmn0.
case: (ltngtP 0 p) => // [pos_p|<-]; last by rewrite !lcmn0.
have posm_np : lcmn n p > 0 by rewrite ltn_0lcm pos_n.
have posm_mn : lcmn m n > 0 by rewrite ltn_0lcm pos_m.
have posdm_mnp : gcdn m (lcmn n p) > 0 by rewrite ltn_0gcd pos_m.
have posd_np : gcdn n p > 0 by rewrite ltn_0gcd pos_n.
apply/eqP; rewrite -(eqn_pmul2r posdm_mnp) muln_lcm_gcd //.
rewrite -(eqn_pmul2r posd_np) -!mulnA muln_lcm_gcd //.
rewrite muln_gcdl muln_lcm_gcd // (muln_gcdr m) -gcdnA -muln_gcdl.
rewrite -[m * n]muln_lcm_gcd // (mulnC (gcdn m n)) -muln_gcdl.
by rewrite !mulnA muln_lcm_gcd // -!mulnA (mulnC p) !mulnA muln_lcm_gcd.
Qed.

Canonical Structure lcmn_monoid := Law lcmnA lcm0n lcmn0.
Canonical Structure lcmn_abeloid := AbelianLaw lcmnC.

End NatMonoids.

(*
Delimit Scope group_scope with G.

Require Import fintype.

Module Group.

Record class (T : Type) : Type := Class {
  unit_ : T;
  inv_ : T -> T;
  mul_ : T -> T -> T;
  _ : associative mul_;
  _ : left_unit unit_ mul_;
  _ : left_inverse unit_ inv_ mul_
}.

Structure type_ : Type := Type_ {
  sort :> Type;
  _ : class sort
}.

Section Operations.
Variable T : type_.
Definition dict := let: Type_ _ cT as T' := T return class T' in cT.
Definition unit := nosimpl unit_ T dict.
Definition inv := nosimpl inv_ T dict.
Definition mul := nosimpl mul_ T dict.
End Operations.
Open Scope group_scope.
Notation "1" := (unit _) : group_scope.
Notation "x ^-1" := (@inv _ x) : group_scope.
Notation "x * y" := (@mul _ x y) : group_scope.
Notation "x ^2" := (x * x) : group_scope.

Definition conj (T : type_) x y : T := y^-1 * x * y.
Notation "x ^ y" := (conj x y) : group_scope.

Definition exp (T : type_) x n : T := iter n (mul x) 1.
Notation "x ^+ n" := (exp x n) : group_scope.
Notation "x ^- n" := (x^-1 ^+ n) : group_scope.

Structure eqType_ : Type := EqType_ {
  eq_sort :> eqType;
  _ : class eq_sort
}.
Canonical Structure base_eq T :=
  Type_ (let: EqType_ _ c as T' := T return class T' in c).

Structure finType_ : Type := FinType_ {
  fin_sort :> finType;
  _ : class fin_sort
}.
Canonical Structure base_fin T :=
  EqType_ (let: FinType_ _ c as T' := T return class T' in c).

Definition bool_group_class := @Class _ _ (fun b => b) _ addbA addFb addbb.

Canonical Structure bool_group_type := Type_ bool_group_class.
Canonical Structure bool_group_eqtype := EqType_ bool_group_class.
Canonical Structure bool_group_fintype := FinType_ bool_group_class.

Module Equations.

Section Equations.

Variable T : type_.
Notation mul := (@mul T) (only parsing).
Notation inv := (@inv T) (only parsing).
Notation Local "'mulr' y" := (fun x : T => x * y) (at level 10).

Lemma mulgA : associative mul. Proof. by case: T => ? []. Qed.
Lemma mul1g : left_unit 1 mul. Proof. by case: T => ? []. Qed.
Lemma mulVg : left_inverse 1 inv mul. Proof. by case: T => ? []. Qed.

Lemma mulKg : forall x, cancel (mul x) (mul x^-1).
Proof. by move=> x y; rewrite mulgA mulVg mul1g. Qed.
Lemma mulIg : forall x, injective (mul x).
Proof. move=> x; exact: can_inj (mulKg x). Qed.

Lemma mulgV : right_inverse 1 inv mul.
Proof. by move=> x; rewrite -{1}(mulKg x^-1 x) mulVg -mulgA mul1g mulVg. Qed.
Lemma mulKgv : forall x, cancel (mul x^-1) (mul x).
Proof. by move=> x y; rewrite mulgA mulgV mul1g. Qed.
Lemma mulg1 : right_unit 1 mul.
Proof. by move=> x; rewrite -(mulVg x) mulKgv. Qed.

Canonical Structure group_monoid := Monoid.Law mulgA mul1g mulg1.

Lemma mulgK : forall x, cancel (mulr x) (mulr x^-1).
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.
Lemma mulgI : forall x, injective (mulr x).
Proof. move=> x; exact: can_inj (mulgK x). Qed.
Lemma mulgKv : forall x, cancel (mulr x^-1) (mulr x).
Proof. by move=> x y; rewrite -mulgA mulVg mulg1. Qed.

Lemma invg1 : 1^-1 = 1 :> T.
Proof. by rewrite -{2}(mulVg 1) mulg1. Qed.
Lemma invgK : involutive inv.
Proof. by move=> x; rewrite -{2}(mulgK x^-1 x) -mulgA mulKgv. Qed.
Lemma invg_mul : forall x y : T, (x * y)^-1 = y^-1 * x^-1. 
Proof. by move=> x y; apply: (@mulIg (x * y)); rewrite mulgA mulgK !mulgV. Qed.

End Equations.

End Equations.

*)

Unset Implicit Arguments.