(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import eqtype.

Require Import BinNat.
Require Export Ring.
Require BinPos.
Require Ndec.

(*   A "reflected" version of Arith, with an emphasis on boolean predicates *)
(* and rewriting; this includes a canonical eqType for nat, as well as      *)
(* reflected predicates, <= (leq) and < for comparison m < n is actually a  *)
(* Notation for m.+1 < n. This has one serious advantage: reduction happens *)
(* in the same way in <= and <, and one drawback: rewrites that match <=    *)
(* will also match <.                                                       *)
(*   Also <= is defined so that it does NOT simpl'ify; instead, rewrite     *)
(* rules are provided for cases where it is useful to do simplification.    *)
(* This makes the manipulation of assertions much more stable, while still  *)
(* allowing conversion for trivial cases.                                   *)
(*   Stable versions of plus and minus, addn and subn, respectively, are    *)
(* provided for the same reasons, and the standard arithmetic lemmas are    *)
(* replicated.                                                              *)
(*   Also included are replacements for the div2 lemmas, that fit better    *)
(* with the rest of the theory.                                             *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Declare legacy Arith operators in new scope. *)

Delimit Scope coq_nat_scope with coq_nat.

Notation "m + n" := (plus m n) : coq_nat_scope.
Notation "m - n" := (minus m n) : coq_nat_scope.
Notation "m * n" := (mult m n) : coq_nat_scope.
Notation "m <= n" := (le m n) : coq_nat_scope.
Notation "m < n" := (lt m n) : coq_nat_scope.
Notation "m >= n" := (ge m n) : coq_nat_scope.
Notation "m > n" := (gt m n) : coq_nat_scope.

(* Rebind scope delimiters, reserving a scope for the "recursive",     *)
(* i.e., unprotected version of operators.                             *)

Delimit Scope N_scope with num.
Delimit Scope nat_scope with N.
Delimit Scope nat_rec_scope with Nrec.

(* Postfix notation for the successor and predecessor functions.  *)
(* SSreflect uses "pred" for the generic predicate type, and S as *)
(* a local bound variable.                                        *)

Notation succn := Datatypes.S (only parsing).

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

(* We provide a structurally decreasing predecessor function. *)

Definition predn n := if n is n'.+1 then n' else n.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Lemma predE : Peano.pred =1 predn. Proof. by case. Qed.
Lemma succnK : cancel succn predn. Proof. by []. Qed.
Lemma succn_inj : injective succn. Proof. by move=> n m []. Qed.

(* Predeclare postfix doubling/halving operators. *)

Reserved Notation "n .*2" (at level 2, format "n .*2").
Reserved Notation "n ./2" (at level 2, format "n ./2").

(* Patch for ssreflect match pattern bug -- see ssrbool.v. *)

Definition ifn_expr T n x y : T := if n is n'.+1 then x n' else y.

Lemma ifnE : forall T x y n,
  (if n is n'.+1 then x n' else y) = ifn_expr n x y :> T.
Proof. by []. Qed.


(* Canonical comparison and eqType for nat.                                *)

Fixpoint eqn (m n : nat) {struct m} : bool :=
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : reflect_eq eqn.
Proof.
move=> n m; apply: (iffP idP) => [|<-]; last by elim n.
by elim: n m => [|n IHn] [|m] //=; move/IHn->.
Qed.

Canonical Structure nat_eqMixin := EqMixin eqnP.
Canonical Structure nat_eqType := EqClass nat_eqMixin.

Implicit Arguments eqnP [x y].
Prenex Implicits eqnP.

Lemma eqnE : eqn = eqd. Proof. by []. Qed.

Lemma eqSS : forall m n, (m.+1 == n.+1) = (m == n). Proof. by []. Qed.

Lemma nat_irrelevance : forall (x y : nat) (E E' : x = y), E = E'.
Proof. exact: eq_irrelevance. Qed.

(* Protected addition, with a more systematic set of lemmas.                *)

Definition addn_rec := plus.
Notation "m + n" := (addn_rec m n) : nat_rec_scope.

Definition addn := nosimpl addn_rec.
Notation "m + n" := (addn m n) : nat_scope.

Lemma addnE : addn = addn_rec. Proof. by []. Qed.

Lemma plusE : plus = addn. Proof. by []. Qed.

Lemma add0n : left_unit 0 addn.                  Proof. by []. Qed.
Lemma addSn : forall m n, m.+1 + n = (m + n).+1. Proof. by []. Qed.
Lemma add1n : forall n, 1 + n = n.+1.            Proof. by []. Qed.

Lemma addn0 : right_unit 0 addn. Proof. by move=> n; apply/eqP; elim: n. Qed.

Lemma addnS : forall m n, m + n.+1 = (m + n).+1.
Proof. by move=> m n; elim: m. Qed.

Lemma addSnnS : forall m n, m.+1 + n = m + n.+1.
Proof. by move=> *; rewrite addnS. Qed.

Lemma addnCA : left_commutative addn.
Proof. by move=> m n p; elim: m => //= m; rewrite addnS => <-. Qed.

Lemma addnC : commutative addn.
Proof. by move=> m n; rewrite -{1}[n]addn0 addnCA addn0. Qed.

Lemma addn1 : forall n, n + 1 = n.+1.
Proof. by move=> n; rewrite addnC. Qed.

Lemma addnA : associative addn.
Proof. by move=> m n *; rewrite (addnC n) addnCA addnC. Qed.

Lemma addnAC : right_commutative addn.
Proof. by move=> m n p; rewrite -!addnA (addnC n). Qed.

Lemma eqn_add0 : forall m n, (m + n == 0) = (m == 0) && (n == 0).
Proof. by do 2 case. Qed.

Lemma eqn_addl : forall p m n, (p + m == p + n) = (m == n).
Proof. by move=> p *; elim p. Qed.

Lemma eqn_addr : forall p m n, (m + p == n + p) = (m == n).
Proof. by move=> p *; rewrite -!(addnC p) eqn_addl. Qed.

Lemma addn_injl : forall p, injective (addn p).
Proof. by move=> p m n Heq; apply: eqP; rewrite -(eqn_addl p) Heq eqxx. Qed.

Lemma addn_injr : forall p, injective (addn^~ p).
Proof. move=> p m n; rewrite -!(addnC p); apply addn_injl. Qed.

Lemma addn2 : forall m, m + 2 = m.+2. Proof. by move=> *; rewrite addnC. Qed.
Lemma add2n : forall m, 2 + m = m.+2. Proof. by []. Qed.
Lemma addn3 : forall m, m + 3 = m.+3. Proof. by move=> *; rewrite addnC. Qed.
Lemma add3n : forall m, 3 + m = m.+3. Proof. by []. Qed.
Lemma addn4 : forall m, m + 4 = m.+4. Proof. by move=> *; rewrite addnC. Qed.
Lemma add4n : forall m, 4 + m = m.+4. Proof. by []. Qed.

Section Iteration.

Variable T : Type.

Definition iter_n n f x : T :=
  let fix loop (m : nat) := if m is i.+1 then f i (loop i) else x in loop n.

Definition iter n f x : T :=
  let fix loop (m : nat) := if m is i.+1 then f (loop i) else x in loop n.

Lemma iter_f : forall n f x, iter n f (f x) = iter n.+1 f x.
Proof. by move=> n f x; elim: n => //= n ->. Qed.

Lemma f_iter : forall n f x, f (iter n f x) = iter n.+1 f x.
Proof. by []. Qed.

Lemma eq_iter : forall f f', f =1 f' -> forall n, iter n f =1 iter n f'.
Proof. by move=> f f' Ef n x; elim: n => //= n ->; rewrite Ef. Qed.

Lemma eq_iter_n : forall f f', f =2 f' -> forall n, iter_n n f =1 iter_n n f'.
Proof. by move=> f f' Ef n x; elim: n => //= n ->; rewrite Ef. Qed.

Lemma iter_addn : forall n m f x, iter (n + m) f x = iter n f (iter m f x).
Proof. by move=> n m f x; elim: n => //= n ->. Qed.

End Iteration.

(* Protected, structurally decreasing substraction, and basic lemmas. *)
(* Further properties depend on ordering conditions.                  *)

Fixpoint subn_rec (m n : nat) {struct m} :=
  match m, n with
  | m'.+1, n'.+1 => (m' - n')%Nrec
  | _, _ => m
  end
where "m - n" := (subn_rec m n) : nat_rec_scope.

Definition subn := nosimpl subn_rec.
Notation "m - n" := (subn m n) : nat_scope.

Lemma subnE : subn = subn_rec. Proof. by []. Qed.
Lemma minusE : minus =2 subn.
Proof. elim=> [|m IHm] [|n] //=; exact: IHm. Qed.

Lemma sub0n : left_zero 0 subn.    Proof. by []. Qed.
Lemma subn0 : right_unit 0 subn.   Proof. by case. Qed.
Lemma subnn : self_inverse 0 subn. Proof. by elim. Qed.

Lemma subSS : forall n m, m.+1 - n.+1 = m - n. Proof. by []. Qed.
Lemma subn1 : forall n, n - 1 = n.-1.          Proof. by do 2?case. Qed.

Lemma subn_add2l : forall p m n, (p + m) - (p + n) = m - n.
Proof. by move=> p *; elim p. Qed.

Lemma subn_add2r : forall p m n, (m + p) - (n + p) = m - n.
Proof. by move=> p *; rewrite -!(addnC p) subn_add2l. Qed.

Lemma addKn : forall n, cancel (addn n) (subn^~ n).
Proof. by move=> n m; rewrite -{2}[n]addn0 subn_add2l subn0. Qed.

Lemma addnK : forall n, cancel (addn^~ n) (subn^~ n).
Proof. by move=> n m; rewrite (addnC m) addKn. Qed.

Lemma subSnn : forall n, n.+1 - n = 1.
Proof. move=> n; exact (addnK n 1). Qed.

Lemma subn_sub : forall m n p, (n - m) - p = n - (m + p).
Proof. by move=> m n p; elim: m n => [|m IHm] [|n]; try exact (IHm n). Qed.

(* Integer ordering, and its interaction with the other operations.       *)

Definition leq m n := m - n == 0.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n"  := (m.+1 <= n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n"  := (n < m) (only parsing)  : nat_scope.

(* For sorting, etc. *)
Definition ltn := [rel m n | m < n].

Notation "m <= n <= p" := ((m <= n) && (n <= p)) : nat_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : nat_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : nat_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : nat_scope.

Lemma ltnS : forall m n, (m < n.+1) = (m <= n).
Proof. by []. Qed.

Lemma leq0n : forall n, 0 <= n.
Proof. by []. Qed.

Lemma ltn0Sn : forall n, 0 < n.+1.
Proof. by []. Qed.

Lemma ltn0 : forall n, n < 0 = false.
Proof. by []. Qed.

Lemma leqnn : forall n, n <= n.
Proof. by elim. Qed.
Hint Resolve leqnn.

Lemma ltnSn : forall n, n < n.+1.
Proof. by []. Qed.

Lemma eq_leq : forall m n, m = n -> m <= n.
Proof. by move=> m n <-. Qed.

Lemma leqnSn : forall n, n <= n.+1.
Proof. by elim. Qed.
Hint Resolve leqnSn.

Lemma leq_pred : forall n, n.-1 <= n.
Proof. by case=> /=. Qed.

Lemma leqSpred : forall n, n <= n.-1.+1.
Proof. by case=> /=. Qed.

Lemma ltn_predK : forall m n, m < n -> n.-1.+1 = n.
Proof. by move=> ? []. Qed.

Lemma prednK : forall n, 0 < n -> n.-1.+1 = n.
Proof. by case. Qed.

Lemma leqNgt : forall m n, (m <= n) = ~~ (n < m).
Proof. by elim=> [|m IHm] [|n] //; rewrite ltnS IHm. Qed.

Lemma ltnNge : forall m n, (m < n) = ~~ (n <= m).
Proof. by move=> *; rewrite leqNgt. Qed.

Lemma ltnn : forall n, n < n = false.
Proof. by move=> *; rewrite ltnNge leqnn. Qed.

Lemma leqn0 : forall n, (n <= 0) = (n == 0).
Proof. by case. Qed.

Lemma lt0n : forall n, (0 < n) = (n != 0).
Proof. by case. Qed.

Lemma lt0n_neq0 : forall n, 0 < n -> n != 0.
Proof. by case. Qed.

Lemma eqn0Ngt : forall n, (n == 0) = ~~ (n > 0).
Proof. by case. Qed.

Lemma neq0_lt0n : forall n, (n == 0) = false -> 0 < n.
Proof. by case. Qed.
Hint Resolve lt0n_neq0 neq0_lt0n.

Lemma eqn_leq : forall m n, (m == n) = (m <= n <= m).
Proof. elim=> [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma anti_leq : antisymmetric leq.
Proof. by move=> m n; rewrite -eqn_leq; move/eqP. Qed.

Lemma neq_ltn : forall m n, (m != n) = (m < n) || (n < m).
Proof. by move=> *; rewrite eqn_leq negb_and orbC -!ltnNge. Qed.

Lemma leq_eqVlt : forall m n, (m <= n) = (m == n) || (m < n).
Proof. elim=> [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma ltn_neqAle : forall m n, (m < n) = (m != n) && (m <= n).
Proof. elim=> [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma leq_trans : forall n m p, m <= n -> n <= p -> m <= p.
Proof. by elim=> [|i IHn] [|m] [|p] //; exact: IHn m p. Qed.

Lemma leq_ltn_trans : forall n m p, m <= n -> n < p -> m < p.
Proof. move=> n m p Hmn; exact: leq_trans. Qed.

Lemma ltnW : forall m n, m < n -> m <= n.
Proof. move=> m n; exact: leq_trans. Qed.
Hint Resolve ltnW.

Lemma leqW : forall m n, m <= n -> m <= n.+1.
Proof. move=> *; exact: ltnW. Qed.

Lemma ltn_trans : forall n m p, m < n -> n < p -> m < p.
Proof. move=> n m p Hmn; move/ltnW; exact: leq_trans. Qed.

Lemma leq_total : forall m n, (m <= n) || (m >= n).
Proof. by move=> m n; rewrite leq_eqVlt orbC orbCA ltnNge orbN orbT. Qed.

(* Link to the legacy comparison predicates. *)

Lemma leP : forall m n, reflect (m <= n)%coq_nat (m <= n).
Proof.
move=> m n; apply: (iffP idP); last by elim: n / => // n _; move/leq_trans->.
elim: n => [|n IHn]; first by case m.
by rewrite leq_eqVlt ltnS; case/predU1P=> [<- //|]; move/IHn; right.
Qed.

Implicit Arguments leP [m n].
Prenex Implicits leP.

Lemma le_irrelevance : forall m n lemn1 lemn2,
  lemn1 = lemn2 :> (m <= n)%coq_nat.
Proof.
move=> m n; elim: {n}n.+1 {-1}n (erefl n.+1) => // n IHn _ [<-] lemn1 lemn2.
pose def_n2 := erefl n; transitivity (eq_ind _ _ lemn2 _ def_n2) => //.
case def_n1: {1 4 5 7}n / lemn1 lemn2 def_n2 => [|n1 lemn1] [|n2 lemn2] def_n2.
- by rewrite (eq_axiomK def_n2).
- by move/leP: (lemn2); rewrite -{1}def_n2 ltnn.
- by move/leP: (lemn1); rewrite {1}def_n2 ltnn.
case: def_n2 (def_n2) lemn2 => ->{n2} def_n2 lemn2.
rewrite (eq_axiomK def_n2) /=; congr le_S; exact: IHn.
Qed.

Lemma ltP : forall m n, reflect (m < n)%coq_nat (m < n).
Proof. move=> *; exact leP. Qed.

Implicit Arguments ltP [m n].
Prenex Implicits ltP.

Lemma lt_irrelevance : forall m n ltmn1 ltmn2,
  ltmn1 = ltmn2 :> (m < n)%coq_nat.
Proof. move=> m; exact: le_irrelevance m.+1. Qed.

(* Comparison predicates. *)

CoInductive leq_xor_gtn (m n : nat) : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Lemma leqP : forall m n, leq_xor_gtn m n (m <= n) (n < m).
Proof.
move=> m n; rewrite ltnNge; case Hmn: (m <= n); constructor; auto.
by rewrite ltnNge Hmn.
Qed.

CoInductive ltn_xor_geq (m n : nat) : bool -> bool -> Set :=
  | LtnNotGeq of m < n  : ltn_xor_geq m n false true
  | GeqNotLtn of n <= m : ltn_xor_geq m n true false.

Lemma ltnP : forall m n, ltn_xor_geq m n (n <= m) (m < n).
Proof. by move=> m n; rewrite -(ltnS n); case (leqP m.+1 n); constructor. Qed.

CoInductive eqn0_xor_pos (n : nat) : bool -> bool -> Set :=
  | Eq0NotPos of n = 0 : eqn0_xor_pos n true false
  | PosNotEq0 of n > 0 : eqn0_xor_pos n false true.

Lemma posnP : forall n, eqn0_xor_pos n (n == 0) (0 < n).
Proof. by case; constructor. Qed.

CoInductive compare_nat (m n : nat) : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n true false false
  | CompareNatGt of m > n : compare_nat m n false true false
  | CompareNatEq of m = n : compare_nat m n false false true.

Lemma ltngtP : forall m n, compare_nat m n (m < n) (n < m) (m == n).
Proof.
move=> m n; rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP => Hm; first move/eqnP; constructor.
Qed.

(* Monotonicity lemmas *)

Definition monotone f := forall m n, (f m <= f n) = (m <= n).

Lemma leq_add2l : forall p m n, (p + m <= p + n) = (m <= n).
Proof. by move=> p *; elim p. Qed.

Lemma ltn_add2l : forall p m n, (p + m < p + n) = (m < n).
Proof. move=> *; rewrite -addnS; exact: leq_add2l. Qed.

Lemma leq_add2r : forall p m n, (m + p <= n + p) = (m <= n).
Proof. move=> p *; rewrite -!(addnC p); apply leq_add2l. Qed.

Lemma ltn_add2r : forall p m n, (m + p < n + p) = (m < n).
Proof. move=> *; exact: leq_add2r _.+1 _. Qed.

Lemma leq_add : forall m1 m2 n1 n2,
  m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2.
Proof.
move=> m1 m2 n1 n2 Hm Hn.
by apply (@leq_trans (m1 + n2)); rewrite ?leq_add2l ?leq_add2r.
Qed.

Lemma leq_addr : forall m n, n <= n + m.
Proof. by move=> m n; rewrite -{1}[n]addn0 leq_add2l. Qed.

Lemma leq_addl : forall m n, n <= m + n.
Proof. move=> *; rewrite addnC; apply leq_addr. Qed.

Lemma ltn_addr : forall m n p, m < n -> m < n + p.
Proof. move=> m n p; move/leq_trans=> -> //; exact: leq_addr. Qed.

Lemma ltn_addl : forall m n p, m < n -> m < p + n.
Proof. move=> m n p; move/leq_trans=> -> //; exact: leq_addl. Qed.

Lemma ltn_0add : forall m n, (0 < m + n) = (0 < m) || (0 < n).
Proof. by move=> m n; rewrite !lt0n -negb_andb eqn_add0. Qed.

Lemma ltn_0sub : forall m n, (0 < n - m) = (m < n).
Proof. elim=> [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma eqn_sub0 : forall m n, (m - n == 0) = (m <= n).
Proof. by []. Qed.

Lemma leq_sub_add : forall m n p, (m - n <= p) = (m <= n + p).
Proof. by move=> *; rewrite /leq subn_sub. Qed.

Lemma leq_subr : forall m n, n - m <= n.
Proof. by move=> *; rewrite leq_sub_add leq_addl. Qed.

Lemma subnK : forall m n, m <= n -> m + (n - m) = n.
Proof. by elim=> [|m IHm] [|n] // Hmn; congr _.+1; apply: IHm. Qed.

Lemma addn_subA : forall m n p, p <= n -> m + (n - p) = m + n - p.
Proof. by move=> m n p le_pn; rewrite -{2}(subnK le_pn) addnCA addKn. Qed.

Lemma subn_subA : forall m n p, p <= n -> m - (n - p) = m + p - n.
Proof. by move=> m n p le_pn; rewrite -{2}(subnK le_pn) addnC subn_add2l. Qed.

Lemma subKn : forall m n, m <= n -> n - (n - m) = m.
Proof. by move=> *; rewrite subn_subA // addKn. Qed.

Lemma leq_subS : forall m n, m <= n -> n.+1 - m = (n - m).+1.
Proof. by move => *; rewrite -add1n -addn_subA. Qed.

Lemma ltn_subS : forall m n, m < n -> n - m = (n - m.+1).+1.
Proof. move=> m; exact: leq_subS m.+1. Qed.

Lemma leq_sub2r : forall p m n, m <= n -> m - p <= n - p.
Proof.
move=> p m n Hmn; rewrite leq_sub_add; apply: (leq_trans Hmn).
by rewrite -leq_sub_add leqnn.
Qed.

Lemma leq_sub2l : forall p m n, m <= n -> p - n <= p - m.
Proof.
move=> p m n; rewrite -(leq_add2r (p - m)) leq_sub_add.
by apply: leq_trans; rewrite -leq_sub_add leqnn.
Qed.

Lemma leq_sub2 :  forall m1 m2 n1 n2,
  m1 <= m2 -> n2 <= n1 -> m1 - n1 <= m2 - n2.
Proof.
move=> m1 m2 n1 n2 Hm Hn; exact: leq_trans (leq_sub2l _ Hn) (leq_sub2r _ Hm).
Qed.

Lemma ltn_sub2r : forall p m n, p < n -> m < n -> m - p < n - p.
Proof. move=> p m n; move/ltn_subS->; exact: (@leq_sub2r p.+1). Qed.

Lemma ltn_sub2l : forall p m n, m < p -> m < n -> p - n < p - m.
Proof. move=> p m n; move/ltn_subS->; exact: leq_sub2l. Qed.

Lemma ltn_add_sub : forall m n p, (m + n < p) = (n < p - m).
Proof. by move=> m n p; rewrite !ltnNge leq_sub_add. Qed.

(* Elimination of the common idiom for structurally decreasing compare and *)
(* subtract. *)

Lemma subn_if_gt : forall T m n F (E : T),
  (if m.+1 - n is m'.+1 then F m' else E) = (if n <= m then F (m - n) else E).
Proof.
move=> m n F E; case: leqP => [le_nm |]; last by move/eqnP->.
by rewrite -{1}(subnK le_nm) -addnS addKn.
Qed.

(* Max and min *)

Definition maxn (m n : nat) := if (m < n) then n else m.

Definition minn (m n : nat) := if (m < n) then m else n.

Lemma max0n : left_unit 0 maxn.  Proof. by case. Qed.
Lemma maxn0 : right_unit 0 maxn. Proof. by []. Qed.

Lemma maxnC : commutative maxn.
Proof. by move=> m n; rewrite /maxn; case ltngtP. Qed.

Lemma add_sub_maxn : forall m n, m + (n - m) = maxn m n.
Proof.
move=> m n; rewrite /maxn; case: leqP; last by move/ltnW; move/subnK.
by move/eqnP->; rewrite addn0.
Qed.

Lemma maxnAC : right_commutative maxn.
Proof.
by move=> *; rewrite -!add_sub_maxn -!addnA -!subn_sub !add_sub_maxn maxnC.
Qed.

Lemma maxnA : associative maxn.
Proof. by move=> m n p; rewrite !(maxnC m) maxnAC. Qed.

Lemma maxnCA : left_commutative maxn.
Proof. by move=> m n p; rewrite !maxnA (maxnC m). Qed.

Lemma eqn_maxr : forall m n, (maxn m n == n) = (m <= n).
Proof. by move=> m n; rewrite maxnC -{2}[n]addn0 -add_sub_maxn eqn_addl. Qed.

Lemma eqn_maxl : forall m n, (maxn m n == m) = (m >= n).
Proof. by move=> m n; rewrite -{2}[m]addn0 -add_sub_maxn eqn_addl. Qed.

Lemma maxnn : idempotent maxn.
Proof. by move=> n; apply/eqP; rewrite eqn_maxl. Qed.

Lemma leq_maxr : forall m n1 n2, (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
move=> m n1 n2; wlog le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => ?; last rewrite maxnC orbC; auto.
rewrite /maxn ltnNge le_n21 /=; case: leqP => // lt_m_n1.
by rewrite leqNgt (leq_trans _ lt_m_n1).
Qed.

Lemma leq_maxl : forall m n1 n2, (maxn n1 n2 <= m) = (n1 <= m) && (n2 <= m).
Proof. by move=> m n1 n2; rewrite leqNgt leq_maxr negb_or -!leqNgt. Qed.

Lemma addn_maxl : left_distributive addn maxn.
Proof. by move=> m1 m2 n; rewrite -!add_sub_maxn subn_add2r addnAC. Qed.

Lemma addn_maxr : right_distributive addn maxn.
Proof. by move=> m n1 n2; rewrite !(addnC m) addn_maxl. Qed.

Lemma min0n : left_zero 0 minn. Proof. by case. Qed.
Lemma minn0 : right_zero 0 minn. Proof. by []. Qed.

Lemma minnC : commutative minn.
Proof. by move=> m n; rewrite /minn; case ltngtP. Qed.

Lemma addn_min_max : forall m n, minn m n + maxn m n = m + n.
Proof.
rewrite /minn /maxn => m n; case: ltngtP => // [_|->] //; exact: addnC.
Qed.

Remark minn_to_maxn : forall m n, minn m n = m + n - maxn m n.
Proof. by move=> *; rewrite -addn_min_max addnK. Qed.

Lemma sub_sub_minn : forall m n, m - (m - n) = minn m n.
Proof.
by move=> m n; rewrite minnC minn_to_maxn -add_sub_maxn subn_add2l.
Qed.

Lemma minnCA : left_commutative minn.
Proof.
move=> m1 m2 m3; rewrite !(minn_to_maxn _ (minn _ _)).
rewrite -(subn_add2r (maxn m2 m3)) -(subn_add2r (maxn m1 m3) (m2 + _)) -!addnA.
by rewrite !addn_maxl !addn_min_max !addn_maxr addnCA maxnAC (addnC m2 m1).
Qed.

Lemma minnA : associative minn.
Proof. by move=> m1 m2 m3; rewrite (minnC m2) minnCA minnC. Qed.

Lemma minnAC : right_commutative minn.
Proof. by move=> m1 m2 m3; rewrite minnC minnCA minnA. Qed.

Lemma eqn_minr : forall m n, (minn m n == n) = (n <= m).
Proof.
move=> m n; rewrite -(eqn_addr m) eq_sym addnC -addn_min_max eqn_addl.
exact: eqn_maxl.
Qed.

Lemma eqn_minl : forall m n, (minn m n == m) = (m <= n).
Proof.
by move=> m n; rewrite -(eqn_addr n) eq_sym -addn_min_max eqn_addl eqn_maxr.
Qed.

Lemma minnn : forall n, minn n n = n.
Proof. by move=> n; apply/eqP; rewrite eqn_minl. Qed.

Lemma leq_minr : forall m n1 n2, (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof.
move=> m n1 n2; wlog le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => ?; last rewrite minnC andbC; auto.
by rewrite /minn ltnNge le_n21 /= andbC; case: leqP => //; move/leq_trans->.
Qed.

Lemma leq_minl : forall m n1 n2, (minn n1 n2 <= m) = (n1 <= m) || (n2 <= m).
Proof. by move=> m n1 n2; rewrite leqNgt leq_minr negb_and -!leqNgt. Qed.

Lemma addn_minl : left_distributive addn minn.
Proof.
move=> m1 m2 n; rewrite !minn_to_maxn -addn_maxl addnA subn_add2r addnAC.
by rewrite -!(addnC n) addn_subA // -addn_min_max leq_addl.
Qed.

Lemma addn_minr : right_distributive addn minn.
Proof. by move=> m n1 n2; rewrite !(addnC m) addn_minl. Qed.

(* Quasi-cacellation (really, absorbtion) lemmas *)
Lemma maxnK : forall m n, minn (maxn m n) m = m.
Proof. by move=> m n; apply/eqP; rewrite eqn_minr leq_maxr leqnn. Qed.

Lemma maxKn : forall m n, minn n (maxn m n) = n.
Proof. by move=> m n; apply/eqP; rewrite eqn_minl leq_maxr leqnn orbT. Qed.

Lemma minnK : forall m n, maxn (minn m n) m = m.
Proof. by move=> m n; apply/eqP; rewrite eqn_maxr leq_minl leqnn. Qed.

Lemma minKn : forall m n, maxn n (minn m n) = n.
Proof. by move=> m n; apply/eqP; rewrite eqn_maxl leq_minl leqnn orbT. Qed.

(* Distributivity. *)

Lemma maxn_minl : left_distributive maxn minn.
Proof.
move=> m1 m2 n; wlog le_m21: m1 m2 / m2 <= m1.
  case/orP: (leq_total m2 m1) => ?; last rewrite minnC (minnC (maxn _ _));
     by auto.
apply/eqP; rewrite /minn ltnNge le_m21 eq_sym eqn_minr leq_maxr !leq_maxl.
rewrite le_m21 leqnn andbT; case: leqP => //; move/ltnW.
by move/(leq_trans le_m21)->.
Qed.

Lemma maxn_minr : right_distributive maxn minn.
Proof. by move=> m n1 n2; rewrite !(maxnC m) maxn_minl. Qed.

Lemma minn_maxl : left_distributive minn maxn.
Proof.
move=> m1 m2 n; rewrite maxn_minr !maxn_minl -minnA maxnn; congr minn.
apply/eqP; rewrite maxnC minnA -maxn_minl eq_sym eqn_minr leq_maxr.
by rewrite leqnn orbT.
Qed.

Lemma minn_maxr : right_distributive minn maxn.
Proof. by move=> m n1 n2; rewrite !(minnC m) minn_maxl. Qed.

(* Getting a concrete value from an abstract existence proof. *)

Section ExMinn.

Variable P : pred nat.
Hypothesis exP : exists n, P n.

Inductive acc_nat i : Prop := AccNat0 of P i | AccNatS of acc_nat i.+1.

Lemma find_ex_minn : {m | P m & forall n, P n -> n >= m}.
Proof.
have: forall n, P n -> n >= 0 by [].
have: acc_nat 0.
  case exP => n; rewrite -(addn0 n); elim: n 0 => [|n IHn] j; first by left.
  rewrite addSnnS; right; exact: IHn.
move: 0; fix 2 => m IHm m_lb; case Pm: (P m); first by exists m.
apply: find_ex_minn m.+1 _ _ => [|n Pn]; first by case: IHm; rewrite ?Pm.
by rewrite ltn_neqAle m_lb //; case: eqP Pm => // ->; case/idP.
Qed.

Definition ex_minn := s2val find_ex_minn.

Inductive ex_minn_spec : nat -> Type :=
  ExMinnSpec m of P m & (forall n, P n -> n >= m) : ex_minn_spec m.

Lemma ex_minnP : ex_minn_spec ex_minn.
Proof. by rewrite /ex_minn; case: find_ex_minn. Qed.

End ExMinn.

Lemma eq_ex_minn : forall P Q exP exQ,
  P =1 Q -> @ex_minn P exP = @ex_minn Q exQ.
Proof.
move=> P Q exP exQ eqPQ.
case: ex_minnP => m1 Pm1 m1_lb; case: ex_minnP => m2 Pm2 m2_lb.
by apply/eqP; rewrite eqn_leq m1_lb (m2_lb, eqPQ) // -eqPQ.
Qed.

(* Multiplication. *)

Definition muln_rec := mult.
Notation "m * n" := (muln_rec m n) : nat_rec_scope.

Definition muln := nosimpl muln_rec.
Notation "m * n" := (muln m n) : nat_scope.

Lemma multE : mult = muln.     Proof. by []. Qed.
Lemma mulnE : muln = muln_rec. Proof. by []. Qed.

Lemma mul0n : left_zero 0 muln. Proof. by []. Qed.
Lemma muln0 : right_zero 0 muln. Proof. by elim. Qed.
Lemma mul1n : left_unit 1 muln. Proof. exact: addn0. Qed.
Lemma mulSn : forall m n, m.+1 * n = n + m * n. Proof. by []. Qed.
Lemma mulSnr : forall m n, m.+1 * n = m * n + n.
Proof. by move=> *; exact: addnC. Qed.
Lemma mulnS : forall m n, m * n.+1 = m + m * n.
Proof. by move=> m n; elim: m => // m; rewrite !mulSn !addSn addnCA => ->. Qed.
Lemma mulnSr : forall m n, m * n.+1 = m * n + m.
Proof. by move=> m n; rewrite addnC mulnS. Qed.

Lemma muln1 : right_unit 1 muln.
Proof. by move=> n; rewrite mulnSr muln0. Qed.

Lemma mulnC : commutative muln.
Proof.
by move=> m n; elim: m => [|m]; rewrite (muln0, mulnS) // mulSn => ->.
Qed.

Lemma muln_addl : left_distributive muln addn.
Proof. by move=> m1 m2 n; elim: m1 => //= m1 IHm; rewrite -addnA -IHm. Qed.

Lemma muln_addr : right_distributive muln addn.
Proof. by move=> m *; rewrite !(mulnC m) muln_addl. Qed.

Lemma muln_subl : left_distributive muln subn.
Proof.
move=> m n [|p]; first by rewrite !muln0.
by elim: m n => // [m IHm] [|n] //; rewrite mulSn subn_add2l -IHm.
Qed.

Lemma muln_subr : right_distributive muln subn.
Proof. by move=> m n p; rewrite !(mulnC m) muln_subl. Qed.

Lemma mulnA : associative muln.
Proof. by move=> m n p; elim: m => //= m; rewrite mulSn muln_addl => ->. Qed.

Lemma mulnCA : left_commutative muln.
Proof. by move=> m *; rewrite !mulnA (mulnC m). Qed.

Lemma mulnAC : right_commutative muln.
Proof. by move=> m n p; rewrite -!mulnA (mulnC n). Qed.

Lemma eqn_mul0 : forall m n, (m * n == 0) = (m == 0) || (n == 0).
Proof. by case=> // m [|n] //=; rewrite muln0. Qed.

Lemma eqn_mul1 : forall m n, (m * n == 1) = (m == 1) && (n == 1).
Proof. by case=> [|[|m]] [|[|n]] //; rewrite muln0. Qed.

Lemma ltn_0mul : forall m n, (0 < m * n) = (0 < m) && (0 < n).
Proof. by case=> // m [|n] //=; rewrite muln0. Qed.

Lemma leq_pmull : forall m n, n > 0 -> m <= n * m.
Proof. by move=> m [|n] // _; exact: leq_addr. Qed.

Lemma leq_pmulr : forall m n, n > 0 -> m <= m * n.
Proof. by move=> m n n_pos; rewrite mulnC leq_pmull. Qed.

Lemma leq_mul2l : forall m n1 n2, (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. by move=> *; rewrite {1}/leq -muln_subr eqn_mul0. Qed.

Lemma leq_mul2r : forall m n1 n2, (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Proof. by move=> m *; rewrite -!(mulnC m) leq_mul2l. Qed.

Lemma leq_mul : forall m1 m2 n1 n2, m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Proof.
move=> m1 m2 n1 n2 le_mn1 le_mn2; apply (@leq_trans (m1 * n2)).
  by rewrite leq_mul2l le_mn2 orbT.
by rewrite leq_mul2r le_mn1 orbT.
Qed.

Lemma eqn_mul2l : forall m n1 n2, (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Proof. by move=> *; rewrite eqn_leq !leq_mul2l -demorgan3 -eqn_leq. Qed.

Lemma eqn_mul2r : forall m n1 n2, (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Proof. by move=> *; rewrite eqn_leq !leq_mul2r -orb_andr -eqn_leq. Qed.

Lemma leq_pmul2l : forall m n1 n2, 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Proof. by case=> // *; rewrite leq_mul2l. Qed.
Implicit Arguments leq_pmul2l [m n1 n2].

Lemma leq_pmul2r : forall m n1 n2, 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2).
Proof. by case=> // *; rewrite leq_mul2r. Qed.
Implicit Arguments leq_pmul2r [m n1 n2].

Lemma eqn_pmul2l : forall m n1 n2, 0 < m -> (m * n1 == m * n2) = (n1 == n2).
Proof. by case=> // *; rewrite eqn_mul2l. Qed.
Implicit Arguments eqn_pmul2l [m n1 n2].

Lemma eqn_pmul2r : forall m n1 n2, 0 < m -> (n1 * m == n2 * m) = (n1 == n2).
Proof. by case=> // *; rewrite eqn_mul2r. Qed.
Implicit Arguments eqn_pmul2r [m n1 n2].

Lemma ltn_mul2l : forall m n1 n2, (m * n1 < m * n2) = (0 < m) && (n1 < n2).
Proof. by move=> *; rewrite lt0n !ltnNge leq_mul2l negb_orb. Qed.

Lemma ltn_mul2r : forall m n1 n2, (n1 * m < n2 * m) = (0 < m) && (n1 < n2).
Proof. by move=> *; rewrite lt0n !ltnNge leq_mul2r negb_orb. Qed.

Lemma ltn_pmul2l : forall m n1 n2, 0 < m -> (m * n1 < m * n2) = (n1 < n2).
Proof. by case=> // *; rewrite ltn_mul2l. Qed.
Implicit Arguments ltn_pmul2l [m n1 n2].

Lemma ltn_pmul2r : forall m n1 n2, 0 < m -> (n1 * m < n2 * m) = (n1 < n2).
Proof. by case=> // *; rewrite ltn_mul2r. Qed.
Implicit Arguments ltn_pmul2r [m n1 n2].

Lemma ltn_Pmull : forall m n, 1 < n -> 0 < m -> m < n * m.
Proof. by move=> m n lt1n m_pos; rewrite -{1}[m]mul1n ltn_pmul2r. Qed.

Lemma ltn_Pmulr : forall m n, 1 < n -> 0 < m -> m < m * n.
Proof. by move=> m n lt1n m_pos; rewrite mulnC ltn_Pmull. Qed.

Lemma ltn_mul : forall m1 m2 n1 n2, m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
Proof.
move=> m1 m2 n1 n2 lt_mn1 lt_mn2; apply (@leq_ltn_trans (m1 * n2)).
  by rewrite leq_mul2l orbC ltnW.
by rewrite ltn_pmul2r // (leq_trans _ lt_mn2).
Qed.

Lemma maxn_mulr : right_distributive muln maxn.
Proof. by case=> // m n1 n2; rewrite /maxn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma maxn_mull : left_distributive muln maxn.
Proof. by move=> m1 m2 n; rewrite -!(mulnC n) maxn_mulr. Qed.

Lemma minn_mulr : right_distributive muln minn.
Proof. by case=> // m n1 n2; rewrite /minn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma minn_mull : left_distributive muln minn.
Proof. by move=> m1 m2 n; rewrite -!(mulnC n) minn_mulr. Qed.

(* Exponentiation. *)

Fixpoint expn_rec (m n : nat) {struct n} : nat :=
  if n is n'.+1 then m * (m ^ n')%Nrec else 1
where "m ^ n" := (expn_rec m n) : nat_rec_scope.

Definition expn := nosimpl expn_rec.
Notation "m ^ n" := (expn m n) : nat_scope.
Notation "m ^2" := (m ^ 2) (only parsing) : nat_scope.

Lemma expn0 : forall m, m ^ 0 = 1. Proof. by []. Qed.

Lemma expnS : forall m n, m ^ n.+1 = m * m ^ n. Proof. by []. Qed.

Lemma expnSr : forall m n, m ^ n.+1 = m ^ n * m.
Proof. by move=> *; rewrite mulnC. Qed.

Lemma exp0n : forall n, 0 < n -> 0 ^ n = 0.
Proof. by elim. Qed.

Lemma expn1 : forall m, m ^ 1 = m.
Proof. by move=> m; rewrite expnS expn0 muln1. Qed.

Lemma exp1n : forall n, 1 ^ n = 1.
Proof. by elim=> // n; rewrite expnS mul1n. Qed.

Lemma expn_add : forall m n1 n2, m ^ (n1 + n2) = m ^ n1 * m ^ n2.
Proof.
by move=> m n1 n2; elim: n1 => [|n1 IHn]; rewrite !(mul1n, expnS) // IHn mulnA.
Qed.

Lemma expn_mull : forall m1 m2 n, (m1 * m2) ^ n = m1 ^ n * m2 ^ n.
Proof.
by move=> m1 m2; elim=> // n IHn; rewrite !expnS IHn -!mulnA (mulnCA m2).
Qed.

Lemma expn_mulr : forall m n1 n2, m ^ (n1 * n2) = (m ^ n1) ^ n2.
Proof.
move=> m n1 n2; elim: n1 => [|n1 IHn]; first by rewrite exp1n.
by rewrite expn_add expn_mull IHn.
Qed.

Lemma ltn_0exp : forall m n, (0 < m ^ n) = (0 < m) || (n == 0).
Proof. by move=> [|m]; elim=> //= n IHn; rewrite ltn_0add IHn. Qed.

Lemma eqn_exp0 : forall m e, (m ^ e == 0) = (m == 0) && (e > 0).
Proof. by move=> *; rewrite !eqn0Ngt ltn_0exp negb_orb -lt0n. Qed.

Lemma ltn_expl : forall m n, 1 < m -> n < m ^ n.
Proof.
move=> m n Hm; elim: n => //= n; rewrite -(leq_pmul2l (ltnW Hm)).
by apply: leq_trans; rewrite -{1}(mul1n n.+1) ltn_pmul2r.
Qed.

Lemma leq_exp2l : forall m n1 n2, 1 < m -> (m ^ n1 <= m ^ n2) = (n1 <= n2).
Proof.
move=> m n1 n2 Hm; elim: n1 n2 => [|n1 IHn] [|n2] //; last 1 first.
- by rewrite ltnS leq_pmul2l // ltnW.
- by rewrite ltn_0mul ltn_0exp ltnW.
by rewrite leqNgt (leq_trans Hm) // -{1}(muln1 m) leq_pmul2l ?ltn_0exp ltnW.
Qed.

Lemma ltn_exp2l : forall m n1 n2, 1 < m -> (m ^ n1 < m ^ n2) = (n1 < n2).
Proof. by move=> *; rewrite !ltnNge leq_exp2l. Qed.

Lemma eqn_exp2l : forall m n1 n2, 1 < m -> (m ^ n1 == m ^ n2) = (n1 == n2).
Proof. by move=> *; rewrite !eqn_leq !leq_exp2l. Qed.

Lemma expn_injl : forall m, 1 < m -> injective (expn m).
Proof. by move=> * e1 e2; move/eqP; rewrite eqn_exp2l //; move/eqP. Qed.

Lemma leq_pexp2l : forall m n1 n2, 0 < m -> n1 <= n2 -> m ^ n1 <= m ^ n2.
Proof. by move=> [|[|m]] // *; [rewrite !exp1n | rewrite leq_exp2l]. Qed.

Lemma ltn_pexp2l : forall m n1 n2, 0 < m -> m ^ n1 < m ^ n2 -> n1 < n2.
Proof. by move=> [|[|m]] // n1 n2; [rewrite !exp1n | rewrite ltn_exp2l]. Qed.

Lemma ltn_exp2r : forall m n e, e > 0 -> (m ^ e < n ^ e) = (m < n).
Proof.
move=> m n e e_pos; apply/idP/idP=> [|ltmn].
  rewrite !ltnNge; apply: contra => lemn.
  elim: e {e_pos} => // e IHe; exact: leq_mul.
elim: e e_pos => // [[|e] IHe] _; first by rewrite !expn1.
by rewrite ltn_mul // IHe.
Qed.

Lemma leq_exp2r : forall m n e, e > 0 -> (m ^ e <= n ^ e) = (m <= n).
Proof. by move=> *; rewrite leqNgt ltn_exp2r // -leqNgt. Qed.

Lemma eqn_exp2r : forall m n e, e > 0 -> (m ^ e == n ^ e) = (m == n).
Proof. by move=> *; rewrite !eqn_leq !leq_exp2r. Qed.

Lemma expn_injr : forall e, e > 0 -> injective (expn^~ e).
Proof. by move=> * m n; move/eqP; rewrite eqn_exp2r //; move/eqP. Qed.

(* Factorial. *)

Fixpoint fact n := if n is n'.+1 then n * fact n' else 1.

(* A (canonical) structure for positive integers.             *)
(* Several types parametrized by integer posses an algebraic  *)
(* structure only for non-zero values of the parameter, e.g., *)
(* integers mod n, or square matrices of order n. The pos_nat *)
(* structure allows the type inference to automatically       *)
(* discharge this positivity condition. Note that pos_nat     *)
(* should not be used for normal arithmetic side condition:   *)
(* as Coq does not allow to declare new instances of a        *)
(* structure in the midst of a proof, it would be difficult   *)
(* to satisfy the conditions for arbitrary expressions.       *)

Record pos_nat : Type := PosNat { pos_nat_val :> nat; _ : pos_nat_val > 0 }.

Lemma pos_natP : forall n : pos_nat, n > 0. Proof. by case. Qed.
Hint Resolve pos_natP.

Canonical Structure pos_nat_subType := SubType pos_nat_val pos_nat_rect vrefl.
Canonical Structure pos_nat_eqType := [subEqType for pos_nat_val].

Canonical Structure S_pos_nat n := PosNat (ltn0Sn n).

Lemma addr_pos_natP : forall m (n : pos_nat), m + n > 0.
Proof. by move=> m n; rewrite ltn_0add pos_natP orbT. Qed.
Canonical Structure addr_pos_nat m n := PosNat (addr_pos_natP m n).

Lemma mul_pos_natP : forall (m n : pos_nat), m * n > 0.
Proof. by move=> m n; rewrite ltn_0mul !pos_natP. Qed.
Canonical Structure mul_pos_nat m n := PosNat (mul_pos_natP m n).

Lemma exp_pos_natP : forall (n : pos_nat) m, n ^ m > 0.
Proof. by move=> n m; rewrite ltn_0exp pos_natP. Qed.
Canonical Structure exp_pos_nat m n := PosNat (exp_pos_natP m n).

Lemma maxr_pos_natP : forall m (n : pos_nat), maxn m n > 0.
Proof. by move=> n m; rewrite leq_maxr pos_natP orbT. Qed.
Canonical Structure maxr_pos_nat m n := PosNat (maxr_pos_natP m n).

Lemma min_pos_natP : forall (m n : pos_nat), minn m n > 0.
Proof. by move=> n m; rewrite leq_minr !pos_natP. Qed.
Canonical Structure min_pos_nat m n := PosNat (min_pos_natP m n).

Lemma ltn_0fact : forall n, fact n > 0.
Proof. by elim=> //= n IHn; rewrite ltn_0mul. Qed.
Canonical Structure fact_pos_nat n := PosNat (ltn_0fact n).

Notation "[ 'pos_nat' 'of' n ]" :=
  (match [is n%N : nat <: pos_nat] as s return {type of PosNat for s} -> _ with
  | PosNat _ np => fun k => k np end
  (@PosNat n)) (at level 0, only parsing) : form_scope.

(* Parity and bits. *)

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Lemma leq_b1 : forall b : bool, b <= 1.
Proof. by case. Qed.

Lemma addn_negb : forall b : bool, ~~ b + b = 1.
Proof. by case. Qed.

Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.

Lemma odd_add : forall m n, odd (m + n) = odd m (+) odd n.
Proof.
by move=> m n; elim: m => [|m IHn] //=; rewrite -addTb IHn addbA addTb.
Qed.

Lemma odd_sub : forall m n, n <= m -> odd (m - n) = odd m (+) odd n.
Proof.
move=> m n le_nm; apply: (@canRL bool) (addKb _) _.
by rewrite -odd_add addnC subnK.
Qed.

Lemma odd_opp : forall i m, odd m = false -> i < m -> odd (m - i) = odd i.
Proof. by move=> i m oddm lti; rewrite (odd_sub (ltnW lti)) oddm. Qed.

Lemma odd_mul : forall m n, odd (m * n) = odd m && odd n.
Proof. by elim=> //= m' IHm n; rewrite odd_add -addTb andb_addl -IHm. Qed.

Lemma odd_exp : forall m n, odd (m ^ n) = (n == 0) || odd m.
Proof.
by move=> m; elim=> // n IHn; rewrite expnS odd_mul {}IHn orbC; case odd.
Qed.

(* Doubling. *)

Fixpoint double_rec n := if n is n'.+1 then n'.*2%Nrec.+2 else 0
where "n .*2" := (double_rec n) : nat_rec_scope.

Definition double := nosimpl double_rec.
Notation "n .*2" := (double n) : nat_scope.

Lemma doubleE : double = double_rec. Proof. by []. Qed.

Lemma double0 : 0.*2 = 0. Proof. by []. Qed.

Lemma doubleS : forall n, n.+1.*2 = n.*2.+2. Proof. by []. Qed.

Lemma addnn : forall n, n + n = n.*2.
Proof. by move=> n; apply: eqP; elim: n => *; rewrite ?addnS. Qed.

Lemma mul2n : forall m, 2 * m = m.*2.
Proof. by move=> *; rewrite mulSn mul1n addnn. Qed.

Lemma muln2 : forall m, m * 2 = m.*2.
Proof. by move=> *; rewrite mulnC mul2n. Qed.

Lemma double_add : forall m n, (m + n).*2 = m.*2 + n.*2.
Proof. by move=> m n; rewrite -!addnn -!addnA (addnCA n). Qed.

Lemma double_sub : forall m n, (m - n).*2 = m.*2 - n.*2.
Proof. elim=> [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma leq_double : forall m n, (m.*2 <= n.*2) = (m <= n).
Proof. by move=> m n; rewrite /leq -double_sub; case (m - n). Qed.

Lemma ltn_double : forall m n, (m.*2 < n.*2) = (m < n).
Proof. by move=> *; rewrite 2!ltnNge leq_double. Qed.

Lemma ltn_Sdouble : forall m n, (m.*2.+1 < n.*2) = (m < n).
Proof. by move=> *; rewrite -doubleS leq_double. Qed.

Lemma leq_Sdouble : forall m n, (m.*2 <= n.*2.+1) = (m <= n).
Proof. by move=> *; rewrite leqNgt ltn_Sdouble -leqNgt. Qed.

Lemma odd_double : forall n, odd n.*2 = false.
Proof. by move=> *; rewrite -addnn odd_add addbb. Qed.

Lemma ltn_0double : forall n, (0 < n.*2) = (0 < n).
Proof. by case. Qed.

Lemma eqn_double0 : forall n, (n.*2 == 0) = (n == 0).
Proof. by case. Qed.

Lemma double_mull : forall m n, (m * n).*2 = m.*2 * n.
Proof. by move=> *; rewrite -!mul2n mulnA. Qed.

Lemma double_mulr : forall m n, (m * n).*2 = m * n.*2.
Proof. by move=> *; rewrite -!muln2 mulnA. Qed.

(* Halving. *)

Fixpoint half (n : nat) : nat := if n is n'.+1 then uphalf n' else n
with   uphalf (n : nat) : nat := if n is n'.+1 then n'./2.+1 else n
where "n ./2" := (half n) : nat_scope.

Lemma doubleK : cancel double half.
Proof. by elim=> //= n ->. Qed.

Definition half_double := doubleK.
Definition double_inj := can_inj doubleK.

Lemma uphalf_double : forall n, uphalf n.*2 = n.
Proof. by elim=> //= n ->. Qed.

Lemma uphalf_half : forall n, uphalf n = odd n + n./2.
Proof. by elim=> //= n ->; rewrite addnA addn_negb. Qed.

Lemma odd_double_half : forall n, odd n + n./2.*2 = n.
Proof.
by elim=> [|n Hrec] //=; rewrite -{3}Hrec uphalf_half double_add; case (odd n).
Qed.

Lemma half_bit_double : forall n (b : bool), (b + n.*2)./2 = n.
Proof. by move=> n [|]; rewrite /= (half_double, uphalf_double). Qed.

Lemma half_add : forall m n, (m + n)./2 = (odd m && odd n) + (m./2 + n./2).
Proof.
move=> m n; rewrite -{1}[n]odd_double_half addnCA -{1}[m]odd_double_half.
rewrite -addnA -double_add.
by do 2!case: odd; rewrite /= ?add0n ?half_double ?uphalf_double.
Qed.

Lemma half_leq : forall m n, m <= n -> m./2 <= n./2.
Proof. by move=> m n; move/subnK <-; rewrite half_add addnCA leq_addr. Qed.

Lemma ltn_0half : forall n, (0 < n./2) = (1 < n).
Proof. by do 2?case. Qed.

(* Squares and square identities. *)

Lemma mulnn : forall m, m * m = m ^ 2.
Proof. by move=> *; rewrite !expnS muln1. Qed.

Lemma sqrn_add : forall m n, (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n).
Proof.
move=> m n; rewrite -!mulnn mul2n muln_addr !muln_addl (mulnC n) -!addnA.
by congr (_ + _); rewrite addnA addnn addnC.
Qed.

Lemma sqrn_sub : forall m n, n <= m ->
  (m - n) ^ 2 = m ^ 2 + n ^ 2 - 2 * (m * n).
Proof.
move=> m n; move/subnK=> def_m; rewrite -{2}def_m sqrn_add addnC 2!addnA addnn.
by rewrite -mul2n -addnA -!mulnn addnCA -2!muln_addr (mulnC n) def_m addnK.
Qed.

Lemma sqrn_add_sub : forall m n, n <= m ->
  (m + n) ^ 2 - 4 * (m * n) = (m - n) ^ 2.
Proof.
move=> m n le_nm; rewrite -[4]/(2 * 2) -mulnA mul2n -addnn -subn_sub.
by rewrite sqrn_add addnK sqrn_sub.
Qed.

Lemma subn_sqr : forall m n, m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
by move=> m n; rewrite muln_subl !muln_addr addnC (mulnC m) subn_add2l !mulnn.
Qed.

Lemma ltn_sqr : forall m n, (m ^ 2 < n ^ 2) = (m < n).
Proof. by move=> m n; rewrite ltn_exp2r. Qed.

Lemma leq_sqr : forall m n, (m ^ 2 <= n ^ 2) = (m <= n).
Proof. by move=> m n; rewrite leq_exp2r. Qed.

Lemma ltn_0sqr : forall n, (0 < n ^ 2) = (0 < n).
Proof. exact: (ltn_sqr 0). Qed.

Lemma eqn_sqr : forall m n, (m ^ 2 == n ^ 2) = (m == n).
Proof. by move=> *; rewrite eqn_exp2r. Qed.

Lemma sqrn_inj : injective (expn ^~ 2).
Proof. exact: expn_injr. Qed.

(* Almost strict inequality: an inequality that is strict unless some    *)
(* specific condition holds, such as the Cauchy-Schwartz or the AGM      *)
(* inequality (we only prove the order-2 AGM here; the general one       *)
(* requires sequences).                                                  *)
(*   We formalize the concept as a rewrite multirule, that can be used   *)
(* both to rewrite the non-strict inequality to true, and the equality   *)
(* to the specific condition (for strict inequalities use the ltn_neqAle *)
(* lemma); in addition, the conditional equality also coerces to a       *)
(* non-strict one.                                                       *)

Definition leqif m n c := ((m <= n) * ((m == n) = c))%type.

Notation "m <= n ?= 'iff' c" := (leqif m n c)
    (at level 70, n at next level,
  format "m '[hv'  <=  n '/'  ?=  'iff'  c ']'") : nat_scope.

Coercion leq_of_leqif m n c (H : m <= n ?= iff c) := H.1 : m <= n.

Lemma leqifP : forall m n c,
   reflect (m <= n ?= iff c) (if c then m == n else m < n).
Proof.
move=> m n c; rewrite ltn_neqAle.
apply: (iffP idP) => [|lte]; last by rewrite !lte; case c.
case c; [move/eqP-> | case/andP; move/negPf]; split=> //; exact: eqxx.
Qed.

Lemma leqif_refl : forall m c, reflect (m <= m ?= iff c) c.
Proof.
move=> m c; apply: (iffP idP) => [-> | <-]; last by rewrite eqxx.
by split; rewrite (leqnn, eqxx).
Qed.

Lemma leqif_trans : forall m1 m2 m3 c1 c2,
  m1 <= m2 ?= iff c1 -> m2 <= m3 ?= iff c2 -> m1 <= m3 ?= iff c1 && c2.
Proof.
move=> m1 m2 m3 c1 c2 ltm12 ltm23; apply/leqifP; rewrite -ltm12.
case eqm12: (m1 == m2).
  by rewrite (eqP eqm12) ltn_neqAle !ltm23 andbT; case c2.
by rewrite (@leq_trans m2) ?ltm23 // ltn_neqAle eqm12 ltm12.
Qed.

Lemma monotone_leqif : forall f, monotone f ->
  forall m n c, (f m <= f n ?= iff c) <-> (m <= n ?= iff c).
Proof.
move=> f f_mono m n c.
by split; move/leqifP=> hyp; apply/leqifP;
   rewrite !eqn_leq !ltnNge !f_mono in hyp *.
Qed.

Lemma leqif_geq : forall m n, m <= n -> m <= n ?= iff (m >= n).
Proof. by move=> m n lemn; split=> //; rewrite eqn_leq lemn. Qed.

Lemma leqif_eq : forall m n, m <= n -> m <= n ?= iff (m == n).
Proof. by []. Qed.

Lemma leqif_add : forall m1 n1 c1 m2 n2 c2,
    m1 <= n1 ?= iff c1 -> m2 <= n2 ?= iff c2 ->
  m1 + m2 <= n1 + n2 ?= iff c1 && c2.
Proof.
move=> m1 n1 c1 m2 n2 c2 le1; move/(monotone_leqif (leq_add2l n1)).
apply: leqif_trans; exact/(monotone_leqif (leq_add2r m2)).
Qed.

Lemma leqif_mul : forall m1 n1 c1 m2 n2 c2,
    m1 <= n1 ?= iff c1 -> m2 <= n2 ?= iff c2 ->
  m1 * m2 <= n1 * n2 ?= iff (n1 * n2 == 0) || (c1 && c2).
Proof.
move=> m1 n1 c1 m2 n2 c2 le1 le2; case: posnP => [n12_0 | ].
  rewrite n12_0; move/eqP: n12_0 {le1 le2}le1.1 le2.1; rewrite eqn_mul0.
  case/orP; move/eqP->; case: m1 m2 => [|m1] [|m2] // _ _;
   rewrite ?muln0; exact/leqif_refl.
rewrite ltn_0mul; move/andP=> [n1_pos n2_pos].
case: (posnP m2) => [m2_0 | m2_pos].
  apply/leqifP; rewrite -le2 andbC eq_sym eqn_leq leqNgt m2_0 muln0.
  by rewrite ltn_0mul n1_pos n2_pos.
move/leq_pmul2l: n1_pos; move/monotone_leqif=> Mn1; move/Mn1: le2 => {Mn1}.
move/leq_pmul2r: m2_pos; move/monotone_leqif=> Mm2; move/Mm2: le1 => {Mm2}.
exact: leqif_trans.
Qed.

Lemma nat_Cauchy : forall m n, 2 * (m * n) <= m ^ 2 + n ^ 2 ?= iff (m == n).
Proof.
move=> m n; wlog le_nm: m n / n <= m.
  by case: (leqP m n); auto; rewrite eq_sym addnC (mulnC m); auto.
apply/leqifP; case: ifP => [|ne_mn].
  by move/eqP->; rewrite mulnn addnn mul2n.
by rewrite -ltn_0sub -sqrn_sub // ltn_0sqr ltn_0sub ltn_neqAle eq_sym ne_mn.
Qed.

Lemma nat_AGM2 : forall m n, 4 * (m * n) <= (m + n) ^ 2 ?= iff (m == n).
Proof.
move=> m n; rewrite -[4]/(2 * 2) -mulnA mul2n -addnn sqrn_add.
apply/leqifP; rewrite ltn_add2r eqn_addr ltn_neqAle !nat_Cauchy.
by case: ifP => ->.
Qed.

(* Support for larger integers. The normal definitions of +, - and even  *)
(* IO are unsuitable for Peano integers larger than 2000 or so because   *)
(* they are not tail-recursive. We provide a workaround module, along    *)
(* with a rewrite multirule to change the tailrec operators to the       *)
(* normal ones. We handle IO via the NatBin module, but provide our      *)
(* own (more efficient) conversion functions.                            *)

Module NatTrec.

(*   Usage:                                             *)
(*     Import NatTrec.                                  *)
(*        in section definining functions, rebinds all  *)
(*        non-tail recursive operators.                 *)
(*     rewrite !trecE.                                  *)
(*        in the correctness proof, restores operators  *)

Fixpoint add (m n : nat) {struct m} :=
  if m is m'.+1 then m' + n.+1 else n
where "n + m" := (add n m) : nat_scope.

Fixpoint add_mul (m n s : nat) {struct m} :=
  if m is m'.+1 then add_mul m' n (n + s) else s.

Definition mul m n := if m is m'.+1 then add_mul m' n n else 0.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint mul_exp (m n p : nat) {struct n} :=
  if n is n'.+1 then mul_exp m n' (m * p) else p.

Definition exp m n := if n is n'.+1 then mul_exp m n' m else 1.

Notation "n ^ m" := (exp n m) : nat_scope.

Notation Local oddn := odd.
Fixpoint odd (n : nat) := if n is n'.+2 then odd n' else eqn n 1.

Notation Local doublen := double.
Definition double n := if n is n'.+1 then n' + n.+1 else 0.
Notation "n .*2" := (double n) : nat_scope.

Lemma addE : add =2 addn.
Proof. by elim=> //= n IHn m; rewrite IHn addSnnS. Qed.

Lemma doubleE : double =1 doublen.
Proof. by case=> // n; rewrite -addnn -addE. Qed.

Lemma add_mulE : forall n m s, add_mul n m s = addn (muln n m) s.
Proof. by elim=> //= n IHn m s; rewrite IHn addE addnCA addnA. Qed.

Lemma mulE : mul =2 muln.
Proof. by case=> //= n m; rewrite add_mulE addnC. Qed.

Lemma mul_expE : forall m n p, mul_exp m n p = muln (expn m n) p.
Proof.
by move=> m; elim=> [|n IHn] p; rewrite ?mul1n //= IHn mulE mulnCA mulnA.
Qed.

Lemma expE : exp =2 expn.
Proof. by move=> m [|n] //=; rewrite mul_expE mulnC. Qed.

Lemma oddE : odd =1 oddn.
Proof.
move=> n; rewrite -{1}[n]odd_double_half addnC.
by elim: n./2 => //=; case (oddn n).
Qed.

Definition trecE :=
  (addE, (doubleE, oddE), (mulE, add_mulE, (expE, mul_expE))).

End NatTrec.

Notation natTrecE := NatTrec.trecE.

Lemma eq_binP : reflect_eq Ndec.Neqb.
Proof.
move=> p q; apply: (iffP idP) => [|[<-]]; last by case: p => //; elim.
by case: q; case: p => //; elim=> [p IHp|p IHp|] [q|q|] //=; case/IHp=> ->.
Qed.

Canonical Structure bin_nat_eqMixin := EqMixin eq_binP.
Canonical Structure bin_nat_eqType := EqClass bin_nat_eqMixin.

Section NumberInterpretation.

Import BinPos.

Section Trec.

Import NatTrec.

Fixpoint nat_of_pos p0 :=
  match p0 with
  | xO p => (nat_of_pos p).*2
  | xI p => (nat_of_pos p).*2.+1
  | xH   => 1
  end.

End Trec.

Coercion Local nat_of_pos : positive >-> nat.

Coercion nat_of_bin b := if b is Npos p then p : nat else 0.

Fixpoint pos_of_nat (n0 m0 : nat) {struct n0} :=
  match n0, m0 with
  | n.+1, m.+2 => pos_of_nat n m
  | n.+1,    1 => xO (pos_of_nat n n)
  | n.+1,    0 => xI (pos_of_nat n n)
  |    0,    _ => xH
  end.

Definition bin_of_nat n0 :=
  if n0 is n.+1 then Npos (pos_of_nat n n) else 0%num.

Lemma bin_of_natK : cancel bin_of_nat nat_of_bin.
Proof.
have sub2nn: forall n, n.*2 - n = n by move=> n; rewrite -addnn addKn.
case=> //= n; rewrite -{3}[n]sub2nn.
by elim: n {2 4}n => // m IHm [|[|n]] //=; rewrite IHm // natTrecE sub2nn.
Qed.

Lemma nat_of_binK : cancel nat_of_bin bin_of_nat.
Proof.
case=> //=; elim=> //= p; case: (nat_of_pos p) => //= n [<-].
  by rewrite natTrecE !addnS {2}addnn; elim: {1 3}n.
by rewrite natTrecE addnS /= addnS {2}addnn; elim: {1 3}n.
Qed.

Lemma nat_of_succ_pos : forall p, Psucc p = p.+1 :> nat.
Proof. by elim=> //= p ->; rewrite !natTrecE. Qed.

Lemma nat_of_add_pos : forall p1 p2, (p1 + p2)%positive = p1 + p2 :> nat.
Proof.
move=> p q; apply: fst (Pplus_carry p q = (p + q).+1 :> nat) _.
elim: p q => [p IHp|p IHp|] [q|q|] //=; rewrite !natTrecE //;
  by rewrite ?IHp ?nat_of_succ_pos ?(doubleS, double_add, addn1, addnS).
Qed.

Lemma nat_of_add_bin : forall b1 b2, (b1 + b2)%num = b1 + b2 :> nat.
Proof. case=> [|p] [|q] //=; exact: nat_of_add_pos. Qed.

Lemma nat_of_mul_bin : forall b1 b2, (b1 * b2)%num = b1 * b2 :> nat.
Proof.
case=> [|p] [|q] //=; elim: p => [p IHp|p IHp|] /=;
  by rewrite ?(mul1n, nat_of_add_pos, mulSn) //= !natTrecE IHp double_mull.
Qed.


Lemma nat_of_exp_bin : forall n (b : N), n ^ (b : nat) = pow_N 1 muln n b.
Proof.
move=> n [|p] /=; first exact: expn0.
elim: p => /= [p <-|p <-|]; last exact: expn1;
  by rewrite natTrecE mulnn -expn_mulr muln2.
Qed.



End NumberInterpretation.

(* Big(ger) nat IO; usage:                              *)
(*     Num 1 072 399                                    *)
(*        to create large numbers for test cases        *)
(* Eval compute in [Num of some expression]             *)
(*        to display the resut of an expression that    *)
(*        returns a larger integer.                     *)

CoInductive number : Type := Num of N.

Coercion bin_of_number nn := let: Num b := nn in b.

Definition extend_number (nn : number) b := Num (nn * 1000 + b)%num.

Coercion extend_number : number >-> Funclass.

Lemma eq_numP : reflect_eq (fun nn1 nn2 : number => nn1 == nn2 :> N).
Proof. by move=> [b1] [b2]; apply: (iffP eqP) => [[]|] ->. Qed.

Canonical Structure number_eqType := mkEqType eq_numP.

Notation "[ 'Num' 'of' e ]" := (Num (bin_of_nat e))
  (at level 0, format "[ 'Num'  'of'  e ]") : nat_scope.

(* Interface to ring/ring_simplify tactics *)


Lemma nat_semi_ring : semi_ring_theory 0 1 addn muln (@eq _).
Proof. exact: mk_srt add0n addnC addnA mul1n mul0n mulnC mulnA muln_addl. Qed.

Lemma nat_semi_morph :
  semi_morph 0 1 addn muln (@eq _) 0%num 1%num Nplus Nmult pred1 nat_of_bin.
Proof.
by move: nat_of_add_bin nat_of_mul_bin; split=> //= m n; move/eqP->.
Qed.

Lemma nat_power_theory : power_theory 1 muln (@eq _) nat_of_bin expn.
Proof. split; exact: nat_of_exp_bin. Qed.

(* Interface to the ring tactic machinery. *)

Fixpoint pop_succn e := if e is e'.+1 then fun n => pop_succn e' n.+1 else id.

Ltac pop_succn e := eval lazy beta iota delta [pop_succn] in (pop_succn e 1).

Ltac nat_litteral e :=
  match pop_succn e with
  | ?n.+1 => constr: (bin_of_nat n)
  |     _ => NotConstant
  end.

Ltac succn_to_add :=
  match goal with
  | |- context G [?e.+1] =>
    let x := fresh "NatLit0" in
    match pop_succn e with
    | ?n.+1 => pose x := n.+1; let G' := context G [x] in change G'
    | _ ?e' ?n => pose x := n; let G' := context G [x + e'] in change G'
    end; succn_to_add; rewrite {}/x
			      | _ => idtac
  end.

Add Ring nat_ring_ssr : nat_semi_ring (morphism nat_semi_morph,
   constants [nat_litteral], preprocess [succn_to_add],
   power_tac nat_power_theory [nat_litteral]).

(* A congruence tactic, similar to the boolean one, along with an .+1/+  *)
(* normalization tactic.                                                 *)


Ltac nat_norm :=
  succn_to_add; rewrite ?add0n ?addn0 -?addnA ?(addSn, addnS, add0n, addn0).

Ltac nat_congr := first
 [ apply: (congr1 succn _)
 | apply: (congr1 predn _)
 | apply: (congr1 (addn _) _)
 | apply: (congr1 (subn _) _)
 | apply: (congr1 (addn^~ _) _)
 | match goal with |- (?X1 + ?X2 = ?X3) =>
     symmetry;
     rewrite -1?(addnC X1) -?(addnCA X1);
     apply: (congr1 (addn X1) _);
     symmetry
   end ].
