(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Export Arith.

Delimit Scope ssrnat_scope with N.
Open Scope ssrnat_scope.
Bind Scope ssrnat_scope with nat.
Arguments Scope S [ssrnat_scope].
Arguments Scope pred [ssrnat_scope].
Arguments Scope plus [ssrnat_scope ssrnat_scope].
Arguments Scope minus [ssrnat_scope ssrnat_scope].
Arguments Scope mult [ssrnat_scope ssrnat_scope].
Arguments Scope le [ssrnat_scope ssrnat_scope].
Arguments Scope lt [ssrnat_scope ssrnat_scope].
Arguments Scope ge [ssrnat_scope ssrnat_scope].
Arguments Scope gt [ssrnat_scope ssrnat_scope].
Arguments Scope iter [type_scope ssrnat_scope _ _].

Notation plus := plus.
Notation minus := minus.

(*   A "reflected" version of Arith, with an emphasis on boolean predicates *)
(* and rewriting; this includes a canonical dataSet for nat, as well as     *)
(* reflected predicates, leq and ltn for comparison (ltn m n) is actually a *)
(* syntactic definition for the expansion of (leq (S m) n)),  hidden by the *)
(* pretty-printer. This has one serious advantage : reduction happen in the *)
(* same way in leq and ltn, and one drawback: rewrites that match leq will  *)
(* also match ltn.                                                          *)
(*   Also leq and ltn are defined so that they do NOT simpl'ify; instead,   *)
(* rewrite rules are provided for cases where it is useful to do such       *)
(* simplifications (also, leq may be unfold'ed to get reduction to true or  *)
(* false, should that be needed). This makes the manipulation of assertions *)
(* much more stable, while still allowing conversion for trivial uses.      *)
(*   Stable versions of plus and minus, addn and subn, respectively, are    *)
(* provided for the same reasons, and the standard arithmetic lemmas are    *)
(* replicated.                                                              *)
(*   Also included are replacements for the div2 lemmas, that fit better    *)
(* with the rest of the theory.                                             *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Canonical comparison and DataSet for nat.                                *)

Fixpoint eqn (m n : nat) {struct m} : bool :=
  match m, n with
  | 0, 0 => true
  | S m', S n' => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : reflect_eq eqn.
Proof.
move=> n m; apply: (iffP idP) => [|<-]; last by elim n.
by elim: n m => [|n Hrec] [|m]; auto.
Qed.

Implicit Arguments eqnP [x y].
Prenex Implicits eqnP.

Canonical Structure nat_eqType := EqType (@eqnP).

Lemma eqnE : eqn = set1. Proof. done. Qed.

Lemma eqSS : forall m n, (S m == S n) = (m == n). Proof. done. Qed.

Lemma nat_irrelevance : forall (x y : nat) (E E' : x = y), E = E'.
Proof. exact: eq_irrelevance. Qed.

(* Protected addition, with a more systematic set of lemmas.                *)

Definition addn := nosimpl plus.

Lemma addnI : plus = addn. Proof. done. Qed.

Notation "x + y" := (addn x y) : ssrnat_scope.

Lemma add0n : forall n, 0 + n = n.
Proof.
done.
Qed.

Lemma addSn : forall m n, S m + n = S (m + n). Proof. done. Qed.
Lemma add1n : forall n, 1 + n = S n. Proof. done. Qed.

Lemma addn0 : forall n, n + 0 = n.
Proof. by move=> n; apply: eqP; elim: n. Qed.

Lemma addnS : forall m n, m + S n = S (m + n).
Proof. by move=> m n; elim: m. Qed.

Lemma addSnnS : forall m n, S m + n = m + S n.
Proof. move=> *; rewrite addnS; apply addSn. Qed.

Lemma addnCA : forall m n p, m + (n + p) = n + (m + p).
Proof. by move=> m n; elim: m => [|m Hrec] p; rewrite ?addSnnS -?addnS. Qed.

Lemma addnC : forall m n, m + n = n + m.
Proof. by move=> m n; rewrite -{1}[n]addn0 addnCA addn0. Qed.

Lemma addn1 : forall n, n + 1 = S n.
Proof. by move=> *; rewrite addnC. Qed.

Lemma addnA : forall m n p, m + (n + p) = m + n + p.
Proof. by move=> m n *; rewrite (addnC n) addnCA addnC. Qed.

Lemma eqn_add0 : forall m n, (m + n == 0) = (m == 0) && (n == 0).
Proof. by do 2 case. Qed.

Lemma eqn_addl : forall p m n, (p + m == p + n) = (m == n).
Proof. by move=> p *; elim p. Qed.

Lemma eqn_addr : forall p m n, (m + p == n + p) = (m == n).
Proof. by move=> p *; rewrite -!(addnC p) eqn_addl. Qed.

Lemma addn_injl : forall p, injective (addn p).
Proof. by move=> p m n Heq; apply: eqP; rewrite -(eqn_addl p) Heq set11. Qed.

Lemma addn_injr : forall p, injective (fun m => m + p).
Proof. move=> p m n; rewrite -!(addnC p); apply addn_injl. Qed.

(* Part of funs.v, delayed so that it uses the new definition of "+".  *)

Lemma iter_addn : forall n m A f (x : A), iter (n + m) f x = iter n f (iter m f x).
Proof. by move=> n m A f x; elim: n => [|n Hrec] //; congr f. Qed.

(* Protected substraction, and basic lemmas. Further properties depend on *)
(* ordering conditions.                                                   *)

Definition subn := nosimpl minus.
Notation "m - n" := (subn m n) : ssrnat_scope.

Lemma subnI : minus = subn. Proof. done. Qed.
Lemma sub0n : forall n, 0 - n = 0. Proof. done. Qed.
Lemma subn0 : forall n, n - 0 = n. Proof. by case. Qed.
Lemma subnn : forall n, n - n = 0. Proof. by elim. Qed.
Lemma subSS : forall n m, S m - S n = m - n. Proof. done. Qed.
Lemma subn1 : forall n, n - 1 = pred n. Proof. by case; try case. Qed.

Lemma subn_add2l : forall p m n, (p + m) - (p + n) = m - n.
Proof. by move=> p *; elim p. Qed.

Lemma subn_add2r : forall p m n, (m + p) - (n + p) = m - n.
Proof. by move=> p *; rewrite -!(addnC p) subn_add2l. Qed.

Lemma addKn : forall n, cancel (addn n) (fun m => m - n).
Proof. by move=> n ?; rewrite -{2}[n]addn0 subn_add2l subn0. Qed.

Lemma addnK : forall n, cancel (fun m => m + n) (fun m => m - n).
Proof. by move=> n m; rewrite (addnC m) addKn. Qed.

Lemma subSnn : forall n, (S n) - n = 1.
Proof. move=> n; exact (addnK n 1). Qed.

Lemma subn_sub : forall m n p, (n - m) - p = n - (m + p).
Proof. by move=> m n p; elim: m n => [|m Hrec] [|n]; try exact (Hrec n). Qed.

(* Integer ordering, and its interaction with the other operations.       *)

Definition leq m n := m - n == 0.

Notation "m <= n" := (leq m n) : ssrnat_scope.
Notation "m < n" := (S m <= n) : ssrnat_scope.
Notation "m >= n" := (n <= m) (only parsing) : ssrnat_scope.
Notation "m > n" := (n < m) (only parsing) : ssrnat_scope.

Lemma leP : forall m n, reflect (m <= n)%nat (m <= n).
Proof.
move=> m n; elim: m n => [|m Hrec] [|n]; try (constructor; auto with arith).
apply: (iffP (Hrec _)); auto with arith.
Qed.

Implicit Arguments leP [m n].
Prenex Implicits leP.

Lemma le_irrelevance : forall m n (H H' : (m <= n)%nat), H = H'.
Proof.
move=> m n; elim: {n}(S n) {-2}n (erefl (S n)) => [|n Hrec] _ // [->].
move=> H; rewrite -[H]/(eq_ind _ _ H _ (erefl n)).
case: {1 2 6}n / H (erefl n) => [|n' H] Dn H'.
  case: H' Dn => [|n'' H'] Dn; first by rewrite (eq_axiomK Dn).
  by case (lt_irrefl n''); rewrite /lt -Dn.
  case: H' Dn {Hrec}(Hrec _ Dn H) => [|n'' H'] Dn Hrec.
  by case: (lt_irrefl n'); rewrite /lt Dn.
by case: Dn (Dn) H' => <- Dn H'; rewrite (eq_axiomK Dn) (Hrec H').
Qed.

Lemma ltP : forall m n, reflect (m < n)%nat (m < n).
Proof. move=> *; exact leP. Qed.

Implicit Arguments ltP [m n].
Prenex Implicits ltP.

Lemma lt_irrelevance : forall m n (H H' : (m < n)%nat), H = H'.
Proof. move=> m; exact: le_irrelevance (S m). Qed.

Lemma leqNgt : forall m n, (m <= n) = ~~ (n < m).
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

Lemma ltnNge : forall m n, (m < n) = ~~ (n <= m).
Proof. by move=> *; rewrite leqNgt. Qed.

Lemma leqnn : forall n, n <= n.
Proof. by elim. Qed.
Hint Resolve leqnn.

Lemma eq_leq : forall m n, m = n -> m <= n.
Proof. by move=> m n <-; apply leqnn. Qed.

Lemma ltnn : forall n, n < n = false.
Proof. by move=> *; rewrite ltnNge leqnn. Qed.

Lemma leqnSn : forall n, n <= S n.
Proof. by elim. Qed.
Hint Resolve leqnSn.

Lemma ltnSn : forall n, n < S n.
Proof. done. Qed.

Lemma ltnS : forall m n, (m < S n) = (m <= n).
Proof. done. Qed.

Lemma leq0n : forall n, 0 <= n.
Proof. done. Qed.

Lemma ltn0Sn : forall n, 0 < S n.
Proof. done. Qed.

Lemma ltn0 : forall n, n < 0 = false.
Proof. done. Qed.

Lemma leq_pred : forall n, pred n <= n.
Proof. by case=> /=. Qed.

Lemma leqSpred : forall n, n <= S (pred n).
Proof. by case=> /=. Qed.

CoInductive leq_xor_gtn (m n : nat) : bool -> bool -> Set :=
  | LeqNotGtn : m <= n -> leq_xor_gtn m n true false
  | GtnNotLeq : n < m -> leq_xor_gtn m n false true.

Lemma leqP : forall m n, leq_xor_gtn m n (m <= n) (n < m).
Proof.
move=> m n; rewrite ltnNge; case Hmn: (m <= n); constructor; auto.
by rewrite ltnNge Hmn.
Qed.

CoInductive ltn_xor_geq (m n : nat) : bool -> bool -> Set :=
  | LtnNotGeq : m < n -> ltn_xor_geq m n true false
  | GeqNotLtn : n <= m -> ltn_xor_geq m n false true.

Lemma ltnP : forall m n, ltn_xor_geq m n (m < n) (n <= m).
Proof. by move=> m n; rewrite -(ltnS n); case (leqP (S m) n); constructor. Qed.

CoInductive eqn0_xor_pos (n : nat) : bool -> bool -> Set :=
  | Eq0NotPos : n = 0 -> eqn0_xor_pos n true false
  | PosNotEq0 : 0 < n -> eqn0_xor_pos n false true.

Lemma posnP : forall n, eqn0_xor_pos n (n == 0) (0 < n).
Proof. by case; constructor. Qed.

Lemma eqn_leq : forall m n, (m == n) = (m <= n) && (n <= m).
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

Lemma ltnSpred : forall n m, m < n -> S (pred n) = n.
Proof. by case. Qed.

Lemma leq_eqVlt : forall m n, (m <= n) = (m == n) || (m < n).
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

Lemma ltn_neqAle : forall m n, (m < n) = (m != n) && (m <= n).
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

CoInductive compare_nat (m n : nat) : bool -> bool -> bool -> Set :=
  | CompareNatLt : m < n -> compare_nat m n true false false
  | CompareNatGt : m > n -> compare_nat m n false true false
  | CompareNatEq : m = n -> compare_nat m n false false true.

Lemma ltngtP : forall m n, compare_nat m n (m < n) (n < m) (m == n).
Proof.
move=> m n; rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP => Hm; first move/eqnP; constructor.
Qed.

Lemma leq_trans : forall n m p, m <= n -> n <= p -> m <= p.
Proof. by elim=> [|m Hrec] [|n] [|p]; try exact (Hrec n p). Qed.

Lemma ltnW : forall m n, m < n -> m <= n.
Proof. move=> m n; exact: leq_trans. Qed.
Hint Resolve ltnW.

Lemma leqW : forall m n, m <= n -> m <= S n.
Proof. auto. Qed.

Lemma ltn_trans : forall n m p, m < n -> n < p -> m < p.
Proof. move=> n m p Hmn; apply: leq_trans; auto. Qed.

Lemma leq_add2l : forall p m n, (p + m <= p + n) = (m <= n).
Proof. by move=> p *; elim p. Qed.

Lemma ltn_add2l : forall p m n, (p + m < p + n) = (m < n).
Proof. move=> *; rewrite -addnS; exact: leq_add2l. Qed.

Lemma leq_add2r : forall p m n, (m + p <= n + p) = (m <= n).
Proof. move=> p *; rewrite -!(addnC p); apply leq_add2l. Qed.

Lemma ltn_add2r : forall p m n, (m + p < n + p) = (m < n).
Proof. move=> *; exact: leq_add2r (S _) _. Qed.

Lemma leq_add2 : forall m1 m2 n1 n2, m1 <= m2 -> n1 <= n2 -> m1 + n1 <= m2 + n2.
Proof.
move=> m1 m2 n1 n2 Hm Hn.
by apply (@leq_trans (m2 + n1)); rewrite ?leq_add2l ?leq_add2r.
Qed.

Lemma leq_addr : forall m n, n <= n + m.
Proof. by move=> m n; rewrite -{1}[n]addn0 leq_add2l. Qed.

Lemma leq_addl : forall m n, n <= m + n.
Proof. move=> *; rewrite addnC; apply leq_addr. Qed.

Lemma leqn0 : forall n, (n <= 0) = (n == 0).
Proof. by move=> *; rewrite eq_sym eqn_leq /=. Qed.

Lemma lt0n : forall n, (0 < n) = (n != 0).
Proof. by case. Qed.

Lemma lt0n_neq0 : forall n, 0 < n -> n != 0.
Proof. by case. Qed.

Lemma neq0_lt0n : forall n, (n == 0) = false -> 0 < n.
Proof. by case. Qed.
Hint Resolve lt0n_neq0 neq0_lt0n.

Lemma ltn_0add : forall m n, (0 < m + n) = (0 < m) || (0 < n).
Proof. by move=> m n; rewrite !lt0n -negb_andb eqn_add0. Qed.

Lemma ltn_0sub : forall m n, (0 < n - m) = (m < n).
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

Lemma eqn_sub0 : forall m n, (m - n == 0) = (m <= n).
Proof. done. Qed.

Lemma leq_subLR : forall m n p, (m - n <= p) = (m <= n + p).
Proof. by move=> *; rewrite /leq subn_sub. Qed.

Lemma leq_subr : forall m n, n - m <= n.
Proof. by move=> *; rewrite leq_subLR leq_addl. Qed.

Lemma subnKl : forall m n, m <= n -> m + (n - m) = n.
Proof. by elim=> [|m Hrec] [|n] // Hmn; congr S; apply: Hrec. Qed.

Lemma subnKr : forall m n, m <= n -> n - m + m = n.
Proof. by move=> *; rewrite addnC subnKl. Qed.

Lemma subKn : forall m n, m <= n -> n - (n - m) = m.
Proof. by move=> m n Hmn; rewrite -{1}(subnKl Hmn) addnK. Qed.

Lemma leq_subS : forall m n, m <= n -> S n - m = S (n - m).
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

Lemma ltn_subS : forall m n, m < n -> n - m = S (n - S m).
Proof. move=> m; exact: leq_subS (S m). Qed.

Lemma leq_sub2r : forall p m n, m <= n -> m - p <= n - p.
Proof.
by move=> p m n Hmn; rewrite leq_subLR; apply: leq_trans Hmn _; rewrite -leq_subLR.
Qed.

Lemma leq_subRL : forall m n p, m + n <= p -> m <= p - n.
Proof. move=> m n *; rewrite -(addnK n m); exact: leq_sub2r. Qed.

Lemma leq_sub2l : forall p m n, m <= n -> p - n <= p - m.
Proof.
move=> p m n; rewrite -(leq_add2r (p - m)) leq_subLR.
by apply: leq_trans; rewrite -leq_subLR.
Qed.

Lemma leq_sub2 :  forall m1 m2 n1 n2,
  m1 <= m2 -> n2 <= n1 -> m1 - n1 <= m2 - n2.
Proof.
move=> m1 m2 n1 n2 Hm Hn; exact: leq_trans (leq_sub2l _ Hn) (leq_sub2r _ Hm).
Qed.

Lemma ltn_sub2r : forall p m n, p < n -> m < n -> m - p < n - p.
Proof. move=> p m n; move/ltn_subS->; exact: (@leq_sub2r (S p)). Qed.

Lemma ltn_sub2l : forall p m n, m < p -> m < n -> p - n < p - m.
Proof. move=> p m n; move/ltn_subS->; exact: leq_sub2l. Qed.

(* Multiplication. *)

Definition muln m n := iter m (addn n) 0.
Notation "m * n" := (muln m n) : ssrnat_scope.

Lemma mulnI : mult =2 muln.
Proof. by elim=> // m Hrec n /=; congr addn. Qed.

Lemma mul0n : forall n, 0 * n = 0. Proof. done. Qed.
Lemma muln0 : forall n, n * 0 = 0. Proof. by elim. Qed.
Lemma mul1n : forall n, 1 * n = n. Proof. exact: addn0. Qed.
Lemma muln1 : forall n, n * 1 = n. Proof. by elim=> //= n ->. Qed.

Lemma mulnC : forall m n, m * n = n * m.
Proof.
move=> m n; elim: m => /= [|m ->]; elim: n => //= n <-; congr S; exact: addnCA.
Qed.

Lemma muln_addl : forall m1 m2 n, (m1 + m2) * n = m1 * n + m2 * n.
Proof. by move=> m1 m2 n; elim: m1 => //= m1 Hrec; rewrite -addnA -Hrec. Qed.

Lemma muln_addr : forall m n1 n2, m * (n1 + n2) = m * n1 + m * n2.
Proof. by move=> m *; rewrite !(mulnC m) muln_addl. Qed.

Lemma muln_subl : forall m n p, (m - n) * p = m * p - n * p.
Proof.
move=> m n [|p]; first by rewrite !muln0.
by elim: m n => // [m IHm] [|n] //=; rewrite subn_add2l -IHm.
Qed.

Lemma muln_subr : forall m n p, p * (m - n) = p * m - p * n.
Proof. by move=> m n p; rewrite !(mulnC p) muln_subl. Qed.

Lemma mulnA : forall m n p, m * (n * p) = m * n * p.
Proof. by move=> m n p; elim: m => //= m ->; rewrite muln_addl. Qed.

Lemma mulnCA : forall m n p, m * (n * p) = n * (m * p).
Proof. by move=> m *; rewrite !mulnA (mulnC m). Qed.

Lemma eqn_mul0 : forall m n, (m * n == 0) = (m == 0) || (n == 0).
Proof. by case=> // m [|n] //=; rewrite muln0. Qed.

Lemma eqn_mul1 : forall m n, (m * n == 1) = (m == 1) && (n == 1).
Proof. by case=> [|[|m]] [|[|n]] //; rewrite muln0. Qed.

Lemma ltn_0mul : forall m n, (0 < m * n) = (0 < m) && (0 < n).
Proof. by case=> // m [|n] //=; rewrite muln0. Qed.

Lemma leq_mul2l : forall m n1 n2, (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. by move=> *; rewrite {1}/leq -muln_subr eqn_mul0. Qed.

Lemma leq_mul2r : forall m n1 n2, (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Proof. by move=> m *; rewrite -!(mulnC m) leq_mul2l. Qed.

Lemma leq_mul : forall m1 m2 n1 n2, m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Proof.
move=> m1 m2 n1 n2 Hmn1 Hmn2; apply (@leq_trans (m1 * n2)).
  by rewrite leq_mul2l Hmn2 orbT.
by rewrite leq_mul2r Hmn1 orbT. 
Qed.

Lemma eqn_mul2l : forall m n1 n2, (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Proof. by move=> *; rewrite eqn_leq !leq_mul2l -demorgan3 -eqn_leq. Qed.

Lemma eqn_mul2r : forall m n1 n2, (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Proof. by move=> *; rewrite eqn_leq !leq_mul2r -demorgan3 -eqn_leq. Qed.

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

(* Parity and bits. *)

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Lemma addn_negb : forall b : bool, ~~ b + b = 1.
Proof. by case. Qed.

Fixpoint odd (n : nat) : bool :=
  if n is S n' then ~~ odd n' else false.

Lemma odd_addn : forall m n, odd (m + n) = odd m (+) odd n.
Proof.
move=> m n; elim: m => [|m Hrec] //=.
by rewrite -addTb addnI Hrec addbA addTb.
Qed.

Lemma odd_subn : forall m n, n <= m -> odd (m - n) = odd m (+) odd n.
Proof.
move=> m n Hnm; apply: (@canRL bool) (addKb _).
rewrite -odd_addn addnC; exact (congr1 odd (subnKl Hnm)).
Qed.

(* Doubling. *)

Fixpoint double_rec (n : nat) : nat :=
  if n is S n' then S (S (double_rec n')) else 0.

Definition double := nosimpl double_rec.

Lemma doubleI : double_rec = double. Proof. done. Qed.

Lemma double0 : double 0 = 0. Proof. done. Qed.

Lemma doubleS : forall n, double (S n) = S (S (double n)).
Proof. done. Qed.

Lemma double_addnn : forall n, double n = addn n n.
Proof. by move=> n; apply: eqP; elim: n => *; rewrite ?addnS. Qed.

Lemma double_mul2 : forall n, double n = 2 * n.
Proof. by move=> n; rewrite double_addnn /= addn0. Qed.

Lemma double_add : forall m n, double (m + n) = double m + double n.
Proof. by move=> m n; rewrite !double_addnn -!addnA (addnCA n). Qed.

Lemma double_sub : forall m n, double (m - n) = double m - double n.
Proof. by elim=> [|m Hrec] [|n]; try exact (Hrec n). Qed.

Lemma leq_double : forall m n, (double m <= double n) = (m <= n).
Proof. by move=> m n; rewrite /leq -double_sub; case (m - n). Qed.

Lemma ltn_double : forall m n, (double m < double n) = (m < n).
Proof. by move=> *; rewrite !ltnNge leq_double. Qed.

Lemma ltn_Sdouble : forall m n, (S (double m) < double n) = (m < n).
Proof. by move=> *; rewrite -doubleS leq_double. Qed.

Lemma leq_Sdouble : forall m n, (double m <= S (double n)) = (m <= n).
Proof. by move=> *; rewrite leqNgt ltn_Sdouble -leqNgt. Qed.

Lemma odd_double : forall n, odd (double n) = false.
Proof. by move=> *; rewrite double_addnn odd_addn addbb. Qed.

(* Halving. *)

Fixpoint half (n : nat) : nat := if n is S n' then uphalf n'   else 0
with   uphalf (n : nat) : nat := if n is S n' then S (half n') else 0.

Lemma half_double : forall n, half (double n) = n.
Proof. by elim=> [|n Hrec] //=; congr S. Qed.

Lemma uphalf_double : forall n, uphalf (double n) = n.
Proof. by elim=> [|n Hrec] //=; congr S. Qed.

Lemma uphalf_half : forall n, uphalf n = odd n + half n.
Proof. by elim=> [|n Hrec] //=; rewrite Hrec addnA addn_negb. Qed.

Lemma odd_double_half : forall n, odd n + double (half n) = n.
Proof.
by elim=> [|n Hrec] //=; rewrite -{3}Hrec uphalf_half double_add; case (odd n).
Qed.

Lemma half_bit_double : forall n (b : bool), half (b + double n) = n.
Proof. move=> n [|]; [ exact (uphalf_double n) | exact (half_double n) ]. Qed.

Lemma half_add : forall m n, half (m + n) = (odd m && odd n) + (half m + half n).
Proof.
move=> m n; rewrite -{1}[n]odd_double_half addnCA -{1}[m]odd_double_half.
rewrite -addnA -double_add.
by case (odd n); case (odd m); rewrite /= ?add0n ?half_double ?uphalf_double.
Qed.

Lemma half_leq : forall m n, m <= n -> half m <= half n.
Proof.
move=> m n; rewrite -{1}[m]odd_double_half -{1}[n]odd_double_half.
case (odd m); case (odd n); rewrite /addn /= ?add0n ?ltnS;
  by rewrite ?leq_double ?ltn_double ?leq_Sdouble; try apply: leqW.
Qed.

(* A congruence tactic, similar to the boolean one, along with an S/addn *)
(* normalization tactic.                                                 *)

Definition natNorm1 := 1.
Lemma addnNorm1 : forall n, S n = natNorm1 + n. Proof. done. Qed.

Ltac nat_norm :=
  rewrite ?add0n ?addn0;
   rewrite -/natNorm1 ?addnNorm1 -?addnA -?addnNorm1 /natNorm1 ?addnS ?addn0.

Ltac nat_congr := first
 [ apply: (congr1 S _)
 | apply: (congr1 pred _)
 | apply: (congr1 (addn _) _)
 | apply: (congr1 (subn _) _)
 | apply: (congr1 (fun n => n + _) _)
 | match goal with |- (addn ?X1 ?X2 = ?X3) =>
     symmetry;
     rewrite -1?(addnC X1) -?(addnCA X1);
     apply: (congr1 (addn X1) _);
     symmetry
   end ].

Unset Implicit Arguments.