Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint orderedalg.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Module zintPOrdered.
Section zintPOrdered.
Implicit Types m n p : zint.

Definition posz n := if n is Posz _ then true else false.

Lemma posz0 : posz 0. Proof. done. Qed.

Lemma posz_add : forall m n, posz m -> posz n -> posz (m + n).
Proof. by move=> [] ? []. Qed.

Lemma posz_mul : forall m n, posz m -> posz n -> posz (m * n).
Proof. by move=> [] ? []. Qed.

Lemma posz_anti : forall n, posz n -> posz (- n) -> n = 0.
Proof. by move=> [[]|]. Qed.

End zintPOrdered.
End zintPOrdered.

Definition zint_POrderedMixin := PartialOrderMixin zintPOrdered.posz0
  zintPOrdered.posz_add zintPOrdered.posz_mul zintPOrdered.posz_anti.
Canonical Structure zint_poIdomainType := POIdomainType zint zint_POrderedMixin.

Lemma poszP : forall n : nat, posr n%:Z. Proof. by []. Qed.
Lemma poszN : forall n : nat, (posr (-(n.+1)%:Z)) = false. Proof. by []. Qed.
Definition poszE := (poszP, poszN).

Module zintOrdered.
Section zintOrdered.
Implicit Types m n p : zint.

Lemma lez_total : (@total zint) (<=%R).
Proof.
by move=> m n; rewrite !ler_pos -oppr_sub; case: (_ - _)=> // p; rewrite orbC.
Qed.

End zintOrdered.
End zintOrdered.

Canonical Structure zint_oIdomainType := OIdomainType zint zintOrdered.lez_total.

Section ZintNatOrder.

Implicit Types m n p : nat.

Lemma lez_nat : forall m n, (m <= n :> zint) = (m <= n)%N.
Proof.
move=> m n; case: leqP=> hmn; first by rewrite ler_pos subzn.
rewrite ler_pos -oppr_sub subzn 1?ltnW //=.
by move: hmn; rewrite -subn_gt0; case: (_ - _)%N.
Qed.

Lemma ltz_nat : forall m n, (m < n :> zint) = (m < n)%N.
Proof. by move=> m n; rewrite ltnNge ltrNge lez_nat. Qed.

Definition ltez_nat := (lez_nat, ltz_nat).

Lemma leNz_nat : forall m n, (- m%:Z <= n). Proof. by move=> [|?] []. Qed. 

Lemma ltNz_nat : forall m n, (- m%:Z < n) = (m != 0%N) || (n != 0%N).
Proof. by move=> [|?] []. Qed.

Definition lteNz_nat := (leNz_nat, ltNz_nat).

Lemma lezN_nat : forall m n, (m%:Z <= - n%:Z) = (m == 0%N) && (n == 0%N).
Proof. by move=> [|?] []. Qed. 

Lemma ltzN_nat : forall m n, (m%:Z < - n%:Z) = false.
Proof. by move=> [|?] []. Qed.

Lemma le0z_nat : forall n : nat, 0 <= n :> zint. Proof. by []. Qed.

Lemma lez0_nat : forall n : nat, n <= 0 :> zint = (n == 0%N :> nat).
Proof. by elim. Qed.

Definition ltezN_nat := (lezN_nat, ltzN_nat).
Definition ltez_natE := (ltez_nat, lteNz_nat, ltezN_nat, le0z_nat, lez0_nat).
End ZintNatOrder.

Section ZintOrdered.

Lemma ltz_leSz : forall x y : zint, (x < y) = (x + 1 <= y).
Proof.
move=> x y; rewrite -![_ _ y]subr_gte0 oppr_add addrA subr_ge0.
by case: (_ - _)=> n //; rewrite ?ltez_nat.
Qed.

Lemma sgrn : forall (n: nat), sgr n%:Z = (n != 0%N). Proof. by case. Qed.

Lemma sgrSn : forall n, sgr n.+1%:Z = 1. Proof. by case. Qed.

Lemma sgr_eq : forall (R R' : oIdomainType) (x : R) (y : R'), 
  (sgr x == sgr y) = ((x == 0) == (y == 0)) && ((0 < x) == (0 < y)).
Proof. 
move=> R R' x y; rewrite -?[0 < _]sgr_cp0 -?[x == 0]sgr_cp0 -?[y == 0]sgr_cp0.
by do 2!case: sgrP.
(* with ssr > 1.2 : by move=> R R' x y; do 2!case: sgrP. *)
 Qed.

End ZintOrdered.

Section ZintROrder.

Variable R : oIdomainType.
Implicit Types x y z : R.
Implicit Types m n p : zint.

Lemma sgr_id : forall (x : R), sgr (sgr x) = sgr x.
Proof. by move=> x; case: (sgrP x); rewrite ?(sgr0, sgr1, sgrN1). Qed.

Lemma posr_mul1rz : forall n, posr (n%:~R : R) = posr n.
Proof.
case=> n; rewrite ?NegzE ?(poszP, poszN) posr_ge0 ?mulrNz ?oppr_cp0.
  by rewrite ler0n.
by rewrite lerNgt ltr0Sn.
Qed.

Lemma mul1rz_ge0 : forall n, (0 <= n%:~R :> R) = (0 <= n).
Proof. by move=> n; rewrite !ler_pos !subr0 posr_mul1rz. Qed.

Lemma mul1rz_gt0 : forall n,  (0 < n%:~R :> R) = (0 < n).
Proof. by move=> n; rewrite !ltrNge -oppr_cp0 -mulrNz mul1rz_ge0 oppr_cp0. Qed.

Definition mul1rz_gte0 := (mul1rz_gt0, mul1rz_ge0).

Lemma mul1rz_le0 : forall n, (n%:~R <= 0 :> R) = (n <= 0).
Proof. by move=>n; rewrite !lerNgt mul1rz_gte0. Qed.

Lemma mul1rz_lt0 : forall n, (n%:~R < 0 :> R) = (n < 0).
Proof. by move=>n; rewrite !ltrNge mul1rz_gte0. Qed.

Definition mul1rz_lte0 := (mul1rz_lt0, mul1rz_le0).

Definition mul1rz_cp0 := (mul1rz_gte0, mul1rz_lte0, mul1rz_eq0).

Lemma ler_mul1rz : forall m n, (m%:~R <= n%:~R :> R) = (m <= n).
Proof. by move=> m n; rewrite -subr_ge0 -mulrz_subr mul1rz_ge0 subr_ge0. Qed.

Lemma ltr_mul1rz : forall m n, (m%:~R < n%:~R :> R) = (m < n).
Proof. by move=> m n; rewrite -subr_gt0 -mulrz_subr mul1rz_gt0 subr_gt0. Qed.

Definition lter_mul1rz := (ler_mul1rz, ltr_mul1rz).

Lemma sgr_mul1rz : forall m, sgr (m%:~R : R) = sgr m.
Proof. by move=> m; apply/eqP; rewrite sgr_eq !mul1rz_cp0 !eqxx. Qed.

Lemma absr_mul1rz : forall m, `|m%:~R| = `|m|%:~R :> R.
Proof. by move=> m; rewrite !absr_dec sgr_mul1rz mulzzr mulrzA. Qed.

Lemma sgr_mulz : forall  (x : zint) (y : R), sgr (y *~ x) = sgr y * sgr x.
Proof. by move=> x y; rewrite -mulrzr sgr_mul sgr_mul1rz. Qed.

Lemma absr_mulz : forall (x : zint) (y : R), `|y *~ x| = `|y| *~ `|x|.
Proof. by move=> x y; rewrite -mulrzl absr_mul absr_mul1rz mulrzl. Qed.

Lemma absr_sg : forall x : R,  `|sgr x| = (x != 0).
Proof. by move=> x; case: sgrP. Qed.

End ZintROrder.

Section Absz.

Implicit Types m n p : zint.

Definition absz m := match m with Posz p => p | Negz n => n.+1 end.

Lemma abszE : forall m : nat, absz m = m. Proof. by []. Qed.

Lemma absrz : forall m, `|m| = absz m. Proof. by case. Qed.

Lemma absz_eq0 : forall m, (absz m == 0%N) = (m == 0). Proof. by case. Qed.

End Absz.
