Require Import ssreflect.
Require Import ssrbool.
Require Import ssrnat.
Require Import funs.
Require Import eqtype.
Require Import seq.

(**************************************************************************)
(* This files contains the definitions of:                                *)
(* -division: divn and modn compute the euclidian quotient and remainder  *)
(*            edivn m d performs the euclidian division of m by d+1       *)
(* -divisibility: dvdn d m <=> d divides m                                *)
(*                divisors m == the ascending divisors list of m if m > 0 *)
(*                gcdn m n == the GCD of m and n                          *)
(*                coprime m n <=> m and n are coprime                     *)
(* The bezout[lr] lemmas give the bezout coefficients.                    *)
(* -primality: prime p <=> p is prime                                     *)
(*             primes m == the list of prime divisors of m if m > 0       *)
(* -powers: expn m n == m ^ n                                             *)
(*          logn p m == the number of times p divides m                   *)
(*          p_part p m == p ^ (logn p m)                                  *)
(*  The main goal of this file is Gauss theorem and the Euclid theorem as *)
(* a direct corollary.                                                    *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Euclidian division *)

Fixpoint edivn_rec (m d q r : nat) {struct m} : nat * nat :=
  match m, r with
  | 0, _ => (q, d - r)
  | S m', 0 => edivn_rec m' d (S q) d
  | S m', S r' => edivn_rec m' d q r'
  end.

Definition edivn m d := edivn_rec m d 0 d.

CoInductive edivn_spec (m d : nat) : nat * nat -> Set :=
  EdivnSpec q r : m = q * S d + r -> r <= d -> edivn_spec m d (q, r).

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
move=> m d; have Dm: m = m + (d - d) + 0 * (S d) by rewrite subnn addn0.
rewrite {1}Dm {Dm} /edivn; elim: m 0 {1 4 8}d (leqnn d) => [|m IHm] q /=.
  by split; [rewrite addnC | rewrite leq_subr].
case=> [|r] /= Hr; last first.
  by rewrite addSnnS -(leq_subS Hr); apply: IHm; auto.
rewrite subn0 addSnnS -{1}(addn0 m) -{1}(subnn d) -addnA; exact: (IHm (S q)).
Qed.

Lemma edivn_eq : forall d q r, r <= d -> edivn (q * S d + r) d = (q, r).
Proof.
move=> d q r; case: edivnP => q' r'.
wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addn_injl->.
rewrite -(@leq_pmul2r (S d)) //=; move/leq_add2=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite -addnA Eqr addSn ltnNge addnC addnA leq_addr.
Qed.

Definition divn m d := if d is S d' then fst (edivn m d') else 0.
Definition modn m d := if d is S d' then snd (edivn m d') else m.

Lemma divn_eq : forall m d, m = divn m d * d + modn m d.
Proof. by move=> m [|d] //=; case edivnP. Qed.

Lemma div0n : forall d, divn 0 d = 0.
Proof. by case. Qed.

Lemma divn_small : forall m d, m < d -> divn m d = 0.
Proof. by move=> m [|d] //= Hm; rewrite -[m]/(0 * S d + m) edivn_eq. Qed.

Lemma divn_addl_mul : forall p m d, 0 < d -> divn (p * d + m) d = p + divn m d.
Proof.
move=> p m [|d] //= _; case: (edivnP m d) => [q r -> Hr] /=.
by rewrite addnA -muln_addl edivn_eq.
Qed.

Lemma divn_mull : forall m d, 0 < d -> divn (m * d) d = m.
Proof. by move=> m [|d] //= _; rewrite -[_ * _]addn0 edivn_eq. Qed.

Lemma divn_mulr : forall m d, 0 < d -> divn (d * m) d = m.
Proof. by move=> *; rewrite mulnC divn_mull. Qed.

Lemma divn1: forall m, divn m 1 = m.
Proof. by move=> m; rewrite -{1}[m]muln1 divn_mull. Qed.

Lemma divnn : forall d, divn d d = (0 < d).
Proof. by case=> // d; rewrite -{1}[S d]muln1 divn_mulr. Qed.

Lemma divn_pmul2l : forall p m d, p > 0 -> divn (p * m) (p * d) = divn m d.
Proof.
case=> // p m [|d] // _; first by rewrite muln0.
rewrite [divn m _]/=; case: edivnP => [q r -> Hr].
by rewrite muln_addr mulnCA divn_addl_mul // addnC divn_small // ltn_pmul2l.
Qed.
Implicit Arguments divn_pmul2l [p m d].

Lemma ltn_mod : forall m d, (modn m d < d) = (0 < d).
Proof.  by move=> m [|d] //=; case: edivnP. Qed.

Lemma leq_div : forall m d, (divn m d) * d <= m.
Proof. by move=> m d; rewrite {2}(divn_eq m d) leq_addr. Qed.

Lemma ltn_Sdiv : forall m d, 0 < d -> m < S (divn m d) * d.
Proof.
by move=> m d Hd /=; rewrite addnC {1}(divn_eq m d) -addnS leq_add2l ltn_mod.
Qed.

Lemma divn_lt : forall m d, 1 < d -> 0 < m -> divn m d < m.
Proof.
case=> // m [|[|d]] //= _ _; case: edivnP => [q r Dm Hr] /=.
rewrite -(@ltn_pmul2r (S (S d))) // (mulnC (S m)) /= addSn ltnS addnCA Dm -!addnA.
exact: leq_addr.
Qed.

Lemma mod0n : forall d, modn 0 d = 0.
Proof. case=> // d; exact: subnn. Qed.

Lemma modn_small : forall m d, m < d -> modn m d = m.
Proof. by move=> m [|d] //= Hm; rewrite [edivn _ _](@edivn_eq d 0 m). Qed.

Lemma modn_mod : forall m d, modn (modn m d) d = modn m d.
Proof. by move=> m [|d] //; apply: modn_small; rewrite ltn_mod. Qed.

Lemma modn_addl_mul : forall p m d, modn (p * d + m) d = modn m d.
Proof.
move=> p m d; case: d (divn_eq (p * d + m) d) => // d; first by rewrite muln0.
by rewrite {1}(divn_eq m (S d)) addnA -muln_addl divn_addl_mul //; move/addn_injl.
Qed.

Lemma modn_pmul2l : forall p m d, 0 < p -> modn (p * m) (p * d) = p * modn m d.
Proof.
move=> p m d Hp; move: (divn_eq (p * m) (p * d)).
by rewrite {1}(divn_eq m d) muln_addr divn_pmul2l // mulnCA; move/addn_injl.
Qed.
Implicit Arguments modn_pmul2l [p m d].

Lemma modnn : forall d, modn d d = 0.
Proof. by move=> d; move: (modn_addl_mul 1 0 d); rewrite /= !addn0 mod0n. Qed.

Lemma modn_add : forall n m d, modn (modn n d + modn m d) d = modn (n + m) d.
Proof.
move=> n m d; rewrite {2}(divn_eq n d) -addnA modn_addl_mul.
by rewrite {2}(divn_eq m d) addnCA modn_addl_mul.
Qed.

Lemma modn_mul : forall n m d, modn (modn n d * modn m d) d = modn (n * m) d.
Proof.
move=> n m d; rewrite {2}(divn_eq n d) muln_addl -mulnA mulnCA (mulnC d).
by rewrite {3}(divn_eq m d) muln_addr mulnA !modn_addl_mul.
Qed.

Lemma modn_mull : forall n d, modn (n * d) d = 0.
Proof. by move=> *; rewrite -modn_mul modnn muln0 mod0n. Qed.

Lemma modn1 : forall m, modn m 1 = 0.
Proof. by move=> m; rewrite -[m]muln1 modn_mull. Qed.

(** Definition of divisibility **)

Definition dvdn d m := modn m d == 0.

Lemma dvdn_n0: forall d, dvdn d 0.
Proof. by move=> n; rewrite /dvdn mod0n. Qed.

Lemma dvdnP: forall d m, reflect (exists k, m = k * d) (dvdn d m).
Proof.
move=> d m; apply: (iffP eqP) => [Hm | [k ->]]; last by rewrite modn_mull.
by exists (divn m d); rewrite {1}(divn_eq m d) Hm addn0.
Qed.
Implicit Arguments dvdnP [d m].
Prenex Implicits dvdnP.

Lemma dvdn0 : forall d, dvdn d 0.
Proof. by move=> d; rewrite /dvdn mod0n. Qed.

Lemma dvdn1 : forall d, dvdn d 1 = (d == 1).
Proof. by case=> [|[|n]] //; rewrite /dvdn modn_small. Qed.

Lemma dvd1n: forall m, dvdn 1 m.
Proof. by move=> m; rewrite /dvdn modn1. Qed.

Lemma dvdnn: forall m, dvdn m m.
Proof. by move=> m; rewrite /dvdn modnn. Qed.

Lemma dvdn_mull: forall d m n, dvdn d n -> dvdn d (m * n).
Proof. by move=> d m n; case/dvdnP=> n' ->; rewrite /dvdn mulnA modn_mull. Qed.

Lemma dvdn_mulr: forall d m n, dvdn d m -> dvdn d (m * n).
Proof. by move=> *; rewrite mulnC dvdn_mull. Qed.

Hint Resolve dvdn0 dvd1n dvdnn dvdn_mull dvdn_mulr.

Lemma dvdn_trans: forall n d m, dvdn d n -> dvdn n m -> dvdn d m.
Proof. move=> n d m Hn; move/dvdnP => [n1 ->]; auto. Qed.

Lemma dvdn_eq : forall d m, dvdn d m = (divn m d * d == m).
Proof.
move=> d m; apply/idP/eqP=> [Hm | <-]; auto.
by rewrite {2}(divn_eq m d) (eqnP Hm) addn0. 
Qed.

Lemma dvdn_leq : forall d m, 0 < m -> dvdn d m -> d <= m.
Proof.
by move=> d m Hm; case/dvdnP=> [[|k] Dm]; rewrite Dm //= leq_addr in Hm *.
Qed.

Lemma dvdn_lt : forall d m,
  1 < d -> 0 < m -> dvdn d m -> 0 < divn m d /\ divn m d < m.
Proof.
move=> d m Hd Hm; rewrite dvdn_eq; move/eqP=> Dm.
by split; last exact: divn_lt; rewrite -Dm ltn_0mul in Hm; case/andP: Hm.
Qed.

Lemma eqn_dvd : forall m n, (m == n) = dvdn m n && dvdn n m.
Proof.
case=> [|m] [|n] //; first by rewrite andbF.
apply/idP/andP; first by move/eqP->; auto.
rewrite eqn_leq => [[Hmn Hnm]]; apply/andP; have:= dvdn_leq; auto.
Qed.

Lemma dvdn_pmul2l : forall p d m, 0 < p -> dvdn (p * d) (p * m) = dvdn d m.
Proof. by case=> // p d m _; rewrite /dvdn modn_pmul2l // eqn_mul0. Qed.
Implicit Arguments dvdn_pmul2l [p m d].

Lemma dvdn_pmul2r : forall p d m, 0 < p -> dvdn (d * p) (m * p) = dvdn d m.
Proof. by move=> n d m Hn; rewrite -!(mulnC n) dvdn_pmul2l. Qed.
Implicit Arguments dvdn_pmul2r [p m d].

Lemma dvdn_addr : forall m d n, dvdn d m -> dvdn d (m + n) = dvdn d n.
Proof. by move=> n d m; move/dvdnP=> [k ->]; rewrite /dvdn modn_addl_mul. Qed.

Lemma dvdn_addl : forall n d m, dvdn d n -> dvdn d (m + n) = (dvdn d m).
Proof. by move=> n d m; rewrite addnC; exact: dvdn_addr. Qed.

Lemma dvdn_add : forall d m n, dvdn d m -> dvdn d n -> dvdn d (m + n).
Proof. by move=> n d m; move/dvdn_addr->. Qed.

Lemma dvdn_add_eq : forall d m n, dvdn d (m + n) -> dvdn d m = dvdn d n.
Proof. by move=> *; apply/idP/idP; [move/dvdn_addr <-| move/dvdn_addl <-]. Qed.

Lemma dvdn_subr : forall d m n, n <= m -> dvdn d m -> dvdn d (m - n) = dvdn d n.
Proof. by move=> *; apply dvdn_add_eq; rewrite addnC subnKl. Qed.

Lemma dvdn_subl : forall d m n, n <= m -> dvdn d n -> dvdn d (m - n) = dvdn d m.
Proof. by move=> d m n Hn; rewrite -{2}(subnKl Hn); move/dvdn_addr. Qed.

Lemma dvdn_sub : forall d m n, dvdn d m -> dvdn d n -> dvdn d (m - n).
Proof.
move=> d n m; case: (leqP m n) => Hm; first by move/dvdn_subr <-.
by rewrite (eqnP (ltnW Hm)) dvdn_n0.
Qed.

Hint Resolve dvdn_add dvdn_sub.

Definition divisors m := filter (fun x => dvdn x m) (iota 1 m).
Definition prime p := divisors p == Seq 1 p.
Definition primes m := filter prime (divisors m).

Lemma dvdn_divisors : forall d m, 0 < m -> dvdn d m = divisors m d.
Proof.
move=> [|d] m Hm; symmetry; rewrite /divisors mem_filter /setI.
  by rewrite ?dvdn_0n; case: m Hm.
case Hd: (dvdn _ m) => //=; rewrite mem_iota; exact: dvdn_leq Hd.
Qed.

Lemma uniq_divisors : forall m, uniq (divisors m).
Proof. move=> m; apply: uniq_filter; exact: uniq_iota. Qed.

Lemma divisor1: forall n, 0 < n -> divisors n 1.
Proof. by move=> *; rewrite -dvdn_divisors // dvd1n. Qed.

Lemma divisorn: forall n, 0 < n -> divisors n n.
Proof. by move=> *; rewrite -dvdn_divisors. Qed.

Lemma primeP : forall p,
  reflect (p > 1 /\ forall d, dvdn d p -> set2 1 p d) (prime p).
Proof.
rewrite /prime; case=> [|[|n]]; last 1 [set p := S (S n)] || by right; case.
apply: (iffP idP) => [Hn | [_ Hn]]; first split=> // d.
  by rewrite dvdn_divisors // (eqP Hn) mem_seq2.
have:= uniq_divisors p; have{Hn}: all (set2 1 p) (divisors p).
  apply/allP=> d; rewrite -dvdn_divisors //; exact: Hn.
rewrite /divisors -{3 5 7}[p](addn1 (S n)) iota_add -[1 + _]/p.
rewrite -(uniq_rot 1) filter_cat /= dvd1n // dvdnn.
case: filter => //= d s; rewrite -mem_seq2 -(mem_rot 1); case/andP=> Hd _.
by rewrite -catA mem_cat; case/andP; case/norP=> _; case/negP.
Qed.
Implicit Arguments primeP [p].
Prenex Implicits primeP.

Lemma prime_gt1 : forall p, prime p -> 1 < p.
Proof. by case=> [|[|p]]. Qed.

Fixpoint gcdn_rec (m p n : nat) {struct n} : nat :=
  if n is S n' then if p is 0 then m else gcdn_rec p (modn m p) n' else m.

Definition gcdn m p := gcdn_rec m p p.

Lemma gcdnE : forall m p,
  gcdn m p = if p == 0 then m else gcdn p (modn m p).
Proof.
move=> m [|p] //=; rewrite /gcdn /=; case: edivnP => /= _ r _ {m}.
elim: r {1 4 5}r p (S p) (leqnn r) => [|n1 IHn1] [|p] [|n2] m //=.
case: edivnP => /= _ r _ {m} Hr Hn1; apply: IHn1; exact: leq_trans Hr Hn1.
Qed.

Lemma gcdnC : forall n1 n2, gcdn n1 n2 = gcdn n2 n1.
Proof.
have Hltn: forall n1 n2, n1 < n2 -> gcdn n1 n2 = gcdn n2 n1.
  by move=> n1 [|n2] Hn12; rewrite gcdnE modn_small.
move=> n1 n2; case: (ltnP n1 n2); first exact: Hltn.
by rewrite leq_eqVlt; case/orP; [move/eqP-> | move/Hltn].
Qed.

Lemma gcdnn : forall n, gcdn n n = n.
Proof. by case=> // n; rewrite gcdnE modnn. Qed.

Lemma gcdn0 : forall n, gcdn n 0 = n.
Proof. done. Qed.

Lemma dvdn_gcdl : forall m n, dvdn (gcdn m n) m.
Proof.
move=> m n; move/S: n {-2}n m (ltnSn n).
elim=> // [i IHi] [|n] m; rewrite ltnS gcdnE [modn]lock //= -lock => Hn.
rewrite {2}(divn_eq m (S n)); set r := modn _ _.
have{Hn} Hr: r < i by apply: leq_trans Hn; rewrite /r ltn_mod.
apply: dvdn_add; auto; case: r Hr => // r Hr; rewrite gcdnE; apply: IHi.
by apply: ltn_trans Hr; rewrite ltn_mod.
Qed.

Lemma dvdn_gcdr : forall m n, dvdn (gcdn m n) n.
Proof. by move=> m n; rewrite gcdnC dvdn_gcdl. Qed.

Lemma ltn_0gcd : forall m n, (0 < gcdn m n) = (0 < m) || (0 < n).
Proof.
move=> m [|n]; rewrite orbC //; have:= dvdn_gcdr m (S n).
by case/dvdnP=> q; rewrite mulnC; case gcdn.
Qed.

Lemma bezoutl : forall m n, m > 0 -> {a | a < m & dvdn m (gcdn m n + a * n)}.
Proof.
move=> m n; elim: {n}(S n) m {-2}n (ltnSn n) => // [i IHi] m n.
case: n (dvdn_gcdl m n) => [|n]; first by exists 0; rewrite // gcdnE addn0.
rewrite ltnS gcdnE /=; case: edivnP => /= q r Dm Hr Hdm Hi.
case: (IHi (S n) r) => // [|{i IHi Hi} a Ha]; first exact: leq_trans Hi.
rewrite dvdn_eq; move: (divn _ _) => b; move/eqP=> Db Hm; exists (m - (q * a + b)).
  rewrite -(ltnSpred Hm) ltnS leq_subLR -add1n leq_add2r.
  by rewrite -(@ltn_pmul2r (S n)) // muln_addl Db !ltn_0add ltn_0gcd orbT.
rewrite muln_subl muln_addl Db -mulnA mulnCA -(addnC (a * r)) addnA -muln_addr -Dm.
rewrite -subn_sub mulnC -muln_subl -(mul1n (gcdn _ _)) subnKl; auto.
by apply: leq_mul; [rewrite ltn_0sub | exact: dvdn_leq].
Qed.

Lemma bezoutr : forall m n, n > 0 -> {a | a < n & dvdn n (gcdn m n + a * m)}.
Proof. by move=> m n; rewrite gcdnC; exact: bezoutl. Qed.

Lemma gcdn_addl_mul : forall k m n, gcdn m (k * m + n) = gcdn m n.
Proof.
by move=> k m n; rewrite !(gcdnC m) !(gcdnE _ m) modn_addl_mul mulnC; case: m.
Qed.

Lemma gcdn_addl: forall m n, gcdn m (m + n) = gcdn m n.
Proof. by move => m n; rewrite -{2}(mul1n m) gcdn_addl_mul. Qed.

Lemma gcdn_addr: forall m n, gcdn m (n + m) = gcdn m n.
Proof. by move=> m n; rewrite addnC gcdn_addl. Qed.

Lemma dvdn_gcd : forall p m n, dvdn p m -> dvdn p n -> dvdn p (gcdn m n).
Proof.
move=> p m [|n] // Hpm Hpn; case: (@bezoutr m (S n)) => // a _.
by move/(dvdn_trans Hpn); rewrite dvdn_addl; auto.
Qed.

Lemma gcdn_mul2l : forall p m n, gcdn (p * m) (p * n) = p * gcdn m n.
Proof.
case=> // p m n; elim: {n}(S n) {-2}n m (ltnSn n) => // h IHh n m.
rewrite gcdnE (gcdnE m) eqn_mul0 modn_pmul2l // [_ || _]/= ltnS => Hh.
by case: posnP => // Hn; apply: IHh; apply: leq_trans Hh; rewrite ltn_mod.
Qed.

Definition coprime m n := gcdn m n == 1.

Lemma coprime_sym : forall m n, coprime m n = coprime n m.
Proof. by move => m n; rewrite /coprime gcdnC. Qed.

Lemma prime_coprime : forall p m, prime p -> coprime p m = ~~ dvdn p m.
Proof.
move=> p m; move/primeP=> [Hp1 Hp].
apply/eqP/negP=> Hm.
  move/dvdnP=> [k Dm]; move: Hm Hp1.
  by rewrite -(addn0 m) Dm gcdn_addl_mul gcdn0 => ->.
move/Hp: (dvdn_gcdl p m); case/orP; move/eqP=> // Dp; case: Hm.
by rewrite Dp dvdn_gcdr.
Qed.

Lemma gauss : forall m n p, coprime m n -> dvdn m (n * p) = (dvdn m p).
Proof.
move => m n p Hmn; apply/idP/idP; last auto.
move/eqnP: Hmn; case: (posnP m) => [->|Hm Hmn]; first by case n; case p.
case/(bezoutl n): Hm => a _ Da; move/(dvdn_mulr a); rewrite mulnC mulnA => Hm.
by move/(dvdn_mulr p): Da; rewrite {}Hmn muln_addl mul1n dvdn_addl.
Qed.

Lemma euclid : forall m n p, prime p -> dvdn p (m * n) = dvdn p m || dvdn p n.
Proof.
move => m n p Hp; case Hm: (dvdn p m); first exact: dvdn_mulr.
by rewrite gauss // prime_coprime // Hm.
Qed.

(* power function *)

Fixpoint expn (m n : nat) {struct n} : nat :=
  if n is S n' then m * (expn m n') else 1.

Lemma expn0 : forall m, expn m 0 = 1.
Proof. done. Qed.

Lemma exp0n : forall n, 0 < n -> expn 0 n = 0.
Proof. by elim. Qed.

Lemma expnS : forall m n, expn m (S n) = m * expn m n.
Proof. done. Qed.

Lemma expn1 : forall m, expn m 1 = m.
Proof. by move=> m; rewrite expnS expn0 muln1. Qed.

Lemma exp1n : forall n, expn 1 n = 1.
Proof. by elim=> //= *; rewrite addn0. Qed.

Lemma expn_add : forall m n1 n2, expn m (n1 + n2) = expn m n1 * expn m n2.
Proof. by move=> m n1 n2; elim: n1 => //= n1 IHn; rewrite -mulnA -IHn. Qed.

Lemma expn_mull : forall m1 m2 n, expn (m1 * m2) n = expn m1 n * expn m2 n.
Proof. by move=> m1 m2; elim=> //= n ->; rewrite -!mulnA (mulnCA m2). Qed.

Lemma expn_mulr : forall m n1 n2, expn m (n1 * n2) = expn (expn m n1) n2.
Proof.
move=> m n1 n2; elim: n1 => [|n1 IHn] /=; first by rewrite exp1n.
by rewrite expn_add expn_mull IHn.
Qed.

Lemma ltn_0exp : forall m n, (0 < expn m n) = (0 < m) || (n == 0).
Proof. by move=> [|m]; elim=> //= n IHn; rewrite ltn_0add IHn. Qed.
 
Lemma ltn_expl : forall m n, 1 < m -> n < expn m n.
Proof.
move=> m n Hm; elim: n => //= n; rewrite -(leq_pmul2l (ltnW Hm)).
by apply: leq_trans; rewrite -{1}(mul1n (S n)) ltn_pmul2r.
Qed.

Lemma leq_exp2l : forall m n1 n2, 1 < m -> (expn m n1 <= expn m n2) = (n1 <= n2).
Proof.
move=> m n1 n2 Hm; elim: n1 n2 => [|n1 IHn] [|n2] //=; last 1 first.
- by rewrite ltnS leq_pmul2l // ltnW.
- by rewrite ltn_0mul ltn_0exp ltnW.
by rewrite leqNgt (leq_trans Hm) // -{1}(muln1 m) leq_pmul2l ?ltn_0exp ltnW.
Qed.

Lemma ltn_exp2l : forall m n1 n2, 1 < m -> (expn m n1 < expn m n2) = (n1 < n2).
Proof. by move=> *; rewrite !ltnNge leq_exp2l. Qed.

Lemma leq_pexp2l : forall m n1 n2, 0 < m -> n1 <= n2 -> expn m n1 <= expn m n2.
Proof. by move=> [|[|m]] // *; [rewrite !exp1n | rewrite leq_exp2l]. Qed.
 
Lemma ltn_pexp2l : forall m n1 n2, 0 < m -> expn m n1 < expn m n2 -> n1 < n2. 
Proof. by move=> [|[|m]] // n1 n2; [rewrite !exp1n | rewrite ltn_exp2l]. Qed.

Fixpoint logn_rec (d m r : nat) {struct r} : nat :=
  match r, edivn m d with
  | S r', (S _ as m', 0) => S (logn_rec d m' r')
  | _, _ => 0
  end.

Definition logn p m := if prime p then logn_rec (pred p) m m else 0.

Lemma lognE : forall p m,
  logn p m = if and3b (prime p) (0 < m) (dvdn p m) then S (logn p (divn m p)) else 0.
Proof.
rewrite /logn /dvdn; move=> [|[|d]] [|m] //=; case: (prime _) => //.
case: edivnP => [[|q] [|r] Dm _] //; congr S; rewrite [fst _]/=.
have{Dm}: q < m by rewrite -ltnS Dm addn0 mulnC /= !addSn addnS !ltnS leq_addr.
elim: m {q}(S q) {-2 3 6}q (ltnSn q) => [|m1 IHm] [|m2] //= q Hm1 Hm2.
case: edivnP=> [[|q'] [|_] Dq _] //; rewrite (IHm m2) //; rewrite addn0 in Dq.
rewrite -ltnS -(@ltn_pmul2r (S (S d))) // -Dq mulnC /=  addSn ltnS addnCA.
by rewrite (leq_trans Hm1) // leq_addr.
Qed.

Lemma dvdn_exp_max : forall p n m,
  prime p -> m > 0 -> dvdn (expn p n) m = (n <= logn p m).
Proof.
move=> p n [|m] // Hp _; elim: {m}(S m) {-2}m (ltnSn m) n => // [h IHh] m //.
rewrite lognE ltnS Hp /= => Hh [|n]; first by rewrite dvd1n.
case Hm: (dvdn p (S m));
  last by apply/dvdnP; case=> /= q Dm; case/negP: Hm; rewrite Dm; auto.
move/prime_gt1: Hp Hm => Hp; rewrite //= dvdn_eq; move/eqP; case: divn => // q Dm.
rewrite -Dm -(mulnC p) dvdn_pmul2l ?IHh; auto.
by apply: leq_trans Hh; rewrite -ltnS -Dm -{1}(muln1 (S q)) ltn_pmul2l.
Qed.

Definition p_part p m := expn p (logn p m).

Lemma dvdn_p_part : forall p m, dvdn (p_part p m) m.
Proof.
rewrite /p_part => p [|m] //.
by case Hp: (prime p); [rewrite dvdn_exp_max | rewrite lognE Hp].
Qed.

Lemma dvdn_p_p_part : forall p m, prime p -> dvdn (p * p_part p m) m = (m == 0).
Proof. by move=> p [|m] Hp; rewrite ?dvdn0 // /p_part -expnS dvdn_exp_max ?ltnn. Qed.

Lemma dvdn_leq_log : forall p m n,
  prime p -> 0 < n -> dvdn m n -> logn p m <= logn p n.
Proof.
move=> d m n Hd Hn; rewrite -dvdn_exp_max //.
apply: dvdn_trans; exact: dvdn_p_part.
Qed.

Lemma logn_exp : forall p n, prime p -> logn p (expn p n) = n.
Proof.
move=> p n Hp; elim: n => [|h IHn]; rewrite /= lognE Hp.
  by rewrite dvdn1 /= eqn_leq leqNgt prime_gt1.
by rewrite ltn_0mul ltn_0exp divn_mulr (ltnW (prime_gt1 Hp)) // IHn dvdn_mulr.
Qed.

Lemma logn_gauss : forall p m n, coprime p m -> logn p (m * n) = logn p n.
Proof.
move=> p m n Hm; elim: {n}(S n) {-2}n (ltnSn n) => // h IHh.
case=> [|n]; rewrite ?muln0 // ltnS => Hh.
rewrite lognE (lognE p (S n)) gauss //= ltn_0mul andbT.
case Hp: (prime p) => //; case: posnP => [Dm | _].
  by rewrite prime_coprime // Dm dvdn0 in Hm.
case Hpn: (dvdn p _); move: (Hpn); rewrite dvdn_eq //=; move/eqP=> Dn.
move/prime_gt1: Hp => Hp; case/dvdn_lt: Hpn => // H0q Hqn.
rewrite -{1}Dn mulnA divn_mull ?IHh; auto; exact: leq_trans Hh.
Qed.

Lemma p_part_coprime : forall p m, prime p -> m > 0 ->
  {q | coprime p q & m = q * p_part p m}.
Proof.
move=> p m Hp Hm; have Hp1:= prime_gt1 Hp; have:= dvdn_p_part p m.
rewrite dvdn_eq; move/eqP=> Dm; exists (divn m (p_part p m)) => //.
move: (lt0n_neq0 Hm); rewrite -(dvdn_p_p_part _ Hp) /= -{2}Dm.
by rewrite prime_coprime ?dvdn_pmul2r // /p_part ltn_0exp ltnW.
Qed.

Lemma logn_mul : forall p m n,
  prime p -> 0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n.
Proof.
move=> p m n Hp Hm Hn.
have [qm Hqm Dm] := p_part_coprime Hp Hm; have [qn Hqn Dn] := p_part_coprime Hp Hn.
rewrite {1}Dm -mulnA logn_gauss // {1}Dn mulnCA logn_gauss // /p_part -expn_add.
by rewrite logn_exp // prime_gt1.
Qed.

Lemma dvdn_exp_prime: forall p d n, prime p -> 
  reflect (exists2 m, m <= n & d = expn p m) (dvdn d (expn p n)).
Proof.
move=> p d n Hp; case/primeP: (Hp) => [Hp1 Hdivp]; have Hp0 := ltnW Hp1.
apply: (iffP dvdnP) => [[q Dq]|[m Hm Dd]]; last first.
  by exists (expn p (n - m)); rewrite Dd -expn_add addnC subnKl.
have Hpn: 0 < expn p n by rewrite ltn_0exp Hp0.
have [Hq Hd]: 0 < q /\ 0 < d by apply/andP; rewrite -ltn_0mul -Dq.
move: (logn_exp n Hp); rewrite Dq logn_mul // => Dn.
exists (logn p d); first by rewrite -Dn leq_addl.
apply/eqP; rewrite eqn_dvd -(dvdn_pmul2l Hq) -Dq -Dn mulnC expn_add mulnC.
rewrite dvdn_pmul2l ?ltn_0exp ?Hp0 //; apply/andP; split; auto; exact: dvdn_p_part.
Qed.

Lemma dvdn_expS : forall n a b, dvdn a b -> dvdn a (expn b (S n)).
Proof. by simpl; auto. Qed.

Unset Implicit Arguments.