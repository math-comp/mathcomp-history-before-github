Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.

(**************************************************************************)
(* This files contains the definitions of:                                *)
(* -division: divn and modn compute the euclidian quotient and remainder  *)
(*            edivn m d performs the euclidian division of m by d         *)
(* -divisibility: dvdn d m <=> d divides m                                *)
(*                divisors m == the ascending divisors list of m if m > 0 *)
(*                gcdn m n == the GCD of m and n                          *)
(*                coprime m n <=> m and n are coprime                     *)
(*                phi n == the Euler totient                              *)
(* The bezout[lr] lemmas give the bezout coefficients.                    *)
(* -primality: prime p <=> p is prime                                     *)
(*             primes m == the list of prime divisors of m if m > 0       *)
(*             prime_decomposition m == self-explanatory                  *)
(* -powers: logn p m == the number of times p divides m                   *)
(*          p_part p m == p ^ (logn p m)                                  *)
(*  The main goal of this file is Gauss theorem and the Euclid theorem as *)
(* a direct corollary.                                                    *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Euclidian division *)

Definition edivn_rec d := fix loop (m q : nat) {struct m} :=
  if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d is d'.+1 then edivn_rec d' m 0 else (0, m).

CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) : edivn_spec m d (q, r).

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
move=> m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
rewrite subn_if_gt; case: ltnP => [// | le_dm].
rewrite -{1}(subnK le_dm) -addSn addnA -mulSnr; apply: IHn.
apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
case: edivnP lt_rd => q' r'; rewrite d_pos /=.
wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addn_injl->.
rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.

Definition divn m d := nosimpl (edivn m d).1.

Notation "m %/ d" := (divn m d) (at level 40, no associativity) : nat_scope.

(* We redefine modn so that it is structurally decreasing. *)

Definition modn_rec d := fix loop (m : nat) :=
  if m - d is m'.+1 then loop m' else m.

Definition modn m d := nosimpl (if d is d'.+1 then modn_rec d' m else m).

Notation "m %% d" := (modn m d) (at level 40, no associativity) : nat_scope.

Lemma modn_def : forall m d, m %% d = (edivn m d).2.
Proof.
rewrite /modn => m [|d] //=; elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=.
rewrite ltnS !subn_if_gt (fun_if (@snd _ _)) => le_mn; rewrite -{}IHn //.
apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_def : forall m d, edivn m d = (m %/ d, m %% d).
Proof. by move=> m d; rewrite /divn modn_def; case edivn. Qed.

Lemma divn_eq : forall m d, m = m %/ d * d + m %% d.
Proof. by move=> m d; rewrite /divn modn_def; case edivnP. Qed.

Lemma div0n : forall d, 0 %/ d = 0. Proof. by case. Qed.
Lemma divn0 : forall m, m %/ 0 = 0. Proof.  by []. Qed.
Lemma mod0n :  forall d, 0 %% d = 0. Proof. by case. Qed.
Lemma modn0 :  forall m, m %% 0 = m. Proof. by []. Qed.

Lemma divn_small : forall m d, m < d -> m %/ d = 0.
Proof. by move=> m d lt_md; rewrite /divn (edivn_eq 0). Qed.

Lemma divn_addl_mul : forall q m d, 0 < d -> (q * d + m) %/ d = q + m %/ d.
Proof.
move=> q m d d_pos; rewrite {1}(divn_eq m d) addnA -muln_addl.
by rewrite /divn edivn_eq // modn_def; case: edivnP; rewrite d_pos.
Qed.

Lemma divn_mull : forall m d, 0 < d -> m * d %/ d = m.
Proof.
by move=> m d d_pos; rewrite -[m * d]addn0 divn_addl_mul // div0n addn0.
Qed.

Lemma divn_mulr : forall m d, 0 < d -> d * m %/ d = m.
Proof. by move=> *; rewrite mulnC divn_mull. Qed.

Lemma modn1 : forall m, m %% 1 = 0.
Proof. by move=> m; rewrite modn_def; case: edivnP => ? []. Qed.

Lemma divn1: forall m, m %/ 1 = m.
Proof. by move=> m; rewrite {2}(@divn_eq m 1) // modn1 addn0 muln1. Qed.

Lemma divnn : forall d, d %/ d = (0 < d).
Proof. by case=> // d; rewrite -{1}[d.+1]muln1 divn_mulr. Qed.

Lemma divn_pmul2l : forall p m d, p > 0 -> p * m %/ (p * d) = m %/ d.
Proof.
move=> p m d p_pos; case: (posnP d) => [-> | d_pos]; first by rewrite muln0.
rewrite {2}/divn; case: edivnP; rewrite d_pos /= => q r ->{m} lt_rd.
rewrite muln_addr mulnCA divn_addl_mul; last by rewrite ltn_0mul p_pos.
by rewrite addnC divn_small // ltn_pmul2l.
Qed.
Implicit Arguments divn_pmul2l [p m d].

Lemma ltn_mod : forall m d, (m %% d < d) = (0 < d).
Proof. by move=> m [|d] //; rewrite modn_def; case: edivnP. Qed.

Lemma ltn_pmod : forall m d, 0 < d -> m %% d < d.
Proof. by move=> m d; rewrite ltn_mod. Qed.

Lemma leq_div : forall m d, m %/ d * d <= m.
Proof. by move=> m d; rewrite {2}(divn_eq m d) leq_addr. Qed.

Lemma ltn_Sdiv : forall m d, 0 < d -> m < (m %/ d).+1 * d.
Proof.
by move=> m d ? /=; rewrite {1}(divn_eq m d) -addnS mulSnr leq_add2l ltn_mod.
Qed.

Lemma divn_lt : forall m d, 1 < d -> 0 < m -> m %/ d < m.
Proof.
move=> m d d_gt1 m_pos; set q := m %/ d; case: (posnP q) => [-> //| q_pos]. 
by apply: leq_trans (leq_div m d); rewrite -[q]muln1 ltn_pmul2l.
Qed.

Lemma modn_small : forall m d, m < d -> m %% d = m.
Proof. by move=> m d lt_md; rewrite {2}(divn_eq m d) divn_small. Qed.

Lemma modn_mod : forall m d, (m %% d) %% d = m %% d.
Proof. by move=> m [|d] //; apply: modn_small; rewrite ltn_mod. Qed.

Lemma modn_addl_mul : forall p m d, (p * d + m) %% d = m %% d.
Proof.
move=> p m d; case: (posnP d) => [-> | d_pos]; first by rewrite muln0. 
by rewrite {1}(divn_eq m d) addnA -muln_addl modn_def edivn_eq // ltn_mod.
Qed.

Lemma modn_pmul2l : forall p m d, 0 < p -> p * m %% (p * d) = p * (m %% d).
Proof.
move=> p m d p_pos; apply: (@addn_injl (p * (m %/ d * d))).
by rewrite -muln_addr -divn_eq mulnCA -(divn_pmul2l p_pos) -divn_eq.
Qed.
Implicit Arguments modn_pmul2l [p m d].

Lemma modn_addl : forall m d, (d + m) %% d = m %% d.
Proof. by move=> m d; rewrite -{1}[d]mul1n modn_addl_mul. Qed.

Lemma modn_addr : forall m d, (m + d) %% d = m %% d.
Proof. by move=> *; rewrite addnC modn_addl. Qed.

Lemma modnn : forall d, d %% d = 0.
Proof. by move=> d; rewrite -{1}[d]addn0 modn_addl mod0n. Qed.

Lemma modn_mull : forall p d, p * d %% d = 0.
Proof. by move=> p d; rewrite -[p * d]addn0 modn_addl_mul mod0n. Qed.

Lemma modn_mulr : forall p d, d * p %% d = 0.
Proof. by move=> p d; rewrite mulnC modn_mull. Qed.

Lemma modn_addml : forall m n d, (m %% d + n) %% d = (m + n) %% d.
Proof. by move=> m n d; rewrite {2}(divn_eq m d) -addnA modn_addl_mul. Qed.

Lemma modn_addmr : forall m n d, (m + n %% d) %% d = (m + n) %% d.
Proof. by move=> m n d; rewrite !(addnC m) modn_addml. Qed.

Lemma modn_add2m : forall m n d, (m %% d  + n %% d) %% d = (m + n) %% d.
Proof. by move=> m n d; rewrite modn_addml modn_addmr. Qed.

Lemma modn_mulml : forall m n d, m %% d * n %% d = m * n %% d.
Proof.
by move=> m n d; rewrite {2}(divn_eq m d) muln_addl mulnAC modn_addl_mul.
Qed.

Lemma modn_mulmr : forall m n d, m * (n %% d) %% d = m * n %% d.
Proof. by move=> m n d; rewrite !(mulnC m) modn_mulml. Qed.

Lemma modn_mul2m : forall m n d, m %% d * (n %% d) %% d = m * n %% d.
Proof. by move=> m n d; rewrite modn_mulml modn_mulmr. Qed.

Lemma modn2_odd : forall m, m %% 2 = odd m.
Proof. by elim=> //= m IHm; rewrite -addn1 -modn_addml IHm; case odd. Qed.

Lemma dvdn2_half : forall m, m %/ 2 = m./2.
Proof.
by move=> m; rewrite {2}(divn_eq m 2) modn2_odd muln2 addnC half_bit_double.
Qed.

Lemma odd_mod : forall m d, odd d = false -> odd (m %% d) = odd m.
Proof.
by move=> m d d_even; rewrite {2}(divn_eq m d) odd_add odd_mul d_even andbF.
Qed.

(** Divisibility **)

Definition dvdn d m := m %% d == 0.

Notation "m %| d" := (dvdn m d) (at level 70, no associativity) : nat_scope.

Lemma dvdn2_even : forall n, (2 %| n) = ~~ odd n.
Proof. by move=> n; rewrite /dvdn modn2_odd; case (odd n). Qed.

Lemma dvdnP: forall d m, reflect (exists k, m = k * d) (d %| m).
Proof.
move=> d m; apply: (iffP eqP) => [Hm | [k ->]]; last by rewrite modn_mull.
by exists (m %/ d); rewrite {1}(divn_eq m d) Hm addn0.
Qed.
Implicit Arguments dvdnP [d m].
Prenex Implicits dvdnP.

Lemma dvdn0 : forall d, d %| 0.
Proof. by move=> d; rewrite /dvdn mod0n. Qed.

Lemma dvdn1 : forall d, (d %| 1) = (d == 1).
Proof. by case=> [|[|n]] //; rewrite /dvdn modn_small. Qed.

Lemma dvd1n : forall m, 1 %| m.
Proof. by move=> m; rewrite /dvdn modn1. Qed.

Lemma ltn_0dvd : forall d m, m > 0 -> d %| m -> d > 0.
Proof. by do 2!case. Qed.

Lemma dvdnn: forall m, m %| m.
Proof. by move=> m; rewrite /dvdn modnn. Qed.

Lemma dvdn_mull: forall d m n, d %| n -> d %| m * n.
Proof. by move=> d m n; case/dvdnP=> n' ->; rewrite /dvdn mulnA modn_mull. Qed.

Lemma dvdn_mulr: forall d m n, d %| m -> d %| m * n.
Proof. by move=> *; rewrite mulnC dvdn_mull. Qed.

Hint Resolve dvdn0 dvd1n dvdnn dvdn_mull dvdn_mulr.

Lemma dvdn_trans: forall n d m, d %| n -> n %| m -> d %| m.
Proof. move=> n d m Hn; move/dvdnP => [n1 ->]; auto. Qed.

Lemma dvdn_eq : forall d m, (d %| m) = (m %/ d * d == m).
Proof.
move=> d m; apply/eqP/eqP=> [modm0 | <-]; last exact: modn_mull.
by rewrite {2}(divn_eq m d) modm0 addn0. 
Qed.

Lemma divnK : forall d m, d %| m -> m %/ d * d = m.
Proof. by move=> m d; rewrite dvdn_eq; move/eqP. Qed.

Lemma dvdn_leq : forall d m, 0 < m -> d %| m -> d <= m.
Proof.
by move=> d m Hm; case/dvdnP=> [[|k] Dm]; rewrite Dm //= leq_addr in Hm *.
Qed.

Lemma dvdn_lt : forall d m,
  1 < d -> 0 < m -> d %| m -> 0 < m %/ d /\ m %/ d < m.
Proof.
move=> d m d_gt1 m_pos; rewrite dvdn_eq; move/eqP=> def_m.
split; last exact: divn_lt.
by move: m_pos; rewrite -{1}def_m ltn_0mul; case/andP.
Qed.

Lemma eqn_dvd : forall m n, (m == n) = (m %| n) && (n %| m).
Proof.
case=> [|m] [|n] //; apply/idP/andP; first by move/eqP->; auto.
rewrite eqn_leq => [[Hmn Hnm]]; apply/andP; have:= dvdn_leq; auto.
Qed.

Lemma dvdn_pmul2l : forall p d m, 0 < p -> (p * d %| p * m) = (d %| m).
Proof. by case=> // p d m _; rewrite /dvdn modn_pmul2l // eqn_mul0. Qed.
Implicit Arguments dvdn_pmul2l [p m d].

Lemma dvdn_pmul2r : forall p d m, 0 < p -> (d * p %| m * p) = (d %| m).
Proof. by move=> n d m Hn; rewrite -!(mulnC n) dvdn_pmul2l. Qed.
Implicit Arguments dvdn_pmul2r [p m d].

Lemma dvdn_addr : forall m d n, d %| m -> (d %| m + n) = (d %| n).
Proof. by move=> n d m; move/dvdnP=> [k ->]; rewrite /dvdn modn_addl_mul. Qed.

Lemma dvdn_addl : forall n d m, d %| n -> (d %| m + n) = (d %| m).
Proof. by move=> n d m; rewrite addnC; exact: dvdn_addr. Qed.

Lemma dvdn_add : forall d m n, d %| m -> d %| n -> d %| m + n.
Proof. by move=> n d m; move/dvdn_addr->. Qed.

Lemma dvdn_add_eq : forall d m n, d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> *; apply/idP/idP; [move/dvdn_addr <-| move/dvdn_addl <-]. Qed.

Lemma dvdn_subr : forall d m n, n <= m -> d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> *; apply dvdn_add_eq; rewrite addnC subnK. Qed.

Lemma dvdn_subl : forall d m n, n <= m -> d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> d m n Hn; rewrite -{2}(subnK Hn); move/dvdn_addr. Qed.

Lemma dvdn_sub : forall d m n, d %|m -> d %| n -> d %| m - n.
Proof.
move=> d n m; case: (leqP m n) => Hm; first by move/dvdn_subr <-.
by rewrite (eqnP (ltnW Hm)) dvdn0.
Qed.

Lemma dvdn_exp : forall k d m, 0 < k -> d %| m -> d %| (m ^ k).
Proof. by case=> // *; rewrite expnS dvdn_mulr. Qed.

Hint Resolve dvdn_add dvdn_sub dvdn_exp.

Lemma eqn_mod_dvd : forall d m n, n <= m -> (m %% d == n %% d) = (d %| m - n).
Proof.
rewrite /dvdn => d m n le_nm; apply/eqP/eqP => [eq_mod | mod_mn_0]; last first.
  by rewrite -(subnK le_nm) -modn_addmr mod_mn_0 addn0.
by rewrite (divn_eq m d) (divn_eq n d) eq_mod subn_add2r -muln_subl modn_mull.
Qed.

(** Primes. *)

Definition divisors m := filter (dvdn^~ m) (iota 1 m).
Definition prime p := divisors p == [:: 1; p].
Definition primes m := filter prime (divisors m).

Lemma dvdn_divisors : forall d m, 0 < m -> (d %| m) = (d \in divisors m).
Proof.
move=> [|d] [|m] // _; rewrite /divisors mem_filter mem_iota //.
by case dv_dm: (_ %| _); rewrite //= ltnS dvdn_leq.
Qed.

Lemma uniq_divisors : forall m, uniq (divisors m).
Proof. move=> m; apply: uniq_filter; exact: uniq_iota. Qed.

Lemma divisor1: forall n, 0 < n -> 1 \in divisors n.
Proof. by move=> *; rewrite -dvdn_divisors // dvd1n. Qed.

Lemma divisorn: forall n, 0 < n -> n \in divisors n.
Proof. by move=> *; rewrite -dvdn_divisors. Qed.

Lemma primeP : forall p,
  reflect (p > 1 /\ forall d, d %| p -> xpred2 1 p d) (prime p).
Proof.
rewrite /prime; case=> [|[|n]]; last 1 [set p := n.+2] || by right; case.
apply: (iffP idP) => [Hn | [_ Hn]]; first split=> // d.
  by rewrite dvdn_divisors // (eqP Hn) mem_seq2 !(eq_sym d).
have:= uniq_divisors p; have{Hn}: all (pred2 1 p) (divisors p).
  apply/allP=> d; rewrite -dvdn_divisors //; exact: Hn.
rewrite /divisors -{3 5 7}[p](addn1 n.+1) iota_add -[1 + _]/p.
rewrite -(uniq_rot 1) filter_cat /= dvd1n // dvdnn.
case: filter => //= d s; rewrite -mem_seq2 -(mem_rot 1).
case/andP=> Hd _; rewrite -catA mem_cat.
by case/andP; case/norP=> _; case/negP.
Qed.

Implicit Arguments primeP [p].
Prenex Implicits primeP.

Lemma primePn : forall n,
  reflect (n < 2 \/ exists2 d, 1 < d < n & d %| n) (~~prime n).
Proof.
move=> n; apply: (iffP idP); last first.
  case; first case: n => //; case => // x Hx Hdx; apply/primeP => [] [Hn1 Hn2].
  by move: Hx; case/orP: (Hn2 _ Hdx); move/eqP<-; rewrite ltnn // andbF.
case: n => [|[|n]] //; try by left.
case E1: (has (predC (xpred2 1 n.+2)) (divisors n.+2)).
  case/hasP: E1 => d Hd; rewrite /= negb_orb; case/andP => Hd1 Hd2.
  right; exists d; move: Hd; rewrite -dvdn_divisors //.
  case: d Hd1 Hd2 => //; case => [|d] // _ Hd1.
  by rewrite [_ < n.+2] ltn_neqAle Hd1; move/(dvdn_leq (ltn0Sn n.+1)).
move/hasPn: E1 => E1; move/negP; case; apply/primeP; split => // d.
by rewrite dvdn_divisors //; move/E1; rewrite negb_involutive.
Qed.

Implicit Arguments primePn [n].
Prenex Implicits primePn.
 
Lemma primePns : forall n,
  reflect (n < 2 \/ exists p, [/\ prime p , p * p <= n & p %| n]) (~~prime n).
Proof.
move=> n; apply: (iffP idP); last first.
  case; first case: n => //; case => // x [Hx1 Hx2 Hx3]; apply/primeP => [] [Hn1 Hn2].
  move: Hx1 Hx2; case/orP: (Hn2 _ Hx3); move/eqP-> => //.
  by rewrite -{4}[n]muln1 leq_pmul2l; case: (n) Hn1 => //; case.
elim: n {-2}n (leqnn n) => [| m Hrec n Hn]; first by case=> //; left.
case/primePn; first by left.
case=> d; case/andP=> Hd1 Hd2 Hd3.
  case P1: (prime d); move/idP: P1 => P1; last first.
  have F1: d <= m by rewrite -ltnS (leq_trans _ Hn).
  case: (Hrec d F1); [by apply/negP | by case: (d) Hd1 => //; case | idtac].
  case=> p [Hp1 Hp2 Hp3]; right; exists p; split => //; last by apply: dvdn_trans Hd3.
  by rewrite (leq_trans Hp2) // ltnW.
case: (leqP (d * d) n) => E1; first by right; exists d.
pose d' := n %/ d; have Hd': d' * d = n := (divnK  Hd3).
have Hd0: 0 < d by apply: leq_trans Hd1.
have Hd'0: 0 < d' by move: Hd2; rewrite -Hd'; case d'.
have Hd'1: d' %| n by rewrite -Hd' dvdn_mulr. 
case P2: (prime d'); move/idP: P2 => P2; last first.
  have F2: d' <= m.
    by rewrite -ltnS (leq_trans _ Hn) // /d' divn_lt //; case: (n) Hd2 => //.
  case: (Hrec d' F2); first by apply/negP.
    by move: Hd2; rewrite -Hd'; case: (d') => //; case=> //; rewrite mul1n ltnn.
  case=> p [Hp1 Hp2 Hp3]; right; exists p; split=> //; last first.
    by rewrite (dvdn_trans Hp3).
  by rewrite (leq_trans Hp2) // -Hd' -{1}[d']muln1 leq_pmul2l.
right; exists d'; split=> //.
by rewrite -Hd' leq_pmul2l // -(@leq_pmul2r d) // Hd' ltnW.
Qed.

Implicit Arguments primePns [n].
Prenex Implicits primePns.

Lemma prime_gt1 : forall p, prime p -> 1 < p. Proof. by do 2?case. Qed.

Lemma ltn_0prime : forall p, prime p -> 0 < p. Proof. by case. Qed.

Hint Resolve prime_gt1 ltn_0prime.

Lemma prime_pos_natP m : prime m -> m > 0.
Proof. by move=>m; move/ltn_0prime. Qed.
Definition prime_pos_nat m (H:prime m) := PosNat (prime_pos_natP H).

Lemma even_prime : forall p, prime p -> p = 2 \/ odd p.
Proof.
move=> p pr_p; case odd_p: (odd p); [by right | left].
have: 2 %| p by rewrite dvdn2_even odd_p.
by case/primeP: pr_p => _ dv_p; move/dv_p; move/(2 =P p).
Qed.

(***********************************************************************)
(* A function that computes the smallest (prime) divisor of a number.  *)
(***********************************************************************)

Definition pdiv n := sub n (divisors n) 1.

Lemma dvdn_pdiv : forall n, dvdn (pdiv n) n.
Proof.
rewrite /pdiv => n; case: (posnP n) => [-> //| ]; move/dvdn_divisors.
by case: (divisors n) => [|a1 [|p sp]] //= => ->; rewrite !in_adds eqxx orbT.
Qed.

Lemma leq_pdiv : forall n, pdiv n <= n.
Proof. by case=> // n; rewrite dvdn_leq // dvdn_pdiv. Qed.

Lemma pdiv_min_dvd : forall m d, 1 < d -> d %| m -> pdiv m <= d.
Proof.
case=> // m d d_gt1; rewrite dvdn_divisors // /pdiv /divisors /= dvd1n /=.
rewrite in_adds eqn_leq leqNgt {}d_gt1 /=.
elim: {2 4}m 2 => //= n IHn p; case: (_ %| _) => //=; last exact: IHn.
rewrite in_adds mem_filter mem_iota andbCA orb_andr eq_sym -leq_eqVlt.
by case/andP.
Qed.

Lemma pdiv_gt1 : forall n, (1 < pdiv n) = (1 < n).
Proof.
case=> // n; have:= dvdnn n.+1.
rewrite dvdn_divisors // /pdiv /divisors /= dvd1n /=; case: n => // n.
set dv := filter _ _; case def_p: dv => //= [p dv']  _.
have: p \in dv by rewrite def_p mem_head.
by rewrite mem_filter mem_iota andbCA; case/andP.
Qed.

Lemma ltn_0pdiv : forall n, (0 < pdiv n) = (0 < n).
Proof. by case=> [|[|n]] //; rewrite ltnW ?pdiv_gt1. Qed.

Lemma prime_pdiv: forall n, 1 < n -> prime (pdiv n).
Proof.
move=> n n_gt1; have p_gt: pdiv n > 1 by rewrite pdiv_gt1.
apply/primeP; rewrite pdiv_gt1; split=> // d dv_d_p.
have: d > 0 by apply: ltn_0dvd dv_d_p; auto.
rewrite leq_eqVlt eq_sym; case: (d == 1) => //= d_gt1.
rewrite eq_sym eqn_leq pdiv_min_dvd //=; first by apply dvdn_leq; auto.
exact: dvdn_trans (dvdn_pdiv n).
Qed.

Lemma ltn_pdiv2_prime : forall n, n < pdiv n ^ 2 -> prime n.
Proof.
move=> n; case def_n: n => [|[|n']] //; rewrite -def_n => lt_n_p2.
suff ->: n = pdiv n by rewrite prime_pdiv ?def_n.
apply/eqP; rewrite eqn_leq leq_pdiv andbT leqNgt; apply/negP=> lt_pm_m.
move: lt_n_p2; rewrite ltnNge; case/negP.
case/dvdnP: (dvdn_pdiv n) => q def_q.
have p_pos: 0 < pdiv n by rewrite ltn_0pdiv def_n.
rewrite {2}def_q -mulnn leq_pmul2r // pdiv_min_dvd //.
  by rewrite -(ltn_pmul2r p_pos) mul1n -def_q.
by rewrite def_q dvdn_mulr.
Qed.

(***********************************************************************)
(*   A function that computes the gcd of 2 numbers                     *)
(***********************************************************************)

Fixpoint gcdn_rec (m n : nat) {struct m} :=
  let n' := n %% m in if n' is 0 then m else
  if m - n'.-1 is m'.+1 then gcdn_rec (m' %% n') n' else n'.

Definition gcdn := nosimpl gcdn_rec.

Lemma gcdnE : forall m n, gcdn m n = if m == 0 then n else gcdn (n %% m) m.
Proof.
rewrite /gcdn => m; elim: m {-2}m (leqnn m) => [|s IHs] [|m] le_ms [|n] //=.
case def_n': (_ %% _) => // [n'].
have lt_n'm: n' < m by rewrite -def_n' -ltnS ltn_pmod.
rewrite {}IHs ?(leq_trans lt_n'm) // subn_if_gt ltnW //=; f_equal.
by rewrite -{2}(subnK (ltnW lt_n'm)) -addSn modn_addl.
Qed.

Lemma gcdnn : idempotent gcdn.
Proof. by case=> // n; rewrite gcdnE modnn. Qed.

Lemma gcdnC : commutative gcdn.
Proof.
move=> m n; wlog lt_nm: m n / n < m.
  by case: (ltngtP n m) => [||->]; [|symmetry|rewrite gcdnn]; auto.
by rewrite gcdnE -{1}(ltn_predK lt_nm) modn_small.
Qed.

Lemma gcd0n : left_unit 0 gcdn. Proof. by case. Qed.
Lemma gcdn0 : right_unit 0 gcdn. Proof. by case. Qed.

Lemma gcd1n : left_zero 1 gcdn.
Proof. by move=> n; rewrite gcdnE modn1. Qed.

Lemma gcdn1 : right_zero 1 gcdn.
Proof. by move=> n; rewrite gcdnC gcd1n. Qed.

Lemma dvdn_gcdr : forall m n, gcdn m n %| n.
Proof.
move=> m; elim: m {-2}m (leqnn m) => [|s IHs] [|m] le_ms [|n] //.
rewrite gcdnE; case def_n': (_ %% _) => [|n']; first by rewrite /dvdn def_n'.
have lt_n's: n' < s by rewrite -ltnS (leq_trans _ le_ms) // -def_n' ltn_pmod.
rewrite /= (divn_eq n.+1 m.+1) def_n' dvdn_addr ?dvdn_mull //; last exact: IHs.
by rewrite gcdnE /= IHs // (leq_trans _ lt_n's) // ltnW // ltn_pmod.
Qed.

Lemma dvdn_gcdl : forall m n, gcdn m n %| m.
Proof. by move=> m n; rewrite gcdnC dvdn_gcdr. Qed.

Lemma ltn_0gcd : forall m n, (0 < gcdn m n) = (0 < m) || (0 < n).
Proof.
move=> [|m] [|n] //; apply: (@ltn_0dvd _ m.+1) => //; exact: dvdn_gcdl.
Qed.

Lemma gcdn_addl_mul : forall k m n, gcdn m (k * m + n) = gcdn m n.
Proof. by move=> k m n; rewrite !(gcdnE m) modn_addl_mul mulnC; case: m. Qed.

Lemma gcdn_addl: forall m n, gcdn m (m + n) = gcdn m n.
Proof. by move => m n; rewrite -{2}(mul1n m) gcdn_addl_mul. Qed.

Lemma gcdn_addr: forall m n, gcdn m (n + m) = gcdn m n.
Proof. by move=> m n; rewrite addnC gcdn_addl. Qed.

Lemma gcdn_mull : forall n m, gcdn n (m * n) = n.
Proof. by move=> n m; rewrite gcdnE modn_mull gcd0n; case defn:n=> /=. Qed.

Lemma gcdn_mulr : forall n m, gcdn n (n * m) = n.
Proof. by move=> n m; rewrite mulnC gcdn_mull. Qed.


(* Extended gcd, which computes Bezout coefficients. *)

Fixpoint bezout_rec (km kn : nat) (qs : seq nat) {struct qs} :=
  if qs is q :: qs' then bezout_rec kn (NatTrec.add_mul q kn km) qs'
  else (km, kn).

Fixpoint egcdn_rec (m n s : nat) (qs : seq nat) {struct s} :=
  if s is s'.+1 then
    let: (q, r) := edivn m n in
    if r > 0 then egcdn_rec n r s' (q :: qs) else
    if odd (size qs) then qs else q.-1 :: qs
  else [::0].

Definition egcdn m n := bezout_rec 0 1 (egcdn_rec m n n [::]).

CoInductive egcdn_spec (m n : nat) : nat * nat -> Type :=
  EgcdnSpec km kn of km * m = kn * n + gcdn m n & kn * gcdn m n < m :
    egcdn_spec m n (km, kn).

Lemma egcdnP : forall m n, m > 0 -> egcdn_spec m n (egcdn m n).
Proof.
rewrite /egcdn => m0 n0; have: (n0, m0) = bezout_rec n0 m0 [::] by [].
case: (posnP n0) => [-> /=|]; first by split; rewrite // mul1n gcdn0.
elim: {1 4}n0 {1 3 5 7}n0 {-1 4}m0 [::] (ltnSn n0) => [[]//|s IHs] n m qs /=.
move=> le_ns n_pos def_mn0 m_pos.
case: edivnP => q r def_m; rewrite n_pos /= => lt_rn.
case: posnP => [r0 {s le_ns IHs lt_rn}|r_pos]; last first.
  by apply: IHs => //=; [rewrite (leq_trans lt_rn) | rewrite natTrecE -def_m].
rewrite {r}r0 addn0 in def_m; set b := odd _; pose d := gcdn m n.
pose km := ~~ b : nat; pose kn := if b then 1 else q.-1.
rewrite (_ : bezout_rec _ _ _ = bezout_rec km kn qs); last first.
  by rewrite /kn /km; case b => //=; rewrite natTrecE addn0 muln1.
have def_d: d = n by rewrite /d def_m gcdnC gcdnE modn_mull gcd0n -[n]prednK.
have: km * m + 2 * b * d = kn * n + d.
  rewrite {}/kn {}/km def_m def_d -mulSnr; case: b; rewrite //= addn0 mul1n.
  by rewrite prednK //; apply: ltn_0dvd m_pos _; rewrite def_m dvdn_mulr.
have{def_m}: kn * d <= m.
  have q_pos : 0 < q by rewrite def_m ltn_0mul n_pos ?andbT in m_pos.
  by rewrite /kn; case b; rewrite def_d def_m leq_pmul2r // leq_pred.
have{def_d}: km * d <= n by rewrite -[n]mul1n def_d leq_pmul2r // leq_b1.
move: km {q}kn m_pos n_pos def_mn0; rewrite {}/d {}/b.
elim: qs m n => [|q qs IHq] n r kn kr n_pos r_pos /=.
  case=> -> -> {m0 n0}; rewrite !addn0 => le_kn_r _ def_d; split=> //.
  have d_pos: 0 < gcdn n r by rewrite ltn_0gcd n_pos.
  have: 0 < kn * n by rewrite def_d ltn_0add d_pos orbT.
  rewrite ltn_0mul n_pos andbT; move/ltn_pmul2l <-.
  by rewrite def_d -addn1 leq_add // mulnCA leq_mul2l le_kn_r orbT.
rewrite !natTrecE; set m:= _ + r; set km := _ * _ + kn; pose d := gcdn m n.
have ->: gcdn n r = d by rewrite [d]gcdnC gcdn_addl_mul.
have m_pos: 0 < m by rewrite ltn_0add r_pos orbT.
have d_pos: 0 < d by rewrite ltn_0gcd m_pos.
move/IHq=> {IHq} IHq le_kn_r le_kr_n def_d; apply: IHq => //; rewrite -/d.
  by rewrite muln_addl leq_add // -mulnA leq_mul2l le_kr_n orbT.
apply: (@addn_injr d); rewrite -!addnA addnn addnCA muln_addr -addnA addnCA.
rewrite /km muln_addl mulnCA mulnA -addnA; congr (_ + _).
by rewrite -def_d addnC -addnA -muln_addl -muln_addr addn_negb -mul2n.
Qed.


Lemma bezoutl : forall m n, m > 0 -> {a | a < m & m %| gcdn m n + a * n}.
Proof.
move=> m n m_pos; case: (egcdnP n m_pos) => km kn def_d lt_kn_m.
exists kn; last by rewrite addnC -def_d dvdn_mull.
apply: leq_ltn_trans lt_kn_m.
by rewrite -{1}[kn]muln1 leq_mul2l ltn_0gcd m_pos orbT.
Qed.

Lemma bezoutr : forall m n, n > 0 -> {a | a < n & n %| gcdn m n + a * m}.
Proof. by move=> m n; rewrite gcdnC; exact: bezoutl. Qed.

(* Back to the gcd. *)

Lemma dvdn_gcd : forall p m n, dvdn p m -> dvdn p n -> dvdn p (gcdn m n).
Proof.
move=> p m n dv_pm dv_pn; case (posnP n) => [->|n_pos]; first by rewrite gcdn0.
case: (bezoutr m n_pos) => // km _; move/(dvdn_trans dv_pn).
by rewrite dvdn_addl // dvdn_mull.
Qed.

Lemma gcdn_mul2l : forall p m n, gcdn (p * m) (p * n) = p * gcdn m n.
Proof.
move=> p m n; case: (posnP p) => [-> //| p_pos].
elim: {m}m.+1 {-2}m n (ltnSn m) => // s IHs m n; rewrite ltnS => le_ms.
rewrite gcdnE (gcdnE m) eqn_mul0 modn_pmul2l // eqn0Ngt p_pos.
case: posnP => // m_pos; apply: IHs; apply: leq_trans le_ms.
exact: ltn_pmod.
Qed.

Lemma gcdn_modr : forall m n, gcdn m (n %% m) = gcdn m n.
Proof. by move=> m n; rewrite {2}(divn_eq n m) gcdn_addl_mul. Qed.

Lemma gcdn_modl: forall m n, gcdn (m %% n) n = gcdn m n.
Proof. by move=> m n; rewrite !(gcdnC _ n) gcdn_modr. Qed.

Lemma gcdnAC : right_commutative gcdn.
Proof.
suff dvd: forall m n p, gcdn (gcdn m n) p %| gcdn (gcdn m p) n.
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

Lemma gcdn_def : forall d m n,
    d %| m -> d %| n -> (forall d', d' %| m -> d' %| n -> d' %| d)
  -> gcdn m n = d.
Proof.
move=> d m n dv_dm dv_dn gdv_d; apply/eqP.
by rewrite eqn_dvd gdv_d /= (dvdn_gcd, dvdn_gcdl, dvdn_gcdr).
Qed.

Lemma gcdn_divnC : forall n m, 0 < n -> 0 < m -> 
   n * (m %/ gcdn n m)  = m * (n %/ gcdn n m).
Proof.
move=> n m n_pos m_pos.
have d_pos: 0 < gcdn n m by rewrite ltn_0gcd n_pos.
case/dvdnP: (dvdn_gcdl n m) => k1 def_n; rewrite {3}def_n.
case/dvdnP: (dvdn_gcdr n m) => k2 def_m; rewrite {1}def_m.
by rewrite !divn_mull // def_n {2}def_m mulnC mulnA mulnAC.
Qed.

(* We derive the lcm directly. *)

Definition lcmn m n := if m * n == 0 then m + n else m * n %/ gcdn m n.

Lemma lcmnC : commutative lcmn.
Proof. by move=> m n; rewrite /lcmn mulnC addnC gcdnC. Qed.

Lemma lcm0n : left_unit 0 lcmn. Proof. done. Qed.
Lemma lcmn0 : right_unit 0 lcmn. Proof. by move=> n; rewrite lcmnC. Qed.

Lemma muln_lcm_gcd : forall m n, m > 0 -> n > 0 -> lcmn m n * gcdn m n = m * n.
Proof.
move=> m n pos_m pos_n; rewrite /lcmn -if_neg -lt0n ltn_0mul pos_m pos_n /=.
apply/eqP; rewrite -dvdn_eq; apply dvdn_mull; exact: dvdn_gcdr.
Qed.

Lemma ltn_0lcm : forall m n, (0 < lcmn m n) = (0 < m) || (0 < n).
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
move=> m n p; case: (posnP m) => [->|m_pos] //.
case: (posnP n) => [->|n_pos]; first by rewrite lcmn0.
case: (posnP p) => [->|pos_p]; first by rewrite !lcmn0.
have mnp_pos : 0 < lcmn n p by rewrite ltn_0lcm n_pos.
have mmn_pos : 0 < lcmn m n by rewrite ltn_0lcm m_pos.
have m_np_pos : 0 < gcdn m (lcmn n p) by rewrite ltn_0gcd m_pos.
have np_pos : 0 < gcdn n p by rewrite ltn_0gcd n_pos.
apply/eqP; rewrite -(eqn_pmul2r m_np_pos) muln_lcm_gcd //.
rewrite -(eqn_pmul2r np_pos) -!mulnA muln_lcm_gcd //.
rewrite muln_gcdl muln_lcm_gcd // (muln_gcdr m) -gcdnA -muln_gcdl.
rewrite -[m * n]muln_lcm_gcd // (mulnC (gcdn m n)) -muln_gcdl.
by rewrite !mulnA muln_lcm_gcd // -!mulnA (mulnC p) !mulnA muln_lcm_gcd.
Qed.

(* Coprime factors *)

Definition coprime m n := gcdn m n == 1.

Lemma coprime1n : forall n, coprime 1 n.
Proof. by move=> n; rewrite /coprime gcd1n. Qed.

Lemma coprimen1 : forall n, coprime n 1.
Proof. by move=> n; rewrite /coprime gcdn1. Qed.

Lemma coprime_sym : forall m n, coprime m n = coprime n m.
Proof. by move => m n; rewrite /coprime gcdnC. Qed.

Lemma coprimeP : forall n m, n > 0 ->
  reflect (exists u, u.1 * n - u.2 * m = 1) (coprime n m).
Proof.
move=> n m pn; apply: (iffP eqP).
  by move<-; case:(egcdnP m pn) => kn km kg _; exists (kn, km); rewrite kg addKn.
case=> [[kn km]] /= E; apply gcdn_def; rewrite ?dvd1n // => d dn dm.
by rewrite -E dvdn_subr ?dvdn_mull // ltnW // -ltn_0sub E.
Qed.

Lemma modn_coprime : forall k n, (O < k) ->
  (exists u, (k * u) %% n = 1%N) -> coprime k n.
Proof.
move=> k n Hpos [u Hu]; apply/coprimeP; first by trivial.
case: (divn_eq (k * u) n); exists (u,(k * u)%/ n)=>/=.
rewrite {1}mulnC {1}H addnC.
by rewrite -addn_subA 1?leq_eqVlt ?eqxx ?orTb // subnn addn0 Hu.
Qed.

Lemma prime_coprime : forall p m, prime p -> coprime p m = ~~ dvdn p m.
Proof.
move=> p m; case/primeP=> p_gt1 p_pr; apply/eqP/negP=> [d1 | ndv_pm].
  case/dvdnP=> k def_m; rewrite -(addn0 m) def_m gcdn_addl_mul gcdn0 in d1.
  by rewrite d1 in p_gt1.
apply: gcdn_def => // d; move/p_pr.
by case/orP; move/eqP => -> //; rewrite ndv_pm.
Qed.


Lemma gauss : forall m n p, coprime m n -> (m %| n * p) = (m %| p).
Proof.
move => m n p co_mn; apply/idP/idP; last by auto.
move/eqnP: co_mn; case: (posnP m) => [->|]; first by case n; case p.
case/(bezoutl n)=> k _ dv_mk co_mn; move/(dvdn_mulr k).
rewrite mulnC mulnA => dv_m_knp.
by move/(dvdn_mulr p): dv_mk; rewrite co_mn muln_addl mul1n dvdn_addl.
Qed.

Lemma gauss_inv : forall m n p,
  coprime m n -> (m * n %| p) = (m %| p) && (n %| p).
Proof.
move=> m n p co_mn; apply/idP/andP => [dv_mn_p| []].
  by split; apply: dvdn_trans dv_mn_p; auto.
case/dvdnP=> k1 ->; rewrite mulnC gauss; last by rewrite coprime_sym.
by case: (posnP m) => [-> //| m_pos]; rewrite dvdn_pmul2l.
Qed.

Lemma gauss_gcdr : forall p m n, coprime p m -> gcdn p (m * n) = gcdn p n.
Proof.
move=> p m n co_pm; symmetry; apply gcdn_def; first exact: dvdn_gcdl.
  rewrite -(@gauss _ m); first exact: dvdn_gcdr.
  by rewrite /coprime gcdnAC (eqnP co_pm) gcd1n.
by move=> d dv_dp dv_dn; apply dvdn_gcd => //; rewrite dvdn_mull.
Qed.

Lemma gauss_gcdl : forall p m n, coprime p n -> gcdn p (m * n) = gcdn p m.
Proof. by move=> *; rewrite mulnC gauss_gcdr. Qed.

Lemma euclid : forall m n p, prime p -> (p %| m * n) = (p %| m) || (p %| n).
Proof.
move => m n p pr_p; case dv_pm: (p %| m); first exact: dvdn_mulr.
by rewrite gauss // prime_coprime // dv_pm.
Qed.

Lemma coprime_mulr : forall p m n,
  coprime p (m * n) = coprime p m && coprime p n.
Proof.
move=> p m n.
case co_pm: (coprime p m) => /=; first by rewrite /coprime gauss_gcdr ?co_pm.
apply/eqP=> co_p_mn; case/eqnP: co_pm; apply gcdn_def => // d dv_dp dv_dm.
by rewrite -co_p_mn dvdn_gcd // dvdn_mulr.
Qed.

Lemma coprime_mull : forall p m n,
  coprime (m * n) p = coprime m p && coprime n p.
Proof. move=> p m n; rewrite !(coprime_sym _ p); exact: coprime_mulr. Qed.

Lemma coprime_pexpl : forall k m n, 0 < k -> coprime (m ^ k) n = coprime m n.
Proof.
case=> // k m n _; elim: k => [|k IHk]; first by rewrite expn1.
by rewrite expnS coprime_mull -IHk; case coprime.
Qed.

Lemma coprime_pexpr : forall k m n, 0 < k -> coprime m (n ^ k) = coprime m n.
Proof. by move=> k m n k_pos; rewrite !(coprime_sym m) coprime_pexpl. Qed.

Lemma coprime_expl : forall k m n, coprime m n -> coprime (m ^ k) n.
Proof. by case=> [|k] p m co_pm; rewrite (coprime1n, coprime_pexpl). Qed.

Lemma coprime_expr : forall k m n, coprime m n -> coprime m (n ^ k). 
Proof. by move=> k m n; rewrite !(coprime_sym m); exact: coprime_expl. Qed.

Lemma coprime_egcdn : forall n m, n > 0 ->
    coprime (egcdn n m).1 (egcdn n m).2.
Proof.
move=> n m pn; case: (egcdnP m pn)=> kn km; case Ekn: kn =>[|k].
  rewrite mul0n; move/eqP; rewrite eq_sym eqn_add0 (eqn0Ngt (gcdn _ _)) ltn_0gcd.
  by rewrite pn andbF.
case/dvdnP: (dvdn_gcdl n m)=> an Ean; case/dvdnP: (dvdn_gcdr n m)=> am Eam Eg _.
apply/coprimeP=> //; exists (an, am); apply/eqP => /=.
rewrite  -(@eqn_pmul2r (gcdn n m)) ?ltn_0gcd ?pn // mul1n muln_subl.
by rewrite (mulnC an) -mulnA -{1}Ean Eg {1}Eam mulnA (mulnC km) addKn.
Qed.



(* Symmetrical Bezout coefficients (used for p-components in frobenius). *)

Definition abezoutn m n :=
  if m > 0 then let: (km, kn) := egcdn m n in (km, m.-1 * kn) else (0, 1).

Lemma abezout_modn : forall m n,
  let: (u, v) := abezoutn m n in 
  (u * m + v * n) %% (m * n) = gcdn m n %% (m * n).
Proof.
rewrite /abezoutn => m n; case: posnP => [->|m_pos].
  by rewrite /= !modn0 gcd0n mul1n.
case: egcdnP => //= km kn -> _.
by rewrite -mulnA addnAC -mulSn prednK // mulnCA modn_addl_mul.
Qed.

Lemma abezout_coprime: forall n m, 1 < m * n -> coprime m n -> 
  let: (u, v) := abezoutn m n in (u * m + v * n) %% (m * n) = 1.
Proof.
move=> n m mn_gt1 co_mn; case: abezoutn (abezout_modn m n) => u v ->.
by rewrite (eqnP co_mn) modn_small.
Qed.


Section Chinese.

(***********************************************************************)
(*   The chinese remainder theorem                                     *)
(***********************************************************************)

Variables m1 m2 : nat.
Hypotheses (m1_pos : 0 < m1) (m2_pos : 0 < m2) (co_m12 : coprime m1 m2).

Lemma chinese_remainder : forall x y,
  (x %% (m1 * m2) == y %% (m1 * m2)) =
     (x %% m1 == y %% m1) && (x %% m2 == y %% m2).
Proof.
move=> x y; wlog le_yx : x y / y <= x.
  by case/orP: (leq_total y x); last rewrite !(eq_sym (x %% _)); auto.
by rewrite !eqn_mod_dvd // gauss_inv.
Qed.

(***********************************************************************)
(*   A function that solves the chinese remainder problem              *)
(***********************************************************************)

Definition chinese r1 r2 :=
  r1 * m2 * (egcdn m2 m1).1 + r2 * m1 * (egcdn m1 m2).1.

Lemma chinese_modl : forall r1 r2, chinese r1 r2 %% m1 = r1 %% m1.
Proof.
rewrite /chinese; case: egcdnP=> // k2 k1 def_m1 _ r1 r2.
rewrite mulnAC -mulnA def_m1 gcdnC (eqnP co_m12) muln_addr mulnA muln1.
by rewrite addnAC (mulnAC _ m1) -muln_addl modn_addl_mul.
Qed.

Lemma chinese_modr : forall r1 r2, chinese r1 r2 %% m2 = r2 %% m2.
Proof.
rewrite /chinese; case: (egcdnP m2) => // k1 k2 def_m2 _ r1 r2.
rewrite addnC mulnAC -mulnA def_m2 (eqnP co_m12) muln_addr mulnA muln1.
by rewrite addnAC (mulnAC _ m2) -muln_addl modn_addl_mul.
Qed.

Lemma chinese_remainderf : forall x,
  x %% (m1 * m2) = chinese (x %% m1) (x %% m2) %% (m1 * m2).
Proof.
move=> x; apply/eqP.
by rewrite chinese_remainder // chinese_modl chinese_modr !modn_mod !eqxx.
Qed.

End Chinese.

(* "prime" logarithms and p-parts. *)

Fixpoint logn_rec (d m r : nat) {struct r} : nat :=
  match r, edivn m d with
  | r'.+1, (_.+1 as m', 0) => (logn_rec d m' r').+1
  | _, _ => 0
  end.

Definition logn p m := if prime p then logn_rec p m m else 0.

Lemma lognE : forall p m,
  logn p m = if [&& prime p, 0 < m & p %| m] then (logn p (m %/ p)).+1 else 0.
Proof.
rewrite /logn /dvdn => p m; case p_pr: (prime p) => //.
rewrite /divn modn_def; case def_m: {2 3}m => [|m'] //=.
case: edivnP def_m => [[|q] [|r] -> _] // def_m; congr _.+1; rewrite [_.1]/=.
have{m def_m}: q < m'.
  by rewrite -ltnS -def_m addn0 mulnC -{1}[q.+1]mul1n ltn_pmul2r // prime_gt1.
elim: {m' q}_.+1 {-2}m' q.+1 (ltnSn m') (ltn0Sn q) => // s IHs.
case=> [[]|r] //= m; rewrite ltnS => lt_rs m_pos le_mr.
rewrite -{3}[m]prednK //=; case: edivnP => [[|q] [|_] def_q _] //.
have{def_q} lt_qm': q < m.-1.
  by rewrite -[q.+1]muln1 -ltnS prednK // def_q addn0 ltn_pmul2l // prime_gt1.
have{le_mr} le_m'r: m.-1 <= r by rewrite -ltnS prednK.
by rewrite (IHs r) ?(IHs m.-1) // ?(leq_trans lt_qm', leq_trans _ lt_rs).
Qed.

Lemma dvdn_exp_max : forall p n m,
  prime p -> m > 0 -> (p ^ n %| m) = (n <= logn p m).
Proof.
move=> p n m p_pr; elim: {m}m.+1 {-2}m (ltnSn m) n => // s IHs m.
rewrite lognE ltnS p_pr /= => le_ms [|n] m_pos; first by rewrite dvd1n.
rewrite m_pos /=; case dv_pm: (p %| m); last first.
  by apply/dvdnP=> [] [/= q def_m]; rewrite def_m mulnCA dvdn_mulr in dv_pm.
have [mp_pos p_pos]: 0 < m %/ p /\ 0 < p.
   by apply/andP; rewrite -ltn_0mul divnK.
rewrite -{1}(divnK dv_pm) mulnC expnS dvdn_pmul2l // IHs //.
apply: leq_trans le_ms; case/dvdn_lt: dv_pm => //; exact: prime_gt1.
Qed.

Definition p_part p m := p ^ logn p m.

Lemma dvdn_p_part : forall p m, p_part p m %| m.
Proof.
rewrite /p_part => p [|m] //.
by case p_pr: (prime p); [rewrite dvdn_exp_max | rewrite lognE p_pr].
Qed.

Lemma dvdn_p_p_part : forall p m, prime p -> (p * p_part p m %| m) = (m == 0).
Proof. by move=> p [|m] p_pr; rewrite ?dvdn0 // -expnS dvdn_exp_max ?ltnn. Qed.

Lemma dvdn_leq_log : forall p m n,
  prime p -> 0 < n -> m %| n -> logn p m <= logn p n.
Proof.
move=> p m n p_pr n_pos; rewrite -dvdn_exp_max //.
apply: dvdn_trans; exact: dvdn_p_part.
Qed.

Lemma logn_exp : forall p n, prime p -> logn p (p ^ n) = n.
Proof.
move=> p n p_pr; elim: n => [|n IHn]; rewrite /= lognE p_pr.
  by rewrite dvdn1 /= eqn_leq leqNgt prime_gt1.
by rewrite ltn_0mul ltn_0exp divn_mulr ltn_0prime // IHn dvdn_mulr.
Qed.

Lemma logn_gauss : forall p m n, coprime p m -> logn p (m * n) = logn p n.
Proof.
move=> p m n co_pm; elim: {n}n.+1 {-2}n (ltnSn n) => // s IHs.
case=> [|n]; rewrite ?muln0 // ltnS => le_ns.
rewrite lognE (lognE p n.+1) gauss //= ltn_0mul andbT.
case p_pr: (prime p) => //; case: posnP => [m0 | _].
  by rewrite prime_coprime // m0 dvdn0 in co_pm.
case dv_pn: (p %| _) => //=.
rewrite -{1}(divnK dv_pn) mulnA divn_mull (ltn_0prime, IHs) //.
apply: leq_trans le_ns; case/dvdn_lt: dv_pn => //; exact: prime_gt1.
Qed.

Lemma p_part_coprime : forall p m, prime p -> m > 0 ->
  {q | coprime p q & m = q * p_part p m}.
Proof.
move=> p m p_pr m_pos; have def_m := divnK (dvdn_p_part p m).
have mp_pos: 0 < p_part p m by rewrite ltn_0exp ltn_0prime.
exists (m %/ p_part p m) => //; rewrite prime_coprime //.
by rewrite -(dvdn_pmul2r mp_pos) def_m dvdn_p_p_part // -lt0n.
Qed.

Lemma logn_mul : forall p m n,
  prime p -> 0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n.
Proof.
move=> p m n p_pr m_pos n_pos.
have [qm co_pqm def_m] := p_part_coprime p_pr m_pos.
have [qn co_pqn def_n] := p_part_coprime p_pr n_pos.
rewrite {1}def_m -mulnA logn_gauss // {1}def_n mulnCA logn_gauss //.
by rewrite -expn_add logn_exp // prime_gt1.
Qed.

Lemma dvdn_exp_prime: forall p d n, prime p -> 
  reflect (exists2 m, m <= n & d = p ^ m) (d %| p ^ n).
Proof.
move=> p d n p_pr; case: (primeP p_pr) => p_gt1 dv_p; have p_pos := ltnW p_gt1.
apply: (iffP dvdnP) => [[q def_q] | [m le_mn def_d]]; last first.
  by exists (p ^ (n - m)); rewrite def_d -expn_add addnC subnK.
have pn_pos: 0 < p ^ n by rewrite ltn_0exp p_pos.
have [q_pos d_pos]: 0 < q /\ 0 < d by apply/andP; rewrite -ltn_0mul -def_q.
move: (logn_exp n p_pr); rewrite def_q logn_mul // => def_n.
exists (logn p d); first by rewrite -def_n leq_addl.
apply/eqP; rewrite eqn_dvd -(dvdn_pmul2l q_pos) -def_q -def_n mulnC expn_add.
by rewrite mulnC dvdn_pmul2l ?(ltn_0exp, p_pos) // !dvdn_p_part.
Qed.
