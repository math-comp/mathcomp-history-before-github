(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq paths div ssralg.
Require Import bigops.

(**************************************************************************)
(* This files contains the definitions of:                                *)
(* -primality: prime p <=> p is prime                                     *)
(*             primes m == the list of prime divisors of m if m > 0       *)
(*             prime_decomposition m == self-explanatory                  *)
(* -powers: logn p m == the number of times p divides m                   *)
(*          p_part p m == p ^ (logn p m)                                  *)
(*          pi_part p m == \prod_(p <- primes n | pi p) p_part p n        *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition prime p := divisors p == [:: 1; p].
Definition primes m := filter prime (divisors m).

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
Proof. by move=> m; move/ltn_0prime. Qed.

Definition prime_pos_nat m (H:prime m) := PosNat (prime_pos_natP H).

Lemma even_prime : forall p, prime p -> p = 2 \/ odd p.
Proof.
move=> p pr_p; case odd_p: (odd p); [by right | left].
have: 2 %| p by rewrite dvdn2_even odd_p.
by case/primeP: pr_p => _ dv_p; move/dv_p; move/(2 =P p).
Qed.

Lemma mem_primes : forall p n,
  (p \in primes n) = [&& prime p, n > 0 & p %| n].
Proof.
move=> p n; rewrite mem_filter; case prime => //.
by case: posnP => [-> //| n_pos]; rewrite dvdn_divisors.
Qed.

Lemma sorted_primes : forall n, sorted ltn (primes n).
Proof. by move=> n; rewrite !(sorted_filter ltn_trans, sorted_ltn_iota). Qed.

Lemma eq_primes : forall m n, (primes m =i primes n) <-> (primes m = primes n).
Proof.
move=> m n; split=> [eqpr| -> //].
by apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes.
Qed.


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


Lemma prime_coprime : forall p m, prime p -> coprime p m = ~~ dvdn p m.
Proof.
move=> p m; case/primeP=> p_gt1 p_pr; apply/eqP/negP=> [d1 | ndv_pm].
  case/dvdnP=> k def_m; rewrite -(addn0 m) def_m gcdn_addl_mul gcdn0 in d1.
  by rewrite d1 in p_gt1.
apply: gcdn_def => // d; move/p_pr.
by case/orP; move/eqP => -> //; rewrite ndv_pm.
Qed.


Lemma euclid : forall m n p, prime p -> (p %| m * n) = (p %| m) || (p %| n).
Proof.
move => m n p pr_p; case dv_pm: (p %| m); first exact: dvdn_mulr.
by rewrite gauss // prime_coprime // dv_pm.
Qed.


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

Lemma ltn_0log : forall p n, (0 < logn p n) = (p \in primes n).
Proof. by move=> p n; rewrite lognE -mem_primes; case: {+}(p \in _). Qed.

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

Lemma logn_exp : forall p n, prime p -> logn p (p ^ n) = n.
Proof.
move=> p n p_pr; elim: n => [|n IHn]; rewrite /= lognE p_pr.
  by rewrite dvdn1 /= eqn_leq leqNgt prime_gt1.
by rewrite ltn_0mul ltn_0exp divn_mulr ltn_0prime // IHn dvdn_mulr.
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

Lemma p_part_0 : forall p, p_part p 0 = 1.
Proof. by move=> p; rewrite /p_part lognE andbF. Qed.

Lemma p_part_1 : forall p, p_part p 1 = 1.
Proof. by move=> p; rewrite /p_part lognE andbC dvdn1; case: eqP => // ->. Qed.

Lemma dvdn_p_part : forall p m, p_part p m %| m.
Proof.
rewrite /p_part => p [|m] //.
by case p_pr: (prime p); [rewrite dvdn_exp_max | rewrite lognE p_pr].
Qed.

Lemma dvdn_p_p_part : forall p m, prime p -> (p * p_part p m %| m) = (m == 0).
Proof. by move=> p [|m] p_pr; rewrite ?dvdn0 // -expnS dvdn_exp_max ?ltnn. Qed.

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

Lemma p_part_mul : forall p m n,
  m > 0 -> n > 0 -> p_part p (m * n) = p_part p m * p_part p n.
Proof.
move=> p m n m_pos n_pos; rewrite /p_part; case p_pr: (prime p).
  by rewrite logn_mul // expn_add.
by do 3!rewrite lognE p_pr /=.
Qed.

Lemma p_part_exp : forall p m n, p_part p (m ^ n) = p_part p m ^ n.
Proof.
move=> p m n; case: (posnP m) => [->|m_pos] //.
  by case: n => [|n]; rewrite !(p_part_0, p_part_1) ?exp1n.
elim: n => // [|n IHn]; first by rewrite p_part_1.
by rewrite expnS p_part_mul ?(IHn, ltn_0exp, m_pos).
Qed.

Lemma dvdn_leq_log : forall p m n,
  prime p -> 0 < n -> m %| n -> logn p m <= logn p n.
Proof.
move=> p m n p_pr n_pos; rewrite -dvdn_exp_max //.
apply: dvdn_trans; exact: dvdn_p_part.
Qed.

Lemma p_part_prime : forall p q, prime q ->
  p_part p q = (if p == q then p else 1).
Proof.
move=> p q pr_q; rewrite /p_part lognE ltn_0prime //=.
case pr_p: (prime p); last by case: eqP pr_p pr_q => // -> ->.
rewrite dvdn_divisors (ltn_0prime, (_ =P [:: 1; q]) pr_q) // mem_seq2.
case: eqP => [-> | _]; first by rewrite exp1n if_same.
by case: eqP => // ->; rewrite divnn ?(ltn_0prime, logn_exp 0, expn1).
Qed.

Lemma p_part_id : forall p q n, prime q ->
  p_part p (p_part q n) = (if p == q then p_part q n else 1).
Proof.
move=> p q n pr_p; rewrite p_part_exp p_part_prime //.
by case: eqP => [->|_]; rewrite ?exp1n.
Qed.

Lemma primes_mul : forall m n p, m > 0 -> n > 0 ->
  (p \in primes (m * n)) = (p \in primes m) || (p \in primes n).
Proof.
move=> m n p m_pos n_pos.
wlog pr_p: / prime p by rewrite !mem_filter; case pp: (prime p); auto.
by rewrite -!ltn_0log -ltn_0add logn_mul.
Qed.

Lemma primes_exp : forall m n, n > 0 -> primes (m ^ n) = primes m.
Proof.
move=> m [|n] // _; case: (posnP m) => [-> //| m_pos]; apply/eq_primes => /= p.
elim: n => [|n IHn]; first by rewrite expn1.
by rewrite expnS primes_mul ?(IHn, orbb, ltn_0exp, m_pos).
Qed.

Lemma primes_prime : forall p, prime p -> primes p = [::p].
Proof.
move=> p pr_p; apply: (eq_sorted_irr ltn_trans ltnn) => // [|q].
  exact: sorted_primes.
rewrite mem_seq1 mem_primes ltn_0prime //=.
apply/andP/eqP=> [[pr_q q_p] | -> //].
case: (primeP pr_p) => _ dv_p; case/orP: (dv_p _ q_p); move/eqP=> // q1.
by rewrite q1 in pr_q.
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


Lemma primes_p_part : forall p n,
  primes (p_part p n) = seqn (p \in primes n) p.
Proof.
move=> p n; rewrite /p_part lognE mem_primes.
case: and3P => [[pr_p n_pos p_n]| //].
by rewrite primes_exp //= primes_prime.
Qed.

Lemma prod_p_parts : forall n, n > 0 ->
  \prod_(p <- primes n) p_part p n = n.
Proof.
move=> n; elim: {n}_.+1 {-2}n (ltnSn n) => // m IHm n; rewrite ltnS => le_nm.
move=> n_pos; case: (leqP n 1) => [le_n1 | lt_1n].
  by rewrite ((n =P 1) _) ?big_seq0 // eqn_leq le_n1.
pose p := pdiv n; have pr_p: prime p by rewrite prime_pdiv.
case: (p_part_coprime pr_p n_pos) => n'; rewrite prime_coprime //.
move/negPf=> p_n' def_n; rewrite {3}def_n mulnC.
have:= n_pos; rewrite {1}def_n ltn_0mul; case/andP=> n'_pos pn_pos.
have def_prn: primes n = p :: primes n'.
  apply: (eq_sorted_irr ltn_trans ltnn); first exact: sorted_primes.
    case def_s: (primes n') (sorted_primes n') => //= [q s] ->.
    have [pr_q _ q_n']: [/\ prime q, n' > 0 & q %| n'].
      by apply/and3P; rewrite -mem_primes def_s mem_head.
    rewrite ltn_neqAle pdiv_min_dvd ?andbT ?prime_gt1 //.
      by apply/eqP=> def_p; rewrite def_p q_n' in p_n'.
    by rewrite def_n dvdn_mulr.
  move=> q; rewrite inE def_n primes_mul // orbC; congr (_ || _).
  by rewrite primes_p_part mem_primes pr_p n_pos dvdn_pdiv mem_seq1.
rewrite def_prn big_adds big_cond_seq; congr (_ * _).
rewrite (eq_bigr (p_part^~ n')) => [|q /=]; last first.
  rewrite inE /= => pr_q; rewrite def_n p_part_mul // p_part_id //.
  case: eqP => [def_q | _]; last by rewrite muln1.
  by rewrite mem_primes def_q p_n' !andbF in pr_q.
rewrite -big_cond_seq {}IHm //; apply: leq_trans le_nm.
rewrite -(muln1 n') def_n ltn_pmul2l //.
by rewrite -(expn0 p) ltn_exp2l ?prime_gt1 // lognE pr_p n_pos dvdn_pdiv.
Qed.


Definition pi_part pi n := (\prod_(p <- primes n | pi p) p_part p n)%N.

Lemma ltn_0p_part : forall p n, 0 < p_part p n.
Proof.
move=> p n; rewrite ltn_0exp lognE.
by case pr_p: (prime p); rewrite (orbT, ltn_0prime).
Qed.

Lemma primes_pi_part :
  forall pi n, primes (pi_part pi n) = filter pi (primes n).
Proof.
rewrite /pi_part => pi n; have ltnT := ltn_trans.
case: (posnP n) => [-> | n_pos]; first by rewrite big_seq0. 
apply: (eq_sorted_irr ltnT ltnn); rewrite ?(sorted_primes, sorted_filter) //.
move=> p; rewrite (mem_filter pi); set pn := primes n.
case pr_p: (prime p); last by rewrite !mem_primes pr_p !andbF.
have: all (mem pn) pn by apply/allP.
elim: {-1}pn => [|q pn' IHn] /=; first by rewrite big_seq0 andbF.
case/andP => pn_q pn_pn'; rewrite big_adds inE; case pi_q: (pi q); last first.
  by case: eqP => //= def_q; rewrite IHn // def_q pi_q.
rewrite primes_mul ?ltn_0p_part //; last first.
  by apply big_prop => // ? ?; rewrite (ltn_0mul, ltn_0p_part) // => ->.
rewrite primes_p_part {}IHn // pn_q mem_seq1.
by case: eqP => //= ->; rewrite pi_q.
Qed.

Lemma pi_partC : forall pi n,
  n > 0 -> (pi_part pi n * pi_part (predC pi) n = n)%N.
Proof.
move=> pi n n_pos; rewrite {2}/pi_part -big_filter.
rewrite /pi_part -big_filter -big_cat /= -{4}(prod_p_parts n_pos).
apply: eq_big_perm; apply/allP=> p _; apply/eqP.
rewrite count_cat 2!count_filter; do 2!rewrite -filter_predI -count_filter.
rewrite -count_predUI addnC (@eq_count _ _ pred0) => [|q] /=; last first.
  by case: (pi q); rewrite !andbF.
by rewrite count_pred0; apply: eq_count => q /=; rewrite -andb_orr orbN andbT.
Qed.

Lemma pi_part_mul : forall pi m n, m * n > 0 ->
  pi_part pi (m * n) = pi_part pi m * pi_part pi n.
Proof.
move=> pi.
have widen: forall m n, n > 0 ->
  pi_part pi m = \prod_(p <- primes (m * n) | pi p) p_part p m.
- move=> m n n_pos; case: (posnP m) => [-> //| m_pos].
  rewrite -big_filter -!filter_predI big_filter big_mkcond /=.
  rewrite /pi_part -big_filter -!filter_predI big_filter.
  rewrite  -{1}(addnK 1 m) (big_nat_widen 1 _ (m * n + 1)); last first.
    by rewrite leq_add2r -{1}(muln1 m) leq_pmul2l.
  rewrite /index_iota addnK big_mkcond /=.
  apply: eq_bigr => p _; case: (@andP _ (prime p)) => // [[_ pr_p]].
  rewrite euclid //; case p_n: (p %| m) => /=.
    by rewrite addn1 ltnS dvdn_leq.
  by rewrite /p_part lognE p_n !andbF if_same.
move=> m n; rewrite ltn_0mul; case/andP=> m_pos n_pos.
rewrite (widen m n) // (widen n m) // (mulnC n) -big_split /=.
by apply: eq_bigr => p _; rewrite p_part_mul.
Qed.
