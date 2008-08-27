(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq paths fintype.
Require Import div ssralg bigops.

(**************************************************************************)
(* This files contains the definitions of:                                *)
(* -primality: prime p <=> p is prime                                     *)
(*             primes m == the list of prime divisors of m if m > 0       *)
(*             pfactor == the type of prime factors (p ^ e)%pfactor       *)
(*             prime_decomp m == the list of prime factors of m           *)
(*             pdiv n == the smallest prime divisor of n                  *)
(*             divisors m     == the (sorted) list of divisors of m       *)
(* -powers: logn p m == the number of times p divides m, if p is prime    *)
(*          p_part p m == p ^ (logn p m)                                  *)
(*          pi_part p m == \prod_(p <- primes n | pi p) p_part p n        *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The complexity of any arithmetic operation with the Peano representation *)
(* is pretty dreadful, so using algorithms for "harder" problems such as    *)
(* factoring, that are geared for efficient artihmetic leads to dismal      *)
(* performance -- it takes a significant time, for instance, to compute the *)
(* divisors of just a two-digit number. On the other hand, for Peano        *)
(* integers, prime factoring (and testing) is linear-time with a small      *)
(* constant factor -- indeed, the same as converting in and out of a binary *)
(* representation. This is implemented by the code below, which is then     *)
(* used to give the "standard" definitions of prime, primes, and divisors,  *)
(* which can then be used casually in proofs with moderately-sized numeric  *)
(* values (indeed, the code here performs well for up to 6-digit numbers).  *)

(* We start with faster mod-2 functions. *)

Fixpoint edivn2 (q r : nat) {struct r} :=
  if r is r'.+2 then edivn2 q.+1 r' else (q, r).

Lemma edivn2P : forall n, edivn_spec n 2 (edivn2 0 n).
Proof.
move=> n; rewrite -[n]odd_double_half addnC -{1}[n./2]addn0 -{1}mul2n mulnC.
elim: n./2 {1 4}0 => [|r IHr] q; first by case (odd n) => //=.
rewrite addSnnS; exact: IHr.
Qed.

Fixpoint elogn2 (e q r : nat) {struct q} :=
  match q, r with
  | 0, _ | _, 0 => (e, q)
  | q'.+1, 1 => elogn2 e.+1 q' q'
  | q'.+1, r'.+2 => elogn2 e q' r'
  end.

CoInductive elogn2_spec n : nat * nat -> Type :=
  Elogn2Spec e m of n = 2 ^ e * m.*2.+1 : elogn2_spec n (e, m).

Lemma elogn2P : forall n, elogn2_spec n.+1 (elogn2 0 n n).
Proof.
move=> n; rewrite -{1}[n.+1]mul1n -[1]/(2 ^ 0) -{1}(addKn n n) addnn.
elim: n {1 4 6}n {2 3}0 (leqnn n) => [|q IHq] [|[|r]] e //=; last first.
  by move/ltnW; exact: IHq.
clear 1; rewrite subn1 -[_.-1.+1]doubleS -mul2n mulnA -expnSr.
rewrite -{1}(addKn q q) addnn; exact: IHq.
Qed.

Definition ifnz T n (x y : T) := if n is 0 then y else x.

CoInductive ifnz_spec T n (x y : T) : T -> Type :=
  | IfnzPos of n > 0 : ifnz_spec n x y x
  | IfnzZero of n = 0 : ifnz_spec n x y y.

Lemma ifnzP : forall T n (x y : T), ifnz_spec n x y (ifnz n x y).
Proof. by move=> T [|n] *; [right | left]. Qed.

Inductive pfactor : Type := Pfactor of nat & nat.
Delimit Scope pfactor_scope with pfactor.
Bind Scope pfactor_scope with pfactor.
Infix "^" := Pfactor : pfactor_scope.
Open Local Scope pfactor_scope.

Definition pfactor_base pf := let: p ^ _ := pf in p.
Coercion nat_of_pfactor pf := let: p ^ e := pf in (p ^ e)%N.

(* For pretty-printing. *)
Definition NumFactor pf := let: p ^ e := pf in ([Num of p], e).

Definition eq_pfactor pf1 pf2 :=
  match pf1, pf2 with p1 ^ e1, p2 ^ e2 => (p1 == p2) && (e1 == e2) end.

Lemma eq_pfactorP : reflect_eq eq_pfactor.
Proof.
by move=> [p1 e1] [p2 e2]; apply: (iffP (pair_eqP (_,_) (_,_))) => [] [-> ->].
Qed.

Canonical Structure pfactor_eqType := EqClass (EqMixin eq_pfactorP).

Definition cons_pfactor p e pd := ifnz e (p ^ e :: pd) pd.

Notation Local "p ^? e :: pd" := (cons_pfactor p e pd)
  (at level 30, e at level 30, pd at level 60) : pfactor_scope.

Section prime_decomp.

Import NatTrec.

Fixpoint prime_decomp_rec (m k a b c e : nat) {struct a} :=
  let p := k.*2.+1 in
  if a is a'.+1 then
    if b - (ifnz e 1 k - c) is b'.+1 then
      [rec m, k, a', b', ifnz c c.-1 (ifnz e p.-2 1), e] else
    if (b == 0) && (c == 0) then
      let b' := k + a' in [rec b'.*2.+3, k, a', b', k.-1, e.+1] else
    let bc' := ifnz e (ifnz b (k, 0) (edivn2 0 c)) (b, c) in
    p ^? e :: ifnz a' [rec m, k.+1, a'.-1, bc'.1 + a', bc'.2, 0] [:: m ^ 1]
  else if (b == 0) && (c == 0) then [:: p ^ e.+2] else p ^? e :: [:: m ^ 1]
where "[ 'rec' m , k , a , b , c , e ]" := (prime_decomp_rec m k a b c e).

Definition prime_decomp n :=
  let: (e2, m2) := elogn2 0 n.-1 n.-1 in
  if m2 < 2 then 2 ^? e2 :: 3 ^? m2 :: [::] else
  let: (a, bc) := edivn m2.-2 3 in
  let: (b, c) := edivn (2 - bc) 2 in
  2 ^? e2 :: [rec m2.*2.+1, 1, a, b, c, 0].

(* The list of divisors is computed directly from the decomposition,   *)
(* using a merge_sort variant to obtain a sorted list.                 *)

Definition add_divisors pe divs :=
  let: p ^ e := pe in 
  let add1 divs' := merge leq (maps (NatTrec.mul p) divs') divs in
  iter e add1 divs.

End prime_decomp.

Definition primes n := maps pfactor_base (prime_decomp n).

Definition prime p := if prime_decomp p is [:: _ ^ 1] then true else false.

Definition pdiv n := head n (primes n).

Definition divisors n := foldr add_divisors [:: 1] (prime_decomp n).

Lemma prime_decomp_correct :
  let pd_val (pd : seq pfactor) := \prod_(pf <- pd) pf in 
  let lb_dvd q m := ~~ has [pred d | d %| m] (index_iota 2 q) in
  let pf_ok pf := let: p ^ e := pf in lb_dvd p p && (0 < e) in
  let pd_ord q pd := path ltn q (maps pfactor_base pd) in
  let pd_ok q n pd := [/\ n = pd_val pd, all pf_ok pd & pd_ord q pd] in
  forall n, n > 0 -> pd_ok 1 n (prime_decomp n).
Proof.
rewrite unlock => pd_val lb_dvd pf_ok pd_ord pd_ok.
have leq_pd_ok : forall m p q pd, q <= p -> pd_ok p m pd -> pd_ok q m pd.
  rewrite /pd_ok /pd_ord => m p q [|[r _] pd] //= leqp [<- ->].
  by case/andP; move/(leq_trans _)=> ->. 
have apd_ok: forall m e q p pd, lb_dvd p p || (e == 0) -> q < p ->
     pd_ok p m pd -> pd_ok q (p ^ e * m) (p ^? e :: pd).
- move=> m [|e] q p pd; rewrite orbC /= => pr_p ltqp.
    rewrite mul1n; apply: leq_pd_ok; exact: ltnW.
  by rewrite /pd_ok /pd_ord /= pr_p ltqp => [[<- -> ->]].
case=> // n _; rewrite /prime_decomp.
case: elogn2P => e2 m2 -> {n}; case: m2 => [|[|abc]]; try exact: apd_ok.
rewrite [_.-2]/= !ltnS ltn0 natTrecE; case: edivnP => a bc ->{abc}.
case: edivnP => b c def_bc /= ltc2 ltbc3; apply: (apd_ok) => //.
move def_m: _.*2.+1 => m; set k := {2}1; rewrite -[2]/k.*2; set e := 0.
pose p := k.*2.+1; rewrite -{1}[m]mul1n -[1]/(p ^ e)%N.
have{def_m bc def_bc ltc2 ltbc3}:
   let kb := (ifnz e k 1).*2 in
   [&& k > 0, p < m, lb_dvd p m, c < kb & lb_dvd p p || (e == 0)]
    /\ m + (b * kb + c).*2 = p ^ 2 + (a * p).*2.
- rewrite -{-2}def_m; split=> //=; last first.
    by rewrite -def_bc addSn -double_add 2!addSn -addnA addnC subnK.
  rewrite ltc2 /lb_dvd /index_iota /= dvdn2_even -def_m.
  by rewrite [_.+2]lock /= odd_double.
move: {2}a.+1 (ltnSn a) => n; clearbody k e.
elim: n => // n IHn in a k p m b c e *; rewrite ltnS => le_a_n [].
set kb := _.*2; set d := _ + c.
case/and5P=> lt0k ltpm leppm ltc pr_p def_m; have def_k1 := ltn_predK lt0k.
have def_kb1: kb.-1.+1 = kb by rewrite /kb -def_k1; case e.
have eq_bc_0: (b == 0) && (c == 0) = (d == 0).
  by rewrite eqn_add0 eqn_mul0 orbC -def_kb1. 
have lt1p: 1 < p by rewrite ltnS ltn_0double.
have co_p_2: coprime p 2.
  by rewrite /coprime gcdnC gcdnE modn2_odd /= odd_double.
have d0_def_pm:
  d == 0 -> [/\ m = (p + a.*2) * p, lb_dvd p p & lb_dvd p (p + a.*2)].
- move/eqP=> d0; have{d0 def_m} def_m: m = (p + a.*2) * p.
    by rewrite d0 addn0 -mulnn -!mul2n mulnA -muln_addl in def_m *.
  split=> //; apply/hasPn=> r; move/(hasPn leppm); apply: contra => /= dv_r.
    by rewrite def_m dvdn_mull.
  by rewrite def_m dvdn_mulr.
case def_a: a => [|a'] /= in le_a_n *; rewrite !natTrecE -/p {}eq_bc_0.
  case: d d0_def_pm def_m => [[//| def_m {pr_p}pr_p pr_m'] _ | d _ def_m] /=.
    rewrite def_m def_a addn0 mulnA -2!expnSr.
    by split; rewrite /pd_ord /= ?muln1 ?pr_p ?leqnn.
  apply: apd_ok => //; split; rewrite /= ?expn1 ?muln1 // ?andbT; last first.
    by rewrite /pd_ord /= ltpm.
  apply: contra leppm; case/hasP=> r /=; rewrite mem_index_iota.
  case/andP=> lt1r ltrm dvrm; apply/hasP; case: (ltnP r p) => [ltrp | lepr].
    by exists r; rewrite // mem_index_iota lt1r.
  case/dvdnP: dvrm => q def_q; exists q; last by rewrite def_q /= dvdn_mulr.
  rewrite mem_index_iota -(ltn_pmul2r (ltnW lt1r)) -def_q mul1n ltrm.
  move: def_m; rewrite def_a addn0 -(@ltn_pmul2r p) // mulnn => <-.
  apply: (@leq_ltn_trans m); first by rewrite def_q leq_mul.
  by rewrite -addn1 leq_add2l.
have def_k2: k.*2 = ifnz e 1 k * kb.
  by rewrite /kb; case e => *; rewrite (mul1n, muln2).
case def_b': (b - _) => [|b']; last first.
  have ->: ifnz e k.*2.-1 1 = kb.-1 by rewrite /kb; case e.
  apply: IHn => {n le_a_n p'}//; rewrite -/p -/kb; split=> //.
    rewrite lt0k ltpm leppm pr_p andbT /=.
    by case: ifnzP; [move/ltn_predK->; exact: ltnW | rewrite def_kb1].
  apply: (@addn_injr p.*2).
  rewrite -2!addnA -!double_add -addnA -mulSnr -def_a -def_m /d.
  have ->: b * kb = b' * kb + (k.*2 - c * kb + kb).
    rewrite addnCA addnC -mulSnr -def_b' def_k2 -muln_subl -muln_addl addnC.
    by rewrite subnK // ltnW // -ltn_0sub def_b'.
  rewrite -addnA; congr (_ + (_ + _).*2).
  case: (c) ltc; first by rewrite -addSnnS def_kb1 subn0 addn0 addnC.
  rewrite /kb; case e => [[] // _|e' c' _] /=; last first.
    by rewrite -subn_sub subnn addnC addSnnS.
  by rewrite mul1n -double_sub -double_add subn1 !addn1 def_k1.
have ltdp: d < p.
  move/eqP: def_b'; rewrite eqn_sub0 -(@leq_pmul2r kb); last first.
    by rewrite -def_kb1.
  rewrite muln_subl -def_k2 ltnS -(leq_add2r c); move/leq_trans; apply.
  have{ltc} ltc: c < k.*2.
    by apply: (leq_trans ltc); rewrite leq_double /kb; case e.
  rewrite -{2}(subnK (ltnW ltc)) addnC leq_add2l leq_sub2l //.
  by rewrite -def_kb1 mulnS leq_addr.
case def_d: d d0_def_pm => [|d'] => [[//|{def_m ltdp pr_p} def_m pr_p pr_m'] | _].
  rewrite eqxx -doubleS -addnS -def_a double_add -addSn -/p def_m.
  rewrite mulnCA mulnC -expnSr.
  apply: IHn => {n le_a_n}//; rewrite -/p -/kb; split.
    rewrite lt0k -addn1 leq_add2l {1}def_a pr_m' pr_p /= def_k1 -addnn.
    by rewrite leq_addr.
  rewrite -addnA -double_add addnCA def_a addSnnS def_k1 -(addnC k) -mulnSr.
  rewrite -[_.*2.+1]/p muln_addl double_add addnA -mul2n mulnA mul2n -mulSn.
  by rewrite -/p mulnn.
have next_pm: lb_dvd p.+2 m.
  rewrite /lb_dvd /index_iota -(subnK lt1p) 2!subSS subn0 addnC iota_add.
  rewrite has_cat; apply/norP; split=> //=; rewrite orbF subnK // orbC.
  apply/norP; split; apply/dvdnP=> [[q def_q]].
     case/hasP: leppm; exists 2; first by rewrite /p -(subnK lt0k).
    by rewrite /= def_q dvdn_mull // dvdn2_even /= odd_double.
  move/(congr1 (dvdn p)): def_m; rewrite -mulnn -!mul2n mulnA -muln_addl.
  rewrite dvdn_mull // dvdn_addr; last by rewrite def_q dvdn_mull.
  case/dvdnP=> r; rewrite mul2n => def_r; move: ltdp (congr1 odd def_r).
  rewrite odd_double -ltn_double {1}def_r -mul2n ltn_pmul2r //.
  by case: r def_r => [|[|[]]] //; rewrite def_d // mul1n /= odd_double.
apply: apd_ok => //; case: a' def_a le_a_n => [|a'] def_a => [_ | lta] /=.
  split; rewrite /pd_ord /= ?expn1 ?muln1 ?andbT //; apply: contra next_pm.
  case/hasP=> q; rewrite mem_index_iota; case/andP=> lt1q ltqm dvqm.
  apply/hasP; case: (ltnP q p.+2) => [ltqp | lepq].
    by exists q; rewrite // mem_index_iota lt1q.
  case/dvdnP: dvqm => r def_r; exists r; last by rewrite def_r /= dvdn_mulr.
  rewrite mem_index_iota -(ltn_pmul2r (ltnW lt1q)) -def_r mul1n ltqm /=.
  rewrite -(@ltn_pmul2l p.+2) //; apply: (@leq_ltn_trans m).
    by rewrite def_r mulnC leq_mul.
  rewrite -addn2 mulnn sqrn_add mul2n muln2 -addnn addnCA -addnA addnCA addnA.
  by rewrite def_a mul1n in def_m; rewrite -def_m addnS -addnA ltnS leq_addr.
set bc := ifnz _ _ _; apply: leq_pd_ok (leqnSn _) _.
rewrite -doubleS -{1}[m]mul1n -[1]/(k.+1.*2.+1 ^ 0)%N.
apply: IHn; first exact: ltnW.
rewrite doubleS -/p [ifnz 0 _ _]/=; do 2?split => //.
  rewrite orbT next_pm /= -(leq_add2r d.*2) def_m 2!addSnnS -doubleS leq_add.
  - move: ltc; rewrite /kb {}/bc andbT; case e => //= e' _; case: ifnzP => //.
    by case: edivn2P.
  - by rewrite -{1}[p]muln1 -mulnn ltn_pmul2l.
  by rewrite leq_double def_a mulSn (leq_trans ltdp) ?leq_addr.
rewrite muln_addl !muln2 -addnA addnCA double_add addnCA.
rewrite (_ : _ + bc.2 = d); last first.
  rewrite /d {}/bc /kb -muln2.
  case: (e) (b) def_b' => //= _ []; first by case edivn2P.
  by case c; do 2?case; rewrite // mul1n /= muln2.
rewrite def_m 3!doubleS addnC -(addn2 p) sqrn_add mul2n muln2 -3!addnA.
congr (_ + _); rewrite 4!addnS -!double_add; congr _.*2.+2.+2.
by rewrite def_a -add2n muln_addl -addnA -muln2 -muln_addr mul2n.
Qed.

Lemma primePn : forall n,
  reflect (n < 2 \/ exists2 d, 1 < d < n & d %| n) (~~ prime n).
Proof.
rewrite /prime => [] [|[|p2]]; try by do 2!left.
case: (@prime_decomp_correct p2.+2) => //; rewrite unlock.
case: prime_decomp => [|[q [|[|e]]] pd] //=; last first; last by rewrite andbF.
  rewrite 2!expnS -!mulnA /=.
  case: (_ ^ _ * _) => [|u -> _]; first by rewrite !muln0.
  case/andP=> lt1q _; left; right; exists q; last by rewrite dvdn_mulr.
  have lt0q := ltnW lt1q; rewrite lt1q -{1}[q]muln1 ltn_pmul2l //.
  by rewrite -[2]muln1 leq_mul.
rewrite expn1; case: pd => [|[r e] pd] /=; last first.
  case: e => [|e] /=; first by rewrite !andbF.
  rewrite expnS -mulnA; case: (_ ^ _ * _) => [|u -> _]; first by rewrite !muln0.
  case/and3P=> lt1q ltqr _; left; right; exists q; last by rewrite dvdn_mulr.
  have:= ltn_mul lt1q ltqr; rewrite lt1q mulnA mul1n; move/leq_trans; apply.
  by rewrite -{1}[q * r]muln1 leq_mul.
rewrite muln1 !andbT => def_q pr_q lt1q; right; case=> // [[d]].
by rewrite def_q -mem_index_iota => in_d_2q dv_d_q; case/hasP: pr_q; exists d.
Qed.

Lemma primeP : forall p,
  reflect (p > 1 /\ forall d, d %| p -> xpred2 1 p d) (prime p).
Proof.
move=> p; rewrite -[prime p]negbK; case: primePn => [npr_p | pr_p].
  right=> [[lt1p pr_p]]; case: npr_p => [|[d n1pd]].
    by rewrite ltnNge lt1p.
  by move/pr_p; case/orP; move/eqP=> def_d; rewrite def_d ltnn ?andbF in n1pd.
case: leqP => [lep1 | lt1p]; first by case: pr_p; left.
left; split=> // d dv_d_p; apply/norP=> [[nd1 ndp]]; case: pr_p; right.
exists d; rewrite // andbC 2!ltn_neqAle ndp eq_sym nd1.
by have lt0p := ltnW lt1p; rewrite dvdn_leq // (ltn_0dvd lt0p).
Qed.

Implicit Arguments primeP [p].
Implicit Arguments primePn [n].
Prenex Implicits primePn primeP.

Lemma prime_gt1 : forall p, prime p -> 1 < p.
Proof. by move=> p; case/primeP. Qed.

Lemma ltn_0prime : forall p, prime p -> 0 < p.
Proof. by move=> *; rewrite ltnW ?prime_gt1. Qed.

Hint Resolve prime_gt1 ltn_0prime.

Definition prime_pos_nat p pr_p := PosNat (@ltn_0prime p pr_p).

Lemma prod_prime_decomp : forall n,
  n > 0 -> n = \prod_(pf <- prime_decomp n) pf.
Proof. by move=> n; case/prime_decomp_correct. Qed.

Lemma even_prime : forall p, prime p -> p = 2 \/ odd p.
Proof.
move=> p pr_p; case odd_p: (odd p); [by right | left].
have: 2 %| p by rewrite dvdn2_even odd_p.
by case/primeP: pr_p => _ dv_p; move/dv_p; move/(2 =P p).
Qed.

Lemma mem_prime_decomp : forall n p e,
  p ^ e \in prime_decomp n -> [/\ prime p, e > 0 & p ^ e %| n].
Proof.
move=> n p e; case: (posnP n) => [-> //| ].
case/prime_decomp_correct=> def_n mem_pd ord_pd pd_pe.
have:= allP mem_pd _ pd_pe; case/andP=> pr_p ->; split=> //; last first.
  case/splitPr: pd_pe def_n => pd1 pd2 ->.
  by rewrite big_cat big_adds /= mulnCA dvdn_mulr.
have lt1p: 1 < p.
  apply: (allP (order_path_min ltn_trans ord_pd)).
  by apply/mapsP; exists (p ^ e).
apply/primeP; split=> // d dv_d_p; apply/norP=> [[nd1 ndp]].
case/hasP: pr_p; exists d => //.
rewrite mem_index_iota andbC 2!ltn_neqAle ndp eq_sym nd1.
by have lt0p := ltnW lt1p; rewrite dvdn_leq // (ltn_0dvd lt0p).
Qed.

Lemma prime_coprime : forall p m, prime p -> coprime p m = ~~ (p %| m).
Proof.
move=> p m; case/primeP=> p_gt1 p_pr; apply/eqP/negP=> [d1 | ndv_pm].
  case/dvdnP=> k def_m; rewrite -(addn0 m) def_m gcdn_addl_mul gcdn0 in d1.
  by rewrite d1 in p_gt1.
by apply: gcdn_def => // d; move/p_pr; case/orP; move/eqP=> ->.
Qed.

Lemma dvdn_prime2 : forall p q, prime p -> prime q -> (p %| q) = (p == q).
Proof.
move=> p q pr_p pr_q; apply: negb_inj.
by rewrite eqn_dvd negb_and -!prime_coprime // coprime_sym orbb.
Qed.

Lemma euclid : forall m n p, prime p -> (p %| m * n) = (p %| m) || (p %| n).
Proof.
move => m n p pr_p; case dv_pm: (p %| m); first exact: dvdn_mulr.
by rewrite gauss // prime_coprime // dv_pm.
Qed.

Lemma mem_primes : forall p n,
  (p \in primes n) = [&& prime p, n > 0 & p %| n].
Proof.
move=> p n; rewrite andbCA; case: posnP => [-> // | /= n_pos].
apply/mapsP/andP=> [[[q e]]|[pr_p]] /=.
  case/mem_prime_decomp=> pr_q e_pos; case/dvdnP=> u -> <- {p}.
  by rewrite -(prednK e_pos) expnS mulnCA dvdn_mulr.
rewrite {1}(prod_prime_decomp n_pos) big_cond_seq /=.
apply big_prop => [| u v IHu IHv | [q e] /= mem_qe dv_p_qe].
- by rewrite dvdn1 eqn_leq leqNgt prime_gt1.
- by rewrite euclid //; case/orP.
exists (q ^ e) => //=; case/mem_prime_decomp: mem_qe => pr_q _ _.
elim: e dv_p_qe => [|e IHe]; first by rewrite dvdn1 eqn_leq leqNgt prime_gt1.
by rewrite expnS euclid // dvdn_prime2 //; case/predU1P.
Qed.

Lemma sorted_primes : forall n, sorted ltn (primes n).
Proof.
move=> n; case: (posnP n) => [-> // | ]; case/prime_decomp_correct=> _ _.
exact: path_sorted.
Qed.

Lemma eq_primes : forall m n, (primes m =i primes n) <-> (primes m = primes n).
Proof.
move=> m n; split=> [eqpr| -> //].
by apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes.
Qed.

Lemma uniq_primes : forall n, uniq (primes n).
Proof. move=> n; exact: (sorted_uniq ltn_trans ltnn (sorted_primes n)). Qed.

(* The smallest prime divisor *)

Lemma primes_pdiv : forall n, (pdiv n \in primes n) = (n > 1).
Proof.
case=> [|[|n]] //; rewrite /pdiv /primes.
have:= prod_prime_decomp (ltn0Sn n.+1); rewrite unlock.
by case: prime_decomp => //= pf pd _; rewrite mem_head.
Qed.

Lemma prime_pdiv : forall n, 1 < n -> prime (pdiv n).
Proof. by move=> n; rewrite -primes_pdiv mem_primes; case/and3P. Qed.

Lemma dvdn_pdiv : forall n, pdiv n %| n.
Proof.
move=> n; case: n (primes_pdiv n) => [|[|n]] //.
by rewrite mem_primes; case/and3P.
Qed.

Lemma leq_pdiv : forall n, pdiv n <= n.
Proof. by case=> // n; rewrite dvdn_leq // dvdn_pdiv. Qed.

Lemma pdiv_gt1 : forall n, (1 < pdiv n) = (1 < n).
Proof. by case=> [|[|n]] //; rewrite prime_gt1 ?prime_pdiv. Qed.

Lemma ltn_0pdiv : forall n, (0 < pdiv n) = (0 < n).
Proof. by case=> [|[|n]] //; rewrite ltnW ?pdiv_gt1. Qed.

Lemma pdiv_min_dvd : forall m d, 1 < d -> d %| m -> pdiv m <= d.
Proof.
case=> // m d lt1d dv_d_m; apply: leq_trans (leq_pdiv d).
have: pdiv d \in primes m.+1.
  by rewrite mem_primes prime_pdiv // (dvdn_trans (dvdn_pdiv d)).
rewrite {2}/pdiv; case: primes (sorted_primes m.+1) => //= p pm ord_pm.
rewrite inE; case/predU1P=> [-> //|].
move/(allP (order_path_min ltn_trans ord_pm)); exact: ltnW.
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

Lemma primePns : forall n,
  reflect (n < 2 \/ exists p, [/\ prime p, p ^ 2 <= n & p %| n]) (~~ prime n).
Proof.
move=> n; apply: (iffP idP) => [npr_p|]; last first.
  case=> [|[p [pr_p le_p2_n dv_p_n]]]; first by case: n => [|[]].
  apply/negP=> pr_n; move: dv_p_n le_p2_n; rewrite dvdn_prime2 //; move/eqP->.
  by rewrite leqNgt -{1}[n]muln1 -mulnn ltn_pmul2l ?prime_gt1 ?ltn_0prime.
case: leqP => [lt1p|]; [right | by left].
exists (pdiv n); rewrite dvdn_pdiv prime_pdiv //; split=> //.
by case: leqP npr_p => //; move/ltn_pdiv2_prime->.
Qed.

Implicit Arguments primePns [n].
Prenex Implicits primePns.

Lemma primes_mul : forall m n p, m > 0 -> n > 0 ->
  (p \in primes (m * n)) = (p \in primes m) || (p \in primes n).
Proof.
move=> m n p m_pos n_pos; rewrite !mem_primes ltn_0mul m_pos n_pos.
by case pr_p: (prime p); rewrite // euclid.
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
by apply/andP/idP=> [[pr_q q_p] | ]; [rewrite -dvdn_prime2 | move/eqP->].
Qed.

Lemma coprime_has_primes : forall m n, m > 0 -> n > 0 ->
  coprime m n = ~~ has (mem (primes m)) (primes n).
Proof.
move=> m n m_pos n_pos; apply/eqnP/hasPn=> [mn1 p | no_p_mn].
  rewrite /= !mem_primes m_pos n_pos /=; case/andP=> pr_p p_n.
  have:= prime_gt1 pr_p; rewrite pr_p ltnNge -mn1 /=; apply: contra => p_m.
  by rewrite dvdn_leq ?ltn_0gcd ?m_pos // dvdn_gcd ?p_m.
case: (ltngtP (gcdn m n) 1) => //; first by rewrite ltnNge ltn_0gcd ?m_pos.
move/prime_pdiv; set p := pdiv _ => pr_p.
move/implyP: (no_p_mn p); rewrite /= !mem_primes m_pos n_pos pr_p /=.
by rewrite !(dvdn_trans (dvdn_pdiv _)) // (dvdn_gcdl, dvdn_gcdr).
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

Lemma logn0 : forall p, logn p 0 = 0.
Proof. by move=> p; rewrite /logn if_same. Qed.

Lemma logn1 : forall p, logn p 1 = 0.
Proof. by move=> p; rewrite lognE dvdn1 /= andbC; case: eqP => // ->. Qed.

Lemma ltn_0pfactor : forall p n, 0 < p ^ logn p n.
Proof. by move=> p n; rewrite ltn_0exp lognE; case: (posnP p) => // ->. Qed.
Hint Resolve ltn_0pfactor.

Lemma pfactor_dvdn : forall p n m,
  prime p -> m > 0 -> (p ^ n %| m) = (n <= logn p m).
Proof.
move=> p n m p_pr; elim: n m => [|n IHn] m m_pos; first exact: dvd1n.
rewrite lognE p_pr m_pos /=; case dv_pm: (p %| m); last first.
  by apply/dvdnP=> [] [/= q def_m]; rewrite def_m mulnCA dvdn_mulr in dv_pm.
case/dvdnP: dv_pm m_pos => q ->{m}; rewrite ltn_0mul; case/andP=> p_pos q_pos.
by rewrite expnSr dvdn_pmul2r // divn_mull // IHn. 
Qed.

Lemma pfactor_dvdnn : forall p n, p ^ logn p n %| n.
Proof.
move=> p [|n] //; case pr_p: (prime p); first by rewrite pfactor_dvdn.
by rewrite lognE pr_p dvd1n.
Qed.

Lemma logn_prime : forall p q, prime q -> logn p q = (p == q).
Proof.
move=> p q pr_q; have q_pos := ltn_0prime pr_q; rewrite lognE q_pos /=.
case pr_p: (prime p); last by case: eqP pr_p pr_q => // -> ->.
by rewrite dvdn_prime2 //; case: eqP => // ->; rewrite divnn q_pos logn1.
Qed.

Lemma pfactor_coprime : forall p n, prime p -> n > 0 ->
  {m | coprime p m & n = m * p ^ logn p n}.
Proof.
move=> p n p_pr n_pos; set k := logn p n.
have dv_pk_n: p ^ k %| n by rewrite pfactor_dvdn.
exists (n %/ p ^ k); last by rewrite divnK.
rewrite prime_coprime // -(@dvdn_pmul2r (p ^ k)) ?ltn_0exp ?ltn_0prime //.
by rewrite -expnS divnK // pfactor_dvdn // ltnn.
Qed.

Lemma pfactorK : forall p n, prime p -> logn p (p ^ n) = n.
Proof.
move=> p n p_pr; have pn_pos: p ^ n > 0 by rewrite ltn_0exp ltn_0prime.
apply/eqP; rewrite eqn_leq -pfactor_dvdn // dvdnn andbT.
by rewrite -(leq_exp2l _ _ (prime_gt1 p_pr)) dvdn_leq // pfactor_dvdn.
Qed.

Lemma dvdn_leq_log : forall p m n, 0 < n -> m %| n -> logn p m <= logn p n.
Proof.
move=> p m n n_pos dv_m_n; have m_pos := ltn_0dvd n_pos dv_m_n.
case p_pr: (prime p); last by do 2!rewrite lognE p_pr /=.
by rewrite -pfactor_dvdn //; apply: dvdn_trans dv_m_n; rewrite pfactor_dvdn.
Qed.

Lemma logn_gauss : forall p m n, coprime p m -> logn p (m * n) = logn p n.
Proof.
move=> p m n co_pm; case p_pr: (prime p); last by rewrite /logn p_pr.
case: (posnP n) => [->|n_pos]; first by rewrite muln0.
case: (posnP m) => [m0|m_pos].
  by rewrite m0 prime_coprime ?dvdn0 in co_pm.
have mn_pos: m * n > 0 by rewrite ltn_0mul m_pos.
apply/eqP; rewrite eqn_leq andbC dvdn_leq_log ?dvdn_mull //.
set k := logn p _; have: p ^ k %| m * n by rewrite pfactor_dvdn.
by rewrite gauss ?coprime_expl // -pfactor_dvdn.
Qed.

Lemma logn_mul : forall p m n,
  0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n.
Proof.
move=> p m n; case p_pr: (prime p); last by rewrite /logn p_pr.
have xlp := pfactor_coprime p_pr.
case/xlp=> m' co_m' def_m; case/xlp=> n' co_n' def_n {xlp}.
by rewrite {1}def_m {1}def_n mulnCA -mulnA -expn_add !logn_gauss // pfactorK.
Qed.

Lemma logn_exp : forall p m n, logn p (m ^ n) = n * logn p m.
Proof.
move=> p m n; case p_pr: (prime p); last by rewrite /logn p_pr muln0.
elim: n => [|n IHn]; first by rewrite logn1.
case: (posnP m) => [->|m_pos]; first by rewrite exp0n // lognE andbF muln0.
by rewrite expnS logn_mul ?IHn // ltn_0exp m_pos.
Qed.

Lemma dvdn_pfactor : forall p d n, prime p ->
  reflect (exists2 m, m <= n & d = p ^ m)%N (d %| p ^ n).
Proof.
move=> p d n p_pr; have pn_pos: p ^ n > 0 by rewrite ltn_0exp ltn_0prime.
apply: (iffP idP) => [dv_d_pn|[m le_m_n ->]]; last first.
  by rewrite -(subnK le_m_n) expn_add dvdn_mulr.
exists (logn p d); first by rewrite -(pfactorK n p_pr) dvdn_leq_log.
have d_pos: d > 0 by exact: ltn_0dvd dv_d_pn.
case: (pfactor_coprime p_pr d_pos) => q co_p_q def_d.
rewrite {1}def_d ((q =P 1) _) ?mul1n // -dvdn1.
suff: q %| p ^ n * 1 by rewrite gauss // coprime_sym coprime_expl.
by rewrite muln1 (dvdn_trans _ dv_d_pn) // def_d dvdn_mulr.
Qed.

(* pi- parts *)

(* Testing for membership in set of prime factors. *)

Definition nat_pred := simpl_pred nat.
Canonical Structure nat_pred_pred := Eval hnf in [predType of nat_pred].

Delimit Scope nat_pred_scope with Np.
Bind Scope nat_pred_scope with nat_pred.

Coercion nat_pred_of_nat (p : nat) : nat_pred := pred1 p.

Definition negn (pi : nat_pred) : nat_pred := predC (mem pi).

Notation "pi ^'" := (negn pi) (at level 2, format "pi ^'") : nat_pred_scope.

Lemma negnK : forall pi, pi^'^'%Np =i pi.
Proof. move=> pi p; exact: negbK. Qed.

Definition p_part (pi : nat_pred) n :=
  \prod_(1 <= p < n.+1 | p \in pi) p ^ logn p n.

Lemma ltn_0prod_pfactor : forall r (P : pred nat) n,
  0 < \prod_(p <- r | P p) p ^ logn p n.
Proof.
by move=> r P n; apply big_prop => // n1 n2; rewrite ltn_0mul => ->.
Qed.

Lemma ltn_0p_part : forall pi n, 0 < p_part pi n.
Proof. move=> pi n; exact: ltn_0prod_pfactor. Qed.
Hint Resolve ltn_0p_part.

Lemma primes_p_part :
  forall pi n, primes (p_part pi n) = filter (mem pi) (primes n).
Proof.
rewrite /p_part => pi n; have ltnT := ltn_trans.
case: (posnP n) => [-> | n_pos]; first by rewrite big_seq0.
apply: (eq_sorted_irr ltnT ltnn); rewrite ?(sorted_primes, sorted_filter) //.
move=> p; rewrite mem_filter /= !mem_primes n_pos ltn_0prod_pfactor /=.
apply/andP/and3P=> [[p_pr] | [pi_p p_pr dv_p_n]].
  apply big_prop => [|n1 n2 IHn1 IHn2|q pi_q].
  - by rewrite dvdn1; case: eqP p_pr => // ->.
  - by rewrite euclid //; case/orP.
  rewrite -{1}(expn1 p) pfactor_dvdn // logn_exp ltn_0mul.
  rewrite ltn_0log mem_primes n_pos - andbA /=; case/and3P=> pr_q dv_q_n.
  by rewrite logn_prime //; case: eqP => // ->.
have p1_p : p.-1.+1 = p by rewrite prednK ?ltn_0prime.
have i_p: p.-1 < n by rewrite p1_p dvdn_leq.
rewrite big_add1 big_mkord (bigD1 (Ordinal i_p)) /= p1_p //.
by rewrite lognE p_pr n_pos dv_p_n -mulnA dvdn_mulr.
Qed.

Lemma p_part_mul : forall pi m n, m * n > 0 ->
  p_part pi (m * n) = p_part pi m * p_part pi n.
Proof.
move=> pi; suffices widen: forall m n, m > 0 ->
  p_part pi n = \prod_(1 <= p < (m * n).+1 | p \in pi) p ^ logn p n.
- move=> m n; rewrite ltn_0mul; case/andP=> m_pos n_pos.
  rewrite (widen _ m n_pos) (widen _ n m_pos) (mulnC n) -big_split /=.
  by apply: eq_bigr => p _; rewrite logn_mul // expn_add.
move=> m n m_pos; have le_n_mn: n <= m * n by rewrite -{1}(mul1n n) leq_mul.
rewrite (@big_cat_nat _ _ _ n.+1) //= mulnC big1_seq ?mul1n //= => p.
rewrite mem_index_iota; case/and3P=> _ lt_n_p _.
by rewrite lognE /dvdn eqn0Ngt modn_small // andbN andbF.
Qed.

Lemma p_part_0 : forall pi, p_part pi 0 = 1.
Proof. by move=> pi; rewrite /p_part big_seq0. Qed.

Lemma p_part_1 : forall pi, p_part pi 1 = 1.
Proof. by move=> pi; rewrite /p_part unlock /= logn1 if_same. Qed.

Lemma p_part_exp : forall pi m n, p_part pi (m ^ n) = (p_part pi m ^ n)%N.
Proof.
move=> pi m; elim=> [|n IHn]; first exact: p_part_1.
case: (posnP m) => [->|m_pos]; first by rewrite p_part_0 exp1n.
by rewrite expnS p_part_mul ?IHn // -expnS ltn_0exp m_pos.
Qed.

Lemma p1_part : forall p n : nat, p_part p n = (p ^ logn p n)%N.
Proof.
move=> p n; case p_ok: (1 <= p <= n).
  case/andP: p_ok => p_pos; rewrite -(prednK p_pos) => i_p.
  by rewrite /p_part big_add1 big_mkord (big_pred1 (Ordinal i_p)).
rewrite /p_part big_hasC; last by rewrite has_pred1 mem_index_iota p_ok.
rewrite lognE; case: and3P => // [[p_pr n_pos dv_p_n]].
by rewrite ltn_0prime // dvdn_leq in p_ok.
Qed.

Lemma p_part_primes : forall n, n > 0 -> p_part [pred p \in primes n] n = n.
Proof.
move=> n n_pos; have def_n := prod_prime_decomp n_pos.
transitivity (\prod_(p <- primes n) p ^ logn p n).
  rewrite /p_part -big_filter; apply: eq_big_perm.
  apply: uniq_perm_eq; rewrite ?(uniq_primes, uniq_filter, uniq_iota) // => p.
  rewrite mem_filter mem_index_iota andbA mem_primes; case: and3P => //=.
  by case=> pr_p _ dv_p_n; rewrite ltnS ltn_0prime // dvdn_leq.  
rewrite big_maps {3}def_n !(big_cond_seq xpredT).
apply: eq_bigr => [[p e]] /= n_p_e; rewrite {}def_n.
have [pr_p _ _] := mem_prime_decomp n_p_e; case/rot_to: n_p_e => i pd def_pd.
have: perm_eq (prime_decomp n) (p ^ e :: pd); last move/(eq_big_perm _)->.
  by rewrite -def_pd perm_eq_sym perm_catC cat_take_drop.
rewrite big_adds /= mulnC logn_gauss ?pfactorK // big_cond_seq /=.
apply big_prop => [|n1 n2|[q e'] pd_q]; first exact: coprimen1.
  by rewrite coprime_mulr => ->.
rewrite prime_coprime //; apply/negP; move/(dvdn_leq_log p); move/implyP.
rewrite ltn_0exp logn_prime // eqxx logn_exp ltn_0mul.
have: q ^ e' \in prime_decomp n by rewrite -(mem_rot i) def_pd inE pd_q orbT.
case/mem_prime_decomp=> pr_q -> _.
rewrite ltn_0prime //= logn_prime {pr_q}//; case: eqP => // def_q.
have:= uniq_primes n; rewrite -(uniq_rot i) -maps_rot def_pd /=.
by case/andP; case/mapsP; exists (q ^ e').
Qed.

Lemma p_partT : forall n, n > 0 -> p_part predT n = n.
Proof.
move=> n n_pos; rewrite -{2}(p_part_primes n_pos) {2}/p_part big_mkcond /=.
by apply: eq_bigr => p _; rewrite -ltn_0log; case: (logn p _).
Qed.

Lemma p_partC : forall pi n,
  n > 0 -> (p_part pi n * p_part pi^' n = n)%N.
Proof.
move=> pi n n_pos; rewrite -{3}(p_partT n_pos) /p_part.
do 2!rewrite mulnC big_mkcond /=; rewrite -big_split; apply: eq_bigr => p _ /=.
by rewrite mulnC inE /=; case: (p \in pi); rewrite /= (muln1, mul1n).
Qed.

Section PiNat.

Implicit Type pi rho : nat_pred.

Definition p_nat pi n := (n > 0) && all (mem pi) (primes n).

Lemma sub_p_nat : forall pi rho n,
  {subset pi <= rho} -> p_nat pi n -> p_nat rho n.
Proof.
rewrite /p_nat => pi rho n subpi; case/andP=> -> pi_n.
apply/allP=> p; move/(allP pi_n); exact: subpi.
Qed.

Lemma eq_p_nat : forall pi rho n, pi =i rho -> p_nat pi n = p_nat rho n.
Proof. by move=> pi rho n eqpi; rewrite /p_nat (eq_all eqpi). Qed.

Lemma p_natCK : forall pi n, p_nat pi^'^' n = p_nat pi n.
Proof. move=> pi n; exact: eq_p_nat (negnK pi). Qed.

Lemma p_natI : forall pi rho n,
  p_nat [predI pi & rho] n = p_nat pi n && p_nat rho n.
Proof. by move=> pi rho n; rewrite /p_nat andbCA all_predI !andbA andbb. Qed.

Lemma p_nat_mul : forall pi m n,
  p_nat pi (m * n) = p_nat pi m && p_nat pi n.
Proof.
move=> pi m n; rewrite /p_nat ltn_0mul andbCA -andbA andbCA.
case: posnP => // n_pos; case: posnP => //= m_pos.
apply/allP/andP=> [pi_mn | [pi_m pi_n] p].
  by split; apply/allP=> p m_p; apply: pi_mn; rewrite primes_mul // m_p ?orbT.
rewrite primes_mul //; case/orP; [exact: (allP pi_m) | exact: (allP pi_n)].
Qed.

Lemma p_nat_part : forall pi n, p_nat pi (p_part pi n).
Proof.
move=> pi n; rewrite /p_nat primes_p_part ltn_0p_part.
by apply/allP=> p; rewrite mem_filter; case/andP.
Qed.

Lemma p_nat_prime : forall pi p, prime p -> p_nat pi p = (p \in pi).
Proof.
by move=> pi p pr_p; rewrite /p_nat ltn_0prime // primes_prime //= andbT.
Qed.

Lemma p_nat_exp : forall pi m n, p_nat pi (m ^ n) = (n == 0) || p_nat pi m.
Proof. by move=> pi m [|n] //; rewrite /p_nat ltn_0exp orbC primes_exp. Qed.

Lemma p_nat_primes : forall n, n > 0 -> p_nat [pred p \in primes n] n.
Proof. rewrite /p_nat => n ->; exact/allP. Qed.

Lemma p_nat_dvdn : forall m n pi, m %| n -> p_nat pi n -> p_nat pi m.
Proof. by move=> m n pi; case/dvdnP=> q ->; rewrite p_nat_mul; case/andP. Qed.

Lemma p_nat_divn : forall m n pi, m %| n -> p_nat pi n -> p_nat pi (n %/ m).
Proof.
move=> m n // pi; case/dvdnP=> q ->; rewrite p_nat_mul andbC; case/andP.
by case: m => // m _; rewrite divn_mull.
Qed.

Lemma coprime_primes' : forall m n,
  m > 0 -> n > 0 -> coprime m n = p_nat [predC primes m] n.
Proof.
by move=> m n m_pos n_pos; rewrite /p_nat n_pos all_predC coprime_has_primes.
Qed.

Lemma p_nat_coprime : forall pi m n, p_nat pi m -> p_nat pi^' n -> coprime m n.
Proof.
move=> pi m n; case/andP=> m_pos pi_m; case/andP=> n_pos pi'_n.
rewrite coprime_has_primes //; apply/hasPn=> p; move/(allP pi'_n).
apply: contra; exact: allP.
Qed.

Lemma p_nat_1 : forall pi n, p_nat pi n -> p_nat pi^' n -> n = 1.
Proof.
by move=> pi n pi_n pi'_n; rewrite -(eqnP (p_nat_coprime pi_n pi'_n)) gcdnn.
Qed.

Lemma part_p_nat : forall pi n, p_nat pi n -> p_part pi n = n.
Proof.
move=> pi n; case/andP=> n_pos pi_n.
rewrite -{2}(p_partT n_pos) /p_part big_mkcond; apply: eq_bigr=> p _.
case: (posnP (logn p n)) => [-> |]; first by rewrite if_same.
by rewrite ltn_0log; move/(allP pi_n)=> /= ->.
Qed.

Lemma part_p'_nat : forall pi n, p_nat pi^' n -> p_part pi n = 1.
Proof.
move=> pi n; case/andP=> n_pos pi'_n; apply: big1_seq => p.
case/andP=> pi_p _; case: (posnP (logn p n)) => [-> //|].
by rewrite ltn_0log; move/(allP pi'_n); case/negP. 
Qed.

Lemma p_natP : forall pi n,
  n > 0 -> reflect (forall p, prime p -> p %| n -> p \in pi) (p_nat pi n).
Proof.
move=> pi n n_pos; rewrite /p_nat n_pos.
apply: (iffP allP) => /= pi_n p => [pr_p p_n|].
  by rewrite pi_n // mem_primes pr_p n_pos.
by rewrite mem_primes n_pos /=; case/andP; move: p.
Qed.

Lemma p1_natP : forall p n,
  prime p -> reflect (exists k, n = p ^ k)%N (p_nat p n).
Proof.
move=> p n pr_p; apply: (iffP idP) => [p_n | [k ->{n}]].
  by exists (logn p n); rewrite -p1_part part_p_nat.
by rewrite p_nat_exp p_nat_prime //= inE /= eqxx orbT.
Qed.

End PiNat.

(************************************)
(* Properties of the divisors list. *)
(************************************)

Lemma divisors_correct : forall n, n > 0 ->
  [/\ uniq (divisors n), sorted leq (divisors n)
    & forall d, (d \in divisors n) = (d %| n)].
Proof.
move=> n; move/prod_prime_decomp=> def_n; rewrite {4}def_n {def_n}.
have: all prime (primes n) by apply/allP=> p; rewrite mem_primes; case/andP.
have:= uniq_primes n; rewrite /primes /divisors; move/prime_decomp: n.
elim=> [|[p e] pd] /=; first by split=> // d; rewrite big_seq0 dvdn1 mem_seq1.
rewrite big_adds /=; move: (foldr _ _ pd) => divs IHpd.
case/andP=> npd_p Upd; case/andP=> pr_p pr_pd.
have lt0p: 0 < p by exact: ltn_0prime.
case: {IHpd Upd}(IHpd Upd pr_pd) => Udivs Odivs mem_divs.
have ndivs_p: p * _ \notin divs.
  move=> m; suff: p \notin divs; rewrite !mem_divs.
    by apply: contra; case/dvdnP=> n ->; rewrite mulnCA dvdn_mulr.
  have ndv_p_1: ~~(p %| 1) by rewrite dvdn1 neq_ltn orbC prime_gt1.
  rewrite big_cond_seq /=; apply big_prop => [//|u v npu npv|[q f] /= pd_qf].
    by rewrite euclid //; apply/norP.
  elim: (f) => // f'; rewrite euclid // orbC negb_or => -> {f'}/=.
  have pd_q: q \in maps pfactor_base pd by apply/mapsP; exists (q ^ f).
  by apply: contra npd_p; rewrite dvdn_prime2 // ?(allP pr_pd) //; move/eqP->.
elim: e => [|e] /=; first by split=> // d; rewrite mul1n.
have Tmulp_inj: injective (NatTrec.mul p).
  by move=> u v; move/eqP; rewrite !natTrecE eqn_pmul2l //; move/eqP.
move: (iter e _ _) => divs' [Udivs' Odivs' mem_divs']; split=> [||d].
- rewrite uniq_merge uniq_cat uniq_maps // Udivs Udivs' andbT /=.
  apply/hasP=> [[d dv_d]]; case/mapsP=> d' _ def_d; case/idPn: dv_d.
  by rewrite -def_d natTrecE.
- rewrite (sorted_merge leq_total) //; case: (divs') Odivs' => //= d ds.
  rewrite (@path_maps _ _ _ _ leq xpred0) ?has_pred0 // => u v _.
  by rewrite !natTrecE leq_pmul2l.
rewrite mem_merge mem_cat; case dv_d_p: (p %| d).
  case/dvdnP: dv_d_p => d' ->{d}; rewrite mulnC (negbET (ndivs_p d')) orbF.
  rewrite expnS -mulnA dvdn_pmul2l // -mem_divs'.
  by rewrite -(mem_maps Tmulp_inj divs') natTrecE.
case pdiv_d: (_ \in _).
  by case/mapsP: pdiv_d dv_d_p => d' _ <-; rewrite natTrecE dvdn_mulr.
by rewrite mem_divs gauss // coprime_sym coprime_expl ?prime_coprime ?dv_d_p.
Qed.

Lemma sorted_divisors : forall n, sorted leq (divisors n).
Proof. by move=> n; case: (posnP n) => [-> //|]; case/divisors_correct. Qed.

Lemma uniq_divisors : forall n, uniq (divisors n).
Proof. by move=> n; case: (posnP n) => [-> //|]; case/divisors_correct. Qed.

Lemma sorted_divisors_ltn : forall n, sorted ltn (divisors n).
Proof.
by move=> n; rewrite sorted_ltn_uniq_leq uniq_divisors sorted_divisors.
Qed.

Lemma dvdn_divisors : forall d m, 0 < m -> (d %| m) = (d \in divisors m).
Proof. by move=> d m; case/divisors_correct. Qed.

Lemma divisor1 : forall n, 1 \in divisors n.
Proof. by case=> // n; rewrite -dvdn_divisors // dvd1n. Qed.

Lemma divisorn: forall n, 0 < n -> n \in divisors n.
Proof. by move=> n n_pos; rewrite -dvdn_divisors. Qed.

