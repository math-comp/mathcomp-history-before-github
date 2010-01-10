(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigops fintype.
Require Import div prime choice.

(****************************************************************************)
(* This files contains the definition  of:                                  *)
(*   bin m n        ==  binomial coeficients, i.e. m choose n               *)
(*                                                                          *)
(* In additions to the properties of this function, triangular_sum, Wilson  *)
(* and Pascal are examples of how to manipulate expressions with bigops.    *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** More properties of the factorial **)
Lemma fact0 : fact 0 = 1.
Proof. by done. Qed.

Lemma factS : forall n, fact n.+1  = n.+1 * fact n.
Proof. by done. Qed.

Lemma fact_smonotone m n: 1 < n -> m < n -> fact m < fact n.
Proof.
move=> m n; elim: n m => // n Hrec m Hn; rewrite factS.
rewrite ltnS leq_eqVlt; case/orP=> Hmn.
  by move/eqP: Hmn=>->; rewrite ltn_Pmull // fact_gt0.
case: {Hn}n Hrec Hmn => // [[|n]] Hrec Hmn; first by case: m Hmn.
by apply: leq_trans (Hrec _ is_true_true Hmn) _; rewrite leq_pmull.
Qed.

Lemma fact_prod n : fact n = \prod_(1 <= i < n.+1) i.
Proof.
elim=> [|n Hrec] //; first by rewrite big_nil.
by apply sym_equal; rewrite factS Hrec // !big_add1 big_nat_recr /= mulnC.
Qed.

Theorem Wilson : forall p, p > 1 -> prime p = (p %| (fact p.-1).+1).
Proof.
have dFact: forall p, 0 < p -> fact p.-1 = \prod_(0 <= i < p | i != 0) i.
  move=> p Hp; rewrite -big_filter fact_prod; symmetry; apply: congr_big=> //.
  rewrite /index_iota subn1 -[p]prednK //=; apply/all_filterP.
  by rewrite all_predC has_pred1 mem_iota.
move=> p lt1p; have p_gt0 := ltnW lt1p.
apply/idP/idP=> [pr_p | dv_pF]; last first.
  apply/primeP; split=> // d dv_dp; have: d <= p by exact: dvdn_leq.
  rewrite orbC leq_eqVlt; case/orP=> [-> // | ltdp].
  have:= dvdn_trans dv_dp dv_pF; rewrite dFact // big_mkord.
  rewrite (bigD1 (Ordinal ltdp)) /=; last by rewrite -lt0n (dvdn_gt0 p_gt0).
  by rewrite orbC -addn1 dvdn_addr ?dvdn_mulr // dvdn1 => ->.
pose Fp1 := Ordinal lt1p; pose Fp0 := Ordinal p_gt0.
have ltp1p: p.-1 < p by [rewrite prednK]; pose Fpn1 := Ordinal ltp1p.
case eqF1n1: (Fp1 == Fpn1); first by rewrite -{1}[p]prednK -1?((1 =P p.-1) _).
have toFpP: _ %% p < p by move=> m; rewrite ltn_mod.
pose toFp := Ordinal (toFpP _).
pose mFp (i j : 'I_p) := toFp (i * j).
have Fp_mod: forall i : 'I_p, i %% p = i by move=> i; exact: modn_small.
have mFpA: associative mFp.
  by move=> i j k; apply: val_inj; rewrite /= modn_mulml modn_mulmr mulnA.
have mFpC: commutative mFp by move=> i j; apply: val_inj; rewrite /= mulnC.
have mFp1: left_id Fp1 mFp by move=> i; apply: val_inj; rewrite /= mul1n.
have mFp1r: right_id Fp1 mFp by move=> i; apply: val_inj; rewrite /= muln1.
pose mFpLaw := Monoid.Law mFpA mFp1 mFp1r.
pose mFpM := Monoid.operator (@Monoid.ComLaw _ _ mFpLaw mFpC).
pose vFp (i : 'I_p) := toFp (egcdn i p).1.
have vFpV: forall i, i != Fp0 -> mFp (vFp i) i = Fp1.
  move=> i; rewrite -val_eqE /= -lt0n => i_gt0; apply: val_inj => /=.
  rewrite modn_mulml; case: egcdnP => //= _ km -> _; rewrite {km}modn_addl_mul.
  suff: coprime i p by move/eqnP->; rewrite modn_small.
  rewrite coprime_sym prime_coprime //; apply/negP; move/(dvdn_leq i_gt0).
  by rewrite leqNgt ltn_ord.
have vFp0: forall i, i != Fp0 -> vFp i != Fp0.
  move=> i; move/vFpV=> inv_i; apply/eqP=> vFp0.
  by have:= congr1 val inv_i; rewrite vFp0 /= mod0n.
have vFpK: {in predC1 Fp0, involutive vFp}.
  by move=> i n0i; rewrite /= -[vFp _]mFp1r -(vFpV _ n0i) mFpA vFpV (vFp0, mFp1).
have le_pmFp: (_ : 'I_p) <= p + _.
  by move=> *; apply: leq_trans (ltnW _) (leq_addr _ _).
have eqFp : forall i j : 'I_p, (i == j) = (p %| p + i - j).
  by move=> i j; rewrite -eqn_mod_dvd ?(modn_addl, Fp_mod).
have vFpId: forall i, (vFp i == i :> nat) = xpred2 Fp1 Fpn1 i.
  move=> i; symmetry; case: (i =P Fp0) => [->{i}|]; last move/eqP=> ni0.
    by rewrite /= -!val_eqE /= -{2}[p]prednK //= modn_small //= -(subnKC lt1p).
  rewrite 2!eqFp -euclid //= -[_ - p.-1]subSS prednK //.
  have lt0i: 0 < i by rewrite lt0n.
  rewrite -addnS addKn -addn_subA // muln_addl -{2}(addn1 i) -subn_sqr.
  rewrite addn_subA ?leq_sqr // mulnS -addnA -mulnn -muln_addl.
  rewrite -(subnK (le_pmFp (vFp i) i)) muln_addl addnCA.
  rewrite -[1 ^ 2]/(Fp1 : nat) -addn_subA // dvdn_addl.
    by rewrite euclid // -eqFp eq_sym orbC /dvdn Fp_mod eqn0Ngt lt0i.
  by rewrite -eqn_mod_dvd // Fp_mod modn_addl -(vFpV _ ni0) eqxx.
suffices [mod_fact]: toFp (fact p.-1) = Fpn1.
  by rewrite /dvdn -addn1 -modn_addml mod_fact addn1 prednK // modnn.
rewrite dFact // (@big_morph _ _ _ Fp1 _ mFpM toFp) //; first last.
- by apply: val_inj; rewrite /= modn_small.
- by move=> i j; apply: val_inj; rewrite /= modn_mul2m.
rewrite big_mkord (eq_bigr id) => [|i _]; last by apply: val_inj => /=.
pose ltv i := vFp i < i; rewrite (bigID ltv) -/mFpM [mFpM _ _]mFpC.
rewrite (bigD1 Fp1) -/mFpM; last by rewrite [ltv _]ltn_neqAle vFpId.
rewrite [mFpM _ _]mFp1 (bigD1 Fpn1) -?mFpA -/mFpM; last first.
  rewrite -lt0n -ltnS prednK // lt1p.
  by rewrite [ltv _]ltn_neqAle vFpId eqxx orbT eq_sym eqF1n1.
rewrite (reindex_onto vFp vFp) -/mFpM => [|i]; last by do 3!case/andP; auto.
rewrite (eq_bigl (xpredD1 ltv Fp0)) => [|i]; last first.
  rewrite andbC -!andbA -2!negb_or -vFpId orbC -leq_eqVlt.
  rewrite andbA -ltnNge; symmetry; case: eqP => [->|].
    by case: eqP => // ->; rewrite !andbF.
  by move/eqP=> ni0; rewrite vFpK //eqxx vFp0.
rewrite -{2}[mFp]/mFpM -[mFpM _ _]big_split -/mFpM.
by rewrite big1 ?mFp1r //= => i; case/andP; auto.
Qed.

(** Binomial coefficients *)

Fixpoint bin_rec (m n : nat) {struct m} :=
  match m, n with
  | m'.+1, n'.+1 => bin_rec m' n + bin_rec m' n'
  | _, 0 => 1
  | 0, _.+1 => 0
  end.

Definition bin := nosimpl bin_rec.

Lemma binE : bin = bin_rec. Proof. by []. Qed.

Lemma bin0 : forall n, bin n 0 = 1.
Proof. by case. Qed.

Lemma bi0n : forall n, bin 0 n = if n is S _ then 0 else 1.
Proof. by case. Qed.

Lemma binS : forall m n,  bin m.+1 n.+1 = bin m n.+1 + bin m n.
Proof. by []. Qed.

Lemma bin1 : forall n, bin n 1 = n.
Proof. by elim=> //= n IHn; rewrite binS bin0 IHn addn1. Qed.

Lemma bin_gt0 : forall m n, (0 < bin m n) = (n <= m).
Proof.
by elim=> [|m IHm] [|n] //; rewrite binS addn_gt0 !IHm orbC ltn_neqAle andKb.
Qed.

Lemma bin_small : forall m n, m < n -> bin m n = 0.
Proof. by move=> m n; rewrite ltnNge -bin_gt0; case: posnP. Qed.

Lemma binn : forall n, bin n n = 1.
Proof. by elim=> [|n IHn] //; rewrite binS bin_small. Qed.

Lemma mul_Sm_binm : forall m n, m.+1 * bin m n = n.+1 * bin m.+1 n.+1.
Proof.
elim=> [|m IHm] [|n] //; first by rewrite bin0 bin1 muln1 mul1n.
by rewrite mulSn {2}binS muln_addr addnCA !IHm -muln_addr.
Qed.

Lemma bin_fact : forall m n,
  n <= m -> bin m n * (fact n * fact (m - n)) = fact m.
Proof.
move=> m n; move/subnKC; move: (m - n) => m0 <-{m}.
elim: n => [|n IHn]; first by rewrite bin0 !mul1n.
by rewrite -mulnA mulnCA mulnA -mul_Sm_binm -mulnA IHn.
Qed.

(* In fact the only exception is m = 0 and n = 1 *)
Lemma bin_factd : forall m n, 1 < n ->
    bin m n  = fact m %/ (fact n * fact (m - n)).
Proof.
move=> m n Hn.
case: (leqP n m) => Hmn.
  rewrite -(bin_fact Hmn) mulnK //.
  by exact (ltn_mul (fact_gt0 _) (fact_gt0 _)).
have->: m - n = 0 by apply/eqP; rewrite subn_eq0 ltnW.
by rewrite bin_small // fact0 muln1 divn_small // fact_smonotone.
Qed.

Lemma bin_sub : forall n m, n <= m -> bin m (m - n) = bin m n.
Proof.
move=> n m le_n_m; apply/eqP; move/eqP: (bin_fact (leq_subr n m)).
by rewrite subKn // -(bin_fact le_n_m) !mulnA mulnAC !eqn_pmul2r // fact_gt0.
Qed.

Lemma binSn : forall n, bin n.+1 n = n.+1.
Proof. by move=> n; rewrite -bin_sub ?leqnSn // subSnn bin1. Qed.

Lemma bin2 : forall n, bin n 2 = (n * n.-1)./2.
Proof. by case=> //= n; rewrite -{3}[n]bin1 mul_Sm_binm mul2n half_double. Qed.

Lemma bin2odd : forall n, odd n -> bin n 2 = n * n.-1./2.
Proof. by case=> // n oddn; rewrite bin2 -!divn2 divn_mulA ?dvdn2. Qed.

Lemma prime_dvd_bin : forall k p, prime p -> 0 < k < p -> p %| bin p k.
Proof.
move=> k p p_pr; case/andP=> k_gt0 lt_k_p; have def_p := ltn_predK lt_k_p.
have: p %| p * bin p.-1 k.-1 by rewrite dvdn_mulr.
by rewrite -def_p mul_Sm_binm def_p prednK // euclid // gtnNdvd.
Qed.

Lemma triangular_sum : forall n, \sum_(0 <= i < n) i = bin n 2.
Proof.
by elim=> [|n IHn]; [rewrite big_geq | rewrite big_nat_recr IHn binS bin1].
Qed.

Lemma textbook_triangular_sum : forall n, \sum_(0 <= i < n) i = bin n 2.
Proof.
move=> n; rewrite bin2; apply: canRL half_double _.
rewrite -addnn {1}big_nat_rev -big_split big_mkord /= ?add0n.
rewrite (eq_bigr (fun _ => n.-1)); first by rewrite sum_nat_const card_ord.
by case: n => [|n] [i le_i_n] //=; rewrite subSS subnK.
Qed.

Theorem Pascal : forall a b n,
  (a + b) ^ n = \sum_(i < n.+1) (bin n i * (a ^ (n - i) * b ^ i)).
Proof.
move=> a b; elim=> [|n IHn]; rewrite big_ord_recl muln1 ?big_ord0 //.
rewrite expnS {}IHn /= muln_addl !big_distrr /= big_ord_recl muln1 subn0.
rewrite !big_ord_recr /= !binn !subnn bin0 !subn0 !mul1n -!expnS -addnA.
congr (_ + _); rewrite addnA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite mulnCA (mulnA a) -expnS -ltn_subS //.
by rewrite (mulnC b) -2!mulnA -expnSr -muln_addl.
Qed.
Definition expn_addl := Pascal.

Lemma subn_exp : forall m n k,
  m ^ k - n ^ k = (m - n) * (\sum_(i < k) m ^ (k.-1 -i) * n ^ i).
Proof.
move=> m n [|k]; first by rewrite big_ord0.
rewrite muln_subl !big_distrr big_ord_recl big_ord_recr /= subn0 muln1.
rewrite subnn mul1n -!expnS -subn_sub; congr (_ - _).
set F := fun _ => _ : nat; rewrite (eq_bigr F) ?addnK {}/F // => i _.
by rewrite mulnCA -expnS mulnA -expnS -ltn_subS.
Qed.

Lemma predn_exp : forall m k, (m ^ k).-1 = m.-1 * (\sum_(i < k) m ^ i).
Proof.
move=> m k; rewrite -!subn1 -{1}(exp1n k) subn_exp; congr (_ * _).
symmetry; rewrite (reindex_inj rev_ord_inj); apply: eq_bigr => i _ /=.
by rewrite -subn1 subn_sub exp1n muln1.
Qed.
