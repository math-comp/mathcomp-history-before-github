Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigops fintype.
Require Import div prime choice.

(**************************************************************************)
(* This files contains the definitions of:                                *)
(* -binomial: definitions upto Pascal formula                             *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Factorial lemma **)
Lemma fact0 : fact 0 = 1.
Proof. by done. Qed.

Lemma factS : forall n, fact n.+1  = n.+1 * fact n.
Proof. by done. Qed.

Lemma fact_prod n : fact n = \prod_(1 <= i < n.+1) i.
Proof.
elim=> [|n Hrec] //; first by rewrite big_nil.
by apply sym_equal; rewrite factS Hrec // !big_add1 big_nat_recr /= mulnC.
Qed.

Theorem Wilson's_Theorem : forall p, p > 1 -> prime p = (p %| fact p.-1 + 1).
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
  by rewrite orbC dvdn_addr ?dvdn_mulr // dvdn1 => ->.
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
    by rewrite /= -!val_eqE /= -{2}[p]prednK //= modn_small //= -(subnK lt1p).
  rewrite 2!eqFp -euclid //= -[_ - p.-1]subSS prednK //.
  have lt0i: 0 < i by rewrite lt0n.
  rewrite -addnS addKn -addn_subA // muln_addl -{2}(addn1 i) -subn_sqr.
  rewrite addn_subA ?leq_sqr // mulnS -addnA -mulnn -muln_addl.
  rewrite -(subnK (le_pmFp (vFp i) i)) muln_addl addnA addnC.
  rewrite -[1 ^ 2]/(Fp1 : nat) -addn_subA // dvdn_addl.
    by rewrite euclid // -eqFp eq_sym orbC /dvdn Fp_mod eqn0Ngt lt0i.
  by rewrite -eqn_mod_dvd // Fp_mod modn_addl -(vFpV _ ni0) eqxx.
suffices [mod_fact]: toFp (fact p.-1) = Fpn1.
  by rewrite /dvdn -modn_addml mod_fact addn1 prednK // modnn.
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
by rewrite -{2}[mFp]/mFpM -big_split big1 ?mFp1r //= => i; case/andP; auto.
Qed.

(** Binomial *)

Definition bin_rec := fix loop (m n : nat) {struct m} :=
  if n is n'.+1 then (if m is m'.+1 then loop m' n + loop m' n' else 0)
  else 1.

Definition bin m n := nosimpl (bin_rec m n).

Lemma bin0: forall n,  bin n 0 = 1.
Proof. by elim. Qed.

Lemma binS: forall m n,  bin m.+1 n.+1 = bin m n.+1 + bin m n.
Proof. by done. Qed.

Lemma bin_small: forall m n, m < n ->  bin m n = 0.
Proof.
elim=> [| m Hrec]; case => // n Hn; rewrite binS !Hrec //.
by apply: ltn_trans Hn.
Qed.

Lemma binn: forall n,  bin n n = 1.
Proof. by elim=> [| n Hrec] //; rewrite binS bin_small. Qed.

Lemma bin_gt0: forall m n, 0 < bin m n == (n <= m).
Proof.
elim=> [| m Hrec]; case=> // n.
rewrite binS addn_gt0 !(eqP (Hrec _)) ltnS ltn_neqAle andbC.
by case: (_ <= _) => //; rewrite orbT.
Qed.

Lemma bin_fact: forall m n, n <= m -> bin m n * (fact n * fact (m - n)) = fact m.
Proof.
move=> m n Hm; rewrite -(subnK Hm) addKn.
set p := m - n.
elim: {m Hm} n p => [| m Hrec].
  by case=> // n; rewrite bin0 // fact0 !mul1n add0n.
elim=> [| n Hrec1].
  by rewrite addn0 fact0 muln1 binS factS bin_small // binn add0n mul1n.
by rewrite addnS binS muln_addl {1}(factS n) {2}(factS m)
          -2!{1}(mulnCA (n.+1)) -(mulnA (m.+1)) -{1}(mulnCA (m.+1))
          Hrec1 addSnnS Hrec -muln_addl factS addnC addSn.
Qed.

Lemma bin_sub: forall n m, n <= m -> bin m n = bin m (m - n).
Proof.
move=> n m Hmn; apply/eqP.
move: (bin_fact Hmn); rewrite -(bin_fact (leq_subr n m)) subKn //.
by rewrite [fact _ * _]mulnC; move/eqP; rewrite eqn_mul2r muln_eq0 !eqn0Ngt !fact_gt0.
Qed.

Theorem exp_pascal : forall a b n,
  (a + b) ^ n = \sum_(i < n.+1) (bin n i * (a ^ (n - i) * b ^ i)).
Proof.
move=> a b n; pose f n i := bin n i * (a ^ (n - i) * b ^ i).
rewrite -!(big_mkord xpredT (f n)).
elim: n => [| n Hrec]; first by rewrite big_nat_recr big_geq.
rewrite big_nat_recr /= big_nat_recl /f /= subn0 subnn 
       !expn0 binn bin0 !mul1n !muln1.
rewrite expnS {}Hrec muln_addl !big_distrr /=.
rewrite big_nat_recl /f /= bin0 mul1n subn0 expn0 muln1 -expnS.
rewrite addnC big_nat_recr /= binn subnn expn0 !mul1n -expnS.
have->: forall x y z t, x + y + (z + t) = z + (x + t) + y 
  by move=> x y z t; ring.
do 2 congr addn; rewrite -big_split; apply: eq_big => //= x _; apply sym_equal.
rewrite binS muln_addl addnC; congr addn; first by rewrite expnS subSS; ring.
rewrite expnS !mulnA; congr muln; rewrite [a * _]mulnC; congr muln.
case: (leqP x.+1 n) => E1; last by rewrite bin_small.
by rewrite leq_subS // expnS mulnA.
Qed.
