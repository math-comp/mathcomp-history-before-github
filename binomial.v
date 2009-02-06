Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigops fintype ssralg.
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

Lemma wilson p: 1 < p -> (prime p <-> p %| (fact (p.-1)).+1).
Proof.
have HF: forall p, 0 < p -> fact p.-1 = \prod_(0 <= i < p | i != 0) i.
  move=> p Hp; rewrite -big_filter fact_prod; symmetry; apply: congr_big=> //.
  rewrite /index_iota subn1 -[p]prednK //=; apply/all_filterP.
  by rewrite all_predC has_pred1 mem_iota.
move=> p Hp; split; last first.
  case: p Hp => //; (do 4 (case=> //)) => p Hp; set p1 := _.+4.
  case Hp1: (prime p1); rewrite // -addn1 dvdn_addr ?dvdn1 // HF //.
  move/idPn: Hp1; case/primePn => //; case=> d Hd1 Hd2.
  pose d' := p1 %/ d; have Hd'd: d' * d = p1 := (divnK  Hd2).
  have Hd3: d < p1 by case/andP: Hd1.
  have Hd4: d != 0 by case: (d) Hd1.
  rewrite big_mkord (bigD1 (Ordinal Hd3)) //=.
  case: (d =P d') => He; last first.
    have Hd'1: d' != 0 by apply/negP=> HH; move: Hd'd; rewrite (eqP HH).
    have Hd'2: d' < p1; first rewrite -Hd'd -{1}[d']muln1 ltn_mul2l.
      by case/andP: Hd1 => -> _; case: (d') Hd'1.
    rewrite (bigD1 (Ordinal Hd'2)) //=.
      by rewrite mulnA [d * _]mulnC Hd'd dvdn_mulr.
    by rewrite Hd'1 eq_sym; apply/eqP; case.
  have Hd5: 2 * d < p1; first rewrite -Hd'd -He ltn_mul2r.
    by move: Hd1 Hd'd; rewrite -He; case: (d) => //; do 2 (case=> //).
  have Hd6: 2 * d !=0 by case: (d) Hd4.
  rewrite (bigD1 (Ordinal Hd5)) //=.
    by rewrite -{1}[2 * d]mulnC !mulnA {1}He Hd'd -mulnA dvdn_mulr. 
  by rewrite Hd6 -val_eqE /= neq_ltn orbC ltn_Pmull // lt0n.
move=> p_prime; have lt1p := prime_gt1 p_prime; have lt0p := ltnW lt1p.
pose Fp1 := Ordinal lt1p; pose Fp0 := Ordinal lt0p.
have ltp1p: p.-1 < p by [rewrite prednK]; pose Fpn1 := Ordinal ltp1p.
case: (Fp1 =P Fpn1); first by rewrite -{2 3}[p]prednK => [[<-]|].
move/eqP=> nFp1n1.
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
  move=> i; rewrite -val_eqE /= -lt0n => i_pos; apply: val_inj => /=.
  rewrite modn_mulml; case: egcdnP => //= _ km -> _; rewrite {km}modn_addl_mul.
  suff: coprime i p by move/eqnP->; rewrite modn_small.
  rewrite coprime_sym prime_coprime //; apply/negP; move/(dvdn_leq i_pos).
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
  by apply/eqP; rewrite -addn1 -modn_addml mod_fact addn1 prednK // modnn.
rewrite HF //.
have: Monoid.morphism 1 Fp1 muln mFpM toFp; last move/(@big_morph _ _ _ _)->.
  by split=> [|i j]; apply: val_inj; rewrite /= (modn_mul2m, modn_small).
rewrite big_mkord (eq_bigr id) => [|i _]; last by apply: val_inj => /=.
pose ltv i := vFp i < i; rewrite (bigID ltv) -/mFpM [mFpM _ _]mFpC.
rewrite (bigD1 Fp1) -/mFpM; last by rewrite [ltv _]ltn_neqAle vFpId.
rewrite [mFpM _ _]mFp1 (bigD1 Fpn1) -?mFpA -/mFpM; last first.
  rewrite -lt0n -ltnS prednK // lt1p.
  by rewrite [ltv _]ltn_neqAle vFpId eqxx orbT eq_sym.
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

Lemma bin_posnat: forall m n, 0 < bin m n == (n <= m).
Proof.
elim=> [| m Hrec]; case=> // n.
rewrite binS ltn_0add !(eqP (Hrec _)) ltnS ltn_neqAle andbC.
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
by rewrite [fact _ * _]mulnC; move/eqP; rewrite eqn_mul2r eqn_mul0 !eqn0Ngt !ltn_0fact.
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
rewrite !mulnA; congr muln; rewrite [a * _]mulnC; congr muln.
case: (leqP x.+1 n) => E1; last by rewrite bin_small.
by rewrite leq_subS // expnS mulnA.
Qed.
