Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths connect finfun ssralg bigops finset.
Require Import groups normal group_perm automorphism action.
Require Import commutators cyclic center sylow schurzass.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma p_part_0 : forall p, p_part p 0 = 1.
Proof. by move=> p; rewrite /p_part lognE andbF. Qed.

Lemma p_part_1 : forall p, p_part p 1 = 1.
Proof. by move=> p; rewrite /p_part lognE andbC dvdn1; case: eqP => // ->. Qed.

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

Lemma mem_primes : forall p n,
  (p \in primes n) = [&& prime p, n > 0 & p %| n].
Proof.
move=> p n; rewrite mem_filter; case prime => //.
by case: posnP => [-> //| n_pos]; rewrite dvdn_divisors.
Qed.

Lemma ltn_0log : forall p n, (0 < logn p n) = (p \in primes n).
Proof. by move=> p n; rewrite lognE -mem_primes; case: {+}(p \in _). Qed.

Lemma sorted_primes : forall n, sorted ltn (primes n).
Proof. by move=> n; rewrite !(sorted_filter ltn_trans, sorted_ltn_iota). Qed.

Lemma eq_primes : forall m n, (primes m =i primes n) <-> (primes m = primes n).
Proof.
move=> m n; split=> [eqpr| -> //].
by apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes.
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

Import GroupScope.

Section MoreHall.
  
Variable gT : finGroupType.

Definition hall_for pi (G H : {set gT}) :=
  [&& H \subset G, all pi (primes #|H|) & all (predC pi) (primes #|G : H|)].

Lemma hall_for_hall : forall pi (G H : {group gT}),
  hall_for pi G H -> hall G H.
Proof.
move=> pi G H; case/and3P=> sHG piH pi'H'; rewrite /hall sHG group_divn //.
have [Hpos H'pos]: 0 < #|H| /\ 0 < #|G : H|.
  by apply/andP; rewrite -ltn_0mul LaGrange.
rewrite /coprime /= eqn_leq ltn_0gcd Hpos andbT leqNgt.
apply/negP; move/prime_pdiv; set p := pdiv _ => pr_p.
have p_div : p %| _ := dvdn_trans (dvdn_pdiv _) _.
have pi_p: pi p.
  by apply: (allP piH); rewrite mem_primes pr_p Hpos p_div // dvdn_gcdl.
case/allPn: pi'H'; exists p; rewrite ?negbK //.
by rewrite mem_primes pr_p H'pos p_div ?dvdn_gcdr.
Qed.

Lemma hall_hall_for : forall G H : {group gT},
  hall G H -> exists pi, hall_for pi G H.
Proof.
move=> G H; case/andP=> sHG; rewrite group_divn // => coHG.
exists (mem (primes #|H|) : pred nat); apply/and3P; split=> //.
  exact/allP.
apply/allP=> p; rewrite /= !mem_primes; case/and3P=> pr_p _ p_H'.
rewrite pr_p pos_card_group /=; apply/negP=> p_H.
by move/prime_gt1: pr_p; rewrite ltnNge dvdn_leq // -(eqnP coHG) dvdn_gcd.
Qed.

Lemma hall_for_part : forall pi (G H : {group gT}),
  hall_for pi G H -> #|H| = pi_part pi #|G|.
Proof.
move=> pi G H; case/and3P=> sHG piH pi'H'.
rewrite -(LaGrange sHG) pi_part_mul ?LaGrange //.
rewrite {2}/pi_part big_hasC ?muln1 -?all_predC //.
by rewrite /pi_part -big_filter (all_filterP piH) prod_p_parts.
Qed.

Definition pi_subgroup pi (G H : {group gT}) :=
  (H \subset G) && all pi (primes #|H|).

End MoreHall.

Lemma HallSolvable : forall pi (gT : finGroupType) (G : {group gT}),
  solvable G -> exists2 H : {group gT}, hall_for pi G H
                & forall K : {group gT}, pi_subgroup pi G K ->
                  exists2 x, x \in G & K \subset H :^ x.
Proof.
move=> pi gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn solG.
case trG: (trivg G); last move/idPn: trG => trG.
  exists G; rewrite (trivGP _ trG).
    by rewrite /hall_for -group_divn subset_refl // cards1.
  move=> K; case/andP; move/trivgP=> ->{K} _.
  by exists (1 : gT); rewrite ?conjs1g ?sub1set set11.
case: (solvable_norm_abel solG (normalsub_refl _)) => // M [sMG nMG ntM [abelM]].
set p := pdiv #|M| => elemM.
have pr_p: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
have{elemM} pM: primes #|M| = [:: p].
  apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes // => q.
  rewrite mem_primes mem_seq1 pos_card_group /=.
  apply/andP/eqP=> [[pr_q q_M] | ->]; last by rewrite dvdn_pdiv.
  case: (cauchy pr_q q_M) => x; case/andP=> Mx; move/eqP=> oxp.
  have:= elemM _ Mx; rewrite [#[x]]oxp; case/primeP: pr_p => _ pr_p.
  by move/pr_p; case/orP; move/eqP=> // q1; rewrite q1 in pr_q.
pose Gb := (G / M)%G; case: (IHn _ Gb) => [||Hb]; try exact: solvable_quo.
  rewrite -[#|_|]mul1n card_quotient; last by case/andP: nMG.
  apply: leq_trans leGn; have:= pos_card_group G.
  rewrite -(LaGrange sMG) ltn_0mul; case/andP=> _ M'pos.
  by rewrite ltn_pmul2r // ltnNge -trivg_card.
case/and3P=> [sHbGb piHb pi'Hb'] transHb.
case: (inv_quotientS nMG sHbGb) => H def_H sMH sHG.
have{transHb} transH: forall K : {group gT}, pi_subgroup pi G K ->
  exists2 x, x \in G & K \subset H :^ x.
- move=> K; case/andP=> sKG piK.
  have nMK: K \subset 'N(M) by apply: subset_trans sKG _; case/andP: nMG.
  case: (transHb (K / M)%G) => [|xb Gxb sKHxb].
    rewrite /pi_subgroup morphimS //.
    apply/allP=> q; rewrite mem_primes; case/and3P=> pr_q _ q_n.
    apply: (allP piK); rewrite mem_primes pr_q pos_card_group /=.
    apply: (dvdn_trans q_n); rewrite -(isog_card (second_isom nMK)) /=.
    have sKMK := subsetIr M K.
    rewrite -(LaGrange sKMK) card_quotient ?dvdn_mull //.
    by apply/normalP=> x Kx; rewrite conjIg (normalP nMK) // conjGid.
  case/morphimP: Gxb => x Nx Gx /= def_x; exists x => //.
  apply/subsetP=> y Ky.
  have: y \in coset_of M y by rewrite coset_ofN (subsetP nMK, rcoset_refl).
  have: coset_of M y \in (H :^ x) / M.
    rewrite /quotient morphimJ //=.
    rewrite def_x def_H in sKHxb; apply: (subsetP sKHxb).
    by rewrite /= -coset_of_norm mem_imset.
  case/morphimP=> z Nz Hxz ->.
  rewrite coset_ofN //; case/rcosetP=> t Mt ->; rewrite groupMl //.
  by rewrite mem_conjg (subsetP sMH) // -mem_conjg (normgP Nx).
have{pi'Hb'} pi'H': all (predC pi) (primes #|G : H|).
  move: pi'Hb'; rewrite -!group_divn // def_H !card_quotient //; last first.
  - by case/andP: nMG.
  - by apply: (subset_trans sHG); case/andP: nMG.
  by rewrite -(divn_pmul2l (pos_card_group M)) !LaGrange.
case pi_p: (pi p).
  exists H => //; apply/and3P; split=> //.
  rewrite -(LaGrange sMH) -card_quotient //; last first.
    case/andP: nMG => _; exact: subset_trans.
  rewrite -[H / M]/(val (H / M)%G) -def_H /=.
  apply/allP=> q; rewrite primes_mul ?pos_card_group // pM mem_seq1.
  by case/predU1P => [-> //|]; move/(allP piHb).
case: (ltnP #|H| #|G|) => [ltHG | leGH {n IHn leGn transH}].
  case: (IHn _ H (leq_trans ltHG leGn)) => [|H1].
    exact: solvable_sub solG.
  case/and3P=> sH1H piH1 pi'H1' transH1.
  have sH1G: H1 \subset G by exact: subset_trans sHG.
  exists H1=> [|K piK].
    apply/and3P; split => //; apply/allP=> q; rewrite -group_divn //.
    rewrite -(LaGrange sHG) -(LaGrange sH1H) -mulnA divn_mulr // primes_mul //.
    case/orP; [exact: (allP pi'H1') | exact: (allP pi'H')].
  case: (transH K piK) => x Gx def_K.
  case: (transH1 (K :^ x^-1)%G) => [|y Hy def_K1].
    apply/andP; rewrite card_conjg; split; last by case/andP: piK.
    by rewrite -(conjsgK x H) conjSg.
  exists (y * x); first by rewrite groupMr // (subsetP sHG).
  by rewrite -(conjsgKV x K) conjsgM conjSg.
have{leGH Gb sHbGb sHG sMH pi'H'} eqHG: H = G.
  by apply/eqP; rewrite -val_eqE eqset_sub_card sHG.
have{H Hb def_H eqHG piHb} hallM: hall_for (predC pi) G M.
  rewrite /hall_for sMG pM /= pi_p -card_quotient //; last by case/andP: nMG.
  by apply/allP=> q GMq; rewrite /= negbK (allP piHb) // def_H eqHG.
case/splitgP: (SchurZass_split (hall_for_hall hallM) nMG) => H trMH defG.
have sHG: H \subset G by rewrite -defG mulG_subr.
exists H => [|K]; last case/andP=> sKG piK.
  case/andP: hallM => _; rewrite /hall_for sHG -!group_divn // -defG.
  rewrite (card_mulG_trivP _ _ trMH) divn_mulr ?divn_mull ?pos_card_group //.
  by rewrite andbC all_predC has_predC negbK.
pose G1 := (K <*> M)%G; pose K1 := (H :&: G1)%G.
have nMK: K \subset 'N(M) by apply: subset_trans sKG _; case/andP: nMG.
have defG1: M * K = G1 by rewrite -normC -?norm_mulgenE.
have sK1G1: K1 \subset M * K by rewrite defG1 subsetIr.
have coMK: coprime #|M| #|K|.
  rewrite -[#|M|]prod_p_parts // pM big_seq1 coprime_expl // prime_coprime //.
  apply/negP=> pK; case/idP: pi_p; apply: (allP piK).
  by rewrite mem_primes pr_p pos_card_group.
case: (SchurZass_trans_sol _ nMK sK1G1 coMK) => [||x Mx defK1].
- exact: solvable_sub solG.
- apply/eqP; rewrite -(eqn_pmul2l (pos_card_group M)).
  rewrite -(card_mulG_trivP _ _ _); last first.
    by apply: subset_trans trMH; rewrite setIA subsetIl.
  rewrite -coprime_card_mulG // defG1; apply/eqP; congr #|(_ : {set _})|.
  rewrite group_modl; last by rewrite -defG1 mulG_subl.
  by apply/setIidPr;  rewrite defG gen_subG subUset sKG.
exists x^-1; first by rewrite groupV (subsetP sMG).
by rewrite -(_ : K1 :^ x^-1 = K) ?(conjSg, subsetIl) // defK1 conjsgK.
Qed.

Module AfterHall. End AfterHall.

Section HallCorollaries.

Variable (gT : finGroupType).

Corollary HallExist : forall pi (G : {group gT}),
  solvable G -> exists H : {group gT}, hall_for pi G H.
Proof. by move=> pi G solG; case: (HallSolvable pi solG) => H; exists H. Qed.

Corollary HallConj : forall pi (G H1 H2 : {group gT}),
  solvable G -> hall_for pi G H1 -> hall_for pi G H2 ->
  exists2 x, x \in G & H1 = (H2 :^ x)%G.
Proof.
move=> pi G H1 H2 solG; case: (HallSolvable pi solG) => H hallH transH.
have conjH: forall K : {group gT},
  hall_for pi G K -> exists2 x, x \in G & K = (H :^ x)%G.
- move=> K hallK; case: (transH K) => [|x Gx sKH].
    by apply/andP; case/and3P: hallK.
  exists x => //; apply/eqP; rewrite -val_eqE eqset_sub_card sKH.
  by rewrite card_conjg (hall_for_part hallH) (hall_for_part hallK) /=.
case/conjH=> x1 Gx1 ->{H1}; case/conjH=> x2 Gx2 ->{H2}.
exists (x2^-1 * x1); first by rewrite groupMl ?groupV.
by apply: val_inj; rewrite /= conjsgM conjsgK.
Qed.

Lemma hall_for_norm_conj : forall pi (G H : {group gT}) x,
  x \in 'N(G) -> hall_for pi G (H :^ x) = hall_for pi G H.
Proof.
move=> pi G H x Nx; rewrite /hall_for -{1 2}(normgP Nx) conjSg.
by case sHG: (H \subset G) => //=; rewrite -!group_divn ?card_conjg // conjSg.
Qed.

Lemma hall_for_conj : forall pi (G H : {group gT}) x,
  x \in G -> hall_for pi G (H :^ x) = hall_for pi G H.
Proof. by move=> pi G *; rewrite hall_for_norm_conj ?(subsetP (normG G)). Qed.

Corollary HallSubset : forall pi (G K : {group gT}),
  solvable G -> pi_subgroup pi G K ->
    exists2 H : {group gT}, hall_for pi G H & K \subset H.
Proof.
move=> pi G K solG; case: (HallSolvable pi solG) => H hallH transH.
by case/transH=> x Gx sKHx; exists (H :^ x)%G; rewrite ?hall_for_conj.
Qed.

Lemma HallFrattini : forall pi (G K H : {group gT}),
  solvable K -> K <| G -> hall_for pi K H -> K * 'N_G(H) = G.
Proof.
move=> pi G K H solK; case/andP=> sKG nKG hallH.
have sHG: H \subset G by apply: subset_trans sKG; case/andP: hallH.
rewrite setIC group_modl //; apply/setIidPr; apply/subsetP=> x Gx.
pose H1 := (H :^ x^-1)%G; have hallH1: hall_for pi K H1.
  by rewrite hall_for_norm_conj // groupV (subsetP nKG).
case: (HallConj solK hallH hallH1) => y Ky defH.
rewrite -(mulKVg y x) mem_mulg //; apply/normgP.
by rewrite conjsgM {1}defH conjsgK conjsgKV.
Qed.

Lemma hall_maximal : forall pi (G H K : {group gT}),
  hall_for pi G H -> pi_subgroup pi G K -> H \subset K -> K = H.
Proof.
move=> pi G H K hallH; case/andP=> sKG piK sHK; apply/eqP.
suff: hall_for pi G K.
  rewrite eq_sym -val_eqE eqset_sub_card sHK (hall_for_part hallH) /=.
  by move/hall_for_part->.
rewrite /hall_for sKG piK; apply/allP=> p K'p.
case/and3P: hallH => sHG _; move/allP; apply.
rewrite -group_divn // -(LaGrange sKG) -(LaGrange sHK) -mulnA divn_mulr //.
by rewrite primes_mul // K'p orbT.
Qed.

Lemma HallSubnormal : forall pi (G K H : {group gT}),
  solvable G -> K <| G -> hall_for pi G H -> hall_for pi K (H :&: K).
Proof.
move=> pi G K H solG; case/andP=> sKG nKG hallH.
case: (HallExist pi (solvable_sub sKG solG)) => H1 hallH1.
have piH1: pi_subgroup pi G H1.
  case/and3P: hallH1 => sH1K piH1 _; apply/andP; split=> //.
  exact: subset_trans sKG.
case: (HallSubset solG piH1) => H2 hallH2 sH12.
case: (HallConj solG hallH hallH2) => x; move/(subsetP nKG) => Nx ->.
rewrite -{2}(normgP Nx) -conjIg hall_for_norm_conj //.
rewrite (@hall_maximal _ _ _ (H2 :&: K)%G hallH1) //.
  rewrite /pi_subgroup subsetIr; apply/allP=> p HKp.
  case/and3P: hallH2 => _ piH2 _; apply: (allP piH2).
  have: H2 :&: K \subset H2 by rewrite subsetIl.
  by move/LaGrange <-; rewrite primes_mul // HKp.
by rewrite subsetI sH12; case/andP: hallH1.
Qed.

End HallCorollaries.


