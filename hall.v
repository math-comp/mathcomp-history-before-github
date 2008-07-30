Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div prime.
Require Import fintype paths ssralg bigops finset.
Require Import groups morphisms normal cyclic sylow schurzass.

(* Require Import connect finfun group_perm automorphism action center. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section MoreHall.
  
Variable gT : finGroupType.

Definition hall_for pi (G H : {set gT}) :=
  [&& H \subset G, all pi (primes #|H|) & all (predC pi) (primes #|G : H|)].

Lemma hall_for_hall : forall pi (G H : {group gT}),
  hall_for pi G H -> hall G H.
Proof.
move=> pi G H; case/and3P=> sHG piH pi'H'; rewrite /hall sHG.
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
move=> G H; case/andP=> sHG coHG; exists (mem (primes #|H|) : pred nat).
apply/and3P; split=> //; first exact/allP.
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
case: (solvable_norm_abel solG (normal_refl _)) => // M [sMG nMG ntM].
case/andP=> abelM; set p := pdiv #|M|; move/forallP=> elemM.
have pr_p: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
have{elemM} pM: primes #|M| = [:: p].
  apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes // => q.
  rewrite mem_primes mem_seq1 pos_card_group /=.
  apply/andP/eqP=> [[pr_q q_M] | ->]; last by rewrite dvdn_pdiv.
  case: (cauchy pr_q q_M) => x; case/andP=> Mx; move/eqP=> oxp.
  have:= elemM x; rewrite Mx [#[x]]oxp; case/primeP: pr_p => _ pr_p.
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
    by apply/normsP=> x Kx; rewrite conjIg (normsP nMK) // conjGid.
  case/morphimP: Gxb => x Nx Gx /= def_x; exists x => //.
  apply/subsetP=> y Ky.
  have: y \in coset_of M y by rewrite coset_ofN (subsetP nMK, rcoset_refl).
  have: coset_of M y \in (H :^ x) / M.
    rewrite /quotient morphimJ //=.
    rewrite def_x def_H in sKHxb; apply: (subsetP sKHxb).
    by rewrite /= -coset_of_norm mem_imset.
  case/morphimP=> z Nz Hxz ->.
  rewrite coset_ofN //; case/rcosetP=> t Mt ->; rewrite groupMl //.
  by rewrite mem_conjg (subsetP sMH) // -mem_conjg (normP Nx).
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
move=> pi G H x Nx; rewrite /hall_for -{1 2}(normP Nx) conjSg.
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
rewrite -(mulKVg y x) mem_mulg //; apply/normP.
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
rewrite -{2}(normP Nx) -conjIg hall_for_norm_conj //.
rewrite (@hall_maximal _ _ _ (H2 :&: K)%G hallH1) //.
  rewrite /pi_subgroup subsetIr; apply/allP=> p HKp.
  case/and3P: hallH2 => _ piH2 _; apply: (allP piH2).
  have: H2 :&: K \subset H2 by rewrite subsetIl.
  by move/LaGrange <-; rewrite primes_mul // HKp.
by rewrite subsetI sH12; case/andP: hallH1.
Qed.

End HallCorollaries.


