Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div prime.
Require Import fintype paths ssralg bigops finset.
Require Import groups morphisms normal pgroups cyclic sylow schurzass.

(* Require Import connect finfun group_perm automorphism action center. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Lemma HallSolvable : forall pi (gT : finGroupType) (G : {group gT}),
  solvable G -> exists2 H : {group gT}, hall pi G H
                & forall K : {group gT}, K \subset G -> pgroup pi K ->
                  exists2 x, x \in G & K \subset H :^ x.
Proof.
move=> pi gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn solG.
case trG: (trivg G); last move/idPn: trG => trG.
  exists G => [|K]; rewrite (trivGP _ trG); last move/trivGP=> -> {K} _.
    by rewrite /hall subset_refl cards1 part_p'_nat.
  by exists (1 : gT); rewrite ?conjs1g ?sub1set set11.
case: (solvable_norm_abelem solG (normal_refl _)) => // M [sMG nMG ntM].
case/andP=> abelM; set p := pdiv #|M|; move/exponentP=> elemM.
have pr_p: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
have{elemM} pM: primes #|M| = [:: p].
  apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes // => q.
  rewrite mem_primes mem_seq1 pos_card_group /=.
  apply/andP/eqP=> [[pr_q q_M] | ->]; last by rewrite dvdn_pdiv.
  case: (Cauchy pr_q q_M) => x Mx oxp.
  apply/eqP; rewrite eqn_leq pdiv_min_dvd ?prime_gt1 1?dvdn_leq ?ltn_0prime //.
  by rewrite -oxp order_dvd elemM.
pose Gb := (G / M)%G; case: (IHn _ Gb) => [||Hb]; try exact: solvable_quo.
  rewrite -[#|_|]mul1n card_quotient; last by case/andP: nMG.
  apply: leq_trans leGn; have:= ltn_0group G.
  rewrite -(LaGrange sMG) ltn_0mul; case/andP=> _ M'pos.
  by rewrite ltn_pmul2r // ltnNge -trivg_card.
rewrite hallE; case/and3P=> [sHbGb piHb pi'Hb'] transHb.
case: (inv_quotientS nMG sHbGb) => H def_H sMH sHG.
have{transHb} transH: forall K : {group gT},
  K \subset G -> pgroup pi K -> exists2 x, x \in G & K \subset H :^ x.
- move=> K sKG piK.
  have nMK: K \subset 'N(M) by apply: subset_trans sKG _; case/andP: nMG.
  case: (transHb (K / M)%G) => [||xb Gxb sKHxb]; first exact: morphimS.
    exact: morphim_pgroup.
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
have{pi'Hb'} pi'H': p_nat pi^' #|G : H|.
  move: pi'Hb'; rewrite -!group_divn // def_H !card_quotient //; last first.
  - by case/andP: nMG.
  - by apply: (subset_trans sHG); case/andP: nMG.
  by rewrite -(divn_pmul2l (ltn_0group M)) !LaGrange.
case pi_p: (p \in pi).
  exists H => //; rewrite hallE; apply/and3P; split=> //.
  rewrite /pgroup -(LaGrange sMH) -card_quotient //; last first.
    case/andP: nMG => _; exact: subset_trans.
  rewrite p_nat_mul {1}/p_nat pM ltn_0group /= pi_p.
  by rewrite def_H in piHb.
case: (ltnP #|H| #|G|) => [ltHG | leGH {n IHn leGn transH}].
  case: (IHn _ H (leq_trans ltHG leGn)) => [|H1].
    exact: solvable_sub solG.
  rewrite hallE; case/and3P=> sH1H piH1 pi'H1' transH1.
  have sH1G: H1 \subset G by exact: subset_trans sHG.
  exists H1=> [|K sKG piK].
    rewrite hallE; apply/and3P; split => //.
    rewrite -group_divn // -(LaGrange sHG) -(LaGrange sH1H) -mulnA.
    by rewrite divn_mulr // p_nat_mul pi'H1'.
  case: (transH K sKG piK) => x Gx def_K.
  case: (transH1 (K :^ x^-1)%G) => [||y Hy def_K1].
  - by rewrite sub_conjgV.
  - by rewrite /pgroup card_conjg.
  exists (y * x); first by rewrite groupMr // (subsetP sHG).
  by rewrite -(conjsgKV x K) conjsgM conjSg.
have{leGH Gb sHbGb sHG sMH pi'H'} eqHG: H = G.
  by apply/eqP; rewrite -val_eqE eqset_sub_card sHG.
have{H Hb def_H eqHG piHb} hallM: hall pi^' G M.
  rewrite hallE sMG /pgroup {1}/p_nat pM /= inE /= pi_p ltn_0group /=.
  apply: etrans piHb; rewrite -card_quotient ?normal_norm // -eqHG def_H.
  by rewrite p_natCK.
case/splitgP: (SchurZass_split (hall_is_hall hallM) nMG) => H trMH defG.
have sHG: H \subset G by rewrite -defG mulG_subr.
exists H => [|K sKG piK].
  apply: etrans hallM; rewrite !hallE sMG sHG /= -!group_divn // -defG andbC.
  by rewrite (card_mulG_trivP _ _ trMH) divn_mulr ?divn_mull // p_natCK.
pose G1 := (K <*> M)%G; pose K1 := (H :&: G1)%G.
have nMK: K \subset 'N(M) by apply: subset_trans sKG _; case/andP: nMG.
have defG1: M * K = G1 by rewrite -normC -?norm_mulgenE.
have sK1G1: K1 \subset M * K by rewrite defG1 subsetIr.
have coMK: coprime #|M| #|K|.
  rewrite coprime_sym (p_nat_coprime piK) //.
  by rewrite  /p_nat pM ltn_0group //= inE /= pi_p.
case: (SchurZass_trans_sol _ nMK sK1G1 coMK) => [||x Mx defK1].
- exact: solvable_sub solG.
- apply/eqP; rewrite -(eqn_pmul2l (ltn_0group M)).
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
  solvable G -> exists H : {group gT}, hall pi G H.
Proof. by move=> pi G solG; case: (HallSolvable pi solG) => H; exists H. Qed.

Corollary HallConj : forall pi (G H1 H2 : {group gT}),
  solvable G -> hall pi G H1 -> hall pi G H2 ->
  exists2 x, x \in G & H1 = (H2 :^ x)%G.
Proof.
move=> pi G H1 H2 solG; case: (HallSolvable pi solG) => H hallH transH.
have conjH: forall K : {group gT},
  hall pi G K -> exists2 x, x \in G & K = (H :^ x)%G.
- move=> K hallK; have:= hallK; rewrite hallE; case/and3P=> sKG piK _.
  case: (transH K sKG piK) => x Gx sKH; exists x => //.
  apply/eqP; rewrite -val_eqE eqset_sub_card sKH card_conjg leq_eqVlt.
  by case/andP: hallK => _; move/eqP->; case/andP: hallH => _ ->.
case/conjH=> x1 Gx1 ->{H1}; case/conjH=> x2 Gx2 ->{H2}.
exists (x2^-1 * x1); first by rewrite groupMl ?groupV.
by apply: val_inj; rewrite /= conjsgM conjsgK.
Qed.

Lemma hall_norm_conj : forall pi (G H : {group gT}) x,
  x \in 'N(G) -> hall pi G (H :^ x) = hall pi G H.
Proof.
by move=> pi G H x Nx; rewrite /hall card_conjg -{1}(normP Nx) conjSg.
Qed.

Lemma hall_conj : forall pi (G H : {group gT}) x,
  x \in G -> hall pi G (H :^ x) = hall pi G H.
Proof. by move=> pi G *; rewrite hall_norm_conj ?(subsetP (normG G)). Qed.

Corollary HallSubset : forall pi (G K : {group gT}),
  solvable G -> K \subset G -> pgroup pi K ->
    exists2 H : {group gT}, hall pi G H & K \subset H.
Proof.
move=> pi G K solG sKG; case: (HallSolvable pi solG) => H hallH transH.
by case/transH=> // x Gx sKHx; exists (H :^ x)%G; rewrite ?hall_conj.
Qed.

Lemma HallFrattini : forall pi (G K H : {group gT}),
  solvable K -> K <| G -> hall pi K H -> K * 'N_G(H) = G.
Proof.
move=> pi G K H solK; case/andP=> sKG nKG hallH.
have sHG: H \subset G by apply: subset_trans sKG; case/andP: hallH.
rewrite setIC group_modl //; apply/setIidPr; apply/subsetP=> x Gx.
pose H1 := (H :^ x^-1)%G; have hallH1: hall pi K H1.
  by rewrite hall_norm_conj // groupV (subsetP nKG).
case: (HallConj solK hallH hallH1) => y Ky defH.
rewrite -(mulKVg y x) mem_mulg //; apply/normP.
by rewrite conjsgM {1}defH conjsgK conjsgKV.
Qed.

Lemma hall_maximal : forall pi (G H K : {group gT}),
  hall pi G H -> K \subset G -> pgroup pi K -> H \subset K -> K = H.
Proof.
move=> pi G H K hallH sKG piK sHK; apply/eqP.
suff: hall pi G K.
  rewrite eq_sym -val_eqE eqset_sub_card sHK leq_eqVlt.
  by case/andP: hallH => _; move/eqP->; case/andP=> _ ->.
move: hallH; rewrite !hallE sKG piK; case/and3P=> _ _; apply: p_nat_dvdn.
rewrite -(dvdn_pmul2l (ltn_0group K)) LaGrange // -(LaGrange sHK) mulnAC.
by rewrite LaGrange (subset_trans sHK, dvdn_mulr).
Qed.

Lemma HallSubnormal : forall pi (G K H : {group gT}),
  solvable G -> K <| G -> hall pi G H -> hall pi K (H :&: K).
Proof.
move=> pi G K H solG; case/andP=> sKG nKG hallH.
case: (HallExist pi (solvable_sub sKG solG)) => H1 hallH1.
have [sH1G piH1]: H1 \subset G /\ pgroup pi H1.
  move: hallH1; rewrite hallE; case/and3P=> sH1K piH1 _; split=> //.
  exact: subset_trans sKG.
case: (HallSubset solG sH1G piH1) => H2 hallH2 sH12.
case: (HallConj solG hallH hallH2) => x; move/(subsetP nKG) => Nx ->.
rewrite -{2}(normP Nx) -conjIg hall_norm_conj //.
rewrite (@hall_maximal _ _ _ (H2 :&: K)%G hallH1) //; first exact: subsetIr.
  apply: pgroupS (subsetIl _ _) _.
  by move: hallH2; rewrite hallE; case/and3P.
by rewrite subsetI sH12; case/andP: hallH1.
Qed.

End HallCorollaries.


