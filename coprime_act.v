Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div prime paths.
Require Import fintype bigops finset groups morphisms automorphism normal action.
Require Import commutators pgroups cyclic sylow schurzass hall.

(* Require Import connect finfun ssralg group_perm center. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section InternalAction.

Variable pi : pred nat.
Variable gT : finGroupType.
Implicit Types G H K A X : {group gT}.

Lemma coprime_norm_cent : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| ->
  'N_G(A) = 'C_G(A).
Proof.
move=> A G nGA coGA; apply/eqP; rewrite eqset_sub andbC setIS ?cent_subset //=.
rewrite subsetI subsetIl /=; apply/centsP; apply/commG1P.
apply: subset_trans (coprime_trivg coGA); rewrite gen_subG.
apply/subsetP=> xy; case/imset2P=> x y; case/setIP=> Gx nAx Ay ->{xy}.
rewrite inE {1}commgEl commgEr (groupMr _ Ay) groupMl  ?groupV //.
by rewrite !memJ_norm ?groupV // ?(subsetP nGA, Gx).
Qed.

Lemma coprime_hall_exists : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  exists2 H : {group gT}, hall pi G H & A \subset 'N(H).
Proof.
move=> A G nGA coGA solG; case: (HallExist pi solG) => H hallH.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genS ?subsetUr.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
pose N := 'N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N.
  apply/normalP; rewrite subsetIr; split=> // x Nx.
  by rewrite conjIg (normP _) // (subsetP nGN, conjGid).
have NG_AG : G * N = A <*> G by apply: HallFrattini hallH => //; exact/andP.
have iGN_A: #|N| %/ #|G :&: N| = #|A|.
  rewrite group_divn ?subsetIr // -card_quotient; last by case/andP: nGN_N.
  rewrite (isog_card (second_isom nGN)) /= -quotient_mulg (normC nGN) NG_AG.
  rewrite card_quotient // -group_divn //= norm_mulgenE //.
  by rewrite coprime_card_mulG 1?coprime_sym // divn_mull.
have hallGN: is_hall N (G :&: N).
  rewrite /is_hall -group_divn subsetIr //= iGN_A.
  by move: coGA; rewrite -(LaGrangeI G N) coprime_mull; case/andP.
case/splitgP: {hallGN nGN_N}(SchurZass_split hallGN nGN_N) => B trBGN defN.
have{trBGN iGN_A} oBA: #|B| = #|A|.
  by rewrite -iGN_A -{1}defN (card_mulG_trivP _ _ trBGN) divn_mulr.
have sBN: B \subset N by rewrite -defN mulG_subr.
case: (SchurZass_trans_sol solG nGA _ coGA oBA) => [|x Gx defB].
  by rewrite -(normC nGA) -norm_mulgenE // -NG_AG -(mul1g B) mulgSS ?sub1G.
exists (H :^ x^-1)%G; first by rewrite hall_conj ?groupV.
apply/subsetP=> y Ay; have: y ^ x \in B by rewrite defB memJ_conjg.
move/(subsetP sBN); case/setIP=> _; move/normP=> nHyx.
by apply/normP; rewrite -conjsgM conjgCV invgK conjsgM nHyx.
Qed.

Lemma coprime_hall_trans : forall A G H1 H2,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  hall pi G H1 -> A \subset 'N(H1) ->
  hall pi G H2 -> A \subset 'N(H2) ->
  exists2 x, x \in 'C_G(A) & H1 = (H2 :^ x)%G.
Proof.
move=> A G H H' nGA coGA solG hallH nHA hallH'.
case: {hallH'}(HallConj solG hallH' hallH) => x Gx ->{H'} nHxA.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genS ?subsetUr.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
pose N := 'N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N.
  apply/normalP; rewrite subsetIr; split=> // y Ny.
  by rewrite conjIg (normP _) // (subsetP nGN, conjGid).
have NG_AG : G * N = A <*> G by apply: HallFrattini hallH => //; exact/andP.
have iGN_A: #|N : G :&: N| = #|A|.
  rewrite -card_quotient //; last by case/andP: nGN_N.
  rewrite (isog_card (second_isom nGN)) /= -quotient_mulg (normC nGN) NG_AG.
  rewrite card_quotient // -group_divn //= norm_mulgenE //.
  by rewrite coprime_card_mulG 1?coprime_sym // divn_mull.
have solGN: solvable (G :&: N) by apply: solvable_sub solG; exact: subsetIl.
have oAxA: #|A :^ x^-1| = #|A| by exact: card_conjg.
have sAN: A \subset N by rewrite subsetI -{1}genGid genS // subsetUl.
have nGNA: A \subset 'N(G :&: N).
  by apply/normsP=> y ?; rewrite conjIg (normsP nGA) ?(conjGid, subsetP sAN).
have coGNA: coprime #|G :&: N| #|A|.
  by move: coGA; rewrite -(LaGrange (subsetIl G N)) coprime_mull; case/andP.
case: (SchurZass_trans_sol solGN nGNA _ coGNA oAxA) => [|y GNy [defAx]].
  have ->: (G :&: N) * A = N.
    apply/eqP; rewrite eqset_sub_card -{2}(mulGid N) mulgSS ?subsetIr //=.
    by rewrite coprime_card_mulG // -iGN_A LaGrange ?subsetIr.
  apply/subsetP=> yx; case/imsetP=> y Ay ->{yx}.
  rewrite inE groupJ ?groupV ?mem_gen //=; try by [apply/setUP; auto].
  by apply/normP; rewrite !conjsgM invgK (normsP nHxA) // conjsgK.
case/setIP: GNy => Gy; case/setIP=> _; move/normP=> nHy.
exists (y * x)^-1.
  rewrite -coprime_norm_cent // groupV inE groupM //=; apply/normP.
  by rewrite conjsgM -defAx conjsgKV.
by apply: val_inj; rewrite /= -{2}nHy -(conjsgM _ y) conjsgK.
Qed.

Lemma norm_conj_cent : forall A G x, x \in 'C(A) ->
  (A \subset 'N(G :^ x)) = (A \subset 'N(G)).
Proof.
move=> A G x; move/centP=> cAx; apply/normsP/normsP=> nGA y Ay.
  by rewrite -[G :^ y](conjsgK x) -(conjsgM _ y) -cAx // conjsgM nGA ?conjsgK.
by rewrite -conjsgM cAx // conjsgM nGA.
Qed.

Lemma coprime_quotient_cent : forall A G H,
    H <| G -> A \subset 'N(H) -> coprime #|H| #|A| -> solvable H ->
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> A G H; case/normalP=> sHG nHG nHA coHA solH.
apply/eqP; rewrite eqset_sub subsetI morphimS ?subsetIl //=.
rewrite (subset_trans _ (morphim_cent _ _)) ?morphimS ?subsetIr //=.
apply/subsetP=> xb; case/setIP; case/morphimP=> x Nx Gx def_x cAxb.
have{cAxb} cAx: forall y, y \in A -> [~ x, y] \in H.
  move=> y Ay; have Ny: y \in 'N(H) by exact: subsetP Ay.
  rewrite coset_of_idr ?groupR // morphR //= -def_x; apply/eqP; apply/commgP.
  by apply: (centP cAxb); rewrite -coset_of_norm mem_imset.
have AxAH : A :^ x \subset H * A.
  apply/subsetP=> yx; case/imsetP=> y Ay ->{yx}.
  rewrite -normC // -(mulKVg y (y ^ x)) -commgEl mem_mulg //.
  by rewrite -groupV invg_comm cAx.
case: (SchurZass_trans_sol _ nHA AxAH) => // [|y Hy]; first exact: card_conjg.
case=> def_Ax; rewrite -coset_of_norm; apply/imsetP.
exists (x * y^-1); last first.
  by rewrite conjgCV mkerl // ker_coset memJ_norm groupV.
rewrite /= inE groupMl // ?(groupV, subsetP sHG) //=.
apply/centP=> z Az; apply/commgP; apply/eqP; apply/set1P.
apply: (subsetP (coprime_trivg coHA)); rewrite inE {1}commgEl commgEr.
rewrite invMg -mulgA invgK groupMl // conjMg mulgA -commgEl.
rewrite groupMl ?cAx // memJ_norm ?(groupV, subsetP nHA) // Hy /=.
by rewrite groupMr // conjVg groupV conjgM -mem_conjg -def_Ax memJ_conjg.
Qed.

(* a weaker, more traditional form of the previous theorem *)
Lemma coprime_quotient_cent_weak : forall A G H,
    H <| G -> A \subset 'N(H) -> coprime #|G| #|A| -> solvable G ->
  'C_G(A) / H = 'C_(G / H)(A / H).
move=> A G H normH nHA co so; have sHG := normal_sub normH.
apply: coprime_quotient_cent => //; last exact: solvable_sub so.  
by rewrite -(LaGrange sHG) coprime_mull in co; case/andP: co.
Qed.

Lemma coprime_comm_normal_part : forall A G K,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  hall (predC pi) G K -> K \subset 'C_G(A) ->
  [~: G, A] \subset 'O_pi(G).
Proof.
move=> A G K nGA coGA solG hallK cKA.
case: (coprime_hall_exists nGA) => // H hallH nHA.
have sHG: H \subset G by case/andP: hallH.
have sKG: K \subset G by case/andP: hallK.
have coKH: coprime #|K| #|H|.
  move: hallH hallK; rewrite !hallE.
  case/and3P=> _ piH _; case/and3P=> _ pi'K _.
  by rewrite coprime_sym (pi_nat_coprime piH pi'K).
have defG: G = K * H :> {set _}.
  apply/eqP; rewrite eq_sym eqset_sub_card coprime_card_mulG //.
  rewrite -{1}(mulGid G) mulgSS //=.
  case/andP: hallH => _; move/eqP->; case/andP: hallK => _; move/eqP->.
  by rewrite mulnC pi_partC.
have sGA_H: [~: G, A] \subset H.
  rewrite gen_subG defG; apply/subsetP=> xya; case/imset2P=> xy a.
  case/imset2P=> x y Kx Hy -> Aa -> {xya xy}.
  rewrite commMgJ (([~ x, a] =P 1) _) ?(conj1g, mul1g).
    by rewrite groupMl ?groupV // memJ_norm ?(subsetP nHA).
  rewrite subsetI sKG in cKA; apply/commgP; exact: (centsP cKA).
apply: subset_core; last first.
  by rewrite /(_ <| G) /=  normGR commsgC subcomm_normal nGA.
by move: hallH; rewrite hallE; case/and3P=> _ piH _; apply: pi_groupS piH.
Qed.

End InternalAction.

Lemma coprime_hall_subset : forall pi (gT : finGroupType) (A G X : {group gT}),
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  X \subset G -> pi_group pi X -> A \subset 'N(X) ->
  exists H : {group gT}, [/\ hall pi G H, A \subset 'N(H) & X \subset H].
Proof.
move=> pi gT A G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT A G *.
rewrite ltnS => leGn X nGA coGA solG sXG piX nXA.
case trG: (trivg G); last move/idPn: trG => trG.
  case: (coprime_hall_exists pi nGA) => // H hallH nHA; exists H; split=> //.
  by apply: subset_trans (subset_trans trG (sub1G _)); case/andP: piX.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genS ?subsetUr.
have sA_AG: A \subset A <*> G by rewrite -{1}genGid genS ?subsetUl.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
have nsG_AG: G <| A <*> G by exact/andP.
case: (solvable_norm_abelem solG nsG_AG) => // M [sMG nMAG ntM].
have{nMAG} [nMA nMG]: A \subset 'N(M) /\ G \subset 'N(M).
  by apply/andP; rewrite -subUset -gen_subG; case/andP: nMAG.
have nMX: X \subset 'N(M) by exact: subset_trans nMG.
case/andP=> abelM; set p := pdiv #|M|; move/exponentP=> elemM.
have pr_p: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
have{elemM} pM: primes #|M| = [:: p].
  apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes // => q.
  rewrite mem_primes mem_seq1 pos_card_group /=.
  apply/andP/eqP=> [[pr_q q_M] | ->]; last by rewrite dvdn_pdiv.
  case: (cauchy pr_q q_M) => x; case/andP=> Mx; move/eqP=> oxq.
  apply/eqP; rewrite eqn_leq pdiv_min_dvd ?prime_gt1 1?dvdn_leq ?ltn_0prime //.
  by rewrite -oxq order_dvd elemM.
pose Gb := (G / M)%G; pose Ab := (A / M)%G; pose Xb := (X / M)%G.
have oAb: #|Ab| = #|A|.
  rewrite /= -quotient_mulg // -norm_mulgenE // card_quotient; last first.
    by rewrite gen_subG subUset nMA normG.
  rewrite -group_divn /= norm_mulgenE ?mulG_subr //.
  rewrite coprime_card_mulG ?divn_mull // coprime_sym.
  by move: coGA; rewrite -(LaGrange sMG) coprime_mull; case/andP.
case: (IHn _ Ab Gb _ Xb); do 1?[exact: solvable_quo | exact: morphim_norms].
- rewrite -[#|_|]mul1n card_quotient //.
  apply: leq_trans leGn; have:= pos_card_group G.
  rewrite -(LaGrange sMG) ltn_0mul; case/andP=> _ M'pos.
  by rewrite ltn_pmul2r // ltnNge -trivg_card.
- rewrite card_quotient // oAb.
  by move: coGA; rewrite -(LaGrange sMG) coprime_mull; case/andP.
- exact: morphimS.
- rewrite /pi_group -(isog_card (second_isom nMX)) /=.
  rewrite card_quotient //; last first.
    by apply: subset_trans (normI _ _); rewrite subsetI nMX normG.
  apply: pi_nat_dvdn piX; exact: indexg_dvdn.
move=> Hb []; rewrite hallE; case/and3P=> sHGb piHb pi'Hb' nHbA sXHb.
case/inv_quotientS: (sHGb) => [|HM defHM sMHM sHMG]; first exact/andP.
have{Xb sXHb} sXHM: X \subset HM.
  apply/subsetP=> x Xx; have:= rcoset_refl M x.
  have: coset_of M x \in Hb.
    by apply: (subsetP sXHb); rewrite /Xb /= -coset_of_norm mem_imset.
  rewrite defHM; case/morphimP=> y Ny Hy /=; move/(congr1 val).
  rewrite /= !coset_ofN // ?(subsetP nMX) // => ->.
  by case/rcosetP=> z Mz ->; rewrite groupMl // (subsetP sMHM).
have{pi'Hb' sHGb} pi'HM': pi_nat (predC pi) #|G : HM|.
  move: pi'Hb'; rewrite -!group_divn // defHM !card_quotient //; last first.
  - exact: subset_trans nMG.
  by rewrite -(divn_pmul2l (pos_card_group M)) !LaGrange.
have{Ab oAb nHbA} nHMA: A \subset 'N(HM).
  apply/subsetP=> x Ax; rewrite inE.
  apply/subsetP=> yx; case/imsetP=> y HMy ->{yx}.
  have nMy: y \in 'N(M) by rewrite (subsetP nMG) // (subsetP sHMG).
  have:= rcoset_refl M (y ^ x); have: coset_of M (y ^ x) \in Hb.
    rewrite morphJ ?(subsetP nMA x Ax) //=.
    rewrite memJ_norm; first by rewrite defHM /= -coset_of_norm mem_imset.
    by rewrite (subsetP nHbA) //= -coset_of_norm mem_imset.
  rewrite defHM; case/morphimP=> z Nz Hz /=; move/(congr1 val).
  rewrite /= !coset_ofN // => [->|]; last by rewrite groupJ // (subsetP nMA).
  by case/rcosetP=> t Mt ->; rewrite groupMl // (subsetP sMHM).
case pi_p: (pi p).
  exists HM; split=> //; rewrite hallE; apply/and3P; split=> //.
  rewrite /pi_group -(LaGrange sMHM) pi_nat_mul.
  rewrite {1}/pi_nat pM /= pi_p ltn_0group.
  by rewrite defHM /pi_group card_quotient ?(subset_trans sHMG) in piHb.
case: (ltnP #|HM| #|G|) => [ltHG | leGHM {n IHn leGn}].
  case: (IHn _ A HM (leq_trans ltHG leGn) X) => // [||H [hallH nHA sXH]].
  - by move: coGA; rewrite -(LaGrange sHMG) coprime_mull; case/andP.
  - exact: solvable_sub solG.
  move: hallH; rewrite hallE; case/and3P=> sHHM piH pi'H'.
  have sHG: H \subset G by exact: subset_trans sHMG.
  exists H; split=> //; rewrite hallE; apply/and3P; split=> //.
  rewrite -group_divn // -(LaGrange sHMG) -(LaGrange sHHM) -mulnA divn_mulr //.
  by rewrite pi'_nat_mul pi'H'.
have{leGHM nHMA sHMG sMHM sXHM pi'HM'} eqHMG: HM = G.
  by apply/eqP; rewrite -val_eqE eqset_sub_card sHMG.
have pi'M: pi'_group pi M by apply/andP; rewrite ltn_0group pM /= pi_p.
have{HM Hb defHM eqHMG piHb} hallM: hall (predC pi) G M.
  rewrite hallE; apply/and3P; split; rewrite // /pi_group pi'_natE'.
  by rewrite defHM /pi_group /= eqHMG card_quotient in piHb.
case: (coprime_hall_exists pi nGA) => // H hallH nHA.
pose XM := (X <*> M)%G; pose Y := (H :&: XM)%G.
have:= hallH; rewrite hallE; case/and3P=> sHG piH _.
have sXXM: X \subset XM by rewrite  -{1}genGid genS ?subsetUl.
have co_pi_M: forall B : {group gT}, pi_group pi B -> coprime #|B| #|M|.
  by move=> B piB; rewrite (pi_nat_coprime piB).
have hallX: hall pi XM X.
  rewrite hallE piX sXXM -group_divn //= norm_mulgenE //.
  by rewrite coprime_card_mulG ?co_pi_M // divn_mulr.
have hallY: hall pi XM Y.
  have sYXM: Y \subset XM by rewrite subsetIr.
  have piY: pi_group pi Y by apply: pi_groupS piH; exact: subsetIl.
  rewrite hallE sYXM piY -group_divn // -(_ : Y * M = XM).
    by rewrite coprime_card_mulG ?co_pi_M // divn_mulr //.
  rewrite /= setIC group_modr /= norm_mulgenE ?mulG_subr //; apply/setIidPl.
  rewrite mulSG ((H * M =P G) _) // eqset_sub_card -{1}(mulGid G) mulgSS //=.
  rewrite coprime_card_mulG ?co_pi_M //.
  case/andP: hallM => _; move/eqP->; case/andP: hallH => _; move/eqP->.
  by rewrite pi_partC.
have nXMA: A \subset 'N(XM).
  apply/normsP=> x Ax; rewrite /= norm_mulgenE // conjsMg.
  by rewrite (normsP nMA) ?(normsP nXA).
have sXMG: XM \subset G by rewrite gen_subG subUset sXG.
case: (coprime_hall_trans nXMA _ _ hallX nXA hallY) => [|||x].
- by have:= coGA; rewrite -(LaGrange sXMG) coprime_mull; case/andP.
- exact: solvable_sub solG.
- by apply/normsP=> x Ax; rewrite conjIg (normsP nHA) ?(normsP nXMA).
case/setIP=> XMx cAx ->; exists (H :^ x)%G; split.
- by rewrite hall_conj ?(subsetP sXMG).
- by rewrite norm_conj_cent.
by rewrite conjSg subsetIl.
Qed.

Module AfterInner. End AfterInner.

Definition quo_act (gT aT : finGroupType) (H : {set gT}) to :=
  fun (Hx : coset H) (a : aT) =>
    if 'N_(|to)(H) == setT then insubd Hx (to^~ a @: Hx) else Hx.

Prenex Implicits quo_act.

(*
Section ExternalAction.

Variables (pi : pred nat) (aT gT : finGroupType) (to : action aT gT).
Variables (A : {group aT}) (G : {group gT}).

Hypothesis morphA : {in A & G &, forall a, {morph to^~ a : x y / x * y}}.

Hypothesis nGA : [acts (A | to) on G].

Hypothesis coGA : coprime #|A| #|G|.

Hypothesis solG : solvable G.

Lemma ext_coprime_hall_exists : 
  exists2 H : {group gT}, hall_for pi G H & [acts (A | to) on H].
Proof.
Admitted.

Lemma ext_coprime_hall_trans : forall H1 H2 : {group gT},
  hall_for pi G H1 -> [acts (A | to) on H1] ->
  hall_for pi G H2 -> [acts (A | to) on H2] ->
  exists2 x, x \in 'C_G(A | to) & H1 = (H2 :^ x)%G.
Proof.
Admitted.

Lemma ext_norm_conj_cent : forall (H : {group gT}) x,
   x \in 'C(A | to) -> [acts (A | to) on H :^ x] = [acts (A | to) on H].
Proof.
Admitted.

(*
Lemma ext_coprime_quotient_cent : forall L : {group gT},
  G <| L -> 'C_L(A | to) / G = 'C_(L / G)(A | quo_act to).
Proof.
Admitted.
*)

Lemma ext_coprime_hall_subset : forall X : {group gT},
    pi_subgroup pi G X -> A \subset 'N_(|to)(X) ->
  exists H : {group gT},
    [/\ hall_for pi G H, [acts (A | to) on H] & X \subset H].
Proof.
Admitted.

End ExternalAction.

*)