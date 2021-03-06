Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div prime paths.
Require Import fintype bigops finset.
Require Import groups morphisms automorphism gprod normal action commutators.
Require Import pgroups cyclic nilpotent sylow maximal schurzass hall.

(* Require Import connect finfun ssralg group_perm center. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section InternalAction.

Variable pi : nat_pred.
Variable gT : finGroupType.
Implicit Types G H K A X : {group gT}.

Lemma coprime_norm_cent : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| ->
  'N_G(A) = 'C_G(A).
Proof.
move=> A G nGA coGA; apply/eqP; rewrite eqEsubset andbC setIS ?cent_sub //=.
rewrite subsetI subsetIl /= (sameP commG1P trivgP) -(coprime_TIg coGA).
rewrite subsetI commg_subr subsetIr andbT.
move: nGA; rewrite -commg_subl; apply: subset_trans.
by rewrite commSg ?subsetIl.
Qed.

Lemma coprime_hall_exists : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  exists2 H : {group gT}, pi.-Hall(G) H & A \subset 'N(H).
Proof.
move=> A G nGA coGA solG; case: (HallExist pi solG) => H hallH.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genS ?subsetUr.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
pose N := 'N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N.
  apply/normalP; rewrite subsetIr; split=> // x Nx.
  by rewrite conjIg (normP _) // (subsetP nGN, conjGid).
have NG_AG: G * N = A <*> G.
  by apply: Hall_Frattini_arg hallH => //; exact/andP.
have iGN_A: #|N| %/ #|G :&: N| = #|A|.
  rewrite divgS ?subsetIr // -card_quotient; last by case/andP: nGN_N.
  rewrite (isog_card (second_isog nGN)) /= -quotient_mulg (normC nGN) NG_AG.
  rewrite card_quotient // -divgS //= norm_mulgenEl //.
  by rewrite coprime_cardMg 1?coprime_sym // mulnK.
have hallGN: Hall N (G :&: N).
  rewrite /Hall -divgS subsetIr //= iGN_A.
  by move: coGA; rewrite -(LaGrangeI G N) coprime_mull; case/andP.
case/splitsP: {hallGN nGN_N}(SchurZass_split hallGN nGN_N) => B.
case/complP=> trBGN defN.
have{trBGN iGN_A} oBA: #|B| = #|A|.
  by rewrite -iGN_A -{1}defN (TI_cardMg trBGN) mulKn.
have sBN: B \subset N by rewrite -defN mulG_subr.
case: (SchurZass_trans_sol solG nGA _ coGA oBA) => [|x Gx defB].
  by rewrite -(normC nGA) -norm_mulgenEl // -NG_AG -(mul1g B) mulgSS ?sub1G.
exists (H :^ x^-1)%G; first by rewrite hall_conj ?groupV.
apply/subsetP=> y Ay; have: y ^ x \in B by rewrite defB memJ_conjg.
move/(subsetP sBN); case/setIP=> _; move/normP=> nHyx.
by apply/normP; rewrite -conjsgM conjgCV invgK conjsgM nHyx.
Qed.

Lemma coprime_hall_trans : forall A G H1 H2,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  pi.-Hall(G) H1 -> A \subset 'N(H1) ->
  pi.-Hall(G) H2 -> A \subset 'N(H2) ->
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
have NG_AG : G * N = A <*> G.
  by apply: Hall_Frattini_arg hallH => //; exact/andP.
have iGN_A: #|N : G :&: N| = #|A|.
  rewrite -card_quotient //; last by case/andP: nGN_N.
  rewrite (isog_card (second_isog nGN)) /= -quotient_mulg (normC nGN) NG_AG.
  rewrite card_quotient // -divgS //= norm_mulgenEl //.
  by rewrite coprime_cardMg 1?coprime_sym // mulnK.
have solGN: solvable (G :&: N) by apply: solvableS solG; exact: subsetIl.
have oAxA: #|A :^ x^-1| = #|A| by exact: cardJg.
have sAN: A \subset N by rewrite subsetI -{1}genGid genS // subsetUl.
have nGNA: A \subset 'N(G :&: N).
  by apply/normsP=> y ?; rewrite conjIg (normsP nGA) ?(conjGid, subsetP sAN).
have coGNA: coprime #|G :&: N| #|A|.
  by move: coGA; rewrite -(LaGrange (subsetIl G N)) coprime_mull; case/andP.
case: (SchurZass_trans_sol solGN nGNA _ coGNA oAxA) => [|y GNy [defAx]].
  have ->: (G :&: N) * A = N.
    apply/eqP; rewrite eqEcard -{2}(mulGid N) mulgSS ?subsetIr //=.
    by rewrite coprime_cardMg // -iGN_A LaGrange ?subsetIr.
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
apply/eqP; rewrite eqEsubset subsetI morphimS ?subsetIl //=.
rewrite (subset_trans _ (morphim_cent _ _)) ?morphimS ?subsetIr //=.
apply/subsetP=> xb; case/setIP; case/morphimP=> x Nx Gx def_x cAxb.
have{cAxb} cAx: forall y, y \in A -> [~ x, y] \in H.
  move=> y Ay; have Ny: y \in 'N(H) by exact: subsetP Ay.
  rewrite coset_idr ?groupR // morphR //= -def_x; apply/eqP; apply/commgP.
  by apply: (centP cAxb); rewrite mem_quotient.
have AxAH : A :^ x \subset H * A.
  apply/subsetP=> yx; case/imsetP=> y Ay ->{yx}.
  rewrite -normC // -(mulKVg y (y ^ x)) -commgEl mem_mulg //.
  by rewrite -groupV invg_comm cAx.
case: (SchurZass_trans_sol _ nHA AxAH) => // [|y Hy]; first exact: cardJg.
case=> def_Ax; rewrite -imset_coset; apply/imsetP.
exists (x * y^-1); last first.
  by rewrite conjgCV mkerl // ker_coset memJ_norm groupV.
rewrite /= inE groupMl // ?(groupV, subsetP sHG) //=.
apply/centP=> z Az; apply/commgP; apply/eqP; apply/set1P.
rewrite -[[set 1]](coprime_TIg coHA) inE {1}commgEl commgEr.
rewrite invMg -mulgA invgK groupMl // conjMg mulgA -commgEl.
rewrite groupMl ?cAx // memJ_norm ?(groupV, subsetP nHA) // Hy /=.
by rewrite groupMr // conjVg groupV conjgM -mem_conjg -def_Ax memJ_conjg.
Qed.

(* a weaker, more traditional form of the previous theorem *)
Lemma coprime_quotient_cent_weak : forall A G H,
    H <| G -> A \subset 'N(H) -> coprime #|G| #|A| -> solvable G ->
  'C_G(A) / H = 'C_(G / H)(A / H).
move=> A G H normH nHA co so; have sHG := normal_sub normH.
apply: coprime_quotient_cent => //; last exact: solvableS so.
by rewrite -(LaGrange sHG) coprime_mull in co; case/andP: co.
Qed.

Lemma coprime_comm_pcore : forall A G K,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  pi^'.-Hall(G) K -> K \subset 'C_G(A) ->
  [~: G, A] \subset 'O_pi(G).
Proof.
move=> A G K nGA coGA solG hallK cKA.
case: (coprime_hall_exists nGA) => // H hallH nHA.
have sHG: H \subset G by case/andP: hallH.
have sKG: K \subset G by case/andP: hallK.
have coKH: coprime #|K| #|H|.
  case/and3P: hallH=> _ piH _; case/and3P: hallK => _ pi'K _.
  by rewrite coprime_sym (pnat_coprime piH pi'K).
have defG: G :=: K * H.
  apply/eqP; rewrite eq_sym eqEcard coprime_cardMg //.
  rewrite -{1}(mulGid G) mulgSS //= (card_Hall hallH) (card_Hall hallK).
  by rewrite mulnC partnC.
have sGA_H: [~: G, A] \subset H.
  rewrite gen_subG defG; apply/subsetP=> xya; case/imset2P=> xy a.
  case/imset2P=> x y Kx Hy -> Aa -> {xya xy}.
  rewrite commMgJ (([~ x, a] =P 1) _) ?(conj1g, mul1g).
    by rewrite groupMl ?groupV // memJ_norm ?(subsetP nHA).
  rewrite subsetI sKG in cKA; apply/commgP; exact: (centsP cKA).
apply: pcore_max; last first.
  by rewrite /(_ <| G) /=  commg_norml commGC commg_subr nGA.
by case/and3P: hallH => _ piH _; apply: pgroupS piH.
Qed.

End InternalAction.

Lemma coprime_hall_subset : forall pi (gT : finGroupType) (A G X : {group gT}),
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  X \subset G -> pi.-group X -> A \subset 'N(X) ->
  exists H : {group gT}, [/\ pi.-Hall(G) H, A \subset 'N(H) & X \subset H].
Proof.
move=> pi gT A G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT A G *.
rewrite ltnS => leGn X nGA coGA solG sXG piX nXA.
case: (eqsVneq G 1) => [G1 | ntG].
  case: (coprime_hall_exists pi nGA) => // H hallH nHA; exists H; split=> //.
  by rewrite (subset_trans sXG) // G1 sub1G.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genS ?subsetUr.
have sA_AG: A \subset A <*> G by rewrite -{1}genGid genS ?subsetUl.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
have nsG_AG: G <| A <*> G by exact/andP.
case: (solvable_norm_abelem solG nsG_AG) => // M [sMG nMAG ntM].
have{nMAG} [nMA nMG]: A \subset 'N(M) /\ G \subset 'N(M).
  by apply/andP; rewrite -subUset -gen_subG; case/andP: nMAG.
have nMX: X \subset 'N(M) by exact: subset_trans nMG.
case/abelemP=> p pr_p; do 2![case/andP]=> abelM _ pM.
have{pM} pM: primes #|M| = [:: p].
  move: ntM; rewrite trivg_card1; case/p_natP: pM => // [[|k]] -> // _.
  by rewrite primes_exp ?primes_prime.
pose Gb := (G / M)%G; pose Ab := (A / M)%G; pose Xb := (X / M)%G.
have oAb: #|Ab| = #|A|.
  rewrite /= -quotient_mulg // -norm_mulgenEl // card_quotient; last first.
    by rewrite gen_subG subUset nMA normG.
  rewrite -divgS /= norm_mulgenEl ?mulG_subr //.
  rewrite coprime_cardMg ?mulnK // coprime_sym.
  by move: coGA; rewrite -(LaGrange sMG) coprime_mull; case/andP.
case: (IHn _ Ab Gb _ Xb); do 1?[exact: quotient_sol | exact: morphim_norms].
- rewrite -[#|_|]mul1n card_quotient //.
  apply: leq_trans leGn; have:= ltn_0group G.
  rewrite -(LaGrange sMG) ltn_0mul; case/andP=> _ M'pos.
  by rewrite ltn_pmul2r // ltnNge -trivg_card_le1.
- rewrite card_quotient // oAb.
  by move: coGA; rewrite -(LaGrange sMG) coprime_mull; case/andP.
- exact: morphimS.
- rewrite /pgroup -(isog_card (second_isog nMX)) /=.
  rewrite card_quotient ?normsI ?normG //.
  apply: pnat_dvd piX; exact: dvdn_indexg.
move=> Hb []; case/and3P=> sHGb piHb pi'Hb' nHbA sXHb.
case/inv_quotientS: (sHGb) => [|HM defHM sMHM sHMG]; first exact/andP.
have{Xb sXHb} sXHM: X \subset HM.
  apply/subsetP=> x Xx; have:= rcoset_refl M x.
  have: coset M x \in Hb by apply: (subsetP sXHb); rewrite mem_quotient.
  rewrite defHM; case/morphimP=> y Ny Hy /=; move/(congr1 val).
  rewrite /= !val_coset // ?(subsetP nMX) // => ->.
  by case/rcosetP=> z Mz ->; rewrite groupMl // (subsetP sMHM).
have{pi'Hb' sHGb} pi'HM': pi^'.-nat #|G : HM|.
  move: pi'Hb'; rewrite -!divgS // defHM !card_quotient //; last first.
  - exact: subset_trans nMG.
  by rewrite -(divn_pmul2l (ltn_0group M)) !LaGrange.
have{Ab oAb nHbA} nHMA: A \subset 'N(HM).
  apply/subsetP=> x Ax; rewrite inE.
  apply/subsetP=> yx; case/imsetP=> y HMy ->{yx}.
  have nMy: y \in 'N(M) by rewrite (subsetP nMG) // (subsetP sHMG).
  have:= rcoset_refl M (y ^ x); have: coset M (y ^ x) \in Hb.
    rewrite morphJ ?(subsetP nMA x Ax) //=.
    rewrite memJ_norm; first by rewrite defHM mem_quotient.
    by rewrite (subsetP nHbA) //= mem_quotient.
  rewrite defHM; case/morphimP=> z Nz Hz /=; move/(congr1 val).
  rewrite /= !val_coset // => [->|]; last by rewrite groupJ // (subsetP nMA).
  by case/rcosetP=> t Mt ->; rewrite groupMl // (subsetP sMHM).
case pi_p: (p \in pi).
  exists HM; split=> //; apply/and3P; split=> //.
  rewrite /pgroup -(LaGrange sMHM) pnat_mul.
  rewrite {1}/pnat pM /= pi_p ltn_0group.
  by rewrite defHM /pgroup card_quotient ?(subset_trans sHMG) in piHb.
case: (ltnP #|HM| #|G|) => [ltHG | leGHM {n IHn leGn}].
  case: (IHn _ A HM (leq_trans ltHG leGn) X) => // [||H [hallH nHA sXH]].
  - by move: coGA; rewrite -(LaGrange sHMG) coprime_mull; case/andP.
  - exact: solvableS solG.
  case/and3P: hallH => sHHM piH pi'H'.
  have sHG: H \subset G by exact: subset_trans sHMG.
  exists H; split=> //; apply/and3P; split=> //.
  rewrite -divgS // -(LaGrange sHMG) -(LaGrange sHHM) -mulnA mulKn //.
  by rewrite pnat_mul pi'H'.
have{leGHM nHMA sHMG sMHM sXHM pi'HM'} eqHMG: HM = G.
  by apply/eqP; rewrite -val_eqE eqEcard sHMG.
have pi'M: pi^'.-group M by apply/andP; rewrite ltn_0group pM /= inE /= pi_p.
have{HM Hb defHM eqHMG piHb} hallM: pi^'.-Hall(G) M.
  apply/and3P; split; rewrite // /pgroup pnatNK.
  by rewrite defHM /pgroup /= eqHMG card_quotient in piHb.
case: (coprime_hall_exists pi nGA) => // H hallH nHA.
pose XM := (X <*> M)%G; pose Y := (H :&: XM)%G.
case/and3P: (hallH) => sHG piH _.
have sXXM: X \subset XM by rewrite  -{1}genGid genS ?subsetUl.
have co_pi_M: forall B : {group gT}, pi.-group B -> coprime #|B| #|M|.
  by move=> B piB; rewrite (pnat_coprime piB).
have hallX: pi.-Hall(XM) X.
  rewrite /pHall piX sXXM -divgS //= norm_mulgenEl //.
  by rewrite coprime_cardMg ?co_pi_M // mulKn.
have hallY: pi.-Hall(XM) Y.
  have sYXM: Y \subset XM by rewrite subsetIr.
  have piY: pi.-group Y by apply: pgroupS piH; exact: subsetIl.
  rewrite /pHall sYXM piY -divgS // -(_ : Y * M = XM).
    by rewrite coprime_cardMg ?co_pi_M // mulKn //.
  rewrite /= setIC group_modr /= norm_mulgenEl ?mulG_subr //; apply/setIidPl.
  rewrite mulSG ((H * M =P G) _) // eqEcard -{1}(mulGid G) mulgSS //=.
  rewrite coprime_cardMg ?co_pi_M // (card_Hall hallM) (card_Hall hallH).
  by rewrite partnC.
have nXMA: A \subset 'N(XM).
  apply/normsP=> x Ax; rewrite /= norm_mulgenEl // conjsMg.
  by rewrite (normsP nMA) ?(normsP nXA).
have sXMG: XM \subset G by rewrite gen_subG subUset sXG.
case: (coprime_hall_trans nXMA _ _ hallX nXA hallY) => [|||x].
- by have:= coGA; rewrite -(LaGrange sXMG) coprime_mull; case/andP.
- exact: solvableS solG.
- by apply/normsP=> x Ax; rewrite conjIg (normsP nHA) ?(normsP nXMA).
case/setIP=> XMx cAx ->; exists (H :^ x)%G; split.
- by rewrite hall_conj ?(subsetP sXMG).
- by rewrite norm_conj_cent.
by rewrite conjSg subsetIl.
Qed.

Module AfterInner. End AfterInner.

Definition quo_act (gT aT : finGroupType) (H : {set gT}) to :=
  fun (Hx : coset_of H) (a : aT) =>
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