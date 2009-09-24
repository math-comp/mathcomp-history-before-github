Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div paths.
Require Import fintype bigops finset prime.
Require Import groups morphisms perm automorphism gprod normal cyclic action.
Require Import commutators pgroups nilpotent sylow maximal hall.

(*****************************************************************************)
(* This file develops the theory of coprime groups action on solvable groups *)
(* (roughly, B & G Proposition 1.5).                                         *)
(*   We mainly develop the theory for internal action (conjugation), though  *)
(* we do provide a group action version of the main solvable coprime action  *)
(* lemmas. It is unclear whether they are easier to use that the internal    *)
(* ones: even when applying an induction hypothesis to a quotient of the     *)
(* acted-on group, it is easy enough to quotient the acting group as well,   *)
(* since this quotient is isomorphic to the acting group due to the coprime  *)
(* orders.                                                                   *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section InternalAction.

Variable pi : nat_pred.
Variable gT : finGroupType.
Implicit Types G H K A X : {group gT}.

(* Part of Aschbacher (18.7.4). *)
Lemma coprime_norm_cent : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| -> 'N_G(A) = 'C_G(A).
Proof.
move=> A G nGA coGA; apply/eqP; rewrite eqEsubset andbC setIS ?cent_sub //=.
rewrite subsetI subsetIl /= (sameP commG1P trivgP) -(coprime_TIg coGA).
rewrite subsetI commg_subr subsetIr andbT.
move: nGA; rewrite -commg_subl; apply: subset_trans.
by rewrite commSg ?subsetIl.
Qed.

(* B & G, Proposition 1.5(a) *)
Lemma coprime_Hall_exists : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  exists2 H : {group gT}, pi.-Hall(G) H & A \subset 'N(H).
Proof.
move=> A G nGA coGA solG; case: (HallExist pi solG) => H hallH.
have sG_AG: G \subset A <*> G by rewrite mulgen_subr.
have nG_AG: A <*> G \subset 'N(G) by rewrite mulgen_subG nGA normG.
pose N := 'N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N by rewrite /(_ <| N) subsetIr normsI ?normG.
have NG_AG: G * N = A <*> G.
  by apply: Hall_Frattini_arg hallH => //; exact/andP.
have iGN_A: #|N| %/ #|G :&: N| = #|A|.
  rewrite setIC divgI -card_quotient // -quotient_mulgr NG_AG.
  rewrite card_quotient -?divgS //= norm_mulgenEl //.
  by rewrite coprime_cardMg 1?coprime_sym // mulnK.
have hallGN: Hall N (G :&: N).
  by rewrite /Hall -divgS subsetIr //= iGN_A (coprimeSg _ coGA) ?subsetIl.
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

(* B & G, Proposition 1.5(c) *)
Lemma coprime_Hall_trans : forall A G H1 H2,
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
  rewrite card_quotient // -divgS //= mulgenC norm_mulgenEr //.
  by rewrite coprime_cardMg // mulnC mulnK.
have solGN: solvable (G :&: N) by apply: solvableS solG; exact: subsetIl.
have oAxA: #|A :^ x^-1| = #|A| by exact: cardJg.
have sAN: A \subset N by rewrite subsetI -{1}genGid genS // subsetUl.
have nGNA: A \subset 'N(G :&: N).
  by apply/normsP=> y ?; rewrite conjIg (normsP nGA) ?(conjGid, subsetP sAN).
have coGNA: coprime #|G :&: N| #|A| := coprimeSg (subsetIl _ _) coGA.
case: (SchurZass_trans_sol solGN nGNA _ coGNA oAxA) => [|y GNy [defAx]].
  have ->: (G :&: N) * A = N.
    apply/eqP; rewrite eqEcard -{2}(mulGid N) mulgSS ?subsetIr //=.
    by rewrite coprime_cardMg // -iGN_A LaGrange ?subsetIr.
  rewrite sub_conjgV conjIg -normJ subsetI conjGid ?mulgen_subl //.
  by rewrite mem_gen // inE Gx orbT.
case/setIP: GNy => Gy; case/setIP=> _; move/normP=> nHy.
exists (y * x)^-1.
  rewrite -coprime_norm_cent // groupV inE groupM //=; apply/normP.
  by rewrite conjsgM -defAx conjsgKV.
by apply: val_inj; rewrite /= -{2}nHy -(conjsgM _ y) conjsgK.
Qed.

(* A complement to the above: 'C(A) acts on 'Nby(A) *)
Lemma norm_conj_cent : forall A G x, x \in 'C(A) ->
  (A \subset 'N(G :^ x)) = (A \subset 'N(G)).
Proof.
move=> A G x; move/centP=> cAx; apply/normsP/normsP=> nGA y Ay.
  by rewrite -[G :^ y](conjsgK x) -(conjsgM _ y) -cAx // conjsgM nGA ?conjsgK.
by rewrite -conjsgM cAx // conjsgM nGA.
Qed.

(* Strongest version of the centraliser lemma -- not found in textbooks! *)
Lemma strongest_coprime_quotient_cent : forall A G H,
   let R := H :&: [~: G, A] in
   A \subset 'N(H) -> R \subset G -> coprime #|R| #|A| -> solvable R ->
   'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> A G H R nHA sRG coRA solR.
have nRA: A \subset 'N(R) by rewrite normsI ?commg_normr.
apply/eqP; rewrite eqEsubset subsetI morphimS ?subsetIl //=.
rewrite (subset_trans _ (morphim_cent _ _)) ?morphimS ?subsetIr //=.
apply/subsetP=> Hx; case/setIP; case/morphimP=> x Nx Gx -> cAHx.
have{cAHx} cAxR: forall y, y \in A -> [~ x, y] \in R.
  move=> y Ay; have Ny: y \in 'N(H) by exact: subsetP Ay.
  rewrite inE mem_commg // andbT coset_idr ?groupR // morphR //=.
  by apply/eqP; apply/commgP; apply: (centP cAHx); rewrite mem_quotient.
have AxRA: A :^ x \subset R * A.
  apply/subsetP=> yx; case/imsetP=> y Ay ->{yx}.
  rewrite -normC // -(mulKVg y (y ^ x)) -commgEl mem_mulg //.
  by rewrite -groupV invg_comm cAxR.
case: (SchurZass_trans_sol _ nRA AxRA) => // [|y Ry]; first exact: cardJg.
case=> def_Ax; rewrite -imset_coset; apply/imsetP.
exists (x * y^-1); last first.
  by rewrite conjgCV mkerl // ker_coset memJ_norm groupV; case/setIP: Ry.
rewrite /= inE groupMl // ?(groupV, subsetP sRG) //=.
apply/centP=> z Az; apply/commgP; apply/eqP; apply/set1P.
rewrite -[[set 1]](coprime_TIg coRA) inE {1}commgEl commgEr /= -/R.
rewrite invMg -mulgA invgK groupMl // conjMg mulgA -commgEl.
rewrite groupMl ?cAxR // memJ_norm ?(groupV, subsetP nRA) // Ry /=.
by rewrite groupMr // conjVg groupV conjgM -mem_conjg -def_Ax memJ_conjg.
Qed.

(* A weaker but more practical version, still stronger than the usual form *)
(* (viz. Aschbacher 18.7.4), similar to the one needed in Aschbacher's     *)
(* proof of Thompson factorization. Note that the coprime and solvability  *)
(* assumptions could be further weakened to H :&: G (and hence become      *)
(* trivial if H and G are TI). However, the assuption that A act on G is   *)
(* needed in this case.                                                    *)

Lemma coprime_norm_quotient_cent : forall A G H,
    A \subset 'N(G) -> A \subset 'N(H) -> coprime #|H| #|A| -> solvable H ->
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> A G H nGA nHA coHA solH; have sRH := subsetIl H [~: G, A].
move: (coprimeSg sRH coHA) (solvableS sRH solH).
apply: strongest_coprime_quotient_cent => //.
by rewrite subIset // commg_subl nGA orbT.
Qed.

(* A useful consequence (similar to Ex. 6.1 in Aschbacher) of the stronger   *)
(* theorem. *)
Lemma coprime_cent_mulG : forall A G H,
     A \subset 'N(G) -> A \subset 'N(H) -> G \subset 'N(H) ->
     coprime #|H| #|A| -> solvable H ->
  'C_(H * G)(A) = 'C_H(A) * 'C_G(A).
Proof.
move=> A G H nHA nGA nHG coHA solH; rewrite -norm_mulgenEr //.
have nsHG: H <| H <*> G by rewrite /normal mulgen_subl mulgen_subG normG.
rewrite -{2}(setIidPr (normal_sub nsHG)) setIAC.
rewrite group_modr ?setSI ?mulgen_subr //=; symmetry; apply/setIidPl.
rewrite -quotientSK ?subIset 1?normal_norm //.
rewrite !coprime_norm_quotient_cent ?norms_mulgen //=.
by rewrite norm_mulgenEr ?quotient_mulgr.
Qed.

(* B & G, Proposition 1.5(d): the more traditional form of the above theorem *)
(* but weakening the assumption H <| G to H \subset G. The stronger coprime  *)
(* and solvability assumptions are easier to satisfy in practice.            *)
Lemma coprime_quotient_cent : forall A G H,
    H \subset G -> A \subset 'N(H) -> coprime #|G| #|A| -> solvable G ->
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move=> A G H sHG nHA coGA solG.
have sRG: H :&: [~: G, A] \subset G by rewrite subIset ?sHG.
move: (coprimeSg sRG coGA) (solvableS sRG solG).
exact: strongest_coprime_quotient_cent.
Qed.

(* B & G, Proposition 1.5(e). *)
Lemma coprime_comm_pcore : forall A G K,
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
    pi^'.-Hall(G) K -> K \subset 'C_G(A) ->
  [~: G, A] \subset 'O_pi(G).
Proof.
move=> A G K nGA coGA solG hallK cKA.
case: (coprime_Hall_exists nGA) => // H hallH nHA.
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

(* B & G, Proposition 1.5(b) *)
Lemma coprime_Hall_subset : forall pi (gT : finGroupType) (A G X : {group gT}),
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  X \subset G -> pi.-group X -> A \subset 'N(X) ->
  exists H : {group gT}, [/\ pi.-Hall(G) H, A \subset 'N(H) & X \subset H].
Proof.
move=> pi gT A G X; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT A G X * => leGn nGA coGA solG sXG piX nXA.
case: (eqsVneq G 1) => [G1 | ntG].
  case: (coprime_Hall_exists pi nGA) => // H hallH nHA.
  by exists H; split; rewrite // (subset_trans sXG) // G1 sub1G.
have sG_AG: G \subset A <*> G by rewrite mulgen_subr.
have sA_AG: A \subset A <*> G by rewrite mulgen_subl.
have nG_AG: A <*> G \subset 'N(G) by rewrite mulgen_subG nGA normG.
have nsG_AG: G <| A <*> G by exact/andP.
case: (solvable_norm_abelem solG nsG_AG) => // M [sMG nsMAG ntM].
have{nsMAG} [nMA nMG]: A \subset 'N(M) /\ G \subset 'N(M).
  by apply/andP; rewrite -mulgen_subG normal_norm.
have nMX: X \subset 'N(M) by exact: subset_trans nMG.
case/abelemP=> p pr_p; do 2![case/andP]=> abelM _ pM.
have: #|G / M| < n by rewrite (leq_trans (ltn_quotient _ _)).
move/(IHn _ (A / M)%G _ (X / M)%G); rewrite !(quotient_norms, quotientS) //.
rewrite !(coprime_morph, quotient_sol, morphim_pgroup) //.
case=> //= Hq []; case/and3P=> sHGq piHq pi'Hq' nHAq sXHq.
case/inv_quotientS: (sHGq) => [|HM defHM sMHM sHMG]; first exact/andP.
have nMHM := subset_trans sHMG nMG.
have{sXHq} sXHM: X \subset HM by rewrite -(quotientSGK nMX) -?defHM.
have{pi'Hq' sHGq} pi'HM': pi^'.-nat #|G : HM|.
  move: pi'Hq'; rewrite -!divgS // defHM !card_quotient //.
  by rewrite -(divn_pmul2l (cardG_gt0 M)) !LaGrange.
have{nHAq} nHMA: A \subset 'N(HM).
  by rewrite -(quotientSGK nMA) ?normsG ?quotient_normG -?defHM //; exact/andP.
case/orP: (orbN (p \in pi)) => pi_p.
  exists HM; split=> //; apply/and3P; split; rewrite /pgroup //.
  by rewrite -(LaGrange sMHM) pnat_mul -card_quotient // -defHM (pi_pnat pM).
case: (ltnP #|HM| #|G|) => [ltHG | leGHM {n IHn leGn}].
  case: (IHn _ A HM X (leq_trans ltHG leGn)) => // [||H [hallH nHA sXH]].
  - exact: coprimeSg coGA.
  - exact: solvableS solG.
  case/and3P: hallH => sHHM piH pi'H'.
  have sHG: H \subset G by exact: subset_trans sHMG.
  exists H; split=> //; apply/and3P; split=> //.
  rewrite -divgS // -(LaGrange sHMG) -(LaGrange sHHM) -mulnA mulKn //.
  by rewrite pnat_mul pi'H'.
have{leGHM nHMA sHMG sMHM sXHM pi'HM'} eqHMG: HM = G.
  by apply/eqP; rewrite -val_eqE eqEcard sHMG.
have pi'M: pi^'.-group M by rewrite /pgroup (pi_pnat pM).
have{HM Hq nMHM defHM eqHMG piHq} hallM: pi^'.-Hall(G) M.
  apply/and3P; split; rewrite // /pgroup pnatNK.
  by rewrite -card_quotient // -eqHMG -defHM.
case: (coprime_Hall_exists pi nGA) => // H hallH nHA.
pose XM := (X <*> M)%G; pose Y := (H :&: XM)%G.
case/and3P: (hallH) => sHG piH _.
have sXXM: X \subset XM by rewrite mulgen_subl.
have co_pi_M: forall B : {group gT}, pi.-group B -> coprime #|B| #|M|.
  by move=> B piB; rewrite (pnat_coprime piB).
have hallX: pi.-Hall(XM) X.
  rewrite /pHall piX sXXM -divgS //= norm_mulgenEl //.
  by rewrite coprime_cardMg ?co_pi_M // mulKn.
have sXMG: XM \subset G by rewrite mulgen_subG sXG.
have hallY: pi.-Hall(XM) Y.
  have sYXM: Y \subset XM by rewrite subsetIr.
  have piY: pi.-group Y by apply: pgroupS piH; exact: subsetIl.
  rewrite /pHall sYXM piY -divgS // -(_ : Y * M = XM).
    by rewrite coprime_cardMg ?co_pi_M // mulKn //.
  rewrite /= setIC group_modr ?mulgen_subr //=; apply/setIidPl.
  rewrite ((H * M =P G) _) // eqEcard mul_subG //= coprime_cardMg ?co_pi_M //. 
  by rewrite (card_Hall hallM) (card_Hall hallH) partnC.
have nXMA: A \subset 'N(XM) by rewrite norms_mulgen.
have:= coprime_Hall_trans nXMA _ _ hallX nXA hallY.
rewrite !(coprimeSg sXMG, solvableS sXMG, normsI) //.
case=> // x; case/setIP=> XMx cAx ->.
exists (H :^ x)%G; split; first by rewrite hall_conj ?(subsetP sXMG).
  by rewrite norm_conj_cent.
by rewrite conjSg subsetIl.
Qed.

Section ExternalAction.

Variables (pi : nat_pred) (aT gT : finGroupType).
Variables (A : {group aT}) (G : {group gT}) (to : groupAction A G).

Section FullExtension.

Local Notation inA := (sdpair2 to).
Local Notation inG := (sdpair1 to).
Local Notation A' := (inA @* gval A).
Local Notation G' := (inG @* gval G).
Let injG : 'injm inG := injm_sdpair1 _.
Let injA : 'injm inA := injm_sdpair2 _.

Hypotheses (coGA : coprime #|G| #|A|) (solG : solvable G).

Lemma external_action_im_coprime : coprime #|G'| #|A'|.
Proof. by rewrite !card_injm. Qed.

Let coGA' := external_action_im_coprime.

Let solG' : solvable G' := morphim_sol _ solG.

Let nGA' := im_sdpair_norm to.

Lemma ext_coprime_Hall_exists : 
  exists2 H : {group gT}, pi.-Hall(G) H & [acts A, on H | to].
Proof.
have [H' hallH' nHA'] := coprime_Hall_exists pi nGA' coGA' solG'.
have sHG' := pHall_sub hallH'.
exists (inG @*^-1 H')%G => /=.
  by rewrite -(morphim_invmE injG) -{1}(im_invm injG) morphim_pHall.
by rewrite actsEsd ?morphpreK // subsetIl. 
Qed.

Lemma ext_coprime_Hall_trans : forall H1 H2 : {group gT},
    pi.-Hall(G) H1 -> [acts A, on H1 | to] ->
    pi.-Hall(G) H2 -> [acts A, on H2 | to] ->
  exists2 x, x \in 'C_(G | to)(A) & H1 = (H2 :^ x)%G.
Proof.
move=> H1 H2 hallH1 nH1A hallH2 nH2A.
have sH1G := pHall_sub hallH1; have sH2G := pHall_sub hallH2.
rewrite !actsEsd // in nH1A nH2A.
have hallH1' : pi.-Hall(G') (inG @* H1) by rewrite morphim_pHall.
have hallH2' : pi.-Hall(G') (inG @* H2) by rewrite morphim_pHall.
have [x'] := coprime_Hall_trans nGA' coGA' solG' hallH1' nH1A hallH2' nH2A.
case/setIP=> /= Gx' cAx'; move/eqP=> defH1; pose x := invm injG x'.
have Gx: x \in G by rewrite -(im_invm injG) mem_morphim.
have def_x': x' = inG x by rewrite invmK.
exists x; first by rewrite inE Gx gacentEsd mem_morphpre /= -?def_x'.
apply/eqP; move: defH1; rewrite -!val_eqE def_x' /= -morphimJ //=.
by rewrite !eqEsubset !injmSK // conj_subG.
Qed.

Lemma ext_norm_conj_cent : forall (H : {group gT}) x,
    H \subset G -> x \in 'C_(G | to)(A) ->
  [acts A, on H :^ x | to] = [acts A, on H | to].
Proof.
move=> H x sHG; case/setIP=> Gx.
rewrite gacentEsd !actsEsd ?conj_subG ?morphimJ // 2!inE Gx /=.
exact: norm_conj_cent.
Qed.

Lemma ext_coprime_Hall_subset : forall X : {group gT},
    X \subset G -> pi.-group X -> [acts A, on X | to] ->
  exists H : {group gT},
    [/\ pi.-Hall(G) H, [acts A, on H | to] & X \subset H].
Proof.
move=> X sXG piX; rewrite actsEsd // => nXA'.
case: (coprime_Hall_subset nGA' coGA' solG' _ (morphim_pgroup _ piX) nXA').
  exact: morphimS.
move=> H' /= [piH' nHA' sXH']; have sHG' := pHall_sub piH'.
exists (inG @*^-1 H')%G; rewrite actsEsd ?subsetIl ?morphpreK // nHA'.
rewrite -sub_morphim_pre //= sXH'; split=> //.
by rewrite -(morphim_invmE injG) -{1}(im_invm injG) morphim_pHall.
Qed.

End FullExtension.

(* We only prove a weaker form of the coprime group action centraliser  *)
(* lemma, because it is more convenient in practice to make G the range *)
(* of the action, whence G both contains H and is stable under A.       *)
(*   However we do restrict the coprime/solvable assumptions to H, and  *)
(* we do not require that G normalize H.                                *)
Lemma ext_coprime_quotient_cent : forall H : {group gT},
    H \subset G -> [acts A, on H | to] -> coprime #|H| #|A| -> solvable H ->
 'C_(|to)(A) / H = 'C_(|to / H)(A).
Proof.
move=> H sHG nHA coHA solH; pose N := 'N_G(H).
have nsHN: H <| N by rewrite normal_subnorm.
have [sHN nHn] := andP nsHN.
have sNG: N \subset G by exact: subsetIl.
have nNA: {acts A, on group N | to}.
  split; rewrite // actsEsd // injm_subnorm ?injm_sdpair1 //=.
  by rewrite normsI ?norms_norm ?im_sdpair_norm -?actsEsd.
rewrite -!(gacentIdom _ A) -quotientInorm -gacentIim setIAC.
rewrite -(gacent_actby nNA) gacentEsd -morphpreIim /= -/N.
have:= (injm_sdpair1 <[nNA]>, injm_sdpair2 <[nNA]>).
set inG := sdpair1 _; set inA := sdpair2 _ => [[injG injA]].
set G' := inG @* N; set A' := inA @* A; pose H' := inG @* H.
have defN: 'N(H | to) = A by apply/eqP; rewrite eqEsubset subsetIl.
have def_Dq: qact_dom to H = A by rewrite qact_domE.
have sAq: A \subset qact_dom to H by rewrite def_Dq.
rewrite {2}def_Dq -(gacent_ract _ sAq); set to_q := (_ \ _)%gact.
have:= And3 (sdprod_sdpair to_q) (injm_sdpair1 to_q) (injm_sdpair2 to_q).
rewrite gacentEsd; set inAq := sdpair2 _; set inGq := sdpair1 _ => /=.
set Gq := inGq @* _; set Aq := inAq @* _ => [[q_d iGq iAq]].
have nH': 'N(H') = setT.
  apply/eqP; rewrite -subTset -im_sdpair mulG_subG morphim_norms //=.
  by rewrite -actsEsd // acts_actby subxx /= (setIidPr sHN).
have: 'dom (coset H' \o inA \o invm iAq) = Aq.
  by rewrite ['dom _]morphpre_invm /= nH' morphpreT.
case/domP=> qA [def_qA ker_qA _ im_qA].
have{coHA} coHA': coprime #|H'| #|A'| by rewrite !card_injm.
have{ker_qA} injAq: 'injm qA.
  rewrite {}ker_qA !ker_comp ker_coset morphpre_invm -morphpreIim /= setIC.
  by rewrite coprime_TIg // -kerE (trivgP injA) morphim1.
have{im_qA} im_Aq : qA @* Aq = A' / H'.
  by rewrite -{}im_qA !morphim_comp im_invm.
have: 'dom (quotm (sdpair1_morphism <[nNA]>) nsHN \o invm iGq) = Gq.
  by rewrite ['dom _]morphpre_invm /= quotientInorm.
case/domP=> qG [def_qG ker_qG _ im_qG].
have{ker_qG} injGq: 'injm qG.
  rewrite {}ker_qG ker_comp ker_quotm morphpre_invm (trivgP injG).
  by rewrite quotient1 morphim1.
have im_Gq: qG @* Gq = G' / H'.
  rewrite -{}im_qG morphim_comp im_invm morphim_quotm //= -/inG -/H'.
  by rewrite -morphimIdom setIAC setIid.
have{def_qA def_qG} q_J : {in Gq & Aq, morph_actJ qG qA}.
  move=> x' a'; case/morphimP=> Hx; case/morphimP=> x nHx Gx -> GHx ->{Hx x'}.
  case/morphimP=> a _ Aa ->{a'} /=; rewrite -/inAq -/inGq. 
  rewrite !{}def_qG {}def_qA /= !invmE // -sdpair_act //= -/inG -/inA.
  have Nx: x \in N by rewrite inE Gx.
  have Nxa: to x a \in N by case: (nNA); move/acts_act->.
  have [Gxa nHxa] := setIP Nxa.
  rewrite invmE qactE ?quotmE ?mem_morphim ?def_Dq //=.
  by rewrite -morphJ /= ?nH' ?inE // -sdpair_act //= actbyE.
pose q := sdprodm q_d q_J.
have{injAq injGq} injq: 'injm q.
  rewrite injm_sdprodm injAq injGq /= {}im_Aq {}im_Gq -/Aq .
  rewrite -(morphimIdom _ Aq) -quotientGI ?im_sdpair_TI ?morphimS //= -/H'.
  by rewrite morphim1 quotient1.
rewrite -[inGq @*^-1 _]morphpreIim -/Gq.
have sC'G: inG @*^-1 'C_G'(A') \subset G by rewrite !subIset ?subxx.
rewrite -[_ / _](injmK iGq) ?quotientS //= -/inGq; congr (_ @*^-1 _).
apply: (injm_morphim_inj injq); rewrite 1?injm_subcent ?subsetT //= -/q.
rewrite 2?morphim_sdprodml ?morphimS //= im_Gq.
rewrite morphim_sdprodmr ?morphimS //= im_Aq.
rewrite -{}im_qG morphim_comp morphim_invm ?morphimS //.
rewrite morphim_quotm morphpreK ?subsetIl //= -/H'.
rewrite coprime_norm_quotient_cent ?im_sdpair_norm ?nH' ?subsetT //=.
exact: morphim_sol.
Qed.

End ExternalAction.
