(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*          The Sylow theorem and its consequences                     *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype div prime finfun finset.
Require Import bigops groups morphisms automorphism normal action.
Require Import cyclic gprod pgroups commutators center nilpotent.

(* Require Import paths connect. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GroupScope.

Section ModP.

Variable (gT : finGroupType) (sT : finType).

Variable to : {action gT &-> sT}.

(***********************************************************************)
(*                                                                     *)
(*           The mod p lemma for the action of p-groups                *)
(*                                                                     *)
(***********************************************************************)

Lemma pgroup_fix_mod : forall (p : nat) (G : {group gT}) (S : {set sT}),
  p.-group G -> [acts (G | to) on S] -> #|S| %% p = #|'C_S(G | to)| %% p.
Proof.
move=> p G S; case/pgroup_1Vpr=> [-> _|[p_pr _ [n cardG] GactS]].
  rewrite (setIidPl _) //; apply/subsetP=> x _.
  by rewrite inE sub1set inE act1.
apply/eqP; rewrite -(cardsID 'C(G | to)) eqn_mod_dvd (leq_addr, addKn) //.
have: [acts (G | to) on S :\: 'C(G | to)]; last move/acts_sum_card_orbit <-.
  apply/actsP=> a Ga x; rewrite !in_setD (actsP GactS) //; congr (~~ _ && _).
  by apply: actsP Ga x; rewrite norm_act_fix ?normG.
apply: dvdn_sum => X; case/imsetP=> x; case/setDP=> _ nfx ->{X}.
have:= dvdn_orbit to G x; rewrite cardG.
case/dvdn_pfactor=> [//|[_|m _ ->]]; last by rewrite expnS dvdn_mulr.
move/card_orbit1=> fix_x; case/afixP: nfx => a Ga; apply/set1P.
by rewrite -fix_x mem_imset.
Qed.

End ModP.

Section Sylow.

Variables (p : nat) (gT : finGroupType) (G : {group gT}).
Implicit Types P Q H K : {group gT}.

Theorem Sylow's_theorem :
  [/\ forall P, [max P | p.-subgroup(G) P] = p.-Sylow(G) P,
      [transitive (G | 'JG) on 'Syl_p(G)],
      forall P, p.-Sylow(G) P -> #|'Syl_p(G)| = #|G : 'N_G(P)|
   &  prime p -> #|'Syl_p(G)| %% p = 1%N ].
Proof.
pose maxp A P := [max P | p.-subgroup(A) P]; pose S := [set P | maxp G P].
pose oG := orbit 'JG%act G.
have actS: [acts (G | 'JG) on S].
  apply/subsetP=> x Gx; rewrite 2!inE; apply/subsetP=> P; rewrite 3!inE.
  exact: max_pgroupJ.
have S_pG: forall P, P \in S -> P \subset G /\ p.-group P.
  by move=> P; rewrite inE; case/maxgroupP; case/andP.
have SmaxN: forall P Q, Q \in S -> Q \subset 'N(P) -> maxp 'N_G(P) Q.
  move=> P Q; rewrite inE; case/maxgroupP; case/andP=> sQG pQ maxQ nPQ.
  apply/maxgroupP; rewrite /psubgroup subsetI sQG nPQ.
  by split=> // R; rewrite subsetI -andbA andbCA; case/andP=> _; exact: maxQ.
have nrmG: forall P, P \subset G -> P <| 'N_G(P).
  by move=> P sPG; rewrite /normal subsetIr subsetI sPG normG.
have sylS: forall P, P \in S -> p.-Sylow('N_G(P)) P.
  move=> P S_P; have [sPG  pP] := S_pG P S_P.
  by rewrite normal_max_pgroup_Hall ?nrmG //; apply: SmaxN; rewrite ?normG.
have{SmaxN} defCS: forall P, P \in S -> 'C_S(P | 'JG) = [set P].
  move=> P S_P; apply/setP=> Q; rewrite {1}in_setI {1}conjG_fix.
  apply/andP/set1P=> [[S_Q nQP]|->{Q}]; last by rewrite normG.
  apply: val_inj; symmetry; case: (S_pG Q) => //= sQG _.
  by apply: uniq_normal_Hall (SmaxN Q _ _ _) => //=; rewrite ?sylS ?nrmG.
have{defCS} oG_mod: {in S &, forall P Q, #|oG P| %% p = (Q \in oG P) %% p}.
  move=> P Q S_P S_Q; have [sQG pQ] := S_pG _ S_Q.
  have soP_S: oG P \subset S by rewrite acts_orbit.
  have: [acts (Q | 'JG) on oG P].
    apply/actsP=> x; move/(subsetP sQG)=> Gx R; apply: orbit_transr.
    exact: mem_imset.
  move/pgroup_fix_mod=> -> //; rewrite -{1}(setIidPl soP_S) -setIA defCS //.
  rewrite (cardsD1 Q) setDE -setIA setICr setI0 cards0 addn0.
  by rewrite inE set11 andbT.
have [P S_P]: exists P, P \in S.
  have: p.-subgroup(G) 1 by rewrite /psubgroup sub1G pgroup1.
  by case/(@maxgroup_exists _ (p.-subgroup(G))) => P; exists P; rewrite inE.
have trS: [transitive (G | 'JG) on S].
  apply/imsetP; exists P => //; apply/eqP.
  rewrite eqEsubset andbC acts_orbit // S_P; apply/subsetP=> Q S_Q.
  have:= S_P; rewrite inE; case/maxgroupP; case/andP=> _.
  case/pgroup_1Vpr=> [|[p_pr _ _] _].
    move/group_inj=> -> max1; move/andP: (S_pG _ S_Q) => sGQ.
    by rewrite (group_inj (max1 Q sGQ (sub1G Q))) orbit_refl.
  have:= oG_mod _ _ S_P S_P; rewrite (oG_mod _ Q) // orbit_refl.
  by case: {+}(Q \in _) => //; rewrite mod0n modn_small ?prime_gt1.
have oS1: prime p -> #|S| %% p = 1%N.
  move=> pr_p; rewrite -(atransP trS P S_P) (oG_mod P P) //.
  by rewrite orbit_refl modn_small ?prime_gt1.
have oSiN: forall Q, Q \in S -> #|S| = #|G : 'N_G(Q)|.
  by move=> Q S_Q; rewrite -(atransP trS Q S_Q) card_orbit conjG_astab1. 
have sylP: p.-Sylow(G) P.
  rewrite pHallE; case: (S_pG P) => // -> /= pP.
  case p_pr: (prime p); last first.
    rewrite p_part lognE p_pr /=.
    by case/pgroup_1Vpr: pP p_pr => [-> _ | [-> //]]; rewrite cards1.
  rewrite -(LaGrangeI G 'N(P)) /= mulnC partn_mul ?cardG_gt0 // part_p'nat.
    by rewrite mul1n (card_Hall (sylS P S_P)).
  by rewrite p'natE // -indexgI -oSiN // /dvdn oS1.
have eqS: forall Q, maxp G Q = p.-Sylow(G) Q.
  move=> Q; apply/idP/idP=> [S_Q|]; last exact: Hall_max.
  have{S_Q} S_Q: Q \in S by rewrite inE.
  rewrite pHallE -(card_Hall sylP); case: (S_pG Q) => // -> _ /=.
  by case: (atransP2 trS S_P S_Q) => x _ ->; rewrite cardJg.
have ->: 'Syl_p(G) = S by apply/setP=> Q; rewrite 2!inE.
by split=> // Q sylQ; rewrite -oSiN ?inE ?eqS.
Qed.

Lemma max_pgroup_Sylow :
  forall P, [max P | p.-subgroup(G) P] = p.-Sylow(G) P.
Proof. by case Sylow's_theorem. Qed.

Lemma Sylow_superset : forall Q,
  Q \subset G -> p.-group Q -> {P : {group gT} | p.-Sylow(G) P & Q \subset P}.
Proof.
move=> Q sQG pQ; case: (@maxgroup_exists _ (p.-subgroup(G)) Q) => [|P].
  exact/andP.
by rewrite max_pgroup_Sylow; exists P.
Qed.

Lemma Sylow_exists : {P : {group gT} | p.-Sylow(G) P}.
Proof. by case: (Sylow_superset (sub1G G) (pgroup1 _ p)) => P; exists P. Qed.

Lemma Syl_trans : [transitive (G | 'JG) on 'Syl_p(G)].
Proof. by case Sylow's_theorem. Qed.

Lemma Sylow_trans : forall P Q,
  p.-Sylow(G) P -> p.-Sylow(G) Q -> exists2 x, x \in G & Q :=: P :^ x.
Proof.
move=> P Q sylP sylQ; have:= (atransP2 Syl_trans) P Q; rewrite !inE.
by case=> // x Gx ->; exists x.
Qed.

Lemma Sylow_subJ : forall P Q,
  p.-Sylow(G) P -> Q \subset G -> p.-group Q ->
  exists2 x, x \in G & Q \subset P :^ x.
Proof.
move=> P Q sylP sQG pQ; have [Px sylPx] := Sylow_superset sQG pQ.
by have [x Gx ->] := Sylow_trans sylP sylPx; exists x.
Qed.

Lemma Sylow_Jsub : forall P Q,
  p.-Sylow(G) P -> Q \subset G -> p.-group Q ->
  exists2 x, x \in G & Q :^ x \subset P.
Proof.
move=> P Q sylP sQG pQ; have [x Gx] := Sylow_subJ sylP sQG pQ.
by exists x^-1; rewrite (groupV, sub_conjgV).
Qed.

Lemma card_Syl : forall P, p.-Sylow(G) P -> #|'Syl_p(G)| = #|G : 'N_G(P)|.
Proof. by case Sylow's_theorem. Qed.

Lemma card_Syl_dvd : #|'Syl_p(G)| %| #|G|.
Proof. case Sylow_exists => P; move/card_Syl->; exact: dvdn_indexg. Qed.

Lemma card_Syl_mod : prime p -> #|'Syl_p(G)| %% p = 1%N.
Proof. by case Sylow's_theorem. Qed.

Lemma Frattini_arg : forall H P, G <| H -> p.-Sylow(G) P -> G * 'N_H(P) = H.
Proof.
move=> H P; case/andP=> sGH nGH sylP.
rewrite -normC ?subIset ?nGH ?orbT // -conjG_astab1.
move/subgroup_transitiveP: Syl_trans => ->; rewrite ?inE //.
apply/imsetP; exists P; rewrite ?inE //.
apply/eqP; rewrite eqEsubset -{1}((atransP Syl_trans) P) ?inE // imsetS //=.
apply/subsetP=> Q; case/imsetP=> x Hx ->{Q}.
by rewrite inE -(normsP nGH x Hx) pHallJ2.
Qed.

End Sylow.

Section MoreSylow.

Variables (p : nat) (gT : finGroupType).
Implicit Types G H P : {group gT}.

Lemma pSylow_normalI : forall G H P,
  G <| H -> p.-Sylow(H) P -> p.-Sylow(G) (G :&: P).
Proof.

move=> G H P; case/normalP=> sGH nGH sylP.
have [Q sylQ] := Sylow_exists p G.
case/maxgroupP: (Hall_max sylQ); case/andP=> sQG pQ maxQ.
have [R sylR sQR] := Sylow_superset (subset_trans sQG sGH) pQ.
have [x Hx ->] := Sylow_trans sylR sylP.
rewrite -(nGH x Hx) -conjIg pHallJ2.
have: Q \subset G :&: R by rewrite subsetI sQG.
move/maxQ->; rewrite // /psubgroup subsetIl.
apply: pgroupS (pHall_pgroup sylR); exact: subsetIr.
Qed.

Lemma normal_sylowP : forall G,
  reflect (exists2 P : {group gT}, p.-Sylow(G) P & P <| G)
          (#|'Syl_p(G)| == 1%N).
Proof.
move=> G; apply: (iffP idP) => [syl1 | [P sylP nPG]]; last first.
  by rewrite (card_Syl sylP) (setIidPl _) (indexgg, normal_norm).
have [P sylP] := Sylow_exists p G; exists P => //.
rewrite /normal (pHall_sub sylP); apply/setIidPl; apply/eqP.
rewrite eqEcard subsetIl -(LaGrangeI G 'N(P)) -indexgI /=.
by rewrite -(card_Syl sylP) (eqP syl1) muln1.
Qed.

Lemma trivg_center_pgroup : forall P, p.-group P -> 'Z(P) = 1 -> P :=: 1.
Proof.
move=> P pP Z1; case: (pgroup_1Vpr pP) => [// | [pr_p _ [n oPp]]].
have: #|'Z(P)| %% p = 1%N by rewrite Z1 cards1 modn_small ?prime_gt1.
rewrite /center -conjg_fix -pgroup_fix_mod ?oPp ?expnS ?modn_mulr //.
by rewrite conjg_astabs normG.
Qed.

Lemma Sylow_transversal_gen : forall (T : {set {group gT}}) G,
  (forall P, P \in T -> P \subset G) ->
  (forall p, p \in \pi(#|G|) -> exists2 P, P \in T & p.-Sylow(G) P) ->
  << \bigcup_(P \in T) P >> = G.
Proof.
move=> T G G_T T_G; apply/eqP; rewrite eqEcard gen_subG.
apply/andP; split; first exact/bigcupsP.
apply: dvdn_leq (cardG_gt0 _) _; apply/dvdn_partP=> // q.
case/T_G=> P T_P sylP; rewrite -(card_Hall sylP); apply: cardSg.
by rewrite sub_gen // bigcup_sup.
Qed.

Lemma Sylow_gen : forall G,
  << \bigcup_(P : {group gT} | Sylow G P) P >> = G.
Proof.
move=> G; set T := [set P : {group gT} | Sylow G P].
rewrite -{2}(@Sylow_transversal_gen T G) => [|P | q _].
- by congr <<_>>; apply: eq_bigl => P; rewrite inE.
- by rewrite inE; case/and3P.
case: (Sylow_exists q G) => P sylP; exists P => //.
by rewrite inE (p_Sylow sylP).
Qed.

Lemma quotient_nilZ : forall G, nilpotent (G / 'Z(G)) = nilpotent G.
Proof.
move=> G; apply/idP/idP; last exact: quotient_nil.
have nZG: G \subset 'N('Z(G)) by rewrite normal_norm ?center_normal.
case/lcnP=> n /=; move/trivgP; rewrite /= -morphim_lcn //.
rewrite quotient_sub1 ?(subset_trans _ nZG) ?lcn_sub0 // subsetI.
case/andP=> _ cLnG; apply/lcnP; exists n.+1; rewrite lcnSn; exact/commG1P.
Qed.

End MoreSylow.

Section Nilpotent.

Variable gT : finGroupType.
Implicit Types G H K P L : {group gT}.
Implicit Types p q : nat.

Lemma pgroup_nil : forall p P, p.-group P -> nilpotent P.
Proof.
move=> p P; move: {2}_.+1 (ltnSn #|P|) => n.
elim: n gT P => // n IHn pT P; rewrite ltnS=> lePn pP.
case: (eqVneq 'Z(P) 1) => [Z1 | ntZ].
  by rewrite (trivg_center_pgroup pP Z1) nilpotent1.
rewrite -quotient_nilZ IHn ?morphim_pgroup // (leq_trans _ lePn) //.
rewrite card_quotient ?normal_norm ?center_normal // -divgS ?subsetIl //.
by rewrite ltn_Pdiv // ltnNge -trivg_card_le1.
Qed.

Lemma pgroup_sol : forall p P, p.-group P -> solvable P.
Proof. move=> p P; move/pgroup_nil; exact: nilpotent_sol. Qed.

Lemma small_nil_class : forall G, nil_class G <= 5 -> nilpotent G.
Proof.
move=> G leK5; case: (ltnP 5 #|G|) => [lt5G | leG5 {leK5}].
  by rewrite nilpotent_class (leq_ltn_trans leK5).
apply: pgroup_nil (pdiv #|G|) _ _; apply/andP; split=> //.
by case: #|G| leG5 => //; do 5!case=> //.
Qed.

Lemma nilpotent_maxp_normal : forall pi G H,
  nilpotent G -> [max H | pi.-subgroup(G) H] -> H <| G.
Proof.
move=> pi G H nilG; case/maxgroupP; case/andP=> sHG piH maxH.
have nHN: H <| 'N_G(H) by rewrite normal_subnorm.
have{maxH} hallH: pi.-Hall('N_G(H)) H.
  apply: normal_max_pgroup_Hall => //; apply/maxgroupP. 
  rewrite /psubgroup normal_sub // piH; split=> // K.
  rewrite subsetI -andbA andbCA; case/andP=> _; exact: maxH.
rewrite /normal sHG; apply/setIidPl; symmetry.
apply: nilpotent_sub_norm; rewrite ?subsetIl ?setIS //=.
by rewrite char_norms // -{1}(normal_Hall_pcore hallH) // pcore_char.
Qed.

Lemma nilpotent_Hall_pcore : forall pi G H,
  nilpotent G -> pi.-Hall(G) H -> H :=: 'O_pi(G).
Proof.
move=> pi G H nilG hallH; have maxH := Hall_max hallH; apply/eqP.
rewrite eqEsubset pcore_max ?(pHall_pgroup hallH) //.
  by rewrite (normal_sub_max_pgroup maxH) ?pcore_pgroup ?pcore_normal.
exact: nilpotent_maxp_normal maxH.
Qed.

Lemma nilpotent_pcore_Hall : forall pi G, nilpotent G -> pi.-Hall(G) 'O_pi(G).
Proof.
move=> pi G nilG; case: (@maxgroup_exists _ (psubgroup pi G) 1) => [|H maxH _].
  by rewrite /psubgroup sub1G pgroup1.
have hallH := normal_max_pgroup_Hall maxH (nilpotent_maxp_normal nilG maxH).
by rewrite -(nilpotent_Hall_pcore nilG hallH).
Qed.

Lemma nilpotent_pcoreC : forall pi G,
   nilpotent G -> 'O_pi(G) \x 'O_pi^'(G) = G.
Proof.
move=> pi G nilG; have trO: 'O_pi(G) :&: 'O_pi^'(G) = 1.
  apply: coprime_TIg; apply: (@pnat_coprime pi); exact: pcore_pgroup.
rewrite dprodE //.
  apply/eqP; rewrite eqEcard mul_subG ?pcore_sub // (TI_cardMg trO).
  by rewrite !(card_Hall (nilpotent_pcore_Hall _ _)) // partnC ?leqnn.
rewrite (sameP commG1P trivgP) -trO subsetI commg_subl commg_subr.
by rewrite !(subset_trans (pcore_sub _ _)) ?normal_norm ?pcore_normal.
Qed.

End Nilpotent.

Definition Zgroup (gT : finGroupType) (A : {set gT}) := 
  forallb V : {group gT}, Sylow A V ==> cyclic V.

Section Zgroups.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types G H K : {group gT}.

Lemma ZgroupS : forall G H, H \subset G -> Zgroup G -> Zgroup H. 
Proof.
move=> G H sHG; move/forallP=> zgG; apply/forallP=> V; apply/implyP.
case/SylowP=> p pr_p; case/and3P=> sVH.
case/(Sylow_superset (subset_trans sVH sHG))=> P sylP sVP _.
have:= zgG P; rewrite (p_Sylow sylP); exact: cyclicS.
Qed.

Lemma morphim_Zgroup : forall G, Zgroup G -> Zgroup (f @* G). 
Proof.
move=> G zgG; wlog sGD: G zgG / G \subset D.
  by rewrite -morphimIdom; apply; rewrite (ZgroupS _ zgG, subsetIl) ?subsetIr.
apply/forallP=> fV; apply/implyP.
case/SylowP=> p pr_p sylfV; have [P sylP] := Sylow_exists p G.
have [|z _ ->] := @Sylow_trans p _ _ (f @* P)%G _ _ sylfV.
  apply: morphim_pHall (sylP); exact: subset_trans (pHall_sub sylP) sGD.
rewrite cyclicJ morphim_cyclic // (implyP (forallP zgG P)) //.
by apply/SylowP; exists p.
Qed.

Lemma nil_Zgroup_cyclic : forall G, Zgroup G -> nilpotent G -> cyclic G.
Proof.
move=> G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G; rewrite ltnS => leGn.
move=> ZgG nilG; case: (trivgVpdiv G) => [->|[p pr_p pG]].
  by rewrite -cycle1 cycle_cyclic.
case/dprodP: (nilpotent_pcoreC p nilG) => _ defG Cpp' _.
have: cyclic 'O_p^'(G).
  have sp'G := pcore_sub p^' G.
  apply: IHn (leq_trans _ leGn) (ZgroupS sp'G _) (nilpotentS sp'G _) => //.
  rewrite proper_card // properEneq sp'G andbT; case: eqP => //= def_p'.
  by have:= pcore_pgroup p^' G; rewrite def_p' /pgroup p'natE ?pG.
have: cyclic 'O_p(G).
  have:= forallP ZgG 'O_p(G)%G.
  by rewrite (p_Sylow (nilpotent_pcore_Hall p nilG)).
case/cyclicP=> x def_p; case/cyclicP=> x' def_p'.
apply/cyclicP; exists (x * x'); rewrite -{}defG def_p def_p' cycleM //.
  by apply: (centsP Cpp'); rewrite (def_p, def_p') cycle_id.
rewrite /order -def_p -def_p' (@pnat_coprime p) //; exact: pcore_pgroup.
Qed.

End Zgroups.

Section NilPGroups.

Variables (p : nat) (gT : finGroupType).
Implicit Type G P N : {group gT}.

(* Bender 1.22 p.9 *)

Lemma normal_pgroup : forall r P N, 
  p.-group P -> N <| P -> r <= logn p #|N| ->
  exists Q : {group gT}, [/\ Q \subset N, Q <| P & #|Q| = (p ^ r)%N].
Proof.
move=> r; elim: r gT => [|r IHr] gTr P N pP nNP le_r.
  by exists (1%G : {group gTr}); rewrite sub1G normal1 cards1.
have: p.-group (N :&: 'Z(P)) by apply: pgroupS pP; rewrite /= setICA subsetIl.
case/pgroup_1Vpr=> [| [p_pr _ [k oZ]]].
  move/(nil_TI_Z (pgroup_nil pP) nNP)=> N1.
  by rewrite N1 cards1 logn1 in le_r.
have{oZ}: p %| #|N :&: 'Z(P)| by rewrite oZ dvdn_exp.
case/Cauchy=> // z; rewrite -sub1set -gen_subG -[<<_>>]/<[z]> !subsetI /order.
case/and3P=> sZN sZP cZP oZ.
have{cZP} nZP: P \subset 'N(<[z]>) by rewrite cents_norm // centsC.
have: N / <[z]> <| P / <[z]> by rewrite morphim_normal.
case/IHr=> [||Qb [sQNb nQPb]]; first exact: morphim_pgroup.
  rewrite card_quotient ?(subset_trans (normal_sub nNP)) // -ltnS.
  apply: (leq_trans le_r); rewrite -(LaGrange sZN) oZ.
  by rewrite logn_mul // ?prime_gt0 // logn_prime ?eqxx.
case/(inv_quotientN _): nQPb sQNb => [|Q -> sZQ nQP]; first exact/andP.
have nZQ := subset_trans (normal_sub nQP) nZP.
rewrite quotientSGK // card_quotient // => sQN.
move/eqP; rewrite -(eqn_pmul2l (cardG_gt0 <[z]>)) LaGrange // oZ -expnS.
by move/eqP; exists Q.
Qed.

Theorem Baer_Suzuki : forall x G,
  x \in G -> (forall y, y \in G -> p.-group <<[set x; x ^ y]>>)
  -> x \in 'O_p(G).
Proof.
move=> x G; elim: {G}_.+1 {-2}G x (ltnSn #|G|) => // n IHn G x; rewrite ltnS.
set E := x ^: G => leGn Gx pE.
have{pE} pE: {in E &, forall x1 x2, p.-group <<[set x1; x2]>>}.
  move=> x1 x2; case/imsetP=> y1 Gy1 ->; case/imsetP=> y2 Gy2 ->.
  rewrite -(mulgKV y1 y2) conjgM -2!conjg_set1 -conjUg genJ pgroupJ.
  by rewrite pE // groupMl ?groupV.
have sEG: <<E>> \subset G by rewrite gen_subG class_subG.
have nEG: G \subset 'N(E) by exact: norm_class.
have Ex: x \in E by exact: class_refl.
have [P Px sylP]: exists2 P : {group gT}, x \in P & p.-Sylow(<<E>>) P.
  have sxxE: <<[set x; x]>> \subset <<E>> by rewrite genS // setUid sub1set.
  have{sxxE} [P sylP sxxP] := Sylow_superset sxxE (pE _ _ Ex Ex).
  by exists P => //; rewrite (subsetP sxxP) ?mem_gen ?setU11.
case sEP: (E \subset P).
  apply: subsetP Ex; rewrite -gen_subG; apply: pcore_max.
    by apply: pgroupS (pHall_pgroup sylP); rewrite gen_subG.
  by rewrite /normal gen_subG class_subG // norms_gen.
pose P_yD D := [pred y | (y \in E :\: P) && p.-group <<y |: D>>].
pose P_D := [pred D : {set gT} | (D \subset P :&: E) && (existsb y, P_yD D y)].
have{Ex Px}: P_D [set x].
  rewrite /= sub1set inE Px Ex; apply/existsP=> /=.
  by  case/subsetPn: sEP => y Ey Py; exists y; rewrite inE Ey Py pE.
case/(@maxset_exists _ P_D)=> D; case/maxsetP; rewrite {P_yD P_D}/=.
rewrite subsetI sub1set -andbA; case/and3P=> sDP sDE.
case/existsP=> y0; set B := _ |: D.
rewrite inE -andbA; case/and3P=> Py0 Ey0 pB maxD Dx.
have sDgE: D \subset <<E>> by exact: sub_gen.
have sDG: D \subset G by exact: subset_trans sEG.
have sBE: B \subset E by rewrite subUset sub1set Ey0.
have sBG: <<B>> \subset G by exact: subset_trans (genS _) sEG.
have sDB: D \subset B by rewrite subsetUr.
have defD: D :=: P :&: <<B>> :&: E.
  apply/eqP; rewrite eqEsubset ?subsetI sDP sDE sub_gen //=.
  apply/setUidPl; apply: maxD; last exact: subsetUl.
  rewrite subUset subsetI sDP sDE setIAC subsetIl.
  apply/existsP; exists y0; rewrite inE Py0 Ey0 /= setUA -/B.
  by rewrite -[<<_>>]mulgen_idl mulgenE setKI genGid.
have nDD: D \subset 'N(D).
  apply/subsetP=> z Dz; rewrite inE; apply/subsetP=> yz.
  case/imsetP=> y; rewrite defD; case/setIP=> PBy Ey ->{yz}.
  rewrite inE groupJ // ?inE ?(subsetP sDP) ?mem_gen ?setU1r //= memJ_norm //.
  exact: (subsetP (subset_trans sDG nEG)).
case nDG: (G \subset 'N(D)).
  apply: subsetP Dx; rewrite -gen_subG pcore_max ?(pgroupS (genS _) pB) //.
  by rewrite /normal gen_subG sDG norms_gen.
have{n leGn IHn nDG} pN: p.-group <<'N_E(D)>>.
  apply: pgroupS (pcore_pgroup p 'N_G(D)); rewrite gen_subG /=.
  apply/subsetP=> x1; case/setIP=> Ex1 Nx1; apply: IHn => [||y Ny].
  - apply: leq_trans leGn; rewrite proper_card // /proper subsetIl.
    by rewrite subsetI nDG andbF.
  - by rewrite inE Nx1 (subsetP sEG) ?mem_gen.
  have Ex1y: x1 ^ y \in E.
    by rewrite  -mem_conjgV (normsP nEG) // groupV; case/setIP: Ny.
  apply: pgroupS (genS _) (pE _ _ Ex1 Ex1y).
  by apply/subsetP=> u; rewrite !inE.
have [y1 Ny1 Py1]: exists2 y1, y1 \in 'N_E(D) & y1 \notin P.
  case sNN: ('N_<<B>>('N_<<B>>(D)) \subset 'N_<<B>>(D)).
    exists y0 => //; have By0: y0 \in <<B>> by rewrite mem_gen ?setU11.
    rewrite inE Ey0 -By0 -in_setI.
    by rewrite -['N__(D)](nilpotent_sub_norm (pgroup_nil pB)) ?subsetIl.
  case/subsetPn: sNN => z; case/setIP=> Bz NNz; rewrite inE Bz inE.
  case/subsetPn=> y; rewrite mem_conjg => Dzy Dy.
  have:= Dzy; rewrite {1}defD; do 2![case/setIP]=> _ Bzy Ezy.
  have Ey: y \in E by rewrite -(normsP nEG _ (subsetP sBG z Bz)) mem_conjg.
  have: y \in 'N_<<B>>(D).
    by rewrite -(normP NNz) mem_conjg inE Bzy ?(subsetP nDD).
  case/setIP=> By Ny; exists y; first by rewrite inE Ey.
  by rewrite defD 2!inE Ey By !andbT in Dy.
have [y2 Ny2 Dy2]: exists2 y2, y2 \in 'N_(P :&: E)(D) & y2 \notin D.
  case sNN: ('N_P('N_P(D)) \subset 'N_P(D)).
    have [z /= Ez sEzP] := Sylow_Jsub sylP (genS sBE) pB.
    have Gz: z \in G by exact: subsetP Ez.
    have: ~~ (B :^ z \subset D).
      apply/negP; move/subset_leq_card; rewrite cardJg cardsU1.
      by rewrite {1}defD 2!inE (negPf Py0) ltnn.
    case/subsetPn=> y Bzy Dy; exists y => //; apply: subsetP Bzy.
    rewrite -setIA setICA subsetI sub_conjg (normsP nEG) ?groupV // sBE.
    have nilP := pgroup_nil (pHall_pgroup sylP).
    by rewrite -['N__(_)](nilpotent_sub_norm nilP) ?subsetIl // -gen_subG genJ.
  case/subsetPn: sNN => z; case/setIP=> Pz NNz; rewrite 2!inE Pz.
  case/subsetPn=> y Dzy Dy; exists y => //; apply: subsetP Dzy.
  rewrite -setIA setICA subsetI sub_conjg (normsP nEG) ?groupV //.
    by rewrite sDE -(normP NNz); rewrite conjSg subsetI sDP.
  apply: subsetP Pz; exact: (subset_trans (pHall_sub sylP)).
suff{Dy2} Dy2D: y2 |: D = D by rewrite -Dy2D setU11 in Dy2.
apply: maxD; last by rewrite subsetUr.
case/setIP: Ny2 => PEy2 Ny2; case/setIP: Ny1 => Ey1 Ny1.
rewrite subUset sub1set PEy2 subsetI sDP sDE.
apply/existsP; exists y1; rewrite inE Ey1 Py1; apply: pgroupS pN.
rewrite genS // !subUset !sub1set !in_setI Ey1 Ny1.
by case/setIP: PEy2 => _ ->; rewrite Ny2 subsetI sDE.
Qed.

End NilPGroups.