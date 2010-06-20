Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div prime fintype.
Require Import bigops ssralg finset groups morphisms perm automorphism normal.
Require Import commutators action zmodp cyclic center gprod pgroups nilpotent.
Require Import sylow abelian gseries maximal hall mxrepresentation.
Require Import BGsection1 BGsection2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Theorem three_dot_four : forall k (gT : finGroupType) (G K R V : {group gT}),
  solvable G -> odd #|G| ->
  K <| G -> Hall G K -> R \in [complements to K in G] -> prime #|R| ->
  k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  'C_V(R) = 1-> [~: R, K] \subset 'C_K(V).
Admitted.

Theorem three_dot_five : forall k (gT : finGroupType) (G K R V : {group gT}),
  solvable G ->
  K <| G -> R \in [complements to K in G] -> prime #|R| -> 'C_K(R) = 1->
  k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  #|'C_V(R)| = k -> K^`(1) \subset 'C_K(V).
Admitted.

Theorem three_dot_six : forall (gT : finGroupType) (G H R R0 : {group gT}),
    solvable G -> odd #|G| ->
    H <| G -> Hall G H -> R \in [complements to H in G] ->
    R0 \subset R -> prime #|R0| -> Zgroup 'C_H(R0) ->
  forall p, prime p -> p.-length_1 [~: H, R].
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn H R R0.
move=> solG oddG nHG hallH compH_R sR0R.
move oR0: #|R0| => r pr_r ZCHR0 p pr_p.
have sRG: R \subset G by case/complP: compH_R => _ <-; exact: mulG_subr.
case/complP: compH_R => trivgHR eqHR_G; case/andP: (hallH) => sHG coHH'.
have{coHH'} coHR: coprime #|H| #|R|.
  by have:= coHH'; rewrite -divgS -eqHR_G ?mulG_subl // TI_cardMg ?mulKn.
have nHR: R \subset 'N(H) := subset_trans sRG (normal_norm nHG).
have IHG: forall H1 R1 : {group gT},
  H1 \subset H -> H1 * R1 \subset 'N(H1) -> R0 \subset R1 -> R1 \subset R ->
  (#|H1| < #|H|) || (#|R1| < #|R|) -> p.-length_1 [~: H1, R1].
- move=> H1 R1 sH1 nH1 sR01 sR1 ltG1.
  move defHR1: (H1 <*> R1)%G => G1; have{defHR1} defG1: G1 :=: H1 * R1.
    have nH1R: R1 \subset 'N(H1) := subset_trans (mulG_subr H1 R1) nH1.
    by rewrite -defHR1 /= mulgenC norm_mulgenEl // normC.
  have coHR1: coprime #|H1| #|R1|.
    rewrite -(LaGrange sH1) -(LaGrange sR1) coprime_mull coprime_mulr in coHR.
    by case/andP: coHR; case/andP.
  have oG1: #|G1| = (#|H1| * #|R1|)%N by rewrite defG1 coprime_cardMg.
  have ltG1n: #|G1| < n.
    have:= leqif_mul (leqif_geq (subset_leq_card sH1))
                     (leqif_geq (subset_leq_card sR1)).
    rewrite -oG1 -coprime_cardMg // eqHR_G eqn0Ngt cardG_gt0 /= => leG1.
    by apply: leq_trans leGn; rewrite ltn_neqAle !leG1 andbT negb_and -!ltnNge.
  have sG1G: G1 \subset G.
    by rewrite defG1 mul_subG // (subset_trans sH1, subset_trans sR1).
  have solG1: solvable G1 := solvableS sG1G solG.
  have oddG1: odd #|G1|.
    move: oddG; do 2!rewrite -[odd _]negbK -dvdn2; apply: contra.
    move/dvdn_trans; apply; exact: cardSg.
  have nHG1: H1 <| G1 by rewrite /(H1 <| _) defG1 mulG_subl.
  have hallH1: Hall G1 H1.
    by rewrite /Hall -divgS normal_sub // oG1 mulKn.
  have complR1: R1 \in [complements to H1 in G1].
    by apply/complP; rewrite coprime_TIg.
  apply: IHn complR1 sR01 _ _ p pr_p => //; first by rewrite oR0.
  exact: ZgroupS (setSI _ sH1) ZCHR0.
without loss defHR: / [~: H, R] = H.
  have:= nHR; rewrite -commg_subr commGC => sHR_R.
  have:= sHR_R; rewrite subEproper; case/predU1P=> [-> -> //|s'HR_H _].
  rewrite -coprime_commGid //; last exact: solvableS solG.
  apply: IHG => //; last by rewrite proper_card.
  apply: subset_trans (normal_norm (commg_normal H R)).
  by rewrite mulgenC norm_mulgenEl // (normC nHR) mulSg.
have{IHn trivgHR hallH} IHquo: forall X : {group gT},
  X :!=: 1 -> X \subset H -> G \subset 'N(X) -> p.-length_1 (H / X).
- move=> X ntX sXH nXG; have nXH := subset_trans sHG nXG.
  have nXR := subset_trans sRG nXG; have nXR0 := subset_trans sR0R nXR.
  rewrite -defHR quotientE morphimR // -!quotientE.
  have ltG'n: #|G / X| < n.
    apply: leq_trans leGn; rewrite card_quotient //.
    rewrite -[#|G : X|]mul1n -(LaGrange (subset_trans sXH sHG)).
    by rewrite ltn_pmul2r // ltnNge -trivg_card_le1.
  have solG': solvable (G / X) by exact: quotient_sol.
  have oddG': odd #|G / X|.
    move: oddG; rewrite !odd_2'nat; exact: morphim_pgroup.
  have nHG': H / X <| G / X by exact: morphim_normal.
  have hallH': Hall (G / X) (H / X) by exact: morphim_Hall.
  have compR': (R / X)%G \in [complements to H / X in G / X].
    apply/complP; split; last by rewrite -morphimMl ?eqHR_G.
    by rewrite -morphimGI ?ker_coset // trivgHR morphim1.
  have sR0R': R0 / X \subset R / X by exact: morphimS.
  have pr_R0X: prime #|R0 / X|.
    have trXR0: X :&: R0 = 1 by apply/trivgP; rewrite -trivgHR setISS.
    by rewrite card_quotient // -divgI setIC trXR0 cards1 divn1 oR0.
  apply: IHn compR' sR0R' pr_R0X _ _ pr_p => //.
  have coHR0: coprime #|H| #|R0|.
    by rewrite -(LaGrange sR0R) coprime_mulr in coHR; case/andP: coHR.
  by rewrite -coprime_quotient_cent ?morphim_Zgroup ?(solvableS sHG).
rewrite defHR.
without loss Op'_H: / 'O_p^'(H) = 1.
  case: (eqVneq 'O_p^'(H) 1) => [_ -> // | ntO _].
  suffices: p.-length_1 (H / 'O_p^'(H)).
    by rewrite p'quo_plength1 ?pcore_normal ?pcore_pgroup.
  apply: IHquo => //; first by rewrite normal_sub ?pcore_normal.
  by rewrite normal_norm // (char_normal_trans (pcore_char _ _)).
move defV: 'F(H)%G => V.
have charV: V \char H by rewrite -defV Fitting_char.
have nVG: G \subset 'N(V) by rewrite normal_norm ?(char_normal_trans charV).
have sVH: V \subset H by rewrite normal_sub ?char_normal.
have defVp: V :=: 'O_p(H).
  rewrite -defV -(nilpotent_pcoreC p (Fitting_nil H)) // p_core_Fitting.
  by rewrite ['O_p^'('F(H))](trivgP _) ?dprodg1 // -Op'_H pcore_Fitting.
have pV: p.-group V by rewrite defVp pcore_pgroup.
have sCV_V: 'C_H(V) \subset V.
  by rewrite -defV cent_sub_Fitting ?(solvableS sHG).
wlog abV: / p.-abelem V.
  move/implyP; rewrite implybE -trivg_Phi //; case/orP=> // ntPhi.
  have chPhi: 'Phi(V) \char H := char_trans (Phi_char _) charV.
  have nPhiH := char_normal chPhi; have sPhiH := normal_sub nPhiH.
  have{chPhi} nPhiG: G \subset 'N('Phi(V)).
    exact: normal_norm (char_normal_trans chPhi nHG).
  rewrite -(pquo_plength1 nPhiH) 1?IHquo //.
    exact: pgroupS (Phi_sub _) pV.
  have: 'O_p^'(H / 'Phi(V)) <| H / 'Phi(V) by exact: pcore_normal.
  case/(inv_quotientN _) => //= W defW sPhiW nWH.
  have p'Wb: p^'.-group (W / 'Phi(V)) by rewrite -defW; exact: pcore_pgroup.
  suffices pW: p.-group W.
    rewrite defW; apply: card1_trivg (pnat_1 _ p'Wb); exact: morphim_pgroup.
  apply/pgroupP=> q pr_q; case/Cauchy=> // x Wx oxq; apply/idPn=> /= neqp.
  suff: <[x]> \subset V.
    rewrite gen_subG sub1set => Vx.
    by move/pgroupP: pV neqp => /= -> //; rewrite -oxq order_dvdG.
  apply: subset_trans sCV_V; rewrite subsetI cycle_subG; apply/andP; split.
    apply: subsetP Wx; exact: normal_sub.
  have coxV: coprime #[x] #|V|.
    by rewrite oxq coprime_sym (pnat_coprime pV) // pnatE.
  apply: (coprime_cent_Phi pV); first by rewrite coprime_sym.
  have: W :&: V \subset 'Phi(V); last apply: subset_trans.
    rewrite -quotient_sub1; last first.
      by rewrite subIset // orbC normal_norm // char_normal // Phi_char.
    rewrite (quotientIG _ (Phi_sub V)) setIC coprime_TIg //.
    by rewrite coprime_morphl // (pnat_coprime pV).
  case/andP: nWH => sWH nWH.
  rewrite subsetI andbC commg_subl cycle_subG; apply/andP; split.
    by apply: subsetP Wx; apply: subset_trans (subset_trans sWH _) nVG.
  move: nWH; rewrite -commg_subr; apply: subset_trans.
  by rewrite commgSS // cycle_subG //.
have{sCV_V} eqVC: V :=: 'C_H(V).
  by apply/eqP; rewrite eqEsubset sCV_V subsetI andbT sVH; case/abelemP: abV.
wlog{IHquo} nondecV:  / forall N1 N2,
      N1 \x N2 = V -> G \subset 'N(N1) :&: 'N(N2) -> N1 = 1 \/ N1 = V.
  pose decV := [pred N | [&& N.1 \x N.2 == V, G \subset 'N(N.1) :&: 'N(N.2),
                             N.1 != 1 & N.2 != 1]].
  case: (pickP decV) => [[A1 A2 /=] | trN12]; last first.
    apply=> N1 N2 defN nNG; move/(_ (N1, N2)): trN12 => /=.
    rewrite -defN eqxx {}nNG /= -negb_or; case/pred2P=> ->; [by left | right].
    by rewrite dprodg1.
  case: eqP => //=; case/dprodP=> [[N1 N2 -> ->{A1 A2}] defN _ trN12].
  have [sN1 sN2]: N1 \subset H /\ N2 \subset H.
    apply/andP; rewrite -subUset (subset_trans _ sVH) // -defN.
    by rewrite subUset mulG_subl mulG_subr.
  case/and3P=> nNG ntN1 ntN2 _; have [nN1 nN2]: N1 <| H /\ N2 <| H.
    by apply/andP; rewrite /normal sN1 sN2 /= -subsetI (subset_trans sHG).
  rewrite subsetI in nNG; case/andP: nNG => nN1G nN2G.
  by rewrite -(quo2_plength1 pr_p nN1 nN2) ?trN12 ?IHquo.
have: 'F(H / V) <| G / V.
  exact: char_normal_trans (Fitting_char _) (morphim_normal _ _).
case/(inv_quotientN _) => [| /= U defU sVU nUG].
  by apply/andP; rewrite (subset_trans sVH).
case/andP: nUG => sUG nUG; have nUR := subset_trans sRG nUG.
have sUH: U \subset H.
  have: U / V \subset H / V by rewrite -defU normal_sub ?Fitting_normal.
  by rewrite morphimSGK ?ker_coset // (subset_trans sUG).
have: exists2 K : {group gT}, p^'.-Hall(U) K & R \subset 'N(K).
  apply: coprime_Hall_exists => //; last exact: (solvableS sUG).
  by rewrite -(LaGrange sUH) coprime_mull in coHR; case/andP: coHR.
case=> K hallK nKR; have [sKU _]:= andP hallK.
have p'K: p^'.-group K by exact: pHall_pgroup hallK.
have p'Ub: p^'.-group 'F(H / V).
  rewrite -['F(H / V)](nilpotent_pcoreC p (Fitting_nil _)) /=.
  by rewrite p_core_Fitting defVp trivg_pcore_quotient dprod1g pcore_pgroup.
have nVU := subset_trans (subset_trans sUH sHG) nVG.
have defVK: U :=: V * K.
  have nVK := subset_trans sKU nVU.
  apply/eqP; rewrite eqEsubset mul_subG //= andbT -quotientSK //.
  rewrite subEproper eq_sym eqEcard.
  have: p^'.-Hall(U / V) (K / V) by exact: morphim_pHall.
  by case/pHallP=> -> ->; rewrite part_pnat_id ?leqnn //= -defU.
have sylV: p.-Sylow(U) V.
  have coVK: coprime #|V| #|K| := pnat_coprime pV p'K.
  by rewrite /pHall sVU [_.-group _]pV -card_quotient // -defU.
have defH: H :=: V * 'N_H(K).
  have nUH: U <| H by apply/andP; rewrite (subset_trans sHG).
  rewrite -{1}(Hall_Frattini_arg _ nUH hallK); last exact: solvableS solG.
  by rewrite defVK -mulgA [K * _]mulSGid // subsetI normG (subset_trans sKU).
have [P sylP nPR]:
  exists2 P : {group gT}, p.-Sylow('N_H(K)) P & R \subset 'N(P).
+ have sNH: 'N_H(K) \subset H by exact: subsetIl.
  apply: coprime_Hall_exists.
  - by apply/normsP=> x Rx /=; rewrite conjIg -normJ !(normsP _ _ Rx).
  - by move: coHR; rewrite -(LaGrange sNH) coprime_mull; case/andP.
  apply: solvableS solG; exact: subset_trans sHG.
have sPN: P \subset 'N_H(K) by case/andP: sylP.
have [sPH nKP]: P \subset H /\ P \subset 'N(K) by apply/andP; rewrite -subsetI.
have nVH := subset_trans sHG nVG; have nVP := subset_trans sPH nVH.
have sylVP: p.-Sylow(H) (V * P).
  have defVP: V * P = V <*> P by rewrite mulgenC -normC ?norm_mulgenEl.
  rewrite defVP pHallE /= -defVP mul_subG //= defVP.
  rewrite -(LaGrange sVH) partn_mul ?muln_gt0 ?cardG_gt0 //=.
  have: V \subset V <*> P by rewrite -defVP mulG_subl.
  move/LaGrange <-; rewrite part_pnat_id // eqn_pmul2l // /=.
  rewrite -!card_quotient //; last by rewrite gen_subG subUset normG.
  rewrite -defVP defH !quotient_mulgr.
  have: p.-Sylow('N_H(K) / V) (P / V) by exact: morphim_pHall.
  by case/pHallP=> _ ->.
case: (eqVneq [~: K, P] 1) => [trKP|ntKP].
  suffices sylVH: p.-Sylow(H) V.
    rewrite p_elt_gen_length1 // (_ : p_elt_gen p H = V).
      rewrite /pHall pcore_sub pcore_pgroup /= pnatNK.
      apply: pnat_dvd pV; exact: dvdn_indexg.
   (rewrite -(genGid V); congr <<_>>; apply/setP=> x; rewrite inE).
    apply/andP/idP=> [[Hx p_x] | Vx].
      by rewrite (mem_normal_Hall sylVH) // /normal sVH.
    split; [exact: (subsetP sVH) | exact: mem_p_elt Vx].
  suffices sPV: P \subset V by rewrite mulGSid in sylVP.
  have sol_HV : solvable (H / V).
    by apply: quotient_sol; apply: (solvableS sHG).
  have qPV: P / V \subset 'C_(H / V)('F(H / V)).
    rewrite defU subsetI; apply/andP; split; first by apply:morphimS.
    rewrite defVK quotient_mulgr; apply: quotient_cents2r.
    by rewrite commGC trKP sub1G.
  have sPU: P \subset U.
    rewrite defVK -quotientSK // -(quotient_mulgr _ K) -defVK -defU.
    exact: subset_trans qPV (cent_sub_Fitting sol_HV).
  rewrite (subset_normal_Hall _ sylV); last exact/andP.
  by rewrite /psubgroup ?sPU (pHall_pgroup sylP).
have{sylVP} dp: [~: V, K] \x 'C_V(K) :=: V.
  apply: coprime_abelian_cent_dprod; last by case/abelemP: abV.
    exact: subset_trans sKU nVU.
  exact: pnat_coprime pV p'K.
have trVeq: 'C_V(K) = 1 \/ 'C_V(K) = V.
  apply: (nondecV _  [~: V, K]); first by rewrite dprodC.
  rewrite -eqHR_G defH -mulgA mul_subG //.
    by rewrite subsetI commg_norml cents_norm // centsC {1}eqVC setIAC subsetIr.
  have: 'N_H(K) * R \subset 'N_G(K) by rewrite mul_subG ?setSI // subsetI sRG.
  move/subset_trans; apply; apply/subsetP=> x; case/setIP=> Gx nKx.
  rewrite 3!inE conjIg -centJ /= -{1}[[~:V, K]]setTI -morphim_conj.
  rewrite morphimR ?subsetT // !morphim_conj !setTI.
  by rewrite (normP nKx) (normsP nVG) ?subxx.
have{sKU sUH} sKH: K \subset H by exact: subset_trans sKU sUH.
have{trVeq dp} [Vcomm trCVK]: [~: V, K] = V /\ 'C_V(K) = 1.
  case trVeq=> [trC | eqC]; first by rewrite -{2}dp // trC dprodg1.
  case/eqP: ntKP; rewrite card1_trivg ?comm1G ?eqxx // (pnat_1 _ p'K) //.
  by apply: pgroupS pV; rewrite eqVC subsetI sKH centsC -eqC subsetIr.
have eqcn: 'N_V(K) = 'C_V(K).
  apply: coprime_norm_cent (pnat_coprime pV p'K).
  by rewrite -commg_subr commGC -{2}Vcomm subxx.
have trVN: V :&: 'N_H(K) = 1 by rewrite setIA (setIidPl sVH) eqcn.
have trVP: V :&: P = 1.
  by apply/trivgP; rewrite -trVN setIS // ?(subset_trans sPN).
have nVN: 'N_H(K) \subset 'N(V) by rewrite (subset_trans _ nVH) ?subsetIl.
have defK: K :=: 'F('N_H(K)).
  have isoV: 'injm (restrm nVN (coset V)).
    by rewrite ker_restrm ker_coset setIC trVN.
  have sKN: K \subset 'N_H(K) by rewrite subsetI sKH normG.
  rewrite -['N_H(K)](im_invm isoV) -injm_Fitting ?injm_invm //=.
  rewrite {2}morphim_restrm setIid -quotientE -quotient_mulgr -defH defU.
  rewrite defVK quotient_mulgr -{10}(setIidPr sKN) quotientE.
  by rewrite -(morphim_restrm nVN) morphim_invm.
have sCKK: 'C_H(K) \subset K.
  rewrite {2}defK; apply: subset_trans (cent_sub_Fitting _).
    by rewrite -defK subsetI subsetIr setIS // cent_sub.
  by apply: solvableS (solvableS sHG solG); apply: subsetIl.
have{nVN} ntKR0: [~: K, R0] != 1.
  rewrite (sameP eqP commG1P); apply: contra ntKP => cKR0.
  have Z_K: Zgroup K by apply: ZgroupS ZCHR0; rewrite subsetI sKH.
  have cycK: cyclic K by rewrite nil_Zgroup_cyclic // defK Fitting_nil.
  have AcycK := Aut_cyclic_abelian cycK.
  have sNR_K: [~: 'N_H(K), R] \subset K.
    apply: subset_trans sCKK; rewrite subsetI; apply/andP; split.
      apply: subset_trans (commSg R (subsetIl _ _)) _.
      by rewrite commGC commg_subr.
    suff: 'N(K)^`(1) \subset 'C(K).
      by apply: subset_trans; rewrite commgSS ?subsetIr.
    rewrite -ker_conj_aut ker_trivg_morphim comm_subG // morphimR //.
    have sjK_AK: conj_aut K @* 'N(K) \subset Aut K.
      apply/subsetP=> a; case/imsetP=> f _ ->; exact: Aut_aut.
    by rewrite -(commG1P AcycK) commgSS.
  suff sPV: P \subset V by rewrite -(setIidPr sPV) trVP commG1.
  have pPV: p.-group (P / V) by exact: morphim_pgroup (pHall_pgroup sylP).
  rewrite -quotient_sub1 // subG1 trivg_card1 (pnat_1 pPV _) //.
  have: p^'.-group (K / V) by exact: morphim_pgroup p'K.
  apply: pgroupS; apply: subset_trans (morphimS _ sNR_K).
  have nVR: R \subset 'N(V) by exact: subset_trans nVG.
  rewrite morphimR // -quotientE -quotient_mulgr -defH -morphimR ?morphimS //.
  by rewrite defHR.
have nKR0: R0 \subset 'N(K) by exact: subset_trans nKR.
have sKR0_G : K <*> R0 \subset G.
  by rewrite gen_subG subUset (subset_trans sKH) ?(subset_trans sR0R).
have nV_KR0: K <*> R0 \subset 'N(V) by exact: subset_trans nVG.
have: K :|: R0 \subset K <*> R0 by rewrite -gen_subG subxx.
rewrite subUset; case/andP=> sK_KR0 sR0_KR0.
have solKR0: solvable (K <*> R0) by exact: solvableS solG.
have coK_R0: coprime #|K| #|R0|.
  have:= coHR; rewrite -(LaGrange sKH) -(LaGrange sR0R).
  by rewrite coprime_mull coprime_mulr -andbA; case/andP.
have oKR0: #|K <*> R0| = (#|K| * #|R0|)%N.
  by rewrite norm_mulgenEr // coprime_cardMg.
have r'K: r^'.-group K.
  apply/pgroupP=> q pr_q dv_qK; apply/eqP=> def_q.
  by rewrite oR0 coprime_sym prime_coprime // -def_q dv_qK in coK_R0.
have rR0: r.-group R0 by by rewrite /pgroup oR0 pnat_id // inE /= eqxx.
have hallK_R0: r^'.-Hall(K <*> R0) K.
  by rewrite /pHall sK_KR0 r'K -divgS // pnatNK oKR0 mulKn.
have hallR0_K: r.-Sylow(K <*> R0) R0.
  by rewrite /pHall sR0_KR0 rR0 -divgS // oKR0 mulnK.
have trCKR0_V: 'C_(K <*> R0)(V) = 1.
  have nC_KR0: 'C_(K <*> R0)(V) <| K <*> R0.
    rewrite /(_ <| _) subsetIl normsI ?normG //.
    by rewrite (subset_trans nV_KR0) ?cent_norm.
  have hallCK: r^'.-Hall('C_(K <*> R0)(V)) 'C_K(V).
    rewrite -{2}(setIidPl sK_KR0) -setIA; exact: HallSubnormal hallK_R0.
  have hallCR0: r.-Sylow('C_(K <*> R0)(V)) 'C_R0(V).
    rewrite -{2}(setIidPl sR0_KR0) -setIA; exact: HallSubnormal hallR0_K.
  have sC_R0: 'C_(K <*> R0)(V) \subset R0.
    apply/setIidPr; apply/eqP; rewrite setIA (setIidPl sR0_KR0) //=.
    rewrite eqEcard -[#|'C_(K <*> R0)(V)|](partnC r) ?cardG_gt0 //.
    case/pHallP: hallCR0 => -> <-; case/pHallP: hallCK => _ <-.
    rewrite -{2}(muln1 #|_|) leq_mul // -trivg_card_le1 -subG1 -trVN.
    rewrite /= -{1}(setIidPl sKH) -setIA -eqVC setIC setIS //.
    by rewrite subsetI sKH normG.
  have:= cardSg sC_R0; rewrite oR0.
  case: (primeP pr_r) => _ dv_r; move/dv_r; rewrite -trivg_card1 /=.
  case/orP; move/eqP=> // oCr.
  case/negP: ntKR0; rewrite -subG1 -(coprime_TIg coK_R0) subsetI.
  rewrite commg_subl commg_subr nKR0 (subset_trans sK_KR0) //.
  rewrite -{2}(('C_(K <*> R0)(V) =P R0) _) ?normal_norm //.
  by rewrite eqEcard sC_R0 oCr /= oR0.
have oCVR0: #|'C_V(R0)| = p.
  case: (eqVneq 'C_V(R0) 1) => [trCVR0 | ntCVR0].
    case/negP: ntKR0; rewrite -subG1/= commGC.
    have <-: 'C_K(V) = 1 by apply/trivgP; rewrite -trCKR0_V setSI.
    apply: three_dot_four abV nV_KR0 _ trCVR0 => //=.
    - move: oddG; do 2!rewrite -[odd _]negbK -dvdn2; apply: contra.
      move/dvdn_trans; apply; exact: cardSg.
    - by rewrite /(K <| _) sK_KR0 gen_subG subUset normG.
    - exact: (pHall_Hall hallK_R0).
    - by apply/complP; rewrite coprime_TIg //= norm_mulgenEr.
    - by rewrite oR0.
    rewrite oKR0 -prime_coprime // coprime_mulr.
    rewrite (pnat_coprime _ p'K) ?pnat_id //=.
    move: coHR; rewrite -(LaGrange sPH) -(LaGrange sR0R).
    rewrite coprime_mull coprime_mulr -andbA andbC oR0; case/andP=> _.
    case/p_natP: (pHall_pgroup sylP) => // [[trP|i ->]].
      by case/negP: ntKP; rewrite (card1_trivg trP) commG1.
    by rewrite coprime_pexpl.
  have: cyclic 'C_V(R0).
    have: Sylow 'C_V(R0) 'C_V(R0); last apply/implyP.
      apply/SylowP; exists p => //.
      rewrite /pHall subxx indexgg andbT.
      apply: pgroupS pV; exact: subsetIl.
    have: Zgroup 'C_V(R0) by apply: ZgroupS ZCHR0; exact: setSI.
    move/forallP; exact.
  case/cyclicP=> x defC; rewrite defC.
  have: #[x] %| p.
    rewrite order_dvdn; apply/eqP.
    have:= cycle_id x; rewrite -defC setIC; case/setIP=> _.
    by case/abelemP: abV => // _; exact.
  case/primeP: pr_p => _ pr_p; move/pr_p; case/orP; move/eqnP=> // ox1.
  by rewrite trivg_card1 /= defC [#|_|]ox1 in ntCVR0.
have trCP_R0: 'C_P(R0) = 1.
  have pP := pHall_pgroup sylP; apply: card1_trivg.
  have: p.-group 'C_P(R0) by apply: pgroupS pP; exact: subsetIl.
  case/p_natP=> // [[-> //| i oC]].
  have {i oC}: p %| #|'C_P(R0)| by rewrite oC dvdn_exp.
  case/Cauchy=> // x Cx oxp.
  suff x1: <[x]> = 1 by rewrite -oxp /order x1 cards1 in pr_p.
  apply/trivgP; rewrite -trVP subsetI andbC cycle_subG /=.
  apply/andP; split; first by case/setIP: Cx.
  suff <-: 'C_V(R0) = <[x]> by rewrite subsetIl.
  have: cyclic 'C_(P <*> V)(R0).
    have: Sylow 'C_(P <*> V)(R0) 'C_(P <*> V)(R0); last apply/implyP.
      apply/SylowP; exists p => //.
      rewrite /pHall subxx indexgg andbT.
      suff: p.-group (P <*> V) by apply: pgroupS; exact: subsetIl.
      have: p.-nat (#|P| * #|V|)%N by rewrite pnat_mul //; exact/andP.
      by rewrite norm_mulgenEl // mul_cardG pnat_mul //; case/andP.
    suff: Zgroup 'C_(P <*> V)(R0) by move/forallP; exact.
    by apply: ZgroupS ZCHR0; rewrite setSI // gen_subG subUset sPH.
  case/cyclicP=> y defC; apply: congr_group.
  have y_x: x \in <[y]>.
    by apply: subsetP Cx; rewrite -defC setSI // sub_gen // subsetUl.
  have: p %| #[y] by rewrite -oxp order_dvdG.
  move/cycle_sub_group; set Cy1 := <[_]>%G => defCy1.
  have ->: <[x]>%G = Cy1.
    apply/set1P; rewrite -defCy1 inE cycle_subG y_x /=; exact/eqP.
  by apply/set1P; rewrite -defCy1 inE oCVR0 -defC setSI //= sub_gen ?subsetUr.
have defP: P :=: [~: P, R0].
  move: coHR; rewrite -(LaGrange sPH) -(LaGrange sR0R).
  rewrite coprime_mull coprime_mulr -andbA andbC; case/andP=> _.
  move/coprime_cent_prod=> defP; rewrite -{1}defP ?(subset_trans sR0R) //.
    by rewrite trCP_R0 mulg1.
  apply: solvableS solG; exact: subset_trans sHG.
have{IHG} IHG: forall X : {group gT},
  P <*> R0 \subset 'N(X) -> X \subset K ->
  (#|V <*> X <*> P| < #|H|) || (#|R0| < #|R|) -> [~: X, P] = 1.
- move=> X nX_PR0 sXK ltX_G; apply/trivgP.
  have sXH: V <*> X <*> P \subset H.
    rewrite gen_subG subUset sPH andbT gen_subG subUset sVH /=.
    exact: subset_trans sKH.
  have nXR0: R0 \subset 'N(V <*> X <*> P).
    rewrite mulgenC mulgenA norms_mulgen //.
      by rewrite (subset_trans sR0R) ?norms_mulgen // (subset_trans sRG).
    by apply: subset_trans nX_PR0; rewrite sub_gen ?subsetUr.
  have trOp'H1: 'O_p^'(V <*> X <*> P) = 1.
    apply: card1_trivg; apply: pnat_1 (pcore_pgroup _ _) => //=.
    have nO_X := pcore_normal p^' (V <*> X <*> P).
    apply: pgroupS pV; rewrite {2}eqVC subsetI.
    rewrite (subset_trans _ sXH) ?(normal_sub nO_X) //= centsC.
    apply/setIidPl; rewrite -coprime_norm_cent.
    + apply/setIidPl; case/andP: nO_X => _; apply: subset_trans.
      by rewrite /= -mulgenA sub_gen // subsetUl.
    + apply: subset_trans nVH; apply: subset_trans sXH; exact: normal_sub.
    apply: pnat_coprime (pcore_pgroup _ _).
    rewrite defVp; exact: pcore_pgroup.
  have{trOp'H1} trOR: 'O_p^'([~: V <*> X <*> P, R0]) = 1.
    apply/trivgP; rewrite -trOp'H1.
    apply: pcore_max; first exact: pcore_pgroup.
    apply: char_normal_trans (pcore_char _ _) _.
    by rewrite /(_ <| _) commg_norml /= commGC commg_subr andbT.
  have sP_O: P \subset 'O_p([~: V <*> X <*> P, R0]).
    rewrite (@subset_normal_Hall _ p _ [~: ((V <*> X) <*> P)%g, R0]).
    + rewrite /psubgroup (pHall_pgroup sylP) {1}defP commSg //.
      by rewrite sub_gen // subsetUr.
    + rewrite /pHall pcore_sub pcore_pgroup /= -(pseries_pop2 _ trOR).
      rewrite -card_quotient ?normal_norm ?pseries_normal //.
      have{ltX_G IHG} VXPR_1: p.-length_1 [~: V <*> X <*> P, R0].
        by apply: IHG ltX_G => //=; rewrite mul_subG ?normG.
      rewrite -{1}((_ =P [~: _, _]) VXPR_1) (quotient_pseries [::_;_]).
      exact: pcore_pgroup.
    exact: pcore_normal.
  have <-: K :&: 'O_p([~: (V <*> X) <*> P, R0]) = 1.
    apply: coprime_TIg; rewrite coprime_sym (pnat_coprime _ p'K) //.
    exact: pcore_pgroup.
  rewrite subsetI; apply/andP; split.
    by apply: subset_trans (commSg _ sXK) _; rewrite commGC commg_subr.
  apply: subset_trans (commgS _ sP_O) _; rewrite commg_subr.
  have: X \subset V <*> X <*> P by rewrite mulgenC mulgenA sub_gen ?subsetUr.
  move/subset_trans; apply; apply: normal_norm.
  apply: char_normal_trans (pcore_char _ _) _.
  by rewrite /(_ <| _) commg_norml andbT /= commGC commg_subr.
clear defH.
have[]: H :==: V * K * P /\ R0 :==: R.
  rewrite eq_sym !eqEcard sR0R ?mul_subG //=; apply/andP.
  do 2!rewrite leqNgt andbC; rewrite -negb_or; apply: contra ntKP.
  rewrite -mulgA -norm_mulgenEr // -norm_mulgenEr; last first.
    by rewrite (subset_trans _ nVH) // gen_subG subUset sPH sKH.
  rewrite mulgenA; move/IHG=> -> //.
  by rewrite gen_subG subUset nKP (subset_trans sR0R).
move/eqP=> defH; move/eqP=> defR.
clear U defU sVU sUG nUG nUR hallK p'Ub nVU defVK sylV sPN.
clear sKR0_G nV_KR0 sK_KR0 sR0_KR0 solKR0 coK_R0 oKR0 hallK_R0 hallR0_K.
move: {sR0R} IHG oR0 ZCHR0 ntKR0 {nKR0} rR0 trCKR0_V oCVR0 trCP_R0 defP.
rewrite {R0}defR ltnn => IHG oR ZCHR ntKR rR trCKR_V oCVR trCP_R defP.
have{sylP} pP: p.-group P by case/and3P: sylP.
have{nVH} nVK: K \subset 'N(V) by exact: subset_trans nVH.
have oVK: #|V <*> K| = (#|V| * #|K|)%N.
  by rewrite norm_mulgenEr // coprime_cardMg // (pnat_coprime pV).
have trVK_P: V <*> K :&: P = 1.
  apply/trivgP; rewrite -trVP /= -{1}(setIid P) setIA setSI //=.
  have sV_VK: V \subset V <*> K by rewrite sub_gen ?subsetUl.
  have sylV: p.-Sylow(V <*> K) V.
    by rewrite pHallE sV_VK oVK partn_mul // /= part_pnat_id ?part_p'nat ?muln1.
  rewrite (subset_normal_Hall _ sylV) /=.
    rewrite /psubgroup subsetIl; apply: pgroupS pP; exact: subsetIr.
  by rewrite /normal sV_VK gen_subG subUset normG.
have oH: (#|H| = #|V| * #|K| * #|P|)%N.
  by rewrite defH -(norm_mulgenEr nVK) -oVK (TI_cardMg trVK_P).
have{IHG} IHK: forall X : {group gT},
  P <*> R \subset 'N(X) -> X \subset K -> X :=: K \/ X \subset 'C(P).
- move=> X nX_PR sXK.
  have:= sXK; rewrite subEproper; case/predU1P; first by left.
  move/proper_card => ltXK; right; apply/commG1P.
  apply: IHG => //; move: nX_PR; rewrite mulgen_subG; case/andP=> nXP _.
  rewrite [_ <*> _]norm_mulgenEr; last first.
    by rewrite norms_mulgen ?nVP // commGC commg_norml.
  rewrite TI_cardMg /=; last first.
    by apply/trivgP; rewrite -trVK_P setSI ?genS ?setUS.
  rewrite oH ltn_pmul2r ?cardG_gt0 // norm_mulgenEr ?(subset_trans sXK) //.
  rewrite orbF coprime_cardMg // ?ltn_pmul2l // (pnat_coprime pV) //.
  exact: pgroupS p'K.
have defKP: K :=: [~: K, P].
  have sKP_K: [~: K, P] \subset K by rewrite commGC commg_subr.
  case: (IHK _ _ sKP_K) => //.
    by rewrite gen_subG subUset /= {1}commGC commg_norml normsR.
  move/commG1P=> /= KP1.
  case/eqP: ntKP; rewrite /= -coprime_commGid //.
    by rewrite coprime_sym (pnat_coprime pP).
  apply: solvableS solG; exact: subset_trans sKH sHG.
have nrp: r != p.
  move: coHR; rewrite oR coprime_sym prime_coprime -?p'natE // => r'H.
  have sCH: 'C_V(R) \subset H by apply: subset_trans sVH; exact: subsetIl.
  by rewrite eq_sym; apply: (pgroupP (pgroupS sCH r'H)); rewrite ?oCVR.
have nKPR: P <*> R \subset 'N(K) by rewrite mulgen_subG nKP.
have trCPR_K: 'C_(P <*> R)(K) = 1.
  have solPR: solvable (P <*> R).
     apply: solvableS solG; rewrite gen_subG subUset sRG.
     by rewrite (subset_trans sPH sHG).
  have coPR: coprime #|P| #|R| by rewrite oR (pnat_coprime pP) ?pnatE.
  have nC_PR: 'C_(P <*> R)(K) <| P <*> R.
    by rewrite /normal subsetIl normsI ?normG ?norms_cent.
  have sP_PR: P \subset P <*> R by rewrite sub_gen ?subsetUl.
  have sR_PR: R \subset P <*> R by rewrite sub_gen ?subsetUr.
  have p'R: p^'.-group R by rewrite /pgroup oR pnatE.
  have sylPC: p.-Sylow('C_(P <*> R)(K)) 'C_P(K).
    rewrite -{2}(setIidPl sP_PR) -setIA (HallSubnormal _ nC_PR) //.
    rewrite /pHall sP_PR pP /= -divgS //= norm_mulgenEr //.
    by rewrite coprime_cardMg // mulKn.
  have hallRC: p^'.-Hall('C_(P <*> R)(K)) 'C_R(K).
    rewrite -{2}(setIidPl sR_PR) -setIA (HallSubnormal _ nC_PR) //.
    rewrite /pHall sR_PR /= -divgS //= norm_mulgenEr //.
    rewrite coprime_cardMg // mulnK // pnatNK; exact/andP.
  have trCP: 'C_P(K) = 1.
    apply/trivgP; rewrite /= -{1}(setIidPl sPH) -setIA.
    have <-: P :&: K = 1 by apply coprime_TIg; exact: pnat_coprime pP p'K.
    exact: setIS.
  have trCR: #|'C_R(K)| = 1%N.
    have: #|'C_R(K)| %| r by rewrite -oR cardSg ?subsetIl.
    case/primeP: pr_r => _ pr_r; move/pr_r; case/orP; move/eqP=> // oCR.
    case/eqP: ntKR; apply/commG1P; rewrite centsC; apply/setIidPl.
    by apply/eqP; rewrite eqEcard oR oCR leqnn subsetIl.
  apply: card1_trivg; rewrite -[#|_|](partnC p) // -(card_Hall sylPC).
  by rewrite -(card_Hall hallRC) trCR muln1 /= trCP cards1.
have [K1 | [q q_pr qKdv]] := trivgVpdiv K.
  by rewrite K1 comm1G eqxx in ntKR.
have nqp: q != p by exact: (pgroupP p'K).
have nrq: r != q by rewrite eq_sym; exact: (pgroupP r'K).
have{defK} qK: q.-group K.
  have IHpi: forall pi, 'O_pi(K) = K \/ 'O_pi(K) \subset 'C(P).
    move=> pi; apply: IHK (pcore_sub _ _).
    by apply: char_norm_trans (pcore_char _ _) _; rewrite mulgen_subG nKP.
  case: (IHpi q) => [<-| cPKq]; first exact: pcore_pgroup.
  have{defK} nilK: nilpotent K by rewrite defK Fitting_nil.
  case/dprodP: (nilpotent_pcoreC q nilK) => _ defK _ _.
  case/eqP: ntKP; apply/commG1P; rewrite -{}defK mul_subG //.
  case: (IHpi q^') => // defK; case/idPn: qKdv.
  rewrite -p'natE // -defK; exact: pcore_pgroup.
pose K' := (K)^`(1); have nK'K: K' <| K := der_normal 1 K.
have nK'PR: P <*> R \subset 'N(K').
  exact: char_norm_trans (der_char 1 K) nKPR.
have iK'K: 'C_(P <*> R / K')(K / K') = 1 -> #|K / K'| > q ^ 2.
  have: q.-group (K / K') by exact: morphim_pgroup qK.
  case/p_natP=> // k oK; rewrite oK ltn_exp2l ?prime_gt1 // ltnNge.
  move=> trCK'; apply: contra ntKP => lek2.
  suff trP: [~: P, R] = 1 by rewrite defP trP commG1.
  have coK_PR: \pi(#|K|)^'.-group (P <*> R).
    rewrite norm_mulgenEr // pgroupM /pgroup -!coprime_pi' // coprime_sym.
    by rewrite (pnat_coprime pP) // coprime_sym oR prime_coprime // -p'natE.
  suff sPR_K': [~: P, R] \subset K'.
    rewrite -(setIidPl sPR_K') coprime_TIg //.
    apply: pnat_coprime (pgroupS (normal_sub nK'K) p'K).
    by apply: pgroupS pP; rewrite /= commGC commg_subr.
  rewrite -quotient_cents2 ?(char_norm_trans (der_char 1 K)) //.
  suffices abPR: abelian (P <*> R / K').
    by apply: subset_trans (subset_trans abPR (centS _));
      rewrite quotientS ?mulgen_subl ?mulgen_subr.
  have nKqPR: P <*> R / K' \subset 'N(K / K') by rewrite quotient_norms.
  case cycK: (cyclic (K / K')).
    have inj_autPR: 'injm (restrm nKqPR (conj_aut (K / K'))).
      by rewrite ker_restrm ker_conj_aut trCK'.
    rewrite -(im_invm inj_autPR) morphim_abelian //.
    apply: abelianS (Aut_cyclic_abelian cycK).
    by apply/subsetP=> pK'x; case/morphimP=> K'x _ _ /= ->; exact: Aut_aut.
  have{cycK} [k2 abelK]: k = 2 /\ q.-abelem (K / K').
    case: k lek2 oK => [|[|[|//]]] _ oK.
    - by rewrite (card1_trivg oK) cyclic1 in cycK.
    - by rewrite prime_cyclic ?oK in cycK.
    split=> //; apply/abelemP=> //=; split=> [|K'x KK'x].
      suff ->: K / K' = 'Z(K / _) by exact: center_abelian.
      have:= center_sub (K / K'); move/cardSg; rewrite oK.
      case/dvdn_pfactor=> [//|[|[|[|//]]] _ oZ].
      - have: q.-group (K / K') by exact: morphim_pgroup.
        by move/trivg_center_pgroup; rewrite /= ['Z(_)]card1_trivg ?oZ // => ->.
      - apply: center_cyclic_abelian (prime_cyclic _).
        rewrite card_quotient ?char_norm ?center_char //=.
        by rewrite -divgS ?subsetIl // oZ oK mulnK // prime_gt0.
      by apply/eqP; rewrite eq_sym eqEcard oK oZ subsetIl leqnn.
    apply/eqP; have:= order_dvdG KK'x; rewrite -order_dvdn oK.
    case/dvdn_pfactor=> // k le_k2 ox; rewrite ox pfactor_dvdn ?prime_gt0 //.
    rewrite logn_prime // eqxx leqNgt leq_eqVlt ltnNge le_k2 orbF eq_sym /=.
    apply/eqP=> k2; case/cyclicP: cycK; exists K'x; apply/eqP.
    by rewrite eq_sym eqEcard cycle_subG KK'x oK -k2 -ox leqnn.
  have ntK: K / K' != 1.
    by rewrite trivg_card1 oK k2 (eqn_sqr _ 1) neq_ltn orbC prime_gt1.
  pose rPR := abelem_repr abelK ntK nKqPR.
  have: mx_faithful rPR by rewrite abelem_mx_faithful.
  move: rPR; rewrite (dim_abelemE abelK ntK) oK pfactorK // k2 => rPR ffPR.
  apply: charf'_GL2_abelian ffPR _.
    by rewrite quotient_odd ?(oddSg _ oddG) // mulgen_subG (subset_trans sPH).
  rewrite quotient_pgroup //; apply: sub_in_pnat coK_PR => q' _.
  apply: contra; rewrite /= (GRing.charf_eq (char_Fp q_pr)); move/eqnP->.
  by rewrite mem_primes q_pr cardG_gt0.
case abelK: (abelian K); last first.
  have [||[dPhiK sK'] dCKP] := abelian_charsimple_special qK _ (esym defKP) _.
  - by rewrite coprime_sym (pnat_coprime pP).
  - apply/bigcupsP=> L; case/andP=> chL.
    case/IHK: (char_sub chL) abelK => // [|-> -> //].
    by rewrite (char_norm_trans chL).
  have xKq: exponent K %| q.
    have oddq: odd q.
      move: oddG; rewrite !odd_2'nat; apply: pnat_dvd.
      by apply: dvdn_trans qKdv (cardSg _); exact: subset_trans sHG.
    have ntK: K :!=: 1 by apply/eqP=> K1; rewrite K1 comm1G eqxx in ntKP.
    have{oddq ntK} [Q [chQ _ _ xQq qCKQ]] := critical_odd oddq qK ntK.
    have: P <*> R \subset 'N(Q) by exact: char_norm_trans nKPR.
    have sQK := char_sub chQ.
    case/IHK=> // [<- | cQP]; first by rewrite xQq.
    case/eqP: ntKP; apply/commG1P.
    rewrite centsC -ker_conj_aut -sub_morphim_pre // -[_ @* _]setIid.
    apply/trivgP; apply: coprime_TIg.
    apply: pnat_coprime (morphim_pgroup _ pP) _.
    apply: (@sub_in_pnat q) => [q' _|]; first by move/eqnP->.
    apply: pgroupS qCKQ; apply/subsetP=> a; case/morphimP=> x _ Px ->{a}.
    rewrite /= astab_ract inE /= Aut_aut; apply/astabP=> y Qy.
    rewrite /= /aperm norm_conj_autE ?(subsetP sQK) ?(subsetP nKP) //.
    by rewrite /conjg (centsP cQP y) ?mulKg.
  have nZK := normal_norm (center_normal K).
  have trCPR_K': 'C_(P <*> R / 'Z(K))(K / 'Z(K)) = 1.
    rewrite -quotient_astabQ -quotientIG /=; last first.
      by rewrite sub_astabQ normG trivg_quotient sub1G.
    apply/trivgP; rewrite -quotient1 quotientS // -trCPR_K subsetI subsetIl /=.
    rewrite (coprime_cent_Phi qK) ?(coprimegS (subsetIl _ _)) //=.
      rewrite norm_mulgenEr // coprime_cardMg ?(coprimeSg sPH) //.
      by rewrite coprime_mulr coprime_sym (pnat_coprime pP) ?(coprimeSg sKH).
    rewrite dPhiK (subset_trans (commgS _ (subsetIr _ _))) //.
    by rewrite astabQ -quotient_cents2 ?subsetIl // cosetpreK centsC /=.
  have nZP := char_norm_trans (center_char _) nKP.
  have nZR := char_norm_trans (center_char _) nKR.
  have solK: solvable K := nilpotent_sol (pgroup_nil qK).
  have dCKR': 'C_K(R) / 'Z(K) = 'C_(K / 'Z(K))(R / 'Z(K)).
    by rewrite coprime_quotient_cent ?center_sub ?(coprimeSg sKH).
  have abK': q.-abelem (K / 'Z(K)).
    by rewrite -dPhiK -trivg_Phi ?morphim_pgroup // Phi_quotient_id.
  case: (eqVneq 'C_(K / 'Z(K))(R / 'Z(K)) 1) => [trCK'_R | ntCK'_R].
    have qZ: q.-group 'Z(K) by exact: pgroupS (center_sub K) qK.
    have q'P: q^'.-group P.
      by apply: sub_in_pnat pP => p' _; move/eqnP->; rewrite eq_sym in nqp.
    have coZP: coprime #|'Z(K)| #|P| := pnat_coprime qZ q'P.
    suff sPZ: P \subset 'Z(K).
       by case/negP: ntKP; rewrite -(setIidPr sPZ) coprime_TIg ?commG1.
    rewrite -quotient_sub1 // defP commGC quotientE morphimR // -?quotientE.
    have <-: 'C_(P /'Z(K))(K / 'Z(K)) = 1.
      by apply/trivgP; rewrite -trCPR_K' setSI ?morphimS ?mulgen_subl.
    move: trCK'_R; have: ~~ (q %| #|P <*> R / 'Z(K)|).
      rewrite -p'natE //; apply: morphim_pgroup.
      by rewrite /= norm_mulgenEr // pgroupM q'P /pgroup oR pnatE.
    have sPRG: P <*> R \subset G by rewrite mulgen_subG sRG (subset_trans sPH).
    have coPR: coprime #|P| #|R| by rewrite (pnat_coprime pP) // oR pnatE.
    apply: three_dot_four abK' _.
    - exact: quotient_sol (solvableS _ solG).
    - rewrite !odd_2'nat in oddG *; apply: morphim_pgroup; exact: pgroupS oddG.
    - by rewrite morphim_normal // /normal mulgen_subl mulgen_subG normG.
    - rewrite morphim_Hall // /Hall -divgS ?mulgen_subl //= norm_mulgenEr //.
      by rewrite coprime_cardMg // mulKn.
    - apply/complP; rewrite -morphimMl //= norm_mulgenEr // ?coprime_TIg //.
      apply: pnat_coprime (morphim_pgroup _ pP) (morphim_pgroup _ _).
      by rewrite /pgroup oR pnatE.
    - rewrite card_morphim ker_coset (setIidPr _) // -indexgI.
      rewrite coprime_TIg ?indexg1 ?oR //.
      rewrite -oR (pnat_coprime rR) //; exact: (pgroupS (subsetIl _ _)).
    by apply: morphim_norms; rewrite mulgen_subG nKP.
  have sKR_C_K': 'C_K(R) :&: [~: K, R] \subset 'Z(K).
    rewrite -quotient_sub1; last by rewrite -setIA subIset ?nZK.
    apply: subset_trans (morphimI _ _ _) _.
    rewrite morphimR; first 1 [rewrite -!quotientE dCKR'] || by [].
    rewrite setIC setICA coprime_abel_cent_TI ?subsetIr ?morphim_norms //.
      by rewrite coprime_morphl // coprime_morphr // (coprimeSg sKH).
    by rewrite sub_der1_abelian //= -sK'.
  have sKR_K: [~: K, R] \proper K.
    rewrite properE {1}commGC commg_subr nKR /=.
    apply/negP=> sK_KR; case/eqP: ntCK'_R; apply/trivgP.
    rewrite /= -dCKR' quotient_sub1; last by rewrite subIset // nZK.
    by rewrite -{1}(setIidPl sK_KR) setIAC.
  rewrite -subG1 /= -dCKR' quotient_sub1 // in ntCK'_R *; last first.
    by rewrite subIset // normal_norm // center_normal.
  have oCKR: #|'C_K(R)| = q.
    have: cyclic 'C_K(R).
      apply: nil_Zgroup_cyclic; first exact: ZgroupS (setSI _ _) ZCHR.
      apply: pgroup_nil (pgroupS _ qK); exact: subsetIl.
    case/cyclicP=> x CKRx.
    have Kx: x \in K by rewrite -cycle_subG -CKRx subsetIl.
    have{Kx}:= dvdn_trans (dvdn_exponent Kx) xKq; rewrite /order CKRx.
    case: (primeP q_pr) => _ dvq; move/dvq; case/orP; move/eqnP=> // x1.
    by rewrite CKRx ((<[x]> =P 1) _) ?sub1G // trivg_card1 x1 in ntCK'_R.
  have trCKR_Z: 'C_K(R) :&: 'Z(K) = 1.
    apply: card1_trivg.
    have:= cardSg (subsetIl 'C_K(R) 'Z(K)); rewrite oCKR.
    case: (primeP q_pr) => _ dvq; move/dvq; case/predU1P=> [-> //| Iq].
    case/setIidPl: ntCK'_R; apply/eqP; rewrite eqEcard subsetIl.
    by rewrite oCKR (eqnP Iq) leqnn.
  have trKR_CR: 'C_[~: K, R](R) = 1.
    rewrite -(setIidPl (proper_sub sKR_K)) -setIA setIC.
    rewrite -(setIidPl sKR_C_K') -setIA setICA trCKR_Z.
    apply/setIidPr; exact: sub1G.
  have abKR: abelian [~: K, R].
    apply/commG1P; apply/trivgP.
    have <-: 'C_[~: K, R](V) = 1.
      have sKRH: [~: K, R] \subset H := subset_trans (proper_sub sKR_K) sKH.
      apply/trivgP; rewrite /= -(setIidPl sKRH) -setIA -eqVC setIC -trVN.
      by rewrite setIS // subsetI sKRH (subset_trans _ (normG K)) ?proper_sub.
    have nKR_R: R \subset 'N([~: K, R]) by rewrite commGC commg_norml.
    have coKR_R: coprime #|R| #|[~: K, R]|.
      exact: pnat_coprime rR (pgroupS (proper_sub sKR_K) r'K).
    have sKRR_G: [~: K, R] <*> R \subset G.
      by rewrite mulgen_subG comm_subG // (subset_trans sKH).
    move: oCVR; have: ~~ (p %| #|[~: K, R] <*> R|).
      rewrite -p'natE // norm_mulgenEr // [_ #|_|]pgroupM.
      by rewrite (pgroupS (proper_sub sKR_K) p'K) /pgroup oR pnatE.
    apply: three_dot_five; rewrite ?oR //.
    - exact: solvableS solG.
    - by rewrite /normal mulgen_subl mulgen_subG normG nKR_R.
    - by apply/complP; rewrite setIC coprime_TIg //= norm_mulgenEr.
    exact: subset_trans nVG.
  case nKR_P: (P \subset 'N([~: K, R])).
    have{nKR_P}: P <*> R \subset 'N([~: K, R]).
      by rewrite mulgen_subG nKR_P commGC commg_norml.
    case/IHK=> [|dKR|cP_KR]; first exact: proper_sub.
      by case/eqP: (proper_neq sKR_K).
    have{cP_KR} cK'_R: R / 'Z(K) \subset 'C(K / 'Z(K)).
      by rewrite quotient_cents2r //= -dCKP commGC subsetI proper_sub.
    case/eqP: ntKR; apply/commG1P; rewrite centsC.
    rewrite (coprime_cent_Phi qK) ?(coprimeSg sKH) // dPhiK.
    by rewrite commGC -quotient_cents2.
  case/subsetPn: nKR_P => x Px; move/normP; move/eqP=> nKRx.
  have iKR: #|K : [~: K, R]| = q.
    rewrite -divgS ?proper_sub // -{1}(coprime_cent_prod nKR) //; last first.
      by rewrite coprime_sym (pnat_coprime rR).
    rewrite TI_cardMg ?mulKn // setICA trKR_CR; apply/setIidPr; exact: sub1G.
  pose IKRx := ([~: K, R] :&: [~: K, R] :^ x)%G.
  have sKRx_K: [~: K, R] :^ x \subset K.
    by rewrite -{2}(normsP nKP x Px) conjSg proper_sub.
  have nKR_K: K \subset 'N([~: K, R]) by exact: commg_norml.
  have iIKRx: #|[~: K, R] : IKRx| = q.
    have: #|[~: K, R] : IKRx| %| q.
      rewrite -divgS ?subsetIl // -{1}(cardJg _ x) /= setIC divgI -iKR.
      rewrite -!card_quotient ?(subset_trans sKRx_K) //.
      apply: cardSg; exact: morphimS.
    case/primeP: q_pr => _ dv_q; move/dv_q; case/orP; move/eqnP=> // iIKR_1.
    case/negP: nKRx; rewrite eq_sym eqEcard cardJg leqnn andbT.
    rewrite (sameP setIidPl eqP) eqEcard subsetIl /=.
    by rewrite -(LaGrange (subsetIl _ ([~: K, R] :^ x))) iIKR_1 muln1 /=.
  have dKx: K :=: [~: K, R] * [~: K, R] :^ x.
    apply/eqP; rewrite eq_sym eqEcard mul_subG // ?proper_sub //.
    rewrite -(leq_pmul2r (cardG_gt0 IKRx)) -mul_cardG cardJg.
    rewrite -(LaGrange (proper_sub sKR_K)) iKR -mulnA leq_pmul2l //.
    by rewrite -iIKRx mulnC LaGrange /= ?subsetIl.
  have sIKRxZ: IKRx \subset 'Z(K).
    rewrite subsetI subIset; last by rewrite sKRx_K orbT.
    rewrite /abelian in abKR.
    by rewrite dKx centM centJ subsetI !subIset // ?conjSg ?abKR ?orbT.
  suffices: #|K / 'Z(K)| <= q ^ 2.
    by rewrite leqNgt -sK' iK'K // [K' : {set _}]sK'.
  rewrite card_quotient ?normal_norm ?center_normal //.
  rewrite -mulnn -{1}iKR -iIKRx LaGrange_index ?subsetIl ?proper_sub //.
  by rewrite dvdn_leq // indexgS.
have trCK_P: 'C_K(P) = 1.
  by rewrite defKP coprime_abel_cent_TI // coprime_sym (pnat_coprime pP).
have abelemK: q.-abelem K.
  apply/abelem_Ohm1P => //.
  case/IHK: (Ohm_sub 1 K) => // [|cPK1].
    by apply: char_norm_trans (Ohm_char 1 K) _; rewrite mulgen_subG nKP.
  case/Cauchy: qKdv => // x Kx oxq.
  have: x \in 'C_K(P).
    rewrite inE Kx (subsetP cPK1) //= (OhmE 1 qK) ?mem_gen // inE Kx.
    by rewrite /= -oxq expn1 expg_order.
  by rewrite trCK_P; move/set1P=> x1; rewrite -oxq x1 order1 in q_pr.
have{iK'K} oKq2: q ^ 2 < #|K|.
  have K'1: K' :=: 1 by exact/commG1P.
  rewrite -indexg1 -K'1 -card_quotient ?normal_norm // iK'K // K'1.
  by rewrite -injm_subcent ?coset1_injm ?norms1 //= trCPR_K morphim1.
pose Vi (Ki : {group gT}) := 'C_V(Ki)%G.
pose mxK := [set Ki : {group gT} | maximal Ki K && (Vi Ki :!=: 1)].
have nKiK: forall Ki, Ki \in mxK -> Ki <| K.
  by move=> Ki; rewrite inE; case/andP=> maxK _; exact: (p_maximal_normal qK).
have nViK: forall Ki, Ki \in mxK -> K \subset 'N(Vi Ki).
  by move=> Ki mxKi; rewrite normsI // norms_cent // normal_norm // nKiK.
have gen_mxK: << \bigcup_(Ki \in mxK) Vi Ki >> = V.
  apply/eqP; rewrite eqEsubset gen_subG; apply/andP; split.
    apply/bigcupsP=> Ki _; exact: subsetIl.
  rewrite (coprime_abelian_gen_cent abelK nVK) ?(pnat_coprime pV) //.
  rewrite bigprodGE gen_subG; apply/bigcupsP=> Kj; case/and3P=> cycKj sKjK nKjK.
  case: (eqsVneq (Vi Kj) 1) => [/= -> | ntVKj]; first by rewrite sub1G.
  rewrite sub_gen // (bigD1 Kj) ?subsetUl //= inE p_index_maximal //.
  have abelKj: q.-abelem (K / Kj).
    apply/abelemP; rewrite ?quotient_abelian //; split=> // Kjx.
    case/morphimP=> x NKjx Kx ->; rewrite -morphX //.
    by case/abelemP: abelemK => // _; move/(_ x Kx)->; rewrite morph1.
  rewrite -card_quotient //; case/cyclicP: cycKj => Kjx /= defKj.
  case: (eqVneq Kjx 1) => [Kjx1 | ntKjx].
    case/eqP: ntVKj; rewrite /= (index1g sKjK) // -card_quotient // defKj.
    by rewrite Kjx1 [#|_|]order1.
  rewrite defKj -/#[_]; case: (abelem_order_p abelKj _ ntKjx) => [|_ -> //].
  by rewrite /= defKj cycle_id.
have dprod_V : \big[dprod/1]_(Ki \in mxK) Vi Ki = V.
  pose dp (sM : {set _}) := \big[dprod/1]_(Ki \in sM) Vi Ki.
  have dp0: dp set0 = 1 by rewrite /dp big_pred0 => // Ki; rewrite inE.
  pose sM0 : {set {group gT}} := set0.
  have: exists sM, group_set (dp sM) && (sM \subset mxK).
    by exists sM0; rewrite sub0set dp0 groupP.
  case/ex_maxset=> sM; case/maxsetP; case/andP=> gW ssM max_sM.
  move defW: (Group gW) => W; move/(congr1 val): defW => /= defW.
  move: ssM; rewrite subEproper /= -{2}gen_mxK.
  case/predU1P=> [<-|]; first by rewrite (bigdprodEgen defW).
  case/andP=> ssM; case/subsetPn=> Kj mxKj nsKj; case/negP: (nsKj).
  suffices trWVj: 'C_W(Kj) = 1.
    rewrite -(max_sM _ _ (subsetUr [set Kj] _)); first by rewrite inE set11.
    rewrite subUset sub1set mxKj ssM /= andbT.
    rewrite /dp (bigD1 Kj) ?setU11 //=.
    suff: group_set (Vi Kj \x dp sM).
      apply: etrans; congr (group_set (_ \x _)); apply: eq_bigl => M1.
      by rewrite !inE andbC; case: eqP => // ->; rewrite (negPf nsKj).
    have cWM: Vi Kj \subset 'C(W).
      rewrite subIset // centsC; apply/orP; left.
      case/and3P: abV => _ abV _; apply: subset_trans abV.
      move/bigdprodEgen: defW => <-; rewrite gen_subG.
      apply/bigcupsP=> M1 _; exact: subsetIl.
    rewrite defW dprodE //; first by rewrite -cent_mulgenEl ?groupP.
    by apply/trivgP; rewrite -trWVj /= setIC setICA subsetIr.
  have: exists mM, ('C_(dp mM)(Kj) == 1) && (mM \subset sM).
    by exists sM0; rewrite sub0set dp0 -subG1 subsetIl.
  case/ex_maxset=> mM; case/maxsetP; case/andP; move/eqP=> trVm.
  rewrite subEproper -defW; case/predU1P=> [<- //|]; case/andP=> smM.
  case/subsetPn=> Ki sKi nmKi max_mM.
  case/negP: (nmKi); rewrite -sub1set; apply/setUidPr.
  apply: max_mM (subsetUr _ _); rewrite subUset sub1set sKi smM !andbT.
  have:= defW; rewrite {1}/dp (bigID [pred Kk \in Ki |: mM]) /=.
  case/dprodP=> [[W' _ defW' _] _ _ _].
  rewrite (_ : bigop _ _ _ _ _ = dp (Ki |: mM)) in defW'; last first.
    apply: eq_bigl => Kk; rewrite -in_setI (setIidPr _) //.
    by rewrite subUset sub1set sKi smM.
  rewrite defW'; move: defW'; rewrite /dp (bigD1 Ki) ?setU11 //=.
  rewrite (_ : bigop _ _ _ _ _ = dp mM); last first.
    apply: eq_bigl => Kk; rewrite !inE andbC; case: eqP => // ->.
    by rewrite (negPf nmKi).
  case/dprodP=> [[_ W2 _ defW2] <-]; rewrite defW2 => cViW2 trViW2.
  rewrite -cent_mulgenEl // -subG1 /= cent_mulgenEl //.
  apply/subsetP=> uv; case/setIP; case/imset2P=> u v Viu W2v ->{uv} Vjuv.
  have mxKi := subsetP ssM _ sKi.
  case/setIdP: mxKj; case/maxgroupP; case/andP=> sKj _ mxKj _.
  have v1: v = 1.
    apply/set1gP; rewrite -trVm inE defW2 W2v /=.
    apply/centP=> x Kjx; apply/commgP; rewrite (sameP eqP set1gP).
    have Kx: x \in K by apply: subsetP Kjx.
    rewrite -trViW2; apply/setIP; split.
      have cuv: commute u v by exact: (centsP cViW2).
      rewrite commgEl -{2}(mulgK u v) -cuv conjMg {1}/conjg.
      rewrite (centP Vjuv x Kjx) mulKg cuv mulgA mulKg groupMl //.
      by rewrite conjVg groupV memJ_norm //; apply: subsetP Kx; rewrite nViK.
    rewrite groupMl ?groupV // memJ_norm // -(bigdprodEgen defW2).
    apply: subsetP Kx; apply big_prop=> [|y z Ny Nz|Kk].
    - by rewrite gen0 norms1.
    - by rewrite -mulgenE -mulgen_idl -mulgen_idr norms_mulgen.
    move/(subsetP (subset_trans smM ssM))=> mxKk.
    by rewrite norms_gen // nViK.
  rewrite -trCVK v1 !mulg1 in Vjuv *.
  have: Ki <*> Kj \subset K by rewrite mulgen_subG sKj normal_sub // nKiK.
  rewrite subEproper; case/predU1P=> [<-|sKij].
    by rewrite cent_mulgen setIA inE Viu.
  have defKj: Ki <*> Kj = Kj by apply: mxKj; rewrite ?mulgen_subr.
  suffices defKi: Kj = Ki by rewrite defKi sKi in nsKj.
  apply: val_inj; move: mxKi; rewrite inE /= -defKj.
  by case/andP; case/maxgroupP=> _ mxKi _; apply: mxKi; rewrite ?mulgen_subl.
have ViJ: forall x Ki, x \in P <*> R -> (Vi Ki :^ x = Vi (Ki :^ x))%G.
  move=> x Ki PRx; apply: group_inj; rewrite /= conjIg centJ (normP _) //.
  by apply: subsetP PRx; rewrite mulgen_subG nVP (subset_trans sRG).
have actsPR_K: [acts P <*> R, on mxK | 'JG].
  apply/subsetP=> x PRx; rewrite 3!inE; apply/subsetP=> Ki.
  rewrite !inE -ViJ // !trivg_card1 cardJg /=.
  case/andP; case/maxgroupP=> sKj mxKj ->.
  rewrite -(normsP nKPR x PRx) andbT.
  apply/maxgroupP; rewrite /proper !conjSg; split=> // Q.
  rewrite !sub_conjg /= -sub_conjgV=> sQ.
  by move/mxKj <-; rewrite // conjsgKV.
have actsPR: [acts P <*> R, on Vi @: mxK | 'JG].
  apply/subsetP=> x PRx; rewrite 3!inE; apply/subsetP=> Vj.
  case/imsetP=> Kj mxKj ->{Vj}.
  by rewrite inE /= ViJ // mem_imset // (actsP actsPR_K).
have transPR: [transitive P <*> R, on Vi @: mxK | 'JG].
  have [K1 mxK1]: exists K1, K1 \in mxK.
    have:= sub0set mxK; rewrite subEproper; case/predU1P=> [mx0|]; last first.
      by case/andP=> _; case/subsetPn=> K1; exists K1.
    have:= pr_p; rewrite -oCVR -dprod_V -mx0 big1 => [|Ki]; rewrite ?inE //.
    by rewrite (setIidPl (sub1G _)) cards1.
  have mxV1: Vi K1 \in Vi @: mxK by rewrite mem_imset.
  apply/imsetP; exists (Vi K1) => //.
  set S := orbit _ _ _; rewrite (bigID [preim Vi of S]) /= in dprod_V.
  case/dprodP: dprod_V (dprod_V) => [[N1 N2 defN1 defN2]].
  pose dp PK := \big[dprod/1]_(Ki \in mxK | PK Ki) Vi Ki.
  rewrite defN1 defN2 => _ cN12 trN12; case/nondecV=> [||N1V].
  - apply/subsetP=> x Gx; rewrite !inE.
    move: Gx; rewrite -eqHR_G defH -mulgA; case/imset2P=> x1 x2 VHx1.
    rewrite -norm_mulgenEr // => PRx2 ->{x}.
    pose idPR (PK : pred {group gT}) :=
      forall y Ki, y \in P <*> R -> PK (Ki :^ y)%G = PK Ki.
    have idS: idPR [preim Vi of S].
      move=> y Ki PRy; rewrite /= -ViJ //; apply: orbit_transr.
      by apply/imsetP; exists y.
    have nN2: forall PK (N : {group _}),
      idPR PK -> dp PK = N -> N :^ (x1 * x2) = N.
    - move=> PK N idPK defN; rewrite -{1}(bigdprodE defN).
      rewrite /dp (reindex (fun Ki => (Ki :^ x2)%G)) in defN; last first.
        exists (fun Ki => (Ki :^ x2^-1)%G) => Ki _; apply: group_inj.
          exact: conjsgK.
        exact: conjsgKV.
      rewrite -(bigdprodE defN) {N defN} /= big_mkcond /=.
      symmetry; rewrite big_mkcond /=; symmetry.
      pose RK := [fun U W => U :^ (x1 * x2) = W].
      apply (big_rel RK) => /= [|U1 _ U2 _ <- <-|Ki _].
      - by rewrite conjs1g.
      - by rewrite conjsMg.
      rewrite idPK // (actsP actsPR_K) //.
      case mxKi: {+}(_ && _); last by rewrite conjs1g.
      rewrite conjsgM (normsP _ x1 VHx1).
        by have:= congr1 val (ViJ _ Ki PRx2) => /= ->.
      case/andP: mxKi => mxKi _; rewrite mul_subG ?nViK //.
      rewrite cents_norm // centsC subIset //; apply/orP; left.
      by case/and3P: abV.
    rewrite (nN2 _ _ _ defN1) // (nN2 _ _ _ defN2) ?subxx // => y Ki PRy.
    by congr (~~ _); exact: idS.
  - move/trivgP; rewrite -(bigdprodEgen defN1) gen_subG.
    move/bigcupsP; move/(_ K1); rewrite mxK1 orbit_refl => trV1.
    by case/setIdP: mxK1 => _; rewrite -subG1 trV1.
  have: S \subset Vi @: mxK by rewrite acts_sub_orbit.
  rewrite subEproper; case/predU1P=> //; case/andP=> _; case/subsetPn=> V2.
  case/imsetP=> K2 mxK2 -> SV2; move/trivgP: trN12.
  rewrite /= N1V -(bigdprodEgen defN2) (setIidPr _) gen_subG.
    move/bigcupsP; move/(_ K2); rewrite mxK2 SV2 => trV2.
    by case/setIdP: mxK2 => _; rewrite -subG1 trV2.
  apply/bigcupsP=> Kj _; exact: subsetIl.
case sR_IN: (forallb K1, (K1 \in mxK) ==> (R \subset 'N(Vi K1))).
  have{sR_IN} sR_IN: R \subset \bigcap_(Ki \in mxK) 'N(Vi Ki).
    by apply/bigcapsP=> Ki mxKi; have:= forallP sR_IN Ki; rewrite mxKi.
  have nIPR: P <*> R \subset 'N(\bigcap_(Ki \in mxK) 'N(Vi Ki)).
    apply/subsetP=> x PRx; rewrite inE.
    apply/subsetP=> yx; case/imsetP=> y Iy -> {yx}.
    apply/bigcapP=> Ki.
    have ->: Ki = ((Ki :^ x^-1) :^ x)%G.
      by apply: group_inj; rewrite /= conjsgKV.
    rewrite -ViJ // (actsP actsPR_K) // normJ memJ_conjg; exact: (bigcapP Iy).
  case/imsetP: transPR => V1; case/imsetP=> K1 mxK1 ->.
  have: P <*> R \subset 'N(Vi K1).
    rewrite mulgen_subG (subset_trans sR_IN) /= ?bigcap_inf // andbT.
    rewrite defP; apply: (subset_trans (commgS P sR_IN)).
    have:= subset_trans (mulgen_subl P R) nIPR.
    rewrite -commg_subr; move/subset_trans; apply; exact: bigcap_inf.
  rewrite -afixJG; move/orbit1P=> -> allV1.
  have defV1: V = Vi K1.
    apply/eqP; rewrite -val_eqE eqEsubset subsetIl /= andbT.
    rewrite -{1}(bigdprodEgen dprod_V) gen_subG; apply/bigcupsP=> Ki mxKi.
    have: Vi Ki \in [set Vi K1] by rewrite -allV1 mem_imset.
    by move/set1P=> -> /=.
  move: mxK1 oKq2; rewrite inE; case/andP=> maxK1.
  have [sK1 _] := andP (p_maximal_normal qK maxK1).
  have:= p_maximal_index qK maxK1.
  have ->: K1 :=: 1.
    apply/trivgP; rewrite -trCKR_V subsetI defV1 centsC subsetIr andbT.
    exact: subset_trans (mulgen_subl K R).
  rewrite indexg1 => -> _.
  by rewrite -{2}(expn1 q) ltn_exp2l // prime_gt1.
case/existsP: sR_IN => K1; rewrite negb_imply; case/andP=> mxK1 nK1R.
have regR_Vi: forall Ki, Ki \in mxK ->
  ~~ (R \subset 'N(Vi Ki)) -> 'N_R(Vi Ki) = 1.
- move=> Ki mxKi fixVi; apply: card1_trivg.
  have: #|'N_R(Vi Ki)| %| r by rewrite -oR cardSg // subsetIl.
  case: (primeP pr_r) => _ dvr; move/dvr {dvr}; case/pred2P=> [//|oN].
  by case/setIidPl: fixVi; apply/eqP; rewrite eqEcard subsetIl oN oR leqnn.
have oV1R: #|orbit 'JG%act R (Vi K1)| = r.
  by rewrite card_orbit astab1JG /= regR_Vi // indexg1 oR.
have nRfix_CR: forall Ki, Ki \in mxK -> ~~ (R \subset 'N(Vi Ki)) ->
           #|Vi Ki| = p /\ 'C_V(R) \subset << class_support (Vi Ki) R >>.
- move=> Ki mxKi fixVi.
  have [//||x Rx ox] := @Cauchy _ r R; first by rewrite oR.
  have xR: <[x]> = R.
    by apply/eqP; rewrite eqEcard oR -ox cycle_subG Rx leqnn.
  have nVx: forall i y, y \in V -> y ^ x ^+ i \in V.
    move=> i y Vy; rewrite memJ_norm  ?groupX //; apply: subsetP Rx.
    exact: subset_trans nVG.
  pose f m y := \prod_(0 <= i < m) y ^ x ^+ i.
  have Vf: forall m y, y \in V -> f m y \in V.
    rewrite /f => m y Vy.
    apply big_prop => [||i _]; [exact: group1 | exact: groupM | exact: nVx].
  case/and3P: abV=> _; move/centsP=> abV _.
  have fM: {in Vi Ki &, {morph f r: y z / y * z}}.
    rewrite /f => y z; case/setIP=> Vy _; case/setIP=> Vz _ /=.
    elim: (r) => [|m IHm]; first by rewrite !big_geq ?mulg1.
    rewrite !big_nat_recr /= conjMg 2!mulgA; congr (_ * _).
    by rewrite {}IHm -2!mulgA; congr (_ * _); rewrite abV ?Vf ?nVx.
  have injf: 'injm (Morphism fM).
    apply/subsetP=> y; case/morphpreP=> Vi_y; move/set1P=> /= fy1.
    have:= dprod_V; rewrite (bigD1 Ki) //=.
    case/dprodP=> [[_ W _ defW] _ _ <-]; rewrite defW inE Vi_y /=.
    rewrite -groupV -(mulg1 y^-1) -fy1 /f big_ltn ?prime_gt0 // conjg1 mulKg.
    rewrite big_cond_seq /=.
    apply big_prop=> [||i]; first 1 [exact: group1 | exact: groupM].
    rewrite mem_index_iota; case/andP=> i_gt0 ltir.
    rewrite -(bigdprodEgen defW) mem_gen //; apply/bigcupP.
    have Rxi: x ^+ i \in R by exact: groupX.
    have PRxi: x ^+ i \in P <*> R by apply: subsetP Rxi; exact: mulgen_subr.
    have:= congr_group (ViJ _ Ki PRxi) => /= Vi_xi.
    exists (Ki :^ (x ^+ i))%G; last by rewrite -Vi_xi memJ_conjg.
    rewrite (actsP actsPR_K) // mxKi -val_eqE (sameP eqP normP).
    apply/normP=> nVi_xi; have: x ^+ i \in 'N_R(Vi Ki).
      by rewrite inE Rxi; apply/normP; rewrite /= Vi_xi nVi_xi.
    by rewrite regR_Vi // inE -order_dvdn ox /dvdn modn_small ?eqn0Ngt ?i_gt0.
  have im_f: Morphism fM @* Vi Ki \subset 'C_V(R).
    rewrite morphimEdom /=.
    apply/subsetP=> fy; case/imsetP=> y; case/setIP=> Vy _ -> {fy}.
    rewrite inE Vf //= -sub1set centsC -xR cycle_subG /= cent_set1 inE.
    rewrite conjg_set1 sub1set; apply/set1P.
    have r1: r.-1.+1 = r by apply: prednK; exact: prime_gt0.
    rewrite /f -r1 {1}big_nat_recr big_nat_recl /= conjMg -conjgM -expgSr.
    rewrite r1 -{2}ox expg_order conjg1 abV //; last first.
      by rewrite memJ_norm ?(subsetP (subset_trans sRG nVG)) ?Vf.
    congr (_ * _); pose Rbig := [fun z u => z ^ x = u].
    apply: (big_rel Rbig) => /= [|z1 _ z2 _ <- <-|i _]; first exact: conj1g.
    - exact: conjMg.
    by rewrite -conjgM -expgSr.
  have: isom (Vi Ki) (Morphism fM @* Vi Ki) (Morphism fM) by exact/isomP.
  move/isom_card=> oVi.
  have{im_f} im_f: Morphism fM @* Vi Ki = 'C_V(R).
    apply/eqP; rewrite eqEcard im_f oCVR -oVi.
    case: (eqsVneq (Vi Ki) 1) => [Vi1 | ntVKi].
      by rewrite inE Vi1 eqxx andbF in mxKi.
    have: p.-group (Vi Ki) by apply: pgroupS pV; exact: subsetIl.
    by case/pgroup_pdiv=> // _ pVKi _; rewrite dvdn_leq.
  rewrite oVi -oCVR -im_f; split=> //.
  rewrite morphimEdom /= /f; apply/subsetP=> fy; case/imsetP=> y Vi_y ->{fy}.
  apply big_prop => [||i _]; first 1 [exact: group1 | exact: groupM].
  rewrite mem_gen // class_supportEr.
  by apply/bigcupP; exists (x ^+ i); rewrite (groupX, memJ_conjg).
have oVi: forall Ki, Ki \in mxK -> #|Vi Ki| = p.
  move=> Ki mxKi.
  have [||z _ ->]:= (atransP2 transPR) (Vi K1) (Vi Ki); try exact: mem_imset.
  by rewrite cardJg; case/nRfix_CR: nK1R.
have: orbit 'JG%act R (Vi K1) \subset Vi @: mxK.
  rewrite acts_sub_orbit ?mem_imset //.
  apply: subset_trans actsPR; exact: mulgen_subr.
have nVjR: forall Kj, Kj \in mxK ->
  Vi Kj \notin orbit 'JG%act R (Vi K1) -> Kj = [~: K, R]%G.
- move=> Kj mxKj V1Rj; case/orP: (orbN (R \subset 'N(Vi Kj))) => [nVjR|].
    have defKj: 'C_K(Vi Kj) = Kj.
      move: mxKj; rewrite inE; case/andP; case/maxgroupP.
      case/andP=> sKjK _ mxKj ntVj; apply: mxKj; last first.
        by rewrite subsetI sKjK centsC subsetIr.
      rewrite properE subsetIl; apply: contra ntVj => cVjK.
      rewrite -subG1 -trCVK subsetI subsetIl centsC.
      apply: (subset_trans cVjK); exact: subsetIr.
    have{nVjR} sKRVj: [~: K, R] \subset Kj.
      rewrite -defKj subsetI {1}commGC commg_subr nKR -ker_conj_aut.
      rewrite -sub_morphim_pre ?comm_subG ?morphimR ?nViK // andTb.
      rewrite (commG1P _) //; apply/centsP.
      have: cyclic (Vi Kj) by rewrite prime_cyclic // oVi.
      case/cyclicP=> v; move/group_inj=> -> a.
      case/imsetP=> y _ -> b; case/imsetP=> z _ ->{a b}.
      apply: (centsP (Aut_cycle_abelian v)); exact: Aut_aut.
    apply/eqP; rewrite -val_eqE eq_sym eqEcard sKRVj.
    rewrite -(leq_pmul2r (prime_gt0 q_pr)).
    have iKj: #|K : Kj| = q.
      by move: mxKj; rewrite inE; case/andP=> maxKj _; exact: p_maximal_index.
    rewrite -{1}iKj LaGrange ?normal_sub ?nKiK //.
    have: [~: K, R] \x 'C_K(R) = K.
      by rewrite coprime_abelian_cent_dprod ?(coprimeSg sKH).
    case/dprodP=> _ defKR _ trKR_C.
    rewrite -{1}defKR (TI_cardMg trKR_C) leq_pmul2l ?cardG_gt0 //=.
    have Z_CK: Zgroup 'C_K(R) by apply: ZgroupS ZCHR; exact: setSI.
    have:= forallP Z_CK 'C_K(R)%G; rewrite (@p_Sylow _ q) /=; last first.
      rewrite pHallE subxx part_pnat_id ?eqxx //.
      apply: pgroupS qK; exact: subsetIl.
    case/cyclicP=> z defC; rewrite defC dvdn_leq ?prime_gt0 // order_dvdn.
    case/abelemP: abelemK => // _ -> //.
    by rewrite -cycle_subG -defC subsetIl.
  case/nRfix_CR=> // _ sCVj; case/nRfix_CR: nK1R => // _ sCV1.
  suff trCVR: 'C_V(R) = 1 by rewrite -oCVR trCVR cards1 in pr_p.
  pose inK1R Ki := Vi Ki \in orbit 'JG%act R (Vi K1).
  apply/trivgP; have:= dprod_V; rewrite (bigID inK1R).
  case/dprodP=> [[W1 Wj defW1 defWj] _ _ <-].
  rewrite defW1 defWj subsetI (subset_trans sCV1) /=; last first.
    rewrite class_supportEr -(bigdprodEgen defW1) genS //.
    apply/bigcupsP=> x Rx; apply/subsetP=> u V1xu.
    have PRx: x \in P <*> R by apply: subsetP Rx; exact: mulgen_subr.
    apply/bigcupP; exists (K1 :^ x)%G; last by rewrite -ViJ.
    by rewrite (actsP actsPR_K) // mxK1 /inK1R -ViJ // mem_imset.
  apply: (subset_trans sCVj); rewrite class_supportEr -(bigdprodEgen defWj).
  apply: genS; apply/bigcupsP=> x Rx; apply/subsetP=> u Vjxu.
  have PRx: x \in P <*> R by apply: subsetP Rx; exact: mulgen_subr.
  apply/bigcupP; exists (Kj :^ x)%G; last by rewrite -ViJ.
  rewrite (actsP actsPR_K) // mxKj; apply: contra V1Rj.
  by move/orbit_transl=> <-; rewrite orbit_sym -ViJ // mem_imset.
rewrite subEproper; case/predU1P=> [defV1R | ]; last first.
  case/andP=> sV1R; case/subsetPn=> Vj; case/imsetP=> Kj mxKj ->{Vj} V1Rj.
  have defmxV: Vi @: mxK = Vi Kj |: orbit 'JG%act R (Vi K1).
    apply/eqP; rewrite eqEsubset andbC subUset sub1set mem_imset //.
    rewrite sV1R; apply/subsetP=> V_i; case/imsetP=> Ki mxKi ->{V_i}.
    rewrite inE orbC; apply/norP=> [[]]; move/nVjR=> -> //; case/set1P.
    by move/nVjR: V1Rj => ->.
  have ViV1: Vi K1 \in Vi @: mxK by rewrite mem_imset.
  rewrite odd_2'nat in oddG; have: 2^'.-group (P <*> R).
    by apply: pgroupS oddG; rewrite mulgen_subG sRG (subset_trans sPH).
  move/(pnat_dvd (atrans_dvd transPR)).
  rewrite defmxV cardsU1 (negPf V1Rj) oV1R -oR.
  rewrite -odd_2'nat /= odd_2'nat; case/negP; exact: pgroupS oddG.
have:= sub0set 'Fix_(Vi @: mxK | 'JG)(P); rewrite subEproper.
case/predU1P=> [fix0|].
  case/negP: nrp; rewrite eq_sym -dvdn_prime2 //; apply/eqnP.
  have:= pgroup_fix_mod pP (subset_trans (mulgen_subl P R) actsPR).
  by rewrite -{1}defV1R oV1R -fix0 cards0 (modn_small (prime_gt0 _)).
case/andP=> _; case/subsetPn=> Vj; case/setIP; case/imsetP=> Kj mxKj ->{Vj}.
rewrite afixJG => nVjP.
suffices trVj: Vi Kj :=: 1 by rewrite -(oVi Kj) // trVj cards1 in pr_p.
apply/trivgP; rewrite -trCVK subsetI subsetIl centsC defKP.
rewrite -ker_conj_aut -sub_morphim_pre ?comm_subG ?morphimR ?nViK // andTb.
rewrite (commG1P _) //; apply/centsP=> a.
case/imsetP=> x _ -> b; case/imsetP=> y _ -> {a b}.
have: cyclic (Vi Kj) by rewrite prime_cyclic ?oVi.
case/cyclicP=> v; move/group_inj->.
apply: (centsP (Aut_cycle_abelian v)); exact: Aut_aut.
Qed.
