Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms group_perm automorphism normal commutators.
Require Import cyclic center pgroups sylow dirprod schurzass hall. 
Require Import coprime_act nilpotent coprime_comm maximal.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.
Section defs.
Variable T : finGroupType.
(* waiting for the actual definition *)
Parameter fitting: {set T} -> {set T}.
Axiom fitting_group_set : forall G : {group T}, group_set (fitting G).
Canonical Structure fitting_group G : {group T} := Group (fitting_group_set G).

Definition Zgroup (A : {set T}) := 
  forallb V : {group T}, Sylow A V ==> cyclic V.

End defs.

Notation "''F' ( G )" := (fitting G)
  (at level 8, format "''F' ( G )") : group_scope.
Notation "''F' ( G )" := (fitting_group G) : subgroup_scope.

Section Props.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types G H K : {group gT}.

Lemma cyclicS : forall G H, H \subset G -> cyclic G -> cyclic H. 
Proof.
move=> G H HsubG; case/cyclicP=> x gex; apply/cyclicP.
exists (x ^+ (#[x] %/ #|H|)); apply: congr_group; apply/set1P.
by rewrite -cycle_sub_group /order -gex ?cardSg // inE HsubG eqxx.
Qed.

Lemma cycleJ : forall x y : rT, <[x]> :^ y = <[x ^ y]>.
Proof. by move=> x y; rewrite -genJ conjg_set1. Qed.

Lemma cyclicJ:  forall (G : {group rT}) x, cyclic (G :^ x) = cyclic G.
Proof.
move=> G x; apply/cyclicP/cyclicP=> [[y] | [y ->]].
  by move/(canRL (conjsgK x)); rewrite cycleJ; exists (y ^ x^-1).
by exists (y ^ x); rewrite cycleJ.
Qed.

Lemma cyclic_morphim : forall G, cyclic G -> cyclic (f @* G).
Proof.
move=> G cG; wlog sGD: G cG / G \subset D.
  by rewrite -morphimIdom; apply; rewrite (cyclicS _ cG, subsetIl) ?subsetIr.
case/cyclicP: cG sGD => x ->; rewrite gen_subG sub1set => Dx.
by apply/cyclicP; exists (f x); rewrite morphim_cycle.
Qed.

Lemma ZgroupS : forall G H, H \subset G -> Zgroup G -> Zgroup H. 
Proof.
move=> G H sHG; move/forallP=> zgG; apply/forallP=> V; apply/implyP.
case/SylowP=> p pr_p; rewrite pHallE p_part; case/andP=> sVH.
case/(sylow1_subset pr_p (subset_trans sVH sHG))=> P; case/andP=> sVP sylP.
by apply: cyclicS sVP (implyP (zgG _) _); apply/SylowP; exists p.
Qed.

Lemma Zgroup_morphim : forall G, Zgroup G -> Zgroup (f @* G). 
Proof.
move=> G zgG; wlog sGD: G zgG / G \subset D.
  by rewrite -morphimIdom; apply; rewrite (ZgroupS _ zgG, subsetIl) ?subsetIr.
apply/forallP=> fV; apply/implyP.
case/SylowP=> p pr_p sylfV; have [P sylP] := sylow1_cor G pr_p.
have [|z _ ->] := (sylow2_cor pr_p) (f @* P)%G _ _ sylfV.
  apply: morphim_pHall (sylP); exact: subset_trans (pHall_subset sylP) sGD.
rewrite cyclicJ cyclic_morphim // (implyP (forallP zgG P)) //.
by apply/SylowP; exists p.
Qed.

Lemma Phi_char: forall G, 'Phi(G) \char G. Admitted.

Lemma coprime_cent_Phi : forall H G,
  coprime #|H| #|G| -> [~: H, G] \subset 'Phi(G) ->  H \subset 'C(G).
Admitted.

Lemma Fitting_def : forall G H,
  H <| G -> nilpotent H -> H \subset 'F(G).
Admitted.

Lemma solvable_self_cent_Fitting : forall G,
  solvable G -> 'C_G('F(G)) \subset 'F(G).
Admitted.

Lemma Fitting_char : forall G, 'F(G) \char G.
Admitted.

Lemma Fitting_normal : forall G, 'F(G) <| G.
Proof. move=> G; apply: char_normal; exact: Fitting_char. Qed.

End Props.

Lemma Fitting_isom :
  forall (gT rT : finGroupType) (G : {group gT}) (f : {morphism G >-> rT}),
  'injm f -> 'F(f @* G) = f @* 'F(G).
Admitted.

Theorem three_dot_four : forall k (gT : finGroupType) (G K R V : {group gT}),
  solvable G -> odd #|G| ->
  K <| G -> Hall G K -> R \in complg G K -> prime #|R| ->
  k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  trivg 'C_V(R) -> [~: R, K] \subset 'C_K(V).
Admitted.
  
Theorem three_dot_five : forall k (gT : finGroupType) (G K R V : {group gT}),
  solvable G ->
  K <| G -> R \in complg G K -> prime #|R| -> trivg 'C_K(R) ->
  k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  #|'C_V(R)| = k -> K^`(1) \subset 'C_K(V).
Admitted.

Theorem three_dot_six : forall (gT : finGroupType) (G H R R0 : {group gT}),
    solvable G -> odd #|G| ->
    H <| G -> Hall G H -> R \in complg G H ->
    R0 \subset R -> prime #|R0| -> Zgroup 'C_H(R0) ->
  forall p, prime p -> p.-length_1 [~: H, R].
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn H R R0.
move=> solG oddG nHG hallH compH_R sR0R.
move oR0: #|R0| => r pr_r ZCHR0 p pr_p.
have sRG: R \subset G by exact: sub_compl compH_R.
case/complgP: compH_R => trivgHR eqHR_G; case/andP: (hallH) => sHG coHH'.
have{coHH'} coHR: coprime #|H| #|R|. 
  have:= coHH'; rewrite -divgS -eqHR_G ?mulG_subl // .
  by rewrite (card_mulG_trivP _ _ trivgHR) ?divn_mulr. 
have nHR: R \subset 'N(H) := subset_trans sRG (normal_norm nHG).
have IHG: forall H1 R1 : {group gT},
  H1 \subset H -> H1 * R1 \subset 'N(H1) -> R0 \subset R1 -> R1 \subset R ->
  (#|H1| < #|H|) || (#|R1| < #|R|) -> p.-length_1 [~: H1, R1].
- move=> H1 R1 sH1 nH1 sR01 sR1 ltG1.
  move defHR1: (H1 <*> R1)%G => G1; have{defHR1} defG1: G1 :=: H1 * R1.
    have nH1R: R1 \subset 'N(H1) := subset_trans (mulG_subr H1 R1) nH1.
    by rewrite -defHR1 /= mulgenC norm_mulgenE // normC.
  have coHR1: coprime #|H1| #|R1|.
    rewrite -(LaGrange sH1) -(LaGrange sR1) coprime_mull coprime_mulr in coHR.
    by case/andP: coHR; case/andP.
  have oG1: #|G1| = (#|H1| * #|R1|)%N by rewrite defG1 coprime_card_mulG.
  have ltG1n: #|G1| < n.
    have:= leqif_mul (leqif_geq (subset_leq_card sH1))
                     (leqif_geq (subset_leq_card sR1)).
    rewrite -oG1 -coprime_card_mulG // eqHR_G eqn0Ngt ltn_0group /= => leG1.
    by apply: leq_trans leGn; rewrite ltn_neqAle !leG1 andbT negb_and -!ltnNge.
  have sG1G: G1 \subset G.
    by rewrite defG1 mul_subG // (subset_trans sH1, subset_trans sR1).
  have solG1: solvable G1 := solvableS sG1G solG.
  have oddG1: odd #|G1|.
    move: oddG; do 2!rewrite -[odd _]negbK -dvdn2_even; apply: contra. 
    move/dvdn_trans; apply; exact: cardSg.
  have nHG1: H1 <| G1 by rewrite /(H1 <| _) defG1 mulG_subl.
  have hallH1: Hall G1 H1.
    by rewrite /Hall -divgS normal_sub // oG1 divn_mulr.
  have complR1: R1 \in complg G1 H1 by apply/complgP; rewrite coprime_trivg.
  apply: IHn complR1 sR01 _ _ p pr_p => //; first by rewrite oR0.
  exact: ZgroupS (setSI _ sH1) ZCHR0.
without loss defHR: / [~: H, R] = H.
  have:= nHR; rewrite -subcomm_normal commsgC => sHR_R.
  have:= sHR_R; rewrite subEproper; case/predU1P=> [-> -> //|s'HR_H _].
  rewrite commGAA //; last exact: solvableS solG.
  apply: IHG => //; last by rewrite proper_card.
  apply: subset_trans (normal_norm (normal_commutator H R)).
  by rewrite mulgenC norm_mulgenE // (normC nHR) mulSg.
have{IHn trivgHR hallH} IHquo: forall X : group gT,
  ~~ trivg X -> X \subset H -> G \subset 'N(X) -> p.-length_1 (H / X).
- move=> X ntX sXH nXG; have nXH := subset_trans sHG nXG.
  have nXR := subset_trans sRG nXG; have nXR0 := subset_trans sR0R nXR.
  rewrite -defHR quotientE morphimR // -!quotientE.
  have ltG'n: #|G / X| < n.
    apply: leq_trans leGn; rewrite card_quotient //.
    rewrite -[#|G : X|]mul1n -(LaGrange (subset_trans sXH sHG)).
    by rewrite ltn_pmul2r // ltnNge -trivg_card.
  have solG': solvable (G / X) by exact: solvable_quo.
  have oddG': odd #|G / X|.
    move: oddG; do 2!rewrite -[odd _]negbK -dvdn2_even; apply: contra. 
    by move/dvdn_trans; apply; exact: dvdn_morphim.
  have nHG': H / X <| G / X by exact: morphim_normal.
  have hallH': Hall (G / X) (H / X) by exact: morphim_Hall.
  have compR': (R / X)%G \in complg (G / X) (H / X).
    apply/complgP; split; last by rewrite -morphimMl ?eqHR_G. 
    by rewrite -morphimGI ?ker_coset // [H :&: R](trivgP _ trivgHR) morphim1.
  have sR0R': R0 / X \subset R / X by exact: morphimS.
  have pr_R0X: prime #|R0 / X|.
    have trXR0: X :&: R0 = 1.
      by apply/trivgP; exact: subset_trans (setISS _ _) trivgHR.
    by rewrite card_quotient // -divgI setIC trXR0 cards1 divn1 oR0.
  apply: IHn compR' sR0R' pr_R0X _ _ pr_p => //.
  have coHR0: coprime #|H| #|R0|.
    by rewrite -(LaGrange sR0R) coprime_mulr in coHR; case/andP: coHR.
  rewrite -coprime_quotient_cent_weak ?Zgroup_morphim //; first exact/andP.
  exact: solvableS solG.
rewrite defHR.
without loss Op'_H: / trivg 'O_p^'(H).
  case/orP: (orbN (trivg 'O_p^'(H))) => [-> -> // | ntO _].
  suffices: p.-length_1 (H / 'O_p^'(H)).
    by rewrite p'quo_plength1 ?pcore_normal ?pcore_pgroup.
  apply: IHquo => //; first by rewrite normal_sub ?pcore_normal.
  by rewrite normal_norm // (char_norm_trans (pcore_char _ _)).
move defV: 'F(H)%G => V.
have charV: V \char H by rewrite -defV Fitting_char.
have nVG: G \subset 'N(V) by rewrite normal_norm ?(char_norm_trans charV).
have sVH: V \subset H by rewrite normal_sub ?char_normal.
have defVp: V :=: 'O_p(H).
  admit.
have pV: p.-group V by rewrite defVp pcore_pgroup.
have sCV_V: 'C_H(V) \subset V.
  rewrite -defV solvable_self_cent_Fitting //; exact: solvableS solG.
wlog abV: / p.-abelem V.
  case/orP: (orbN (trivg 'Phi(V))) => [trPhi -> // | ntPhi _].
    admit.
  have chPhi: 'Phi(V) \char H := char_trans (Phi_char _) charV.
  have nPhiH := char_normal chPhi; have sPhiH := normal_sub nPhiH.
  have{chPhi} nPhiG: G \subset 'N('Phi(V)).
    exact: normal_norm (char_norm_trans chPhi nHG).
  rewrite -(pquo_plength1 nPhiH) 1?IHquo //.
    exact: pgroupS (Phi_sub _) pV.
  have: 'O_p^'(H / 'Phi(V)) <| H / 'Phi(V) by exact: pcore_normal.
  case/(inv_quotientN _) => //= W defW sPhiW nWH.
  have p'Wb: p^'.-group (W / 'Phi(V)) by rewrite -defW; exact: pcore_pgroup.
  suffices pW: p.-group W.
    rewrite trivg_card (@pnat_1 p #|_|) //= defW //.
    exact: morphim_pgroup.
  apply/pgroupP=> q pr_q; case/Cauchy=> // x Wx oxq; apply/idPn=> /= neqp.
  suff: <[x]> \subset V.
    rewrite gen_subG sub1set => Vx.
    by move/pgroupP: pV neqp => /= -> //; rewrite -oxq order_dvd_g.
  apply: subset_trans sCV_V; rewrite subsetI cycle_h /=; last first.
    apply: subsetP Wx; exact: normal_sub.
  have coxV: coprime #[x] #|V|.
    by rewrite oxq coprime_sym (pnat_coprime pV) // pnatE.
  apply: coprime_cent_Phi coxV _.
  have: W :&: V \subset 'Phi(V); last apply: subset_trans.
    rewrite -trivg_quotient; last first.
      by rewrite subIset // orbC normal_norm // char_normal // Phi_char.  
    rewrite quotientE morphimIG ?ker_coset ?Phi_sub // -!quotientE.
    rewrite setIC coprime_trivg // (@pnat_coprime p) //.
    by rewrite [_.-nat _]morphim_pgroup.
  case/andP: nWH => sWH nWH.
  rewrite subsetI andbC subcomm_normal cycle_h; last first.
    by apply: subsetP Wx; apply: subset_trans (subset_trans sWH _) nVG.
  move: nWH; rewrite -subcomm_normal commsgC; apply: subset_trans.
  by rewrite commgSS // cycle_h //.
have{sCV_V} eqVC: V :=: 'C_H(V). 
  by apply/eqP; rewrite eqset_sub sCV_V subsetI andbT sVH; case/p_abelemP: abV.
wlog{IHquo} nondecV:  / forall N1 N2,
      N1 \x N2 = V -> G \subset 'N(N1) :&: 'N(N2) -> trivg N1 \/ N1 = V.
  pose decV := [pred N | [&& N.1 \x N.2 == V, G \subset 'N(N.1) :&: 'N(N.2),
                             ~~ trivg N.1 & ~~ trivg N.2]].
  case: (pickP decV) => [[A1 A2 /=] | trN12]; last first.
    apply=> N1 N2 defN nNG; move/(_ (N1, N2)): trN12 => /=.
    rewrite defN eqxx {}nNG /= -negb_or; case/orP; first by left.
    case/dprodGP: defN => [] [_ N3 _ -> <- _] _; move/trivgP->.
    by right; rewrite mulg1.
  case: eqP => //=; case/dprodGP=> [[N1 N2 -> ->{A1 A2} defN _] trN12].
  have [sN1 sN2]: N1 \subset H /\ N2 \subset H.
    apply/andP; rewrite -subUset (subset_trans _ sVH) // -defN.
    by rewrite subUset mulG_subl mulG_subr.
  case/and3P=> nNG ntN1 ntN2 _; have [nN1 nN2]: N1 <| H /\ N2 <| H.
    by apply/andP; rewrite /normal sN1 sN2 /= -subsetI (subset_trans sHG).
  rewrite subsetI in nNG; case/andP: nNG => nN1G nN2G.
  by rewrite -(quo2_plength1 pr_p nN1 nN2 trN12) ?IHquo.
have: 'F(H / V) <| G / V.
  exact: char_norm_trans (Fitting_char _) (morphim_normal _ _).
case/(inv_quotientN _) => [| /= U defU sVU nUG].
  by apply/andP; rewrite (subset_trans sVH).
case/andP: nUG => sUG nUG; have nUR := subset_trans sRG nUG.
have sUH: U \subset H.
  have: U / V \subset H / V by rewrite -defU normal_sub ?Fitting_normal.
  by rewrite morphimSGK ?ker_coset // (subset_trans sUG).
have: exists2 K : {group gT}, p^'.-Hall(U) K & R \subset 'N(K).
  apply: coprime_hall_exists => //; last exact: (solvableS sUG).
  by rewrite -(LaGrange sUH) coprime_mull in coHR; case/andP: coHR.
case=> K hallK nKR; have [sKU _]:= andP hallK.
have p'K: p^'.-group K by exact: pHall_pgroup hallK.
have p'Ub: p^'.-group 'F(H / V) by admit.
have nVU := subset_trans (subset_trans sUH sHG) nVG.
have defVK: U :=: V * K.
  have nVK := subset_trans sKU nVU.
  apply/eqP; rewrite eqset_sub mul_subG //= andbT -quotientSK //.
  rewrite subEproper eq_sym eqset_sub_card.
  have: p^'.-Hall(U / V) (K / V) by exact: morphim_pHall.
  by case/pHallP=> -> ->; rewrite part_pnat ?leqnn //= -defU.
have sylV: p.-Sylow(U) V.
  have coVK: coprime #|V| #|K| := pnat_coprime pV p'K.
  by rewrite /pHall sVU [_.-group _]pV -card_quotient // -defU.
have defH: H :=: V * 'N_H(K).
  have nUH: U <| H by apply/andP; rewrite (subset_trans sHG).
  rewrite -{1}(HallFrattini _ nUH hallK); last exact: solvableS solG.
  by rewrite defVK -mulgA [K * _]mulSGid // subsetI normG (subset_trans sKU).
have [P sylP nPR]:
  exists2 P : {group gT}, p.-Sylow('N_H(K)) P & R \subset 'N(P).
+ have sNH: 'N_H(K) \subset H by exact: subsetIl.
  apply: coprime_hall_exists.
  - by apply/normsP=> x Rx /=; rewrite conjIg -normJ !(normsP _ _ Rx).
  - by move: coHR; rewrite -(LaGrange sNH) coprime_mull; case/andP.
  apply: solvableS solG; exact: subset_trans sHG.
have sPN: P \subset 'N_H(K) by case/andP: sylP.
have [sPH nKP]: P \subset H /\ P \subset 'N(K) by apply/andP; rewrite -subsetI.
have nVH := subset_trans sHG nVG; have nVP := subset_trans sPH nVH.
have sylVP: p.-Sylow(H) (V * P).
  have defVP: V * P = V <*> P by rewrite mulgenC -normC ?norm_mulgenE.
  rewrite defVP pHallE /= -defVP mul_subG //= defVP.
  rewrite -(LaGrange sVH) partn_mul ?ltn_0mul ?ltn_0group //=.
  have: V \subset V <*> P by rewrite -defVP mulG_subl.
  move/LaGrange <-; rewrite part_pnat // eqn_pmul2l // /=.
  rewrite -!card_quotient //; last by rewrite gen_subG subUset normG.
  rewrite -defVP defH !quotient_mulgr.
  have: p.-Sylow('N_H(K) / V) (P / V) by exact: morphim_pHall.
  by case/pHallP=> _ ->.
case/orP: (orbN (trivg [~: K, P])) => [tKP|ntKP].
  suffices sylVH: p.-Sylow(H) V.
    rewrite p_elt_gen_length1 // (_ : p_elt_gen p H = V).
      rewrite /pHall pcore_sub pcore_pgroup /= pnatNK.
      apply: pnat_dvd pV; exact: dvdn_indexg.
    rewrite -(genGid V); congr <<_>>; apply/setP=> x; rewrite inE.
    apply/andP/idP=> [[Hx p_x] | Vx].
      by rewrite (mem_normal_Hall sylVH) // /normal sVH.
    split; [exact: (subsetP sVH) | exact: mem_p_elt Vx].
  suffices sPV: P \subset V by rewrite mulGSid in sylVP.
  have sol_qHV : solvable (H /V). 
    by apply: solvable_quo; apply: (solvableS sHG).
  have qPV: P / V \subset 'C_(H / V)('F(H / V)).
    rewrite defU subsetI; apply/andP; split; first by apply:morphimS.
    rewrite defVK quotient_mulgr; apply: center_commgr; rewrite commsgC.
    case/trivgP: tKP; move ->; apply: sub1G.
  have sPU: P \subset U.
    rewrite defVK -quotientSK // -(quotient_mulgr _ K) -defVK -defU.
    by apply (subset_trans qPV (solvable_self_cent_Fitting sol_qHV)).
  case/pHallP: sylP => _; rewrite p_part; move/eqP=> cardP. 
  apply: (sylow2_subset pr_p sPU cardP); rewrite //=.
  rewrite/normal sVU //=.
have{sylVP} dp: [~: V, K] \x 'C_V(K) :=: V.
  apply: sym_eq; apply: comm_center_dir_prod; last by case/p_abelemP: abV.
    exact: subset_trans sKU nVU.
  exact: pnat_coprime pV p'K.
have trVeq: trivg 'C_V(K) \/ 'C_V(K) = V.
  apply: (nondecV _  [~: V, K]); first by rewrite dprodC.
  rewrite -eqHR_G defH -mulgA mul_subG //.
    by rewrite subsetI normGR cents_norm // centsC {1}eqVC setIAC subsetIr.
  have: 'N_H(K) * R \subset 'N_G(K) by rewrite mul_subG ?setSI // subsetI sRG.
  move/subset_trans; apply; apply/subsetP=> x; case/setIP=> Gx nKx.
  rewrite 3!inE conjIg -centJ /= -{1}[[~:V, K]]setTI -morphim_conj.
  rewrite morphimR ?subsetT // !morphim_conj !setTI.
  by rewrite (normP nKx) (normsP nVG) ?subset_refl.
have{sKU sUH} sKH: K \subset H by exact: subset_trans sKU sUH.
have{trVeq dp} [Vcomm trCVK]: [~: V, K] :=: V /\ trivg 'C_V(K).
  case trVeq=> [trC | eqC]. 
    by rewrite -{2}dp // ['C_V(K)](trivgP _ trC) dprodg1.
  case/negP: ntKP; suff: trivg K by move/trivgP->; rewrite comm1G.
  rewrite trivg_card (pnat_1 _ p'K) //; apply: pgroupS pV.
  by rewrite eqVC subsetI sKH centsC -eqC subsetIr.
have eqcn: 'N_V(K) = 'C_V(K).
  apply: coprime_norm_cent (pnat_coprime pV p'K).
  by rewrite -subcomm_normal commsgC -{2}Vcomm subset_refl.
have VIN: trivg (V :&: 'N_H(K)) by rewrite setIA (setIidPl sVH) eqcn.
have VIP: trivg (V :&: P).
  apply: subset_trans VIN; apply: setIS; exact: (subset_trans sPN).
have nVN: 'N_H(K) \subset 'N(V) by rewrite (subset_trans _ nVH) ?subsetIl.
have defK: K :=: 'F('N_H(K)).
  have isoV: 'injm (restrm nVN (coset_of V)).
    by rewrite ker_restrm ker_coset setIC.
  have sKN: K \subset 'N_H(K) by rewrite subsetI sKH normG.
  rewrite -['N_H(K)](invm_dom isoV) Fitting_isom ?injm_invm //=.
  rewrite {2}morphim_restrm setIid -quotientE -quotient_mulgr -defH defU.
  rewrite defVK quotient_mulgr -{10}(setIidPr sKN) quotientE.
  by rewrite -(morphim_restrm nVN) morphim_invm.
have sCKK: 'C_H(K) \subset K.
  rewrite {2}defK; apply: subset_trans (solvable_self_cent_Fitting _).
    by rewrite -defK subsetI subsetIr setIS // cent_sub.
  by apply: solvableS (solvableS sHG solG); apply: subsetIl.
have{nVN} ntKR0: ~~ trivg [~: K, R0].
  apply/commG1P; move/centsP=> cKR0; case/negP: ntKP.
  have Z_K: Zgroup K by apply: ZgroupS ZCHR0; rewrite subsetI sKH.
  have cycK: cyclic K by admit.
  have AcycK : abelian (Aut K).
    case/cyclicP: cycK => x ->; exact: aut_cycle_commute.
  have sNR_K: [~: 'N_H(K), R] \subset K.
    apply: subset_trans sCKK; rewrite subsetI; apply/andP; split.
      apply: subset_trans (commSg R (subsetIl _ _)) _.
      by rewrite commsgC subcomm_normal.
    suff: 'N(K)^`(1) \subset 'C(K).
      by apply: subset_trans; rewrite commgSS ?subsetIr.
    rewrite -ker_conj_aut ker_trivg_morphim comm_subG // morphimR //.
    have sjK_AK: conj_aut K @* 'N(K) \subset Aut K.
      apply/subsetP=> a; case/imsetP=> f _ ->; exact: Aut_aut_of.
    move/centsP: AcycK; move/commG1P; apply: subset_trans; exact: commgSS.
  suff sPV: P \subset V.
    by rewrite -(setIidPr sPV) [V :&: P](trivgP _ VIP) commG1.
  have pPV: p.-group (P / V) by exact: morphim_pgroup (pHall_pgroup sylP).
  rewrite -trivg_quotient // trivg_card (pnat_1 pPV _) //.
  have: p^'.-group (K / V) by exact: morphim_pgroup p'K.
  apply: pgroupS; apply: subset_trans (morphimS _ sNR_K).
  have nVR: R \subset 'N(V) by exact: subset_trans nVG.
  rewrite morphimR // -quotientE -quotient_mulgr -defH -morphimR ?morphimS //.
  by rewrite defHR.
have nKR0: R0 \subset 'N(K) by exact: subset_trans nKR.
have sKR0_G : K <*> R0 \subset G.
  by rewrite gen_subG subUset (subset_trans sKH) ?(subset_trans sR0R).
have nV_KR0: K <*> R0 \subset 'N(V) by exact: subset_trans nVG.
have: K :|: R0 \subset K <*> R0 by rewrite -gen_subG subset_refl.
rewrite subUset; case/andP=> sK_KR0 sR0_KR0.
have solKR0: solvable (K <*> R0) by exact: solvableS solG.
have coK_R0: coprime #|K| #|R0|.
  have:= coHR; rewrite -(LaGrange sKH) -(LaGrange sR0R).
  by rewrite coprime_mull coprime_mulr -andbA; case/andP.
have oKR0: #|K <*> R0| = (#|K| * #|R0|)%N.
  by rewrite norm_mulgenEr // coprime_card_mulG.
have r'K: r^'.-group K.
  apply/pgroupP=> q pr_q dv_qK; apply/eqP=> def_q.
  by rewrite oR0 coprime_sym prime_coprime // -def_q dv_qK in coK_R0.
have rR0: r.-group R0 by by rewrite /pgroup oR0 pnat_id // inE /= eqxx.
have hallK_R0: r^'.-Hall(K <*> R0) K.
  by rewrite /pHall sK_KR0 r'K -divgS // pnatNK oKR0 divn_mulr.
have hallR0_K: r.-Sylow(K <*> R0) R0.
  by rewrite /pHall sR0_KR0 rR0 -divgS // oKR0 divn_mull.
have trCKR0_V: trivg 'C_(K <*> R0)(V).
  have nC_KR0: 'C_(K <*> R0)(V) <| K <*> R0.
    rewrite /(_ <| _) subsetIl normsI ?normG //.
    by rewrite (subset_trans nV_KR0) ?cent_norm.
  have hallCK: r^'.-Hall('C_(K <*> R0)(V)) 'C_K(V).
    rewrite -{2}(setIidPl sK_KR0) -setIA; exact: HallSubnormal hallK_R0.
  have hallCR0: r.-Sylow('C_(K <*> R0)(V)) 'C_R0(V).
    rewrite -{2}(setIidPl sR0_KR0) -setIA; exact: HallSubnormal hallR0_K.
  have sC_R0: 'C_(K <*> R0)(V) \subset R0.
    apply/setIidPr; apply/eqP; rewrite setIA (setIidPl sR0_KR0) //=.
    rewrite eqset_sub_card -[#|'C_(K <*> R0)(V)|](partnC r) ?ltn_0group //.
    case/pHallP: hallCR0 => -> <-; case/pHallP: hallCK => _ <-.
    rewrite -{2}(muln1 #|_|) leq_mul // -trivg_card; apply: subset_trans VIN.
    rewrite /= -{1}(setIidPl sKH) -setIA -eqVC setIC setIS //.
    by rewrite subsetI sKH normG.
  have:= cardSg sC_R0; rewrite oR0.
  case: (primeP pr_r) => _ dv_r; move/dv_r; rewrite eqn_leq -trivg_card orbC.
  case/predU1P => [oCr|]; last by case/andP.
  case/negP: ntKR0; apply: subset_trans (coprime_trivg coK_R0).
  rewrite subsetI {1}commsgC !subcomm_normal nKR0.
  apply: (subset_trans sK_KR0); case/andP: nC_KR0 => _; apply: etrans.
  congr (_ \subset 'N(_)); apply/eqP.
  by rewrite eq_sym eqset_sub_card sC_R0 oCr /= oR0.
have oCVR0: #|'C_V(R0)| = p.
  case trCVR0: (trivg 'C_V(R0)).
    case/negP: ntKR0; have: trivg 'C_K(V); last apply: subset_trans.
      by apply: subset_trans trCKR0_V; rewrite setSI.
    rewrite commsgC; apply: three_dot_four abV nV_KR0 _ trCVR0 => //.
    - move: oddG; do 2!rewrite -[odd _]negbK -dvdn2_even; apply: contra. 
      move/dvdn_trans; apply; exact: cardSg.
    - by rewrite /(K <| _) sK_KR0 gen_subG subUset normG.
    - exact: (pHall_Hall hallK_R0).
    - by apply/complgP; rewrite coprime_trivg //= norm_mulgenEr.
    - by rewrite oR0.
    rewrite oKR0 -prime_coprime // coprime_mulr.
    rewrite (pnat_coprime _ p'K) ?pnat_id //=.
    move: coHR; rewrite -(LaGrange sPH) -(LaGrange sR0R).
    rewrite coprime_mull coprime_mulr -andbA andbC oR0; case/andP=> _.
    case/p_natP: (pHall_pgroup sylP) => // [[trP|i ->]].
      by case/negP: ntKP; rewrite (trivgP P _) ?commG1 // trivg_card trP.
    by rewrite coprime_pexpl.
  have: cyclic 'C_V(R0).
    have: Sylow 'C_V(R0) 'C_V(R0); last apply/implyP.
      apply/SylowP; exists p => //.
      rewrite /pHall subset_refl indexgg andbT.
      apply: pgroupS pV; exact: subsetIl.
    have: Zgroup 'C_V(R0) by apply: ZgroupS ZCHR0; exact: setSI.
    move/forallP; exact.
  case/cyclicP=> x defC; rewrite defC.
  have: #[x] %| p.
    rewrite order_dvd; apply/eqP.
    have:= cyclenn x; rewrite -defC setIC; case/setIP=> _.
    by case/p_abelemP: abV => // _; exact.
  case/primeP: pr_p => _ pr_p; move/pr_p; case/orP; move/eqnP=> // ox1.
  by rewrite trivg_card /= defC [#|_|] ox1 in trCVR0.
have trCP_R0: trivg 'C_P(R0).
  have pP := pHall_pgroup sylP.
  have: p.-group 'C_P(R0) by apply: pgroupS pP; exact: subsetIl.
  rewrite trivg_card; case/p_natP=> // [[-> //| i oC]].
  have {i oC}: p %| #|'C_P(R0)| by rewrite oC dvdn_mulr.
  case/Cauchy=> // x Cx oxp.
  suff: trivg <[x]> by rewrite trivg_card [#|_|]oxp leqNgt prime_gt1.
  apply: subset_trans VIP; rewrite subsetI andbC.
  rewrite cycle_h /=; last by case/setIP: Cx.
  suff <-: 'C_V(R0) = <[x]> by rewrite subsetIl.
  have: cyclic 'C_(P <*> V)(R0).
    have: Sylow 'C_(P <*> V)(R0) 'C_(P <*> V)(R0); last apply/implyP.
      apply/SylowP; exists p => //.
      rewrite /pHall subset_refl indexgg andbT.
      suff: p.-group (P <*> V) by apply: pgroupS; exact: subsetIl.
      have: p.-nat (#|P| * #|V|)%N by rewrite pnat_mul //; exact/andP.
      by rewrite norm_mulgenE // -card_mulG pnat_mul //; case/andP.
    suff: Zgroup 'C_(P <*> V)(R0) by move/forallP; exact.
    by apply: ZgroupS ZCHR0; rewrite setSI // gen_subG subUset sPH.
  case/cyclicP=> y defC; apply: congr_group.
  have y_x: x \in <[y]>.
    by apply: subsetP Cx; rewrite -defC setSI // sub_gen // subsetUl.
  have: p %| #[y] by rewrite -oxp order_dvd_g.
  move/cycle_sub_group; set Cy1 := <[_]>%G => defCy1.
  have ->: <[x]>%G = Cy1.
    apply/set1P; rewrite -defCy1 inE cycle_h //=; exact/eqP.
  by apply/set1P; rewrite -defCy1 inE oCVR0 -defC setSI //= sub_gen ?subsetUr.
have defP: P :=: [~: P, R0].
  move: coHR; rewrite -(LaGrange sPH) -(LaGrange sR0R).
  rewrite coprime_mull coprime_mulr -andbA andbC; case/andP=> _.
  move/comm_center_prod=> defP; rewrite {1}defP ?(subset_trans sR0R) //.
    by rewrite ['C__(_)](trivgP _ trCP_R0) mulg1.
  apply: solvableS solG; exact: subset_trans sHG.
have{IHG} IHG: forall X : {group gT},
  P <*> R0 \subset 'N(X) -> X \subset K ->
  (#|V <*> X <*> P| < #|H|) || (#|R0| < #|R|) -> trivg [~: X, P].
- move=> X nX_PR0 sXK ltX_G.
  have sXH: V <*> X <*> P \subset H.
    rewrite gen_subG subUset sPH andbT gen_subG subUset sVH /=.
    exact: subset_trans sKH.
  have nXR0: R0 \subset 'N(V <*> X <*> P).
    rewrite mulgenC mulgenA norms_mulgen //.
      by rewrite (subset_trans sR0R) ?norms_mulgen // (subset_trans sRG).
    by apply: subset_trans nX_PR0; rewrite sub_gen ?subsetUr.
  have trOp'H1: trivg 'O_p^'(V <*> X <*> P).
    rewrite trivg_card (pnat_1 _ (pcore_pgroup _ _)) //; apply: pgroupS pV.
    have nO_X := pcore_normal p^' (V <*> X <*> P).
    rewrite {2}eqVC subsetI (subset_trans _ sXH) ?(normal_sub nO_X) //=.
    rewrite centsC; apply/setIidPl; rewrite -coprime_norm_cent.
    + apply/setIidPl; case/andP: nO_X => _; apply: subset_trans.
      by rewrite /= -mulgenA sub_gen // subsetUl.
    + apply: subset_trans nVH; apply: subset_trans sXH; exact: normal_sub.
    apply: pnat_coprime (pcore_pgroup _ _).
    rewrite defVp; exact: pcore_pgroup.
  have{trOp'H1} trOR: trivg 'O_p^'([~: V <*> X <*> P, R0]).
    apply: subset_trans trOp'H1.
    apply: subset_pcore; first exact: pcore_pgroup.
    apply: char_norm_trans (pcore_char _ _) _.
    by rewrite /(_ <| _) normGR /= commsgC subcomm_normal andbT.
  have sP_O: P \subset 'O_p([~: V <*> X <*> P, R0]).
    rewrite (@subset_normal_Hall _ p _ [~: ((V <*> X) <*> P)%g, R0]).
    + rewrite /psubgroup (pHall_pgroup sylP) {1}defP commSg //.
      by rewrite sub_gen // subsetUr.
    + rewrite /pHall pcore_sub pcore_pgroup /= -(pseries_pop2 _ trOR).
      rewrite -card_quotient ?normal_norm ?pseries_normal //.
      have{ltX_G IHG} VXPR_1: p.-length_1 [~: V <*> X <*> P, R0].
        by apply: IHG ltX_G => //=; rewrite mul_subG ?normG.
      rewrite -{1}((_ =P [~: _, _]) VXPR_1) quotient_pseries.
      exact: pcore_pgroup.
    exact: pcore_normal.
  have: trivg (K :&: 'O_p([~: (V <*> X) <*> P, R0])).
    apply: coprime_trivg; rewrite coprime_sym (pnat_coprime _ p'K) //.
    exact: pcore_pgroup.
  apply: subset_trans; rewrite subsetI; apply/andP; split.
    by apply: subset_trans (commSg _ sXK) _; rewrite commsgC subcomm_normal.
  apply: subset_trans (commgS _ sP_O) _; rewrite subcomm_normal.
  have: X \subset V <*> X <*> P by rewrite mulgenC mulgenA sub_gen ?subsetUr.
  move/subset_trans; apply; apply: normal_norm.
  apply: char_norm_trans (pcore_char _ _) _.
  by rewrite /(_ <| _) normGR andbT /= commsgC subcomm_normal.
clear defH.
have[]: H :==: V * K * P /\ R0 :==: R; last (move/eqP=> defH; move/eqP=> defR).
  rewrite eq_sym !eqset_sub_card sR0R ?mul_subG //=; apply/andP.
  do 2!rewrite leqNgt andbC; rewrite -negb_or; apply: contra ntKP.
  rewrite -mulgA -norm_mulgenEr // -norm_mulgenEr; last first.
    by rewrite (subset_trans _ nVH) // gen_subG subUset sPH sKH.
  rewrite mulgenA; move/IHG; apply => //.
  by rewrite gen_subG subUset nKP (subset_trans sR0R). 
clear U defU sVU sUG nUG nUR hallK p'Ub nVU defVK sylV sPN.
clear sKR0_G nV_KR0 sK_KR0 sR0_KR0 solKR0 coK_R0 oKR0 hallK_R0 hallR0_K.
move: {sR0R} IHG oR0 ZCHR0 ntKR0 {nKR0} rR0 trCKR0_V oCVR0 trCP_R0 defP.
rewrite {R0}defR ltnn => IHG oR ZCHR ntKR rR trCKR_V oCVR trCP_R defP.
have{sylP} pP: p.-group P by case/and3P: sylP.
have{nVH} nVK: K \subset 'N(V) by exact: subset_trans nVH.
have defKP: K :=: [~: K, P].
  have sKP_K: [~: K, P] \subset K by rewrite commsgC subcomm_normal.
  apply/eqP; rewrite eq_sym eqset_sub_card sKP_K leqNgt.
  apply: contra ntKP => psKP_P; rewrite commGAA //; first last.
  - apply: solvableS solG; exact: subset_trans sKH sHG.
  - rewrite coprime_sym; exact: pnat_coprime pP p'K.
  rewrite IHG ?orbF //.
    rewrite gen_subG subUset /= {1}commsgC normGR.
    apply/normsP=> x Rx; rewrite -{1}(setTI [~: K, P]).
    rewrite -morphim_conj morphimR ?subsetT // !morphim_conj !setTI.
    by rewrite (normsP nKR) // (normsP nPR).
  rewrite /= norm_mulgenEr; last first.
    by rewrite norms_mulgen ?nVP // commsgC normGR.
  have oVK: #|V <*> K| = (#|V| * #|K|)%N.
    by rewrite norm_mulgenEr // coprime_card_mulG // (pnat_coprime pV).
  have trVK_P: trivg ((V <*> K) :&: P).
    apply: subset_trans VIP; rewrite -{1}(setIid P) setIA setSI //.
    have sV_VK: V \subset V <*> K by rewrite sub_gen ?subsetUl.
    rewrite (@subset_normal_Hall _ p _ (V <*> K)%G).
    - rewrite /psubgroup subsetIl; apply: pnat_dvd pP.
      by rewrite cardSg ?subsetIr.
    - by rewrite /pHall sV_VK pV -divgS // oVK divn_mulr.
    by rewrite /(V <| _) sV_VK gen_subG subUset normG.
  rewrite (card_mulG_trivP _ _ _) /=; last first.
    by apply: subset_trans trVK_P; rewrite setSI ?genS ?setUS.
  rewrite defH -(norm_mulgenEr nVK) (card_mulG_trivP _ _ trVK_P).
  rewrite ltn_pmul2r ?ltn_0group // oVK norm_mulgenEr ?(subset_trans sKP_K) //.
  rewrite coprime_card_mulG // ?ltn_pmul2l // (pnat_coprime pV) //.
  apply: pnat_dvd p'K; exact: cardSg.
have nrp: r != p.
  have: 'C_V(R) \subset H by apply: subset_trans sVH; exact: subsetIl.
  move/LaGrange=> oH; move: coHR; rewrite -oH oR oCVR coprime_mull; case/andP.
  by rewrite coprime_sym prime_coprime // dvdn_prime2.
have trCPR_K: trivg 'C_(P <*> R)(K).
  have solPR: solvable (P <*> R).
     apply: solvableS solG; rewrite gen_subG subUset sRG.
     by rewrite (subset_trans sPH sHG).
  have coPR: coprime #|P| #|R| by rewrite oR (pnat_coprime pP) ?pnatE.
  have nC_PR: 'C_(P <*> R)(K) <| P <*> R.
    rewrite /normal subsetIl normsI ?normG ?norms_cent //.
    by rewrite gen_subG subUset nKP nKR.
  have sP_PR: P \subset P <*> R by rewrite sub_gen ?subsetUl.
  have sR_PR: R \subset P <*> R by rewrite sub_gen ?subsetUr.
  have p'R: p^'.-group R by rewrite /pgroup oR pnatE.
  have sylPC: p.-Sylow('C_(P <*> R)(K)) 'C_P(K).
    rewrite -{2}(setIidPl sP_PR) -setIA (HallSubnormal _ nC_PR) //.
    rewrite /pHall sP_PR pP /= -divgS //= norm_mulgenEr //.
    by rewrite coprime_card_mulG // divn_mulr. 
  have hallRC: p^'.-Hall('C_(P <*> R)(K)) 'C_R(K).
    rewrite -{2}(setIidPl sR_PR) -setIA (HallSubnormal _ nC_PR) //.
    rewrite /pHall sR_PR /= -divgS //= norm_mulgenEr //.
    rewrite coprime_card_mulG // divn_mull // pnatNK; exact/andP.
  have trCP: trivg 'C_P(K).
    have: trivg (P :&: K) by apply coprime_trivg; exact: pnat_coprime pP p'K.
    by apply: subset_trans; rewrite -{1}(setIidPl sPH) -setIA setIS.
  have trCR: #|'C_R(K)| = 1%N.
    have: #|'C_R(K)| %| r by rewrite -oR cardSg ?subsetIl.
    case/primeP: pr_r => _ pr_r; move/pr_r; case/orP; move/eqP=> // oCR.
    case/commG1P: ntKR; apply/centsP; rewrite centsC; apply/setIidPl.
    by apply/eqP; rewrite eqset_sub_card oR oCR leqnn subsetIl.
  rewrite trivg_card -[#|_|](partnC p) // -(card_Hall sylPC).
  by rewrite -(card_Hall hallRC) trCR muln1 -trivg_card.
admit.
Qed.


