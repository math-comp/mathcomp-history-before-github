Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms group_perm automorphism normal commutators.
Require Import action cyclic center pgroups sylow dirprod schurzass hall. 
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

Lemma ZgroupS : forall G H, H \subset G -> Zgroup G -> Zgroup H. 
Proof.
move=> G H sHG; move/forallP=> zgG; apply/forallP=> V; apply/implyP.
case/SylowP=> p pr_p; case/and3P=> sVH.
case/(Sylow_superset (subset_trans sVH sHG))=> P sylP sVP _.
have:= zgG P; rewrite (p_Sylow sylP); exact: cyclicS.
Qed.

Lemma Zgroup_morphim : forall G, Zgroup G -> Zgroup (f @* G). 
Proof.
move=> G zgG; wlog sGD: G zgG / G \subset D.
  by rewrite -morphimIdom; apply; rewrite (ZgroupS _ zgG, subsetIl) ?subsetIr.
apply/forallP=> fV; apply/implyP.
case/SylowP=> p pr_p sylfV; have [P sylP] := Sylow_exists p G.
have [|z _ ->] := @Sylow_trans p _ _ (f @* P)%G _ _ sylfV.
  apply: morphim_pHall (sylP); exact: subset_trans (pHall_sub sylP) sGD.
rewrite cyclicJ cyclic_morphim // (implyP (forallP zgG P)) //.
by apply/SylowP; exists p.
Qed.

Lemma nil_Zgroup_cyclic : forall G, Zgroup G -> nilpotent G -> cyclic G.
Proof.
move=> G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G; rewrite ltnS => leGn.
move=> ZgG nilG; case: (leqP #|G| 1).
  rewrite -trivg_card; move/trivgP->; apply/cyclicP; exists (1 : gT).
  by rewrite cycle_unit.
move/prime_pdiv; set p := pdiv _ => pr_p.
case/dprodGP: (nilpotent_pcoreC p nilG) => [[_ _ _ _ defG Cpp'] _].
have: cyclic 'O_p^'(G).
  have sp'G := pcore_sub p^' G.
  apply: IHn (leq_trans _ leGn) (ZgroupS sp'G _) (nilpotentS sp'G _) => //.
  rewrite proper_card // properEneq sp'G andbT; case: eqP => //= def_p'.
  by have:= pcore_pgroup p^' G; rewrite def_p' /pgroup p'natE ?dvdn_pdiv.
have: cyclic 'O_p(G).
  have:= forallP ZgG 'O_p(G)%G.
  by rewrite (p_Sylow (nilpotent_pcore_Hall p nilG)).
case/cyclicP=> x def_p; case/cyclicP=> x' def_p'.
apply/cyclicP; exists (x * x'); rewrite -{}defG def_p def_p' cycle_mul //.
  by apply: (centsP Cpp'); rewrite (def_p, def_p') cyclenn.
rewrite /order -def_p -def_p' (@pnat_coprime p) //; exact: pcore_pgroup.
Qed.

Lemma Phi_char : forall G, 'Phi(G) \char G. Admitted.

Lemma maximal_p_group : forall (p : nat) (P M : {group gT}),
  p.-group P -> maximal M P -> M <| P /\ #|P / M| = p.
Proof.
move=> p P M pP; case/maximalP; case/andP=> sMP sPM maxM.
have nMP: P \subset 'N(M).
  have:= subsetIl P 'N(M); rewrite subEproper.
  case/predU1P; [by move/setIidPl | move/maxM => /= SNM].
  case/negP: sPM; rewrite (nilpotent_sub_norm (pgroup_nil pP) sMP) //.
  by rewrite SNM // subsetI sMP normG.
have snMP: M <| P by exact/andP.
have: p.-group (P / M) by exact: morphim_pgroup.
case/pgroup_1Vpr=> [/= PM1|[p_pr _ [k oMp]]]. 
  by case/negP: sPM; rewrite -trivg_quotient ?PM1.
have{k oMp}: p %| #|P / M| by rewrite oMp dvdn_mulr.
case/Cauchy=> // Mx; rewrite /order -cycle_subG.
case/inv_quotientS=> [|L /= ->{Mx} sML]; first exact/andP.
rewrite subEproper; case/predU1P=> [-> // | sLP].
by rewrite (maxM L) // trivial_quotient cards1 => p1; rewrite -p1 in p_pr.
Qed.

Lemma coprime_cent_Phi : forall H G,
  coprime #|H| #|G| -> [~: H, G] \subset 'Phi(G) ->  H \subset 'C(G).
Admitted.

Lemma Fitting_def : forall G H,
  H <| G -> nilpotent H -> H \subset 'F(G).
Admitted.

Lemma Fitting_nilpotent : forall G, nilpotent 'F(G).
Admitted.

Lemma solvable_self_cent_Fitting : forall G,
  solvable G -> 'C_G('F(G)) \subset 'F(G).
Admitted.

Lemma Fitting_char : forall G, 'F(G) \char G.
Admitted.

Lemma Fitting_normal : forall G, 'F(G) <| G.
Proof. move=> G; apply: char_normal; exact: Fitting_char. Qed.

Lemma pcore_Fitting : forall pi G, 'O_pi('F(G)) \subset 'O_pi(G).
Proof.
move=> pi G; rewrite subset_pcore ?pcore_pgroup //.
exact: char_normal_trans (pcore_char _ _) (Fitting_normal _).
Qed.

Lemma p_core_Fitting : forall (p : nat) G, 'O_p('F(G)) = 'O_p(G).
Proof.
move=> p G; apply/eqP; rewrite eqset_sub pcore_Fitting.
rewrite subset_pcore ?pcore_pgroup //.
apply: normalS (normal_sub (Fitting_normal _)) (pcore_normal _ _).
exact: Fitting_def (pcore_normal _ _) (pgroup_nil (pcore_pgroup _ _)).
Qed.

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
  have:= nHR; rewrite -commg_subr commGC => sHR_R.
  have:= sHR_R; rewrite subEproper; case/predU1P=> [-> -> //|s'HR_H _].
  rewrite commGAA //; last exact: solvableS solG.
  apply: IHG => //; last by rewrite proper_card.
  apply: subset_trans (normal_norm (commg_normal H R)).
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
  have solG': solvable (G / X) by exact: quotient_sol.
  have oddG': odd #|G / X|.
    move: oddG; rewrite !odd_2'nat; exact: morphim_pgroup.
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
  by rewrite normal_norm // (char_normal_trans (pcore_char _ _)).
move defV: 'F(H)%G => V.
have charV: V \char H by rewrite -defV Fitting_char.
have nVG: G \subset 'N(V) by rewrite normal_norm ?(char_normal_trans charV).
have sVH: V \subset H by rewrite normal_sub ?char_normal.
have defVp: V :=: 'O_p(H).
  rewrite -defV -(nilpotent_pcoreC p (Fitting_nilpotent H)) // p_core_Fitting.
  rewrite ['O_p^'('F(H))](trivgP _ _) ?dprodg1 //.
  exact: subset_trans (pcore_Fitting _ _) Op'_H.
have pV: p.-group V by rewrite defVp pcore_pgroup.
have sCV_V: 'C_H(V) \subset V.
  rewrite -defV solvable_self_cent_Fitting //; exact: solvableS solG.
wlog abV: / p.-abelem V.
  case/orP: (orbN (trivg 'Phi(V))) => [trPhi -> // | ntPhi _].
    apply/p_abelemP=> //; split=> [|x Vx].
      apply/centsP; apply/commG1P; apply: subset_trans trPhi.
      apply/bigcap_inP=> M; case/predU1P=> [->|]; first exact: der1_subG.
      case/(maximal_p_group pV)=> //; case/andP=> sMV nMV oVM.
      have{oVM} VMcyc: cyclic (V / M) by rewrite cyclic_prime ?oVM.      
      rewrite -quotient_cents2 //; apply/centsP.
      by case/cyclicP: VMcyc => x ->; exact: commute_cycle_com.
    apply/set1P; rewrite -[[set 1]](trivgP _ trPhi).
    apply/bigcapP=> M; case/predU1P=> [->|]; first exact: groupX.
    case/(maximal_p_group pV)=> //; case/andP=> sMV nMV oVM.
    have Nx: x \in 'N(M) by exact: (subsetP nMV).
    apply: coset_idr; rewrite (groupX, morphX) //= -oVM.
    by apply/eqP; rewrite -order_dvd order_dvd_g ?mem_imset // inE Nx.
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
    rewrite trivg_card (@pnat_1 p #|_|) //= defW //.
    exact: morphim_pgroup.
  apply/pgroupP=> q pr_q; case/Cauchy=> // x Wx oxq; apply/idPn=> /= neqp.
  suff: <[x]> \subset V.
    rewrite gen_subG sub1set => Vx.
    by move/pgroupP: pV neqp => /= -> //; rewrite -oxq order_dvd_g.
  apply: subset_trans sCV_V; rewrite subsetI cycle_subG; apply/andP; split.
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
  rewrite subsetI andbC commg_subr cycle_subG; apply/andP; split.
    by apply: subsetP Wx; apply: subset_trans (subset_trans sWH _) nVG.
  move: nWH; rewrite -commg_subr commGC; apply: subset_trans.
  by rewrite commgSS // cycle_subG //.
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
  exact: char_normal_trans (Fitting_char _) (morphim_normal _ _).
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
have p'Ub: p^'.-group 'F(H / V).
  rewrite -['F(H / V)](nilpotent_pcoreC p (Fitting_nilpotent _)).
  rewrite ['O_p(_)](trivgP _ _) ?dprod1g ?pcore_pgroup // defVp.
  exact: subset_trans (pcore_Fitting _ _) (trivg_pcore_quotient _ _).
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
  rewrite -{1}(Hall_Frattini_arg _ nUH hallK); last exact: solvableS solG.
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
  have sol_HV : solvable (H / V). 
    by apply: quotient_sol; apply: (solvableS sHG).
  have qPV: P / V \subset 'C_(H / V)('F(H / V)).
    rewrite defU subsetI; apply/andP; split; first by apply:morphimS.
    rewrite defVK quotient_mulgr; apply: quotient_cents2r; rewrite commGC.
    case/trivgP: tKP; move ->; exact: sub1G.
  have sPU: P \subset U.
    rewrite defVK -quotientSK // -(quotient_mulgr _ K) -defVK -defU.
    exact: subset_trans qPV (solvable_self_cent_Fitting sol_HV).
  rewrite (subset_normal_Hall _ sylV); last exact/andP.
  by rewrite /psubgroup ?sPU (pHall_pgroup sylP).
have{sylVP} dp: [~: V, K] \x 'C_V(K) :=: V.
  apply: sym_eq; apply: comm_center_dir_prod; last by case/p_abelemP: abV.
    exact: subset_trans sKU nVU.
  exact: pnat_coprime pV p'K.
have trVeq: trivg 'C_V(K) \/ 'C_V(K) = V.
  apply: (nondecV _  [~: V, K]); first by rewrite dprodC.
  rewrite -eqHR_G defH -mulgA mul_subG //.
    by rewrite subsetI commg_norml cents_norm // centsC {1}eqVC setIAC subsetIr.
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
  by rewrite -commg_subr commGC -{2}Vcomm subset_refl.
have VIN: trivg (V :&: 'N_H(K)) by rewrite setIA (setIidPl sVH) eqcn.
have VIP: trivg (V :&: P).
  apply: subset_trans VIN; apply: setIS; exact: (subset_trans sPN).
have nVN: 'N_H(K) \subset 'N(V) by rewrite (subset_trans _ nVH) ?subsetIl.
have defK: K :=: 'F('N_H(K)).
  have isoV: 'injm (restrm nVN (coset V)).
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
  have cycK: cyclic K by rewrite nil_Zgroup_cyclic // defK Fitting_nilpotent.
  have AcycK : abelian (Aut K).
    case/cyclicP: cycK => x ->; exact: aut_cycle_commute.
  have sNR_K: [~: 'N_H(K), R] \subset K.
    apply: subset_trans sCKK; rewrite subsetI; apply/andP; split.
      apply: subset_trans (commSg R (subsetIl _ _)) _.
      by rewrite commGC commg_subr.
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
  rewrite subsetI {1}commGC !commg_subr nKR0.
  apply: (subset_trans sK_KR0); case/andP: nC_KR0 => _; apply: etrans.
  congr (_ \subset 'N(_)); apply/eqP.
  by rewrite eq_sym eqset_sub_card sC_R0 oCr /= oR0.
have oCVR0: #|'C_V(R0)| = p.
  case trCVR0: (trivg 'C_V(R0)).
    case/negP: ntKR0; have: trivg 'C_K(V); last apply: subset_trans.
      by apply: subset_trans trCKR0_V; rewrite setSI.
    rewrite commGC; apply: three_dot_four abV nV_KR0 _ trCVR0 => //.
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
  rewrite cycle_subG; apply/andP; split; first by case/setIP: Cx.
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
    apply/set1P; rewrite -defCy1 inE cycle_subG y_x /=; exact/eqP.
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
      rewrite -{1}((_ =P [~: _, _]) VXPR_1) quotient_pseries.
      exact: pcore_pgroup.
    exact: pcore_normal.
  have: trivg (K :&: 'O_p([~: (V <*> X) <*> P, R0])).
    apply: coprime_trivg; rewrite coprime_sym (pnat_coprime _ p'K) //.
    exact: pcore_pgroup.
  apply: subset_trans; rewrite subsetI; apply/andP; split.
    by apply: subset_trans (commSg _ sXK) _; rewrite commGC commg_subr.
  apply: subset_trans (commgS _ sP_O) _; rewrite commg_subr.
  have: X \subset V <*> X <*> P by rewrite mulgenC mulgenA sub_gen ?subsetUr.
  move/subset_trans; apply; apply: normal_norm.
  apply: char_normal_trans (pcore_char _ _) _.
  by rewrite /(_ <| _) commg_norml andbT /= commGC commg_subr.
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
have oVK: #|V <*> K| = (#|V| * #|K|)%N.
  by rewrite norm_mulgenEr // coprime_card_mulG // (pnat_coprime pV).
have trVK_P: trivg ((V <*> K) :&: P).
  apply: subset_trans VIP; rewrite -{1}(setIid P) setIA setSI //.
  have sV_VK: V \subset V <*> K by rewrite sub_gen ?subsetUl.
  have sylV: p.-Sylow(V <*> K) V.
    by rewrite pHallE sV_VK oVK partn_mul 1?part_pnat ?part_p'nat ?muln1 ?eqxx.
  rewrite (subset_normal_Hall _ sylV).
    rewrite /psubgroup subsetIl; apply: pgroupS pP; exact: subsetIr.
  by rewrite /normal sV_VK gen_subG subUset normG.
have oH: (#|H| = #|V| * #|K| * #|P|)%N.
  by rewrite defH -(norm_mulgenEr nVK) -oVK (card_mulG_trivP _ _ trVK_P).
have{IHG} IHK: forall X : {group gT},
  P <*> R \subset 'N(X) -> X \subset K -> X :=: K \/ X \subset 'C(P).
- move=> X nX_PR sXK.
  have:= sXK; rewrite subEproper; case/predU1P; first by left.
  move/proper_card => ltXK; right; apply/centsP; apply/commG1P.
  apply: IHG => //; move: nX_PR; rewrite mulgen_subG; case/andP=> nXP _.
  rewrite [_ <*> _]norm_mulgenEr; last first.
    by rewrite norms_mulgen ?nVP // commGC commg_norml.
  rewrite (card_mulG_trivP _ _ _) /=; last first.
    by apply: subset_trans trVK_P; rewrite setSI ?genS ?setUS.
  rewrite oH ltn_pmul2r ?ltn_0group // norm_mulgenEr ?(subset_trans sXK) //.
  rewrite orbF coprime_card_mulG // ?ltn_pmul2l // (pnat_coprime pV) //.
  exact: pgroupS p'K.
have defKP: K :=: [~: K, P].
  have sKP_K: [~: K, P] \subset K by rewrite commGC commg_subr.
  case: (IHK _ _ sKP_K) => //.
    by rewrite gen_subG subUset /= {1}commGC commg_norml normsR.
  move/centsP; move/commG1P; move/trivgP=> /= KP1.
  case/trivgP: ntKP; rewrite /= commGAA //.
    by rewrite coprime_sym (pnat_coprime pP).
  apply: solvableS solG; exact: subset_trans sKH sHG.
have nrp: r != p.
  move: coHR; rewrite oR coprime_sym prime_coprime -?p'natE // => r'H.
  have sCH: 'C_V(R) \subset H by apply: subset_trans sVH; exact: subsetIl.
  by rewrite eq_sym; apply: (pgroupP _ _ (pgroupS sCH r'H)); rewrite ?oCVR.
have nKPR: P <*> R \subset 'N(K) by rewrite mulgen_subG nKP.
have trCPR_K: trivg 'C_(P <*> R)(K).
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
have [q q_pr qKdv]: exists2 q, prime q & q %| #|K|.
  exists (pdiv #|K|); last exact: dvdn_pdiv.
  rewrite prime_pdiv // ltnNge -trivg_card; apply: contra ntKP.
  by apply: subset_trans; rewrite commGC commg_subr.
have nqp: q != p by exact: (pgroupP _ _ p'K).
have nrq: r != q by rewrite eq_sym; exact: (pgroupP _ _ r'K).
have{defK} qK: q.-group K.
  have IHpi: forall pi, 'O_pi(K) = K \/ 'O_pi(K) \subset 'C(P).
    move=> pi; apply: IHK (pcore_sub _ _).
    by apply: char_norm_trans (pcore_char _ _) _; rewrite mulgen_subG nKP.
  case: (IHpi q) => [<-| cPKq]; first exact: pcore_pgroup.
  have{defK} nilK: nilpotent K by rewrite defK Fitting_nilpotent.
  case/dprodGP: (nilpotent_pcoreC q nilK) => [[_ _ _ _ defK _] _].
  case/commG1P: ntKP; apply/centsP; rewrite -{}defK mul_subG //.
  case: (IHpi q^') => // defK; case/idPn: qKdv.
  rewrite -p'natE // -defK; exact: pcore_pgroup.
pose K' := 'L_1(K)%G; have nK'K: K' <| K := der_normal K 0.
have nK'PR: P <*> R \subset 'N(K').
  exact: char_norm_trans (der_char K 1) nKPR.
have iK'K: trivg 'C_(P <*> R / K')(K / K') -> #|K / K'| > q ^ 2.
  have: q.-group (K / K') by exact: morphim_pgroup qK.
  case/p_natP=> // k oK; rewrite oK ltn_exp2l ?prime_gt1 // ltnNge.
  move=> sCK'; apply: contra ntKP => lek2.
  suff trP: trivg [~: P, R] by rewrite defP [[~: P, R]](trivgP _ trP) commG1.
  have coK_PR: \pi(#|K|)^'.-group (P <*> R).
    rewrite norm_mulgenEr // pgroupM /pgroup -!coprime_pi' // coprime_sym.
    by rewrite (pnat_coprime pP) // coprime_sym oR prime_coprime // -p'natE.
  suff sPR_K': [~: P, R] \subset K'.
    rewrite -(setIidPl sPR_K') coprime_trivg //.
    apply: pnat_coprime (pgroupS (normal_sub nK'K) p'K).
    by apply: pgroupS pP; rewrite /= commGC commg_subr.
  rewrite -quotient_cents2 ?(char_norm_trans (der_char K 1)) //.
  rewrite (sameP centsP commG1P); apply: subset_trans sCK'.
  rewrite subsetI comm_subG ?morphimS ?(mulgen_subl, mulgen_subr) //.
  rewrite -ker_conj_aut -sub_morphim_pre; last first.
    by rewrite comm_subG ?morphim_norms.
  rewrite morphimR ?morphim_norms //.
  suffices: abelian (Aut (K / K')).
    move/centsP; move/commG1P; apply: subset_trans.
    by apply: commgSS; apply/subsetP=> fx;
       case/imsetP=> x Nx ->; apply: Aut_aut_of.
  case cycK: (cyclic (K / K')).
    case/cyclicP: cycK => x ->; exact: aut_cycle_commute.
  case: k lek2 oK => [|[|[|//]]] _ oK.
  - case/cyclicP: cycK; exists (1 : coset_of K'); rewrite cycle_unit.
    by apply/trivgP; rewrite trivg_card oK.
  - by case/idP: cycK; rewrite cyclic_prime // oK expn1.
  have [lt1q dv_q] := primeP q_pr.
  have: q %| #|K / K'| by rewrite oK dvdn_mulr.
  case/Cauchy=> // u Ku ou; have: <[u]> \proper K / K'.
    by rewrite properEcardlt cycle_subG Ku oK [#|_|]ou -{1}(expn1 q) ltn_exp2l.
  case/andP=> _; case/subsetPn=> v Kv uv.
  have:= Kv; rewrite -cycle_subG; move/cardSg; rewrite oK.
  case/dvdn_pfactor=> [//|[|[|[|//]]] _ ov]; last 1 first.
  - case/cyclicP: cycK; exists v; apply/eqP.
    by rewrite eq_sym eqset_sub_card oK ov cycle_subG Kv leqnn.
  - by rewrite -(expg1 v) -[1%N]ov order_expn1 group1 in uv.
  have abK: abelian (K / K').
    suff ->: K / K' = 'Z(K / _) by rewrite /abelian subIset // centsC subsetIr.
    have:= center_sub (K / K'); move/cardSg; rewrite oK.
    case/dvdn_pfactor=> [//|[|[|[|//]]] _ oZ].
    - have: q.-group (K / K') by exact: morphim_pgroup.
      move/trivg_center_pgroup; move/implyP; rewrite !trivg_card oZ oK /=.
      by rewrite leqNgt -{1}(expn0 q) ltn_exp2l.
    - apply: center_cyclic_abelian (cyclic_prime _).
      rewrite card_quotient ?normal_norm ?center_normal //.
      by rewrite -divgS ?subsetIl // oZ oK divn_mull // muln1 ltnW.
    by symmetry; apply/eqP; rewrite eqset_sub_card oK oZ subsetIl leqnn.
  have cuv: commute u v by apply: (centsP abK).
  have truv: trivg (<[u]> :&: <[v]>).
    have sI := subsetIr <[u]> <[v]>.
    have:= cardSg sI; rewrite ov expn1; move/dv_q; case/orP; move/eqP=> oI.
      by rewrite trivg_card oI.
    have:= sI; rewrite subEproper properEcardlt oI ov expn1 ltnn andbF orbF.
    by rewrite (sameP eqP setIidPr) cycle_subG (negPf uv).
  have defK: K / K' = <[u]> * <[v]>.
    apply/eqP; rewrite eq_sym eqset_sub_card mul_subG ?cycle_subG // oK.
    by rewrite (card_mulG_trivP _ _ truv) {1}[#|_|]ou ov leqnn.
  have{ov} ov: #[v] = q by rewrite expn1 in ov.
  admit. (* at this point, we need Theorem 2.6 from B & G *)
case abelK: (abelian K); last first.
  have [dCKP sK' dPhiK]:
    [/\ 'C_K(P) = 'Z(K), K^`(1) = 'Z(K) & 'Phi(K) = 'Z(K)].
  + (* C_K(P) = K^(1) = Phi(K)  = Z(K) by Asch. 24.7 *) admit.
  have xKq: exponent K %| q.
    have [Q [chQ xQq qCKQ]]: exists Q : {group gT},
      [/\ Q \char K, exponent Q %| q & q.-group 'C_(Aut K | 'P)(Q)].
      (* B & G 1.13 *) admit.
    have: P <*> R \subset 'N(Q) by exact: char_norm_trans nKPR.
    have sQK := char_sub chQ.
    case/IHK=> // [<- //|cQP]; case/commG1P: ntKP; apply/centsP.
    rewrite centsC -ker_conj_aut -sub_morphim_pre // -[_ @* _]setIid.
    apply: coprime_trivg; apply: pnat_coprime (morphim_pgroup _ pP) _.
    apply: (@subd_pnat q) => [q' _|]; first by move/eqnP->.
    apply: pgroupS qCKQ; apply/subsetP=> a; case/morphimP=> x _ Px ->{a}.
    rewrite inE /= Aut_aut_of; apply/astabP=> y Qy.
    rewrite /= /aperm norm_conj_autE ?(subsetP sQK) ?(subsetP nKP) //.
    by rewrite /conjg (centsP cQP y) ?mulKg.
  have trCPR_K': trivg 'C_(P <*> R / 'Z(K))(K / 'Z(K)).
    rewrite -dPhiK. admit. (* B & G Theorem 1.8 *)
  have nZP := char_norm_trans (center_char _) nKP.
  have nZR := char_norm_trans (center_char _) nKR.
  have nZK := normal_norm (center_normal K).
  have solK: solvable K := nilpotent_sol (pgroup_nil qK).
  have dCKR': 'C_K(R) / 'Z(K) = 'C_(K / 'Z(K))(R / 'Z(K)).
    rewrite coprime_quotient_cent_weak ?center_normal //.
    by rewrite coprime_sym (pnat_coprime rR r'K).
  have abK': q.-abelem (K / 'Z(K)).
    rewrite -dPhiK. admit. (* B & G 1.7 or above *)    
  case ntCK'_R: (trivg 'C_(K / 'Z(K))(R / 'Z(K))).
    have qZ: q.-group 'Z(K) by exact: pgroupS (center_sub K) qK.
    have q'P: q^'.-group P.
      by apply: subd_pnat pP => p' _; move/eqnP->; rewrite eq_sym in nqp.
    have coZP: coprime #|'Z(K)| #|P| := pnat_coprime qZ q'P.
    suff sPZ: P \subset 'Z(K).
       case/negP: ntKP; rewrite (trivgP P _) ?commG1 //.
       by rewrite -(setIidPr sPZ) coprime_trivg.
    rewrite -trivg_quotient // defP commGC quotientE morphimR // -?quotientE.
    have: trivg 'C_(P /'Z(K))(K / 'Z(K)); last apply: subset_trans.
      exact: subset_trans (setSI _ (morphimS _ (mulgen_subl P R))) _.
    move: ntCK'_R; have: ~~ (q %| #|P <*> R / 'Z(K)|).
      rewrite -p'natE //; apply: morphim_pgroup.
      by rewrite /= norm_mulgenEr // pgroupM q'P /pgroup oR pnatE.
    have sPRG: P <*> R \subset G by rewrite mulgen_subG sRG (subset_trans sPH).
    have coPR: coprime #|P| #|R| by rewrite (pnat_coprime pP) // oR pnatE.
    apply: three_dot_four abK' _.
    - exact: quotient_sol (solvableS _ solG).   
    - rewrite !odd_2'nat in oddG *; apply: morphim_pgroup; exact: pgroupS oddG.
    - by rewrite morphim_normal // /normal mulgen_subl mulgen_subG normG.
    - rewrite morphim_Hall // /Hall -divgS ?mulgen_subl //= norm_mulgenEr //.
      by rewrite coprime_card_mulG // divn_mulr.
    - apply/complgP; rewrite -morphimMl //= norm_mulgenEr // ?coprime_trivg //.
      apply: pnat_coprime (morphim_pgroup _ pP) (morphim_pgroup _ _).
      by rewrite /pgroup oR pnatE.
    - rewrite card_morphim ker_coset (setIidPr _) // -indexgI.
      rewrite [R :&: _](trivgP _ (coprime_trivg _)) ?indexg1 ?oR //.
      rewrite -oR (pnat_coprime rR) //; exact: (pgroupS (subsetIl _ _)).
    by apply: morphim_norms; rewrite mulgen_subG nKP.
  have sKR_C_K': 'C_K(R) :&: [~: K, R] \subset 'Z(K).
    rewrite -trivg_quotient; last by rewrite -setIA subIset ?nZK.
    apply: subset_trans (morphimI _ _ _) _.
    rewrite morphimR; first 1 [rewrite -!quotientE dCKR'] || by [].
    rewrite setIC comm_center_triv; first exact: trivg1.
    - exact: morphim_norms.
    - rewrite coprime_sym (pnat_coprime (morphim_pgroup _ rR)) //.
      exact: morphim_pgroup.
    by case/andP: abK'; case/andP.
  have sKR_K: [~: K, R] \proper K.
    rewrite properE {1}commGC commg_subr nKR /=.
    apply/negP=> sK_KR; case/idP: ntCK'_R.
    rewrite -dCKR' trivg_quotient; last by rewrite subIset // nZK.
    by rewrite -{1}(setIidPl sK_KR) setIAC.
  rewrite -dCKR' trivg_quotient // in ntCK'_R *; last first.
    by rewrite subIset // normal_norm // center_normal.
  have oCKR: #|'C_K(R)| = q.
    have: cyclic 'C_K(R).
      apply: nil_Zgroup_cyclic; first exact: ZgroupS (setSI _ _) ZCHR.
      apply: pgroup_nil (pgroupS _ qK); exact: subsetIl.
    case/cyclicP=> x CKRx.
    have Kx: x \in K by rewrite -cycle_subG -CKRx subsetIl.
    have{Kx}:= dvdn_trans (dvdn_exponent Kx) xKq; rewrite /order CKRx.
    case: (primeP q_pr) => _ dvq; move/dvq; case/orP; move/eqnP=> // x1.
    by rewrite CKRx [<[x]>](trivgP _ _) ?sub1G // trivg_card x1 in ntCK'_R.
  have trCKR_Z: trivg ('C_K(R) :&: 'Z(K)).
    have:= cardSg (subsetIl 'C_K(R) 'Z(K)); rewrite trivg_card oCKR.
    case: (primeP q_pr) => _ dvq; move/dvq; case/predU1P=> [-> //| Iq].
    case/setIidPl: ntCK'_R; apply/eqP; rewrite eqset_sub_card subsetIl.
    by rewrite oCKR (eqnP Iq) leqnn.
  have trKR_CR: trivg ('C_[~: K, R](R)).
    rewrite -(setIidPl (proper_sub sKR_K)) -setIA setIC.
    rewrite -(setIidPl sKR_C_K') -setIA setICA.
    apply: subset_trans trCKR_Z; exact: subsetIr.
  have abKR: abelian [~: K, R].
    apply/centsP; apply/commG1P.
    have: trivg 'C_[~: K, R](V); last apply: subset_trans.
      have sKRH: [~: K, R] \subset H :=  subset_trans (proper_sub sKR_K) sKH.
      rewrite -(setIidPl sKRH) -setIA -eqVC setIC; apply: subset_trans VIN.
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
    - by apply/complgP; rewrite setIC coprime_trivg //= norm_mulgenEr.
    exact: subset_trans nVG.
  case nKR_P: (P \subset 'N([~: K, R])).
    have{nKR_P}: P <*> R \subset 'N([~: K, R]).
      by rewrite mulgen_subG nKR_P commGC commg_norml.
    case/IHK=> [|dKR|cP_KR]; first exact: proper_sub.
      by case/eqP: (proper_neq sKR_K).
    have{cP_KR} cK'_R: R / 'Z(K) \subset 'C(K / 'Z(K)).
      by rewrite quotient_cents2r //= -dCKP commGC subsetI proper_sub.
    case/negP: ntKR; apply/commG1P; apply/centsP; rewrite centsC.
    admit. (* B & G 1.18 *)
  case/subsetPn: nKR_P => x Px; move/normP; move/eqP=> nKRx.
  have iKR: #|K : [~: K, R]| = q.
    rewrite -divgS ?proper_sub // {1}(comm_center_prod nKR) //; last first.
      by rewrite coprime_sym (pnat_coprime rR).
    rewrite (card_mulG_trivP _ _ _) ?divn_mulr //.
    by apply: subset_trans trKR_CR; rewrite setICA subsetIr.
  pose IKRx := ([~: K, R] :&: [~: K, R] :^ x)%G.
  have sKRx_K: [~: K, R] :^ x \subset K.
    by rewrite -{2}(normsP nKP x Px) conjSg proper_sub.
  have nKR_K: K \subset 'N([~: K, R]) by exact: commg_norml.
  have iIKRx: #|[~: K, R] : IKRx| = q.
    have: #|[~: K, R] : IKRx| %| q.
      rewrite -divgS ?subsetIl // -{1}(card_conjg _ x) /= setIC divgI -iKR.
      rewrite -!card_quotient ?(subset_trans sKRx_K) //.
      apply: cardSg; exact: morphimS.
    case/primeP: q_pr => _ dv_q; move/dv_q; case/orP; move/eqnP=> // iIKR_1.
    case/negP: nKRx; rewrite eq_sym eqset_sub_card card_conjg leqnn andbT.
    rewrite (sameP setIidPl eqP) eqset_sub_card subsetIl /=.
    by rewrite -(LaGrange (subsetIl _ ([~: K, R] :^ x))) iIKR_1 muln1 /=.
  have dKx: K :=: [~: K, R] * [~: K, R] :^ x.
    apply/eqP; rewrite eq_sym eqset_sub_card mul_subG // ?proper_sub //.
    rewrite -(leq_pmul2r (ltn_0group IKRx)) card_mulG card_conjg.
    rewrite -(LaGrange (proper_sub sKR_K)) iKR -mulnA leq_pmul2l //.
    by rewrite -iIKRx mulnC LaGrange /= ?subsetIl.
  have sIKRxZ: IKRx \subset 'Z(K).
    rewrite subsetI subIset; last by rewrite sKRx_K orbT.
    rewrite /abelian in abKR.
    by rewrite dKx centMG centJ subsetI !subIset // ?conjSg ?abKR ?orbT.
  suffices: #|K / 'Z(K)| <= q ^ 2.
    by rewrite leqNgt -sK' iK'K // [K' : set _]sK'.
  rewrite card_quotient ?normal_norm ?center_normal //.
  rewrite -mulnn -{1}iKR -iIKRx LaGrange_index ?subsetIl ?proper_sub //.
  by rewrite dvdn_leq // indexgS.
have trCK_P: trivg 'C_K(P).
  apply/trivgP; rewrite -(comm_center_triv nKP) -?defKP ?setIA ?setIid //.
  by rewrite coprime_sym (pnat_coprime pP).
have abelemK: q.-abelem K.
  rewrite /p_abelem qK andbC; apply/abelem_Ohm1P; rewrite ?(pgroup_p qK) //.
  case/IHK: (Ohm_sub 1 K) => // [|cPK1].
    by apply: char_norm_trans (Ohm_char 1 K) _; rewrite mulgen_subG nKP.
  case/Cauchy: qKdv => // x Kx oxq.
  have: x \in 'C_K(P).
    rewrite inE Kx (subsetP cPK1) //= (OhmE 1 qK) ?mem_gen // inE Kx.
    by rewrite /= -oxq expn1 order_expn1.
  by move/(subsetP trCK_P); move/set1P=> x1; rewrite -oxq x1 order1 in q_pr.
have{iK'K} oKq2: q ^ 2 < #|K|.
  have K'1: K' :=: 1 by apply/trivgP; apply/commG1P; apply/centsP.
  rewrite -indexg1 -K'1 -card_quotient ?normal_norm // iK'K // K'1.
  have inj1 := coset1_injm gT.
  rewrite /trivg /= -(trivial_quotient 1) {3}/quotient -(morphpre_invm inj1).
  rewrite -sub_morphim_pre; last by rewrite subIset // morphimS ?norms1.
  rewrite morphimGI ?ker_invm ?sub1G // morphim_invm ?norms1 //.
  apply: subset_trans (setIS _ _) trCPR_K.
  by rewrite -{2}[K : set _](morphim_invm inj1) ?norms1 // morphim_cent.
pose Vi (Ki : {group gT}) := 'C_V(Ki)%G.
pose mxK := [set Ki : {group gT} | maximal Ki K && ~~ trivg (Vi Ki)].
have nKiK: forall Ki, Ki \in mxK -> Ki <| K.
  by move=> Ki; rewrite inE; case/andP; case/(maximal_p_group qK).
have nViK: forall Ki, Ki \in mxK -> K \subset 'N(Vi Ki).
  by move=> Ki mxKi; rewrite normsI // norms_cent // normal_norm // nKiK.
have gen_mxK: << \bigcup_(Ki \in mxK) Vi Ki >> = V.
  admit. (* B & G, Prop. 1.16 *)
have dprod_V : \big[direct_product/1]_(Ki \in mxK) Vi Ki = V.

  pose dp (sM : {set _}) := \big[direct_product/1]_(Ki \in sM) Vi Ki.
  have dp0: dp set0 = 1 by rewrite /dp big_pred0 => // Ki; rewrite inE.
  pose sM0 : {set {group gT}} := set0.
  have: exists sM, group_set (dp sM) && (sM \subset mxK).
    by exists sM0; rewrite sub0set dp0 groupP.
  case/ex_maxset=> sM; case/maxsetP; case/andP=> gW ssM max_sM.
  move defW: (Group gW) => W; move/(congr1 val): defW => /= defW.
  move: ssM; rewrite subEproper /= -{2}gen_mxK.
  case/predU1P=> [<-|]; first by rewrite (bigdprodEgen defW).
  case/andP=> ssM; case/subsetPn=> Kj mxKj nsKj; case/negP: (nsKj).
  suffices trWVj: trivg 'C_W(Kj).
    rewrite -(max_sM _ _ (subsetUr [set Kj] _)); first by rewrite inE set11.
    rewrite subUset sub1set mxKj ssM /= andbT.
    rewrite /dp -setU1E (bigD1 Kj) ?setU11 //=.
    suff: group_set (Vi Kj \x dp sM).
      apply: etrans; congr (group_set (_ \x _)); apply: eq_bigl => M1.
      by rewrite !inE andbC; case: eqP => // ->; rewrite (negPf nsKj).
    have cWM: Vi Kj \subset 'C(W).
      rewrite subIset // centsC; apply/orP; left.
      case/andP: abV; case/andP=> abV _ _; apply: subset_trans abV.
      move/bigdprodEgen: defW => <-; rewrite gen_subG.
      apply/bigcup_inP=> M1 _; exact: subsetIl.
    rewrite defW dprodGE //; first by rewrite -cent_mulgenE ?groupP.
    by apply: subset_trans trWVj; rewrite setIC setICA subsetIr.
  have: exists mM, trivg 'C_(dp mM)(Kj) && (mM \subset sM).
    by exists sM0; rewrite sub0set dp0 andbT; exact: subsetIl.
  case/ex_maxset=> mM; case/maxsetP; case/andP=> trVm; rewrite subEproper.
  rewrite -defW; case/predU1P=> [<- //|]; case/andP=> smM.
  case/subsetPn=> Ki sKi nmKi max_mM.
  case/negP: (nmKi); rewrite -sub1set; apply/setUidPr.
  apply: max_mM (subsetUr _ _); rewrite subUset sub1set sKi smM !andbT -setU1E.
  have:= defW; rewrite {1}/dp (bigID [pred Kk \in Ki |: mM]) /=.
  case/dprodGP=> [[W' _ defW' _ _ _] _].
  rewrite (_ : reducebig _ _ _ _ _ = dp (Ki |: mM)) in defW'; last first.
    apply: eq_bigl => Kk; rewrite -in_setI (setIidPr _) //.
    by rewrite setU1E subUset sub1set sKi smM.
  rewrite defW'; move: defW'; rewrite /dp (bigD1 Ki) ?setU11 //=.
  rewrite (_ : reducebig _ _ _ _ _ = dp mM); last first.
    apply: eq_bigl => Kk; rewrite !inE andbC; case: eqP => // ->.
    by rewrite (negPf nmKi).
  case/dprodGP=> [[_ W2 _ defW2 <-]]; rewrite defW2 => cViW2 trViW2.
  apply/subsetP=> uv; case/setIP; case/imset2P=> u v Viu W2v ->{uv} Vjuv.
  have mxKi := subsetP ssM _ sKi.
  move: mxKj; rewrite inE; case/andP; case/maximalP; case/andP=> sKj _ mxKj _.
  have v1: v = 1.
    apply/set1P; apply: (subsetP trVm); rewrite inE defW2 W2v /=.
    apply/centP=> x Kjx; apply/commgP; rewrite (sameP eqP (set1P _ _)).
    have Kx: x \in K by apply: subsetP Kjx.
    apply: (subsetP trViW2); apply/setIP; split.
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
  apply: (subsetP trCVK); rewrite v1 !mulg1 in Vjuv *.
  have: Ki <*> Kj \subset K by rewrite mulgen_subG sKj normal_sub // nKiK.
  rewrite subEproper; case/predU1P=> [<-|sKij].
    by rewrite cent_mulgen setIA inE Viu.
  have defKj: Ki <*> Kj = Kj by apply: mxKj; rewrite ?mulgen_subr.
  suffices defKi: Kj = Ki by rewrite defKi sKi in nsKj.
  apply: val_inj; move: mxKi; rewrite inE /= -defKj.
  by case/andP; case/maximalP=> _ mxKi _; apply: mxKi; rewrite ?mulgen_subl.
have ViJ: forall x Ki, x \in P <*> R -> ((Vi Ki) :^ x)%G = Vi (Ki :^ x)%G.
  move=> x Ki PRx; apply: group_inj; rewrite /= conjIg centJ (normP _) //.
  by apply: subsetP PRx; rewrite mulgen_subG nVP (subset_trans sRG).
have actsPR_K: [acts (P <*> R | 'JG) on mxK].
  apply/subsetP=> x PRx; rewrite inE; apply/subsetP=> Ki.
  rewrite !inE -ViJ // !trivg_card card_conjg /=.
  case/andP; case/maximalP=> sKj mxKj ->.
  rewrite -(normsP nKPR x PRx) andbT.
  apply/maximalP; rewrite /proper !conjSg; split=> // Q.
  by rewrite !sub_conjg /= -sub_conjgV=> sQ; move/mxKj <-; rewrite // conjsgKV.
have actsPR: [acts (P <*> R | 'JG) on Vi @: mxK].
  apply/subsetP=> x PRx; rewrite inE; apply/subsetP=> Vj.
  case/imsetP=> Kj mxKj ->{Vj}.
  by rewrite inE /= ViJ // mem_imset // (actsP actsPR_K).
have transPR: [transitive (P <*> R | 'JG) on Vi @: mxK].
  have [K1 mxK1]: exists K1, K1 \in mxK.
    have:= sub0set mxK; rewrite subEproper; case/predU1P=> [mx0|]; last first.
      by case/andP=> _; case/subsetPn=> K1; exists K1.
    have:= pr_p; rewrite -oCVR -dprod_V -mx0 big1 => [|Ki]; rewrite ?inE //.
    by rewrite (setIidPl (sub1G _)) cards1.
  have mxV1: Vi K1 \in Vi @: mxK by rewrite mem_imset.
  apply/imsetP; exists (Vi K1) => //.
  set S := orbit _ _ _; rewrite (bigID [preim Vi of S]) /= in dprod_V.
  case/dprodGP: dprod_V (dprod_V) => [[N1 N2 defN1 defN2]].
  pose dp PK := \big[direct_product/1]_(Ki \in mxK | PK Ki) Vi Ki.
  rewrite defN1 defN2 => _ cN12 trN12; case/nondecV=> [||N1V].
  - apply/subsetP=> x Gx; rewrite !inE.
    move: Gx; rewrite -eqHR_G defH -mulgA; case/imset2P=> x1 x2 VHx1.
    rewrite -norm_mulgenEr // => PRx2 ->{x}.
    pose idPR (PK : pred {group gT}) :=
      forall y Ki, y \in P <*> R -> PK (Ki :^ y)%G = PK Ki.
    have idS: idPR [preim Vi of S].
      move=> y Ki PRy; rewrite /= -ViJ //; apply: orbit_transr.
      by apply/imsetP; exists y.
    have nN2: forall PK (N : group _),
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
      by case/andP: abV; case/andP.
    rewrite (nN2 _ _ _ defN1) // (nN2 _ _ _ defN2) ?subset_refl // => y Ki PRy.
    by congr (~~ _); exact: idS.
  - rewrite /trivg -(bigdprodEgen defN1) gen_subG.
    move/bigcup_inP; move/(_ K1); rewrite mxK1 orbit_refl => trV1.
    by move: mxK1; rewrite inE; case/andP=> _; case/negP; exact: trV1.
  have: S \subset Vi @: mxK by rewrite acts_orbit.
  rewrite subEproper; case/predU1P=> //; case/andP=> _; case/subsetPn=> V2.
  case/imsetP=> K2 mxK2 -> SV2.
  move: trN12; rewrite N1V /trivg -(bigdprodEgen defN2) (setIidPr _) gen_subG.
    move/bigcup_inP; move/(_ K2); rewrite mxK2 SV2 => trV2.
    by move: mxK2; rewrite inE; case/andP=> _; case/negP; exact: trV2.
  apply/bigcup_inP=> Kj _; exact: subsetIl.
case sR_IN: (forallb K1, (K1 \in mxK) ==> (R \subset 'N(Vi K1))).
  have{sR_IN} sR_IN: R \subset \bigcap_(Ki \in mxK) 'N(Vi Ki).
    by apply/bigcap_inP=> Ki mxKi; have:= forallP sR_IN Ki; rewrite mxKi.
  have nIPR: P <*> R \subset 'N(\bigcap_(Ki \in mxK) 'N(Vi Ki)).
    apply/subsetP=> x PRx; rewrite inE.
    apply/subsetP=> yx; case/imsetP=> y Iy -> {yx}.
    apply/bigcapP=> Ki.
    have ->: Ki = ((Ki :^ x^-1) :^ x)%G.
      by apply: group_inj; rewrite /= conjsgKV.
    rewrite -ViJ // (actsP actsPR_K) // normJ memJ_conjg.
    exact: (bigcapP _ _ _ Iy).
  case/imsetP: transPR => V1; case/imsetP=> K1 mxK1 ->.
  have: P <*> R \subset 'N(Vi K1).
    rewrite mulgen_subG (subset_trans sR_IN) /= ?bigcap_inf // andbT.
    rewrite defP; apply: (subset_trans (commgS P sR_IN)).
    have:= subset_trans (mulgen_subl P R) nIPR.
    rewrite -commg_subr; move/subset_trans; apply; exact: bigcap_inf.
  rewrite -conjG_fix; move/orbit1P <- => allV1.
  have defV1: V = Vi K1.
    apply/eqP; rewrite -val_eqE eqset_sub subsetIl /= andbT.
    rewrite -{1}(bigdprodEgen dprod_V) gen_subG; apply/bigcup_inP=> Ki mxKi.
    have: Vi Ki \in [set Vi K1] by rewrite -allV1 mem_imset.
    by move/set1P=> -> /=.
  move: mxK1 oKq2; rewrite inE; case/andP; case/(maximal_p_group qK).
  case/andP=> sK1 nK1; rewrite card_quotient {nK1}//.
  have trK1: trivg K1.
    apply: subset_trans trCKR_V; rewrite subsetI defV1 centsC subsetIr andbT.
    exact: subset_trans (mulgen_subl K R).
  rewrite (trivgP _ trK1) indexg1 => -> _.
  by rewrite -{2}(expn1 q) ltn_exp2l // prime_gt1.
case/existsP: sR_IN => K1; rewrite negb_imply; case/andP=> mxK1 nK1R.
have regR_Vi: forall Ki, Ki \in mxK ->
  ~~ (R \subset 'N(Vi Ki)) -> 'N_R(Vi Ki) = 1.
- move=> Ki mxKi fixVi; apply/trivgP; rewrite trivg_card /=.
  have: #|'N_R(Vi Ki)| %| r by rewrite -oR cardSg // subsetIl.
  case: (primeP pr_r) => _ dvr; move/dvr {dvr}; case/predU1P=> [->//|].
  move/eqP=> oN; case/setIidPl: fixVi; apply/eqP.
  by rewrite eqset_sub_card subsetIl oN oR leqnn.
have oV1R: #|orbit 'JG%act R (Vi K1)| = r.
  by rewrite card_orbit conjG_astab1 /= regR_Vi // indexg1 oR.
have nRfix_CR: forall Ki, Ki \in mxK -> ~~ (R \subset 'N(Vi Ki)) ->
           #|Vi Ki| = p /\ 'C_V(R) \subset << class_support (Vi Ki) R >>.
- move=> Ki mxKi fixVi.
  have [//||x Rx ox] := @Cauchy _ r R; first by rewrite oR.
  have xR: <[x]> = R.
    by apply/eqP; rewrite eqset_sub_card oR -ox cycle_subG Rx leqnn.
  have nVx: forall i y, y \in V -> y ^ x ^+ i \in V.
    move=> i y Vy; rewrite memJ_norm  ?groupX //; apply: subsetP Rx.
    exact: subset_trans nVG.
  pose f m y := \prod_(0 <= i < m) y ^ x ^+ i.
  have Vf: forall m y, y \in V -> f m y \in V.
    rewrite /f => m y Vy.
    apply big_prop => [||i _]; [exact: group1 | exact: groupM | exact: nVx].
  case/andP: abV; case/andP; move/centsP=> abV _ _.
  have fM: {in Vi Ki &, {morph f r: y z / y * z}}.
    rewrite /f => y z; case/setIP=> Vy _; case/setIP=> Vz _ /=.
    elim: (r) => [|m IHm]; first by rewrite !big_geq ?mulg1.
    rewrite !big_nat_recr /= conjMg 2!mulgA; congr (_ * _).
    by rewrite {}IHm -2!mulgA; congr (_ * _); rewrite abV ?Vf ?nVx.
  have injf: 'injm (Morphism fM).
    apply/subsetP=> y; case/morphpreP=> Vi_y; move/set1P=> /= fy1.
    have:= dprod_V; rewrite (bigD1 Ki) //=; case/dprodGP=> [[_ W _ defW _ _]].
    rewrite defW; move/subsetP; apply; rewrite inE Vi_y /=.
    rewrite -groupV -(mulg1 y^-1) -fy1 /f big_ltn ?ltn_0prime // conjg1 mulKg.
    rewrite big_cond_seq /=.
    apply big_prop=> [||i]; first 1 [exact: group1 | exact: groupM].
    rewrite mem_index_iota; case/andP=> i_pos ltir.
    rewrite -(bigdprodEgen defW) mem_gen //; apply/bigcupP.
    have Rxi: x ^+ i \in R by exact: groupX.
    have PRxi: x ^+ i \in P <*> R by apply: subsetP Rxi; exact: mulgen_subr.
    have:= congr_group (ViJ _ Ki PRxi) => /= Vi_xi.
    exists (Ki :^ (x ^+ i))%G; last by rewrite -Vi_xi memJ_conjg.
    rewrite (actsP actsPR_K) // mxKi -val_eqE (sameP eqP normP).
    apply/normP=> nVi_xi; have: x ^+ i \in 'N_R(Vi Ki).
      by rewrite inE Rxi; apply/normP; rewrite /= Vi_xi nVi_xi.
    by rewrite regR_Vi // inE -order_dvd ox /dvdn modn_small ?eqn0Ngt ?i_pos.
  have im_f: Morphism fM @* Vi Ki \subset 'C_V(R).
    rewrite morphimEdom /=.
    apply/subsetP=> fy; case/imsetP=> y; case/setIP=> Vy _ -> {fy}.
    rewrite inE Vf //= -sub1set centsC -xR cycle_subG /= cent_set1 inE.
    rewrite conjg_set1 sub1set; apply/set1P.
    have r1: r.-1.+1 = r by apply: prednK; exact: ltn_0prime.
    rewrite /f -r1 {1}big_nat_recr big_nat_recl /= conjMg -conjgM -expgSr.
    rewrite r1 -{2}ox order_expn1 conjg1 abV //; last first.
      by rewrite memJ_norm ?(subsetP (subset_trans sRG nVG)) ?Vf.
    congr (_ * _); pose Rbig := [fun z u => z ^ x = u].
    apply: (big_rel Rbig) => /= [|z1 _ z2 _ <- <-|i _]; first exact: conj1g.
    - exact: conjMg.
    by rewrite -conjgM -expgSr.
  have: isom (Vi Ki) (Morphism fM @* Vi Ki) (Morphism fM) by exact/isomP.
  move/isom_card=> oVi.
  have{im_f} im_f: Morphism fM @* Vi Ki = 'C_V(R).
    apply/eqP; rewrite eqset_sub_card im_f oCVR -oVi.
    have: p.-group (Vi Ki) by apply: pgroupS pV; exact: subsetIl.
    by case/pgroup_1Vpr=> [Vi1| [//]]; rewrite inE Vi1 trivg1 andbF in mxKi.
  rewrite oVi -oCVR -im_f; split=> //.
  rewrite morphimEdom /= /f; apply/subsetP=> fy; case/imsetP=> y Vi_y ->{fy}.
  apply big_prop => [||i _]; first 1 [exact: group1 | exact: groupM].
  rewrite mem_gen // class_supportEr.
  by apply/bigcupP; exists (x ^+ i); rewrite (groupX, memJ_conjg).
have oVi: forall Ki, Ki \in mxK -> #|Vi Ki| = p.
  move=> Ki mxKi.
  have [||z _ ->]:= (atransP2 transPR) (Vi K1) (Vi Ki); try exact: mem_imset.
  by rewrite card_conjg; case/nRfix_CR: nK1R.
have: orbit 'JG%act R (Vi K1) \subset Vi @: mxK.
  rewrite acts_orbit ?mem_imset //.
  apply: subset_trans actsPR; exact: mulgen_subr.
have nVjR: forall Kj, Kj \in mxK ->
  Vi Kj \notin orbit 'JG%act R (Vi K1) -> Kj = [~: K, R]%G.
- move=> Kj mxKj V1Rj; case/orP: (orbN (R \subset 'N(Vi Kj))) => [nVjR|].
    have defKj: 'C_K(Vi Kj) = Kj.
      move: mxKj; rewrite inE; case/andP; case/maximalP.
      case/andP=> sKjK _ mxKj ntVj; apply: mxKj; last first.
        by rewrite subsetI sKjK centsC subsetIr.
      rewrite properE subsetIl; apply: contra ntVj => cVjK.
      apply: subset_trans trCVK; rewrite subsetI subsetIl centsC.
      apply: (subset_trans cVjK); exact: subsetIr.
    have{nVjR} sKRVj: [~: K, R] \subset Kj.
      rewrite -defKj subsetI {1}commGC commg_subr nKR -ker_conj_aut.
      rewrite -sub_morphim_pre ?comm_subG ?morphimR ?nViK //; apply/commG1P.
      have: cyclic (Vi Kj) by rewrite cyclic_prime // oVi.
      case/cyclicP=> v.
      move/group_inj=> -> a; case/imsetP=> y _ -> b; case/imsetP=> z _ ->{a b}.
      apply: (centsP (aut_cycle_commute v)); exact: Aut_aut_of.
    apply/eqP; rewrite -val_eqE eq_sym eqset_sub_card sKRVj.
    rewrite -(leq_pmul2r (ltn_0prime q_pr)).
    have iKj: #|K : Kj| = q.
      move: mxKj; rewrite inE; case/andP; case/(maximal_p_group qK).
      by case/andP=> _ nKjK; rewrite card_quotient.
    rewrite -{1}iKj LaGrange ?normal_sub ?nKiK //.
    have: [~: K, R] \x 'C_K(R) = K.
      rewrite -comm_center_dir_prod //.
      by rewrite oR coprime_sym prime_coprime // -p'natE.
    case/dprodGP=> [[_ _ _ _ defKR _] trKR_C].
    rewrite -{1}defKR (card_mulG_trivP _ _ trKR_C) leq_pmul2l ?ltn_0group //=.
    have Z_CK: Zgroup 'C_K(R) by apply: ZgroupS ZCHR; exact: setSI.
    have:= forallP Z_CK 'C_K(R)%G; rewrite (@p_Sylow _ q) /=; last first.
      rewrite pHallE subset_refl part_pnat ?eqxx //.
      apply: pgroupS qK; exact: subsetIl.
    case/cyclicP=> z defC; rewrite defC dvdn_leq ?ltn_0prime // order_dvd.
    case/p_abelemP: abelemK => // _ -> //.
    by rewrite -cycle_subG -defC subsetIl.
  case/nRfix_CR=> // _ sCVj; case/nRfix_CR: nK1R => // _ sCV1.
  suff: trivg 'C_V(R) by rewrite trivg_card oCVR leqNgt prime_gt1.
  pose inK1R Ki := Vi Ki \in orbit 'JG%act R (Vi K1).
  have:= dprod_V; rewrite (bigID inK1R).
  case/dprodGP=> [[W1 Wj defW1 defWj _ _]]; apply: subset_trans.
  rewrite defW1 defWj subsetI (subset_trans sCV1) /=; last first.
    rewrite class_supportEr -(bigdprodEgen defW1) genS //.
    apply/bigcup_inP=> x Rx; apply/subsetP=> u V1xu.
    have PRx: x \in P <*> R by apply: subsetP Rx; exact: mulgen_subr.
    apply/bigcupP; exists (K1 :^ x)%G; last by rewrite -ViJ.
    by rewrite (actsP actsPR_K) // mxK1 /inK1R -ViJ // mem_imset.
  apply: (subset_trans sCVj); rewrite class_supportEr -(bigdprodEgen defWj).
  apply: genS; apply/bigcup_inP=> x Rx; apply/subsetP=> u Vjxu.
  have PRx: x \in P <*> R by apply: subsetP Rx; exact: mulgen_subr.
  apply/bigcupP; exists (Kj :^ x)%G; last by rewrite -ViJ.
  rewrite (actsP actsPR_K) // mxKj; apply: contra V1Rj.
  by move/orbit_transl=> <-; rewrite orbit_sym -ViJ // mem_imset.
rewrite subEproper; case/predU1P=> [defV1R | ]; last first.
  case/andP=> sV1R; case/subsetPn=> Vj; case/imsetP=> Kj mxKj ->{Vj} V1Rj.
  have defmxV: Vi @: mxK = Vi Kj |: orbit 'JG%act R (Vi K1).
    apply/eqP; rewrite eqset_sub andbC {1}setU1E subUset sub1set mem_imset //.
    rewrite sV1R; apply/subsetP=> V_i; case/imsetP=> Ki mxKi ->{V_i}.
    rewrite inE orbC; apply/norP=> [[]]; move/nVjR=> -> //; case/eqP.
    by move/nVjR: V1Rj => ->.
  have ViV1: Vi K1 \in Vi @: mxK by rewrite mem_imset.
  rewrite odd_2'nat in oddG; have: 2^'.-group (P <*> R).
    by  apply: pgroupS oddG; rewrite mulgen_subG sRG (subset_trans sPH).
  move/(pnat_dvd (trans_div ViV1 transPR)).
  rewrite defmxV cardsU1 (negPf V1Rj) oV1R -oR.
  rewrite -odd_2'nat /= odd_2'nat; case/negP; exact: pgroupS oddG.
have:= sub0set 'C_(Vi @: mxK)(P | 'JG); rewrite subEproper.
case/predU1P=> [fix0|].
  case/negP: nrp; rewrite eq_sym -dvdn_prime2 //; apply/eqnP.
  have:= pgroup_fix_mod pP (subset_trans (mulgen_subl P R) actsPR).
  by rewrite -{1}defV1R oV1R -fix0 cards0 (modn_small (ltn_0prime _)).
case/andP=> _; case/subsetPn=> Vj; case/setIP; case/imsetP=> Kj mxKj ->{Vj}.
rewrite conjG_fix => nVjP.
suffices: trivg (Vi Kj) by rewrite trivg_card leqNgt oVi ?prime_gt1.
apply: subset_trans trCVK; rewrite subsetI subsetIl centsC defKP.
rewrite -ker_conj_aut -sub_morphim_pre ?comm_subG ?morphimR ?nViK //.
apply/commG1P=> a; case/imsetP=> x _ -> b; case/imsetP=> y _ -> {a b}.
have: cyclic (Vi Kj) by rewrite cyclic_prime ?oVi.
case/cyclicP=> v; move/group_inj->.
apply: (centsP (aut_cycle_commute v)); exact: Aut_aut_of.
Qed.
