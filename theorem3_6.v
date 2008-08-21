Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms automorphism normal commutators.
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
  forallb V : {group T}, is_sylow A V ==> cyclic V.

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
by rewrite -cycle_sub_group /order -gex ?group_dvdn // inE HsubG eqxx.
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
case/is_sylowP=> p pr_p; rewrite sylowE; case/andP=> sVH.
case/(sylow1_subset pr_p (subset_trans sVH sHG))=> P; case/andP=> sVP sylP.
by apply: cyclicS sVP (implyP (zgG _) _); apply /is_sylowP; exists p.
Qed.

Lemma Zgroup_morphim : forall G, Zgroup G -> Zgroup (f @* G). 
Proof.
move=> G zgG; wlog sGD: G zgG / G \subset D.
  by rewrite -morphimIdom; apply; rewrite (ZgroupS _ zgG, subsetIl) ?subsetIr.
apply/forallP=> fV; apply/implyP.
case/is_sylowP=> p pr_p sylfV; have [P sylP] := sylow1_cor G pr_p.
have [|z _ ->] := (sylow2_cor pr_p) (f @* P)%G _ _ sylfV.
  by apply: morphim_sylow (subset_trans _ sGD) _ => //; case/andP: sylP.
rewrite cyclicJ cyclic_morphim // (implyP (forallP zgG P)) //.
by apply/is_sylowP; exists p.
Qed.

Lemma Phi_char: forall G, 'Phi(G) \char G. Admitted.

Lemma p_length_1_quo_p : forall p G H,
  prime p -> H <| G -> trivg 'O_[~p] (G / H) ->
  p_length_1 p (G / H) -> p_length_1 p G.
Admitted.

Lemma p_length_1_quo2 : forall p G H K,
  prime p -> H <| G -> K <| G -> trivg (H :&: K) ->
  p_length_1 p (G / H) -> p_length_1 p (G / K) -> p_length_1 p G.
Admitted.

Lemma coprime_cent_Phi : forall H G,
  coprime #|H| #|G| -> [~: H, G] \subset 'Phi(G) ->  H \subset 'C(G).
Admitted.

Lemma solvable_self_cent_Fitting : forall G,
  solvable G -> 'C_G('F(G)) \subset 'F(G).
Admitted.

Lemma Fitting_char : forall G, 'F(G) \char G.
Admitted.

Lemma Fitting_normal : forall G, 'F(G) <| G.
Proof. move=> G; apply: normal_char; exact: Fitting_char. Qed.

End Props.

Section MoreSubsets.

Variables (T : finType) (A B C D : {set T}).
Hypotheses (sAC : A \subset C) (sBD : B \subset D).

Lemma setISS : A :&: B \subset C :&: D.
Proof. exact: subset_trans (setIS _ _) (setSI _ _). Qed.

Lemma setUSS : A :|: B \subset C :|: D.
Proof. exact: subset_trans (setUS _ _) (setSU _ _). Qed.

Lemma setDSS : A :\: D \subset C :\: B.
Proof. exact: subset_trans (setDS _ _) (setSD _ _). Qed.

End MoreSubsets.

Theorem three_dot_six : forall (gT : finGroupType) (G H R R0 : {group gT}),
    solvable G -> odd #|G| ->
    H <| G -> is_hall G H -> R \in complg G H ->
    R0 \subset R -> prime #|R0| -> Zgroup 'C_H(R0) ->
  forall p, prime p -> p_length_1 p [~: H, R].
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn H R R0.
move=> solG oddG nHG hallH compH_R sR0R.
move oR0: #|R0| => r pr_r ZCHR0 p pr_p.
have sRG: R \subset G by exact: sub_compl compH_R.
case/complgP: compH_R => trivgHR eqHR_G; case/andP: (hallH) => sHG coHH'.
have{coHH'} coHR: coprime #|H| #|R|. 
  have:= coHH'; rewrite -group_divn -eqHR_G ?mulG_subl // .
  by rewrite (card_mulG_trivP _ _ trivgHR) ?divn_mulr. 
have nHR: R \subset 'N(H) := subset_trans sRG (normal_norm nHG).
have IHG: forall H1 R1 : {group gT},
  H1 \subset H -> H1 * R1 \subset 'N(H1) -> R0 \subset R1 -> R1 \subset R ->
  (#|H1| < #|H|) || (#|R1| < #|R|) -> p_length_1 p [~: H1, R1].
- move=> H1 R1 sH1 nH1 sR01 sR1 ltG1.
  move defHR1: (H1 <*> R1)%G => G1; have{defHR1} defG1: G1 = H1 * R1 :> set _.
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
  have solG1: solvable G1 := solvable_sub sG1G solG.
  have oddG1: odd #|G1|.
    move: oddG; do 2!rewrite -[odd _]negbK -dvdn2_even; apply: contra. 
    move/dvdn_trans; apply; exact: group_dvdn.
  have nHG1: H1 <| G1 by rewrite /(H1 <| _) defG1 mulG_subl.
  have hallH1: is_hall G1 H1.
    by rewrite /is_hall -group_divn normal_sub // oG1 divn_mulr.
  have complR1: R1 \in complg G1 H1 by apply/complgP; rewrite coprime_trivg.
  apply: IHn complR1 sR01 _ _ p pr_p => //; first by rewrite oR0.
  exact: ZgroupS (setSI _ sH1) ZCHR0.
without loss defHR: / [~: H, R] = H.
  have:= nHR; rewrite -subcomm_normal commsgC => sHR_R.
  have:= sHR_R; rewrite subEproper; case/predU1P=> [-> -> //|s'HR_H _].
  rewrite commGAA //; last exact: solvable_sub solG.
  apply: IHG => //; last by rewrite proper_card.
  apply: subset_trans (normal_norm (normal_commutator H R)).
  by rewrite mulgenC norm_mulgenE // (normC nHR) mulSg.
have{IHn trivgHR hallH} IHquo: forall X : group gT,
  ~~ trivg X -> X \subset H -> G \subset 'N(X) -> p_length_1 p (H / X).
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
  have hallH': is_hall (G / X) (H / X) by exact: morphim_is_hall.
  have compR': (R / X)%G \in complg (G / X) (H / X).
    apply/complgP; split; last by rewrite -morphimMl ?eqHR_G. 
    by rewrite -morphimGI ?ker_coset // [H :&: R](trivgP _ trivgHR) morphim1.
  have sR0R': R0 / X \subset R / X by exact: morphimS.
  have pr_R0X: prime #|R0 / X|.
    have trXR0: X :&: R0 = 1.
      by apply/trivgP; exact: subset_trans (setISS _ _) trivgHR.
    by rewrite card_quotient // -group_divnI setIC trXR0 cards1 divn1 oR0.
  apply: IHn compR' sR0R' pr_R0X _ _ pr_p => //.
  have coHR0: coprime #|H| #|R0|.
    by rewrite -(LaGrange sR0R) coprime_mulr in coHR; case/andP: coHR.
  rewrite -coprime_quotient_cent_weak ?Zgroup_morphim //; first exact/andP.
  exact: solvable_sub solG.
rewrite defHR.
without loss Op'_H: / trivg 'O_[~ p](H).
  case/orP: (orbN (trivg 'O_[~ p](H))) => [-> -> // | ntO _].
  suffices: p_length_1 p (H / 'O_[~ p](H)) by admit.
  apply: IHquo => //; first by rewrite normal_sub ?core_normal.
  by rewrite normal_norm // (char_norm_trans (char_core _ _)).
move defV: 'F(H)%G => V.
have charV: V \char H by rewrite -defV Fitting_char.
have nVG: G \subset 'N(V) by rewrite normal_norm ?(char_norm_trans charV).
have sVH: V \subset H by rewrite normal_sub ?normal_char.
have defVp: V = 'O_[p](H) :> set _.
  admit.
have pV: pgroup p V by rewrite defVp /pgroup pi_group_core.
have sCV_V: 'C_H(V) \subset V.
  rewrite -defV solvable_self_cent_Fitting //; exact: solvable_sub solG.
wlog abV: / abelem p V.
  case/orP: (orbN (trivg 'Phi(V))) => [trPhi -> // | ntPhi _].
    admit.
  have chPhi: 'Phi(V) \char H := char_trans (Phi_char _) charV.
  have nPhiH := normal_char chPhi; have sPhiH := normal_sub nPhiH.
  have{chPhi} nPhiG: G \subset 'N('Phi(V)).
    exact: normal_norm (char_norm_trans chPhi nHG).
  apply: (p_length_1_quo_p pr_p nPhiH); last exact: IHquo.
  have: 'O_[~p](H / 'Phi(V)) <| H / 'Phi(V) by exact: core_normal.
  case/(inv_quotientN _) => // W; move/(congr1 val)=> /= defW sPhiW nWH.
  have p'Wb: p'group p (W / 'Phi(V)) by rewrite -defW; exact: pi_group_core.
  suffices pW: pgroup p W.
    rewrite trivg_card (@pi_nat_1 (pred1 p) #|_|) //= defW //.
    exact: morphim_pi_group.
  apply/pi_groupP=> q pr_q; case/Cauchy=> // x Wx oxq; apply/idPn=> /= neqp.
  suff: <[x]> \subset V.
    rewrite gen_subG sub1set => Vx.
    by move/pi_groupP: pV neqp => /= -> //; rewrite -oxq order_dvd_g.
  apply: subset_trans sCV_V; rewrite subsetI cycle_h /=; last first.
    apply: subsetP Wx; exact: normal_sub.
  have coxV: coprime #[x] #|V|.
    by rewrite oxq coprime_sym (pi_nat_coprime pV) // /pi'_nat pi_nat_prime.
  apply: coprime_cent_Phi coxV _.
  have: W :&: V \subset 'Phi(V); last apply: subset_trans.
    rewrite -trivg_quotient; last first.
      by rewrite subIset // orbC normal_norm // normal_char // Phi_char.  
    rewrite quotientE morphimIG ?ker_coset ?Phi_subset // -!quotientE.
    rewrite setIC coprime_trivg // (@pi_nat_coprime (pred1 p)) //.
    by rewrite [pi_nat _ _]morphim_pi_group.
  case/andP: nWH => sWH nWH.
  rewrite subsetI andbC subcomm_normal cycle_h; last first.
    by apply: subsetP Wx; apply: subset_trans (subset_trans sWH _) nVG.
  move: nWH; rewrite -subcomm_normal commsgC; apply: subset_trans.
  by rewrite commgSS // cycle_h //.
have{sCV_V} eqVC: V = 'C_H(V) :> (set _). 
  by apply/eqP; rewrite eqset_sub sCV_V subsetI andbT sVH; case/andP: abV.
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
  apply: (p_length_1_quo2 pr_p nN1 nN2 trN12); exact: IHquo.
have: 'F(H / V) <| G / V.
  exact: char_norm_trans (Fitting_char _) (morphim_normal _ _).
case/(inv_quotientN _) => [|U]; last move/(congr1 val)=> /= defU sVU nUG.
  by apply/andP; rewrite (subset_trans sVH).
case/andP: nUG => sUG nUG; have nUR := subset_trans sRG nUG.
have sUH: U \subset H.
  have: U / V \subset H / V by rewrite -defU normal_sub ?Fitting_normal.
  by rewrite morphimSGK ?ker_coset // (subset_trans sUG).
have: exists2 K : {group gT}, hall (predC1 p) U K & R \subset 'N(K).
  apply: coprime_hall_exists => //; last exact: (solvable_sub sUG).
  by rewrite -(LaGrange sUH) coprime_mull in coHR; case/andP: coHR.
case=> K hallK nKR; have [sKU _]:= andP hallK.
have p'K: p'group p K by move: hallK; rewrite hallE; case/and3P.
have p'Ub: p'group p 'F(H / V) by admit.
have nVU := subset_trans (subset_trans sUH sHG) nVG.
have defVK: U = V * K :> {set gT}.
  have nVK := subset_trans sKU nVU.
  apply/eqP; rewrite eqset_sub mul_subG //= andbT -quotientSK //.
  rewrite subEproper eq_sym eqset_sub_card.
  have: hall (predC1 p) (U / V) (K / V) by exact: morphim_hall.
  by case/andP=> ->; move/eqP=> ->; rewrite part_pi_nat ?leqnn // -defU.
have sylV: sylow p U V.
  have coVK: coprime #|V| #|K| := pi_nat_coprime pV p'K.
  by rewrite [sylow p U V]hallE sVU [pi_group _ V]pV -card_quotient // -defU.
have defH: H = V * 'N_H(K) :> {set gT}.
  have nUH: U <| H by apply/andP; rewrite (subset_trans sHG).
  rewrite -{1}(HallFrattini _ nUH hallK); last exact: solvable_sub solG.
  by rewrite defVK -mulgA [K * _]mulSGid // subsetI normG (subset_trans sKU).
have [P sylP nPR]: exists2 P : {group gT}, sylow p 'N_H(K) P & R \subset 'N(P).
  have sNH: 'N_H(K) \subset H by exact: subsetIl.
  apply: coprime_hall_exists.
  - by apply/normsP=> x Rx /=; rewrite conjIg -normJ !(normsP _ _ Rx).
  - by move: coHR; rewrite -(LaGrange sNH) coprime_mull; case/andP.
  apply: solvable_sub solG; exact: subset_trans sHG.
have sPN: P \subset 'N_H(K) by case/andP: sylP.
have [sPH nKP]: P \subset H /\ P \subset 'N(K) by apply/andP; rewrite -subsetI.
 have nVH := subset_trans sHG nVG; have nVP := subset_trans sPH nVH.
have sylVP: sylow p H (V * P).
  have defVP: V * P = V <*> P by rewrite mulgenC -normC ?norm_mulgenE.
  rewrite /sylow /hall mul_subG //= defVP.
  rewrite -(LaGrange sVH) pi_part_mul ?ltn_0mul ?ltn_0group //=.
  have: V \subset V <*> P by rewrite -defVP mulG_subl.
  move/LaGrange <-; rewrite part_pi_nat // eqn_pmul2l // /=.
  rewrite -!card_quotient //; last by rewrite gen_subG subUset normG.
  rewrite -defVP defH !quotient_mulgr.
  have: sylow p ('N_H(K) / V) (P / V) by exact: morphim_sylow.
  by case/andP.
case/orP: (orbN (trivg [~: K, P])) => [tKP|ntKP].
  suffices sylVH: sylow (gT:=gT) p H V. admit.
(*  rewrite /p_length_1. rewrite/qp'_core.
    have Op'_H1: 'O_[~ p](H) = 1 by case/trivgP: Op'_H.
    rewrite Op'_H1. *) 
  suffices sPV: P \subset V by rewrite mulGSid in sylVP.
  have sol_qHV : solvable (H /V). 
    by apply: solvable_quo; apply: (solvable_sub sHG).
  have qPV: P / V \subset 'C_(H / V)('F(H / V)).
    rewrite defU subsetI; apply/andP; split; first by apply:morphimS.
    rewrite defVK quotient_mulgr; apply: center_commgr; rewrite commsgC.
    case/trivgP: tKP; move ->; apply: sub1G.
  have sPU: P \subset U.
    rewrite defVK -quotientSK // -(quotient_mulgr _ K) -defVK -defU.
    by apply (subset_trans qPV (solvable_self_cent_Fitting sol_qHV)).
  case/andP: sylP; rewrite -p_part_pi /p_part => _ cardP. 
  apply: (sylow2_subset pr_p sPU cardP); rewrite //=.
  rewrite/normal sVU //=.
have{sylVP} dp: [~: V, K] \x 'C_V(K) = V :> set _.
  apply: sym_eq; apply: comm_center_dir_prod.
  - exact: (subset_trans sKU nVU).
  - exact (pi_nat_coprime  pV p'K).
  - by case/andP: abV.
have trVeq: trivg 'C_V(K) \/ 'C_V(K) = V.
  apply: (nondecV _  [~: V, K]); first by rewrite dprodC.
  rewrite subsetI; apply/andP; split; admit.
have Vcomm: [~: V, K] = V :> set _ /\ trivg  'C_V(K).
  case trVeq=> [trC|eqC]. 
  - split; last done.
    by rewrite -{2}dp; case/trivgP:trC; move ->; rewrite dprodg1.
  - apply: False_ind.
    have sKV: K \subset V by rewrite eqVC subsetI (subset_trans sKU sUH) centsC -eqC subsetIr.
    have trK: trivg K. 
      by rewrite trivg_card (pi_nat_1 _ p'K) //; apply: (pi_nat_dvdn _ pV); apply: group_dvdn.
    by apply: (negP ntKP); rewrite (trivgP _ trK); apply/trivgP; rewrite //= comm1G.
have eqcn: 'N_V(K) = 'C_V(K).
  apply: coprime_norm_cent.
  - rewrite -subcomm_normal commsgC; case Vcomm=> eqV _; rewrite -{2}eqV; apply: subset_refl.
  - exact (pi_nat_coprime  pV p'K).
have PIV: V :&: P = 1.
  apply/eqP; rewrite eqset_sub sub1G andb_true_r.
  apply: (subset_trans (setIS _ sPN)); rewrite setIA (setIidPl sVH) eqcn.
  case Vcomm => _ ; move/trivgP <-; apply: subset_refl.
admit.
Qed.


