Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime binomial.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent abelian. 
Require Import maximal hall BGsection1.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(* belongs in commutators.v *)
Lemma der1_mulgen_cycles : forall (gT : finGroupType) (x y : gT), 
  let XY := <[x]> <*> <[y]> in let xy := [~ x, y] in
  xy \in 'C(XY) -> XY^`(1) = <[xy]>.
Proof. 
move=> gT x y; rewrite mulgen_idl mulgen_idr /= -sub_cent1; move/norms_gen=> ?.
apply/eqP; rewrite eqEsubset cycle_subG mem_commg ?mem_gen ?set21 ?set22 //.
rewrite der1_min // quotient_gen -1?gen_subG // quotientU abelian_gen.
rewrite /abelian subUset centU !subsetI andbC centsC -andbA -!abelianE.
rewrite !quotient_abelian ?(abelianS (subset_gen _) (cycle_abelian _)) //=.
by rewrite andbb quotient_cents2r ?genS // /commg_set imset2_set1l imset_set1.
Qed.

Section Section4.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

Lemma order_prime_squared_abelian : forall gT (G : {group gT}) p,
  prime p -> #|G| = (p ^ 2)%N -> abelian G.
Proof.
move=> gT G p primep orderG.
have pG: p.-group G by rewrite /pgroup orderG pnat_exp pnat_id.
by rewrite (p2group_abelian pG) // orderG pfactorK.
Qed.

Lemma four_dot_three : forall gT (R : {group gT}) p,
       p.-group R -> odd #|R| -> nil_class R <= 2 + (p > 3) ->
    exponent 'Ohm_1(R) %| p
 /\ (R^`(1) \subset 'Ohm_1(R) -> {in R &, {morph expgn^~ p : x y / x * y}}).
Proof.
move=> gT R p pR oddR classR.
pose f n := bin n 3; pose g n := (bin n 3).*2 + bin n 2.
have fS : forall n, f n.+1 = bin n 2 + f n.
  by move=> n; rewrite /f binS addnC. 
have gS : forall n, g n.+1 = (bin n 2).*2 + bin n 1 + g n.
  by move=> n; rewrite /g !binS double_add -!addnA; do 3!nat_congr.
case: (eqsVneq R 1) => [-> |].
  rewrite Ohm1 exponent1 der_sub dvd1n; split=> // _ u v; do 2!move/set1P->.
  by rewrite !(mulg1, exp1gn).
case/(pgroup_pdiv pR)=> p_pr p_dv_R _.
have pdivbin2: p %| bin p 2.
  rewrite prime_dvd_bin //= ltn_neqAle prime_gt1 // andbT.
  by apply: contraL oddR; rewrite -dvdn2; move/eqP->.
have pdivfp : p > 3 -> p %| f p by move=> pgt3; apply: prime_dvd_bin.
have pdivgp : p > 3 -> p %| g p.
  by move=> pgt3; rewrite dvdn_add // -muln2 dvdn_mulr // pdivfp.
have exp_dv_p : forall x m (S : {group gT}),
  exponent S %| p -> p %| m -> x \in S -> x ^+ m = 1.
- move=> x m S expSp p_dv_m Sx; apply/eqP; rewrite -order_dvdn.
  by apply: dvdn_trans (dvdn_trans expSp p_dv_m); exact: dvdn_exponent.
have p3_L21: p <= 3 -> {in R & &, forall u v w, [~ u, v, w] = 1}.
  move=> lep3 u v w Ru Rv Rw; rewrite (ltnNge 3) lep3 nil_class2 in classR. 
  apply/eqP; apply/commgP; red; rewrite (centerC Rw) //.
  by rewrite (subsetP classR) // mem_commg.
have{fS gS} eq44 : {in R &, forall u v n (r := [~ v, u]),
  (u * v) ^+ n = u ^+ n * v ^+ n * r ^+ bin n 2
                  * [~ r, u] ^+ f n * [~ r, v] ^+ g n}.
- move=> u v Ru Rv; move=> n r; have Rr: r \in R by exact: groupR.
  have cRr: {in R &, forall x y, commute x [~ r, y]}.
    move=> x y Rx Ry /=; red; rewrite (centerC Rx) //.
    have: [~ r, y] \in 'L_3(R) by rewrite !mem_commg.
    by apply: subsetP; rewrite -nil_class3 (leq_trans classR) // !ltnS leq_b1.
  elim: n => [| n IHn]; first by rewrite !mulg1.
  rewrite 3!expgSr {}IHn -!mulgA (mulgA (_ ^+ f n)); congr (_ * _).
  rewrite -commuteM; try by apply: commuteX; red; rewrite cRr ?groupM.
  rewrite -mulgA; do 2!rewrite (mulgA _ u) (commgC _ u) -2!mulgA.
  congr (_ * (_ * _)); rewrite (mulgA _ v).
  have ->: [~ v ^+ n, u] = r ^+ n * [~ r, v] ^+ bin n 2. 
    elim: n => [|n IHn]; first by rewrite comm1g mulg1.
    rewrite !expgS commMgR -/r {}IHn commgX; last exact: cRr.
    rewrite binS bin1 addnC expgn_add -2!mulgA; congr (_ * _); rewrite 2!mulgA.
    by rewrite commuteX2 // /commute cRr.
  rewrite commXg 1?commuteX2 -?[_ * v]commuteX; try exact: cRr.
  rewrite mulgA {1}[mulg]lock mulgA -mulgA -(mulgA v) -!expgn_add -fS -lock.
  rewrite -{2}(bin1 n) addnC -binS -2!mulgA (mulgA _ v) (commgC _ v).
  rewrite -commuteX; last by red; rewrite cRr ?(Rr, groupR, groupX, groupM).
  rewrite -3!mulgA; congr (_ * (_ * _)); rewrite 2!mulgA.
  rewrite commXg 1?commuteX2; try by red; rewrite cRr 1?groupR.
  by rewrite -!mulgA -!expgn_add addnCA binS addnAC addnn addnC -gS.
have expR1p: exponent 'Ohm_1(R) %| p.
  elim: _.+1 {-2 4}R (ltnSn #|R|) (subxx R) => // n IHn Q leQn sQR.
  rewrite (OhmE 1 (pgroupS sQR pR)) expn1; apply/exponentP=> x.
  rewrite gen_set_id; first by case/setIdP; case: eqP. 
  apply/group_setP; rewrite !inE group1 exp1gn /=; split=> {x}// x y.
  case/setIdP=> Qx; move/eqP=> xp1; case/setIdP=> Qy; case/eqP=> yp1.
  rewrite inE groupM //=; apply/eqP.
  have sxQ: <[x]> \subset Q by rewrite cycle_subG.
  have [[{sxQ}defQ]|[S maxS /= sxS]] := maximal_exists sxQ.
    rewrite expMgn; first by rewrite xp1 yp1 mulg1.
    by apply: (centsP (cycle_abelian x)); rewrite ?defQ.
  have:= maxgroupp maxS; rewrite properEcard; case/andP=> sSQ ltSQ.
  have pQ := pgroupS sQR pR; have pS := pgroupS sSQ pQ.
  have{ltSQ leQn} ltSn: #|S| < n by exact: leq_trans ltSQ _.
  have expS1p := IHn _ ltSn (subset_trans sSQ sQR).
  have defS1 := Ohm1Eexponent p_pr expS1p; move/exp_dv_p: expS1p => expS1p.
  have nS1Q: [~: Q, 'Ohm_1(S)] \subset 'Ohm_1(S).
    rewrite commg_subr (char_norm_trans (Ohm_char 1 S)) ?normal_norm //.
    exact: p_maximal_normal pQ maxS.
  have S1x : x \in 'Ohm_1(S) by rewrite defS1 inE -cycle_subG sxS xp1 /=.
  have S1yx : [~ y, x] \in 'Ohm_1(S) by rewrite (subsetP nS1Q) ?mem_commg.
  have S1yxx : [~ y, x, x] \in 'Ohm_1(S) by rewrite groupR.
  have S1yxy : [~ y, x, y] \in 'Ohm_1(S).
    by rewrite -invg_comm groupV (subsetP nS1Q) 1?mem_commg.
  rewrite eq44 ?(subsetP sQR) //= xp1 yp1 expS1p ?mul1g //.
  case: (leqP p 3) => [p_le3 | p_gt3]; last by rewrite ?expS1p ?mul1g; auto.
  by rewrite !p3_L21 // ?(subsetP sQR) // !exp1gn mulg1.
split=> // sR'R1 x y Rx Ry; rewrite -[x ^+ p * _]mulg1 eq44 // -2!mulgA //.
have expR'p := exp_dv_p _ _ _ (dvdn_trans (exponentS sR'R1) expR1p).
congr (_ * _); rewrite expR'p ?mem_commg // mul1g.
case: (leqP p 3) => [p_le3 | p_gt3].
  by rewrite !p3_L21 // ?(subsetP sQR) // !exp1gn mulg1.
by rewrite !expR'p 1?mem_commg ?groupR ?mulg1; auto.
Qed.

(* B & G 4.4b, G 7.6.5 *)
Lemma centralizer_scn_pgroup_eq : forall gT (R G A : {group gT}) p,
  p.-Sylow(G) R -> A \in 'SCN(R) -> 'O_p^'('C_G(A)) \x A = 'C_G(A).
Proof.
move=> gT R G A p sylR scnA; have [sRG _ _] := and3P sylR.
case/maxgroupP: (SCN_max scnA); case/andP=> nAG abelA maxA.
case/SCN_P: scnA => nAR CRA_A.
set C := 'C_G(A).
have CiP_eq : C :&: R = A by rewrite -CRA_A setIC setIA (setIidPl sRG).
have sylA: p.-Sylow(C) A.
  rewrite -CiP_eq; apply: (pSylow_normalI (subcent_normal _ _)).
  by apply: pHall_subl sylR; rewrite ?subsetIl // subsetI sRG normal_norm.
rewrite dprodEsdprod; last by rewrite (subset_trans (pcore_sub _ _)) ?subsetIr.
by apply: Burnside_normal_complement; rewrite // subIset ?subsetIr.
Qed.

Section Four_dot_Five_b.

Import GRing.Theory.

Lemma four_dot_five_b : forall gT (R : {group gT}) p x,
    p.-group R -> odd #|R| -> ~~ cyclic R -> x \in R -> #|R : <[x]>| = p ->
  ('Ohm_1(R))%G \in 'E_p^2(R).
Proof.
move=> gT R p x pR oddR ncycR Rx; set X := <[x]> => indexRX.
have sXR : <[x]> \subset R by [rewrite cycle_subG]; have pX := pgroupS sXR pR.
have [p_gt2 p_pr]: p > 2 /\ prime p.
  case: (eqsVneq R 1) ncycR oddR => [->|]; first by rewrite cyclic1.
  case/(pgroup_pdiv pR) => p_pr _ [k ->] _; rewrite odd_exp /= ltn_neqAle.
  by rewrite prime_gt1 //; case: eqP => // <-.
have maxX : maximal X R by rewrite p_index_maximal // indexRX.
have nXR : R \subset 'N(<[x]>) by rewrite normal_norm ?(p_maximal_normal pR).
case: (eqVneq X 1) => [X1 | ntX].
  by move: ncycR; rewrite prime_cyclic // -indexg1 -X1 indexRX.
have [_ _ [n oX]] := pgroup_pdiv pX ntX; rewrite -orderE in oX.
have: X != R by apply: contra ncycR; move/eqP <-; exact: cycle_cyclic.
rewrite eqEsubset sXR //=; case/subsetPn=> y Ry X'y.
have nXy := subsetP nXR y Ry; have Xyp: y ^+ p \in X.
  rewrite coset_idr ?groupX ?morphX // -indexRX; apply/eqP.
  by rewrite -order_dvdn -card_quotient ?order_dvdG ?mem_morphim.
have: x ^ y \in X by rewrite memJ_norm ?cycle_id.
case/cycleP=> k; case: (posnP k) => [-> | k_gt0] def_xy.
  by rewrite cycle_eq1 -(conjgK y x) def_xy conj1g eqxx in ntX.
have kp_modX: k ^ p == 1 %[mod p ^ n.+1].
  rewrite -oX -eq_expg_mod_order expg1; apply/eqP.
  transitivity (x ^ (y ^+ p)); last first.
    by rewrite /conjg -(centsP (cycle_abelian x) _ Xyp) ?cycle_id ?mulKg.
  elim: (p) => [|j IHj]; rewrite ?conjg1 // expnSr expgn_mul {}IHj.
  by rewrite expgS conjgM def_xy conjXg.
have{kp_modX} k_modZ: k == 1 %[mod p ^ n].
  have ki_gt0 : k ^ _ > 0 by move=> i; rewrite expn_gt0 k_gt0.
  have chFp := char_Fp p_pr; rewrite !eqn_mod_dvd // !subn1 in kp_modX *.
  have k1: (k%:R == 1 :> 'F_p)%R.
    rewrite -(Frobenius_aut_nat chFp) Frobenius_autE -natr_exp.
    rewrite -val_eqE /= val_Fp_nat ?Fp_cast // eqn_mod_dvd // subn1.
    by apply: dvdn_trans kp_modX; rewrite expnS dvdn_mulr.
  pose u := \sum_(i < p) \sum_(j < i) k ^ j.
  have u0: (u%:R == 0 :> 'F_p)%R.
    apply/eqP; rewrite -(@bin_lt_charf_0 _ _ chFp 2) //.
    have psum := (big_morph (fun m => m%:R : 'F_p)%R (@natr_add _) (mulr0n _)).
    rewrite -triangular_sum big_mkord !psum; apply: eq_bigr => i _.
    rewrite psum (eq_bigr (fun _ => 1%R)) ?sumr_const ?card_ord // => j _.
    by rewrite natr_exp (eqP k1) exp1rn.
  rewrite -!val_eqE /= !val_Fp_nat ?Fp_cast // !eqn_mod_dvd ?subn0 // in k1 u0.
  have def_kp: (k ^ p).-1 = (k.-1 * (k.-1 * u + 1 * p))%N.
    rewrite mul1n -{2}[p]card_ord -sum1_card predn_exp; congr (_ * _)%N.
    rewrite big_distrr -big_split; apply: eq_bigr => i _ /=.
    by rewrite -predn_exp addn1 prednK.
  case/dvdnP: u0 def_kp kp_modX => q -> ->; rewrite mulnA -muln_addl mulnCA.
  rewrite mulnA expnSr dvdn_pmul2r ?prime_gt0 ?gauss ?coprime_expl // -subn1.
  by case/dvdnP: k1 => q' ->; rewrite mulnAC /coprime gcdn_addl_mul gcdn1.
have: X :&: 'Z(R) != 1 by rewrite nil_meet_Z ?(pgroup_nil pR) /normal ?sXR.
case/(pgroup_pdiv (pgroupS (subsetIl _ _) pX)) => _; case/Cauchy=> // z.
case/setIP=> Xz; case/setIP=> Rz cRz oz _; set r := [~ x, y].
have def_z: <[z]> = 'Ohm_1(X).
  apply/eqP; rewrite eqEcard {1}(OhmE _ pX) cycle_subG.
  rewrite mem_gen /=; last by rewrite inE -oz Xz expg_order /=.
  rewrite (Ohm_p_cycle _ pX) subn1 -orderE orderXdiv ?pfactor_dvdn ?leq_pred //.
  by rewrite -orderE oz oX pfactorK // expnS mulnK // expn_gt0 prime_gt0.
have{k k_gt0 k_modZ def_xy} z_r: r \in <[z]>.
  rewrite def_z (OhmE _ pX) mem_gen //= /r commgEl def_xy -(subnKC k_gt0).
  rewrite expgS mulKg inE mem_cycle -expgn_mul -order_dvdn oX expnSr.
  by rewrite dvdn_pmul2r ?prime_gt0 // -eqn_mod_dvd.
have cRr: r \in 'C(R) by apply: subsetP z_r; rewrite cycle_subG.
have nrR: R \subset 'N(<[r]>) by rewrite cents_norm // centsC cycle_subG.
have defR: R :=: X <*> <[y]>.
  apply/eqP; rewrite eq_sym eqEproper mulgen_subG !cycle_subG Rx Ry /=.
  apply/negP; case/maxgroupP: maxX => _ maxX; move/maxX => /= defX.
  by rewrite -cycle_subG /= -defX ?mulgen_subl ?mulgen_subr in X'y.
have defR': R^`(1) = <[r]>.
  rewrite defR der1_mulgen_cycles // (subsetP _ _ cRr) // centS //.
  by rewrite mulgen_subG !cycle_subG Rx.
have sR1R': R^`(1) \subset 'Ohm_1(R).
  rewrite defR' (OhmE _ pR) genS // sub1set inE groupR //=.
  by rewrite -order_dvdn -oz order_dvdG.
case/four_dot_three: (pR) => // [|expR1p]; last move/(_ sR1R') => morphRp.
  apply: leq_trans _ (leq_addr _ _).
  by rewrite nil_class2 defR' cycle_subG inE cRr groupR.
case/cycleP: Xyp => qp def_yp; have: p %| qp.
  apply: contraR ncycR.
  rewrite -prime_coprime // -(@coprime_pexpl n.+1) // -oX => co_x_qp.
  apply/cyclicP; exists y; rewrite defR /mulgen (setUidPr _) ?genGid //.
  by rewrite cycle_subG -[x](expgnK co_x_qp) -?def_yp ?groupX ?cycle_id.
case/dvdnP => q def_qp; rewrite {qp}def_qp in def_yp.
pose t := y * x ^- q; have Rt: t \in R by rewrite groupM ?groupV ?groupX.
have{X'y} X't: t \notin X by rewrite groupMr ?groupV ?mem_cycle.
have{def_yp} ot: #[t] = p.
  apply/eqP; case: (eqVneq t 1) X't => [->|]; first by rewrite group1.
  rewrite -cycle_eq1 eqn_dvd; case/(pgroup_pdiv (mem_p_elt pR Rt)) => _ -> _ _.
  rewrite order_dvdn morphRp ?groupV ?groupX // expVgn -expgn_mul -def_yp.
  by rewrite mulgV eqxx.
have{defR} defR: X <*> <[t]> = R.
  apply/eqP; rewrite eqEproper mulgen_subG !cycle_subG Rx Rt /=.
  apply/negP; case/maxgroupP: maxX => _ maxX; move/maxX => /= defX.
  by rewrite -cycle_subG /= -defX ?mulgen_subl ?mulgen_subr in X't.
have nZt: <[t]> \subset 'N(<[z]>).
  rewrite cycle_subG; apply: subsetP Rt.
  by rewrite cents_norm // centsC cycle_subG.
pose R1 := <[z]> <*> <[t]>; rewrite !inE /= Ohm_sub /= -2!andbA expR1p.
have ->: 'Ohm_1(R) = R1.
  rewrite -(setIidPl (Ohm_sub _ _)) /R1 norm_mulgenEr //= -{2}defR.
  rewrite norm_mulgenEr ?cycle_subG ?(subsetP nXR) -?group_modr //=; last first.
    by rewrite (OhmE _ pR) genS //= sub1set inE Rt -ot expg_order /=.
  congr (_ * _); apply/eqP; rewrite eqEsubset andbC.
  rewrite def_z subsetI Ohm_sub OhmS //=.
  apply/subsetP=> u; case/setIP; move/(exponentP expR1p)=> up1 Xu.
  by rewrite (OhmE _ pX) mem_gen //= inE Xu up1 /=.
have oR1: #|R1| = (p ^ 2)%N.
  rewrite /R1 mulgenC norm_mulgenEl ?TI_cardMg ?prime_TIg -?orderE ?oz ?ot //.
  by apply: contra X't; rewrite cycle_subG; apply: subsetP; rewrite cycle_subG.
have pR1: p.-group R1 by rewrite /pgroup oR1 pnat_exp pnat_id.
by rewrite pR1 (p2group_abelian pR1) oR1 pfactorK.
Qed.

End Four_dot_Five_b.

Section Four_dot_Five_ac.

Variables (gT : finGroupType) (R : {group gT}) (p : nat).
Hypotheses (pR : p.-group R) (oddR : odd #|R|) (ncycR : ~~ cyclic R).

Lemma four_dot_five_a : exists2 S : {group gT}, S <| R & S \in 'E_p^2(R).
Proof.
have: exists G : {group gT}, (G <| R) && ~~ cyclic G.
  by exists R; rewrite normal_refl.
case/ex_mingroup=> M; case/mingroupP; case/andP=> nsMR ncycM minM.
have [sMR _] := andP nsMR; have pM := pgroupS sMR pR.
exists ('Ohm_1(M))%G; first exact: char_normal_trans (Ohm_char 1 M) nsMR.
apply: (subsetP (pnElemS _ _ sMR)).
case: (eqsVneq M 1) (ncycM) => [-> | ntM _]; first by rewrite cyclic1.
have{ntM} [p_pr _ [e oM]] := pgroup_pdiv pM ntM.
have le_e_M: e <= logn p #|M| by rewrite ltnW // oM pfactorK.
have{le_e_M} [N [sNM nsNR] oN] := normal_pgroup pR nsMR le_e_M.
have ltNM: ~~ (#|N| >= #|M|) by rewrite -ltnNge oM oN ltn_exp2l ?prime_gt1.
have cycN : cyclic N by apply: contraR ltNM => ncycN; rewrite minM //= nsNR.
case/cyclicP: cycN => x defN; have Mx : x \in M by rewrite -cycle_subG -defN.
apply: four_dot_five_b Mx _; rewrite ?(oddSg sMR) //.
by rewrite -divgS /= -defN // oM oN expnS mulnK // expn_gt0 prime_gt0.
Qed.

Let Z := 'Ohm_1('Z_2(R)).

Lemma four_dot_five_c : ~~ cyclic Z /\ exponent Z %| p.
Proof. 
case: (four_dot_five_a) => S [nsSR]; case/pnElemP=> sSR abelS dimS2.
have [pS cSS expSp]:= and3P abelS; have nilR := pgroup_nil pR.
case: (eqsVneq S 1) dimS2 => [-> | ntS dimS2]; first by rewrite cards1 logn1.
have [p_pr _ _] :=  pgroup_pdiv pS ntS.
pose SR := [~: S, R]; pose SRR := [~: SR, R].
have sSR_S : SR \subset S by rewrite commg_subl normal_norm.
have sSRR_SR : SRR \subset SR by rewrite commSg.
have sSR_R := subset_trans sSR_S sSR.
(* shouldn't this be a separate lemma for nilpotent groups? *) 
have{ntS} prSR: SR \proper S.
  rewrite properE sSR_S //=; apply: contraL (forallP nilR S).
  by rewrite (setIidPr sSR_R) => ->.
have SRR1 : SRR = 1.
  case: (eqVneq SR 1) => [SR1 | ntSR]; first by rewrite /SRR SR1 comm1G. 
  have prSRR: SRR \proper SR.
    rewrite /proper sSRR_SR; apply: contra ntSR => sSR_SRR.
    by rewrite (implyP (forallP nilR _)) // subsetI sSR_R.
  have pSR := pgroupS sSR_R pR; have pSRR := pgroupS sSRR_SR pSR.
  have [_ _ [e oSR]] := pgroup_pdiv pSR ntSR; have [f oSRR] := p_natP pSRR.
  have e0 : e = 0.
    have:= proper_card prSR; rewrite oSR -(part_pnat pS) p_part dimS2.
    by rewrite ltn_exp2l ?prime_gt1 // !ltnS leqn0; move/eqP.
  apply/eqP; have:= proper_card prSRR; rewrite trivg_card1 oSR oSRR e0.
  by rewrite ltn_exp2l ?prime_gt1 // ltnS; case f.
have sSR_ZR : [~: S, R] \subset 'Z(R).
  by rewrite subsetI sSR_R /=; apply/commG1P.
have sS_Z2R : S \subset 'Z_2(R).
  rewrite ucnSnR; apply/subsetP=> s Ss; rewrite inE (subsetP sSR) //= ucn1.
  by apply: subset_trans sSR_ZR; rewrite commSg ?sub1set.
have sZ2R_R := ucn_sub 2 R; have pZ2R := pgroupS sZ2R_R pR.
have pZ : p.-group Z. 
  apply: pgroupS pR; exact: subset_trans (Ohm_sub _ _) (ucn_sub 2 R).
have sSZ : S \subset Z.
  apply/subsetP=> s Ss; rewrite /Z (OhmE 1 pZ2R) mem_gen // inE.
  by rewrite (subsetP sS_Z2R) //= (exponentP expSp).
have ncycX: ~~ cyclic S by rewrite (abelem_cyclic abelS) dimS2.
split; first by apply: contra ncycX; exact: cyclicS.
(* should this be proved for arbitrary n? *)
have nilclassZ : nil_class 'Z_2(R) <= 2.
  rewrite nil_class2 subsetI der_sub /= (subset_trans (commgS _ sZ2R_R)) //.
  by apply: (subset_trans (ucn_comm _ _)); rewrite ucn1 subIset // centS ?orbT.
by case: (four_dot_three pZ2R (oddSg sZ2R_R oddR) (leq_trans nilclassZ _)).
Qed.

End Four_dot_Five_ac.

Lemma four_dot_six : forall gT (R S : {group gT}) p,
    p.-group R -> odd #|R| -> S <| R -> ~~ cyclic S ->
  exists H : {group gT}, H <| R /\ H \in 'E_p^2(R).
Proof.
move=> gT R S p pR oddR nsSR ncycS; pose Z := 'Ohm_1('Z_2(S)).
have nsZR: Z <| R.
  by rewrite (char_normal_trans (char_trans (Ohm_char 1 _) (ucn_char 2 S))).
have pZ: p.-group Z := pgroupS (normal_sub nsZR) pR.
have [sSR _] := andP nsSR; have pS := pgroupS sSR pR.
have [] := four_dot_five_c pS (oddSg sSR oddR) ncycS; rewrite -/Z.
case: (eqVneq Z 1) => [-> | ntZ ncycZ expZp]; first by rewrite cyclic1.
have [p_pr _ [e]] := pgroup_pdiv pZ ntZ; rewrite /= -/Z => cardZ.
have e_gt0 : 0 < e.
  by case: (posnP e) => // e0; rewrite prime_cyclic ?cardZ ?e0 in ncycZ.
have lognpZ : 2 <= logn p #|Z| by rewrite cardZ pfactorK.
case: (normal_pgroup pR nsZR lognpZ) => H [sHZ nHR cardH].
exists H; split; first done.
rewrite pnElemE // inE cardH eqxx andbT inE (normal_sub nHR) /=.
rewrite abelemE // (order_prime_squared_abelian p_pr) //=.
by apply: (dvdn_trans _ expZp); apply: exponentS.
Qed.

Lemma odd_pgroup_rank1_cyclic : forall gT (G : {group gT}) (p : nat),
  p.-group G -> odd #|G| -> cyclic G = ('r_p(G) <= 1).
Proof.
move=> gT G p pG oddG; apply/idP/idP=> [cycG | dimG1].
  have cGG := cyclic_abelian cycG; rewrite p_rank_abelian //.
  by rewrite -abelem_cyclic ?(cyclicS (Ohm_sub _ _)) ?Ohm1_abelem.
apply: contraLR dimG1 => ncycG; rewrite -ltnNge; apply/p_rank_geP.
by have [E _ EP2_E] := four_dot_five_a pG oddG ncycG; exists E.
Qed.

Lemma odd_rank1_Zgroup : forall gT (G : {group gT}),
  odd #|G| -> Zgroup G = ('r(G) <= 1).
Proof.
move=> gT G oddG; apply/forallP/idP=> [ZgG | rG_1 P].
  have [p p_pr ->]:= rank_witness G; have [P sylP]:= Sylow_exists p G.
  have [sPG pP _] := and3P sylP; have oddP := oddSg sPG oddG.
  rewrite (p_rank_Sylow sylP) -(odd_pgroup_rank1_cyclic pP) //.
  by apply: (implyP (ZgG P)); exact: (p_Sylow sylP).
apply/implyP; case/SylowP=> p p_pr; case/and3P=> sPG pP _.
rewrite (odd_pgroup_rank1_cyclic pP (oddSg sPG oddG)).
by apply: leq_trans (leq_trans (p_rank_le_rank p G) rG_1); exact: p_rankS.
Qed.

(* move this to action.v, or fold into the proof below? *)
Lemma astabsQR_point : forall gT (A H : {set gT}) (G : {group gT}),
    H \subset 'N(G) -> A \subset 'N(G) -> 
  'C_H(A / G | 'Q) = H :&: [set x | (commg x @: A) \subset G].
Proof. 
move=> gt A H G sH_NG sA_NG; apply/setP=> x.
case Hx : (x \in H); rewrite inE [x \in _ :&: _]inE Hx //=. 
rewrite -sub1set astabsQR ?inE ?sub1set ?(subsetP sH_NG) //.
by rewrite gen_subG /commg_set imset2_set1l.
Qed.

Section Twenty_Three_dot_Fifteen. (* in Aschbacher *)

Variables (gT : finGroupType) (G A : {group gT}).
Hypothesis (SCN_A : A \in 'SCN(G)).

Let Z := 'Ohm_1(A).

Lemma der1_stab_Ohm1_SCN_series : 
  ('C(Z) :&: 'C_G(A / Z | 'Q))^`(1) \subset A.
Proof.
case/SCN_P: SCN_A=> nsAG CGAeq; have nAG := (normal_norm nsAG).
have nZG := (normal_norm (char_normal_trans (Ohm_char 1 _) nsAG)).
rewrite -{4}CGAeq subsetI; apply/andP; split.
  by apply: (subset_trans (der_sub _ _)); rewrite subIset // subsetIl orbT.
rewrite gen_subG; apply/subsetP=> w; case/imset2P=> u v.
rewrite astabsQR_point ?(subset_trans (normal_sub nsAG)) // !inE.
case/andP; move/centP=> centuZ; case/andP=> Gu /= s_commguA_Z.
case/andP; move/centP=> centvZ; case/andP=> Gv /= s_commgvA_Z ->{w}. 
apply/centP=> a Aa; symmetry; rewrite mulgA [a * _]commgC /conjg 2!mulgA.
have NZu : u \in 'N(Z) by apply: (subsetP nZG u Gu).
have Zauinv : [~ a, u^-1] \in Z.
  rewrite -(memJ_norm _ NZu); apply: (subsetP s_commguA_Z).
  by apply/imsetP; exists a => //; rewrite /conjg /commg !mulgA invgK mulgKV.
rewrite -(mulgA _ _ v^-1) (commuteV (commute_sym (centvZ _ Zauinv))).
rewrite !mulgA invgK mulgKV -(mulgA _ _ v^-1) [a * _]commgC 2!mulgA.
have NZv : v \in 'N(Z) by apply: (subsetP nZG v Gv).
have Zavinv : [~ a, v^-1] \in Z.
  rewrite -(memJ_norm _ NZv); apply: (subsetP s_commgvA_Z).
  by apply/imsetP; exists a => //; rewrite /conjg /commg !mulgA invgK mulgKV.
have cAA : A \subset 'C(A) by rewrite -abelianE; apply: (SCN_abelian SCN_A).
have sZA := (Ohm_sub 1 A).
rewrite -(mulgA _ _ a^-1) (centsP cAA _ (subsetP sZA _ Zavinv)) ?groupV //. 
rewrite mulgA mulgK -(mulgA _ _ u) -(centuZ _ Zavinv) mulgA -(mulgA _ _ a).
rewrite (centsP cAA _ (subsetP sZA _ Zavinv)) // /commg /conjg !mulgA.
by rewrite mulgK mulgKV invgK.
Qed.

Variable (p : nat).
Hypotheses (oddp : odd p) (pgroupG : p.-group G).

Lemma Ohm1_stab_Ohm1_SCN_series : 'Ohm_1('C_G(Z)) \subset 'C_G(A / Z | 'Q).
Proof.
case Geq1 : (G == 1%G).
  rewrite (eqP Geq1) /= (subset_trans (Ohm_sub _ _)) //.
  by rewrite (subset_trans (subsetIl _ _)) // sub1set group1.
case: (pgroup_pdiv pgroupG (negbT Geq1)) => primep _ _.
case/SCN_P: SCN_A=> nAG CGAeq; have sGNA := (normal_norm nAG).
have sGNZ := (normal_norm (char_normal_trans (Ohm_char 1 _) nAG)).
have sANZ := (subset_trans (normal_sub nAG) sGNZ).
have sACA : A \subset 'C(A) by apply: (SCN_abelian SCN_A).
have pgroupCGZ : p.-group 'C_G(Z) by rewrite (pgroupS _ pgroupG) // subsetIl.
rewrite (OhmE 1 pgroupCGZ) gen_subG expn1; apply/subsetP=> x; rewrite 2!inE /=.
case/andP; case/andP=> Gx CZx xpeq1.
pose CA_XZ := 'C_A(<[x]> / Z | 'Q). 
have CA_XZ_eq : CA_XZ = A :&: [set g | commg g @: <[x]> \subset Z].
  by rewrite /CA_XZ astabsQR_point //= ?gen_subG ?sub1set ?(subsetP sGNZ).
have sX_NCAXZ : <[x]> \subset 'N(CA_XZ).
  rewrite normsI //; first by rewrite cycle_subG (subsetP sGNA).
  rewrite normsG // astabsQ cycle_subG (subsetP (cent_sub _)) //.
  by rewrite -abelianE quotient_abelian // cycle_abelian.
pose Y := <[x]> <*> CA_XZ.
have sxG : <[x]> \subset G by rewrite cycle_subG.
have sCA_XZ_G : CA_XZ \subset G. 
  exact: (subset_trans (subsetIl _ _) (normal_sub nAG)).
have sYG : Y \subset G by rewrite mulgen_subG sxG.
have pgroupY := (pgroupS sYG pgroupG). 
have Yeq : Y = <[x]> * 'C_A(<[x]> / Z | 'Q) by apply: norm_mulgenEl.
have nZx : <[x]> \subset 'N(Z) by rewrite cents_norm ?cycle_subG.
have nZY : Y \subset 'N(Z). 
  by rewrite mulgen_subG nZx (subset_trans (subsetIl _ _)).
have sY'_Z : Y^`(1) \subset Z.
  rewrite der1_min //= -/Y Yeq -/Z quotientMl // abelianM.
  rewrite !quotient_abelian ?cycle_abelian ?(abelianS _ sACA) ?subsetIl //.
  by rewrite /= quotientGI ?Ohm_sub // centsC quotient_astabQ subsetIr.
have {sY'_Z}nil_classY : nil_class Y <= 2.
  rewrite nil_class2 (subset_trans sY'_Z _) // subsetI.
  rewrite (subset_trans _ (mulgen_subr _ _)) /= 1?subsetI; last first.
    by rewrite Ohm_sub //= astabsQ normG /= trivg_quotient sub1set group1.
  rewrite centsC mulgen_subG cycle_subG CZx //=. 
  rewrite (subset_trans (subsetIl _ _)) // centsC //.
  by rewrite (subset_trans (Ohm_sub _ _)).
pose XA := <[x]> <*> A.
rewrite -cycle_subG subsetI sxG /= astabsQ nZx /= centsC -/Z. 
suffices: XA \subset Y.
  rewrite Yeq group_modl /=; last first.
    by rewrite astabsQ nZx; apply: quotient_abelian; apply: cycle_abelian.
  rewrite subsetI {1}[XA]norm_mulgenEl ?subxx /=; last first.
    by apply: (subset_trans _ sGNA); rewrite cycle_subG.
  rewrite astabsQ; case/andP=> _ /=; apply: subset_trans; apply: quotientS.
  exact: mulgen_subr.
have XAeq : XA = <[x]> * A.
  by apply: norm_mulgenEl; rewrite gen_subG sub1set (subsetP sGNA).
have sYXA : Y \subset XA.
  rewrite mulgen_subG mulgen_subl; apply: (subset_trans _ (mulgen_subr _ _)).
  exact: subsetIl.
have pgroupXA : p.-group XA.
  apply: (pgroupS _ pgroupG); rewrite mulgen_subG gen_subG sub1set Gx /=.
  exact: (normal_sub nAG).
have pgroupA := (pgroupS (normal_sub nAG) pgroupG).
have sY1_XZ : 'Ohm_1(Y) \subset <[x]> * Z.
  apply/subsetP=> w Y1w.
  move: (subsetP sYXA _ (subsetP (Ohm_sub _ _) _ Y1w)) (Y1w).
  rewrite XAeq; case/imset2P=> y a; case/cycleP=> i ->{y} Aa ->{Y1w w}.
  rewrite groupMl; last first.
    rewrite groupX //= (OhmE _ pgroupY) mem_gen // inE expn1 xpeq1 andbT.
    by apply: (subsetP (mulgen_subl _ _)); apply: cycle_id.
  pose expY1 := (exponentP (exponent_Ohm1_class2 oddp pgroupY nil_classY)).
  move/(expY1 _)=> apeq; apply: mem_imset2; first exact: mem_cycle.
  by rewrite [Z](OhmE 1 pgroupA) mem_gen // inE Aa expn1 apeq eq_refl.
suffices ->: XA = Y by rewrite subxx.
apply: (nilpotent_sub_norm (pgroup_nil pgroupXA)).
  rewrite mulgen_subG mulgen_subl; apply: (subset_trans _ (mulgen_subr _ _)).
  exact: subsetIl.
have sNXAY_NXAY1 : 'N_XA(Y) \subset 'N_XA('Ohm_1(Y)).
  rewrite subsetI subsetIl /=.
  apply: (subset_trans (normal_norm (normalSG sYXA))); apply normal_norm.
  by apply: (char_normal_trans (Ohm_char _ _)); apply: normalG.
apply: (subset_trans sNXAY_NXAY1) => {sNXAY_NXAY1}.
apply/subsetP=> w; case/setIP; rewrite XAeq; case/imset2P=> y a.
case/cycleP=> i ->{y} Aa -> NY1xi; rewrite /= [_ <*> _]Yeq.
rewrite mem_imset2 // ?mem_cycle //.
have Y1x : x \in 'Ohm_1(Y).
  rewrite (OhmE 1 pgroupY); apply: (subsetP (subset_gen _)).
  by rewrite inE expn1 (subsetP (mulgen_subl _ _)) //= cycle_id.
move: (Y1x); rewrite -(memJ_norm _ NY1xi) conjgM {NY1xi}.
rewrite (conjgE x) (commuteX i (commute_refl x)) mulgA mulVg mul1g.
move/(subsetP sY1_XZ _); case/imset2P=> y z; case/cycleP=> j ->{y} Zz xaeq.
have xjorda : x^+(j ^ #[a]) = x^+j.
  case/p_natP: (mem_p_elt pgroupA Aa) => n ->; rewrite (divn_eq (j^_) p).
  rewrite expgn_add mulnC expgn_mul (eqP xpeq1) exp1gn mul1g.
  rewrite {2}(divn_eq j p) expgn_add mulnC expgn_mul (eqP xpeq1) exp1gn mul1g.
  apply: congr1; elim: n => [|n ih]; first by rewrite expn0 expn1.
  rewrite expnSr expn_mulr -modn_exp ih modn_exp.
  case pdivj : (p %| j).
    case/dvdnP: pdivj=> k ->; rewrite -modn_exp modn_mull. 
    by rewrite exp0n ?prime_gt0 // mod0n. 
  rewrite -{1}(prednK (prime_gt0 primep)) expnS.
  have phip : phi p = p.-1.
    by rewrite -{1}(expn1 p) phi_pfactor //= expn0 muln1.
  rewrite -modn_mulmr -phip Euler 1?coprime_sym ?prime_coprime ?pdivj //.
  by rewrite modn_mulmr muln1.
have x1j : x *  x^-j \in Z.
  rewrite -{1}(conjg1 x) -(expg_order a) -xjorda {xjorda}.
  elim: #[a] => [|n ih]. 
    by rewrite expn0 !expg0 expg1 conjg1 mulgV group1.
  rewrite expgS conjgM xaeq conjMg conjXg expnSr expgn_mul -expVgn.
  have centzA := (centP (subsetP sACA _ (subsetP (Ohm_sub 1 A) z Zz))).
  rewrite [z^_]mulgA -centzA ?groupV ?groupX // mulgKV.
  rewrite -mulgA commuteX; last first.
    apply: commuteV; apply: commuteX; apply: commute_sym. 
    by apply: (centP CZx).
  rewrite mulgA groupM // -expMgn ?groupX //.
  pose x1 := x ^ a ^+ n; pose x2 := x ^- (j ^n); rewrite -[x^_](mulgK x2 x1). 
  apply: commuteV; apply: commuteX; apply: commute_sym. 
  apply: commuteM; by [ apply: (centP CZx) | rewrite invgK; apply: commuteX].
rewrite ['C__(_|_)]CA_XZ_eq inE Aa /=; rewrite inE; apply/subsetP=> h.
case/imsetP=> y; case/cycleP=> k ->{y} ->{h}.
rewrite commgEr conjVg conjXg xaeq expMgn; last first.
  by apply: commute_sym; apply: commuteX; rewrite /commute (centP CZx).
rewrite invMg -mulgA groupM ?groupV ?groupX // -expVgn -expMgn.
  by rewrite groupX // (commute_sym _) //; apply: commuteV; apply: commuteX.
by apply: commute_sym; apply: commuteV; apply: commuteX.
Qed.

End Twenty_Three_dot_Fifteen.

Section Twenty_Three_dot_Sixteen. 

Variables (gT : finGroupType) (G Z : {group gT}) (p : nat).
Hypotheses (oddp : odd p) (pgroupG : p.-group G).
Hypothesis (max_pabelem_normal_Z : [max Z | (Z <| G) && p.-abelem Z]).

Let X := ('Ohm_1('C_G(Z)))%G.

Lemma max_pabelem_normal_eq_Ohm1_cent : Z = X.
Proof.
case/maxgroupP: max_pabelem_normal_Z; case/andP=> nZG pabelemZ maxZ. 
have sG_NZ := (normal_norm nZG).
case Geq1 : (G == 1%G).
  apply/eqP; rewrite [_ == _]eqEsubset (subset_trans (normal_sub nZG)) /=.
    rewrite (subset_trans (Ohm_sub _ _)) // (subset_trans (subsetIl _ _)) //.
    by rewrite (eqP Geq1) sub1set group1 //=.
  by rewrite (eqP Geq1) sub1set group1 //=.
case: (pgroup_pdiv pgroupG (negbT Geq1)) => primep _ _ {Geq1}.
case: (abelemP primep pabelemZ)=> abelZ expZp.
move: (abelZ); rewrite abelianE => sZ_CZ.
have nXG : X <| G.
  apply: (char_normal_trans (Ohm_char 1 'C_G(Z))).
  apply: (normalS _ _ (subcent_normal _ _)); first exact: subsetIl.
  by rewrite subsetI subxx (normal_norm nZG).
have sXG := (normal_sub nXG).
have sX_CZ : X \subset 'C(Z).
  by apply: (subset_trans (Ohm_sub _ _)); rewrite subsetIr.
have sZX : Z \subset X.
  rewrite /X /= (OhmE 1 (pgroupS (subsetIl _ _) pgroupG)).
  apply: (subset_trans _ (subset_gen _)); apply/subsetP=> x Zx.
  rewrite !inE expn1 expZp // eq_refl (subsetP (normal_sub nZG)) //= andbT. 
  exact: (subsetP abelZ _ Zx).
have nZX := (normalS sZX (normal_sub nXG) nZG).
suffices expXp : exponent X %| p.
  have sXZ_G : X <*> Z \subset G by rewrite mulgen_subG (subset_trans sZX) sXG.
  have nZ_XZ := (normalS (mulgen_subr _ _) sXZ_G nZG). 
  suffices Zeq : Z = (X <*> Z)%G.
    by apply/eqP; rewrite [_ == _]eqEsubset (normal_sub nZX) Zeq mulgen_subl.
  apply: (quotient_injG (normal_refl Z) nZ_XZ); symmetry.
  rewrite trivg_quotient quotient_mulgen ?(normal_norm nZX) //.
  apply: (nil_TI_Z (pgroup_nil (quotient_pgroup Z pgroupG))) => /=.
    by apply: quotient_normal.
  apply/eqP; rewrite eqEsubset sub1G andbT; apply/subsetP=> xbar.  
  rewrite inE; case/andP; case/imsetP=> x; case/setIP => NZx Xx ->{xbar} /=. 
  rewrite inE; case/andP=> _ CZ_xZ; rewrite inE; apply/eqP; apply: coset_id.
  suffices Zeq : <[x]> <*> Z = Z.
    by rewrite -Zeq (subsetP (mulgen_subl _ _)) ?cycle_id //.
  have sxZ_G : <[x]> <*> Z \subset G.
    by rewrite mulgen_subG (normal_sub nZG) gen_subG sub1set (subsetP sXG).
  have sZ_CxZ : Z \subset 'C(<[x]> <*> Z).
    rewrite cent_mulgen subsetI sZ_CZ centsC gen_subG sub1set.
    by rewrite (subsetP sX_CZ).
  have nZ_xZ : Z <| <[x]> <*> Z by apply: (normalS (mulgen_subr _ _) sxZ_G nZG).
  have nxZ_G : <[x]> <*> Z <| G.
    rewrite /normal sxZ_G -(quotientSGK sG_NZ) /=; last by apply: cents_norm.
    rewrite quotient_normG //= quotient_mulgen /= ?gen_subG ?sub1set //.
    rewrite quotient_cycle //; apply: cents_norm; rewrite centsC.
    by rewrite gen_subG sub1set.
  have abel_xZ : abelian (<[x]> <*> Z).
    rewrite abelianE cent_mulgen subsetI centsC cent_mulgen subsetI.
    rewrite cents_cycle ?commutexx //= gen_subG sub1set (subsetP sX_CZ) //=.
    rewrite centsC cent_mulgen subsetI sZ_CZ centsC gen_subG sub1set.
    by rewrite (subsetP sX_CZ) //=.
  apply: maxZ => /=; rewrite ?(normal_sub nZ_xZ) // nxZ_G /=.
  rewrite abelemE // abel_xZ /=.
  apply/exponentP=> g; rewrite /= norm_mulgenEl; last first.
    by apply: (subset_trans _ sG_NZ); rewrite gen_subG sub1set (subsetP sXG).
  case/mulsgP=> y z xy Zz ->; rewrite expMgn; last first.
    apply: (centsP sX_CZ) => //; apply: (subsetP _ _ xy).
    by rewrite gen_subG sub1set.
  rewrite (expZp _ Zz) mulg1.
  move/exponentP: expXp; apply; apply: (subsetP _ _ xy).
  by rewrite gen_subG sub1set.
pose normal_abelian := [pred A | ((A : {group gT}) <| G) && (abelian A)].
have normal_abelian_Z : normal_abelian Z.
  by rewrite /normal_abelian /= nZG abelZ. 
case: (maxgroup_exists normal_abelian_Z) => A max_normal_abelian_A.
have SCNG_A : A \in 'SCN(G) by apply: (max_SCN pgroupG max_normal_abelian_A).
move: max_normal_abelian_A; case/maxgroupP; case/andP=> nAG abelA maxA sZA.
have pgroupA := (pgroupS (normal_sub nAG) pgroupG).
have OhmAeqZ : 'Ohm_1(A) = Z.
  apply: maxZ => /=; last by rewrite -(Ohm1_id pabelemZ) OhmS.
  by rewrite Ohm1_abelem // andbT (char_normal_trans (Ohm_char _ _) nAG).
pose W := 'C_G(A / 'Ohm_1(A) | 'Q).
have sX_CWOhmA : X \subset 'C('Ohm_1(A)) :&: W.
  rewrite subsetI /X /W -OhmAeqZ.
  rewrite (Ohm1_stab_Ohm1_SCN_series SCNG_A oddp pgroupG) andbT /=.
  by apply: (subset_trans (Ohm_sub _ _)); apply: subsetIr. 
have {sX_CWOhmA} sX1_A : X^`(1) \subset A.
  rewrite (subset_trans _ (der1_stab_Ohm1_SCN_series SCNG_A)) //.
  by rewrite !derg1 commgSS.
case expX : (exponent X %| p) => //.
pose Uprop := [pred U | ('Ohm_1(U : {group gT}) == U) && ~~(exponent U %| p)].
have UpropX : Uprop X by rewrite inE expX /= Ohm_id eq_refl.
case: (mingroup_exists UpropX)=> U; case/mingroupP; case/andP.
case/eqP=> OhmUeqU; move/negP=> expU minU sUX.
have pgroupU := (pgroupS (subset_trans sUX sXG) pgroupG).
have existsxy : existsb x, existsb y, 
  [&& (x \in U), (y \in U), x^+p == 1, y^+p == 1 & (x * y)^+p != 1].
  apply: negbNE; apply/negP; rewrite negb_exists; move/forallP => forall_hyp.
  pose UU := [set x \in U | x^+p==1].
  have group_set_UU : group_set UU.
    apply/group_setP; split; first by rewrite inE group1 exp1gn eq_refl.
    move=> x y; rewrite inE; case/andP=> Ux xp1.
    rewrite inE; case/andP=> Uy yp1; rewrite inE groupM //=.
    move: (forall_hyp x); rewrite negb_exists; move/forallP; move/(_ y). 
    by rewrite Ux Uy xp1 yp1 /=; apply: negbNE.
  have sU_UU : U \subset UU.
    rewrite -OhmUeqU -(gen_set_id group_set_UU) (OhmE 1 pgroupU) gen_subG /=. 
    by apply: sub_gen; apply/subsetP=> x; rewrite !inE expn1.
  apply: expU; apply/exponentP=> x Ux; move: (subsetP sU_UU x Ux).
  by rewrite inE; case/andP => _; case/eqP.
case/existsP: existsxy=> x; case/existsP=> y; case/and5P=> Ux Uy xp1 yp1.
move/negP=> xyp_ne1; pose XY := << [set x; y] >>.
have sXY_U : XY \subset U by rewrite gen_subG subUset !sub1set Ux Uy.
have pgroupXY := (pgroupS sXY_U pgroupU).
have XYx : x \in XY by rewrite mem_gen // !inE eq_refl.
have XYy : y \in XY by rewrite mem_gen // !inE eq_refl orbT.
have XYeqU : XY = U.
  apply: minU => //; rewrite inE; apply/andP; split.
    rewrite eqEsubset Ohm_sub /= gen_subG /= (OhmE 1 pgroupXY) sub_gen //.
    by rewrite expn1 subUset !sub1set !inE XYx XYy xp1 yp1.
  apply/negP; move/exponentP; move/(_ (x * y)); rewrite groupM //=.
  by move/(_ is_true_true)=> xyp1; apply: xyp_ne1; rewrite xyp1 eq_refl.
pose V := << class_support <[x]> U >>%G.
have xx_subnormal_U : <[x]> <|<| U.
  apply: (nilpotent_subnormal (pgroup_nil pgroupU)).
  by rewrite gen_subG sub1set.
case: (subnormalEsupport xx_subnormal_U) => /= [Ueq | VproperU].
  case: xyp_ne1; apply/eqP; rewrite expMgn ?(eqP xp1) ?(eqP yp1) ?mulg1 //.
  by move: Uy; rewrite -Ueq; case/cycleP=> i ->; apply: commuteX.
have sVU := proper_sub VproperU.
case expV : (exponent V %| p); last first.
  move: VproperU; rewrite properEneq; case/andP; case/negP; apply/eqP. 
  apply: minU; rewrite /Uprop ?sVU //= expV andbT eqEsubset.
  rewrite Ohm_sub /= gen_subG /= (OhmE 1 (pgroupS sVU pgroupU)).
  apply: sub_gen; apply/subsetP=> v Vv; rewrite inE expn1 mem_gen ?Vv //=.
  move: Vv; rewrite class_supportEl; case/bigcupP=> z; case/cycleP=> j ->{z}.
  case/imsetP=> u Uu ->; rewrite -conjXg -expgn_mul mulnC expgn_mul.
  by rewrite (eqP xp1) exp1gn conj1g eq_refl.
have Zcommxy : [~ x, y] \in Z.
  rewrite -OhmAeqZ (OhmE 1 pgroupA) mem_gen // inE expn1. 
  rewrite (subsetP sX1_A) /=; last first.
    by rewrite derg1 mem_gen //; apply: mem_imset2; rewrite (subsetP sUX).
  apply/eqP; apply: (exponentP expV); rewrite commgEl groupM ?groupV //. 
    apply: (subsetP _ _ (cycle_id _)); apply: sub_gen.
    by apply: (sub_class_support U <[x]>).
  rewrite mem_gen // class_supportEl; apply/bigcupP.
  by exists x; [apply: cycle_id | apply: mem_imset].
move: xyp_ne1; case; rewrite expMg_Rmul -1?invg_comm; first last.
  - by apply: commuteV; apply: (centsP sX_CZ _ (subsetP sUX _ Ux) _ Zcommxy).
  by apply: commuteV; apply: (centsP sX_CZ _ (subsetP sUX _ Uy) _ Zcommxy).
rewrite (eqP xp1) (eqP yp1) !mul1g.
have p_dvd_bin : p %| bin p 2.
  rewrite prime_dvd_bin //=.
  move: (prime_gt1 primep); rewrite leq_eqVlt; case/orP => //.
  by move/eqP => p_eq; move: oddp; rewrite -p_eq.
case/dvdnP: p_dvd_bin=> i ->; rewrite mulnC expgn_mul expZp ?exp1gn ?eqxx //.
by rewrite groupV.
Qed.

End Twenty_Three_dot_Sixteen.

Lemma pgroup_odd_card: forall (gT : finGroupType) (P : {group gT}) p,
  p.-group P -> odd p -> odd #|P|.
Proof.
move=> gT P p pP oddp; rewrite odd_2'nat (pi_pnat pP) //; apply: contraL oddp.
by move/eqnP->.
Qed.

Lemma pgroup_proper_logn_card: forall (gT : finGroupType) (P Q : {group gT}) p,
  p.-group P -> Q \proper P -> logn p #|Q| < logn p #|P|.
Proof. 
move=> gT P Q p pP; rewrite properEneq eqEcard andbC ltnNge; case/andP=> sQP.
rewrite sQP /= -{1}(part_pnat pP) -{1}(part_pnat (pgroupS sQP pP)) !p_part {pP}.
by apply: contra; case: p => [|p] lePQ; rewrite ?logn0 // leq_pexp2l.
Qed.

Lemma SCN3_empty_iff : forall (gT : finGroupType) (R : {group gT}) p,
  p.-group R -> odd p -> ('SCN_3(R) == set0) = ('r(R) <= 2).
Proof.
move=> gT R p pgroupR oddp; have oddR := (pgroup_odd_card pgroupR oddp).
case SCN3empty: ('SCN_3(R) == set0); last first.
  symmetry; apply/negP => lrR2; case/set0Pn: (negbT SCN3empty) => A.
  rewrite inE; case/andP; case/SCN_P=> nsAR _=> l2rR.
  by move: (leq_trans (leq_trans l2rR (rankS (normal_sub nsAR))) lrR2).
case cyclicR : (cyclic R); symmetry.
  move: cyclicR; rewrite (odd_pgroup_rank1_cyclic pgroupR oddR) -rank_pgroup //.
  by move/leq_trans; apply.
rewrite (rank_pgroup pgroupR) leqNgt; apply/negP; case/p_rank_geP => A.
rewrite !inE; case/andP; case/andP => sAR pabelemA logpA.
case: (four_dot_five_a pgroupR oddR (negbT cyclicR))=> Z nsZR; rewrite !inE. 
case/andP; case/andP=> sZR pabelemZ; move/eqP=> logpZ. 
have Zeq : Z = 'Ohm_1('C_R(Z))%G.
  apply: (max_pabelem_normal_eq_Ohm1_cent oddp pgroupR).
  apply/maxgroupP; split => [|H]; first by rewrite nsZR pabelemZ.
  case/andP=> nsHR pabelemH sZH; apply/eqP; rewrite eq_sym eqEproper sZH /=.
  apply/negP=> pZH.
  pose normal_abelian := [pred K | ((K : {group gT}) <| R) && (abelian K)].
  have naH : normal_abelian H 
    by rewrite /normal_abelian /= nsHR (abelem_abelian pabelemH).
  case: (maxgroup_exists naH)=> K maxK sHK.
  move: (max_SCN pgroupR maxK) => SCN_K{maxK}.
  suffices: K \in 'SCN_3(R) by rewrite (eqP SCN3empty) inE.
  rewrite inE SCN_K /= -logpZ (leq_trans _ (rankS sHK)) //.
  rewrite (rank_abelem pabelemH).
  exact: (pgroup_proper_logn_card (pgroupS (normal_sub nsHR) pgroupR) pZH).
have nZA : A \subset 'N(Z) by apply: (subset_trans sAR (normal_norm nsZR)).
pose H:= 'C_A(Z); have sHA : H \subset A by apply: subsetIl. 
have logpHge2: logn p #|H| >= 2. 
  rewrite -(leq_add2r 1) addn1 /= -(eqP logpA) -(LaGrange sHA) logn_mul //.
  by rewrite leq_add2l (logn_quotient_cent_abelem nZA pabelemZ) // logpZ.
pose K := 'C_A(Z) <*> Z.
have cprodK : 'C_A(Z) \* Z = K by apply: cprodEgen; apply: subsetIr.
have sKR : K \subset R by rewrite mulgen_subG (subset_trans (subsetIl _ _)).
have sK_CRZ: K \subset 'C_R(Z).
  by rewrite subsetI sKR mulgen_subG subsetIr; apply: (abelem_abelian pabelemZ).
have pabelemK : p.-abelem K.
  by rewrite (cprod_abelem _ cprodK) pabelemZ andbT (abelemS (subsetIl _ _)).
suffices : 'r(Z) >= 3 by rewrite (rank_abelem pabelemZ) logpZ.
rewrite Zeq rank_Ohm1 (leq_trans _ (rankS sK_CRZ)) //.
case sZA : (Z \subset A). 
  rewrite -(eqP logpA) -rank_abelem // rankS //. 
  rewrite (subset_trans _ (mulgen_subl _ _)) // subsetI subxx /=.
  by rewrite (subset_trans (abelem_abelian pabelemA)) // centS.
rewrite (leq_ltn_trans logpHge2) // (rank_abelem pabelemK).
rewrite (pgroup_proper_logn_card) //=; first exact: (pgroupS _ pgroupR).
by rewrite properE (mulgen_subl _ _) /= mulgen_subG !subsetI sZA !andbF.
Qed.

End Section4.

(*
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
*)
