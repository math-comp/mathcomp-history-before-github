Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime binomial.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent abelian. 
Require Import maximal hall BGsection1.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Section4.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* B & G, Lemma 4.1 (also, Gorenstein, 1.3.4, and Aschbacher, ex. 2.4) is     *)
(* covered by Lemma center_cyclic_abelian, in cyclic.v.                       *)

(* B & G, Lemma 4.2 is covered by Lemmas commXg, commgX, commXXg (for 4.2(a)) *)
(* and expMg_Rmul (for 4.2(b)) in commutators.v.                              *)

(* This is B & G, Theorem 4.3 (a) and (b). *)
Lemma exponent_odd_nil23 : forall gT (R : {group gT}) p,
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

(* This is B & G, Proposition 4.4(b), or Gorenstein 7.6.5 *)
Lemma dprod_cent_SCN_Sylow : forall gT (R G A : {group gT}) p,
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

Section ExtremalOhm1.

Import GRing.Theory.

(* This is B & G, Lemma 4.5(b), or Gorenstein, 5.4.4 and 5.5.5 *)
Lemma Ohm1_extremal_odd : forall gT (R : {group gT}) p x,
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
case/exponent_odd_nil23: (pR) => // [|expR1p]; last move/(_ sR1R') => morphRp.
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

End ExtremalOhm1.

Section OddNonCyclic.

Variables (gT : finGroupType) (p : nat) (R : {group gT}).
Hypotheses (pR : p.-group R) (oddR : odd #|R|) (ncycR : ~~ cyclic R).

(* This is B & G, Lemma 4.5(a), or Gorenstein 5.4.10. *)
Lemma ex_odd_normal_abelem2 : exists2 S : {group gT}, S <| R & S \in 'E_p^2(R).
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
apply: Ohm1_extremal_odd Mx _; rewrite ?(oddSg sMR) //.
by rewrite -divgS /= -defN // oM oN expnS mulnK // expn_gt0 prime_gt0.
Qed.

(* This is B & G, Lemma 4.5(c). *)
Lemma Ohm1_odd_ucn2 :
  let Z := 'Ohm_1('Z_2(R)) in ~~ cyclic Z /\ exponent Z %| p.
Proof. 
have [S nsSR] := ex_odd_normal_abelem2; case/pnElemP=> sSR abelS dimS2 Z.
have [pS cSS expSp]:= and3P abelS; have nilR := pgroup_nil pR.
case: (eqsVneq S 1) dimS2 => [-> | ntS dimS2]; first by rewrite cards1 logn1.
have [p_pr _ _] :=  pgroup_pdiv pS ntS.
pose SR := [~: S, R]; pose SRR := [~: SR, R].
have sSR_S: SR \subset S by rewrite commg_subl normal_norm.
have sSRR_SR: SRR \subset SR by rewrite commSg.
have sSR_R := subset_trans sSR_S sSR.
have{ntS} prSR: SR \proper S.
  by rewrite (nil_comm_properl nilR) // subsetI subxx -commg_subl.
have SRR1: SRR = 1.
  case: (eqVneq SR 1) => [SR1 | ntSR]; first by rewrite /SRR SR1 comm1G. 
  have prSRR: SRR \proper SR.
    rewrite /proper sSRR_SR; apply: contra ntSR => sSR_SRR.
    by rewrite (implyP (forallP nilR _)) // subsetI sSR_R.
  have pSR := pgroupS sSR_R pR; have pSRR := pgroupS sSRR_SR pSR.
  have [_ _ [e oSR]] := pgroup_pdiv pSR ntSR; have [f oSRR] := p_natP pSRR.
  have e0: e = 0.
    have:= proper_card prSR; rewrite oSR -(part_pnat pS) p_part dimS2.
    by rewrite ltn_exp2l ?prime_gt1 // !ltnS leqn0; move/eqP.
  apply/eqP; have:= proper_card prSRR; rewrite trivg_card1 oSR oSRR e0.
  by rewrite ltn_exp2l ?prime_gt1 // ltnS; case f.
have sSR_ZR: [~: S, R] \subset 'Z(R).
  by rewrite subsetI sSR_R /=; apply/commG1P.
have sS_Z2R: S \subset 'Z_2(R).
  rewrite ucnSnR; apply/subsetP=> s Ss; rewrite inE (subsetP sSR) //= ucn1.
  by rewrite (subset_trans _ sSR_ZR) ?commSg ?sub1set.
have sZ2R_R := ucn_sub 2 R; have pZ2R := pgroupS sZ2R_R pR.
have pZ: p.-group Z. 
  apply: pgroupS pR; exact: subset_trans (Ohm_sub _ _) (ucn_sub 2 R).
have sSZ: S \subset Z.
  apply/subsetP=> s Ss; rewrite /Z (OhmE 1 pZ2R) mem_gen // inE.
  by rewrite (subsetP sS_Z2R) //= (exponentP expSp).
have ncycX: ~~ cyclic S by rewrite (abelem_cyclic abelS) dimS2.
split; first by apply: contra ncycX; exact: cyclicS.
have nclZ2R : nil_class 'Z_2(R) <= 2 + _ := leq_trans (nil_class_ucn _ _) _.
by have [] := exponent_odd_nil23 pZ2R (oddSg sZ2R_R oddR) (nclZ2R _ _).
Qed.

End OddNonCyclic.

(* Some "obvious" consequences of the above, which are used casually and      *)
(* pervasively throughout B & G.                                              *)
Lemma odd_pgroup_rank1_cyclic : forall gT p (G : {group gT}),
  p.-group G -> odd #|G| -> cyclic G = ('r_p(G) <= 1).
Proof.
move=> gT p G pG oddG; apply/idP/idP=> [cycG | dimG1].
  have cGG := cyclic_abelian cycG; rewrite p_rank_abelian //.
  by rewrite -abelem_cyclic ?(cyclicS (Ohm_sub _ _)) ?Ohm1_abelem.
apply: contraLR dimG1 => ncycG; rewrite -ltnNge; apply/p_rank_geP.
by have [E _ EP2_E] := ex_odd_normal_abelem2 pG oddG ncycG; exists E.
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

(* This is B & G, Theorem 4.6 (a stronger version of 4.5(a)). *)
Lemma odd_normal_abelem2_exists : forall gT p (R S : {group gT}),
    p.-group R -> odd #|R| -> S <| R -> ~~ cyclic S ->
  exists E : {group gT}, [/\ E \subset S, E <| R & E \in 'E_p^2(R)].
Proof.
move=> gT p R S pR oddR nsSR ncycS; have sSR := normal_sub nsSR.
have{sSR ncycS} []:= Ohm1_odd_ucn2 (pgroupS sSR pR) (oddSg sSR oddR) ncycS.
set Z := 'Ohm_1(_) => ncycZ expZp.
have chZS: Z \char S := char_trans (Ohm_char 1 _) (ucn_char 2 S).
have{nsSR}nsZR: Z <| R := char_normal_trans chZS nsSR.
have [sZR _] := andP nsZR; have pZ: p.-group Z := pgroupS sZR pR.
have geZ2: 2 <= logn p #|Z|.
  rewrite (odd_pgroup_rank1_cyclic pZ (oddSg sZR oddR)) -ltnNge /= -/Z in ncycZ.
  by case/p_rank_geP: ncycZ => E; case/pnElemP=> sEZ _ <-; rewrite lognSg.
have [E [sEZ nsER oE]] := normal_pgroup pR nsZR geZ2.
have [sER _] := andP nsER; have{pR} pE := pgroupS sER pR.
have{geZ2} p_pr: prime p by move: geZ2; rewrite lognE; case: (prime p).
have{oE p_pr} dimE2: logn p #|E| = 2 by rewrite oE pfactorK.
exists E; split; rewrite ?(subset_trans _ (char_sub chZS)) {chZS nsZR}//.
rewrite !inE /abelem sER pE (p2group_abelian pE) dimE2 //= andbT.
by apply: (dvdn_trans _ expZp); apply: exponentS.
Qed.

(* This is B & G, Lemma 4.7, and (except for the trivial converse) Gorenstein *)
(* 5.4.15 and Aschbacher 23.17.                                               *)
Lemma rank2_SCN3_empty : forall gT p (R : {group gT}),
  p.-group R -> odd #|R| -> ('r(R) <= 2) = ('SCN_3(R) == set0).
Proof.
move=> gT p R pR oddR; apply/idP/idP=> [leR2 | SCN_3_empty].
  apply/set0Pn=> [[A]]; case/setIdP; case/SCN_P; case/andP=> sAR _ _.
  by rewrite ltnNge (leq_trans (rankS sAR)).
rewrite (rank_pgroup pR) leqNgt; apply/negP=> gtR2.
have ncycR: ~~ cyclic R by rewrite (odd_pgroup_rank1_cyclic pR) // -ltnNge ltnW.
have{ncycR} [Z nsZR] := ex_odd_normal_abelem2 pR oddR ncycR.
case/pnElemP=> sZR abelZ dimZ2; have [pZ cZZ _] := and3P abelZ.
have{SCN_3_empty} defZ: 'Ohm_1('C_R(Z)) = Z.
  apply: (Ohm1_cent_max_normal_abelem _ pR).
    by have:= oddSg sZR oddR; rewrite -(part_pnat pZ) p_part dimZ2 odd_exp.
  apply/maxgroupP; split=> [|H]; first exact/andP.
  case/andP=> nsHR abelH sZH; have [pH cHH _] := and3P abelH.
  apply/eqP; rewrite eq_sym eqEproper sZH /=.
  pose normal_abelian := [pred K : {group gT} | (K <| R) && abelian K].
  have [|K maxK sHK] := @maxgroup_exists _ normal_abelian H; first exact/andP.
  apply: contraL SCN_3_empty => ltZR; apply/set0Pn; exists K.
  rewrite inE (max_SCN pR) {maxK}//= -dimZ2 (leq_trans _ (rankS sHK)) //.
  by rewrite (rank_abelem abelH) properG_ltn_log.
have{gtR2} [A] := p_rank_geP gtR2; pose H := 'C_A(Z); pose K := H <*> Z.
case/pnElemP=> sAR abelA dimA3; have [pA cAA _] := and3P abelA.
have{nsZR} nZA := subset_trans sAR (normal_norm nsZR).
have sHA: H \subset A := subsetIl A _; have abelH := abelemS sHA abelA.
have geH2: logn p #|H| >= 2. 
  rewrite -ltnS -dimA3 -(LaGrange sHA) logn_mul // -addn1 leq_add2l /= -/H.
  by rewrite logn_quotient_cent_abelem ?dimZ2.
have{abelH} abelK : p.-abelem K.
  by rewrite (cprod_abelem _ (cprodEgen _)) ?subsetIr ?abelH.
suffices{sZR cZZ defZ}: 'r(Z) < 'r(K).
  by rewrite ltnNge -defZ rank_Ohm1 rankS // mulgen_subG setSI // subsetI sZR.
rewrite !(@rank_abelem _ p) // properG_ltn_log ?abelem_pgroup //= -/K properE.
rewrite mulgen_subr mulgen_subG subxx andbT subEproper; apply: contraL geH2.
case/predU1P=> [defH | ltHZ]; last by rewrite -ltnNge -dimZ2 properG_ltn_log.
rewrite -defH [H](setIidPl _) ?dimA3 // in dimZ2.
by rewrite centsC -defH subIset // -abelianE cAA.
Qed.

End Section4.
