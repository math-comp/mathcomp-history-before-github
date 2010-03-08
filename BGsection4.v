Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime binomial.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent abelian. 
Require Import maximal hall gfunc BGsection1.

(******************************************************************************)
(*   This file covers B & G, section 4, i.e., the proof the a structure       *)
(* theorem for solvable groups with a small (of rank at most 2) Fitting       *)
(* subgroup.                                                                  *)
(******************************************************************************)

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
pose f n := 'C(n, 3); pose g n := 'C(n, 3).*2 + 'C(n, 2).
have fS : forall n, f n.+1 = 'C(n, 2) + f n.
  by move=> n; rewrite /f binS addnC. 
have gS : forall n, g n.+1 = 'C(n, 2).*2 + 'C(n, 1) + g n.
  by move=> n; rewrite /g !binS double_add -!addnA; do 3!nat_congr.
case: (eqsVneq R 1) => [-> |].
  rewrite Ohm1 exponent1 der_sub dvd1n; split=> // _ u v; do 2!move/set1P->.
  by rewrite !(mulg1, exp1gn).
case/(pgroup_pdiv pR)=> p_pr p_dv_R _.
have pdivbin2: p %| 'C(p, 2).
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
  (u * v) ^+ n = u ^+ n * v ^+ n * r ^+ 'C(n, 2)
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
  have ->: [~ v ^+ n, u] = r ^+ n * [~ r, v] ^+ 'C(n, 2). 
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
    have:= proper_card prSR; rewrite oSR -(part_pnat_id pS) p_part dimS2.
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
    by have:= oddSg sZR oddR; rewrite -(part_pnat_id pZ) p_part dimZ2 odd_exp.
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

(* B & G, Proposition 4.8 (a). *)
Lemma pgroup_rank_le2_exponentp : forall gT (R : {group gT}) p,
  p.-group R -> rank R <= 2 -> exponent R %| p -> logn p #|R| <= 3.
Proof.
move=> gT R p pR rankR expR.
have [A max_na_A]: {A | [max A | (A <| R) && abelian A]}.
  by apply: ex_maxgroup; exists 1%G; rewrite normal1 abelian1.
have {max_na_A} SCN_A := max_SCN pR max_na_A.
have abelA := SCN_abelian SCN_A; case/SCN_P: SCN_A => nAR cRAA.
have sAR := normal_sub nAR; have pA := pgroupS sAR pR.
have pabelemA : p.-abelem A.
  by rewrite /abelem pA abelA /= (dvdn_trans (exponentS sAR) expR).
have cardA : logn p #|A| <= 2.
  by rewrite -rank_abelem // (leq_trans (rankS sAR) rankR). 
have cardRA : logn p #|R : A| <= 1.
  by rewrite -cRAA logn_quotient_cent_abelem // (normal_norm nAR).
rewrite -(LaGrange sAR) logn_mul ?cardG_gt0 //.
by apply: (leq_trans (leq_add cardA cardRA)).
Qed.

(* B & G, Proposition 4.8 (b). *)
Lemma pgroup_rank_le2_Ohm1 : forall gT (R : {group gT}) p,
  p.-groupR -> rank R <= 2 -> p > 3 -> exponent 'Ohm_1(R) %| p.
Proof.
move=> gT R p pR rankR pgt3.
case Req1 : (R == 1%G); first by rewrite (eqP Req1) Ohm1 exponent1 dvd1n.
case: (pgroup_pdiv pR (negbT Req1)) => primep _ _ {Req1}.
case: (even_prime primep) => oddp; first by rewrite oddp in pgt3.
apply/negPn; apply/negP => expOR_ndivp.
have [U]: {U | [min U | ~~ (exponent 'Ohm_1(U) %| p)] & (U \subset R)}.
  by apply: mingroup_exists; rewrite expOR_ndivp.
case/mingroupP => /= expUR_ndivp minU sUR {expOR_ndivp}.
apply: (negP expUR_ndivp); have pU := pgroupS sUR pR.
apply: (proj1 (exponent_odd_nil23 pU (odd_pgroup_odd oddp pU) _)). 
rewrite pgt3 addn1.
case gsetU1: (group_set [set x \in U | x ^+ p == 1]).
  case/negP: expUR_ndivp; apply/exponentP => x.
  by rewrite (OhmE 1 pU) gen_set_id // inE expn1; case/andP => _; case/eqP.
move: gsetU1; rewrite /group_set inE group1 exp1gn eqxx; case/subsetPn=> xy.
case/imset2P=> x y; case/setIdP=> Ux xp1; case/setIdP=> Uy yp1 ->{xy}.
rewrite inE groupM //= => nt_xyp; pose XY := <[x]> <*> <[y]>.
have {nt_xyp} XYeqU : XY = U.
  have sXY_U : XY \subset U by rewrite mulgen_subG !cycle_subG Ux Uy.
  have pXY := pgroupS sXY_U pU.
  apply: minU => //=; apply/negP; move/exponentP => expXY; apply: (negP nt_xyp).
  rewrite expXY // groupM //= (OhmE 1 pXY) mem_gen // inE expn1 /=.
    by rewrite (subsetP (mulgen_subl _ _)) //= cycle_id.
  by rewrite (subsetP (mulgen_subr _ _)) //= cycle_id.
have sXU : <[x]> \subset U by rewrite cycle_subG.
have XneqU : ~ (<[x]> = U).
  move=> Xeq; apply: (negP expUR_ndivp); rewrite -Xeq.
  apply: (dvdn_trans (exponentS (Ohm_sub _ _))).
  by apply: (dvdn_trans (exponent_dvdn _)); rewrite order_dvdn.
case: (maximal_exists sXU); first by move/XneqU.
case=> S maxS sXS; have nsSU := p_maximal_normal pU maxS.
move: (maxgroupp maxS) => /= pSU; have neSU := proper_neq pSU.
have sSU := normal_sub nsSU; have pgrpS := pgroupS sSU pU.
have nsOS_U := char_normal_trans (Ohm_char 1 S) nsSU.
have sOS_U := normal_sub nsOS_U; have nOS_U := normal_norm nsOS_U.
have OSx : x \in 'Ohm_1(S).
  by rewrite (OhmE 1 pgrpS) mem_gen // inE (subsetP sXS) ?cycle_id //=.
pose OS_Y := 'Ohm_1(S) <*> <[y]>; have Ueq : OS_Y = U.
  apply/eqP; rewrite eqEsubset mulgen_subG (normal_sub nsOS_U) cycle_subG Uy /=.
  rewrite -XYeqU mulgen_subG mulgen_subr andbT cycle_subG. 
  by rewrite (subsetP (mulgen_subl _ _)).
have expOS : exponent 'Ohm_1(S) %| p.
  apply/negPn; apply/negP => expOS_ndivp; apply: (negP neSU); apply/eqP.
  by apply: minU => //.
have pOS := pgroupS (Ohm_sub 1 _) pgrpS.
have sOS_R := subset_trans sOS_U sUR.
have cardOS : logn p #|'Ohm_1(S)| <= 3.
  by apply: pgroup_rank_le2_exponentp => //; apply: (leq_trans (rankS sOS_R)).
have cardUOS : logn p #|U / 'Ohm_1(S)| <= 1.
  rewrite -Ueq /OS_Y mulgenE setUC -mulgenE quotient_mulgen; last first.
    by rewrite (subset_trans _ (normal_norm nsOS_U)) // cycle_subG.
  rewrite -{6}(pfactorK 1 primep) expn1 dvdn_leq_log ?prime_gt0 //.
  by rewrite (dvdn_trans (dvdn_quotient _ _)) // -orderE order_dvdn.
rewrite (leq_trans (nil_class_pgroup pU)) // leq_maxl /= -[3]succnK. 
rewrite -!subn1 leq_sub2r // -(LaGrange sOS_U) logn_mul // -card_quotient //.
by apply: (leq_trans (leq_add cardOS cardUOS)).
Qed.

(* This is B & G, Lemma 4.9 *)
Lemma pgroup_Ohm1_p2_normal_p2 : forall gT (R : {group gT}) p,
  p.-groupR -> p > 3 -> logn p #|'Ohm_1(R)| <= 2 ->
    forall (T : {group gT}), T <| R -> logn p #|'Ohm_1(R/T)| <= 2.
Proof. 
move=> gT R p pR pgt3; move: {2}_.+1 (ltnSn #|R|) => n.
elim: n gT => // n IHn gT in R pR *; move=> cardRlt cardOR T nsTR.
case Req1 : (R == 1%G); first by rewrite (eqP Req1) quotient1 Ohm1 cards1 logn1.
case: (pgroup_pdiv pR (negbT Req1)) => primep _ _.
case: (even_prime primep) => oddp; first by rewrite oddp in pgt3.
have oddR := odd_pgroup_odd oddp pR; rewrite leqNgt; apply/negP => cardO1RTgt.
have [U minU] : {U | [min U | (U <| R) && (2 < logn p #|'Ohm_1(R / U)|)]}.
  by apply: ex_mingroup; exists T; rewrite nsTR.
case/mingroupP: minU; case/andP => nsUR cardO1RUgt minU {T nsTR cardO1RTgt}.
have [sUR nUR] := (andP nsUR); have pU := pgroupS sUR pR.   
have neU1 : U != 1%G.
  apply: contraL cardO1RUgt; move/eqP => ->.
  have : 'Ohm_1(R) \isog 'Ohm_1(R / 1) by rewrite bgFunc_isog ?quotient1_isog.
  move/isog_card <-; by rewrite -leqNgt.
case (eqVneq (logn p #|U|) 1%N) => [cardU|] {T nsTR cardO1RTgt}; last first.
  case: (pgroup_pdiv pU neU1) => _ _ [m cardU].
  rewrite neq_ltn ltnS leqn0 {1}cardU pfactorK //= => cardUlt.
  case/idPn: cardO1RUgt; rewrite -leqNgt.
  case/trivgPn: (nil_meet_Z (pgroup_nil pR) nsUR neU1) => x.
  case/setIP => /= Ux ZRx nx1; pose X := <[x]>%G.
  have sXU : X \subset U by rewrite cycle_subG.
  have pX := pgroupS sXU pU.
  have nX1 : X != 1%G by apply/trivgPn; exists x; rewrite // cycle_id.
  case: (pgroup_pdiv pX nX1) => _ _ [k cardX].
  have cardXgt : 1 <= logn p #|X| by rewrite cardX pfactorK.
  case: (normal_pgroup pX (normal_refl X) cardXgt) => Z [sZX nsZX cardZ].
  have nZ1 : Z != 1%G by rewrite -cardG_gt1 cardZ prime_gt1.
  have sZU := subset_trans sZX sXU; have sZR := subset_trans sZU sUR.
  have nsZR : Z <| R.
    rewrite /normal sZR /= cents_norm // centsC (subset_trans sZX) //.
    by rewrite cycle_subG (subsetP _ _ ZRx) // subsetIr.
  have neZU : ~ Z = U by move=> eZU; move: cardUlt; rewrite -eZU cardZ pfactorK.
  have cardORZle : logn p #|'Ohm_1(R / Z) | <= 2.
    rewrite leqNgt; apply/negP => cardORZgt; apply: neZU; apply: val_inj.
    by apply: (minU Z); rewrite // nsZR.
  have RUZUisog := third_isog sZU nsZR nsUR.
  have : 'Ohm_1(R / Z / (U / Z)) \isog 'Ohm_1(R / U) by apply: bgFunc_isog.
  have cardRZlt := ltn_quotient nZ1 sZR.
  move/isog_card <-; apply: IHn; rewrite ?quotient_pgroup ?quotient_normal //. 
  by rewrite (leq_trans cardRZlt).
case eO1RU: (R / U == 'Ohm_1(R / U)); last first.
  have nsO1RU_RU := (char_normal (Ohm_char 1 (R / U))).
  case: (inv_quotientN nsUR nsO1RU_RU)=> K eO1RUKU sUK nsKR.
  have sKR := (normal_sub nsKR); have nsUK := (normalS sUK sKR nsUR).
  rewrite ltnNge in cardO1RUgt; move/negP: cardO1RUgt; apply.
  rewrite -Ohm_id eO1RUKU; apply: IHn; rewrite ?(pgroupS sKR) //.
    rewrite ltnS in cardRlt; rewrite (leq_trans _ cardRlt) // proper_card //.
    by rewrite properEneq sKR (contra _ (negbT eO1RU)) //= eO1RUKU; move/eqP ->.
  by apply: (leq_trans _ cardOR); apply: lognSg; apply: OhmS.
have pRU := (quotient_pgroup U pR).
have [cardRU expRU] : logn p #| R / U | = 3 /\ exponent (R / U) %| p.
  case rankRU: ('r(R / U) > 2). 
    move/idP: rankRU; rewrite ltnNge (rank2_SCN3_empty pRU) ?quotient_odd //.
    case/set0Pn=> E; rewrite inE; case/andP=> SCN_E rankE.
    have abelE := SCN_abelian SCN_E; have [nsERU _] := (SCN_P _ _ SCN_E).
    have pE := (pgroupS (normal_sub nsERU) pRU); pose OE := 'Ohm_1(E).
    have nsOE_RU := (char_normal_trans (Ohm_char 1 _) nsERU).
    have pabelemOE : p.-abelem OE by apply: Ohm1_abelem.
    have pOE := (pgroupS (Ohm_sub _ _) pE).
    have cardOEgt : logn p #|'Ohm_1(E)| >= 3.
      by rewrite -rank_abelem // rank_Ohm1.
    case: (normal_pgroup pRU nsOE_RU cardOEgt) => E1 [sE1_OE nsE1_RU cardE1].
    have pabelemE1 := (abelemS sE1_OE pabelemOE).
    case: (inv_quotientN nsUR nsE1_RU)=> K eE1KU sUK nsKR.
    have sKR := (normal_sub nsKR); have pK := pgroupS sKR pR.
    have cardOKle : logn p #|'Ohm_1(K)| <= 2.
      by rewrite (leq_trans _ cardOR) ?dvdn_leq_log ?cardG_gt0 ?cardSg // OhmS.
    have cardOKUgt : logn p #|'Ohm_1(K / U)| > 2.
      by rewrite -eE1KU (Ohm1_id pabelemE1) cardE1 pfactorK.
    have nsKU := (normalS sUK sKR nsUR).
    have <- : K = R.
      apply/eqP; apply: contraLR cardOKUgt => neKR; rewrite -leqNgt.
      have pKR : K \proper R by rewrite properEneq neKR.
      by apply: IHn => //; apply: (leq_trans (proper_card pKR)); rewrite -ltnS.
    rewrite -eE1KU; split; first by rewrite cardE1 pfactorK.
    rewrite (dvdn_trans (exponentS sE1_OE)) // exponent_Ohm1_class2 //.
    by rewrite (leq_trans _ (leqnSn _)) // nil_class1.
  move: rankRU; move/negbT; rewrite -leqNgt=> rankRU.
  have expRU : exponent (R / U) %| p.
    by rewrite (eqP eO1RU) pgroup_rank_le2_Ohm1.
  split => //; apply/eqP; rewrite eqn_leq pgroup_rank_le2_exponentp //=.
  by rewrite (eqP eO1RU).
have {cardRU} cardR : logn p #|R| = 4.
  rewrite -(LaGrange sUR) logn_mul ?cardG_gt0 // cardU.
  by rewrite -card_quotient ?(normal_norm nsUR) // cardRU. 
have neRU : (R / U) != 1.
  by apply/negP=> eRU1; rewrite (eqP eRU1) Ohm1 cards1 logn1 in cardO1RUgt. 
have ncycR : ~~ cyclic R.
  apply/negP=> cycR; move: cardO1RUgt; have cycRU := quotient_cyclic U cycR. 
  by rewrite (Ohm1_cyclic_pgroup_prime cycRU pRU neRU) (pfactorK 1).
case: (ex_odd_normal_abelem2 pR oddR ncycR)=> S nSR {ncycR}.
case/pnElemP=> sSR pabelS cardS.
have cardO1R : logn p #|'Ohm_1(R)| = 2.
  apply/eqP; rewrite eqn_leq cardOR /= -cardS lognSg // -(Ohm1_id pabelS).
  exact: OhmS.
have pRO1R : p.-group (R / 'Ohm_1(R)) by rewrite quotient_pgroup.
have nsO1R := char_normal (Ohm_char 1 R); have [sO1R nO1R] := (andP nsO1R).
have nilclassR : nil_class R <= 3.
  by rewrite (leq_trans (nil_class_pgroup pR)) // cardR.
have sR'O1R : R^`(1) \subset 'Ohm_1(R).
  rewrite der1_min // (p2group_abelian pRO1R) //.
  by rewrite card_quotient // -divgS // logn_div ?cardSg // cardR cardO1R.
case: (exponent_odd_nil23 pR oddR _) => [|_ morph_exp]; first by rewrite pgt3.
pose expp := Morphism (morph_exp sR'O1R).
have : logn p #|R / 'ker expp| <= 1.
  rewrite (isog_card (first_isog expp)) -cardU lognSg //= morphimEsub //.
  apply/subsetP=> x; case/imsetP=> g Rg ->{x} /=; apply: coset_idr.
    by rewrite groupX ?(subsetP nUR).
  by rewrite morphX ?(subsetP nUR) // (exponentP expRU) // mem_quotient.
apply/negP; rewrite -ltnNge card_quotient ?ker_norm // -divgS ?subsetIl //.
rewrite logn_div ?cardSg ?subsetIl // cardR -ltn_add_sub addn1 !ltnS. 
rewrite -cardO1R lognSg //; apply/subsetP=> g /=; case/setIP=> Rg.
by rewrite !inE /= (OhmE _ pR) => gp1; rewrite mem_gen // inE Rg.
Qed.

(* move this to cyclic.v? *)
Section Metacyclic.

Variable gT : finGroupType.
Implicit Type G : {group gT}.

Definition metacyclic G := existsb H, 
  [&& ((H : {group gT}) <| G), cyclic H & cyclic (G / H)].

Lemma metacyclicP : forall G,
  reflect (exists H, [/\ (H : {group gT}) <| G, cyclic H & cyclic (G / H)]) 
    (metacyclic G).
Proof. 
move=> G; apply: (iffP existsP) => [] [H]; [case/and3P|]; exists H => //.
by apply/and3P.
Qed.

End Metacyclic.

(* This is B & G, Theorem 4.10 *)
Lemma Ohm1_metacyclic_pgroup_odd_prime: forall gT (R : {group gT}) p,
  metacyclic R -> p.-group R -> odd #|R| -> ~~ cyclic R -> 
  logn p #|'Ohm_1(R)| = 2.
Proof.
move=> gT R p; case/metacyclicP=> S' [nsS'R cycS' cycRS'] pR oddR ncycR.
have [S maxS] : {S | [max S | [&& (S <| R), cyclic S & cyclic (R / S)]]}. 
  by apply: ex_maxgroup; exists S'; apply/and3P.
case/maxgroupP: maxS; case/and3P => nsSR cycS cycRS maxS.
have {S' nsS'R cycS' cycRS'} neR1 : R != 1%G.
  by apply: (contra _ ncycR); move/eqP=> ->; apply cyclic1.
have neRS1 : (R / S) != 1.
  apply: (contra _ ncycR); move/eqP; rewrite -(trivg_quotient S).
  by move/(quotient_inj nsSR (normal_refl S)) => ->.
have [primep _ _] := (pgroup_pdiv pR neR1); have pRS := (quotient_pgroup S pR).
pose ORS := 'Ohm_1(R/S); have nsORS_RS := char_normal (Ohm_char 1 (R/S)).
case: (inv_quotientN nsSR nsORS_RS) => /= T ORSeq sST nsTR.
have sTR := normal_sub nsTR; have pT := pgroupS sTR pR.
have nST := (normal_norm (normalS sST sTR nsSR)).
have cardORS: #|'Ohm_1(R/S)| = p by apply: Ohm1_cyclic_pgroup_prime.
have ->: 'Ohm_1(R) = 'Ohm_1(T).
  apply/eqP; rewrite eqEsubset (OhmS _ sTR) andbT (OhmE 1 pR) (OhmE 1 pT).
  rewrite gen_subG sub_gen //; apply/subsetP=> g; rewrite !inE.
  case/andP=> Rg egp1; have NSg := (subsetP (normal_norm nsSR) _ Rg).
  rewrite egp1 andbT -sub1set -(quotientSGK _ sST) ?quotient_set1 ?sub1set //.
  rewrite -ORSeq (OhmE 1 pRS) mem_gen // inE mem_quotient //= -morphX //=.
  by rewrite (eqP egp1) coset_id.
case/cyclicP: cycS=> x eSX.
have Tx : x \in T by rewrite (subsetP sST) // eSX cycle_id.
have indexTX : #|T : <[x]>| = p.
  by rewrite -eSX -card_quotient // -ORSeq cardORS.
have ncycT : ~~ cyclic T.
  apply/negP=> cycT; move: (prime_gt1 primep); rewrite -cardORS ORSeq.
  suff ->: T :=: S; first by rewrite trivg_quotient cards1.
  apply: maxS; rewrite ?sST // nsTR cycT /=.
  by rewrite -(isog_cyclic (third_isog sST nsSR nsTR)) quotient_cyclic.
move: (Ohm1_extremal_odd pT (oddSg sTR oddR) ncycT Tx indexTX).
by rewrite inE; case/andP=> _; case/eqP.  
Qed.

(* This is B & G, Theorem 4.18(b) *)
Lemma rank2_pdiv_complement : forall gT (G : {group gT}) (p := pdiv #|G|),
  odd #|G| -> solvable G -> 'r_p(G) <= 2 -> p^'.-Hall(G) 'O_p^'(G).
Proof.
Admitted.

(* This is B & G, Corollary 4.19 *)
Lemma rank2_cent_chief : forall gT p (G Gs U V : {group gT}),
    odd #|G| -> solvable G -> Gs <| G -> 'r_p(Gs) <= 2 -> 
    chief_factor G V U -> p.-group (U / V) -> U \subset Gs ->
  G^`(1) \subset 'C(U / V | 'Q).
Proof.
Admitted.

(* This is B & G, Lemma 4.20(a) *)
Lemma rank2_der1_sub_Fitting : forall gT (G : {group gT}),
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> G^`(1) \subset 'F(G).
Proof.
move=> gT G oddG solG Fle2.
apply: subset_trans (chief_stab_sub_Fitting solG _) => //.
rewrite subsetI der_sub; apply/bigcapsP=> [[U V] /=]; case/andP=> chiefUV sUF.
have [p p_pr] := is_abelemP (sol_chief_abelem solG chiefUV).
case/andP=> pUV _; apply: rank2_cent_chief (Fitting_normal _) _ _ pUV sUF => //.
exact: leq_trans (p_rank_le_rank p _) Fle2.
Qed.

(* This is B & G, Lemma 4.20(b) *)
Lemma rank2_char_Sylow_normal : forall gT (G S T : {group gT}),
  odd #|G| -> solvable G -> 'r('F(G)) <= 2 -> 
  Sylow G S -> T \char S -> T \subset S^`(1) -> T <| G.
Proof.
move=> gT G S T oddG solG; set F := 'F(G) => Fle2.
case/SylowP=> p p_pr sylS charT sTS'; have [sSG pS _] := and3P sylS.
have nsFG: F <| G := Fitting_normal G; have [sFG nFG] := andP nsFG.
have nFS := subset_trans sSG nFG; have nilF: nilpotent F := Fitting_nil _.
have cGGq: abelian (G / F).
  by rewrite sub_der1_abelian ?rank2_der1_sub_Fitting.
have nsFS_G: F <*> S <| G.
  rewrite -(quotientGK nsFG) norm_mulgenEr // -(quotientK nFS) cosetpre_normal.
  by rewrite -sub_abelian_normal ?quotientS.
have sylSF: p.-Sylow(F <*> S) S.
  by rewrite (pHall_subl _ _ sylS) ?mulgen_subr // mulgen_subG sFG.
have defG: G :=: F * 'N_G(S).
  rewrite -{1}(Frattini_arg nsFS_G sylSF) /= norm_mulgenEr // -mulgA.
  by congr (_ * _); rewrite mulSGid // subsetI sSG normG.
rewrite /normal (subset_trans (char_sub charT)) //= defG mulG_subG /= -/F.
rewrite setIC andbC subIset /=; last by rewrite (char_norm_trans charT).
case/dprodP: (nilpotent_pcoreC p nilF); rewrite /= -/F => _ defF cFpFp' _.
have defFp: 'O_p(F) = F :&: S.
  rewrite -{2}defF -group_modl ?coprime_TIg ?mulg1 //.
    by rewrite coprime_sym (pnat_coprime pS (pcore_pgroup _ _)).
  by rewrite p_core_Fitting pcore_sub_Hall.
rewrite -defF mulG_subG /= -/F defFp setIC subIset ?(char_norm charT) //=.
rewrite cents_norm // centsC (subset_trans _ cFpFp') // defFp subsetI.
rewrite (char_sub charT) (subset_trans (subset_trans sTS' (dergS 1 sSG))) //.
exact: rank2_der1_sub_Fitting.
Qed.

(* This is the first statement of B & G, Lemma 4.20(c) *)
Lemma p_rank_2_min_p'core_Hall : forall gT (G : {group gT}),
    odd #|G| -> solvable G -> 'r('F(G)) <= 2 ->
  let p := pdiv #|G| in (p^'.-Hall(G) 'O_p^'(G) : Prop).
Proof.
move=> gT G oddG solG; set F := 'F(G) => Fle2 p.
have nsFG: F <| G := Fitting_normal G; have [sFG nFG] := andP nsFG.
have [H] := inv_quotientN nsFG  (pcore_normal p^' _).
rewrite /= -/F => defH sFH nsHG; have [sHG nHG] := andP nsHG.
have [P sylP] := Sylow_exists p H; have [sPH pP _] := and3P sylP.
have sPF: P \subset F.
  rewrite -quotient_sub1 ?(subset_trans (subset_trans sPH sHG)) //.
  rewrite -(setIidPl (quotientS _ sPH)) -defH coprime_TIg //.
  by rewrite coprime_morphl // (pnat_coprime pP (pcore_pgroup _ _)).
have nilGq: nilpotent (G / F).
  by rewrite abelian_nil ?sub_der1_abelian ?rank2_der1_sub_Fitting.
have pGq: p.-group (G / H).
  rewrite /pgroup -(isog_card (third_isog sFH nsFG nsHG)) /= -/F -/(pgroup _ _).
  case/dprodP: (nilpotent_pcoreC p nilGq) => /= _ <- _ _.
  by rewrite defH quotient_mulg quotient_pgroup ?pcore_pgroup.
rewrite pHallE pcore_sub -(LaGrange sHG) partn_mul // -card_quotient //=.
have hallHp': p^'.-Hall(H) 'O_p^'(H).
  case p'H: (p^'.-group H).
    by rewrite pHallE /= pcore_pgroup_id ?subxx //= part_pnat_id.
  have def_p: p = pdiv #|H|.
    have [p_pr pH]: prime p /\ p %| #|H|.
      apply/andP; apply: contraFT p'H => p'H; apply/pgroupP=> q q_pr qH.
      by apply: contra p'H; move/eqnP <-; rewrite q_pr qH.
    apply/eqP; rewrite eqn_leq ?pdiv_min_dvd ?prime_gt1 //.
      rewrite pdiv_prime // cardG_gt1.
      by case: eqP p'H => // ->; rewrite pgroup1.
    exact: dvdn_trans (pdiv_dvd _) (cardSg (normal_sub nsHG)).
  rewrite def_p rank2_pdiv_complement ?(oddSg sHG) ?(solvableS sHG) -?def_p //.
  rewrite (p_rank_Sylow sylP) (leq_trans (p_rank_le_rank _ _)) //.
  exact: leq_trans (rankS sPF) Fle2.
rewrite -(card_Hall hallHp') part_p'nat ?pnatNK ?muln1 // subset_leqif_card.
  by rewrite pcore_max ?pcore_pgroup ?(char_normal_trans (pcore_char _ _)).
rewrite pcore_max ?pcore_pgroup // (normalS _ _ (pcore_normal _ _)) //.
rewrite -quotient_sub1 ?(subset_trans (pcore_sub _ _)) //.
rewrite -(setIidPr (quotientS _ (pcore_sub _ _))) coprime_TIg //.
by rewrite coprime_morphr // (pnat_coprime pGq (pcore_pgroup _ _)).
Qed.

(* This is a consequence of B & G, Lemma 4.20(c) *)
Lemma rank2_pcore_geq_Hall : forall gT m (G : {group gT}),
    odd #|G| -> solvable G -> 'r('F(G)) <= 2 ->
  let pi := [pred p | p >= m] in (pi.-Hall(G) 'O_pi(G) : Prop).
Proof.
move=> gT m G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G.
rewrite ltnS => leGn oddG solG Fle2 pi; pose p := pdiv #|G|.
case: (eqVneq 'O_pi(G) G) => [defGpi | not_pi_G].
  by rewrite /pHall pcore_sub pcore_pgroup defGpi indexgg.
have pi'_p: (p \in pi^').
  apply: contra not_pi_G => pi_p; rewrite eqEsubset pcore_sub pcore_max //.
  apply/pgroupP=> q q_pr qG; apply: leq_trans pi_p _.
  by rewrite pdiv_min_dvd ?prime_gt1.
pose Gp' := 'O_p^'(G); have sGp'G: Gp' \subset G := pcore_sub _ _.
have hallGp'pi: pi.-Hall(Gp') 'O_pi(Gp').
  apply: IHn; rewrite ?(oddSg sGp'G) ?(solvableS sGp'G) //; last first.
    by apply: leq_trans (rankS _) Fle2; rewrite /= Fitting_pcore pcore_sub.
  apply: leq_trans (proper_card _) leGn.
  rewrite properEneq pcore_sub andbT; apply/eqP=> defG.
  suff: p \in p^' by case/eqnP.
  have p'G: p^'.-group G by rewrite -defG pcore_pgroup.
  rewrite (pgroupP p'G) ?pdiv_dvd ?pdiv_prime // cardG_gt1.
  by apply: contra not_pi_G; move/eqP->; rewrite (trivgP (pcore_sub _ _)).
have defGp'pi: 'O_pi(Gp') = 'O_pi(G).
  rewrite -pcoreI; apply: eq_pcore => q; apply: andb_idr.
  by apply: contraL => /=; move/eqnP->.
have hallGp': p^'.-Hall(G) Gp' by rewrite p_rank_2_min_p'core_Hall.
rewrite pHallE pcore_sub /= -defGp'pi (card_Hall hallGp'pi) (card_Hall hallGp').
by rewrite partn_part // => q; apply: contraL => /=; move/eqnP->.
Qed.

(* This is another consequence of B & G, Lemma 4.20(c) *)
Lemma rank2_pcore_max_Sylow : forall gT (G : {group gT}),
    odd #|G| -> solvable G -> 'r('F(G)) <= 2 ->
  let p := max_pdiv #|G| in (p.-Sylow(G) 'O_p(G) : Prop).
Proof.
move=> gT G oddG solG Fle2 p; pose pi := [pred q | p <= q].
rewrite pHallE pcore_sub eqn_leq -{1}(part_pnat_id (pcore_pgroup _ _)).
rewrite dvdn_leq ?partn_dvd ?cardSg ?pcore_sub // /=.
rewrite (@eq_in_partn _ pi) => [|q piGq]; last first.
  by rewrite !inE eqn_leq; apply: andb_idl => le_q_p; exact: max_pdiv_max.
rewrite -(card_Hall (rank2_pcore_geq_Hall p oddG solG Fle2)) -/pi.
rewrite subset_leq_card // pcore_max ?pcore_normal //.
apply: sub_in_pnat (pcore_pgroup _ _) => q; move/(piSg (pcore_sub _ _)) => piGq.
by rewrite !inE eqn_leq max_pdiv_max.
Qed.

End Section4.
