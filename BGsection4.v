Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype finfun bigops ssralg finset prime binomial.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups gseries nilpotent sylow.
Require Import abelian maximal hall gfunc BGsection1 BGsection2 matrix.
Require Import mxrepresentation.


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
(* covered by Lemma center_cyclic_abelian, in center.v.                       *)

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

Definition metacyclic G := existsb H, 
  [&& cyclic (H : {group gT}), H <| G & cyclic (G / H)].

Lemma metacyclicP : forall G, 
  reflect (exists H, [/\ cyclic (H : {group gT}), H <| G & cyclic (G / H)]) 
    (metacyclic G).
Proof. 
move=> G; apply: (iffP existsP) => [] [H]; [case/and3P|]; exists H => //.
by apply/and3P.
Qed.

Lemma metacyclic1 : metacyclic 1.
Proof. 
by apply/existsP; exists 1%G; rewrite normal1 trivg_quotient !cyclic1.
Qed.

Lemma cyclic_metacyclic : forall G, cyclic G -> metacyclic G.
Proof.
move=> G; case/cyclicP => x ->; apply/existsP; exists (<[x]>)%G.
by rewrite normal_refl cycle_cyclic trivg_quotient cyclic1.
Qed.

Lemma metacyclicN : forall (G H : {group gT}), 
  metacyclic G -> H <| G -> metacyclic H.
Proof. 
move=> G H; case/metacyclicP=> K [cycK]; case/andP=> sKG nKG cycGK.  
case/andP=> sHG nHG; apply/existsP; exists (H :&: K)%G.
have nKH := (subset_trans sHG nKG).
rewrite (cyclicS (subsetIr _ _)) // /normal subsetIl normsI ?normG //=.
by rewrite setIC (isog_cyclic (second_isog nKH)) /= (cyclicS (quotientS K sHG)).
Qed.

End Metacyclic.

(* This is B & G, Theorem 4.10 *)
Lemma Ohm1_metacyclic_pgroup_odd_prime : forall gT (R : {group gT}) p,
  metacyclic R -> p.-group R -> odd #|R| -> ~~ cyclic R -> 
  'Ohm_1(R)%G \in 'E_p^2(R).
Proof.
move=> gT R p; case/metacyclicP=> S' [cycS' nsS'R cycRS'] pR oddR ncycR.
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
rewrite !inE Ohm_sub /=.
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
by rewrite !inE Ohm_sub.
Qed.

(* This is B & G, Proposition 4.11 *)
Lemma pgroup_Ohm1_p2_metacyclic : forall gT (R : {group gT}) p,
  p.-group R -> p > 3 -> logn p #|'Ohm_1(R)| <= 2 -> metacyclic R.
Proof.
move=> gT R p pR pgt3; move: {2}_.+1 (ltnSn #|R|) => n.
elim: n gT => // n IHn gT in R pR *; move=> cardRlt cardOR.
case: (eqsVneq R 1) => [-> | ntR]; first exact: metacyclic1.
have [primep _ _] := pgroup_pdiv pR ntR.
have oddp : odd p by case: (even_prime primep) pgt3 => [->|].
case cRR : (abelian R).
  have [b Req Rtype] := abelian_structure cRR.
  move: Req cardOR ntR; rewrite unlock -p_rank_abelian // -rank_pgroup //.
  rewrite -size_abelian_type // -{}Rtype size_map.
  case: b => [<-|a [|b []]] //=; rewrite ?eqxx // dprodg1 => Req _ _.
    by rewrite -Req cyclic_metacyclic ?cycle_cyclic.
  apply/existsP; exists <[a]>%G; rewrite cycle_cyclic /=.
  case/dprodP: Req => _ <-; rewrite centsC => cAB _.
  rewrite /normal mulG_subl mul_subG ?normG ?cents_norm //= quotient_mulgr. 
  by rewrite quotient_cycle ?cycle_cyclic // -cycle_subG cents_norm. 
pose R' := R^`(1); pose MR' := 'Mho^1(R').
have nsR'R := der_normal 1 R; have sR'R := normal_sub nsR'R.
have [z [ordz R'ZRz MR'ZRz]] : exists z, 
  [/\ #[z] = p, z \in R' :&: 'Z(R) & MR' != 1 -> z \in MR' :&: 'Z(R)].
  case eMR'1 : (MR' == 1).
    have pR'ZR : p.-group (R' :&: 'Z(R)).
      by rewrite (pgroupS _ pR) // (subset_trans (subsetIl _ _)). 
    have neR'ZR_1: R' :&: 'Z(R) != 1.
      rewrite nil_meet_Z ?(pgroup_nil pR) //; apply/negP; move/eqP.
      by move/commG1P; rewrite -abelianE cRR.
    case: (pgroup_pdiv pR'ZR neR'ZR_1) => _ pdvd _.
    by case: (Cauchy primep pdvd) => z; exists z; split.
  have pMR'ZR : p.-group (MR' :&: 'Z(R)). 
    by rewrite (pgroupS _ pR) // (subset_trans (subsetIr _ _)) // subsetIl.
  have neMR'ZR_1 : MR' :&: 'Z(R) != 1.
    rewrite nil_meet_Z ?(pgroup_nil pR) ?(char_normal_trans (Mho_char 1 _)) //.
    by rewrite eMR'1.
  case: (pgroup_pdiv pMR'ZR neMR'ZR_1) => _ pdvd _.
  case: (Cauchy primep pdvd) => z MR'z ordz; exists z; split => //.
  by apply/setIP; split; case/setIP: MR'z => //; move/(subsetP (Mho_sub 1 _)).
case/setIP: R'ZRz=> R'Z ZRz; pose T := <[z]>.
have sT_ZR : T \subset 'Z(R) by rewrite cycle_subG.
move: (sT_ZR); rewrite subsetI centsC; case/andP=> sTR cTR.
have nTR : R \subset 'N(T) by rewrite cents_norm.
have nsTR : T <| R by rewrite /normal sTR.
have cardORT : logn p #|'Ohm_1(R / T)| <= 2 by apply: pgroup_Ohm1_p2_normal_p2.
have {IHn cardRlt}: metacyclic (R / T).
  rewrite IHn ?quotient_pgroup //= (leq_trans (ltn_quotient _ _)) -1?ltnS //.
  by rewrite cycle_eq1 -order_eq1 ordz neq_ltn prime_gt1 // orbT.
case/metacyclicP=> S; case; case/cyclicP=> aT ->{S}.
case: (cosetP aT) => a NTa ->{aT}; case/(inv_quotientN nsTR)=> /= AT.
pose A := <[a]>; rewrite -quotient_cycle //= -/A -/T => ATTeq sT_AT nsAT_R.
have sAT_R := normal_sub nsAT_R; have nsT_AT := normalS sT_AT sAT_R nsTR.
have ATeq: AT :=: A <*> T.
  apply: (quotient_inj nsT_AT); rewrite ?quotient_mulgen ?cycle_subG -?ATTeq //.
  by rewrite /normal mulgen_subr /= mulgen_subG normG cycle_subG NTa.
rewrite ATTeq (isog_cyclic (third_isog _ _ _)) //=.
case/cyclicP=> bAT; case: (cosetP bAT)=> b NATb ->{bAT}; pose B := <[b]>.
rewrite -quotient_cycle // -[B / AT]quotient_mulgen ?cycle_subG //= -/B=> RATeq.
have {RATeq} Req: R :=: B <*> AT.
  rewrite (quotient_inj nsAT_R _ RATeq) //.
  by rewrite /normal mulgen_subr /= mulgen_subG normG cycle_subG NATb.
have ATa : a \in AT by rewrite ATeq (subsetP (mulgen_subl _ _)) ?cycle_id.
have Ra : a \in R by rewrite Req (subsetP (mulgen_subr _ _)).
have Rb : b \in R by rewrite Req (subsetP (mulgen_subl _ _)) ?cycle_id.
have neATT_1 : (AT / T) != 1.
  apply: (contra _ (negbT cRR))=> ATT1.
  rewrite center_cyclic_abelian ?center_abelian //.
  rewrite -(isog_cyclic (third_isog sT_ZR nsTR (center_normal R))).
  rewrite quotient_cyclic //= Req norm_mulgenEl ?cycle_subG // quotientMl.
    by rewrite (eqP ATT1) mulg1 quotient_cyclic // cycle_cyclic.
  by rewrite cycle_subG // (subsetP nTR).
have nTa : ~~ (a \in T).
  apply: (contra _ neATT_1)=> Ta.
  by rewrite -ATTeq -subG1 quotient_sub1 ?cycle_subG.
pose Ap := <[a^+p]>; pose ApT := Ap <*> T.
have sApT_AT : ApT \subset AT by rewrite mulgen_subG cycle_subG groupX ?Ra. 
have sApT_R : ApT \subset R by apply: (subset_trans sApT_AT sAT_R).
have sT_ApT := mulgen_subr Ap T.
have nsT_ApT : T <| ApT by rewrite (normalS sT_ApT sApT_R).
have ATTeq' : AT / T = <[coset T a]>.
  by rewrite ATeq quotient_mulgen ?cycle_subG // quotient_cycle.
have ApTTeq : ApT / T = <[coset T (a^+p)]>.
  by rewrite quotient_mulgen ?cycle_subG ?groupX // quotient_cycle ?groupX.
have charApTT_ATT : ApT / T \char AT / T.
  by rewrite ATTeq' cycle_subgroup_char // -ATTeq' quotientS.
have nsApT_R : [group of ApT] <| R.
  rewrite -(quotientGK nsTR) -(quotientGK nsT_ApT) cosetpre_normal.
  by apply: (char_normal_trans charApTT_ATT); apply: quotient_normal.
have nsApTT_RT : ApT / T <| R / T by apply: quotient_normal.
have nsApT_AT := (normalS sApT_AT sAT_R nsApT_R).
have {neATT_1} card_ApTAT : #|AT / ApT| = p.
  rewrite -(isog_card (third_isog sT_ApT nsT_AT nsApT_AT)).
  rewrite card_quotient /= ?(normal_norm (char_normal charApTT_ATT)) //. 
  rewrite ATTeq' ApTTeq -divgS /= ?cycle_subG morphX ?groupX ?cycle_id //=. 
  rewrite -!orderE orderXgcd divn_divr ?dvdn_gcdl // mulKn //.
  apply: gcdn_def => //.
  have pATT: p.-group (AT / T) by rewrite quotient_pgroup // (pgroupS sAT_R pR).
  by case: (pgroup_pdiv pATT neATT_1); rewrite /= ATTeq' orderE. 
have sATApT_ZRApT : (AT / ApT) \subset 'Z(R / ApT).
  apply/setIidPl; apply/eqP; rewrite eqEcard subsetIl /= dvdn_leq ?cardG_gt0 //.
  pose W := AT / ApT :&: 'Z(R / ApT).
  have pW: p.-group W.
    by rewrite (pgroupS (subsetIl _ _)) // quotient_pgroup ?(pgroupS sAT_R).
  have neW1 : W != 1.
    rewrite nil_meet_Z ?(pgroup_nil (quotient_pgroup _ pR)) ?quotient_normal //.
    by rewrite trivg_card1 card_ApTAT; apply: (contraL _ pgt3); move/eqP => ->.
  by rewrite card_ApTAT; case: (pgroup_pdiv pW neW1) => _ pdvdW _.
have cRApT_RApT: abelian (R / ApT).
  have nsATApT_RApT := quotient_normal [group of ApT] nsAT_R.
  rewrite [_ / _]center_cyclic_abelian ?center_abelian //=.
  have temp_isog := third_isog sATApT_ZRApT nsATApT_RApT (center_normal _).
  rewrite -(isog_cyclic temp_isog) quotient_cyclic //=.
  rewrite (isog_cyclic (third_isog sApT_AT nsApT_R nsAT_R)) /=.
  by rewrite Req quotient_mulgen ?cycle_subG // quotient_cycle // cycle_cyclic.
move: (der1_min (normal_norm nsApT_R) cRApT_RApT) => sR'_ApT {cRApT_RApT}.
have : [~ a, b] \in R' by rewrite [R']derg1 mem_gen // mem_imset2. 
move/(subsetP sR'_ApT); rewrite /= [ApT]norm_mulgenEl ?cycle_subG ?groupX //=.
case/mulsgP => g h; case/cycleP=> i ->{g}; case/cycleP=> j ->{h}. 
rewrite -expgn_mul => ab_eq.
clear sApT_AT sApT_R sT_ApT nsT_ApT ATTeq' ApTTeq charApTT_ATT nsApT_R.
clear  nsApTT_RT nsApT_AT card_ApTAT sATApT_ZRApT sR'_ApT Ap ApT.
have {ordz} MhoAT : 'Mho^1(AT) = 'Mho^1(A).
  have: A \* T = AT. 
    by rewrite cprodE ?ATeq ?norm_mulgenEl // ?(subset_trans _ cTR) ?cycle_subG.
  have peltz : p.-elt z by rewrite (mem_p_elt pR) // -cycle_subG.
  move/(Mho_cprod 1) <-. 
  by rewrite (Mho_p_cycle 1 peltz) -ordz expg_order cycle1 cprodg1.
case eMR'1 : (MR' == 1); last first.
  have sT_MR': T \subset MR'.
    by case/setIP: (MR'ZRz (negbT eMR'1)); rewrite cycle_subG. 
  have sTA : T \subset <[a]>.
    rewrite (subset_trans _ (Mho_sub 1 _)) ?(subset_trans sT_MR') // -MhoAT.
    rewrite (MhoS 1) //= der1_min ?(normal_norm nsAT_R) // cyclic_abelian //. 
    by rewrite Req quotient_mulgen ?cycle_subG //= quotient_cycle ?cycle_cyclic.
  have ATeq': AT :=: <[a]> by rewrite ATeq mulgenE (setUidPl sTA) genGid.
  apply/metacyclicP; exists AT.
  rewrite /= nsAT_R Req quotient_mulgen ?cycle_subG //.
  by rewrite quotient_cycle // ATeq' !cycle_cyclic.
have abelR' : p.-abelem R'.
  have pR' := (pgroupS sR'R pR); have pOR' := (pgroupS (Ohm_sub 1 _) pR').
  rewrite -[R']derg1 -(eqP (trivg_Mho eMR'1)) /= (abelem_Ohm1 pR').
  rewrite (p2group_abelian pOR') // (leq_trans _ cardOR) //. 
  by rewrite dvdn_leq_log ?cardG_gt0 // cardSg // OhmS.
clear ATTeq sT_AT nsAT_R sAT_R nsT_AT MR'ZRz eMR'1 MR' MhoAT ATa.
have {abelR'} R1_eq : R^`(1) = <[ [~ a, b] ]>.
  have [cR'R' expR'p] := (abelemP primep abelR').
  have abJ_eq: a^b = a^+(p*i).+1 * z^+j 
    by rewrite conjg_mulR ab_eq mulgA -expgS.
  have cRz : R \subset 'C[z] by rewrite sub_cent1 -cycle_subG centsC.
  have ca_ab : a \in 'C[[~a, b]].
    apply/cent1P; rewrite ab_eq; apply: commuteM; apply: commuteX => //.
    by apply/cent1P; rewrite (subsetP cRz).
  have cRab : R \subset 'C[[~a, b]].
    rewrite Req ATeq !(gen_subG, subUset) !sub1set ca_ab (cent1C z).
    rewrite (subsetP cRz) ?groupR //= andbT inE conjg_set1 sub1set inE.
    rewrite ab_eq conjMg [(z^+j)^b](conjg_fixP _); last first.
      by apply/commgP; apply/cent1P; rewrite groupX // cent1C (subsetP cRz).
    rewrite conjXg conjg_mulR expMgn; last by apply: (cent1P ca_ab).
    rewrite [[~_, _]^+_]expgn_mul expR'p ?exp1gn ?mulg1 //= derg1 mem_gen //.
    exact: mem_imset2.
  pose Nab := 'N(<[[~a,b]]>).
  have nRab : R \subset Nab by rewrite cents_norm ?cent_cycle.
  have [Nab_a Nab_b Nab_z] : [/\ a \in Nab, b \in Nab & z \in Nab].
    by rewrite !(subsetP nRab) // -cycle_subG.
  apply/eqP; rewrite eq_sym eqEsubset cycle_subG mem_gen ?mem_imset2 //=.
  rewrite der1_min // Req norm_mulgenEl // ?cycle_subG //. 
  rewrite quotientMl ?cycle_subG // abelianM /=.
  rewrite {1}quotient_cycle // cycle_abelian /=.
  rewrite ATeq norm_mulgenEl ?cycle_subG // quotientMl ?cycle_subG //.
  rewrite abelianM /= 2?{1}quotient_cycle // ?cycle_abelian /= centM subsetI.
  rewrite quotient_cents ?(subset_trans _ cTR) ?cycle_subG //=. 
  rewrite -andbC quotient_cents ?(subset_trans _ cTR) ?cycle_subG //=.
  rewrite !quotient_cycle // cycle_subG /= cent_cycle.
  apply/cent1P; apply/commgP. 
  by rewrite -morphR //= coset_id // -groupV invg_comm cycle_id.
have [S maxS sR'S] : {S | [max S | (S \subset R) && cyclic S] & (R' \subset S)}.
  by apply: maxgroup_exists; rewrite der1_subG /= R1_eq cycle_cyclic.
case/maxgroupP: maxS; case/andP => sSR cycS maxS.
have nsSR : S <| R.
  by rewrite /normal sSR -commg_subl (subset_trans _ sR'S) // commSg.
apply/existsP; exists S; rewrite cycS nsSR //=. 
apply: negbNE; apply/negP=> ncycRS.
suffices S1unique : forall S1 : {group gT}, 
  S \subset S1 -> S1 \subset R -> #|S1 / S| = p -> S1 :=: 'Ohm_1(R) <*> S.
  have pRS := quotient_pgroup S pR.
  have oddRS : odd #|R / S| by rewrite (odd_pgroup_odd oddp pRS).
  case: (ex_odd_normal_abelem2 pRS oddRS ncycRS) => /= Sbar nsSbar_RS.
  rewrite !inE; case/andP; case/andP => sSbar_RS abel_Sbar card_Sbar.
  case: (abelian_structure (abelem_abelian abel_Sbar))=> b'.
  rewrite (abelian_type_abelem abel_Sbar) (rank_abelem abel_Sbar).
  rewrite (eqP card_Sbar) unlock; case: b' => [|u [|v []]] => //=. 
  rewrite dprodg1; case/dprodP=> _ Sbar_eq _ eUIV; case=> cardu cardv.
  have sU_RS : <[u]> \subset R / S.
    by rewrite (subset_trans _ sSbar_RS) // -Sbar_eq mulG_subl. 
  case: (inv_quotientS nsSR sU_RS) => K /= Ueq sSK sKR.
  have sV_RS : <[v]> \subset R / S.
    by rewrite (subset_trans _ sSbar_RS) // -Sbar_eq mulG_subr. 
  case: (inv_quotientS nsSR sV_RS) => L /= Veq sSL sLR.
  have cardKS : #|K / S| = p by rewrite -Ueq -orderE /= cardu //=.
  have cardLS : #|L / S| = p by rewrite -Veq -orderE /= cardv //=.
  move: eUIV cardv (prime_gt1 primep); rewrite Ueq (S1unique _ sSK sKR cardKS).
  rewrite -(S1unique _ sSL sLR cardLS) -Veq setIid orderE => ->.
  by rewrite cards1 => <-.
move=> S1 sS_S1 sS1_R cardS1S; pose OS1 := 'Ohm_1(S1).
have pS1 := pgroupS sS1_R pR; have oddS1 := odd_pgroup_odd oddp pS1.
case cycS1 : (cyclic S1).
  move: cardS1S (prime_gt1 primep).
  suff ->: S1 :=: S by rewrite trivg_quotient cards1 => <-.
  by apply: (maxS _ _ sS_S1); rewrite sS1_R cycS1.
have nS_S1 : S1 \subset 'N(S).
  by rewrite (subset_trans sS1_R (normal_norm nsSR)).
case/cyclicP: (cycS) (cardS1S) => x Seq.
rewrite card_quotient // Seq => cardS1X.
have S1x : x \in S1 by rewrite (subsetP sS_S1) // Seq -cycle_subG.
move: (Ohm1_extremal_odd pS1 oddS1 (negbT cycS1) S1x cardS1X).
rewrite /= !inE; case/andP; case/andP => _ abelOS1 cardOS1.
have eOS1OR : OS1 = 'Ohm_1(R)%G.
  have pOR : p.-group 'Ohm_1(R) by apply: (pgroupS (Ohm_sub _ _) pR).
  apply/eqP; rewrite eqEproper OhmS //=; apply/negP; move/(properG_ltn_log pOR).
  by rewrite (eqP cardOS1) ltnNge cardOR.
have : maximal S S1 by rewrite p_index_maximal // Seq cardS1X.
case/maxgroupP => _ maximalSS1; apply/eqP; rewrite -eOS1OR -Seq eq_sym.
rewrite eqEproper mulgen_subG Ohm_sub sS_S1 /=; apply/negP=> pO1S_S1.
have OS1Seq : OS1 <*> S :=: S by rewrite maximalSS1 // mulgen_subr.
have : cyclic OS1 by apply: (cyclicS _ cycS); rewrite -OS1Seq mulgen_subl.
by rewrite (abelem_cyclic abelOS1) (eqP cardOS1).
Qed.

(* This is B & G, Theorem 4.12, for an internal group of operators *)
Lemma commutator_metacyclic_pgroup_p'group : forall gT (R A : {group gT}) p, 
  let RA := [~: R, A] in 
  let CRA := 'C_R(A) in 
  let R' := R^`(1) in
  p.-group R -> odd #|R| -> metacyclic R -> p^'.-group A -> A \subset 'N(R) ->
    abelian RA /\ R :=: RA * CRA /\ 'C_RA(A) = 1 /\ 
    (~ abelian R -> RA :!=: 1 -> 
    CRA :!=: 1 /\ cyclic RA /\ cyclic CRA /\ R' \subset RA).
Proof.
move=> gT R A p RA CRA R' pR oddR mcycR p'A nRA.
suffices cRA_RA: abelian RA; first split => //.
  have sRA_R : RA \subset R by rewrite commg_subl.
  have nsRA_R : RA <| R by rewrite /normal sRA_R commg_norml.
  have coprimeRA := pnat_coprime pR p'A.
  have solvR : solvable R by rewrite nilpotent_sol // (pgroup_nil pR).
  have eRAA_RA : [~: RA, A] = RA by rewrite -{2}[RA]coprime_commGid.
  have eR_RACRA : R :=: RA * CRA by rewrite -(coprime_cent_prod nRA).
  have nRAA: A \subset 'N(RA) by rewrite commg_normr.
  have coprimeRAA := pnat_coprime (pgroupS sRA_R pR) p'A.
  case/dprodP: (coprime_abelian_cent_dprod nRAA coprimeRAA cRA_RA) => _ _ _. 
  rewrite eRAA_RA !setIA setIid=> eCRAA_1; split=> //; split=> // [ncRR neRA1].
  have neCRA1 : CRA != 1; last split=> //.
    apply/negP; move/eqP=> eCRA1; apply: ncRR; move: eR_RACRA.  
    by rewrite eCRA1 mulg1 => ->. 
  have ncycR : ~~ (cyclic R). 
    by move/negP: ncRR; apply: contra; apply: cyclic_abelian.
  case: (Ohm1_metacyclic_pgroup_odd_prime mcycR pR oddR ncycR); rewrite !inE /=.
  case/andP; case/andP=> _ abelOR cardOR.
  pose OR := 'Ohm_1(R); pose ORA := 'Ohm_1(RA); pose OCRA := 'Ohm_1(CRA).
  have sORA_OR := OhmS 1 sRA_R.
  have sORA_R := subset_trans sORA_OR (Ohm_sub 1 _).
  have sOCRA_OR := OhmS 1 (subsetIl R 'C(A)).  
  have sOCRA_R := subset_trans sOCRA_OR (Ohm_sub 1 _).
  have sum_card_le : logn p #|ORA| + logn p #|OCRA| <= 2.
    rewrite -(eqP cardOR) -logn_mul ?cardG_gt0 // -TI_cardMg //=; last first.
      apply/trivgP; rewrite -eCRAA_1 setISS ?Ohm_sub //.
      by rewrite (subset_trans (Ohm_sub _ _)) // subsetIr.
    rewrite -norm_mulgenEl; last first.
      rewrite (subset_trans sORA_OR) // cents_norm // centsC.
      by rewrite (subset_trans sOCRA_OR) //; apply: (abelem_abelian abelOR).
    by rewrite lognSg // mulgen_subG sORA_OR //=.
  have cardORA_ge: logn p #|ORA| >= 1.
    have <-: logn p #|[1 gT]| = 0 by rewrite cards1 logn1.
    rewrite properG_ltn_log // ?(pgroupS sORA_R pR) //.
    rewrite properEneq sub1set group1 andbT eq_sym /=.
    rewrite -(setIidPr (Ohm_sub 1 [group of RA])); apply/negP; move/eqP.
    move/TI_Ohm1; rewrite setIid; move/eqP; apply: (negP neRA1). 
  have cardOCRA_ge: logn p #|OCRA| >= 1.
    have <-: logn p #|[1 gT]| = 0 by rewrite cards1 logn1.
    rewrite properG_ltn_log // ?(pgroupS sOCRA_R pR) //.
    rewrite properEneq sub1set group1 andbT eq_sym /=.
    rewrite -(setIidPr (Ohm_sub 1 [group of CRA])); apply/negP; move/eqP. 
    move/TI_Ohm1; rewrite setIid; move/eqP; apply: (negP neCRA1).
  have cardORA_le : logn p #|ORA| <= 1%N.
    move: (leq_trans  (leq_add (leqnn _) cardOCRA_ge) sum_card_le).
    by rewrite addn1 ltnS.
  have cardOCRA_le : logn p #|OCRA| <= 1%N.
    move: (leq_trans  (leq_add cardORA_ge (leqnn _)) sum_card_le).
    by rewrite add1n ltnS.
  rewrite (odd_pgroup_rank1_cyclic (pgroupS sRA_R pR) (oddSg sRA_R oddR)).
  have cORA_ORA := abelem_abelian (abelemS sORA_OR abelOR). 
  rewrite -p_rank_Ohm1 p_rank_abelian // Ohm_id cardORA_le; split => //.
  have sCRA_R : CRA \subset R by rewrite subsetIl.
  have cOCRA_OCRA := abelem_abelian (abelemS sOCRA_OR abelOR).
  have cycCRA : cyclic CRA; last split=> //.
    rewrite (odd_pgroup_rank1_cyclic (pgroupS sCRA_R pR) (oddSg sCRA_R oddR)).
    by rewrite -p_rank_Ohm1 p_rank_abelian // Ohm_id cardOCRA_le.
  have eRACRA : RA * CRA = (RA <*> CRA). 
    by rewrite /= norm_mulgenEr // subIset // (normal_norm nsRA_R).
  rewrite /R' {1}eR_RACRA eRACRA der1_min //=.
    by rewrite -eRACRA -eR_RACRA (normal_norm nsRA_R).
  rewrite /= mulgenC quotient_mulgen ?subIset // ?(normal_norm nsRA_R) //.
  by rewrite quotient_abelian // cyclic_abelian.
move: {2}_.+1 (ltnSn #|R|) => n.
elim: n => // n IHn in R RA CRA R' pR oddR mcycR nRA *.
rewrite ltnS; move=> cardRle.
have sRA_R : RA \subset R by rewrite commg_subl.
have nsRA_R : RA <| R by rewrite /normal sRA_R commg_norml.
have eRA_RAA: RA = [~: RA, A].
  rewrite /= -{1}[RA]coprime_commGid ?nilpotent_sol ?(pgroup_nil pR) //.
  by rewrite (pnat_coprime pR p'A).
case : (eqVneq RA R)=> eR_RA; last first.
  rewrite eRA_RAA IHn ?(pgroupS sRA_R) ?(oddSg sRA_R) ?commg_normr //=. 
    exact: (metacyclicN mcycR).
  by rewrite (leq_trans _ cardRle) // proper_card // properEneq eR_RA.
case neR1 : (R == 1%G); first by rewrite eR_RA (eqP neR1) abelian1.
have {IHn neR1}[primep _ _] := pgroup_pdiv pR (negbT neR1).
case ncRR : (abelian R); first by exact: (abelianS sRA_R).
have ncycR : ~~ cyclic R by apply/negP; move/cyclic_abelian; rewrite ncRR.
case/metacyclicP: (mcycR)=> K [cycK nsKR cycKR].
have {eRA_RAA sRA_R nsRA_R} cycR' : cyclic R'.
  by apply: (cyclicS _ cycK); rewrite der1_min ?normal_norm // cyclic_abelian.
have nR'A: A \subset 'N(R') by exact: (char_norm_trans (der_char 1 _) nRA).
have {K cycK nsKR cycKR cycR' nR'A}[S maxS sR'S] : {S | 
    [max S | [&& (S \subset R), cyclic S & A \subset 'N(S)]] & (R' \subset S)}.
  by apply: maxgroup_exists; rewrite der1_subG cycR'.
case/maxgroupP: maxS; case/and3P=> sSR cycS nSA maxS.
have nSR : R \subset 'N(S).
  by rewrite -commg_subr (subset_trans _ sR'S) // commgS.
have nsSR : S <| R by rewrite /normal sSR.
have cSR : R \subset 'C(S).
  pose prodRA := R <*> A; pose prodRA' := prodRA^`(1).
  have sRA_prodRA' : RA \subset prodRA'.
    by rewrite commgSS ?mulgen_subl ?mulgen_subr.
  rewrite -eR_RA (subset_trans sRA_prodRA') //.
  have nS_prodRA : prodRA \subset 'N(S) by rewrite mulgen_subG nSR.
  rewrite der1_min //= ?norms_cent ?mulgen_subG ?nSR //.
  rewrite -ker_conj_aut (abelianS (quotientS _ nS_prodRA)) //.
  rewrite (isog_abelian (first_isog _)) (abelianS (Aut_conj_aut _ _)) //.
  by rewrite Aut_cyclic_abelian.
have cRS_RS : abelian (R / S) by rewrite sub_der1_abelian.
have pRS := quotient_pgroup S pR. 
pose OR := 'Ohm_1(R); pose ORS := 'Ohm_1(R / S).
have abelORS : p.-abelem ORS.
  by rewrite (abelem_Ohm1 pRS) (abelianS _ cRS_RS) // Ohm_sub.
have sORS_ORS : OR / S \subset 'Ohm_1(R / S) by apply: morphim_Ohm.
have p'AS := quotient_pgroup S p'A.
have nORS_AS : A / S \subset 'N(ORS).
  by rewrite (char_norm_trans (Ohm_char _ _)) ?quotient_norms.
have nOR_S_AS : A / S \subset 'N(OR / S).
  by rewrite quotient_norms // (char_norm_trans (Ohm_char _ _)). 
case: (Maschke_abelem abelORS p'AS sORS_ORS nORS_AS nOR_S_AS) => /= W.
case/dprodP=> /= _ ORSeq _; pose X := coset S @*^-1 W.
have sXR : X \subset R.
  rewrite sub_cosetpre_quo /normal ?sSR //=.  
  by rewrite (subset_trans _ (Ohm_sub 1 _)) // -ORSeq mulG_subr.
rewrite -(cosetpreK W) -/X in ORSeq * => disjORS_SX.
have sSX : S \subset X by rewrite sub_cosetpre.
have nsSX : S <| X by apply: (normalS sSX sXR).
have nXS : S \subset 'N(X) by rewrite cents_norm // centsC (subset_trans sXR). 
rewrite -quotient_normG // quotientSGK //= -/X => nXA {nXS}.
case: (Ohm1_metacyclic_pgroup_odd_prime mcycR pR oddR ncycR)=> {mcycR}.
rewrite !inE Ohm_sub /=; case/andP=> abelOR; case/eqP=> cardOR.
have cOR_OR := abelem_abelian abelOR.
have OSeq: 'Ohm_1(S) = S :&: OR.
  apply/eqP; rewrite eqEsubset subsetI (Ohm_sub 1 _) OhmS //=. 
  rewrite (OhmE 1 (pgroupS sSR pR)) sub_gen //; apply/subsetP=> g; rewrite !inE.
  rewrite [OR](OhmEabelian pR) ?(abelem_abelian abelOR) // inE.
  by case/and3P => ->.
have neS1 : S != 1%G.
  apply: (contra _ (negbT ncRR))=> eS1; apply/commG1P; apply/trivgP.
  by rewrite (subset_trans sR'S) // (eqP eS1).
have {disjORS_SX} cardOXle : #|'Ohm_1(X)| <= p.
  rewrite -(Ohm1_cyclic_pgroup_prime cycS (pgroupS sSR pR) neS1).
  rewrite OSeq subset_leq_card // subsetI OhmS // andbT. 
  have sOX: 'Ohm_1(X) \subset X :&: OR 
    by rewrite subsetI Ohm_sub OhmS // subsetIr.
  rewrite (subset_trans sOX) // -quotient_sub1; last first.
    by rewrite subIset // (subset_trans sXR nSR).
  by rewrite (subset_trans (quotientI _ _ _)) // setIC disjORS_SX.  
have {cardOXle} eXS : X = S.
  have pX := pgroupS sXR pR; have oddX := oddSg sXR oddR.
  have pOX := pgroupS (Ohm_sub 1 _) pX.
  have cOX_OX := abelianS (OhmS 1 sXR) cOR_OR.
  apply: maxS => //=; rewrite sXR nXA /= andbT (odd_pgroup_rank1_cyclic pX) //.
  rewrite -p_rank_Ohm1 p_rank_abelian // Ohm_id.
  by rewrite -(leq_exp2l _ _ (prime_gt1 primep)) -p_part part_pnat_id.
rewrite {}eXS trivg_quotient mulg1 in ORSeq => {X sXR sSX nsSX nXA W}.
have cardORS_le : logn p #|'Ohm_1(R/S)| <= 1.
  rewrite -ORSeq -(isog_card (second_isog _)) ?(subset_trans _ nSR) ?Ohm_sub //.
  have pOR := pgroupS (Ohm_sub 1 _) pR.
  rewrite -ltnS -cardOR (ltn_log_quotient pOR) ?subsetIr //= -OSeq -cardG_gt1.
  by rewrite (Ohm1_cyclic_pgroup_prime cycS (pgroupS sSR pR) neS1) prime_gt1. 
rewrite eR_RA center_cyclic_abelian ?center_abelian //.
have sS_ZR : S \subset 'Z(R) by rewrite subsetI sSR /= centsC.
rewrite -(isog_cyclic (third_isog sS_ZR nsSR _)) ?center_normal //.
rewrite quotient_cyclic // (odd_pgroup_rank1_cyclic pRS (quotient_odd S oddR)).
by rewrite -p_rank_Ohm1 p_rank_abelem. 
Qed.

(* This corresponds to Lemmas 4.13 and 4.14 in B & G. *)
Lemma automorphism_prime_order_pgroup_rank_le2 : 
  forall gT (R : {group gT}) p q (a : gT),
    p.-group R -> odd #|R| -> 'r(R) <= 2 -> a \in 'N(R) :\: 'C(R) -> 
      prime q -> p != q -> #[a] = q ->
    q %| (p^2).-1 /\ (q %| p.+1./2 \/ q %| p.-1./2) /\ q < p.
Proof.
move=> gT R p q a pR oddR rankR; case/setDP=> NRa nCRa primeq nepq ord_a.
move: {2}_.+1 (ltnSn #|R|) => n.
elim: n => // n IHn in R pR oddR rankR NRa nCRa *; rewrite ltnS=> cardRle.
case neR1 : (R == 1%G); first by case: nCRa; rewrite (eqP neR1) cent1T inE.
have [primep _ [m cardR]] := pgroup_pdiv pR (negbT neR1).
have oddp : odd p by move: oddR; rewrite cardR odd_exp.
have p2m1_eq : (p^2).-1 = ((p.+1) * (p.-1))%N.
  by rewrite -(subn1 p) muln_subr muln1 mulSn addnC -[_-p.+1]predn_sub addnK.
pose A := <[a]>; pose RA := [~: R, A]; pose OR := 'Ohm_1(R).
have nRA : A \subset 'N(R) by rewrite cycle_subG.
have coprimeRA : coprime #|R| #|A|.
  by rewrite (pnat_coprime pR) // -orderE ord_a p'natE // dvdn_prime2.
case eR_RA : (R :==: RA); last first.
  have sRA_R : RA \subset R by rewrite commg_subl.
  have pRA_R : RA \proper R by rewrite properEneq eq_sym eR_RA.
  have pRA := pgroupS sRA_R pR; have oddRA := oddSg sRA_R oddR.
  have NRAa : a \in 'N(RA) by rewrite (subsetP (commg_normr _ _)) // cycle_id.
  have cardRA : #|RA| < n by apply: (leq_trans (proper_card pRA_R)).
  apply: (IHn _ pRA); rewrite // ?(leq_trans (rankS sRA_R)) //.
  rewrite -cycle_subG /= centsC (sameP commG1P eqP).
  rewrite coprime_commGid ?(pgroup_sol pR) ?cycle_subG //=.
  by rewrite (sameP eqP commG1P) centsC cycle_subG.
case eR_OR : (R :==: 'Ohm_1(R)); last first.
  have sOR_R := Ohm_sub 1 R; have pOR := pgroupS sOR_R pR.
  have pOR_R : OR \proper R by rewrite properEneq eq_sym eR_OR.
  have oddOR := oddSg sOR_R oddR.
  have NORa : a \in 'N(OR) by apply: (subsetP (char_norms (Ohm_char 1 _))).
  have cardOR : #|OR| < n by apply: (leq_trans (proper_card pOR_R)).
  apply: (IHn _ pOR oddOR _ NORa); rewrite ?(leq_trans (rankS sOR_R)) //.
  apply: (contra _ nCRa); rewrite -!cycle_subG -/A. 
  exact: (coprime_odd_faithful_Ohm1 pR).
suffices {IHn cardRle n} qdiv: q %| (p ^ 2).-1; first split => //.
  have even_pm1 : odd (p.-1) = false. 
    by rewrite -subn1 odd_sub ?prime_gt0 //= oddp.
  case oddq : (odd q); last first.
    have pgt2 : p > 2.
      by rewrite ltn_neqAle prime_gt1 // andbT eqn_dvd dvdn2 oddp.
    case: (even_prime primeq)=> [->|]; last by rewrite oddq.
    split=> //; rewrite -{1}[p]prednK ?prime_gt0 // -(addn2 (p.-1)) half_add /=.
    by rewrite even_pm1 add0n !dvdn2 addn1 /=; apply/orP; case: (odd (p.-1)./2).
  have p1eq: p.+1 = ((p.+1)./2 * 2)%N.
    by rewrite -{1}(odd_double_half p.+1) /= oddp muln2.
  have pm1eq: p.-1 = ((p.-1)./2 * 2)%N.
    rewrite -{1}(odd_double_half p.-1) -subn1 odd_sub ?prime_gt0 //.
    by rewrite oddp muln2.
  rewrite p2m1_eq !euclid // in qdiv; split.
    have qdiv2 : ~~ (q %| 2).
      by apply: (contraL _ oddq); rewrite dvdn_prime2 //; move/eqP=> ->.
    by rewrite p1eq pm1eq !euclid // (negbTE qdiv2) !orbF in qdiv; apply/orP.
  rewrite ltn_neqAle eq_sym nepq /= -ltnS ltn_neqAle; apply/andP; split.
  apply: (contraL _ oddq); move/eqP=> ->; by rewrite /= oddp.
  case/orP: qdiv=> [|qdiv']; first by apply: dvdn_leq; rewrite ltnS.
  have pm1_gt0: p.-1 > 0 by rewrite -ltnS prednK ?prime_gt0 ?prime_gt1.
  by apply: (leq_trans (leq_trans (dvdn_leq pm1_gt0 qdiv') (leq_pred _))).
have {p2m1_eq} main_lemma : 
  forall (hT : finGroupType) (b : hT) (E : {group hT}), 
    p.-abelem E -> E != 1%G -> rank E <= 2 -> b \in 'N(E) :\: 'C(E) -> 
      #[b] = q -> q %| (p^2).-1.
  move=> hT b E abelE neE1 rankE; case/setDP=> NEb nCEb ord_b; pose B := <[b]>.
  have eCBE_1 : 'C_B(E) = 1%G.
    have: #|'C_B(E)| %| q by rewrite -ord_b orderE cardSg // subsetIl.
    move/(proj2 (primeP primeq)); rewrite -trivg_card1; case/orP; case/eqP=> //.
    move=> card_CBE; case (negP nCEb); rewrite -cycle_subG; apply/setIidPl=> /=.
    by apply/eqP; rewrite eqEcard subsetIl /= -orderE ord_b card_CBE.
  rewrite -cycle_subG in NEb; pose rP := reprGLm (abelem_repr abelE neE1 NEb).
  have qdiv: q %| #|rP @* B|.
    by rewrite card_injm -?orderE ?ord_b // ker_reprGLm rker_abelem eCBE_1.
  move: (dvdn_trans qdiv (cardSg (@subsetT _ (rP @* B))))=> //=.
  have: 0 < 'dim E <= 2.
    by rewrite (dim_abelemE abelE neE1) -(rank_abelem abelE) rank_gt0 neE1.
  move: ('dim E); case=> [|[|[|u]]]=> //= _.
    by rewrite card_GL_1 /= card_Fp // p2m1_eq; apply: dvdn_mull.
  rewrite card_GL_2 /= card_Fp // !euclid // dvdn_prime2 // eq_sym.
  by rewrite (negbTE nepq) /= orbb p2m1_eq euclid // orbC.
pose char_abelians := \bigcup_(H | ((H : {group gT}) \char R) && abelian H) H.
case Afix: (char_abelians \subset 'C(A)); last first.
  case/subsetPn: (negbT Afix)=> h; case/bigcupP=> H.
  case/andP=> charHR cHH Hh nCAh.
  have ncHA : ~~ (A \subset 'C(H)) by rewrite centsC; apply/subsetPn; exists h. 
  have [sHR nHR] := andP (char_normal charHR); have oddH := oddSg sHR oddR.
  have pH := pgroupS sHR pR.
  pose E := 'Ohm_1(H); have abelE : p.-abelem E by apply: (Ohm1_abelem pH).
  have sER := subset_trans (Ohm_sub 1 _) sHR.
  have nEA : A \subset 'N(E).
    by apply: char_norm_trans (Ohm_char 1 _) (char_norm_trans charHR nRA).
  have ncEA : ~~ (A \subset 'C(E)).
    apply: (contra _ ncHA); apply: (coprime_odd_faithful_Ohm1 pH)=> //=.
      by apply: (char_norm_trans charHR).
    by rewrite (coprime_dvdl _ coprimeRA) // cardSg.
  have neE1 : E != 1 by apply: (contra _ ncEA); move/eqP=> ->; apply cents1.
  have rankE : rank E <= 2 by apply: (leq_trans (rankS sER) rankR).
  by apply: (main_lemma _ a _ abelE); rewrite // inE -!cycle_subG ncEA.
have ncRR : ~~ (abelian R).
  apply: (contra _ nCRa)=> cRR; rewrite -cycle_subG centsC.
  rewrite (subset_trans _ Afix) //; apply: bigcup_max (subxx R). 
  by rewrite char_refl.
have nsZR : 'Z(R) <| R by apply: center_normal R. 
have [sZR nZR] := andP nsZR; have pZR := pgroupS sZR pR.
have {Afix char_abelians} [specR _]: special R /\ 'C_R(A) = 'Z(R).
  by apply: (abelian_charsimple_special pR) => //; rewrite ?{2}(eqP eR_RA).
have abelZR := center_special_abelem pR specR; case: specR=> ePhiR eR'.
have {eR'} nc2_R : nil_class R <= 2 by rewrite nil_class2 eR'.
have {nc2_R} expR : exponent R %| p. 
  rewrite (eqP eR_OR) (proj1 (exponent_odd_nil23 pR oddR _)) //. 
  by rewrite (leq_trans nc2_R).
have NZRa : a \in 'N('Z(R)). 
 by rewrite (subsetP (char_norm_trans (center_char R) nRA)) // cycle_id.
have neZR1 : 'Z(R) != 1.
  rewrite /center -{1}(setIid R) -setIA nil_meet_Z ?(pgroup_nil pR)  //. 
  by rewrite ?(negbT neR1).
move: (pgroup_rank_le2_exponentp pR rankR expR); rewrite leq_eqVlt ltnS.
case/orP=> lcardR; last by rewrite (p2group_abelian pR lcardR) in ncRR.
have {lcardR m cardR} cardR : #|R| = (p^3)%N.
  by rewrite cardR pfactorK // in lcardR; rewrite cardR (eqP lcardR).
pose E := R / 'Z(R); pose b := coset 'Z(R) a; pose B := <[b]>.
have abelE : p.-abelem E by rewrite /E -ePhiR Phi_quotient_abelem.
have ord_b : #[b] = q.
  have: #[b] %| q by rewrite order_dvdn -morphX // -ord_a expg_order morph1.
  move/(proj2 (primeP primeq)); case/orP; last by move/eqP.
  rewrite order_eq1; move/eqP; move/(coset_idr NZRa); rewrite inE.
  by rewrite (negbTE nCRa) andbF.
have nEB : B \subset 'N(E) by rewrite -[B]quotient_cycle // quotient_norms.
have nsR_ZR : ~~ (R \subset 'Z(R)) by rewrite subsetI subxx /= ncRR. 
have ncEB : ~~ (B \subset 'C(E)).
  rewrite -[B]quotient_cycle // quotient_cents2 ?cycle_subG //=.
  by rewrite commGC -/RA -(eqP eR_RA). 
have neE1 : E != 1 by rewrite eqEsubset quotient_sub1 // negb_and nsR_ZR. 
have rankE : rank E <= 2.
  rewrite (rank_abelem abelE) -ltnS (leq_trans (ltn_log_quotient pR _ sZR)) //.
  by rewrite cardR pfactorK.
by apply: (main_lemma _ b _ abelE)=> //; rewrite inE -!cycle_subG ncEB.
Qed.

(* Lemma 4.15 in B & G can be found in maximal.v *)

(* This is B & G, Theorem 4.16 *)
Theorem Blackburn_theorem : forall gT (R A : {group gT}) p,
  p.-group R -> odd #|R| -> R != 1%G -> 'r(R) <= 2 -> [~: R, A] == R ->
  'C_A(R) == 1%G -> p^'.-group A -> odd #|A|  -> 
    p > 3 /\ (abelian R \/ exists R1, exists R2, 
      R1 \* R2 = R /\ ~~ (abelian R1) /\ logn p #|R1| = 3 /\ exponent R1 %| p 
      /\ cyclic R2 /\ 'Ohm_1(R2) = R1^`(1)).
Proof.
move=> gT R A p pR oddR neR1 rankR eRA_R TI_CAR p'A oddA.
have [primep pdivR _] := pgroup_pdiv pR neR1.
have nRA : A \subset 'N(R) by rewrite -commg_subl (eqP eRA_R).
have gtp3 : p > 3; last split => //.
  have neA1 : A != 1%G.
    by apply: (contraL _ eRA_R); move/eqP=> ->; rewrite commG1 eq_sym.
  have cardA_gt1 : #|A| > 1. 
    by rewrite ltn_neqAle eq_sym -trivg_card1 neA1 cardG_gt0. 
  have [q primeq qdivA] := pdivP cardA_gt1.
  have [a Aa orda_eq] := Cauchy primeq qdivA.
  have coprimeRA := (pnat_coprime pR p'A).
  have coprimepq := coprime_dvdr qdivA (coprime_dvdl pdivR coprimeRA).
  have nepq : p != q.
    apply: (contraL _ coprimepq); move/eqP=> ->.
    by rewrite /coprime gcdnn neq_ltn prime_gt1 // orbT.
  have NRDCRa : a \in 'N(R) :\: 'C(R).
    rewrite inE (subsetP nRA _ Aa) andbT.
    apply: contraL (prime_gt1 primeq) => CRa.
    have: a \in 1%G by rewrite -(eqP TI_CAR) inE Aa.
    by rewrite -orda_eq inE; move/eqP=> ->; rewrite order1.
  case: (automorphism_prime_order_pgroup_rank_le2 pR _ _ NRDCRa primeq)=> //.
  move=> _ [_]; apply: leq_trans; rewrite ltnS ltn_neqAle prime_gt1 // andbT.
  by apply: contraL oddA; rewrite -dvdn2; move/eqP=> ->.
pose S := 'Ohm_1(R); pose S' := S^`(1); have pS := pgroupS (Ohm_sub 1 _) pR.
have nsSR : S <| R by rewrite char_normal // Ohm_char.
have [sSR nSR] := andP nsSR.
have rankS : rank S <= 2 by rewrite rank_Ohm1.
case lcardS : (logn p #|S| <= 2).
  have mcR : metacyclic R by apply: (pgroup_Ohm1_p2_metacyclic pR).
  case: (commutator_metacyclic_pgroup_p'group pR oddR mcR p'A nRA)=> cRR _.
  by rewrite (eqP eRA_R) in cRR; apply: or_introl.
have expS : exponent S %| p by apply: pgroup_rank_le2_Ohm1.
have {lcardS}lcardS : logn p #|S| = 3.
  apply/eqP; move: (negbT lcardS); rewrite -ltnNge eqn_leq => ->; rewrite andbT.
  by apply: pgroup_rank_le2_exponentp.
have cardS : #|S| = (p ^ 3)%N by rewrite -(part_pnat_id pS) p_part lcardS.
have neS1 : S != 1.
  by move/eqP: lcardS; apply: contraL; move/eqP=> ->; rewrite cards1 logn1.
have ncSS : ~~ abelian S.
  apply: (contraL _ rankS); rewrite -(abelem_Ohm1 pR)=> abelS.
  by rewrite (rank_abelem abelS) lcardS.
case/andP: (center_normal [group of S])=> /= sZSS nZSS.
have neZS1 : 'Z(S) != 1%G.
  by apply/negP; move/eqP; move/(trivg_center_pgroup pS); move/eqP; apply/negP.
have lcardZS : logn p #|'Z(S)| <= 2.
  rewrite -ltnS -lcardS (properG_ltn_log pS) // properEneq subsetIl andbT /=.
  by apply: (contra _ ncSS); move/eqP=> ZSeq; rewrite -[S]ZSeq center_abelian.
have {lcardZS}lcardZS : logn p #|'Z(S)| = 1%N.
  case: (pgroup_pdiv (pgroupS (subsetIl _ _) pS) neZS1)=> /= _ pdivZS [m m_def].
  apply/eqP; rewrite eqn_leq {2}m_def pfactorK // ltn0Sn andbT -ltnS ltn_neqAle.
  rewrite lcardZS andbT; apply: contra ncSS; move/eqP=> {lcardZS}lcardZS.
  rewrite [S](@center_cyclic_abelian _ [group of S]) ?center_abelian //=.
  rewrite prime_cyclic // card_quotient // -divgS //= -/S cardS.
  rewrite -(part_pnat_id (pgroupS sZSS pS)) p_part lcardZS mulnK //. 
  by rewrite muln_gt0 prime_gt0.
have pS' : p.-group S' by apply: (pgroupS (der_sub _ _)).
have eS'ZS : S' = 'Z(S).
  apply/eqP; rewrite eqEcard der1_min //=; last first.
    apply: (p2group_abelian (quotient_pgroup _ pS)).
    by rewrite -ltnS -lcardS ltn_log_quotient.
  rewrite -(part_pnat_id (pgroupS _ pS)) ?subsetIl // p_part lcardZS.
  have neS'1 : S' != 1%G by apply: (contra _ ncSS); move/eqP; move/commG1P.
  case: (pgroup_pdiv pS' neS'1)=> _ _ [m ->].
  by rewrite dvdn_leq // ?expn_gt0 ?prime_gt0 // dvdn_exp2l.
have cardS' : #|S'| = p by rewrite -(part_pnat_id pS') p_part eS'ZS lcardZS.
have eS'PhiS : S' == 'Phi(S).
  rewrite eqEcard der1_min // ?(char_norm (Phi_char _)) //=; last first. 
    by apply: abelem_abelian (Phi_quotient_abelem pS).
  have nsPhiSS : 'Phi(S) <| S by apply: Phi_normal.
  have [sPhiSS nPhiSS] := andP nsPhiSS.
  rewrite cardS' -(part_pnat_id (pgroupS sPhiSS pS)) p_part.
  rewrite -{3}(expn1 p) leq_exp2l ?prime_gt1 //.
  rewrite -ltnS ltn_neqAle; apply/andP; split; last first.
    by rewrite -ltnS -lcardS (properG_ltn_log pS) // Phi_proper //.
  apply: (contra _ ncSS); move/eqP=> lcardPhiS; apply: cyclic_abelian.
  rewrite Phi_quotient_cyclic // prime_cyclic // card_quotient //. 
  rewrite -divgS ?(normal_sub (Phi_normal _)) // cardS.
  rewrite -(part_pnat_id (pgroupS _ pS)) // p_part lcardPhiS mulnK //.
  by rewrite muln_gt0 prime_gt0.
have {eS'PhiS}espS : extraspecial S.
  by rewrite /extraspecial -eS'ZS cardS' /special -eS'ZS -(eqP eS'PhiS).
have eqS'OCRS : S' == 'Ohm_1('C_R(S)).
  rewrite eqEsubset {2}eS'ZS subsetI OhmS ?subsetIl //=.
  rewrite (subset_trans (Ohm_sub 1 _)) ?subsetIr // andbT.
  rewrite (OhmE 1 (pgroupS (subsetIl _ _) pR)) sub_gen //=.
  apply/subsetP=> x S'x; rewrite inE -order_dvdn -cardS' order_dvdG // andbT. 
  by rewrite eS'ZS in S'x; rewrite (subsetP _ _ S'x) // setSI.
have cycCRS : cyclic 'C_R(S).
  have sCRS_R : 'C_R(S) \subset R by exact: subsetIl.
  have pCRS := pgroupS sCRS_R pR; have oddCRS := oddSg sCRS_R oddR.
  rewrite (odd_pgroup_rank1_cyclic pCRS) //.
  rewrite -p_rank_Ohm1 p_rank_abelem ?abelem_Ohm1 //= -(eqP eqS'OCRS).
    by rewrite cardS' (pfactorK 1).
  by rewrite cyclic_abelian // prime_cyclic // cardS'.
pose T := [~: S, R]; suffices sTS' : T \subset S'.
  apply: or_intror; exists S; exists 'C_R(S); split; last first.
    by do 4!split=> //; apply/eqP; rewrite eq_sym.
  rewrite cprodEgen 1?centsC ?subsetIr //.
  by rewrite {2}(critical_extraspecial pR sSR espS sTS').
apply: negbNE; apply/negP=> nsTS'. 
have pTS : T \proper S.
 by rewrite (nil_comm_properl (pgroup_nil pR)) // ?subsetI ?subxx.
have sTS := proper_sub pTS; have pT : p.-group T by apply: pgroupS pS.
have sTR : T \subset R by apply: comm_subG.
have nTR : R \subset 'N(T) by apply: commg_normr. 
have lcardT: logn p #|T| = 2.
  apply/eqP; rewrite eqn_leq -ltnS -lcardS properG_ltn_log //=.
  by rewrite -lcardZS -eS'ZS properG_ltn_log // properE nsTS' commgS.
have cardT : #|T| = (p^2)%N by rewrite -(part_pnat_id pT) p_part lcardT.
have neT1 : T != 1%G.
  by rewrite trivg_card1 cardT eqn_mul1 andbb neq_ltn prime_gt1 // orbT.
have expT : exponent T %| p by rewrite (dvdn_trans (exponentS sTS) expS).
have cTT : abelian T by rewrite (p2group_abelian pT) // lcardT.
have abelT : p.-abelem T by rewrite abelemE // cTT.
have nsSCT : ~~ (S \subset 'C(T)).
  by move: nsTS'; rewrite eS'ZS subsetI sTS /= centsC.
have nCRT_R : R \subset 'N('C_R(T)) by rewrite normsI // ?normG // norms_cent.
have cardR_CRT : #| R / 'C_R(T)| = p.
  have pR_CRT : p.-group (R / 'C_R(T)) by apply: quotient_pgroup.
  suffices : #|R / 'C_R(T)| %| p.
    have neR_CRT_1 : (R / 'C_R(T)) != 1.
      apply: (contra _ nsSCT); rewrite eqEsubset/= quotient_sub1 //.
      by rewrite subsetI; case/andP; case/andP=> _; move/(subset_trans sSR). 
    move/(proj2 (primeP primep)); rewrite -trivg_card1 (negbTE neR_CRT_1) //=.
    by move/eqP.
  suffices : #| R / 'C_R(T)| %| #|'GL_2(p)|.
    rewrite card_GL_2 card_Fp // -mulnA mulnC gauss => //.
    rewrite (pnat_coprime pR_CRT) // !pnat_mul andbb !p'natE //.
    rewrite -addn1 -subn1 dvdn_addr ?dvdn_subr ?dvdnn ?prime_gt0 // andbb.
    by rewrite dvdn1 neq_ltn prime_gt1 // orbT.
  pose rP := abelem_repr abelT neT1 nTR.
  have <-: rker rP = 'C_R(T) by apply: rker_abelem.
  rewrite -ker_reprGLm (isog_card (first_isog _)) /=.
  by rewrite -lcardT -(dim_abelemE abelT neT1) /= (cardSg (@subsetT _ _)).
have Req : R :=: S <*> 'C_R(T).
  apply/eqP; rewrite eq_sym eqEcard mulgen_subG sSR subsetIl /=.
  rewrite dvdn_leq -1?(part_pnat_id pR) ?p_part ?pfactor_dvdn ?cardG_gt0 //.
  have sCRTR : 'C_R(T) \subset R by rewrite subsetIl.
  rewrite -(LaGrange sCRTR) -card_quotient // cardR_CRT.
  rewrite logn_mul ?cardG_gt0 ?prime_gt0 // (pfactorK 1) // addn1.
  rewrite properG_ltn_log //.
    by rewrite(pgroupS _ pR) // mulgen_subG sSR subsetIl.
  by rewrite properE (mulgen_subr _ _) mulgen_subG subsetI (negbTE nsSCT) andbF.
pose CRT_CRS := 'C_R(T) / 'C_R(S).
have cCRT_CRS : abelian CRT_CRS.
  rewrite sub_der1_abelian // subsetI comm_subG ?subsetIl //=; apply/commG1P.
  suffices CRT_S_CRT: [~: S, ('C_R(T))%G, ('C_R(T))%G] = 1. 
    by apply: three_subgroup=> //; rewrite [[~: _, S]]commGC.
  apply/commG1P; rewrite (subset_trans (commgS S (subsetIl R _))) // centsC.
  by rewrite subsetIr.
have {cCRT_CRS}abelCRT_CRS : p.-abelem CRT_CRS.
  apply/(abelemP primep); split=> //= gCRS.
  case/imsetP=> g; case/setIP=> NCRSg; case/setIP=> Rg CTg /= ->{gCRS}.
  rewrite -morphX //= coset_id // inE groupX //= -sub_cent1.
  apply/subsetP=> y Sy.
  have Syg : [~ y, g] \in T by apply: mem_commg.
  apply/cent1P; apply/commgP; rewrite commgX ?(exponentP expT) //. 
  by apply: (centP CTg).
have nsCRS_R : 'C_R(S) <| R.
  by rewrite (normalS (subsetIl _ _) _ (subcent_normal _ _)) // subsetI subxx.
have nsCRS_CRT : 'C_R(S) <| 'C_R(T).
  by rewrite (normalS _ _ nsCRS_R) ?setIS ?subsetIl // centS.
have p'A_CRS : p^'.-group (A / 'C_R(S)) by apply: quotient_pgroup.
have sT_CRS_CRT_CRS : (T / 'C_R(S)) \subset ('C_R(T) / 'C_R(S)).
  by rewrite quotientS // subsetI comm_subG.
have nSA : A \subset 'N(S) by apply: (char_norm_trans (Ohm_char 1 _) nRA).
have nTA : A \subset 'N(T) by apply: normsR.
have nT_CRS_A_CRT: (A / 'C_R(S)) \subset 'N(T / 'C_R(S)).
  by rewrite quotient_norms.
have nCRT_CRS_A_CRT: (A / 'C_R(S)) \subset 'N(CRT_CRS).
  by rewrite quotient_norms // normsI // norms_cent.
case: (Maschke_abelem abelCRT_CRS p'A_CRS sT_CRS_CRT_CRS _ _)=> //= XCRS.
rewrite -/T; case/dprodP=> /= _ CRT_CRSeq cXCRS_T_CRS.
have nsXCRS_CRT_CRS : XCRS <| CRT_CRS.
  rewrite /CRT_CRS -CRT_CRSeq /normal mulG_subr /= mulG_subG normG andbT /=.
  by rewrite cents_norm.
move: cXCRS_T_CRS CRT_CRSeq; case: (inv_quotientN nsCRS_CRT nsXCRS_CRT_CRS).
move=> /= X ->{nsXCRS_CRT_CRS XCRS cRT_CRSeq} sCRS_X nsX_CRT cX_CRS_T_CRS.
have sXR : X \subset R. 
  by apply: (subset_trans (normal_sub nsX_CRT) (subsetIl _ _)).
have pX := pgroupS sXR pR; have pOX := pgroupS (Ohm_sub 1 _) pX.
move=> CRT_CRSeq; rewrite -quotientIG //; move/trivgP.
rewrite quotient_sub1 /= -/T=> [sTIX_CRS|]; last first.
  by rewrite subIset // normsI //= ?(subset_trans sTR) ?normG // norms_cent.
rewrite -quotient_normG ?(normalS sCRS_X sXR nsCRS_R) //=.
rewrite quotientSGK //= ?normsI // ?norms_cent // => [nXA|]; last first.
  exact: (subset_trans (normal_sub nsCRS_CRT) (normal_norm nsX_CRT)).
have eqT_OCRT: T == 'Ohm_1('C_R(T)).
  rewrite eqEcard -{1}[T](Ohm1_id abelT) OhmS /= ?subsetI ?sTR //=.
  have pOCRT : p.-group 'Ohm_1('C_R(T)).
    by apply: (pgroupS _ pR); apply: (subset_trans (Ohm_sub 1 _)(subsetIl _ _)).
  rewrite -(part_pnat_id pT) -(part_pnat_id pOCRT) !p_part.
  rewrite leq_exp2l ?prime_gt1 // lcardT -ltnS -lcardS properG_ltn_log //.
  rewrite properEneq (OhmS 1) ?subsetIl // andbT /= -/S.
  apply: contra nsSCT; move/eqP=> <-; apply: (subset_trans (Ohm_sub 1 _)).
  exact: subsetIr.
have cardOX : #|'Ohm_1(X)| <= p.
  have neCRS1 : 'C_R(S) != 1.
    apply: contra neZS1; rewrite -eS'ZS (eqP eqS'OCRS); move/eqP=> ->.
    by rewrite Ohm1.
  rewrite -(Ohm1_cyclic_pgroup_prime cycCRS (pgroupS (subsetIl _ _) pR) neCRS1).
  rewrite dvdn_leq ?cardG_gt0 // cardSg //= -(Ohm_id 1) OhmS //=.
  rewrite (subset_trans _ sTIX_CRS) // (eqP eqT_OCRT) subsetI Ohm_sub andbT.
  by rewrite OhmS // (normal_sub nsX_CRT).
have {sTIX_CRS cardOX} cycX : cyclic X.
  rewrite (odd_pgroup_rank1_cyclic pX (oddSg sXR oddR)) -p_rank_Ohm1.
  case eOX1 : ('Ohm_1(X) == 1); first by rewrite (eqP eOX1) p_rank1.
  case: (pgroup_pdiv pOX (negbT eOX1))=> _ pdivOX _.
  have {cardOX}cardOX: #|'Ohm_1(X)| == p.
    by rewrite eqn_leq cardOX /= dvdn_leq // cardG_gt0.
  rewrite p_rank_abelian ?Ohm_id ?cyclic_abelian ?prime_cyclic ?(eqP cardOX) //.
  by rewrite (pfactorK 1).
have eR_SX : R :==: S <*> X.
  rewrite eqEsubset mulgen_subG sSR sXR !andbT Req mulgen_subG.
  rewrite mulgen_subl /=.
  suff ->: 'C_R(T) = T <*> X.
    by rewrite mulgen_subG mulgen_subr andbT (subset_trans sTS) // mulgen_subl.
  apply: (quotient_inj nsCRS_CRT)=> //=. 
    rewrite (normalS _ _ nsCRS_R) // ?(subset_trans sCRS_X) ?mulgen_subl //.
      by rewrite mulgen_subr.
    by rewrite mulgen_subG sTR.
  rewrite -CRT_CRSeq -quotientMr ?(normal_norm nsX_CRT) //; last first. 
    by apply: (subset_trans sXR (normal_norm nsCRS_R)).
  by rewrite norm_mulgenEr // (subset_trans sXR).
clear oddR neR1 TI_CAR p'A pdivR gtp3 rankS expS lcardS neS1 sZSS nZSS neZS1.
clear espS eqS'OCRS cycCRS pTS expT cardR_CRT abelCRT_CRS nsCRS_R nsCRS_CRT.
clear p'A_CRS sT_CRS_CRT_CRS nT_CRS_A_CRT nCRT_CRS_A_CRT CRT_CRS.
clear pOX CRT_CRSeq eqT_OCRT lcardZS cX_CRS_T_CRS lcardT.
have nsS'R : S' <| R by apply: (char_normal_trans (der_char _ _) nsSR). 
have nsXS_S': ~~ ([~: X, S] \subset S'). 
  apply: contra nsTS'=> sXS_S'; rewrite /T (eqP eR_SX).
  rewrite norm_mulgenEr ?(subset_trans sXR (char_norm (Ohm_char 1 _))) //.
  by rewrite commGC commMG ?mul_subG //= (subset_trans sXR (normal_norm nsS'R)).
have {cardS}cardST : #|S / T| = p.
  rewrite card_quotient ?(subset_trans sSR nTR) // -divgS // cardS cardT.
  by rewrite mulnK // muln_gt0 prime_gt0.
have : cyclic (S / T) by rewrite prime_cyclic // cardST.
case/cyclicP=> /= Ty STeq; have: Ty \in S / T by rewrite STeq cycle_id.
case/imsetP=> y /=; case/setIP=> NTy Sy Tyeq; rewrite {}Tyeq {Ty} in STeq.
have {cardS' cardT} cardTS' : #|T / S'| = p.
  rewrite card_quotient ?(subset_trans sTR (normal_norm nsS'R)) //.
  by rewrite -divgS ?commgS // cardT cardS' mulnK // prime_gt0.
have : cyclic (T / S') by rewrite prime_cyclic // cardTS'.
case/cyclicP=> /= S'z TS'eq; have: S'z \in T / S' by rewrite TS'eq cycle_id.
case/imsetP=> z /=; case/setIP=> NS'z Tz S'zeq. rewrite {}S'zeq {S'z}in TS'eq.
have {nsSCT nCRT_R} : ~~ ([~: S, A] \subset T).
  apply: contra nsSCT=> sSA_T; apply: (subset_trans sSR); rewrite -(eqP eRA_R).
  rewrite Req norm_mulgenEl ?(subset_trans sSR nCRT_R) //.
  rewrite commMG /=; last by rewrite cents_norm // subIset // centS ?orbT.
  rewrite mul_subG // ?(subset_trans sSA_T) //=.
  rewrite (subset_trans _ (subsetIr R _)) // commg_subl.
  rewrite (char_norm_trans _ nRA) // subcent_char ?charR ?char_refl //.
  by rewrite Ohm_char.
rewrite gen_subG; case/subsetPn=> sa; case/imset2P=> s a Ss Aa ->{sa}.
rewrite /= -/T => nTsa.
have NXa : a \in 'N(X) by apply: (subsetP nXA).
case/cyclicP: cycX=> x Xeq {cycX}.
have : x^a \in X by rewrite memJ_norm // Xeq cycle_id.
rewrite Xeq; case/cycleP=> i xa_eq.
have NSa : a \in 'N(S) by apply: (subsetP nSA).
have: (coset T (y^a)) \in S / T.
  rewrite morphJ //= ?(subsetP nTA) // memJ_norm ?mem_quotient //.
  by rewrite -quotient_normG /normal ?sTS //= ?(subset_trans sSR) ?mem_quotient.
rewrite STeq; case/cycleP=> j Tya_eq.
have nS'A : A \subset 'N(S') by exact: (char_norm_trans (der_char _ _) nSA).
have NTa : a \in 'N(T) by apply: (subsetP nTA).
have nsS'T : S' <| T by rewrite (normalS _ _ nsS'R) // commgS.
have: (coset S' (z^a)) \in T / S'.
  rewrite morphJ //= ?(subsetP nS'A) // memJ_norm ?mem_quotient //.
  by rewrite -quotient_normG //= mem_quotient.
rewrite TS'eq; case/cycleP=> k S'za_eq.
set Ty := coset T y in Tya_eq; set S'z := coset S' z in S'za_eq. 
have Tya2_eq: coset T (y ^ (a ^+ 2)) = Ty ^+ (j ^2)%N.
  rewrite morphJ // ?groupX ?(subsetP nTA) //= morphX // conjgM -morphJ //=.
  by rewrite Tya_eq conjXg -morphJ //= Tya_eq -expgn_mul.
have : coset T s \in <[coset T y]> by rewrite -STeq mem_quotient.
case/cycleP=> m Ts_eq.
have {cardST oddA} nej21_modp : j^2 != 1 %[mod p].
  apply: contra nTsa; rewrite -cardST STeq -eq_expg_mod_order expg1 -Tya2_eq.
  move/eqP=> cardTya_eq'.
  have Tya_eq': coset T (y ^ a) = Ty.
    have <- : a ^+ (2 * (expgn_inv <[a]> 2)) = a.
      rewrite expgn_mul expgnK ?cycle_id //= coprime_sym prime_coprime //=.
      by rewrite dvdn2 negbK (oddSg _ oddA) // cycle_subG.  
    elim : (expgn_inv _ _)=>[|n ih]; first by rewrite muln0 expg0 conjg1.
    rewrite mulnS addnC expgn_add conjgM morphJ ?groupJ ?groupX //= ih.
    by rewrite -morphJ ?groupX.
  have NTs : s \in 'N(T) by apply: (subsetP (subset_trans sSR nTR)). 
  rewrite coset_idr //= ?groupR // morphR //= Ts_eq -/T commgEl conjXg.
  by rewrite -morphJ //= Tya_eq' mulVg.
have nsTS : T <| S by rewrite /normal sTS /= commg_norml. 
have eS_Ty: S = T <*> <[y]>.
  apply: (quotient_inj nsTS)=> /=; last first.
    by rewrite STeq mulgenC quotient_mulgen ?cycle_subG // quotient_cycle.
  rewrite /normal mulgen_subl //= (subset_trans _ (commg_norm _ _)) //.
  rewrite mulgen_subG (subset_trans sTS (mulgen_subl _ _)) /=.
  by rewrite (subset_trans _ (mulgen_subr _ _)) // cycle_subG (subsetP sSR).
have eT_S'z: T = S' <*> <[z]>.
  apply: (quotient_inj nsS'T)=> /=.
    by rewrite /normal mulgen_subl //= mulgen_subG normG /= cycle_subG.
  by rewrite TS'eq mulgenC quotient_mulgen ?cycle_subG // quotient_cycle.
have {ncSS eT_S'z} ne_yz1: [~ y, z] != 1.
  apply: contra ncSS=> yz_eq; rewrite eS_Ty norm_mulgenEr ?cycle_subG //.
  rewrite /= -/T eT_S'z norm_mulgenEr ?cycle_subG //= -/S' -mulgA.
  have cYZ : <[z]> \subset 'C(<[y]>).
    by rewrite cycle_subG /= cent_cycle cent1E (commgP yz_eq).
  have zyeq : <[z]> <*> <[y]> = <[z]> * <[y]>.
    by rewrite norm_mulgenEr // cents_norm // centsC. 
  rewrite -zyeq abelianM -/S /= -/S' eS'ZS center_abelian /=.
  rewrite (subset_trans (subsetIr _ _)) ?andbT; last first.
    by rewrite centS // mulgen_subG ?cycle_subG (subsetP sTS) //=.
  by rewrite zyeq abelianM ?cycle_abelian.
have {nXA} nei0_modp : i != 0 %[mod p].
  apply: contra nsXS_S'; rewrite eqn_mod_dvd // subn0 => p_div_i.
  case eX1 : (X == 1%G); first by rewrite (eqP eX1) comm1G sub1G.
  have [_ _ [t cardX]] := pgroup_pdiv (pgroupS sXR pR) (negbT eX1).
  suff : coprime #[x] i. 
    by rewrite orderE -Xeq cardX coprime_pexpl // prime_coprime // p_div_i.
  by rewrite -generator_coprime -xa_eq /generator cycleJ (normP _) // -Xeq.
have Txy : [~ x, y] \in T.
  by rewrite [T]commGC mem_commg // (subsetP sXR) // Xeq cycle_id.
have Xx : x \in X by rewrite Xeq cycle_id.
have {nsX_CRT} CTx : T \subset 'C[x].
  by rewrite sub_cent1 (subsetP (subset_trans (normal_sub nsX_CRT) _))?subsetIr.
have {eS_Ty nsXS_S'} nS'xy : [~ x, y] \notin S'.
  apply: contra nsXS_S'=> S'xy; rewrite eS_Ty norm_mulgenEr ?cycle_subG //= -/T.
  have eTX1 : [~: T, X] = 1.
    by apply/commG1P; rewrite centsC Xeq cycle_subG -sub_cent1. 
  rewrite commGC commMG eTX1 ?norms1 //= mul1g commGC Xeq gen_subG /= -/S'.
  apply/subsetP=> g; case/imset2P=> xu yv; case/cycleP=> u ->{xu}.
  case/cycleP=> v ->{xv} ->{g}; rewrite commXXg ?groupX //.
    by apply: commute_sym; apply: (cent1P _); apply: (subsetP CTx).
  apply/cent1P; rewrite (subsetP _ _ Sy) // sub_cent1 (subsetP _ _ S'xy) //.
  by rewrite eS'ZS subsetIr.
have S'yz : [~ y, z] \in S'.
  by rewrite mem_commg // (subsetP (normal_sub nsTS)).
have {sCRS_X}Xyz : [~ y, z] \in X.
  by rewrite (subsetP sCRS_X) // (subsetP _ _ S'yz) // eS'ZS setSI.
move: Tya_eq; rewrite -morphX //=.
case/kercoset_rcoset; rewrite ?groupJ ?groupX // => t Tt yaeq'.
move: (S'za_eq); rewrite -morphX //=.
case/kercoset_rcoset; rewrite ?groupJ ?groupX // ?(subsetP nS'A) //= -/S'.
move=> s' S's' zaeq'.
have cS'S : S' \subset 'C(S) by rewrite eS'ZS subsetIr.
have {abelT}yzi_eq : [~ y, z] ^+ i = [~ y, z] ^+ (j * k).
  move: Xyz; rewrite Xeq; case/cycleP=> u yzeq.
  rewrite {1}yzeq -expgn_mul mulnC expgn_mul -xa_eq -conjXg -yzeq conjRg.
  rewrite yaeq' commMgJ.
  have ->: [~ t, z ^ a] = 1.
    apply/eqP; apply/commgP; apply: (centsP (abelem_abelian abelT))=> //.
    by rewrite memJ_norm.
  rewrite conj1g mul1g zaeq' commgMJ.
  have ->: [~ y ^+ j, s'] = 1.
    apply/eqP; apply/commgP; apply: commute_sym; apply: commuteX.
    by apply: (centsP cS'S).
  rewrite conj1g mulg1.
  rewrite commXXg //; apply: commute_sym; apply: (centsP cS'S)=> //.
  by rewrite (subsetP sTS). 
have nS'R := normal_norm nsS'R.
have nS'T := normal_norm nsS'T.
have NS'x : x \in 'N(S') by rewrite (subsetP (subset_trans sXR nS'R)).
have NS'y : y \in 'N(S') by rewrite (subsetP (subset_trans sSR nS'R)).
have NS'a : a \in 'N(S') by rewrite (subsetP nS'A).
have xyk_eq : coset S' ([~ x, y] ^+ k) = coset S' ([~ x, y] ^+ (i * j)).
  have : coset S' [~ x , y] \in T / S' by rewrite mem_quotient.
  rewrite TS'eq; case/cycleP=> u S'xyeq; rewrite morphX ?(subsetP _ _ Txy) //=.
  rewrite S'xyeq -expgn_mul mulnC expgn_mul -S'za_eq morphJ //. 
  rewrite -conjXg /= -S'xyeq morphR //=.
  rewrite conjRg -!morphJ //= -morphR /= ?groupJ // xa_eq yaeq' commgMJ.
  have ->: [~ x ^+ i, t] = 1; first clear -CTx Tt.
    apply/eqP; apply/commgP; apply/cent1P; rewrite groupX // cent1C.
    by rewrite (subsetP CTx).
  rewrite conj1g mulg1 morphR ?groupX //= !morphX // ?groupR //=. 
  rewrite commXXg; first by rewrite morphR ?groupX.
    clear -Tt CTx NS'x NS'y Txy; apply/commgP; rewrite -!morphR // ?groupR //. 
    rewrite /= coset_id //.
    suff -> : [~ x, [~x, y]] = 1 by rewrite group1.
    by apply/eqP; apply/commgP; apply/cent1P; rewrite cent1C (subsetP CTx). 
  suff cSS'_TS' : S / S' \subset 'C(T / S').
    by apply: (centsP cSS'_TS'); rewrite -?morphR // ?mem_quotient.
  rewrite centsC (subset_trans (quotientS _ sTS)) //.
  apply: (der_abelian 0 [group of S]).
have pdvdyz: p %| #[[~ y, z]].
  have neyz1 : <[[~ y, z]]> != 1 by rewrite cycle_eq1.
  have pyz : p.-group <[[~ y, z]]>.
    rewrite (pgroupS _ pR) // cycle_subG groupR //.
      by rewrite (subsetP sSR).
    by rewrite (subsetP sTR).
  by case: (pgroup_pdiv pyz neyz1).
move/eqP: yzi_eq; rewrite eq_expg_mod_order; move/eqP.
move/(congr1 (fun x => x %% p)); rewrite !(modn_dvdm _ pdvdyz)=> e_i_jk_p.
have pdvdxy: p %| #[coset S' [~ x, y]].
  have ne_xy1 : <[coset S' [~ x, y]]> != 1.
    rewrite cycle_eq1; apply: contra nS'xy; move/eqP; apply: coset_idr.
    by rewrite groupR.
  have pxy : p.-group <[coset S' [~ x, y]]>.
    rewrite -quotient_cycle ?groupR // quotient_pgroup //.
    rewrite (pgroupS _ pR) // cycle_subG groupR //.
      by rewrite (subsetP sXR).
    by rewrite (subsetP sSR).
  by case: (pgroup_pdiv pxy ne_xy1). 
move/eqP: xyk_eq; rewrite !morphX // ?groupR // eq_expg_mod_order; move/eqP.
move/(congr1 (fun x => x %% p)); rewrite !(modn_dvdm _ pdvdxy)=> e_k_ij_p.
move: (e_i_jk_p); rewrite -modn_mulmr e_k_ij_p modn_mulmr mulnC -mulnA.
have gt_jj0 : j * j > 0.
  rewrite muln_gt0 andbb lt0n; apply: contra nei0_modp.
  by rewrite e_i_jk_p; move/eqP=> -> /=; rewrite mul0n.
apply/eqP; rewrite eq_sym eqn_mod_dvd; last by rewrite leq_pmulr.
rewrite -{2}(muln1 i) -muln_subr (euclid _ _ primep).
rewrite -eqn_mod_dvd // negb_or nej21_modp andbT. 
by rewrite -(subn0 i) // -eqn_mod_dvd // leq0n.
Qed.

Let subset_transP:
  forall (fT : finType) (A B C : {set fT}), A \subset B -> 
    reflect (forall x, x \in A -> x \in B -> x \in C) (A \subset C).
Proof.
move=> fT A B C sAB; apply: (iffP subsetP); first by move=> sAC *; apply sAC.
by move=> xC a aA; apply: xC => //; apply: subsetP _ _ aA.
Qed.

Implicit Arguments subset_transP [fT A B C].

Let coset_modact_astab :
    forall (gT rT : finGroupType) (D : {group gT}) (to : action D rT) 
    (H : {group _}) (K : {group _}) (x : gT),
    x \in 'N_D(K) -> K \subset 'C( H | to) ->
  coset K x \in 'C( H | to %% K ) -> x \in 'C( H | to).
Proof.
move=> gT rT D to H K x; case/setIP=> xD xN sKC.
rewrite inE mem_quotient // !inE xD => /= HC.
apply/(subset_transP HC)=> h hH; rewrite !inE (modactE xD) ?(subsetP _ _ hH) //.
by rewrite -astabCin ?subsetIl // subIset // orbC sKC.
Qed.

(* This is B & G, Theorem 4.17 *)
Lemma rank2_odd_sol_Aut_pgroup_der1 : 
    forall gT (R : {group gT}) (A : {group perm_of_finGroupType gT}) p, 
    p.-group R -> odd #|R| -> A \subset Aut R -> solvable A -> 
    'r(R) <= 2 -> odd #|A| ->
  p.-group A^`(1).
Proof.
move=> gT R A p pR oddR sAAut solA rR oddA.
wlog ntR: / R :!=: 1.
  case: eqP sAAut => [->|ntR _]; last by apply.
  by rewrite Aut1; move/trivgP=> ->; rewrite derg1 commG1 pgroup1.
have [p_pr _ [r cR]] := pgroup_pdiv pR ntR.
case oddp: (odd p); last first.
  by move: oddp oddR; rewrite cR odd_exp orbC; move=>->.
case: (critical_odd _ pR)=> // H [cHR sHRZ] ncH exH pCAu.
have pCAH : p.-group('C_A(H | 'A_R)) := pgroupS (subsetIr _ _) pCAu.
have pH := pgroupS (char_sub cHR) pR.
have rH : 'r(H) <= 2.
  by rewrite (leq_trans _ rR) // !(@rank_pgroup _ p) // p_rankS ?char_sub.
have ntH : H :!=: 1.
  by case: eqP (exponent1 gT) exH (prime_gt1 p_pr) (ltnn p) => // -> -> <-.
have cH : #|H| <= p^3.
  have := pgroup_rank_le2_exponentp pH rH; rewrite exH dvdnn.
  have [_ _ [s ->]] := pgroup_pdiv pH ntH.
  by rewrite pfactorK // leq_exp2l ?prime_gt1 //; apply.
pose V := H / 'Phi(H); pose C := 'C_A(V | 'A_R / _).
have abeV : p.-abelem V by exact: Phi_quotient_abelem.
have acts_APH : [acts A, on 'Phi(H) | 'A_R].
  by apply: gacts_char => //; exact: (char_trans (Phi_char _)).
have sPR : 'Phi(H) \subset R by rewrite (subset_trans (Phi_sub _)) ?char_sub.
have sCAHC: 'C_A(H|'A_R) \subset C.
  have nPH : H \subset 'N('Phi(H)) by rewrite char_norm ?Phi_char.
  have qdomA : A \subset qact_dom  'A_R 'Phi(H) by rewrite qact_domE.
  apply/subsetP=> x; rewrite /C 3!inE; case/and3P=> Ax AutRx sHFix.
  rewrite 2!inE Ax {1}qact_domE //=.
  rewrite (subsetP acts_APH) // inE; apply/subsetP=> vH; case/morphimP.
  move=> v Nv Hv ->{vH} /=; rewrite inE qactE ?(subsetP _ _ Ax) //.
  by move/subsetP: sHFix; move/(_ _ Hv); rewrite inE; move/eqP=> ->.
have pCC : p.-group(C / 'C_A(H | 'A_R)).
  suffices p'1: forall x, x \in  C  / 'C_A(H | 'A_R) -> p^'.-elt x -> x = 1.
    apply/pgroupP=> q q_pr; case/Cauchy=> // y yC q_y. 
    apply: contraLR (q_pr) => p'q; rewrite -q_y.
    by rewrite (p'1 y) ?order1 // /p_elt ?q_y pnatE.
  move=> z zC p'z; case/andP: (cHR) => sHR; move/forall_inP=> charH.
  have cPHH := Phi_char H; have [/= sPHH nPHH] := andP (char_normal cPHH).
  have pPH := pgroupS sPHH pH; have cop := pnat_coprime pPH p'z.
  have zAR : z \in Aut R / _.
    case: (cosetP z) zC => w wN -> SS; apply: subsetP _ _ SS.
    by rewrite quotientS // (subset_trans _ sAAut)//subsetIl.
  have ? : forall H A, 'C_A(H | 'A_R) \subset 'C(H | 'P).
    by move=>? ?; apply/subsetP=> a; rewrite !inE; case/and3P=> ? ?.
  have act : [acts <[z]>, on H | 'A_R %% _ ].
    apply/subsetP=> xp xpC; rewrite 3?inE (subsetP _ _ xpC) ?cycle_subG //.
    apply/subsetP=> h hH; rewrite inE; case/cyclePmin: xpC=> i _ ->.
    case/morphimP: zC => w wN; case/setIP=> wA wC -> /=.
    have wAR := subsetP sAAut _ wA. 
    rewrite -morphX //= modactE ?in_group //.
      by apply: subsetP (charH _ (groupX i wAR)) _ _; apply/imsetP; exists h.
    by apply: subsetP _ _ hH; rewrite -astabC /= setIA (setIidPr sAAut).
  have AA : {acts <[z]>, on group H | 'A_R %% _}.
    by split; rewrite ?gacentE ?subIset ?sAAut ?subxx // subsetI sHR -astabC /=.
  have {act} act : {acts <[z]>%G, on group H | <[AA]> }.
    by split; rewrite // acts_actby subxx setIid.
  have thm1_8: z \in 'C(V | <[AA]> / _) -> z \in 'C(H | <[AA]>).
    rewrite -!cycle_subG /= !astabCin ?qact_domE ?gacts_char // => V_fix.
    apply/setIidPl; rewrite -subgacentE // -['C_(H | _)(_)]genGid.
    apply: Phi_nongen; apply/eqP; rewrite eqEsubset mulgen_subG sPHH subsetIl.
    rewrite -genM_mulgen sub_gen // -quotientSK // quotientGI //= subsetI subxx.
    rewrite ext_coprime_quotient_cent ?gacts_char ?(pgroup_sol pPH) //.
    by rewrite gacentE ?qact_domE  ?gacts_char // subsetI subxx V_fix. 
  case/morphimP: zC => x xN; case/setIP=> xA xC defz; rewrite defz /=.
  have xAu : x \in Aut R by apply: subsetP sAAut _ _.
  suff zCm: z \in 'C(V | <[AA]> / 'Phi(H)) => [|{thm1_8}].
    apply: coset_id; rewrite inE xA /=.
    move/thm1_8: zCm; rewrite astab_actby // setIid inE cycle_id defz => /= xCC.
    by apply: coset_modact_astab _ (subsetIr _ _) xCC; rewrite inE xAu xN.
  have xNPH := subsetP (gacts_char 'A_R sAAut (char_trans cPHH cHR)) _ xA.
  rewrite defz /= in AA act *.  
  rewrite inE {1}qact_domE // astabs_actby /= inE cycle_id /=.
  rewrite (_: (_ \in _) = true); last first.
    rewrite (setIidPr sPHH) inE mem_quotient // inE; apply/subsetP=> h hPH.
    rewrite inE /= modactE ?(astabs_act _ xNPH) // (subsetP _ _ hPH) //.
    by rewrite (subset_trans sPHH) // -astabC /= setIA (setIidPr sAAut) /=.
  rewrite inE /=; apply/subsetP=> v'; case/morphimP=> v vN vH ->.
  rewrite inE /= qactE // ?qact_domE //; last first.
    by apply: subsetP (gacts_char _ (subxx _) cPHH) _ (cycle_id _).
  rewrite actbyE ?cycle_id //= modactE ?(subsetP _ _ vH) 1?setIA //; last first.
    by rewrite (setIidPr sAAut) -astabC /=.
  by rewrite -(astab_act xC (mem_quotient _ vH)) /= qactE ?qact_domE // xNPH.
have pC : p.-group C.
  move: pCC; rewrite pquotient_pgroup // normsI //.
    by rewrite normsG // subsetIl.
  rewrite (subset_trans _ (astab_norm _ _)) //=.
  by apply: gacts_char => //; rewrite (subset_trans (subsetIl _ _)).
have nRA : {acts A, on group V | 'A_R / 'Phi(H)}.  
  split; rewrite ?quotientS ?(char_sub cHR) //= acts_quotient //.
  rewrite qact_domE /= ?(subset_trans (Phi_sub _)) ?(char_sub cHR) //.
  by rewrite subsetI // !gacts_char ?(char_trans (Phi_char _)).
pose fA := actperm <[nRA]> @* A.
have abfA : A/C \isog fA.
  by rewrite /C -[V]setIT -(astab_actby nRA) -ker_actperm first_isog.
have nPH : H \subset 'N('Phi(H)) := char_norm (Phi_char H).
have: 'r(V) <= 3.
  rewrite (rank_abelem abeV) /= (leq_trans (logn_quotient _ _ _)) //.
  move: cH; have [_ _ [[->|[->|]]]] := pgroup_pdiv pH ntH; rewrite ?pfactorK //.
  by case=> [->|m ->]; [ rewrite pfactorK | rewrite leq_exp2l // prime_gt1 ].
rewrite 2!leq_eqVlt !eqSS !ltnS (orbC (_ == 2)); case/or3P => rV.
  have trivPhi: 'Phi(H) == 1.
    rewrite trivg_card_le1 -(@leq_pmul2r #|V|) ?cardG_gt0 //.
    rewrite  {1}card_quotient // LaGrange ?Phi_sub // mul1n.
    rewrite -(part_pnat_id (abelem_pgroup abeV)) p_part.
    by rewrite -(rank_abelem abeV) (eqP rV).
  have cHH: abelian H by rewrite (@abelem_abelian _ p) -?(trivg_Phi pH).
  case/idPn: rH; rewrite -ltnNge -(eqP rV).
  by rewrite /V (eqP trivPhi) (isog_rank (quotient1_isog _)).
- have abAC : abelian (A / C).
    have pV := abelem_pgroup abeV.
    have oddV : odd #|V| := quotient_odd _ (oddSg _ oddR).
    rewrite (isog_abelian abfA) /= -/fA; move: rV.
    rewrite (rank_pgroup pV) -odd_pgroup_rank1_cyclic ?oddV ?(char_sub cHR) //=.
    move/Aut_cyclic_abelian; rewrite /= -/V => abAV.
    by apply: abelianS _ abAV; exact: im_actperm_Aut.
  apply: pgroupS (der1_min _ abAC) pC.
  by rewrite normsI ?normG ?(subset_trans _ (astab_norm _ _)) //; case: (nRA).
have ? : A \subset 'N(C).
  rewrite normsI ?(normG _) // (subset_trans _ (astab_norm _ _)) //.
  by rewrite acts_quotient // qact_domE // subsetI acts_APH gacts_char.
rewrite -(pquotient_pgroup pC) ?(subset_trans (der_sub 1 A)) //= -/C.
have abeVV : p.-abelem(sdpair1 <[nRA]> @* V) := morphim_abelem _ abeV. 
have nVVA : sdpair2 <[nRA]> @* A \subset 'N(sdpair1 <[nRA]> @* V). 
  exact: im_sdpair_norm.
have ntVV : sdpair1 <[nRA]> @* V != 1.
  rewrite -cardG_gt1 (card_injm (injm_sdpair1 _)) //= cardG_gt1 /= -/V.
  by move: rV; case: (@eqP _ V) => // ->; rewrite rank1.
pose repr := morphim_repr (abelem_repr abeVV ntVV nVVA) (subxx _).
have dimVV : 'dim (sdpair1 <[nRA]> @* V) = 2.
  rewrite -(eqP rV) -(injm_rank (injm_sdpair1 <[nRA]>)) ?subxx //.
  by rewrite (rank_abelem abeVV) (dim_abelemE abeVV ntVV).
have oddAC: odd #|(A / rker repr)| := quotient_odd _ oddA.
have fait := kquo_mx_faithful repr; have := der1_odd_GL2_charf oddAC.
rewrite -dimVV => thm26; move/thm26: fait => {thm26} /=.
have -> : rker repr = C.
  rewrite rker_morphim rker_abelem morphpreI morphimK //=.
  rewrite (trivgP (injm_sdpair2 <[nRA]>)) 1?setIA ?mul1g //.
  by rewrite -astabEsd // astab_actby setIA !setIid.
rewrite quotient_der //= -/C => Fp; rewrite -(@eq_pgroup _ [char 'F_p]%R) //. 
by apply: GRing.charf_eq; exact: char_Fp.
Qed.

(* This is B & G, Theorem 4.18(a) *)
Lemma rank2_max_pdiv : forall gT (G : {group gT}) p, 
    solvable G -> odd #|G| -> 'r_p(G) <= 2 -> 
  forall q, prime q -> q %| #|G / 'O_p^'(G)| -> q <= p.
Proof.
move=> gT G p solG oddG rG q pr_q qd.
wlog trivK : gT G p solG oddG rG q pr_q qd / 'O_p^'(G) = 1.
  move/(_ _ (G / 'O_p^'(G))%G p ); rewrite quotient_sol // quotient_odd //.
  rewrite trivg_pcore_quotient -(isog_card (quotient1_isog _)); apply=> //=.
  case: (Sylow_exists p G) => X SylX.
  have nKX : X \subset 'N('O_p^'(G)).
    by rewrite (subset_trans (pHall_sub SylX)) // normal_norm ?pcore_normal.
  move/(quotient_pHall nKX) : (SylX) => /= SylXK.
  rewrite (p_rank_Sylow SylXK) /= -(isog_p_rank (quotient_isog nKX _)) //.
    exact: leq_trans (p_rankS _ (pHall_sub SylX)) rG.
  exact: coprime_TIg (pnat_coprime (pHall_pgroup SylX) (pcore_pgroup _ _)).  
set R := 'O_p(G); set C := 'C_G(R); have pR : p.-group R by exact: pcore_pgroup.
have sCR : C \subset R by rewrite /C /R -(Fitting_eq_pcore _) ?cent_sub_Fitting.
have pC : p.-group C := pgroupS sCR pR; have oddR := oddSg (pcore_sub p _) oddG.
have rR : 'r(R) <= 2.
  by rewrite (rank_pgroup pR) (leq_trans (p_rankS _ (pcore_sub _ _)) rG).
move: (dvdn_trans qd (dvdn_quotient _ _)); case/Cauchy=> //= a aG oa.
case: (eqVneq p q) => [-> //| npq]; move:(npq); rewrite eq_sym=>nqp.
have ?: a \in 'N(R) :\: 'C(R).
  rewrite inE [a \in 'N(_)](subsetP _ _ aG) ?char_norm ?pcore_char ?andbT //.
  apply: contra nqp => aCR; have aR : a \in R by rewrite (subsetP sCR) ?inE ?aG.
  by move/pnatP: (mem_p_elt pR aR); apply; rewrite ?order_gt0 // -oa dvdnn.
case: (automorphism_prime_order_pgroup_rank_le2 _ _ rR _ _ npq oa)=>// _ [] _.
exact: leqW.
Qed.

(* This is B & G, Theorem 4.18(c,e) *)
Lemma rank2_pdiv_compl_der_abelian_p'group: forall gT (G : {group gT}) p, 
    solvable G -> odd #|G| -> 'r_p(G) <= 2 ->
  [/\ p^'.-Hall(G^`(1)) 'O_p^'(G^`(1)), 
      abelian (G / 'O_{p^',p}(G)) & 
      p^'.-group (G / 'O_{p^',p}(G))].
Proof.
move=> gT G p solG oddG rG.
wlog trivK : gT G p solG oddG rG / 'O_p^'(G) = 1.
  have nKG : G \subset 'N('O_p^'(G)) by rewrite normal_norm ?pcore_normal.
  move/(_ _ (G / 'O_p^'(G))%G p); rewrite quotient_sol // quotient_odd //=.
  have -> : 'r_p(G / 'O_p^'(G)) <= 2.
    have [X SX] := Sylow_exists p G.
    have nKX : X \subset 'N('O_p^'(G)) by rewrite (subset_trans (pHall_sub SX)).
    move/(quotient_pHall nKX) : (SX) => /= SXK.
    rewrite (leq_trans _ rG) // (p_rank_Sylow SXK) /=.
    rewrite -(isog_p_rank (quotient_isog nKX _)) ?p_rankS ?(pHall_sub SX) //.
    exact: coprime_TIg (pnat_coprime (pHall_pgroup SX) (pcore_pgroup _ _)).
  rewrite -quotient_der //= trivg_pcore_quotient; do 4 move/(_ (refl_equal _)). 
  have nKG' : G^`(1) \subset 'N('O_p^'(G)) := subset_trans (der_sub _ _) nKG.
  move: (second_isog nKG') => /= iso. 
  have pKI := pgroupS (subsetIl _ G^`(1)) (pcore_pgroup p^' G).
  have nKIG : ('O_p^'(G) :&: G^`(1)) <| G^`(1).
    by rewrite /normal subsetIr normsI // ?normG ?norml_norm ?pcore_normal.
  rewrite (pseries_pop2 _ (trivg_pcore_quotient _ _)) /= -quotient_pseries2.
  have iso3 := third_isog _ (pcore_normal p^' G) (pseries_normal _ G).
  case=> hall abel pg; split.
    rewrite -(pquotient_pHall pKI nKIG) /normal /=; last first.
      by rewrite normsI ?(subset_trans (pcore_sub _ _)) ?normG ?pcore_max //.
    move: hall; rewrite !pHallE /=; case/andP=> _ hall.
    rewrite -pquotient_pcore // pcore_sub.
    by rewrite (isog_card iso) (isog_card (bgFunc_isog (bgFunc_pcore p^') iso)).
  - by rewrite -(isog_abelian (iso3 _ _)) //= -pseries1 pseries_sub_catl.
  by rewrite /pgroup -(isog_card (iso3 _ _)) //= -pseries1 pseries_sub_catl.
set R := 'O_p(G); set C := 'C_G(R); have pR : p.-group R by exact: pcore_pgroup.
have nRG : G \subset 'N(R) by rewrite char_norm ?pcore_char.
have pG'C : p.-group (G^`(1) <*> C).
  have sCR : C \subset R.
    by rewrite /C /R -(Fitting_eq_pcore _) // cent_sub_Fitting.
  have pC : p.-group C := pgroupS sCR (pcore_pgroup _ _).
  have nCG : G \subset 'N(C) by rewrite normsI ?normG // norms_cent.
  have: p.-group((G / C)^`(1)). 
    pose J := [morphism of restrm nRG (conj_aut [group of R])].
    have inA : J @* G \subset Aut R by rewrite morphim_restrm Aut_conj_aut.
    have rR : 'r(R) <= 2.
      by rewrite (rank_pgroup pR) (leq_trans (p_rankS _ (pcore_sub _ _))).
    have solA : solvable (J @* G) by rewrite morphim_sol.
    have oddA : odd #|J @* G| by rewrite morphim_odd.
    have oddR : odd #|R| := oddSg (pcore_sub _ _) oddG.
    have pA' : p.-group (J @* G)^`(1). 
      exact: rank2_odd_sol_Aut_pgroup_der1 _ oddR _ solA rR oddA.
    rewrite /pgroup (_: C = 'ker J); last by rewrite ker_restrm ker_conj_aut.
    by rewrite (isog_card (isog_sFunctor (gFunc_der 1) (first_isog J))). 
  have ? : G^`(1) \subset 'N(C) by rewrite (subset_trans _ nCG) // der_sub.
  have ? : G^`(1) <*> C \subset 'N(C) by rewrite mulgen_subG andbC normG.
  by rewrite -quotient_der // -quotient_mulgen // pquotient_pgroup ?pC. 
have sG'CR : G^`(1) <*> C \subset R.
  apply: pcore_max; rewrite /normal ?pG'C // mulgen_subG subsetIl der_sub.
  by rewrite norms_mulgen // ?der_norm ?normsI ?normG ?norms_cent.
have pG' := pgroupS (subset_trans (mulgen_subl _ _) sG'CR) pR.
rewrite pseries_pop2 //.
have abGR : abelian (G / R).
  by rewrite sub_der1_abelian // (subset_trans _ sG'CR) // mulgen_subl.
split => //; first exact: nilpotent_pcore_Hall (pgroup_nil pG').
(* there must be a lemma for that, I think *)
apply/pgroupP=> q pr_q; case/Cauchy=> // x; rewrite -cycle_subG !inE /= -/R.
move => xGO xq; apply: contraL (prime_gt1 pr_q); move/eqP=> defq.
have px : p.-group <[x]> by rewrite /pgroup -orderE xq defq pnat_id // -defq.
have nx : <[x]> <| G / R by rewrite /normal xGO cents_norm ?(centsS xGO).
have := pcore_max px nx; rewrite trivg_pcore_quotient //. 
by move/subset_leq_card; rewrite cards1 -orderE xq -ltnNge.
Qed.

(* This is B & G, Theorem 4.18(b) *)
Lemma rank2_pdiv_complement : forall gT (G : {group gT}) (p := pdiv #|G|),
    solvable G -> odd #|G| -> 'r_p(G) <= 2 ->
  p^'.-Hall(G) 'O_p^'(G).
Proof.
move=> gT G p solG oddG rG; rewrite /pHall pcore_pgroup char_sub ?pcore_char //.
rewrite pnatNK -card_quotient ?char_norm ?pcore_char//; apply/pgroupP=> q pq qd.
rewrite [_ \in _]eqn_leq pdiv_min_dvd ?prime_gt1 // 1?(rank2_max_pdiv solG) //. 
exact: dvdn_trans qd (dvdn_quotient _ _).
Qed.

(* This is B & G, Theorem 4.18(d) *)
Lemma rank2_pdiv_psubg_pcore : forall gT (G A: {group gT}) p,
    solvable G -> odd #|G| -> 'r_p(G) <= 2 ->
  p^'.-subgroup(G^`(1)) A -> A \subset 'O_p^'(G^`(1)). 
Proof.
move=> gT G A p solG oddG rG; case/andP=> sAG' p'A.
have sG'G := der_sub 1 G; have solG' := solvableS sG'G solG.
case: (HallSubset solG' sAG' p'A) => H HH sAH; rewrite (subset_trans sAH _) //. 
case: (rank2_pdiv_compl_der_abelian_p'group _ _ rG) => // compl _ _.
case: (HallConj solG' HH compl) => x xG' ->.
by rewrite /= (normP _) // -/p (subsetP _ _ xG') ?char_norm ?pcore_char.
Qed.

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
