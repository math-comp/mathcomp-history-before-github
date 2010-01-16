Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime binomial.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent maximal hall.
Require Import BGsection1.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* why is bigU so hard to use with unions? *)
Lemma lcmnS : forall (T : finType) (A B: {set T}) (F : T -> nat), 
  A \subset B -> 
  \big[lcmn/1%N]_(x \in A) (F x) %| \big[lcmn/1%N]_(x \in B) (F x).
Proof.
move=> T A B F sAB.
have B_eq : B = A :|: (B :\: A).
  by rewrite setDE setUIr setUCr setIT (setUidPr _).
have B_eq' : B =i [predU (mem A) & (mem (B :\: A))].
  by rewrite {1}B_eq => x; rewrite !inE.
rewrite (eq_bigl _ _ B_eq') bigU /=; last first.
  by rewrite disjoint_sym disjoints_subset setDE subsetIr.
exact: dvdn_lcml.
Qed.

(* shouldn't this, and Pascal, be proved for arbitrary rings? *)
(* how should it be stated? *)
Lemma geometric_sum : forall (a n : nat), a^n - 1 = (a - 1) * \sum_(i < n) a^i.
Proof.
move=> a; elim=> [|n ih]; first by rewrite expn0 subnn big_ord0 muln0.
case a0 : (a == 0); first by rewrite (eqP a0) exp0n ?ltn0Sn. 
rewrite expnS big_ord_recr /= muln_addr -ih muln_subl mul1n addnC. 
have agt0 := (neq0_lt0n a0).
by rewrite addn_subA ?expn_gt0 ?agt0 // subnK // leq_pmull.
Qed.

(* how should this be stated in full generality? *)
Lemma modn_sumn : forall n m F, 
  \sum_(i < n) F i = \sum_(i < n) F i %% m  %[mod m].
Proof.
elim => [|n ih] m F; first by rewrite !big_ord0.
by rewrite !big_ord_recr /= -modn_add2m ih modn_addml.
Qed.

Import GroupScope.

Section Exponent.

Variables (gT : finGroupType).
 
Lemma exponentS: forall (A B: {set gT}),
  A \subset B -> exponent A %| exponent B.
Proof. by move=> A B sAB; apply: lcmnS. Qed.

(* dvdn_exponent should be strengthened - same proof *)
Lemma dvdn_exponent' : forall x (A : {set gT}), x \in A -> #[x] %| exponent A.
Proof. by move=> x A Ax; rewrite /exponent (bigD1 x) //= dvdn_lcml. Qed.

(* same here *)
Lemma exponentP' : forall (A : {set gT}) n,
  reflect (forall x, x \in A -> x ^+ n = 1) (exponent A %| n).
Proof.
rewrite /exponent => A n; apply: (iffP idP) => [eAn x Ax | eAn].
  apply/eqP; rewrite -order_dvdn; apply: dvdn_trans eAn; exact: dvdn_exponent'.
apply big_prop=> [|p' q p'n qn|x Ax]; [exact: dvd1n | by rewrite dvdn_lcm p'n | ].
by rewrite order_dvdn eAn.
Qed.

(* In this end, I didn't need this. But is it useful? *)
Lemma abelian_exponent_gen : forall (A : {set gT}), 
  abelian A -> exponent << A >> = exponent A.
Proof.
move=> A; rewrite -abelian_gen => abelA.
apply/eqP; rewrite eqn_dvd; apply/andP; split; last first.
  exact: exponentS (subset_gen _).
apply/exponentP.
suffices genAsub : << A >> \subset [set x \in << A >> | x ^+ exponent A == 1].
  move=> x /= cycAx; move/(subsetP genAsub _): (cycAx). 
  by rewrite inE cycAx; case/eqP. 
rewrite -[[set x | _]]gen_set_id.
  apply: genS; apply/subsetP => x Ax; rewrite inE (subsetP (subset_gen _)) //.
  by rewrite -order_dvdn dvdn_exponent'.
apply/group_setP; split; first by rewrite inE exp1gn eq_refl group1.
move=> x y; rewrite !inE; case/andP=> cycAx; move/eqP => xexpA.
case/andP=> cycAy; move/eqP => yexpA; rewrite groupM //=.
rewrite expMgn; first by rewrite xexpA yexpA mulg1 eqxx.
exact: (centsP abelA).
Qed.

End Exponent.

Section ElementaryAbelian.

Variables (gT : finGroupType) (G : {group gT}) (p : nat).
Hypotheses (primep : prime p) (pgroupG : p.-group(G)).

Lemma abelian_OhmE : forall n, 
  abelian 'Ohm_n(G) -> 'Ohm_n(G) = [set x \in G | x ^+ (p ^ n) == 1].
Proof. 
move=> n abelOhmn; rewrite (OhmE n pgroupG); apply: gen_set_id.
apply/group_setP; split; first by rewrite inE exp1gn eq_refl group1.
move=> x y; rewrite !inE; case/andP=> Gx; move/eqP => xexpeq.
case/andP=> Gy; move/eqP => yexpeq; rewrite groupM //=.
rewrite expMgn; first by rewrite xexpeq yexpeq mulg1 eq_refl.
apply: (centsP abelOhmn); rewrite (OhmE n pgroupG) (subsetP (subset_gen _)) //.
  by rewrite inE Gx xexpeq eq_refl.
by rewrite inE Gy yexpeq eq_refl.
Qed.

(* strengthens Ohm_abelian *)
Lemma abelian_Ohm1 : abelian 'Ohm_1(G) -> p.-abelem 'Ohm_1(G).
Proof.
move=> abelOhm1; rewrite p_abelemE // abelOhm1 //= abelian_OhmE //.
by apply/exponentP'=> x; rewrite inE expn1; case/andP=> Rx; move/eqP.
Qed.

End ElementaryAbelian.

Lemma order_prime_squared_abelian : 
  forall (gT : finGroupType) (G : {group gT}) (p : nat),
  prime p -> #|G| = (p ^ 2)%N -> abelian G.
Proof.
move=> gT G p primep orderG.
have ord_ZG : #|'Z(G)| %| p^2 by rewrite -orderG cardSg // center_sub.
have normal_ZG := (normal_norm (center_normal G)).
case/(dvdn_pfactor _ _ primep): ord_ZG => m; rewrite leq_eqVlt; case/orP.
  move/eqP => ->; rewrite -orderG => card_ZG.
  suffices Geq : 'Z(G)%G == G by move/eqP: Geq => <-; apply: abelian_center.
  by rewrite [_ == _]eqEcard center_sub card_ZG leqnn.
rewrite ltnS leq_eqVlt; case/orP.
  move/eqP => -> ord_ZG; rewrite center_cyclic_abelian ?abelian_center //.
  rewrite prime_cyclic //= card_quotient // -divgS ?center_sub //. 
  by rewrite orderG ord_ZG expn1 mulnK // prime_gt0.
have pgroupG : p.-group G by rewrite /pgroup orderG pnat_exp pnat_id.
rewrite ltnS leqn0; move/eqP => ->; rewrite expn0; move/eqP.
rewrite -trivg_card1 /=; move/eqP => ZGeq1.
by rewrite (trivg_center_pgroup pgroupG ZGeq1) abelian1.
Qed.

Section Four_Dot_Three.

Variables (gT : finGroupType) (R : {group gT}) (p : nat).
Hypotheses (primep : prime p) (oddp : odd p) (pgroupR : p.-group R).
Hypothesis (hyp : nil_class R <= 2 \/ (nil_class R <= 3 /\ p > 3)).

Lemma four_dot_three : exponent 'Ohm_1(R) %| p /\ 
  (R^`(1) \subset 'Ohm_1(R) -> morphic R (fun x => x ^+ p)).
Proof.
have sRRR_ZR: [~: R, R, R] \subset 'Z(R).
  by rewrite -nil_class3; case: (hyp); case => //; move/leq_trans; apply.
have RRRcom: forall x y z w, 
  x \in R -> y \in R -> z \in R -> w \in R -> commute [~ x, y, z] w.
  move=> x y z w Rx Ry Rz Rw; apply: commute_sym; apply: (centerC Rw). 
  by rewrite (subsetP sRRR_ZR) // !mem_commg.
have eq42: forall u w n, u \in R -> w \in R -> 
  [~ u ^+ n, w] = [~ u, w] ^+ n * [~ u, w, u] ^+ bin n 2.
  move=> u w; elim=> [|n ih] Ru Rw; first by rewrite !expg0 comm1g mulg1.
  rewrite expgS commMgR commgX; last first. 
    by apply: (centerC Ru); rewrite (subsetP sRRR_ZR) ?mem_commg //.
  rewrite ih //; rewrite mulgA -(mulgA [~ _ , _]).
  rewrite (commute_sym (commuteX n _)); last first.
    by apply: commute_sym; apply RRRcom; rewrite // groupX ?groupR //.
  by rewrite mulgA -expgS -mulgA -expgn_add binS bin1 addnC.
pose f n := bin n 3; pose g n := 2 * bin n 3 + bin n 2.
have fS : forall n, f (n.+1) = bin n 2 + f n.
  by move=> n; rewrite /f binS //= addnC. 
have gS : forall n, g (n.+1) = 2 * bin n 2 + bin n 1 + g n.
  move=> n; rewrite /g !binS !muln_addr (addnC (2 * _)%N).
  by rewrite (addnC (bin n 2)) 2!addnA (addnAC (2 * _)%N).
have pdivbin2: p %| bin p 2.
  apply: prime_dvd_bin; rewrite //= ltn_neqAle prime_gt1 // andbT.
  by apply/eqP=> peq; move: peq oddp => <-.
have pdivfp : p > 3 -> p %| f p.
  by move => pgt3; apply: prime_dvd_bin.
have pdivgp : p > 3 -> p %| g p.
  by move=> pgt3; rewrite dvdn_add // dvdn_mull // pdivfp.
have nilclass2 : nil_class R <= 2 -> forall u v w, u \in R -> v \in R -> 
  w \in R -> [~ u, v, w] = 1.
  move=> R1sub u v w Ru Rv Rw. 
  have RRsub: [~: R, R] \subset 'Z(R) by rewrite -nil_class2.
  have uvcomm: forall z, z \in R -> commute z [~ u, v].
    by move=> z Rz; apply: (centerC Rz); rewrite (subsetP RRsub) // mem_commg.
  by rewrite commgEr conjgE uvcomm ?groupV // mulKg mulVg.
have {fS gS} eq44 : forall u v, u \in R -> v \in R -> forall n,
  (u * v) ^+ n = u ^+ n * v ^+ n * [~ v, u] ^+ bin n 2 * 
  [~v, u, u] ^+ f n * [~ v, u, v] ^+ g n.
  move=> u v Ru Rv; elim=> [| n ih]; first by rewrite !expg0 !mulg1.
  rewrite expgSr ih -!mulgA.
  rewrite (commute_sym (commuteX (g n) _)); last first.
    by apply: commute_sym; apply: RRRcom; rewrite // groupM.
  rewrite (mulgA (_ ^+ f n)) (commute_sym (commuteX (f n) _)); last first.
    by apply: commute_sym; apply: RRRcom; rewrite // groupM.
  rewrite !mulgA -(mulgA  _ u) -(mulgA _ _ (u * v)) (commgC _ (u * v)).
  rewrite commXg; last first.
    by apply: commute_sym; apply: RRRcom; rewrite // ?groupR ?groupM.
  rewrite commgMR {6}/commg /conjg (RRRcom v u u v) // mulKg mulVg mulg1.
  rewrite expMgn; last by apply: RRRcom; rewrite ?groupR. 
  rewrite !mulgA -(mulgA _ _ (_ ^+ f n)) -expgn_add -fS.
  rewrite -(mulgA _ _ u) (commgC _ u) eq42 // !mulgA -expgSr.
  rewrite -(mulgA _ _ v) [_ * v](commute_sym (commuteX _ _)); last first.
    by rewrite /commute RRRcom.
  rewrite !mulgA -(mulgA _ _ v) (commgC _ v).
  rewrite 2!mulgA -(mulgA _ _ v) -(expgSr v).
  rewrite commXg; last by rewrite /commute RRRcom ?groupR.
  rewrite -(mulgA _ (_ ^+ n) (_ ^+ bin n 2)) -expgn_add.
  rewrite -(mulgA _ _ ([~ v, u] ^+ _)) [_ ^+ (_ + _) * _]commuteX; last first. 
    apply: commute_sym; apply: commuteX; apply: commute_sym.
    by apply: RRRcom; rewrite // groupR.
  rewrite !mulgA -(mulgA _ _ ([~ v, u] ^+ _)) -expgn_add binS bin1 addnC.
  rewrite -(mulgA _ _ (_ ^+ bin n 2)) -expgn_add.
  rewrite -(mulgA _ _ (_ ^+ f n.+1)) (commuteX (f n.+1)); last first.
    by rewrite /commute RRRcom // groupX // !groupR.
  rewrite !mulgA -(mulgA _ _ (_ ^+ g n)) -expgn_add gS bin1.
  by rewrite -[(2 * _)%N]/((1 + 1) * _)%N muln_addl mul1n (addnAC (bin n 2)).
have expOhm : exponent 'Ohm_1(R) %| p.
  move: {-2 4}R (ltnSn #|R|) (subxx R).
  elim: (#|_|.+1) => [| n ih] R'; first by rewrite ltn0.
  move=> R'lt sR'R; rewrite (OhmE 1 (pgroupS sR'R pgroupR)). 
  apply/exponentP; rewrite /= gen_set_id expn1 => [x|].
    by rewrite inE; case/andP=> _; move/eqP. 
  apply/group_setP; rewrite !inE; split; first by rewrite group1 exp1gn eqxx. 
  move=> x y; rewrite !inE; case/andP=> R'x; case/eqP=> xp1; 
  case/andP=> R'y; case/eqP=> yp1.
  rewrite groupM //=; apply/eqP; case genxy: (y \in <[x]>).
    rewrite expMgn; first by rewrite xp1 yp1 mulg1.
    apply: commute_sym; apply/cent1P.
    move: (cycle_abelian x); rewrite abelianE cent_gen cent_set1=> genxsubCx.
    exact: (subsetP genxsubCx).
  have genxsubR' : <[ x ]> \subset R' by rewrite gen_subG sub1set.
  case: (maximal_exists genxsubR').
    move/setP; move/(_ y); rewrite genxy R'y //=.
  case=> S maxS genXsubS.
  have pgroupR' := (pgroupS sR'R pgroupR).
  have cardSR' := (proper_card (maxgroupp maxS)).
  have sSR' := (proper_sub (maxgroupp maxS)).
  have pgroupS := (pgroupS sSR' pgroupR').
  move: (leq_ltn_trans cardSR' R'lt); rewrite ltnS=> cardSn.
  move/exponentP: (ih _ cardSn (subset_trans sSR' sR'R)) => expS.
  have normSR' := (p_maximal_normal pgroupR' maxS).
  have {normSR'} normOR' := 
    normal_norm (char_normal_trans (Ohm_char 1 S) normSR').
  have Ox : x \in 'Ohm_1(S).
    rewrite (OhmE 1 pgroupS) (subsetP (subset_gen _)) // inE.
    rewrite expn1 xp1 eqxx andbT.
    by apply: (subsetP genXsubS); exact: cycle_id.
  have Oyx : [~ y,x] \in 'Ohm_1(S).
    by rewrite commgEr groupM // memJ_norm ?groupV // (subsetP normOR').
  have Oyxx : [~ y, x, x] \in 'Ohm_1(S) by rewrite groupR.
  have Oyxy : [~ y, x, y] \in 'Ohm_1(S).
    by rewrite commgEl groupM // ?groupV // memJ_norm // (subsetP normOR').
  rewrite eq44 ?(subsetP sR'R) // xp1 yp1.
  case/dvdnP: (pdivbin2) => k ->.
  rewrite (mulnC k) expgn_mul (expS _ Oyx) exp1gn !mulg1 mul1g //.
  case: (hyp) => [ncR2 | [_ pg3]].
    by rewrite !(nilclass2 ncR2) ?(subsetP sR'R) // !exp1gn !mulg1.
  case/dvdnP: (pdivfp pg3) => k1 ->.
  rewrite (mulnC k1) expgn_mul (expS _ Oyxx) exp1gn mul1g // => {k1}.
  case/dvdnP: (pdivgp pg3) => k2 ->.
  by rewrite (mulnC k2) expgn_mul (expS _ Oyxy) exp1gn.
split => [| R1subO]; first exact: expOhm. 
have commp : forall u v, u \in R -> v \in R -> [~ u, v]^+ p = 1. 
  move=> u v Ru Rv.
  have Ouv : [~ u, v] \in 'Ohm_1(R).
    by apply: (subsetP R1subO); apply: mem_commg.
  by move/exponentP: expOhm; apply.
apply/morphicP=> x y Rx Ry; rewrite eq44 //. 
case/dvdnP: (pdivbin2) => k ->.
rewrite (mulnC k) expgn_mul commp // exp1gn mulg1.
case: (hyp).
  by move=> ncR2; rewrite !(nilclass2 ncR2) ?(subsetP sR'R) // !exp1gn !mulg1.
case=> _ pg3; case/dvdnP: (pdivfp pg3) => k1 ->.
rewrite (mulnC k1) expgn_mul commp ?groupR // exp1gn mulg1 => {k1}.
case/dvdnP: (pdivgp pg3) => k2 ->.
by rewrite (mulnC k2) expgn_mul commp ?groupR // exp1gn mulg1.
Qed.

End Four_Dot_Three.

Section CentralizerSCNpgroup.

Variables (gT : finGroupType) (R : {group gT}) (p : nat).
Variables  (G A : {group gT}).
Hypotheses (psylGR : p.-Sylow(G) R) (scnA : A \in 'SCN(R)).

(* B & G 4.4b, G 7.6.5 *)
Lemma centralizer_scn_pgroup_eq : 'C_G(A) = 'O_p^'('C_G(A)) \x A.
Proof.
case/and3P: psylGR=> sRG _ _.
case/maxgroupP: (SCN_max scnA); case/andP=> nAG abelA maxA.
case/SCN_P: scnA=> nAR CRA_A.
pose C := 'C_G(A).
have CiP_eq : C :&: R = A by rewrite -CRA_A setIC setIA (setIidPl sRG).
have psylAC : p.-Sylow(C) A.
  rewrite -CiP_eq; apply: (pSylow_normalI (subcent_normal _ _)).
  by apply: pHall_subl psylGR; rewrite ?subsetIl // subsetI sRG normal_norm.
rewrite -{1}(Burnside_normal_complement psylAC) /=; last first.
  by apply: (subset_trans (subsetIl _ _)); apply: subsetIr.
symmetry; apply: dprodEsdprod.
apply: (subset_trans (pcore_sub _ _)); apply: subsetIr.
Qed.

End CentralizerSCNpgroup.

Section OddPrime.

Variables (gT : finGroupType) (p : nat).
Hypotheses (primep : prime p) (oddp : odd p).

Section Four_dot_Five_b.

Variables (R : {group gT}). 
Hypotheses (pgroupR : p.-group R) (ncycR : ~ cyclic R).

Lemma four_dot_five_b : forall x, 
  x \in R -> #|R : <[x]>| = p -> ('Ohm_1(R))%G \in 'E_p^2(R).
Proof.
move=> x Rx indexRX.
have p_ge3: p >= 3.
  move: (prime_gt1 primep); rewrite leq_eqVlt; case/orP => //.
  by move/eqP => p_eq; move: oddp; rewrite -p_eq.
have sXR : <[x]> \subset R by rewrite gen_subG sub1set.
have maxX : maximal <[x]> R by rewrite p_index_maximal // indexRX.
have Xproper : forall K : {group gT}, (* make this a separate lemma? *) 
  <[x]> \proper K -> K \subset R -> K = R.
  move=> K propXK sKR; apply/eqP; rewrite [_ == _]eqEproper sKR /=.
  apply/negP => properKR; move: (propXK); case/maxgroupP: maxX => _.
  move/(_ _ properKR (proper_sub propXK)) => ->. 
  apply: (negP (proper_irrefl _)).
have nXR : <[x]> <| R by rewrite (p_maximal_normal pgroupR).
have xne1 : (x <> 1). 
  move=> xeq1; apply: ncycR; apply: prime_cyclic; move: indexRX.
  by rewrite xeq1 cycle1 indexg1 => ->.
case/p_natP: (mem_p_elt pgroupR Rx)=> e ordx.
have egt0 : e > 0.
  rewrite lt0n; apply/negP; move/eqP=> eeq0.
  by apply: xne1; apply/eqP; rewrite -order_eq1 ordx eeq0 expn0.
have p_dvdn_ordx : p %| #[x] by rewrite ordx dvdn_exp ?dvdnn //.
have propXR : <[x]> \proper R.
  rewrite properEneq sXR andbT; apply/negP; case/eqP=> cardeq.
  by move: indexRX primep; rewrite cardeq indexgg => <-; move/prime_gt1.
case/properP: propXR => _ [y Ry ncycxy].
have Req : R = << [set x; y] >>%G.
  symmetry; apply: (Xproper _); last first.
    rewrite gen_subG; apply/subsetP=> w; rewrite !inE.
    case/orP; move/eqP => -> //.
  apply/properP; rewrite gen_subG sub1set mem_gen ?set21 //; split => //.
  by exists y; rewrite // mem_gen ?set22.
have sR_NX : R \subset 'N(<[x]>) by apply: normal_norm nXR.
have Xyp : y ^+ p \in <[x]>.
  rewrite coset_idr ?(subsetP sR_NX) ?groupX // morphX ?(subsetP sR_NX) //=.
  apply: (exponentP (R / <[x]>)); last by apply: mem_quotient.
  by rewrite (dvdn_trans (exponent_dvdn _)) // card_quotient // indexRX.
have Xxy : x^y \in <[x]> by rewrite memJ_norm ?cycle_id // (subsetP sR_NX). 
case/cycleP: Xxy => l l_def.
have lgt0 : l > 0.
  rewrite lt0n; apply/negP; move/eqP => leq0; apply: xne1.
  by apply: (conjg_inj y); rewrite l_def leq0 expg0 conj1g.
have xypx : x^(y^+p)=x. 
  apply/conjg_fixP; apply/commgP. 
  by apply: (centsP (cycle_abelian x)); rewrite ?cycle_id.
have ordx_dvdn_lp1 : #[x] %| (l^p).-1.
  rewrite order_dvdn; rewrite -(mulg1 (x ^+ _)) -{1}(mulgV x) mulgA.
  rewrite -{2}(expg1 x) -expgn_add addn1 prednK ?expn_gt0 ?lgt0 // -eq_mulgV1.
  rewrite -{2}xypx; elim: p => [|n]; first by rewrite expn0 expg0 expg1 conjg1.
  by rewrite expgS conjgM l_def conjXg expnSr expgn_mul; move/eqP => ->.
have lp_gt0 : l^p > 0 by rewrite expn_gt0 lgt0. 
have lp_modn : l^p = 1 %[mod p].
  by apply/eqP; rewrite eqn_mod_dvd // subn1 (dvdn_trans p_dvdn_ordx).
have coprimelp : coprime l p.
  rewrite coprime_sym prime_coprime //; apply/negP => pdvdnl.
  have pdvdnlp: p %| l ^ p by rewrite euclid_exp // pdvdnl prime_gt0.
  move: pdvdnlp lp_modn; rewrite /dvdn; move/eqP => ->; rewrite modn_small //.
  exact: prime_gt1.
have lp1_modn : l^(p.-1) = 1 %[mod p].
  by rewrite -(@Euler l p) // -{3}(expn1 p) phi_pfactor //= expn0 muln1.
have l_modn : l = 1 %[mod p].
  transitivity (l^p %% p) => //; rewrite -{2}(prednK (prime_gt0 primep)) expnS.
  by rewrite  -modn_mulmr lp1_modn modn_mulmr muln1.
pose k := l %/ p; have l_eq : l = k * p + 1.
  by rewrite {1}(divn_eq l p) l_modn modn_small // prime_gt1.

(* Here is one way of showing that one can write l = k * p^2 * (1 + u) for
   some u. It does not seem any easier than the alternative below, which was
   my original approach. The difficulty is in manipulating ordinal sums. 
   Is there a better way? *)
pose f i := \sum_(j < i) bin i j * (k * p) ^ (i - j).
have sumli : \sum_(i < p) l^i = p + \sum_(i < p) f i.
  transitivity (\sum_(i < p) (1 + f i)). 
    apply: eq_bigr => i _; rewrite l_eq Pascal big_ord_recr /= binn subnn exp1n.
    rewrite expn0 muln1 addnC; congr (fun n => 1 + n); apply: eq_bigr => j _.
    by rewrite exp1n muln1.
  by rewrite big_split /= sum1_card card_ord.
(* this is painful!! *)
pose g i := \sum_(j < i) bin i.+1 j * (k * p) ^ (i.+1 - j).
have temp : \sum_(i < p) f i = (k * p * \sum_(i < p) i) + \sum_(i < p.-1) g i.
  case: {-6}p; first by rewrite !big_ord0 !muln0 addn0. 
  elim; first by rewrite !big_ord_recr /f !big_ord0 /= !muln0 addn0.  
  move=> n ih; rewrite big_ord_recr ih (big_ord_recr n.+1) /=.
  rewrite muln_addr (addnAC _ _ (\sum_(i < n.+1) g i)).
  rewrite [\sum_(i < n.+1) g i]big_ord_recr -!addnA; do 2 congr addn. 
  by rewrite /f big_ord_recr /= binSn subSnn expn1 (mulnC n.+1). 
have p2div : p^2 %| \sum_(i < p) f i.
  rewrite temp{temp} dvdn_addr.
    apply: dvdn_sum => i _; rewrite /g; apply: dvdn_sum => j _. 
    rewrite expn_mull mulnA; apply: dvdn_mull.
    rewrite leq_subS; last by rewrite leq_eqVlt (ltn_ord j) orbT.
    rewrite !expnS dvdn_pmul2l ?prime_gt0 //.
    have ij : 0 < i - j by rewrite subn_gt0 ltn_ord.
    by rewrite -(prednK ij) expnS dvdn_pmul2l ?prime_gt0.
  (* what is going on here? *)
  rewrite -(@big_mkord _ _ _ _ (fun _ => true) (fun i => i)).
  rewrite triangular_sum -mulnA dvdn_mull // expnS dvdn_pmul2l ?prime_gt0 //.
  by rewrite expn1 prime_dvd_bin.
case/dvdnP: p2div => u' sumfi_eq; pose u := (p * u')%N.
have lp1_eq : (l^p).-1 = (k * p^2 * (1 + u))%N.
  rewrite -subn1 geometric_sum {1}l_eq addn1 subn1 /= sumli sumfi_eq.
  by rewrite !muln_addr !mulnA muln1 !(mulnAC _ u').
have {sumli sumfi_eq f g temp} pdivu : p %| u by rewrite dvdn_mulr // dvdnn.

(* This was the previous way:
pose u := bin p 2 * k + \sum_(i < p - 2) bin p (3 + i) * k * (k * p) ^ (1 + i).
have lp1_eq : (l^p).-1 = (k * p^2 * (1 + u))%N.
  rewrite -{1}(subnK (prime_gt1 primep)) addn2 l_eq addnC Pascal.
  rewrite !big_ord_recl //= !exp1n !bin0 !mul1n /bump //= addn0 expn1 !mulnA.
  rewrite -addn2 (subnK (prime_gt1 primep)) bin1 -[1+1]/2.
  rewrite muln_addr (mulnC p k) muln1; apply/eqP; rewrite eqn_addl.
  rewrite /u muln_addr (mulnC _ ((bin p 2) * _)%N) (mulnC k p) !mulnA eqn_addl.
  rewrite big_distrr; apply/eqP; apply: eq_bigr => i _ //=.
  rewrite exp1n mul1n !addnA 2!expnS !addn1 add1n (mulnC (p * k * p)%N).
  by rewrite 2!(mulnAC _ _ (p * k * p)%N) !mulnA.
have pdivu : p %| u.
  rewrite dvdn_addl; first by rewrite dvdn_mulr // prime_dvd_bin.
  by apply: dvdn_sum => i _; rewrite dvdn_mull // dvdn_exp // dvdn_mull.
*)

have {ordx_dvdn_lp1} ordx_dvdn_kp2 : #[x] %| k * p^2.
  move: ordx_dvdn_lp1; rewrite lp1_eq mulnC gauss // ordx coprime_pexpl //.
  rewrite prime_coprime //; move: pdivu; rewrite /dvdn -modn_addmr //.
  by move/eqP ->; rewrite addn0 modn_small ?prime_gt1.
have commxy : [~ x, y] = x ^+ (k * p)%N.
  rewrite commgEl l_def invg_expg -expgn_add l_eq addnC -addnA (addnC 1%N).
  by rewrite addn1 prednK ?order_gt0 // expgn_add expg_order mulg1. 
have commxyp : [~ x, y] ^+ p = 1.
  apply/eqP; rewrite commxy -expgn_mul -order_dvdn -mulnA.
  exact: ordx_dvdn_kp2.
have {l_def lgt0 lp_gt0 lp_modn coprimelp lp1_modn l_modn} 
  commute_xpy: commute (x^+p) y.
  move/eqP: (commxyp); rewrite commgEl expMgn; last first.
    rewrite l_def; apply: commuteX; apply: commute_sym; apply: commuteV.
    exact: commute_refl.
  by rewrite expVgn -conjXg mulgA -invMg -eq_mulVg1 eq_sym; move/eqP.
have commute_commxy_x : commute [~ x, y] x. 
  by rewrite commxy; apply: commute_sym; apply: commuteX; apply: commute_refl.
have commute_commxy_y : commute [~ x, y] y. 
  rewrite commxy mulnC expgn_mul; apply: commute_sym; apply: commuteX.
  exact: commute_sym.
case/cycleP: (Xyp) => n n_def.
have p_dvdn_n : p %| n.
  suffices not_coprime_pn : ~~ coprime p n. 
    by rewrite (prime_coprime _ primep) negb_involutive in not_coprime_pn.
  apply/negP=> coprime_pn; apply: ncycR.
  have coprime_ordx : coprime #[x] n by rewrite ordx coprime_pexpl //.  
  move: (expgnK coprime_ordx (cycle_id x)); rewrite /= -n_def -expgn_mul => xeq.
  have Yx : x \in <[y]> by rewrite -xeq mem_cycle.
  apply/cyclicP; exists y; apply/eqP. 
  rewrite eq_sym eqEproper gen_subG sub1set Ry //=; apply/negP => Yprop.
  case/maxgroupP: maxX => _; move/(_ _ Yprop); rewrite gen_subG sub1set /=.
  by move/(_ Yx) => YeqX; move/negP: ncycxy; apply; rewrite -YeqX cycle_id.
case/dvdnP: p_dvdn_n => m n_eq.
case e1 : (e == 1%N).
  rewrite (eqP e1) expn1 /order in ordx.
  have orderR : #|R| = (p ^ 2)%N by rewrite -(LaGrange sXR) /= ordx indexRX.
  have ordery : #[y] = p.
    move: (order_dvdG Ry); rewrite orderR; move/dvdn_pfactor.
    case/(_  primep)=> f; rewrite leq_eqVlt; case/orP.
      rewrite /order; move/eqP => -> ordy; suffices fls : False by [].
      apply: ncycR; apply/cyclicP; exists y; symmetry.
      by apply/eqP; rewrite eqEcard gen_subG sub1set Ry /= orderR ordy.
    rewrite ltnS leq_eqVlt; case/orP; first by move/eqP => ->; rewrite expn1.
    rewrite ltnS leqn0; move/eqP=> ->; rewrite expn0; move/eqP.
    by rewrite order_eq1; move/eqP=> y1; rewrite y1 group1 in ncycxy.
  have commute_xy : commute x y.
    by apply/commgP; rewrite commxy mulnC expgn_mul -ordx expg_order exp1gn.
  have Ohm1_eq : 'Ohm_1(R) = R.
    apply/eqP; rewrite eqEsubset Ohm_sub /= {1}Req gen_subG /=.
    rewrite (OhmE 1 pgroupR); apply/subsetP => w; rewrite !inE expn1.
    case/orP; move/eqP => ->; rewrite mem_gen // inE //.
      by rewrite -ordx expg_order Rx eqxx.
    by rewrite -ordery expg_order Ry eqxx.
  rewrite pnElemE // inE /= Ohm1_eq orderR eqxx andbT.
  rewrite inE Ohm_sub andTb. apply: abelian_Ohm1 => //.
  rewrite Ohm1_eq Req //= abelian_gen // abelianE.
  apply/subsetP => w; rewrite inE.
  case/orP; rewrite inE; move/eqP => ->; apply/centP => z; 
    case/set2P => -> //.  (* a no-no *)
have egt1 : e > 1 by rewrite ltn_neqAle eq_sym e1 //=.
pose cyc1 := <[y * x ^- m]>; pose cyc2 := <[ x ^+ (p ^ e.-1)]>.
pose K := cyc1 <*> cyc2.
have [_ divp] := (primeP primep).
have yxmp : (y * x^-m)^+p = 1.
  have comm1 : commute (x ^+ m) ([~ x, y] ^+ m).
    by apply: commuteX; apply: commute_sym; apply: commuteX; apply: commute_sym.
  rewrite expMg_Rmul ?commVg ?commXg //; first last.
  - by apply: commuteV; apply: commuteX. 
  - apply: commuteV; apply: commuteX; apply: commute_sym; apply: commuteV.
    by apply: commuteX; apply: commute_sym.
  rewrite -expVgn -expgn_mul -n_eq expVgn n_def mulgV mul1g bin2 -divn2.
  rewrite -divn_mulA; last first. 
    by rewrite /dvdn modn2 -subn1 odd_sub ?prime_gt0 ?oddp.
  rewrite expgn_mul expVgn -expgn_mul mulnC expgn_mul commxyp !exp1gn invg1.
  by rewrite exp1gn.
have order_cyc1 : #|cyc1| = p.
  move/eqP: yxmp; rewrite -order_dvdn; move/(divp _); rewrite order_eq1.
  rewrite -eq_mulgV1; case/orP; last by move/eqP => <-.
  by move/eqP=> yeq; rewrite yeq (mem_cycle _ m) in ncycxy.
have order_cyc2_div : #|cyc2| %| p.
  by rewrite order_dvdn -expgn_mul -expnSr prednK // -ordx expg_order.
have {order_cyc2_div} order_cyc2 : #|cyc2| = p.
  move: (divp _ order_cyc2_div). rewrite order_eq1 -order_dvdn ordx.
  rewrite pfactor_dvdn // ?expn_gt0 ?prime_gt0 // pfactorK //.
  by rewrite -{1}(prednK egt0) ltnn /=; move/eqP.
have cyc1Icyc2 : cyc1 :&: cyc2 = 1.
  apply/setP => w; rewrite !inE; apply/andP/eqP => [|->]; last first.
    by rewrite !group1.
  case; case/cycleP=> j ->; case pdvdnj : (p %| j). 
    by case/dvdnP: pdvdnj => jj ->; rewrite mulnC expgn_mul yxmp exp1gn.
  move=> cyc2_yxmj.
  have coprime_cyc1j : coprime #|cyc1| j.
    by rewrite order_cyc1 prime_coprime // pdvdnj.
  have cyc2_yxm : (y * x ^- m) \in cyc2.
    by rewrite -(expgnK coprime_cyc1j (cycle_id _)) groupX.
  have Xyxm : (y * x ^- m) \in <[x]>.
    apply: (subsetP _ _ cyc2_yxm). 
    by rewrite gen_subG sub1set groupX // cycle_id.
  suffices fls: False by [].
  apply: (negP ncycxy); move: Xyxm.
  by rewrite groupMr // groupV groupX ?cycle_id.
have sKOhm1 : K \subset 'Ohm_1(R).
  rewrite gen_subG subUset !gen_subG !sub1set //= (OhmE 1 pgroupR) !mem_gen //.
    rewrite inE groupX //= expn1 -expgn_mul -expnSr prednK //.
    by rewrite -ordx expg_order.
  by rewrite inE groupM ?groupV ?groupX //= expn1 yxmp.
have commute_xym_xpe1: commute (y * x ^- m) (x ^+ (p ^ e.-1)).
  rewrite -(@prednK e.-1); last by rewrite -subn1 subn_gt0 //.
  rewrite expnS expgn_mul. apply: commuteX; apply: commute_sym. 
  by apply: commuteM => //; apply: commuteV; apply: commuteX2.
have cardK : #|K| = (p ^ 2)%N.
  rewrite [K]comm_mulgenE /=.
    by rewrite TI_cardMg // order_cyc1 order_cyc2.
  by apply: centC; apply: cents_cycle.
have sxpZR : <[x^+p]> \subset 'Z(R).
  rewrite gen_subG sub1set; apply/centerP; split; first by rewrite groupX.
  apply/centP; rewrite Req cent_gen //=; apply/centP => w; rewrite !inE. 
  case/orP; case/eqP => -> //.
  by apply: commute_sym; apply: commuteX.
have ordxp : #[x^+p] = (p^e.-1)%N.
  rewrite orderXdiv ordx -{1}[e]prednK // expnSr ?dvdn_mull ?dvdnn //.
  by rewrite mulnK ?prime_gt0.
have nxpR : R \subset 'N(<[x ^+ p]>).
  apply: (subset_trans _ (cent_sub _)); rewrite centsC.
  by apply: (subset_trans sxpZR); apply: subsetIr.
have sxpX : <[x^+p]> \subset <[x]>.
  by rewrite gen_subG sub1set mem_cycle.
have sR'xp : R^`(1) \subset <[x^+p]>.
  apply: der1_min => //.
  apply: (order_prime_squared_abelian primep). 
  rewrite card_quotient // -(LaGrange_index sXR) // indexRX -divgS //=.
  rewrite [#|<[x]>|]ordx [#|_|]ordxp -{1}[e]prednK //.
  by rewrite expnS mulnK // expn_gt0 prime_gt0.
have nil_class2_R : nil_class R <= 2.
  by rewrite nil_class2 (subset_trans sR'xp sxpZR).
have exponent_Ohm1 : exponent 'Ohm_1(R) %| p.
  exact: exponent_Ohm1_class2.
have Ohm1IXsub : 'Ohm_1(R) :&: <[x]> \subset <[ x ^+ (p ^ e.-1) ]>.
  apply/subsetP=> w; rewrite !inE; case/andP.
  move/(exponentP _ _ exponent_Ohm1)=> wp1; case/cycleP => t t_def.
  move: wp1; rewrite t_def -expgn_mul; move/eqP; rewrite -order_dvdn.
  rewrite ordx -{1}[e]prednK // expnSr dvdn_pmul2r ?prime_gt0 //.
  by case/dvdnP => s ->; rewrite -mulnC expgn_mul groupX // cycle_id.
have Ohm1eq : 'Ohm_1(R) = K.
  symmetry; apply/eqP; rewrite eqEcard sKOhm1 /= cardK.
  rewrite -(LaGrangeI _ <[x]>); apply: leq_mul.
    by rewrite -order_cyc2; apply: (subset_leq_card Ohm1IXsub).
  by rewrite -indexRX; apply: subset_leq_card; apply: imsetS; apply: Ohm_sub.
rewrite pnElemE // inE /= Ohm1eq cardK eqxx andbT.
rewrite /pElem inE Ohm_sub //=; apply: abelian_Ohm1 => //.
rewrite Ohm1eq [K]mulgen_idr mulgen_idl mulgenE abelian_gen // abelianE.
apply/subsetP => w; rewrite !inE.
by case/orP; move/eqP => ->; apply/centP => z; rewrite !inE; case/orP;
  move/eqP => ->; rewrite //=.
Qed.

End Four_dot_Five_b.

Section Four_dot_Five_ac.

Variables (R : {group gT}). 
Hypotheses (pgroupR : p.-group R) (ncycR : ~ cyclic R).

Lemma four_dot_five_a : exists S, (S : {group gT}) <| R /\ (S \in 'E_p^2(R)).
Proof.
have ex_nn : exists G, [pred G : {group gT} | (G <| R) && ~~ cyclic G] G.
  by exists R; rewrite /= normal_refl /=; apply/negP.
case: (ex_mingroup ex_nn) => M {ex_nn}; case/mingroupP => /=. 
case/andP=> nMR ncycM minM.
have pgroupM := (pgroupS (normal_sub nMR) (pgroupR)).
case/p_natP: pgroupM => e cardM.
have egt0 : e > 0.
  rewrite lt0n; apply/negP; case/eqP => eeq0; move/negP: ncycM; apply.
  move/eqP: cardM; rewrite eeq0 expn0 -trivg_card1; move/eqP => ->.
  by rewrite cyclic1.
case: (normal_pgroup pgroupR nMR (leq_pred (logn p #|M|))) => N [sNM nNR].
rewrite cardM pfactorK // => cardN.
have cycN : cyclic N.
  rewrite [cyclic N]negb_involutive_reverse; apply/negP => ncycN.
  have temp : (N <| R) && ~~ cyclic N by rewrite nNR //=.
  move: cardN; rewrite (minM N temp sNM) cardM; move/eqP. 
  by rewrite eqn_exp2l ?prime_gt1 // -{1}(prednK egt0) eqn_leq ltnn.
exists ('Ohm_1(M))%G; split.
  exact: (char_normal_trans (Ohm_char 1 M) nMR).
case/cyclicP: cycN=> x Neq.
have Mx : x \in M by apply: (subsetP sNM); rewrite Neq cycle_id.
have indexMx : #|M : <[x]>| = p.
  rewrite -divgS ?gen_subG ?sub1set //= cardM -Neq cardN -{1}(prednK egt0).
  by rewrite expnS mulnK // expn_gt0 prime_gt0 //.
have pgroupM := (pgroupS (normal_sub nMR) pgroupR).
move: (four_dot_five_b pgroupM (negP ncycM) Mx indexMx).
rewrite !pnElemE // !inE; case/andP; case/andP=> Ohm1sub pabelem ordeq.
by rewrite ordeq pabelem !andbT // (subset_trans Ohm1sub) // normal_sub.
Qed.

Let Z := 'Ohm_1('Z_2(R)).

(* Using 'E_p^2(_) requires a lot of unpacking. Get rid of it? *)

Lemma four_dot_five_c : ~ cyclic Z /\ exponent Z %| p.
Proof. 
case: (four_dot_five_a) => S [nSR]; rewrite pnElemE // !inE p_abelemE //.
case/andP; case/and3P=> sSR abelS expS cardS.
have nilpotentR := (pgroup_nil pgroupR).
set SR := [~: S, R]; set SRR := [~: S, R, R].
have sSR_S : SR \subset S by rewrite commg_subl normal_norm.
have sSRR_SR : SRR \subset SR by rewrite commSg.
have sSR_R := subset_trans sSR_S sSR.
(* shouldn't this be a separate lemma for nilpotent groups? *) 
have pSR_S : SR \proper S.
  rewrite properE sSR_S //=; apply/negP=> sS_SR.
  move: (forallP nilpotentR S); rewrite subsetI sSR sS_SR /=.
  move/eqP=> seq; move: cardS; rewrite seq cards1 eq_sym eqn_mul1 andbb.
  by move/eqP=> peq; move: (prime_gt1 primep); rewrite peq.
have SRR1 : SRR = 1.
  case SR1 : (SR == 1); first by rewrite /SRR [[~: S, R]](eqP SR1) comm1G.
  have pgroupSR := (pgroupS (subset_trans sSR_S sSR) pgroupR).
  have pSRRSR : [~: S, R, R] \proper [~: S, R]. 
    rewrite properE sSRR_SR /=; apply/negP=> sSR_SSR.
    move: (forallP nilpotentR [~: S, R]%G).
    by rewrite subsetI sSR_SSR SR1 sSR_R. 
  have pgroupSRR := (pgroupS sSRR_SR pgroupSR).
  case/p_natP: pgroupSR => e cardSR; case/p_natP: pgroupSRR => f cardSRR.
  have ele1 : e <= 1. 
    rewrite -ltnS -(ltn_exp2l e 2 (prime_gt1 primep)) -(eqP cardS) -cardSR.
    by rewrite proper_card.
  apply/eqP; rewrite trivg_card1 cardSRR -(expn0 p) eqn_exp2l ?prime_gt1 //.
  rewrite -leqn0 -ltnS (leq_trans _ ele1) //.
  by rewrite -(ltn_exp2l f e (prime_gt1 primep)) -cardSRR -cardSR proper_card.
have sSR_ZR : [~: S, R] \subset 'Z(R).
  by rewrite subsetI sSR_R /=; apply/commG1P.
have sS_Z2R : S \subset 'Z_2(R).
  rewrite ucnSnR; apply/subsetP=> s Ss; rewrite inE (subsetP sSR) //= ucn1.
  apply: (subset_trans _ sSR_ZR); apply: (subset_trans _ (subset_gen _)).
  by rewrite -imset2_set1l imset2S // sub1set.
have sZ2R_R := (ucn_sub0 R 2).
have pgroup_Z2R := (pgroupS (ucn_sub0 R 2) pgroupR).
have pgroupZ : p.-group Z. 
  apply: (pgroupS _ pgroupR); apply: (subset_trans (Ohm_sub _ _)).
  exact: ucn_sub0 R 2.
have sSZ : S \subset Z.
  rewrite /Z (OhmE 1 pgroup_Z2R) (subset_trans _ (subset_gen _)) //.
  apply/subsetP=> s Ss; rewrite inE (subsetP sS_Z2R) //= expn1.
  by rewrite (exponentP _ _ expS).
have ncycX : ~ cyclic S.
  case/cyclicP=> x Seq.
  have ordx : #[x] = (p^2)%N by rewrite /order -Seq (eqP cardS).
  have Sx : x \in S by rewrite Seq cycle_id.
  move: (exponentP _ _ expS x Sx); move/eqP; rewrite -order_dvdn ordx. 
  by rewrite pfactor_dvdn ?prime_gt0 // -{2}(expn1 p) pfactorK.
split; first by move=> cycZ; apply: ncycX; apply: (cyclicS sSZ).
(* should this be proved for arbitrary n? *)
have nilclassZ : nil_class 'Z_2(R) <= 2.
  rewrite nil_class2 subsetI der_sub0 /= (subset_trans (commgS _ sZ2R_R)) //.
  by apply: (subset_trans (ucn_comm _ _)); rewrite ucn1 subIset // centS ?orbT.
by move: (four_dot_three primep oddp pgroup_Z2R); case; [apply: or_introl |].
Qed.

End Four_dot_Five_ac.

Section Four_dot_Six.

Variables (R S : {group gT}). 
Hypotheses (pgroupR : p.-group R) (nSR : S <| R) (ncycS : ~ cyclic S).

Lemma four_dot_six : exists H, (H : {group gT}) <| R /\ H \in 'E_p^2(R).
Proof.
pose Z := 'Ohm_1('Z_2(S)).
have nZR := (char_normal_trans (char_trans (Ohm_char 1 _) (ucn_char S 2)) nSR).
have pZ := (pgroupS (normal_sub nZR) pgroupR).
have pS := (pgroupS (normal_sub nSR) pgroupR).
case: (four_dot_five_c pS ncycS) => ncycZ expZ; case/p_natP: pZ => e cardZ.
have ege2 : 2 <= e.
  rewrite ltnNge leq_eqVlt ltnS leq_eqVlt ltn0 orbF. 
  apply/negP; case/orP; case/eqP => e_eq; apply: ncycZ; move: cardZ.
    by rewrite e_eq expn1 => cardZ; apply: prime_cyclic; rewrite cardZ.
  by rewrite e_eq expn0; move/(card1_trivg)=> ->; apply: cyclic1.
have lognpZ : 2 <= logn p #|Z| by rewrite cardZ pfactorK.
case: (normal_pgroup pgroupR nZR lognpZ) => H [sHZ nHR cardH].
exists H; split; first done.
rewrite pnElemE // inE cardH eqxx andbT inE (normal_sub nHR) /=.
rewrite p_abelemE // (order_prime_squared_abelian primep) //=.
by apply: (dvdn_trans _ expZ); apply: exponentS.
Qed.

End Four_dot_Six.

End OddPrime.

Lemma astabsQR_point : 
  forall (gT : finGroupType) (A H : {set gT}) (G : {group gT}),
    H \subset 'N(G) -> A \subset 'N(G) -> 
    'C_H(A / G | 'Q) = H :&: \bigcap_(a \in A) [set g | [~ g, a] \in G].
Proof. 
move=> gt A H G sH_NG sA_NG.
apply/setP=> x.
case Hx : (x \in H); last by rewrite !inE Hx //=.
rewrite inE Hx //= -sub1set astabsQR ?sub1set ?(subsetP sH_NG) //.
rewrite inE Hx //= gen_subG /commg_set imset2_set1l.
apply/subsetP/bigcapP.
  by move=> hyp i Ai; rewrite inE; apply: hyp; apply: mem_imset.
by move=> hyp j; case/imsetP => i Ai ->; move: (hyp i Ai); rewrite inE.
Qed.

Section Twenty_Three_dot_Fifteen. (* in Aschbacher *)

Variables (gT : finGroupType) (G A : {group gT}).
Hypothesis (SCN_A : A \in 'SCN(G)).

Let Z := 'Ohm_1(A).

Lemma twenty_three_fifteen_one : ('C_G(A / Z | 'Q) :&: 'C(Z))^`(1) \subset A.
Proof.
case/SCN_P: SCN_A=> nAG CGAeq.
have sGNA := (normal_norm nAG).
have sZA := (Ohm_sub 1 A).
have nZG : Z <| G by apply: (char_normal_trans (Ohm_char 1 _) nAG).
have sGNZ := (normal_norm nZG).
have sANZ := (subset_trans (normal_sub nAG) sGNZ).
have sACA : A \subset 'C(A) by rewrite -abelianE; apply: (SCN_abelian SCN_A).
rewrite -{4}CGAeq subsetI; apply/andP; split.
  by apply: (subset_trans (der_sub0 _ _)); rewrite subIset // subsetIl.
rewrite gen_subG; apply/subsetP=> w; case/imset2P=> u v.
rewrite astabsQR_point // !inE.
case/andP; case/andP=> Gu; move/bigcapP=> temp; move/centP=> centuZ.
have {temp}Zcommgu : forall a, a \in A -> [~ u, a] \in Z.
  by move=> a Aa; move: (temp a Aa); rewrite inE.
case/andP; case/andP=> Gv; move/bigcapP=> temp; move/centP=> centvZ ->.
have {temp}Zcommgv : forall a, a \in A -> [~ v, a] \in Z. 
  by move=> a Aa; move: (temp a Aa); rewrite inE.
apply/centP=> a Aa; symmetry; rewrite mulgA [a * _]commgC /conjg 2!mulgA.
have NZu : u \in 'N(Z) by apply: (subsetP sGNZ u Gu).
have Zauinv : [~ a, u^-1] \in Z.
  rewrite -(memJ_norm _ NZu); move: (Zcommgu a Aa).
  by rewrite /conjg /commg !mulgA invgK mulgKV.
rewrite -(mulgA _ _ v^-1) (commuteV (commute_sym (centvZ _ Zauinv))).
rewrite !mulgA invgK mulgKV -(mulgA _ _ v^-1) [a * _]commgC 2!mulgA.
have NZv : v \in 'N(Z) by apply: (subsetP sGNZ v Gv).
have Zavinv : [~ a, v^-1] \in Z.
  rewrite -(memJ_norm _ NZv); move: (Zcommgv a Aa).
  by rewrite /conjg /commg !mulgA invgK mulgKV.
rewrite -(mulgA _ _ a^-1) (centsP sACA _ (subsetP sZA _ Zavinv)) ?groupV //. 
rewrite mulgA mulgK -(mulgA _ _ u) -(centuZ _ Zavinv) mulgA -(mulgA _ _ a).
rewrite (centsP sACA _ (subsetP sZA _ Zavinv)) // /commg /conjg !mulgA.
by rewrite mulgK mulgKV invgK.
Qed.

Variable (p : nat).
Hypotheses (oddp : odd p) (primep : prime p) (pgroupG : p.-group G).

Lemma twenty_three_fifteen_two : 'Ohm_1('C_G(Z)) \subset 'C_G(A / Z | 'Q).
Proof.
(* copied from above! how to share them? *)
case/SCN_P: SCN_A=> nAG CGAeq.
have sGNA := (normal_norm nAG).
have sZA := (Ohm_sub 1 A).
have nZG : Z <| G by apply: (char_normal_trans (Ohm_char 1 _) nAG).
have sGNZ := (normal_norm nZG).
have sANZ := (subset_trans (normal_sub nAG) sGNZ).
have sACA : A \subset 'C(A) by rewrite -abelianE; apply: (SCN_abelian SCN_A).

have sCGZ_G := (subsetIl G ('C(Z))); have pgroupCGZ := (pgroupS sCGZ_G pgroupG).
rewrite (OhmE 1 pgroupCGZ) gen_subG expn1; apply/subsetP=> x; rewrite 2!inE /=.
case/andP; case/andP=> Gx CZx xpeq1.
pose CA_XZ := 'C_A(<[x]> / Z | 'Q). 
have CA_XZ_eq : CA_XZ = A :&: \bigcap_(y \in <[x]>) [set g | [~ g, y] \in Z].
  by rewrite /CA_XZ astabsQR_point // ?gen_subG ?sub1set ?(subsetP sGNZ).
have sX_NCAXZ : <[x]> \subset 'N(CA_XZ).
  rewrite gen_subG sub1set /= inE CA_XZ_eq conjIg (normP (subsetP sGNA _ Gx)).
  apply/subsetP=> w; rewrite !inE; case Aw : (w \in A) => //=.
  rewrite mem_conjg; move/bigcapP=> hyp; apply/bigcapP=> x' Xx'; rewrite inE.
  move: (hyp (x'^(x^-1))); rewrite groupJ ?groupV ?cycle_id //.
  by move/implyP; rewrite /= inE -conjRg memJ_norm ?groupV ?(subsetP sGNZ).
pose Y := <[x]> <*> CA_XZ.
have pgroupY : p.-group Y.
  apply: (pgroupS _ pgroupG); rewrite mulgen_subG gen_subG sub1set Gx /=.
  by apply: (subset_trans (subsetIl _ _) (normal_sub nAG)).
have Yeq : Y = <[x]> * 'C_A(<[x]> / Z | 'Q) by apply: norm_mulgenEl.
have sY1_Z : Y^`(1) \subset Z.
  rewrite gen_subG; apply/subsetP=> w; case/imset2P=> u v.
  rewrite Yeq ['C__(_|_)]CA_XZ_eq.
  case/imset2P=> x' a; case/cycleP=> i ->{x'}; case/setIP=> Aa.
  move/bigcapP=> commaX ->{u}.
  case/imset2P=> x' b; case/cycleP=> j ->{x'}; case/setIP=> Ab.
  move/bigcapP=> commbX ->{v} ->; rewrite commMgJ !commgMJ.
  rewrite commXXg ?commgg // exp1gn conj1g mulg1.
  move/commgP: (centsP sACA a Aa b Ab); move/eqP=> temp; rewrite temp{temp}.
  rewrite mul1g groupM // memJ_norm ?(subsetP sANZ) //; last first.
    by move: (commaX (x^+j)); rewrite mem_cycle inE; move/implyP.
  rewrite -groupV invg_comm.
  by move: (commbX (x^+i)); rewrite mem_cycle inE; move/implyP.
have {sY1_Z}nil_classY : nil_class Y <= 2.
  rewrite nil_class2; apply: (subset_trans sY1_Z); rewrite subsetI.
  apply/andP => //=; split.
    apply: (subset_trans _ (mulgen_subr _ _)).
    rewrite CA_XZ_eq subsetI Ohm_sub /=; apply/subsetP=> z Zz.
    apply/bigcapP=> y; case/cycleP=> i ->{y}; rewrite inE -groupV invg_comm.
    move/commgP: (centP CZx z Zz); move/eqP=> commxz1.
    by rewrite commXg commxz1 // exp1gn group1.
  rewrite centsC mulgenE gen_subG subUset gen_subG sub1set CZx /=.
  apply: (subset_trans (subsetIl _ _)); rewrite centsC.
  exact: (subset_trans (Ohm_sub _ _)).
pose XA := <[x]> <*> A.
have XAeq : XA = <[x]> * A.
  by apply: norm_mulgenEl; rewrite gen_subG sub1set (subsetP sGNA).
have sYXA : Y \subset XA.
  rewrite mulgen_subG mulgen_subl; apply: (subset_trans _ (mulgen_subr _ _)).
  exact: subsetIl.
have pgroupXA : p.-group XA.
  apply: (pgroupS _ pgroupG); rewrite mulgen_subG gen_subG sub1set Gx /=.
  exact: (normal_sub nAG).
have pgroupA := (pgroupS (normal_sub nAG) pgroupG).
have sOY_XA : 'Ohm_1(Y) \subset <[x]> * Z.
  apply/subsetP=> w OYw.
  move: (subsetP sYXA _ (subsetP (Ohm_sub _ _) _ OYw)) (OYw).
  rewrite XAeq; case/imset2P=> y a; case/cycleP=> i ->{y} Aa ->{OYw w}.
  rewrite groupMl; last first.
    rewrite groupX //= (OhmE _ pgroupY) mem_gen // inE expn1 xpeq1 andbT.
    by apply: (subsetP (mulgen_subl _ _)); apply: cycle_id.
  pose expOY := (exponentP _ _ (exponent_Ohm1_class2 oddp pgroupY nil_classY)).
  move/(expOY _)=> apeq; apply: mem_imset2; first exact: mem_cycle.
  by rewrite [Z](OhmE 1 pgroupA) mem_gen // inE Aa expn1 apeq eq_refl.
have sNXAY_NXAOY : 'N_XA(Y) \subset 'N_XA('Ohm_1(Y)).
  rewrite subsetI subsetIl /=.
  apply: (subset_trans (normal_norm (normalSG sYXA))); apply normal_norm.
  by apply: (char_normal_trans (Ohm_char _ _)); apply: normalG.
have XAeqY : XA = Y.
  apply: (nilpotent_sub_norm (pgroup_nil pgroupXA)).
    rewrite mulgen_subG mulgen_subl; apply: (subset_trans _ (mulgen_subr _ _)).
    exact: subsetIl.
  apply: (subset_trans sNXAY_NXAOY).
  apply/subsetP=> w; case/setIP; rewrite XAeq; case/imset2P=> y a.
  case/cycleP=> i ->{y} Aa -> NOYxi; rewrite /= [_ <*> _]Yeq.
  rewrite mem_imset2 // ?mem_cycle //.
  have OYx : x \in 'Ohm_1(Y).
    rewrite (OhmE 1 pgroupY); apply: (subsetP (subset_gen _)).
    by rewrite inE expn1 (subsetP (mulgen_subl _ _)) //= cycle_id.
  move: (OYx); rewrite -(memJ_norm _ NOYxi) conjgM {NOYxi}.
  rewrite (conjgE x) (commuteX i (commute_refl x)) mulgA mulVg mul1g.
  move/(subsetP sOY_XA _); case/imset2P=> y z; case/cycleP=> j ->{y} Zz xaeq.
  have xjorda : x^+(j ^ #[a]) = x^+j.
    case/p_natP: (mem_p_elt pgroupA Aa) => n ->; rewrite (divn_eq (j^_) p).
    rewrite expgn_add mulnC expgn_mul (eqP xpeq1) exp1gn mul1g.
    rewrite {2}(divn_eq j p) expgn_add mulnC expgn_mul (eqP xpeq1) exp1gn mul1g.
    apply: congr1; elim: n => [|n ih]; first by rewrite expn0 expn1.
    rewrite expnSr expn_mulr -modn_exp ih modn_exp.
    case pdivj : (p %| j).
      case/dvdnP: pdivj=> k ->. rewrite -modn_exp modn_mull. 
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
    have centzA := (centP (subsetP sACA _ (subsetP sZA z Zz))).
    rewrite [z^_]mulgA -centzA ?groupV ?groupX // mulgKV.
    rewrite -mulgA commuteX; last first.
      apply: commuteV; apply: commuteX; apply: commute_sym. 
      by apply: (centP CZx).
    rewrite mulgA groupM // -expMgn ?groupX //.
    pose x1 := x ^ a ^+ n; pose x2 := x ^- (j ^n); rewrite -[x^_](mulgK x2 x1). 
    apply: commuteV; apply: commuteX; apply: commute_sym. 
    apply: commuteM; by [ apply: (centP CZx) | rewrite invgK; apply: commuteX].
  rewrite ['C__(_|_)]CA_XZ_eq inE Aa /=; apply/bigcapP=> y.
  case/cycleP=> k ->{y}; rewrite inE commgEr conjVg conjXg xaeq.
  rewrite expMgn; last first.
    apply: commute_sym; apply: commuteX; apply: commute_sym.
    by apply: (centP CZx).
  rewrite invMg -mulgA groupM ?groupV ?groupX // -expVgn -expMgn.
    by rewrite groupX // (commute_sym _) //; apply: commuteV; apply: commuteX.
  by apply: commute_sym; apply: commuteV; apply: commuteX.
rewrite astabsQR_point // inE Gx /=; apply/bigcapP=> a Aa; rewrite inE.
move: (subsetP (mulgen_subr <[x]> _) _ Aa); rewrite [_ <*> _]XAeqY Yeq.
case/imset2P=> w b; case/cycleP=> j ->{y}.
rewrite astabsQR_point //; last first.
  by apply: (subset_trans _ sGNZ); rewrite gen_subG sub1set.
rewrite inE; case/andP=> Ab; move/bigcapP=> bprop ->; rewrite commgMJ.
rewrite commgXg conj1g mulg1; move: (bprop x (cycle_id x)). 
by rewrite inE -groupV invg_comm.
Qed.

End Twenty_Three_dot_Fifteen.

(*
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
*)

