Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops prime binomial finset ssralg.
Require Import groups morphisms normal automorphism commutators.
Require Import cyclic center pgroups nilpotent sylow maximal gprod hall.
Require Import coprime_act mxrepresentation.

(******************************************************************************)
(* This file contains most of the material in B & G, section 1, including the *)
(* definitions:                                                               *)
(*   stable_factor A H G == H <| G and A centralises G / H (H G : {group gT}) *)
(*   stable_series A s   == A stabilises the series 1%G :: s                  *)
(* This file currently covers B & G 1.6, 1.8-1.12, and 1.14, as well as       *)
(* Aschbacher 23.7 and 24.7. Other results from B & G section 1 should slot   *)
(* in here as well.                                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section BGsection1.

Variable gT : finGroupType.
Implicit Type p : nat.

(* This is B & G, Proposition 1.3. We give a direct proof for now, in lieu of *)
(* applying the (stronger) Proposition 1.2.                                   *)
Lemma cent_sub_Fitting : forall G : {group gT},
  solvable G -> 'C_G('F(G)) \subset 'F(G).
Proof.
move=> G solG; rewrite -quotient_sub1 ?cents_norm ?subsetIr //.
apply/trivgP; apply/eqP; apply/idPn => /=; set Cq := (_ / _).
have [sFG nFG]:= andP (Fitting_normal G).
have nsCq: Cq <| G / 'F(G).
  by rewrite quotient_normal // -{3}(setIidPl nFG) subcent_normal.
case/(solvable_norm_abelem _ nsCq) => [|Mq [sMCq nMGq ntMq]].
  by rewrite morphim_sol // (solvableS (subsetIl _ _)).
case/abelemP=> p p_pr; case/andP=> _ pMq; case/negP: ntMq.
case/(inv_quotientN (Fitting_normal G)): nMGq => M defMq sFM nsMG.
have sMG := normal_sub nsMG; have nFM := subset_trans sMG nFG.
rewrite defMq (sameP eqP trivgP) quotient_sub1 // Fitting_max //.
move: sMCq; rewrite defMq quotientSK //; move/setIidPr.
rewrite -group_modl //= setIAC (setIidPr sMG) => defC.
have [P sylP]:= Sylow_exists p 'C_M('F(G)); have [sPC pP _]:= and3P sylP.
have [sPM sPCF]: P \subset M /\ 'F(G) \subset 'C(P).
  by apply/andP; rewrite centsC -subsetI.
suffices <-: 'F(G) * P = M by rewrite mulg_nil // Fitting_nil (pgroup_nil pP).
apply/eqP; rewrite eqEsubset -{1}defC mulgS //= -quotientSK // -defMq.
rewrite -subset_leqif_card; last by rewrite defMq quotientS.
rewrite -(part_pnat pMq) defMq -defC quotient_mulgr; apply/eqP.
by apply: card_Hall; rewrite morphim_pSylow ?(subset_trans sPM).
Qed.

(* Stronger variant of B & G 1.6(a) *)
Lemma coprimeR_cent_prod : forall A G : {group gT},
    A \subset 'N(G) -> coprime #|[~: G, A]| #|A| -> solvable [~: G, A] ->
  [~: G, A] * 'C_G(A) = G.
Proof.
move=> A G nGA coRA solR.
have nRG: [~: G, A] <| G by rewrite /normal commg_subl nGA commg_norml.
apply/eqP; rewrite eqEsubset mulG_subG commg_subl nGA subsetIl /=.
rewrite -quotientSK ?commg_norml ?coprime_norm_quotient_cent ?commg_normr //=.
by rewrite subsetI subxx quotient_cents2r.
Qed.

(* B & G, Proposition 1.6(a) *)
Lemma coprime_cent_prod : forall A G : {group gT},
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  [~: G, A] * 'C_G(A) = G.
Proof.
move=> A G nGA; have sRG: [~: G, A] \subset G by rewrite commg_subl.
rewrite -(LaGrange sRG) coprime_mull; case/andP=> coRA _; move/(solvableS sRG).
exact: coprimeR_cent_prod.
Qed.

(* B & G, Proposition 1.6(b) *)
Lemma coprime_commGid : forall A G : {group gT},
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  [~: G, A, A] = [~: G, A].
Proof.
move=> A G nGA coGA solG; apply/eqP; rewrite eqEsubset commSg ?commg_subl //=.
have nAC: 'C_G(A) \subset 'N(A) by rewrite subIset ?cent_sub ?orbT.
rewrite -{1}(coprime_cent_prod nGA) // commMG //=; first 1 last.
  by rewrite !normsR // subIset ?normG.
by rewrite (commG1P (subsetIr _ _)) mulg1.
Qed.

(* B & G, Proposition 1.6(c) *)
Lemma coprime_commGG1P : forall A G : {group gT},
    A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  [~: G, A, A] = 1 -> A \subset 'C(G).
Proof.
by move=> A G nGA coGA solG; rewrite centsC coprime_commGid //; move/commG1P.
Qed.

Section AbelianTI.
(* B & G, Proposition 1.6(d) (TI-part only) *)
(* We go with B & G rather than Aschbacher and will derive 1.6(e) from (d), *)
(* rather than the converse, because the derivation of 24.6 from 24.3 in *)
(* Aschbacher requires a separate reduction to p-groups to yield 1.6(d), *)
(* making it altogether longer than the direct Gaschutz-style proof. *)

Import FiniteModule.

Lemma coprime_abel_cent_TI : forall (aT : finGroupType) (A G : {group aT}),
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G -> 'C_[~: G, A](A) = 1.
Proof.
move=> aT A G nGA coGA abG; pose f x := val (\sum_(a \in A) fmod abG x ^@ a)%R.
have fM: {in G &, {morph f : x y / x * y}}.
  move=> x y Gx Gy /=; rewrite -fmvalA -big_split /=; congr (fmval _).
  by apply: eq_bigr => a Aa; rewrite fmodM // actAr.
have nfA: forall x a, a \in A -> f (x ^ a) = f x.
  move=> x a Aa; rewrite {2}/f (reindex_inj (mulgI a)) /=; congr (fmval _).
  apply: eq_big => [b | b Ab]; first by rewrite groupMl.
  by rewrite -!fmodJ ?groupM ?(subsetP nGA) // conjgM.
have kerR: [~: G, A] \subset 'ker (Morphism fM).
  rewrite gen_subG; apply/subsetP=> xa; case/imset2P=> x a Gx Aa -> {xa}.
  have Gxa: x ^ a \in G by rewrite memJ_norm ?(subsetP nGA).
  rewrite commgEl; apply/kerP; rewrite (groupM, morphM) ?(groupV, morphV) //=.
  by rewrite nfA ?mulVg.
apply/trivgP; apply/subsetP=> x; case/setIP=> Rx cAx; apply/set1P.
have Gx: x \in G by apply: subsetP Rx; rewrite commg_subl.
rewrite -(expgnK coGA Gx) (_ : x ^+ _ = 1) ?exp1gn //.
rewrite -(fmodK abG Gx) -fmvalZ -(mker (subsetP kerR x Rx)); congr fmval.
rewrite -GRing.sumr_const; apply: eq_bigr => a Aa.
by rewrite -fmodJ ?(subsetP nGA) // /conjg (centP cAx) // mulKg.
Qed.

End AbelianTI.

(* B & G, Proposition 1.6(d) (direct product) *)
Theorem coprime_abelian_cent_dprod : forall A G : {group gT},
    A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
  [~: G, A] \x 'C_G(A) = G.
Proof.
move=> A G nGA coGA abelG; rewrite dprodE ?coprime_cent_prod ?abelian_sol //.
  by rewrite centsC subIset 1?(subset_trans abelG) // centS // commg_subl.
by apply/trivgP; rewrite /= setICA coprime_abel_cent_TI ?subsetIr.
Qed.

(* B & G, Proposition 1.6(e), which generalises Aschbacher 24.3 *)
Lemma coprime_abelian_faithful_Ohm1 : forall A G : {group gT},
    A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
  A \subset 'C('Ohm_1(G)) -> A \subset 'C(G).
Proof.
move=> A G nGA coGA abG; rewrite centsC => cGAp; rewrite centsC.
case/dprodP: (coprime_abelian_cent_dprod nGA coGA abG) => _ defG _ TI_G.
have sRG: [~: G, A] \subset G by rewrite commg_subl.
rewrite -{}defG -(setIidPl sRG) TI_Ohm1 ?mul1g ?subsetIr //.
by apply/trivgP; rewrite -{}TI_G setIS // subsetI Ohm_sub.
Qed.

(* B & G, Proposition 1.8, Aschbacher 24.1. Note that the coprime      *)
(* assumption is slightly weaker than requiring that A be a p'-group.  *)
Lemma coprime_cent_Phi : forall p (A G : {group gT}),
    p.-group G -> coprime #|G| #|A| -> [~: G, A] \subset 'Phi(G) ->
  A \subset 'C(G).
Proof.
move=> p A G pG coGA sRphi; rewrite centsC; apply/setIidPl.
rewrite -['C_G(A)]genGid; apply: Phi_nongen; apply/eqP.
rewrite eqEsubset mulgen_subG Phi_sub subsetIl -genM_mulgen sub_gen //=.
have [sPhiG nPhiG] := andP (char_normal (Phi_char G)).
have nPhiA: A \subset 'N('Phi(G)).
  by rewrite -commg_subl (subset_trans _ sRphi) ?commSg.
rewrite -quotientSK // coprime_quotient_cent ?(pgroup_sol pG) // subsetI subxx.
by rewrite (sameP commG1P trivgP) /= -morphimR ?quotient_sub1 // comm_subG.
Qed.

Definition stable_factor (A : {set gT}) (H G : {group gT}) :=
  ([~: G, A] \subset H) && (H <| G). (* this orders allows and3P to be used *)

Definition stable_series A s := path (stable_factor A) 1%G s.

(* B & G, Proposition 1.9, base (and most common) case *)
Theorem stable_factor_cent : forall A G H : {group gT},
    A \subset 'C(H) -> stable_factor A H G ->
    coprime #|G| #|A| -> solvable G ->
  A \subset 'C(G).
Proof.
move=> A G H cHA; case/and3P=> sRH sHG nHG coGA solG.
suffices: G \subset 'C_G(A) by rewrite subsetI subxx centsC.
rewrite -(quotientSGK nHG) ?subsetI ?sHG 1?centsC //.
by rewrite coprime_quotient_cent ?cents_norm ?subsetI ?subxx ?quotient_cents2r.
Qed.

(* B & G, Proposition 1.9 *)
Theorem stable_series_cent : forall (A G : {group gT}) s,
   last 1%G s :=: G -> stable_series A s -> coprime #|G| #|A| -> solvable G ->
  A \subset 'C(G).
Proof.
move=> A _ s <-; elim/last_ind: s => /= [| s G IHs]; first by rewrite cents1.
rewrite last_rcons -cats1 /stable_series path_cat /= andbT.
case/andP; move/IHs {IHs}; move: {s}(last _ _) => H IH_H nHGA coGA solG.
have [_ sHG _] := and3P nHGA.
by rewrite (stable_factor_cent _ nHGA) ?IH_H ?(solvableS sHG) ?(coprimeSg sHG).
Qed.

(* Aschbacher, exercise 3.6 (used in proofs of B & G 1.10 and Aschbacher 24.7 *)
Lemma comm_cent_cent_norm : forall A G H : {group gT},
    A \subset 'N(G) -> A \subset 'C(H) -> G \subset 'N(H) ->
  [~: G, A] \subset 'C(H).
Proof.
move=> A G H nGA; move/centsP=> cHA nHG; rewrite commGC gen_subG centsC.
apply/centsP=> x Hx ay; case/imset2P=> a y Aa Gy ->{ay}; red.
rewrite mulgA -[x * _]cHA ?groupV // -!mulgA; congr (_ * _).
rewrite (mulgA x) (conjgC x) (conjgCV y) 3!mulgA; congr (_ * _).
by rewrite -2!mulgA (cHA a) // -mem_conjg (normsP nHG).
Qed.

(* B & G, Proposition 1.10 *)
Theorem coprime_nil_faithful_cent_stab : forall A G : {group gT},
     A \subset 'N(G) -> coprime #|G| #|A| -> nilpotent G ->
  let C := 'C_G(A) in 'C_G(C) \subset C -> A \subset 'C(G).
Proof.
move=> A G nGA coGA nilG C; rewrite subsetI subsetIl centsC /= -/C => cCA.
pose N := 'N_G(C); have sNG: N \subset G by rewrite subsetIl.
have sCG: C \subset G by rewrite subsetIl.
suffices cNA : A \subset 'C(N).
  rewrite centsC (sameP setIidPl eqP) -(nilpotent_sub_norm nilG sCG) //= -/C.
  by rewrite subsetI subsetIl centsC.
have{nilG} solN: solvable N by rewrite(solvableS sNG) ?nilpotent_sol.
rewrite (stable_factor_cent cCA) ?(coprimeSg sNG) /stable_factor //= -/N -/C.
rewrite subcent_normal subsetI (subset_trans (commSg A sNG)) ?commg_subl //=.
rewrite comm_cent_cent_norm 1?centsC ?subsetIr // normsI // !norms_norm //.
by rewrite cents_norm 1?centsC ?subsetIr.
Qed.

(* Aschbacher 24.7 (replaces Gorenstein 5.3.7) *)
Theorem abelian_charsimple_special : forall (p : nat) (A G : {group gT}),
    p.-group G -> coprime #|G| #|A| -> [~: G, A] = G ->
    \bigcup_(H : {group gT} | (H \char G) && abelian H) H \subset 'C(A) ->
  special G /\ 'C_G(A) = 'Z(G).
Proof.
move=> p A G pG coGA defG; move/bigcupsP=> cChaA.
have cZA: 'Z(G) \subset 'C_G(A).
  by rewrite subsetI center_sub cChaA // center_char abelian_center.
have cChaG: forall H : {group gT}, H \char G -> abelian H -> H \subset 'Z(G).
  move=> H chH abH; rewrite subsetI char_sub //= centsC -defG.
  rewrite comm_cent_cent_norm ?(char_norm chH) -?commg_subl ?defG //.
  by rewrite centsC cChaA ?chH.
have cZ2GG: [~: 'Z_2(G), G, G] = 1.
  by apply/commG1P; rewrite (subset_trans (ucn_comm G 1)) // ucn1 subsetIr.
have{cZ2GG} cG'Z: 'Z_2(G) \subset 'C(G^`(1)).
  by rewrite centsC; apply/commG1P; rewrite three_subgroup // (commGC G).
have{cG'Z} sZ2G'_Z: 'Z_2(G) :&: G^`(1) \subset 'Z(G).
  apply: cChaG; first by rewrite charI ?ucn_char ?der_char.
  by rewrite /abelian subIset // (subset_trans cG'Z) // centS ?subsetIr.
have{sZ2G'_Z} sG'Z: G^`(1) \subset 'Z(G).
  rewrite -quotient_sub1; last first.
    by rewrite (subset_trans (der_sub0 G 1)) ?char_norm ?center_char.
  apply/trivgP; have: nilpotent (G / 'Z(G)) := quotient_nil _ (pgroup_nil pG).
  move/nil_TI_Z; apply; first by rewrite quotient_normal ?der_normal.
  apply/trivgP; rewrite /= -ucn1 -ucn_central -quotientIG ?ucn_sub //= ucn1.
  by rewrite setIC quotient_sub1 //= (subset_trans sZ2G'_Z) ?normG.
have sCG': 'C_G(A) \subset G^`(1).
  rewrite -quotient_sub1 //; last by rewrite subIset // char_norm ?der_char.
  rewrite (subset_trans (quotient_subcent _ G A)) //= -{6}defG.
  have nGA: A \subset 'N(G) by rewrite -commg_subl defG.
  rewrite quotientR ?(char_norm_trans (der_char _ _)) ?normG //.
  rewrite coprime_abel_cent_TI ?quotient_norms ?coprime_morph //.
  exact: sub_der1_abelian.
have defZ: 'Z(G) = G^`(1) by apply/eqP; rewrite eqEsubset (subset_trans cZA).
split; last by apply/eqP; rewrite eqEsubset cZA defZ sCG'.
split=> //; apply/eqP; rewrite eqEsubset defZ (Phi_mulgen pG) mulgen_subl.
rewrite mulgen_subG subxx andbT /= -defZ.
have:= pG; rewrite -pnat_exponent; case/p_natP=> n expGpn.
rewrite -(subnn n.-1); elim: {2}n.-1 => [|m IHm].
  rewrite (MhoE _ pG) gen_subG; apply/subsetP=> xp; case/imsetP=> x Gx ->{xp}.
  rewrite subn0 -subn1 -add1n add_sub_maxn maxnC -add_sub_maxn expn_add.
  by rewrite expgn_mul -expGpn (exponentP _ _ (dvdnn _)) ?groupX ?group1.
rewrite cChaG ?Mho_char //= (MhoE _ pG) /abelian cent_gen gen_subG.
apply/centsP=> xp; case/imsetP=> x Gx -> yp; case/imsetP=> y Gy ->{xp yp}.
move: sG'Z; rewrite subsetI centsC; case/andP=> _; move/centsP=> cGG'.
apply/commgP; rewrite {1}expnSr expgn_mul.
rewrite commXg -?commgX; try by apply: cGG'; rewrite ?mem_commg ?groupX.
apply/commgP; rewrite subsetI Mho_sub centsC in IHm; apply: (centsP IHm).
  by rewrite groupX.
rewrite -add1n -(addn1 m) -subn_sub add_sub_maxn maxnC -add_sub_maxn.
rewrite -expgn_mul -expnSr -addSn expn_add expgn_mul groupX //=.
by rewrite (MhoE _ pG) mem_gen //; apply: mem_imset.
Qed.

(* Aschbacher 23.7, should go in maximal ? *)
Lemma center_special_abelem : forall p (G : {group gT}),
  p.-group G -> special G -> p.-abelem 'Z(G).
Proof.
move=> p G pG [defPhi defG']; case: (pgroup_1Vpr pG) => [-> | [p_pr _ _]].
  by rewrite center1 p_abelem1.
have fM: {in 'Z(G) &, {morph expgn^~ p : x y / x * y}}.
  move=> x y; case/setIP=> _ CxG; case/setIP=> Gy _.
  rewrite expMgn //; exact: (centP CxG).
rewrite p_abelemE //= abelian_center; apply/exponentP=> /= z Zz.
apply: (@kerP _ _ _ (Morphism fM)) => //; apply: subsetP z Zz.
rewrite -{1}defG' gen_subG; apply/subsetP=> xy.
case/imset2P=> x y Gx Gy ->{xy}.
have Zxy: [~ x, y] \in 'Z(G) by rewrite -defG' mem_commg.
have Zxp: x ^+ p \in 'Z(G).
  rewrite -defPhi (Phi_mulgen pG) (MhoE 1 pG) mulgen_idr mem_gen // !inE.
  by rewrite expn1 orbC (mem_imset (expgn^~ p)).
rewrite mem_morphpre /= ?defG' ?Zxy // inE -commXg; last first.
  by red; case/setIP: Zxy => _; move/centP->.
by apply/commgP; red; case/setIP: Zxp => _; move/centP->.
Qed.

(* B & G, Theorem 1.11, via Aschbacher 24.8 rather than Gorenstein 5.3.10 *)
Theorem coprime_odd_faithful_Ohm1 : forall p (A G : {group gT}),
    p.-group G -> A \subset 'N(G) -> coprime #|G| #|A| -> odd #|G| ->
  A \subset 'C('Ohm_1(G)) -> A \subset 'C(G).
Proof.
move=> p A G pG nGA coGA oddG; rewrite !(centsC A) => cAG1.
wlog{oddG} [p_pr oddp]: / prime p /\ odd p.
  case/pgroup_1Vpr: pG oddG => [-> | [-> _ [k ->]]]; first by rewrite sub1G.
  by rewrite !odd_2'nat pnat_exp orbF => -> ->.
wlog defR: G pG nGA coGA cAG1 / [~: G, A] = G.
  move=> IH; have solG := pgroup_sol pG.
  rewrite -(coprime_cent_prod nGA) ?mul_subG ?subsetIr //=.
  have sRG: [~: G, A] \subset G by rewrite commg_subl.
  rewrite IH ?coprime_commGid ?(pgroupS sRG) ?commg_normr ?(coprimeSg sRG) //.
  by rewrite (subset_trans (OhmS 1 sRG)).
have [|[defPhi defG'] defC] := abelian_charsimple_special pG coGA defR.
  apply/bigcupsP=> H; case/andP=> chH abH; have sHG := char_sub chH.
  have nHA := char_norm_trans chH nGA.
  rewrite centsC coprime_abelian_faithful_Ohm1 ?(coprimeSg sHG) //.
  by rewrite centsC (subset_trans (OhmS 1 sHG)).
have elemZ: p.-abelem 'Z(G) by exact: center_special_abelem.
have cAZ: {in 'Z(G), centralised A} by apply/centsP; rewrite -defC subsetIr.
have cGZ: {in 'Z(G), centralised G} by apply/centsP; rewrite subsetIr.
have defG1: 'Ohm_1(G) = 'Z(G).
  apply/eqP; rewrite eqEsubset -{1}defC subsetI Ohm_sub cAG1 /=.
  case/andP: elemZ => elemZ; move/pgroup_p=> pZ.
  by rewrite -(abelem_Ohm1P (abelian_center _) pZ elemZ) OhmS ?center_sub.
rewrite (subset_trans _ (subsetIr G _)) // defC -defG1 -{1}defR gen_subG /=.
apply/subsetP=> xa; case/imset2P=> x a Gx Aa ->{xa}; rewrite commgEl.
set u := x^-1; set v := x ^ a; pose w := [~ v, u].
have [Gu Gv]: u \in G /\ v \in G by rewrite groupV memJ_norm ?(subsetP nGA).
have Zw: w \in 'Z(G) by rewrite -defG' mem_commg.
rewrite (OhmE 1 pG) mem_gen // inE expn1 groupM //=.
rewrite expMg_Rmul /commute ?(cGZ w) // bin2odd // expgn_mul.
case/(p_abelemP _ p_pr): elemZ => _; move/(_ w)=> -> //.
rewrite exp1gn mulg1 expVgn -conjXg (sameP commgP eqP) cAZ //.
rewrite -defPhi (Phi_mulgen pG) (MhoE 1 pG) mulgen_idr mem_gen // !inE.
by rewrite orbC expn1 (mem_imset (expgn^~ p)).
Qed.

(* B & G, Corollary 1.12 *)
Corollary coprime_odd_faithful_cent_abelem : forall p (A G E : {group gT}),
    E \in 'E_p(G) -> p.-group G ->
    A \subset 'N(G) -> coprime #|G| #|A| -> odd #|G| ->
  A \subset 'C([set x \in 'C_G(E) | #[x] == p]) -> A \subset 'C(G).
Proof.
move=> p A G E; rewrite inE; case/andP=> sEG elemE pG nGA coGA oddG cCEA.
case: (pgroup_1Vpr pG) => [-> | [p_pr _ _]]; first by rewrite cents1.
have spG: p.-group (G :&: _) := pgroupS (subsetIl _ _) pG.
have{cCEA} cCEA: A \subset 'C('Ohm_1('C_G(E))).
  apply: subset_trans cCEA _; rewrite -cent_gen centS // (OhmE 1 (spG _)).
  rewrite gen_subG; apply/subsetP=> x; case/setIdP=> CEx.
  rewrite expn1 -order_dvdn; case/primeP: p_pr => _ p_pr; move/p_pr.
  rewrite order_eq1; case/predU1P=> [-> | defM]; first exact: group1.
  by rewrite mem_gen // inE CEx.
apply: coprime_nil_faithful_cent_stab (pgroup_nil pG) _ => //.
rewrite subsetI subsetIl centsC /=; set CC := 'C_G(_).
have sCCG: CC \subset G := subsetIl _ _; have pCC := pgroupS sCCG pG.
rewrite (coprime_odd_faithful_Ohm1 pCC) ?(coprimeSg sCCG) ?(oddSg sCCG) //.
  by rewrite !(normsI, norms_cent, normG).
rewrite (subset_trans cCEA) // centS // OhmS // setIS // centS //.
rewrite subsetI sEG /= centsC (subset_trans cCEA) // centS //.
have abelE: abelian E by case/andP: elemE; case/andP.
suffices defE1: 'Ohm_1(E) = E by rewrite -{1}defE1 OhmS // subsetI sEG.
by case/andP: elemE => elemE; move/pgroup_p=> pE; apply/abelem_Ohm1P.
Qed.

Section CoprimeQuotientPgroup.

(* This is B & G, Lemma 1.14, which we divide in four lemmas, each one giving *)
(* the (sub)centraliser or (sub)normaliser of a quotient by a coprime p-group *)
(* acting on it. Note that we weaken the assumptions of B & G -- M does not   *)
(* need to be normal in G, T need not be a subgroup of G, p need not be a     *)
(* prime, and M only needs to be coprime with T. Note also that the subcenter *)
(* quotient lemma is special case of a lemma in coprime_act.                  *)

Variables (p : nat) (T M G : {group gT}).
Hypothesis pT : p.-group T.
Hypotheses (nMT : T \subset 'N(M)) (coMT : coprime #|M| #|T|).

Lemma coprime_norm_quotient_pgroup : 'N(T / M) = 'N(T) / M.
Proof.
case: (pgroup_1Vpr pT) => [-> | [p_pr _ [m oMpm]]].
  by rewrite quotient1 !norm1 -quotientInorm setTI quotientT.
apply/eqP; rewrite eqEsubset morphim_norms // andbT; apply/subsetP=> Mx.
case: (cosetP Mx) => x Nx ->{Mx} nTqMx.
have sylT: p.-Sylow(M <*> T) T.
  rewrite /pHall pT -divgS mulgen_subr //= norm_mulgenEr ?coprime_cardMg //.
  rewrite mulnK // ?p'natE -?prime_coprime // coprime_sym.
  by rewrite -(@coprime_pexpr m.+1) -?oMpm.
have sylTx: p.-Sylow(M <*> T) (T :^ x).
  have nMTx: x \in 'N(M <*> T).
    rewrite norm_mulgenEr // inE -quotientSK ?conj_subG ?mul_subG ?normG //.
    by rewrite quotientJ // quotient_mulgr (normP nTqMx).
  by rewrite pHallE /= -{1}(normP nMTx) conjSg cardJg -pHallE.
have{sylT sylTx} [ay] := Sylow_trans sylT sylTx.
rewrite /= mulgenC norm_mulgenEl //; case/imset2P=> a y Ta.
rewrite -groupV => My ->{ay} defTx; rewrite -(coset_kerr x My).
rewrite mem_morphim //; first by rewrite groupM // (subsetP (normG M)).
by rewrite inE !(conjsgM, defTx) conjsgK conjGid.
Qed.

Lemma coprime_cent_quotient_pgroup : 'C(T / M) = 'C(T) / M.
Proof.
symmetry; rewrite -quotientInorm -quotient_mulgr -['C(T / M)]cosetpreK.
congr (_ / M); set Cq := _ @*^-1 _; set C := 'N__(M).
suff <-: 'N_Cq(T) = C.
  rewrite setIC group_modl ?sub_cosetpre //= -/Cq; apply/setIidPr.
  rewrite -quotientSK ?subsetIl // cosetpreK.
  by rewrite -coprime_norm_quotient_pgroup cent_sub.
apply/eqP; rewrite eqEsubset subsetI -sub_quotient_pre ?subsetIr //.
rewrite quotientInorm quotient_cents //= andbC subIset ?cent_sub //=.
have nMC': 'N_Cq(T) \subset 'N(M) by rewrite subIset ?subsetIl.
rewrite subsetI nMC' andbT (sameP commG1P trivgP) /=.
rewrite -(coprime_TIg coMT) subsetI commg_subr subsetIr andbT.
by rewrite -quotient_cents2 ?sub_quotient_pre ?subsetIl.
Qed.

Hypothesis sMG : M \subset G.

Lemma coprime_subnorm_quotient_pgroup : 'N_(G / M)(T / M) = 'N_G(T) / M.
Proof. by rewrite quotientGI -?coprime_norm_quotient_pgroup. Qed.

Lemma coprime_subcent_quotient_pgroup : 'C_(G / M)(T / M) = 'C_G(T) / M.
Proof. by rewrite quotientGI -?coprime_cent_quotient_pgroup. Qed.

End CoprimeQuotientPgroup.

(* This is B & G, Proposition 1.16, second assertion. Contrary to the text,  *)
(* we derive this directly, rather than by induction on the first, because   *)
(* this is actually how the proof is done in Gorenstein. Note that the non   *)
(* cyclic assumption for A is not needed here.                               *)
Lemma coprime_abelian_gen_cent : forall A G : {group gT},
   abelian A -> A \subset 'N(G) -> coprime #|G| #|A| ->
  G = (\prod_(B : {group gT} | cyclic (A / B) && (B <| A)) 'C_G(B))%G.
Proof.
move=> A G abelA nGA coGA; apply: val_inj; rewrite /= bigprodGE.
move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT => // n IHn aT in A G abelA nGA coGA *; rewrite ltnS => leGn.
without loss nilG: G nGA coGA leGn / nilpotent G.
  move=> {IHn} IHn; apply/eqP; rewrite eqEsubset gen_subG.
  apply/andP; split; last by apply/bigcupsP=> B _; exact: subsetIl.
  pose T := [set P : {group aT} | Sylow G P && (A \subset 'N(P))].
  rewrite -{1}(@Sylow_transversal_gen _ T G) => [|P | p _]; first 1 last.
  - by rewrite inE -!andbA; case/and4P.
  - have [//|P sylP nPA] := sol_coprime_Sylow_exists p (abelian_sol abelA) nGA.
    by exists P; rewrite ?inE ?(p_Sylow sylP).
  rewrite gen_subG; apply/bigcupsP=> P; rewrite {T}inE.
  case/andP; case/SylowP=> p _ sylP nPA; have sPG := pHall_sub sylP.
  rewrite (IHn P) ?(pgroup_nil (pHall_pgroup sylP)) ?(coprimeSg sPG) ?genS //.
    by apply/bigcupsP=> B cycBq; rewrite (bigcup_max B) ?setSI.
  by rewrite (leq_trans (subset_leq_card sPG)).
apply/eqP; rewrite eqEsubset gen_subG.
apply/andP; split; last by apply/bigcupsP=> B _; exact: subsetIl.
case: (eqsVneq 'Z(G) 1) => [Z1 | ntZ].
  by rewrite (nil_TI_Z _ (normal_refl G)) ?Z1 ?(setIidPr _) ?sub1G.
have nZA: A \subset 'N('Z(G)) := char_norm_trans (center_char G) nGA.
have{ntZ nZA} [M /= minM] := minnormal_exists ntZ nZA.
rewrite subsetI centsC; case/andP=> sMG; move/cents_norm=> nMG. 
have coMA := coprimeSg sMG coGA; have{nilG} solG := nilpotent_sol nilG.
have [nMA ntM abelM] := minnormal_solvable minM sMG solG.
set GC := <<_>>; have sMGC: M \subset GC.
  rewrite sub_gen ?(bigcup_max 'C_A(M)%G) //=; last first.
    by rewrite subsetI sMG centsC subsetIr.
  case/abelemP: abelM => p _ abelM; rewrite -(ker_abelem_repr abelM ntM nMA).
  have ker_q_cyc := mx_repr_faithful_irr_abelian_cyclic _ (kquo_mx_faithful _).
  rewrite mx_repr_ker_normal {}ker_q_cyc ?morphim_abelian //.
  by apply/quo_mx_irr=> //; exact/abelem_mx_irrP.
rewrite -(quotientSGK nMG sMGC).
have: A / M \subset 'N(G / M) by rewrite morphim_norms.
move/IHn->; rewrite ?morphim_abelian ?coprime_morph {IHn}//; first 1 last.
  by rewrite (leq_trans _ leGn) ?ltn_quotient.
rewrite gen_subG; apply/bigcupsP=> Bq; rewrite andbC; case/andP.
have: A :&: M = 1 by rewrite setIC coprime_TIg.
move/(quotient_isom nMA); case/isomP=> /=; set qM := restrm _ _ => injqM <-.
move=> nsBqA; have sBqA := normal_sub nsBqA.
rewrite -(morphpreK sBqA) /= -/qM; set B := qM @*^-1 Bq.
move: nsBqA; rewrite -(morphpre_normal sBqA) ?injmK //= -/B => nsBA.
rewrite -(morphim_quotm _ nsBA) /= -/B injm_cyclic ?injm_quotm //= => cycBA.
rewrite morphim_restrm -quotientE morphpreIdom -/B; have sBA := normal_sub nsBA.
rewrite -coprime_quotient_cent ?(coprimegS sBA, subset_trans sBA) //= -/B.
by rewrite quotientS ?sub_gen // (bigcup_max [group of B]) ?cycBA.
Qed.

(* B & G, Proposition 1.16, first assertion. *)
Lemma coprime_abelian_gen_cent1 : forall A G : {group gT},
   abelian A -> ~~ cyclic A -> A \subset 'N(G) -> coprime #|G| #|A| ->
  G = (\prod_(a \in A^#) 'C_G[a])%G.
Proof.
move=> A G abelA ncycA nGA coGA.
apply/eqP; rewrite -val_eqE eqEsubset /= bigprodGE gen_subG.
apply/andP; split; last by apply/bigcupsP=> B _; exact: subsetIl.
rewrite {1}(coprime_abelian_gen_cent abelA nGA) // bigprodGE genS //.
apply/bigcupsP=> B; case: (eqsVneq B 1) => [-> |].
  by rewrite injm_cyclic ?coset1_injm ?norms1 ?(negbTE ncycA).
case/trivgPn=> a Ba n1a; case/and3P=> _ sBA _.
rewrite (bigcup_max a) ?inE ?n1a ?(subsetP sBA) // setIS //=.
by rewrite -cent_set1 centS // sub1set.
Qed.

End BGsection1.
