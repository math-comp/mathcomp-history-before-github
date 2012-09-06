(* (c) Copyright Microsoft Corporation and Inria. All rights reserved.        *)
Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat seq div fintype.
Require Import tuple finfun bigop ssralg finset prime binomial poly polydiv.
Require Import fingroup morphism quotient automorphism action finalg zmodp.
Require Import gproduct cyclic commutator pgroup abelian frobenius BGsection1.
Require Import matrix mxalgebra mxabelem vector falgebra fieldext galois.
Require Import finfield ssrnum algC classfun character integral_char inertia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section AppendixC.

Variables (gT : finGroupType) (p q : nat) (H P P0 U Q : {group gT}).
Let nU := ((p ^ q).-1 %/ p.-1)%N.

(* External statement of the finite field assumption. *)
CoInductive finFieldImage : Prop :=
  FinFieldImage (F : finFieldType) (sigma : {morphism P >-> F}) of
     isom P [set: F] sigma & sigma @*^-1 <[1 : F]> = P0
   & exists2 sigmaU : {morphism U >-> {unit F}},
     'injm sigmaU & {in P & U, morph_act 'J 'U sigma sigmaU}.

(* These correspond to hypothesis (A) of B & G, Appendix C, Theorem C.        *)
Hypotheses (pr_p : prime p) (pr_q : prime q) (coUp1 : coprime nU p.-1).
Hypotheses (defH : P ><| U = H) (fieldH : finFieldImage).
Hypotheses (oP : #|P| = (p ^ q)%N) (oU : #|U| = nU).

(* These correspond to hypothesis (B) of B & G, Appendix C, Theorem C.        *)
Hypotheses (abelQ : q.-abelem Q) (nQP0 : P0 \subset 'N(Q)).
Hypothesis nU_P0Q : exists2 y, y \in Q & P0 :^ y \subset 'N(U).

Section ExpandHypotheses.

(* Negation of the goal of B & G, Appendix C, Theorem C.                      *)
Hypothesis ltqp : (q < p)%N.

(* From the fieldH assumption. *)
Variables (fT : finFieldType) (charFp : p \in [char fT]).
Local Notation F := (PrimeCharType charFp).
Local Notation galF := [splittingFieldType 'F_p of F].
Let Fpq : {vspace F} := fullv.
Let Fp : {vspace F} := 1%VS.

Hypothesis oF : #|F| = (p ^ q)%N.
Let oF_p : #|'F_p| = p. Proof. exact: card_Fp. Qed.
Let oFp : #|Fp| = p. Proof. by rewrite card_vspace1. Qed.
Let oFpq : #|Fpq| = (p ^ q)%N. Proof. by rewrite card_vspacef. Qed.
Let dimFpq : \dim Fpq = q. Proof. by rewrite primeChar_dimf oF pfactorK. Qed.

Variables (sigma : {morphism P >-> F}) (sigmaU : {morphism U >-> {unit F}}).
Hypotheses (inj_sigma : 'injm sigma) (inj_sigmaU : 'injm sigmaU).
Hypothesis im_sigma : sigma @* P = [set: F].
Variable s : gT.
Hypotheses (sP0P : P0 \subset P) (sigma_s : sigma s = 1) (defP0 : <[s]> = P0).

Let psi u : F := val (sigmaU u).
Let inj_psi : {in U &, injective psi}.
Proof. by move=> u v Uu Uv /val_inj/(injmP _ inj_sigmaU)->. Qed.

Hypothesis sigmaJ : {in P & U, forall x u, sigma (x ^ u) = sigma x * psi u}.

Let Ps : s \in P. Proof. by rewrite -cycle_subG defP0. Qed.
Let P0s : s \in P0. Proof. by rewrite -defP0 cycle_id. Qed.

Let nz_psi u : psi u != 0. Proof. by rewrite -unitfE (valP (sigmaU u)). Qed.

Let sigma1 : sigma 1%g = 0. Proof. exact: morph1. Qed.
Let sigmaM : {in P &, {morph sigma : x1 x2 / (x1 * x2)%g >-> x1 + x2}}.
Proof. exact: morphM. Qed.
Let sigmaV : {in P, {morph sigma : x / x^-1%g >-> - x}}.
Proof. exact: morphV. Qed.
Let sigmaX n : {in P, {morph sigma : x / (x ^+ n)%g >-> x *+ n}}.
Proof. exact: morphX. Qed.

Let psi1 : psi 1%g = 1. Proof. by rewrite /psi morph1. Qed.
Let psiM : {in U &, {morph psi : u1 u2 / (u1 * u2)%g >-> u1 * u2}}.
Proof. by move=> u1 u2 Uu1 Uu2; rewrite /psi morphM. Qed.
Let psiV : {in U, {morph psi : u / u^-1%g >-> u^-1}}.
Proof. by move=> u Uu; rewrite /psi morphV. Qed.
Let psiX n : {in U, {morph psi : u / (u ^+ n)%g >-> u ^+ n}}.
Proof. by move=> u Uu; rewrite /psi morphX // val_unitX. Qed.

Let sigmaE := (sigma1, sigma_s, mulr1, mul1r,
               (sigmaJ, sigmaX, sigmaM, sigmaV), (psi1, psiX, psiM, psiV)).

Let psiE u : u \in U -> psi u = sigma (s ^ u).
Proof. by move=> Uu; rewrite !sigmaE. Qed.

Let nPU : U \subset 'N(P). Proof. by have [] := sdprodP defH. Qed.
Let memJ_P : {in P & U, forall x u, x ^ u \in P}.
Proof. by move=> x u Px Uu; rewrite /= memJ_norm ?(subsetP nPU). Qed.
Let in_PU := (memJ_P, in_group).

Let sigmaP0 : sigma @* P0 =i Fp.
Proof.
rewrite -defP0 morphim_cycle // sigma_s => x.
apply/cycleP/vlineP=> [] [n ->]; first by exists n%:R; rewrite scaler_nat.
by exists (val n); rewrite -{1}[n]natr_Zp -in_algE rmorph_nat zmodXgE.
Qed.

Let nt_s : s != 1%g.
Proof. by rewrite -(morph_injm_eq1 inj_sigma) // sigmaE oner_eq0. Qed.

Let p_gt0 : (0 < p)%N. Proof. exact: prime_gt0. Qed.
Let q_gt0 : (0 < q)%N. Proof. exact: prime_gt0. Qed.
Let p1_gt0 : (0 < p.-1)%N. Proof. by rewrite -subn1 subn_gt0 prime_gt1. Qed.

(* This is B & G, Appendix C, Remark I. *)
Let not_dvd_q_p1 : ~~ (q %| p.-1)%N.
Proof.
rewrite -prime_coprime // -[q]card_ord -sum1_card -coprime_modl -modn_summ.
have:= coUp1; rewrite /nU predn_exp mulKn //= -coprime_modl -modn_summ.
congr (coprime (_ %% _) _); apply: eq_bigr => i _.
by rewrite -{1}[p](subnK p_gt0) subn1 -modnXm modnDl modnXm exp1n.
Qed.

(* This is the first assertion of B & G, Appendix C, Remark V. *)
Let odd_p : odd p.
Proof.
by apply: contraLR ltqp => /prime_oddPn-> //; rewrite -leqNgt prime_gt1.
Qed.

(* This is the second assertion of B & G, Appendix C, Remark V. *)
Let odd_q : odd q.
Proof.
apply: contraR not_dvd_q_p1 => /prime_oddPn-> //.
by rewrite -subn1 dvdn2 odd_sub ?odd_p.
Qed.

Let qgt2 : (2 < q)%N. Proof. by rewrite odd_prime_gt2. Qed.
Let pgt4 : (4 < p)%N. Proof. by rewrite odd_geq ?(leq_ltn_trans qgt2). Qed.
Let qgt1 : (1 < q)%N. Proof. exact: ltnW. Qed.

Local Notation Nm := (galNorm Fp Fpq).
Local Notation uval := (@FinRing.uval _).

Let cycFU (FU : {group {unit F}}) : cyclic FU.
Proof. exact: field_unit_group_cyclic. Qed.
Let cUU : abelian U.
Proof. by rewrite cyclic_abelian // -(injm_cyclic inj_sigmaU) ?cycFU. Qed.

(* This is B & G, Appendix C, Remark VII. *)
Let im_psi (x : F) : (x \in psi @: U) = (Nm x == 1).
Proof.
have /cyclicP[u0 defFU]: cyclic [set: {unit F}] by exact: cycFU.
have o_u0: #[u0] = (p ^ q).-1 by rewrite orderE -defFU card_finField_unit oF.
have ->: psi @: U = uval @: (sigmaU @* U) by rewrite morphimEdom -imset_comp.
have /set1P[->]: (sigmaU @* U)%G \in [set <[u0 ^+ (#[u0] %/ nU)]>%G].
  rewrite -cycle_sub_group ?inE; last first.
    by rewrite o_u0 -(divnK (dvdn_pred_predX p q)) dvdn_mulr.
  by rewrite -defFU subsetT card_injm //= oU.
rewrite divnA ?dvdn_pred_predX // -o_u0 mulKn //.
have [/= alpha alpha_gen Dalpha] := finField_galois_generator (subvf Fp).
have{Dalpha} Dalpha x1: x1 != 0 -> x1 / alpha x1 = x1^-1 ^+ p.-1.
  move=> nz_x1; rewrite -[_ ^+ _](mulVKf nz_x1) -exprS Dalpha ?memvf // exprVn.
  by rewrite dimv1 oF_p prednK ?prime_gt0.
apply/idP/(hilbert's_theorem_90 alpha_gen (memvf _)) => [|[u [_ nz_u] ->]].
  case/imsetP=> /= _ /cycleP[n ->] ->; rewrite expgAC; set u := (u0 ^+ n)%g.
  have nz_u: (val u)^-1 != 0 by rewrite -unitfE unitrV (valP u).
  by exists (val u)^-1; rewrite ?memvf ?Dalpha //= invrK val_unitX.
have /cycleP[n Du]: (insubd u0 u)^-1%g \in <[u0]> by rewrite -defFU inE.
have{Du} Du: u^-1 = val (u0 ^+ n)%g by rewrite -Du /= insubdK ?unitfE.
by rewrite Dalpha // Du -val_unitX mem_imset // expgAC mem_cycle.
Qed.

(* This is B & G, Appendix C, Remark VIII. *)
Let defFU : sigmaU @* U \x [set u | uval u \in Fp] = [set: {unit F}].
Proof.
have fP v: in_alg F (uval v) \is a GRing.unit by rewrite rmorph_unit ?(valP v).
pose f (v : {unit 'F_p}) := FinRing.unit F (fP v).
have fM: {in setT &, {morph f: v1 v2 / (v1 * v2)%g}}.
  by move=> v1 v2 _ _; apply: val_inj; rewrite /= -in_algE rmorphM.
pose galFpU := Morphism fM @* [set: {unit 'F_p}].
have ->: [set u | uval u \in Fp] = galFpU.
  apply/setP=> u; rewrite inE /galFpU morphimEdom.
  apply/idP/imsetP=> [|[v _ ->]]; last by rewrite /= rpredZ // memv_line.
  case/vlineP=> v Du; have nz_v: v != 0.
    by apply: contraTneq (valP u) => v0; rewrite unitfE /= Du v0 scale0r eqxx.
  exists (insubd (1%g : {unit 'F_p}) v); rewrite ?inE //.
  by apply: val_inj; rewrite /= insubdK ?unitfE.
have oFpU: #|galFpU| = p.-1.
  rewrite card_injm ?card_finField_unit ?oF_p //.
  by apply/injmP=> v1 v2 _ _ []/(fmorph_inj [rmorphism of in_alg F])/val_inj.
have oUU: #|sigmaU @* U| = nU by rewrite card_injm.
rewrite dprodE ?coprime_TIg ?oUU ?oFpU //; last first.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cycFU [set: _]))) ?subsetT.
apply/eqP; rewrite eqEcard subsetT coprime_cardMg oUU oFpU //=.
by rewrite card_finField_unit oF divnK ?dvdn_pred_predX.
Qed.

(* This is B & G, Appendix C, Remark IX. *)
Let frobH : [Frobenius H = P ><| U].
Proof.
apply/Frobenius_semiregularP=> // [||u /setD1P[ntu Uu]].
- by rewrite -(morphim_injm_eq1 inj_sigma) // im_sigma finRing_nontrivial.
- rewrite -cardG_gt1 oU ltn_divRL ?dvdn_pred_predX // mul1n -!subn1.
  by rewrite ltn_sub2r ?(ltn_exp2l 0) ?(ltn_exp2l 1) ?prime_gt1.
apply/trivgP/subsetP=> x /setIP[Px /cent1P/commgP].
rewrite inE -!(morph_injm_eq1 inj_sigma) ?(sigmaE, in_PU) //.
rewrite -mulrN1 addrC -mulrDr mulf_eq0 subr_eq0 => /orP[] // /idPn[].
by rewrite (inj_eq val_inj (sigmaU u) 1%g) morph_injm_eq1.
Qed.

(* From the abelQ assumption of Peterfalvi, Theorem (14.2) to the assumptions *)
(* of part (B) of the assumptions of Theorem C.                               *)
Let p'q : q != p. Proof. by rewrite ltn_eqF. Qed.
Let cQQ : abelian Q. Proof. exact: abelem_abelian abelQ. Qed.
Let p'Q : p^'.-group Q. Proof. exact: pi_pgroup (abelem_pgroup abelQ) _. Qed.

Let pP : p.-group P. Proof. by rewrite /pgroup oP pnat_exp ?pnat_id. Qed.
Let coQP : coprime #|Q| #|P|. Proof. exact: p'nat_coprime p'Q pP. Qed.
Let sQP0Q : [~: Q, P0] \subset Q. Proof. by rewrite commg_subl. Qed.

(* This is B & G, Appendix C, Remark X. *)
Let defQ : 'C_Q(P0) \x [~: Q, P0] = Q.
Proof. by rewrite dprodC coprime_abelian_cent_dprod // (coprimegS sP0P). Qed.

(* This is B & G, Appendix C, Remark XI. *)
Let nU_P0QP0 : exists2 y, y \in [~: Q, P0] & P0 :^ y \subset 'N(U).
Proof.
have [_ /(mem_dprod defQ)[z [y [/setIP[_ cP0z] QP0y -> _]]]] := nU_P0Q.
by rewrite conjsgM (normsP (cent_sub P0)) //; exists y.
Qed.

Let E := [set x : galF | Nm x == 1 & Nm (2%:R - x) == 1].

Let E_1 : 1 \in E.
Proof. by rewrite !inE -addrA subrr addr0 galNorm1 eqxx. Qed.

(* This is B & G, Appendix C, Lemma C.1. *)
Let Einv_gt1_le_pq : E = [set x^-1 | x in E] -> (1 < #|E|)%N -> (p <= q)%N.
Proof.
rewrite (cardsD1 1) E_1 ltnS card_gt0 => Einv /set0Pn[/= a /setD1P[not_a1 Ea]].
pose tau (x : F) := (2%:R - x)^-1.
have Etau x: x \in E -> tau x \in E.
  rewrite inE => Ex; rewrite Einv (mem_imset (fun y => y^-1)) //.
  by rewrite inE andbC opprD addNKr opprK.
pose Pa := \prod_(beta in 'Gal(Fpq / Fp)) (beta (1 - a) *: 'X + 1).
have galPoly_roots: all (root (Pa - 1)) (enum Fp).
  apply/allP=> x; rewrite mem_enum => /vlineP[b ->].
  rewrite rootE !hornerE horner_prod subr_eq0 /=; apply/eqP.
  pose h k := (1 - a) *+ k + 1; transitivity (Nm (h b)).
    apply: eq_bigr => beta _; rewrite !(rmorphB, rmorphD, rmorphMn) rmorph1 /=.
    by rewrite -mulr_natr -scaler_nat natr_Zp hornerD hornerZ hornerX hornerC.
  elim: (b : nat) => [|k IHk]; first by rewrite /h add0r galNorm1.
  suffices{IHk}: h k / h k.+1 \in E.
    rewrite inE -invr_eq1 => /andP[/eqP <- _].
    by rewrite galNormM galNormV /= [galNorm _ _ (h k)]IHk mul1r invrK.
  elim: k => [|k IHk]; first by rewrite /h add0r mul1r addrAC Etau.
  have nz_hk1: h k.+1 != 0.
    apply: contraTneq IHk => ->; rewrite invr0 mulr0.
    by rewrite inE galNorm0 eq_sym oner_eq0.
  congr (_ \in E): (Etau _ IHk); apply: canLR (@invrK _) _; rewrite invfM invrK.
  apply: canRL (mulKf nz_hk1) _; rewrite mulrC mulrBl divfK // mulrDl mul1r.
  by rewrite {2}/h mulrS -2!addrA addrK addrAC -mulrSr.
have sizePa: size Pa = q.+1.
  have sizePaX (beta : {rmorphism F -> F}) : size (beta (1 - a) *: 'X + 1) = 2.
    rewrite -mul_polyC size_MXaddC oner_eq0 andbF size_polyC fmorph_eq0.
    by rewrite subr_eq0 eq_sym (negbTE not_a1).
  rewrite size_prod => [|i _]; last by rewrite -size_poly_eq0 sizePaX.
  rewrite (eq_bigr (fun _ => 2)) => [|beta _]; last by rewrite sizePaX.
  rewrite sum_nat_const muln2 -addnn -addSn addnK.
  by rewrite -galois_dim ?finField_galois ?subvf // dimv1 divn1 dimFpq.
have sizePa1: size (Pa - 1) = q.+1.
  by rewrite size_addl // size_opp size_poly1 sizePa.
have nz_Pa1 : Pa - 1 != 0 by rewrite -size_poly_eq0 sizePa1.
by rewrite -ltnS -oFp -sizePa1 cardE max_poly_roots ?enum_uniq.
Qed.

(* This is B & G, Appendix C, Lemma C.2. *)
Let E_gt1 : (1 < #|E|)%N.
Proof.
have [q_gt4 | q_le4] := ltnP 4 q.
  pose inK x := enum_rank_in (classes1 H) (x ^: H).
  have inK_E x: x \in H -> enum_val (inK x) = x ^: H.
    by move=> Hx; rewrite enum_rankK_in ?mem_classes. 
  pose j := inK s; pose k := inK (s ^+ 2)%g; pose e := gring_classM_coef j j k.
  have cPP: abelian P by rewrite -(injm_abelian inj_sigma) ?zmod_abelian.
  have Hs: s \in H by rewrite -(sdprodW defH) -[s]mulg1 mem_mulg.
  have DsH n: (s ^+ n) ^: H = (s ^+ n) ^: U.
    rewrite -(sdprodW defH) classM (abelian_classP _ cPP) ?groupX //.
    by rewrite class_support_set1l.
  have injJU: {in U &, injective (conjg s)}.
    by move=> u v Uu Uv eq_s_uv; apply/inj_psi; rewrite ?psiE ?eq_s_uv.
  have ->: #|E| = e.
    rewrite /e /gring_classM_coef !inK_E ?groupX //.
    transitivity #|[set u in U | s^-1 ^ u * s ^+ 2 \in s ^: U]%g|.
      rewrite -(card_in_imset (sub_in2 _ inj_psi)) => [|u /setIdP[] //].
      apply: eq_card => x; rewrite inE -!im_psi.
      apply/andP/imsetP=> [[/imsetP[u Uu ->] /imsetP[v Uv Dv]]{x} | ].
        exists u; rewrite // inE Uu /=; apply/imsetP; exists v => //.
        by apply: (injmP _ inj_sigma); rewrite ?(sigmaE, in_PU) // mulN1r addrC.
      case=> u /setIdP[Uu /imsetP[v Uv /(congr1 sigma)]].
      rewrite ?(sigmaE, in_PU) // mulN1r addrC => Dv ->.
      by rewrite Dv !mem_imset.
    rewrite DsH (DsH 1%N) expg1; have [w Uw ->] := repr_class U (s ^+ 2).
    pose f u := (s ^ (u * w), (s^-1 ^ u * s ^+ 2) ^ w).
    rewrite -(@card_in_imset _ _ f) => [|u v]; last first.
      by move=> /setIdP[Uu _] /setIdP[Uv _] [/injJU/mulIg-> //]; apply: groupM.
    apply: eq_card => [[x1 x2]]; rewrite inE -andbA.
    apply/imsetP/and3P=> [[u /setIdP[Uu sUs2u'] [-> ->]{x1 x2}] | []].
      rewrite /= conjgM -(rcoset_id Uw) class_rcoset !memJ_conjg mem_orbit //.
      by rewrite sUs2u' -conjMg conjVg mulKVg.
    case/imsetP=> u Uu /= -> sUx2 /eqP/(canRL (mulKg _)) Dx2.
    exists (u * w^-1)%g; last first.
      by rewrite /f /= conjMg -conjgM mulgKV conjVg -Dx2.
    rewrite inE !in_PU // Uw -(memJ_conjg _ w) -class_rcoset rcoset_id //.
    by rewrite conjMg -conjgM mulgKV conjVg -Dx2.
  pose chi_s2 i := 'chi[H]_i s ^+ 2 * ('chi_i (s ^+ 2)%g)^* / 'chi_i 1%g.
  have De: e%:R = #|U|%:R / #|P|%:R * (\sum_i chi_s2 i).
    have Ks: s \in enum_val j by rewrite inK_E ?class_refl.
    have Ks2: (s ^+ 2)%g \in enum_val k by rewrite inK_E ?groupX ?class_refl.
    rewrite (gring_classM_coef_sum_eq Ks Ks Ks2) inK_E //; congr (_ * _).
    have ->: #|s ^: H| = #|U| by rewrite (DsH 1%N) (card_in_imset injJU).
    by rewrite -(sdprod_card defH) mulnC !natrM invfM mulrA mulfK ?neq0CG.
  pose linH := [pred i | P \subset cfker 'chi[H]_i].
  have nsPH: P <| H by have [] := sdprod_context defH.
  have sum_linH: \sum_(i in linH) chi_s2 i = #|U|%:R.
    have isoU: U \isog H / P := sdprod_isog defH.
    have abHbar: abelian (H / P) by rewrite -(isog_abelian isoU).
    rewrite (card_isog isoU) -(card_Iirr_abelian abHbar) -sumr_const.
    rewrite (reindex _ (mod_Iirr_bij nsPH)) /chi_s2 /=.
    apply: eq_big => [i | i _]; rewrite ?mod_IirrE ?cfker_mod //.
    have lin_i: ('chi_i %% P)%CF \is a linear_char.
      exact/cfMod_lin_char/char_abelianP.
    rewrite lin_char1 // divr1 -lin_charX // -normCK.
    by rewrite normC_lin_char ?groupX ?expr1n.
  have degU i: i \notin linH -> 'chi_i 1%g = #|U|%:R.
    case/(Frobenius_Ind_irrP (FrobeniusWker frobH)) => {i}i _ ->.
    rewrite cfInd1 ?normal_sub // -(index_sdprod defH) lin_char1 ?mulr1 //.
    exact/char_abelianP.
  have ub_linH' m (s_m := (s ^+ m)%g):
    (0 < m < 5)%N -> \sum_(i in predC linH) `|'chi_i s_m| ^+ 2 <= #|P|%:R.
  - case/andP=> m_gt0 m_lt5; have{m_gt0 m_lt5} P1sm: s_m \in P^#.
      rewrite !inE groupX // -order_dvdn -(order_injm inj_sigma) // sigmaE.
      by rewrite andbT order_primeChar ?oner_neq0 ?gtnNdvd ?(leq_trans m_lt5).
    have ->: #|P| = (#|P| * (s_m \in s_m ^: H))%N by rewrite class_refl ?muln1.
    have{P1sm} /eqP <-: 'C_H[s ^+ m] == P.
      rewrite eqEsubset (Frobenius_cent1_ker frobH) // subsetI normal_sub //=.
      by rewrite sub_cent1 groupX // (subsetP cPP).
    rewrite mulrnA -second_orthogonality_relation ?groupX // big_mkcond.
    by apply: ler_sum => i _; rewrite normCK; case: ifP; rewrite ?mul_conjC_ge0.
  have sqrtP_gt0: 0 < sqrtC #|P|%:R by rewrite sqrtC_gt0 ?gt0CG.
  have{De ub_linH'}: `|(#|P| * e)%:R - #|U|%:R ^+ 2| <= #|P|%:R * sqrtC #|P|%:R.
    rewrite natrM De mulrCA mulrA divfK ?neq0CG // (bigID linH) /= sum_linH.
    rewrite mulrDr addrC addKr mulrC mulr_suml /chi_s2.
    rewrite (ler_trans (ler_norm_sum _ _ _)) // -ler_pdivr_mulr // mulr_suml.
    apply: ler_trans (ub_linH' 1%N isT); apply: ler_sum => i linH'i.
    rewrite ler_pdivr_mulr // degU ?divfK ?neq0CG //.
    rewrite normrM -normrX norm_conjC ler_wpmul2l ?normr_ge0 //.
    rewrite -ler_sqr ?qualifE ?normr_ge0 ?(@ltrW _ 0) // sqrtCK. 
    apply: ler_trans (ub_linH' 2 isT); rewrite (bigD1 i) ?ler_paddr //=.
    by apply: sumr_ge0 => i1 _; rewrite exprn_ge0 ?normr_ge0.
  rewrite natrM real_ler_distl ?rpredB ?rpredM ?rpred_nat // => /andP[lb_Pe _]. 
  rewrite -ltC_nat -(ltr_pmul2l (gt0CG P)) {lb_Pe}(ltr_le_trans _ lb_Pe) //.
  rewrite ltr_subr_addl (@ler_lt_trans _ ((p ^ q.-1)%:R ^+ 2)) //; last first.
    rewrite  -!natrX ltC_nat ltn_sqr oU ltn_divRL ?dvdn_pred_predX //.
    rewrite -(subnKC qgt1) /= -!subn1 mulnBr muln1 -expnSr.
    by rewrite ltn_sub2l ?(ltn_exp2l 0) // prime_gt1.
  rewrite -mulrDr -natrX -expnM muln2 -subn1 doubleB -addnn -addnBA // subn2.
  rewrite expnD natrM -oP ler_wpmul2l ?ler0n //.
  apply: ler_trans (_ : 2%:R * sqrtC #|P|%:R <= _).
    rewrite mulrDl mul1r ler_add2l -(@expr_ge1 _ 2) ?(ltrW sqrtP_gt0) // sqrtCK.
    by rewrite oP natrX expr_ge1 ?ler0n ?ler1n.
  rewrite -ler_sqr ?rpredM ?rpred_nat ?qualifE ?(ltrW sqrtP_gt0) //.
  rewrite exprMn sqrtCK -!natrX -natrM leC_nat -expnM muln2 oP.
  rewrite -(subnKC q_gt4) doubleS (expnS p _.*2.+1) -(subnKC pgt4) leq_mul //.
  by rewrite ?leq_exp2l // !doubleS !ltnS -addnn leq_addl.
have q3: q = 3 by apply/eqP; rewrite eqn_leq qgt2 andbT -ltnS -(odd_ltn 5).
rewrite (cardsD1 1) E_1 ltnS card_gt0; apply/set0Pn => /=.
pose f (c : 'F_p) : {poly 'F_p} := 'X * ('X - 2%:R%:P) * ('X - c%:P) + ('X - 1).
have fc0 c: (f c).[0] = -1 by rewrite !hornerE.
have fc2 c: (f c).[2%:R] = 1 by rewrite !(subrr, hornerE) /= addrK.
have /existsP[c nz_fc]: [exists c, ~~ [exists d, root (f c) d]].
  have nz_f_0 c: ~~ root (f c) 0 by rewrite /root fc0 oppr_eq0.
  rewrite -negb_forall; apply/negP=> /forallP/(_ _)/existsP.
  case/fin_all_exists=> /= rf rfP; suffices inj_rf: injective rf.
    by have /negP[] := nz_f_0 (invF inj_rf 0); rewrite -{2}[0](f_invF inj_rf).
  move=> a b eq_rf_ab; apply/oppr_inj/(addrI (rf a)).
  have: (f a).[rf a] = (f b).[rf a] by rewrite {2}eq_rf_ab !(rootP _).
  rewrite !(hornerXsubC, hornerD, hornerM) hornerX => /addIr/mulfI-> //.
  rewrite mulf_neq0 ?subr_eq0 1?(contraTneq _ (rfP a)) // => -> //.
  by rewrite /root fc2.
have{nz_fc} /= nz_fc: ~~ root (f c) _ by apply/forallP; rewrite -negb_exists.
have sz_fc_lhs: size ('X * ('X - 2%:R%:P) * ('X - c%:P)) = 4.
  by rewrite !(size_mul, =^~ size_poly_eq0) ?size_polyX ?size_XsubC.
have sz_fc: size (f c) = 4 by rewrite size_addl ?size_XsubC sz_fc_lhs.
have irr_fc: irreducible_poly (f c) by apply: cubic_irreducible; rewrite ?sz_fc.
have fc_monic : f c \is monic.
  rewrite monicE lead_coefDl ?size_XsubC ?sz_fc_lhs // -monicE.
  by rewrite !monicMl ?monicXsubC ?monicX.
pose inF := [rmorphism of in_alg F]; pose fcF := map_poly inF (f c).
have /existsP[a fcFa_0]: [exists a : F, root fcF a].
  suffices: ~~ coprimep (f c) ('X ^+ #|F| - 'X).
    apply: contraR; rewrite -(coprimep_map inF) negb_exists => /forallP nz_fcF.
    rewrite -/fcF rmorphB rmorphX /= map_polyX finField_genPoly.
    elim/big_rec: _ => [|x gF _ co_fcFg]; first exact: coprimep1.
    by rewrite coprimep_mulr coprimep_XsubC nz_fcF.
  have /irredp_FAdjoin[L dimL [z /coprimep_root fcz0 _]] := irr_fc.
  pose finL := [vectType 'F_p of FinFieldExtType L].
  set fcL := map_poly _ _ in fcz0; pose inL := [rmorphism of in_alg L].
  rewrite -(coprimep_map inL) -/fcL rmorphB rmorphX /= map_polyX.
  apply: contraL (fcz0 _) _; rewrite hornerD hornerN hornerXn hornerX subr_eq0.
  have ->: #|F| = #|{: finL}%VS| by rewrite oF card_vspace dimL sz_fc oF_p q3.
  by rewrite card_vspacef (expf_card (z : finL)).
have Fp_fcF: fcF \is a polyOver Fp.
  by apply/polyOverP => i; rewrite coef_map /= memvZ ?memv_line.
pose G := 'Gal(Fpq / Fp).
have galG: galois Fp Fpq by rewrite finField_galois ?subvf.
have oG: #|G| = 3 by rewrite -galois_dim // dimv1 dimFpq q3.
have Fp'a: a \notin Fp.
  by apply: contraL fcFa_0 => /vlineP[d ->]; rewrite fmorph_root.
have DfcF: fcF = \prod_(beta in G) ('X - (beta a)%:P).
  pose Pa : {poly F} := minPoly Fp a.
  have /eqP szPa: size Pa == 4.
    rewrite size_minPoly eqSS (sameP eqP (prime_nt_dvdP _ _)) -?elemDeg1 //.
    by rewrite elementDegreeE dimv1 divn1 -q3 -dimFpq field_dimS ?subvf.
  have dvd_Pa_fcF: Pa %| fcF by apply: minPoly_dvdp fcFa_0.
  have{dvd_Pa_fcF} /eqP <-: Pa == fcF.
    rewrite -eqp_monic ?monic_minPoly ?monic_map // -dvdp_size_eqp //.
    by rewrite szPa size_map_poly sz_fc.
  have /galois_factors[_ /(_ a (memvf a))[r [srG /map_uniq Ur defPa]]] := galG.
  rewrite -/Pa big_map in defPa; rewrite defPa big_uniq //=.
  apply/eq_bigl/subset_cardP=> //; apply/eqP.
  by rewrite -eqSS (card_uniqP Ur) oG -szPa defPa size_prod_XsubC.
exists a; rewrite !inE; apply/and3P; split.
- by apply: contraNneq Fp'a => ->; apply: mem1v.
- apply/eqP; transitivity ((- 1) ^+ #|G| * fcF.[inF 0]).
    rewrite DfcF horner_prod -prodrN; apply: eq_bigr => beta _.
    by rewrite rmorph0 hornerXsubC add0r opprK.
  by rewrite -signr_odd mulr_sign oG horner_map fc0 rmorphN1 opprK.
apply/eqP; transitivity fcF.[inF 2%:R]; last by rewrite horner_map fc2 rmorph1.
rewrite DfcF horner_prod; apply: eq_bigr => beta _.
by rewrite hornerXsubC rmorphB !rmorph_nat.
Qed.

Section AppendixC3.

Import GroupScope.

Variables y : gT.
Hypotheses (QP0y : y \in [~: Q, P0]) (nUP0y : P0 :^ y \subset 'N(U)).
Let Qy : y \in Q. Proof. by rewrite (subsetP sQP0Q). Qed.

Let t := s ^ y.
Let P1 := P0 :^ y.

(* This is B & G, Appendix C, Lemma C.3, Step 1. *)
Let splitH x :
     x \in H ->
  exists2 u, u \in U & exists2 v, v \in U & exists2 s1, s1 \in P0
  & x = u * s1 * v.
Proof.
case/(mem_sdprod defH) => z [v [Pz Uv -> _]].
have [-> | nt_z] := eqVneq z 1.
  by exists 1 => //; exists v => //; exists 1; rewrite ?mulg1.
have nz_z: sigma z != 0 by rewrite (morph_injm_eq1 inj_sigma).
have /(mem_dprod defFU)[]: finField_unit nz_z \in setT := in_setT _.
move=> _ [w [/morphimP[u Uu _ ->] Fp_w /(congr1 val)/= Dz _]].
have{Fp_w Dz} [n Dz]: exists n, sigma z = sigma ((s ^+ n) ^ u).
  move: Fp_w; rewrite {}Dz inE => /vlineP[n ->]; exists n.
  by rewrite -{1}(natr_Zp n) scaler_nat mulr_natr conjXg !sigmaE ?in_PU.
exists u^-1; last exists (u * v); rewrite ?groupV ?groupM //.
exists (s ^+ n); rewrite ?groupX // mulgA; congr (_ * _).
by apply: (injmP _ inj_sigma); rewrite -?mulgA ?in_PU.
Qed.

(* This is B & G, Appendix C, Lemma C.3, Step 2. *)
Let not_splitU s1 s2 u :
  s1 \in P0 -> s2 \in P0 -> u \in U -> s1 * u * s2 \in U ->
  (s1 == 1) && (s2 == 1) || (u == 1) && (s1 * s2 == 1).
Proof.
move=> P0s1 P0s2 Uu; have [_ _ _ tiPU] := sdprodP defH.
have [Ps1 Ps2]: s1 \in P /\ s2 \in P by rewrite !(subsetP sP0P).
have [-> | nt_s1 /=] := altP (s1 =P 1).
  by rewrite mul1g groupMl // -in_set1 -set1gE -tiPU inE Ps2 => ->.
have [-> | nt_u /=] := altP (u =P 1).
  by rewrite mulg1 -in_set1 -set1gE -tiPU inE (groupM Ps1).
rewrite (conjgC _ u) -mulgA groupMl // => Us12; case/negP: nt_u.
rewrite -(morph_injm_eq1 inj_sigmaU) // -in_set1 -set1gE.
have [_ _ _ <-] := dprodP defFU; rewrite !inE mem_morphim //= -/(psi u).
have{Us12}: s1 ^ u * s2 == 1.
  by rewrite -in_set1 -set1gE -tiPU inE Us12 andbT !in_PU.
rewrite -(morph_injm_eq1 inj_sigma) ?(in_PU, sigmaE) // addr_eq0.
move/eqP/(canRL (mulKf _))->; rewrite ?morph_injm_eq1 //.
by rewrite mulrC rpred_div ?rpredN //= -sigmaP0 mem_morphim.
Qed.

(* This is B & G, Appendix C, Lemma C.3, Step 3. *)
Let tiH_P1 t1 : t1 \in P1^# -> H :&: H :^ t1 = U.
Proof.
case/setD1P=>[nt_t1 P1t1]; set X := H :&: _.
have [nsPH sUH _ _ tiPU] := sdprod_context defH.
have sUX: U \subset X.
  by rewrite subsetI sUH -(normsP nUP0y t1 P1t1) conjSg.
have defX: (P :&: X) * U = X.
  by rewrite setIC group_modr // (sdprodW defH) setIAC setIid.
have [tiPX | ntPX] := eqVneq (P :&: X) 1; first by rewrite -defX tiPX mul1g.
have irrPU: acts_irreducibly U P 'J.
  apply/mingroupP; (split=> [|V /andP[ntV]]; rewrite astabsJ) => [|nVU sVP].
    by have [_ ->] := Frobenius_context frobH.
  apply/eqP; rewrite eqEsubset sVP; apply/subsetP=> x Px.
  have [-> // | ntx] := eqVneq x 1.
  have [z Vz ntz] := trivgPn _ ntV; have Pz := subsetP sVP z Vz.
  have nz_z: sigma z != 0%R by rewrite morph_injm_eq1.
  have uP: (sigma x / sigma z)%R \is a GRing.unit.
    by rewrite unitfE mulf_neq0 ?invr_eq0 ?morph_injm_eq1.
  have: FinRing.unit F uP \in setT := in_setT _.
  case/(mem_dprod defFU)=> _ [s1 [/morphimP[u Uu _ ->]]].
  rewrite inE => /vlineP[n Ds1] /(congr1 val)/= Dx _.
  suffices ->: x = (z ^ u) ^+ n by rewrite groupX ?memJ_norm ?(subsetP nVU).
  apply: (injmP _ inj_sigma); rewrite ?(in_PU, sigmaE) //.
  by rewrite -mulr_natr -scaler_nat natr_Zp -Ds1 -mulrA -Dx mulrC divfK.
have{ntPX defX irrPU} defX: X :=: H.
  rewrite -(sdprodW defH) -defX; congr (_ * _).
  have [_ -> //] := mingroupP irrPU; rewrite ?subsetIl //= -/X astabsJ ntPX.
  by rewrite normsI // normsG.
have nHt1: t1 \in 'N(H) by rewrite -groupV inE sub_conjgV; apply/setIidPl.
have oP0: #|P0| = p by rewrite -(card_injm inj_sigma) // (eq_card sigmaP0) oFp.
have{nHt1} nHP1: P1 \subset 'N(H).
  apply: prime_meetG; first by rewrite cardJg oP0.
  by apply/trivgPn; exists t1; rewrite // inE P1t1.
have{nHP1} nPP1: P1 \subset 'N(P).
  have /Hall_pi hallP: Hall H P by apply: Frobenius_ker_Hall frobH.
  by rewrite -(normal_Hall_pcore hallP nsPH) (char_norm_trans (pcore_char _ _)).
have sylP0: p.-Sylow(Q <*> P0) P0.
  rewrite /pHall -divgS joing_subr ?(pgroupS sP0P) //=.
  by rewrite norm_joinEr // coprime_cardMg ?(coprimegS sP0P) ?mulnK.
have sP1QP0: P1 \subset Q <*> P0.
  by rewrite conj_subG ?joing_subr ?mem_gen // inE Qy.
have nP10: P1 \subset 'N(P0).
  have: P1 \subset 'N(P :&: (Q <*> P0)) by rewrite normsI // normsG.
  by rewrite norm_joinEr // -group_modr // setIC coprime_TIg // mul1g.
have eqP10: P1 :=: P0.
  apply/eqP; rewrite eqEcard cardJg leqnn andbT.
  rewrite (comm_sub_max_pgroup (Hall_max sylP0)) //; last exact: normC.
  by rewrite pgroupJ (pHall_pgroup sylP0).
have /idPn[] := prime_gt1 pr_p.
rewrite -oP0 cardG_gt1 negbK -subG1 -(Frobenius_trivg_cent frobH) subsetI sP0P.
apply/commG1P/trivgP; rewrite -tiPU commg_subI // subsetI ?subxx //.
by rewrite sP0P -eqP10.
Qed.
  
(* This is B & G, Appendix C, Lemma C.3, Step 4. *)
Fact BGappendixC3_Ediv : E = [set (x^-1)%R | x in E].
Proof.
have HtP1 : t \in P1 by rewrite memJ_conjg.
have HUconj r : r \in P1 -> U :^ r = U by move/(subsetP nUP0y)/normP.
have HutnU u n : u \in U -> u ^ (t ^+ n) \in U.
  by rewrite memJ_norm // groupX // (subsetP nUP0y).
have HutNnU u n : u \in U -> u ^ (t ^- n) \in U.
  by rewrite memJ_norm // groupV groupX // (subsetP nUP0y).
have HtsQ i : s ^- i * t ^+ i \in Q.
  rewrite -conjXg !mulgA groupM // -mulgA memJ_norm ?groupV // groupX //.
  by apply: (subsetP nQP0).
suffices Hsuff a: a \in U -> psi a \in E -> psi (a^-1 ^ (t ^+ 3)) \in E.
  suffices sE'E: [set (x^-1)%R | x in E] \subset E.
    apply/esym/eqP; rewrite eqEcard sE'E card_imset //=.
    exact: can_inj (@invrK _).
  apply/subsetP => _ /imsetP [x Ex ->].
  have /imsetP[a Ua Dx]: x \in psi @: U.
    by rewrite im_psi !inE in Ex *; case/andP: Ex.
  suffices: psi (a^-1 ^ 1) \in E by rewrite conjg1 Dx sigmaE.
  have /eqP <- : (t ^+ (3 * p ^ q)) == 1.
    by rewrite -order_dvdn dvdn_mull // orderJ -oP order_dvdG.
  rewrite -(odd_double_half (p ^ q)) odd_exp odd_p orbT addnC.
  elim: _./2 => [|n /= IHn]; first by rewrite Hsuff -?Dx.
  rewrite doubleS 2!addSn !mulnSr 2!expgD 2!conjgM.
  by rewrite -[u in u ^ t ^+ 3]invgK -conjVg !Hsuff ?(HutnU, groupV).
rewrite 2!inE => Ha /andP[_ Hb].
have Hainvt3 : a^-1 ^ t ^+ 3 \in U by rewrite HutnU ?groupV.
pose goal v1 := s ^+ 2 = s ^ v1 * s ^ a^-1 ^ t ^+ 3.
suffices [v1 Hv1U /(congr1 sigma)]: exists2 v1, v1 \in U & goal v1.
  rewrite sigmaX // sigma_s sigmaM ?memJ_P -?psiE // => /(canLR (addrK _))->.
  by rewrite -!im_psi !mem_imset.
have{Hb} /imsetP[b Hb]: 2%:R - psi a \in psi @: U by rewrite im_psi.
move/(canRL (subrK _))/esym; rewrite addrC => Hab.
(* In the book k is aribtrary in Fp; however only k := 3 is used *)
pose k := 3.
have [_ HPU _ HPUI] := sdprodP defH.
have C5inH m n r u : u \in U -> s ^+ m * u ^ t ^+ r * s ^- n \in H.
  move => Hu.
  apply: groupM; first apply groupM; rewrite ?groupV ?groupX // -HPU.
  - by apply: (subsetP (mulG_subl U P)).
  - by apply: (subsetP (mulG_subr P U)); apply: HutnU.
  - by apply: (subsetP (mulG_subl U P)).
have [|u1 Hu1 [v1 Hv1 [s1 Hs1 Husv1]]] :=
         @splitH (s ^+ k.-2 * a^-1 ^ t ^+ k * s ^- k.-1).
  by apply: C5inH; rewrite groupV.
have [|u2 Hu2 [v2 Hv2 [s2 Hs2 Husv2]]] :=
         @splitH (s ^+ k * (a * b^-1) ^ t ^+ k.-1 * s ^- k.-2).
  by apply: C5inH; rewrite groupM ?groupV.
have [|{C5inH} u3 Hu3 [v3 Hv3 [s3 Hs3 Husv3]]] :=
         @splitH (s ^+ k.-1 * b ^ t ^+ k.-2 * s ^- k).
  by apply: C5inH.
exists v1; first done.
have C6 m n r u ui vi si : s ^+ m * u ^ t ^+ r * s ^- n = ui * si * vi ->
  s ^+ m != s ^+ n -> (s ^+ m != 1) || (s ^- n != 1) ->
  u \in U -> ui \in U -> vi \in U -> si != 1.
- case: (eqVneq si 1) => [->|//].
  rewrite mulg1 => Huv Hmn HmVn Hu Hui Hvi.
  have Hsm : s ^+ m \in P0 by apply: groupX.
  have Hsn : s ^- n \in P0 by rewrite groupV; apply: groupX.
  have Hut : u ^ t ^+ r \in U by apply: HutnU.
  have := groupM Hui Hvi; rewrite -Huv.
  case/(not_splitU Hsm Hsn Hut)/orP.
    by move: HmVn; rewrite -negb_and; case: (_ && _).
  by rewrite -eq_mulgV1 andbC; case: (s ^+ _ == _) Hmn.
have ss_neq_1 : s ^+ 2 != 1.
  rewrite -order_dvdn gtnNdvd // odd_gt2 ?order_gt1 // orderE defP0.
  by rewrite (oddSg sP0P) // oP odd_exp odd_p orbT.
have s1neq1 : s1 != 1.
  move/C6: Husv1 => -> //; rewrite ?groupV //.
    by rewrite eq_mulVg1 !(expg1, expgS) mulKg.
  by rewrite expg1 nt_s.
have{C6} s3neq1 : s3 != 1.
  move/C6: Husv3 => -> //; last by rewrite ss_neq_1.
  by rewrite eq_mulVg1 !(expg1, expgS) !invMg -!mulgA !mulKg.
pose w1 := v2 ^ t^-1 * u3.
pose w2 := v3 * u1 ^ t ^- 2.
pose w3 := v1 * u2 ^ t.
wlog suff{s1neq1 s3neq1 goal Hainvt3} C7_gen : a b u1 s1 v1 u2 s2 v2 u3 s3 v3 
  Husv1 Husv2 Husv3 Hab Ha Hb Hu1 Hs1 Hv1 Hu2 Hs2 Hv2 Hu3 Hs3 Hv3
  @w1 @w2 @w3  /
  t^-1 * s2 * t^-1 = ((w1 * s3 * w2) * (t ^+ 2 * s1 * w3))^-1; last first.
- apply/eqP; rewrite invMg -(canF_eq (mulgK _)) eq_sym eq_invg_mul; apply/eqP.
  have: s ^- 2 * (s ^ a * s ^ b) == 1.
    by rewrite -(morph_injm_eq1 inj_sigma) ?{1}(sigmaE, in_PU) // Hab addNr.
  pose l := (k - 2)%N; rewrite -(conjg_eq1 _ (t ^+ l)).
  rewrite [X in X == _](_ : _ = 
    ((t ^- l * s ^+ l) * (s ^- k * t ^+ k)) * a^-1 ^ t ^+ k *
    ((t ^- k * s ^+ k) * (s ^- k.-1 * t ^+ k.-1)) * (a * b^-1) ^ t ^+ k.-1 * 
    ((t ^- k.-1 * s ^+ k.-1) * (s ^- l * t ^+ l)) * b ^ t ^+ l *
    s ^- k * s ^+ k); last by rewrite /t !conjgE !invMg !mulgA !mulgK !mulgKV.
  have ts_commute m n : commute (t ^- m * s ^+ m) (s ^- n * t ^+ n).
    apply: (centsP (abelem_abelian abelQ)) => //.
    by rewrite -groupV invMg invgK.
  rewrite !ts_commute {ts_commute} -(conjg_eq1 _ (s ^- k)).
  set C5a := s ^+ k.-2 * a^-1 ^ t ^+ k * s ^- k.-1.
  set C5b := s ^+ k * (a * b^-1) ^ t ^+ k.-1 * s ^- k.-2.
  set C5c := s ^+ k.-1 * b ^ t ^+ k.-2 * s ^- k.
  rewrite [X in X == _](_ : _ = t ^+ 2 * C5a * t^-1 * C5b * t^-1 * C5c);
      last first.
    rewrite /C5a /C5b /C5c expgS expg1 /t !conjgE.
    by rewrite !invMg -!mulgA !mulKg !mulKVg !invgK.
  rewrite [C5a]Husv1 [C5b]Husv2 [C5c]Husv3 -(conjg_eq1 _ (u1 ^ t ^- 2)).
  move/eqP <-; rewrite /w1 /w2 /w3 -!conjXg !conjgE !(invgK, invMg) !mulgA.
  by rewrite !(mulgK, mulgKV).
have C7 : t^-1 * s2 * t^-1 = (w1 * s3 * w2 * (t ^+ 2 * s1 * w3))^-1.
  by apply: (C7_gen a b).
have moduloP u ui si vi m n r : s ^+ m * u ^ t ^+ r * s ^- n = ui * si * vi ->
  u \in U -> ui \in U -> si \in P0 -> vi \in U -> ui * vi = u ^ t ^+ r.
- rewrite [_ * si]conjgCV -2!mulgA [_ * s ^- n]conjgCV {1}mulgA.
  move/(canRL (mulgK _)); rewrite -mulgA; move/(canLR (mulKg _)) => Husvi.
  move => Hu Hui Hsi Hvi.
  apply/eqP; rewrite eq_mulgV1; apply/eqP/set1P.
  rewrite -[[set 1]]HPUI inE -{1}Husvi.
  by rewrite !(HutnU, memJ_P, groupV, groupM) ?groupX // (subsetP sP0P).
have: t^-1 * s2 * t^-1 = (w1 ^+ p * s3 * w2 ^+ p * (t ^+ 2 * s1 * w3 ^+ p))^-1.
  pose ap := a ^+ p; pose bp := b ^+ p.
  have Hapbp : psi ap + psi bp = 2%:R.
    by rewrite !sigmaE // -!Frobenius_autE -rmorphD Hab rmorph_nat.
  suff Husvp u ui si vi m n r : s ^+ m * u ^ t ^+ r * s ^- n = ui * si * vi ->
    u \in U -> ui \in U -> si \in P0 -> vi \in U ->
    s ^+ m * (u ^+ p) ^ t ^+ r * s ^- n = ui ^+ p * si * vi ^+ p.
  - have -> : w1 ^+ p = (v2 ^+ p) ^ t^-1 * u3 ^+ p.
      rewrite conjXg expgMn //; apply: (centsP cUU) => //.
      by rewrite -[t]expg1 HutNnU.
    have -> : w2 ^+ p = v3 ^+ p * (u1 ^+ p) ^ t ^- 2.
      rewrite conjXg expgMn //; apply: (centsP cUU) => //.
      by rewrite HutNnU.
    have -> : w3 ^+ p = v1 ^+ p * (u2 ^+ p) ^ t.
      rewrite conjXg expgMn //; apply: (centsP cUU) => //.
      by rewrite -[t]expg1 HutnU.
    apply: (C7_gen ap bp) => //; try apply: groupX => //.
    - by rewrite -[ap^-1]expgVn; apply: Husvp => //; rewrite groupV.
    - rewrite -[bp^-1]expgVn -expgMn; last first.
        by apply: (centsP cUU); rewrite // groupV.
      by apply: Husvp => //; rewrite groupM // groupV.
    - by apply: Husvp => //.
  move => Husvi Hu Hui Hsi Hvi.
  have Huivi := moduloP _ _ _ _ _ _ _ Husvi Hu Hui Hsi Hvi.
  move: (Husvi).
  rewrite [_ * si]conjgCV -2!mulgA [_ * s ^- n]conjgCV {1}mulgA -Huivi.
  move/(can_inj (mulgK _))/eqP; rewrite eq_sym.
  rewrite (canF_eq (conjgKV _)) conjMg -conjgM invMg mulgKV conjVg !conjXg.
  move/eqP/(congr1 (fun x => Frobenius_aut charFp (sigma x)))/eqP.
  rewrite morphM ?morphV ?morphX -?psiE ?groupV ?groupX ?memJ_P ?groupV //.
  rewrite rmorphB !zmodXgE -![val _ *+ _]mulr_natl !rmorphM !rmorph_nat /=.
  rewrite !Frobenius_autE.
  have : sigma si \in Fp by rewrite -sigmaP0 morphimEsub ?mem_imset.
  rewrite [_ \in _]Fermat's_little_theorem dimv1 oF_p => /eqP->.
  rewrite -!psiX ?groupV // !mulr_natl !psiE ?groupX ?groupV //.
  rewrite -!sigmaE.1.2 ?in_PU //.
  rewrite (inj_in_eq (injmP _ inj_sigma)) ?in_PU // ?(subsetP sP0P) //.
  rewrite -!conjXg -conjVg expgVn => /eqP->; rewrite mulgA -conjgC.
  rewrite -3!mulgA -conjgCV; congr (_ * _); rewrite mulgA; congr (_ * _).
  by rewrite -expgMn ?Huivi -?conjXg //; apply: (centsP cUU).
rewrite C7 {C7_gen} => /invg_inj.
rewrite [X in X = _](_ : _ = w1 * s3 * w2 * t ^+ 2 * (s1 * w3));
  last by rewrite !mulgA.
rewrite [X in _ = X](_ : _ = w1 ^+ p * s3 * w2 ^+ p * t ^+ 2 * (s1 * w3 ^+ p));
  last by rewrite !mulgA.
move/(canLR (mulKg _)); rewrite mulgA; move/(canRL (mulgK _)).
rewrite [X in X = _](_ : _ = 
  ((w1 ^+ p * s3 * w2 ^+ p)^-1 * (w1 * s3 * w2)) ^ t ^+ 2); last first.
- by rewrite conjgE !(invMg, mulgA).
move => Hw.
have Hw1 : w1 \in U by rewrite groupM // -[t]expg1 HutNnU.
have Hw2 : w2 \in U by rewrite groupM // HutNnU.
have Hw3 : w3 \in U by by rewrite groupM // -[t]expg1 HutnU.
have : (s1 == 1) && (s1^-1 == 1) || (w3 ^+ p * w3^-1 == 1) && (s1 * s1^-1 == 1).
  apply: not_splitU; rewrite ?groupV //.
  - by rewrite groupM ?groupV ?groupX. 
  have Ht2 : t ^+ 2 \in P1^#.
    by rewrite 2!inE groupX // andbT -conjXg conjg_eq1.
  rewrite [X in X \in _](_ : _ =  s1 * w3 ^+ p * (s1 * w3)^-1);
    last by rewrite !invMg !mulgA.
  rewrite -(tiH_P1 Ht2) inE -{2}Hw {Hw}.
  have /subsetP HUH : U \subset H by rewrite -HPU; apply: mulG_subr.
  move: w1 w2 w3 {C7 Hw1 Hw2 Hw3} (HUH _ Hw1) (HUH _ Hw2) (HUH _ Hw3).
  move => w1 w2 w3 Hw1 Hw2 Hw3.
  by apply/andP; split; last apply: mem_imset;
     rewrite !(groupV, groupM, groupX) // -HPU;
     apply: (subsetP (mulG_subl U P)); apply (subsetP sP0P).
rewrite eq_invg1 andbb (negbTE s1neq1) /=.
rewrite -[p]prednK ?prime_gt0 // expgSr mulgK.
have Hwp1 wi : wi \in U -> wi ^+ p.-1 == 1 -> wi = 1.
  by move=> Uwi /eqP/(canRL_in (expgK _) Uwi)->; rewrite ?expg1n ?oU.
case/andP => /(Hwp1 _ Hw3) w3_eq1 _.
move/eqP: Hw.
rewrite w3_eq1 expg1n mulg1 mulgV conjg_eq1 -eq_mulVg1.
rewrite -(canF_eq (mulKVg _)) invMg !mulgA (canF_eq (mulgK _)) => /eqP Hw.
have : (s3^-1 == 1) && (s3 == 1) || (w1^-1 * w1 ^+ p == 1) && (s3^-1 * s3 == 1).
  by apply: not_splitU; rewrite ?groupV // ?mulgA ?Hw groupM ?groupV ?groupX.
rewrite eq_invg1 andbb (negbTE s3neq1) /=.
rewrite -[p]prednK ?prime_gt0 // expgS mulKg.
case/andP => /(Hwp1 _ Hw1) w1_eq1 _.
move/eqP: Hw.
rewrite !w1_eq1 invg1 expg1n !mulg1 mulVg eq_sym -eq_mulgV1 eq_mulVg1.
rewrite -[p]prednK ?prime_gt0 // expgS mulKg.
move/(Hwp1 _ Hw2) => w2_eq1.
move: C7.
rewrite {} w1_eq1 {} w2_eq1  {} w3_eq1 {w1 w2 w3 Hw1 Hw2 Hw3 Hwp1}.
rewrite !(mulg1, mul1g) => C7.
have P0_abelian : abelian P0 by rewrite -defP0 cycle_abelian.
have /eqP : s3 * s1 * s2 = 1.
  have := C7.
  have tiP0Q: P0 :&: Q = 1 by rewrite setIC coprime_TIg ?(coprimegS sP0P).
  pose st := (s ^- 1 * t ^+ 1).
  have -> : t^-1 = st ^-1 * s^-1.
    by rewrite /st -invMg !expg1 mulKVg.
  rewrite -[t ^+ 2](mulKVg (s ^+ 2)).
  set st2 := (s ^-2 * t ^+ 2).
  rewrite 3!invMg -!mulgA.
  move/(canRL (mulKVg _)).
  rewrite [st^-1 * _]conjgC 3!mulgA [st * _]conjgC -[X in _ = X]mulgA.
  move/(canRL (mulgK _)).
  rewrite -[X in _ = X]mulgA.
  move/(canLR (mulKVg _)).
  rewrite [X in _ = X * _]mulgA [_ * (s ^- 2 * _)]conjgC -[X in _ = X]mulgA.
  rewrite -invMg.
  move/(canLR (mulKVg _)).
  have -> : commute s^-1 s2.
    by apply: (centsP P0_abelian); rewrite ?groupV.
  rewrite -[s2 * _ * _]mulgA [s1 * _]mulgA -invMg.
  have -> : commute (s1 * s2) (s * s)^-1.
    by apply: (centsP P0_abelian); rewrite !(groupV, groupM).
  rewrite mulgA expgS expg1 mulgK mulgA => Hs123.
  apply/set1P; rewrite -set1gE -tiP0Q inE {2}Hs123 2?groupM //; last first.
    by rewrite groupV memJ_norm groupV ?HtsQ // (subsetP nQP0).
  rewrite memJ_norm; last by rewrite (subsetP nQP0) // groupV !groupM.
  rewrite groupM //; last by rewrite groupV HtsQ.
  by rewrite memJ_norm ?HtsQ // groupV (subsetP nQP0).
rewrite -eq_invg_mul eq_sym => /eqP s2E.
move/eqP: C7.
rewrite {}s2E {u2 v2 s2 Hu2 Hv2 Hs2 Husv2}.
rewrite [X in _ == X]invMg -(canF_eq (mulKg _)) eq_mulgV1 invgK.
rewrite -conjXg -{1}[s1](mulKg (s ^+ 2)) -conjVg.
rewrite -{1}(_ : (s^-2 * s) ^ s1 = s^-1); last first.
  rewrite invMg mulgKV.
  by apply/conjg_fixP/commgP; apply: (centsP P0_abelian); rewrite ?groupV.
rewrite -{1}[s3](mulgKV s) -{2}[s^-1](_ : s^-1 ^ s3^-1 = _); last first.
  by apply/conjg_fixP/commgP; apply: (centsP P0_abelian); rewrite ?groupV.
rewrite [X in X == _](_ : _ = 
  y^-1 * y ^ s ^- 2 * y^-1 ^ (s1^-1 * s ^- 2) * y ^ (s1^-1 * s^-1) *
  y^-1 ^ (s3 * s^-1) * y ^ s3); last by rewrite !conjgE !invMg !invgK !mulgA.
have sQP0_Q: [~: Q, P0] \subset Q by rewrite commg_subl.
have QP0_abelian : abelian [~: Q, P0].
  by apply: (abelianS sQP0_Q); apply: (abelem_abelian abelQ).
have /subsetP QP0_norm := commg_normr P0 Q.
pose x := y^-1 ^ s3 * y ^ s^-1 * y^-1 ^ (s1^-1 * s^-1) * y.
rewrite [X in X == _](_ : _ = x ^ s^-1 * x^-1); last first.
  rewrite 4!invMg -!conjVg invgK 3!conjMg -3!conjgM mulgA.
  set ysN2 := y ^ (s^-1 * s^-1).
  set yNs1N1sN2 := y^-1 ^ (s1^-1 * s^-1 * s^-1).
  set ys1N1sN1 := y ^ (s1^-1 * s^-1).
  set yNs3sN1 :=  y^-1 ^ (s3 * s^-1).
  set ys3 := y ^ s3.
  rewrite mulgA.
  have -> : commute (yNs3sN1 * ysN2 * yNs1N1sN2 * y ^ s^-1) y^-1.
    by apply: (centsP QP0_abelian);
      rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  rewrite [ys1N1sN1 * _]mulgA.
  have -> : commute ys1N1sN1 (y^-1 ^ s^-1).
    by apply: (centsP QP0_abelian);
      rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  rewrite 3!mulgA conjVg mulgK -[yNs3sN1 * _ * yNs1N1sN2]mulgA.
  rewrite -[X in _ = X * _]mulgA -[yNs3sN1 * _ * ys1N1sN1]mulgA.
  have -> : commute yNs3sN1  (ysN2 * yNs1N1sN2 * ys1N1sN1).
    by apply: (centsP QP0_abelian);
      rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  by rewrite 3!mulgA.
rewrite -eq_mulgV1 => /eqP Hx.
have {Hx} : x == 1.
  apply/eqP/set1P.
  have HxQP0 : x \in [~: Q, P0].
    by rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  have [_ _ _ tiCP0_QP0] := dprodP defQ.
  rewrite -set1gE -tiCP0_QP0 2!inE (subsetP sQP0_Q) HxQP0 //= andbT.
  by rewrite -defP0 -cycleV cent_cycle cent1C !inE conjg_set1 Hx.
pose t1 := s1 ^ y.
pose t3 := s3 ^ y.
have {x} -> : x = s3^-1 * (t3 * t) * (s1 * (t * t1)^-1).
  by rewrite /x conjVg !conjgE !invMg !mulgA !invgK !mulgK !mulgKV.
rewrite -eq_invg_mul invMg invgK => /eqP Hs1s3.
case: (eqVneq (t * t1)^-1 1) => [|Ht1t]; last first.
  suff Utriv u : u \in U -> u = 1.
    by rewrite /goal (Utriv v1) // (Utriv a) // invg1 conj1g conjg1 expgS expg1.
  have Ht1tP1 : (t * t1)^-1 \in P1^#.
    by rewrite 2!inE Ht1t groupV groupM //; apply: mem_imset.
  move => Hu.
  suff : (u ^ s1) ^ (t * t1)^-1 \in U.
    rewrite -mem_conjg HUconj; last by apply: groupM => //; apply: mem_imset.
    rewrite conjgE mulgA => Hus1U.
    have : (s1^-1 == 1) && (s1 == 1) || (u == 1) && (s1^-1 * s1 == 1).
      by apply: not_splitU; rewrite ?groupV.
    rewrite (negbTE s1neq1) andbF /=.
    by case/andP => /eqP.
  have Hs1H : s1 \in H.
    by rewrite -HPU (subsetP (mulG_subl _ _)) // (subsetP sP0P).
  have Hs3H : s3 \in H.
    by rewrite -HPU (subsetP (mulG_subl _ _)) // (subsetP sP0P).
  rewrite -(tiH_P1 Ht1tP1) inE; apply/andP; split; last first.
    apply: mem_imset.
    by rewrite !groupM ?groupV // -HPU (subsetP (mulG_subr _ _)).
  rewrite -conjgM -Hs1s3 conjgM.
  apply: groupM; first by rewrite groupV; apply Hs3H.
  apply: groupM; last by apply Hs3H.
  rewrite -HPU (subsetP (mulG_subr _ _)) // -mem_conjg HUconj //.
  by apply: groupM => //; apply: mem_imset.
move/eqP.
rewrite {Hs1s3 t3 u3 v3 s3 Hu3 Hv3 Hs3 Husv3 s3neq1} -conjMg eq_invg1 conjg_eq1.
rewrite -eq_invg_mul => /eqP Hs1s.
have := moduloP _ _ _ _ _ _ _ Husv1 _ Hu1 Hs1 Hv1.
rewrite groupV; move/(_ Ha) => Hu1v1.
move/(canRL (mulgKV _))/(canLR (mulKg _)) : Husv1.
rewrite -{}Hs1s expg1 !invMg invgK /goal => <-.
rewrite [s * _ ^ _]conjgC.
rewrite mulgA; congr (_ * _); rewrite -!mulgA; congr (_ * (_ * _)).
by rewrite -Hu1v1 mulKg.
Qed.

End AppendixC3.

Fact BGappendixC_inner_subproof : (p <= q)%N.
Proof.
have [y QP0y nUP0y] := nU_P0QP0.
by apply: Einv_gt1_le_pq E_gt1; apply: BGappendixC3_Ediv nUP0y.
Qed.

End ExpandHypotheses.

(* This is B & G, Appendix C, Theorem C. *)
Theorem prime_dim_normed_finField : (p <= q)%N.
Proof.
apply: wlog_neg; rewrite -ltnNge => ltqp.
have [F sigma /isomP[inj_sigma im_sigma] defP0] := fieldH.
case=> sigmaU inj_sigmaU sigmaJ.
have oF: #|F| = (p ^ q)%N by rewrite -cardsT -im_sigma card_injm.
have charFp: p \in [char F] := card_finCharP oF pr_p.
have sP0P: P0 \subset P by rewrite -defP0 subsetIl.
pose s := invm inj_sigma 1%R.
have sigma_s: sigma s = 1%R by rewrite invmK ?im_sigma ?inE.
have{defP0} defP0: <[s]> = P0.
  by rewrite -morphim_cycle /= ?im_sigma ?inE // morphim_invmE.
exact: BGappendixC_inner_subproof defP0 sigmaJ.
Qed.

End AppendixC.
