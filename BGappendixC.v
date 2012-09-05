(* (c) Copyright Microsoft Corporation and Inria. All rights reserved.        *)
Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat seq div fintype.
Require Import tuple finfun bigop ssralg finset prime binomial poly polydiv.
Require Import fingroup morphism quotient automorphism action finalg zmodp.
Require Import gproduct cyclic commutator pgroup abelian frobenius BGsection1.
Require Import matrix mxalgebra mxabelem vector falgebra fieldext galois.
Require Import myfinfield ssrnum algC classfun character integral_char inertia.

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

(* From the negation of the goal of B & G, Appendix C, Theorem C, and Remarks *)
(* (I) and (V).                                                               *)
Hypotheses (odd_p : odd p) (odd_q : odd q) (p'q : q != p).

(* From the fieldH assumption. *)
Variables (fT : finFieldType) (charFp : p \in [char fT]).
Local Notation F := (PrimeCharType charFp).

Variables (sigma : {morphism P >-> F}) (sigmaU : {morphism U >-> {unit F}}).
Hypotheses (inj_sigma : 'injm sigma) (inj_sigmaU : 'injm sigmaU).
Hypothesis (im_sigma : sigma @* P = [set: F]).
Variable s : gT.
Hypotheses (sP0P : P0 \subset P) (sigma_s : sigma s = 1) (defP0 : <[s]> = P0).
Let psi u : F := val (sigmaU u).

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

Let oF : #|F| = (p ^ q)%N.
Proof. by rewrite -cardsT -im_sigma card_injm. Qed.

Let oFp : #|'F_p| = p. Proof. exact: card_Fp. Qed.

Let galF := [splittingFieldType 'F_p of F].

Let dimF : \dim {:galF} = q. Proof. by rewrite primeChar_dimf oF pfactorK. Qed.

Let Fp : {vspace galF} := 1%VS.

Let sigmaP0 : sigma @* P0 =i Fp.
Proof.
rewrite -defP0 morphim_cycle // sigma_s => x.
apply/cycleP/vlineP=> [] [n ->]; first by exists n%:R; rewrite scaler_nat.
by exists (val n); rewrite -{1}[n]natr_Zp -in_algE rmorph_nat zmodXgE.
Qed.

Let nt_s : s != 1%g.
Proof. by rewrite -(morph_injm_eq1 inj_sigma) // sigmaE oner_eq0. Qed.

(* From the nUQ_P0 assumption, and Remarks (X) and (XI). *)
Hypothesis defQ : 'C_Q(P0) \x [~: Q, P0] = Q.
Variables y : gT.
Hypotheses (QP0y : y \in [~: Q, P0]) (nUP0y : P0 :^ y \subset 'N(U)).

Let sQP0Q : [~: Q, P0] \subset Q. Proof. by rewrite commg_subl. Qed.
Let Qy : y \in Q. Proof. by rewrite (subsetP sQP0Q). Qed.

(*
Lemma BG_appendix_C_remark_I : coprime ((p ^ q).-1 %/ p.-1) p.-1.
Proof.
rewrite -coprime_modl.
suff -> : ((p ^ q).-1 %/ p.-1) = q %[mod p.-1].
  by rewrite coprime_modl prime_coprime // BG_appendix_C_q_prime_subproof.
case (leqP p.-1 1%N) => [|H2p].
  by case: p p_prime => [|[|[|]]] //; rewrite !modn1.
rewrite predn_exp mulKn; last by rewrite ltnW.
rewrite -modn_summ -[q in X in _ = X]card_ord -sum1_card.
apply: f_equal2 => //; apply: eq_bigr => i _.
rewrite -modnXm -{1}[p]prednK ?prime_gt0 //.
by rewrite -addn1 modnDl [X in (X ^ _)%N]modn_small // exp1n modn_small.
Qed.
*)

Local Notation Nm := (@galNorm _ galF 1 fullv).
Local Notation uval v := (FinRing.uval v).

(* This is B & G, Appendix C, Remark VII. *)
Let im_psi x : (x \in psi @: U) = (Nm x == 1).
Proof.
have cycFU: cyclic [set: {unit F}] := field_unit_group_cyclic _.
have [u0 defFU] := cyclicP cycFU.
have o_u0: #[u0] = (p ^ q).-1 by rewrite orderE -defFU card_finField_unit oF.
rewrite (imset_comp val) -morphimEdom.
have /set1P[->]: (sigmaU @* U)%G \in [set <[u0 ^+ (#[u0] %/ nU)]>%G].
  rewrite -cycle_sub_group ?inE; last first.
    by rewrite o_u0 -(divnK (dvdn_pred_predX p q)) dvdn_mulr.
  by rewrite -defFU subsetT card_injm //= oU.
rewrite divnA ?dvdn_pred_predX // -o_u0 mulKn //.
have [/= alpha alpha_gen Dalpha] := finField_galois_generator (sub1v {:galF}).
have{Dalpha} Dalpha x1: x1 != 0 -> x1 / alpha x1 = x1^-1 ^+ p.-1.
  move=> nz_x1; rewrite -[_ ^+ _](mulVKf nz_x1) -exprS Dalpha ?memvf // exprVn.
  by rewrite card_vspace dimv1 oFp prednK ?prime_gt0.
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
  rewrite card_injm ?card_finField_unit ?oFp //.
  by apply/injmP=> v1 v2 _ _ []/(fmorph_inj [rmorphism of in_alg F])/val_inj.
have oUU: #|sigmaU @* U| = nU by rewrite card_injm.
rewrite dprodE ?coprime_TIg ?oUU ?oFpU //; last first.
  by apply/centsP=> u1 _ u2 _; apply: val_inj; rewrite /= mulrC.
apply/eqP; rewrite eqEcard subsetT coprime_cardMg oUU oFpU //=.
by rewrite card_finField_unit oF divnK ?dvdn_pred_predX.
Qed.

(* This is B & G, Appendix C, Remark IX. *)
Let frobH : [Frobenius H = P ><| U].
Proof.
apply/Frobenius_semiregularP=> // [||u /setD1P[ntu Uu]].
- rewrite -(morphim_injm_eq1 inj_sigma) // im_sigma.
  exact: (finRing_nontrivial [finRingType of F]).
- rewrite -cardG_gt1 oU ltn_divRL ?dvdn_pred_predX // mul1n -!subn1.
  by rewrite ltn_sub2r ?(ltn_exp2l 0) ?(ltn_exp2l 1) ?prime_gt1 ?prime_gt0.
apply/trivgP/subsetP=> x /setIP[Px /cent1P/commgP].
rewrite inE -!(morph_injm_eq1 inj_sigma) ?(sigmaE, in_PU) //.
rewrite -mulrN1 addrC -mulrDr mulf_eq0 subr_eq0 => /orP[] // /idPn[].
by rewrite (inj_eq val_inj (sigmaU u) 1%g) morph_injm_eq1.
Qed.

Let E := [set x : galF | Nm x == 1 & Nm (2%:R - x) == 1].

Let E_1 : 1 \in E.
Proof. by rewrite !inE -addrA subrr addr0 galNorm1 eqxx. Qed.

Let E_2sub x : (x \in E) = (2%:R - x \in E).
Proof. by rewrite !inE opprB addrA [2%:R + x]addrC addrK andbC. Qed.

Let q_gt2 : (2 < q)%N. Proof. by rewrite odd_geq ?prime_gt1. Qed.

Let inj_psi : {in U &, injective psi}.
Proof. by move=> u v Uu Uv /val_inj/(injmP _ inj_sigmaU)->. Qed.

(* This is B & G, Appendix C, Lemma C.1. *)
Let Einv_gt1_le_pq : E = [set x^-1 | x in E] -> (1 < #|E|)%N -> (p <= q)%N.
Proof.
move=> HEinv; rewrite (cardsD1 1) E_1 add1n ltnS card_gt0.
case/set0Pn => /= a.
rewrite 2!inE => /andP [Ha1 HaE].
pose tau (b : F) := (2%:R - b)^-1.
have HtauE b : b \in E -> tau b \in E.
  by rewrite /tau E_2sub => Hb; rewrite HEinv; apply: mem_imset.
pose tauk k (b : F) := (k%:R - (k%:R - 1) * b) / (k%:R + 1 - k%:R * b).
have Htauk k : tauk k a \in E.
  elim: k {Ha1} a HaE => [|k IH] b HbE.
    by rewrite /tauk !add0r !mul0r !subr0 divr1 mulN1r opprK.
  have H2b0 : (2%:R - b) != 0.
    rewrite -(galNorm_eq0 1 {:galF}).
    by move: HbE; rewrite inE => /andP [_ /eqP ->]; apply: oner_neq0.
  move/HtauE/IH: HbE.
  rewrite /tauk /tau [k.+1%:R]mulrSr addrK.
  rewrite -[X in (X - _) / _](mulfK H2b0) -mulrBl.
  rewrite -[X in _ / (X - _)](mulfK H2b0) -mulrBl.
  rewrite [X in (_ / X)]mulrC invfM mulrA invrK mulfVK //.
  have -> : (k%:R * (2%:R - b) - (k%:R - 1)) = (k%:R + 1 - k%:R * b).
    rewrite mulrBr opprB addrC addrA; congr (_ - _).
    by rewrite mulr2n mulrDr mulr1 addrA subrK addrC.
  suff -> : ((k%:R + 1) * (2%:R - b) - k%:R) = (k%:R + 1 + 1 - (k%:R + 1) * b).
    done.
  rewrite mulrDr mulrN -[X in X = _]addrA [_ - _]addrC addrA; congr (_ - _).
  rewrite [X in X * _]addrC mulr2n mulrDr mulr1 addrA addrK.
  by rewrite [X in X + _]addrC.
pose Gal := 'Gal({:galF} / 1).
pose galPoly := \prod_(x in Gal) (x (1 - a) *: 'X + 1).
have galPoly_roots :
  all (root (galPoly - 1)) [seq in_alg F x | x : 'F_p].
  apply/allP => _ /mapP [k _ ->].
  rewrite rootE !hornerE horner_prod subr_eq0 /=.
  rewrite -[X in X%:A]valZpK -Zp_nat -scalerMnl scale1r.
  apply/eqP.
  pose prod_tau_inv := \prod_(i < k)
    ((i.+1%:R - (i.+1%:R - 1) * a)^-1 / (i.+1%:R + 1 - i.+1%:R * a)^-1).
  transitivity (Nm prod_tau_inv); last first.
    rewrite galNorm_prod.
    apply: big1 => i _.
    have := Htauk i.+1.
    rewrite inE -invfM galNormV.
    by case/andP => /eqP ->; rewrite invr1.
  have -> : prod_tau_inv = k%:R + 1 - k%:R * a.
    rewrite /prod_tau_inv {prod_tau_inv}.
    case: {k} (k : nat) => [|k]; first by rewrite big_ord0 add0r mul0r subr0.
    rewrite big_split big_ord_recl big_ord_recr /=.
    rewrite subrr mul0r subr0 invr1 mul1r invrK.
    rewrite mulrA -(big_split (GRing.mul_comoid galF)) big1 ?mul1r //= => i _.
    rewrite mulrSr addrK invrK mulVf //; apply: contraTneq (Htauk i.+2) => Da.
    by rewrite inE {1}/tauk mulrSr addrK Da mul0r galNorm0 eq_sym oner_eq0.
  have ->: k%:R + 1 - k%:R * a = (1 - a) * k%:R + 1.
    by rewrite mulrBl mul1r mulrC addrAC.
  apply/esym/eq_bigr => i Hi.
  by rewrite !hornerE rmorphD rmorphM rmorphMn rmorph1.
rewrite -ltnS.
have size_galPoly : size galPoly = q.+1.
  have Hfactor (x : {rmorphism F -> F}) : size (x (1 - a) *: 'X + 1) = 2.
    rewrite -mul_polyC size_MXaddC (negbTE (oner_neq0 _)) andbF.
    by rewrite size_polyC fmorph_eq0 subr_eq0 eq_sym (negbTE Ha1).
  rewrite size_prod; last first.
    by move => i _; rewrite -size_poly_eq0 (Hfactor [rmorphism of i]).
  set S := (\sum_(i in Gal) _)%N.
  have -> : S = (\sum_(i in Gal) 2)%N.
    by apply: eq_bigr => i _; apply: (Hfactor [rmorphism of i]).
  rewrite sum_nat_const -add1n mulnC !addnA addn0 addnK add1n.
  have /galois_dim <- := finField_galois (sub1v {:galF}).
  by rewrite dimv1 divn1 dimF.
have size_galPoly1 : size (galPoly - 1) = q.+1.
  by rewrite size_addl // size_opp size_poly1 size_galPoly ltnS prime_gt0.
rewrite -size_galPoly1.
have galPoly1_neq0 : galPoly - 1 != 0.
  by rewrite -size_poly_eq0 size_galPoly1.
rewrite -{1}[p]card_Fp // cardE -(size_map (in_alg galF)).
by apply: max_poly_roots => //; apply/injectiveP; apply: fmorph_inj.
Qed.

(* This is B & G, Appendix C, Lemma C.2. *)
Let E_gt1 : (1 < #|E|)%N.
Proof.
have [q_gt4 | q_le4] := ltnP 4 q.
  pose k1 := enum_rank_in (classes1 H) (s ^: H).
  pose k2 := enum_rank_in (classes1 H) ((s ^+ 2) ^: H).
  pose e := gring_classM_coef k1 k1 k2.
  have cPP: abelian P by rewrite -(injm_abelian inj_sigma) ?zmod_abelian.
  have Hs: s \in H by have /mulG_sub[/subsetP->] := sdprodW defH.
  have DsH n: (s ^+ n) ^: H = (s ^+ n) ^: U.
    rewrite -(sdprodW defH) classM (abelian_classP _ cPP) ?groupX //.
    by rewrite class_support_set1l.
  have injJU: {in U &, injective (conjg s)}.
    by move=> u v Uu Uv eq_s_uv; apply/inj_psi; rewrite ?psiE ?eq_s_uv.
  have ->: #|E| = e.
    rewrite /e /gring_classM_coef !enum_rankK_in ?mem_classes ?groupX //.
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
  have cUU: abelian U.
    rewrite cyclic_abelian // -(injm_cyclic inj_sigmaU) //.
    exact: field_unit_group_cyclic.
  rewrite -ltC_nat; pose chi_s2 i := ('chi[H]_i (s ^+ 2)%g)^*.
  have De: 
    e%:R = #|U|%:R / #|P|%:R * (\sum_i 'chi_i s ^+ 2 * chi_s2 i / 'chi_i 1%g).
    have [k1s k2s2]: s \in enum_val k1 /\ (s ^+ 2)%g \in enum_val k2.
      by rewrite !enum_rankK_in ?class_refl ?mem_classes ?groupX.
    rewrite (gring_classM_coef_sum_eq k1s k1s k2s2); congr (_ * _).
    have ->: #|enum_val k1| = #|U|.
      case/imsetP: (enum_valP k1) k1s => _ _ -> /class_transr <-.
      by rewrite (DsH 1%N) (card_in_imset injJU).
    by rewrite -(sdprod_card defH) mulnC !natrM invfM mulrA mulfK ?neq0CG.
  pose linH := [pred i | P \subset cfker 'chi[H]_i].
  have nsPH: P <| H by have [] := sdprod_context defH.
  have sum_linH (FF : Iirr H -> algC):
      (forall i, 'chi_i \is a linear_char -> FF i = 1) ->
    \sum_(i in linH) FF i = #|U|%:R.
  - move=> FF_1; have isoU: U \isog H / P := sdprod_isog defH.
    rewrite (card_isog isoU); rewrite (isog_abelian isoU) in cUU.
    rewrite -(card_Iirr_abelian cUU) (reindex _ (mod_Iirr_bij nsPH)).
    rewrite -sumr_const; apply: eq_big => [i | i _].
      by rewrite mod_IirrE ?cfker_mod.
    by rewrite FF_1 ?mod_IirrE //; apply/cfMod_lin_char/char_abelianP.
  have degU i: i \notin linH -> 'chi_i 1%g = #|U|%:R.
    case/(Frobenius_Ind_irrP (FrobeniusWker frobH)) => {i}i _ ->.
    rewrite cfInd1 ?normal_sub // -(index_sdprod defH) lin_char1 ?mulr1 //.
    exact/char_abelianP.
  have ub_linH' j:
    coprime j p -> \sum_(i in predC linH) `|'chi_i (s ^+ j)%g| ^+ 2 <= #|P|%:R.
  - move=> co_j_p; have{co_j_p} P1sj: (s ^+ j)%g \in P^#.
      rewrite !inE groupX // -order_dvdn -(order_injm inj_sigma) // sigmaE.
      by rewrite andbT order_primeChar ?oner_neq0 -?prime_coprime 1?coprime_sym.
    have ->: #|P|%:R = #|P|%:R *+ (s ^+ j \in s ^+ j ^: H)%g :> algC.
      by rewrite class_refl.
    have{P1sj} /eqP <-: 'C_H[s ^+ j] == P.
      rewrite eqEsubset (Frobenius_cent1_ker frobH) // subsetI normal_sub //=.
      by rewrite sub_cent1 groupX // (subsetP cPP).
    rewrite -second_orthogonality_relation ?groupX // big_mkcond.
    apply: ler_sum => i _; rewrite -normCK; case: ifP => // _.
    by rewrite exprn_ge0 ?normr_ge0.
  have ub_Pe: `|(#|P| * e)%:R - #|U|%:R ^+ 2| <= #|P|%:R * sqrtC #|P|%:R.
    rewrite natrM De mulrCA mulrA divfK ?neq0CG //.
    rewrite (bigID linH) /= sum_linH => [|i Lchi]; last first.
      rewrite lin_char1 // divr1 /chi_s2 lin_charX // rmorphX -exprMn.
      by rewrite -normCK normC_lin_char ?expr1n.
    rewrite mulrDr addrC addKr mulrC mulr_suml.
    apply: ler_trans (ler_norm_sum _ _ _) _.
    have:= ub_linH' _ (coprime1n p).
    rewrite -(@ler_pmul2r _ (sqrtC #|P|%:R)) ?sqrtC_gt0 ?gt0CG //.
    apply: ler_trans; rewrite mulr_suml ler_sum // => i linH'i.
    rewrite degU // divfK ?neq0CG // normrM -normrX ler_wpmul2l ?normr_ge0 //.
    rewrite -ler_sqr ?qualifE ?sqrtC_ge0 ?normr_ge0 ?ler0n // sqrtCK.
    apply: ler_trans (ub_linH' 2 _); last by rewrite coprime2n.
    rewrite norm_conjC (bigD1 i) //= ler_paddr //.
    by apply: sumr_ge0 => j _; rewrite exprn_ge0 ?normr_ge0.
  rewrite -(ltr_pmul2l (gt0CG P)) mulr1 -natrM.
  move: ub_Pe; rewrite distrC => /(ler_trans (ler_sub_dist _ _)).
  rewrite normrX !normr_nat ler_subl_addr -ler_subl_addl; apply: ltr_le_trans.
  rewrite ltr_subr_addl.
  apply: ler_lt_trans (_ : (p ^ q.-1)%:R ^+ 2 < _); last first.
    rewrite  -!natrX ltC_nat ltn_sqr oU ltn_divRL ?dvdn_pred_predX //.
    rewrite mulnC -subn1 mulnBl mul1n -expnS prednK ?prime_gt0 //.
    by rewrite -!subn1 -(subnKC q_gt4) ltn_sub2l ?(ltn_exp2l 0) // prime_gt1.
  rewrite -natrX -expnM muln2 -subn1 doubleB -addnn -addnBA ?prime_gt1 // subn2.
  rewrite addrC -{1}[_%:R]mulr1 -mulrDr expnD natrM -oP ler_wpmul2l ?ler0n //.
  apply: ler_trans (_ : 3%:R / 2%:R * sqrtC #|P|%:R <= _).
    rewrite mulrAC ler_pdivl_mulr ?ltr0n // [_ * _]mulrC mulrDr !mulr_natl.
    rewrite ler_add2r -ler_sqr ?qualifE ?sqrtC_ge0 ?ler0n // sqrtCK oP -natrX.
    by rewrite leC_nat (@leq_trans (p ^ 2)) ?leq_exp2l ?leq_exp2r ?prime_gt1.
  rewrite -ler_sqr ?rpredM ?rpredV ?qualifE ?sqrtC_ge0 ?ler0n // exprMn sqrtCK.
  apply: ler_trans (_ : (3 * #|P|)%:R <= _).
    by rewrite natrM ler_wpmul2r ?ler0n // -!CratrE; compute.
  rewrite -natrX leC_nat oP -expnM -subn2 muln2 doubleB -addnn.
  rewrite -{2}(subnKC q_gt4) -addnA expnS.
  apply: leq_mul; first by rewrite odd_geq ?prime_gt1.
  by rewrite leq_exp2l ?prime_gt1 ?leq_addl.
have q3: q = 3 by apply/eqP; rewrite eqn_leq q_gt2 andbT -ltnS -(odd_ltn 5).
rewrite (cardsD1 1) E_1 ltnS card_gt0; apply/set0Pn => /=.
pose f' (c : 'F_p) := 'X * ('X - 2%:R%:P) * ('X - c%:P) + ('X - 1).
pose f c := map_poly (in_alg F) (f' c).
have /= Hf0 c : ~~ root (f' c) 0 by rewrite /root !hornerE oppr_eq0 oner_eq0.
have /= Hf2 c : ~~ root (f' c) 2%:R.
  by rewrite /root !{1}(hornerE, subrr) /= addrK oner_neq0.
have /= Hf_root a b d : root (f a) d -> root (f b) d -> a = b.
  move => Hfa Hfb.
  have Hd_neq0 : d != 0.
    apply: contraNneq (Hf0 a).
    by rewrite -(fmorph_root [rmorphism of in_alg F]) rmorph0 => <-.
  have Hd_neq2: d - 2%:R != 0.
    apply: contra (Hf2 a).
    rewrite subr_eq0 -(fmorph_root [rmorphism of in_alg F]).
    by rewrite rmorphMn rmorph1 => /eqP <-.
  move: Hfb Hfa; rewrite /root => /eqP <-.
  rewrite /f !{1}[map_poly _ _]rmorphD !{1}rmorphM !{1}rmorphB /=.
  rewrite map_polyX !map_polyC /= -in_algE rmorphMn rmorph1 !hornerE /=.
  rewrite 2!(can_eq (addrK _)) -!mulrA.
  rewrite (can_eq (mulKf Hd_neq0)) (can_eq (mulKf Hd_neq2)).
  rewrite (can_eq (addKr _)) eqr_opp -!in_algE (inj_eq (fmorph_inj _)).
  by apply/eqP.
case: (boolP [forall c, exists d, root (f' c) d]).
  move/forallP=> /(_ _)/existsP/=/fin_all_exists[ch f'ch0].
  suffices /injF_bij[chinv _ chinvK] : injective ch.
    by have /idPn[] := f'ch0 (chinv 0); rewrite chinvK Hf0.
  move=> a b Hab; apply: (Hf_root _ _ (ch a)%:A).
    by rewrite fmorph_root f'ch0.
  by rewrite Hab fmorph_root f'ch0.
rewrite negb_forall => /existsP/=[c]; rewrite negb_exists => /forallP/=Hc.
have size_fcr : size ('X * ('X - 2%:R%:P) * ('X - c%:P)) = 4.
  rewrite -mulrA mulrC size_mulX ?mulf_eq0 ?polyXsubC_eq0 //.
  by rewrite size_mul ?polyXsubC_eq0 // !size_XsubC.
have size_fc : size (f' c) = 4.
  by rewrite size_addl ?size_XsubC size_fcr.
have fc_monic : f' c \is monic.
  rewrite monicE lead_coefDl ?size_XsubC ?size_fcr //.
  by rewrite -monicE !monicMl ?monicXsubC ?monicX.
have {size_fcr} fc_irr : irreducible_poly (f' c).
  by apply: cubic_irreducible; first rewrite size_fc.
suff /existsP [a Ha] : [exists a, root (f c) a].
  have fc_over1 : f c \is a polyOver 1%AS.
    by apply/polyOverP => i; rewrite coef_map /= memvZ // mem1v.
  have /eqP fc_min : minPoly 1 a == f c.
    rewrite -eqp_monic ?monic_minPoly ?monic_map //.
    have := minPoly_dvdp fc_over1 Ha.
    have := size_minPoly 1 a.
    suff [r <-] : {r | map_poly (in_alg F) r = minPoly 1 a}.
      rewrite size_map_poly dvdp_map eqp_map => Hsize.
      by apply: fc_irr; rewrite Hsize.
    set p_a := minPoly 1 a; rewrite -[p_a]coefK.
    have rP i: {b | p_a`_i = b%:A}.
      exact/sig_eqW/vlineP/(polyOverP (minPolyOver 1 a)).
    exists (\poly_(i < size p_a) sval (rP i)); apply/polyP=> i.
    by rewrite coef_map !coef_poly; case: (rP i); case: ifP; rewrite ?raddf0.
  have Hgalois := finField_galois (sub1v {:galF}).
  have card_gal : #|'Gal({:galF} / 1)| = 3.
    by rewrite -(galois_dim Hgalois) dimv1 divn1 dimF.
  have fc_factor : f c = \prod_(x in 'Gal({:galF} / 1)) ('X - (x a)%:P).
    rewrite -fc_min.
    have : size (minPoly 1 a) = (\dim_(1%AS : {vspace F}) {:galF}).+1.
      by rewrite fc_min size_map_poly size_fc dimv1 divn1 dimF q3.
    have/galois_factors [_] := Hgalois.
    case/(_ _ (memvf a)) => r [Hr /map_uniq Hr_uniq ->].
    rewrite big_map size_prod_XsubC big_uniq //=.
    case => size_r.
    move/card_uniqP: Hr_uniq; rewrite size_r (galois_dim Hgalois) => card_r.
    apply: eq_bigl.
    by apply/(subset_cardP card_r).
  exists a; rewrite !inE; apply/and3P; split.
  - apply: contraTneq Ha => ->.
    by rewrite -[1]scale1r fmorph_root; apply Hc.
  - rewrite -eqr_opp; apply/eqP.
    have -> : -1 = (f c).[in_alg _ 0].
      by rewrite horner_map !hornerE rmorphN rmorph1.
    rewrite rmorph0 -mulN1r.
    have -> : -1 = (-1) ^+ #|'Gal({:galF} / 1)| :> F.
      by rewrite card_gal -signr_odd expr1.
    rewrite -prodrN fc_factor horner_prod.
    by apply: eq_bigr => i _; rewrite !hornerE.
  - apply/eqP.
    transitivity (f c).[in_alg _ 2%:R]; last first.
      by rewrite horner_map !hornerE /= subrr mulr0 mul0r add0r addrK scale1r.
    rewrite fc_factor horner_prod.
    by apply: eq_bigr => i _; rewrite rmorphB !rmorphMn !rmorph1 !hornerE.
suff : ~~ coprimep (f' c) ('X ^+ #|{:F}| - 'X).
  apply: contraR; rewrite negb_exists => /forallP Hroot.
  rewrite -(coprimep_map [rmorphism of (in_alg F)]) -gcdp_eqp1 -/(f c).
  rewrite rmorphB /= map_polyXn map_polyX (finField_genPoly fT).
  have /dvdp_prod_XsubC [m Hm] := dvdp_gcdr (f c) (\prod_x ('X - x%:P)).
  rewrite (eqp_trans Hm) // /eqp dvd1p andbT uniq_roots_dvdp //; last first.
    by rewrite uniq_rootsE mask_uniq // /index_enum /= -enumT enum_uniq.
  apply/allP => x.
  rewrite -root_prod_XsubC -(eqp_root Hm) root_gcd.
  by rewrite -[root (f c) x]negbK Hroot.
case/irredp_FAdjoin: fc_irr => L dimL [z Hz H1z].
rewrite -(coprimep_map [rmorphism of in_alg L]).
rewrite rmorphB /= map_polyXn map_polyX.
move: (map_poly _ _) Hz => r root_r.
suffices: ('X^#|{:F}| - 'X).[z] == 0 by apply: contraL => /coprimep_root->.
rewrite oF q3 !(hornerE, hornerXn) subr_eq0.
pose fL := FinSplittingFieldType 'F_p (FinFieldExtType L).
have <-: #|{: fL}%VS| = (p ^ 3)%N by rewrite card_vspace oFp dimL size_fc.
by rewrite card_vspacef (expf_card (z : fL)).
Qed.

Let t := s ^ y.
Let P1 := P0 :^ y.

Import GroupScope.

Let BG_appendix_C3_1 x : x \in H ->
  exists u, exists v, exists s1, 
  [/\ u \in U, v \in U, s1 \in P0 & x = u * s1 * v].
Proof.
case/(mem_sdprod defH) => s' [u' [Hs' Hu' -> _]].
case: (eqVneq s' 1) => [Hs1|Hs_neq1].
  exists u', 1, 1.
  by split => //; rewrite !mulg1 Hs1 mul1g.
have Hsigma_s' : sigma s' \is a GRing.unit.
  by rewrite unitfE (morph_injm_eq1 inj_sigma).
have /(mem_dprod defFU)[]: FinRing.unit F Hsigma_s' \in setT := in_setT _.
move=> _ [w [/morphimP[u Uu _ ->] Fp_w /(congr1 val)/= Ds' _]].
have{Fp_w Ds'} [n Ds']: exists n, sigma s' = sigma ((s ^+ n) ^ u).
  move: Fp_w; rewrite {}Ds' inE => /vlineP[n ->]; exists n.
  by rewrite -{1}(natr_Zp n) scaler_nat mulr_natr conjXg !sigmaE ?in_PU.
exists u^-1, (u * u'), (s ^+ n); rewrite ?in_group // mulgA -[_ * u]mulgA.
by split=> //; congr (_ * _); apply: (injmP _ inj_sigma); rewrite ?in_PU.
Qed.

Let BG_appendix_C3_2 s1 s2 u :
  s1 \in P0 -> s2 \in P0 -> u \in U -> s1 * u * s2 \in U ->
  (s1 == 1) && (s2 == 1) || (u == 1) && (s1 * s2 == 1).
Proof.
move=> Hs1 Hs2 Hu; have [_ _ _ HPUI] := sdprodP defH.
have Hs1P := subsetP sP0P _ Hs1.
have Hs2P := subsetP sP0P _ Hs2.
case: (boolP (s1 == 1)) => [/eqP ->|Hs1_neq1].
  by rewrite mul1g groupMl // -in_set1 -[[set 1]]HPUI inE Hs2P => ->.
case: (boolP (s2 == 1)) => [/eqP ->|Hs2_neq1].
  rewrite mulg1 groupMr // => Hs1U.
  move: Hs1_neq1.
  by rewrite -in_set1 -[[set 1]]HPUI inE Hs1U Hs1P.
move => Hs1us2.
suff /eqP Hu1 : u == 1.
  rewrite Hu1 eqxx /= -in_set1 -[[set 1]]HPUI inE groupM //=.
  move: Hu1 Hs1us2 ->.
  by rewrite mulg1.
rewrite -(morph_injm_eq1 inj_sigmaU) // -in_set1 -set1gE.
have [_ _ _ <-] := dprodP defFU; rewrite !inE mem_morphim //= -/(psi u).
have : s1 ^ u * s2 == 1.
  rewrite -in_set1 -[[set 1]]HPUI inE // groupMr // in_PU //=.
  by rewrite -mulgA groupMl ?groupV.
rewrite -(morph_injm_eq1 inj_sigma) ?(in_PU, sigmaE) // addr_eq0 => /eqP.
move/(canRL (mulKf _))->; last by rewrite morph_injm_eq1.
by rewrite mulrC rpred_div ?rpredN //= -/Fp -sigmaP0 mem_morphim.
Qed.

Let BG_appendix_C3_3 t1 : t1 \in P1^# -> H :&: H :^ t1 = U.
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
have oP0: #|P0| = p.
  by rewrite -(card_injm inj_sigma) // (eq_card sigmaP0) card_vspace oFp dimv1.
have{nHt1} nHP1: P1 \subset 'N(H).
  apply: prime_meetG; first by rewrite cardJg oP0.
  by apply/trivgPn; exists t1; rewrite // inE P1t1.
have{nHP1} nPP1: P1 \subset 'N(P).
  have /Hall_pi hallP: Hall H P by apply: Frobenius_ker_Hall frobH.
  by rewrite -(normal_Hall_pcore hallP nsPH) (char_norm_trans (pcore_char _ _)).
have p'Q: p^'.-group Q by apply: pi_pgroup (abelem_pgroup abelQ) _.
have pP: p.-group P by rewrite /pgroup oP pnat_exp ?pnat_id.
have coPQ: coprime #|P| #|Q| by rewrite (pnat_coprime pP).
have sylP0: p.-Sylow(Q <*> P0) P0.
  rewrite /pHall -divgS joing_subr ?(pgroupS sP0P) //=.
  by rewrite joingC norm_joinEl // coprime_cardMg ?(coprimeSg sP0P) ?mulKn.
have sP1QP0: P1 \subset Q <*> P0.
  by rewrite conj_subG ?joing_subr ?mem_gen // inE Qy.
have nP10: P1 \subset 'N(P0).
  have: P1 \subset 'N(P :&: (Q <*> P0)) by rewrite normsI // normsG.
  by rewrite norm_joinEr // -group_modr // coprime_TIg // mul1g.
have eqP10: P1 :=: P0.
  apply/eqP; rewrite eqEcard cardJg leqnn andbT.
  rewrite (comm_sub_max_pgroup (Hall_max sylP0)) //; last exact: normC.
  by rewrite pgroupJ (pHall_pgroup sylP0).
have /idPn[] := prime_gt1 pr_p.
rewrite -oP0 cardG_gt1 negbK -subG1 -(Frobenius_trivg_cent frobH) subsetI sP0P.
apply/commG1P/trivgP; rewrite -tiPU commg_subI // subsetI ?subxx //.
by rewrite sP0P -eqP10.
Qed.
  
Let Einv : E = [set (x^-1)%R | x in E].
Proof.
have HtP1 : t \in P1 by rewrite memJ_conjg.
have cUU: abelian U.
  rewrite cyclic_abelian // -(injm_cyclic inj_sigmaU) //.
  exact: field_unit_group_cyclic.
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
  rewrite 8?{1}sigmaE ?memJ_P // mul1r => /(canLR (addrK _))->.
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
case: (@BG_appendix_C3_1 (s ^+ k.-2 * a^-1 ^ t ^+ k * s ^- k.-1))
    => [|u1 [v1 [s1 [Hu1 Hv1 Hs1 Husv1]]]].
  by apply: C5inH; rewrite groupV.
case: (@BG_appendix_C3_1 (s ^+ k * (a * b^-1) ^ t ^+ k.-1 * s ^- k.-2))
    => [|u2 [v2 [s2 [Hu2 Hv2 Hs2 Husv2]]]].
  by apply: C5inH; rewrite groupM ?groupV //.
case: (@BG_appendix_C3_1 (s ^+ k.-1 * b ^ t ^+ k.-2 * s ^- k))
  => [|u3 [v3 [s3 [Hu3 Hv3 Hs3 Husv3]]] {C5inH}].
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
  case/(BG_appendix_C3_2 Hsm Hsn Hut)/orP.
    by move: HmVn; rewrite -negb_and; case: (_ && _).
  by rewrite -eq_mulgV1 andbC; case: (s ^+ _ == _) Hmn.
have ss_neq_1 : s ^+ 2 != 1.
  rewrite -order_dvdn.
  apply/prime_nt_dvdP => //; first by rewrite order_eq1.
  apply/eqP.
  case: (eqVneq #[s] 2) (order_dvdG Ps) => [->|//].
  by rewrite oP dvdn2 odd_exp odd_p orbT.
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
  rewrite [_ \in _]Fermat's_little_theorem card_vspace dimv1 oFp => /eqP->.
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
  apply: BG_appendix_C3_2; rewrite ?groupV //.
  - by rewrite groupM ?groupV ?groupX. 
  have Ht2 : t ^+ 2 \in P1^#.
    by rewrite 2!inE groupX // andbT -conjXg conjg_eq1.
  rewrite [X in X \in _](_ : _ =  s1 * w3 ^+ p * (s1 * w3)^-1);
    last by rewrite !invMg !mulgA.
  rewrite -(BG_appendix_C3_3 Ht2) inE -{2}Hw {Hw}.
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
  apply: BG_appendix_C3_2; rewrite ?groupV //.
  - by rewrite groupM ?groupV ?groupX.
  rewrite !mulgA Hw.
  by rewrite groupM ?groupV ?groupX.
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
  have tiP0Q: P0 :&: Q = 1.
    have pP: p.-group P by rewrite /pgroup oP pnat_exp ?pnat_id.
    have p'Q: p^'.-group Q by apply: (pi_pgroup (abelem_pgroup abelQ)).
    by rewrite coprime_TIg ?(pnat_coprime (pgroupS sP0P pP)).
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
      by apply: BG_appendix_C3_2; rewrite ?groupV.
    rewrite (negbTE s1neq1) andbF /=.
    by case/andP => /eqP.
  have Hs1H : s1 \in H.
    by rewrite -HPU (subsetP (mulG_subl _ _)) // (subsetP sP0P).
  have Hs3H : s3 \in H.
    by rewrite -HPU (subsetP (mulG_subl _ _)) // (subsetP sP0P).
  rewrite -(BG_appendix_C3_3 Ht1tP1) inE; apply/andP; split; last first.
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

Lemma BG_appendix_C_main : (p <= q)%N.
Proof. exact: Einv_gt1_le_pq Einv E_gt1. Qed.

End ExpandHypotheses.

Theorem BG_appendix_C : (p <= q)%N.
Proof.
apply: wlog_neg; rewrite -ltnNge => ltqp.
have p'q: q != p by rewrite ltn_eqF.
have [-> | p_odd] := even_prime pr_p; first by rewrite prime_gt1.
have q_odd: odd q.
  set r := p.-1.
  have r_gt0: (0 < r)%N by rewrite /r -subn1 subn_gt0 prime_gt1.
  suffices eq_nU_q: nU = q %[mod r].
    have:= coUp1; rewrite -coprime_modl eq_nU_q coprime_modl /r.
    rewrite -[p]odd_double_half p_odd -mul2n coprime_mulr coprimen2.
    by case/andP.
  rewrite /nU -/r -(prednK (prime_gt0 pr_p)) -/r -add1n expnDn.
  rewrite -(prednK (prime_gt0 pr_q)) 2!big_ord_recl !exp1n /=.
  rewrite prednK ?prime_gt0 // bin1 mul1n expn1 divnMDl // addnC.
  elim/big_rec: _ => [|i s _ IHi]; first by rewrite div0n.
  by rewrite exp1n mul1n !expnSr !mulnA divnMDl // -addnA modnMDl.
have [F sigma /isomP[inj_sigma im_sigma] defP0] := fieldH.
case=> sigmaU inj_sigmaU sigmaJ.
have oF: #|F| = (p ^ q)%N by rewrite -cardsT -im_sigma card_injm.
have charFp: p \in [char F] := card_finCharP oF pr_p.
have sP0P: P0 \subset P by rewrite -defP0 subsetIl.
pose s := invm inj_sigma 1%R.
have sigma_s: sigma s = 1%R by rewrite invmK ?im_sigma ?inE.
have{defP0} defP0: <[s]> = P0.
  by rewrite -morphim_cycle /= ?im_sigma ?inE // morphim_invmE.
have pP: p.-group P by rewrite /pgroup oP pnat_exp ?pnat_id.
have p'Q: p^'.-group Q by rewrite (pi_pgroup (abelem_pgroup abelQ)).
have defQ: 'C_Q(P0) \x [~: Q, P0] = Q.
  rewrite dprodC coprime_abelian_cent_dprod // ?(abelem_abelian abelQ) //.
  by rewrite (coprimegS sP0P) ?(p'nat_coprime p'Q).
have [_ /(mem_dprod defQ)[z [y [/setIP[_ cP0z] QP0y -> _]]]] := nU_P0Q.
rewrite conjsgM (normsP (cent_sub P0)) // => nU_P0y.
exact: BG_appendix_C_main defP0 sigmaJ defQ y QP0y nU_P0y.
Qed.

End AppendixC.
