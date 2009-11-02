Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent maximal hall.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import GroupScope.

Import GRing.Theory FiniteModule.

Section Transfer.

Variables (gT aT : finGroupType) (G H : {group gT}). 
Variable alpha : {morphism H >-> aT}.

Hypotheses (sHG : H \subset G) (abelA : abelian (alpha @* H)).

Lemma transfer_morph_subproof : H \subset alpha @*^-1 (alpha @* H).
Proof. by rewrite -sub_morphim_pre. Qed.

Let fmalpha := restrm transfer_morph_subproof (fmod abelA \o alpha).

Let V X g := \sum_(Hx \in rcosets H G) fmalpha (X Hx * g * (X (Hx :* g))^-1).

Definition transfer g := V repr g.

(* Aschbacher 37.2 *)
Lemma transferM : {in G &, {morph transfer : x y / (x * y)%g >-> x + y}}.
Proof.
move=> s t Gs Gt /=.
rewrite [transfer t](reindex_acts 'Rs _ Gs) ?actsRs_rcosets //= -big_split /=.
apply: eq_bigr => C; case/rcosetsP=> x Gx ->{C}; rewrite !rcosetE -!rcosetM.
rewrite -[_ + _]morphM -?mem_rcoset; first by rewrite !mulgA mulgKV rcosetM.
  by rewrite rcoset_repr rcosetM mem_rcoset mulgK mem_repr_rcoset.
by rewrite rcoset_repr (rcosetM _ _ t) mem_rcoset mulgK mem_repr_rcoset.
Qed.

Canonical Structure transfer_morphism :=
  @Morphism gT (subFinGroupType _) G transfer transferM.

Lemma transfer1 : transfer 1 = 0. Proof. exact: morph1. Qed.

Lemma transferV : {in G, {morph transfer: x / x^-1%g >-> - x}}. Proof. exact: morphV. Qed.

Lemma transferX : forall n, {in G, {morph transfer: x / (x ^+ n)%g >-> x *+ n}}.
Proof. exact: morphX. Qed.

Definition coset_transversal X := {in rcosets H G, forall Hx : {set gT}, X Hx \in Hx}.

(* Aschbacher 37.1 *)
Lemma transfer_indep : forall X, coset_transversal X -> {in G, transfer =1 V X}.
Proof.
move=> X repsX g Gg.
apply: (@addrI _ (\sum_(Hx \in rcosets H G) fmalpha (repr Hx * (X Hx)^-1))).
rewrite {1}(reindex_acts 'Rs _ Gg) ?actsRs_rcosets // -!big_split /=.
apply: eq_bigr => Hx; case/rcosetsP=> x Gx ->{Hx}; rewrite !rcosetE -!rcosetM.
case: repr_rcosetP => h1 Hh1; case: repr_rcosetP => h2 Hh2.
have: H :* (x * g) \in rcosets H G by rewrite -rcosetE mem_imset ?groupM.
have: H :* x \in rcosets H G by rewrite -rcosetE mem_imset.
move/repsX; case/rcosetP=> h3 Hh3 ->; move/repsX; case/rcosetP=> h4 Hh4 ->.
rewrite -!(mulgA h1) -!(mulgA h2) -!(mulgA h3) !(mulKVg, invMg).
by rewrite addrC -![_ + _]morphM ?groupM ?groupV // -!mulgA !mulKg.
Qed.

(* The next few lemmas have to do with picking representatives of orbits
   of cosets and representatives of those representatives. Are there ways
   to eliminate them and streamline the proofs below? *)

Section FactorTransfer.

Variable g : gT.
Hypothesis Gg : g \in G.

(* ccycle Hx is the cycle of coset Hx under g *)
Let ccycle := pcycle (actperm 'Rs g).
Let ccycles := ccycle @: (rcosets H G).

(* the cycle of coset Hx under g, as a sequence starting with Hx *)
Let ccycle_seq Hx:= traject (actperm 'Rs g) Hx #|ccycle Hx|.

Lemma repr_ccycle : forall Hx, repr (ccycle Hx) \in ccycle Hx.
Proof. by move=> Hx; apply: mem_repr (pcycle_id _ _). Qed.

Lemma ccycle_rcoset : forall Hx Hy,
  Hy \in ccycle Hx -> Hx \in rcosets H G -> Hy \in rcosets H G.
Proof.
move=> Hx Hy; case/imsetP=> pgi; rewrite -morphim_cycle ?inE //.
case/morphimP=> gi _ g_gi ->{pgi}; rewrite actpermK => ->{Hy} HG_Hx.
rewrite (actsP (actsRs_rcosets _ _)) //.
by apply: subsetP g_gi; rewrite cycle_subG.
Qed.

Lemma repr_repr_ccycle : forall Hx,
  Hx \in rcosets H G -> repr (repr (ccycle Hx)) \in repr (ccycle Hx).
Proof.
move=> Hx; move/(ccycle_rcoset (repr_ccycle Hx)); case/rcosetsP=> x Gx ->{Hx}.
exact: mem_repr_rcoset.
Qed.

Lemma repr_repr_ccycle2 : forall C, C \in ccycles -> repr (repr C) \in G.
Proof.
move=> C; case/imsetP=> Hx HG_Hx ->{C}; apply: subsetP (repr_repr_ccycle HG_Hx).
move/(ccycle_rcoset (repr_ccycle Hx)): HG_Hx; case/rcosetsP=> x Gx ->{Hx}.
by rewrite mul_subG ?sub1set.
Qed.

(* a particular choice of coset representatives *)
Let transX Hx :=
  let Hy := repr (ccycle Hx) in repr Hy * g ^+ index Hx (ccycle_seq Hy).

Lemma coset_transversal_transX : coset_transversal transX.
Proof.
rewrite /transX => Hx HG_Hx /=; have [x Gx defHx] := rcosetsP HG_Hx.
have [y Gy] := rcosetsP (ccycle_rcoset (repr_ccycle Hx) HG_Hx).
set Hy := repr (ccycle Hx); set i := index _ _ => defHy.
have cycHy: ccycle Hy = ccycle Hx by apply: orbit_transl; rewrite repr_ccycle.
have Hy_Hx : Hx \in ccycle_seq Hy.
  by rewrite -pcycle_traject [pcycle _ _]cycHy pcycle_id.
have lt_i := Hy_Hx; rewrite -index_mem -/i in lt_i.
rewrite defHx rcoset_sym rcosetM defHy rcoset_repr -defHy.
rewrite  -rcosetE -actpermE morphX ?inE // permX.
by rewrite  -(nth_traject _ lt_i) size_traject nth_index // defHx rcoset_refl.
Qed.

Lemma transfer_eq1 : forall C,
  C \in ccycles -> g ^+ #|C| ^ (repr (repr C))^-1 \in H.
Proof.
move=> C; case/imsetP=> Hx HG_Hx ->{C}.
have [y Gy] := rcosetsP (ccycle_rcoset (repr_ccycle Hx) HG_Hx).
set Hy := repr (ccycle Hx) => defHy.
have <-: ccycle Hy = ccycle Hx by apply: orbit_transl; rewrite repr_ccycle.
rewrite -mem_lcoset -memV_rcosetV invMg !invgK defHy rcoset_repr -defHy.
rewrite -mem_rcoset -rcosetE -actpermE morphX ?inE // permX iter_pcycle.
by rewrite defHy mem_repr_rcoset.
Qed.

Lemma transfer_eq2 : (\sum_(C \in ccycles) #|C|)%N = #|G : H|.
Proof.
rewrite /ccycles /ccycle pcycleE acts_sum_card_orbit //= -morphim_cycle ?inE //.
apply/subsetP=> px; case/morphimP=> x _ gx ->{px}.
apply/astabsP=> Hy; rewrite /= actpermK (actsP (actsRs_rcosets _ _)) //.
by apply: subsetP gx; rewrite cycle_subG.
Qed.

Lemma transfer_eq : 
  transfer g = \sum_(C \in ccycles) fmalpha (g ^+ #|C| ^ (repr (repr C))^-1).
Proof.
rewrite (transfer_indep coset_transversal_transX Gg).
rewrite [V _ _](partition_big_imset ccycle) /=; apply: eq_bigr => C.
case/imsetP=> Hx HG_Hx ->{C}; set Hy := repr (ccycle Hx).
have cycHy: ccycle Hy = ccycle Hx by apply: orbit_transl; rewrite repr_ccycle.
rewrite (eq_bigl (mem (ccycle_seq Hy))) /ccycle_seq => [|D] /=; last first.
  rewrite -pcycle_traject eq_pcycle_mem -/ccycle cycHy andbC.
  by case cycD: (D \in ccycle Hx) => //; exact: ccycle_rcoset cycD _.
case def_n: {-}#|_| => [|n]; first by rewrite (cardD1 Hy) pcycle_id in def_n.
have UcycHy: uniq (ccycle_seq Hy) := uniq_traject_pcycle _ _.
have transXE: forall i, i <= n -> transX (Hy :* g ^+ i)%g = repr Hy * g ^+ i.
  move=> i; rewrite -ltnS -def_n  -rcosetE -actpermE morphX ?inE // => lt_i.
  rewrite /transX [ccycle _]pcycle_perm [pcycle _ _]cycHy -/Hy permX.
  by rewrite -(nth_traject _ lt_i) index_uniq ?size_traject.
rewrite -big_uniq {UcycHy}//= conjgE invgK -cycHy -{1}[Hy]rcoset1 -{1}(expg0 g).
rewrite def_n; elim: {1 3}n 0%N (addn0 n) => [|m IHm] i def_i /=.
  rewrite big_cons big_nil addr0 {i}[i]def_i transXE // -(mulgA _ _ g) -rcosetM.
  rewrite -expgSr -rcosetE -actpermE morphX ?inE // permX // -def_n iter_pcycle.
  by rewrite mulgA -{3}[Hy]rcoset1 (transXE 0%N) ?mulg1.
rewrite big_cons transXE; last by rewrite -def_i leq_addl.
rewrite permE /= rcosetE -rcosetM -(mulgA _ _ g) -expgSr.
rewrite addSnnS in def_i; rewrite transXE; last by rewrite -def_i leq_addl.
by rewrite mulgV [fmalpha 1]morph1 add0r IHm.
Qed.

End FactorTransfer.

End Transfer.

Section Focal_Subgroup.

Variable gT : finGroupType.
Variables (G S : {group gT}) (p : nat).
Hypothesis sylS : p.-Sylow(G) S.

Theorem focal_subgroup_gen :
  S :&: G^`(1) = <<[set [~ x, u] | x <- S, u <- G, x ^ u \in S]>>.
Proof.
set K := <<_>>; set G' := G^`(1); have [sSG coSiSG] := andP (pHall_Hall sylS).
apply/eqP; rewrite eqEsubset gen_subG andbC; apply/andP; split.
  apply/subsetP=> xu; case/imset2P=> x u Sx; case/setIdP=> Gu Sxu ->{xu}.
  by rewrite inE groupM ?groupV // mem_commg // (subsetP sSG).
apply/subsetP=> g; case/setIP=> Sg G'g; have Gg := subsetP sSG g Sg.
have nKS: S \subset 'N(K).
  rewrite norms_gen //; apply/subsetP=> y Sy; rewrite inE.
  apply/subsetP=> xuy; case/imsetP=> xu; case/imset2P=> x u Sx.
  case/setIdP=> Gu Sxu ->{xu} ->{xuy}; rewrite conjRg mem_imset2 ?groupJ //.
  by rewrite inE -conjJg /= 2?groupJ // (subsetP sSG).
set alpha := restrm_morphism nKS (coset_morphism K).
have alphim: (alpha @* S) = (S / K) by rewrite morphim_restrm setIid.
have abelSK : abelian (alpha @* S).
  rewrite alphim sub_der1_abelian // genS //.
  apply/subsetP=> xy; case/imset2P=> x y Sx Sy ->{xy}.
  by rewrite mem_imset2 // inE (subsetP sSG) ?groupJ.
set ker_trans := 'ker (transfer G abelSK : _ -> subg_of _).
have G'ker : G' \subset ker_trans.
  rewrite gen_subG; apply/subsetP=> h; case/imset2P=> h1 h2 Gh1 Gh2 ->{h}.
  rewrite !inE groupR // morphR //; apply/commgP.
  exact: (addrC (transfer _ _ _)).
have transg0: transfer G abelSK g = 0.
  by move/kerP: (subsetP G'ker g G'g); apply.
have gGSeq0: fmod abelSK (alpha g) *+ #|G : S| = 0. 
  rewrite -transg0 (transfer_eq abelSK Gg) -(transfer_eq2 S Gg).
  rewrite -GRing.sumr_muln_r /restrm.
  apply: eq_bigr=> cyc cyccyc; rewrite -[_ *+ _]morphX ?mem_morphim //=.
  rewrite -morphX //= /restrm; congr fmod.
  apply/rcoset_kercosetP; rewrite /= -/K. 
  - by rewrite (subsetP nKS) ?groupX.
  - by rewrite (subsetP nKS) ?(transfer_eq1 Gg).
  rewrite mem_rcoset -{1}[g ^+ _]invgK -conjVg -commgEl mem_gen ?mem_imset2 //.
    by rewrite groupV groupX.
  by rewrite inE conjVg !groupV (transfer_eq1 Gg) ?(repr_repr_ccycle2 sSG Gg).
move: (congr_fmod gGSeq0).
rewrite fmval0 morphX ?inE //= fmodK ?mem_morphim // /restrm /=.
move/((congr1 (expgn^~ (expgn_inv (S / K) #|G : S|))) _).
rewrite exp1gn expgnK ?mem_quotient ?coprime_morphl // => Kg1.
by rewrite coset_idr ?(subsetP nKS).
Qed.

Theorem Burnside_normal_complement :
  'N_G(S) \subset 'C(S) -> 'O_p^'(G) ><| S = G.
Proof.
move=> cSN; set K := 'O_p^'(G); have [sSG pS _] := and3P sylS.
have [p'K]:  p^'.-group K /\ K <| G by rewrite pcore_pgroup pcore_normal.
case/andP=> sKG nKG; have{nKG} nKS := subset_trans sSG nKG.
have{pS p'K} tiKS: K :&: S = 1 by rewrite setIC coprime_TIg ?(pnat_coprime pS).
suffices{tiKS nKS} hallK: p^'.-Hall(G) K.
  rewrite sdprodE //= -/K; apply/eqP; rewrite eqEcard ?mul_subG //=.
  by rewrite TI_cardMg //= (card_Hall sylS) (card_Hall hallK) mulnC partnC. 
pose G' := G^`(1); have nsG'G : G' <| G by rewrite der_normal.
suffices{K sKG} p'G': p^'.-group G'.
  have nsG'K: G' <| K by rewrite (normalS _ sKG) ?pcore_max.
  rewrite -(pquotient_pHall p'G') -?pquotient_pcore //= -/G'.
  by rewrite nilpotent_pcore_Hall ?abelian_nil ?der_abelian.
suffices{nsG'G} tiSG': S :&: G' = 1.
  have sylG'S : p.-Sylow(G') (G' :&: S) by rewrite (pSylow_normalI _ sylS).
  rewrite /pgroup -[#|_|](partnC p) ?cardG_gt0 // -{sylG'S}(card_Hall sylG'S).
  by rewrite /= setIC tiSG' cards1 mul1n pnat_part.
apply/trivgP; rewrite /= focal_subgroup_gen ?(p_Sylow sylS) // gen_subG.
apply/subsetP=> z; case/imset2P=> x u Sx; case/setIdP=> Gu Sxu ->{z}.
have cSS: forall y, y \in S -> S \subset 'C_G[y].
  move=> y; rewrite subsetI sSG -cent_set1 centsC sub1set; apply: subsetP.
  by apply: subset_trans cSN; rewrite subsetI sSG normG.
have{cSS} [v]: exists2 v, v \in 'C_G[x ^ u | 'J] & S :=: S :^ u :^ v.
  have sylSu : p.-Sylow(G) (S :^ u) by rewrite pHallJ.
  have [sSC sCG] := (cSS _ Sxu, subsetIl G 'C[x ^ u]).
  rewrite astab1J; apply: (@Sylow_trans p); apply: pHall_subl sCG _ => //=.
  by rewrite -conjg_set1 normJ -(conjGid Gu) -conjIg conjSg cSS.
rewrite in_set1 -conjsgM; case/setIP=> Gv; move/astab1P=> cx_uv nSuv.
apply/conjg_fixP; rewrite -cx_uv /= -conjgM; apply: astabP Sx.
by rewrite astabJ (subsetP cSN) // !inE -nSuv groupM /=.
Qed.

End Focal_Subgroup.
