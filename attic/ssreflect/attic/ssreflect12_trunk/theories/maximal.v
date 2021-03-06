(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype finfun.
Require Import bigops finset prime binomial groups morphisms normal perm.
Require Import commutators automorphism action cyclic gfunc pgroups center.
Require Import gprod gseries nilpotent sylow abelian finmod.

(******************************************************************************)
(*   This file establishes basic properties of several important classes of   *)
(* maximal subgroups: maximal, max and min normal, simple, characteristically *)
(* simple subgroups, the Frattini and Fitting subgroups, the Thompson         *)
(* critical subgroup, special and extra-special groups, and self-centralising *)
(* normal (SCN) subgroups. In detail, we define:                              *)
(*      charsimple G == G is characteristically simple (it has no nontrivial  *)
(*                      characteristic subgroups, and is nontrivial)          *)
(*           'Phi(G) == the Frattini subgroup of G, i.e., the intersection of *)
(*                      all its maximal proper subgroups.                     *)
(*             'F(G) == the Fitting subgroup of G, i.e., the largest normal   *)
(*                      nilpotent subgroup of G (defined as the (direct)      *)
(*                      product of all the p-cores of G).                     *)
(*      critical C G == C is a critical subgroup of G: C is characteristic    *)
(*                      (but not functorial) in G, the center of C contains   *)
(*                      both its Frattini subgroup and the commutator [G, C], *)
(*                      and is equal to the centraliser of C in G. The        *)
(*                      Thompson_critical theorem provides critical subgroups *)
(*                      for p-groups; we also show that in this case the      *)
(*                      centraliser of C in Aut G is a p-group as well.       *)
(*         special G == G is a special group: its center, Frattini, and       *)
(*                      derived sugroups coincide (we follow Aschbacher in    *)
(*                      not considering nontrivial elementary abelian groups  *)
(*                      as special); we show that a p-group factors under     *)
(*                      coprime action into special groups (Aschbacher 24.7). *)
(*    extraspecial G == G is a special group whose center has prime order     *)
(*                      (hence G is non-abelian).                             *)
(*           'SCN(G) == the set of self-centralising normal abelian subgroups *)
(*                      of G (the A <| G such that 'C_G(A) = A).              *)
(*         'SCN_n(G) == the subset of 'SCN(G) containing all groups with rank *)
(*                      at least n (i.e., A \in 'SCN(G) and 'm(A) >= n).      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Defs.

Variable gT : finGroupType.
Implicit Types A B D : {set gT}.
Implicit Type G : {group gT}.

Definition charsimple A := [min A of G | (G :!=: 1) && (G \char A)].

Definition Frattini A := \bigcap_(G : {group gT} | maximal_eq G A) G.

Canonical Structure Frattini_group A : {group gT} :=
  Eval hnf in [group of Frattini A].

Definition Fitting A := \big[dprod/1]_(p <- primes #|A|) 'O_p(A).

Lemma Fitting_group_set : forall G, group_set (Fitting G).
Proof.
move=> G; suff [F ->]: exists F : {group gT}, Fitting G = F by exact: groupP.
rewrite /Fitting; elim: primes (primes_uniq #|G|) => [_|p r IHr] /=.
  by exists [1 gT]%G; rewrite big_nil.
case/andP=> rp; case/IHr=> F defF; rewrite big_cons defF.
suffices{IHr}: p^'.-group F && (F <| G).
  case/and3P=> p'F sFG nFG; exists ('O_p(G) <*> F)%G.
  have nFO: 'O_p(G) \subset 'N(F) by exact: (subset_trans (pcore_sub _ _)).
  have trOF: 'O_p(G) :&: F = 1.
    by apply: coprime_TIg; apply: pnat_coprime p'F; exact: pcore_pgroup.
  rewrite /= norm_mulgenEl ?dprodE // (sameP commG1P trivgP) -trOF.
  rewrite subsetI commg_subl commg_subr nFO.
  by rewrite (subset_trans sFG) // normal_norm ?pcore_normal.
move/bigdprodEgen: defF => <- {F}; elim: r rp => [_|q r IHr] /=.
  by rewrite big_nil gen0 pgroup1 normal1.
rewrite inE eq_sym big_cons -mulgenE -mulgen_idr; case/norP=> qp.
move/IHr {IHr}; set F := <<_>>; case/andP=> p'F nFG; rewrite norm_mulgenEl.
  rewrite pgroupM p'F normalM ?pcore_normal //= !andbT.
  by apply: sub_in_pnat (pcore_pgroup q G) => q' _; move/eqnP->.
exact: subset_trans (pcore_sub q G) (normal_norm nFG).
Qed.

Canonical Structure Fitting_group G := group (Fitting_group_set G).

Definition critical A B :=
  [/\ A \char B,
      Frattini A \subset 'Z(A),
      [~: B, A] \subset 'Z(A)
   & 'C_B(A) = 'Z(A)].

Definition special A := Frattini A = 'Z(A) /\  A^`(1) = 'Z(A).

Definition extra_special A := special A /\ prime #|'Z(A)|.

Definition SCN B := [set A : {group gT} | (A <| B) && ('C_B(A) == A)].

Definition SCN_at n B := [set A \in SCN B | n <= 'r(A)].

End Defs.

Prenex Implicits maximal simple charsimple critical special extra_special.

Notation "''Phi' ( A )" := (Frattini A)
  (at level 8, format "''Phi' ( A )") : group_scope.
Notation "''Phi' ( G )" := (Frattini_group G) : subgroup_scope.

Notation "''F' ( G )" := (Fitting G)
  (at level 8, format "''F' ( G )") : group_scope.
Notation "''F' ( G )" := (Fitting_group G) : subgroup_scope.

Notation "''SCN' ( B )" := (SCN B)
  (at level 8, format "''SCN' ( B )") : group_scope.
Notation "''SCN_' n ( B )" := (SCN_at n B)
  (at level 8, n at level 2, format "''SCN_' n ( B )") : group_scope.

Section PMax.

Variables (gT : finGroupType) (p : nat) (P M : {group gT}).
Hypothesis pP : p.-group P.

Lemma p_maximal_normal : maximal M P -> M <| P.
Proof.
case/maxgroupP; case/andP=> sMP sPM maxM; rewrite /normal sMP.
have:= subsetIl P 'N(M); rewrite subEproper.
case/predU1P; [by move/setIidPl | move/maxM => /= SNM].
case/negP: sPM; rewrite (nilpotent_sub_norm (pgroup_nil pP) sMP) //.
by rewrite SNM // subsetI sMP normG.
Qed.

Lemma p_maximal_index : maximal M P -> #|P : M| = p.
Proof.
move=> maxM; have nM := p_maximal_normal maxM.
rewrite -card_quotient ?normal_norm //.
rewrite -(quotient_maximal _ nM) ?normal_refl // trivg_quotient in maxM.
case/maxgroupP: maxM; rewrite properEneq eq_sym sub1G andbT /=.
case/(pgroup_pdiv (quotient_pgroup M pP)) => p_pr; case/Cauchy=> // xq.
rewrite /order -cycle_subG subEproper; case/predU1P=> [-> // | sxPq oxq_p _].
by move/(_ _ sxPq (sub1G _)) => xq1; rewrite -oxq_p xq1 cards1 in p_pr.
Qed.

Lemma p_index_maximal : M \subset P -> prime #|P : M| -> maximal M P.
Proof.
move=> sMP; case/primeP=> lt1PM pr_PM.
apply/maxgroupP; rewrite properEcard sMP -(LaGrange sMP).
rewrite -{1}(muln1 #|M|) ltn_pmul2l //; split=> // H sHP sMH.
apply/eqP; rewrite eq_sym eqEcard sMH.
case/orP: (pr_PM _ (indexSg sMH (proper_sub sHP))); move/eqP=> iM.
  by rewrite -(LaGrange sMH) iM muln1 /=.
by have:= proper_card sHP; rewrite -(LaGrange sMH) iM LaGrange ?ltnn.
Qed.

End PMax.

Section Frattini.

Variables gT : finGroupType.
Implicit Type G M : {group gT}.

Lemma Phi_sub : forall G, 'Phi(G) \subset G.
Proof. by move=> G; rewrite bigcap_inf // /maximal_eq eqxx. Qed.

Lemma Phi_sub_max : forall G M, maximal M G -> 'Phi(G) \subset M.
Proof. by move=> G M maxM; rewrite bigcap_inf // /maximal_eq predU1r. Qed.

Lemma Phi_proper : forall G, G :!=: 1 -> 'Phi(G) \proper G.
Proof.
move=> G; move/eqP; case/maximal_exists: (sub1G G) => [<- //| [M maxM _] _].
exact: sub_proper_trans (Phi_sub_max maxM) (maxgroupp maxM).
Qed.

Lemma Phi_nongen : forall G X, 'Phi(G) <*> X = G -> <<X>> = G.
Proof.
move=> G X defG; have: <<X>> \subset G by rewrite -{1}defG genS ?subsetUr.
case/maximal_exists=> //= [[M maxM]]; rewrite gen_subG => sXM.
case/andP: (maxgroupp maxM) => _; case/negP.
by rewrite -defG gen_subG subUset Phi_sub_max.
Qed.

Lemma Frattini_cont : forall (rT : finGroupType) G (f : {morphism G >-> rT}),
  f @* 'Phi(G) \subset 'Phi(f @* G).
Proof.
move=> rT G f; apply/bigcapsP=> M maxM.
rewrite sub_morphim_pre ?Phi_sub //; apply: bigcap_inf.
have defG: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
by rewrite -{2}defG morphpre_maximal_eq ?maxM //; case/maximal_eqP: maxM.
Qed.

End Frattini.

Canonical Structure bgFunc_Frattini := [bgFunc by Phi_sub & Frattini_cont].
Canonical Structure gFunc_Frattini := GFunc Frattini_cont.

Section Frattini0.

Variables (gT : finGroupType) (G : {group gT}).

Lemma Phi_char : 'Phi(G) \char G.
Proof. exact: bgFunc_char. Qed.

Lemma Phi_normal : 'Phi(G) <| G.
Proof. exact: bgFunc_normal. Qed.

End Frattini0.

Section Frattini2.

Variables gT : finGroupType.
Implicit Type G : {group gT}.

Lemma Phi_quotient_id : forall G, 'Phi (G / 'Phi(G)) = 1.
Proof.
move=> G; apply/trivgP; rewrite -cosetpreSK cosetpre1 /=.
apply/bigcapsP=> M maxM.
have nPhi := Phi_normal G; have nPhiM: 'Phi(G) <| M.
  by apply: normalS nPhi; [exact: bigcap_inf | case/maximal_eqP: maxM].
by rewrite sub_cosetpre_quo ?bigcap_inf // quotient_maximal_eq.
Qed.

Lemma Phi_quotient_cyclic : forall G, cyclic (G / 'Phi(G)) -> cyclic G.
Proof.
move=> G; case/cyclicP=> /= Px; case: (cosetP Px) => x nPx ->{Px} defG.
apply/cyclicP; exists x; symmetry; apply: Phi_nongen.
rewrite -mulgen_idr norm_mulgenEr -?quotientK ?cycle_subG //.
by rewrite /quotient morphim_cycle //= -defG quotientGK ?Phi_normal.
Qed.

Variables (p : nat) (P : {group gT}).

Lemma trivg_Phi : p.-group P -> ('Phi(P) == 1) = p.-abelem P.
Proof.
move=> pP; case: (eqsVneq P 1) => [P1 | ntP].
  by rewrite P1 abelem1 -subG1 -P1 Phi_sub.
have [p_pr _ _] := pgroup_pdiv pP ntP.
apply/eqP/idP=> [trPhi | abP].
  apply/abelemP=> //; split=> [|x Px].
    apply/commG1P; apply/trivgP; rewrite -trPhi.
    apply/bigcapsP=> M; case/predU1P=> [-> | maxM]; first exact: der1_subG.
    have [_ nMP] := andP (p_maximal_normal pP maxM).
    have: cyclic (P / M).
      by rewrite prime_cyclic // card_quotient // (p_maximal_index pP).
    case/cyclicP=> Px defP; rewrite -quotient_cents2 // defP.
    rewrite gen_subG centsC gen_subG /= cent_set1 sub1set; exact/cent1P.
  apply/set1gP; rewrite -trPhi; apply/bigcapP=> M.
  case/predU1P=> [-> | maxM]; first exact: groupX.
  have [_ nMP] := andP (p_maximal_normal pP maxM).
  have nMx : x \in 'N(M) by exact: subsetP Px.
  apply: coset_idr; rewrite ?groupX ?morphX //=; apply/eqP.
  rewrite -(p_maximal_index pP maxM) -card_quotient // -order_dvdn cardSg //=.
  by rewrite -morphim_cycle ?morphimS ?cycle_subG.
apply/trivgP; apply/subsetP=> x Phi_x; rewrite -cycle_subG.
have Px: x \in P by exact: (subsetP (Phi_sub P)).
have sxP: <[x]> \subset P by rewrite cycle_subG.
case/splitsP: (abelem_splits abP sxP) => K; case/complP=> trKx defP.
case: (eqVneq x 1) => [-> | nt_x]; first by rewrite cycle1.
have [_ oxp] := abelem_order_p abP Px nt_x.
rewrite /= -trKx subsetI subxx cycle_subG.
apply: (bigcapP Phi_x); apply/orP; right.
apply: p_index_maximal; rewrite -?divgS -defP ?mulG_subr //.
by rewrite (TI_cardMg trKx) mulnK // [#|_|]oxp.
Qed.

End Frattini2.

Section Frattini3.

Variables (gT : finGroupType) (p : nat) (P : {group gT}).
Hypothesis pP : p.-group P.

Lemma Phi_quotient_abelem : p.-abelem (P / 'Phi(P)).
Proof. by rewrite -trivg_Phi ?morphim_pgroup //= Phi_quotient_id. Qed.

Lemma Phi_mulgen : 'Phi(P) = P^`(1) <*> 'Mho^1(P).
Proof.
have [sPhiP nPhiP] := andP (Phi_normal P).
apply/eqP; rewrite eqEsubset mulgen_subG.
case: (eqsVneq P 1) => [-> | ntP] in sPhiP *.
  by rewrite /= (trivgP sPhiP) sub1G der_subS Mho_sub.
have [p_pr _ _] := pgroup_pdiv pP ntP.
have [abP x1P] := abelemP p_pr Phi_quotient_abelem.
apply/andP; split.
  have nMP: P \subset 'N(P^`(1) <*> 'Mho^1(P)).
    by rewrite norms_mulgen // char_norm ?der_char ?Mho_char.
  rewrite -quotient_sub1 ?(subset_trans sPhiP) //=.
  suffices <-: 'Phi(P / (P^`(1) <*> 'Mho^1(P))) = 1.
    exact: morphim_sFunctor.
  apply/eqP; rewrite (trivg_Phi (morphim_pgroup _ pP)) /= -quotientE.
  apply/abelemP=> //; rewrite [abelian _]quotient_cents2 ?mulgen_subl //.
  split=> // Mx; case/morphimP=> x Nx Px ->{Mx} /=.
  rewrite -morphX //= coset_id // (MhoE 1 pP) mulgen_idr expn1.
  by rewrite mem_gen //; apply/setUP; right; exact: mem_imset.
rewrite -quotient_cents2 // [_ \subset 'C(_)]abP (MhoE 1 pP) gen_subG /=.
apply/subsetP=> xp; case/imsetP=> x Px ->{xp}.
have nPhi_x: x \in 'N('Phi(P)) by exact: (subsetP nPhiP).
by rewrite /= expn1 coset_idr ?groupX ?morphX ?x1P ?mem_morphim.
Qed.

End Frattini3.

Section Frattini4.

Variables (p : nat) (gT : finGroupType).
Implicit Type rT : finGroupType.
Implicit Types P H K D : {group gT}.

Lemma morphim_Phi : forall rT P D (f : {morphism D >-> rT}),
  p.-group P -> P \subset D -> f @* 'Phi(P) = 'Phi(f @* P).
Proof.
move=> rT P D f pP sPD; rewrite !(@Phi_mulgen _ p) ?morphim_pgroup //.
rewrite morphim_gen ?(subset_trans _ sPD) ?subUset ?der_subS ?Mho_sub //.
by rewrite morphimU -mulgenE morphimR ?morphim_Mho.
Qed.

Lemma quotient_Phi : forall P H,
  p.-group P -> P \subset 'N(H) -> 'Phi(P) / H = 'Phi(P / H).
Proof. move=> P H; exact: morphim_Phi. Qed.

Lemma Phi_mulg : forall H K,
    p.-group H -> p.-group K -> H \subset 'C(K) ->
  'Phi(H * K) = 'Phi(H) * 'Phi(K).
Proof.
move=> H K pH pK cHK; rewrite -!cent_mulgenEl ?(centSS _ _ cHK) ?Phi_sub //=.
rewrite !(@Phi_mulgen _ p) //=; last by rewrite cent_mulgenEl ?pgroupM ?pH.
case/cprodP: (der_cprod 1 (cprodEgen cHK)) => _ <-; move/cent_mulgenEl <-.
case/cprodP: (Mho_cprod 1 (cprodEgen cHK)) => _ <-; move/cent_mulgenEl <-.
by rewrite !mulgenA -!(mulgenA H^`(1)) (mulgenC K^`(1)).
Qed.

End Frattini4.

Section Simple.

Implicit Types gT rT : finGroupType.

Lemma charsimpleP : forall gT (G : {group gT}),
   reflect
     (G :!=: 1 /\ forall K : {group gT}, K :!=: 1 -> K \char G -> K :=: G)
     (charsimple G).
Proof.
move=> gT G.
apply: (iffP mingroupP); rewrite char_refl andbT => [[ntG simG]].
  by split=> // K ntK chK; apply: simG; rewrite ?ntK // char_sub.
split=> // K; case/andP=> ntK chK _; exact: simG.
Qed.

End Simple.

Section Fitting.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma Fitting_normal : forall G, 'F(G) <| G.
Proof.
move=> G; rewrite -['F(G)](bigdprodEgen (erefl 'F(G))).
apply big_prop => [|A B nAG nBG|p _]; first by rewrite gen0 normal1.
  rewrite -mulgenE -mulgen_idl -mulgen_idr norm_mulgenEl ?normalM //.
  exact: subset_trans (normal_sub nAG) (normal_norm nBG).
by rewrite genGid pcore_normal.
Qed.

Lemma Fitting_sub : forall G, 'F(G) \subset G.
Proof. by move=> G; rewrite normal_sub ?Fitting_normal. Qed.

Lemma Fitting_nil : forall G, nilpotent 'F(G).
Proof.
move=> G; apply: (bigdprod_nil (erefl 'F(G))) => p _.
exact: pgroup_nil (pcore_pgroup p G).
Qed.

Lemma Fitting_max : forall G H, H <| G -> nilpotent H -> H \subset 'F(G).
Proof.
move=> G H nHG nilH; rewrite -(Sylow_gen H) gen_subG.
apply/bigcupsP=> P; case/SylowP=> p _ SylP.
case Gp: (p \in \pi(#|G|)); last first.
  rewrite card1_trivg ?sub1G // (card_Hall SylP).
  rewrite part_p'nat // (pnat_dvd (cardSg (normal_sub nHG))) //.
  by rewrite /pnat cardG_gt0 all_predC has_pred1 Gp.
move/nilpotent_Hall_pcore: SylP => ->{P} //.
rewrite -(bigdprodEgen (erefl 'F(G))) sub_gen //.
rewrite -(filter_pi_of (ltnSn _)) big_filter big_mkord.
have le_pG: p < #|G|.+1.
  by rewrite ltnS dvdn_leq //; move: Gp; rewrite mem_primes; case/and3P.
apply: (bigcup_max (Ordinal le_pG)) => //=.
apply: pcore_max (pcore_pgroup _ _) _.
exact: char_normal_trans (pcore_char p H) nHG.
Qed.

Lemma pcore_Fitting : forall pi G, 'O_pi('F(G)) \subset 'O_pi(G).
Proof.
move=> pi G; rewrite pcore_max ?pcore_pgroup //.
exact: char_normal_trans (pcore_char _ _) (Fitting_normal _).
Qed.

Lemma p_core_Fitting : forall (p : nat) G, 'O_p('F(G)) = 'O_p(G).
Proof.
move=> p G; apply/eqP; rewrite eqEsubset pcore_Fitting.
rewrite pcore_max ?pcore_pgroup //.
apply: normalS (normal_sub (Fitting_normal _)) (pcore_normal _ _).
exact: Fitting_max (pcore_normal _ _) (pgroup_nil (pcore_pgroup _ _)).
Qed.

Lemma nilpotent_Fitting : forall G, nilpotent G -> 'F(G) = G.
Proof.
by move=> G nilG; apply/eqP; rewrite eqEsubset Fitting_sub Fitting_max.
Qed.

Lemma Fitting_eq_pcore : forall (p : nat) G, 'O_p^'(G) = 1 -> 'F(G) = 'O_p(G).
Proof.
move=> p G p'G1.
case/dprodP: (nilpotent_pcoreC p (Fitting_nil G)) => _  /= <- _ _.
by rewrite p_core_Fitting ['O_p^'(_)](trivgP _) ?mulg1 // -p'G1 pcore_Fitting.
Qed.

Lemma FittingEgen : forall G,
  'F(G) = <<\bigcup_(p < #|G|.+1 | (p : nat) \in \pi(#|G|)) 'O_p(G)>>.
Proof.
move=> G; apply/eqP; rewrite eqEsubset gen_subG /=.
rewrite -{1}(bigdprodEgen (erefl 'F(G))) (big_nth 0) big_mkord genS.
  by apply/bigcupsP=> p _; rewrite -p_core_Fitting pcore_sub.
apply/bigcupsP=> [[i /= lti]] _; set p := nth _ _ i.
have pi_p: p \in \pi(#|G|) by rewrite mem_nth.
have p_dv_G: p %| #|G| by rewrite mem_primes in pi_p; case/and3P: pi_p.
have lepG: p < #|G|.+1 by rewrite ltnS dvdn_leq.
by rewrite (bigcup_max (Ordinal lepG)).
Qed.

End Fitting.

Section FittingFun.

Implicit Types gT rT : finGroupType.

Lemma morphim_Fitting : forall gT rT (G D : {group gT}),
  forall f : {morphism D >-> rT}, f @* 'F(G) \subset 'F(f @* G).
Proof.
move=> gT rT G D f; apply: Fitting_max.
  by rewrite morphim_normal ?Fitting_normal.
by rewrite morphim_nil ?Fitting_nil.
Qed.

Lemma FittingS : forall gT (G H : {group gT}),
  H \subset G -> H :&: 'F(G) \subset 'F(H).
Proof.
move=> gT G H sHG; rewrite -{2}(setIidPl sHG).
do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom; exact: morphim_Fitting.
Qed.

Lemma Fitting_cont : forall gT rT (G : {group gT}) (f : {morphism G >-> rT}),
  f @* 'F(G) \subset 'F(f @* G).
Proof. move=> gT rT G f; exact: morphim_Fitting. Qed.

Lemma Fitting_hereditary : hereditary Fitting.
Proof. by move=> gT H G; move/FittingS; rewrite setIC. Qed.

End FittingFun.

Canonical Structure bgFunc_Fitting := [bgFunc by Fitting_sub & Fitting_cont].
Canonical Structure gFunc_Fitting := GFunc Fitting_cont.
Canonical Structure hgFunc_Fitting := HGFunc Fitting_hereditary.

Lemma Fitting_char : forall (gT : finGroupType) (G : {group gT}),
  'F(G) \char G.
Proof. exact: bgFunc_char. Qed.

Lemma injm_Fitting :
  forall (gT rT : finGroupType) (G D : {group gT}) (f : {morphism D >-> rT}),
  'injm f -> G \subset D -> f @* 'F(G) = 'F(f @* G).
Proof. exact: bgFunc_ascont. Qed.

Section CharSimple.

Variable gT : finGroupType.
Implicit Type rT : finGroupType.
Implicit Types G H K L : {group gT}.

Lemma minnormal_charsimple : forall G H, minnormal H G -> charsimple H.
Proof.
move=> G H; case/mingroupP; case/andP=> ntH nHG minH.
apply/charsimpleP; split=> // K ntK chK.
by apply: minH; rewrite ?ntK (char_sub chK, char_norm_trans chK).
Qed.

Lemma maxnormal_charsimple : forall G H L,
  G <| L -> maxnormal H G L -> charsimple (G / H).
Proof.
move=> G H L; case/andP=> sGL nGL.
case/maxgroupP; do 2![case/andP] => sHG sGH nHL maxH.
have nHG: G \subset 'N(H) := subset_trans sGL nHL.
apply/charsimpleP; rewrite -subG1 quotient_sub1 //; split=> // HK ntHK chHK.
case/(inv_quotientN _): (char_normal chHK) => [|K defHK sHK]; first exact/andP.
case/andP; rewrite subEproper defHK; case/predU1P=> [-> //|sKG nKG].
have nHK: H <| K by rewrite /normal sHK (subset_trans (proper_sub sKG)).
case/negP: ntHK; rewrite defHK -subG1 quotient_sub1 ?normal_norm //.
rewrite (maxH K) // sKG -(quotientGK nHK) -defHK.
apply: subset_trans (morphpre_norm _ _).
by rewrite -sub_quotient_pre // (char_norm_trans chHK) ?quotient_norms.
Qed.

Lemma p_abelem_split1 : forall rT (p : nat) (A : {group rT}) x,
     p.-abelem A -> x \in A ->
  exists B : {group rT},
     [/\ B \subset A, #|B| = #|A| %/ #[x] & <[x]> \x B = A].
Proof.
move=> rT p A x pA Ax; have sxA: <[x]> \subset A by rewrite cycle_subG.
case/splitsP: (abelem_splits pA sxA) => B; case/complP=> trxB defA.
have sBA: B \subset A by rewrite -defA mulG_subr.
exists B; split => //; first by rewrite -defA (TI_cardMg trxB) mulKn.
rewrite dprodE // cycle_subG; apply: subsetP Ax; rewrite centsC.
by apply: subset_trans sBA _; case/and3P: pA.
Qed.

Lemma abelem_split_dprod : forall rT (p : nat) (A B : {group rT}),
  p.-abelem A -> B \subset A -> exists C : {group rT}, B \x C = A.
Proof.
move=> rT p A B pA sBA.
case/splitsP: (abelem_splits pA sBA) => C; case/complP=> trBC defA.
exists C; rewrite dprodE // (subset_trans sBA) // centsC.
case/and3P: pA => _ abA _; apply: subset_trans abA.
by rewrite -defA mulg_subr.
Qed.

Lemma abelem_charsimple : forall (p : nat) G,
  p.-abelem G -> G :!=: 1 -> charsimple G.
Proof.
move=> p G pG ntG; apply/charsimpleP; split=> {ntG}// K ntK; case/charP.
rewrite subEproper; case/predU1P=> //; case/andP=> sKG.
case/subsetPn=> x Gx Kx chK; case: (abelem_order_p pG Gx) => [|pr_p ox].
  by apply/eqP=> x1; rewrite x1 group1 in Kx.
have [A [sAG oA defA]] := p_abelem_split1 pG Gx.
case/trivgPn: ntK => y Ky; have Gy := subsetP sKG y Ky.
case/(abelem_order_p pG) => // _ oy.
have [B [sBG oB defB]] := p_abelem_split1 pG Gy.
have: isog A B; last case/isogP=> fAB injAB defAB.
  rewrite (isog_abelem_card _ (abelemS sAG pG)) (abelemS sBG) //=.
  by rewrite oA oB ox oy.
have: isog <[x]> <[y]>; last case/isogP=> fxy injxy /= defxy.
  by rewrite isog_cyclic_card ?cycle_cyclic // [#|_|]oy -ox eqxx.
have cfxA: fxy @* <[x]> \subset 'C(fAB @* A).
  by rewrite defAB defxy; case/dprodP: defB.
have injf: 'injm (dprodm defA cfxA).
  by rewrite injm_dprodm injAB injxy defAB defxy; apply/eqP; case/dprodP: defB.
case/negP: Kx; rewrite -cycle_subG -(injmSK injf) ?cycle_subG //=.
rewrite morphim_dprodml // defxy cycle_subG /= chK //.
case/dprodP: defB => _ defBG _ _; rewrite -{4}defBG.
case/dprodP: (defA) => _ defAG _ _; rewrite -{3}defAG.
by rewrite morphim_dprodm // defAB defxy.
Qed.

Lemma charsimple_dprod : forall G, charsimple G ->
  exists H : {group gT}, [/\ H \subset G, simple H
                         & exists2 I : {set {perm gT}}, I \subset Aut G
                         & \big[dprod/1]_(f \in I) f @: H = G].
Proof.
move=> G; case/charsimpleP=> ntG simG.
have [H minH sHG]: {H : {group gT} | minnormal H G & H \subset G}.
  by apply: mingroup_exists; rewrite ntG normG.
case/mingroupP: minH; case/andP=> ntH nHG minH.
pose Iok (I : {set {perm gT}}) :=
  (I \subset Aut G) &&
  (existsb M : {group gT}, (M <| G) &&
    (\big[dprod/1]_(f \in I) f @: H == M)).
have defH: (1 : {perm gT}) @: H = H.
  apply/eqP; rewrite eqEcard card_imset ?leqnn; last exact: perm_inj.
  by rewrite andbT; apply/subsetP=> fx; case/imsetP=> x Hx ->; rewrite perm1.
have [|I] := @maxset_exists _ Iok 1.
  rewrite /Iok sub1G; apply/existsP; exists H.
  by rewrite /normal sHG nHG (big_pred1 1) => [|f]; rewrite ?defH /= ?inE.
case/maxsetP; case/andP=> Aut_I; case/existsP=> M; do 2![case/andP]=> sMG nMG.
move/eqP=> defM maxI; rewrite sub1set=> ntI; move: sMG; rewrite subEproper.
case/predU1P=> [defG|]; last case/andP=> sMG sGM.
  exists H; split=> //; last by exists I; rewrite ?defM.
  apply/mingroupP; rewrite ntH normG; split=> // N; case/andP=> ntN nNH sNH.
  apply: minH => //; rewrite ntN /= -defG.
  move: defM; rewrite (bigD1 1) //= defH; case/dprodP=> [[_ K _ ->] <- cHK _].
  by rewrite mul_subG // cents_norm // centsC (subset_trans sNH).
have defG: <<\bigcup_(f \in Aut G) f @: H>> = G.
  have sXG: \bigcup_(f \in Aut G) f @: H \subset G.
    apply big_prop => [|A B sAG sBG|f Af]; first exact: sub0set.
    - by rewrite subUset sAG.
    by rewrite -(im_autm Af) morphimEdom imsetS.
  apply: simG.
    apply: contra ntH; rewrite -!subG1; apply: subset_trans.
    by rewrite sub_gen // (bigcup_max 1) ?group1 ?defH.
  rewrite /characteristic gen_subG sXG; apply/forallP=> f; apply/implyP=> Af.
  rewrite -(autmE Af) -morphimEsub ?gen_subG ?morphim_gen // genS //.
  rewrite morphimEsub //= autmE.
  apply/subsetP=> fgx; case/imsetP=> gx; case/bigcupP=> g Ag.
  case/imsetP=> x Hx -> -> {gx fgx}; apply/bigcupP.
  exists (g * f); first exact: groupM.
  by apply/imsetP; exists x; rewrite // permM.
have [f Af sfHM]: exists2 f, f \in Aut G & ~~ (f @: H \subset M).
  move: sGM; rewrite -{1}defG gen_subG; case/subsetPn=> x.
  by case/bigcupP=> f Af fHx Mx; exists f => //; apply/subsetPn; exists x.
case If: (f \in I).
  by case/negP: sfHM; rewrite -(bigdprodEgen defM) sub_gen // (bigcup_max f).
case/idP: (If); rewrite -(maxI ([set f] :|: I)) ?subsetUr ?inE ?eqxx //.
rewrite {maxI}/Iok subUset sub1set Af {}Aut_I; apply/existsP.
have sfHG: autm Af @* H \subset G by rewrite -{4}(im_autm Af) morphimS.
have{minH nHG}: minnormal (autm Af @* H) G.
  apply/mingroupP; rewrite andbC -{1}(im_autm Af) morphim_norms //=.
  rewrite -subG1 sub_morphim_pre // -kerE ker_autm subG1.
  split=> // N; case/andP=> ntN nNG sNfH.
  have sNG: N \subset G := subset_trans sNfH sfHG.
  apply/eqP; rewrite eqEsubset sNfH sub_morphim_pre //=.
  rewrite -(morphim_invmE (injm_autm Af)) [_ @* N]minH //=.
    rewrite -subG1 sub_morphim_pre /= ?im_autm // morphpre_invm morphim1 subG1.
    by rewrite ntN -{1}(im_invm (injm_autm Af)) /= {2}im_autm morphim_norms.
  by rewrite sub_morphim_pre /= ?im_autm // morphpre_invm.
case/mingroupP; case/andP=> ntfH nfHG minfH.
have{minfH sfHM} trfHM: autm Af @* H :&: M = 1.
  apply/eqP; apply/idPn=> ntMfH; case/setIidPl: sfHM.
  rewrite -(autmE Af) -morphimEsub //.
  by apply: minfH; rewrite ?subsetIl // ntMfH normsI.
have cfHM: autm Af @* H \subset 'C(M).
  rewrite (sameP commG1P trivgP); rewrite -trfHM.
  rewrite subsetI commg_subl commg_subr (subset_trans sMG) //.
  exact: (subset_trans sfHG).
exists (autm Af @* H <*> M)%G.
rewrite /normal /= mulgen_subG sMG sfHG norms_mulgen //=.
rewrite (bigD1 f) ?inE ?eqxx // (eq_bigl (mem I)) /= => [|g]; last first.
  by rewrite /= !inE andbC; case: eqP => // ->.
by rewrite defM -(autmE Af) -morphimEsub // dprodE // cent_mulgenEl ?eqxx.
Qed.

Lemma charsimple_solvable : forall G,
  charsimple G -> solvable G -> is_abelem G.
Proof.
move=> G; case/charsimple_dprod=> H [sHG simH [I Aut_I defG]] solG.
case/simpleP: simH => ntH simH; pose p := pdiv #|H|.
have pr_p: prime p by rewrite pdiv_prime // ltnNge -trivg_card_le1.
have{solG ntH} abH: abelian H.
  apply/commG1P; case/simH: (der_normal 1 H) => //; move/eqP; case/idPn.
  by rewrite proper_neq // (sol_der1_proper solG).
have{simH} oHp: #|H| = p.
  have [x Hx ox] := Cauchy pr_p (pdiv_dvd _).
  case: (simH <[x]>%G) => [|/= x1|<- //].
    by rewrite /normal cents_norm 1?centsC cycle_subG ?Hx ?(subsetP abH).
  by rewrite -ox /order x1 cards1 in pr_p.
apply/is_abelemP; exists p => //; move: (G) defG.
apply big_prop => [_ <-|A1 A2 IH1 IH2 M|f If _ <-]; first exact: abelem1.
  case/dprodP=> [[G1 G2 dG1 dG2]]; rewrite dG1 dG2 => defM cG12 _.
  have [abG1 pG1] := abelemP pr_p (IH1 G1 dG1).
  have [abG2 pG2] := abelemP pr_p (IH2 G2 dG2).
  apply/abelemP; rewrite // -{M}defM /abelian !centM !subsetI.
  rewrite !mul_subG // 1?centsC //; split=> // x.
  case/imset2P=> x1 x2 Gx1 Gx2 ->; rewrite expMgn; last exact: (centsP cG12).
  by rewrite pG1 // pG2 // mulg1.
have Af := subsetP Aut_I f If; rewrite -(autmE Af) -morphimEsub //.
apply/abelemP; rewrite /abelian ?morphim_cents //; split=> // fx.
case/morphimP=> x Gx Hx ->{fx}; rewrite -morphX 1?((x ^+ p =P 1) _) ?morph1 //.
by rewrite -order_dvdn -oHp cardSg // cycle_subG.
Qed.

Lemma minnormal_solvable : forall L G H : {group gT},
  minnormal H L -> H \subset G -> solvable G ->
  [/\ L \subset 'N(H), H :!=: 1 & is_abelem H].
Proof.
move=> L G H minH sHG solG; have [ntH nHL] := andP (mingroupp minH).
split=> //; apply: (charsimple_solvable (minnormal_charsimple minH)).
exact: solvableS solG.
Qed.

Lemma solvable_norm_abelem : forall L G,
  solvable G -> G <| L -> G :!=: 1 ->
  exists H : {group gT}, [/\ H \subset G, H <| L, H :!=: 1 & is_abelem H].
Proof.
move=> L G solG; case/andP=> sGL nGL ntG.
have [H minH sHG]: {H : {group gT} | minnormal H L & H \subset G}.
  by apply: mingroup_exists; rewrite ntG.
have [nHL ntH abH] := minnormal_solvable minH sHG solG.
by exists H; split; rewrite // /normal (subset_trans sHG).
Qed.

Lemma trivg_Fitting : forall G, solvable G -> ('F(G) == 1) = (G :==: 1).
Proof.
move=> G solG; apply/idP/idP=> [F1|]; last first.
  by rewrite -!subG1; apply: subset_trans; exact: Fitting_sub.
apply/idPn; case/(solvable_norm_abelem _ (normal_refl _)) => // M [_] nsMG ntM.
case/is_abelemP=> p _; case/and3P=> pM _ _; case/negP: ntM.
by rewrite -subG1 -(eqP F1) Fitting_max ?(pgroup_nil pM).
Qed.

Lemma Fitting_pcore : forall pi G, 'F('O_pi(G)) = 'O_pi('F(G)).
Proof.
move=> pi G; apply/eqP; rewrite eqEsubset.
rewrite (subset_trans _ (pcoreS _ (Fitting_sub _))); last first.
  rewrite subsetI Fitting_sub Fitting_max ?Fitting_nil //.
  by rewrite (char_normal_trans (Fitting_char _)) ?pcore_normal.
rewrite (subset_trans _ (FittingS (pcore_sub _ _))) // subsetI pcore_sub.
rewrite pcore_max ?pcore_pgroup //.
by rewrite (char_normal_trans (pcore_char _ _)) ?Fitting_normal.
Qed.

End CharSimple.

Section Special.

Variables (gT : finGroupType) (p : nat) (A G : {group gT}).

(* Aschbacher 23.7 *)
Lemma center_special_abelem : p.-group G -> special G -> p.-abelem 'Z(G).
Proof.
move=> pG [defPhi defG'].
case: (eqsVneq G 1) => [-> | ntG]; first by rewrite center1 abelem1. 
have [p_pr _ _] := pgroup_pdiv pG ntG.  
have fM: {in 'Z(G) &, {morph expgn^~ p : x y / x * y}}.
  move=> x y; case/setIP=> _ CxG; case/setIP=> Gy _.
  rewrite expMgn //; exact: (centP CxG).
rewrite abelemE //= center_abelian; apply/exponentP=> /= z Zz.
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

(* Aschbacher 24.7 (replaces Gorenstein 5.3.7) *)
Theorem abelian_charsimple_special :
    p.-group G -> coprime #|G| #|A| -> [~: G, A] = G ->
    \bigcup_(H : {group gT} | (H \char G) && abelian H) H \subset 'C(A) ->
  special G /\ 'C_G(A) = 'Z(G).
Proof.
move=> pG coGA defG; move/bigcupsP=> cChaA.
have cZA: 'Z(G) \subset 'C_G(A).
  by rewrite subsetI center_sub cChaA // center_char center_abelian.
have cChaG: forall H : {group gT}, H \char G -> abelian H -> H \subset 'Z(G).
  move=> H chH abH; rewrite subsetI char_sub //= centsC -defG.
  rewrite comm_norm_cent_cent ?(char_norm chH) -?commg_subl ?defG //.
  by rewrite centsC cChaA ?chH.
have cZ2GG: [~: 'Z_2(G), G, G] = 1.
  by apply/commG1P; rewrite (subset_trans (ucn_comm 1 G)) // ucn1 subsetIr.
have{cZ2GG} cG'Z: 'Z_2(G) \subset 'C(G^`(1)).
  by rewrite centsC; apply/commG1P; rewrite three_subgroup // (commGC G).
have{cG'Z} sZ2G'_Z: 'Z_2(G) :&: G^`(1) \subset 'Z(G).
  apply: cChaG; first by rewrite charI ?ucn_char ?der_char.
  by rewrite /abelian subIset // (subset_trans cG'Z) // centS ?subsetIr.
have{sZ2G'_Z} sG'Z: G^`(1) \subset 'Z(G).
  rewrite -quotient_sub1; last first.
    by rewrite (subset_trans (der_sub 1 G)) ?char_norm ?center_char.
  apply/trivgP; have: nilpotent (G / 'Z(G)) := quotient_nil _ (pgroup_nil pG).
  move/nil_TI_Z; apply; first by rewrite quotient_normal ?der_normalS.
  apply/trivgP; rewrite /= -ucn1 -ucn_central -quotientIG ?ucn_subS //= ucn1.
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
  by rewrite expgn_mul -expGpn expg_exponent ?groupX ?group1.
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

End Special.

Section SCN.

Variables (gT : finGroupType) (p : nat) (G : {group gT}).
Implicit Type A Z H : {group gT}.

Lemma SCN_P : forall A, reflect (A <| G /\ 'C_G(A) = A) (A \in 'SCN(G)).
Proof. by move=> A; apply: (iffP setIdP) => [] [->]; move/eqP. Qed.

Lemma SCN_abelian : forall A, A \in 'SCN(G) -> abelian A.
Proof.
by move=> A; case/SCN_P=> _ defA; rewrite /abelian -{1}defA subsetIr.
Qed.

Lemma exponent_Ohm1_class2 : forall H,
  odd p -> p.-group H -> nil_class H <= 2 -> exponent 'Ohm_1(H) %| p.
Proof.
move=> H odd_p pH; rewrite nil_class2 => sH'Z.
apply/exponentP=> x; rewrite /= (OhmE 1 pH) expn1 gen_set_id => [|{x}].
  by case/setIdP=> _; move/eqP.
apply/group_setP; split=> [|x y]; first by rewrite inE group1 exp1gn eqxx.
case/setIdP=> Hx; move/eqP=> xp1; case/setIdP=> Hy; move/eqP=> yp1.
rewrite inE groupM //.
have: [~ y, x] \in 'Z(H) by rewrite (subsetP sH'Z) ?mem_commg.
case/setIP=> _; move/centP=> czH.
rewrite expMg_Rmul ?xp1 ?yp1 /commute ?czH //= !mul1g.
by rewrite bin2odd // -commXXg ?yp1 /commute ?czH // comm1g.
Qed.

(* SCN_max and max_SCN cover Aschbacher 23.15(1) *)
Lemma SCN_max : forall A, A \in 'SCN(G) -> [max A | (A <| G) && abelian A].
Proof.
move=> A; case/SCN_P => nAG scA; apply/maxgroupP; split=> [|H].
  by rewrite nAG /abelian -{1}scA subsetIr.
do 2![case/andP]=> sHG _ abelH sAH; apply/eqP.
by rewrite eqEsubset sAH -scA subsetI sHG centsC (subset_trans sAH).
Qed.

Lemma max_SCN : forall A,
  p.-group G -> [max A | (A <| G) && abelian A] -> A \in 'SCN(G).
Proof.
move=> A; move/pgroup_nil=> nilG; rewrite /abelian.
case/maxgroupP; case/andP=> nsAG abelA maxA; have [sAG nAG] := andP nsAG.
rewrite inE nsAG eqEsubset /= andbC subsetI abelA normal_sub //=.
rewrite -quotient_sub1; last by rewrite subIset 1?normal_norm.
apply/trivgP; apply: (nil_TI_Z (quotient_nil A nilG)).
  by rewrite quotient_normal // /normal subsetIl normsI ?normG ?norms_cent.
apply/trivgP; apply/subsetP=> Ax; case/setIP; case/morphimP=> x Nx.
case/setIP=> _; rewrite -cycle_subG /= => Cx -> {Ax}; case/setIP=> GAx CAx.
have{CAx GAx}: <[coset A x]> <| G / A.
  by rewrite /normal cycle_subG GAx cents_norm // centsC cycle_subG.
case/(inv_quotientN nsAG)=> B /= defB sAB nBG.
rewrite -cycle_subG defB (maxA B) ?trivg_quotient // nBG.
have{defB} defB : B :=: A * <[x]>.
  rewrite -quotientK ?cycle_subG ?quotient_cycle // defB quotientGK //.
  exact: normalS (normal_sub nBG) nsAG.
apply/setIidPl; rewrite ?defB -[_ :&: _]center_prod 1?centsC //=.
rewrite /center !(setIidPl _) //; exact: cycle_abelian.
Qed.

(* The two other assertions of Aschbacher 23.15 state properties of the       *)
(* normal series 1 <| Z = 'Ohm_1(A) <| A with A \in 'SCN(G).                  *)

Section SCNseries.

Variables A : {group gT}.
Hypothesis SCN_A : A \in 'SCN(G).

Let Z := 'Ohm_1(A).
Let cAA := SCN_abelian SCN_A.
Let sZA: Z \subset A := Ohm_sub 1 A.
Let nZA : A \subset 'N(Z) := sub_abelian_norm cAA sZA.

(* This is Aschbacher 23.15(2). *)
Lemma der1_stab_Ohm1_SCN_series : 
  ('C(Z) :&: 'C_G(A / Z | 'Q))^`(1) \subset A.
Proof.
case/SCN_P: SCN_A; case/andP=> sAG nAG defA; rewrite -{4}defA {defA}.
rewrite subsetI {1}setICA comm_subG ?subsetIl //= gen_subG.
apply/subsetP=> w; case/imset2P=> u v.
rewrite -groupV -(groupV _ v) /= astabQR //= -/Z !inE groupV.
case/and4P=> cZu _ _ sRuZ; case/and4P=> cZv' _ _ sRvZ ->{w}.
apply/centP=> a Aa; rewrite /commute -!mulgA (commgCV v) (mulgA u).
rewrite (centP cZu); last by rewrite (subsetP sRvZ) ?mem_commg ?set11 ?groupV.
rewrite 2!(mulgA v^-1) mulKVg 4!mulgA invgK (commgC u^-1) mulgA.
rewrite -(mulgA _ _ v^-1) -(centP cZv') ?(subsetP sRuZ) ?mem_commg ?set11//.
by rewrite -!mulgA invgK mulKVg !mulKg.
Qed.

(* This is Aschbacher 23.15(3); note that this proof does not depend on the   *)
(* maximality of A.                                                           *)
Lemma Ohm1_stab_Ohm1_SCN_series :
  odd p -> p.-group G -> 'Ohm_1('C_G(Z)) \subset 'C_G(A / Z | 'Q).
Proof.
case: (eqsVneq G 1) => [-> | ntG]; first by rewrite !(setIidPl (sub1G _)) Ohm1.
move=> p_odd pG; have{ntG} [p_pr _ _] := pgroup_pdiv pG ntG.
case/SCN_P: SCN_A; case/andP=> sAG nAG _; have pA := pgroupS sAG pG.
have pCGZ : p.-group 'C_G(Z) by rewrite (pgroupS _ pG) // subsetIl.
rewrite {pCGZ}(OhmE 1 pCGZ) gen_subG; apply/subsetP=> x; do 2!case/setIdP.
rewrite -!cycle_subG => sXG cZX xp1 /=; have cXX := cycle_abelian x.
have nZX := cents_norm cZX; have{nAG} nAX := subset_trans sXG nAG.
pose XA := <[x]> <*> A; pose C := 'C(<[x]> / Z | 'Q); pose CA := A :&: C.
pose Y := <[x]> <*> CA; pose W := 'Ohm_1(Y). 
have sXC: <[x]> \subset C by rewrite sub_astabQ nZX (quotient_cents _ cXX).
have defY : Y = <[x]> * CA by rewrite -norm_mulgenEl // normsI ?nAX ?normsG.
have{nAX} defXA: XA = <[x]> * A := norm_mulgenEl nAX.
suffices{sXC}: XA \subset Y.
  rewrite subsetI sXG /= sub_astabQ nZX centsC defY group_modl //= -/Z -/C.
  by rewrite subsetI defXA subxx sub_astabQ quotientMl //= !mulG_subG; case/and3P.
have sZCA: Z \subset CA by rewrite subsetI sZA [C]astabQ sub_cosetpre.
have cZCA: CA \subset 'C(Z) by rewrite subIset 1?(sub_abelian_cent2 cAA).
have sZY: Z \subset Y by rewrite (subset_trans sZCA) ?mulgen_subr.
have{cZCA cZX} cZY: Y \subset 'C(Z) by rewrite mulgen_subG cZX. 
have{cXX nZX} sY'Z : Y^`(1) \subset Z.
  rewrite der1_min ?cents_norm //= -/Y defY quotientMl // abelianM /= -/Z -/CA.
  rewrite !quotient_abelian // ?(abelianS _ cAA) ?subsetIl //=.
  by rewrite /= quotientGI ?Ohm_sub // centsC quotient_astabQ subsetIr.
have{sY'Z cZY} nil_classY: nil_class Y <= 2.
  by rewrite nil_class2 (subset_trans sY'Z ) // subsetI sZY centsC.
have pY: p.-group Y by rewrite (pgroupS _ pG) // mulgen_subG sXG subIset ?sAG.
have sXW: <[x]> \subset W.
  by rewrite [W](OhmE 1 pY) ?genS // sub1set inE -cycle_subG mulgen_subl.
have{nil_classY pY sXW sZY sZCA} defW: W = <[x]> * Z.
  rewrite -[W](setIidPr (Ohm_sub _ _)) /= -/Y {1}defY -group_modl //= -/Y -/W.
  congr (_ * _); apply/eqP; rewrite eqEsubset {1}[Z](OhmE 1 pA).
  rewrite subsetI setIAC subIset //; first by rewrite sZCA -[Z]Ohm_id OhmS.
  rewrite setIdE sub_gen ?setIS //; apply/subsetP=> w Ww; rewrite inE.
  by apply/eqP; apply: exponentP w Ww; exact: exponent_Ohm1_class2.
have{sXG sAG} sXAG: XA \subset G by rewrite mulgen_subG sXG.
have{sXAG} nilXA: nilpotent XA := nilpotentS sXAG (pgroup_nil pG).
have sYXA: Y \subset XA by rewrite defY defXA mulgS ?subsetIl.
rewrite -[Y](nilpotent_sub_norm nilXA) {nilXA sYXA}//= -/Y -/XA.
apply: subset_trans (setIS _ (char_norm_trans (Ohm_char 1 _) (subxx _))) _.
rewrite {XA}defXA -group_modl ?normsG /= -/W ?{W}defW ?mulG_subl //.
rewrite {Y}defY mulgS // {CA}subsetI subsetIl {C}sub_astabQ subIset ?nZA //= -/Z.
rewrite (subset_trans (quotient_subnorm _ _ _)) //= quotient_mulg /= -/Z.
rewrite -quotient_sub1 ?subIset ?cent_norm ?orbT //.
rewrite (subset_trans (quotientI _ _ _)) ?coprime_TIg //.
rewrite (@pnat_coprime p) // -/(pgroup p _) ?quotient_pgroup {pA}//=.
rewrite -(setIidPr (cent_sub _)) [pnat _ _]p'group_quotient_cent_prime //.
by rewrite (dvdn_trans (dvdn_quotient _ _)) ?order_dvdn.
Qed.

End SCNseries.

(* This is Aschbacher 23.16. *)
Lemma Ohm1_cent_max_normal_abelem : forall Z,
    odd p -> p.-group G -> [max Z | (Z <| G) && p.-abelem Z] ->
  'Ohm_1('C_G(Z)) = Z.
Proof.
move=> Z p_odd pG; set X := 'Ohm_1('C_G(Z)).
case/maxgroupP; case/andP=> nsZG abelZ maxZ. 
have [sZG nZG] := andP nsZG; have [_ cZZ expZp] := and3P abelZ.
have{nZG} nsXG: X <| G.
  apply: (char_normal_trans (Ohm_char 1 'C_G(Z))).
  by rewrite /normal subsetIl normsI ?normG ?norms_cent.
have cZX : X \subset 'C(Z) := subset_trans (Ohm_sub _ _) (subsetIr _ _).
have{sZG expZp} sZX: Z \subset X.
  rewrite [X](OhmE 1 (pgroupS _ pG)) ?subsetIl ?sub_gen //.
  apply/subsetP=> x Zx; rewrite !inE  ?(subsetP sZG) ?(subsetP cZZ) //=.
  by rewrite (exponentP expZp).
suffices{sZX} expXp: (exponent X %| p).
  apply/eqP; rewrite eqEsubset sZX andbT -quotient_sub1 ?cents_norm //= -/X.
  have pGq: p.-group (G / Z) by rewrite quotient_pgroup.
  rewrite (nil_TI_Z (pgroup_nil pGq)) ?quotient_normal //= -/X setIC; apply/eqP.
  apply/trivgPn=> [[Zd]]; rewrite inE -!cycle_subG -cycle_eq1 -subG1 /= -/X.
  case/andP; move/sub_center_normal => nsZdG.
  have{nsZdG} [D defD sZD nsDG] := inv_quotientN nsZG nsZdG; rewrite defD.
  have sDG := normal_sub nsDG; have nsZD := normalS sZD sDG nsZG.
  rewrite quotientSGK ?quotient_sub1 ?normal_norm //= -/X => sDX; case/negP.
  rewrite (maxZ D) // nsDG andbA (pgroupS sDG) ?(dvdn_trans (exponentS sDX)) //.
  rewrite center_cyclic_abelian ?center_abelian //.
  have sZZD: Z \subset 'Z(D) by rewrite subsetI sZD centsC (subset_trans sDX).
  rewrite -(isog_cyclic (third_isog sZZD nsZD (center_normal D))) /= -defD.
  by rewrite quotient_cyclic ?cycle_cyclic.
pose normal_abelian := [pred A : {group gT} | (A <| G) && abelian A].
have{nsZG cZZ} normal_abelian_Z : normal_abelian Z by exact/andP.
have{normal_abelian_Z} [A maxA sZA] := maxgroup_exists normal_abelian_Z.
have SCN_A : A \in 'SCN(G) by apply: max_SCN pG maxA.
move/maxgroupp: maxA; case/andP{normal_abelian}=> nsAG cAA.
have pA := pgroupS (normal_sub nsAG) pG.
have{abelZ maxZ nsAG cAA sZA} defA1: 'Ohm_1(A) = Z.
  apply: maxZ; last by rewrite -(Ohm1_id abelZ) OhmS.
  by rewrite Ohm1_abelem ?(char_normal_trans (Ohm_char _ _) nsAG).
have{SCN_A} sX'A: X^`(1) \subset A.
  have sX_CWA1 : X \subset 'C('Ohm_1(A)) :&: 'C_G(A / 'Ohm_1(A) | 'Q).
    rewrite subsetI /X -defA1 (Ohm1_stab_Ohm1_SCN_series _ p_odd) //= andbT.
    exact: subset_trans (Ohm_sub _ _) (subsetIr _ _). 
  by apply: subset_trans (der1_stab_Ohm1_SCN_series SCN_A); rewrite commgSS.
pose genXp := [pred U : {group gT} | ('Ohm_1(U) == U) && ~~(exponent U %| p)].
apply/idPn=> expXp'; have genXp_X: genXp [group of X] by rewrite /= Ohm_id eqxx.
have{genXp_X expXp'} [U] := mingroup_exists genXp_X; case/mingroupP; case/andP.
move/eqP=> defU1 expUp' minU sUX; case/negP: expUp'.
have{nsXG} pU := pgroupS (subset_trans sUX (normal_sub nsXG)) pG.
case gsetU1: (group_set [set x \in U | x ^+ p == 1]).
  rewrite -defU1 (OhmE 1 pU) gen_set_id //.
  by apply/exponentP=> x; case/setIdP=> _; move/eqP.
move: gsetU1; rewrite /group_set inE group1 exp1gn eqxx; case/subsetPn=> xy.
case/imset2P=> x y; case/setIdP=> Ux xp1; case/setIdP=> Uy yp1 ->{xy}.
rewrite inE groupM //= => nt_xyp; pose XY := <[x]> <*> <[y]>.
have{yp1 nt_xyp} defXY: XY = U.
  have sXY_U: XY \subset U by rewrite mulgen_subG !cycle_subG Ux Uy.
  rewrite [XY]minU //= eqEsubset Ohm_sub (OhmE 1 (pgroupS _ pU)) //.
  rewrite /= mulgen_idl mulgen_idr genS; last first.
    by rewrite setIdE subsetI subset_gen subUset !sub1set !inE xp1 yp1.
  apply: contra nt_xyp; move/exponentP=> -> //.
  by rewrite groupMl mem_gen // (set21, set22).
have: <[x]> <|<| U by rewrite nilpotent_subnormal ?(pgroup_nil pU) ?cycle_subG.
case/subnormalEsupport=> [defU | /=].
  by apply: dvdn_trans (exponent_dvdn U) _; rewrite -defU order_dvdn.
set V := <<class_support <[x]> U>>; case/andP=> sVU ltVU.
have{genXp minU xp1 sVU ltVU} expVp: exponent V %| p.
  apply: contraR ltVU => expVp'; rewrite [V]minU //= expVp' eqEsubset Ohm_sub.
  rewrite (OhmE 1 (pgroupS sVU pU)) genS //= setIdE subsetI subset_gen.
  rewrite class_supportEr; apply/bigcupsP=> z _; apply/subsetP=> v Vv.
  by rewrite inE -order_dvdn (dvdn_trans (order_dvdG Vv)) // cardJg order_dvdn.
have{A pA defA1 sX'A V expVp} Zxy: [~ x, y] \in Z.
  rewrite -defA1 (OhmE 1 pA) mem_gen // inE (exponentP expVp). 
    by rewrite (subsetP sX'A) //= mem_commg ?(subsetP sUX).
  by rewrite groupMl -1?[x^-1]conjg1 mem_gen // mem_imset2 // ?groupV cycle_id.
have{Zxy sUX cZX} cXYxy: [~ x, y] \in 'C(XY).
  by rewrite centsC in cZX; rewrite defXY (subsetP (centS sUX)) ?(subsetP cZX).
rewrite -defU1 exponent_Ohm1_class2 // nil_class2 -defXY der1_mulgen_cycles //.
by rewrite subsetI {1}defXY !cycle_subG groupR.
Qed.

Lemma critical_class2 : forall H, critical H G -> nil_class H <= 2.
Proof.
move=> H [chH _ sRZ _].
by rewrite nil_class2 (subset_trans _ sRZ) ?commSg // char_sub.
Qed.

(* This proof of the Thompson critical lemma is adapted from Aschbacher 23.6 *)
Lemma Thompson_critical : p.-group G -> {K : {group gT} | critical K G}.
Proof.
move=> pG; pose qcr A := (A \char G) && ('Phi(A) :|: [~: G, A] \subset 'Z(A)).
have [|K]:= @maxgroup_exists _ qcr 1 _.
  by rewrite /qcr trivg_char center1 commG1 subUset Phi_sub subxx.
case/maxgroupP; rewrite {}/qcr subUset; case/and3P=> chK sPhiZ sRZ maxK _.
have sKG := char_sub chK; have nKG := char_normal chK.
exists K; split=> //; apply/eqP; rewrite eqEsubset andbC setSI //=.
have chZ: 'Z(K) \char G by [exact: subcent_char]; have nZG := char_norm chZ.
have chC: 'C_G(K) \char G by exact: subcent_char (char_refl G) chK.
rewrite -quotient_sub1; last by rewrite subIset // char_norm.
apply/trivgP; apply: (nil_TI_Z (quotient_nil _ (pgroup_nil pG))).
  rewrite quotient_normal // /normal subsetIl normsI ?normG ?norms_cent //.
  exact: char_norm.
apply: TI_Ohm1; apply/trivgP; rewrite -trivg_quotient -sub_cosetpre_quo //.
rewrite morphpreI quotientGK /=; last first.
  by apply: normalS (char_normal chZ); rewrite ?subsetIl ?setSI.
set X := _ :&: _; pose gX := [group of X].
have sXG: X \subset G by rewrite subIset ?subsetIl.
have cXH: gX \subset 'C(K) by rewrite 2?subIset // subxx orbT.
rewrite subsetI cXH andbT -(mul1g K) -mulSG mul1g -(cent_mulgenEl cXH).
rewrite [_ <*> K]maxK ?mulgen_subr //= andbC (cent_mulgenEl cXH).
rewrite -center_prod // (subset_trans _ (mulG_subr _ _)).
  rewrite charM 1?charI ?(char_from_quotient (normal_cosetpre _)) //.
  by rewrite cosetpreK (char_trans _ (center_char _)) ?Ohm_char.
rewrite (@Phi_mulg p) ?(pgroupS _ pG) // subUset commGC commMG; last first.
  by rewrite normsR ?(normsG sKG) // cents_norm // centsC.
rewrite !mul_subG 1?commGC //.
  apply: subset_trans (commgS _ (subsetIr _ _)) _.
  rewrite -quotient_cents2 ?subsetIl // centsC // cosetpreK //.
  by rewrite (subset_trans (Ohm_sub _ _)) // subsetIr.
have nZX := subset_trans sXG nZG; have pX : p.-group gX by exact: pgroupS pG.
rewrite -quotient_sub1 ?(subset_trans (Phi_sub _)) //=.
have pXZ: p.-group (gX / 'Z(K)) by exact: morphim_pgroup.
rewrite (quotient_Phi pX nZX) subG1 (trivg_Phi pXZ).
apply: (abelemS (quotientS _ (subsetIr _ _))); rewrite /= cosetpreK /=.
have pZ: p.-group 'Z(G / 'Z(K)).
  by rewrite (pgroupS (center_sub _)) ?morphim_pgroup.
by rewrite Ohm1_abelem ?center_abelian.
Qed.

Lemma critical_p_stab_Aut : forall H,
  critical H G -> p.-group G -> p.-group 'C(H | 'A_G).
Proof.
move=> H [chH sPhiZ sRZ eqCZ] pG; have sHG := char_sub chH.
pose G' := (sdpair1 'A_G @* G)%G; pose H' := (sdpair1 'A_G @* H)%G.
apply/pgroupP=> q pr_q; case/Cauchy=>//= f cHF; move: (cHF);rewrite astab_ract.
case/setIP=> Af cHFP ofq; rewrite -cycle_subG in cHF; apply: (pgroupP pG) => //.
pose F' := (sdpair2 'A_G @* <[f]>)%G.
have trHF: [~: H', F'] = 1.
  apply/trivgP; rewrite gen_subG; apply/subsetP=> u; case/imset2P=> x' a'.
  case/morphimP=> x Gx Hx ->; case/morphimP=> a Aa Fa -> -> {u x' a'}.
  by rewrite inE commgEl -sdpair_act ?(astab_act (subsetP cHF _ Fa) Hx) ?mulVg.
have sGH_H: [~: G', H'] \subset H'.
  by rewrite -morphimR ?(char_sub chH) // morphimS // commg_subr char_norm.
have{trHF sGH_H} trFGH: [~: F', G', H'] = 1.
  apply: three_subgroup; last by rewrite trHF comm1G.
  by apply/trivgP; rewrite -trHF commSg.
apply/negP=> qG; case: (qG); rewrite -ofq.
suffices ->: f = 1 by rewrite order1 dvd1n.
apply/permP=> x; rewrite perm1; case Gx: (x \in G); last first.
  by apply: out_perm (negbT Gx); case/setIdP: Af.
have Gfx: f x \in G by rewrite -(im_autm Af) -{1}(autmE Af) mem_morphim.
pose y := x^-1 * f x; have Gy: y \in G by rewrite groupMl ?groupV.
have inj1 := injm_sdpair1 'A_G; have inj2 := injm_sdpair2 'A_G.
have Hy: y \in H.
  rewrite (subsetP (center_sub H)) // -eqCZ -cycle_subG.
  rewrite -(injmSK inj1) ?cycle_subG // injm_subcent // subsetI.
  rewrite morphimS ?morphim_cycle ?cycle_subG //=.
  suffices: sdpair1 'A_G y \in [~: G', F'].
    by rewrite commGC; apply: subsetP; exact/commG1P.
  rewrite morphM ?groupV ?morphV //= sdpair_act // -commgEl.
  by rewrite mem_commg ?mem_morphim ?cycle_id.
have fy: f y = y := astabP cHFP _ Hy.
have: (f ^+ q) x = x * y ^+ q.
  elim: (q) => [|i IHi]; first by rewrite perm1 mulg1.
  rewrite expgSr permM {}IHi -(autmE Af) morphM ?morphX ?groupX //= autmE.
  by rewrite fy expgS mulgA mulKVg.
move/eqP; rewrite -{1}ofq expg_order perm1 eq_mulVg1 mulKg -order_dvdn.
case/primeP: pr_q => _ pr_q; move/pr_q; rewrite order_eq1 -eq_mulVg1.
by case: eqP => //= _; move/eqP=> oyq; case: qG; rewrite -oyq order_dvdG.
Qed.

End SCN.

