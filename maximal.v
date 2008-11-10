(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype ssralg bigops.
Require Import seq div prime finfun finset groups morphisms normal group_perm.
Require Import commutators automorphism cyclic pgroups center gprod sylow.
Require Import nilpotent.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Defs.

Variables (gT : finGroupType).
Implicit Types A B D : {set gT}.
Implicit Types G : {group gT}.

Definition maximal A B := [max A of G | G \proper B].

Definition maximal_eq A B := (A == B) || maximal A B.

Definition maxnormal A B D :=
  [max A of G | (G \proper B) && (D \subset 'N(G))].

Definition minnormal A D := [min A of G | (G :!=: 1) && (D \subset 'N(G))].

Definition simple A := minnormal A A.

Definition charsimple A := [min A of G | (G :!=: 1) && (G \char A)].

Definition Frattini A := \bigcap_(G : {group gT} | maximal_eq G A) G.

Canonical Structure Frattini_group A : {group gT} :=
  Eval hnf in [group of Frattini A].

Definition Fitting A := \big[dprod/1]_(p <- primes #|A|) 'O_p(A).

Lemma Fitting_group_set : forall G, group_set (Fitting G).
Proof.
move=> G; suff [F ->]: exists F : {group gT}, Fitting G = F by exact: groupP.
rewrite /Fitting; elim: primes (uniq_primes #|G|) => [_|p r IHr] /=.
  by exists [1 gT]%G; rewrite big_seq0.
case/andP=> rp; case/IHr=> F defF; rewrite big_adds defF.
suffices{IHr}: p^'.-group F && (F <| G).
  case/and3P=> p'F sFG nFG; exists ('O_p(G) <*> F)%G.
  have nFO: 'O_p(G) \subset 'N(F) by exact: (subset_trans (pcore_sub _ _)).
  have trOF: 'O_p(G) :&: F = 1.
    by apply: coprime_TIg; apply: pnat_coprime p'F; exact: pcore_pgroup.
  rewrite /= norm_mulgenEl ?dprodE // (sameP commG1P trivgP) -trOF.
  rewrite subsetI commg_subl commg_subr nFO.
  by rewrite (subset_trans sFG) // normal_norm ?pcore_normal.
move/bigdprodEgen: defF => <- {F}; elim: r rp => [_|q r IHr] /=.
  by rewrite big_seq0 gen0 pgroup1 normal1.
rewrite inE eq_sym big_adds -mulgenE -mulgen_idr; case/norP=> qp.
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

Definition SCN_at n B := [set A \in SCN B | n <= 'm(A)].

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

Section MaxProps.

Variable gT : finGroupType.
Implicit Types G H M : {group gT}.

Lemma maximal_eqP : forall M G,
  reflect (M \subset G  /\
             forall H, M \subset H -> H \subset G -> H :=: M \/ H :=: G)
       (maximal_eq M G).
Proof.
move=> M G; rewrite subEproper /maximal_eq; case: eqP => [->|_]; first left.
  by split=> // H sGH sHG; right; apply/eqP; rewrite eqEsubset sHG.
apply: (iffP maxgroupP) => [] [sMG maxM]; split=> // H.
  by move/maxM=> maxMH; rewrite subEproper; case/predU1P; auto.
by rewrite properEneq; case/andP; move/eqP=> neHG sHG; case/maxM.
Qed.

Lemma maximal_exists : forall H G,
    H \subset G ->
  H :=: G \/ (exists2 M : {group gT}, maximal M G & H \subset M).
Proof.
move=> H G; rewrite subEproper; case/predU1P=> sHG; first by left.
suff [M *]: {M : {group gT} | maximal M G & H \subset M} by right; exists M.
exact: maxgroup_exists.
Qed.

End MaxProps.

Section MorphPreMax.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types Q R : {group rT}.

Lemma morphpre_proper : forall Q R,
  Q \subset f @* D -> R \subset f @* D ->
  (f @*^-1 Q \proper f @*^-1 R) = (Q \proper R).
Proof. by move=> Q R dQ dR; rewrite /proper !morphpreSK. Qed.

Lemma morphpre_maximal : forall Q R,
  Q \subset f @* D -> R \subset f @* D ->
  maximal (f @*^-1 Q) (f @*^-1 R) = maximal Q R.
Proof.
move=> Q R dQ dR.
apply/maxgroupP/maxgroupP; rewrite morphpre_proper //= => [] [sQR maxQ].
  split=> // M sMR sQM; have dM := subset_trans (proper_sub sMR) dR.
  rewrite -(morphpreK dQ) -(maxQ (f @*^-1 M)%G) ?morphpreK ?morphpreSK //.
  by rewrite morphpre_proper.
split=> // M sMR sQM; have dM: M \subset D.
  apply: subset_trans (proper_sub sMR) _; exact: subsetIl.
have defM: f @*^-1 (f @* M) = M.
  apply: morphimGK dM; apply: subset_trans sQM; exact: ker_sub_pre.
rewrite -defM; congr (f @*^-1 _); apply: maxQ.
  by rewrite -defM morphpre_proper ?morphimS in sMR.
by rewrite -(morphpreK dQ) morphimS.
Qed.

Lemma morphpre_maximal_eq : forall Q R,
  Q \subset f @* D -> R \subset f @* D ->
  maximal_eq (f @*^-1 Q) (f @*^-1 R) = maximal_eq Q R.
Proof.
move=> Q R dQ dR.
by rewrite /maximal_eq morphpre_maximal // !eqEsubset !morphpreSK.
Qed.

End MorphPreMax.

Section InjmMax.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Variables G H K : {group gT}.

Hypothesis injf : 'injm f.

Lemma injm_proper :
  G \subset D -> H \subset D -> (f @* G \proper f @* H) = (G \proper H).
Proof.
move=> dG dH; rewrite -(morphpre_invm injf) -(morphpre_invm injf H).
by rewrite morphpre_proper ?morphim_invm.
Qed.

Lemma injm_maximal :
  G \subset D -> H \subset D -> maximal (f @* G) (f @* H) = maximal G H.
Proof.
move=> dG dH; rewrite -(morphpre_invm injf) -(morphpre_invm injf H).
by rewrite morphpre_maximal ?morphim_invm.
Qed.

Lemma injm_maximal_eq :
  G \subset D -> H \subset D -> maximal (f @* G) (f @* H) = maximal G H.
Proof.
by move=> dG dH; rewrite /maximal_eq injm_maximal // !eqEsubset !injmSK.
Qed.

End InjmMax.

Section QuoMax.

Variables (gT : finGroupType) (K G H : {group gT}).

Lemma cosetpre_proper : forall Q R : {group coset_of K},
  (coset K @*^-1 Q \proper coset K @*^-1 R) = (Q \proper R).
Proof. by move=> Q R; rewrite morphpre_proper ?coset_im. Qed.

Lemma cosetpre_maximal : forall Q R : {group coset_of K},
  maximal (coset K @*^-1 Q) (coset K @*^-1 R) = maximal Q R.
Proof. by move=> Q R; rewrite morphpre_maximal ?coset_im. Qed.

Lemma cosetpre_maximal_eq : forall Q R : {group coset_of K},
  maximal_eq (coset K @*^-1 Q) (coset K @*^-1 R) = maximal_eq Q R.
Proof.
by move=> Q R; rewrite /maximal_eq !eqEsubset !cosetpreSK cosetpre_maximal.
Qed.

Lemma quotient_proper :
  K <| G -> K <| H -> (G / K \proper H / K) = (G \proper H).
Proof. by move=> nKG nKH; rewrite -cosetpre_proper ?quotientGK. Qed.

Lemma quotient_maximal :
  K <| G -> K <| H -> maximal (G / K) (H / K) = maximal G H.
Proof. by move=> nKG nKH; rewrite -cosetpre_maximal ?quotientGK. Qed.

Lemma quotient_maximal_eq :
  K <| G -> K <| H -> maximal_eq (G / K) (H / K) = maximal_eq G H.
Proof. by move=> nKG nKH; rewrite -cosetpre_maximal_eq ?quotientGK. Qed.

Lemma properJ : forall x, (G :^ x \proper H :^ x) = (G \proper H).
Proof. by move=> x; rewrite /proper !conjSg. Qed.

Lemma maximalJ : forall x, maximal (G :^ x) (H :^ x) = maximal G H.
Proof.
move=> x; rewrite -{1}(setTI G) -{1}(setTI H) -!morphim_conj.
by rewrite injm_maximal ?subsetT ?injm_conj.
Qed.

Lemma maximal_eqJ : forall x, maximal_eq (G :^ x) (H :^ x) = maximal_eq G H.
Proof. by move=> x; rewrite /maximal_eq !eqEsubset !conjSg maximalJ. Qed.

End QuoMax.

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
have: p.-group (P / M) by exact: morphim_pgroup.
case/pgroup_1Vpr=> /= [->|[pr_p _ [k iM]] _ maxM]; first by case/eqP.
have{k iM}: p %| #|P / M| by rewrite iM dvdn_mulr.
case/Cauchy=> // x; rewrite /order -cycle_subG.
rewrite subEproper; case/predU1P=> [-> // | sxP ox].
by rewrite -ox [<[x]>](maxM _ sxP) ?sub1G ?cards1 in pr_p.
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

Lemma gfunc_Phi : forall (rT : finGroupType) G (f : {morphism G >-> rT}),
  f @* 'Phi(G) \subset 'Phi(f @* G).
Proof.
move=> rT G f; apply/bigcapsP=> M maxM.
rewrite sub_morphim_pre ?Phi_sub //; apply: bigcap_inf.
have defG: f @*^-1 (f @* G) = G by rewrite morphimGK ?subsetIl.
by rewrite -{2}defG morphpre_maximal_eq ?maxM //; case/maximal_eqP: maxM.
Qed.

End Frattini.

Section Frattini0.

Variables (gT : finGroupType) (G : {group gT}).

Lemma Phi_char : 'Phi(G) \char G.
Proof. exact: gfunctor_char Phi_sub gfunc_Phi _ _. Qed.

Lemma Phi_normal : 'Phi(G) <| G.
Proof. exact: char_normal Phi_char. Qed.

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

Lemma abelem_splits : forall G,
  p.-abelem P -> G \subset P -> [splits P, over G].
Proof.
move=> G abP; have: exists K : {group gT}, (K \subset P) && (G :&: K == 1).
  by exists [1 gT]%G; rewrite (setIidPr _) sub1G /=.
case/ex_maxgroup=> K; case/maxgroupP; case/andP=> sKP trGK maxK sGP.
apply/splitsP; exists K; rewrite inE trGK eqEsubset mul_subG //=.
have cKP: P \subset 'C(K).
  by rewrite centsC (subset_trans sKP) //; case/andP: abP; case/andP.
have cKG := subset_trans sGP cKP.
rewrite -cent_mulgenEl //; apply/subsetP=> x Px.
have: p.-group (G <*> K :&: <[x]>)
  by apply: pgroupS (abelem_pgroup abP); rewrite subIset // cycle_subG Px orbT.
case/pgroup_1Vpr=> /= [trGKx | [pr_p geGKp _]]; last first.
  rewrite -cycle_subG (sameP setIidPr eqP) eqEcard subsetIr /=.
  apply: leq_trans geGKp; rewrite dvdn_leq ?ltn_0prime // order_dvd.
  by case/p_abelemP: abP => // _ ->.
rewrite -(maxK (<[x]> <*> K)%G) ?mulgen_subr //.
  by rewrite mulgenC -mulgenA -cycle_subG mulgen_subl.
rewrite mulgen_subG cycle_subG Px sKP /=.
rewrite -(mulg1 G) -(eqP trGK) /= (setIC G) group_modl // setIAC.
rewrite cent_mulgenEl ?(subset_trans _ cKP) ?cycle_subG //= -cent_mulgenEl //.
by rewrite -group_modr ?mulgen_subr // trGKx mul1g setIC.
Qed.

Lemma trivg_Phi : p.-group P -> ('Phi(P) == 1) = p.-abelem P.
Proof.
move=> pP; case/pgroup_1Vpr: (pP) => [P1 | [pr_p _ _]].
  by rewrite P1 p_abelem1 -subG1 -P1 Phi_sub.
apply/eqP/idP=> [trPhi | abP].
  apply/p_abelemP=> //; split=> [|x Px].
    apply/commG1P; apply/trivgP; rewrite -trPhi.
    apply/bigcapsP=> M; case/predU1P=> [-> | maxM]; first exact: der1_subG.
    have [_ nMP] := andP (p_maximal_normal pP maxM).
    have: cyclic (P / M).
      by rewrite cyclic_prime // card_quotient // (p_maximal_index pP).
    case/cyclicP=> Px defP; rewrite -quotient_cents2 // defP.
    rewrite gen_subG centsC gen_subG /= cent_set1 sub1set; exact/cent1P.
  apply/set1gP; rewrite -trPhi; apply/bigcapP=> M.
  case/predU1P=> [-> | maxM]; first exact: groupX.
  have [_ nMP] := andP (p_maximal_normal pP maxM).
  have nMx : x \in 'N(M) by exact: subsetP Px.
  apply: coset_idr; rewrite ?groupX ?morphX //=; apply/eqP.
  rewrite -(p_maximal_index pP maxM) -card_quotient // -order_dvd cardSg //=.
  by rewrite -morphim_cycle ?morphimS ?cycle_subG.
apply/trivgP; apply/subsetP=> x Phi_x; rewrite -cycle_subG.
have Px: x \in P by exact: (subsetP (Phi_sub P)).
have sxP: <[x]> \subset P by rewrite cycle_subG.
case/splitsP: (abelem_splits abP sxP) => K; case/complP=> trKx defP.
case/pgroup_1Vpr: (pgroupS sxP pP) => [/= -> // | [_ gexp _]].
have{abP} [abP elP] := p_abelemP P pr_p abP.
have{elP gexp} ox: #[x] = p.
  by apply/eqP; rewrite eqn_leq gexp dvdn_leq ?ltn_0prime // order_dvd elP.
rewrite /= -trKx subsetI subxx cycle_subG.
apply: (bigcapP Phi_x); apply/orP; right.
apply: p_index_maximal; rewrite -?divgS -defP ?mulG_subr //.
by rewrite (TI_cardMg trKx) mulnK // [#|_|]ox.
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
case/pgroup_1Vpr: pP => [-> | [pr_p _ _]] in sPhiP *.
  by rewrite /= ['Phi(1)](trivgP sPhiP) sub1G der_sub Mho_sub.
have [abP x1P] := p_abelemP _ pr_p Phi_quotient_abelem.
apply/andP; split.
  have nMP: P \subset 'N(P^`(1) <*> 'Mho^1(P)).
    by rewrite norms_mulgen // char_norm ?der_char ?Mho_char.
  rewrite -quotient_sub1 ?(subset_trans sPhiP) //=.
  suffices <-: 'Phi(P / (P^`(1) <*> 'Mho^1(P))) = 1.
    exact: (morphim_gfunctor Phi_sub gfunc_Phi).
  apply/eqP; rewrite (trivg_Phi (morphim_pgroup _ pP)) /= -quotientE.
  apply/p_abelemP=> //; rewrite [abelian _]quotient_cents2 ?mulgen_subl //.
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
Implicit Types P H D : {group gT}.

Lemma morphim_Phi : forall rT P D (f : {morphism D >-> rT}),
  p.-group P -> P \subset D -> f @* 'Phi(P) = 'Phi(f @* P).
Proof.
move=> rT P D f pP sPD; rewrite !(@Phi_mulgen _ p) ?morphim_pgroup //.
rewrite morphim_gen ?(subset_trans _ sPD) ?subUset ?der_sub ?Mho_sub //.
by rewrite morphimU -mulgenE morphimR ?morphim_Mho.
Qed.

Lemma quotient_Phi : forall P H,
  p.-group P -> P \subset 'N(H) -> 'Phi(P) / H = 'Phi(P / H).
Proof. move=> P H; exact: morphim_Phi. Qed.

End Frattini4.

Section Simple.

Implicit Types gT rT : finGroupType.

Lemma simpleP : forall gT (G : {group gT}),
  reflect (G :!=: 1 /\ forall H : {group gT}, H <| G -> H :=: 1 \/ H :=: G)
          (simple G).
Proof.
move=> gT G; apply: (iffP mingroupP); rewrite normG andbT.
  case=> ntG simG; split=> // N; case/andP=> sNG nNG.
  by case: (eqsVneq N 1) => [|ntN]; [left | right; apply: simG; rewrite ?ntN].
case=> ntG simG; split=> // N; case/andP=> ntN nNG sNG.
by case: (simG N) ntN => // [|->]; [exact/andP | case/eqP].
Qed.

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

Lemma quotient_simple : forall gT (G H : {group gT}),
  H <| G -> simple (G / H) = maxnormal H G G.
Proof.
move=> gT G H nHG; apply/simpleP/maxgroupP=> [[ntG simG] | []].
  rewrite andbAC andbC -(quotient_sub1 (normal_norm nHG)) subG1 ntG.
  split=> // N; do 2![case/andP] => sNG ntN nNG sHN.
  case: (simG (N / H)%G) => [|| /= eqNG].
  - apply: quotient_normal; exact/andP.
  - move/trivgP=> trNH; apply/eqP; rewrite eqEsubset sHN andbT.
    by rewrite -quotient_sub1 // (subset_trans sNG) ?normal_norm.
  by case/negP: ntN; rewrite -(quotientSGK _ sHN) ?normal_norm // eqNG.
rewrite andbAC -subG1 (quotient_sub1 (normal_norm nHG)).
case/andP=> _ sGH simG; split=> // NH.
case/(inv_quotientN _) => //= N ->{NH} sHN nNG.
case sGN: (G \subset N); [right | left].
  by congr (_ / H); apply/eqP; rewrite eqEsubset sGN normal_sub.
by rewrite (simG N) ?trivg_quotient // andbAC sGN andbT.
Qed.

Lemma isog_simple : forall gT rT (G : {group gT}) (M : {group rT}),
  G \isog M -> simple G = simple M.
Proof.
move=> gT rT G M eqGM; wlog simM: gT rT G M eqGM / simple M.
  by move=> IH; apply/idP/idP=> sim; move/IH: (sim) ->; rewrite // isog_sym.
rewrite simM; case/simpleP: simM; case/isogP: eqGM => f injf <- ntM simM.
apply/simpleP; split=> [|N nNG].
  by apply: contra ntM; move/eqP=> /= M1; rewrite {3}M1 /= morphim1.
case: (andP nNG); move/(morphim_invm injf) => <- _.
have: f @* N <| f @* G by rewrite morphim_normal.
by case/simM=> /= ->; [left | right]; rewrite (morphim1, morphim_invm).
Qed.

Lemma simple_maxnormal : forall gT (G : {group gT}),
   simple G = maxnormal 1 G G.
Proof.
move=> gT G; rewrite -quotient_simple ?normal1 //.
by rewrite -(isog_simple (quotient1_isog G)).
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
  by rewrite /pnat ltn_0group all_predC has_pred1 Gp.
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

Lemma gfunc_Fitting : forall gT rT (G : {group gT}) (f : {morphism G >-> rT}),
  f @* 'F(G) \subset 'F(f @* G).
Proof. move=> gT rT G f; exact: morphim_Fitting. Qed.

Lemma Fitting_char : forall gT (G : {group gT}), 'F(G) \char G.
Proof. exact: gfunctor_char Fitting_sub gfunc_Fitting. Qed.

Lemma injm_Fitting : forall gT rT (D G : {group gT}) (f : {morphism D >-> rT}),
  'injm f -> G \subset D -> f @* 'F(G) = 'F(f @* G).
Proof. exact: injm_gfunctor Fitting_sub gfunc_Fitting. Qed.

Lemma FittingS : forall gT (G H : {group gT}),
  H \subset G -> H :&: 'F(G) \subset 'F(H).
Proof.
move=> gT G H sHG; rewrite -{2}(setIidPl sHG).
do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom; exact: morphim_Fitting.
Qed.

End FittingFun.

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

Lemma minnormal_exists : forall G H, H :!=: 1 -> G \subset 'N(H) ->
  {M : {group gT} | minnormal M G & M \subset H}.
Proof. by move=> G H ntH nHG; apply: mingroup_exists (H) _; rewrite ntH. Qed.

Lemma abelem_order_p : forall rT (p : nat) (A : {group rT}) x,
  p.-abelem A -> x \in A -> x != 1 -> prime p /\ #[x] = p.
Proof.
move=> rT p A x pA Ax; rewrite -in_set1 -cycle_subG.
have: p.-elt x := mem_p_elt (abelem_pgroup pA) Ax.
case/pgroup_1Vpr=> [/= -> | [pr_p lepx _] _]; first by rewrite subxx.
split=> //; apply/eqP; rewrite eqn_leq lepx dvdn_leq ?ltn_0prime // order_dvd.
by case/p_abelemP: pA => // _ ->.
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
by apply: subset_trans sBA _; case/andP: pA; case/andP.
Qed.

Lemma isog_abelem_card : forall rT (p : nat) G (A : {group rT}),
  p.-abelem G -> isog G A = p.-abelem A && (#|A| == #|G|).
Proof.
move=> rT p G A pG; apply/idP/idP=> [isoAG | ].
  rewrite (isog_card isoAG) eqxx andbT; case/isogP: isoAG => f injf <- {A}.
  case/pgroup_1Vpr: (abelem_pgroup pG) => [G1 | [pr_p _ _]].
     by rewrite {3}G1 morphim1 p_abelem1.
  case/p_abelemP: pG => // abG pG; apply/p_abelemP=> //; split=> [|fx].
    by apply/setIidPl; rewrite // -injm_cent // -morphimIdom (setIidPl _).
  by case/morphimP=> x Gx _ ->{fx}; rewrite -morphX ?pG ?morph1.
elim: {A}_.+1 {-2}A (ltnSn #|A|) => // n IHn A leAn in G pG *.
rewrite ltnS in leAn; case/andP=> pA; move/eqP=> oA.
case/pgroup_1Vpr: (abelem_pgroup pA) => [A1 | [pr_p geAp _]].
  have G1: G :=: 1 by rewrite card1_trivg // -oA A1 cards1.
  apply/isogP; exists (triv_morph rT G).
    by rewrite subIset // G1 subxx.
  by rewrite {5}G1 morphim1.
have{pr_p} lt1p: 1 < p by exact: prime_gt1.
have ntA: A :!=: 1 by rewrite trivg_card_le1 -ltnNge (leq_trans lt1p).
have ntG: G :!=: 1 by rewrite trivg_card1 -oA -trivg_card1.
case/trivgPn: ntG => x Gx; case/(abelem_order_p pG)=> // _ ox.
have [H [sHG oH defG]] := p_abelem_split1 pG Gx.
case/trivgPn: ntA => y Ay; case/(abelem_order_p pA)=> // _ oy.
have [B [sBA oB defA]] := p_abelem_split1 pA Ay.
rewrite (isog_dprod defG defA) //.
  by rewrite isog_cyclic_card ?cycle_cyclic // [#|_|]oy -ox eqxx.
apply: IHn; rewrite ?(p_abelemS sHG, p_abelemS sBA) //=; last first.
  by rewrite oB oH oA ox oy.
by apply: leq_trans leAn; rewrite oB ltn_Pdiv ?oy.
Qed.

Lemma dom_kerP : forall rT1 rT2 (G1 : {group rT1}) (f : {morphism G1 >-> rT2}),
  forall x, x \in G1 -> reflect (f x = 1) (x \in 'ker f).
Proof. move=> rT1 rT2 G1 f x Gx; rewrite 2!inE Gx; exact: set1P. Qed.

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
  rewrite (isog_abelem_card _ (p_abelemS sAG pG)) (p_abelemS sBG) //=.
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

Lemma charsimple_dprodg : forall G, charsimple G ->
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
    by rewrite -(autm_dom Af) morphimEdom imsetS.
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
have sfHG: autm Af @* H \subset G by rewrite -{4}(autm_dom Af) morphimS.
have{minH nHG}: minnormal (autm Af @* H) G.
  apply/mingroupP; rewrite andbC -{1}(autm_dom Af) morphim_norms //=.
  rewrite -subG1 sub_morphim_pre // -kerE ker_autm subG1.
  split=> // N; case/andP=> ntN nNG sNfH.
  have sNG: N \subset G := subset_trans sNfH sfHG.
  apply/eqP; rewrite eqEsubset sNfH sub_morphim_pre //=.
  rewrite -(morphim_invmE (injm_autm Af)) [_ @* N]minH //=.
    rewrite -subG1 sub_morphim_pre /= ?autm_dom // morphpre_invm morphim1.
    rewrite subG1 ntN.
    by rewrite -{1}(invm_dom (injm_autm Af)) /= {2}autm_dom morphim_norms.
  by rewrite sub_morphim_pre /= ?autm_dom // morphpre_invm.
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
  charsimple G -> solvable G -> abelem G.
Proof.
move=> G; case/charsimple_dprodg=> H [sHG simH [I Aut_I defG]] solG.
case/simpleP: simH => ntH simH; pose p := pdiv #|H|.
have pr_p: prime p by rewrite prime_pdiv // ltnNge -trivg_card_le1.
have{solG ntH} abH: abelian H.
  apply/commG1P.
  case/simH: (der_normal H 0) => // perH; have:= forallP solG H.
  by rewrite subsetI sHG [[~: H, H]]perH subxx (negPf ntH).
have{simH} oHp: #|H| = p.
  have [x Hx ox] := Cauchy pr_p (dvdn_pdiv _).
  case: (simH <[x]>%G) => [|/= x1|<- //].
    by rewrite /normal cents_norm 1?centsC cycle_subG ?Hx ?(subsetP abH).
  by rewrite -ox /order x1 cards1 in pr_p.
apply/abelemP; exists p => //; move: (G) defG.
apply big_prop => [_ <-|A1 A2 IH1 IH2 M|f If _ <-]; first exact: p_abelem1.
  case/dprodP=> [[G1 G2 dG1 dG2]]; rewrite dG1 dG2 => defM cG12 _.
  have [abG1 pG1] := p_abelemP G1 pr_p (IH1 G1 dG1).
  have [abG2 pG2] := p_abelemP G2 pr_p (IH2 G2 dG2).
  apply/p_abelemP; rewrite // -{M}defM /abelian !centM !subsetI.
  rewrite !mul_subG // 1?centsC //; split=> // x.
  case/imset2P=> x1 x2 Gx1 Gx2 ->; rewrite expMgn; last exact: (centsP cG12).
  by rewrite pG1 // pG2 // mulg1.
have Af := subsetP Aut_I f If; rewrite -(autmE Af) -morphimEsub //.
apply/p_abelemP; rewrite /abelian ?morphim_cents //; split=> // fx.
case/morphimP=> x Gx Hx ->{fx}; rewrite -morphX 1?((x ^+ p =P 1) _) ?morph1 //.
by rewrite -order_dvd -oHp cardSg // cycle_subG.
Qed.

Lemma minnormal_solvable : forall L G H : {group gT},
  minnormal H L -> H \subset G -> solvable G ->
  [/\ L \subset 'N(H), H :!=: 1  & abelem H].
Proof.
move=> L G H minH sHG solG; have [ntH nHL] := andP (mingroupp minH).
split=> //; apply: (charsimple_solvable (minnormal_charsimple minH)).
exact: solvableS solG.
Qed.

Lemma solvable_norm_abelem : forall L G : {group gT},
  solvable G -> G <| L -> G :!=: 1 ->
  exists H : {group gT}, [/\ H \subset G, H <| L, H :!=: 1 & abelem H].
Proof.
move=> L G solG; case/andP=> sGL nGL ntG.
have [H minH sHG]: {H : {group gT} | minnormal H L & H \subset G}.
  by apply: mingroup_exists; rewrite ntG.
have [nHL ntH abH] := minnormal_solvable minH sHG solG.
by exists H; split; rewrite // /normal (subset_trans sHG).
Qed.

End CharSimple.

              

