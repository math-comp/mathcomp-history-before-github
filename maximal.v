(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype ssralg bigops.
Require Import seq div prime finset groups morphisms normal group_perm.
Require Import commutators automorphism cyclic pgroups center dirprod sylow.
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

Definition minnormal A D := [min A of G | ~~ trivg G && (D \subset 'N(G))].

Definition simple A := minnormal A A.

Definition char_simple A := [min A of G | ~~(G \subset A) && (G \char A)].

Definition Frattini A := \bigcap_(G : {group gT} | maximal_eq G A) G.

Canonical Structure Frattini_group A : {group gT} :=
  Eval hnf in [group of Frattini A].

Definition Fitting A := \big[direct_product/1]_(p <- primes #|A|) 'O_p(A).

Lemma Fitting_group_set : forall G, group_set (Fitting G).
Proof.
move=> G; suff [F ->]: exists F : {group gT}, Fitting G = F by exact: groupP.
rewrite /Fitting; elim: primes (uniq_primes #|G|) => [_|p r IHr] /=.
  by exists [1 gT]%G; rewrite big_seq0.
case/andP=> rp; case/IHr=> F defF; rewrite big_adds defF.
suffices{IHr}: p^'.-group F && (F <| G).
  case/and3P=> p'F sFG nFG; exists ('O_p(G) <*> F)%G.
  have nFO: 'O_p(G) \subset 'N(F) by exact: (subset_trans (pcore_sub _ _)).
  have trOF: trivg ('O_p(G) :&: F).
    by apply: coprime_trivg; apply: pnat_coprime p'F; exact: pcore_pgroup.
  rewrite /= norm_mulgenEl ?dprodGE // (sameP centsP commG1P).
  apply: subset_trans trOF; rewrite subsetI commg_subl commg_subr nFO.
  by rewrite (subset_trans sFG) // normal_norm ?pcore_normal.
move/bigdprodEgen: defF => <- {F}; elim: r rp => [_|q r IHr] /=.
  by rewrite big_seq0 gen0 pgroup1 normal1.
rewrite inE eq_sym big_adds -mulgenE -mulgen_idr; case/norP=> qp.
move/IHr {IHr}; set F := <<_>>; case/andP=> p'F nFG; rewrite norm_mulgenEl.
  rewrite pgroupM p'F normalM ?pcore_normal //= !andbT.
  by apply: subd_pnat (pcore_pgroup q G) => q' _; move/eqnP->.
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

Prenex Implicits maximal simple char_simple critical special extra_special.

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
  by split=> // H sGH sHG; right; apply/eqP; rewrite eqset_sub sHG.
apply: (iffP (maxgroupP _ _)) => [] [sMG maxM]; split=> // H.
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
by rewrite /maximal_eq morphpre_maximal // !eqset_sub !morphpreSK.
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
by move=> dG dH; rewrite /maximal_eq injm_maximal // !eqset_sub !injmSK.
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
by move=> Q R; rewrite /maximal_eq !eqset_sub !cosetpreSK cosetpre_maximal.
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
Proof. by move=> x; rewrite /maximal_eq !eqset_sub !conjSg maximalJ. Qed.

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
rewrite -(quotient_maximal _ nM) ?normal_refl // trivial_quotient in maxM.
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
apply/maxgroupP; rewrite properEcardlt sMP -(LaGrange sMP).
rewrite -{1}(muln1 #|M|) ltn_pmul2l //; split=> // H sHP sMH.
apply/eqP; rewrite eq_sym eqset_sub_card sMH.
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

Lemma Phi_proper : forall G, ~~ trivg G -> 'Phi(G) \proper G.
Proof.
move=> G; move/trivgP; case/maximal_exists: (sub1G G) => [<- //| [M maxM _] _].
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
move=> rT G f; apply/bigcap_inP=> M maxM.
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
move=> G; apply/trivgP; rewrite /trivg -cosetpreSK cosetpre1 /=.
apply/bigcap_inP=> M maxM.
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
  p.-abelem P -> G \subset P -> [splits P over G].
Proof.
move=> G abP; have: exists K : {group gT}, (K \subset P) && trivg (G :&: K).
  by exists [1 gT]%G; rewrite sub1G /trivg subsetIr.
case/ex_maxgroup=> K; case/maxgroupP; case/andP=> sKP trGK maxK sGP.
apply/splitsP; exists K; rewrite inE trGK eqset_sub mul_subG //=.
have cKP: P \subset 'C(K).
  by rewrite centsC (subset_trans sKP) //; case/andP: abP; case/andP.
have cKG := subset_trans sGP cKP.
rewrite -cent_mulgenE //; apply/subsetP=> x Px.
have: p.-group (G <*> K :&: <[x]>)
  by apply: pgroupS (abelem_pgroup abP); rewrite subIset // cycle_subG Px orbT.
case/pgroup_1Vpr=> /= [trGKx | [pr_p geGKp _]]; last first.
  rewrite -cycle_subG (sameP setIidPr eqP) eqset_sub_card subsetIr /=.
  apply: leq_trans geGKp; rewrite dvdn_leq ?ltn_0prime // order_dvd.
  by case/p_abelemP: abP => // _ ->.
rewrite -(maxK (<[x]> <*> K)%G) ?mulgen_subr //.
  by rewrite mulgenC -mulgenA -cycle_subG mulgen_subl.
rewrite mulgen_subG cycle_subG Px sKP /=.
rewrite -(mulg1 G) -(trivgP _ trGK) /= (setIC G) group_modl // setIAC.
rewrite cent_mulgenE ?(subset_trans _ cKP) ?cycle_subG //= -cent_mulgenE //.
by rewrite -group_modr ?mulgen_subr // trGKx mul1g setIC.
Qed.

Lemma trivg_Phi : p.-group P -> trivg 'Phi(P) = p.-abelem P.
Proof.
move=> pP; case/pgroup_1Vpr: (pP) => [P1 | [pr_p _ _]].
  by rewrite P1 p_abelem1 /trivg /= -P1 Phi_sub.
apply/idP/idP=> [trPhi | abP].
  apply/p_abelemP=> //; split=> [|x Px].
    apply/centsP; apply/commG1P; apply: subset_trans trPhi.
    apply/bigcap_inP=> M; case/predU1P=> [-> | maxM]; first exact: der1_subG.
    have [_ nMP] := andP (p_maximal_normal pP maxM).
    have: cyclic (P / M).
      by rewrite cyclic_prime // card_quotient // (p_maximal_index pP).
    case/cyclicP=> Px defP; rewrite -quotient_cents2 // defP.
    rewrite gen_subG centsC gen_subG /= cent_set1 sub1set; exact/cent1P.
  apply/set1P; apply: (subsetP trPhi); apply/bigcapP=> M.
  case/predU1P=> [-> | maxM]; first exact: groupX.
  have [_ nMP] := andP (p_maximal_normal pP maxM).
  have nMx : x \in 'N(M) by exact: subsetP Px.
  apply: coset_idr; rewrite ?groupX ?morphX //=; apply/eqP.
  rewrite -(p_maximal_index pP maxM) -card_quotient // -order_dvd cardSg //=.
  by rewrite -morphim_cycle ?morphimS ?cycle_subG.
apply/subsetP=> x Phi_x; rewrite -cycle_subG.
have Px: x \in P by exact: (subsetP (Phi_sub P)).
have sxP: <[x]> \subset P by rewrite cycle_subG.
case/splitsP: (abelem_splits abP sxP) => K; case/complP=> trKx defP.
case/pgroup_1Vpr: (pgroupS sxP pP) => [/= -> // | [_ gexp _]].
have{abP} [abP elP] := p_abelemP P pr_p abP.
have{elP gexp} ox: #[x] = p.
  by apply/eqP; rewrite eqn_leq gexp dvdn_leq ?ltn_0prime // order_dvd elP.
apply: subset_trans (trKx); rewrite subsetI subset_refl cycle_subG.
apply: (bigcapP _ _ _ Phi_x); apply/orP; right.
apply: p_index_maximal; rewrite -?divgS -defP ?mulG_subr //.
by rewrite (card_mulG_trivP _ _ trKx) divn_mull // [#|_|]ox.
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
apply/eqP; rewrite eqset_sub mulgen_subG.
case/pgroup_1Vpr: pP => [-> | [pr_p _ _]] in sPhiP *.
  by rewrite /= ['Phi(1)](trivgP _ sPhiP) sub1G der_sub Mho_sub.
have [abP x1P] := p_abelemP _ pr_p Phi_quotient_abelem.
apply/andP; split.
  have nMP: P \subset 'N(P^`(1) <*> 'Mho^1(P)).
    by rewrite norms_mulgen // char_norm ?der_char ?Mho_char.
  rewrite -trivg_quotient ?(subset_trans sPhiP) //.
  suffices: trivg 'Phi(P / (P^`(1) <*> 'Mho^1(P))).
    apply: subset_trans; exact: (morphim_gfunctor Phi_sub gfunc_Phi).
  rewrite (trivg_Phi (morphim_pgroup _ pP)) /= -quotientE.
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

Theorem simpleP : forall gT (G : {group gT}),
  reflect (~~ trivg G /\ forall H : {group gT}, H <| G -> H :=: 1 \/ H :=: G)
          (simple G).
Proof.
move=> gT G; apply: (iffP (mingroupP _ _)); rewrite normG andbT.
  case=> ntG simG; split=> // N; case/andP=> sNG nNG.
  case trN: (trivg N); first by left; exact/trivgP.
  by right; apply: simG; rewrite ?trN.
case=> ntG simG; split=> // N; case/andP=> ntN nNG sNG.
by case: (simG N) => // [|N1]; [exact/andP | case/trivgP: ntN].
Qed.

Lemma quotient_simple : forall gT (G H : {group gT}),
  H <| G -> simple (G / H) = maxnormal H G G.
Proof.
move=> gT G H nHG; apply/simpleP/maxgroupP=> [[ntG simG] | []].
  rewrite andbAC andbC -(trivg_quotient (normal_norm nHG)) ntG; split=> // N.
  do 2![case/andP] => sNG ntN nNG sHN.
  case: (simG (N / H)%G) => [|| /= eqNG].
  - apply: quotient_normal; exact/andP.
  - move/trivgP=> trNH; apply/eqP; rewrite eqset_sub sHN andbT.
    by rewrite -trivg_quotient // (subset_trans sNG) ?normal_norm.
  by case/negP: ntN; rewrite -(quotientSGK _ sHN) ?normal_norm // eqNG.
rewrite andbAC (trivg_quotient (normal_norm nHG)); case/andP=> _ sGH simG.
split=> // NH; case/(inv_quotientN _) => //= N -> sHN nNG.
case sGN: (G \subset N); [right | left].
  by congr (_ / H); apply/eqP; rewrite eqset_sub sGN normal_sub.
by rewrite (simG N) ?trivial_quotient // andbAC sGN andbT.
Qed.

Lemma isog_simple : forall gT rT (G : {group gT}) (M : {group rT}),
  G \isog M -> simple G = simple M.
Proof.
move=> gT rT G M eqGM; wlog simM: gT rT G M eqGM / simple M.
  by move=> IH; apply/idP/idP=> sim; move/IH: (sim) ->; rewrite // isog_sym.
rewrite simM; case/simpleP: simM; case/isogP: eqGM => f injf <- ntM simM.
apply/simpleP; split=> [|N nNG].
  by apply: contra ntM; move/trivgP=> /= M1; rewrite {3}M1 /= morphim1.
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
apply/bigcup_inP=> P; case/SylowP=> p _ SylP.
case Gp: (p \in \pi(#|G|)); last first.
  rewrite (trivgP P _) ?sub1G // trivg_card (card_Hall SylP).
  rewrite part_p'nat // (pnat_dvd (cardSg (normal_sub nHG))) //.
  by rewrite /pnat ltn_0group all_predC has_pred1 Gp.
move/nilpotent_Hall_pcore: SylP => ->{P} //.
rewrite -(bigdprodEgen (erefl 'F(G))) sub_gen //.
rewrite -(filter_pi_of (ltnSn _)) big_filter big_mkord.
have le_pG: p < #|G|.+1.
  by rewrite ltnS dvdn_leq //; move: Gp; rewrite mem_primes; case/and3P.
apply: subset_trans (@bigcup_sup _ _ _ _ (Ordinal le_pG) _) => //=.
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
move=> p G; apply/eqP; rewrite eqset_sub pcore_Fitting.
rewrite pcore_max ?pcore_pgroup //.
apply: normalS (normal_sub (Fitting_normal _)) (pcore_normal _ _).
exact: Fitting_max (pcore_normal _ _) (pgroup_nil (pcore_pgroup _ _)).
Qed.

Lemma nilpotent_Fitting : forall G, nilpotent G -> 'F(G) = G.
Proof.
by move=> G nilG; apply/eqP; rewrite eqset_sub Fitting_sub Fitting_max.
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




              

