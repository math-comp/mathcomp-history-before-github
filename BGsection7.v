(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime binomial groups.
Require Import morphisms perm action automorphism normal zmodp cyclic.
Require Import gfunc pgroups nilpotent gprod center commutators.
Require Import maximal sylow hall matrix mxrepresentation BGsection1 BGsection6.
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(* move to groups.v and maybe jordanholder *)
Definition subnormal (gT : finGroupType) (H G : {set gT}) :=
  (H \subset G) && (iter #|G| (fun K => <<class_support H K>>) G == H).

Notation "H <|<| G" := (subnormal H G)
  (at level 70, no associativity) : group_scope.

Prenex Implicits normal.

Notation "pG .-series" :=
    (path (rel_of_simpl_rel [rel G H | pG (gval G) (gval H)]))
  (at level 2, format "pG .-series") : group_scope.

Definition invariant_factor (gT : finGroupType) (A G H : {set gT}) :=
  [&& A \subset 'N(G), A \subset 'N(H) & G <| H].

Notation "A .-invariant" := (invariant_factor A)
  (at level 2, format "A .-invariant") : group_scope.

Section Subnormal.

Variable gT : finGroupType.
Local Notation GT := {group gT}.

(* norm_conj_cent in hall.v should be derived from this. *)
Lemma norm_conj_norm : forall (x : gT) (A B : {set gT}),
  x \in 'N(A) -> (A \subset 'N(B :^ x)) = (A \subset 'N(B)).
Proof. by move=> x A B Nx; rewrite normJ -sub_conjgV (normP _) ?groupV. Qed.

Lemma class_support_subG : forall H G : GT,
  H \subset G -> class_support H G \subset G.
Proof.
move=> H G sHG; rewrite class_supportEr.
by apply/bigcupsP=> x Gx; exact: conj_subG.
Qed.

Lemma sub_class_support : forall H G : GT, H \subset class_support H G.
Proof. by move=> H G; rewrite class_supportEr (bigcup_max 1) ?conjsg1. Qed.

Lemma class_support_id : forall G : GT, class_support G G = G.
Proof.
by move=> G; apply/eqP; rewrite eqEsubset sub_class_support class_support_subG.
Qed.

Let setIgr (H G : GT) := (G :&: H)%G.
Let sub_setIgr : forall (G H : GT), G \subset H -> G = setIgr H G.
Proof. by move=> G H; move/setIidPl; move/group_inj. Qed.

Let path_setIgr : forall (G H : GT) (s : seq GT),
   normal.-series G s -> normal.-series (setIgr H G) (map (setIgr H) s).
Proof.
move=> G H s; elim: s G => //= K s IHs G; do 2![case/andP] => sGK nGK Ksn.
by rewrite /normal setSI ?normsIG ?IHs.
Qed.

Lemma class_support_sub_norm : forall G H K : GT,
  H \subset K -> G \subset 'N(K) -> class_support H G \subset K.
Proof.
move=> G H K sHK nKG; rewrite class_supportEr.
by apply/bigcupsP=> x Gx; rewrite sub_conjg (normsP nKG) ?groupV.
Qed.

Lemma norms_class_support : forall A B C : {set gT},
  A \subset 'N(B) -> A \subset 'N(C) -> A \subset 'N(class_support B C).
Proof.
move=> A B C nBA nCA; apply/subsetP=> x Ax.
rewrite inE sub_conjg class_supportEr; apply/bigcupsP=> y Cy.
rewrite -sub_conjg -conjsgM conjgC conjsgM (normsP nBA) //.
by rewrite bigcup_sup ?memJ_norm ?(subsetP nCA).
Qed.

Lemma subnormalP : forall H G : GT,
  reflect (exists2 s : seq GT, normal.-series H s & last H s = G) (H <|<| G).
Proof.
move=> H G; apply: (iffP andP) => [[sHG snHG] | [s Hsn <-{G}]].
  elim: {G}#|G| {-2}G sHG snHG => [|m IHm] G sHG.
    by exists [::]; last by apply/eqP; rewrite eq_sym.
  rewrite iterSr; case/IHm=> [|s Hsn defG].
    by rewrite sub_gen // class_supportEr (bigD1 1) //= conjsg1 subsetUl.
  exists (rcons s G); rewrite ?last_rcons // -cats1 path_cat Hsn defG /=.
  rewrite /normal gen_subG class_support_subG ?norms_gen //.
  by apply/normsP=> x Gx; exact: class_supportGidr.
set f := fun _ => <<_>>; have idf: iter _ f H == H.
  by elim=> //= m IHm; rewrite (eqP IHm) /f class_support_id genGid.
elim: {s}(size s) {-2}s (eqxx (size s)) Hsn => [[] //= | m IHm s].
case/lastP: s => // s G; rewrite size_rcons last_rcons -cats1 path_cat /=.
set K := last H s => def_m; case/and3P=> Hsn; case/andP=> sKG nKG _.
have:= sKG; rewrite subEproper; case/predU1P=> [<-|prKG]; first exact: IHm.
pose L := [group of f G].
have sHK: H \subset K by case/IHm: Hsn.
have sLK: L \subset K by rewrite gen_subG class_support_sub_norm.
rewrite -(subnK (proper_card (sub_proper_trans sLK prKG))) iter_add iterSr.
have defH: H = setIgr L H by rewrite -sub_setIgr ?sub_gen ?sub_class_support.
have: normal.-series H (map (setIgr L) s) by rewrite defH path_setIgr.
case/IHm=> [|_]; first by rewrite size_map.
by rewrite {1 2}defH last_map (subset_trans sHK) //= (setIidPr sLK); move/eqP->.
Qed.

Lemma subnormal_refl : forall G : GT, G <|<| G.
Proof. by move=> G; apply/subnormalP; exists [::]. Qed.

Lemma subnormal_trans : forall G H K : GT, G <|<| H -> H <|<| K -> G <|<| K.
Proof.
move=> G H K; case/subnormalP=> s1 Gs1 <-; case/subnormalP=> s2 Gs12 <-.
by apply/subnormalP; exists (s1 ++ s2); rewrite ?last_cat // path_cat Gs1.
Qed.

Lemma normal_subnormal : forall G H : GT, G <| H -> G <|<| H.
Proof.
by move=> G H nsGH; apply/subnormalP; exists [:: H]; rewrite //= nsGH.
Qed.

Lemma setI_subnormal : forall G H K : GT,
  K \subset G -> H <|<| G -> H :&: K <|<| K.
Proof.
move=> G H K sKG; case/subnormalP=> s Hs defG; apply/subnormalP.
exists (map (setIgr K) s); first exact: path_setIgr.
rewrite (last_map (setIgr K)) defG.
by apply: val_inj; rewrite /= (setIidPr sKG).
Qed.

Lemma subnormal_sub : forall G H : GT, H <|<| G -> H \subset G.
Proof. by move=> G H; case/andP. Qed.

Lemma nilpotent_subnormal : forall G H : GT,
  nilpotent G -> H \subset G -> H <|<| G.
Proof.
move=> G H; elim: {H}_.+1 {-2}H (ltnSn (#|G| - #|H|)) => // m IHm H.
rewrite ltnS -subSS => leGHm nilG sHG; pose K := 'N_G(H).
case/orP: (orbN (K \subset H)) => [|nsKH].
  move/(nilpotent_sub_norm nilG)=> -> //; exact: subnormal_refl.
have nsHK: H <| K by rewrite normalSG.
have sKG: K \subset G by exact: subsetIl.
apply: (subnormal_trans (normal_subnormal nsHK)); apply: IHm => //.
rewrite -(leq_subS (subset_leq_card sKG)) (leq_trans _ leGHm) ?leq_sub2l //.
by rewrite proper_card // /proper normal_sub.
Qed.

Lemma invariant_subnormal : forall A G H : GT,
    A \subset 'N(G) -> A \subset 'N(H) -> H <|<| G ->
  exists2 s : seq GT, (A.-invariant).-series H s & last H s = G.
Proof.
move=> A G H nGA nHA; case/andP; move: #|G| => m.
elim: m => [|m IHm] in G nGA * => sHG.
  by rewrite eq_sym; exists [::]; last exact/eqP.
rewrite iterSr; set K := <<_>>.
have nKA: A \subset 'N(K) by rewrite norms_gen ?norms_class_support.
have sHK: H \subset K by rewrite sub_gen ?sub_class_support.
case/IHm=> // s Hsn defK; exists (rcons s G); last by rewrite last_rcons.
rewrite -cats1 path_cat Hsn /= -!andbA defK nGA nKA.
rewrite gen_subG class_support_subG ?norms_gen //.
apply/normsP; exact: class_supportGidr.
Qed.

Lemma subnormalEsupport : forall G H : GT,
  H <|<| G -> H :=: G \/ <<class_support H G>> \proper G.
Proof.
move=> G H; case/andP=> sHG; set K := <<_>>; move/eqP <-.
have: K \subset G by rewrite gen_subG class_support_subG.
rewrite subEproper; case/predU1P=> [defK|]; [left | by right].
by elim: #|G| => //= _ ->.
Qed.

Lemma subnormalEr : forall G H : GT,
  H <|<| G -> H :=: G \/ (exists K : GT, [/\ H <|<| K, K <| G & K \proper G]).
Proof.
move=> G H; case/subnormalP=> s Hs <-{G}.
elim/last_ind: s Hs => [|s G IHs]; first by left.
rewrite last_rcons -cats1 path_cat /= andbT; set K := last H s.
case/andP=> Hs nsKG; have:= normal_sub nsKG; rewrite subEproper.
case/predU1P=> [<- | prKG]; [exact: IHs | right; exists K; split=> //].
by apply/subnormalP; exists s.
Qed.

Lemma subnormalEl : forall G H : GT,
  H <|<| G -> H :=: G \/ (exists K : GT, [/\ H <| K, K <|<| G & H \proper K]).
Proof.
move=> G H; case/subnormalP=> s Hs <-{G}.
elim: s H Hs => /= [|K s IHs] H; first by left.
case/andP=> nsHK Ks; have:= normal_sub nsHK; rewrite subEproper.
case/predU1P=> [-> | prHK]; [exact: IHs | right; exists K; split=> //].
by apply/subnormalP; exists s.
Qed.

End Subnormal.
Implicit Arguments subnormalP [gT G H].
Prenex Implicits subnormal subnormalP.

(* to be moved to morphisms *)
Lemma morphim_subnormal : forall (aT rT : finGroupType) (D : {group aT}),
                          forall (f : {morphism D >-> rT}) (G H : {group aT}),
  G <|<| H -> f @* G <|<| f @* H.
Proof.
move=> aT rT D f G H; case/subnormalP=> s Gs <-{H}; apply/subnormalP.
elim: s G Gs => [|K s IHs] G /=; first by exists [::].
case/andP=> nsGK; case/IHs=> fs Gfs <-.
by exists (f @* K :: fs)%G; rewrite /= ?morphim_normal.
Qed.

Lemma quotient_subnormal : forall (gT : finGroupType) (G H K : {group gT}),
  G <|<| H -> G / K <|<| H / K.
Proof. by move=> gT G H K; exact: morphim_subnormal. Qed.

(* To be moved to pgroups *)
Section P_rank.

Variable gT : finGroupType.
Implicit Types G H K L A E P : {group gT}.
Implicit Types p q : nat.

Lemma bigmax_leqP : forall (I : finType) (P : pred I) m F,
  reflect (forall i, P i -> F i <= m) (\max_(i | P i) F i <= m).
Proof.
move=> I P m F; apply: (iffP idP) => leFm => [i Pi|].
  by apply: leq_trans leFm; exact: leq_bigmax_cond.
by apply big_prop => // m1 m2; rewrite leq_maxl => ->.
Qed.

Lemma bigmax_sup : forall (I : finType) i0 (P : pred I) m F,
  P i0 -> m <= F i0 -> m <= \max_(i | P i) F i.
Proof.
by move=> I i0 P m F Pi0 le_m_Fi0; exact: leq_trans (leq_bigmax_cond i0 Pi0).
Qed.
Implicit Arguments bigmax_sup [I P m F].

Lemma prime_TIg : forall G H, prime #|G| -> ~~ (G \subset H) -> G :&: H = 1.
Proof.
move=> G H; case/primeP=> _; move/(_ _ (cardSg (subsetIl G H))).
rewrite (sameP setIidPl eqP) eqEcard subsetIl -ltnNge ltn_neqAle -trivg_card1.
by case/predU1P=> ->.
Qed.

Lemma lognSg : forall p G H, G \subset H -> logn p #|G| <= logn p #|H|.
Proof. by move=> p G H sGH; rewrite dvdn_leq_log ?cardSg. Qed.

Lemma commg_subI : forall G H K L,
  G \subset 'N_K(L) -> H \subset 'N_L(K) -> [~: G, H] \subset K :&: L.
Proof.
move=> G H K L; rewrite !subsetI -commg_subr -commg_subl.
case/andP=> sGK sRL; case/andP=> sHL sRK.
by rewrite (subset_trans _ sRK) ?commSg // (subset_trans _ sRL) ?commgS.
Qed.

Lemma pElemS : forall p G H, G \subset H -> 'E_p(G) \subset 'E_p(H).
Proof.
move=> p G H sGH; apply/subsetP=> E; rewrite !inE.
by case/andP; move/subset_trans->.
Qed.

Lemma pnElemS : forall p n G H,
  G \subset H -> 'E_p^n(G) \subset 'E_p^n(H).
Proof.
move=> p n G H sGH; apply/subsetP=> E; rewrite !inE -!andbA.
by case/andP; move/subset_trans->.
Qed.

Lemma pmaxElemS : forall p G H,
  G \subset H -> 'E*_p(H) :&: subgroups G \subset 'E*_p(G).
Proof.
move=> p G H sGH; apply/subsetP=> E; rewrite !inE.
case/andP; case/maxgroupP; case/andP=> _ abelE maxE sEG.
apply/maxgroupP; rewrite sEG; split=> // E'.
by case/andP=> sE'G abelE'; apply: maxE; rewrite (subset_trans sE'G).
Qed.

Lemma p_rank_pi' : forall p G, p \notin \pi(#|G|) -> 'm_p(G) = 0.
Proof.
move=> p G; rewrite mem_primes cardG_gt0 /= => pi'p.
apply: big1_seq => E; rewrite inE -andbA; case/andP=> sEG _.
rewrite lognE; case: ifP => //; case/and3P=> p_pr _ pE; case/negP: pi'p.
by rewrite p_pr (dvdn_trans pE (cardSg sEG)).
Qed.

Lemma p_rank1 : forall p, 'm_p([1 gT]) = 0.
Proof. by move=> p; rewrite p_rank_pi' ?cards1. Qed.

Lemma grank1 : 'm([1 gT]) = 0.
Proof. by rewrite ['m(1)]big1_seq // => p _; rewrite p_rank1. Qed.

Lemma orderE : forall x : gT, #[x] = #|<[x]>|. Proof. by []. Qed.

Lemma logn_le_p_rank : forall p G E, E \in 'E_p(G) -> logn p #|E| <= 'm_p(G).
Proof. by move=> p G E EpG_E; rewrite (bigmax_sup E). Qed.

Lemma p_rank_witness : forall p G, exists E, E \in 'E_p^('m_p(G))(G).
Proof.
move=> p G; have [E EG_E mE]: {E | E \in 'E_p(G) & 'm_p(G) = logn p #|E| }.
  by apply: eq_bigmax_cond; rewrite (cardD1 1%G) inE sub1G p_abelem1.
by exists E; rewrite inE EG_E -mE /=.
Qed.

Lemma p_rank_le_grank : forall p G, 'm_p(G) <= 'm(G).
Proof.
move=> p G; case/orP: (orbN (p \in \pi(#|G|))); last by move/p_rank_pi'->.
rewrite mem_primes; case/and3P=> p_pr _ pG.
have lepg: p < #|G|.+1 by rewrite ltnS dvdn_leq.
by rewrite ['m(G)]big_mkord (bigmax_sup (Ordinal lepg)).
Qed.

Lemma grank_witness : forall G, exists2 p, prime p & 'm(G) = 'm_p(G).
Proof.
move=> G; have [p _ defmG]: {p : 'I_(#|G|.+1) | true & 'm(G) = 'm_p(G)}.
  by rewrite ['m(G)]big_mkord; apply: eq_bigmax_cond; rewrite card_ord.
case p_pr: (prime p); first by exists p.
rewrite p_rank_pi' ?mem_primes ?p_pr // in defmG.
by exists 2 => //; apply/eqP; rewrite eqn_leq p_rank_le_grank defmG.
Qed.

Lemma grank_gt0 : forall G, ('m(G) > 0) = (G :!=: 1).
Proof.
move=> G; case: (eqsVneq G 1) => [-> |]; first by rewrite grank1 eqxx.
case: (trivgVpdiv G) => [-> | [p p_pr]]; first by case/eqP.
case/Cauchy=> // x Gx oxp ->; apply: leq_trans (p_rank_le_grank p G).
have EpGx: <[x]>%G \in 'E_p(G).
  by rewrite inE cycle_subG Gx p_abelemE // cycle_abelian -oxp exponent_dvdn.
by apply: leq_trans (logn_le_p_rank EpGx); rewrite -orderE oxp logn_prime ?eqxx.
Qed.

Lemma grank_pgroup : forall p G, p.-group G -> 'm(G) = 'm_p(G).
Proof.
move=> p G pG; apply/eqP; rewrite eqn_leq p_rank_le_grank andbT.
rewrite ['m(G)]big_mkord; apply/bigmax_leqP=> [[q /= _] _].
case: (eqVneq q p) => [-> //| ne_q_p]; rewrite p_rank_pi' // mem_primes.
by apply: contra ne_q_p; case/and3P=> q_pr _; apply: (pgroupP _ _ pG).
Qed.

Lemma p_rank_abelem : forall p G, p.-abelem G -> 'm_p(G) = logn p #|G|.
Proof.
move=> p G abelG; apply/eqP; rewrite eqn_leq andbC (bigmax_sup G) //.
  by apply/bigmax_leqP=> E; rewrite inE; case/andP; move/lognSg->.
by rewrite inE subxx.
Qed.

Lemma grank_abelem : forall p G, p.-abelem G -> 'm(G) = logn p #|G|.
Proof.
move=> p G abelG; have [_ pG] := andP abelG.
by rewrite (grank_pgroup pG) p_rank_abelem.
Qed.

Lemma p_rankS : forall p G H, G \subset H -> 'm_p(G) <= 'm_p(H).
Proof.
move=> p G H sGH; apply/bigmax_leqP=> E; move/(subsetP (pElemS p sGH)) => EpH_E.
by rewrite (bigmax_sup E).
Qed.

Lemma exponentJ : forall G x, exponent (G :^ x) = exponent G.
Proof.
move=> G x; rewrite /exponent (reindex_inj (conjg_inj x)).
by apply: eq_big => [y | y _]; rewrite ?orderJ ?memJ_conjg.
Qed.

Lemma abelemJ : forall G x, abelem (G :^ x) = abelem G.
Proof. by move=> G x; rewrite /abelem exponentJ abelianJ pgroupJ. Qed.

Lemma p_abelemJ : forall p G x, p.-abelem (G :^ x) = p.-abelem G.
Proof. by move=> p G x; rewrite /p_abelem abelemJ pgroupJ. Qed.

Lemma p_rankJ : forall p G x, 'm_p(G :^ x) = 'm_p(G).
Proof.
move=> p G x; rewrite /p_rank.
rewrite (reindex_inj (@act_inj _ _ _ 'JG x)).
by apply: eq_big => [E | E _]; rewrite ?cardJg // !inE conjSg p_abelemJ.
Qed.

Lemma grankJ : forall G x, 'm(G :^ x) = 'm(G).
Proof.
by move=> G x; rewrite /rank cardJg; apply: eq_bigr => p _; rewrite p_rankJ.
Qed.

Lemma grankS : forall G H, G \subset H -> 'm(G) <= 'm(H).
Proof.
move=> G H sGH; rewrite /rank !big_mkord; apply/bigmax_leqP=> p _.
have leGH: #|G| < #|H|.+1 by rewrite ltnS subset_leq_card.
by rewrite (bigmax_sup (widen_ord leGH p)) // p_rankS.
Qed.

Lemma p_rank_Sylow : forall p G P, p.-Sylow(G) P -> 'm_p(G) = 'm_p(P).
Proof.
move=> p G P sylP; apply/eqP; rewrite eqn_leq (p_rankS _ (pHall_sub sylP)).
rewrite andbT; apply/bigmax_leqP=> E; rewrite inE; case/andP=> sEG abelE.
have [P1 sylP1 sEP1] := Sylow_superset sEG (abelem_pgroup abelE).
have [x _ ->] := Sylow_trans sylP1 sylP.
by rewrite p_rankJ -(p_rank_abelem abelE) (p_rankS _ sEP1).
Qed.

Lemma Ohm1_p_abelian : forall p G,
  p.-group G -> abelian G -> p.-abelem ('Ohm_1(G)).
Proof.
move=> p G pG abG; rewrite /p_abelem Ohm_abelian ?(pgroup_p pG) //.
by rewrite (pgroupS (Ohm_sub 1 G)).
Qed.

Lemma Ohm1_id : forall p G, p.-abelem G -> 'Ohm_1(G) = G.
Proof.
move=> p G; case/andP=> abelG pG; have [abG _] := andP abelG.
by apply/abelem_Ohm1P=> //; exact: (pgroup_p pG).
Qed.

Lemma Ohm_id: forall n G, 'Ohm_n('Ohm_n(G)) = 'Ohm_n(G).
Proof.
move=> n G; apply/eqP; rewrite eqEsubset Ohm_sub genS //.
by apply/subsetP=> x; case/setIdP=> Gx oxn; rewrite inE mem_gen // inE Gx.
Qed.

Lemma p_rank_Ohm1 : forall p G, 'm_p('Ohm_1(G)) = 'm_p(G).
Proof.
move=> p G; apply/eqP; rewrite eqn_leq p_rankS ?Ohm_sub //.
apply/bigmax_leqP=> E; rewrite inE; case/andP=> sEG abelE.
by rewrite (bigmax_sup E) // inE -{1}(Ohm1_id abelE) OhmS.
Qed.

Lemma eq_piP : forall m n, \pi(m) =i \pi(n) <-> \pi(m) = \pi(n).
Proof.
rewrite /pi_of => m n; have eqs := eq_sorted_irr ltn_trans ltnn.
by split=> [|-> //]; move/(eqs _ _ (sorted_primes m) (sorted_primes n)) ->.
Qed.

Lemma piSg : forall G H, G \subset H -> {subset \pi(#|G|) <= \pi(#|H|)}.
Proof.
move=> G H sGH p; rewrite !mem_primes !cardG_gt0; case/and3P=> -> _ pG.
exact: dvdn_trans (cardSg sGH).
Qed.

Lemma piOhm1 : forall G, \pi(#|'Ohm_1(G)|) = \pi(#|G|).
Proof.
move=> G; apply/eq_piP => p; apply/idP/idP; first exact: (piSg (Ohm_sub 1 G)).
rewrite !mem_primes !cardG_gt0; case/andP=> p_pr; case/Cauchy=> // x Gx oxp.
by rewrite p_pr -oxp order_dvdG //= Ohm1Eprime mem_gen // inE Gx oxp.
Qed.

Lemma nil_meet_Z : forall G H,
  nilpotent G -> H <| G -> H :!=: 1 -> H :&: 'Z(G) != 1.
Proof. by move=> G H nilG nsHG; apply: contra; move/eqP; move/nil_TI_Z->. Qed.

Lemma pi_center_nilpotent : forall G, nilpotent G -> \pi(#|'Z(G)|) = \pi(#|G|).
Proof.
move=> G nilG; apply/eq_piP => p.
apply/idP/idP=> [|pG]; first exact: (piSg (center_sub _)).
move: (pG); rewrite !mem_primes !cardG_gt0; case/andP=> p_pr _.
pose Z := 'O_p(G) :&: 'Z(G); have ntZ: Z != 1.
  rewrite nil_meet_Z ?pcore_normal // trivg_card_le1 -ltnNge.
  rewrite (card_Hall (nilpotent_pcore_Hall p nilG)) p_part.
  by rewrite (ltn_exp2l 0 _ (prime_gt1 p_pr)) logn_gt0.
have pZ: p.-group Z := pgroupS (subsetIl _ _) (pcore_pgroup _ _).
have{ntZ pZ} [_ pZ _] := pgroup_pdiv pZ ntZ.
by rewrite p_pr (dvdn_trans pZ) // cardSg ?subsetIr.
Qed.

Lemma grank_Ohm1 : forall G, 'm('Ohm_1(G)) = 'm(G).
Proof.
move=> G; apply/eqP; rewrite eqn_leq grankS ?Ohm_sub // /rank !big_mkord.
apply/bigmax_leqP=> [[p /= _] _]; case pi_p: (p \in \pi(#|G|)); last first.
  by rewrite p_rank_pi' ?pi_p.
move: pi_p; rewrite -piOhm1 mem_primes; case/and3P=> p_pr _ pOhm1.
have lepG1: p < #|'Ohm_1(G)|%G.+1 by rewrite ltnS dvdn_leq.
by rewrite (bigmax_sup (Ordinal lepG1)) ?p_rank_Ohm1.
Qed.

Lemma abelem_pnElem : forall p n G,
  p.-abelem G -> n <= logn p #|G| -> exists E, E \in 'E_p^n(G).
Proof.
move=> p n G abelG; elim: n => [|n IHn].
  by exists 1%G; rewrite !inE sub1G p_abelem1 cards1 logn1.
rewrite ltn_neqAle eq_sym; case/andP=> ndimGn le_n_G.
case/andP: (abelG); case/andP=> abG _ pG.
have [D] := IHn le_n_G; rewrite !inE -andbA; case/and3P=> sDG _ dimHn.
have nsDG: D <| G by rewrite /normal cents_norm // 1?centsC (subset_trans sDG).
have: D :!=: G by apply: contra ndimGn; move/eqP <-.
rewrite eqEsubset sDG -quotient_sub1 ?normal_norm //= subG1.
case/(pgroup_pdiv (quotient_pgroup _ pG)) => p_pr.
case/Cauchy=> // Hx G_Hx oHx _; rewrite -cycle_subG in G_Hx.
case/inv_quotientS: G_Hx => // E defHx sDE sEG; exists E.
rewrite 2!inE sEG (p_abelemS sEG) // -(LaGrange sDE) logn_mul //.
rewrite -card_quotient ?(subset_trans _ (normal_norm nsDG)) //.
by rewrite -defHx addnC [#|_|]oHx logn_prime ?eqxx.
Qed.

Lemma p_rank_geP : forall p n G,
 reflect (exists E, E \in 'E_p^n(G)) (n <= 'm_p(G)).
Proof.
move=> p n G; apply: (iffP idP) => [|[E]]; last first.
  by rewrite inE; case/andP=> Ep_E; move/eqP <-; rewrite (bigmax_sup E).
have [D] := p_rank_witness p G; rewrite 2!inE -andbA.
case/and3P=> sDG abelD; move/eqP => <-; case/abelem_pnElem=> // E.
by exists E; exact: (subsetP (pnElemS _ _ sDG)).
Qed.

Lemma nElemP : forall n G E,
  reflect (exists p, E \in 'E_p^n(G)) (E \in 'E^n(G)).
Proof.
move=> n G E; rewrite ['E^n(G)]big_mkord.
apply: (iffP bigcupP) => [[[p /= _] _] | [p]] EpnG_E; first by exists p.
case: (eqVneq E 1%G) (EpnG_E) => [-> | ntE].
  rewrite inE cards1 logn1; case/andP=> _ n0; exists ord0 => //.
  by rewrite !inE sub1G p_abelem1.
rewrite !inE -2!andbA; case/and4P=> sEG _; case/pgroup_pdiv => // _ pE _ _.
suffices lepG: p < #|G|.+1  by exists (Ordinal lepG).
by rewrite ltnS dvdn_leq ?(dvdn_trans _ (cardSg sEG)).
Qed.

Lemma nElemS : forall n G H, G \subset H -> 'E^n(G) \subset 'E^n(H).
Proof.
move=> n G H sGH; apply/subsetP=> E; case/nElemP=> p EpnG_E.
by apply/nElemP; exists p; rewrite // (subsetP (pnElemS _ _ sGH)).
Qed.

Lemma def_pnElem : forall p n G, 'E_p^n(G) = 'E_p(G) :&: 'E^n(G).
Proof.
move=> p n G; apply/setP=> E; rewrite !inE.
case sEG: (E \subset G) => //; case abelE: (p.-abelem E) => //=.
case: (eqVneq E 1%G) => [-> | ntE].
  rewrite cards1 logn1; apply/idP/nElemP=> [n0 | [q]].
    by exists 2; rewrite // !inE sub1G p_abelem1 cards1 logn1.
  by rewrite inE cards1 logn1; case/andP.
have [p_pr pE _] := pgroup_pdiv (abelem_pgroup abelE) ntE.
apply/idP/nElemP=> [dimEn | [q]]; first by exists p; rewrite !inE sEG abelE.
rewrite !inE -2!andbA; case/and4P=> _ _ qE.
by rewrite (eqnP (pgroupP _ _ qE p p_pr pE)).
Qed.

Lemma grank_geP : forall n G, reflect (exists E, E \in 'E^n(G)) (n <= 'm(G)).
Proof.
move=> n G; apply: (iffP idP) => [|[E]].
  have [p _ ->] := grank_witness G; case/p_rank_geP=> E.
  by rewrite def_pnElem; case/setIP; exists E.
case/nElemP=> p; rewrite inE; case/andP=> EpG_E; move/eqP <-.
by rewrite (leq_trans (logn_le_p_rank EpG_E)) ?p_rank_le_grank.
Qed.

Lemma pnElemI : forall p n G H, 'E_p^n(G :&: H) = 'E_p^n(G) :&: subgroups H.
Proof.
move=> p n G H; apply/setP=> E; rewrite !inE subsetI -!andbA; do !bool_congr.
Qed.

Lemma pElemI : forall p G H, 'E_p(G :&: H) = 'E_p(G) :&: subgroups H.
Proof.
move=> p G H; apply/setP=> E; rewrite !inE subsetI -3!andbA; do !bool_congr.
Qed.

Lemma nElemI : forall n G H, 'E^n(G :&: H) = 'E^n(G) :&: subgroups H.
Proof.
move=> n G H; apply/setP=> E; apply/nElemP/setIP=> [[p] | []].
  by rewrite pnElemI; case/setIP; split=> //; apply/nElemP; exists p.
by case/nElemP=> p EpnG_E sHE; exists p; rewrite pnElemI inE EpnG_E.
Qed.

Section SubAbelian.

Variables G H : {group gT}.
Hypothesis cGG : abelian G.

Lemma sub_abelian_cent : H \subset G -> G \subset 'C(H).
Proof. by move=> sHG; rewrite centsC (subset_trans sHG). Qed.

Lemma sub_abelian_norm : H \subset G -> G \subset 'N(H).
Proof. by move=> sHG; rewrite cents_norm ?sub_abelian_cent. Qed.

Lemma sub_abelian_normal : (H \subset G) = (H <| G).
Proof.
by rewrite /normal; case sHG: (H \subset G); rewrite // sub_abelian_norm.
Qed.

End SubAbelian.

Definition dim_gen (A : {set gT}) := #|gT| - \max_(B | <<~: B>> == A) #|B|.

Lemma dim_gen_min : forall B : {set gT}, dim_gen <<B>> <= #|B|.
Proof.
by move=> B; rewrite cardsCs leq_sub2l // (bigmax_sup (~: B)) ?setCK.
Qed.

Lemma dim_gen_witness : forall G, {B | <<B>> = G & #|B| = dim_gen G}.
Proof.
move=> G; have: 0 < #|[pred B | <<~: B>> == G]|.
  by rewrite lt0n; apply/existsP; exists (~: G); rewrite /= setCK genGid.
case/(eq_bigmax_cond (fun B : {set gT} => #|B|)) => B /= defG def_d.
by exists (~: B); [exact/eqP | rewrite cardsCs setCK -def_d].
Qed.

End P_rank.

Section Morph_p_rank.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Types G H E : {group aT}.

Lemma exponent_morphim : forall G, exponent (f @* G) %| exponent G.
Proof.
move=> G; apply/exponentP=> fx; case/morphimP=> x Dx Gx ->{fx}.
by rewrite -morphX // (exponentP _ _ (dvdnn _)) // morph1.
Qed.

Lemma morphim_p_abelem : forall p G, p.-abelem G -> p.-abelem (f @* G).
Proof.
move=> p G; case: (eqsVneq G 1) => [-> | ntG] abelG.
  by rewrite morphim1 p_abelem1.
have [p_pr _ _] := pgroup_pdiv (abelem_pgroup abelG) ntG.

case/p_abelemP: abelG => // abG elemG.
apply/p_abelemP; rewrite ?morphim_abelian //; split=> // fx.
by case/morphimP=> x Dx Gx ->{fx}; rewrite -morphX // elemG ?morph1.
Qed.

Lemma morphim_abelem : forall G, abelem G -> abelem (f @* G).
Proof.
move=> G; case/abelemP=> p p_pr abelG; apply/abelemP; exists p => //.
exact: morphim_p_abelem abelG.
Qed.

End Morph_p_rank.

Section InitialReduction.

Implicit Type gT : finGroupType.

Record minSimpleOddGroupMixin gT : Prop := MinSimpleOddGroupMixin {
  _ : odd #|[set: gT]|;
  _ : simple [set: gT];
  _ : ~~ solvable [set: gT];
  _ : forall M : {group gT}, M \proper [set: gT] -> solvable M
}.

Structure minSimpleOddGroupType := MinSimpleOddGroupType {
  minSimpleOddGroupType_base :> finGroupType;
  _ : minSimpleOddGroupMixin minSimpleOddGroupType_base
}.

Hypothesis IH_FT : minSimpleOddGroupType -> False.

Lemma minSimpleOdd_ind : forall gT (G : {group gT}), odd #|G| -> solvable G.
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT G *; rewrite ltnS => leGn oddG.
have oG: #|[subg G]| = #|G| by rewrite (isog_card (isog_subg G)).
apply/idPn=> nsolG; case: IH_FT; exists [finGroupType of subg_of G].
do [split; rewrite ?oG //=] => [||M].
- rewrite -(isog_simple (isog_subg _)); apply/simpleP; split=> [|H nsHG].
    by apply: contra nsolG; move/eqP->; rewrite abelian_sol ?abelian1.
  have [sHG _]:= andP nsHG; apply/pred2P; apply: contraR nsolG; case/norP=> ntH.
  rewrite eqEcard sHG -ltnNge (series_sol nsHG) => ltHG.
  by rewrite !IHn ?(oddSg sHG) ?quotient_odd ?(leq_trans _ leGn) ?ltn_quotient.
- by apply: contra nsolG => solG; rewrite -(sgvalEdom G) morphim_sol.
rewrite properEcard oG; case/andP=> sMG ltMG.
by apply: IHn (leq_trans ltMG leGn) (oddSg sMG _); rewrite oG.
Qed.

(* Temporary sanity check. *)
Lemma minSimpleOdd_prime : forall gT (G : {group gT}),
  odd #|G| -> simple G -> prime #|G|.
Proof.
move=> gT G oddG simpG.
have solG := minSimpleOdd_ind oddG.
have chsimG: charsimple G := minnormal_charsimple simpG.
have: abelem G := charsimple_solvable chsimG solG.
case/abelemP=> p p_pr; do 2![case/andP]=> abG _ pG.
case/simpleP: simpG => ntG simpG; have{pG ntG} [_ pG _] := pgroup_pdiv pG ntG.
case/Cauchy: pG => // x Gx oxp; move: p_pr; rewrite -{}oxp /order.
suffices: <[x]> <| G by case/simpG=> -> //; rewrite cards1.
by rewrite /normal andbC cents_norm ?(subset_trans abG) ?centS ?cycle_subG.
Qed.

End InitialReduction.

Notation TheMinSimpleOddGroup gT :=
    [set: FinGroup.sort (FinGroup.base (minSimpleOddGroupType_base gT))]
  (only parsing).

(* for finset.v *)
Lemma properT : forall (T : finType) (M : {set T}),
 (M \proper setT) = (M != setT).
Proof. by move=> T M; rewrite properEneq subsetT andbT. Qed.

Section MinSimpleOdd.

Variable gT : minSimpleOddGroupType.
Notation G := (TheMinSimpleOddGroup gT).

Lemma minSimple_odd : forall H : {group gT}, odd #|H|.
Proof. by move=> H; apply: (oddSg (subsetT H)); case: gT => ? []. Qed.

Lemma minSimple_simple : simple G.
Proof. by case: gT => ? []. Qed.

Lemma minSimple_nonSolvable : ~~ solvable G.
Proof. by case: gT => ? []. Qed.

Lemma proper_minSimple_sol : forall M : {group gT}, M \proper G -> solvable M.
Proof. by case: gT => ? []. Qed.

Lemma minSimple_nonAbelian : ~~ abelian G.
Proof. apply: contra minSimple_nonSolvable; exact: abelian_sol. Qed.

Lemma quotient_minSimple_odd : forall M H : {group gT}, odd #|M / H|.
Proof. by move=> M H; rewrite quotient_odd ?minSimple_odd. Qed.

Lemma proper_norm_minSimple : forall H : {group gT},
  H :!=: 1 -> H \proper G -> 'N(H) \proper G.
Proof.
move=> H ntH; rewrite !properT; apply: contra; move/eqP=> nHG; apply/eqP.
move/eqP: ntH; case/simpleP: minSimple_simple => _; case/(_ H) => //.
by rewrite /= -nHG normalG.
Qed.

Lemma trivg_cent_minSimple : 'C(G) = 1.
Proof.
apply/eqP; apply: contraR minSimple_nonAbelian => ntC.
rewrite /abelian subTset /= eqEproper subsetT /=; apply/negP=> prC.
have:= proper_norm_minSimple ntC prC.
by rewrite /proper subsetT norms_cent ?normG.
Qed.

Lemma proper_cent_minSimple : forall H : {group gT},
  H :!=: 1 -> 'C(H) \proper G.
Proof.
move=> H; case: (eqsVneq H G) => [-> | ].
  by rewrite trivg_cent_minSimple properT eq_sym.
rewrite -properT => prH ntH; apply: sub_proper_trans (cent_sub H) _.
exact: proper_norm_minSimple.
Qed.

Lemma quotient_minSimple_sol : forall M H : {group gT},
  H :!=: 1 -> solvable (M / H).
Proof.
move=> M H ntH; case: (eqsVneq H G) => [-> |].
  rewrite [_ / _](trivgP _) ?abelian_sol ?abelian1 //.
  by rewrite quotient_sub1 ?normsG ?subsetT.
rewrite -properT => prH; rewrite -quotientInorm morphim_sol //.
apply: solvableS (subsetIr _ _) (proper_minSimple_sol _).
by rewrite proper_norm_minSimple.
Qed.


Definition max_groups := [set M : {group gT} | maximal M G].
Definition max_supgroups (H : {set gT}) := [set M \in max_groups | H \subset M].
Definition uniq_max_subgroups := [set U : {group gT} | #|max_supgroups U| <= 1].
Definition minSimple_SCN_at n p := \bigcup_(P \in 'Syl_p(G)) 'SCN_n(P).

Lemma normal_max_group : forall M H : {group gT},
  M \in max_groups -> H <| M -> H :!=: 1 -> 'N(H) = M.
Proof.
move=> M H; rewrite inE; case/maxgroupP=> prM maxM; case/andP=> sHM nHM ntH.
apply: maxM nHM; rewrite proper_norm_minSimple //.
exact: sub_proper_trans prM.
Qed.

Lemma max_supgroupS : forall H K : {set gT},
  H \subset K -> max_supgroups K \subset max_supgroups H.
Proof.
move=> H K sHK; apply/subsetP=> M; rewrite !inE; case/andP=> ->.
exact: subset_trans.
Qed.

Lemma uniq_maxP : forall M1 M2 U : {group gT},
  U \in uniq_max_subgroups ->
  M1 \in max_supgroups U -> M2 \in max_supgroups U -> M1 = M1.
Proof.
move=> M1 M2 U uU M1_U M2_U; have:= uU.
by rewrite inE (cardD1 M1) (cardD1 M2) M1_U inE /= M2_U; case: eqP.
Qed.

Lemma uniq_maxS : forall U V : {group gT},
  U \subset V -> U \in uniq_max_subgroups -> V \in uniq_max_subgroups.
Proof.
move=> U V sUV; rewrite !inE; apply: leq_trans.
by rewrite subset_leq_card ?max_supgroupS.
Qed.

End MinSimpleOdd.

Notation "''M'" := (max_groups _) (at level 8, format "''M'") : group_scope.
Notation "''M' ( H )" := (max_supgroups H)
 (at level 8, format "''M' ( H )") : group_scope.
Notation "''U'" := (uniq_max_subgroups _) (at level 8) : group_scope.
Notation "''SCN_' n [ p ]" := (minSimple_SCN_at _ n p)
  (at level 8, n at level 2, format "''SCN_' n [ p ]") : group_scope.


Section Hypothesis7_1.

Variable gT : finGroupType.

Definition normed_pgroups (X A : {set gT}) pi :=
  [set Y : {group gT} | pi.-subgroup(X) Y && (A \subset 'N(Y))].

Definition max_normed_pgroups (A : {set gT}) pi :=
  [set Y | [max Y | pi.-group Y && (A \subset 'N(Y))]].

Inductive normed_constrained (A : {set gT}) :=
  NormedConstrained (pi := \pi(#|A|)) of A != 1 & A \proper setT
  & forall X Y : {group gT},
      A \subset X -> X \proper setT -> Y \in normed_pgroups X A pi^' -> 
    Y \subset 'O_pi^'(X).

End Hypothesis7_1.

Notation "|/|_ X ( A ; pi )" := (normed_pgroups X A pi)
  (at level 8, X at level 2, format "|/|_ X ( A ;  pi )") : group_scope.
Notation "|/|* ( A ; pi )" := (max_normed_pgroups A pi)
  (at level 8, format "|/|* ( A ;  pi )") : group_scope.

Section Seven.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H P Q R K M A : {group gT}.
Implicit Type p q : nat.

Section NormedConstrained.

Variables (q : nat) (A : {group gT}).
Let pi := \pi(#|A|).
Let K := 'O_pi^'('C(A)).

Lemma norm_acts_max_norm : forall P, [acts 'N(P), on |/|*(P; q) | 'JG].
Proof.
move=> P; apply/subsetP=> z Nz; rewrite !inE; apply/subsetP=> Q; rewrite !inE.
case/maxgroupP=> qQ maxQ; apply/maxgroupP; rewrite pgroupJ norm_conj_norm //.
split=> // Y; rewrite sub_conjg /= => qY; move/maxQ=> <-; rewrite ?conjsgKV //.
by rewrite pgroupJ norm_conj_norm ?groupV.
Qed.

Lemma trivg_max_norm : forall P, 1%G \in |/|*(P; q) -> |/|*(P; q) = [set 1%G].
Proof.
move=> P max1; apply/eqP; rewrite eqEsubset sub1set max1 andbT; apply/subsetP=> Q.
rewrite !inE -val_eqE /= in max1 *; case/maxgroupP: max1 => _ max1.
by move/maxgroupp; move/max1->; rewrite ?sub1G.
Qed.

Let nsKC : K <| 'C(A) := pcore_normal _ _.

Lemma cent_core_acts_max_norm : [acts K, on |/|*(A; q) | 'JG].
Proof.
apply: subset_trans (subset_trans (pcore_sub _ _) (cent_sub A)) _.
exact: norm_acts_max_norm.
Qed.
Let actsKmax := actsP cent_core_acts_max_norm.

Hypotheses (cstrA : normed_constrained A) (pi'q : q \notin pi).
Let hyp71 : forall H R,
  A \subset H -> H \proper G -> R \in |/|_H(A; pi^') -> R \subset 'O_pi^'(H).
Proof. by case cstrA. Qed.

Lemma normed_constrained_Hall : pi^'.-Hall('C(A)) K.
Proof.
have [_ ntA prA _] := cstrA; rewrite -[setT]/G in prA.
rewrite /pHall pcore_pgroup pcore_sub pnatNK /=.
rewrite -card_quotient ?bgFunc_norm //= -/K.
apply/pgroupP=> p p_pr; case/Cauchy=> // Kx; case/morphimP=> x Nx Cx ->{Kx}.
rewrite /order -quotient_cycle //= -/K => def_p; apply/idPn=> pi'p.
have [P sylP] := Sylow_exists p <[x]>; have [sPx pP _]:= and3P sylP.
suffices: P \subset K.
  have nKP: P \subset 'N(K) by rewrite (subset_trans sPx) ?cycle_subG.
  rewrite -quotient_sub1 //= -/K (sameP trivgP eqP) trivg_card1.
  rewrite (card_Hall (morphim_pHall _ nKP sylP)) def_p part_pnat ?pnat_id //.
  by case: eqnP p_pr => // ->.
suffices sP_pAC: P \subset 'O_pi^'(A <*> 'C(A)).
  rewrite (subset_trans sP_pAC) ?pcore_max ?pcore_pgroup //.
  rewrite /normal (char_norm_trans (pcore_char _ _)) ?normsG ?mulgen_subr //.
  rewrite andbT -quotient_sub1; last first.
    rewrite (subset_trans (pcore_sub _ _)) // mulgen_subG normG cents_norm //.
    by rewrite centsC.
  rewrite /= -(setIidPr (pcore_sub _ _)) quotientGI ?mulgen_subr //=.
  rewrite {1}cent_mulgenEr // quotient_mulg coprime_TIg // coprime_morph //.
  by rewrite coprime_pi' ?cardG_gt0 //= -/pi [pnat _ _]pcore_pgroup.
apply: hyp71; first exact: mulgen_subl.
  apply: sub_proper_trans (proper_norm_minSimple ntA prA).
  by rewrite mulgen_subG normG cent_sub.
have sPC: P \subset 'C(A) by rewrite (subset_trans sPx) ?cycle_subG.
rewrite inE /psubgroup cents_norm 1?centsC // andbT.
rewrite (subset_trans sPC) ?mulgen_subr //=.
by apply: sub_in_pnat pP => p' _; move/eqnP->.
Qed.
Let hallK := normed_constrained_Hall.

Lemma normed_constrained_meet_trans : forall Q1 Q2 H,
    A \subset H -> H \proper G -> Q1 \in |/|*(A; q) -> Q2 \in |/|*(A; q) ->
    Q1 :&: H != 1 -> Q2 :&: H != 1 ->
  exists2 k, k \in K & Q2 :=: Q1 :^ k.
Proof.
move=> Q1 Q2 H; move: {2}_.+1 (ltnSn (#|G| - #|Q1 :&: Q2|)) => m.
elim: m => // m IHm in H Q1 Q2 * => geQ12m sAH prHG maxQ1 maxQ2 ntHQ1 ntHQ2.
have:= maxQ1; rewrite inE; case/maxgroupP; case/andP=> qQ1 nQ1A maxQ1P.
have:= maxQ2; rewrite inE; case/maxgroupP; case/andP=> qQ2 nQ2A maxQ2P.
have prQ12: Q1 :&: Q2 \proper G.
  rewrite properT; apply: contra (minSimple_nonSolvable gT); move/eqP <-.
  by apply: pgroup_sol (pgroupS _ qQ1); rewrite subsetIl.
wlog defH: H prHG sAH ntHQ1 ntHQ2 / Q1 :&: Q2 != 1 -> H :=: 'N(Q1 :&: Q2).
  case: (eqVneq (Q1 :&: Q2) 1) => [-> | ntQ12] IH.
    by apply: (IH H) => //; case/eqP.
  apply: (IH 'N(Q1 :&: Q2)%G); rewrite ?normsI ?proper_norm_minSimple //;
    apply: contra ntQ12; rewrite -!subG1; apply: subset_trans;
    by rewrite subsetI normG (subsetIl, subsetIr).
pose L := 'O_pi^'(H); have sLH: L \subset H := pcore_sub _ _.
have [nLA coLA solL]: [/\ A \subset 'N(L), coprime #|L| #|A| & solvable L].
- rewrite (char_norm_trans (pcore_char _ _)) ?normsG //.
  rewrite coprime_sym coprime_pi' ?cardG_gt0 ?[pnat _ _]pcore_pgroup //.
  by rewrite (solvableS sLH) ?proper_minSimple_sol.
have Qsyl: forall Q, Q \in |/|*(A; q) -> Q :&: H != 1 ->
  exists R : {group _}, [/\ q.-Sylow(L) R, A \subset 'N(R) & Q :&: H \subset R].
- move=> Q; rewrite inE; case/maxgroupP; case/andP=> qQ nQA _ ntQH.
  have qQH: q.-group (Q :&: H) by rewrite (pgroupS _ qQ) ?subsetIl.
  have nQHA: A \subset 'N(Q :&: H) by rewrite normsI // normsG.
  apply: coprime_Hall_subset => //; apply: (hyp71) => //.
  rewrite inE nQHA /psubgroup subsetIr andbT.
  by apply: sub_in_pnat qQH => p _; move/eqnP->.
have [R1 [sylR1 nR1A sQR1]] := Qsyl _ maxQ1 ntHQ1.
have [R2 [sylR2 nR2A sQR2]] := Qsyl _ maxQ2 ntHQ2.
have [h Ch defR2] := coprime_Hall_trans nLA coLA solL sylR2 nR2A sylR1 nR1A.
have{Ch} [Hh Kh]: h \in H /\ h \in K.
  case/setIP: Ch => Lh Ch; rewrite (subsetP sLH) //.
  rewrite (mem_normal_Hall hallK (pcore_normal _ _)) //.
  by rewrite (mem_p_elt _ Lh) ?pcore_pgroup.
have [Q3 maxQ3 sR2Q3]: exists2 Q3, Q3 \in |/|*(A; q) & R2 \subset Q3.
  pose nAq Q := q.-group Q && (A \subset 'N(Q)).
  have: nAq R2 by rewrite /nAq (pHall_pgroup sylR2).
  by case/maxgroup_exists => Q3 maxQ3 sR2Q3; exists Q3; rewrite ?inE.
have maxQ1h: (Q1 :^ h)%G \in |/|*(A; q) by rewrite actsKmax.
case: (eqsVneq Q1 Q2) => [| neQ12]; first by exists 1; rewrite ?group1 ?conjsg1.
have ntHQ3: Q3 :&: H != 1.
  apply: contra ntHQ2; rewrite -!subG1; apply: subset_trans.
  by rewrite subsetI subsetIr (subset_trans sQR2).
have ntHQ1h: (Q1 :^ h) :&: H != 1.
  by move: ntHQ1; rewrite !trivg_card1 -(cardJg _ h) conjIg (conjGid Hh).
suff [prI1 prI2]: Q1 :&: Q2 \proper Q1 :&: R1 /\ Q1 :&: Q2 \proper Q2 :&: R2.
  have: #|G| - #|(Q1 :^ h) :&: Q3| < m.
    rewrite ltnS in geQ12m; apply: leq_trans geQ12m.
    rewrite ltn_sub2l ?(proper_card prQ12) // -(cardJg _ h) proper_card //.
    by rewrite (proper_sub_trans _ (setIS _ sR2Q3)) // defR2 -conjIg properJ.
  have: #|G| - #|Q3 :&: Q2| < m.
    rewrite ltnS in geQ12m; apply: leq_trans geQ12m.
    rewrite ltn_sub2l ?proper_card // (proper_sub_trans prI2) //.
    by rewrite setIC setISS.
  case/(IHm H) => // k2 Kk2 defQ2; case/(IHm H) => // k3 Kk3 defQ3.
  by exists (h * k3 * k2); rewrite ?groupM ?conjsgM // -defQ3.
case: (eqVneq (Q1 :&: Q2) 1) => [-> | ntQ12].
  rewrite !proper1G; split; [apply: contra ntHQ1 | apply: contra ntHQ2];
    by rewrite -!subG1; apply: subset_trans; rewrite subsetI subsetIl.
rewrite -(setIidPr (subset_trans (pHall_sub sylR1) sLH)) setIA.
rewrite -(setIidPr (subset_trans (pHall_sub sylR2) sLH)) setIA.
rewrite (setIidPl sQR1) (setIidPl sQR2) {}defH //.
rewrite !properE !(subsetI (Q1 :&: Q2)) subsetIl subsetIr !normG /=.
split; apply: contra neQ12.
  move/(nilpotent_sub_norm (pgroup_nil qQ1) (subsetIl _ _)); move/esym.
  by move/setIidPl=> sQ12; rewrite (maxQ1P Q2) ?qQ2.
move/(nilpotent_sub_norm (pgroup_nil qQ2) (subsetIr _ _)); move/esym.
by move/setIidPr=> sQ21; rewrite (maxQ2P Q1) ?qQ1.
Qed.

Theorem normed_constrained_rank3_trans :
  'm('Z(A)) >= 3 -> [transitive K, on |/|*(A; q) | 'JG].
Proof.
case/grank_geP=> B.
case/nElemP=> p; rewrite !inE -andbA; case/and3P=> sBZ abelB mB3.
have p_pr: prime p by move: mB3; rewrite lognE; case: and3P => [[]|//].
rewrite subsetI in sBZ; case/andP: sBZ => sBA cAB.
have:= abelB; do 2![case/andP]=> abB _ _.
have q'B: forall Q, q.-group Q -> coprime #|Q| #|B|.
  move=> Q qQ; apply: coprimegS sBA _; rewrite coprime_sym coprime_pi' //.
  by apply: sub_in_pnat qQ => q' _; move/eqnP->.
have [Q1 maxQ1]: exists Q1, Q1 \in |/|*(A; q).
  have: exists Q1 : {group gT}, q.-group Q1 && (A \subset 'N(Q1)).
    by exists 1%G; rewrite pgroup1 norms1.
  by case/ex_maxgroup=> Q1; exists Q1; rewrite inE.
apply/imsetP; exists Q1 => //; apply/setP=> Q2.
apply/idP/imsetP=> [maxQ2|[k Kk] ->]; last by rewrite actsKmax.
have:= maxQ1; rewrite inE; move/maxgroupp; case/andP=> qQ1 nQ1A.
have:= maxQ2; rewrite inE; move/maxgroupp; case/andP=> qQ2 nQ2A.
case: (eqVneq Q1 1%G) => [trQ1 | ntQ1].
  exists 1; rewrite ?group1 // act1; apply/eqP.
  by rewrite trivg_max_norm -trQ1 // inE in maxQ2.
case: (eqVneq Q2 1%G) => [trQ2 | ntQ2].
  by case/negP: ntQ1; rewrite trivg_max_norm -trQ2 // inE in maxQ1 *.
have [C]: exists C : {group gT}, [&& 'C_Q1(C) != 1, C <| B & cyclic (B / C)].
  apply/existsP; apply: contraR ntQ1; rewrite negb_exists; move/forallP=> trQ1.
  have nQ1B := subset_trans sBA nQ1A.
  rewrite (coprime_abelian_gen_cent _ nQ1B) ?q'B //.
  rewrite big1 //= => C; case/andP=> cycC nsCB; apply/eqP.
  by have:= trQ1 C; rewrite cycC nsCB !andbT negbK.
case/and3P=> ntCQ1 nsCB cycBC; have [sCB nCB]:= andP nsCB.
have{mB3} ncycC: ~~ cyclic C.
  apply/cyclicP=> [[x defC]]; have Bx: x \in B by rewrite -cycle_subG -defC.
  have maxB: forall y, y \in B -> logn p #[y] <= 1.
    move=> y By; case/p_abelemP: abelB => // _; move/(_ y By) => yp1.
    by rewrite -(pfactorK 1 p_pr) dvdn_leq_log ?prime_gt0 // order_dvdn yp1.
  case/cyclicP: cycBC => Cy defBC; have: Cy \in B / C by rewrite defBC cycle_id.
  case/morphimP=> y Ny By defCy; rewrite {Cy}defCy -quotient_cycle // in defBC.
  have:= leq_add (maxB x Bx) (maxB y By); rewrite leqNgt -(eqP mB3); case/negP.
  rewrite -(quotientGK nsCB) defBC quotientK ?cycle_subG // defC.
  rewrite -logn_mul // mul_cardG /= -defC -?norm_mulgenEr ?cycle_subG //.
  by rewrite logn_mul ?leq_addr ?cardG_gt0.
have [z]: exists z, (z \in C^#) && ('C_Q2[z] != 1).
  apply/existsP; apply: contraR ntQ2; rewrite negb_exists; move/forallP=> trQ2.
  have nQ2C := subset_trans sCB (subset_trans sBA nQ2A).
  rewrite (coprime_abelian_gen_cent1 _ ncycC nQ2C) ?(abelianS sCB) //.
    by rewrite big1 //= => z Cz; apply/eqP; have:= trQ2 z; rewrite Cz negbK.
  by rewrite (coprimegS sCB) ?q'B.
rewrite 2!inE -andbA; case/and3P=> ntz Cz ntzQ2.
have prCz: 'C[z] \proper G.
  by rewrite -cent_set1 -cent_gen proper_cent_minSimple ?cycle_eq1.
have sACz: A \subset 'C[z].
  by rewrite -cent_set1 centsC sub1set (subsetP cAB) ?(subsetP sCB).
have [|//|k Kk defQ2]:= normed_constrained_meet_trans sACz prCz maxQ1 maxQ2.
  apply: contra ntCQ1; rewrite -!subG1; apply: subset_trans.
  by rewrite setIS //= -cent_set1 centS // sub1set.
exists k => //; exact: val_inj.
Qed.

Lemma atrans_dvd : forall (sT : finType) (to : {action gT &-> sT}),
  forall H (S : {set sT}), [transitive H, on S | to] -> #|S| %| #|H|.
Proof. by move=> sT to H S; case/imsetP=> x _ ->; exact: dvdn_orbit. Qed.

Lemma normed_constrained_rank2_trans :
  q %| #|'C(A)| -> 'm('Z(A)) >= 2 -> [transitive K, on |/|*(A; q) | 'JG].
Proof.
move=> qC; case/grank_geP=> B EnZ_B.
have{EnZ_B} [sBZ ncycB]: B \subset 'Z(A) /\ ~~ cyclic B.
  case/nElemP: EnZ_B => p; rewrite !inE -andbA; case/and3P=> sBZ abelB mB2.
  split=> //; apply: contraL (leqnn 2); rewrite -leqNgt -(eqP mB2).
  case/cyclicP=> x defB; case p_pr: (prime p); last by rewrite lognE p_pr.
  case/p_abelemP: abelB => // _; move/(_ x) => xp1.
  rewrite -(pfactorK 1 p_pr) dvdn_leq_log ?prime_gt0 // defB order_dvdn xp1 //.
  by rewrite defB cycle_id.
rewrite subsetI in sBZ; case/andP: sBZ => sBA cAB.
have abB: abelian B by exact: subset_trans cAB (centS _).
have [R0 sylR0] := Sylow_exists q 'C(A); have [cAR0 qR0 _] := and3P sylR0.
have [R maxR sR0R]: exists2 R, R \in |/|*(A; q) & R0 \subset R.
  suff [R]: {R | [max R | q.-group R && (A \subset 'N(R))] & R0 \subset R}.
    by exists R; rewrite 1?inE.
  by apply: maxgroup_exists; rewrite qR0 cents_norm // centsC.
have:= maxR; rewrite inE; case/maxgroupP; case/andP=> qR nRA maxRP.
apply/imsetP; exists R => //; apply/setP=> Q.
apply/idP/imsetP=> [maxQ|[k Kk] ->]; last by rewrite actsKmax.
have:= maxQ; rewrite inE; case/maxgroupP; case/andP=> qQ nQA maxQP.
case: (eqVneq 'C_R(A) 1) => [tiRC| ntRC].
  have: R0 :==: 1 by rewrite -subG1 -tiRC subsetI sR0R.
  rewrite trivg_card1 -dvdn1 (card_Hall sylR0) p_part.
  case q_pr: (prime q) => [] => [|_].
    by rewrite pfactor_dvdn // logn1 lognE q_pr qC cardG_gt0.
  exists 1; rewrite ?group1 //=; apply: val_inj; rewrite /= conjsg1.
  apply: etrans (_ : 1 = _); apply/eqP; rewrite ?(eq_sym 1) trivg_card1.
    by rewrite -(part_pnat qQ) p_part lognE q_pr.
  by rewrite -(part_pnat qR) p_part lognE q_pr.
have ntR: R :!=: 1.
  by apply: contra ntRC; rewrite -!subG1 => R1; rewrite subIset ?R1.
have ntQ: Q :!=: 1.
  by apply: contra ntR; move/eqP=> defQ; rewrite maxQP ?defQ ?sub1G ?qR.
have [z]: exists z, (z \in B^#) && ('C_Q[z] != 1).
  apply/existsP; apply: contraR ntQ; rewrite negb_exists; move/forallP=> trQ.
  have nQB := subset_trans sBA nQA.
  rewrite (coprime_abelian_gen_cent1 _ ncycB nQB) //; last first.
    rewrite (coprimegS sBA) // coprime_sym coprime_pi' //. 
    by apply: sub_in_pnat qQ => q' _; move/eqnP->.
  by rewrite big1 //= => z Cz; apply/eqP; have:= trQ z; rewrite Cz negbK.
rewrite 2!inE -andbA; case/and3P=> ntz Bz ntzQ.
have prCz: 'C[z] \proper G.
  by rewrite -cent_set1 -cent_gen proper_cent_minSimple ?cycle_eq1.
have sACz: A \subset 'C[z].
  by rewrite -cent_set1 centsC sub1set (subsetP cAB).
have [|//|k Kk defQ2]:= normed_constrained_meet_trans sACz prCz maxR maxQ.
  apply: contra ntRC; rewrite -!subG1; apply: subset_trans.
  by rewrite setIS //= -cent_set1 centS // sub1set (subsetP sBA).
exists k => //; exact: val_inj.
Qed.

Theorem normed_trans_superset : forall P : {group gT},
    A <|<| P -> pi.-group P -> [transitive K, on |/|*(A; q) | 'JG] ->
 [/\ 'C_K(P) = 'O_pi^'('C(P)),
     [transitive 'O_pi^'('C(P)), on |/|*(P; q) | 'JG],
     |/|*(P; q) \subset |/|*(A; q)
   & {in |/|*(P; q), forall Q,
         P :&: 'N(P)^`(1) \subset 'N(Q)^`(1)
      /\ 'N(P) = 'C_K(P) * 'N_('N(P))(Q)}].
Proof.
move=> P snAP piP trnK.
have defK: forall B : {group gT}, A \subset B -> 'C_K(B) = 'O_pi^'('C(B)).
  move=> B sAB; apply/eqP; rewrite eqEsubset {1}setIC pcoreS ?centS //.
  rewrite subsetI pcore_sub (subset_normal_Hall _ hallK) ?pcore_normal //.
  by rewrite /psubgroup pcore_pgroup (subset_trans (pcore_sub _ _)) ?centS.
suffices [trnKP smnPA]: [transitive 'O_pi^'('C(P)), on |/|*(P; q) | 'JG]
                        /\ |/|*(P; q) \subset |/|*(A; q).
- set KP := 'O_pi^'('C(P)) in trnKP *; rewrite (defK _ (subnormal_sub snAP)).
  have nsKPN: KP <| 'N(P) := char_normal_trans (pcore_char _ _) (cent_normal _).
  split=> // Q maxQ; have defNP: KP * 'N_('N(P))(Q) = 'N(P).
    rewrite -(astab1JG Q) -normC; last by rewrite subIset 1?normal_norm.
    apply/(subgroup_transitiveP maxQ); rewrite ?normal_sub //=.
    by rewrite (atrans_supgroup _ trnKP) ?norm_acts_max_norm ?normal_sub.
  split=> //; move/prod_norm_coprime_subs_derI: defNP => -> //.
  - by rewrite subIset // orbC commgSS ?subsetIr.
  - by rewrite subsetI normG; rewrite inE in maxQ; case/andP: (maxgroupp maxQ).
  by rewrite /= (pnat_coprime piP (pcore_pgroup _ _)).
elim: {P}_.+1 {-2}P (ltnSn #|P|) piP snAP => // m IHm P lePm piP snAP.
wlog{snAP} [B maxnB snAB]: / {B : {group gT} | maxnormal B P P & A <|<| B}.
  case/subnormalEr: snAP => [<- // | [D [snAD nDP prDP]]]; apply.
  have [B maxnB sDB]: {B : {group gT} | maxnormal B P P & D \subset B}.
    by apply: maxgroup_exists; rewrite prDP normal_norm.
  exists B => //; apply: subnormal_trans snAD (normal_subnormal _).
  by apply: normalS sDB _ nDP; case/andP: (maxgroupp maxnB); case/andP.
have [prBP nBP] := andP (maxgroupp maxnB); have sBP := proper_sub prBP.
have{lePm}: #|B| < m by exact: leq_trans (proper_card prBP) _.
case/IHm=> {IHm}// [|trnB smnBA]; first by rewrite (pgroupS sBP).
have{maxnB} abelPB: abelem (P / B).
  apply: charsimple_solvable (maxnormal_charsimple _ maxnB) _ => //.
  apply: quotient_sol (proper_minSimple_sol _).
  apply: sub_proper_trans nBP (proper_norm_minSimple _ _); last first.
    exact: proper_sub_trans prBP (subsetT _).
  rewrite -proper1G (proper_sub_trans _ (subnormal_sub snAB)) // proper1G.
  by case cstrA.
have{abelPB} [p p_pr pPB]: exists2 p, prime p & p.-group (P / B).
  by case/abelemP: abelPB => p p_pr; case/andP; exists p.
have{prBP} pi_p: p \in pi.
  case/pgroup_pdiv: pPB => [|_ pPB _].
    by rewrite -subG1 quotient_sub1 // proper_subn.
  by apply: pgroupP p_pr pPB; exact: quotient_pgroup.
pose S := |/|*(B; q); pose nq P Q := q.-group Q && (P \subset 'N(Q)).
have pi'S: pi^'.-nat #|S| := pnat_dvd (atrans_dvd trnB) (pcore_pgroup _ _).
have{pi'S} p'S: #|S| %% p != 0.
  by rewrite -prime_coprime // (pnat_coprime _ pi'S) ?pnatE.
have{p'S} [Q S_Q nQP]: exists2 Q, Q \in S & P \subset 'N(Q).
  have sTSB: setT \subset G / B by rewrite -quotientT quotientS ?subsetT.
  have modBE: {in P & S, forall x Q, ('JG %% B) Q (coset B x) = 'JG Q x}%act.
    move=> x Q Px; rewrite inE; move/maxgroupp; case/andP=> _ nQB.
    by rewrite /= modactE ?(subsetP nBP) ?afixJG ?setTI ?inE.
  have actsPB: [acts P / B, on S | 'JG %% B \ sTSB].
    apply/subsetP=> Bx; case/morphimP => x Nx Px ->{Bx}.
    rewrite !inE; apply/subsetP=> Q S_Q; rewrite inE /= modBE //.
    by rewrite (actsP (norm_acts_max_norm B)).
  move: p'S; rewrite (pgroup_fix_mod pPB actsPB); set nQ := #|_|.
  case: (posnP nQ) => [->|]; first by rewrite mod0n.
  rewrite lt0n; case/existsP=> Q; case/setIP=> Q_S fixQ; exists Q => //.
  apply/normsP=> x Px; apply: congr_group; have Nx := subsetP nBP x Px.
  by have:= afixP fixQ (coset B x); rewrite /= modBE ?mem_morphim //= => ->.
have{nQP}: nq P Q.
  by rewrite /nq nQP andbT; rewrite inE in S_Q; case/andP: (maxgroupp S_Q).
case/maxgroup_exists=> Q0 maxQ0 sQQ0; have [_ nQ0P] := andP (maxgroupp maxQ0).
have{maxQ0} mnP_Q0: Q0 \in |/|*(P; q) by rewrite inE.
case tr_mnP: (1%G \in |/|*(P; q)) => [|{Q S_Q sQQ0}].
  rewrite trivg_max_norm // ?inE in mnP_Q0 *; split.
    apply/imsetP; exists 1%G; rewrite ?set11 //.
    apply/eqP; rewrite eqEsubset sub1set orbit_refl.
    apply/subsetP=> R; case/imsetP=> z _ ->{R}.
    by rewrite inE -val_eqE /= conjs1g.
  rewrite (eqP mnP_Q0) subG1 in sQQ0; rewrite ((Q =P 1%G) sQQ0) in S_Q.
  by rewrite -(trivg_max_norm S_Q).
have sAB := subnormal_sub snAB; have sAP := subset_trans sAB sBP.
have smnP_S: |/|*(P; q) \subset S.
  apply/subsetP=> Q1 mnP_Q1; have ntQ1: Q1 :!=: 1.
    by apply: contraL mnP_Q1; move/eqP; move/val_inj->; rewrite tr_mnP.
  have:= mnP_Q1; rewrite inE; case/maxgroupP; case/andP=> qQ1 nQ1P mP_Q1.
  have prNQ1: 'N(Q1) \proper G.
    rewrite proper_norm_minSimple // properT.
    apply: contra (minSimple_nonSolvable gT); move/eqP <-; exact: pgroup_sol qQ1.
  have nQ1A: A \subset 'N(Q1) by rewrite (subset_trans sAP).
  have: nq B Q1 by rewrite /nq qQ1 (subset_trans sBP).
  case/maxgroup_exists=> Q2 nmB_Q2 sQ12; have S_Q2: Q2 \in S by rewrite inE.
  have [qQ2 nQ2B]:= andP (maxgroupp nmB_Q2).
  have qNQ2: q.-group 'N_Q2(Q1) by rewrite (pgroupS _ qQ2) ?subsetIl.
  have sNQ2_KN: 'N_Q2(Q1) \subset 'O_pi^'('N(Q1)).
    rewrite hyp71 // inE normsI ?norms_norm ?(subset_trans sAB nQ2B) //=.
    rewrite /psubgroup subsetIr andbT.
    by apply: sub_in_pnat qNQ2 => q' _; move/eqnP->.
  have [Q3 [sylQ3 nQ3P sQ13]]: exists Q3 : {group gT},
    [/\ q.-Sylow('O_pi^'('N(Q1))) Q3, P\subset 'N(Q3) & Q1 \subset Q3].
  - apply: coprime_Hall_subset=> //.
    + by rewrite (char_norm_trans (pcore_char _ _)) ?norms_norm.
    + by rewrite coprime_sym (pnat_coprime piP (pcore_pgroup _ _)).
    + by rewrite (solvableS (pcore_sub _ _)) ?proper_minSimple_sol.
    rewrite pcore_max /normal ?normG ?subxx //.
    by apply: sub_in_pnat qQ1 => q' _; move/eqnP->.
  have: 'N_Q2(Q1) \subset Q1.
    rewrite subEproper eq_sym eqEcard subsetI sQ12 normG /=.
    rewrite -{2}(mP_Q1 Q3) ?(pHall_pgroup sylQ3) // dvdn_leq ?cardG_gt0 //.
    by rewrite -(part_pnat qNQ2) (card_Hall sylQ3) partn_dvd ?cardSg.
  by move/(nilpotent_sub_norm (pgroup_nil qQ2) sQ12); move/val_inj <-.
split; last exact: subset_trans smnP_S smnBA.
apply/imsetP; exists Q0 => //; apply/setP=> Q2.
apply/idP/imsetP=> [maxQ2 | [k Pk ->]]; last first.
  rewrite (actsP (subset_trans _ (norm_acts_max_norm P)) k Pk) //.
  exact: subset_trans (pcore_sub _ _) (cent_sub _).
have [S_Q0 S_Q2]: Q0 \in S /\ Q2 \in S by rewrite !(subsetP smnP_S).
pose KB := 'O_pi^'('C(B)); pose KP := KB <*> P.
have pi'KB: pi^'.-group KB by exact: pcore_pgroup.
have nKB_P: P \subset 'N(KB).
  by rewrite (char_norm_trans (pcore_char _ _)) ?norms_cent.
have [k KBk defQ2]:= atransP2 trnB S_Q0 S_Q2.
have:= maxQ2; rewrite inE; move/maxgroupp; case/andP=> qQ2 nQ2P.
have hallP: pi.-Hall('N_KP(Q2)) P.
  have sPN: P \subset 'N_KP(Q2) by rewrite subsetI mulgen_subr.
  rewrite pHallE eqn_leq -{1}(part_pnat piP) dvdn_leq ?partn_dvd ?cardSg //.
  have ->: #|P| = #|KP|`_pi.
    rewrite /KP mulgenC norm_mulgenEl // coprime_cardMg ?(pnat_coprime piP) //.
    by rewrite partn_mul // part_pnat // part_p'nat // muln1.
  by rewrite sPN dvdn_leq ?partn_dvd ?cardSg ?cardG_gt0 ?subsetIl.
have hallPk: pi.-Hall('N_KP(Q2)) (P :^ k).
  rewrite pHallE -(card_Hall hallP) cardJg eqxx andbT subsetI /=.
  by rewrite defQ2 normJ conjSg conj_subG ?mulgen_subr // mem_gen // inE KBk.
have [gz]: exists2 gz, gz \in 'N_KP(Q2) & (P = P :^ k :^ gz)%G.
  apply: HallConj (solvableS (subsetIr _ _) _) hallP hallPk.
  apply: proper_minSimple_sol (proper_norm_minSimple _ _).
    by apply: contraL maxQ2; move/(Q2 =P _)->; rewrite tr_mnP.
  rewrite properT; apply: contra (minSimple_nonSolvable gT); move/eqP <-.
  exact: pgroup_sol qQ2.
rewrite [KP]norm_mulgenEr //= setIC -group_modr //= setIC -/KB.
case/imset2P=> g z; case/setIP=> KBg nQ2g Pz ->{gz} defP.
exists (k * g); last first.
  by apply: val_inj; rewrite /= conjsgM -(normP nQ2g) defQ2.
rewrite -defK // (subsetP (subsetIl _ 'C(B))) //= setIAC defK // -/KB.
rewrite -coprime_norm_cent 1?coprime_sym ?(pnat_coprime piP) //= -/KB.
rewrite inE groupM //; apply/normP.
by rewrite -{2}(conjsgK z P) (conjGid Pz) {2}defP /= !conjsgM conjsgK.
Qed.

End NormedConstrained.

Lemma plenght_1_normed_constrained : forall p A,
    A :!=: 1 -> A :=: [set x \in 'C(A) | x ^+ p == 1] ->
    (forall M, M \proper G -> p.-length_1 M) ->
  normed_constrained A.
Proof. Admitted. (* Requires B & G 6.7 *)

Lemma SCN_normed_constrained : forall p P A,
  p.-Sylow(G) P -> A \in 'SCN_2(P) -> normed_constrained A.
Proof.
move=> p P A sylP; rewrite 2!inE -andbA; case/and3P=> nsAP.
have [sAP nAP]:= andP nsAP; move/eqP=> defCA lt1mA.
have pP := pHall_pgroup sylP; have pA := pgroupS sAP pP.
have abA: abelian A by rewrite /abelian -{1}defCA subsetIr.
have prP: P \proper G.
  rewrite properT; apply: contra (minSimple_nonSolvable gT); move/eqP <-.
  exact: pgroup_sol pP.
have ntA: A :!=: 1 by rewrite -grank_gt0 ltnW.
pose pi : nat_pred := \pi(#|A|).
have [p_pr pdvA [r oApr]] := pgroup_pdiv pA ntA.
have{r oApr} def_pi: pi =i (p : nat_pred).
  by move=> p'; rewrite !inE oApr primes_exp // primes_prime ?inE.
have def_pi' := eq_negn def_pi; have defK := eq_pcore _ def_pi'.
pose Z := 'Ohm_1('Z(P)); have sZ_ZP: Z \subset 'Z(P) by exact: Ohm_sub.
have sZP_A: 'Z(P) \subset A by rewrite -defCA setIS ?centS.
have sZA := subset_trans sZ_ZP sZP_A.
have nsA1: 'Ohm_1(A) <| P by exact: (char_normal_trans (Ohm_char _ _)).
have [B [E2_B nsBP sBZ]]: exists B, [/\ B \in 'E_p^2(A), B <| P
                                      & B \subset Z \/ #|Z| = p /\ Z \subset B].
- have pZP: p.-group 'Z(P) by exact: pgroupS (center_sub _) pP.
  have pZ: p.-group Z by exact: pgroupS sZ_ZP pZP.
  have abelZ: p.-abelem Z.
    by rewrite /p_abelem Ohm_abelian ?(pgroup_p pZP) ?abelian_center.
  have nsZP: Z <| P; last have [sZP nZP] := andP nsZP.
    by rewrite (char_normal_trans (Ohm_char _ _)) ?center_normal.
  case: (eqVneq Z 1).
    rewrite -(setIidPr sZ_ZP); move/TI_Ohm1; rewrite setIid.
    by move/(trivg_center_pgroup pP)=> P1; rewrite -subG1 -P1 sAP in ntA.
  case/(pgroup_pdiv pZ)=> _ _ [[|k] /=]; rewrite -/Z => oZ; last first.
    have: 2 <= 'm_p(Z) by rewrite p_rank_abelem // oZ pfactorK.
    case/p_rank_geP=> B; rewrite /= -/Z => Ep2Z_B; exists B.
    rewrite (subsetP (pnElemS _ _ sZA)) //.
    move: Ep2Z_B; rewrite !inE -andbA; case/andP=> sBZ _.
    split=> //; last by left.
    have sBZP := subset_trans sBZ sZ_ZP.
    rewrite /normal ?(subset_trans sBZP) ?center_sub ?cents_norm //.
    by rewrite centsC (subset_trans sBZP) ?subsetIr.
  have: ('Ohm_1(A) / Z) :&: 'Z(P / Z) != 1.
    rewrite nil_meet_Z // ?quotient_nil ?(pgroup_nil pP) ?quotient_normal //.
    rewrite -subG1 quotient_sub1 ?(subset_trans (normal_sub nsA1) nZP) //= -/Z.
    apply: contraL lt1mA => sA1Z; rewrite -leqNgt -grank_Ohm1.
    by rewrite (leq_trans (grankS sA1Z)) // (grank_abelem abelZ) oZ pfactorK.
  case/trivgPn=> Zx; case/setIP; case/morphimP=> x Nx A1x defZx Z_Zx ntZx.
  pose B := Z <*> <[x]>; rewrite -cycle_subG in Nx; exists [group of B].
  split; last by right; rewrite mulgen_subl.
    have sBA1: B \subset 'Ohm_1(A) by rewrite mulgen_subG cycle_subG OhmS.
    rewrite 2!inE (subset_trans _ (Ohm_sub 1 A)) //=.
    have abelB: p.-abelem B by rewrite (p_abelemS sBA1) ?Ohm1_p_abelian.
    have sZB: Z \subset B by rewrite mulgen_subl.
    rewrite abelB -(LaGrange sZB) oZ -card_quotient ?mulgen_subG ?normG //= -/Z.
    rewrite norm_mulgenEr // quotient_mulgr quotient_cycle -?cycle_subG //.
    have abelBZ: p.-abelem (B / Z) := morphim_p_abelem _ abelB.
    have B_Zx: Zx \in B / Z.
      by rewrite defZx mem_morphim -?cycle_subG ?mulgen_subr.
    have [_ oBx] := abelem_order_p abelBZ B_Zx ntZx.
    by rewrite -defZx -orderE oBx -expnSr pfactorK.
  rewrite /= -(quotientGK nsZP) /B norm_mulgenEr //= -quotientK //= -/Z.
  rewrite morphpre_normal ?quotientS // quotient_cycle -?cycle_subG // -defZx.
  case/setIP: Z_Zx => P_Zx cP_Zx.
  by rewrite /normal cents_norm ?andbT 1?centsC cycle_subG.
split; rewrite ?(sub_proper_trans sAP) // => X Y sAX prX.
rewrite inE defK -andbA (eq_pgroup _ def_pi'); case/and3P=> sYX p'Y nYA.
move: E2_B; rewrite 2!inE -andbA; case/and3P=> sBA abelB dimB2.
have [] := andP abelB; case/andP=> abB _ pB.
have ntB: B :!=: 1 by case: (eqsVneq B 1) dimB2 => // ->; rewrite cards1 logn1.
have cBA: forall b, b \in B -> A \subset 'C[b].
  move=> b Bb; rewrite -cent_set1 centsC sub1set.
  by rewrite (subsetP abA) ?(subsetP sBA).
have solCB: forall b : gT, b != 1 -> solvable 'C[b].
  move=> b; rewrite -cycle_eq1; move/proper_cent_minSimple.
  by rewrite cent_gen cent_set1; exact: proper_minSimple_sol.
wlog{sAX prX} [b B'b defX]: X Y p'Y nYA sYX / exists2 b, b \in B^# & 'C[b] = X.
  move=> IH; have nYB := subset_trans sBA nYA.
  rewrite (coprime_abelian_gen_cent1 abB _ nYB); last first.
  - by rewrite coprime_sym (pnat_coprime pB).
  - apply: contraL dimB2; case/cyclicP=> x defB.
    have: x \in B by rewrite defB cycle_id.
    case/(abelem_order_p abelB)=> [|_]; first by rewrite -cycle_eq1 -defB.
    by rewrite /order -defB => ->; rewrite logn_prime ?eqxx.
  rewrite bigprodGE gen_subG; apply/bigcupsP=> b B'b.
  have [ntb Bb]:= setD1P B'b; have sYbY: 'C_Y[b] \subset Y := subsetIl _ _.
  have{IH} sYbKb: 'C_Y[b] \subset 'O_p^'('C[b]).
    rewrite IH ?(pgroupS sYbY) ?subsetIr //; last by exists b.
    by rewrite normsI // ?normsG ?cBA.
  have{sYbKb} sYbKXb: 'C_Y[b] \subset 'O_p^'('C_X(<[b]>)).
    apply: subset_trans (pcoreS _ (subsetIr _ _)).
    by rewrite /= cent_gen cent_set1 subsetI setSI.
  rewrite (subset_trans sYbKXb) // p'core_cent_pgroup ?proper_minSimple_sol //.
  rewrite /psubgroup ?(pgroupS _ pB) cycle_subG //.
  by rewrite (subsetP sAX) ?(subsetP sBA).
wlog Zb: b X Y defX B'b p'Y nYA sYX / b \in Z.
  move=> IH; case Zb: (b \in Z); first exact: IH Zb.
  case/setD1P: B'b => ntb Bb; have solX := solCB b ntb; rewrite defX in solX.
  case: sBZ => [sBZ | [oZ sZB]]; first by rewrite (subsetP sBZ) in Zb.
  have defB: Z * <[b]> = B.
    apply/eqP; rewrite eqEcard mulG_subG sZB cycle_subG Bb.
    have [_ obp] := abelem_order_p abelB Bb ntb.
    rewrite -(part_pnat pB) p_part //= (eqP dimB2) TI_cardMg -/#[_] ?oZ ?obp //.
    rewrite -obp in p_pr; case: (prime_subgroupVti [group of Z] p_pr) => //.
    by rewrite cycle_subG Zb.
  pose P1 := P :&: X; have sP1P: P1 \subset P := subsetIl _ _.
  have pP1 := pgroupS sP1P pP.
  have [P2 sylP2 sP12] := Sylow_superset (subsetIr _ _) pP1.
  have defP1: P1 = 'C_P(B).
    rewrite -defB centM /= -/Z setIA /cycle cent_gen cent_set1 defX.
    by rewrite [P :&: _](setIidPl _) // centsC (subset_trans sZ_ZP) ?subsetIr.
  have dimPP1: logn p #|P : P1| <= 1.
    have nBP := normal_norm nsBP; pose rP := abelem_repr abelB ntB nBP.
    have ->: P1 = 'ker (reprGLm rP) by rewrite ker_reprGLm rker_abelem.
    rewrite -card_quotient ?ker_norm // (isog_card (first_isog _)).
    apply: leq_trans (dvdn_leq_log _ _ (cardSg (subsetT _))) _ => //.
    by rewrite logn_card_GL_p // (dim_abelemE abelB) // (eqP dimB2).
  have{dimPP1} nsP12: P1 <| P2.
    have pP2 := pHall_pgroup sylP2.
    have: logn p #|P2 : P1| <= 1.
      apply: leq_trans dimPP1; rewrite dvdn_leq_log //.
      rewrite -(dvdn_pmul2l (cardG_gt0 [group of P1])) !LaGrange ?subsetIl //.
      by rewrite -(part_pnat pP2) (card_Hall sylP) partn_dvd ?cardSg ?subsetT.
    rewrite -(pfactorK 1 p_pr) -pfactor_dvdn ?prime_gt0 // -p_part.
    rewrite part_pnat ?(pnat_dvd (dvdn_indexg _ _)) //=.
    case: (primeP p_pr) => _ dv_p; move/dv_p=> {dv_p}.
    case/pred2P=> oP21; first by rewrite -(index1g sP12 oP21) normal_refl.
    by rewrite (p_maximal_normal pP2) ?p_index_maximal ?oP21.
  have nsZP1_2: 'Z(P1) <| P2 by rewrite (char_normal_trans (center_char _)).
  have sZKp: Z \subset 'O_{p^', p}(X).
    suff: 'Z(P1) \subset 'O_{p^', p}(X).
      apply: subset_trans; rewrite subsetI {1}defP1 (subset_trans sZB).
        by rewrite (subset_trans sZ_ZP) ?subIset // orbC centS.
      by rewrite subsetI normal_sub.
    apply: odd_p_abelian_constrained sylP2 (abelian_center _) nsZP1_2 => //.
    exact: minSimple_odd.
  have coYZ: coprime #|Y| #|Z|.
    by rewrite oZ coprime_sym (pnat_coprime _ p'Y) ?pnatE ?inE.
  have nYZ := subset_trans sZA nYA.
  have <-: [~: Y, Z] * 'C_Y(Z) = Y.
    exact: coprime_cent_prod (solvableS sYX solX).
  set K := 'O_p^'(X); have [nKY nKZ]: Y \subset 'N(K) /\ Z \subset 'N(K).
    rewrite !(char_norm_trans (pcore_char _ _)) ?(subset_trans sZA) ?normsG //.
    by rewrite -defX cBA.
  rewrite mul_subG //.
    have coYZK: coprime #|Y / K| #|'O_p(X / K)|.
      by rewrite coprime_sym coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
    rewrite -quotient_sub1 ?comm_subG // -(coprime_TIg coYZK) subsetI.
    rewrite /= -quotient_pseries2 !quotientS ?commg_subl //.
    by rewrite (subset_trans (commgSS sYX sZKp)) ?commg_subr //= bgFunc_norm.
  have: 'O_p^'('C_X(Z)) \subset K.
    rewrite p'core_cent_pgroup // /psubgroup /pgroup oZ pnat_id //.
    by rewrite -defX (subset_trans sZA) ?cBA.
  apply: subset_trans; apply: subset_trans (pcoreS _ (subsetIr _ _)).
  have: cyclic Z by rewrite prime_cyclic ?oZ.
  case/cyclicP=> z defZ; have Zz: z \in Z by rewrite defZ cycle_id.
  rewrite subsetI setSI //= (IH z) ?subsetIr ?(pgroupS (subsetIl _ _)) //.
  - by rewrite defZ /= cent_gen cent_set1.
  - rewrite !inE -cycle_eq1 -defZ trivg_card_le1 oZ -ltnNge prime_gt1 //=.
    by rewrite (subsetP sZB).
  by rewrite normsI // norms_cent // cents_norm // centsC (subset_trans sZA).
set K := 'O_p^'(X); have nsKX: K <| X by exact: pcore_normal.
case/setD1P: B'b => ntb Bb.
have [sAX solX]: A \subset X /\ solvable X by rewrite -defX cBA ?solCB.
have sPX: P \subset X.
  by rewrite -defX -cent_set1 centsC sub1set; case/setIP: (subsetP sZ_ZP b Zb).
have [nKA nKY nKP]: [/\ A \subset 'N(K), Y \subset 'N(K) & P \subset 'N(K)].
  by rewrite !(subset_trans _ (normal_norm nsKX)).
have sylPX: p.-Sylow(X) P by exact: pHall_subl (subsetT _) sylP.
have sAKb: A \subset 'O_{p^', p}(X).
  exact: (odd_p_abelian_constrained (minSimple_odd _)) abA nsAP.
have coYZK: coprime #|Y / K| #|'O_p(X / K)|.
  by rewrite coprime_sym coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
have cYAq: A / K \subset 'C_('O_p(X / K))(Y / K).
  rewrite subsetI -quotient_pseries2 quotientS //= (sameP commG1P trivgP).
  rewrite /= -quotientR // -(coprime_TIg coYZK) subsetI /= -quotient_pseries2.
  rewrite !quotientS ?commg_subr // (subset_trans (commgSS sAKb sYX)) //.
  by rewrite commg_subl /= bgFunc_norm.
have cYKq: Y / K \subset 'C('O_p(X / K)).
  apply: coprime_nil_faithful_cent_stab => /=.
  - by rewrite (char_norm_trans (pcore_char _ _)) ?normsG ?quotientS.
  - by rewrite coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
  - exact: pgroup_nil (pcore_pgroup _ _).
  apply: subset_trans (cYAq); rewrite -defCA -['C_P(A) / K](morphim_restrm nKP).
  rewrite injm_cent ?ker_restrm ?ker_coset ?morphim_restrm -?quotientE //.
    rewrite setIid (setIidPr sAP) setISS ?centS //.
    by rewrite pcore_sub_Hall ?morphim_pHall.
  by rewrite coprime_TIg ?(pnat_coprime _ (pcore_pgroup _ _)).
rewrite -quotient_sub1 //= -/K -(coprime_TIg coYZK) subsetI subxx /=.
rewrite -Fitting_eq_pcore ?trivg_pcore_quotient // in cYKq *.
apply: subset_trans (cent_sub_Fitting (quotient_sol _ solX)).
by rewrite subsetI quotientS.
Qed.

Theorem Thompson_transitivity : forall p q A,
    A \in 'SCN_3[p] -> q \in p^' ->
  [transitive 'O_p^'('C(A)), on |/|*(A; q) | 'JG].
Proof.
move=> p q A; case/bigcupP=> P; rewrite 2!inE => sylP; case/andP=> SCN_A mA3.
have [defZ def_pi']: 'Z(A) = A /\ \pi(#|A|)^' =i p^'.
  rewrite inE -andbA in SCN_A; case/and3P: SCN_A => sAP _; move/eqP=> defCA.
  case: (eqsVneq A 1) mA3 => [-> | ntA _].
    rewrite /rank big1_seq // => p1 _; rewrite /p_rank big1 // => E.
    by rewrite inE; case/andP; move/trivgP->; rewrite cards1 logn1.
  have [p_pr _ [k ->]] := pgroup_pdiv (pgroupS sAP (pHall_pgroup sylP)) ntA.
  split=> [|p1]; last by rewrite !inE primes_exp // primes_prime ?inE.
  by apply/eqP; rewrite eqEsubset subsetIl subsetI subxx -{1}defCA subsetIr.
rewrite -(eq_pcore _ def_pi') -def_pi' => pi'q.
apply: normed_constrained_rank3_trans; rewrite ?defZ //.
by apply: SCN_normed_constrained sylP _; rewrite inE SCN_A ltnW.
Qed.

End Seven.

