Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime groups.
Require Import finalg morphisms automorphism normal perm action zmodp gprod.
Require Import commutators cyclic center pgroups sylow nilpotent maximal hall.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Import GroupScope.

Import GRing.Theory FinRing.Theory FiniteModule.

Section ActPerm.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variable to : action D rT.

Lemma orbit_morphim_actperm : forall A : {set aT},
  A \subset D -> orbit 'P (actperm to @* A) =1 orbit to A.
Proof.
move=> A AsubD x. 
rewrite -[orbit 'P _ _]imset_comp (setIidPr AsubD).
by apply: eq_imset => a //=; rewrite actpermK.
Qed.

End ActPerm. 

Section PcycleActPerm.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Lemma pcycle_actperm : forall a,
  a \in D -> pcycle (actperm to a) =1 orbit to <[a]>.
Proof.
move=> a Da x.
by rewrite pcycleE -(orbit_morphim_actperm to) ?cycle_subG // morphim_cycle.
Qed.

End PcycleActPerm.

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
rewrite -zmodMgE -morphM -?mem_rcoset; first by rewrite !mulgA mulgKV rcosetM.
  by rewrite rcoset_repr rcosetM mem_rcoset mulgK mem_repr_rcoset.
by rewrite rcoset_repr (rcosetM _ _ t) mem_rcoset mulgK mem_repr_rcoset.
Qed.

Canonical Structure transfer_morphism := Morphism transferM.

Definition coset_transversal X := 
  {in rcosets H G, forall Hx : {set gT}, X Hx \in Hx}.

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
by rewrite addrC -!zmodMgE -!morphM ?groupM ?groupV // -!mulgA !mulKg.
Qed.

Section FactorTransfer.

Variable g : gT.
Hypothesis Gg : g \in G.

Let Gcycg : <[g]> \subset G. Proof. by rewrite cycle_subG. Qed.
Let H_g_rcosets x := rcosets (H :* x) <[g]>.
Let n_ x := #|H_g_rcosets x|.

Lemma mulg_exp_card_rcosets : forall x, x * (g ^+ n_ x) \in H :* x.
Proof.
move=> x; rewrite /n_ /H_g_rcosets -orbitRs -pcycle_actperm ?inE //.
rewrite -{2}(iter_pcycle (actperm 'Rs g) (H :* x)) -permX -morphX ?inE //.
by rewrite actpermE //= rcosetE -rcosetM rcoset_refl. 
Qed.

Definition rcosets_pcycle_transversal (X : {set gT}) :=
  [/\ {in X &, injective H_g_rcosets}, X \subset G & G \subset H * X * <[ g ]>].

CoInductive rcosets_pcycle_transversal_witness : Prop :=
   RcosetPcycleTransversalWitness X (n_ := n_) of rcosets_pcycle_transversal X.

Lemma rcosets_pcycle_transversal_exists : rcosets_pcycle_transversal_witness.
Proof.
pose r1 x := repr (H_g_rcosets x); pose r2 x := repr (r1 x).
have mem_r1: forall x, x \in G -> r1 x \in H_g_rcosets x.
  by move=> x Gx; apply: (mem_repr (H :* x)); apply: orbit_refl.
have id_r2: forall x, x \in G -> H_g_rcosets (r2 x) = H_g_rcosets x.
  move=> x Gx; apply: orbit_transl; rewrite /r2.
  case/rcosetsP: (mem_r1 x Gx) => gi Ggi ->.
  by rewrite -rcosetM rcoset_repr rcosetM -rcosetE mem_orbit. 
exists (r2 @: G); split=> [w z ||].
- case/imsetP=> x Gx ->{w}; case/imsetP=> y Gy ->{z}.
  by rewrite !id_r2 /r2 /r1 // => ->.
- apply/subsetP=> u; case/imsetP=> x Gx ->{u}.
  rewrite /r2; case/rcosetsP: (mem_r1 x Gx) => y; case/cycleP=> i ->{y} ->.
  rewrite -rcosetM; apply: subsetP (mem_repr_rcoset H _).
  by rewrite mul_subG // sub1set groupM ?groupX.
apply/subsetP=> x Gx; case/rcosetsP: (mem_r1 x Gx) => y gy def_r1x.
rewrite -[x](mulgK y) mem_mulg ?groupV // -sub1set -mulGS.
by rewrite -rcoset_repr mulgS // sub1set rcosetM -def_r1x -/(r2 x) mem_imset.
Qed.

Variable X : {set gT}.
Hypothesis trX : rcosets_pcycle_transversal X.

Lemma rcosets_pcycle_transversal_im :
  H_g_rcosets @: X = orbit 'Rs <[g]> @: rcosets H G.
Proof.
have [_ sXG sGHXg]:= trX.
apply/setP=> Hxg; apply/imsetP/imsetP=> [[x Xx ->{Hxg}]|[Hx]] /=.
  by exists (H :* x); rewrite // -rcosetE mem_imset ?(subsetP sXG).
case/rcosetsP=> hxgi; move/(subsetP sGHXg); case/mulsgP=> hx gi.
case/mulsgP=> h x Hh Xx -> g_gi -> -> -> {hx hxgi Hxg Hx}; exists x => //.
by apply: orbit_transl; rewrite !rcosetM rcoset_id // -rcosetE mem_orbit.
Qed.
Local Notation imHg_eq := rcosets_pcycle_transversal_im.

Lemma sum_card_rcosets_pcycles : (\sum_(x \in X) n_ x)%N = #|G : H|.
Proof.
have [injHg _ _]:= trX.
transitivity (\sum_(Hxg \in orbit 'Rs <[g]> @: rcosets H G) #|Hxg|)%N. 
  by rewrite -imHg_eq big_imset.
exact: (acts_sum_card_orbit (subset_trans Gcycg (actsRs_rcosets _ _))).
Qed.

Lemma transfer_pcycle_def :
  transfer g = \sum_(x \in X) fmalpha ((g ^+ n_ x) ^ x^-1).
Proof.
have [injHg sXG sGHXg] := trX.
pose repset := \bigcup_(x \in X) [set x * g ^+ (i : 'I__) | i <- 'I_(n_ x)].
pose transX Hy := repr (Hy :&: repset).
pose pcyc x := pcycle (actperm 'Rs g) (H :* x).
pose traj x := traject (actperm 'Rs g) (H :* x) #|pcyc x|.
have Hgr_eq : forall x, H_g_rcosets x = pcyc x.
  by move=> x; rewrite /H_g_rcosets -orbitRs -pcycle_actperm ?inE.
have pcyc_eq : forall x, pcyc x =i traj x by move=> x; apply: pcycle_traject.
have uniq_traj : forall x, uniq (traj x)
  by move=> x; apply: uniq_traject_pcycle.
have n_eq: forall x, n_ x = #|pcyc x| by move=> x; rewrite /n_ Hgr_eq.
have size_traj : forall x, size (traj x) = n_ x 
  by move=> x; rewrite n_eq size_traject.
have nth_traj : forall x j, 
  j < n_ x -> nth (H :* x) (traj x) j = H :* (x * g ^+ j). 
  move=> x j j_less; rewrite nth_traject -?n_eq //.
  by rewrite  -permX -morphX ?inE // actpermE //= rcosetE rcosetM.
have transX_mem : forall y, y \in G -> transX (H :* y) \in H :* y :&: repset.
  move=> y Gy; case/mulsgP: (subsetP sGHXg _ Gy)=> t g0.
  case/mulsgP=> h x Hh Xx ->{t} cycGg0 ->; rewrite -mulgA rcosetM rcoset_id //.
  pose j := index (H :* (x * g0)) (traj x).
  have j_less : j < n_ x.
    by rewrite -size_traj index_mem rcosetM -rcosetE -pcyc_eq -Hgr_eq mem_imset.
  apply: (subsetP _ _ (mem_repr (x * g ^+ j) _)); first by [].
  apply/setIP; split.
    rewrite rcoset_sym -nth_traj // nth_index ?rcoset_refl //.
    by rewrite -pcyc_eq -Hgr_eq rcosetM -rcosetE mem_imset.
  by apply/bigcupP; exists x => //; apply/imsetP; exists (Ordinal j_less).
have coset_transversal_transX : coset_transversal transX.
  move=> Hy HG_Hy /=; have [y Gy ->] := rcosetsP HG_Hy.
  exact: (subsetP (subsetIl _ _) _ (transX_mem _ _)).
have transXE : forall x i, 
    x \in X -> i < n_ x -> transX (H :* x :* g ^+ i)%g = x * g ^+ i.
  move=> x i Xx i_less; rewrite -rcosetM.
  have Gxgi : x * g ^+ i \in G by rewrite groupM ?(subsetP sXG x) // ?groupX. 
  case/setIP: (transX_mem _ Gxgi) => Hxgi_transX {Gxgi}.
  case/bigcupP=> x' Xx'; case/imsetP=> j Ij transX_eq; rewrite transX_eq.
  have xx' : x = x'.
    apply: injHg => //; apply: orbit_transl; apply/orbitP. 
    exists (g ^+j * g ^- i) => /=.
      by rewrite ?groupM ?groupV ?groupX //= ?cycle_id //.
    rewrite rcosetE -rcosetM mulgA rcosetM -transX_eq.
    by rewrite (rcoset_transl Hxgi_transX) -rcosetM mulgK.
  congr mulg => //; congr expgn.
  have j_less : j < n_ x by rewrite xx'.
  apply/eqP; rewrite -(@nth_uniq _ (H :* x) (traj x)) ?size_traj //.
  apply/eqP; rewrite !nth_traj // -?size_traj //.
  by apply: rcoset_transl; rewrite {1}xx' -transX_eq.
rewrite (transfer_indep coset_transversal_transX Gg) /V.
rewrite (partition_big_imset (orbit 'Rs <[g]>)) /=.
rewrite -imHg_eq big_imset //=; apply eq_bigr=> x Xx.
rewrite (eq_bigl (mem (H_g_rcosets x))) //=; last first.
  move=> Hx; rewrite /H_g_rcosets orbit_eq_mem //=.
  apply/andP/idP; [case=> // | split=> //].
  apply: subsetP H0; apply/subsetP=> Hz; case/orbitP=> g0 cycgg0 <-.
  rewrite //= rcosetE -rcosetM -rcosetE mem_imset //.
  by rewrite groupM ?(subsetP sXG x) ?(subsetP Gcycg g0).
rewrite Hgr_eq (eq_bigl _ _ (pcyc_eq x)) -big_uniq // /traj /n_ Hgr_eq /=.
case def_n: {-}(#|_|) => [|n].
  by rewrite (cardD1 (H :* x)) pcycle_id in def_n.
rewrite conjgE invgK -{1}[H :* x]rcoset1 -{1}(expg0 g).
rewrite def_n; elim: {1 3}n 0%N (addn0 n) => [|m IHm] i def_i /=.
  rewrite big_cons big_nil addr0 {i}[i]def_i transXE // ?n_eq ?def_n //.
  rewrite  -(mulgA _ _ g) -rcosetM -expgSr -[(H :* x) :* _]rcosetE. 
  rewrite -actpermE morphX ?inE // permX // -def_n iter_pcycle mulgA.
  by rewrite -[H :* x]rcoset1 (transXE _ 0%N) ?mulg1 // n_eq def_n.
rewrite big_cons transXE //; last by rewrite n_eq def_n -def_i ltnS leq_addl. 
rewrite permE /= rcosetE -rcosetM -(mulgA _ _ g) -expgSr.
rewrite addSnnS in def_i; rewrite transXE //; last first.
  by rewrite n_eq def_n -def_i ltnS leq_addl.
by rewrite mulgV [fmalpha 1]morph1 add0r IHm.
Qed.

End FactorTransfer.

End Transfer.
