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

(* chooses a representative from a set of sets *)
Definition repr_set (T : finType) (C : {set set_of_finType T}) := 
  odflt set0 (pick (mem C)).

Section Transfer.

Variables (gT aT : finGroupType) (G H : {group gT}). 
Variable alpha : {morphism H >-> aT}.

Hypotheses (sHG : H \subset G) (abelA : abelian (alpha @* H)).

Notation fmalpha := (fmod abelA \o alpha).

(* there are generic facts about morphisms from a group to an abelian
   group construed as a module. They are needed to avoid duplication of
   side conditions *)

Lemma fmod_morphM: {in H &, {morph fmalpha : x y / (x * y)%g >-> x + y}}.
Proof. 
by move=> x y Hx Hy /=; rewrite morphM // fmodM ?mem_morphim.
Qed.
  
Lemma fmod_morphV: {in H, {morph fmalpha : x / x^-1%g >-> - x}}.
Proof.
by move=> x Hx /=; rewrite morphV // fmodV ?mem_morphim.
Qed.

Lemma fmod_morphX: forall n, {in H, {morph fmalpha : x / x ^+ n >-> x *+ n}}.
Proof.
by move=> n x Hx /=; rewrite morphX // fmodX ?mem_morphim.
Qed.

Notation V X g := 
  (\sum_(C \in rcosets H G) fmalpha (X C * g * (X (C :* g))^-1)%g).

Definition transfer g := V repr g.

(* Aschbacher 37.2 *)
Lemma transfer_morphism: 
  {in G &, {morph transfer : x y / (x * y)%g >-> x + y}}.
Proof.
move=> s t sinG tinG; rewrite /transfer.
have reind := (reindex_acts 'Rs (A := G) (S := rcosets H G) (a := s)).
rewrite {-3}[bigop]lock reind ?actsRs_rcosets // -lock -big_split /=.
apply: eq_bigr => C; move/rcosetsP => [x xinG ->].
rewrite !rcosetE. 
rewrite -fmod_morphM. 
- apply: congr1; apply: congr1.
  by rewrite !mulgA mulgKV rcosetM.
- rewrite -mem_rcoset -rcosetM rcoset_repr mem_rcoset invMg mulgA mulgK.
  by rewrite -mem_rcoset mem_repr_rcoset.
rewrite -mem_rcoset -!rcosetM rcoset_repr mem_rcoset invMg mulgA mulgK.
by rewrite -mem_rcoset mem_repr_rcoset.
Qed.

(* annoying: because we are going from a group to a module, we need
   to show morphism properties by hand *)

Lemma transfer1: transfer 1 = 0.
Proof.
suffices a: transfer 1 + transfer 1 = transfer 1.
  by move/eqP: a; rewrite eq_sym -subr_eq addrN eq_sym; move/eqP. 
by rewrite -transfer_morphism // mulg1.
Qed.

Lemma transferV: forall g, g \in G -> transfer (g^-1) = - transfer g.
Proof.
move=> g Gg; apply/eqP; rewrite -subr_eq0 opprK -transfer_morphism ?groupV //.
by rewrite mulVg transfer1.
Qed.

Notation cosetReps X := {in rcosets H G, forall C, X C \in C}.

(* Aschbacher 37.1 *)
Lemma transfer_indep : forall (X : {set gT} -> gT) g, g \in G -> 
  cosetReps X -> transfer g = V X g.
Proof.
move=> X g ginG repsX; rewrite /transfer.
apply: (@trans_eq _ _ (\sum_(C \in rcosets H G) ((fmalpha (repr C * (X C)^-1)) + 
  fmalpha (X C * g * (X (C :* g))^-1) -  
  fmalpha (repr (C :* g) * (X (C :* g))^-1))%g)); last first.
  rewrite !big_split sumr_opp /=.  (* should have sumr_split *)
  have reind := (reindex_acts 'Rs (A := G) (S := rcosets H G) (a := g)).
  rewrite reind ?actsRs_rcosets //=; apply/eqP.
  rewrite addrC -subr_eq0 -addrA addrK addrC subr_eq0; apply/eqP.
  by apply: eq_bigr=> C _; rewrite rcosetE.
apply: eq_bigr => C; move/rcosetsP=> [x xinG ->]; rewrite -!rcosetM.
have in1: repr (H :* (x * g)) * (X (H :* (x * g)))^-1 \in H.
  rewrite -mem_rcoset (rcoset_transl (repsX _ _)) ?mem_repr_rcoset //.
  by rewrite -rcosetE mem_imset ?groupM.
have in2: repr (H :* x) * (X (H :* x))^-1 \in H.
  rewrite -mem_rcoset (rcoset_transl (repsX _ _)) -?rcosetE ?mem_imset //.
  by rewrite !rcosetE mem_repr_rcoset.
have in3: X (H :* x) * g * (X (H :* (x * g)))^-1 \in H.
  rewrite -mem_rcoset (rcoset_transl (repsX _ _)); last first.
    by rewrite -rcosetE mem_imset ?groupM. 
  rewrite mem_rcoset invMg mulgA mulgK -mem_rcoset repsX //.
  by rewrite -rcosetE mem_imset.
rewrite -fmod_morphV // -!fmod_morphM // ?groupV // 1?groupM //.
by apply: congr1; rewrite invMg !mulgA invgK !mulgKV.
Qed.

(* The next few lemmas have to do with picking representatives of orbits
   of cosets and representatives of those representatives. Are there ways
   to eliminate them and streamline the proofs below? *)

(* cycle g C is the cycle of coset C under g *)
Notation ccycle g := (pcycle (actperm 'Rs g)).
Notation ccycles g := (ccycle g @: (rcosets H G)).

(* the cycle of coset C under g, as a sequence starting with C *)
Definition ccycle_seq (g : gT) C := 
  (traject (actperm 'Rs g) C #|ccycle g C|).

Lemma repr_set_ccycle : forall (g : gT) C, repr_set (ccycle g C) \in ccycle g C.
Proof.
move=> g C; rewrite /repr_set. 
have cycC : C \in ccycle g C by apply: pcycle_id.
case: pickP; first done. 
by move/(_ C); rewrite [mem _ _]cycC.
Qed.

Lemma ccycle_rcoset : forall g C D, g \in G -> C \in rcosets H G -> 
  D \in ccycle g C -> D \in rcosets H G.
Proof.
move=> g C D Gg; case/imsetP => h Gh ->{C}.
case/imsetP=> p; case/cycleP=> i -> ->.
rewrite apermE actpermX ?in_setT // actpermE ['Rs%act _ _]rcosetE.
by rewrite rcosetE -rcosetM -rcosetE mem_imset // groupM // groupX.
Qed.

Lemma repr_repr_set_ccycle : forall (g : gT) C, C \in rcosets H G ->
  repr (repr_set (ccycle g C)) \in repr_set (ccycle g C).
Proof.
move=> g C rcosC.
case/imsetP: (repr_set_ccycle g C) => p; case/cycleP=> i -> ->.
rewrite apermE actpermX ?in_setT // actpermE ['Rs%act _ _]rcosetE.
case/imsetP: rcosC => h _ ->{C}.
by rewrite rcosetE -rcosetM mem_repr_rcoset.
Qed.

Lemma rep_repr_set_ccycle2 : forall g cyc, g \in G -> cyc \in ccycles g ->
  repr (repr_set cyc) \in G.
Proof.
move=> g cyc Gg; case/imsetP=> C rcosC ->.
have cycrep_rcos := (ccycle_rcoset Gg rcosC (repr_set_ccycle g C)).
case/imsetP: cycrep_rcos=> h Gh ->; rewrite rcosetE.
case/rcosetP: (mem_repr_rcoset H h)=> x Hx ->. 
by rewrite groupM // (subsetP sHG).
Qed.

(* a particular choice of coset representatives *)
Definition transX (g : gT) C := (repr (repr_set (ccycle g C))) * 
  (g ^+ (index C (ccycle_seq g (repr_set (ccycle g C))))).

Lemma coset_reps_transX : forall g, cosetReps (transX g).
Proof.
move=> g C cosC. rewrite /transX.
have cyceq : ccycle g C == ccycle g (repr_set (ccycle g C)).
  by rewrite eq_sym eq_pcycle_mem repr_set_ccycle //.
have cycsub : ccycle g C \subset ccycle_seq g (repr_set (ccycle g C)).
  by rewrite {1}(eqP cyceq) (eq_subxx (pcycle_traject _ _)).
have cycC : C \in ccycle_seq g (repr_set (ccycle g C)).
  exact: ((subsetP cycsub _) (pcycle_id _ _)).
case/(nthP (repr_set (ccycle g C))): cycC=> i ilt nthi.
rewrite -{2}nthi index_uniq ?uniq_traject_pcycle //.
move: nthi; rewrite nth_traject; last first.
  by move: ilt; rewrite size_traject.
rewrite -permX actpermX ?in_setT // actpermE => eqC.
by rewrite -{2}eqC /= rcosetE mem_rcoset mulgK repr_repr_set_ccycle.
Qed.

Lemma transfer_eq1: forall g, g \in G -> forall cyc, cyc \in ccycles g ->
  g ^+ #|cyc| ^ (repr (repr_set cyc))^-1 \in H.
Proof.
move=> g Gg cyc; case/imsetP=> C rcosC ->.
set C' := (repr_set _).
have cyceq : ccycle g C == ccycle g C'.
  by rewrite eq_sym eq_pcycle_mem repr_set_ccycle //.
rewrite (eqP cyceq) conjgE invgK mulgA -mem_rcoset.
have rcosC' : C' \in rcosets H G.
  exact: (ccycle_rcoset Gg rcosC (repr_set_ccycle g C)).
have C'eq : C' = H :* repr C'.
  by case/imsetP: rcosC'=> h Gh ->; rewrite rcosetE rcoset_repr.
rewrite -C'eq.
have C'geq : C':* g ^+ #|ccycle g C'| = C'.
  rewrite -{3}(iter_pcycle (actperm 'Rs g) C') -permX.
  by rewrite actpermX ?in_setT // actpermE ['Rs%act _ _]rcosetE.
by rewrite -{3}C'geq mem_rcoset mulgK C'eq mem_repr_rcoset.
Qed.

Lemma transfer_eq2: forall g, g \in G -> (\sum_(cyc \in ccycles g) #|cyc|)%N = 
  #| G : H |.
Proof.
move=> g Gg. 
rewrite pcycleE acts_sum_card_orbit; first done.
(* is there a better way to do this? we have actsRs_rcosets -- which 
   could be useful -- but these is no lemma for passing to <[g]> *)
apply/subsetP=> h; case/cycleP=> i ->{h}; rewrite /astabs !inE andTb.
apply/subsetP=> C; case/rcosetsP=> h Gh ->{C}. 
rewrite inE /= apermE actpermX ?inE // actpermE ['Rs%act _ _]rcosetE.
rewrite -rcosetM -rcosetE mem_imset // groupM // groupX //.
Qed.

Lemma transfer_eq : forall g, g \in G -> transfer g = 
  \sum_(cyc \in ccycles g) fmalpha (g ^+ #|cyc| ^ (repr (repr_set cyc))^-1).
Proof.
move=>g Gg.
rewrite [transfer _](transfer_indep Gg (coset_reps_transX g)).
rewrite [V _ _](partition_big_imset (fun C => ccycle g C)) /=.
apply: eq_bigr=> cyc; case/imsetP=> C rcosC ->.
have cyceq : ccycle g C == ccycle g (repr_set (ccycle g C)).
  by rewrite eq_sym eq_pcycle_mem repr_set_ccycle //.
have cyceq2 : [pred i \in rcosets H G | ccycle g i == ccycle g C] =i 
  ccycle_seq g (repr_set (ccycle g C)).
  move=> D; rewrite /ccycle_seq -pcycle_traject !inE eq_pcycle_mem -(eqP cyceq).
  by case cycD: (D \in ccycle _ _); 
    rewrite ?andb_false_r ?(@ccycle_rcoset g C D).
rewrite (eq_bigl _ _ cyceq2) /ccycle_seq.
set C' := (repr_set _).
have rcosC' : C' \in rcosets H G.
  exact: (ccycle_rcoset Gg rcosC (repr_set_ccycle g C)).
apply: (@trans_eq _ _ (fmod abelA (alpha 
  (transX g C' * (g ^+ #|ccycle g C'|) * 
  (transX g (C' :* (g ^+ #|ccycle g C'|)))^-1)%g))); last first.
  apply congr1; apply congr1.
  have eq1 : C':* g ^+ #|ccycle g C'| = C'.
    rewrite -{3}(iter_pcycle (actperm 'Rs g) C') -permX.
    by rewrite actpermX ?in_setT // actpermE ['Rs%act _ _]rcosetE.
  have pos_card_cyc: 0 < #|ccycle g C|.
    rewrite card_gt0; apply/set0Pn; exists (repr_set (ccycle g C)). 
    exact: repr_set_ccycle.
  have eq2 : transX g C' = repr C'.
    rewrite /transX /C' /ccycle_seq -!(eqP cyceq). 
    by rewrite -(prednK pos_card_cyc) /= eqxx expg0 mulg1.
  by rewrite eq1 !eq2 conjgE invgK mulgA (eqP cyceq).
(* the recursive definition of traject forces an unnatural induction *)
move: (uniq_traject_pcycle (actperm 'Rs g) C'); move: (rcosC'); 
  move: #|_|=> n; move: (C').
elim: n => [|n ih] D rcosD.
  by rewrite big_pred0_eq expg0 mulg1 rcoset1 mulgV morph1 fmod1. 
rewrite /=; case/andP => disjD uniq'.
rewrite (eq_bigl [predU (pred1 D) & 
  (traject (actperm 'Rs g) (actperm 'Rs g D) n)]); last first.
  by move=> x; rewrite !inE.
rewrite bigU /=; last by rewrite disjoint1.
rewrite big_pred1_eq ih // !actpermE; last first.
  by rewrite (acts_act (actsRs_rcosets _ _)).
  rewrite !['Rs%act _ _]rcosetE -!rcosetM -!expgS.
case/rcosetsP: rcosD=> h Gh ->; rewrite -!rcosetM.
have in1: transX g (H :* h) \in H :* h. 
  by rewrite coset_reps_transX // -rcosetE ?mem_imset.
have in2: transX g (H :* (h * g)) \in H :* (h * g).
  by rewrite coset_reps_transX // -rcosetE mem_imset ?groupM //.
have in3: transX g (H :* (h * g ^+ n.+1)) \in H :* (h * g ^+ n.+1).
  by rewrite coset_reps_transX // -rcosetE mem_imset ?groupM ?groupX //.
rewrite -fmod_morphM.
- by rewrite 2!mulgA mulgKV expgS !mulgA.
- rewrite -mem_rcoset (rcoset_transl in2) mem_rcoset invMg mulgA. 
  by rewrite mulgK -mem_rcoset.
rewrite -mem_rcoset (rcoset_transl in3) expgS mem_rcoset mulgA invMg.
by rewrite mulgA mulgK -mem_rcoset.
Qed.

End Transfer.

Section Focal_Subgroup.

Variables (gT : finGroupType) (G S : {group gT}).

Hypothesis (sylS : Sylow G S).

Theorem Focal_Subgroup : S :&: [~: G, G] = 
  << [set [~ x, u] | x <- S, u <- G, x^u \in S] >>.
Proof.
set K := << [set _ | x <- _, u <- _, _] >>; set G' := [~: G, G].
case/SylowP: sylS => p primep; case/andP=> SsubG _.
apply/setP; apply/subset_eqP; apply/andP; split; last first.
  rewrite gen_subG; apply/subsetP=> g.
  case/imset2P=> x u Sx; rewrite inE; case/andP=> Gu Sxu ->{g}.
  by rewrite in_setI groupM ?groupV // mem_commg // ?(subsetP SsubG).
apply/subsetP=> g; case/setIP=> Sg G'g.
have Gg := subsetP SsubG g Sg.
have nS: S \subset 'N(K).
  apply: (subset_trans _ (norm_gen _)).
  apply/subsetP=> y Sy; rewrite inE; apply/subsetP=> z; case/imsetP=> w.
  case/imset2P=> x u Sx; rewrite inE; case/andP=> Gu Sxu ->{w} ->{z}.
  by apply/imset2P; exists (x^y) (u^y);  (* a no-no *)
    rewrite ?inE -1?conjJg ?(Sxu, groupJ) // ?(subsetP SsubG) // conjRg.
set alpha:= restrm_morphism nS (coset_morphism K).
have alphim: (alpha @* S) = (S / K).
  by rewrite morphim_restrm quotientE setIid.
have abelSK : abelian (alpha @* S).
  rewrite alphim sub_der1_abelian //. 
  rewrite gen_subG; apply: (subset_trans _ (subset_gen _)).
  apply/subsetP=>y; case/imset2P=> x u Sx Su ->.
  by rewrite mem_imset2 // inE groupJ // (subsetP SsubG).
(* annoying: transfer maps to a module rather than a group, so we 
   can't talk about the kernel. *)
set ker_trans := [set g \in G | transfer G abelSK g == 0].
have ker_transG : group_set ker_trans.
  apply/group_setP; split; first by rewrite !inE group1 transfer1 eq_refl.
  move=> h k; rewrite !inE; case/andP=> Gh th0; case/andP=> Gk tk0. 
  by rewrite transfer_morphism // groupM // (eqP th0) (eqP tk0) addr0 eq_refl.
have G'ker : G' \subset group (ker_transG).
  rewrite gen_subG; apply/subsetP=> h; case/imset2P=> h1 h2 Gh1 Gh2 ->{h}.
  rewrite !inE groupR // !transfer_morphism ?groupV ?groupJ ?groupM //.
  by rewrite !transferV // !addrA (addrC (- _)) addrNK addNr eq_refl.
have transg0: transfer G abelSK g = 0.
  by move: (subsetP G'ker g G'g); rewrite inE Gg // andTb; move/eqP.
have gGSeq0: fmod abelSK (alpha g) *+ #|G : S| = 0. 
  rewrite -transg0 (transfer_eq abelSK Gg) -(transfer_eq2 S Gg).
  (* it would be helful if this had a name, to go with sumr_muln --
     maybe sumrn_muln *)
  rewrite (big_morph _ (mulrn_addr (fmod abelSK (alpha g))) 
    (mulr0n _)).
  apply: eq_bigr=> cyc cyccyc; rewrite -fmod_morphX // /comp /=.
  apply: congr1; apply/rcoset_kercosetP. 
  - by apply (subsetP nS); rewrite groupX.
  - by apply (subsetP nS); apply: (transfer_eq1 Gg).
  rewrite rcoset_sym mem_rcoset -groupV invMg -conjVg.
  apply: (subsetP (subset_gen _)). 
  apply/imset2P; exists (g ^- #|cyc|) (repr (repr_set cyc))^-1.
  - by rewrite groupV groupX.
  - rewrite inE groupV conjVg groupV (transfer_eq1 Gg) // andbT.
    exact: (rep_repr_set_ccycle2 SsubG Gg).
  by rewrite commgEl.
move: (congr_fmod gGSeq0).
rewrite fmval0 -fmod_morphX /comp //= fmodK; last first.
  by rewrite mem_imset // setIid groupX //.
rewrite /restrm morphX ?(subsetP nS) //.
move/((congr1 (expgn^~ (expgn_inv (S / K) #|G : S|))) _). 
rewrite expgnK ?mem_imset //; last first. 
  by rewrite 1!inE (subsetP nS).
  have hallGS: Hall G S by case/andP: sylS.
  have coprime: coprime #|S| #|G : S| by case/andP: hallGS.
  apply: (coprime_dvdl _ coprime).
  exact: dvdn_quotient.
rewrite exp1gn.
apply: coset_idr.
by rewrite (subsetP nS).
Qed.

End Focal_Subgroup.

