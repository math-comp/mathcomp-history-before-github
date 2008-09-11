Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms normal commutators.
Require Import cyclic center pgroups sylow dirprod schurzass hall. 
Require Import coprime_act nilpotent.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section coprime_comm.
Variable T : finGroupType.


Lemma quotientSK : forall G H K : {group T}, G \subset 'N(K) ->
  (G / K \subset H / K) = (G \subset K * H).
Proof. by move=> *; rewrite morphimSK ?ker_coset. Qed.

(* same as the following but with weaker assumptions 
Lemma comm_center_prod: forall (A G: group T),
  A \subset 'N(G) -> coprime #|[~: G, A]| #|A| -> solvable [~: G, A] ->
  G = [~: G, A] * 'C_G(A) :> set _.
Proof.
move=> A G AsubNG coprime solv.
apply/eqP; rewrite eqset_sub; apply/andP; split.
- apply: sub_gmul; rewrite /=; first by apply:normGR.
  - by apply: (subset_trans _ (normGR G A)); rewrite /centraliser; apply: subsetIl.
  - rewrite coprime_quotient_cent //=.
    - by rewrite subsetI; apply/andP; split; last by apply: center_commgr.
    - apply/andP; rewrite //=; split; last by apply:normGR.
      by rewrite commsgC subcomm_normal //.
    - by rewrite commsgC; apply: normGR.
- rewrite -{3}mulGid; apply:imset2S; last by apply: subsetIl.
  by rewrite commsgC subcomm_normal //.
Qed.
*)

Lemma comm_center_prod : forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  G :=: [~: G, A] * 'C_G(A).
Proof.
move=> A G AsubNG coprime solv.
apply/eqP; rewrite eqset_sub andbC -{3}mulGid imset2S ?subsetIl //; last first.
  by rewrite commsgC subcomm_normal.
rewrite -quotientSK ?normGR // coprime_quotient_cent_weak //=; last first.
- by rewrite commsgC normGR.
- by rewrite [_ <| G]andbC normGR commsgC subcomm_normal.
by rewrite subsetI andbC center_commgr /=.
Qed.

Lemma commGAA:   forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  [~: G, A] = [~: G, A, A].
Proof.
move=> A G AsubNG coGA solG.
apply/eqP; rewrite eqset_sub; apply/andP; split; last first.
  by rewrite commsgC subcomm_normal /= commsgC normGR.
rewrite {1}(comm_center_prod AsubNG coGA solG) distr_sgcomm //=.
- by rewrite triv_comm_centr mulg1 subset_refl.
- by rewrite subIset // normGR.
by rewrite subIset // orbC cent_subset.
Qed.

Lemma comm_center_triv:   forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
 [~: G, A] :&: 'C_G(A) = 1.
Proof.
move => A G norm co abel.
pose toG x : {x' | x' \in G} := insubd (Sub 1 (group1 G)) x.
have valG: {in G, cancel toG val} by move=> *; exact: insubdK.
pose Ggrp := [is {x | x \in G} <: finGroupType].
have mulGC : commutative (@mulg Ggrp).
  by case=> x Gx [y Gy]; apply: val_inj; rewrite /= (centsP abel).
pose gTG := Ring.AdditiveGroup (@mulgA _) mulGC (@mul1g _) (@mulVg _).
have Gval: forall u : gTG, sval u \in G by exact: valP.
have valM: forall a b : gTG, sval (a + b)%R = sval a * sval b by [].
pose f x y: gTG := toG (conjg x y).
pose phi y := sval (\sum_(x \in A) f y x)%R.
have morphic_phi: {in G &, {morph phi : x y / x * y}}.
  move => x y xin yin; rewrite /phi -valM -big_split //=. 
  congr (sval _); apply: eq_bigr => z; rewrite inE /= => Az.
  have xz: x ^ z \in G by rewrite memJ_norm //; apply (subsetP norm).
  have yz: y ^ z \in G by rewrite memJ_norm //; apply (subsetP norm).
  by rewrite /f conjMg; apply: val_inj; rewrite /= !valG //; apply: groupM.
have phia : forall a y, a \in A -> phi (conjg y a) = phi y.
  move=> a y ain; rewrite /phi; apply: sym_eq.
  rewrite (reindex (fun x => a * x))  /=; last first.
    - exists (fun x => a^-1 * x); move => b abin; rewrite //=; first by rewrite mulKg //.
      by rewrite mulKVg //.
    - rewrite (eq_bigl (fun x => x \in A)); last by move => x; rewrite //=; apply: groupMl.
      by congr (sval _); apply: eq_bigr => x xin; rewrite /f conjgM //.
pose Mphi := Morphism  morphic_phi.
have kerphi: forall c, c \in [~: G, A] -> c \in 'ker Mphi.
  move=>c; move/generatedP; apply {c}.
  apply/subsetP; move=> c; case/imset2P=> x a xin ain -> {c}. 
  have xinv : x^-1 \in G by apply:groupVr.
  have xconja: x ^ a \in G by rewrite memJ_norm //; apply: (subsetP norm).
  apply/morphpreP; split; rewrite/commg //=; first by apply: groupM.
  by apply/set1P; rewrite morphic_phi // phia // (morphV Mphi) //; apply: mulVg.
have centr : forall v, v \in 'C_G(A) -> phi v = v^+ #|A|.
  move=> v; rewrite inE; case/andP=> inG; move/centP=> inC.
  pose cphi y := sval (\sum_(x \in A) (toG y:gTG))%R.
  have phiv: phi v = cphi v.
    rewrite /phi /cphi; congr (sval _); apply: eq_bigr => x; rewrite inE // /f => xin.
    by congr (toG _); rewrite /conjg -{2}(mulKg x v); congr (x^-1*_); apply: inC.
  rewrite phiv /cphi sumr_const. 
  by elim: {+}#|_| => [  | n indh]; first done; rewrite //= valG // expgS indh.
have v1: forall v, v \in G ->  v ^+ #|A| = 1 -> v = 1.
  move => v vin; move/eqP; rewrite -order_dvd => div. 
  have ov1: #[ v ] = 1%nat.
    rewrite /coprime in co; apply/eqP; rewrite -dvdn1 -(eqP co).
    by apply: dvdn_gcd; last done; apply: order_dvd_g.
  rewrite -(expg1 v) -ov1; apply: order_expn1.
  apply/eqP; rewrite eqset_sub; apply/andP; split. 
  - apply/subsetP => x; case/setIP => inco incen; move: (incen).
    rewrite inE; case/andP=> inG ince; apply/set1P; apply: v1; first done.
    by rewrite -centr; last done; apply: (mker (kerphi x inco)).
  - by apply/subsetP => x; move/set1P ->; apply/setIP; split; apply: group1.
Qed. 

Theorem nilpotent_solvable: forall (G: {group T}), nilpotent G -> solvable G.
Proof.
move => G. rewrite /nilpotent; move/implyP => nil; rewrite /solvable; apply/implyP => sub.
apply: nil. move/forallP => nil. 
have nil1: forall (H: {group T}), H \subset G :&: [~: H, G] -> trivg H by move=> H; apply/implyP.
apply:sub; apply/forallP=>H; apply/implyP; rewrite subsetI; case/andP=> HsubG HsubC. 
apply: nil1; rewrite subsetI. apply/andP; split; first done. 
apply (subset_trans HsubC (commgS H HsubG)).
Qed.

Theorem abelian_nilpotent : forall G : {group T},
  abelian G -> nilpotent G.
Proof.
move=> G; move/centsP; move/commG1P; move/trivgP=> trivG'.
by apply/lcnP; exists 1%N.
Qed.

Theorem comm_center_dir_prod: forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
  G :=: [~: G, A] \x 'C_G(A).
move=> A G AsubNG coprime abel.
have trI: trivg ([~: G, A] :&: 'C_G(A)) by apply/trivgP; apply: comm_center_triv.
rewrite /direct_product trI // cprodGE.
- apply: comm_center_prod => //.
  apply: nilpotent_solvable; exact: abelian_nilpotent.
apply: subset_trans (centS (subsetIl _ _)); apply: subset_trans abel.
by rewrite /= commsgC subcomm_normal.
Qed.

Definition stabn (A:{set T}) (G G1:{group T}):= 
(G1 <| G) && (A \subset 'N(G1)) && (A/G1 \subset 'C(G/G1)).

Definition stabn_seq A G s:= path (stabn A) G s && (last (unit_group T) (G::s) == (unit_group T)).

Theorem centraliser1: 'C(1) = @setT T.
Proof. 
by apply/setP=> x; apply/centP; rewrite inE; move =>y; move /set1P ->; apply: commute1.
Qed.

Theorem stabn_seq_cent: forall (A G: {group T}) s, 
coprime #|G| #|A| -> solvable G -> stabn_seq A G s -> A \subset 'C(G).
Proof.
move => A G s; rewrite /stabn_seq; move: G.
elim: s => [G1 _ _|G1 t indh G cop solv]; rewrite /=; first by move /eqP ->; rewrite centraliser1; apply:subsetT.
rewrite /=. case/andP. case/andP. case /andP. case /andP.
move=> G1nG AnG1 subC ph lh.
have subC1: A \subset 'C(G1).
  apply: indh; last by apply/andP; split.
  - by have G1sG := normal_sub G1nG; rewrite -(LaGrange G1sG) coprime_mull in cop; case/andP: cop.
  - by apply: (solvable_sub (normal_sub G1nG)). 
have lem: G \subset G1 * 'C_G(A).
  rewrite -quotientSK; last by apply:normal_norm. 
  rewrite coprime_quotient_cent_weak; last done; last done; last done; last done.
  by rewrite subsetI; apply/andP; split; first done; rewrite centsC.
have lem2: G1 * 'C_G(A) \subset 'C(A).
  apply: mul_subG; first by rewrite centsC. by apply: subsetIr.
by rewrite centsC; apply: (subset_trans lem lem2).
Qed.

(* B+G Prop 1.09 *)
Theorem faithful_cent_fix_nil : forall A G: {group T},
    A \subset 'N(G) -> coprime #|G| #|A| -> nilpotent G ->
  'C_G('C_G(A)) \subset 'C(A) -> G \subset 'C(A).
Proof.
move=> A G subN co nil subC.
suff AsubCNC: A \subset 'C('N_G('C_G(A))).
  have eqGC: G = 'C_G(A)%G. 
    by apply: nilpotent_sub_norm; rewrite ? subsetIl // subsetI subsetIl centsC AsubCNC.
  rewrite eqGC; apply: subsetIr.
suff stab: stabn_seq A 'N_G('C_G(A)) [:: 'C_G(A)%G ; 1%G].
apply: stabn_seq_cent _ _ stab.
  by rewrite -(LaGrange (subsetIl G 'N('C_G(A)))) coprime_mull in co; case/andP: co.
  by apply: nilpotent_solvable; apply: (nilpotent_sub _ nil); rewrite subsetIl.
apply/andP; split; last done.
have AsubNC: A \subset 'N('C_G(A)).
  apply: (subset_trans _ (normI _ _)).
  rewrite subsetI subN /=; apply: (subset_trans (normG A) (cent_norm _)).
rewrite /stabn /= andbT; apply/andP; split. 
  rewrite /stabn AsubNC /(_ <| _) subsetIr subsetI subsetIl /= normG /=.
  apply: center_commgr. 
  rewrite gen_subG; apply/subsetP=> ax; case/imset2P=> a x Aa Nx ->{ax}.
  case/setIP: Nx => Gx Nx.
  have subCG: 'C_G('C_G(A)) \subset 'C_G(A) by rewrite subsetI subC subsetIl //. 
  apply: (subsetP subCG); rewrite inE commgEr groupMr // memJ_norm ?(subsetP subN, groupV) // Gx.
  apply/centP=> y Cy.
  rewrite /commute -mulgA (conjgCV x y) 2!mulgA; congr (_ * _).
  have Cyx: y ^ x^-1 \in 'C_G(A) by rewrite -mem_conjg (normP Nx). 
  have Cfixa: forall z, z \in 'C_G(A) -> z ^ a = z.
    by move=> z; case/setIP=> _ Cz; rewrite conjgE (centP Cz) ?mulKg.
  by rewrite -{2}(Cfixa y Cy) -(Cfixa _ Cyx) -!conjMg -conjgC.
rewrite /(_ <| _) sub1G normaliser1 !subsetT /= center_commgr //.
by rewrite [_ \subset _](sameP commG1P centsP) centsC subsetIr.
Qed.

Lemma norm_quot: forall A H: {group T},
A \subset 'N(H) -> coset_of H @*^-1 'N(A / H) \subset 'N(A * H).
Proof.
by move=> A H nHA; rewrite normC // -{8}(ker_coset H) -morphimK ?morphpre_norm.
Qed.

Lemma not_dvdn_partn1: forall n p,
  0 < n -> prime p -> ~ (p %| n) -> n`_p = 1%N.
Proof.
move=> n p npos pr; move/negP=> nd.
by rewrite p_part lognE npos pr //= (negbET nd).
Qed.

Lemma divp_pgroup_p: forall G: {group T}, forall p d, 1 < d -> prime p -> 
  p.-group G -> d %| #|G| -> pdiv d = p.
Proof.
move=> G p d lt1d pr; move/pgroupP=> pG dG; apply/eqP; apply: pG.
  exact: prime_pdiv.
exact: dvdn_trans (dvdn_pdiv _) dG.
Qed.

Lemma card_pgroup_p: forall (G : {group T}) p,
  prime p -> p.-group G -> #|G| = #|G|`_p.
Proof. by move=> G p _ pG; rewrite part_p_nat. Qed.

Lemma dvdn_sub_primes: forall d n: nat, 0 < n ->
  d %| n -> {subset primes d <= primes n}.
Proof.
move=> d n lt0n dvd m; rewrite !mem_primes lt0n; case/and3P=> -> _ /= dvm.
exact: dvdn_trans dvd.
Qed. 

Lemma pgroup_coprime: forall A H : {group T}, forall p : nat, prime p -> 
  p.-group A ->  ~ p %| #|H| -> coprime #|A| #|H|.
Proof.
move=> A H p pr; case/p_natP=> // k ->; move/negP; rewrite -prime_coprime //.
exact: coprime_expl.
Qed.

Lemma pgroup_quotient_normal_inv : forall A G H : {group T}, forall p : nat,
  prime p -> p.-group A -> A \subset G -> H <| G -> ~ p %| #|H| -> 
  forall x, x \in 'N(H) -> x \in G -> coset_of H x \in 'N(A / H) ->
  x \in 'N_G(A) * H.
Proof.
move=> A G H p pr pg AsubG normH pndvdn x Nx Gx xbin.
suff exz: exists2 z, z \in A * H & (A :^ x)%G = (A :^ z)%G.
  case exz=> z; case/imset2P=> a y ain yin  -> eq; move: (congr1 val eq).
  rewrite //= conjsgM (conjsgE _ a) rcoset_id // lcoset_id ?groupVr // => eqyx.
  rewrite -(mulgKV y x); apply/imset2P; apply: (Imset2spec _ yin); last done. 
  have yinG: y \in G by apply: (subsetP (normal_sub normH) _ yin).
  rewrite inE; rewrite groupM ?groupVr //=.
  by apply/normP; rewrite conjsgM eqyx conjsgK.
rewrite -norm_mulgenE; last by apply: (subset_trans AsubG (normal_norm normH)).
suff sylowA: p.-Sylow(A <*> H) A.
  apply: (sylow2_cor pr sylowA).
  suff xnormAH : x \in 'N(A <*> H).
    by rewrite //= -(conj_norm xnormAH) -(sylow_sconjg p (A <*> H) A x).
  rewrite //= norm_mulgenE; last by apply: (subset_trans AsubG (normal_norm normH)). 
  apply: (subsetP (norm_quot _)); first by apply: (subset_trans AsubG (normal_norm normH)).
  by rewrite morphpreE; apply/morphpreP.
rewrite piHallE sub_gen ?subsetUl //= norm_mulgenE; last by apply: (subset_trans AsubG (normal_norm normH)).
have co: coprime #|A| #|H| by apply: (pgroup_coprime pr).
rewrite (card_mulG_trivP _ _ (coprime_trivg co)). 
rewrite muln_part ?ltn_0mul ?ltn_0group //=.
rewrite (@not_dvdn_partn1 #|H|); rewrite //=; last by apply: pos_card_group.
by rewrite muln1; apply/eqP; apply: card_pgroup_p.
Qed.

Lemma pgroup_quotient_normal : forall A G H: {group T}, forall p:nat, prime p ->
    p.-group A -> A \subset G -> H <| G -> ~ p %| #|H| -> 
  'N_G(A) / H = 'N_(G / H)(A / H).
move => A G H p pr pgroupA AsubG normH co.
apply/eqP; rewrite eqset_sub subsetI morphimS ?subsetIl //= morphim_norms ?morphimS ?subsetIr //=.
apply/subsetP=> xb; case/setIP; rewrite quotientE; case /morphimP=> x Nx Gx -> xbin.
rewrite -quotient_mulg; apply/imsetP; exists x; rewrite // inE Nx /=.
apply: (pgroup_quotient_normal_inv pr); rewrite //.
Qed.

Lemma pgroup_quotient_central : forall A G H: {group T}, forall p:nat, prime p ->
    p.-group A -> A \subset G -> H <| G -> ~ p %| #|H| -> 
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move => A G H p pr pgroupA AsubG normH pndivn.
apply/eqP; rewrite eqset_sub subsetI morphimS ?subsetIl //=.
rewrite morphim_cents ?morphimS ?subsetIr //=. 
apply/subsetP=> xb; case/setIP. 
rewrite quotientE; case /morphimP=> x Nx Gx -> xbin.
rewrite -quotient_mulg; apply/imsetP; exists x; rewrite // inE Nx /=.
have nHA: A \subset 'N(H) by apply: subset_trans AsubG _; case/andP: normH.
suff subC: coset_of H @*^-1 'C_(G / H)(A / H) :&: 'N_G(A) \subset 'C_G(A).
  apply: (subsetP (mulSg _ subC)); rewrite group_modr ?in_setI; rewrite ?Nx //=.
  - rewrite inE in_setI xbin -andbA /=; apply/andP; split. 
    by apply/imsetP; exists x; rewrite ?in_setI ?Nx.
    by apply: (pgroup_quotient_normal_inv pr); rewrite //; apply: (subsetP (cent_subset _)).
  - have lem: H \subset coset_of H @*^-1 ('C_G(A)/H).
      by rewrite morphimK ?ker_coset ?mulG_subl ?(subset_trans (subsetIl _ _)) ?normal_norm.
    apply: (subset_trans lem); apply: morphpreS.
    by rewrite subsetI morphimS ?subsetIl ?morphim_cents ?subsetIr.
rewrite subsetI {x Nx Gx xbin}. rewrite {1}subIset ?subsetIl ?orb_true_r //=.
apply/centsP; apply/commG1P; apply/trivgP; apply/eqP; rewrite eqset_sub sub1G andb_true_r.
have co: coprime #|H| #|A| by rewrite coprime_sym; apply: (pgroup_coprime pr).
rewrite -(trivgP _ (coprime_trivg co)); rewrite subsetI; apply/andP; split.
- apply: (subset_trans (commSg _ (subsetIl _ _))); apply: center_commgl; rewrite //.
  - apply: (subset_trans _ (normal_norm normH)); have HsubG := normal_sub normH.
    rewrite sub_morphpre_im ?subsetIl ?ker_coset ?normal_norm //=. 
    by apply: (subset_trans (subsetIl _ _)); apply: morphimS; apply: normal_norm.
  - apply/subsetP=> Hx; case/imsetP=> x; rewrite in_setI; case/andP => xinN.
    by rewrite !inE; case/andP => _ ; case/andP => _ Hxin ->.
- by apply: (subset_trans (commSg _ (subsetIr _ _))); rewrite subcomm_normal subsetIr.
Qed.

End coprime_comm.
