Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun bigops finset ssralg.
Require Import groups morphisms normal commutators.
Require Import cyclic center pgroups sylow gprod schurzass hall. 
Require Import coprime_act nilpotent.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section coprime_comm.
Variable T : finGroupType.

(* same as the following but with weaker assumptions 
Lemma comm_center_prod: forall (A G: group T),
  A \subset 'N(G) -> coprime #|[~: G, A]| #|A| -> solvable [~: G, A] ->
  G = [~: G, A] * 'C_G(A) :> set _.
Proof.
move=> A G AsubNG coprime solv.
apply/eqP; rewrite eqEsubset; apply/andP; split.
- apply: sub_gmul; rewrite /=; first by apply:commg_norml.
  - by apply: (subset_trans _ (commg_norml G A)); rewrite /centraliser; apply: subsetIl.
  - rewrite coprime_quotient_cent //=.
    - by rewrite subsetI; apply/andP; split; last by apply: quotient_cents2r.
    - apply/andP; rewrite //=; split; last by apply:commg_norml.
      by rewrite commGC commg_subr //.
    - by rewrite commGC; apply: commg_norml.
- rewrite -{3}mulGid; apply:imset2S; last by apply: subsetIl.
  by rewrite commGC commg_subr //.
Qed.
*)

Lemma comm_center_prod : forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  G :=: [~: G, A] * 'C_G(A).
Proof.
move=> A G AsubNG coprime solv.
apply/eqP; rewrite eqEsubset andbC -{3}mulGid imset2S ?subsetIl //; last first.
  by rewrite commGC commg_subr.
rewrite -quotientSK ?commg_norml // coprime_quotient_cent_weak //=; last first.
- by rewrite commGC commg_norml.
- by rewrite [_ <| G]andbC commg_norml commGC commg_subr.
by rewrite subsetI andbC quotient_cents2r /=.
Qed.

Lemma commGAA:   forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  [~: G, A] = [~: G, A, A].
Proof.
move=> A G AsubNG coGA solG.
apply/eqP; rewrite eqEsubset; apply/andP; split; last first.
  by rewrite commSg // commg_subl.
rewrite {1}(comm_center_prod AsubNG coGA solG) commMG.
- by rewrite (commG1P (subsetIr _ _)) //= mulg1.
- by rewrite subIset // commg_norml.
by rewrite subIset // orbC cent_sub.
Qed.

Lemma comm_center_triv:   forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
 [~: G, A] :&: 'C_G(A) = 1.
Proof.
move => A G norm co abel.
have mulGC : @commutative (subg_of G) mulg.
  by case=> x Gx [y Gy]; apply: val_inj; rewrite /= (centsP abel).
pose gTm := ZmodMixin (@mulgA _) mulGC (@mul1g _) (@mulVg _).
pose gTG := ZmodType gTm; hnf in gTG.
have Gval: forall u : gTG, sgval u \in G by exact: valP.
have valM: forall a b : gTG, sgval (a + b)%R = sgval a * sgval b by [].
pose f x y : gTG := subg G (conjg x y).
pose phi y := sgval (\sum_(x \in A) f y x)%R.
have morphic_phi: {in G &, {morph phi : x y / x * y}}.
  move => x y xin yin; rewrite /phi -valM -big_split //=. 
  congr (sgval _); apply: eq_bigr => z Az.
  have xz: x ^ z \in G by rewrite memJ_norm //; apply (subsetP norm).
  have yz: y ^ z \in G by rewrite memJ_norm //; apply (subsetP norm).
  by rewrite /f conjMg; apply: val_inj; rewrite /= !subgK //; apply: groupM.
have phia : forall a y, a \in A -> phi (conjg y a) = phi y.
  move=> a y ain; rewrite /phi; apply: sym_eq.
  rewrite (reindex (fun x => a * x))  /=; last first.
    - exists (fun x => a^-1 * x); move => b abin; rewrite //=; first by rewrite mulKg //.
      by rewrite mulKVg //.
    - rewrite (eq_bigl (fun x => x \in A)); last by move => x; rewrite //=; apply: groupMl.
      by congr (sgval _); apply: eq_bigr => x xin; rewrite /f conjgM //.
pose Mphi := Morphism  morphic_phi.
have kerphi: forall c, c \in [~: G, A] -> c \in 'ker Mphi.
  move=>c; move/generatedP; apply {c}.
  apply/subsetP; move=> c; case/imset2P=> x a xin ain -> {c}. 
  have xinv : x^-1 \in G by apply:groupVr.
  have xconja: x ^ a \in G by rewrite memJ_norm //; apply: (subsetP norm).
  apply/morphpreP; split; rewrite/commg //=; first by apply: groupM.
  by apply/set1P; rewrite morphic_phi // phia // [phi _](morphV Mphi) // mulVg.
have centr : forall v, v \in 'C_G(A) -> phi v = v^+ #|A|.
  move=> v; rewrite inE; case/andP=> inG; move/centP=> inC.
  pose cphi y := sgval (\sum_(x \in A) (subg G y : gTG))%R.
  have phiv: phi v = cphi v.
    congr (sgval _); apply: eq_bigr => x; rewrite /f => xin.
    by congr subg; rewrite /conjg -{2}(mulKg x v); congr (_ * _); apply: inC.
  rewrite phiv /cphi GRing.sumr_const. 
  by case: {+}#|_| => //; elim=> [|n IHn]; rewrite /= subgK ?IHn.
have v1: forall v, v \in G ->  v ^+ #|A| = 1 -> v = 1.
  move => v vin; move/eqP; rewrite -order_dvdn => div. 
  have ov1: #[ v ] = 1%nat.
    rewrite /coprime in co; apply/eqP.
    by rewrite -dvdn1 -(eqP co) dvdn_gcd order_dvdG.
  rewrite -(expg1 v) -ov1; apply: expg_order.
  apply/eqP; rewrite eqEsubset; apply/andP; split. 
  - apply/subsetP => x; case/setIP=> inco incen; move: (incen).
    rewrite inE; case/andP=> inG ince; apply/set1P; apply: v1; first done.
    by rewrite -centr; last done; apply: (mker (kerphi x inco)).
  - by apply/subsetP => x; move/set1P ->; apply/setIP; split; apply: group1.
Qed. 

Theorem comm_center_dir_prod: forall A G : {group T},
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
  G :=: [~: G, A] \x 'C_G(A).
move=> A G AsubNG coprime abel.
have trI: [~: G, A] :&: 'C_G(A) = 1 by apply: comm_center_triv.
rewrite dprodE //.
- apply: comm_center_prod => //.
  apply: nilpotent_sol; exact: abelian_nil.
apply: subset_trans (centS (subsetIl _ _)); apply: subset_trans abel.
by rewrite commg_subl.
Qed.

Definition stabn (A:{set T}) (G G1:{group T}):= 
  (G1 <| G) && (A \subset 'N(G1)) && (A/G1 \subset 'C(G/G1)).

Definition stabn_seq A G s:=
  path (stabn A) G s && (last [1 T]%G (G :: s) == [1 T]%G).

Theorem stabn_seq_cent: forall (A G: {group T}) s, 
coprime #|G| #|A| -> solvable G -> stabn_seq A G s -> A \subset 'C(G).
Proof.
move => A G s; rewrite /stabn_seq; move: G.
elim: s => [G1 _ _|G1 t indh G cop solv] /=; first by move/eqP->; rewrite cents1.
rewrite /=. case/andP. case/andP. case /andP. case /andP.
move=> G1nG AnG1 subC ph lh.
have subC1: A \subset 'C(G1).
  apply: indh; last by apply/andP; split.
  - by have G1sG := normal_sub G1nG; rewrite -(LaGrange G1sG) coprime_mull in cop; case/andP: cop.
  - by apply: (solvableS (normal_sub G1nG)). 
have lem: G \subset G1 * 'C_G(A).
  rewrite -quotientSK; last by apply:normal_norm. 
  by rewrite coprime_quotient_cent_weak // subsetI subxx /= centsC.
have lem2: G1 * 'C_G(A) \subset 'C(A).
  by apply: mul_subG; [rewrite centsC | exact: subsetIr].
by rewrite centsC; apply: (subset_trans lem lem2).
Qed.

(* B+G Prop 1.09 *)
Theorem faithful_cent_fix_nil : forall A G: {group T},
    A \subset 'N(G) -> coprime #|G| #|A| -> nilpotent G ->
  'C_G('C_G(A)) \subset 'C(A) -> G \subset 'C(A).
Proof.
move=> A G subN co nil subC.
suff AsubCNC: A \subset 'C('N_G('C_G(A))).
  apply/setIidPl; symmetry; apply: nilpotent_sub_norm; rewrite ?subsetIl //.
  by rewrite subsetI subsetIl centsC AsubCNC.
suff stab: stabn_seq A 'N_G('C_G(A)) [:: 'C_G(A)%G ; 1%G].
apply: stabn_seq_cent _ _ stab.
  by rewrite -(LaGrange (subsetIl G 'N('C_G(A)))) coprime_mull in co; case/andP: co.
  by apply: nilpotent_sol; apply: (nilpotentS _ nil); rewrite subsetIl.
apply/andP; split; last done.
have AsubNC: A \subset 'N('C_G(A)) by rewrite normsI ?norms_cent ?normG.
rewrite /stabn /= andbT; apply/andP; split. 
  rewrite /stabn AsubNC /(_ <| _) subsetIr subsetI subsetIl /= normG /=.
  apply: quotient_cents2r. 
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
rewrite /(_ <| _) sub1G norm1 !subsetT /= quotient_cents2r //.
by rewrite (sameP trivgP commG1P) centsC subsetIr.
Qed.

Lemma not_dvdn_partn1: forall n p,
  0 < n -> prime p -> ~ (p %| n) -> n`_p = 1%N.
Proof.
move=> n p npos pr; move/negP=> nd.
by rewrite p_part lognE npos pr //= (negbTE nd).
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
Proof. by move=> G p _ pG; rewrite part_pnat. Qed.

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
  forall x, x \in 'N(H) -> x \in G -> coset H x \in 'N(A / H) ->
  x \in 'N_G(A) * H.
Proof.
move=> A G H p pr pg AsubG normH pndvdn x Nx Gx xbin.
suff exz: exists2 z, z \in A * H & A :^ x :=: A :^ z.
  case exz=> z; case/imset2P=> a y ain yin  ->.
  rewrite //= conjsgM (conjsgE _ a) rcoset_id // lcoset_id ?groupVr // => eqyx.
  rewrite -(mulgKV y x) mem_imset2 //.
  have yinG: y \in G by apply: (subsetP (normal_sub normH) _ yin).
  rewrite inE groupM ?groupVr //=.
  by apply/normP; rewrite conjsgM eqyx conjsgK.
rewrite -norm_mulgenEl; last by apply: (subset_trans AsubG (normal_norm normH)).
suff sylowA: p.-Sylow(A <*> H) A.
  apply: (Sylow_trans sylowA).
  suff xnormAH : x \in 'N(A <*> H) by rewrite /= -(normP xnormAH) pHallJ2.
  have nAH : A \subset 'N(H) by apply: subset_trans (normal_norm normH).
  rewrite mulgenC norm_mulgenEr // -quotientK //.
  by rewrite (subsetP (morphpre_norm _ _)) ?mem_morphpre.
rewrite pHallE sub_gen ?subsetUl //= norm_mulgenEl; last by apply: (subset_trans AsubG (normal_norm normH)).
have co: coprime #|A| #|H| by apply: (pgroup_coprime pr).
rewrite coprime_cardMg // partn_mul ?muln_gt0 ?cardG_gt0 //=.
rewrite (@not_dvdn_partn1 #|H|); rewrite //=; last by apply: cardG_gt0.
by rewrite muln1; apply/eqP; apply: card_pgroup_p.
Qed.


Lemma pgroup_quotient_normal : forall A G H: {group T}, forall p:nat, prime p ->
    p.-group A -> A \subset G -> H <| G -> ~ p %| #|H| -> 
  'N_G(A) / H = 'N_(G / H)(A / H).
move => A G H p pr pgroupA AsubG normH co.
apply/eqP; rewrite eqEsubset subsetI morphimS ?subsetIl //= morphim_norms ?morphimS ?subsetIr //=.
apply/subsetP=> xb; case/setIP; rewrite quotientE; case /morphimP=> x Nx Gx -> xbin.
rewrite -quotient_mulg; apply/imsetP; exists x; rewrite // inE Nx /=.
apply: (pgroup_quotient_normal_inv pr); rewrite //.
Qed.

Lemma pgroup_quotient_central : forall A G H: {group T}, forall p:nat, prime p ->
    p.-group A -> A \subset G -> H <| G -> ~ p %| #|H| -> 
  'C_G(A) / H = 'C_(G / H)(A / H).
Proof.
move => A G H p pr pgroupA AsubG normH pndivn.
apply/eqP; rewrite eqEsubset subsetI morphimS ?subsetIl //=.
rewrite morphim_cents ?morphimS ?subsetIr //=. 
apply/subsetP=> xb; case/setIP. 
rewrite quotientE; case /morphimP=> x Nx Gx -> xbin.
rewrite -quotient_mulg; apply/imsetP; exists x; rewrite // inE Nx /=.
have nHA: A \subset 'N(H) by apply: subset_trans AsubG _; case/andP: normH.
suff subC: coset H @*^-1 'C_(G / H)(A / H) :&: 'N_G(A) \subset 'C_G(A).
  apply: (subsetP (mulSg _ subC)); rewrite group_modr ?in_setI; rewrite ?Nx //=.
  - rewrite inE in_setI xbin -andbA /=; apply/andP; split. 
    by apply/imsetP; exists x; rewrite ?in_setI ?Nx.
    by apply: (pgroup_quotient_normal_inv pr); rewrite //; apply: (subsetP (cent_sub _)).
  - have lem: H \subset coset H @*^-1 ('C_G(A) / H).
      by rewrite morphimK ?ker_coset ?mulG_subl ?(subset_trans (subsetIl _ _)) ?normal_norm.
    apply: (subset_trans lem); apply: morphpreS.
    by rewrite subsetI morphimS ?subsetIl ?morphim_cents ?subsetIr.
rewrite subsetI {1}subIset ?subsetIl ?orbT {x Nx Gx xbin}//=.
have co: coprime #|H| #|A| by rewrite coprime_sym; apply: (pgroup_coprime pr).
rewrite (sameP commG1P trivgP) -(coprime_TIg co).
rewrite subsetI commg_subr /= {2}setIA subsetIr andbT.
apply: subset_trans (commSg _ (subsetIl _ _)) _.
by rewrite -quotient_cents2 ?subsetIl // cosetpreK subsetIr.
Qed.

End coprime_comm.
