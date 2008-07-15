Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths connect finfun ssralg bigops finset.
Require Import groups normal commutators.
Require Import cyclic center sylow dirprod schurzass hall coprime_act.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.
Variable T : finGroupType.

Lemma sub_gmul: forall (G H K : group T), G \subset 'N(K) -> H \subset 'N(K) ->
G/K  \subset H/K -> G \subset K * H.
move=> G H K normG normH.
rewrite quotientE; rewrite quotientE; move/subsetP=> sub; apply/subsetP=> g gin.
have exh: exists2 h : T, h \in 'N(K) :&: H & coset_of K g = coset_of K h.
  apply/imsetP; apply: sub; apply/imsetP; exists g; rewrite //.
  by apply/setIP; split; rewrite //=; apply: (subsetP normG).
case exh => h; case/setIP => inNK inH coseteq.
rewrite -mem_rcosets; apply/rcosetsP; exists h; first done. 
rewrite -(coset_ofN inNK); rewrite -(coset_ofN (subsetP normG _ gin)).
by congr val.
Qed.

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

Lemma comm_center_prod: forall (A G: group T),
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  G = [~: G, A] * 'C_G(A) :> set _.
Proof.
move=> A G AsubNG coprime solv.
apply/eqP; rewrite eqset_sub; apply/andP; split.
- apply: sub_gmul; rewrite /=; first by apply:normGR.
  - by apply: (subset_trans _ (normGR G A)); rewrite /centraliser; apply: subsetIl.
  - rewrite coprime_quotient_cent_weak //=.
    - by rewrite subsetI; apply/andP; split; last by apply: center_commgr.
    - apply/andP; rewrite //=; split; last by apply:normGR.
      by rewrite commsgC subcomm_normal //.
    - by rewrite commsgC; apply: normGR.
- rewrite -{3}mulGid; apply:imset2S; last by apply: subsetIl.
  by rewrite commsgC subcomm_normal //.
Qed.

Lemma commGAA:   forall (A G: group T),
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  [~: G, A] = [~: G, A, A].
move=> A G AsubNG coprime solv.
apply/eqP; rewrite eqset_sub; apply/andP; split; last first.
Search [subset commutator].
- by apply:commSg; rewrite commsgC subcomm_normal //.
- rewrite {1}(comm_center_prod AsubNG coprime solv).
  rewrite distr_sgcomm /=.
  - by rewrite triv_comm_centr mulg1; apply: subset_refl.
  - apply: (subset_trans (subsetIl G 'C(A))); apply: normGR.
  - apply: (subset_trans (subsetIr G 'C(A))); apply cent_subset.
Qed.

Lemma comm_center_triv:   forall (A G: group T),
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G ->
 [~: G, A] :&: 'C_G(A) = 1.
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
  move => v vin; move/eqP; rewrite -orderg_dvd => div. 
  have ov1: #[ v ] = 1%nat.
    rewrite /coprime in co; apply/eqP; rewrite -dvdn1 -(eqP co).
    by apply: dvdn_gcd; last done; apply: orderg_dvd_g.
  rewrite -(expg1 v) -ov1; apply: orderg_expn1.
  apply/eqP; rewrite eqset_sub; apply/andP; split. 
  - apply/subsetP => x; case/setIP => inco incen; move: (incen).
    rewrite inE; case/andP=> inG ince; apply/set1P; apply: v1; first done.
    by rewrite -centr; last done; apply: (mker (kerphi x inco)).
  - by apply/subsetP => x; move/set1P ->; apply/setIP; split; apply: group1.
Qed. 
 