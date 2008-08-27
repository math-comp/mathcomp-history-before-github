(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of the center of a group and a centraliser             *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype div prime finset ssralg bigops.
Require Import groups morphisms action normal pgroups automorphism.
Require Import cyclic dirprod.

(* Require Import seq paths connecct bigops group_perm. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Definition center (gT : finGroupType) (A : {set gT}) := 'C_A(A).

Notation "''Z' ( A )" := (center A)
  (at level 9, format "''Z' ( A )") : group_scope.

Canonical Structure center_group (gT : finGroupType) (H : {group gT}) :=
  Eval hnf in [group of 'Z(H)].

Notation "''Z' ( H )" := (center_group H) : subgroup_scope.

Section Center.

Variable gT : finGroupType.
Implicit Types x y : gT.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Lemma subcentP : forall A B x,
  reflect (x \in A /\ centralises x B) (x \in 'C_A(B)).
Proof.
move=> A B x; rewrite inE. case: (x \in A); last by right; case.
by apply: (iffP centP) => [|[]].
Qed.

Lemma centerP : forall A x,
  reflect (x \in A /\ centralises x A) (x \in 'Z(A)).
Proof. move=> A x; exact: subcentP. Qed.

Lemma subset_center : forall A, 'Z(A) \subset A.
Proof. move=> A; exact: subsetIl. Qed.

Lemma center1: 'Z(1) = 1 :> set gT .
Proof. by apply/eqP; rewrite eqset_sub subset_center sub1G. Qed.

Lemma centerC : forall A, {in A, centralised 'Z(A)}.
Proof. by move=> A; apply/centsP; rewrite centsC subsetIr. Qed.

Lemma centerN : forall H, 'Z(H) <| H.
Proof.
move=> H; apply/normalP; split=> [|x Hx]; first exact: subset_center.
by rewrite conjIg conjGid // (normsP (cent_norm _)) // (subsetP (normG _)).
Qed.

Lemma characteristic_center : forall H, 'Z(H) \char H.
Proof.
move=> H; apply/charP; split=> [|f injf Hf]; first exact: subset_center.
apply/morphim_fixP=> //; first exact: subsetIl.
by rewrite /= -{4}Hf subsetI morphimS ?subsetIl // morphimIdom morphim_cent.
Qed.

Section CyclicCenter.

Variable H : group gT.

(* G. 1.3.4 *)

Lemma center_cyclic_abelian : cyclic (H / 'Z(H)) -> H :=: 'Z(H).
Proof.
case/cyclicP=> a Ha; apply/eqP; rewrite eqset_sub subset_center /= andbT.
case: (cosetP a) => /= z Nz def_a.
have H_Zz: H :=: 'Z(H) * <[z]>.
  rewrite -['Z(H)]ker_coset -morphimK ?cycle_h ?morphim_cycle //=.
  by rewrite -def_a -Ha morphimGK ?ker_coset //; case/andP: (centerN H).
rewrite -(mulg1 'Z(H)) {1}H_Zz mulGS mulg1 /= H_Zz subsetI mulG_subr /=.
rewrite centMG subsetI centsC subIset /=.
  apply/centsP; exact: commute_cycle_com.
by rewrite orbC centS // H_Zz mulG_subr.
Qed.

End CyclicCenter.

(*********************************************************************)
(*              Definition of the centraliser                        *)
(*    y is in the centraliser of x if y * x = x * y                  *)
(*********************************************************************)

Variable H : {group gT}.

Lemma centraliser_id : forall x, x \in H -> x \in 'C_H[x].
Proof. move=> x Hx; rewrite inE Hx; exact/cent1P. Qed.

Lemma centraliserP: forall x y,
  reflect (y \in H /\ commute x y) (y \in 'C_H[x]).
Proof.
by move=> x y; apply: (iffP (setIP _ _ _))=> [] [Hy];
  last move/commute_sym; move/cent1P.
Qed.

Lemma subset_centraliser : forall x, 'C_H[x] \subset H.
Proof. move=> x; exact: subsetIl. Qed.

Lemma centraliserC : forall x y,
  x \in H -> y \in 'C_H[x] -> x \in 'C_H[y].
Proof. by move=> x y Hx; case/centraliserP=> *; apply/centraliserP. Qed.

(* most certainly redundant *)
Lemma centraliserM : forall x y z,
  y \in 'C_H[x] -> z \in 'C_H[x] -> y * z \in 'C_H[x].
Proof. move=> *; exact: groupM. Qed.

Lemma centraliserV : forall x y,
  y \in 'C_H[x] -> y^-1 \in 'C_H[x].
Proof. by move=> *; rewrite groupV. Qed.

Lemma centraliserXr : forall x y n,
  y \in 'C_H[x] -> y ^+ n \in 'C_H[x].
Proof. move=> *; exact: groupX. Qed.

Lemma centraliserXl : forall x y n, x \in H ->
  y \in 'C_H[x] -> y \in 'C_H[x ^+ n].
Proof.
move => x y n Hx; case/centraliserP=> Hy cxy.
by apply: centraliserC=> //; apply: centraliserXr; apply/centraliserP.
Qed.

Section CyclicCentraliser.

Lemma normal_centraliser: forall x, x \in H -> 'C_H[x] \subset 'N(<[x]>).
Proof.
move=> x Hx; apply/normsP=> y.
case/centraliserP=> Hy cxy; apply/setP=> z.
by rewrite -cycle_conjgs /conjg cxy mulgA; gsimpl.
Qed.

Lemma cycle_subset_centraliser: forall x,
     x \in H -> <[x]> \subset 'C_H[x].
Proof.
move => x Hx; apply/subsetP=> y; case/cycleP=> n <-{y}.
by rewrite centraliserXr // centraliser_id.
Qed.

Lemma centraliser_normaliser:
  forall x, x \in H -> 'C_H[x] \subset 'N(<[x]>).
Proof. exact: normal_centraliser. (* sic!!! -- GG *) Qed.

End CyclicCentraliser.

End Center.

(* Maybe this should be put in dirprod but then there is
   a circular dependency dir_prod -> fp -> center *)
Section Product.

Variable gT : finGroupType.
Infix "\*" := central_product (at level 40, left associativity).
Implicit Types G H : {group gT}.
Implicit Types A B C : {set gT}.

Lemma center_prod: forall (H1 H2: {group gT}),
   H1 \subset 'C(H2) -> 'Z(H1) * 'Z(H2) = 'Z(H1 * H2).
Proof.
move=> H1 H2 CH1H2.
apply/eqP; rewrite eqset_sub; apply/andP; split.
  apply/subsetP => x; case/imset2P => x1 x2; rewrite !inE.
  case/andP => H1x1 H2x1; case/andP => H1x2 H2x2 ->.
  apply/andP; split; first by apply/imset2P; exists x1 x2.
  apply/centP => z; case/imset2P => z1 z2 Hz1 Hz2 ->.
  move/centP: H2x1; move/(_ _ Hz1) => R1.
  move/centP: H2x2; move/(_ _ Hz2) => R2.
  move: (subsetP CH1H2 _ H1x1); move/centP; move/(_ _ Hz2) => R3.
  move: (subsetP CH1H2 _ Hz1); move/centP; move/(_ _ H1x2) => R4.
  by rewrite /commute -!mulgA [x2 * _ ]mulgA -R4 !mulgA R1
             -!mulgA R2 [x1 * _ ]mulgA R3 !mulgA.
apply/subsetP => z.
rewrite !inE; case/andP; case/imset2P => z1 z2 Hz1 Hz2 ->.
move/centP => Hz1z2; apply/imset2P; exists z1 z2;
 rewrite // inE ?Hz1 ?Hz2; apply/centP => t Ht.
  have Htz2m1: t * z2^-1 \in H1 * H2.
    by apply/imset2P; exists t z2^-1; rewrite // groupV.
  move: (Hz1z2 _ Htz2m1).
  move: (subsetP CH1H2 _ Hz1); move/centP; move/(_ _ Hz2) => R1.
  have Hz2m1: z2^-1 \in H2 by rewrite groupV.
  move: (subsetP CH1H2 _ Ht); move/centP; move/(_ _ Hz2m1) => R2.
  by rewrite /commute {2}R1 {1}R2 !mulgA mulgK mulgKV.
have Hz1m1t: z1^-1 * t \in H1 * H2.
  by apply/imset2P; exists z1^-1 t; rewrite // groupV.
move: (Hz1z2 _ Hz1m1t).
move: (subsetP CH1H2 _ Hz1); move/centP; move/(_ _ Hz2) => R1.
have Hz1m1: z1^-1 \in H1 by rewrite groupV.
move: (subsetP CH1H2 _ Hz1m1); move/centP; move/(_ _ Ht) => R2.
by rewrite /commute {1}R1 {2}R2 !mulgA mulgK mulgKV.
Qed.

Lemma center_cprod : forall A B G, A \* B = G -> 'Z(A) \* 'Z(B) = 'Z(G).
Proof.
move=> A B G; case/cprodGP => H1 H2 -> -> <- CH1H2.
rewrite -center_prod // /(A \* B).
case: eqP => E1; first by rewrite E1 mul1g.
case: eqP => E2; first by rewrite E2 mulg1.
suff->: 'Z(H1) \subset 'C('Z(H2)) by rewrite !groupP.
apply/subsetP => x1; rewrite inE; case/andP => H1x1 H2x1.
apply/centP => x2; rewrite inE; case/andP => H1x2 H2x2.
by move: (subsetP CH1H2 _ H1x1); move/centP; move/(_ _ H1x2).
Qed.

(* I don't like this I -> {group gT} but I need it to apply center_prod *)
Lemma center_bigcprod : forall I r P (F: I -> {group gT}) G,
  \big[central_product/1]_(i <- r | P i) F i = G
  -> \prod_(i <- r | P i) 'Z(F i) = 'Z(G).
Proof.
move=> I r P F; rewrite -!(big_filter r).
elim: {r}filter => [|i r IHr] G; rewrite !(big_seq0, big_adds) //=.
  by move<-; rewrite center1.
case/cprodGP => _ G' _ defG' <- HH.
by rewrite defG' (IHr _ defG') center_prod // -defG'.
Qed.

Lemma center_dprod : forall A B G, A \x B = G -> 'Z(A) \x 'Z(B) = 'Z(G).
Proof.
move=> A B G; rewrite  /(_ \x _) /(_ \x _); case E1: (trivg _); last first.
  by move/setP; move/(_ 1); rewrite group1 inE.
suff->: trivg ('Z(A) :&: 'Z(B)) by exact: center_cprod.
apply: (subset_trans _ (idP E1)).
apply: (subset_trans _ (setSI B (subset_center A))).
apply: setIS; apply: subset_center.
Qed.

(* I don't like this I -> {group gT} but I need it to apply center_prod *)
Lemma center_bigdprod : forall I r P (F: I -> {group gT}) G,
  \big[direct_product/1]_(i <- r | P i) F i = G
  -> \prod_(i <- r | P i) 'Z(F i) = 'Z(G).
Proof.
move=> I r P F; rewrite -!(big_filter r).
elim: {r}filter => [|i r IHr] G; rewrite !(big_seq0, big_adds) //=.
  by move<-; rewrite center1.
case/dprodGP=> [[_ G' _ defG' defG CH _]].
by rewrite (IHr _ defG') center_prod // -defG' // defG.
Qed.


End Product.


Section CharacteristicCentralizer.

Variable gT : finGroupType.

Lemma char_cent : forall G H : {group gT},
  H \char G -> 'C_G(H) \char G.
Proof.
move=> G H; case/charP=> sHG chHG; apply/charP.
split=> [|f injf Gf]; last apply/morphim_fixP; rewrite ?subsetIl //.
have{chHG} Hf: f @* H = H by exact: chHG.
by rewrite morphimGI ?subsetIl // Gf setIS // -{2}Hf morphim_cent.
Qed.

End CharacteristicCentralizer.


Section PGroups.
(* Some properties on p-groups *)

Variable p n: nat.
Variable Hp: prime p.
Variable gT: finGroupType.
Variable G: {group gT}.
Variable HG: #|G| = (p ^ n.+1)%N.

Open Scope group_scope.

Lemma pgroup_ntriv : ~~ trivg 'Z(G).
Proof.
apply/trivgP=> /= Z1.
suffices{Z1}: #|'Z(G)| %% p = 0 by rewrite Z1 cards1 modn_small ?prime_gt1.
suff ->: 'Z(G) = 'C_G(G | 'J).
  have: pgroup p G by apply/p1_natP=> //; exists n.+1.
  move/pgroup_fix_mod=> <- //; first by rewrite HG modn_mulr.
  apply/actsP=> x Gx y; exact: groupJr.
congr (_ :&: _); apply/setP=> x; apply/centP/afixP=> cxG y; move/cxG=> /=.
  by move/commgP; move/conjg_fixP.
by move/conjg_fixP; move/commgP.
Qed.

End PGroups.


