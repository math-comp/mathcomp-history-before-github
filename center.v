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

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype div.
Require Import finset bigops groups morphisms normal automorphism cyclic.
Require Import gprod gfunc.

(* Require Import seq paths connecct bigops perm. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Defs.

Variable gT : finGroupType.

Definition center (A : {set gT}) := 'C_A(A).

Canonical Structure center_group (G : {group gT}) : {group gT} :=
  Eval hnf in [group of center G].

End Defs.

Notation "''Z' ( A )" := (center A)
  (at level 9, format "''Z' ( A )") : group_scope.
Notation "''Z' ( H )" := (center_group H) : subgroup_scope.

Section Center.

Variables gT : finGroupType.
Implicit Type rT : finGroupType.
Implicit Types x y : gT.
Implicit Types A B : {set gT}.
Implicit Types G H K D : {group gT}.

Lemma subcentP : forall A B x,
  reflect (x \in A /\ centralises x B) (x \in 'C_A(B)).
Proof.
move=> A B x; rewrite inE. case: (x \in A); last by right; case.
by apply: (iffP centP) => [|[]].
Qed.

Lemma subcent_sub : forall A B, 'C_A(B) \subset 'N_A(B).
Proof. by move=> A B; rewrite setIS ?cent_sub. Qed.

Lemma subcent_norm : forall G B, 'N_G(B) \subset 'N('C_G(B)).
Proof. by move=> G B; rewrite normsI ?subIset ?normG // orbC cent_norm.  Qed.

Lemma subcent_normal : forall G B, 'C_G(B) <| 'N_G(B).
Proof. by move=> G B; rewrite /normal subcent_sub subcent_norm. Qed.

Lemma subcent_char : forall G H K, H \char G -> K \char G -> 'C_H(K) \char G.
Proof.
move=> G H K; case/charP=> sHG chHG; case/charP=> sKG chKG; apply/charP.
split=> [|f injf Gf]; first by rewrite subIset ?sHG.
by rewrite injm_subcent ?chHG ?chKG.
Qed.

Lemma centerP : forall A x,
  reflect (x \in A /\ centralises x A) (x \in 'Z(A)).
Proof. move=> A x; exact: subcentP. Qed.

Lemma center_sub : forall A, 'Z(A) \subset A.
Proof. move=> A; exact: subsetIl. Qed.

Lemma center1 : 'Z(1) = [1 gT].
Proof. by apply/eqP; rewrite eqEsubset center_sub sub1G. Qed.

Lemma centerC : forall A, {in A, centralised 'Z(A)}.
Proof. by move=> A; apply/centsP; rewrite centsC subsetIr. Qed.

Lemma center_normal : forall G, 'Z(G) <| G.
Proof. by move=> G; rewrite -{2}(setIidPl (normG G)) subcent_normal. Qed.

Lemma morphim_center : forall rT A D (f : {morphism D >-> rT}),
  f @* 'Z(A) \subset 'Z(f @* A).
Proof. move=> rT A D f; exact: morphim_subcent. Qed.

Lemma abelian_center : forall G, abelian 'Z(G).
Proof.
by move=> P; rewrite /abelian subIset // centsC subIset // subxx orbT.
Qed.

Lemma center_char : forall G, 'Z(G) \char G.
Proof.
move=> G; apply/charP; split=> [|f injf Gf]; first exact: center_sub.
by apply/morphim_fixP; rewrite ?subsetIl //= -{4}Gf morphim_center.
Qed.

Lemma subcent1P : forall A x y,
  reflect (y \in A /\ commute x y) (y \in 'C_A[x]).
Proof.
move=> A x y; rewrite inE; case: (y \in A); last by right=> [[]].
by apply: (iffP cent1P) => [|[]].
Qed.

Lemma subcent1_id : forall x G, x \in G -> x \in 'C_G[x].
Proof. move=> x G Gx; rewrite inE Gx; exact/cent1P. Qed.

Lemma subcent1_sub : forall x G, 'C_G[x] \subset G.
Proof. move=> x G; exact: subsetIl. Qed.

Lemma subcent1C : forall x y G, x \in G -> y \in 'C_G[x] -> x \in 'C_G[y].
Proof. by move=> x y G Gx; case/subcent1P=> *; apply/subcent1P. Qed.

Lemma subcent1_cycle_sub : forall x G, x \in G -> <[x]> \subset 'C_G[x].
Proof. by move=> x G Gx; rewrite cycle_subG ?subcent1_id. Qed.

Lemma subcent1_cycle_norm : forall x G, 'C_G[x] \subset 'N(<[x]>).
Proof. by move=> x G; rewrite cents_norm // cent_gen cent_set1 subsetIr. Qed.

Lemma subcent1_cycle_normal : forall x G, x \in G -> <[x]> <| 'C_G[x].
Proof.
by move=> x G Gx; rewrite /normal subcent1_cycle_norm subcent1_cycle_sub.
Qed.

(* Gorenstein. 1.3.4 *)

Lemma center_cyclic_abelian : forall G, cyclic (G / 'Z(G)) -> G :=: 'Z(G).
Proof.
move=> G; case/cyclicP=> a Ga; apply/eqP; rewrite eqEsubset center_sub andbT.
case: (cosetP a) => /= z Nz def_a.
have G_Zz: G :=: 'Z(G) * <[z]>.
  rewrite -['Z(G)]ker_coset -morphimK ?cycle_subG ?morphim_cycle //=.
  by rewrite -def_a -Ga quotientGK // center_normal.
rewrite -(mulg1 'Z(G)) {1}G_Zz mulGS mulg1 /= G_Zz subsetI mulG_subr /=.
rewrite centM subsetI centsC subIset /=; first exact: cycle_abelian.
by rewrite orbC centS // G_Zz mulG_subr.
Qed.

(* Functoriality *)

Lemma center_resp : resp center.
Proof.
move=> hT iT H phi /=; apply: (subset_trans (morphimI _ _ _ )).
rewrite subsetI subsetIl /=; apply: subset_trans (subsetIr (phi @* H) _) _.
exact: morphim_cent.
Qed.

Lemma center_hereditary : hereditary center.
Proof.
move=> hT H G sHG; rewrite setIC /center setIA (setIidPl sHG) setIS //.
by rewrite (centsS sHG).
Qed.

End Center.

Canonical Structure bgFunc_center :=
  [bgFunc by fun _ _ => center_sub _ & center_resp].

Canonical Structure gFunc_center := GFunc center_resp.

Canonical Structure hgFunc_center := HGFunc center_hereditary.

Section Product.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.
Implicit Types A B C : {set gT}.

Lemma center_prod : forall H1 H2,
  H1 \subset 'C(H2) -> 'Z(H1) * 'Z(H2) = 'Z(H1 * H2).
Proof.
move=> H1 H2 CH1H2; apply/setP=> z; rewrite {3}/center centM !inE.
apply/imset2P/and3P=> [[z1 z2]| []].
  case/setIP=> Hz1 Cz1; case/setIP=> Hz2 Cz2 -> {z}.
  rewrite mem_imset2 ?groupM // ?(subsetP CH1H2) //.
  by apply: subsetP Hz2; rewrite centsC.
case/imset2P=> z1 z2 Hz1 Hz2 ->{z}.
rewrite groupMr => [Cz1|]; last by apply: subsetP Hz2; rewrite centsC.
rewrite groupMl => [Cz2|]; last exact: subsetP Hz1.
by exists z1 z2; rewrite ?inE ?Hz1 ?Hz2.
Qed.

Lemma center_cprod : forall A B G, A \* B = G -> 'Z(A) \* 'Z(B) = 'Z(G).
Proof.
move=> A B G; case/cprodP => [[H1 H2 -> ->] <- CH1H2].
rewrite cprodE ?center_prod //=.
apply: subset_trans (subset_trans (center_sub _)  CH1H2) (centS _).
exact: center_sub.
Qed.

Lemma center_bigcprod : forall I r P (F : I -> {set gT}) G,
  \big[cprod/1]_(i <- r | P i) F i = G
  -> \big[cprod/1]_(i <- r | P i) 'Z(F i) = 'Z(G).
Proof.
move=> I r P F; pose R A C := forall G, A :=: G -> C = 'Z(G).
apply (big_rel R) => [_ <-|A B C D IHA IHB G dG|_ _ G ->]; rewrite ?center1 //.
case/cprodP: dG IHA IHB (dG) => [[H K -> ->] _ _] IHH IHK dG.
by rewrite (IHH H) // (IHK K) // (center_cprod dG).
Qed.

Lemma center_dprod : forall A B G, A \x B = G -> 'Z(A) \x 'Z(B) = 'Z(G).
Proof.
move=> A B G; case/dprodP=> [[H1 H2 -> ->] defG cH12 trH12].
move: defG; rewrite -cprodE //; move/center_cprod.
case/cprodP=> _ /= <- cZ12; apply: dprodE => //=.
by rewrite setIAC setIA -setIA trH12 (setIidPl _) ?sub1G.
Qed.

Lemma center_bigdprod : forall I r P (F: I -> {set gT}) G,
  \big[dprod/1]_(i <- r | P i) F i = G
  -> \big[dprod/1]_(i <- r | P i) 'Z(F i) = 'Z(G).
Proof.
move=> I r P F; pose R A C := forall G, A :=: G -> C = 'Z(G).
apply (big_rel R) => [_ <-|A B C D IHA IHB G dG|_ _ G ->]; rewrite ?center1 //.
case/dprodP: dG IHA IHB (dG) => [[H K -> ->] _ _ _] IHH IHK dG.
by rewrite (IHH H) // (IHK K) // (center_dprod dG).
Qed.

End Product.



