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

Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import fintype div prime finset.
Require Import groups morphisms normal automorphism cyclic action.

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
move=> A B x; rewrite inE; case: (x \in A); last by right; case.
by apply: (iffP centP) => [|[]].
Qed.

Lemma centerP : forall A x,
  reflect (x \in A /\ centralises x A) (x \in 'Z(A)).
Proof. move=> A x; exact: subcentP. Qed.

Lemma subset_center : forall A, 'Z(A) \subset A.
Proof. move=> A; exact: subsetIl. Qed.

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

Lemma center_cyclic_abelian : forall a, H / 'Z(H) = <[a]> -> (H = 'Z(H))%G.
Proof.
move=> /= a Ha; apply/eqP; rewrite -val_eqE eqset_sub subset_center /= andbT.
case: (cosetP a) => /= z Nz def_a.
have H_Zz: H = 'Z(H) * <[z]> :> set _.
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
suffices{Z1}: #|'Z(G)| %%p = 0 by rewrite Z1 cards1 modn_small ?prime_gt1.
suff ->: 'Z(G) = 'C_G(G | 'J).
  rewrite -(mpl Hp HG); first by rewrite HG modn_mulr.
  apply/actsP=> x Gx y; exact: groupJr.
congr (_ :&: _); apply/setP=> x; apply/centP/afixP=> cxG y; move/cxG=> /=.
  by move/commgP; move/conjg_fixP.
by move/conjg_fixP; move/commgP.
Qed.

End PGroups.


