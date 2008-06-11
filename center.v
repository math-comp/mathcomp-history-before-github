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
Require Import fintype paths connect div finset bigops.
Require Import groups normal group_perm automorphism cyclic action.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Definition center (gT : finGroupType) (A : {set gT}) := C_(A)(A).

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

Lemma subcentgP : forall A B x, 
  reflect (x \in A /\ {for x, central B}) (x \in C_(A)(B)).
Proof.
move=> A B x; rewrite inE; case: (x \in A); last by right; case.
by apply: (iffP centgP) => [|[]].
Qed.

Lemma centerP : forall A x,
  reflect (x \in A /\ {for x, central A}) (x \in 'Z(A)).
Proof. move=> A x; exact: subcentgP. Qed.

Lemma subset_center : forall A, 'Z(A) \subset A.
Proof. move=> A; exact: subsetIl. Qed.

Lemma centerC : forall A, {in A, central 'Z(A)}.
Proof. by move=> A; apply: central_sym => x; case/centerP. Qed.

Lemma centerN : forall H, 'Z(H) <| H.
Proof.
move=> H; apply/normalsubP; split=> [|x Hx]; first exact: subset_center.
by rewrite conjIg conjGid // (normalP (norm_centg _)) // (subsetP (normG _)).
Qed.

Lemma characteristic_center : forall H, characteristic H 'Z(H).
Proof.
move=> H; apply/subset_charP; split; first exact: subset_center.
move=> f Haut /=; apply/subsetP=> x Hfx; apply/centerP.
move/andP: (isom_morph_of_aut Haut)=> [Hm _]; split.
  move/eqP: Hm =><-; rewrite /morph_of_aut /= Haut /=.
  move/andP: (Haut)=>[_ Hmorph].
  rewrite -(dfequal_imset (dfequal_morphicrestr Hmorph)).
  by move/subsetP: (imsetS f (subset_center H)); apply.
move=> y; rewrite -(eqP Hm)=> Hy; move/imsetP : Hfx=> [x0 Hx0 ->].
move/imsetP : Hy=> [y0 Hy0 ->]; rewrite /morph_of_aut /= Haut /=.
move/andP: (Haut)=>[_ Hmorph]; move/subsetP: (subset_center H)=>Hsub.
rewrite -(dfequal_morphicrestr Hmorph) //; move/morphP: (Hmorph)=> morphM.
by move/centerP: Hx0 => [Hx Hcen]; rewrite /commute -!morphM // Hcen.
Qed.

Section CyclicCenter.

Variable H : group gT.

(* G. 1.3.4 *)

Lemma center_cyclic_abelian : forall a, H / 'Z(H) = cyclic a -> (H = 'Z(H))%G.
Proof.
move=> /= a Ha; apply group_inj; apply/setP.
apply/subset_eqP; apply/andP; split; last exact:subset_center.
case trivco: (trivm (coset_of 'Z(H))).
  by move/trivm_coset_of: trivco=>/= nH; case/andP: (centerN H); rewrite nH.
have Hdec: forall x, x \in H ->
  exists2 z, z \in 'Z(H) & exists n, x = z * (repr a ^+ n).
- move=> x Hx; case/andP: (centerN H) => _; move/subsetP=> nZH.
  pose xbar := coset_of 'Z(H) x.
  have: x \in xbar by rewrite /xbar coset_ofN ?(rcoset_refl, nZH).
  have: xbar \in H / 'Z(H) by rewrite imset_f_imp.
  rewrite Ha; case/cyclicP=> n <-{xbar}.
  rewrite -{1}(coset_of_repr a) -morphX; last first.
    by rewrite (subsetP (subset_dom_coset _)) ?norm_repr_coset.
  rewrite coset_ofN ?groupX ?norm_repr_coset //.
  by case/rcosetP=> z; exists z; last exists n. 
apply/subsetP=> /= x Hx; rewrite inE Hx; apply/centgP=> y Hy.
move: (Hdec _ Hx) (Hdec _ Hy) => [xx Hcx [nx Hnx]] [yy Hcy [ny Hny]].
have [Hxx Hyy]: xx \in H /\ yy \in H.
  by split; exact: (subsetP (subset_center H)).
rewrite Hnx Hny; apply: commuteM; first by apply: centerC Hcy; rewrite -Hnx.
apply: commute_sym; apply: commuteM.
  by apply: centerC Hcx; rewrite -(groupMl _ Hyy) -Hny.
by apply: commuteX; apply: commute_sym; exact: commuteX.
Qed.

End CyclicCenter.

(*********************************************************************)
(*              Definition of the centraliser                        *)
(*    y is in the centraliser of x if y * x = x * y                  *)
(*********************************************************************)

Variable H : {group gT}.

Lemma centraliser_id : forall x, x \in H -> x \in C_(H)[x].
Proof. move=> x Hx; rewrite inE Hx; exact/centg1P. Qed.

Lemma centraliserP: forall x y,
  reflect (y \in H /\ commute x y) (y \in C_(H)[x]).
Proof.
by move=> x y; apply: (iffP (setIP _ _ _))=> [] [Hy];
  last move/commute_sym; move/centg1P.
Qed.

Lemma subset_centraliser : forall x, C_(H)[x] \subset H.
Proof. move=> x; exact: subsetIl. Qed.

Lemma centraliserC : forall x y,
  x \in H -> y \in C_(H)[x] -> x \in C_(H)[y].
Proof. by move=> x y Hx; case/centraliserP=> *; apply/centraliserP. Qed.

(* most certainly redundant *)
Lemma centraliserM : forall x y z,
  y \in C_(H)[x] -> z \in C_(H)[x] -> y * z \in C_(H)[x].
Proof. move=> *; exact: groupM. Qed.

Lemma centraliserV : forall x y,
  y \in C_(H)[x] -> y^-1 \in C_(H)[x].
Proof. by move=> *; rewrite groupV. Qed.

Lemma centraliserXr : forall x y n,
  y \in C_(H)[x] -> y ^+ n \in C_(H)[x].
Proof. move=> *; exact: groupX. Qed.

Lemma centraliserXl : forall x y n, x \in H ->
  y \in C_(H)[x] -> y \in C_(H)[x ^+ n].
Proof.
move => x y n Hx; case/centraliserP=> Hy cxy.
by apply: centraliserC=>//; apply: centraliserXr; apply/centraliserP.
Qed.

Section CyclicCentraliser.

Lemma normal_centraliser: forall x, x \in H -> C_(H)[x] \subset 'N(cyclic x).
Proof.
move=> x Hx; apply/normalP=> y.
case/centraliserP=> Hy cxy; apply/setP=>z.
by rewrite -cyclic_conjgs /conjg cxy mulgA; gsimpl.
Qed.

Lemma cyclic_subset_centraliser: forall x,
     x \in H -> cyclic x \subset C_(H)[x].
Proof.
move => x Hx; apply/subsetP=> y; case/cyclicP=> n <-{y}.
by rewrite centraliserXr // centraliser_id.
Qed.

Lemma centraliser_normaliser:
  forall x, x \in H -> C_(H)[x] \subset 'N(cyclic x).
Proof. exact: normal_centraliser. (* sic!!! -- GG *) Qed.

End CyclicCentraliser.

End Center.

Section CharacteristicCentralizer.

Variable G : finGroupType.

Lemma char_centralizer_ofchar : forall I H : {group G},
  characteristic I H -> characteristic I C_(I)(H).
Proof.
move=> I H; case/andP=> sHI; move/forallP=> chHI.
apply/subset_charP; split=> [|f Autf]; first exact: subsetIl.
apply/subsetP=> fz; case/imsetP=> z; case/setIP=> Iz; move/centgP=> cHz ->{fz}.
rewrite inE -{1}(autom_imset Autf) imset_f_imp //; apply/centgP=> fx.
have:= chHI f; rewrite Autf /=; move/eqP <-; case/imsetP=> x Hx ->{fx}.
case/andP: Autf => _; move/morphP=> fM; have Ix := subsetP sHI x Hx.
by rewrite /commute -!fM ?cHz.
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

Lemma pgroup_ntriv:~~ trivg 'Z(G).
Proof.
apply/negP => Ht.
have F1: #|'Z(G)| = 1%N.
  apply/eqP; rewrite eqn_leq -(trivg_card) Ht.
  by move: (subset_leq_card (sub1G 'Z(G))); rewrite cards1.
suff: #|'Z(G)| %%p = 0 by rewrite F1 modn_small // prime_gt1.
pose act := Action (@conjg1 gT) (@conjgM gT).
suff F2: [mem 'Z(G)] =1 (predI (act_fix act G) (mem G)).
  rewrite (eq_card F2) -(mpl  Hp HG); first by rewrite HG modn_mulr.
  by move=> x y; case/orbitP => z Hz <-; rewrite /= groupJr.
move=> x; apply/idP/andP => /=; rewrite !inE.
  case/andP => H1x H2x; split => //.
  rewrite /act_fix /= eqset_sub; apply/andP; split; apply/subsetP => y Hy.
    by case/stabilizerP: Hy.
  apply/stabilizerP; split => //; rewrite /act /=.
  move/centgP: H2x; move/(_ y Hy) => Hc.
  by rewrite /conjg Hc mulgA mulVg mul1g.
case; rewrite /act_fix; move/eqP => H1x H2x.
rewrite H2x; apply/centgP => y.
rewrite -H1x; case/stabilizerP => H1y H2y.
by rewrite /commute -{2}H2y /= conjgC.
Qed.

End PGroups.


