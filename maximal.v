(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import fintype.
Require Import ssralg.
Require Import bigops.
Require Import finset.
Require Import groups.
Require Import morphisms.
Require Import automorphism.
Require Import normal.
Require Import pgroups.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope group_scope with g.
Delimit Scope subgroup_scope with G.

Import GroupScope.

Section Defs.

Variables (gT : finGroupType) (A : {set gT}).

Definition Frattini := \bigcap_(H : {group gT} | maximal_eq H A) H.

Canonical Structure Frattini_group := Eval hnf in [group of Frattini].

End Defs.

Notation "''Phi' ( A )" := (Frattini A)
  (at level 8, format "''Phi' ( A )") : group_scope.
Notation "''Phi' ( G )" := (Frattini_group G) : subgroup_scope.

Section Props.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H K M : {group gT}.

Lemma Phi_sub : forall G, 'Phi(G) \subset G.
Proof. by move=> G; apply: bigcap_inf (G) _; apply/orP; left. Qed.

Lemma Phi_proper : forall G, ~~ trivg G -> 'Phi(G) \proper G.
Proof.
move=> G ntG; have{ntG} [M maxM]: {M : {group gT} | maximal M G}.
  by apply: ex_maxgroup; exists (1%G : group gT); rewrite /proper sub1G.
apply: sub_proper_trans (maxgroupp maxM).
by apply: bigcap_inf (M) _; apply/orP; right.
Qed.

Lemma Phi_not_gen : forall (G : {group gT}) (X : {set gT}),
  X \subset G -> (G \subset <<X>>) = (G  \subset << X :|: 'Phi(G) >>).
Proof.
move=> G X sXG; apply/idP/idP=> [|sGXF].
  by move/subset_trans; apply; rewrite genS ?subsetUl.
move: sXG; rewrite -gen_subG; case/maximal_existence=> [<- //=| [M maxM]].
rewrite gen_subG => sXM; case/andP: (maxgroupp maxM) => _; case/negP.
apply: (subset_trans sGXF); rewrite gen_subG subUset sXM.
by apply: bigcap_inf (M) _; apply/orP; right.
Qed.

End Props.

Section Morphisms.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types G H M : {group gT}.

Lemma maximal_morphim : forall G M,
  G \subset D -> maximal_eq M G -> maximal_eq (f @* M) (f @* G).
Proof.
move=> G M sGD; case/maximal_eqP=> sMG maxM; apply/maximal_eqP.
split=> [|fH sMH sHG]; first by rewrite morphimS.
have defH: fH = (restrm sGD f @* (restrm sGD f @*^-1 fH))%G.
  apply: group_inj; rewrite /= morphpreK // (subset_trans sHG) //.
  by rewrite morphim_restrm setIid /=.
rewrite defH; case: (maxM (restrm sGD f @*^-1 fH)%G) => /= [||->|->].
- by rewrite -sub_morphim_pre //= morphim_restrm (setIidPr _).
- by rewrite subsetIl.
- by left; rewrite morphim_restrm (setIidPr _).
by right; rewrite morphim_restrm setIid.
Qed.

End Morphisms.
  

