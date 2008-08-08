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

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H K M : {group gT}.

Definition maximal A B := [max A | A \proper B].

Definition maximal_eq A B := (A == B) || maximal A B.

Definition Frattini A := \bigcap_(H : {group gT} | maximal_eq H A) H.

Canonical Structure Frattini_group A := Eval hnf in [group of Frattini A].

End Defs.

Notation "''Phi' ( A )" := (Frattini A)
  (at level 8, format "''Phi' ( A )") : group_scope.
Notation "''Phi' ( G )" := (Frattini_group G) : subgroup_scope.

Section Props.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H K M : {group gT}.

Lemma maximalP : forall M G,
  reflect (M \proper G /\ (forall H, H \proper G -> M \subset H -> H = M))
          (maximal M G).
Proof. move=> M G; exact: maxgroupP. Qed.

Lemma maximal_eqP : forall M G,
  reflect (M \subset G  /\
             forall H, M \subset H -> H \subset G -> H = M \/ H = G)
       (maximal_eq M G).
Proof.
move=> M G; rewrite subEproper /maximal_eq; case: eqP => [->|_]; first left.
  by split=> // H sGH sHG; right; apply/eqP; rewrite -val_eqE eqset_sub sHG.
apply: (iffP (maxgroupP _ _)) => [] [sMG maxM]; split=> // H.
  by move/maxM=> maxMH; rewrite subEproper val_eqE; case/predU1P; auto.
by rewrite properEneq val_eqE; case/andP; move/eqP=> neHG sHG; case/maxM.
Qed.

Lemma maximal_existence : forall H G, H \subset G ->
  H = G \/ exists2 M : {group gT}, maximal M G & H \subset M.
Proof.
move=> H G; rewrite subEproper val_eqE; case/predU1P=> sHG; first by left.
suff [M *]: {M : {group gT} | maximal M G & H \subset M} by right; exists M.
exact: maxgroup_exists.
Qed.

Lemma Phi_subset : forall G, 'Phi(G) \subset G.
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
rewrite defH; case: (maxM (restrm sGD f @*^-1 fH)%G) => [||->|->].
- by rewrite -sub_morphim_pre //= morphim_restrm (setIidPr _).
- by rewrite subsetIl.
- by left; apply: val_inj; rewrite /= morphim_restrm (setIidPr _).
by right; apply: val_inj; rewrite /= morphim_restrm setIid.
Qed.

End Morphisms.
  

