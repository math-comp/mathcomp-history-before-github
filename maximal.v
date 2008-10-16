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

Canonical Structure Frattini_group : {group gT} :=
  Eval hnf in [group of Frattini].

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
  by apply: ex_maxgroup; exists (1%G : {group gT}); rewrite /proper sub1G.
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
Implicit Types G M : {group gT}.
Implicit Types H J : {group rT}.

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

Lemma maximal_morphpre : forall H J,
  H \subset f @* D -> maximal_eq J H -> maximal_eq (f @*^-1 J) (f @*^-1 H).
Proof.
move=> H J sfHD; case/maximal_eqP=> sJH maxJ; apply/maximal_eqP.
split=> [|fH sfJH sHfH]; first by rewrite morphpreS.
move: (subset_trans sfJH sHfH) => sJfH.
move: (morphpreS f sfHD); rewrite morphimGK // =>[sHD|]; 
last by move/subsetP:(@dom_ker _ _ _ f).
have HkerfH: ('ker (restrm_morphism sHD f) \subset fH).
  rewrite /ker morphpre_restrm; move: (morphpreI f H 1).
  rewrite (setIidPr (sub1G H)) =><-; apply: (subset_trans _ sfJH).
  by apply:morphpreS; apply:sub1G.
have defH: fH = (restrm sHD f @*^-1 (restrm sHD f @* fH))%G.
  by apply:val_inj; rewrite /= morphimGK. 
rewrite defH; case: (maxJ (restrm sHD f @* fH)%G); try apply:val_inj.
- rewrite -sub_morphpre_im ?morphpre_restrm ?(setIidPr _) //=.
  by rewrite morphim_restrm setIid morphpreK.
- rewrite /= morphim_restrm; move/setIidPr: (sHfH) =>->.
  by rewrite sub_morphim_pre; last by apply: (subset_trans _ sHD).
- by move/val_inj => ->; left; rewrite /= morphpre_restrm (setIidPr _).
- by move/val_inj => ->; right; rewrite /= morphpre_restrm setIid.
Qed.

End Morphisms.
  
Section Simple.

Variables gT : finGroupType.
Implicit Type G H : {group gT}.

Definition simple (A : {set gT}) := #|[set H : {group gT} | H <| A]| == 2.

Theorem simpleP : forall G,
  reflect (~~ trivg G /\ forall H, H <| G -> H :=: 1 \/ H :=: G) (simple G).
Proof.
move=> G; rewrite /simple (cardsD1 G) inE normal_refl eqSS (cardsD1 1%G).
rewrite 2!inE /(_ <| _) -val_eqE eqset_sub sub1G /= -/(trivg G).
rewrite -cent_set1 centsC sub1G andbT; case: trivGP => [-> | _].
  apply: (iffP idP) => [|[//]]; rewrite eqn_leq lt0n; case/andP=> _.
  rewrite eq_card0 // => H; rewrite !inE; apply/and4P=> [] [_ nH1 sH1 _].
  by case/eqP: nH1; move/trivGP: sH1.
rewrite eqSS; apply: (iffP eqP) => [simG | [_ simG]].
  split=> // H nHG; have:= card0_eq simG H; rewrite !inE nHG andbT -negb_or.
  by case/orP; rewrite -val_eqE; move/eqP; [left | right].
apply: eq_card0=> H; rewrite !inE andbA andbC; apply/andP=> [] [].
by rewrite -!(val_eqE H) /=; case/simG=> ->; rewrite eqxx ?andbF.
Qed.

End Simple.

Section IsoSimple.

Variables gT rT : finGroupType.
Implicit Type G : {group gT}.
Implicit Type M : {group rT}.

Lemma isog_simpl : forall G M, G \isog M -> simple G -> simple M.
Proof.
move=> G M; move/isog_symr; case/isogP=> f injf <-.
case/simpleP=> ntM simM; apply/simpleP; split=> [|L nLM].
  by apply: contra ntM; move/trivGP=> M1; rewrite {3}M1 /= morphim1.
case: (andP nLM); move/(morphim_invm injf); move/group_inj=> <- _.
have: f @* L <| f @* M by rewrite morphim_normal.
by case/simM=> /= ->; [left | right]; rewrite (morphim1, morphim_invm).
Qed.

End IsoSimple.


