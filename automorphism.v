(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import bigops.
Require Import ssralg.
Require Import paths.
Require Import connect.
Require Import div.
Require Import groups.
Require Import group_perm.
Require Import finset.
Require Import normal.
Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Morphic.

Variables (G G' : finGroupType) (H : {set G}) (g : G -> G').

Definition morphic :=
  forallb x, forallb y, (x \in H) && (y \in H) ==> (g (x * y) == g x * g y).

(* morphic is the morphM property of morphisms seen through morphP *)

Lemma morphP : reflect {in H &, {morph g : x y / x * y}} morphic.
Proof.
apply: (iffP forallP) => [gmorph x y Hx Hy | gmorph x].
  by have:= forallP (gmorph x) y; rewrite Hx Hy /=; move/eqP.
by apply/forallP=> y; apply/implyP; case/andP=> Hx Hy; rewrite gmorph.
Qed.

End Morphic.

Implicit Arguments morphP [G G' H g].
Prenex Implicits morphic morphP.

Lemma morphic_subgroup : forall (G G': finGroupType) (H1 H2: group G),
  H1 \subset H2 ->
  forall (g:G -> G'), morphic H2 g -> morphic H1 g.
Proof.
move=> G G' H1 H2; move/subsetP=> Hsub g; move/morphP => Hmorph.
by apply/morphP=> x y H1x H1y; apply (Hmorph _ _ (Hsub _ H1x) (Hsub _ H1y)).
Qed.

Section MorphicRestriction.

Variable G : finGroupType.
Variable G': finGroupType.

Variables (f : G -> G') (H : {set G}).

Definition mrestr := [fun x => if x \in H then f x else 1].

Lemma trivm_mrestr : (trivm mrestr) = (trivm_(H) f) || (H == set0).
Proof.
apply/existsP/norP => [[x /=] | []].
  case Hx: (x \in H) => [] => [nfx1|]; last by rewrite eqxx.
  split; first by apply/existsP; exists x; rewrite Hx.
  by apply/eqP=> H0; rewrite H0 inE in Hx.
case/existsP=> x; rewrite negb_imply; case/andP=> Hx nfx1 _.
by exists x; rewrite /= Hx.
Qed.

Definition morphicrestr := if ~~ morphic H f then (fun _ => 1) else mrestr.

End MorphicRestriction.

Prenex Implicits mrestr morphicrestr.

Section MorphicRestrictionProps.

Variables G G': finGroupType.
Variable (f : G -> G').
Variable (H : {group G}).

Lemma group_trivm_mrestr : trivm (mrestr f H) = trivm_(H) f.
Proof.
rewrite trivm_mrestr orbC; case: eqP => // H0.
by have:= group1 H; rewrite H0 inE.
Qed.

Hypothesis Hmorph: morphic H f.

Lemma dom_mrestr : ~~ trivm_(H) f -> dom (mrestr f H) = H.
Proof.
move=> Htriv; apply/setP=> x; apply/idP/idP.
  case/setUP; last by rewrite inE /=; case: (x \in H); rewrite ?eqxx.
  move: Htriv; rewrite -group_trivm_mrestr; case/existsP=> y nfHy1.
  have:= nfHy1 => /=; case: ifP => [Hy nfy1|_]; last by rewrite eqxx.
  rewrite -(groupMr x Hy); move/kerP; move/(_ y); rewrite /= Hy.
  by case: ifP => // _ fy1; case/eqP: nfy1.
rewrite /mrestr !inE => Hx /=; rewrite Hx orbC.
case: eqP => //= fx1; apply/forallP=> y; rewrite groupMl //.
by case Hy : (y \in H); rewrite // (morphP Hmorph) // fx1 mul1g.
Qed.

Lemma group_set_dom_mrestr : group_set (dom (mrestr f H)).
Proof.
case e: (trivm_(H) f); last by rewrite (dom_mrestr (negbT e)) groupP.
move: (group_trivm_mrestr); rewrite e; move/trivm_dom=>->; exact: groupP.
Qed.

Lemma mrestrM : {in dom (mrestr f H) &, {morph mrestr f H: x y / x * y}}.
Proof.
move: (group_trivm_mrestr); case e: (trivm_(H) f).
  move/trivm_is_cst=>Htriv=> x y _ _; by rewrite !Htriv mulg1.
move/negbT: e=>Htriv _; rewrite (dom_mrestr Htriv)=> x y Hx Hy.
by rewrite /= Hx Hy groupM //; move/morphP: Hmorph =>->.
Qed.

Definition mrestr_morphism := Morphism group_set_dom_mrestr mrestrM.

Lemma ker_mrestr : ~~ trivm_(H) f ->
  ker (mrestr f H) = ker_(H) f :|: (H :\: dom f).
Proof.
move=> Htriv; apply/setP=> x; rewrite /dom [ker]lock !inE -lock.
case Hx: (x \in H); rewrite !(andbT, andbF) /=; last first.
  by rewrite -dom_mrestr // inE in Hx; case/norP: Hx; move/negPf.
have Dx: x \in dom mrestr_morphism by rewrite dom_mrestr.
rewrite (sameP (kerMP Dx) eqP) /= Hx negb_or negbK.
case Kx: (x \in ker f) => //=; have:= kerP _ _ Kx x.
by rewrite (morphP Hmorph) //; move/(canRL (mulgK _))->; rewrite mulgV eqxx.
Qed.

Lemma dfequal_morphicrestr : {in H, f =1 morphicrestr f H}.
Proof. by move=> x Hx; rewrite /morphicrestr Hmorph /= Hx. Qed.

End MorphicRestrictionProps.


Section MorphicRestrictionMorphism.

Variable G: finGroupType.
Variable G': finGroupType.
Variables (f : G -> G') (H : {group G}).

Lemma group_set_dom_morphicrestr : group_set (dom (morphicrestr f H)).
Proof.
rewrite /morphicrestr; case e: (morphic H f); first exact: group_set_dom_mrestr.
rewrite dom_triv_morph; exact: group_setT.
Qed.

Lemma morphicrestrM :
  {in dom (morphicrestr f H) &, {morph morphicrestr f H: x y / x * y}}.
Proof.
rewrite /morphicrestr; case e: (morphic H f) => x y /=; first exact: mrestrM.
by rewrite mulg1.
Qed.

Canonical Structure morph_morphicrestr :=
  Morphism group_set_dom_morphicrestr morphicrestrM.

End MorphicRestrictionMorphism.

Section MorphicProps.

Variables G G' : finGroupType.
Variables (f : G -> G') (H : {group G}).

Hypothesis Hmorph : morphic H f.

Lemma morphic1 : f 1 = 1.
Proof.
move/dfequal_morphicrestr: Hmorph => ->; [exact: morph1 | exact:group1].
Qed.

Lemma morphicmker : forall x, x \in ker f -> f x = 1.
Proof. by move=> x; move/kerP=> Kx; rewrite -[x]mulg1 Kx morphic1. Qed.

Lemma kermorphicP :  forall x,
  x \in dom_(H) f -> reflect (f x = 1) (x \in ker f).
Proof.
move=> x; case/setIP=> Dx _; apply: introP; first exact: morphicmker.
by move/negPf=> nKx; apply/eqP; rewrite inE nKx inE in Dx.
Qed.

Lemma injmorphicP : reflect {in H &, injective f} (injm f H).
Proof.
move/dfequal_morphicrestr: Hmorph => Heq; apply: (iffP idP).
  case e: (trivm_(H) f).
    move/(conj (idP e)); move/andP; move/trivm_injm_r.
    by move/trivgP=>-> x y /=; rewrite !inE /=; repeat move/eqP=><-.
  move=> Hinj; suff: (injm (morphicrestr f H) H).
    by move/injmP=> Hdinj x y Hx Hy; rewrite !Heq //; exact: Hdinj.
  move/negbT:e=>Htriv; move: (dom_mrestr Hmorph Htriv).
  rewrite /injm /morphicrestr Hmorph /= =>->.
  rewrite (ker_mrestr Hmorph Htriv) setDUr setDIr setDDr setDv setU0 set0U.
  rewrite setDE setIA (setIC H) -(setIA (~: ker f)) setIid setIC setIA -setDE.
  rewrite /injm in Hinj; rewrite subsetI Hinj andTb.
  by apply/subsetP=>x; rewrite inE; move/andP=> [_ Hx].
move=>Hinj; apply/subsetP=> x; rewrite inE; case/andP=> Hx1 Ax.
case Hfx1: (f x != 1).
  have Dx: x \in dom f by exact: dom_nu.
  rewrite inE Dx andbT.
  apply/kermorphicP; by [rewrite inE Ax Dx andbT | apply/eqP].
case/eqP: Hx1; move/eqP: Hfx1; rewrite -morphic1; exact: Hinj.
Qed.

Lemma injm_morphicrestr : injm f H -> injm (morphicrestr f H) H.
Proof.
move=> Hinj; apply/injmP; move=> y z Hy Hz /=.
rewrite -!(dfequal_morphicrestr Hmorph) //; move/injmorphicP: Hinj.
by apply.
Qed.

End MorphicProps.

Notation Aut := (fun (H : {set _}) f => perm_on H f && morphic H f).

Section Automorphism.

(* a group automorphism is a permutation on a subset of a finGroupType,*)
(* that respects the morphism law                                      *)

Variable G : finGroupType.

Variable H : {group G}.

Lemma group_autom : group_set (set_of (Aut H)).
Proof.
rewrite /group_set !inE /=; rewrite -andbA; apply/and3P; split.
- by apply/subsetP=> x; case/negP; rewrite permE.
- by apply/morphP => x Hx y Hy; rewrite !permE.
apply/subsetP=> f; case/mulsgP=> g h; rewrite !inE; case/andP=> pg mg.
case/andP=>ph mh ->; rewrite perm_onM //=; apply/morphP=> x y Hx Hy.
rewrite !permM; move/morphP: mg => -> //.
by move/morphP: mh => ->; rewrite // perm_closed.
Qed.

Canonical Structure automorphism_group := Group (group_autom).

Section AutomorphicInverse.

Lemma automorphic_inv : forall f, (Aut H f) -> (Aut H (perm_inv f)).
Proof.
move=> f; move/andP=> [Hperm Hmorph]; apply/andP.
have Hperminv : (perm_on H (perm_inv f)).
  apply/subsetP=> x Hx; move/subsetP: Hperm; apply.
  apply/idPn; rewrite -{2}(f_finv (@perm_inj _ f) x);apply/negP=>Heq.
  move/eqP: Heq; move/perm_inj; move/eqP; rewrite eq_sym; move/negbET: Hx.
  by rewrite /perm_inv permE=>->.
split; first by trivial.
apply/morphP=> x y Hx Hy; rewrite !permE; apply:(@perm_inj _ f).
rewrite -(@perm_closed _ _ _ _ Hperminv) permE in Hx.
rewrite -(@perm_closed _ _ _ _ Hperminv) permE in Hy.
move/morphP: Hmorph; move/(_ _ _ Hx Hy)=>->; move: (@perm_inj _ f)=> Hinj.
by rewrite !f_finv.
Qed.

End AutomorphicInverse.

End Automorphism.

Notation "[ 'Aut' G ]" := (automorphism_group G)
  (at level 0, G at level 9, format "[ 'Aut'  G ]") : subgroup_scope.

Section Morph_of_Aut.

Variable G : finGroupType.

Definition morph_of_aut f H :=
  if ~~ Aut H f then (fun _ => 1 : G) else morphicrestr f H.

Variable f : perm G.

Lemma morph_autrestr_eq : forall (H:set G), Aut H f ->
  morph_of_aut f H = morphicrestr f H.
Proof. by move=>H; rewrite /morph_of_aut /=; move/andP=>[->] ->. Qed.

Variable H : group G.

Lemma trivm_aut: Aut H f -> ~~ trivm_(H) f || trivg H.
Proof.
move/andP=>[Hperm Hmorph].
have: {in H &, injective f} by move=> x y Hx Hy; apply: perm_inj.
move/(injmorphicP Hmorph); case e:(trivm_(H) f); last by rewrite orTb.
by move/(conj (idP e)); move/andP; move/trivm_injm_r=>->; rewrite orFb.
Qed.

Lemma morphic_morph_of_aut : morphic H (morph_of_aut f H).
Proof.
apply/morphP=> x y Hx Hy; rewrite /morph_of_aut.
case: andP => [[_ fM] | _] /=; last by rewrite mulg1.
by rewrite /morphicrestr fM /= Hx Hy groupM // (morphP fM).
Qed.

Lemma morph_of_NAut : ~~(Aut H f) -> trivm (morph_of_aut f H).
Proof. by move => HNaut; apply/pred0P; rewrite /morph_of_aut HNaut eqxx. Qed.

Section DomainMorphOfAut.

Hypothesis Haut : (Aut H f).

Lemma morph_of_aut_ondom : forall x, x \in H -> morph_of_aut f H x = f x.
Proof.
rewrite /morph_of_aut => x /=; move: Haut => ->.
by rewrite /= /morphicrestr; move/andP:Haut =>[_]=>-> /= ->.
Qed.


Lemma dom_morph_of_aut : ~~(trivm_(H) f) -> dom (morph_of_aut f H) = H.
Proof.
rewrite /morph_of_aut Haut; move/(dom_mrestr _); rewrite /morphicrestr.
by move/andP:Haut=>[_]-> /=; move/(_ is_true_true)=>Hdom; rewrite -{2}Hdom /=.
Qed.

End DomainMorphOfAut.

Lemma morphM_morph_of_aut :  morphic (dom (morph_of_aut f H)) (morph_of_aut f H).
Proof.
move: morphic_morph_of_aut; rewrite /morph_of_aut.
case e: (Aut H f) => /=; last first.
  by rewrite dom_triv_morph => _ /=; apply/morphP; move; rewrite /= mul1g.
move: {+}e (@dom_mrestr _ _ f H); rewrite /morphicrestr; move/andP=>[_]->.
case ee:(trivm_(H) f) => /= => [_ _ | -> //].
by apply/morphP; apply: mrestrM; case/andP: e.
Qed.

Lemma group_set_morph_of_aut : group_set (dom (morph_of_aut f H)).
Proof.
rewrite /morph_of_aut; case e: (Aut H f) => /=; first exact: group_set_dom.
(* why doesn't apply:group_set_dom. work ?*)
exact: group_set_triv_morph.
Qed.

Lemma morph_of_aut_M :
  {in dom (morph_of_aut f H) &, {morph morph_of_aut f H: x y / x * y}}.
Proof. apply/morphP; exact: (morphM_morph_of_aut). Qed.

Canonical Structure morph_ofaut := 
  Morphism group_set_morph_of_aut morph_of_aut_M.

Lemma morph_of_aut_injm : (Aut H f) -> injm (morph_of_aut f H) H.
Proof.
move=> Haut; rewrite /morph_of_aut Haut; apply/injmP=>/=.
move=> x y Hx Hy; move:(@dfequal_morphicrestr _ _ f H); move/andP:Haut=>[_]->.
by move/(_ is_true_true)=>Heq; rewrite -(Heq _ Hx) -(Heq _ Hy); apply: perm_inj.
Qed.

Lemma isom_morph_of_aut : (Aut H f) -> isom (morph_of_aut f H) H H.
Proof.
move=> /= Haut; have Iaut := morph_of_aut_injm Haut.
rewrite /isom Iaut andbT; apply/eqP; apply/setP.
apply/subset_cardP; first by rewrite card_dimset; last exact/injmP.
apply/subsetP=> x; move/imsetP=> [x0 Hx0] ->{x} /=.
rewrite /morph_of_aut Haut /=; case/andP: Haut => Hf fM.
by rewrite -dfequal_morphicrestr // (perm_closed _ Hf).
Qed.

Lemma autom_imset : (Aut H f) -> f @: H = H.
Proof.
move=> Haut; move/andP: (isom_morph_of_aut Haut)=> [Heq _]; move/eqP: Heq=>Heq.
rewrite -{2}Heq; apply:dfequal_imset=> x Hx; rewrite /morph_of_aut /= Haut /=.
by move/andP:Haut=>[_ Hmorph]; rewrite (dfequal_morphicrestr Hmorph).
Qed.

End Morph_of_Aut.

Section Restriction.

Variables (T : finType) (f : T -> T) (H : {set T}).

Definition restr x := if x \in H then f x else x.

Hypothesis Hs : (f @: H) \subset H.

Lemma in_inj_inj_restr :  {in H &, injective f} -> injective restr.
Proof.
move=> Hdinj x x'; rewrite /restr.
case e:(x \in H); case e':(x'\in H)=> // eq; first exact: Hdinj.
  move/negbT: e'; case/negP;  move/subsetP: Hs; move/(_ x'); apply.
  apply/imsetP; by exists x.
move/negbT: e; case/negP; move/subsetP: Hs; move/(_ x); apply.
apply/imsetP; by exists x'.
Qed.

End Restriction.

Section PermExtension.

Variable d : finType.

Variable H : {set d}.

Section PermRestriction.

Variable f : {perm d}.

Hypothesis Hs : f @: H \subset H.

Lemma closed2perm : injective (restr f H).
Proof. apply (in_inj_inj_restr Hs)=> x y Hx Hy; exact: perm_inj. Qed.

Definition restriction := perm_of closed2perm.

Lemma perm_restriction : perm_on H restriction.
Proof.
apply/subsetP=>x Hrtr; case e:(x\in H)=> //; move/negP: Hrtr.
by rewrite permE /restr e eq_refl.
Qed.

Lemma dfequal_restriction : {in H , f =1 restriction}.
Proof. by move=> x /= Hx; rewrite /restriction permE /restr Hx. Qed.

End PermRestriction.

Section Perm_of_Restriction.

Variable f : d -> d.
Hypothesis Hs : f @: H \subset H.
Hypothesis Hdinj : {in H &, injective f}.

Definition perm_of_restriction := perm_of (in_inj_inj_restr Hs Hdinj).

End Perm_of_Restriction.

End PermExtension.

Section AutoMorphicRestriction.

Variables (G : finGroupType) (f : perm G) (H : group G).
Hypothesis Hs : f @: H \subset H.
Hypothesis Hm : morphic H f.

Lemma morph_restriction : morphic H (restriction Hs).
Proof.
apply/morphP=> x y Hx Hy; rewrite !permE /restr Hx Hy (groupM Hx Hy).
by move/morphP: Hm=>Hp; apply:Hp.
Qed.

Lemma autom_restriction : Aut H (restriction Hs).
Proof. by rewrite /= morph_restriction perm_restriction. Qed.

End AutoMorphicRestriction.

Section ConjugationMorphism.

Variable G : finGroupType.

Definition conjgm (g : G) := (perm_of (can_inj (conjgK g))).

Variable H : group G.

Lemma conjg_closed : forall g, g \in H -> (conjgm g @: H) \subset H.
Proof.
move=> g Hg; apply/subsetP=> x; move/imsetP=>[y Hy ->].
by rewrite permE groupJ.
Qed.

Lemma conjg_morphic : forall g, morphic H (conjgm g).
Proof. by move=> g; apply/morphP=> x y Hx Hy; rewrite !permE conjMg. Qed.

Definition conjgm_autP : forall g (P : g \in H),
 (Aut H (restriction (conjg_closed P))) :=
 (fun g P => autom_restriction (conjg_closed P) (conjg_morphic g)).

End ConjugationMorphism.

Section Characteristicity.

Variable G : finGroupType.

Definition characteristic (H K : {set G}) := 
  (K \subset H) && (forallb f : perm G, (Aut H f) ==> (f @: K == K)).

Variable H : group G.

Lemma normal_char : forall K, characteristic H K -> K <| H.
Proof.
move=> K; case/andP=> sKH chKH; rewrite /(K <| H) sKH; apply/normalP=> x Hx.
have:= forallP chKH (restriction (conjg_closed Hx)); rewrite conjgm_autP /=.
move/eqP=> eqKxK; rewrite -{2}eqKxK; apply: dfequal_imset=> y Hy.
by rewrite -dfequal_restriction (permE, subsetP sKH).
Qed.

Lemma subset_charP : forall K : {group G}, 
  reflect (K \subset H /\ forall f, Aut H f -> f @: K \subset K) 
          (characteristic H K).
Proof.
move=> K; apply: (iffP idP).
  move/andP=> [Hsub Himage];split; first by trivial.
  move/forallP: Himage => Hchar f Haut; move/implyP: (Hchar f); move/(_ Haut).
  by move/eqP=>->; apply:subset_refl.
move=> [Hsub Hchar]; apply/andP; split; first by trivial.
apply/forallP => f; apply/implyP=> Haut; apply/eqP; apply/setP.
apply/subset_eqP; rewrite (Hchar f Haut) andTb; move/andP: (Haut)=> [_ Hmorph].
move: (Hchar _ (automorphic_inv Haut)); move/(imsetS f).
rewrite -imset_comp=> Hsub1; apply: (subset_trans _ Hsub1).
apply/subsetP=> x Hx; apply/imsetP.
by exists x; rewrite // /comp /= permE f_finv; last apply:perm_inj.
Qed.

Lemma trivg_char : characteristic H 1.
Proof.
apply/subset_charP; split; first by rewrite sub1G.
move=> f; move/andP=> [_ Hmorph] /=; rewrite imset_set1 sub1set.
by apply/set1P; rewrite (morphic1 Hmorph).
Qed.

Lemma setT_group_char : characteristic H H.
Proof.
apply/subset_charP; split; first by apply subset_refl.
move=> f; move/autom_imset=>->; exact: subset_refl.
Qed.

Lemma lone_subgroup_char : forall (K : {group G}) m, 
  K \subset H ->
  (#|K| = m) ->
  (forall J : {group G}, J \subset H -> #|J| = m -> J = K) ->
  characteristic H K.
Proof.
move=> K m Hsub Hcard Huniq; apply/subset_charP; split; first by trivial.
move=> f Haut; move/andP: (Haut)=> [_ Hmorph].
suff: (f @: K = K) by move/setP; move/subset_eqP; move/andP=>[H1 _].
rewrite (dfequal_imset (subin1 (subsetP Hsub) (dfequal_morphicrestr Hmorph))).
rewrite -{2} (Huniq [group of morphicrestr f H @: K]) //=.
  move/andP: (isom_morph_of_aut Haut)=> [Heq _]; move/eqP: Heq.
  by rewrite /morph_of_aut /= Haut /= =>H1; rewrite -{2}H1; apply:imsetS.
rewrite card_dimset // => x y  Hx Hy.
by rewrite -!(dfequal_morphicrestr Hmorph) /= ?(subsetP Hsub) //; apply:perm_inj.
Qed.

End Characteristicity.

Prenex Implicits characteristic.

Section CharacteristicityProps.

Variable G : finGroupType.

Lemma char_trans : forall (H I K : {group G}),
  characteristic H I ->
  characteristic I K ->
  characteristic H K.
Proof.
move=> H I K HcharI HcharK; apply/subset_charP; split.
  move/andP: HcharI=> [HsubI _]; move/andP: HcharK=> [HsubK _].
  by apply: (subset_trans HsubK).
move=> f Haut; move/andP: (Haut)=>[_ Hmorph].
move/subset_charP: HcharI =>[HsubI]; move/(_ _ Haut)=> HimageI.
move/subset_charP: HcharK => [HsubK].
move/(_ _ (autom_restriction HimageI (morphic_subgroup HsubI Hmorph))).
by rewrite -(dfequal_imset
     (subin1 (subsetP HsubK) (dfequal_restriction HimageI))).
Qed.

Lemma char_norm_trans : forall (H I K : {group G}),
  characteristic K H ->
  K <| I ->
  H <| I.
Proof.
move=> H I K; case/andP=> sHK charH; case/normalsubP=> sKI nKI.
apply/normalsubP; split=> [|x Ix]; first exact: subset_trans sHK sKI.
have:= nKI _ Ix; move/eqP; rewrite eqset_sub andbC; case/andP=> _.
have <-: conjgm x @: K = K :^ x.
  by apply: dfequal_imset=> y Ky; rewrite -((permE (can_inj (conjgK x))) y).
move=> nK; have:= forallP charH (restriction nK).
rewrite autom_restriction ?conjg_morphic //=; move/eqP=> eqKxK.
rewrite -{2}eqKxK; apply:dfequal_imset=> y Ky /=.
by rewrite -dfequal_restriction (subsetP sHK, permE).
Qed.

End CharacteristicityProps.

Unset Implicit Arguments.
