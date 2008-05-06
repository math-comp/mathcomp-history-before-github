(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of conjugate set, normal set and quotient group        *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.
Require Import finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section NormalProp.

Variables (gT : finGroupType) (H K : {group gT}).

Lemma normalsubS : forall L : {group gT},
  H <| K -> H \subset L -> L \subset K -> H <| L.
Proof.
move=> L; case/andP=> _ nHK sHL sLK.
by rewrite /(H <| _) sHL (subset_trans sLK).
Qed.

Lemma norm_normal : H <| 'N(H).
Proof. by rewrite /(H <| _) normG subset_refl. Qed.

Lemma norm_in_normal : H \subset K -> H <| N_(K)(H).
Proof.
by move=> sHK; rewrite /(H <| _) subsetI sHK normG subIset // subset_refl orbT.
Qed.

End NormalProp.


Section Simple.

Variables (gT : finGroupType) (H : {set gT}).

Definition simple := forallb K : {group gT}, (K <| H) ==> pred2 1 H K.

Theorem simpleP:
  reflect
   (forall K : {group gT}, K <| H -> K = 1 :> {set gT} \/ K = H :> {set gT})
   simple.
Proof.
(* have F1: forall z, pred1 1 z = set1 (1: gT) z by move => z; rewrite inE. *)
apply: (iffP forallP) => /= [Hf K Hk | Hf K].
  by have:= Hf K; rewrite Hk; case/orP => HH; [left|right]; exact/eqP.
by apply/implyP; case/Hf=> ->; rewrite eqxx ?orbT.
Qed.

End Simple.

(********************************************************************)
(*       Cosets are right cosets of elements in the normaliser      *)
(********************************************************************)

Section Cosets.

Variables (gT : finGroupType) (A : {set gT}).

(* We let cosets coerce to GroupSet.sort, so they inherit the   *)
(* group subset base group structure. Later we will define a    *)
(* proper group structure on cosets, which will then hide the   *)
(* inherited structure (once coset unifies with FinGroup.sort   *)
(* the coercion to GroupSet.sort will no longer be used). Note  *)
(* that for Hx Hy : coset H, Hx * Hy : {set gT} can be either   *)
(*           set_of_coset (mulg Hx Hy)                          *)
(*   or mulg (set_of_coset Hx) (set_of_coset Hy)                *)
(* However, since the two terms are actually convertible, we    *)
(* can live with this ambiguity.                                *)

Record coset : Type := Coset {
  set_of_coset :> GroupSet.sort gT;
  _ : set_of_coset \in rcosets A 'N(A)
}.

Canonical Structure coset_subType := SubType set_of_coset coset_rect vrefl.
Canonical Structure coset_eqType :=
  Eval hnf in [subEqType for set_of_coset : coset -> {set gT}].
Canonical Structure coset_finType := Eval hnf in [subFinType of coset_eqType].

End Cosets.

Prenex Implicits coset.

(********************************************************************)
(*  The domain of a morphism is inferred from the values of the     *)
(*  function. A morphism is constant 1 outside its domain           *)
(********************************************************************)

Section MorphismDefs.

Open Scope group_scope.

Variables (gT1 gT2 : finGroupType) (f : gT1 -> gT2).

(* Kernel *)
Definition ker := [set x : gT1 | forallb y, f (x * y) == f y].

(* Domain of the morphism *)
Definition dom := ker :|: [set x | f x != 1].

(* Preimage *)
Definition mpreim (B : {set gT2}) := (f @^-1: B) :&: dom.

(* Being a trivial morphism *)
Definition trivm := forallb z, f z == 1.

(* Quotient morphism *)
Definition mquo (A : {set gT1}) (Ax : coset A) : FinGroup.sort gT2 :=
  if A \subset ker then f (repr Ax) else 1.

(* Being a morphism injective on A*)
Definition injm (A : {set gT1}) := A :\ 1 \subset dom :\: ker.

(* Being an isomorphism between A and B *)
Definition isom (A : {set gT1}) (B : {set gT2}) :=
  (f @: A == B) && injm A.

(* The inverse morphism of an injective morphism *)
Definition invm  A y : FinGroup.sort gT1 :=
  if injm A then repr [set x \in A | f x == y] else 1.

Definition idm (x : gT1) : FinGroup.sort gT1 := x.

End MorphismDefs.

Implicit Arguments mquo [gT1 gT2].
Implicit Arguments idm [].

Prenex Implicits dom ker mpreim trivm mquo injm isom invm.

Notation "'ker_' ( G ) f" := (ker f :&: G)
  (at level 10, format "'ker_' ( G )  f") : group_scope.

Notation "'dom_' ( G ) f" := (dom f :&: G)
  (at level 10, format "'dom_' ( G )  f") : group_scope.

Notation "'preim_' ( G ) f B" := ((f @^-1: B) :&: G)
  (at level 10, format "'preim_' ( G )  f  B") : group_scope.

Notation "'trivm_' ( G ) f" := (forallb z, (z \in G) ==> (f z == 1))
  (at level 10, format "'trivm_' ( G )  f") : group_scope.

Section GenericProps.

Open Scope group_scope.

Variables (gT1 gT2 : finGroupType)(f : gT1 -> gT2).

Lemma kerP : forall x, reflect (forall y, f (x * y) = f y) (x \in ker f).
Proof.
by move=> x; rewrite inE; apply: (iffP forallP) => [] Kx y; move/eqP: (Kx y).
Qed.

(* The kernel of an arbitrary function is a group *)
Lemma group_set_ker : group_set (ker f).
Proof.
apply/andP; split; first by apply/kerP=> x; rewrite mul1g.
apply/subsetP=> x; case/mulsgP=> y z; move/kerP=> Hy; move/kerP=> Hz ->.
by apply/kerP=> t; rewrite -mulgA Hy Hz.
Qed.

Canonical Structure ker_group := Group group_set_ker.

Lemma dom_k : forall x, x \in ker f -> x \in dom f.
Proof. by move=> x kx; rewrite inE; apply/orP; left. Qed.

Lemma dom_nu : forall x, f x != 1 -> x \in dom f.
Proof. by move=> x kx; rewrite inE; apply/orP; right; rewrite inE. Qed.

Lemma out_dom : forall x, (x \in dom f) = false -> f x = 1.
Proof.
move=> x; rewrite inE; case/norP=> _; rewrite inE=> H1; apply/eqP.
exact (negbE2 H1).
Qed.

Lemma trivm_is_cst : trivm f -> f =1 (fun _ => 1).
Proof. by move/pred0P=> Hf x; move/eqP: (Hf x). Qed.

Lemma trivm_ker :  trivm f -> ker f = setT.
Proof.
move/trivm_is_cst=> Hf; apply/setP=> x; rewrite !inE; apply/forallP=> y.
by rewrite !Hf.
Qed.

Lemma trivm_dom : trivm f -> dom f = setT.
Proof.
by move/trivm_ker=> Hf; apply/setP=> u; rewrite inE Hf !inE.
Qed.

Lemma subset_mpreim : forall A B : {set gT2},
  A \subset B -> mpreim f A \subset mpreim f B.
Proof.
move=> A B  HAB; apply/subsetP=> x; rewrite 2!inE; case/andP=> Hfx Dfx.
by rewrite inE Dfx inE (subsetP HAB).
Qed.

Lemma mpreimP : forall (A : {set gT2}) x,
  reflect (f x \in A /\ x \in dom f) (x \in mpreim f A).
Proof. move=> A x; rewrite !inE; exact: andP. Qed.

Lemma subset_mpreim_dom : forall A : {set gT2},
  mpreim f A \subset dom f.
Proof. by move=> A; apply/subsetP=> x; case/mpreimP. Qed.

Lemma injm_dom : forall A : {set gT1}, injm f A -> A \subset dom f.
Proof.
move=> A; move/subsetP=> H1; apply/subsetP=> x Ax.
case Hx: (x \in A :\ 1); first by move/H1: Hx; rewrite inE; case/andP.
by move: Hx; rewrite inE Ax andbT; move/eqP->; rewrite dom_k ?group1.
Qed.

Lemma subset_ker_r : forall A : {set gT1}, ker_(A) f \subset ker f.
Proof. by move=> A; apply/subsetP=> u; case/setIP. Qed.

Lemma ker_r_dom : ker_(dom f) f = ker f.
Proof.
apply/setP; apply/subset_eqP; rewrite subset_ker_r /=; apply/subsetP=> x Kx.
by apply/setIP; rewrite Kx dom_k.
Qed.

Lemma subset_dom_r : forall A : {set gT1}, dom_(A) f \subset dom f.
Proof. by move=> A; apply/subsetP=> x; case/setIP. Qed.

Lemma trivm_dom_ker_r : forall A : {set gT1},
  trivm_(A) f -> dom_(A) f = ker_(A) f.
Proof.
move=> A; move/forallP=> ftriv; apply/setP=> x; rewrite !inE.
by case: (x \in A) (ftriv x) => [/= ->|_]; rewrite ?orbF ?andbF.
Qed.

Variable H : {group gT1}.

Lemma ker_injm : injm f H -> ker_(H) f = 1.
Proof.
rewrite /injm=> H1; apply/setP.
apply/subset_eqP; apply/andP; split; apply/subsetP=> x; last first.
  by rewrite inE; move/eqP->; rewrite group1.
case/setIP=> Kx; move/setD1K: (group1 H)=> <-; rewrite inE.
by case/orP; last move/(subsetP H1); rewrite inE // Kx. 
Qed.

Lemma injm_ker : H \subset dom f -> ker_(H) f = 1 -> injm f H.
Proof.
move=> Hsub Hker; rewrite /injm; apply/subsetP=> x Hx; rewrite inE in Hx.
move/andP: Hx=> [Hxn1 HxH]; rewrite setDE; apply/setIP; split; last first.
   rewrite inE; apply/negP=>HH; move: HxH; move/(conj HH); move/setIP.
   by rewrite Hker inE (negbET Hxn1).
by apply:(subsetP Hsub).
Qed.

Lemma ker_dinj : {in H &, injective f} -> ker_(H) f = 1.
Proof.
move=> injf; apply/eqP; rewrite eqset_sub sub1set group1 andbT.
apply/subsetP=> x; case/setIP; move/kerP=> Kx Hx; have:= Kx 1.
by rewrite mulg1 inE; move/injf->.
Qed.

Lemma trivm_injm_r : trivm_(H) f && injm f H -> trivg H.
Proof.
move/andP.
move=> [Htriv]; rewrite /injm setDUl setDv set0U => Hinj.
apply/subsetP=> x Hx; rewrite inE; apply/idPn => nx1.
case/pred0Pn: Htriv; exists x; rewrite Hx /=.
have: (x \in H :\ 1) by rewrite !inE Hx andbT.
by move/(subsetP Hinj); rewrite !inE; case/andP.
Qed.

End GenericProps.

Notation "[ 'ker' f ]" := (ker_group f)
  (at level 0, f at level 9, format "[ 'ker'  f ]") : subgroup_scope.
Notation "'ker_' ( G ) f" := ([ker f] :&: G)%G : subgroup_scope.

(* Definition of the morphism structure *)
Section Morphisms.

Variables (gT1 gT2 : finGroupType).

Structure morphism : Type := Morphism {
  mfun :> gT1 -> FinGroup.sort gT2;
  group_set_dom : group_set (dom mfun);
  morphM : {in dom mfun &, {morph mfun : x y / x * y}}
}.

Variable f : morphism.

Canonical Structure dom_group := Group (group_set_dom f).

Lemma morph1 : f 1 = 1.
Proof. by apply (mulg_injl (f 1)); rewrite -morphM ?group1 // !mulg1. Qed.

Lemma morphV : {in dom f, {morph f : x / x^-1 >-> x^-1}}.
Proof.
move=> x Dx; apply: (mulg_injl (f x)); rewrite mulgV -morphM ?groupV //.
by rewrite mulgV morph1.
Qed.

Lemma morphJ : {in dom f &, {morph f : x y / x ^ y}}.
Proof. by move=> *; rewrite /conjg !morphM ?morphV // ?groupM ?groupV. Qed.

Lemma morphX : forall n, {in dom f, {morph f : x / x ^+ n}}.
Proof.
move=> n.
elim: n => [x Dx| n Hrec x Dx]; first by rewrite !expg0 morph1.
by rewrite !expgS morphM ?groupX ?Hrec.
Qed.

Lemma mker : forall x, x \in ker f -> f x = 1.
Proof.
move=> x; rewrite inE; move/forallP; move/(_ 1); move/eqP.
by rewrite mulg1 morph1.
Qed.

(* The kernel of a morphism is the set of elements in the domain *)
(* that are mapped to the unit *)
Lemma kerMP : forall x, x \in dom f -> reflect (f x = 1) (x \in ker f).
Proof.
move=> x Dx; apply: (iffP idP); first exact: mker.
rewrite inE => Hx; apply/forallP => y.
case Dy: (y \in dom f); first by rewrite morphM // Hx mul1g.
by rewrite (out_dom Dy) (@out_dom _ _ f) // groupMl.
Qed.

Lemma ker_rcoset : forall x y, x \in dom f -> y \in dom f ->
  reflect (exists k, k \in ker f /\ x = k * y) (f x == f y).
Proof.
move=> x y dx dy; apply: (iffP eqP).
  move=> Exy; exists (x * y^-1); split; last by gsimpl.
  by apply/kerMP; rewrite ?morphM // ?Exy ?morphV ?mulgV ?groupM ?groupV.
by case=> k [Kk ->]; rewrite morphM ?(dom_k Kk) // mker // mul1g.
Qed.

Lemma imset_smul : forall A B : {set gT1},
  A \subset dom f -> B \subset dom f -> f @: (A * B) = (f @: A) * (f @: B).
Proof.
move=> A B DomA DomB; apply/setP=> y; apply/imsetP/mulsgP.
  case=> x; case/mulsgP=> a b Aa Bb -> ->.
  exists (f a) (f b); [apply/imsetP; exists a|apply/imsetP; exists b|]=>//.
  by rewrite morphM // ?((subsetP DomA) a) ?(subsetP DomB).
case=> u v; case/imsetP=> a Aa ->; case/imsetP=> b Bb -> ->.
exists (a * b); first by apply/mulsgP; exists a b.
by rewrite  morphM // ?((subsetP DomA) a) ?(subsetP DomB).
Qed.

Lemma imset_conj : forall (A : {set gT1}) x,
  A \subset dom f -> x \in dom f ->  f @: (A :^ x) = (f @: A) :^ (f x).
Proof.
move=> A x DomA Domx; rewrite !conjsgE -morphV //.
rewrite -!(imset_set1 f) -!imset_smul  // ?sub1set ?groupV //.
by rewrite -[dom f]mulGid mulgSS ?sub1set.
Qed.

Section MorphIm.

Variable H : {group gT1}.

Lemma im_group_dom : f @: H = f @: (H :&: dom f).
Proof.
apply/setP=> u.
apply/imsetP/imsetP; last by case=> x; case/setIP=> Hx Dx ->; exists x.
case=> x Hx ->; case domx : (x \in dom f); first by exists x=> //; apply/setIP.
exists (1 : gT1); first by apply/setIP; split; rewrite group1.
move/negbT: domx; rewrite !inE negb_or negbK morph1; case/andP=> _.
by move/eqP.
Qed.

Lemma group_set_imset : group_set (f @: H).
Proof.
rewrite im_group_dom /group_set; apply/andP; split.
  by apply/imsetP; exists (1:gT1); rewrite ?group1 // -morph1.
apply/subsetP=> t; case/mulsgP=> u v.
case/imsetP=> x; case/setIP=> Hx Dx ->.
case/imsetP=> y; case/setIP=> Hy Dy -> ->.
apply/imsetP; exists (x * y); last by rewrite morphM.
by apply/setIP; rewrite !groupM.
Qed.

Canonical Structure morph_imset_group := Group group_set_imset.

End MorphIm.

Section MorphPreIm.

Lemma mpreimUker : forall A : {set gT2},
  1 \in A -> mpreim f A = (f @^-1: (A :\ 1)) :|: (ker f).
Proof.
move=> A A1; apply/setP=> u; apply/setIP/setUP.
  rewrite inE => Hu; apply/orP; case ku : (u \in ker f); rewrite // ?orbT //.
  by rewrite orbF !inE; case: Hu => ->; rewrite andbT inE ku /= inE eq_sym.
case=> [|Ku]; first by  rewrite !inE; case/andP=> -> ->; rewrite orbT.
by rewrite dom_k // inE (kerMP _ Ku) ?A1 // dom_k.
Qed.

Variable H : {group gT2}.

Lemma mpreim_group_set : group_set (mpreim f H).
Proof.
rewrite /group_set; do 2 rewrite inE; rewrite morph1 !group1 /=.
apply/subsetP=> u; case/mulsgP=> x y; case/setIP; rewrite inE.
move=> Hx1 dx; case/setIP; rewrite inE=> Hy1 dy ->.
by apply/setIP; apply/andP; rewrite inE morphM ?groupM.
Qed.

Canonical Structure mpreim_group := Group mpreim_group_set.

End MorphPreIm.

Lemma morph_norml_im : forall K : {group gT1},
  K <| dom f -> (f @: K) <| (f @: dom f).
Proof.
move=> K; case/normalsubP=> sKD nKD; rewrite /(_ <| _) imsetS //=.
by apply/normalP=> fx; case/imsetP=> x Kx ->{fx}; rewrite -imset_conj ?nKD.
Qed.

Lemma normal_ker : ker f <| dom f.
Proof.
rewrite /(_ <| _) subsetUl; apply/normalP=> x Dx; apply/normgP; rewrite inE.
apply/subsetP=> yx; case/imsetP=> y Ky ->{yx}.
have Dy: y \in dom f by rewrite inE Ky.
by apply/kerMP; rewrite (morphJ, groupJ) // mker // conj1g.
Qed.

Lemma normal_ker_r : forall H : {group gT1},
  ker_(H) f <| dom_(H) f.
Proof.
move=> H; case/andP: normal_ker => sKD nKD; rewrite /(_ <| _) setSI //.
apply/subsetP=> x; case/setIP=> Dx Hx.
apply/normgP; rewrite conjIg (normgP (subsetP nKD _ Dx)).
by rewrite conjsgE rcoset_id // lcoset_id // groupV.
Qed.


(* Being isomorphic *)
Definition isog (A : {set gT1})(B : {set gT2}) :=
  exists g : morphism, isom g A B.

Lemma injmP : forall A: {group gT1}, reflect {in A &,injective f} (injm f A).
Proof.
move=> A; apply: (iffP idP) => [injf x y Ax Ay eq_fxy | injf].
  case xAy : (x * y ^-1 \in A :\ 1).
    move/(subsetP injf): xAy; rewrite inE andbC.
    case/andP=> Dxy; case/(kerMP Dxy); apply: (mulg_injr (f y)).
    by rewrite mul1g -morphM ?mulgKV // (subsetP (injm_dom injf)).
  move: xAy; rewrite -{2}(mulgKV y x) inE groupM ?groupV // andbT.
  by move/eqP->; rewrite mul1g.
apply/subsetP=> x; rewrite inE; case/andP=> nx1 Ax.
case: (f x =P 1) => [fx1|].
  by case/eqP: nx1; apply: injf; rewrite // morph1.
move/eqP=> nfx1; have Dx: x \in dom f by exact: dom_nu.
rewrite inE Dx andbT; apply/(kerMP Dx); exact/eqP.
Qed.

Lemma gen_f_com : forall A : {set gT1},
  A \subset dom f -> f @: <<A>> = <<f @: A>>.
Proof.
move=> A sAD; apply/setP; apply/subset_eqP; apply/andP.
split; last by apply: bigcap_inf => /=; apply: imsetS; apply/bigcap_inP.
apply/bigcap_inP=> /= H; move/subsetP=> sfAH.
suff sAf'H: A \subset mpreim f H.
  rewrite -gen_subG /= in sAf'H; apply: subset_trans (imsetS f sAf'H) _.
  by apply/subsetP=> y; case/imsetP=> x; case/mpreimP=> Hfx _ ->.
by apply/subsetP=> x Ax; rewrite 2!inE sfAH (subsetP sAD, imset_f_imp).
Qed.

End Morphisms.

Prenex Implicits isog.

Notation "[ 'morphism' 'of' f ]" :=
  (match {f : _ -> _ as morphism _ _} as s
   return [type of @Morphism _ _ for s] -> _ with
   | Morphism _ domG fM => fun k => k domG fM
   end (@Morphism _ _ f)) (at level 0, only parsing) : form_scope.

Notation "[ 'dom' f ]" := (dom_group f)
  (at level 0, f at level 9, format "[ 'dom'  f ]") : subgroup_scope.
Notation "'dom_' ( G ) f" := ([dom f] :&: G)%G : subgroup_scope.
Notation "f @: G" := (morph_imset_group f G) : subgroup_scope.
Notation "f @^-1: G" := (mpreim_group f G) : subgroup_scope.

Section IdMorphism.

Variable gT : finGroupType.

Notation Local gT_id := (idm gT).

Lemma dom_id : dom gT_id = setT.
Proof.
apply/setP=> x; rewrite in_setT /= inE orbC inE.
by case: eqP=> // x1; apply/kerP=> y; rewrite [x]x1 mul1g.
Qed.

Lemma group_set_dom_id : group_set (dom gT_id).
Proof. by rewrite dom_id group_setT. Qed.

Lemma idmorphM : {in dom gT_id &, {morph gT_id : x y / x * y}}.
Proof. by []. Qed.

Canonical Structure morph_id := Morphism group_set_dom_id idmorphM.

End IdMorphism.

Section TrivMorphism.

Variables (gT1 gT2 : finGroupType).

Notation Local triv := (fun _ : gT1 => (1 : gT2)).

Lemma dom_triv_morph : dom triv = setT.
Proof. by apply/setP=> x; rewrite in_setT dom_k //; apply/kerP. Qed.

Lemma group_set_triv_morph : group_set (dom triv).
Proof. by rewrite dom_triv_morph group_setT. Qed.

Lemma trivmorphM : {in dom triv &, {morph triv : x y / x * y}}.
Proof. by move=> x y _ _ /=; rewrite mulg1. Qed.

Canonical Structure triv_morph := Morphism group_set_triv_morph trivmorphM.

Lemma iim_trivm : forall (A : {set gT1}) x, x \in A -> triv @: A = 1.
Proof.
move=> A x Ax; apply/setP=> y; rewrite inE.
by apply/idP/eqP=> [|<-]; [case/imsetP | apply/imsetP; exists x].
Qed.

Lemma trivial_isog : forall (A : {group gT1}) (B : {group gT2}),
  trivg A -> trivg B -> isog A B.
Proof.
move=> A B; move/trivgP=> ->; move/trivgP=> ->.
exists triv_morph; apply/andP; split.
  by rewrite (@iim_trivm _ 1) ?inE //.
by apply/injmP=> x y; rewrite !inE /=; move/eqP=> ->; move/eqP.
Qed.

End TrivMorphism.

(* Canonical Structure of morphism for the composition of 2 morphs *)
(* Composing morphisms can lead to trivial morphisms, in that case,*)
(* the equations for ker and dom do not hold anymore,              *)
(* but only one inclusion.                                         *)

Section MorphismComposition.

Variables (gT1 gT2 gT3 : finGroupType).

Variable f : morphism gT1 gT2.
Variable g : morphism gT2 gT3.

Notation Local gof := (mfun g \o mfun f).

Lemma morph_nuc : forall (h : gT1 -> gT2) x, (g \o h) x != 1 -> h x != 1.
Proof.
by move=> h x Hx; apply/eqP=> Hhx; rewrite /= Hhx morph1 eq_refl in Hx.
Qed.

Lemma trivm_cn : forall h : gT1 -> gT2,
  ~~ trivm (g \o h) -> (~~ trivm g) /\ (~~ trivm h).
Proof.
move=> h; case/pred0Pn=> x Hx; split; apply/pred0Pn; first by exists (h x).
by exists x; apply morph_nuc.
Qed.

Lemma subset_ker_c : mpreim f (ker g) \subset ker gof.
Proof.
apply/subsetP=> x; case/mpreimP; move/kerP=> Hx Dfx; apply/kerP=> y /=.
case Dfy: (y \in dom f); first by rewrite morphM.
by congr (g _); rewrite out_dom ?groupMl // out_dom.
Qed.

Lemma ker_c : ~~ trivm gof -> ker gof = (mpreim f (ker g)).
Proof.
case/pred0Pn=> x Hnt; apply/setP; apply/subset_eqP.
rewrite subset_ker_c andbT; apply/subsetP=> y; move/kerP=> /= Hy.
have Hyx : gof (y * x) != 1 by rewrite /= Hy.
have Dfx : x \in dom f by rewrite dom_nu // morph_nuc.
have Dfy : y \in dom f by rewrite -(groupMr _ Dfx) dom_nu // morph_nuc.
rewrite inE Dfy andbT inE; apply/kerMP.
  by rewrite -(@groupMr _ _ (f x)) -?morphM // dom_nu.
by rewrite -(mulg1 y) Hy !morph1.
Qed.

Lemma subset_dom_c : mpreim f (dom g) \subset dom gof.
Proof.
apply/subsetP=> x; case/mpreimP; case/setUP; last first.
  by rewrite inE=> ? _; exact: dom_nu.
move=> Kx Dx; apply: dom_k; apply: (subsetP subset_ker_c); exact/mpreimP.
Qed.

Lemma dom_c : ~~ trivm gof -> dom gof = (mpreim f (dom g)).
Proof.
move=> Hnt; apply/setP; apply/subset_eqP; rewrite subset_dom_c andbT.
apply/subsetP=> x; case/setUP.
  rewrite ker_c //; apply: (subsetP (subset_mpreim _ _)).
  apply/subsetP; exact: dom_k.
by rewrite 3!inE => Hx; rewrite !dom_nu // morph_nuc.
Qed.

Lemma group_set_dom_c : group_set (dom gof).
Proof.
case Hnt: (trivm gof); last by rewrite dom_c ?Hnt ?groupP.
rewrite trivm_dom //; apply/group_setP; split=> [|? ? *]; exact: in_setT.
Qed.

Lemma morphMc : {in dom gof &, {morph gof: x y / x * y}}.
Proof.
case Ht: (trivm gof) => [] x y; last move/negbT: Ht => Hnt.
  by rewrite !(trivm_is_cst Ht) mulg1.
rewrite !(dom_c Hnt); case/mpreimP=> [Hgx Hx]; case/mpreimP=> [Hgy Hy].
by rewrite /= !morphM.
Qed.

Canonical Structure comp_morph := Morphism group_set_dom_c morphMc.

Lemma ker_c_loc : forall G : {group gT1},
    G \subset dom f -> f @: G \subset dom g ->
  ker_(G) gof = mpreim f (ker_(f @: G) g) :&: G.
Proof.
move=> G sGd sfGd; apply/setP=> x.
rewrite -!(setIC G) 2![x \in _ :&: _]inE.
case Gx : (x \in G)=> //=; apply/idP/idP=> [Kx|].
  rewrite 2!inE (subsetP sGd) // andbT; apply/setIP.
  split; last by apply/imsetP; exists x.
  apply/kerMP; rewrite ?(subsetP sfGd) //; first by apply/imsetP; exists x.
  by apply: (kerMP _ Kx); rewrite dom_k.
rewrite inE; case/andP; rewrite inE; case/setIP=> Kx _ Dx.
by rewrite (subsetP subset_ker_c) // inE Dx andbT inE.
Qed.

End MorphismComposition.

(* We build a new (canonical) structure of groupType for cosets. *)
(* This group type is the largest possible quotient 'N(H) / H    *)

Section CosetGroupType.

Variable gT : finGroupType.
Implicit Types A : {set gT}.
Implicit Types H : {group gT}.

Lemma coset_set_unit : forall A, A \in rcosets A 'N(A).
Proof.
by move=> A; apply/rcosetsP; exists (1 : gT); rewrite (group1, mulg1).
Qed.

Definition coset_unit A := Coset (coset_set_unit A).

Variable H : {group gT}.

Lemma coset_set_mul : forall Hx Hy : coset H, Hx * Hy \in rcosets H 'N(H).
Proof.
case=> A /=; case/rcosetsP=> x Hx ->{A} [A] /=; case/rcosetsP=> y Hy ->{A}.
by apply/rcosetsP; exists (x * y); rewrite (groupM, rcoset_mul).
Qed.

Definition coset_mul Hx Hy := Coset (coset_set_mul Hx Hy).

Lemma coset_set_inv : forall Hx : coset H, Hx^-1 \in rcosets H 'N(H).
Proof.
case=> A /=; case/rcosetsP=> x Hx ->{A}; rewrite norm_rlcoset // invg_lcoset.
by apply/rcosetsP; exists x^-1; rewrite ?groupV.
Qed.

Definition coset_inv Hx := Coset (coset_set_inv Hx).

Lemma coset_mulP : forall Hx Hy Hz,
  coset_mul Hx (coset_mul Hy Hz) = coset_mul (coset_mul Hx Hy) Hz.
Proof. by move=> Hx Hy Hz; apply: val_inj; rewrite /= mulgA. Qed.

Lemma coset_unitP : forall Hx, coset_mul (coset_unit H) Hx = Hx.
Proof.
case=> A cosetT; apply: val_inj => /=; case/rcosetsP: cosetT => x Hx ->{A}.
by rewrite mulgA mulGid.
Qed.

Lemma coset_invP : forall Hx, coset_mul (coset_inv Hx) Hx = coset_unit H.
Proof.
case=> A cosetT; apply: val_inj => /=; case/rcosetsP: cosetT => x Hx ->{A}.
rewrite invg_rcoset -mulgA (mulgA H) mulGid norm_rlcoset //.
by rewrite -lcosetM mulVg mul1g.
Qed.

Canonical Structure coset_preGroupType :=
  [baseFinGroupType of coset H by coset_mulP, coset_unitP & coset_invP].
Canonical Structure coset_groupType := FinGroupType coset_invP.

End CosetGroupType.

Section Quotient.

Open Scope group_scope.

Variable gT : finGroupType.

(* Projection of the initial group type over the cosets groupType  *)
(* Again we need to separate the case of trivial projection for the*)
(* dom and ker equations                                           *)

Definition coset_of A x : @coset gT A := insubd (coset_unit A) (A :* x).

Variable H : {group gT}.

Lemma coset_set_rcoset : forall x,
  (H :* x \in rcosets H 'N(H)) = (x \in 'N(H)).
Proof. by move=> x; rewrite mem_rcosets mulSGid // normG. Qed.

Lemma set_of_coset_of : forall x,
  coset_of H x = (if x \in 'N(H) then H :* x else H) :> {set _}.
Proof.
by move=> x; rewrite -coset_set_rcoset val_insubd coset_set_rcoset.
Qed.

Lemma coset_ofN : forall x, x \in 'N(H) -> coset_of H x = H :* x :> set _.
Proof. by move=> x; rewrite set_of_coset_of => ->. Qed.

Lemma coset_of_id : forall x, x \in H -> coset_of H x = 1.
Proof.
move=> x Hx; apply: val_inj; rewrite /= coset_ofN ?rcoset_id //.
exact: (subsetP (normG H)).
Qed.

Lemma coset_of_idr : forall x, x \in 'N(H) -> coset_of H x = 1 -> x \in H.
Proof.
move => x Hx H1 /=.
rewrite -(rcoset1 H) rcoset_sym.
move: (coset_ofN Hx); rewrite H1 => <-.
by rewrite group1.
Qed.

Lemma coset_ofV : forall x, coset_of H x^-1 = (coset_of H x)^-1.
Proof.
move=> x; apply: val_inj.
rewrite /= !set_of_coset_of groupV.
case Nx: (x \in 'N(H)); last by rewrite invGid.
by rewrite -invg_lcoset norm_rlcoset.
Qed.

Lemma subset_ker_coset : H \subset ker (coset_of H).
Proof.
apply/subsetP=> x Hx; apply/kerP=> y; apply: val_inj.
have Nx := subsetP (normG _) _ Hx.
rewrite /= !set_of_coset_of groupMl // -rcoset_mul // rcoset_id //=.
by rewrite mulgA mulGid.
Qed.

Lemma nu_coset_of_norm : forall x, coset_of H x != 1 -> x \in 'N(H).
Proof.
move=> x; rewrite -(inj_eq val_inj) /= set_of_coset_of.
by case: ifP; rewrite // eq_refl.
Qed.

Lemma ker_coset : ~~ trivm (coset_of H) -> ker (coset_of H) = H.
Proof.
case/pred0Pn=> y Nty; have Hy := nu_coset_of_norm Nty.
apply/setP; apply/subset_eqP; rewrite subset_ker_coset andbT.
apply/subsetP=> x; move/kerP=> Kx; rewrite -Kx in Nty.
move/(_ 1): Kx; rewrite mulg1 (@coset_of_id 1) //.
move/(congr1 (@set_of_coset _ _)).
rewrite {2}/set_of_coset /= coset_ofN => [<- | ].
  by apply/rcosetP; exists (1 : gT); rewrite ?mul1g.
by rewrite -(mulgK y x) groupM ?groupV // nu_coset_of_norm.
Qed.

Lemma subset_dom_coset : 'N(H) \subset dom (coset_of H).
Proof.
apply/subsetP=> x Nx; apply/setUP; case Hx: (x \in H); [left | right].
  exact: (subsetP subset_ker_coset).
rewrite inE -(inj_eq val_inj) /= coset_ofN //.
apply/eqP=> dH; rewrite -dH in Hx.
by case/rcosetP: Hx; exists (1 : gT); rewrite ?mul1g.
Qed.

Lemma dom_coset : ~~ trivm (coset_of H) -> dom (coset_of H) = 'N(H).
Proof.
move=> Hnt; apply/setP; apply/subset_eqP; rewrite subset_dom_coset andbT.
rewrite /dom ker_coset //; apply/subsetP=> x; case/setUP.
  exact: (subsetP (normG _)).
by rewrite inE; exact: nu_coset_of_norm.
Qed.

Lemma group_set_dom_coset : group_set (dom (coset_of H)).
Proof.
case Hnt: (trivm (coset_of H)); first by rewrite trivm_dom // groupP.
by rewrite dom_coset ?Hnt ?groupP.
Qed.

Lemma coset_of_morphM :
  {in dom (coset_of H) &, {morph coset_of H : x y / x * y}}.
Proof.
case Hnt: (trivm (coset_of H)) => x y.
  by rewrite !(trivm_is_cst Hnt) mulg1.
rewrite dom_coset ?Hnt // => Nx Ny; apply: val_inj.
by rewrite /= !coset_ofN ?groupM // rcoset_mul.
Qed.

Canonical Structure coset_of_morphism :=
  Morphism group_set_dom_coset coset_of_morphM.

(* Why the duplication ?? - GG *)
Lemma coset_ofX : forall n,
  {in dom (coset_of H), {morph coset_of H : x / x ^+ n}}.
Proof. exact: morphX. Qed.

Lemma trivm_coset_of :
  reflect (normaliser H = H) (trivm (coset_of H)).
Proof.
apply: (iffP idP); last first.
  move=> NH; apply/pred0P=> x; apply/eqP; apply: val_inj => /=.
  rewrite set_of_coset_of.
  by case Nx: (x \in _)=> //; rewrite rcoset_id //= -1?NH.
move=> Htriv; apply/setP; apply/subset_eqP; rewrite normG andbT.
apply/subsetP=> x Nx; suff: H :* x = H by move=> <-; rewrite rcoset_refl.
by rewrite -coset_ofN // trivm_is_cst.
Qed.

Lemma ker_coset_of_loc : forall K : group gT,
  K \subset 'N(H)-> ker_(K) (coset_of H) = H :&: K.
Proof.
move=> K nHK.
case Htriv : (trivm (coset_of H)); last by rewrite ker_coset ?Htriv.
apply/setP=> x; rewrite trivm_ker // !inE /= andbC.
by case Kx : (x \in K); rewrite //= -(trivm_coset_of Htriv) (subsetP nHK).
Qed.

Lemma ker_coset_of_sub : forall K : group gT,
  H <| K -> ker_(K) (coset_of H) = H.
Proof.
move=> K; case/andP=> sHK; move/ker_coset_of_loc->.
by apply/eqP; rewrite eqsetIl.
Qed.

Definition quotient (A B : {set gT}) := (coset_of B) @: A.

Notation "A / B" := (quotient A B).

Variable K : {group gT}.

Canonical Structure quotient_group := Eval hnf in [group of K / H].

Lemma quotientP : forall xbar,
  reflect (exists x, [/\ x \in K, x \in 'N(H) & xbar = coset_of H x])
          (xbar \in K / H).
Proof.
move=> xb; apply: (iffP imsetP) => [[x Kx ->{xb}] | [x [*]]]; last by exists x.
case Nx: (x \in 'N(H)); first by exists x.
exists (1 : gT); rewrite !group1 morph1; split=> //.
by apply: val_inj; rewrite /= set_of_coset_of Nx.
Qed.

Lemma set_of_coset_quotient : val @: (K / H) = rcosets H N_(K)(H).
Proof.
apply/setP=> A; apply/imsetP/rcosetsP=> [[xbar Kxbar]|[x NKx]] ->{A}.
  case/quotientP: Kxbar => x [Kx Nx ->{xbar}].
  by exists x; [rewrite inE Kx | rewrite /= coset_ofN].
case/setIP: NKx => Nx Kx.
by exists (coset_of H x); [apply/imsetP; exists x | rewrite /= coset_ofN].
Qed.

Lemma card_quotient : K \subset 'N(H) -> #|K / H| = indexg H K.
Proof.
move=> sHK; rewrite -(card_imset _ val_inj).
rewrite set_of_coset_quotient; congr #|_ @: (_ : set _)|.
by apply/eqP; rewrite eqsetIl.
Qed.

End Quotient.

Notation "A / B" := (quotient A B) : group_scope.
Notation "G / H" := (quotient_group H G) : subgroup_scope.

Prenex Implicits coset_of quotient.

Section TrivialQuotient.

Open Scope group_scope.

Variables (gT : finGroupType) (H : {group gT}).

Lemma trivial_quotient : H / H = 1.
Proof.
apply/setP=> A; apply/quotientP/set1P => [[x [Hx _ ->]] | ->].
  by rewrite coset_of_id.
by exists (1 : gT); rewrite coset_of_id !group1.
Qed.

End TrivialQuotient.

(* Canonical structure of morphism for the quotient morphism *)

Section QuotientMorphism.

Variables gT gT' : finGroupType.

Variable f : morphism gT gT'.
Variable H : group gT.

Notation Local fq := (mquo f H).
Let domN := subsetP (subset_dom_coset H).

Lemma norm_repr_coset : forall xbar : coset H, repr xbar \in 'N(H).
Proof.
case=> A /=; case/rcosetsP=> x Nx ->{A}; case: repr_rcosetP=> z Hz.
by rewrite groupMr // (subsetP (normG _)).
Qed.

Lemma coset_of_repr : forall xbar : coset H, coset_of H (repr xbar) = xbar.
Proof.
move=> xbar; apply: val_inj.
rewrite /= set_of_coset_of norm_repr_coset.
case: xbar => A /=; case/rcosetsP=> x Nx ->{A}; exact: rcoset_repr.
Qed.

Lemma cosetP : forall xbar, {x | x \in 'N(H) & xbar = coset_of H x}.
Proof.
by move=> xbar; exists (repr xbar); rewrite ?coset_of_repr ?norm_repr_coset.
Qed.

Lemma factor_mquo_norm : H \subset ker f ->
  forall x, x \in 'N(H) -> fq (coset_of H x) = f x.
Proof.
move=> sHK x Nx; rewrite /mquo sHK coset_ofN //; case: repr_rcosetP=> y Hy.
apply: kerP; exact: (subsetP sHK).
Qed.

Lemma factor_mquo : H \subset ker f ->  H <| dom f ->
  forall x, fq (coset_of H x) = f x.
Proof.
move=> sHK; case/andP=> _ nHD x.
case Nx: (x \in 'N(H)); first exact: factor_mquo_norm.
rewrite /mquo sHK set_of_coset_of Nx -(rcoset1 H); case: repr_rcosetP => y Hy.
rewrite (@out_dom _ _ f x); last by apply/negP; move/(subsetP nHD); rewrite Nx.
rewrite -(morph1 f); apply: kerP; exact: (subsetP sHK).
Qed.

Lemma factor_mquo_iim : H \subset ker f ->
  forall A : {group gT}, A \subset 'N(H) -> fq @: (A / H) = f @: A.
Proof.
move=> sHK A; move/subsetP=> nHA.
apply/setP=> y; apply/imsetP/imsetP=> [[B]|[x Hx ->{y}]].
  by case/imsetP=> x Ax ->{B} ->{y}; exists x; rewrite ?factor_mquo_norm ?nHA.
by exists (coset_of H x); rewrite (imset_f_imp, factor_mquo_norm) ?nHA.
Qed.

Lemma mquo_nt_subker : ~~ trivm fq ->  H \subset ker f.
Proof. by case/existsP=> x; rewrite /mquo; case: subset => //; case/eqP. Qed.

Lemma ker_mquo_nt : ~~ trivm fq -> ker fq = ker f / H.
Proof.
move=> Hnt; have fqc := factor_mquo_norm (mquo_nt_subker Hnt).
apply/setP=> xbar; apply/kerP/quotientP => [Kxbar | [x [Kx Nx ->{xbar}]] ybar].
  case: (cosetP xbar) => x Nx -> {xbar} in Kxbar *; exists x; split=> //=.
  case/pred0Pn: Hnt => zbar.
  case: (cosetP zbar) {Kxbar}(Kxbar zbar) => z Nz -> {zbar}.
  rewrite -morphM ?domN ?fqc ?groupMl // => fxz fz1.
  have Dz: z \in dom f by exact: dom_nu.
  have Dx: x \in dom f by rewrite -(mulgK z x) groupMr ?groupV // dom_nu ?fxz.
  by apply/(kerMP Dx); apply: (mulg_injr (f z)); rewrite mul1g -morphM.
case: (cosetP ybar) => y Ny ->{ybar}.
by rewrite -morphM ?domN // !fqc ?groupMl //; exact: kerP.
Qed.

Lemma subset_ker_mquo : ker f / H \subset ker fq.
Proof.
apply/subsetP=> Abar KAbar.
case Hnt: (trivm fq); first by rewrite trivm_ker ?in_setT.
by rewrite ker_mquo_nt ?Hnt.
Qed.

Lemma mquo_triv : H \subset ker f -> H <| dom f -> trivm fq -> trivm f.
Proof.
move=> sHk sdN fqTriv; apply/pred0P=> x.
by rewrite -factor_mquo // trivm_is_cst ?eq_refl.
Qed.

Lemma ker_mquo : H \subset ker f -> H <| dom f -> ker fq = ker f / H.
Proof.
case Htr: (trivm fq) => [] sHK nHD; last by rewrite ker_mquo_nt ?Htr.
apply/setP=> xbar; rewrite trivm_ker // in_setT; symmetry; apply/imsetP.
case: (cosetP xbar) => x _ ->{xbar}; exists x => //=.
rewrite trivm_ker ?in_setT {x}//; apply/pred0P=> x.
by rewrite -factor_mquo ?(pred0P Htr).
Qed.


Lemma dom_mquo_nt : ~~ trivm fq -> dom fq = dom f / H.
Proof.
move=> Hnt; apply/setP=> xbar; rewrite 2!inE ker_mquo_nt //.
have fqc := factor_mquo_norm (mquo_nt_subker Hnt).
apply/orP/imsetP=> [|[x Dx ->{xbar}]].
  case.
    by case/quotientP=> x /= [Kx Nx ->{xbar}]; exists x; rewrite // inE Kx.
  case: (cosetP xbar) => x Nx ->{xbar}; rewrite fqc //.
  by exists x => //; exact: dom_nu.
case Nx: (x \in 'N(H)).
  by case/setUP: Dx; [left; apply/imsetP; exists x | rewrite inE fqc //; right].
left; apply/imsetP; exists (1 : gT); rewrite ?group1 //; apply: val_inj.
by rewrite /= set_of_coset_of Nx coset_of_id.
Qed.

Lemma subset_dom_mquo : dom f / H \subset dom fq.
Proof.
apply/subsetP=> Abar DAbar.
case Hnt: (trivm fq); first by rewrite trivm_dom ?in_setT.
by rewrite dom_mquo_nt ?Hnt.
Qed.

Lemma dom_mquo : H \subset ker f -> H <| dom f -> dom fq = dom f / H.
Proof.
case Htr: (trivm fq) => [] sHK nHD; last by rewrite dom_mquo_nt ?Htr.
apply/setP=> xbar; case: (cosetP xbar) => x _ -> {xbar}.
rewrite trivm_dom // in_setT; symmetry; apply/imsetP; exists x => //.
rewrite trivm_dom ?in_setT {x}//; apply/pred0P=> x.
by rewrite -factor_mquo ?(pred0P Htr) //.
Qed.

Lemma group_set_dom_mquo : group_set (dom fq).
Proof.
case Hnt: (trivm fq); last by rewrite dom_mquo_nt ?Hnt // groupP.
by rewrite trivm_dom ?groupP.
Qed.

Lemma mquoM : {in dom fq &, {morph fq: x y / x * y}}.
Proof.
move=> xbar ybar; case Hnt: (trivm fq); first by rewrite !(trivm_is_cst Hnt) mulg1.
have fqc := factor_mquo_norm (mquo_nt_subker (negbT Hnt)).
rewrite !dom_mquo_nt ?Hnt //.
case/quotientP=> x [Nx Dx ->{xbar}]; case/quotientP=> y [Ny Dy ->{ybar}].
by rewrite -morphM ?domN // !fqc ?groupMl // morphM.
Qed.

Canonical Structure mquo_morphism := Morphism group_set_dom_mquo mquoM.

Lemma ker_mquo_loc : H \subset ker f ->
  forall G : {group gT},
   G \subset dom f -> ker_(G / H) (mquo f H) = ker_(G) f / H.
Proof.
move=> sHK G sGd; apply/setP=> Hx; apply/setIP/quotientP.
  case=> KHx; case/quotientP=> x [Gx Nx E1]; exists x; split => //=.
  rewrite inE Gx andbT; apply/kerMP; first exact:(subsetP sGd).
  by rewrite -factor_mquo_norm // ?dom_k ?(subsetP subset_ker_mquo) // -E1 mker.
case=> x []; case/setIP=> Kx Gx Nx ->; split; last by apply/quotientP; exists x.
by rewrite (subsetP subset_ker_mquo) //; apply/imsetP; exists x.
Qed.

End QuotientMorphism.

Section InverseMorphism.

Variables (gT1 gT2 : finGroupType) (H : {group gT1}).
Variable f : morphism gT1 gT2.

Notation Local invfH := (invm f H).

Lemma invm_nu : forall y, let x := invm f H y in
   x != 1 -> [/\ injm f H, x \in H & f x = y].
Proof.
move=> y; rewrite /invm /repr; move/eqP; case: ifP => // injf.
by case: pickP => //= x; rewrite inE; case/andP=> Hx; move/eqP.
Qed.

Lemma invIm : injm f H -> {in H, cancel f invfH}.
Proof.
move=> injf x Hx; rewrite /invm injf; set A := set_of _.
have: repr A \in A by rewrite (mem_repr x) // inE Hx /=.
rewrite inE; case/andP=> HrA; move/eqP; exact: (injmP _ _ injf).
Qed.

Lemma invmI : injm f H -> {in f @: H, cancel invfH f}.
Proof. by move=> injf fx; case/imsetP=> x Hx ->; rewrite invIm. Qed.
 
Lemma triv_invm : trivm invfH = (injm f H ==> trivg H).
Proof.
apply/forallP/implyP=> [invf1 finj | inj_trH y].
  by apply/subsetP=> x Hx; rewrite inE -(invIm finj Hx) invf1.
set x := _ y; apply/idPn=> nx1; case: (invm_nu nx1); rewrite -/x => finj.
by move/trivgP: (inj_trH finj) ->; rewrite inE /= (negPf nx1).
Qed.

Lemma kert_invm : injm f H -> ~~ trivg H -> ker invfH  = 1.
Proof.
move=> injf ntrH; have [x [nx1 Hx]]: exists x, x != 1 /\ x \in H.
  rewrite trivg_card (cardsD1 1) group1 ltnS leqn0 in ntrH.
  by case/existsP: ntrH => x H'x; exists x; apply/andP; rewrite -in_setD1.
apply/setP=> y; apply/kerP/set1P=> [|-> z]; last by rewrite mul1g.
move/(_ (f x)); rewrite invIm {Hx}// => def_x; rewrite -def_x in nx1.
by case/invm_nu: nx1 => _ _;  move/(canLR (mulgK _))=> <-; rewrite def_x mulgV.
Qed.

Lemma dom_invm : injm f H -> ~~ trivg H -> dom invfH  = f @: H.
Proof.
move=> injf ntrH; rewrite /dom kert_invm // -setU1E.
apply/setP=> y; apply/setU1P/imsetP=> [[->|]|[x Hx ->{y}]].
- by exists (1 : gT1); rewrite ?morph1.
- by rewrite inE; case/invm_nu; exists (invm f H y).
rewrite inE invIm //; case: (x =P 1) => [->|]; first by left; rewrite morph1.
by move/eqP; right.
Qed.

Lemma ker_invm : injm f H -> ker_(f @: H) invfH = 1.
Proof.
case trH: (trivg H) => injf; apply/eqP. 
  suff: trivg (f @: H) by case/trivgP=> ->; rewrite eqsetIr sub1G.
  move: trH; rewrite !trivg_card; apply: leq_trans; exact: leq_imset_card.
by rewrite kert_invm ?trH // eqsetIl sub1G.
Qed.

Lemma invm_group : group_set (dom invfH).
Proof.
case triv_inv: (trivm invfH); first by rewrite trivm_dom ?groupP.
move/idPn: triv_inv; rewrite triv_invm negb_imply; case/andP=> injf ntrH.
by rewrite dom_invm ?groupP.
Qed.

Lemma invmM : {in dom invfH &, {morph invfH : x y / x * y}}.
Proof.
case triv_inv: (trivm invfH).
  by move=> x y _ _ /=; rewrite !(trivm_is_cst triv_inv) mulg1.
move/idPn: triv_inv; rewrite triv_invm negb_imply; case/andP=> injf ntrH.
rewrite dom_invm // => fx fy.
case/imsetP=> x Hx ->{fx}; case/imsetP=> y Hy ->{fy}.
by rewrite -morphM ?(subsetP (injm_dom injf)) // !invIm // groupM.
Qed.

Canonical Structure invm_morph := Morphism invm_group invmM.

Lemma invm_inj : injm f H -> injm invfH (f @: H).
Proof. move=> injf; apply/injmP; exact: (in_can_inj (invmI injf)). Qed.

Lemma imset_invm : injm f H ->
  forall A : {set gT1}, A \subset H -> invfH @: (f @: A) = A.
Proof.
move=> injf A; move/subsetP=> sAH; apply/setP=> x; apply/imsetP/idP=> [[y]|Ax].
  by case/imsetP=> x' Ax' -> ->; rewrite invIm // sAH.
by exists (f x); rewrite (imset_f_imp, invIm) // sAH.
Qed.  

Lemma invm_isom : injm f H -> isom invfH (f @: H) H.
Proof. by move=> injf; rewrite /isom invm_inj // andbT  imset_invm. Qed.

End InverseMorphism.

Section Isomorphisms.

Variables gT1 gT2 gT3 : finGroupType.
Variables (H : {group gT1}) (G : {group gT2}) (K : {group gT3}).

Lemma isog_refl : isog H H.
Proof.
exists [morphism of idm gT1]; apply/andP; split=> /=; last by apply/injmP=> ?.
by apply/eqP; apply/setP=> y; apply/imsetP/idP => [[x Hx ->//]| Hy]; exists y.
Qed.

Lemma isog_card : isog H G -> #|H| = #|G|.
Proof.
case=> f; case/andP; move/eqP=> <- injf.
symmetry; apply: card_dimset; exact/injmP.
Qed.

Lemma isog_triv : isog H G -> trivg H = trivg G.
Proof. by move=> isoHG; rewrite !trivg_card isog_card. Qed.

Lemma isog_sym : isog H G -> isog G H.
Proof.
case=> f; case/andP; move/eqP=> <- injf.
exists [morphism of invm f H] => /=; exact: invm_isom.
Qed.

Lemma isog_trans : isog H G -> isog G K -> isog H K.
Proof.
case=> f; case/andP; move/eqP=> <- injf [g]; case/andP; move/eqP=> <- injg.
exists [morphism of g \o f]; rewrite -imset_comp /isom eqxx /=.
apply/injmP=> x y Hx Hy /= eq_gfxy; move/injmP: injf; apply=> //.
by move/injmP: injg; apply; rewrite ?imset_f_imp.
Qed.

Lemma isog_simpl : isog H G -> simple H -> simple G.
Proof.
case/isog_sym=> f; case/andP; move/eqP=> <- injf.
move/simpleP=> simpH; apply/simpleP=> L.
case/andP=> sLG; move/normalP=> nLG; rewrite -(imset_invm injf sLG).
have dG: G \subset dom f by exact: injm_dom.
have{nLG sLG dG}: f @: L <| f @: G.
  rewrite /(_ <| _) imsetS //.
  apply/normalP=> fx; case/imsetP=> x Gx ->{fx}.  
  by rewrite -imset_conj ?nLG // (subset_trans _ dG, subsetP dG).
case/simpH=> {simpH} /= ->; last by right; rewrite imset_invm.
by left; rewrite imset_set1 morph1.
Qed.

End Isomorphisms.

Section FirstIsomorphism.

Variables (gT1 gT2 : finGroupType) (f : morphism gT1 gT2) (H : {group gT1}).

Hypothesis sHD : H \subset dom f.

Lemma first_isom : isog (H / ker_(H) f) (f @: H).
Proof.
exists [morphism of mquo f (ker_(H) f)]; apply/andP=> /=; split.
  rewrite factor_mquo_iim ?subsetIl //=.
  have defH: dom_(H) f = H by apply/eqP; rewrite eqsetIr.
  by rewrite -{1}defH; case/andP: (normal_ker_r f H).
apply/injmP=> xbar ybar; case/quotientP=> [x [Hx Nx ->]] {xbar}.
case/quotientP=> [y [Hy Ny ->]] {ybar} /=.
rewrite !factor_mquo_norm //= ?(subset_ker_r f) // => eq_fxy.
apply: val_inj; rewrite /= !set_of_coset_of Nx Ny; apply: rcoset_trans1 => /=.
rewrite mem_rcoset inE (groupMl _ Hx) groupV Hy andbT.
apply/kerMP; first by rewrite groupMl ?groupV (subsetP sHD).
by rewrite morphM ?(morphV, groupV, subsetP sHD) // eq_fxy mulgV.
Qed.

End FirstIsomorphism.

Section SecondIsomorphism.

Variables (gT : finGroupType) (H K : {group gT}).

Hypothesis nKH : H \subset 'N(K).

Lemma second_isom : isog (H / (K :&: H)) (H / K).
Proof.
rewrite -[K :&: H]/(set_of_group _) -(group_inj (ker_coset_of_loc nKH)) /=.
by apply: first_isom; apply: subset_trans (subset_dom_coset K).
Qed.

Lemma quotient_mulg : H * K / K = H / K.
Proof.
rewrite normC //; apply/setP=> Kx; apply/imsetP/imsetP=> [] [x Hx ->{Kx}].
  case/mulsgP: Hx => k h Kk Hh->; exists h => //; apply: kerP.
  by rewrite (subsetP (subset_ker_coset _)).
by exists x; rewrite // (subsetP (mulG_subr _ _)).
Qed.

Lemma weak_second_isom : isog (H / (K :&: H)) (H * K / K).
Proof. rewrite quotient_mulg; exact: second_isom. Qed.

End SecondIsomorphism.

Section ThirdIsomorphism.

Variables (gT : finGroupType) (G H K : {group gT}).

Hypothesis sHK : H \subset K.
Hypothesis snHG : H <| G.
Hypothesis snKG : K <| G.

Theorem third_iso  : isog (G / H / (K / H)) (G / K).
Proof.
case/andP: snHG => _ nHG; case/andP: snKG => sKG nKG. 
have sHker: H \subset ker (coset_of K).
  by rewrite (subset_trans sHK) ?subset_ker_coset.
have sGdom: G \subset dom (coset_of K).
  by rewrite (subset_trans nKG) ?subset_dom_coset.
have sGHdom: G / H \subset dom (mquo (coset_of K) H).
  apply: subset_trans (subset_dom_mquo _ _); exact: imsetS.
pose f := mquo (coset_of K) H.
have KH_ker : K / H = ker_(G / H) f.
  rewrite ker_mquo_loc // ker_coset_of_loc //; congr (_ / H).
  apply/setP=> x; rewrite inE.
  by case Kx: (x \in K); rewrite //= (subsetP sKG).
rewrite -[K / H]/(set_of_group _) {KH_ker}(group_inj KH_ker) /=.
have -> : G / K = f @: (G / H) by rewrite factor_mquo_iim.
exact: first_isom.
Qed.

End ThirdIsomorphism.

Unset Implicit Arguments.