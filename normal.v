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

Section Normal.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : {set elt}).

(********************************************************************)
(*              Definition of a normal set                          *)
(*    H is normal in K iff xHx^-1 = H forall x in K                 *)
(*    it is sufficient that xHx^\u00af1 is included in H            *)
(*    since both sets have same cardinal                            *)
(********************************************************************)

Definition normal := K \subset normaliser H.

Theorem normalP : reflect (forall x, x \in K -> (H :^ x) = H) normal.
Proof.
apply: (iffP idP).
  by move/subsetP=> H1 x Kx; apply norm_sconjg; apply H1.
  by move=> H1; apply/subsetP=> x Kx; rewrite/normaliser setE H1 //; apply subset_refl.
Qed.

End Normal.

Notation "H '<|' K" := (normal H K) (at level 50) : group_scope.

Section NormalProp.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : {group elt}).

Hypothesis sHK : H \subset K.
Hypothesis nHK : H <| K.

Theorem normal_subset : forall L : {group elt}, L \subset K ->  H <| L.
Proof. move=> L sLK; exact: subset_trans sLK _. Qed.

Theorem norm_normal: H <| normaliser H.
Proof. exact: subset_refl. Qed.

End NormalProp.


Section Simple.

Variables (elt : finGroupType) (H : {set elt}).

Definition simple :=
  forallb K : {group elt}, (K \subset H) && (K <| H) ==> pred2 [set 1] H K.

Theorem simpleP:
  reflect
   (forall K : {group elt},
      K \subset H -> K <| H -> K = [set 1] :> set elt \/ K = H :> set elt)
   simple.
Proof.
(* have F1: forall z, pred1 1 z = set1 (1: elt) z by move => z; rewrite setE. *)
apply: (iffP forallP) => /= [Hf K Hk1 Hk2 | Hf K].
  have:= Hf K; rewrite Hk1 Hk2.
  by case/orP => HH; [left|right]; exact/eqP.
apply/implyP; case/andP => E1 E2.
by case: (Hf K) => //= ->; rewrite eqxx // orbT.
Qed.

End Simple.

(********************************************************************)
(*       Cosets are right cosets of elements in the normaliser      *)
(********************************************************************)

Section Cosets.

Open Scope group_scope.

Variables (elt : finGroupType) (A : {set elt}).

Definition coset_set := [image rcoset A of normaliser A].

Record coset : Type :=
  Coset {set_of_coset :> {set elt}; _ : coset_set set_of_coset}.

Canonical Structure coset_subType := SubType set_of_coset coset_rect vrefl.
Canonical Structure coset_eqType := [subEqType for set_of_coset].
Canonical Structure coset_finType := Eval hnf in [subFinType of coset_eqType].

End Cosets.

Prenex Implicits coset.

(********************************************************************)
(*  The domain of a morphism is inferred from the values of the     *)
(*  function. A morphism is constant 1 outside its domain           *)
(********************************************************************)


Section MorphismDefs.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType) (f : elt1 -> elt2).

(* Kernel *)
Definition ker  := [set x : elt1 | forallb y, f (x * y) == f y].

(* Domain of the morphism *)
Definition dom := ker :|: [set x | f x != 1].

(* Preimage *)
Definition mpreim (B : {set elt2}) := (f @^-1: B) :&: dom.

(* Being a trivial morphism *)
Definition trivm := forallb z, f z == 1.

(* Quotient morphism *)
Definition mquo (A : {set elt1})(Ax : coset A):=
  if A \subset ker then f (repr Ax) else 1.

(* Being a morphism injective on A*)
Definition injm (A : {set elt1}) := A :\ 1 \subset dom :\: ker.

(* Being an isomorphism between A and B *)
Definition isom (A : {set elt1}) (B : {set elt2}) :=
  (f @: A == B) && injm A.

(* The inverse morphism of an injective morphism *)
Definition invm  A y :=
  if injm A then repr [set x \in A | f x == y] else 1.

Definition idm (x : elt1) := x.

End MorphismDefs.

Implicit Arguments mquo [elt1 elt2].
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

Variables (elt1 elt2 : finGroupType)(f : elt1 -> elt2).

Lemma kerP : forall x, reflect (forall y, f (x * y) = f y) (x \in ker f).
Proof.
by move=> x; rewrite setE; apply: (iffP forallP) => [] Kx y; move/eqP: (Kx y).
Qed.

(* The kernel of an arbitrary function is a group *)
Lemma group_set_ker : group_set (ker f).
Proof.
apply/andP; split; first by apply/kerP=> x; rewrite mul1g.
apply/subsetP=> x; case/smulgP=> y z; move/kerP=> Hy; move/kerP=> Hz ->.
by apply/kerP=> t; rewrite -mulgA Hy Hz.
Qed.

Canonical Structure group_ker := Group group_set_ker.

Lemma dom_k : forall x, x \in ker f -> x \in dom f.
Proof. by move=> x kx; rewrite setE; apply/orP; left. Qed.

Lemma dom_nu : forall x, f x != 1 -> x \in dom f.
Proof. by move=> x kx; rewrite setE; apply/orP; right; rewrite setE. Qed.

Lemma out_dom : forall x, (x \in dom f) = false -> f x = 1.
Proof.
move=> x; rewrite setE; case/norP=> _; rewrite setE=> H1; apply/eqP.
exact (negbE2 H1).
Qed.

Lemma trivm_is_cst : trivm f -> f =1 (fun _ => 1).
Proof. by move/pred0P=> Hf x; move/eqP: (Hf x). Qed.

Lemma trivm_ker :  trivm f -> ker f = setA.
Proof.
move/trivm_is_cst=> Hf; apply/setP=> x; rewrite !setE; apply/forallP=> y.
by rewrite !Hf.
Qed.

Lemma trivm_dom : trivm f -> dom f = setA.
Proof.
by move/trivm_ker=> Hf; apply/setP=> u; rewrite setE Hf !setE.
Qed.

Lemma subset_mpreim : forall A B : {set elt2},
  A \subset B -> mpreim f A \subset mpreim f B.
Proof.
move=> A B  HAB; apply/subsetP=> x; rewrite 2!setE; case/andP=> Hfx Dfx.
by rewrite setE Dfx setE (subsetP HAB).
Qed.

Lemma mpreimP : forall (A : {set elt2}) x,
  reflect (f x \in A /\ x \in dom f) (x \in mpreim f A).
Proof. move=> A x; rewrite !setE; exact: andP. Qed.


Lemma subset_mpreim_dom : forall A : {set elt2},
  mpreim f A \subset dom f.
Proof. by move=> A; apply/subsetP=> x; case/mpreimP. Qed.


Lemma injm_dom : forall A : {set elt1}, injm f A -> A \subset dom f.
Proof.
move=> A; move/subsetP=> H1; apply/subsetP=> x Ax.
case Hx: (x \in A :\ 1); first by move/H1: Hx; rewrite setE; case/andP.
by move: Hx; rewrite setE Ax andbT; move/eqP->; rewrite dom_k ?group1.
Qed.

Lemma subset_ker_r : forall A : {set elt1}, ker_(A) f \subset ker f.
Proof. by move=> A; apply/subsetP=> u; case/setIP. Qed.

Lemma ker_r_dom : ker_(dom f) f = ker f.
Proof.
apply/setP; apply/subset_eqP; rewrite subset_ker_r /=; apply/subsetP=> x Kx.
by apply/setIP; rewrite Kx dom_k.
Qed.

Lemma subset_dom_r : forall A : {set elt1}, dom_(A) f \subset dom f.
Proof. by move=> A; apply/subsetP=> x; case/setIP. Qed.

Lemma trivm_dom_ker_r : forall A : {set elt1},
  trivm_(A) f -> dom_(A) f = ker_(A) f.
Proof.
move=> A; move/forallP=> ftriv; apply/setP=> x; rewrite !setE.
by case: (x \in A) (ftriv x) => [/= ->|_]; rewrite ?orbF ?andbF.
Qed.

Variable H : {group elt1}.

Lemma ker_injm : injm f H -> ker_(H) f = [set 1].
Proof.
rewrite /injm=> H1; apply/setP.
apply/subset_eqP; apply/andP; split; apply/subsetP=> x; last first.
  by rewrite setE; move/eqP->; rewrite group1.
case/setIP=> Kx; move/setD1K: (group1 H)=> <-; rewrite setE.
by case/orP; last move/(subsetP H1); rewrite setE // Kx. 
Qed.

Lemma injm_ker :
  H \subset dom f -> ker_(H) f = [set 1] -> injm f H.
Proof.
move=> Hsub Hker; rewrite /injm; apply/subsetP=> x Hx; rewrite setE in Hx.
move/andP: Hx=> [Hxn1 HxH]; rewrite setDE; apply/setIP; split; last first.
   rewrite setE; apply/negP=>HH; move: HxH; move/(conj HH); move/setIP.
   by rewrite Hker setE (negbET Hxn1).
by apply:(subsetP Hsub).
Qed.

Lemma ker_dinj : {in H &, injective f} -> ker_(H) f = [set 1].
Proof.
move=> If; apply/setP=> x; apply/setIP/idP; rewrite !setE; last first.
  by move/eqP->; rewrite group1; split=> //; apply/forallP=> y; rewrite mul1g.
by case=> Kx Hx; have:= forallP Kx 1; rewrite mulg1; move/eqP; move/If->.
Qed.

Lemma trivm_injm_r : trivm_(H) f && injm f H -> trivg H.
Proof.
move/andP.
move=> [Htriv]; rewrite /injm setDUl setDv set0U => Hinj.
apply/subsetP=> x Hx; rewrite setE; apply/idPn => nx1.
case/pred0Pn: Htriv; exists x; rewrite Hx /=.
have: (x \in H :\ 1) by rewrite !setE Hx andbT.
by move/(subsetP Hinj); rewrite !setE; case/andP.
Qed.

End GenericProps.


(* Definition of the morphism structure *)
Section Morphisms.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType).

Structure morphism : Type := Morphism {
  mfun :> elt1 -> elt2;
  group_set_dom : group_set (dom mfun);
  morphM : {in dom mfun &, {morph mfun : x y / x * y}}
(* forall x y, x \in dom mfun -> x \in dom mfun ->
           mfun (x * y) = mfun x * mfun y *)
}.

Variable f : morphism.

Canonical Structure mdom := Group (group_set_dom f).

Lemma morph1 : f 1 = 1.
Proof. by apply (mulg_injl (f 1)); rewrite -morphM ?group1 // !mulg1. Qed.

Lemma morphV : {in dom f, {morph f : x / x^-1 >-> x^-1}}.
Proof.
move=> x Dx; apply: (mulg_injl (f x)); rewrite mulgV -morphM ?groupV //.
by rewrite mulgV morph1.
Qed.

Lemma morphJ : {in dom f &, {morph f : x y / x ^ y}}.
Proof. by move=> *; rewrite /conjg !morphM ?morphV // ?groupM ?groupV. Qed.

Lemma morphE : forall n, {in dom f, {morph f : x / x ** n}}.
Proof.
move=> n.
elim: n => [x Dx| n Hrec x Dx]; first by rewrite !gexpn0 morph1.
by rewrite !gexpnS morphM ?groupE ?Hrec.
Qed.

Lemma mker: forall x, x \in ker f -> f x = 1.
Proof.
move=> x; rewrite setE; move/forallP; move/(_ 1); move/eqP.
by rewrite mulg1 morph1.
Qed.

(* The kernel of a morphism is the set of elements in the domain *)
(* that are mapped to the unit *)
Lemma kerMP : forall x, x \in dom f -> reflect (f x = 1) (x \in ker f).
Proof.
move=> x Dx; apply: (iffP idP); first exact: mker.
rewrite setE => Hx; apply/forallP => y.
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


Lemma imset_smul : forall A B : {set elt1},
  A \subset dom f -> B \subset dom f -> f @: (A :*: B) = (f @: A) :*: (f @: B).
Proof.
move=> A B DomA DomB; apply/setP=> y; apply/imsetP/smulgP.
  case=> x; case/smulgP=> a b Aa Bb -> ->.
  exists (f a) (f b); [apply/imsetP; exists a|apply/imsetP; exists b|]=>//.
  by rewrite morphM // ?((subsetP DomA) a) ?(subsetP DomB).
case=> u v; case/imsetP=> a Aa ->; case/imsetP=> b Bb -> ->.
exists (a * b); first by apply/smulgP; exists a b.
by rewrite  morphM // ?((subsetP DomA) a) ?(subsetP DomB).
Qed.

Lemma imset_conj : forall (A : {set elt1}) x,
  A \subset dom f -> x \in dom f ->  f @: (A :^ x) = (f @: A) :^ (f x).
Proof.
move=> A x DomA Domx.
rewrite !sconjg_coset !rcoset_smul !lcoset_smul -morphV //.
rewrite -(imset_set1 f)  -!imset_smul  // ?subset_set1 ?groupVr //.
rewrite ?imset_smul ?(imset_set1 f) // ?subset_set1 // ?groupV //.
apply/subsetP=> wl; case/smulgP=> u v; rewrite setE; move/eqP=> -> Av ->.
by rewrite groupM ?groupV // (subsetP DomA).
Qed.

Section MorphIm.

Variable H : {group elt1}.

Lemma im_group_dom : f @: H = f @: (H :&: dom f).
Proof.
apply/setP=> u.
apply/imsetP/imsetP; last by case=> x; case/setIP=> Hx Dx ->; exists x.
case=> x Hx ->; case domx : (x \in dom f); first by exists x=> //; apply/setIP.
exists (1 : elt1); first by apply/setIP; split; rewrite group1.
move/negbT: domx; rewrite !setE negb_or negbK morph1; case/andP=> _.
by move/eqP.
Qed.

Lemma group_set_im : group_set (f @: H).
Proof.
rewrite im_group_dom /group_set; apply/andP; split.
  by apply/imsetP; exists (1:elt1); rewrite ?group1 // -morph1.
apply/subsetP=> t; case/smulgP=> u v.
case/imsetP=> x; case/setIP=> Hx Dx ->.
case/imsetP=> y; case/setIP=> Hy Dy -> ->.
apply/imsetP; exists (x * y); last by rewrite morphM.
by apply/setIP; rewrite !groupM.
Qed.

Canonical Structure group_im := Group group_set_im.

End MorphIm.

Section MorphPreIm.

Lemma mpreimUker : forall A : {set elt2},
  1 \in A -> mpreim f A = (f @^-1: (A :\ 1)) :|: (ker f).
Proof.
move=> A A1; apply/setP=> u; apply/setIP/setUP.
  rewrite setE => Hu; apply/orP; case ku : (u \in ker f); rewrite // ?orbT //.
  by rewrite orbF !setE; case: Hu => ->; rewrite andbT setE ku /= setE eq_sym.
case=> [|Ku]; first by  rewrite !setE; case/andP=> -> ->; rewrite orbT.
by rewrite dom_k // setE (kerMP _ Ku) ?A1 // dom_k.
Qed.

Variable H : {group elt2}.

Lemma mpreim_group : group_set (mpreim f H).
Proof.
rewrite /group_set; do 2 rewrite setE; rewrite morph1 !group1 /=.
apply/subsetP=> u; case/smulgP=> x y; case/setIP; rewrite setE.
move=> Hx1 dx; case/setIP; rewrite setE=> Hy1 dy ->.
by apply/setIP; apply/andP; rewrite setE morphM ?groupM.
Qed.

Canonical Structure mpreim_group_struct := Group mpreim_group.

End MorphPreIm.

Lemma morph_norml_im : forall K : {group elt1},
  K \subset dom f ->  K <| dom f -> (f @: K) <| (f @: dom f).
Proof.
move=> K sKD; move/normalP=> HnK; apply/normalP=> x.
by case/imsetP=> u Hu ->; rewrite -imset_conj ?HnK.
Qed.

Lemma normal_ker : ker f <| dom f.
Proof.
apply/normalP=> x Dx; apply/setP=> y; apply/idP/idP.
  rewrite setE; move=> Kxy.
  have Dy: (y \in dom f) by rewrite -(@groupJr _ _ y x^-1) ?groupV // dom_k //.
  apply/(kerMP Dy); apply (conjg_inj (f (x^-1))).
  by rewrite conj1g -morphJ ?groupV // mker.
move=> ky; have Dy: y \in dom f by apply: dom_k.
rewrite setE; apply/kerMP; rewrite ?groupJr ?groupV //.
by rewrite morphJ ?groupV // (mker ky) conj1g.
Qed.

Lemma normal_ker_r : forall H : {group elt1},
  ker_(H) f <| dom_(H) f.
Proof.
move=> A; apply/subsetP=> d; case/setIP=> Dd Hd; rewrite setE; apply/subsetP=> x; rewrite setE.
case/setIP=> Kxd Hxd; apply/setIP.
have: d \in normaliser (ker f) by rewrite (subsetP normal_ker _).
rewrite setE; move/subsetP; move/(_ x)=> ->; rewrite 1?setE //.
by rewrite -(@groupJr _ _ _ d^-1) ?groupV.
Qed.


(* Being isomorphic *)
Definition isog (A : {set elt1})(B : {set elt2}) :=
  exists g : morphism, isom g A B.

Lemma injmP : forall A: {group elt1}, reflect {in A &,injective f} (injm f A).
Proof.
move=> A; apply: (iffP idP) => [H1 x y Ax Ay Hxy | IfA].
  case HxyV : (x * y ^-1 \in A :\ 1).
    move/(subsetP H1): HxyV; rewrite setE andbC.
    case/andP=> Dxy; case/(kerMP Dxy); apply: (mulg_injr (f y)).
    by rewrite mul1g -morphM ?mulgKv // (subsetP (injm_dom H1)).
  move: HxyV; rewrite -{2}(mulgKv y x) setE groupM ?groupV // andbT.
  by move/eqP->; rewrite mul1g.
apply/subsetP=> x; rewrite setE; case/andP=> Hx1 Ax.
case: (f x =P 1) => [f1|]; first by case/eqP: Hx1; apply: IfA; rewrite // morph1.
move/eqP=> nfx1; have Dx: x \in dom f by exact: dom_nu.
rewrite setE Dx andbT; apply/(kerMP Dx); exact/eqP.
Qed.

Lemma gen_f_com : forall (S:{set elt1}),
  S \subset (dom f) -> f @: << S >> = << f @: S >>.
Proof.
move=> S Hsub; apply/setP; apply/subset_eqP; apply/andP.
split; last by apply: bigcap_inf=>/=; apply subset_imset; apply/bigcap_inP.
apply/bigcap_inP=>H Hsub2.
suff: (S \subset (mpreim f H)).
  rewrite [S \subset _]subset_gen_stable /=; move/(subset_imset f)=>Hsub3.
  apply: (subset_trans Hsub3); apply/subsetP=> x; move/imsetP=> [x0].
  by  move/mpreimP; move=>[Hp _] Heq; move: Heq Hp=>->.
apply/subsetP=> x Sx; apply/mpreimP; move/subsetP: Hsub; move/(_ _ Sx)=>->.
apply/andP; rewrite andbT; move/subsetP:Hsub2; move/(_ (f x)); apply.
by apply/imsetP; exists x.
Qed.

End Morphisms.


Prenex Implicits isog.


Section IdMorphism.

Variable elt : finGroupType.

Notation Local elt_id := (idm elt).

Lemma dom_id : dom elt_id = setA.
Proof.
apply/setP=> x; rewrite setAP /= setE orbC setE.
by case: eqP=> // x1; apply/kerP=> y; rewrite [x]x1 mul1g.
Qed.

Lemma group_set_dom_id : group_set (dom elt_id).
Proof. by rewrite dom_id group_setA. Qed.

Lemma idmorphM : {in dom elt_id &, {morph elt_id : x y / x * y}}.
Proof. by []. Qed.

Canonical Structure morph_id := Morphism group_set_dom_id idmorphM.

End IdMorphism.


Section TrivMorphism.

Variables (elt1 elt2 : finGroupType).

Notation Local triv := (fun _ : elt1 => (1 : elt2)).

Lemma dom_triv_morph : dom triv = setA.
Proof. by apply/setP=> x; rewrite setAP dom_k //; apply/kerP. Qed.

Lemma group_set_triv_morph : group_set (dom triv).
Proof. by rewrite dom_triv_morph group_setA. Qed.

Lemma trivmorphM : {in dom triv &, {morph triv : x y / x * y}}.
Proof. by move=> x y _ _ /=; rewrite mulg1. Qed.

Canonical Structure triv_morph := Morphism group_set_triv_morph trivmorphM.

Lemma iim_trivm : forall (A : {set elt1}) x, x \in A -> triv @: A = [set 1].
Proof.
move=> A x Ax; apply/setP=> y; rewrite setE; apply/idP/eqP; first by case/imsetP.
by move=> <-; apply/imsetP; exists x.
Qed.

Lemma trivial_isog : forall (A : {group elt1}) (B : {group elt2}),
  trivg A -> trivg B -> isog A B.
Proof.
move=> A B; move/trivgP=> ->; move/trivgP=> ->.
exists triv_morph; apply/andP; split.
  by rewrite (@iim_trivm _ 1) ?setE //.
by apply /injmP=> x y; rewrite ?inE /= !setE; move/eqP=> ->; move/eqP.
Qed.

End TrivMorphism.


(* Canonical Structure of morphism for the composition of 2 morphs *)
(* Composing morphisms can lead to trivial morphisms, in that case,*)
(* the equations for ker and dom do not hold anymore,              *)
(* but only one inclusion.                                         *)


Section MorphismComposition.

Open Scope group_scope.

Variables (elt1 elt2 elt3 : finGroupType).

Variable f : morphism elt1 elt2.
Variable g : morphism elt2 elt3.

Notation Local gof := ((mfun g) \o (mfun f)).


Lemma morph_nuc : forall (h : elt1 -> elt2) x, (g \o h) x != 1 -> h x != 1.
Proof.
by move=> h x Hx; apply/eqP=> Hhx; rewrite /= Hhx morph1 eq_refl in Hx.
Qed.

Lemma trivm_cn : forall h : elt1 -> elt2,
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
rewrite setE Dfy andbT setE; apply/kerMP.
  by rewrite -(@groupMr _ _ (f x)) -?morphM // dom_nu.
by rewrite -(mulg1 y) Hy !morph1.
Qed.


Lemma subset_dom_c : mpreim f (dom g) \subset dom gof.
Proof.
apply/subsetP=> x; case/mpreimP; case/setUP; last first.
  by rewrite setE=> ? _; exact: dom_nu.
move=> Kx Dx; apply: dom_k; apply: (subsetP subset_ker_c); exact/mpreimP.
Qed.

Lemma dom_c : ~~ trivm gof -> dom gof = (mpreim f (dom g)).
Proof.
move=> Hnt; apply/setP; apply/subset_eqP; rewrite subset_dom_c andbT.
apply/subsetP=> x; case/setUP.
  rewrite ker_c //; apply: (subsetP (subset_mpreim _ _)).
  apply/subsetP; exact: dom_k.
by rewrite 3!setE => Hx; rewrite !dom_nu // morph_nuc.
Qed.

Lemma group_set_dom_c : group_set (dom gof).
Proof.
case Hnt: (trivm gof); last by rewrite dom_c ?Hnt ?set_of_groupP.
rewrite trivm_dom //; apply/groupP; split=> *; exact: setAP.
Qed.

Lemma morphMc : {in dom gof &, {morph gof: x y / x * y}}.
Proof.
case Ht: (trivm gof) => [] x y; last move/negbT: Ht => Hnt.
  by rewrite !(trivm_is_cst Ht) mulg1.
rewrite !(dom_c Hnt); case/mpreimP=> [Hgx Hx]; case/mpreimP=> [Hgy Hy].
by rewrite /= !morphM.
Qed.

Canonical Structure morph_c := Morphism group_set_dom_c morphMc.

Lemma ker_c_loc : forall G : {group elt1},
    G \subset dom f -> f @: G \subset dom g ->
  ker_(G) gof = mpreim f (ker_(f @: G) g) :&: G.
Proof.
move=> G sGd sfGd; apply/setP=> x.
rewrite -!(setIC G) 2![x \in _ :&: _]setE.
case Gx : (x \in G)=> //=; apply/idP/idP=> [Kx|].
  rewrite 2!setE (subsetP sGd) // andbT; apply/setIP.
  split; last by apply/imsetP; exists x.
  apply/kerMP; rewrite ?(subsetP sfGd) //; first by apply/imsetP; exists x.
  by apply: (kerMP _ Kx); rewrite dom_k.
rewrite setE; case/andP; rewrite setE; case/setIP=> Kx _ Dx.
by rewrite (subsetP subset_ker_c) // setE Dx andbT setE.
Qed.

End MorphismComposition.



(* We build a new (canonical) structure of groupType for cosets. *)
(* This group type is the largest possible quotient N (H) / H    *)


Section CosetGroupType.

Open Scope group_scope.

Variable elt : finGroupType.

Lemma coset_set_unit :forall A : {set elt}, coset_set A A.
Proof.
by move=> A; apply/imageP; exists (1 : elt); rewrite /= ?group1 ?rcoset1.
Qed.

Definition coset_unit (A : {set elt}) := Coset (coset_set_unit A).

Variable H : group elt.

Notation Local N := (normaliser H).

Lemma coset_set_mul : forall Hx Hy : coset H, coset_set H (Hx :*: Hy).
Proof.
rewrite /set_of_coset => [] [[Hx nHx]] [[Hy nHy]] /=.
case/imageP: nHx => [x Nx ->{Hx}]; case/imageP: nHy => [y Ny ->{Hy}].
by apply/imageP; exists (x * y); rewrite /= ?groupM // rcoset_mul.
Qed.

Definition coset_mul Hx Hy := Coset (coset_set_mul Hx Hy).

Lemma coset_set_inv : forall Hx : coset H, coset_set H (Hx :^-1).
Proof.
rewrite /set_of_coset => [] [[A]] /=; move/imageP=>[x Nx ->{A}].
by apply/imageP; exists x^-1; rewrite /= ?groupV // -sinvg_lcoset norm_rlcoset.
Qed.

Definition coset_inv Hx := Coset (coset_set_inv Hx).

Lemma coset_unitP : forall Hx, coset_mul (coset_unit H) Hx = Hx.
Proof.
move=> [Hx nHx]; apply: val_inj => /=; case/imageP: nHx => x Nx ->{Hx}.
by rewrite !rcoset_smul smulgA smulgg.
Qed.

Lemma coset_invP : forall Hx, coset_mul (coset_inv Hx) Hx = coset_unit H.
Proof.
move=> [Hx nHx]; apply: val_inj => /=; case/imageP: nHx => x Nx ->{Hx}.
rewrite {1}norm_rlcoset // sinvg_lcoset ?rcoset_mul ?groupV // mulVg.
by rewrite rcoset1.
Qed.

Lemma coset_mulP : forall Hx Hy Hz,
  coset_mul Hx (coset_mul Hy Hz) = coset_mul (coset_mul Hx Hy) Hz.
Proof.
by move=> [Hx nHx] [Hy nHy] [Hz nHz]; apply: val_inj; rewrite /= smulgA.
Qed.

Canonical Structure coset_groupType :=
  FinGroupType coset_unitP coset_invP coset_mulP.

End CosetGroupType.


Section Quotient.

Open Scope group_scope.

Variable elt : finGroupType.

(* Projection of the initial group type over the cosets groupType  *)
(* Again we need to separate the case of trivial projection for the*)
(* dom and ker equations                                           *)

Definition coset_of A x : @coset elt A := insubd (coset_unit A) (A :* x).

Variable H : {group elt}.

Notation Local N := (normaliser H).

Lemma coset_set_rcoset : forall x, coset_set H (H :* x) = (x \in N).
Proof.
move=> x; apply/imageP/idP=> [[y /= Ny Hy]|]; last by exists x.
move: Ny; rewrite !setE !sconjg_coset -[_ *: H]sinvgK sinvg_lcoset invgK.
rewrite -Hy -{1}[x]invgK -sinvg_lcoset sinvgK !lcoset_smul !rcoset_smul.
by rewrite -!smulgA -!rcoset_smul Hy.
Qed.

(*
Lemma set_of_coset_of : forall x,
  coset_of H x = if N x then H :* x else H :> set _.
*)
Lemma set_of_coset_of : forall x,
  coset_of H x = (if x \in N then H :* x else H) :> set _.
Proof.
move=> x; rewrite -coset_set_rcoset /coset_of /insubd.
by case insubP => [u -> <- //|]; move/negbET->.
Qed.

Lemma coset_ofN : forall x, x \in N -> coset_of H x = H :* x :> set _.
Proof. by move=> x; rewrite set_of_coset_of => ->. Qed.

Lemma coset_of_id : forall x, x \in H -> coset_of H x = 1.
Proof.
move=> x Hx; apply: val_inj; rewrite /= coset_ofN ?rcoset_id //.
exact: (subsetP (norm_refl _)).
Qed.

Lemma coset_of_idr : forall x, x \in N -> coset_of H x = 1 -> x \in H.
Proof.
move => x Hx H1 /=.
rewrite -(rcoset1 H) rcoset_sym.
move: (coset_ofN Hx); rewrite H1 => <-.
by rewrite group1.
Qed.


Lemma coset_ofV : forall x, coset_of H (x ^-1) = (coset_of H x) ^-1.
Proof.
move=> x; apply: val_inj.
rewrite /= !set_of_coset_of groupV.
case Nx: (x \in N); last by rewrite sinvG.
by rewrite -sinvg_lcoset norm_rlcoset.
Qed.

Lemma subset_ker_coset : H \subset ker (coset_of H).
Proof.
apply/subsetP=> x Hx; apply/kerP=> y; apply: val_inj.
have Nx := subsetP (norm_refl _) _ Hx.
rewrite /= !set_of_coset_of groupMl // -rcoset_mul // rcoset_id //.
by rewrite !rcoset_smul smulgA smulgg.
Qed.

Lemma nu_coset_of_norm : forall x, coset_of H x != 1 -> x \in N.
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
  by apply/rcosetP; exists (1 : elt); rewrite ?mul1g.
by rewrite -(mulgK y x) groupM ?groupV // nu_coset_of_norm.
Qed.

Lemma subset_dom_coset : N \subset dom (coset_of H).
Proof.
apply/subsetP=> x Nx; apply/setUP; case Hx: (x \in H); [left | right].
  exact: (subsetP subset_ker_coset).
rewrite setE -(inj_eq val_inj) /= coset_ofN //.
apply/eqP=> dH; rewrite -dH in Hx.
by case/rcosetP: Hx; exists (1 : elt); rewrite ?mul1g.
Qed.

Lemma dom_coset : ~~ trivm (coset_of H) -> dom (coset_of H) = N.
Proof.
move=> Hnt; apply/setP; apply/subset_eqP; rewrite subset_dom_coset andbT.
rewrite /dom ker_coset //; apply/subsetP=> x; case/setUP.
  exact: (subsetP (norm_refl _)).
by rewrite setE; exact: nu_coset_of_norm.
Qed.

Lemma group_set_dom_coset : group_set (dom (coset_of H)).
Proof.
case Hnt: (trivm (coset_of H)).
  by rewrite trivm_dom //; apply/groupP; split=> *; rewrite setAP.
by rewrite dom_coset ?Hnt ?set_of_groupP.
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
Lemma coset_ofE : forall n,
  {in dom (coset_of H), {morph coset_of H : x / x ** n}}.
Proof. exact: morphE. Qed.

Lemma trivm_coset_of :
  reflect (normaliser H = H) (trivm (coset_of H)).
Proof.
apply: (iffP idP); last first.
  move=> NH; apply/pred0P=> x; apply/eqP; apply: val_inj => /=.
  by rewrite set_of_coset_of; case Nx: (x \in N)=> //; rewrite rcoset_id //= -1?NH.
move=> Htriv; apply/setP; apply/subset_eqP; rewrite norm_refl andbT.
apply/subsetP=> x Nx; suff: H :* x = H by move=> <-; rewrite rcoset_refl.
by rewrite -coset_ofN // trivm_is_cst.
Qed.

Lemma ker_coset_of_loc : forall K : group elt,
  H <| K -> ker_(K) (coset_of H) = H :&: K.
Proof.
move=> K nHK.
case Htriv : (trivm (coset_of H)); last by rewrite ker_coset ?Htriv.
apply/setP=> x; rewrite trivm_ker // !setE /= andbC.
by case Kx : (x \in K); rewrite //= -(trivm_coset_of Htriv) (subsetP nHK).
Qed.


Definition quotient (A B : {set elt}) := (coset_of B) @: A.

Notation "A / B" := (quotient A B).

Variable K : group elt.

Canonical Structure quotient_group := Eval hnf in [group of K / H].

Lemma quotientP : forall xbar,
  reflect (exists x, [/\ x \in K, x \in N & xbar = coset_of H x])
          (xbar \in K / H).
Proof.
move=> xbar; apply: (iffP (imsetP _ _ _)) => [[x Kx -> {xbar}] | [x [*]]]; last by exists x.
case Nx: (x \in N); first by exists x .
exists (1 : elt); rewrite !group1 morph1; split=> //.
by apply: val_inj; rewrite /= set_of_coset_of Nx.
Qed.


Lemma set_of_coset_quotient :
  (@set_of_coset _ H) @: (K / H) = (rcoset H) @: (N :&: K).
Proof.
apply/setP=> A; apply/imsetP/imsetP=> [[xbar Kxbar]|[x NKx]] ->{A}.
  case/quotientP: Kxbar => x [Nx Kx ->{xbar}].
  by exists x; [rewrite setE Kx | rewrite coset_ofN].
case/setIP: NKx => Nx Kx.
by exists (coset_of H x); [apply/imsetP; exists x | rewrite coset_ofN].
Qed.

Lemma card_quotient : H <| K -> #|K / H| = indexg H K.
Proof.
move=> sHK; rewrite -(card_imset _ val_inj).
rewrite set_of_coset_quotient; congr #|_ @: (_ : set _)|.
by apply/eqP; rewrite setIC eqsetIl.
Qed.

End Quotient.

Notation "A / B" := (quotient A B) : group_scope.

Prenex Implicits coset_of quotient.

Section TrivialQuotient.

Open Scope group_scope.

Variables (elt : finGroupType) (H : group elt).

Lemma trivial_quotient : (H / H) = [set 1].
Proof.
apply/setP=> A; apply/quotientP/set1P => [[x [Hx _ ->]] | ->].
  by rewrite coset_of_id.
by exists (1 : elt); rewrite coset_of_id !group1.
Qed.

End TrivialQuotient.


(* Canonical structure of morphism for the quotient morphism *)


Section QuotientMorphism.

Open Scope group_scope.

Variables elt elt' : finGroupType.

Variable f : morphism elt elt'.
Variable H : group elt.

Notation Local fq := (mquo f H).
Notation Local N := (normaliser H).
Let domN := subsetP (subset_dom_coset H).

Lemma norm_repr_coset : forall xbar : coset H, repr xbar \in N.
Proof.
case=> [[Hx csHx]]; rewrite /set_of_coset /=; case/imageP: (csHx) => x Nx ->.
by case: repr_rcosetP=> z Hz; rewrite groupMr // (subsetP (norm_refl _)).
Qed.

Lemma coset_of_repr : forall xbar : coset H, coset_of H (repr xbar) = xbar.
Proof.
move=> xbar; apply: val_inj.
rewrite /= set_of_coset_of norm_repr_coset.
case: xbar; case=> A /=; case/imageP=> x Nx ->{A}; exact: rcoset_repr.
Qed.

Lemma cosetP : forall xbar, {x | x \in N & xbar = coset_of H x}.
Proof.
by move=> xbar; exists (repr xbar); rewrite ?coset_of_repr ?norm_repr_coset.
Qed.

Lemma factor_mquo_norm : H \subset ker f ->
  forall x, x \in N -> fq (coset_of H x) = f x.
Proof.
move=> sHK x Nx; rewrite /mquo sHK coset_ofN //; case: repr_rcosetP=> y Hy.
apply: kerP; exact: (subsetP sHK).
Qed.

Lemma factor_mquo : H \subset ker f ->  H <| dom f ->
  forall x, fq (coset_of H x) = f x.
Proof.
move=> sHK nHD x; case Nx: (x \in N); first exact: factor_mquo_norm.
rewrite /mquo sHK set_of_coset_of Nx -(rcoset1 H); case: repr_rcosetP => y Hy.
rewrite (@out_dom _ _ f x); last by apply/negP; move/(subsetP nHD); rewrite Nx.
rewrite -(morph1 f); apply: kerP; exact: (subsetP sHK).
Qed.

Lemma factor_mquo_iim : H \subset ker f ->
  forall A : {group elt}, A \subset N -> fq @: (A / H) = f @: A.
Proof.
move=> sHK A sAN ; apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP => x.
  case/imsetP=> Hx pHx ->; case/imsetP: pHx=> y Ay ->.
    by apply/imsetP; exists y ; rewrite // factor_mquo_norm ?(subsetP sAN).
case/imsetP=> y Ay ->; apply/imsetP.
exists (coset_of H y); rewrite ?factor_mquo_norm ?(subsetP sAN) //.
by apply/imsetP; exists y.
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
case: (cosetP ybar) => y Ny ->{ybar}; rewrite -morphM ?domN // !fqc ?groupMl //; exact: kerP.
Qed.

Lemma subset_ker_mquo : ker f / H \subset ker fq.
Proof.
apply/subsetP=> Abar KAbar; case Hnt: (trivm fq); first by rewrite trivm_ker ?setAP.
by rewrite ker_mquo_nt ?Hnt.
Qed.

Lemma mquo_triv : H \subset ker f -> H <| dom f -> trivm fq -> trivm f.
Proof.
by move=> sHk sdN fqTriv; apply/pred0P=> x; rewrite -factor_mquo // trivm_is_cst ?eq_refl.
Qed.

Lemma ker_mquo : H \subset ker f -> H <| dom f -> ker fq = ker f / H.
Proof.
case Htr: (trivm fq) => [] sHK nHD; last by rewrite ker_mquo_nt ?Htr.
apply/setP=> xbar; rewrite trivm_ker // setAP; symmetry; apply/imsetP.
case: (cosetP xbar) => x _ ->{xbar}; exists x => //=.
by rewrite trivm_ker ?setAP {x}//; apply/pred0P=> x; rewrite -factor_mquo ?(pred0P Htr).
Qed.


Lemma dom_mquo_nt : ~~ trivm fq -> dom fq = dom f / H.
Proof.
move=> Hnt; apply/setP=> xbar; rewrite 2!setE ker_mquo_nt //.
have fqc := factor_mquo_norm (mquo_nt_subker Hnt).
apply/orP/imsetP=> [|[x Dx ->{xbar}]].
  case; first by case/quotientP=> x /= [Kx Nx ->{xbar}]; exists x => //; apply/setUP; left.
  case: (cosetP xbar) => x Nx ->{xbar}; rewrite fqc //; exists x => //; exact: dom_nu.
case Nx: (x \in N).
  by case/setUP: Dx; [left; apply/imsetP; exists x | rewrite setE fqc //; right].
left; apply/imsetP; exists (1 : elt); rewrite ?group1 //; apply: val_inj.
by rewrite /= set_of_coset_of Nx coset_of_id.
Qed.

Lemma subset_dom_mquo : dom f / H \subset dom fq.
Proof.
apply/subsetP=> Abar DAbar; case Hnt: (trivm fq); first by rewrite trivm_dom ?setAP.
by rewrite dom_mquo_nt ?Hnt.
Qed.

Lemma dom_mquo : H \subset ker f -> H <| dom f -> dom fq = dom f / H.
Proof.
case Htr: (trivm fq) => [] sHK nHD; last by rewrite dom_mquo_nt ?Htr.
apply/setP=> xbar; case: (cosetP xbar) => x _ -> {xbar}.
rewrite trivm_dom // setAP; symmetry; apply/imsetP; exists x => //.
rewrite trivm_dom ?setAP {x}//; apply/pred0P=> x.
by rewrite -factor_mquo ?(pred0P Htr) //.
Qed.

Lemma group_set_dom_mquo : group_set (dom fq).
Proof.
case Hnt: (trivm fq); last by rewrite dom_mquo_nt ?Hnt // set_of_groupP.
by rewrite trivm_dom //; apply/groupP; split=> *; rewrite setAP.
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
  forall G : {group elt}, G \subset dom f ->
  ker_(G / H) (mquo f H) = (ker_(G) f) / H.
Proof.
move=> sHK G sGd; apply/setP=> Hx; apply/setIP/quotientP.
  case=> KHx; case/quotientP=> x [Gx Nx E1]; exists x; split => //=.
  rewrite setE Gx andbT; apply/kerMP; first exact:(subsetP sGd).
  by rewrite -factor_mquo_norm // ?dom_k ?(subsetP subset_ker_mquo) // -E1 mker.
case=> x []; case/setIP=> Kx Gx Nx ->; split; last by apply/quotientP; exists x.
by rewrite (subsetP subset_ker_mquo) //; apply/imsetP; exists x.
Qed.

End QuotientMorphism.


Section InverseMorphism.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType)(H : {group elt1}).
Variable f : morphism elt1 elt2.

Hypothesis injmf : injm f H.

Notation Local invfH := (invm f H).

Lemma ker_invm : ker_(f @: H) invfH = [set 1].
Proof.
apply/setP=> y; apply/setIP/set1P=> [[]|->{y}]; last by rewrite !group1.
move/kerP=> Hkx; case/imsetP=> x Hx Ey; apply/eqP.
have:= Hkx 1; rewrite mulg1; rewrite /invm injmf; rewrite {}Ey.
set kerH := [set y \in H | f y == 1] => Er.
have: 1 \in kerH by rewrite setE group1 morph1 eq_refl.
move/mem_repr; rewrite -Er setE; case/andP=> _; move/eqP <-.
have: x \in [set y \in H | f y == f x] by rewrite setE Hx eqxx.
by move/mem_repr; rewrite setE eq_sym; case/andP.
Qed.

Lemma invIm: forall x, x \in H -> invm f H (f x) = x.
Proof.
move=> x Hx; rewrite /invm injmf /repr; case: pickP => [z|] /=.
  rewrite setE; case/andP=> HH1; move/eqP; exact: (injmP _ _ injmf).
by move/(_ x); rewrite /= setE Hx eq_refl.
Qed.

Hypothesis Hntriv: ~trivg H.

Lemma kert_invm : ker invfH  = [set 1].
Proof.
case E1: (pred0b (predD1 (mem H) 1)); apply sym_equal.
  case: Hntriv; apply/trivgP.
  apply/setP=> z; rewrite setE; have:= pred0P E1 z => /=.
  by case: eqP => // ->; rewrite group1.
case/pred0Pn: E1 => x; case/andP => Hdx Hx.
apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP => y.
  by rewrite setE; move/eqP->; apply/kerP => z; rewrite mul1g.
move/kerP; move /(_ (f x)); rewrite invIm //.
rewrite /invm injmf /repr; case pickP; last first.
  by move=> *; case/negP: Hdx; apply/eqP.
move=> t; rewrite /= setE; case/andP=> Ht Ht1 He.
by rewrite -(mulgK (f x) y) -(eqP Ht1) He mulgV set11.
Qed.

Lemma invm_dom: dom invfH  = f @: H.
Proof.
rewrite /dom.
apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP => y; last first.
  case/imsetP=> z Hz ->; case Ez: (1 == z); apply/setUP.
    by rewrite -(eqP Ez) morph1; left; apply/kerP=> t; rewrite mul1g.
  right; rewrite setE; rewrite /invm injmf /repr; case pickP; last first.
    by move/(_ z); rewrite /= setE Hz eq_refl.
  move=> t; rewrite /= setE; case/andP=> Ht; move/eqP=> Hf.
  by move/injmP: injmf; move/(_ _ _ Ht Hz Hf)=> ->; rewrite eq_sym Ez.
rewrite setE; case/orP.
  by rewrite kert_invm setE; move/eqP->; apply/imsetP; exists (1: elt1); rewrite ?group1 // morph1.
rewrite setE /invm injmf/repr; case pickP; last by move=> _; case/negP.
by move=> z; rewrite /= setE; case/andP=> Hz; move/eqP=> <- _; apply/imsetP; exists z.
Qed.

Lemma invm_group: group_set (dom invfH).
Proof.
apply/groupP; split; first by rewrite setE group1.
move=> x y; rewrite !invm_dom.
case/imsetP=> x1 Hx1 ->; case/imsetP=> y1 Hy1 ->.
rewrite -morphM; first by apply/imsetP; exists (x1 * y1); rewrite // groupM.
  by move: (injm_dom injmf); move/subsetP; move/(_ x1) => ->.
by move: (injm_dom injmf); move/subsetP; move/(_ y1) => ->.
Qed.

Lemma invmI: forall x, x \in dom invfH -> f (invfH x) = x.
Proof.
move=> x; rewrite invm_dom; case/imsetP=> y Hy ->.
rewrite /invm injmf /repr; case pickP; last first.
  by move/(_ y); rewrite /= setE Hy eq_refl.
by move=> z; rewrite /= setE; case/andP=> _; move/eqP.
Qed.

Lemma invmM : {in dom invfH &, {morph invfH : x y / x * y}}.
Proof.
move=> x y; rewrite invm_dom.
case/imsetP=> x1 Hx1 ->; case/imsetP=> x2 Hx2 ->.
by rewrite -morphM ?invIm //; first (by rewrite groupM); apply (subsetP (injm_dom injmf)).
Qed.

Definition invm_morph := Morphism invm_group invmM.

End InverseMorphism.

Section Isomorphisms.

Open Scope group_scope.

Variables elt1 elt2 elt3 : finGroupType.
Variables (H : {group elt1}) (G : {group elt2}) (K : {group elt3}).

Lemma isog_refl : isog H H.
Proof.
exists {idm elt1 as morphism _ _}=> /=; rewrite /isom; apply/andP; split.
  apply/eqP; apply/setP=> x; apply/imsetP/idP; rewrite /idm; first by case=> y Hy ->.
  by move=> Hx; exists x.
by apply/injmP; move=> x y Hx Hy /=; rewrite /idm.
Qed.

Lemma isog_card: isog H G -> #|H| = #|G|.
Proof.
case=> f; case/andP; move/eqP=> <- HH.
apply sym_equal; apply card_dimset.
by apply/injmP.
Qed.

Lemma isog_triv: isog H G -> trivg H = trivg G.
Proof.
move => Hi; case Gt: (trivg G).
  rewrite [trivg _](eq_subset_r (setE (pred1 1))) subset_disjoint disjoint_sym.
  have:= isog_card Hi; move/trivgP: Gt => ->; rewrite (cardD1 1) group1 cards1.
  by move/eqP.
apply/negP=> Gh; case/negP: Gt.
rewrite [trivg _](eq_subset_r (setE (pred1 1))) subset_disjoint disjoint_sym.
move: (isog_card Hi); move/trivgP: Gh=> ->; rewrite (cardD1 1 (mem G)) group1.
by rewrite cards1; move/eqP; rewrite eq_sym.
Qed.

Lemma isog_sym : isog H G -> isog G H.
Proof.
move=> Hi; case: (Hi)=> f; case/andP=> Him Hf.
case Th: (trivg H); move/idP: Th=> Th.
  by apply: trivial_isog; rewrite // -(isog_triv Hi).
exists (invm_morph Hf Th); apply/andP; split=> /=; rewrite -(eqP Him).
  apply/eqP; apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP=> y.
    by case/imsetP=> t; case/imsetP=> u Hu ->; rewrite invIm // => ->.
  move=> Hy; apply/imsetP; exists (f y); last by rewrite invIm.
  by apply/imsetP; exists y.
apply/(@injmP _ _ (invm_morph Hf Th))=> /= x1 y1.
by case/imsetP=> x2 Hx2 ->; case/imsetP=> y2 Hy2 ->; rewrite !invIm=> // ->.
Qed.

Lemma isog_trans: isog H G -> isog G K -> isog H K.
Proof.
move=> Hi; case: (Hi)=> f; case/andP=> Him Hf.
move=> Hj; case: (Hj)=> g; case/andP=> Gim Hg.
exists (morph_c f g); apply/andP; split.
  rewrite -(eqP Gim) -(eqP Him).
  apply/eqP; apply/setP => x; apply/imsetP/imsetP; case => y.
    by move=> Hy ->; exists (f y) => //; apply/imsetP; exists y.
  by case/imsetP=> z Hz -> ->; exists z.
apply/injmP => x y Hx Hy HH.
move/injmP: Hf; move/(_ x  y) => -> //.
move/injmP: Hg; move/(_ (f x) (f y)) => -> //; rewrite -(eqP Him).
  by apply/imsetP; exists x.
by apply/imsetP; exists y.
Qed.

Lemma isog_simpl: isog H G -> simple H -> simple G.
Proof.
move=> HH; move: {HH}(isog_sym HH).
case=> f; case/andP => Hf Hf1.
move/simpleP => HH; apply/simpleP => K1 Hk Knorm.
have Hki: group_im f K1 \subset H.
  rewrite /group_im /= -(eqP Hf).
  apply/subsetP => x; case/imsetP => y Ky ->.
  by apply/imsetP; exists y => //; apply: (subsetP Hk).
have HKinorm: group_im f K1 <| H.
  move/normalP: Knorm => Hk2.
  apply/normalP => x /=; rewrite -(eqP Hf).
  case/imsetP => y Gy ->.
  rewrite -!imset_conj; first by rewrite (Hk2 _ Gy).
    by apply: (subset_trans Hk); apply: injm_dom Hf1.
  by apply: (subsetP (injm_dom Hf1)).
case (HH _ Hki HKinorm) => HH1; [left | right]; first last.
  apply/setP; apply/subset_eqP; rewrite Hk; apply/subsetP=> g Hg.
  have: f g \in H by rewrite -(eqP Hf); apply/imsetP; exists g.
  rewrite -HH1; case/imsetP => g1 Hg1.
  move/injmP: Hf1 => HH2 Hi.
  by rewrite (HH2 _ _ Hg _ Hi) ?inE //= (subsetP Hk).
apply/setP; apply/subset_eqP; apply/andP; split;
    apply/subsetP => z; rewrite setE; last first.
  by move/eqP->; exact: group1.
move=> Hz.
have Hf1z: f 1 = f z.
  have: f z \in group_im f K1 by apply/imsetP; exists z.
  rewrite HH1 setE; move/eqP->.
  have: f 1 \in group_im f K1 by apply/imsetP; exists (1: elt2).
  by rewrite HH1 setE; move/eqP->.
apply/eqP; move/injmP: Hf1 => HH3.
by rewrite (HH3 _ _ _ _ Hf1z) ?inE //= (subsetP Hk).
Qed.

End Isomorphisms.

Section FirstIsomorphism.


Open Scope group_scope.

Variables (elt1 elt2 : finGroupType) (f : morphism elt1 elt2).


Notation Local D := (dom f).
Notation Local K := (group_ker f).


Variable H : {group elt1}.

Hypothesis sHD : H \subset dom f.

Lemma sHDr : H \subset dom_(H) f.
Proof. by apply/subsetP=> x Hx; apply/setIP; rewrite ?(subsetP sHD). Qed.


Notation Local fbar := (mquo f (ker_(H) f)).

Lemma first_isom : isog (H / (ker_(H) f)) (f @: H).
Proof.
rewrite /isog; exists {fbar as morphism _ _}; apply/andP=> /=; split.
  apply/eqP; apply/setP; apply/subset_eqP.
  apply/andP; split; apply/subsetP=> x; case/imsetP=> y.
    case/quotientP=> z=> [[Hz Nz ->]] ->.
    by apply/imsetP; exists z; rewrite ?factor_mquo_norm //= (subset_ker_r f).
  move=> Hy ->; apply/imsetP=> /=; exists (coset_of (ker_(H) f) y).
    apply/quotientP; exists y.
    rewrite Hy (subsetP (normal_ker_r _ _)) ?(subsetP sHDr) //.
  rewrite factor_mquo_norm //= ?(subset_ker_r f) // (subsetP (normal_ker_r _ _)) //.
  by rewrite (subsetP sHDr).
apply/injmP=> xbar ybar; case/quotientP=> [x [Dx Nx ->]] {xbar}.
case/quotientP=> [y [Dy Ny ->]] {ybar} /=.
rewrite !factor_mquo_norm //= ?(subset_ker_r f) // => Heq.
apply: val_inj; rewrite /= !set_of_coset_of Nx Ny.
apply rcoset_trans1; apply/rcosetP; exists (y * x^-1) => /= ; last by gsimpl.
apply/setIP; apply/andP; rewrite groupM ?groupV // andbT.
apply/kerMP; rewrite ?groupM ?groupV ?(subsetP sHD) // morphM ?groupV ?(subsetP sHD) //.
by rewrite -Heq morphV ?mulgV ?(subsetP sHD).
Qed.

End FirstIsomorphism.


Section SecondIsomorphism.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : group elt).

Hypothesis nKH : K <| H.

Notation Local f := (coset_of K).

Lemma second_isom : isog (H / (K :&: H)) (H / K).
Proof.
rewrite -[K :&: H]/(set_of_group _).
rewrite -(set_of_group_inj (ker_coset_of_loc nKH))  /=.
by apply: first_isom; apply: subset_trans _ (subset_dom_coset K).
Qed.


Lemma quotient_mulg : (H :*: K) / K = H / K.
Proof.
rewrite -norm_smulC //.
apply/setP=> Kx; apply/imsetP/imsetP=> [] [x Hx ->{Kx}].
  case/smulgP: Hx=> k h Kk Hh->; exists h => //; apply: kerP.
  by rewrite (subsetP (subset_ker_coset _)).
by exists x=> //; rewrite (subsetP (smulg_subr _ (group1 K))) ?Hx.
Qed.


Lemma weak_second_isom : isog (H / (K :&: H)) ((H :*: K) / K).
Proof. rewrite quotient_mulg; exact: second_isom. Qed.


End SecondIsomorphism.

Section ThirdIsomorphism.

Variables (elt : finGroupType) (G H K : group elt).

Hypothesis sHK : H \subset K.
Hypothesis sKG : K \subset G.
Hypothesis nHG : H <| G.
Hypothesis nKG : K <| G.

Theorem third_iso  : isog ((G / H) / (K / H)) (G / K).
Proof.
have sHker: H \subset ker (coset_of K).
  by rewrite (subset_trans sHK) ?subset_ker_coset.
have sGdom: G \subset dom (coset_of K).
  by rewrite (subset_trans nKG) ?subset_dom_coset.
have sGHdom: G / H \subset dom (mquo (coset_of K) H).
  apply: subset_trans (subset_dom_mquo _ _); exact: subset_imset.
have KH_ker : K / H = ker_(G / H) (mquo (coset_of K) H).
  rewrite ker_mquo_loc // ker_coset_of_loc //; congr (_ / H).
  apply/setP=> x; rewrite setE.
  by case Kx: (x \in K); rewrite //= (subsetP sKG).
rewrite -[K / H]/(set_of_group _) {KH_ker}(set_of_group_inj KH_ker) /=.
have -> : G / K = mquo (coset_of K) H @: G / H by rewrite factor_mquo_iim.
exact: first_isom.
Qed.

End ThirdIsomorphism.

Unset Implicit Arguments.