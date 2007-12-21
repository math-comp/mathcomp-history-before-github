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
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section Normal.

Open Scope group_scope.

Variables (elt: finGroupType) (H K: setType elt).

(*Hypothesis subset_HK: subset H K.*)


(********************************************************************)
(*              Definition of a normal set                          *)
(*    H is normal in K iff xHx^-1 = H forall x in K                 *)
(*    it is sufficient that xHx^¯1 is included in H                 *)
(*    since both sets have same cardinal                            *)
(********************************************************************)



Definition normal := subset K (normaliser H).


Theorem normalP:
  reflect (forall x, K x -> (H :^ x) = H) normal.
Proof.
apply: (iffP idP).
  by move/subsetP=> H1 x Kx; apply norm_sconjg; apply H1.
  by move=> H1; apply/subsetP=> x Kx; rewrite/normaliser s2f H1 //; apply subset_refl.
Qed.

End Normal.

Notation "H '<|' K" := (normal H K)(at level 50):group_scope.


Section NormalProp.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : group elt).

Hypothesis subset_HK : subset H K.
Hypothesis nHK : H <| K.

Theorem normal_subset: forall L : group elt, subset L K ->  H <| L.
Proof. move=> L HLK; exact: subset_trans HLK _. Qed.

Theorem norm_normal: H <| (normaliser H).
Proof. exact: subset_refl. Qed.

End NormalProp.


Section Simple.

Variables (elt : finGroupType) (H : setType elt).

Definition  simple :=
  forallb K : setType elt,
 [ ==> (group_set K) , (subset K H) , (K <| H) => (K == {: 1} ) || (K == H)].

Theorem simpleP:
 reflect
 (forall K: group elt, subset K H -> K <| H -> K =1 set1 1 \/ K =1 H)
 simple.
Proof.
apply: (iffP idP).
  move/forallP => Hf K Hk1 Hk2.
  by move: (Hf K); rewrite set_of_groupP Hk1 Hk2; case/orP; move/eqP => ->;
    [left|right] => // z; rewrite s2f.
move=> Hf; apply/forallP => K; apply/implyP => E0; apply/implyP => E1; apply/implyP => E2.
by apply/orP; case (Hf (Group E0)) => //= HH; [left | right];
   apply/eqP; apply/isetP => // z; rewrite HH s2f.
Qed.

End Simple.



(********************************************************************)
(*       Cosets are right cosets of elements in the normaliser      *)
(********************************************************************)


Section Cosets.

Open Scope group_scope.

Variables (elt : finGroupType) (A : setType elt).

Definition coset_set := image (rcoset A) (normaliser A).

CoInductive coset : Type := Coset of eq_sig coset_set.

Definition sig_of_coset u := let: Coset v := u in v.

Remark sig_of_cosetK : cancel sig_of_coset Coset. Proof. by case. Qed.

Canonical Structure coset_eqType := EqType (can_eq sig_of_cosetK).
Canonical Structure coset_finType := FinType (can_uniq sig_of_cosetK).

Coercion set_of_coset u := val (sig_of_coset u) : setType elt.

Lemma set_of_coset_inj : injective set_of_coset.
Proof. exact: inj_comp (@val_inj _ _) (can_inj sig_of_cosetK). Qed.

End Cosets.

Prenex Implicits coset.
(********************************************************************)
(*  The domain of a morphism is inferred from the values of the     *)
(*  function. A morphism is constant 1 outside its domain           *)
(********************************************************************)

Section MorphismDefs.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType)(f : elt1 -> elt2).

(* Kernel *)
Definition ker  := {x, subset elt1 {y: elt1, f (x * y) == f y}}.

(* Domain of the morphism *)
Definition dom := ker :|: {x, f x != 1}.

(* Preimage *)
Definition preim (B : setType elt2) := (f @^-1: B) :&: dom.

(* Being a trivial morphism *)
Definition trivm := set0b (fun z => f z != 1).

(* Quotient morphism *)
Definition mquo (A : setType elt1)(Ax : coset A):=
  if subset A ker then f (repr Ax) else 1.

(* Being a morphism injective on A*)
Definition injm (A : setType elt1) := subset (A :\ 1) (dom :\: ker).

(* Being an isomorphism between A and B *)
Definition isom (A : setType elt1)(B : setType elt2) := 
  (f @: A == B) && injm A.

(* The inverse morphism of an injective morphism *)
Definition invm  A y :=
  if injm A then repr {x, A x && (f x == y)} else 1.

Definition idm (x : elt1) := x.

End MorphismDefs.

Implicit Arguments mquo [elt1 elt2].
Implicit Arguments idm [].

Prenex Implicits dom ker preim trivm mquo injm isom invm.


Notation "'ker_' ( G ) f" := (ker f :&: G)
  (at level 10, format "'ker_' ( G )  f") : group_scope.

Notation "'dom_' ( G ) f" := (dom f :&: G)
  (at level 10, format "'dom_' ( G )  f") : group_scope.

Notation "'preim_' ( G ) f B" := ((f @^-1: B) :&: G)
  (at level 10, format "'preim_' ( G )  f  B") : group_scope.

Section GenericProps.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType)(f : elt1 -> elt2).

Lemma kerP : forall x, reflect (forall y, f (x * y) = f y) (ker f x).
Proof.
move=> x; apply: (iffP idP); rewrite s2f.
   by move/subsetP=> Kx y; apply/eqP; move: (Kx y); rewrite s2f=> ->.
by move=> Hx; apply/subsetP=> y _; rewrite s2f; rewrite Hx.
Qed.

(* The kernel of an arbitrary function is a group *)
Lemma group_set_ker : group_set (ker f).
Proof.
apply/andP; split; first by apply/kerP=> x; rewrite mul1g.
apply/subsetP=> x; case/smulgP=> y z; move/kerP=> Hy; move/kerP=> Hz ->.
by apply/kerP=> t; rewrite -mulgA Hy Hz.
Qed.

Canonical Structure group_ker := Group group_set_ker.

Lemma dom_k : forall x, ker f x -> dom f x.
Proof. by move=> x kx; rewrite s2f; apply/orP; left. Qed.

Lemma dom_nu : forall x, f x != 1 -> dom f x.
Proof. by move=> x kx; rewrite s2f; apply/orP; right; rewrite s2f. Qed.


Lemma out_dom : forall x, dom f x = false -> f x = 1.
Proof.
move=> x; rewrite s2f; case/norP=> _; rewrite s2f=> H1; apply/eqP.
exact (negbE2 H1).
Qed.

Lemma trivm_is_cst : trivm f -> f =1 (fun _ => 1).
Proof. by move/set0P=> Hf x; move/eqP: (Hf x). Qed.

Lemma trivm_ker :  trivm f -> ker f = elt1.
Proof. 
move/trivm_is_cst=> Hf; apply/isetP=> x; rewrite !s2f; apply/subsetP=> y _.
by rewrite s2f !Hf.
Qed.

Lemma trivm_dom : trivm f -> dom f = elt1.
Proof.
by move/trivm_ker=> Hf; apply/isetP=> u; rewrite s2f Hf !s2f.
Qed.


Lemma subset_preim : forall A B : setType elt2,
  subset A B -> subset (preim f A) (preim f B).
Proof.
move=> A B  HAB; apply/subsetP=> x; rewrite 2!s2f; case/andP=> Hfx Dfx.
by rewrite s2f Dfx s2f (subsetP HAB).
Qed.

Lemma preimP : forall (A: setType _) x, 
  reflect (A (f x) /\ dom f x) (preim f A x).
Proof. move=> A x; rewrite !s2f; exact: andP. Qed.


Lemma subset_preim_dom : forall A : setType elt2,
  subset (preim f A) (dom f).
Proof. by move=> A; apply/subsetP=> x; case/preimP. Qed.


Lemma injm_dom : forall A : setType elt1, (injm f A) -> subset A (dom f).
Proof.
move=> A; move/subsetP=> H1; apply/subsetP=> x Ax.
case Hx: ((A :\ 1) x); first by move/H1: Hx; rewrite s2f; case/andP.
by move:Hx; rewrite s2f Ax andbT; move/eqP=> <-; rewrite dom_k ?group1.
Qed.

Lemma subset_ker_r : forall A : setType elt1,
  subset (ker_(A) f) (ker f).
Proof. by move=> A; apply/subsetP=> u; case/isetIP. Qed.

Lemma ker_r_dom : ker_(dom f) f = ker f.
Proof.
apply/isetP; apply/subset_eqP; rewrite subset_ker_r /=; apply/subsetP=> x Kx.
by apply/isetIP; rewrite Kx dom_k.
Qed.

Lemma subset_dom_r : forall A : setType elt1,
  subset (dom_(A) f) (dom f).
Proof. by move=> A; apply/subsetP=> x; case/isetIP. Qed.


End GenericProps.




(* Definition of the morphism structure *)
Section Morphisms.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType).

Structure morphism : Type := Morphism {
  mfun :> elt1 -> elt2;
  group_set_dom : group_set (dom mfun);
  morphM : forall x y, dom mfun x -> dom mfun y ->
           mfun (x * y) = mfun x * mfun y
}.

Variable f : morphism.

Canonical Structure mdom := Group (group_set_dom f).

Lemma morph1 : f 1 = 1.
Proof. by apply (mulg_injl (f 1)); rewrite -morphM ?group1 // !mulg1. Qed.

Lemma morphV : forall x, dom f x -> f x^-1 = (f x) ^-1.
Proof.
move=> x MDx; apply (mulg_injl (f x)); rewrite mulgV -morphM ?groupV //.
by rewrite mulgV morph1.
Qed.

Lemma morphJ : forall x y, 
  dom f x -> dom f y -> f (x ^ y) = (f x) ^ (f y).
Proof.
by move=> x y Dx Dy; rewrite /conjg !morphM ?morphV // ?groupM ?groupV.
Qed.

Lemma morphE : forall n x,
 dom f x -> f (x ** n) = (f x) ** n.
Proof.
move=> n.
elim: n => [x Dx| n Hrec x Dx]; first by rewrite !gexpn0 morph1.
by rewrite !gexpnS morphM ?groupE ?Hrec.
Qed.

Lemma mker: forall x, ker f x -> f x = 1.
Proof.
move=> x; rewrite s2f; move/subsetP=> Hx; move: (Hx 1); rewrite s2f mulg1=> H1.
by rewrite (eqP (H1 _)) ?group1 // morph1.
Qed.

(* The kernel of a morphism is the set of elements in the domain *)
(* that are mapped to the unit *)
Lemma kerMP : forall x, dom f x -> reflect (f x = 1) (ker f x).
Proof.
move=> x Dx; apply: (iffP idP); first exact: mker.
rewrite s2f; move=> Hx; apply/subsetP=> y _; rewrite s2f.
case Dy: (dom f y); first  by  rewrite morphM // Hx mul1g.
by rewrite (out_dom Dy) (@out_dom _ _ f (x *y)) // groupMl.
Qed.


Lemma ker_rcoset : forall x y, dom f x -> dom f y ->
  reflect (exists k, (ker f k)/\ (x = k * y)) (f x == f y).
Proof.
move=> x y dx dy; apply: (iffP eqP).
  move=> Exy; exists (x * y^-1); split; last by gsimpl.
  by apply/kerMP; rewrite ?morphM // ?Exy ?morphV ?mulgV ?groupM ?groupV.
by case=> k [Kk ->]; rewrite morphM ?(dom_k Kk) // mker // mul1g.
Qed.

Lemma iimage_smul : forall A B : setType elt1,
 subset A (dom f) -> subset B (dom f)->
 f @: (A :*: B) = (f @: A) :*: (f @: B).
Proof.
move=> A B DomA DomB; apply/isetP=> y; apply/iimageP/smulgP.
  case=> x; case/smulgP=> a b Aa Bb -> ->.
  exists (f a) (f b); [apply/iimageP; exists a|apply/iimageP; exists b|]=>//.
  by rewrite morphM // ?((subsetP DomA) a) ?(subsetP DomB).
case=> u v; case/iimageP=> a Aa ->; case/iimageP=> b Bb -> ->.
exists (a * b); first by apply/smulgP; exists a b.
by rewrite  morphM // ?((subsetP DomA) a) ?(subsetP DomB).
Qed.

Lemma iimage_conj : forall (A : setType elt1) x, 
  subset A (dom f) -> dom f x ->  f @: (A :^ x) = (f @: A) :^ (f x).
Proof.
move=> A x DomA Domx.
rewrite !sconjg_coset !rcoset_smul !lcoset_smul -morphV //.
rewrite -(iimage_set1 f)  -!iimage_smul  // ?subset_set1 ?groupVr //.
rewrite ?iimage_smul ?(iimage_set1 f) // ?subset_set1 // ?groupV //.
apply/subsetP=> w; case/smulgP=> u v; rewrite s2f; move/eqP=> <- Av ->.
by rewrite groupM ?groupV // (subsetP DomA).
Qed.

Section MorphIm.

Variable H : group elt1.

Lemma im_group_dom : f @: H = f @: (H :&: (dom f)).
Proof.
apply/isetP=> u.
apply/iimageP/iimageP; last by case=> x; case/isetIP=> Hx Dx ->; exists x.
case=> x Hx ->; case domx : (dom f x); first by exists x=> //; apply/isetIP.
exists (1:elt1); first by apply/isetIP; split; rewrite group1.
case Ex : (f x == 1); first by rewrite (eqP Ex) morph1.
have: dom f x == true by  apply/eqP; apply/isetUP; rewrite s2f Ex /=; right.
by rewrite domx; move/eqP=> *.
Qed.

Lemma group_set_im : group_set (f @: H).
Proof.
rewrite im_group_dom /group_set; apply/andP; split.
  by apply/iimageP; exists (1:elt1); rewrite ?group1 // -morph1.
apply/subsetP=> t; case/smulgP=> u v.
case/iimageP=> x; case/isetIP=> Hx Dx ->.
case/iimageP=> y; case/isetIP=> Hy Dy -> ->.
apply/iimageP; exists (x * y); last by rewrite morphM.
by apply/isetIP; rewrite !groupM.
Qed.

Canonical Structure group_im := Group group_set_im.

End MorphIm.

Section MorphPreIm.

Lemma preimUker : forall A : setType elt2,
  A 1 -> preim f A = (f @^-1: (A :\ 1)) :|: (ker f).
Proof.
move=> A A1; apply/isetP=> u; apply/isetIP/isetUP.
  rewrite s2f => Hu; apply/orP; case ku : (ker f u); rewrite // ?orbT //.
  by rewrite orbF !s2f; case: Hu => ->; rewrite andbT s2f ku /= s2f eq_sym.
case; first by do 3 rewrite s2f; case/andP=> Hu ->; rewrite dom_nu 1?eq_sym.
by move=> ku; rewrite dom_k // s2f (kerMP _ ku) ?A1 // dom_k.
Qed.

Variable H : group elt2.


Lemma preim_group : group_set (preim f H).
Proof.
rewrite /preim /group_set; do 2 rewrite s2f; rewrite morph1 !group1 /=.
apply/subsetP=> u; case/smulgP=> x y; case/isetIP; rewrite s2f.
move=> Hx1 dx; case/isetIP; rewrite s2f=> Hy1 dy ->.
by apply/isetIP; apply/andP; rewrite s2f morphM ?groupM.
Qed.

Canonical Structure preim_group_struct := Group preim_group.

End MorphPreIm.

Lemma morph_norml_im : forall K : group elt1,
subset K (dom f) ->  K <| (dom f) -> (f @: K) <| (f @: (dom f)).
Proof.
move=> K sKD; move/normalP=> HnK; apply/normalP=> x.
by case/iimageP=> u Hu ->; rewrite -iimage_conj ?HnK.
Qed.

Lemma normal_ker : (ker f) <| (dom f).
Proof.
apply/normalP=> x Dx; apply/isetP=> y; apply/idP/idP.
  rewrite s2f; move=> Kxy.
  have Dy: (dom f y) by rewrite -(@groupJr _ _ y x^-1) ?groupV // dom_k //.
  rewrite s2f; apply/subsetP=> z _ ; rewrite s2f.
  suff : ker f y.
    by rewrite s2f; move/subsetP=> ky; move: (ky z); rewrite s2f; auto.
  apply/kerMP=> //; apply (conjg_inj (f (x^-1))).
  rewrite -morphJ ?groupV // conj1g; move/kerMP: Kxy=> -> //.
  by rewrite ?groupJ ?groupV.
move=> ky; have Dy : dom f y  by apply: dom_k.
rewrite s2f; apply/kerMP; rewrite ?groupJr ?groupV //.
by rewrite morphJ ?groupV //; move/kerMP: ky=> ky; rewrite ky ?conj1g.
Qed.



Lemma normal_ker_r : forall H : group elt1,
(ker_(H) f) <| (dom_(H) f).
Proof.
move=> A; apply/subsetP=> d; case/isetIP=> Dd Hd; rewrite s2f; apply/subsetP=> x; rewrite s2f.
case/isetIP=> Kxd Hxd; apply/isetIP.
have : normaliser (ker f) d by rewrite (subsetP normal_ker _).
rewrite s2f; move/subsetP; move/(_ x)=> ->; rewrite 1?s2f //.
by rewrite -(@groupJr _ _ _ d^-1) ?groupV.
Qed.


(* Being isomorphic *)
Definition isog (A : setType elt1)(B : setType elt2) :=
  exists g : morphism, isom g A B.

Lemma injmP : forall A: group elt1, reflect (dinjective A f) (injm f A).
Proof.
move=> A; apply: (iffP idP) => [H1 x y Ax Ay Hxy | IfA].
  case HxyV : ((A :\ 1) (x * y ^-1)).
    move/(subsetP H1): HxyV; rewrite s2f andbC.
    case/andP=> Dxy; case/(kerMP Dxy); apply: (mulg_injr (f y)).
    by rewrite mul1g -morphM ?mulgKv // (subsetP (injm_dom H1)).
  move: HxyV; rewrite -{2}(mulgKv y x) s2f groupM ?groupV // andbT.
  by move/eqP=> <-; rewrite mul1g.
apply/subsetP=> x; rewrite s2f; case/andP=> Hx1 Ax.
case Hfx1: (f x != 1).
  have Dx: dom f x by exact: dom_nu.
  rewrite s2f Dx andbT; apply/(kerMP Dx); exact/eqP.
by case/eqP: Hx1; apply: IfA => //; rewrite morph1; move/eqP: Hfx1.
Qed.



End Morphisms.

Prenex Implicits isog.

Section IdMorphism.

Variable elt : finGroupType.

Notation Local elt_id := (idm elt).

Lemma dom_id : dom elt_id = elt.
Proof.
apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP=> x //.
move=> _; case Ix : (x == 1); [rewrite dom_k // | rewrite dom_nu //].
  by  apply/kerP=> y; rewrite (eqP Ix) mul1g.
by rewrite Ix /idm.
Qed.

Lemma group_set_dom_id : group_set (dom elt_id).
Proof. 
by rewrite dom_id; apply/andP; split => //; apply/subsetP=> u. 
Qed.

Lemma idmorphM : forall x y, 
  dom elt_id x -> dom elt_id y -> 
  elt_id (x * y) = (elt_id x) * (elt_id y).
Proof. by rewrite /idm. Qed.

Canonical Structure morph_id := Morphism group_set_dom_id idmorphM.

End IdMorphism.


Section TrivMorphism.


Variables (elt1 elt2 : finGroupType).

Notation Local triv := (fun x : elt1 => (1 : elt2)).

Lemma dom_triv_morph : dom triv = elt1.
Proof.
apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP=> x //.
by move=> _; rewrite dom_k //; apply/kerP.
Qed.

Lemma group_set_triv_morph : group_set (dom triv).
Proof.
by rewrite dom_triv_morph; apply/andP; split => //; apply/subsetP.
Qed.


Lemma trivmorphM : forall x y, dom triv x -> dom triv y ->
  triv (x * y) = (triv x) * (triv y).
Proof. by move=> x y _ _ /=; rewrite mulg1. Qed.

Canonical Structure triv_morph := Morphism group_set_triv_morph trivmorphM.


Lemma iim_trivm : forall (A : setType elt1) x, A x -> triv @: A = {: 1}.
Proof.
move=> A x Ax; apply/isetP=> y; rewrite s2f; apply/idP/eqP; first by case/iimageP.
by move=> <-; apply/iimageP; exists x.
Qed.

Lemma trivial_isog : forall (A : group elt1) (B : group elt2),
  trivg A -> trivg B -> isog A B.
Proof.
move=> A B; move/trivgP=> ->; move/trivgP=> ->.
exists triv_morph; apply/andP; split.
  by rewrite (@iim_trivm _ 1) ?s2f //.
by apply /injmP=> x y /=; rewrite !s2f; move/eqP=> ->; move/eqP.
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
by move=> h x Hx; apply/eqP=> Hhx; rewrite /comp Hhx morph1 eq_refl in Hx.
Qed.

Lemma trivm_cn : forall h : elt1 -> elt2,
  ~~ trivm (g \o h) -> (~~ trivm g) /\ (~~ trivm h).
Proof.
move=> h; case/set0Pn=> x Hx; split; apply/set0Pn; first by exists (h x).
by exists x; apply morph_nuc.
Qed.


Lemma subset_ker_c : subset (preim f (ker g)) (ker gof).
Proof.
apply/subsetP=> x; case/preimP; move/kerP=> Hx Dfx.
apply/kerP=> y; rewrite /comp.
case Dfy : (dom f y); first by rewrite morphM.
by congr (g _); rewrite out_dom ?groupMl // out_dom.
Qed.


Lemma ker_c : ~~ trivm gof -> ker gof = (preim f (ker g)).
Proof.
case/set0Pn=> x Hnt; apply/isetP; apply/subset_eqP.
rewrite subset_ker_c andbT; apply/subsetP=> y; move/kerP=> Hy.
have Hyx : gof (y * x) != 1 by rewrite Hy.
have Dfx : dom f x by rewrite dom_nu // morph_nuc.
have Dfy : dom f y by rewrite -(groupMr _ Dfx) dom_nu // morph_nuc.
rewrite s2f Dfy andbT s2f; apply/kerMP.
  by rewrite -(@groupMr _ _ (f x)) -?morphM // dom_nu.
by rewrite -(mulg1 y) [g _]Hy /comp !morph1.
Qed.


Lemma subset_dom_c : subset (preim f (dom g)) (dom gof).
Proof.
apply/subsetP=> x; case/preimP; case/isetUP; last first.
  by rewrite s2f=> ? _; exact: dom_nu.
move=> Kx Dx; apply dom_k; apply: (subsetP subset_ker_c); exact/preimP.
Qed.



Lemma dom_c : ~~ trivm gof -> dom gof = (preim f (dom g)).
Proof.
move=> Hnt; apply/isetP; apply/subset_eqP; rewrite subset_dom_c andbT.
apply/subsetP=> x; case/isetUP.
  rewrite ker_c //; apply: (subsetP (subset_preim _ _)).
  apply/subsetP; exact: dom_k.
by rewrite 3!s2f => Hx; rewrite !dom_nu // morph_nuc.
Qed.

Lemma group_set_dom_c : group_set (dom gof).
Proof.
case Hnt: (trivm gof); last by rewrite dom_c ?Hnt ?set_of_groupP.
rewrite trivm_dom //; apply/groupP; split=> *; exact: isetAP.
Qed.

Lemma morphMc : forall x y, 
  dom (gof) x -> dom (gof) y ->
  (gof) (x * y) = ((gof) x) * ((gof) y).
Proof.
case Ht: (trivm gof) => [] x y; last move/negbT: Ht => Hnt.
  by rewrite !(trivm_is_cst Ht) mulg1.
rewrite !(dom_c Hnt); case/preimP=> [Hgx Hx]; case/preimP=> [Hgy Hy].
by rewrite /comp !morphM.
Qed.

Canonical Structure morph_c := Morphism group_set_dom_c morphMc.


Lemma ker_c_loc : forall G : group elt1,
  subset G (dom f) -> subset (f @: G) (dom g) ->
  ker_(G) gof = (preim f (ker_(f @: G) g)) :&: G.
Proof.
move=> G sGd sfGd; apply/isetP=> x; rewrite 2![(_ :&: _) x]s2f 2![_ && G x]andbC. 
case Gx : (G x)=> //=; apply/idP/idP.
  move=> Kx; rewrite 2!s2f (subsetP sGd) // andbT; apply/isetIP.
  split; last by apply/iimageP; exists x.
  apply/kerMP; rewrite ?(subsetP sfGd) //; first by  apply/iimageP; exists x.
  by apply: (kerMP _ Kx); rewrite dom_k.
rewrite s2f; case/andP; rewrite s2f; case/isetIP=> Kx _ Dx.
by rewrite (subsetP subset_ker_c) // s2f Dx andbT s2f.
Qed.



End MorphismComposition.



(* We build a new (canonical) structure of groupType for cosets. *)
(* This group type is the largest possible quotient N (H) / H    *)
Section CosetGroupType.

Open Scope group_scope.

Variable elt : finGroupType. 

Lemma coset_set_unit :forall A : setType elt, coset_set A A.
Proof. 
by move=> A; apply/imageP;  exists (1:elt); rewrite ?group1 ?rcoset1. 
Qed.

Definition coset_unit(A : setType elt) := 
  Coset (EqSig _ _ (coset_set_unit A)).

Variable H : group elt.

Notation Local N := (normaliser H).

Lemma coset_set_mul : forall Hx Hy : coset H, coset_set H (Hx :*: Hy).
Proof.
rewrite /set_of_coset => [] [[Hx nHx]] [[Hy nHy]] /=.
case/imageP: nHx => [x Nx ->{Hx}]; case/imageP: nHy => [y Ny ->{Hy}].
by apply/imageP; exists (x * y); rewrite ?groupM // rcoset_mul.
Qed.

Definition coset_mul Hx Hy := Coset (EqSig _ _ (coset_set_mul Hx Hy)).

Lemma coset_set_inv : forall Hx : coset H, coset_set H (Hx :^-1).
Proof.
rewrite /set_of_coset => [] [[A]] /=; move/imageP=>[x Nx ->{A}].
by apply/imageP; exists x^-1; rewrite ?groupV // -sinvg_lcoset norm_rlcoset.
Qed.

Definition coset_inv Hx := Coset (EqSig _ _ (coset_set_inv Hx)).


Lemma coset_unitP : forall Hx, coset_mul (coset_unit H) Hx = Hx.
Proof.
move=> [[Hx nHx]]; apply: set_of_coset_inj; do 3 rewrite /set_of_coset /=.
by case/imageP: nHx => [x Nx ->{Hx}]; rewrite !rcoset_smul smulgA smulgg.
Qed.

Lemma coset_invP : forall Hx, coset_mul (coset_inv Hx) Hx = coset_unit H.
Proof.
move=> [[Hx nHx]]; apply: set_of_coset_inj; do 3!rewrite /set_of_coset /=.
case/imageP: nHx => [x Nx ->{Hx}].
rewrite {1}norm_rlcoset // sinvg_lcoset ?rcoset_mul ?groupV // mulVg.
by rewrite  rcoset1.
Qed.


Lemma coset_mulP : forall Hx Hy Hz,
  coset_mul Hx (coset_mul Hy Hz) = coset_mul (coset_mul Hx Hy) Hz.
Proof.
move=> [[Hx nHx]] [[Hy nHy]] [[Hz nHz]]; apply: set_of_coset_inj.
by do 3!rewrite /set_of_coset /=;  rewrite smulgA.
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

Definition coset_of (A : setType elt) x := 
  if insub (coset_set A) (A :* x) is Some u then Coset u 
    else (coset_unit A).

Variable H : group elt.

Notation Local N := (normaliser H).

Lemma coset_set_rcoset : forall x,  coset_set H (H :* x) = N x.
Proof.
move=> x; apply/imageP/idP=> [[y Ny Hy]|]; last by exists x.
move: Ny; rewrite !s2f !sconjg_coset -[_ *: H]sinvgK sinvg_lcoset invgK.
rewrite -Hy -{1}[x]invgK -sinvg_lcoset sinvgK !lcoset_smul !rcoset_smul.
by rewrite -!smulgA -!rcoset_smul Hy.
Qed.

(*
Lemma set_of_coset_of : forall x,
  coset_of H x = if N x then H :* x else H :> setType _.
*)
Lemma set_of_coset_of : forall x,
  coset_of H x = (if N x then H :* x else H) :> setType _.
Proof.
move=> x; rewrite -coset_set_rcoset /coset_of.
by case insubP => [u -> <- //|]; move/negbET->.
Qed.

Lemma coset_ofN : forall x, N x -> coset_of H x = H :* x :> setType _.
Proof. by move=> x; rewrite set_of_coset_of => ->. Qed.

Lemma coset_of_id : forall x, H x -> coset_of H x = 1.
Proof.
move=> x Hx; apply: set_of_coset_inj; rewrite coset_ofN ?rcoset_id //.
exact: (subsetP (norm_refl _)).
Qed.


Lemma coset_of_idr : forall x, 
 N x -> coset_of H x = 1 -> H x.
Proof.
move => x Hx H1 /=.
change ((H: setType _) x).
rewrite -(rcoset1 H) rcoset_sym.
move: (coset_ofN Hx); rewrite H1 => <-.
by rewrite group1.
Qed.


Lemma coset_ofV : forall x, coset_of H (x ^-1) = (coset_of H x) ^-1.
Proof.
move=> x; apply: set_of_coset_inj.
rewrite {2}/set_of_coset /= !set_of_coset_of groupV.
case Nx: (N x); last by rewrite sinvG.
by rewrite -sinvg_lcoset norm_rlcoset.
Qed.

Lemma subset_ker_coset : subset H (ker (coset_of H)).
Proof.
apply/subsetP=> x Hx; apply/kerP=> y; apply: set_of_coset_inj.
have Nx := subsetP (norm_refl _) _ Hx.
rewrite !set_of_coset_of groupMl // -rcoset_mul // rcoset_id //.
by rewrite !rcoset_smul smulgA smulgg.
Qed.

Lemma nu_coset_of_norm : forall x, coset_of H x != 1 -> N x.
Proof.
move=> x; rewrite -(inj_eq (@set_of_coset_inj _ H)) set_of_coset_of.
by case: ifP; rewrite // set11.
Qed.  

Lemma ker_coset : ~~ trivm (coset_of H) -> ker (coset_of H) = H.
Proof.
case/set0Pn=> y Nty; have Hy := nu_coset_of_norm Nty.
apply/isetP; apply/subset_eqP; rewrite subset_ker_coset andbT.
apply/subsetP=> x; move/kerP=> Kx; rewrite -Kx in Nty.
move/(_ 1): Kx; rewrite mulg1 (@coset_of_id 1) //.
move/(congr1 (@set_of_coset _ _)).
rewrite {2}/set_of_coset /= coset_ofN => [<- | ].
  by apply/rcosetP; exists (1 : elt); rewrite ?mul1g.
by rewrite -(mulgK y x) groupM ?groupV // nu_coset_of_norm.
Qed.

Lemma subset_dom_coset : subset N (dom (coset_of H)).
Proof.
apply/subsetP=> x Nx; apply/isetUP; case Hx: (H x); [left | right].
  exact: (subsetP subset_ker_coset).
rewrite s2f -(inj_eq (@set_of_coset_inj _ H)) coset_ofN //.
rewrite /set_of_coset /=; apply/eqP=> dH; rewrite -dH in Hx.
by case/rcosetP: Hx; exists (1 : elt); rewrite ?mul1g.
Qed.

Lemma dom_coset : ~~ trivm (coset_of H) -> dom (coset_of H) = N.
Proof.
move=> Hnt; apply/isetP; apply/subset_eqP; rewrite subset_dom_coset andbT.
rewrite /dom ker_coset //; apply/subsetP=> x; case/isetUP.
  exact: (subsetP (norm_refl _)).
by rewrite s2f; exact: nu_coset_of_norm.
Qed.

Lemma group_set_dom_coset : group_set (dom (coset_of H)).
Proof.
case Hnt: (trivm (coset_of H)).
  by rewrite trivm_dom //; apply/groupP; split=> *; rewrite isetAP.
by rewrite dom_coset ?Hnt ?set_of_groupP.
Qed.

Lemma coset_of_morphM : forall x y,
    dom (coset_of H) x -> dom (coset_of H) y ->
  coset_of H (x * y) = (coset_of H x) * (coset_of H y).
Proof.
case Hnt: (trivm (coset_of H)) => x y.
  by rewrite !(trivm_is_cst Hnt) mulg1.
rewrite dom_coset ?Hnt // => Nx Ny; apply: set_of_coset_inj.
by rewrite {2}/set_of_coset /= !coset_ofN ?groupM // rcoset_mul.
Qed.

Lemma coset_ofE : forall n x, 
  dom (coset_of H) x -> coset_of H (x ** n) = (coset_of H x) ** n.
Proof.
case Hnt: (trivm (coset_of H)).
  by move => x y; rewrite !(trivm_is_cst Hnt) gexp1n.
elim => [| n Hrec] x Hx; first by rewrite coset_of_id // group1.
rewrite !gexpnS coset_of_morphM // ?Hrec //.
elim: n {Hrec} Hx => [| n Hrec] Hx.
  by rewrite dom_coset ?Hnt // group1.
rewrite gexpnS.
move: Hx (Hrec Hx).
rewrite !dom_coset ?Hnt // => Hx Hx1.
exact: groupM.
Qed.

Canonical Structure coset_of_morphism :=
  Morphism group_set_dom_coset coset_of_morphM.



Lemma trivm_coset_of :
  reflect (normaliser H = H) (trivm (coset_of H)).
Proof.
apply: (iffP idP); last first.
  move=> NH; apply/set0P=> x; apply/set1P; apply:set_of_coset_inj.
  by rewrite set_of_coset_of; case Nx: (normaliser H x)=> //; rewrite rcoset_id //= -1?NH.
move=> Htriv; apply/isetP; apply/subset_eqP; rewrite norm_refl andbT.
apply/subsetP=> x Nx; suff: H :* x = H by move=> <-; rewrite rcoset_refl.
by rewrite -coset_ofN // trivm_is_cst.
Qed.




Lemma ker_coset_of_loc : forall K : group elt,
  H <| K -> ker_(K) (coset_of H) = H :&: K.
Proof.
move=> K nHK.
case Htriv : (trivm (coset_of H)); last by rewrite ker_coset ?Htriv.
apply/isetP=> x; rewrite trivm_ker // !s2f /= andbC; case Kx : (K x)=> //=.
by rewrite -(trivm_coset_of Htriv) (subsetP nHK).
Qed.


Definition quotient (A B : setType elt) := (coset_of B) @: A.

Notation "A / B" := (quotient A B).

Variable K : group elt.

Lemma group_set_quotient : group_set (K / H).
Proof. exact: set_of_groupP. Qed.

Canonical Structure quotient_group := Group group_set_quotient.


Lemma quotientP : forall xbar,
  reflect (exists x, and3 (K x) (N x) (xbar = coset_of H x)) ((K / H) xbar).
Proof.
move=> xbar; apply: (iffP (iimageP _ _ _)) => [[x Kx -> {xbar}] | [x [*]]]; last by exists x.
case Nx: (N x); [by exists x | exists (1 : elt); rewrite !group1 morph1; split=> //].
by apply: set_of_coset_inj; rewrite set_of_coset_of Nx.
Qed.


Lemma set_of_coset_quotient :
  (@set_of_coset _ H) @: (K / H) = (rcoset H) @: (N :&: K).
Proof.
apply/isetP=> A; apply/iimageP/iimageP=> [[xbar Kxbar]|[x NKx]] ->{A}.
  case/quotientP: Kxbar => x [Nx Kx ->{xbar}].
  by exists x; [rewrite s2f Kx | rewrite coset_ofN].
case/isetIP: NKx => Nx Kx.
by exists (coset_of H x); [apply/iimageP; exists x | rewrite coset_ofN].
Qed.

Lemma card_quotient : H <| K -> card (K / H) = indexg H K.
Proof.
move=> sHK; rewrite -(card_iimage (@set_of_coset_inj _ H)).
rewrite set_of_coset_quotient; congr (card (_ @: s2s _)).
apply/isetP=> x; rewrite s2f andbC.
by case Kx: (K x); first exact: (subsetP sHK).
Qed.

End Quotient.

Notation "A / B" := (quotient A B) : group_scope.

Prenex Implicits coset_of quotient.

Section TrivialQuotient.

Open Scope group_scope.

Variables (elt : finGroupType) (H : group elt).

Lemma trivial_quotient : (H / H) = {: 1}.
Proof.
apply/isetP=> A; apply/quotientP/iset1P => [[x [Hx _ ->]] | <-].
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

Lemma norm_repr_coset : forall xbar : coset H, N (repr xbar).
Proof.
case=> [[Hx csHx]]; rewrite /set_of_coset /=; case/imageP: (csHx) => x Nx ->.
by case: repr_rcosetP=> z Hz; rewrite groupMr // (subsetP (norm_refl _)).
Qed.

Lemma coset_of_repr : forall xbar : coset H, coset_of H (repr xbar) = xbar.
Proof.

move=> xbar; apply: set_of_coset_inj.
rewrite set_of_coset_of norm_repr_coset /set_of_coset.
case: xbar; case=> A /=; case/imageP=> x Nx ->{A}; exact: rcoset_repr.
Qed.

Lemma cosetP : forall xbar, {x | N x & xbar = coset_of H x}.
Proof.
by move=> xbar; exists (repr xbar); rewrite ?coset_of_repr ?norm_repr_coset.
Qed.

Lemma factor_mquo_norm : subset H (ker f) -> forall x, N x -> fq (coset_of H x) = f x.
Proof.
move=> sHK x Nx; rewrite /mquo sHK coset_ofN //; case: repr_rcosetP=> y Hy.
apply: kerP; exact: (subsetP sHK).
Qed.


Lemma factor_mquo : subset H (ker f) ->  H <| dom f -> forall x, fq (coset_of H x) = f x.
Proof.
move=> sHK nHD x; case Nx: (N x); first exact: factor_mquo_norm.
rewrite /mquo sHK set_of_coset_of Nx -(rcoset1 H); case: repr_rcosetP => y Hy.
rewrite (@out_dom _ _ f x); last by apply/negP; move/(subsetP nHD); rewrite Nx.
rewrite -(morph1 f); apply: kerP; exact: (subsetP sHK).
Qed.


Lemma factor_mquo_iim : subset H (ker f) ->
  forall A : group elt, subset A N -> fq @: (A / H) = f @: A.
Proof.
move=> sHK A sAN ; apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP => x.
  case/iimageP=> [[Hx pHx]] ->; case/iimageP: pHx=> y Ay ->.
    by apply/iimageP; exists y ; rewrite // factor_mquo_norm ?(subsetP sAN).
case/iimageP=> y Ay ->; apply/iimageP.
exists (coset_of H y); rewrite ?factor_mquo_norm ?(subsetP sAN) //.
by apply/iimageP; exists y.
Qed.



Lemma mquo_nt_subker : ~~ trivm fq -> subset H (ker f).
Proof. by case/set0Pn=> x; rewrite /mquo; case: subset => //; case/eqP. Qed.

Lemma ker_mquo_nt : ~~ trivm fq -> ker fq = ker f / H.
Proof.
move=> Hnt; have fqc := factor_mquo_norm (mquo_nt_subker Hnt).
apply/isetP=> xbar; apply/kerP/quotientP => [Kxbar | [x [Kx Nx ->{xbar}]] ybar].
  case: (cosetP xbar) => x Nx -> {xbar} in Kxbar *; exists x; split=> //=.
  case/set0Pn: Hnt => zbar; case: (cosetP zbar) {Kxbar}(Kxbar zbar) => z Nz -> {zbar}.
  rewrite -morphM ?domN ?fqc ?groupMl // => fxz fz1; have Dz: dom f z by exact: dom_nu.
  have Dx: dom f x by rewrite -(mulgK z x) groupMr ?groupV // dom_nu ?fxz.
  by apply/(kerMP Dx); apply: (mulg_injr (f z)); rewrite mul1g -morphM.
case: (cosetP ybar) => y Ny ->{ybar}; rewrite -morphM ?domN // !fqc ?groupMl //; exact: kerP.
Qed.

Lemma subset_ker_mquo : subset (ker f / H) (ker fq).
Proof.
apply/subsetP=> Abar KAbar; case Hnt: (trivm fq); first by rewrite trivm_ker ?isetAP.
by rewrite ker_mquo_nt ?Hnt.
Qed.

Lemma mquo_triv : subset H (ker f) -> H <| (dom f) -> trivm fq -> trivm f.
Proof.
by move=> sHk sdN fqTriv; apply/set0P=> x; rewrite -factor_mquo // trivm_is_cst ?eq_refl.
Qed.



Lemma ker_mquo : subset H (ker f) -> H <| dom f -> ker fq = ker f / H.
Proof.
case Htr: (trivm fq) => [] sHK nHD; last by rewrite ker_mquo_nt ?Htr.
apply/isetP=> xbar; rewrite trivm_ker // isetAP; symmetry; apply/iimageP.
case: (cosetP xbar) => x _ ->{xbar}; exists x => //=.
by rewrite trivm_ker ?isetAP {x}//; apply/set0P=> x; rewrite -factor_mquo ?(set0P Htr).
Qed.


Lemma dom_mquo_nt : ~~ trivm fq -> dom fq = dom f / H.
Proof.
move=> Hnt; apply/isetP=> xbar; rewrite 2!s2f ker_mquo_nt //.
have fqc := factor_mquo_norm (mquo_nt_subker Hnt).
apply/orP/iimageP=> [|[x Dx ->{xbar}]].
  case; first by case/quotientP=> x /= [Kx Nx ->{xbar}]; exists x => //; apply/isetUP; left.
  case: (cosetP xbar) => x Nx ->{xbar}; rewrite fqc //; exists x => //; exact: dom_nu.
case Nx: (N x).
  by case/isetUP: Dx; [left; apply/iimageP; exists x | rewrite s2f fqc //; right].
left; apply/iimageP; exists (1 : elt); rewrite ?group1 //; apply: set_of_coset_inj.
by rewrite set_of_coset_of Nx coset_of_id.
Qed.

Lemma subset_dom_mquo : subset (dom f / H) (dom fq).
Proof.
apply/subsetP=> Abar DAbar; case Hnt: (trivm fq); first by rewrite trivm_dom ?isetAP.
by rewrite dom_mquo_nt ?Hnt.
Qed.

Lemma dom_mquo : subset H (ker f) -> H <| dom f -> dom fq = dom f / H.
Proof.
case Htr: (trivm fq) => [] sHK nHD; last by rewrite dom_mquo_nt ?Htr.
apply/isetP=> xbar; case: (cosetP xbar) => x _ -> {xbar}.
rewrite trivm_dom // isetAP; symmetry; apply/iimageP; exists x => //.
rewrite trivm_dom ?isetAP {x}//; apply/set0P=> x.
by rewrite -factor_mquo ?(set0P Htr) //.
Qed.


Lemma group_set_dom_mquo : group_set (dom fq).
Proof.
case Hnt: (trivm fq); last by rewrite dom_mquo_nt ?Hnt // set_of_groupP.
by rewrite trivm_dom //; apply/groupP; split=> *; rewrite isetAP.
Qed.

Lemma mquoM : forall xbar ybar,
  dom fq xbar -> dom fq ybar -> fq (xbar * ybar) = fq xbar * fq ybar.
Proof.
move=> xbar ybar; case Hnt: (trivm fq); first by rewrite !(trivm_is_cst Hnt) mulg1.
have fqc := factor_mquo_norm (mquo_nt_subker (negbT Hnt)).
rewrite !dom_mquo_nt ?Hnt //.
case/quotientP=> x [Nx Dx ->{xbar}]; case/quotientP=> y [Ny Dy ->{ybar}].
by rewrite -morphM ?domN // !fqc ?groupMl // morphM.
Qed.

Canonical Structure mquo_morphism := Morphism group_set_dom_mquo mquoM.



Lemma ker_mquo_loc :  subset H (ker f) -> forall G : group elt, subset G (dom f) ->
  ker_(G / H) (mquo f H) = (ker_(G) f) / H.
Proof.
move=> sHK G sGd; apply/isetP=> Hx; apply/isetIP/quotientP.
  case=> KHx; case/quotientP=> x [Gx Nx E1]; exists x; split => //=.
  rewrite s2f Gx andbT; apply/kerMP; first exact:(subsetP sGd).
  by rewrite -factor_mquo_norm // ?dom_k ?(subsetP subset_ker_mquo) // -E1 mker.
case=> x []; case/isetIP=> Kx Gx Nx ->; split; last by apply/quotientP; exists x.
by rewrite (subsetP subset_ker_mquo) //; apply/iimageP; exists x.
Qed.



End QuotientMorphism.

Section InverseMorphism.

Open Scope group_scope.

Variables (elt1 elt2 : finGroupType)(H : group elt1).
Variable f : morphism elt1 elt2.

Hypothesis injmf : injm f H.

Notation Local invfH := (invm f H).


Lemma isetD1E : forall (A : setType elt1) x, A x -> A = (A :\ x) :|: {: x}.
Proof.
move=> A x Ax; apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP=> y.
  by move=> Ay; rewrite !s2f; case: (x == y)=> //=; rewrite orbF.
by rewrite !s2f; case/orP; [case/andP | move/eqP=> <-].
Qed.

Lemma ker_injm : ker_(H) f = {: 1}.
Proof.
move: injmf; rewrite /injm=> H1; apply/isetP.
apply/subset_eqP; apply/andP; split; apply/subsetP=> x; last first.
  by rewrite s2f; move/eqP=> <-; rewrite group1.
case/isetIP=> Kx; move/isetD1E: (group1 H)=> ->; rewrite !s2f.
case/orP=> //; move/subsetP: H1; move/(_ x); rewrite s2f=> H1 H2.
by move: (H1 H2)=> {H1}; rewrite s2f Kx/=.
Qed.



Lemma ker_invm : ker_(f @: H) invfH = {:1}.
Proof.
apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP=> y.
  case/isetIP; move/kerP=> Hkx; case/iimageP=> x Hx Ey; rewrite s2f.
  move:(Hkx 1); rewrite mulg1; rewrite /invm injmf; rewrite Ey {Ey}=> Er.
  have H1 : ({x : elt1, H x && (f x == 1)} 1).
    by rewrite s2f group1 morph1 eq_refl.
  move: (@mem_repr _ 1 {x : elt1, H x && (f x == 1)} H1)=> {H1}.
  rewrite -Er s2f; move/andP; case=> _; move/eqP=> <-.
  have Tmpx : ({x0 : elt1, H x0 && (f x0 == f x)} x).
    by rewrite s2f Hx eq_refl.
  move: (@mem_repr _ x {y : elt1, H y && (f y == f x)} Tmpx).
    by rewrite s2f; move/andP; case=> _.
by rewrite s2f; move/eqP => <-; rewrite group1.
Qed.



End InverseMorphism.

Section Isomorphisms.

Open Scope group_scope.


Variables (elt1 elt2 : finGroupType)(H : group elt1)(G : group elt2).

Lemma isog_refl : isog H H.
Proof.
exists {idm elt1 as morphism _ _}=> /=; rewrite /isom; apply/andP; split.
  apply/eqP; apply/isetP=> x; apply/iimageP/idP; rewrite /idm; first by case=> y Hy ->.
  by move=> Hx; exists x.
by apply/injmP; move=> x y Hx Hy /=; rewrite /idm.
Qed.

Lemma isog_sym : isog H G -> isog G H.
Proof.
Admitted.

Lemma isog_simpl: isog H G -> simple H -> simple G.
Proof.
move=> HH; move: {HH}(isog_sym HH).
case=> f; case/andP => Hf Hf1.
move/simpleP => HH; apply/simpleP => K Hk Hk1.
case (HH (group_im f K)).
- rewrite /group_im /= -(eqP Hf).
  apply/subsetP => x; case/iimageP => y Ky ->.
  by apply/iimageP; exists y => //; apply: (subsetP Hk).
- move/normalP: Hk1 => Hk2.
  apply/normalP => x /=; rewrite -(eqP Hf).
  case/iimageP => y Gy ->.
  rewrite -!iimage_conj; first by rewrite (Hk2 _ Gy).
  - by apply: (subset_trans Hk); apply: injm_dom Hf1.
  by apply: (subsetP (injm_dom Hf1)).
- move=> /= HH1; left.
  apply/subset_eqP; apply/andP; split; apply/subsetP => z Hz; last first.
    by rewrite -(eqP Hz) group1.
  have Hf1z: f 1 = f z.
    suff ->: f 1 = 1 by apply/eqP; rewrite -(HH1 (f z)); apply/iimageP; exists z.
    by apply sym_equal; apply/eqP; rewrite -(HH1 (f 1)); apply/iimageP; exists (1: elt2); rewrite // group1.
  apply/eqP; move/injmP: Hf1 => HH2.
  by rewrite (HH2 _ _ _ _ Hf1z) // (subsetP Hk).
move=> /= HH1; right.
apply/subset_eqP; rewrite Hk; apply/subsetP=> g Hg.
have: (f @: K) (f g) by rewrite HH1 -(eqP Hf); apply/iimageP; exists g.
case/iimageP => g1 Hg1.
move/injmP: Hf1 => HH2 Hi.
by rewrite (HH2 _ _ Hg _ Hi) // (subsetP Hk).
Qed.
  
End Isomorphisms.



Notation "'ker_' ( G ) f" := (ker f :&: G)
  (at level 10, format "'ker_' ( G )  f") : group_scope.

Notation "'dom_' ( G ) f" := (dom f :&: G)
  (at level 10, format "'dom_' ( G )  f") : group_scope.

Notation "'preim_' ( G ) f B" := ((f @^-1: B) :&: G)
  (at level 10, format "'preim_' ( G )  f  B") : group_scope.


Section FirstIsomorphism.

  
Open Scope group_scope.

Variables (elt1 elt2 : finGroupType) (f : morphism elt1 elt2).


Notation Local D := (dom f).
Notation Local K := (group_ker f).


Variable H : group elt1.

Hypothesis sHD : subset H (dom f).

Lemma sHDr : subset H (dom_(H) f).
Proof. by apply/subsetP=> x Hx; apply/isetIP; rewrite ?(subsetP sHD). Qed.


Notation Local fbar := (mquo f (ker_(H) f)).

Lemma first_isom : isog (H / (ker_(H) f)) (f @: H).
Proof.
rewrite /isog; exists {fbar as morphism _ _}; apply/andP=> /=; split.
  apply/eqP; apply/isetP; apply/subset_eqP.
  apply/andP; split; apply/subsetP=> x; case/iimageP=> y.
    case/quotientP=> z=> [[Hz Nz ->]] ->.
    by apply/iimageP; exists z; rewrite ?factor_mquo_norm //= (subset_ker_r f).
  move=> Hy ->; apply/iimageP=> /=; exists (coset_of (ker_(H) f) y).
    apply/quotientP; exists y.
    rewrite Hy (subsetP (normal_ker_r _ _)) ?(subsetP sHDr) //.
  rewrite factor_mquo_norm //= ?(subset_ker_r f) // (subsetP (normal_ker_r _ _)) //.
  by rewrite (subsetP sHDr).
apply/injmP=> xbar ybar; case/quotientP=> [x [Dx Nx ->]] {xbar}.
case/quotientP=> [y [Dy Ny ->]] {ybar} /=.
rewrite !factor_mquo_norm //= ?(subset_ker_r f) // => Heq.
apply:set_of_coset_inj; rewrite !set_of_coset_of Nx Ny.
apply rcoset_trans1; apply/rcosetP; exists (y * x^-1) => /= ; last by gsimpl.
apply/isetIP; apply/andP; rewrite groupM ?groupV // andbT.
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
rewrite -(set_of_group_inj (ker_coset_of_loc nKH)) /=.
by apply: first_isom; apply: subset_trans _ (subset_dom_coset K).
Qed.


Lemma quotient_mulg : (H :*: K) / K = H / K.
Proof.
rewrite -norm_smulC //.
apply/isetP=> Kx; apply/iimageP/iimageP=> [] [x Hx ->{Kx}].
  case/smulgP: Hx=> k h Kk Hh->; exists h => //; apply: kerP.
  by rewrite (subsetP (subset_ker_coset _)).
by exists x=> //; rewrite (subsetP (smulg_subr _ (group1 K))) ?Hx.
Qed.


Lemma weak_second_isom : isog (H / (K :&: H)) ((H :*: K) / K).
Proof. rewrite quotient_mulg; exact: second_isom. Qed.


End SecondIsomorphism.


Lemma subset_iimage : forall (elt1 elt2 : finType) (A B: setType elt1)
  (f : elt1 -> elt2) , 
  subset A B -> subset (f @: A) (f @: B).
Proof.
move=> elt1 elt2 A B f sAB; apply/subsetP=> y; case/iimageP=> x Ax ->.
by apply/iimageP; exists x; rewrite ?(subsetP sAB).
Qed.
  
Section ThirdIsomorphism.

Variables (elt : finGroupType) (G H K : group elt).

Hypothesis sHK : subset H K.
Hypothesis sKG : subset K G.
Hypothesis nHG : H <| G.
Hypothesis nKG : K <| G.

Theorem third_iso  : isog ((G / H) / (K / H)) (G / K).
Proof.
have sHker: subset H (ker (coset_of K)).
  by rewrite (subset_trans sHK) ?subset_ker_coset.
have sGdom: subset G (dom (coset_of K)).
  by rewrite (subset_trans nKG) ?subset_dom_coset.
have sGHdom: subset (G / H) (dom (mquo (coset_of K) H)).
  apply: subset_trans (subset_dom_mquo _ _); exact: subset_iimage.
have KH_ker : K / H = ker_(G / H) (mquo (coset_of K) H).
  rewrite ker_mquo_loc // ker_coset_of_loc //; congr (_ / H).
  apply/isetP=> x; rewrite s2f.
  by case Kx: (K x); rewrite //= (subsetP sKG).
rewrite -[K / H]/(set_of_group _) {KH_ker}(set_of_group_inj KH_ker) /=.
have -> : G / K = mquo (coset_of K) H @: G / H by rewrite factor_mquo_iim.
exact: first_isom.
Qed.  

End ThirdIsomorphism.



Unset Implicit Arguments.