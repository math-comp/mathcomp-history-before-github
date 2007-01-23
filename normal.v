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

Hypothesis gH: group H.
Hypothesis gK: group K.
Hypothesis subset_HK: subset H K.


(********************************************************************)
(*              Definition of a normal set                          *)
(*    H is normal in K iff xHx^-1 = H forall x in K                 *)
(*    it is sufficient that H is included in xHx^¯1                 *)
(*    since both sets have same cardinal                            *)
(********************************************************************)


Definition normal := subset K (normaliser H). 


Theorem normalP:
  reflect (forall x, K x -> (H :^ x) = H) normal.
Proof.
apply: (iffP idP).
 by rewrite/normal; move/subsetP=> H1 x Kx; apply norm_conjsg; apply H1.
by move=> H1; apply/subsetP=> x Kx; rewrite/normaliser s2f H1 //; apply subset_refl.
Qed.


End Normal.

Section NormalProp.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : setType elt).
Hypothesis gH : group H.
Hypothesis gK : group K.
Hypothesis subset_HK : subset H K.
Hypothesis nHK : normal H K.

Theorem normal_subset: forall L : setType elt, subset L K -> normal H L.
Proof. move=> L HLK; exact: subset_trans HLK _. Qed.

Theorem norm_normal: normal H (normaliser H).
Proof. exact: subset_refl. Qed.

Notation Local N := (normaliser H).

Lemma rcoset_mul : forall x y, 
  N x -> N y -> (H :* x) :*: (H :* y) = H :* (x * y).
Proof.
move=> x y Nx Ny.
rewrite !rcoset_prod -prodgA (prodgA _ H) -lcoset_prod -norm_rcoset_lcoset //.
by rewrite rcoset_prod -prodgA prodg_set1 prodgA prodgg.
Qed.

End NormalProp.

Section Cosets.

Open Scope group_scope.

Variables (elt : finGroupType) (H : setType elt).
Hypothesis gH: group H.

Notation Local N := (normaliser H).
Let gN := group_norm H.


(* Definition of the cosets as the rcosets of elements of the normalizer *)

Definition coset_set := image (rcoset H) N.

CoInductive cosetType : Type := Coset of eq_sig coset_set.

Definition sig_of_coset u := let: Coset v := u in v.

Remark sig_of_cosetK : cancel sig_of_coset Coset. Proof. by case. Qed.

Canonical Structure coset_eqType := EqType (can_eq sig_of_cosetK).
Canonical Structure coset_finType := FinType (can_uniq sig_of_cosetK).

Coercion set_of_coset u := val (sig_of_coset u) : setType elt.

Lemma coset_set_inj : injective set_of_coset.
Proof. exact: inj_comp (@val_inj _ _) (can_inj sig_of_cosetK). Qed.

Lemma coset_unit_set : coset_set H.
Proof. by apply/imageP; exists (1:elt); rewrite ?group1 // rcoset1. Qed.

Definition coset_unit := Coset (EqSig _ _ coset_unit_set).

Lemma coset_mul_set : forall Hx Hy : cosetType, coset_set (Hx :*: Hy).
Proof.
rewrite /set_of_coset => [] [[Hx nHx]] [[Hy nHy]] /=.
case/imageP: nHx => [x Nx ->{Hx}]; case/imageP: nHy => [y Ny ->{Hy}].
by apply/imageP; exists (x * y); [apply: groupM | rewrite rcoset_mul].
Qed.

Definition coset_mul Hx Hy := Coset (EqSig _ _ (coset_mul_set Hx Hy)).

Lemma coset_inv_set : forall Hx : cosetType, coset_set (Hx :^-1).
Proof.
rewrite /set_of_coset => [] [[A]] /=; move/imageP=> [x Nx ->{A}].
rewrite norm_rcoset_lcoset // invsg_lcoset //.
by apply/imageP; exists x^-1; first rewrite groupV.
Qed.

Definition coset_inv Hx := Coset (EqSig _ _ (coset_inv_set Hx)).

Lemma coset_unitP : forall Hx, coset_mul coset_unit Hx = Hx.
Proof.
move=> [[Hx nHx]]; apply: coset_set_inj; do 3!rewrite /set_of_coset /=.
case/imageP: nHx => [x Nx ->{Hx}]; rewrite rcoset_prod prodgA.
by rewrite [H :*: H]prodsgg //; [rewrite group1 | apply subset_refl].
Qed.

Lemma coset_invP : forall Hx, coset_mul (coset_inv Hx) Hx = coset_unit.
Proof.
move=> [[Hx nHx]]; apply: coset_set_inj; do 3!rewrite /set_of_coset /=.
case/imageP: nHx => [x Nx ->{Hx}].
by rewrite {1}norm_rcoset_lcoset ?invsg_lcoset ?rcoset_mul ?mulVg ?rcoset1 ?groupV.
Qed.

Lemma coset_mulP : forall Hx Hy Hz,
  coset_mul Hx (coset_mul Hy Hz) = coset_mul (coset_mul Hx Hy) Hz.
Proof.
move=> [[Hx nHx]] [[Hy nHy]] [[Hz nHz]]; apply: coset_set_inj.
do 3!rewrite /set_of_coset /=.
case/imageP: nHx => [x Nx ->{Hx}]; case/imageP: nHy => [y Ny ->{Hy}].
by case/imageP: nHz => [z Nz ->{Hz}]; rewrite prodgA.
Qed.


Canonical Structure coset_groupType :=
  FinGroupType coset_unitP coset_invP coset_mulP.


Lemma val_morph : forall x y : coset_groupType,
  set_of_coset (x * y) = (set_of_coset x) :*: (set_of_coset y).
Proof. by move=> *; constructor. Qed.

Section Quotient.

Variable K : setType elt.

(* This is in fact HK/H *)

Definition quotient  :=  {u: coset_finType, (image (rcoset H) K) u}.

Hypothesis gK : group K.
Hypothesis nK : normal H K.

Lemma group_quotient : group quotient.
Proof.
apply/andP; split.
 rewrite !s2f; apply/imageP; exists (1:elt); first exact: group1.
 by rewrite rcoset_prod prodg1.
apply/subsetP => x; move/prodgP=> [fy fz]; rewrite !s2f; move/imageP=>[y Hy Ey].
move/imageP=>[z Hz Ez]->; apply/imageP; exists (y * z); first by rewrite groupM.
by rewrite val_morph Ey Ez rcoset_mul //; apply (subsetP nK).
Qed.

End Quotient.

End Cosets.

Notation "H / K" := (quotient K H).
Section Morphism.

Open Scope group_scope.

Variables (elt elt' : finGroupType) (H : setType elt) (H' : setType elt').

Variable f : elt -> elt'.

Definition morphism := forall x y, 
  H x -> H y -> f (x * y) = (f x) * (f y).


Hypothesis mf : morphism.

Hypothesis gH : group H.

Lemma morph1 :  f 1 = 1.
Proof. by apply: (mulg_injl (f 1)); rewrite -mf ?group1 // !mulg1. Qed.


Lemma morphV : forall x, 
  H x -> f (x ^-1) = (f x) ^-1.
Proof.
by move=> x Hx; apply: (mulg_injl (f x)); rewrite -mf ?groupV // !mulgV morph1.
Qed.

Lemma morph_conjg : forall x y, H x -> H y -> f (x ^ y) = (f x) ^ (f y).
Proof. move=> x y Hx Hy; rewrite/conjg -morphV // -!mf // ?groupM // groupV //. Qed.

Lemma iimage_prod : forall A B : setType elt, 
  subset A H -> subset B H -> iimage f (A :*: B) = (iimage f A) :*: (iimage f B).
Proof.
move=> A B; move/subsetP=> sAH; move/subsetP=> sBH.
apply/eqP;apply/isetP=> u; apply/iimageP/prodgP.
 case=> xy; move/prodgP=> [x y Ax By ->{xy}] ->{u}; rewrite mf; auto.
 by exists (f x) (f y) => //; apply/iimageP; [exists x | exists y].
case=>fx fy; move/iimageP=>[x Ax ->]; move/iimageP=>[y By ->] ->; rewrite -mf; auto.
by exists (x * y)=> //; apply/prodgP; exists x y.
Qed.

Lemma iimage_conj : forall (A : setType elt) x,
  subset A H -> H x -> iimage f (A :^ x) = (iimage f A) :^ (f x).
Proof.
move=> A x sAH => Hx; rewrite !conjsg_coset !rcoset_prod !lcoset_prod -morphV //.
rewrite -!(iimage_set1 f) -!iimage_prod // ?subset_set1 ?groupVr // -(prodgg gH).
by apply: subset_trans (prodgs _ sAH); apply: prodsg; rewrite subset_set1 groupVr.
Qed.

Lemma morph_image_grp : group (iimage f H).
Proof.
apply/andP; split.
 by apply/iimageP; exists (1:elt); [apply: group1=>//| symmetry; exact: morph1].
by rewrite -iimage_prod ?prodgg // subset_refl.
Qed.

Definition gpreimage (A : setType elt') := {x, A (f x)}.

Hypothesis gH': group H'.

Lemma morph_preimage_grp : subset (gpreimage H') H -> group (gpreimage H').
Proof.
move/subsetP=>Hsubset; apply/andP.
split; first by rewrite s2f morph1 group1.
apply/subsetP=> x Hx; case/prodgP:Hx => x1 x2; rewrite !s2f => Hx1 Hx2 ->.
by rewrite mf ?groupM ?Hsubset // s2f.
Qed.

Variable K : setType elt.

Hypothesis gK : group K.
Hypothesis subset_KH : subset K H.


Lemma morph_normal_im : normal K H -> normal (iimage f K) (iimage f H).
Proof.
move/normalP=> Hn; apply/normalP => x; move/iimageP=> [u Hu ->].
by rewrite -iimage_conj // Hn.
Qed.

Section Ker.

Definition ker :=  gpreimage {:1} :&: H.

Lemma ker1 : forall x, ker x -> f x = 1.
Proof. by move=> x; rewrite !s2f ; case/andP; move/eqP->. Qed.

Lemma ker_sub : forall x, ker x -> H x.
Proof. by move=> x; rewrite !s2f ; case/andP. Qed.

Lemma ker_grp : group ker.
Proof.
apply/andP;split; first by rewrite !s2f morph1 eq_refl group1.
apply/subsetP=> x; move/prodgP=>[y1 y2]; rewrite !s2f.
move/andP=>[Hfy1 Hy1]; move/andP=> [Hfy2 Hy2 ->].
by rewrite mf // -(eqP Hfy1) -(eqP Hfy2) mulg1 eq_refl groupM.
Qed.


Lemma normal_ker : normal ker H.
Proof.
apply/subsetP=> x Hx; rewrite !s2f; apply/subsetP=> y; rewrite !s2f.
move/andP=> [H1 Hy]; rewrite -(conjgKv x y) morph_conjg // -(eqP H1) conj1g.
by rewrite eq_refl andTb /conjg groupM // groupM // groupV.
Qed.


Lemma kerP : 
  reflect (forall x y, H x -> H y -> (f x = f y -> x = y)) (trivg ker).
Proof.
apply: (iffP idP); rewrite /setI/gpreimage.
 move/subsetP=> H1 x y Hx Hy Hxy; apply (mulg_injl (y^-1)); rewrite mulVg.
 suff: {:1}(y ^-1 * x) by rewrite s2f; move/eqP; auto.
 by apply H1; rewrite !s2f mf ?morphV ?groupMl ?groupV // -Hxy mulVg eq_refl; auto.
move=> H1; apply/subsetP=> x; rewrite !s2f; move/andP=>[Hx1 Hx]; apply/eqP. 
by apply H1; rewrite ?morph1 ?group1 // (eqP Hx1).
Qed.

Definition isomorphism := morphism /\ (trivg ker).

End Ker.

End Morphism.


Section MorphismRestriction.


Open Scope group_scope.

Variables (elt elt' : finGroupType) (H K: setType elt).
Variable f : elt -> elt'.

Hypothesis gH : group H.
Hypothesis gK : group K.

Hypothesis sHK : subset K H.
Hypothesis mfH : morphism H f.


Lemma morph_r : morphism K f.
Proof. by move=> x y Kx Ky; apply mfH; apply (subsetP sHK). Qed.

(* et quoi d'autre? *)

End MorphismRestriction.

Section Isomporhism_theorems.


Section First_theorem.

Open Scope group_scope.
 
Variables (elt elt' : finGroupType) (H : setType elt).

Hypothesis gH: group H.

Variable f : elt -> elt'.
Hypothesis mf : morphism H f.

Notation Local K := (ker H f).

Let gK := ker_grp mf gH.

Notation Local q_elt := (coset_groupType gK).

Let norm_HmodK := normal_ker mf gH.

Let group_HmodK := group_quotient gK gH norm_HmodK.

Notation Local fquo := (fun x : q_elt => f (repr x)).

Variable K' : setType elt.
Hypothesis gK' : group K'.

Notation Local q'_elt := (coset_groupType gK').

Notation Local fquo' := (fun x : q'_elt => f (repr x)).


Hypothesis sK'K : subset K' K.
Hypothesis norm_HmodK' : normal K' H.

Check normal_subset.
Notation Local norm_KmodK' : normal K.

Lemma fquo_morph : morphism (H /K') fquo'.
Proof.
move=>fx fy; rewrite !s2f val_morph; move/imageP=>[x Hx ->]; move/imageP=>[y Hy ->].
have: normaliser K' x; first by exact: (subsetP norm_HmodK')=>//.
have: normaliser K' y; first by exact: (subsetP norm_HmodK')=>//.
have: sub_set K' H; first move=> u K'u. apply: ker_sub. apply: (subsetP sK'K _ K'u). ((subsetP sK'K) K'u)).
move=> N'x N'y.
rewrite rcoset_mul //.
move/rcosetP: (rcoset_repr gK' x)=>[k'x K'x ->] {fx}.
move/rcosetP: (rcoset_repr gK' y)=>[k'y K'y ->] {fy}.
move/rcosetP: (rcoset_repr gK' (x * y))=>[k'xy K'xy ->].
rewrite !mf ?groupM // ?(ker1 (subsetP sK'K _ K'x)) ?(ker1 (subsetP sK'K _ K'y)) ?(ker1 (subsetP sK'K _ K'xy)).

 (ker1 K'y) (ker1 K'xy).
by gsimpl.
Qed.


Lemma fquo_morph :  morphism (H /K) fquo.
Proof.
move=>fx fy; rewrite !s2f val_morph; move/imageP=>[x Hx ->]; move/imageP=>[y Hy ->].
rewrite rcoset_mul //; try apply (subsetP norm_HmodK)=>//.
move/rcosetP: (rcoset_repr gK x)=>[kx Kx ->] {fx}.
move/rcosetP: (rcoset_repr gK y)=>[ky Ky ->] {fy}.
move/rcosetP: (rcoset_repr gK (x * y))=>[kxy Kxy ->].
rewrite !mf ?groupM // ?(@ker_sub _ _ H f) // (ker1 Kx) (ker1 Ky) (ker1 Kxy).
by gsimpl.
Qed.


(* this proof is too long, do not understand
 why it is so complicated to remove all the layers*)

Lemma fquo_ker : trivg (ker (H / K) fquo).
Proof.
apply/subsetP=> A; rewrite !s2f; case/andP=> [fA HKA]; apply/eqP; apply: coset_set_inj.
case/imageP: HKA fA => [x Hx ->{A}]; move/rcosetP: (rcoset_repr gK x) => [y Ky ->] Dfxy.
rewrite -(@rcoset_trans1 _ _ gK 1 x) rcoset1 // -(groupMl gK _ Ky) !s2f Dfxy groupM //.
by rewrite s2f in Ky; case/andP: Ky.
Qed.



(* (preimage coset) definit une bijection entre les sous groupes de *)
(* H/Ker et les sous groupes de H qui contiennent le ker *)


End First_theorem.



Section Third_theorem.

Open Scope group_scope.

 
Variables (GT : finGroupType) (G H K : set GT).

Hypothesis G_grp : group G.
Hypothesis gH : group H.
Hypothesis K_grp : group K.

Hypothesis subset_HK : subset H K.
Hypothesis subset_KG : subset K G.

Hypothesis normal_HG : normal H G.
Hypothesis normal_KG : normal K G.

Let KoverH := quotient gH K.
Let GoverH := quotient gH G.


Let normal_HK := normal_subset normal_HG subset_KG.

Let KovergH := group_quotient gH K_grp normal_HK.
Let GovergH := group_quotient gH G_grp normal_HG.

Check morphism. 
Let Hquo := coset_groupType gH.


Lemma morphism_coset : morphism G (coset gH).
Proof.
move=> x y; do 2 move/(subsetP normal_HG)=> ?; exact: coset_morph. 
Qed.

Lemma normal_KoH_GoH : normal KoverH GoverH.
Proof. exact: (morph_normal_im morphism_coset). Qed.

Definition third_grp_iso (u : coset_groupType KovergH) : coset_groupType K_grp :=
  coset K_grp (val (val u)).

(* Not Loc *)
Let f (u : Hquo) := coset K_grp (val u).

Let mf : morphism GoverH f.

Lemma morphism_third_grp_iso : morphism (quotient KovergH GoverH) third_grp_iso.
Proof.

apply: fquo_morph.

) : coset_groupType
  KovergH :=

G_grp _ _ _. subset_KG normal_KG.
have:= morph_normal_im morphism_coset G_grp subset_KG normal_KG.
done.
apply (@morph_normal_im  _ _ _ coset _ _ _ subset_HK normal_HK)

apply/normalP=> x y; rewrite /KoverH /GoverH /quotient; set Hcoset := coset gH.
move/gimageP=> [x1 Hx1 ->]; move/imageP=> [x2 Hx2 ->].
have : Hcoset x2 = 1.
move=> i. rewrite/Hcoset.

SearchAbout coset.
have : (Hcoset x1)^-1 = Hcoset (x1 ^-1).
rewrite /Hcoset=> i; rewrite
SearchAbout coset_inv.


rewrite /conjg.

rewrite /invg /= /coset_inv /mulg /= /coset_mul /Hcoset !val_coset. !coset_mul_morph -/Hcoset.


 -coset_mul_morph.
rewrite
rewrite /coset_mul.
apply/imageP.


 Print conjg. 
SearchAbout coset.  
rewrite /quotient; apply/imageP.



End Isomporhism_theorems.


Unset Implicit Arguments.






