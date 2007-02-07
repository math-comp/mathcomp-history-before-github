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
  by move/subsetP=> H1 x Kx; apply norm_sconjg; apply H1.
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
  N x  -> (H :* x) :*: (H :* y) = H :* (x * y).
Proof.
move=> x y Nx.
rewrite !rcoset_smul -smulgA (smulgA _ H) -lcoset_smul -norm_rcoset_lcoset //.
by rewrite rcoset_smul -smulgA smulg_set1 smulgA smulgg.
Qed.


End NormalProp.


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

(*
Definition gimage (A : setType elt) := iset_of_fun (image  f A).

Lemma gimageP : forall (A : setType elt) y, 
  reflect (exists2 x, A x & y = f x) (gimage A y).
Proof. move=> A y; rewrite s2f; exact: imageP. Qed.

Lemma gimage_set1 : forall x, gimage {: x } = {: f x}.
Proof.
move=> x; apply iset_eq => y; rewrite !s2f; apply/imageP/eqP.
 by case=>x'; rewrite s2f; move/eqP->.
by exists x=> //; rewrite iset11.
Qed.

Lemma gimage_smul : forall A B : setType elt, 
  subset A H -> subset B H -> gimage (A :*: B) = (gimage A) :*: (gimage B).
Proof.
move=> A B; move/subsetP=> sAH; move/subsetP=> sBH.
apply: iset_eq=> u; apply/gimageP/smulgP.
 case=> xy; move/smulgP=> [x y Ax By ->{xy}] ->{u}; rewrite mf; auto.
 by exists (f x) (f y) => //; apply/gimageP; [exists x | exists y].
case=>fx fy; move/gimageP=>[x Ax ->]; move/gimageP=>[y By ->] ->; rewrite -mf; auto.
by exists (x * y)=> //; apply/smulgP; exists x y.
Qed.

*)

(* to be moved to tuples *)
(*
Lemma subset_set1 : forall (A : setType elt) x, subset {:x} A = A x.
Proof.
move=> A x; apply/subsetP/idP.
 by move=> xA; apply xA; rewrite s2f set11.
by move=> Ax x'; rewrite s2f; move/eqP<-.
Qed.
*)



Lemma iimage_smul : forall A B : setType elt, 
  subset A H -> subset B H -> f @: (A :*: B) = (f @: A) :*: (f @: B).
Proof.
move=> A B; move/subsetP=> sAH; move/subsetP=> sBH.
apply /isetP=> u; apply/iimageP/smulgP.
 case=> xy; move/smulgP=> [x y Ax By ->{xy}] ->{u}; rewrite mf; auto.
 by exists (f x) (f y) => //; apply/iimageP; [exists x | exists y].
case=>fx fy; move/iimageP=>[x Ax ->]; move/iimageP=>[y By ->] ->; rewrite -mf; auto.
by exists (x * y)=> //; apply/smulgP; exists x y.
Qed.


Lemma iimage_conj : forall (A : setType elt) x,
  subset A H -> H x -> f @: (A :^ x) = (f @: A) :^ (f x).
Proof.
move=> A x sAH => Hx; rewrite !sconjg_coset !rcoset_smul !lcoset_smul -morphV //.
rewrite -(iimage_set1 f) -!iimage_smul // ?subset_set1 ?groupVr //.
rewrite ?iimage_smul ?(iimage_set1 f) // ?subset_set1 ?groupV // -(smulgg gH). 
apply: (@subset_trans _ _ (H :*: A)); [apply smulsg |apply smulgs]; rewrite ?subset_set1 //.
by rewrite ?groupV.
Qed.


Lemma morph_image_grp : group (f @: H).
Proof.
apply/andP; split.
 by apply/iimageP; exists (1:elt); [apply: group1=>//| symmetry; exact: morph1].
by rewrite -iimage_smul ?smulgg // subset_refl.
Qed.


(*
Definition gpreimage (A : setType elt') := {x, A (f x)}.
*)
Hypothesis gH': group H'.

Lemma morph_preimage_grp : subset (f @^-1: H') H -> group (f @^-1: H').
Proof.
move/subsetP=>Hsubset; apply/andP.
split; first by rewrite !s2f morph1 group1.
apply/subsetP=> x Hx; case/smulgP:Hx => x1 x2; rewrite !s2f => H1 H2 ->.
by rewrite mf  ?groupM // Hsubset // !s2f.
Qed.

Variable K : setType elt.

Hypothesis gK : group K.
Hypothesis subset_KH : subset K H.


Lemma morph_normal_im : normal K H -> normal (f @: K) (f @: H).
Proof.
move/normalP=> Hn; apply/normalP => x; move/iimageP=> [u Hu ->].
by rewrite -iimage_conj // Hn.
Qed.

Section Ker.

Definition ker :=  (f @^-1: {:1}) :&: H.

Lemma ker1 : forall x, ker x -> f x = 1.
Proof. by move=> x; rewrite !s2f ; case/andP;move/eqP=><-. Qed.

Lemma subset_ker : subset ker H.
Proof. by apply/subsetP=> x; rewrite !s2f ; case/andP; auto. Qed.

Lemma ker_grp : group ker.
Proof.
apply/andP; split; first by rewrite !s2f group1 ?morph1 ?eq_refl.
apply/subsetP=> x; move/smulgP=>[y1 y2]; rewrite !s2f.
move/andP=> [Hfy1 Hy1];move/andP=>[Hfy2 Hy2] ->.
apply/andP; split; last by rewrite groupM.
by rewrite mf // -(eqP Hfy1) -(eqP Hfy2);gsimpl.
Qed.

Lemma normal_ker : normal ker H.
Proof.
apply/subsetP=> x Hx; rewrite !s2f; apply/subsetP=> y; rewrite !s2f.
move/andP=> [H1 Hy]; rewrite -(conjgKv x y) morph_conjg // -(eqP H1) conj1g.
by rewrite eq_refl groupJr ?groupV.
Qed.


Lemma kerP : 
  reflect (forall x y, H x -> H y -> (f x = f y -> x = y)) (trivg ker).
Proof.
apply: (iffP idP); rewrite /setI/ipreimage.
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


End MorphismRestriction.


Section MorphismComposition.


Open Scope group_scope.

Variables (elt1 elt2 elt3 : finGroupType)(H : setType elt1).

Variable f : elt1 -> elt2.
Variable g : elt2 -> elt3.

Hypothesis mf : morphism H f.
Hypothesis mg : morphism (iimage f H) g.

Lemma morph_c : morphism H (g \o f).
Proof. 
by move=> x y Hx Hy; rewrite /comp mf  ?mg //; apply/iimageP; [exists x | exists y] => //.
Qed.

Lemma im_morph_c : (g \o f) @: H = g @: (f @: H).
Proof.
apply/isetP=> x; rewrite/comp; apply/iimageP/iimageP.
 by case=> y Hy ->; exists (f y)=> //; apply/iimageP; exists y.
by case=> y; move/iimageP; case=> z Hz -> ->; exists z.
Qed.

Lemma ker_morph_c : ker H (g \o f) =  ( f @^-1: (ker (f @: H) g) ) :&: H.
Proof.
apply/isetP => x; rewrite !s2f; apply/andP/andP; rewrite /comp.
 by case=> -> Hx; split=> //; apply/iimageP; exists x.
by case; move/andP=> [-> _ ->].
Qed.


End MorphismComposition.



Section Cosets.

Open Scope group_scope.

Variables (elt : finGroupType) (H : setType elt).
Hypothesis gH: group H.

Notation Local N := (normaliser H).

Let gN := group_normaliser H.


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
rewrite norm_rcoset_lcoset // sinvg_lcoset //.
by apply/imageP; exists x^-1; first rewrite groupV.
Qed.

Definition coset_inv Hx := Coset (EqSig _ _ (coset_inv_set Hx)).

Lemma coset_unitP : forall Hx, coset_mul coset_unit Hx = Hx.
Proof.
move=> [[Hx nHx]]; apply: coset_set_inj; do 3!rewrite /set_of_coset /=.
by case/imageP: nHx => [x Nx ->{Hx}]; rewrite rcoset_smul smulgA [H :*: H]smulgg.
Qed.

Lemma coset_invP : forall Hx, coset_mul (coset_inv Hx) Hx = coset_unit.
Proof.
move=> [[Hx nHx]]; apply: coset_set_inj; do 3!rewrite /set_of_coset /=.
case/imageP: nHx => [x Nx ->{Hx}].
by rewrite {1}norm_rcoset_lcoset ?sinvg_lcoset ?rcoset_mul ?mulVg ?rcoset1 ?groupV.
Qed.

Lemma coset_mulP : forall Hx Hy Hz,
  coset_mul Hx (coset_mul Hy Hz) = coset_mul (coset_mul Hx Hy) Hz.
Proof.
move=> [[Hx nHx]] [[Hy nHy]] [[Hz nHz]]; apply: coset_set_inj.
do 3!rewrite /set_of_coset /=.
case/imageP: nHx => [x Nx ->{Hx}]; case/imageP: nHy => [y Ny ->{Hy}].
by case/imageP: nHz => [z Nz ->{Hz}]; rewrite smulgA.
Qed.


Canonical Structure coset_groupType :=
  FinGroupType coset_unitP coset_invP coset_mulP.

Lemma set_of_coset_morph : forall x y : coset_groupType,
  set_of_coset (x * y) = (set_of_coset x) :*: (set_of_coset y).
Proof. by move=> *; constructor. Qed.

Section Quotient.

Variable K : setType elt.

(* This is in fact HK/H *)

Definition quotient_canonical_proj x := if N x then rcoset H x else H.

Notation proj := quotient_canonical_proj.

Lemma coset_set_proj : forall x, coset_set (proj x).
Proof.
move=> x; rewrite/proj; case Nx: (N x); last by exact: coset_unit_set.
by apply/imageP; exists x.
Qed.

Definition coset x := Coset (EqSig _ _ (coset_set_proj x)).

Definition quotient := coset @: K.

Lemma morphism_coset : morphism N coset.
Proof.
move=> x y Nx Ny; apply: coset_set_inj; rewrite  /set_of_coset /= /coset /set_of_coset /=.
have Nxy : N (x * y) by rewrite groupM.
by rewrite /proj Nx Ny Nxy rcoset_mul.
Qed.

Hypothesis gK : group K.
Hypothesis nK : normal H K.


Lemma group_quotient : group quotient.
Proof. by apply: morph_image_grp=> //; apply: morph_r morphism_coset. Qed.

End Quotient.

End Cosets.

Notation "H / K" := (quotient K H).

Section TrivialQuotient.


Open Scope group_scope.

Variables (elt : finGroupType) (H : setType elt).

Hypothesis gH: group H.


Lemma trivial_quotient : H / H = {:(1 : coset_groupType gH)}.
Proof.
apply/isetP=> A; rewrite s2f /set1 /= /set1 /=; apply/iimageP/eqP.
 case=> x Hx ->{A} /=; rewrite /quotient_canonical_proj.
  suff ->: H :* x = H by rewrite if_same.
  by rewrite -{1 3}(rcoset1 H) in Hx *; rewrite (rcoset_trans1 gH Hx).
move=> dA; exists (1 : elt); first exact: group1.
by apply: coset_set_inj; rewrite /set_of_coset /= /quotient_canonical_proj rcoset1 if_same.
Qed.

End TrivialQuotient.


Section Isomporhism_theorems.


Section FirstTheorem.

Open Scope group_scope.
 
Variables (elt elt' : finGroupType) (H : setType elt).

Hypothesis gH: group H.

Variable f : elt -> elt'.
Hypothesis mf : morphism H f.

Notation Local K := (ker H f).

Let gK := ker_grp mf gH.

Notation Local modK := (coset_groupType gK).

Let norm_HmodK := normal_ker mf gH.

Let group_HmodK := group_quotient gK gH norm_HmodK.

Definition fquo := (fun x : modK => f (repr x)).

Section StrongFirstIsoTheorem.

Variable K' : setType elt.
Hypothesis gK' : group K'.

Notation Local modK' := (coset_groupType gK').

Notation Local fquo' := (fun x : modK' => f (repr x)).


Hypothesis sK'K : subset K' K.
Hypothesis norm_HmodK' : normal K' H.


Notation Local norm_KmodK' := (normal K).

Lemma fquo'_coset : forall x, H x -> fquo' (coset K' x) = f x.
Proof.
move=> x Hx; rewrite /set_of_coset /= /quotient_canonical_proj (subsetP norm_HmodK') //.
move/rcosetP: (repr_rcoset gK' x)=> [y K'y ->].
case/isetIP: (subsetP sK'K y K'y); rewrite !s2f; move/eqP=> Dfy Hy.
by rewrite mf // -Dfy mul1g.
Qed.


Lemma morph_fquo : morphism (H /K') fquo'.
Proof.
move=>fx fy; rewrite /quotient;  move/iimageP=>[x Hx ->]; move/iimageP=>[y Hy ->].
by rewrite -morphism_coset ?(subsetP norm_HmodK') // !fquo'_coset ?groupM // mf.
Qed.


Lemma ker_fquo : ker (H / K') fquo' = K / K'.
Proof.
apply/isetP=> K'x; rewrite !s2f andbC; apply/andP/iimageP.
 case; move/iimageP=> [x Hx ->]; rewrite fquo'_coset // => Kx;  exists x=> //.
 by rewrite !s2f Kx Hx.
case=> x; rewrite !s2f; move/andP=> [Kx Hx] ->; rewrite fquo'_coset //; split => //.
by apply/iimageP; exists x.
Qed.


End StrongFirstIsoTheorem.

Lemma fquo_isomorph :  isomorphism (H /K) fquo.
Proof.
rewrite/fquo; split; first by  apply: morph_fquo=>//; exact: subset_refl.
by rewrite /trivg ker_fquo ?subset_refl // (trivial_quotient gK) subset_refl.
Qed.


(* (preimage coset) definit une bijection entre les sous groupes de *)
(* H/Ker et les sous groupes de H qui contiennent le ker *)

End FirstTheorem.

Section SecondTheorem.




End SecondTheorem.



Section Third_theorem.

Open Scope group_scope.

 
Variables (elt : finGroupType) (G H K : setType elt).

Hypothesis gG : group G.
Hypothesis gH : group H.
Hypothesis gK : group K.

Hypothesis sHK : subset H K.
Hypothesis sKG : subset K G.

Hypothesis nHG : normal H G.
Hypothesis nKG : normal K G.

Let KmodH := K / H.
Let GmodH := G / H.

Notation Local nHK := (normal_subset nHG sKG).

Notation Local gKmodH := (group_quotient gH gK nHK).

Notation Local gGmodH := (group_quotient gH gG nHG).

Let modH := coset_groupType gH.

Notation Local Nh := (normaliser H).

Let gNh := group_normaliser H.

Lemma nKmodH_GmodH : @normal modH KmodH GmodH.
Proof. apply: morph_normal_im=> //; apply: (morph_r nHG); exact: morphism_coset. Qed.

Let modK := coset_groupType gK.

Definition third_grp_iso (u : coset_groupType gKmodH) : modK := 
  coset K (repr (repr u)).

Lemma morphism_third_grp_iso : morphism ((G / H) / (K / H)) third_grp_iso.
Proof.
have mKG := morph_r nKG (morphism_coset gK).
have sKkK : subset K (@ker _ modK G (coset K)).
  apply/subsetP=> x Hx; rewrite !s2f (subsetP sKG) // andbT.
  suff: (K / K) (coset K x) by rewrite (trivial_quotient gK) !s2f.
  by apply/iimageP; exists x.
have sHkK := subset_trans sHK sKkK.
apply: (@morph_fquo _ _ _ gGmodH (fun u : modH => coset K (repr u))) _ nKmodH_GmodH.
  apply: morph_fquo=> //.
rewrite ker_fquo //; apply/subsetP=> A; case/iimageP=> x Kx ->{A}.
apply/iimageP; exists x=> //; exact: (subsetP sKkK).
Qed.

Let modKmodH := coset_groupType gKmodH.

Lemma ker_third_group_iso : trivg (ker ((G / H) / (K / H)) third_grp_iso).
Proof.
apply/subsetP=> x. 


rewrite  (ker_fquo gKmodH).
have mKG := morph_r nKG (morphism_coset gK).
Check ker_fquo.

 rewrite !s2f; case/andP=> H1x Hx.


(* ker -> isomorphisme *)

End Third_theorem.


End Isomporhism_theorems.


Unset Implicit Arguments.




