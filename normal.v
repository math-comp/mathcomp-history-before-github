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


Lemma norm_coset : 
  forall (L : group elt) x y, 
     L :* x = L :* y -> normaliser L x = normaliser L y.
Proof.
move=> L x y Lxy; apply/idP/idP => Ny.
  have : (L :* x) y by rewrite Lxy rcoset_refl.
  case/rcosetP=> l Ll ->.
  by rewrite groupM // (subsetP (norm_refl L)).
have : (L :* y) x by rewrite -Lxy rcoset_refl.
case/rcosetP=> l Ll ->.
by rewrite groupM // (subsetP (norm_refl L)).
Qed.

End Normal.

(* restreindre aux groups *)
Notation "H '<|' K" := (normal H K)(at level 50):group_scope.

Section NormalProp.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : setType elt).

Hypothesis subset_HK : subset H K.
Hypothesis nHK : H <| K.

Theorem normal_subset: forall L : setType elt, subset L K ->  H <| L.
Proof. move=> L HLK; exact: subset_trans HLK _. Qed.

Theorem norm_normal: H <| (normaliser H).
Proof. exact: subset_refl. Qed.

End NormalProp.


Section Morphism.

Open Scope group_scope.

Variables (elt elt' : finGroupType) (H : group elt) (H' : group elt').

Variable f : elt -> elt'.

Definition morphismb (A : setType elt) :=
  subset A (fun x => subset A (fun y => f (x * y) == (f x) * (f y))).

Definition morphism(A : setType elt) := forall x y, 
  A x -> A y -> f (x * y) = (f x) * (f y).

Lemma morphismP : forall A, reflect (morphism A) (morphismb A).
Proof.
move=> A; apply: (iffP subsetP).
  by move=> mA x y; move/mA; move/subsetP=> mAx; move/mAx; move/eqP.
by move=> mA x Ax; apply/subsetP=> y Ay; rewrite mA.
Qed.

Hypothesis mf : morphism H.

Lemma morph1 :  f 1 = 1.
Proof. by apply: (mulg_injl (f 1)); rewrite -mf ?group1 // !mulg1. Qed.

Lemma morphE : forall x n, 
  H x -> f (x ** n) = (f x) ** n.
Proof.
move=> x n Hx; elim: n => [| n Hrec]; first by rewrite !gexpn0 morph1.
by rewrite !gexpnS mf // ?Hrec // groupE.
Qed.

Lemma morphV: forall x, 
  H x -> f (x ^-1) = (f x) ^-1.
Proof.
by move=> x Hx; apply: (mulg_injl (f x)); rewrite -mf ?groupV // !mulgV morph1.
Qed.

Lemma morph_conjg : forall x y, H x -> H y -> f (x ^ y) = (f x) ^ (f y).
Proof. move=> x y Hx Hy; rewrite/conjg -morphV // -!mf // ?groupM // groupV //. Qed.


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
rewrite ?iimage_smul ?(iimage_set1 f) // ?subset_set1 ?groupV // -smulgg. 
apply: (@subset_trans _ _ (H :*: A)); [apply smulsg |apply smulgs]; rewrite ?subset_set1 //.
by rewrite ?groupV.
Qed.



Lemma morph_image_group_set : group_set (f @: H).
Proof.
apply/andP; split.
 by apply/iimageP; exists (1:elt); [apply: group1=>//| symmetry; exact: morph1].
by rewrite -iimage_smul ?smulgg // subset_refl.
Qed.

Canonical Structure morph_im_group := Group morph_image_group_set.


Lemma morph_preimage_group_set : subset (f @^-1: H') H -> group_set (f @^-1: H').
Proof.
move/subsetP=>Hsubset; apply/andP.
split; first by rewrite !s2f morph1 group1.
apply/subsetP=> x Hx; case/smulgP:Hx => x1 x2; rewrite !s2f => H1 H2 ->.
by rewrite mf  ?groupM // Hsubset // !s2f.
Qed.

(* define a canonical structure for preimage?*)

Variable K : group elt.

Hypothesis subset_KH : subset K H.


Lemma morph_normal_im : K <| H -> (f @: K) <| (f @: H).
Proof.
move/normalP=> Hn; apply/normalP => x; move/iimageP=> [u Hu ->].
by rewrite -iimage_conj // Hn.
Qed.

Section Ker.

Definition ker (A : setType elt) := 
  if morphismb A then (f @^-1: {:1}) :&: A else {:1}.

Lemma subset_ker : forall G : group elt, subset (ker G) G.
Proof. by rewrite /ker => G; case: ifP => _; rewrite ?subsetIr // subset_set1. Qed.



Lemma kerP : forall x, reflect (H x /\ f x = 1) (ker H x).
Proof.
move=> x; rewrite /ker (introT (morphismP _) mf) !s2f eq_sym.
apply: (iffP andP); case; split=> //; exact/eqP.
Qed.


Lemma ker_group_set : forall G : group elt, group_set (ker G).
Proof.
rewrite /ker => G; case: morphismP => [mf1 | _]; last exact: set_of_groupP.
apply/groupP; split=> [|x y]; rewrite !s2f.
  by rewrite group1 andbT -(eqtype.can_eq (mulKg (f 1))) -mf1; gsimpl.
move/andP=> [fx1 Gx]; move/andP=> [fy1 Gy]; rewrite groupM // andbT mf1 //.
by rewrite -(eqP fx1) -(eqP fy1); gsimpl.
Qed.

Canonical Structure ker_group G := Group (ker_group_set G).

Lemma ker1 : forall x, ker H x -> f x = 1.
Proof. by move=> x; case/kerP. Qed.

Lemma normal_ker : (ker H) <| H.
Proof.
apply/subsetP=> x Hx; rewrite s2f; apply/subsetP=> y; rewrite -{1}(invgK x) sconjgE.
case/kerP=> Hyx fyx1; apply/kerP; split; first by rewrite groupJr ?groupV in Hyx.
by rewrite -(conjgKv x y) morph_conjg // fyx1 conj1g.
Qed.

Lemma triv_kerP : 
  reflect (forall x y, H x -> H y -> (f x = f y -> x = y)) (trivg (ker H)).
Proof.
apply: (iffP idP).
  move/subsetP=> H1 x y Hx Hy Hxy; apply (mulg_injl (y^-1)); rewrite mulVg.
  suff: {:1} (y ^-1 * x) by rewrite s2f; move/eqP; auto.
  by apply H1; apply/kerP; rewrite mf ?groupMl ?groupV // Hxy -mf ?mulVg ?morph1; auto.
move=> H1; apply/subsetP=> x; case/kerP=> Hx fx1; rewrite s2f; apply/eqP; apply: H1 => //.
by rewrite fx1 morph1.
Qed.

Definition isomorphism (A : setType elt) := (morphism A) /\ (trivg (ker A)).

End Ker.


End Morphism.


Section MorphismRestriction.


Open Scope group_scope.

Variables (elt elt' : finGroupType) (H : setType elt).
Variable f : elt -> elt'.

Hypothesis mfH : morphism f H.


Section SetMorphRestrictions.

Variable K : setType elt.

Hypothesis sHK : subset K H.



Lemma morph_r : morphism f K.
Proof. by move=> x y Kx Ky; apply: mfH; apply (subsetP sHK). Qed.


Lemma subset_ker_r : subset (ker f K ) (ker f H).
Proof.
apply/subsetP=> x; rewrite /ker; move/morphismP: mfH=> ->; move/morphismP: morph_r=> ->.
by rewrite !s2f; case/andP=> H1 Kx; rewrite (subsetP sHK) ?andbT.
Qed.

End SetMorphRestrictions.


Variable K : group elt.

Hypothesis sHK : subset K H.

Lemma ker_r : (ker f K) = K :&: (ker f H).
Proof.
apply/isetP=> x; rewrite !s2f; apply/idP/andP.
  by move=> H1; rewrite (subsetP (subset_ker_r sHK)) // (subsetP (subset_ker f K )).
case=> Kx; rewrite /ker; move/morphismP: (morph_r sHK)=> ->; move/morphismP: mfH=> ->.
by rewrite !s2f; rewrite Kx andbT; case/andP.
Qed.



End MorphismRestriction.


Section MorphismComposition.


Open Scope group_scope.

Variables (elt1 elt2 elt3 : finGroupType) (H : group elt1).

Variable f : elt1 -> elt2.
Variable g : elt2 -> elt3.

Hypothesis mf : morphism f H.
Hypothesis mg : morphism g (iimage f H).

Lemma morph_c : morphism (g \o f) H.
Proof. 
by move=> x y Hx Hy; rewrite /comp mf  ?mg //; apply/iimageP; [exists x | exists y] => //.
Qed.

Lemma im_morph_c : (g \o f) @: H = g @: (f @: H).
Proof.
apply/isetP=> x; rewrite/comp; apply/iimageP/iimageP.
 by case=> y Hy ->; exists (f y)=> //; apply/iimageP; exists y.
by case=> y; move/iimageP; case=> z Hz -> ->; exists z.
Qed.

Lemma ker_morph_c : ker (g \o f) H =  ( f @^-1: (ker g (f @: H)) ) :&: H.
Proof.
have:= kerP mg; move/(_ mf)=> Kg.
apply/isetP => x; rewrite !s2f; apply/(kerP morph_c)/andP; last by case; case/Kg.
by case=> Hx gfx1; split=> //; apply/Kg; split=> //; apply/iimageP; exists x.
Qed.


End MorphismComposition.


Section Cosets.

Open Scope group_scope.

Variables (elt : finGroupType) (H : setType elt).


(* is it elsewhere ?*)

(* Search eq [subset {: _}].*)
Lemma subset1 : forall (d : finType) (A : set d) x, subset {:x} A = A x.
Proof.
move=> d A x; apply/subsetP/idP; first by move=> sAx; apply (sAx x); rewrite s2f.
by move=> Ax y; rewrite s2f; move/eqP=> <-.
Qed.

Lemma normalized_refl : forall A : group elt, normalized A A.
Proof. move=> A; rewrite /normalized;  exact: norm_refl. Qed.


Lemma gmulgg : forall A : group elt, A :**: A = A.
Proof. by move=> A; rewrite -norm_gmulr ?smulgg // normalized_refl. Qed.

Lemma norm_normalized : forall (A : setType elt) x, normaliser A x = normalized A {:x}.
Proof. by move=> A x; rewrite /normalized subset1. Qed.


(* bad name *)
Lemma norm_grcoset : forall (A : setType elt) x,
  normaliser A x -> A :**: {:x} = A :* x.
Proof. by move=> A x Nx; rewrite -norm_gmulr -?norm_normalized // -rcoset_smul. Qed.

Lemma grcoset_id : forall (A : group elt) x,
  A x -> A :**: {:x} = A.
Proof. 
by move=> A x Ax; rewrite norm_grcoset ?rcoset_id // (subsetP (norm_refl A)). Qed.


(* move to groups ? *)

Definition coset (A : setType elt) (x : elt) := 
      if (normaliser A x) then A :**: {:x} else A.

Notation "A ':**' x" := (coset A x) (at level 40) : group_scope.


Lemma cosetN : forall A x, normaliser A x -> A :** x = A :* x.
Proof. by move=> A x Nx; rewrite /coset Nx ?gmul_refl norm_grcoset. Qed.


Lemma cosetD : forall A x, normaliser A x = false -> A :** x = A.
Proof. by move=> A x Nx; rewrite /coset Nx. Qed.

Definition cosets := iimage (coset H) elt.

Lemma cosetsP: forall H1, reflect (exists x, coset H x = H1) (cosets H1).
Proof.
move => H1.
apply: (iffP idP).
  by move/iimageP => [x2 _ Hx2]; exists x2.
by move => [x Hx]; apply/iimageP; exists x.
Qed.


CoInductive cosetType : Type := Coset of eq_sig cosets.

Definition sig_of_coset u := let: Coset v := u in v.

Remark sig_of_cosetK : cancel sig_of_coset Coset. Proof. by case. Qed.

Canonical Structure coset_eqType := EqType (can_eq sig_of_cosetK).
Canonical Structure coset_finType := FinType (can_uniq sig_of_cosetK).

Coercion set_of_coset u := val (sig_of_coset u) : setType elt.

Lemma coset_set_inj : injective set_of_coset.
Proof. exact: inj_comp (@val_inj _ _) (can_inj sig_of_cosetK). Qed.


Lemma coset1 : H :** 1 = H.
Proof.
by rewrite cosetN ?rcoset1 // s2f sconj1g subset_refl.
Qed.

Lemma coset_id : forall A: group elt, forall x,  A x -> coset A x = A.
Proof. 
by move=> A x Hx; rewrite /coset (subsetP (norm_refl A)) ?grcoset_id. Qed.


Lemma cosets_unit : cosets H.
Proof. by apply/iimageP;  exists (1:elt)=> //;  rewrite coset1. Qed.

Definition coset_unit := Coset (EqSig _ _ cosets_unit).


End Cosets.

Notation "A ':**' x" := (coset A x) (at level 40) : group_scope.

Section Repr.

Variables (elt: finGroupType) (H: group elt).


Lemma mem_coset_repr: forall H1, cosets H H1 -> H1 (repr H1).
Proof.
move => H1; case/cosetsP => x <-.
case E1: (normaliser H x).
  rewrite cosetN //.
  apply: (@mem_repr _ x); exact: rcoset_refl.
rewrite cosetD //.
by apply: (@mem_repr _ 1%G); exact: group1.
Qed.


Theorem coset_repr: forall x, H :** (repr (H:** x)) = H:** x.
Proof.
move => x.
case E1: (normaliser H x).
  rewrite (@cosetN _ _ x) //.
  have F1: normaliser H (repr (H :* x)).
    move: E1; rewrite !s2f.
    case: repr_rcosetP => y Hy.
    rewrite sconjgM (@norm_sconjg _ _ y) //.
    by apply: (subsetP (norm_refl _)).
  by rewrite cosetN // rcoset_repr.
rewrite (@cosetD _ _ x) // cosetN.
  rewrite rcoset_id //.
  by apply: (@mem_repr _ 1%G); exact: group1.
apply: (subsetP (norm_refl H)).
by apply: (@mem_repr _ 1%G); exact: group1.
Qed.
End Repr.


Section CosetGroup.


Open Scope group_scope.

Variables (elt : finGroupType) (H : group elt).

Notation Local N := (normaliser H).

Lemma cosets_mul : forall Hx Hy : cosetType H, cosets H (Hx :*: Hy).
Proof.
rewrite /set_of_coset => [] [[Hx nHx]] [[Hy nHy]] /=.
case/iimageP: nHx => [x _ ->{Hx}]; case/iimageP: nHy => [y _ ->{Hy}].
case Nx: (normaliser H x); rewrite ?(cosetN Nx) ?(cosetD Nx).
  case Ny: (normaliser H y); rewrite ?(cosetN Ny) ?(cosetD Ny).
  -by apply/iimageP; exists (x * y)=> //; rewrite cosetN ?groupM // rcoset_mul.
  -by apply/iimageP; exists x=> //; rewrite cosetN ?norm_rlcoset // lcoset_smul -smulgA smulgg.
case Ny: (normaliser H y); rewrite ?(cosetN Ny) ?(cosetD Ny).
  - by apply/iimageP; exists y=> //; rewrite rcoset_smul smulgA smulgg cosetN ?rcoset_smul.
  - by apply/iimageP; exists (1: elt)=> //; rewrite smulgg coset1.
Qed.

Definition coset_mul Hx Hy := Coset (EqSig _ _ (cosets_mul Hx Hy)).

Lemma cosets_inv : forall Hx : cosetType H, cosets H (Hx :^-1).
Proof.
rewrite /set_of_coset => [] [[A]] /=.
move/iimageP=>[x _ ->{A}]; apply/iimageP; exists x ^-1=>//.
case Nx: (normaliser H x); last by rewrite /coset groupV Nx ?sinvG //.
by rewrite !cosetN ?groupV // norm_rlcoset // sinvg_lcoset.
Qed.

Definition coset_inv Hx := Coset (EqSig _ _ (cosets_inv Hx)).

Lemma coset_unitP : forall Hx, coset_mul (coset_unit H) Hx = Hx.
Proof.
move=> [[Hx nHx]]; apply: coset_set_inj; do 3!rewrite /set_of_coset /=.
case/iimageP: nHx => [x _ ->{Hx}].
case Nx: (normaliser H x); last by rewrite /coset Nx smulgg.
by rewrite cosetN // rcoset_smul smulgA smulgg.
Qed.

Lemma coset_invP : forall Hx, coset_mul (coset_inv Hx) Hx = coset_unit H.
Proof.
move=> [[Hx nHx]]; apply: coset_set_inj; do 3!rewrite /set_of_coset /=.
case/iimageP: nHx => [x _ ->{Hx}].
case Nx: (normaliser H x); last by rewrite /coset Nx sinvG smulgg.
by rewrite cosetN // {1}norm_rlcoset ?sinvg_lcoset ?rcoset_mul ?mulVg ?rcoset1 ?groupV.
Qed.

Lemma coset_mulP : forall Hx Hy Hz,
  coset_mul Hx (coset_mul Hy Hz) = coset_mul (coset_mul Hx Hy) Hz.
Proof.
move=> [[Hx nHx]] [[Hy nHy]] [[Hz nHz]]; apply: coset_set_inj.
do 3!rewrite /set_of_coset /=; case/iimageP: nHx => [x _ ->{Hx}].
by case/iimageP: nHy => [y _ ->{Hy}]; rewrite smulgA.
Qed.

Canonical Structure coset_groupType :=
  FinGroupType coset_unitP coset_invP coset_mulP.

Lemma set_of_coset_morph : forall x y : coset_groupType,
  set_of_coset (x * y) = (set_of_coset x) :*: (set_of_coset y).
Proof. by move=> *; constructor. Qed.

Lemma cosetP : forall x : coset_groupType, exists y, set_of_coset x = H :** y.
Proof.
case=> [[e]]; rewrite /cosets; move => y.
by case: (iimageP _ _ _ y)=> z _ He; exists z; rewrite /set_of_coset.
Qed.



Section Quotient.



(* This is in fact HK/H *)

(*Definition quotient_canonical_proj x := if N x then rcoset H x else H.*)


Lemma cosets_coset : forall (A : setType elt) x, cosets A (A :** x).
Proof.
move=> A x; rewrite/coset; case Nx: (normaliser A x); last by exact: cosets_unit.
by apply/iimageP; exists x=> //; rewrite /coset Nx.
Qed.

Definition coset_of (A : setType elt) x := Coset (EqSig _ _ (cosets_coset A x)).

Lemma coset_of_id : forall x, H x -> coset_of H x = 1.
Proof.
move=> x Hx; apply: coset_set_inj.
by rewrite /set_of_coset /= /coset_of /set_of_coset /= coset_id.
Qed.


Lemma morph_coset_of : morphism (coset_of H) N.
Proof.
move=> x y Nx Ny; apply: coset_set_inj.
by rewrite /set_of_coset /= /coset_of /set_of_coset /= !cosetN ?groupM // rcoset_mul.
Qed.

Lemma coset_ofE : forall x n, N x -> coset_of H (x ** n) = (coset_of H x) ** n.
Proof.
by move=> x n Hx; apply: (morphE (morph_coset_of)).
Qed.


Lemma coset_ofV : forall x, N x -> coset_of H (x ^-1) = (coset_of H x)^-1.
Proof.
by move=> x Hx; apply: (morphV (morph_coset_of)).
Qed.

Lemma ker_cosetP : forall x, N x -> reflect (H x) ((coset_of H) x == 1).
Proof.
move=> x Nx; apply: (iffP idP).
 move/eqP=>[]; rewrite /coset_of /coset Nx => <-. 
 by rewrite -norm_gmulr ?rcoset_smul -?norm_normalized // -rcoset_smul rcoset_refl.
move=> Hx; apply/eqP; apply: coset_set_inj;  rewrite  /set_of_coset /= /coset_of /coset Nx.
by rewrite norm_grcoset // rcoset_id.
Qed.

Lemma ker_coset_of : ker (coset_of H) N = H.
Proof.
apply/isetP=> x; apply/(kerP morph_coset_of)/idP.
  by case=> /= Nx; move/eqP; move/ker_cosetP; apply.
by move=> Hx; split; first exact: subsetP (norm_refl _) _ Hx; rewrite coset_of_id.
Qed.

Definition quotient (A B : setType elt) := (coset_of B) @: A.

Notation "H / K" := (quotient H K).

Lemma quotientP : forall (A : group elt) (B : setType elt) (C : cosetType B), 
  reflect (exists x, and3 (A x) (normaliser B x) (C = coset_of B x))
          ((A/B) C).
Proof. 
move=> A B Bx; rewrite (_:(A / B) Bx = (((normaliser B) :&: A) / B) Bx).
  apply:(iffP (iimageP _ _ _)); case.
    by move=> x; case/isetIP=> Nx Ax ->; exists x.
  by move=> x [Ax Nx ->]; exists x => //; apply/isetIP.
apply/iimageP/iimageP; case=> x.
  move=> Ax; rewrite /coset_of /coset. 
  case: Bx; case=> Be BeB=> [[C]]; move: C.
  case Nx : (normaliser B x)=> dBe.
    exists x; first by apply/isetIP.
    apply: (can_inj (@sig_of_cosetK elt B)); apply: val_inj=> /=.
    by rewrite Nx.
  exists (1:elt); first by apply/isetIP; rewrite !group1.
  apply: (can_inj (@sig_of_cosetK elt B)); apply: val_inj=> /=.
  by rewrite group1 gmulg1.
by case/isetIP=> Nx Ax ->; exists x.
Qed.


Lemma iimage_quotientP: 
  forall A B: group elt, forall (t : finType) (f : _ -> t), 
   (f @: (A/B) = f @: ((A :&: normaliser B)/B)).
Proof.
move=> A B t f; apply/isetP=> x; apply/iimageP/iimageP;
case=> By; case/iimageP=> y Ay dBy ->; case Ny: (normaliser B y);
exists By => //; apply/iimageP.
- by exists y => //; apply/isetIP.
- exists (1:elt) => //; first by apply/isetIP; rewrite !group1.
  rewrite dBy; apply: (can_inj (@sig_of_cosetK elt B)); apply: val_inj=> /=.
  by rewrite cosetD // coset1.
- by exists y => //; case/isetIP: Ay.
by exists (1:elt) => //; case/isetIP: Ay; rewrite Ny.
Qed.
 
Variable K : group elt.

Lemma group_set_quotient : group_set (quotient K H).
Proof. 
suff ->: quotient K H = coset_of H @: (K :&: N).
  apply: morph_image_group_set=> //; apply: (morph_r morph_coset_of); exact: subsetIr.
apply/isetP=> C; apply/iimageP/iimageP=> [] [x Kx ->{C}]; last by case/isetIP: Kx; exists x.
case Nx: (N x); first by exists x; first exact/isetIP.
exists (1 : elt); first rewrite s2f !group1 //.
by apply: coset_set_inj; rewrite /set_of_coset /= {1}/coset Nx coset_id.  
Qed.


Canonical Structure group_quotient := Group group_set_quotient.

End Quotient.

End CosetGroup.

Section Rep.

Variable elt: finGroupType.
Variable H: group elt.


Lemma coset_group_repr: forall (y: coset_groupType H), y (repr y).
Proof.
move => y; case: (cosetP y).
move => z1  ->.
case E1: (normaliser H z1).
  rewrite cosetN //.
  apply: (@mem_repr _ z1).
  by apply/rcosetP; exists (1:elt); rewrite ?group1; gsimpl.
rewrite cosetD //.
by apply: (@mem_repr _ 1); rewrite group1.
Qed.

Lemma coset_of_repr: forall (y: coset_groupType H), 
  coset_of H (repr y) = y.
Proof.
move => y.
case y; case => u Hu /=.
apply: coset_set_inj.
rewrite /coset_of /= /set_of_coset /=.
move: (coset_repr H).
by case/cosetsP: Hu => z <-.
Qed.

Lemma repr_1: forall (y: coset_groupType H),
  reflect (H (repr y)) (y == 1).
Proof.
move => y; apply: (iffP idP) => Hx1.
  rewrite (eqP Hx1).
  apply: (@mem_repr _ 1); exact: group1.
rewrite -(coset_of_repr y).
by apply/eqP; apply: coset_of_id.
Qed.

Lemma cosetV_repr: forall (x: coset_groupType H), 
  (x^-1)%G  ((repr x)^-1).
Proof.
move => x; rewrite /coset_inv /=.
rewrite /coset_of /= /set_of_coset /=.
case: x => /=.
case => /= x1 Hx1.
rewrite /set_of_coset s2f /=; gsimpl.
by apply: (@mem_coset_repr _ H).
Qed.

Lemma cosetM_repr: forall (x y: coset_groupType H), 
  (x * y)%G  (repr x * repr y).
Proof.
move => x y; rewrite /coset_mul /=.
rewrite /coset_of /= /set_of_coset /=.
case: x; case: y => /=.
case => /= x1 Hx1.
case => /= x2 Hx2.
apply/smulgP; exists (repr (x2)) (repr x1) => //;
  by apply: (@mem_coset_repr _ H).
Qed.

Lemma cosetE_repr: forall (x: coset_groupType H) n, 
  (x ** n)%G  (repr x ** n).
Proof.
move => x; elim => [|n Hrec].
  rewrite !gexpn0; exact: group1.
rewrite !gexpnS.
rewrite /coset_of /= /set_of_coset /=.
apply/smulgP; exists (repr x) (repr x ** n) => //.
exact: coset_group_repr.
Qed.

Notation "H / K" := (quotient H K).

Variable K: group elt.
Hypothesis HK: subset K H.

Lemma quotient_repr: forall x, (H/K) x -> H (repr x).
Proof.
move => x; rewrite /quotient.
move/iimageP => [y Hy ->].
rewrite /coset_of /= /set_of_coset /=.
case E1: (normaliser K y).
  rewrite cosetN //.
  case: repr_rcosetP => y1 Hy1.
  by apply: groupM  => //; apply: (subsetP HK).
rewrite cosetD //.
apply: (subsetP HK).
apply: (@mem_repr _ 1); exact: group1.
Qed.

End Rep.

Notation "H / K" := (quotient H K).

Section Card.

Variable elt: finGroupType.
Variable H K: group elt.
Hypothesis HK: subset K H.
Hypothesis nKH : K <| H.

Lemma quotient_card:
  card H = (card (H/K) * card K)%N.
Proof.
have F1: (partition (H/K) (fun x => K :* (repr x)) H).
  split.
    move => u v x Hu Hv /= Hsu Hsv.
    apply: (@trans_equal _ _ (1 * u)); first gsimpl.
    have F1:= (quotient_repr HK Hu).
    have F2:= (quotient_repr HK Hv).
    case/rcosetP: Hsu => k1 Hk1.
    case/rcosetP: Hsv => k2 Hk2 -> HH.
    have F3: K (repr v * (repr u)^-1) by 
      rewrite -(mul1g (_ * _)) -(mulVg k2) -mulgA
              (mulgA k2) HH -!mulgA mulgV mulg1 groupM // groupV.
    have F4: normaliser K (repr v * (repr u)^-1).
      by apply (subsetP nKH); rewrite groupM // groupV.
    move/(ker_cosetP F4): F3.
    rewrite morph_coset_of; try
        (by apply (subsetP nKH); rewrite ?groupV).
    rewrite coset_of_repr.
    rewrite coset_ofV; last
        (by apply (subsetP nKH); rewrite ?groupV).
    rewrite coset_of_repr.
    move => F5; rewrite -(eqP F5); gsimpl.
  apply/coverP; split => x Hx.
    apply/subsetP => y; case/rcosetP => z Kz ->.
    rewrite groupM //; first exact: (subsetP HK).
    by apply: quotient_repr.
  exists (coset_of K x).
  have F1: H (repr (coset_of K x)).
    apply quotient_repr => //.
    by apply/iimageP; exists x.
  apply/andP; split; first by apply/iimageP; exists x.
  apply/rcosetP.
  exists (x * (repr (coset_of K x))^-1); last gsimpl.
  apply/ker_cosetP; first 
    by apply (subsetP nKH); rewrite groupM // groupV.
  rewrite morph_coset_of; try 
    by apply (subsetP nKH); rewrite // groupV.
  rewrite coset_ofV; last by apply (subsetP nKH).
  by rewrite coset_of_repr; gsimpl.
apply: (card_partition_id F1) => x Hx.
by rewrite card_rcoset.
Qed.

Lemma quotient_indexg: card (H/K) = indexg K H.
Proof.
have F1: card K == 0 = false by case: card (pos_card_group K).
  by apply/eqP; rewrite -[_==_]orFb -F1 -eqn_mul2l
                        LaGrange // quotient_card mulnC.
Qed.

End Card.


Section TrivialQuotient.

Open Scope group_scope.

Variables (elt : finGroupType) (H : group elt).

Lemma trivial_quotient : (H / H) = {: 1}.
Proof.
apply/isetP=> A; rewrite s2f /set1 /= /set1 /=; apply/iimageP/eqP.
  by case=> x Hx ->{A} /=; rewrite coset_id.
move=> dA; exists (1 : elt); first by rewrite !group1.
by apply: coset_set_inj; rewrite /set_of_coset /= coset1.
Qed.


End TrivialQuotient.

Lemma foobar : True. done. Qed.

Section FirstTheorem.

Open Scope group_scope.
 
Variables elt elt' : finGroupType.

Definition fquo H (f : elt -> elt') (Hx : cosetType H) := f (repr Hx).

Variables (H : group elt) (f : elt -> elt').
Hypothesis mf : morphism f H.

Notation Local K := (ker f H).

Let nKH := normal_ker mf.

(*Let group_HmodK := group_quotient gK gH norm_HmodK.*)

Section StrongFirstIsoTheorem.

Variable K' : group elt.

Hypothesis sK'K : subset K' K.

Hypothesis nK'H : K' <| H.

(*Notation Local norm_KmodK' := (normal K).*)

Lemma fquo_coset : forall x, H x -> fquo f (coset_of K' x) = f x.
Proof.
move=> x Hx; rewrite /fquo /set_of_coset /= cosetN ?(subsetP nK'H) //.
case: repr_rcosetP => [y K'y].
rewrite mf ?(ker1 mf (subsetP sK'K _ K'y)) ?mul1g // (subsetP (subset_ker f _)) //.
exact: (subsetP sK'K).
Qed.

Lemma morph_fquo : morphism (fquo f) (H / K').
Proof.
move=> K'x K'y; case/iimageP=> [x Hx ->]; case/iimageP=> [y Hy ->].
by rewrite -morph_coset_of ?(subsetP nK'H) // !fquo_coset ?groupM // mf.
Qed.


Lemma ker_fquo : ker (fquo f) (H / K') = K / K'.
Proof.
apply/isetP=> K'y; apply/(kerP morph_fquo)/iimageP; case.
  move/iimageP=> [x Hx ->]; rewrite fquo_coset // => Kx; exists x=> //; exact/kerP.
move=> x; case/kerP=> // Kx Hx ->; rewrite fquo_coset //; split => //.
by apply/iimageP; exists x.
Qed.


End StrongFirstIsoTheorem.

Lemma fquo_isomorph :  isomorphism (fquo f) (H / K).
Proof.
rewrite/fquo; split; first by  apply: morph_fquo=>//; exact: subset_refl.
by rewrite /trivg ker_fquo ?subset_refl // trivial_quotient subset_refl.
Qed.


(* (preimage coset) definit une bijection entre les sous groupes de *)
(* H/Ker et les sous groupes de H qui contiennent le ker *)

End FirstTheorem.

Prenex Implicits fquo ker.

Section SecondTheorem.




End SecondTheorem.



Section Third_theorem.

Open Scope group_scope.

Variables (elt : finGroupType) (G H K : group elt).


Hypothesis sHK : subset H K.
Hypothesis sKG : subset K G.

Notation Local sHG := (subset_trans sHK sKG).

Hypothesis nHG : H <| G.
Hypothesis nKG : K <| G.

Notation Local nHK := (normal_subset nHG sKG).

(*
Let KmodH := {K / H as group _}.
Let GmodH := {G / H as group _}.
Let GmodHmodKmodH := { (G / H) / (K / H) as group _}.
*)

(*Notation Local gKmodH := (group_quotient gH gK nHK).

Notation Local gGmodH := (group_quotient gH gG nHG).
*)

Let modH := coset_groupType H.

Notation Local Nh := (normaliser H).

(*Let gNh := group_normaliser H.*)

Lemma nKmodH_GmodH : (K / H) <| (G / H).
Proof. 
apply: morph_normal_im=> //; apply: (morph_r _ nHG); exact: morph_coset_of. 
Qed.
(*
Let modK := coset_groupType K.

Let modKmodH :=  coset_groupType KmodH.
*)

Notation Local f_aux := (fquo (coset_of K)).

Notation Local f3 := (fquo f_aux).

Lemma Il_subset : forall A B : setType elt, subset A B -> A :&: B = A.
Proof.
move=> A B sAB; apply/isetP=> x; apply/isetIP/idP; first by case.
by move=> Ax; rewrite Ax (subsetP sAB).
Qed.


Lemma Ir_subset : forall A B : setType elt, subset B A -> A :&: B = B.
Proof.
move=> A B sBA; apply/isetP=> x; apply/isetIP/idP; first by case.
by move=> Bx; rewrite Bx (subsetP sBA).
Qed.

Lemma morphism_third_grp_iso :
  morphism f3 ((G / H) / (K / H)).
Proof.
have mf : morphism (coset_of K) G by apply: (morph_r _ nKG); exact: morph_coset_of.
have sHker : subset H (ker (coset_of (elt:=elt) K) G).
  by rewrite (ker_r (@morph_coset_of  _ K)) // ker_coset_of Ir_subset.
have kf : ker (coset_of K) G = K.
  by rewrite (ker_r (@morph_coset_of  _ K)) // ker_coset_of Ir_subset.
apply: morph_fquo.
Admitted.

Lemma ker_third_group_iso : trivg (ker f3 ((G / H) / (K / H))).
Proof.
Admitted.
(*
rewrite /set_of_coset /=. quotient_id //.
case/iimageP:GmodHy => z Gz Eyz; rewrite Eyz.
apply/iimageP.
*)

End Third_theorem.




Unset Implicit Arguments.




