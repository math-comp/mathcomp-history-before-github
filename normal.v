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

Variables (G: finGroupType) (H K: set G).

Hypothesis group_H: group H.
Hypothesis group_K: group K.
Hypothesis subset_HK: subset H K.


(********************************************************************)
(*              Definition of a normal set                          *)
(*    H is normal in K iff xHx^-1 = H forall x in K                 *)
(*    it is sufficient that H is included in xHx^¯1                 *)
(*    since both sets have same cardinal                            *)
(********************************************************************)


Definition normal := subset K (normaliser H). 

Theorem normalP:
  reflect (forall x y,  K x -> H y -> H (y ^g x)) normal.
Proof.
apply: (iffP idP).
  move/subsetP => H0 x y H1 H2; exact: (subsetP (H0 x H1)).
move => H0; apply/subsetP => x H1; apply/subsetP => y H2; exact: H0.
Qed.

Theorem conjsg_normal: forall x, 
  normal -> K x -> conjsg H x =1 H.
Proof.
move => x H0 H1 y; apply/idP/idP => H2; last exact: (normalP H0) => //.
  rewrite /conjsg in H2; rewrite -conjs1g -(mulgV x) conjsg_conj; apply: (normalP H0) => //.
  exact: groupVr => //.
Qed.

End Normal.

Section NormalProp.

Open Scope group_scope.

Variables (G : finGroupType) (H K : set G).
Hypothesis subgrp_H: group H.
Hypothesis subgrp_K: group K.
Hypothesis subset_HK: subset H K.
Hypothesis normal_HK: normal H K.

Theorem normal_subset: forall L,
 (* group L -> subset H L ->*) subset L K -> normal H L.
Proof. move=> L HLK; exact: subset_trans HLK _. Qed.

Theorem normaliser_normal: normal H (normaliser H).
Proof. exact: subset_refl. Qed.

End NormalProp.

Section RcosetRepr.

Open Scope group_scope.

Variables (G : finGroupType) (H : set G).
Hypothesis group_H: group H.

Let group_normH := normaliser_grp H.

(* a more appropriate pick for representative in a rcoset *)
Definition rcoset_repr x :=
  if H x then 1 else
  if pick (rcoset H x) is Some y then y else 1.

Lemma rcoset_rcoset_repr : forall x, rcoset H x (rcoset_repr x).
Proof.
rewrite /rcoset_repr => x; case Hx: (H x); first by rewrite rcoset_sym // rcoset1 //.
case pickP => // K; case/idP: {K}(K x); exact: rcoset_refl.
Qed.

(* we could have chosen to set the default values at the identity in *)
(* the definition of rcoset-repr but proving the following lemma by *)
(* rewriting becomes then tedious *)
Lemma rcoset_reprP : forall x y,
  reflect (rcoset_repr x = rcoset_repr y) (rcoset H x y).
Proof.
move => x y; apply: (iffP idP) => [Hxy | Dx].
  rewrite /rcoset_repr (eq_pick (rcoset_trans1 group_H Hxy)) -!(rcoset1 H).
  by rewrite (rcoset_trans1r group_H Hxy).
by rewrite (rcoset_trans1r group_H (rcoset_rcoset_repr y)) -Dx rcoset_rcoset_repr.
Qed.

Lemma rcoset_repr1 : rcoset_repr 1 = 1.
Proof. by rewrite /rcoset_repr [H 1]group1. Qed.

Lemma rcoset_repr1P : forall x, reflect (rcoset_repr x = 1) (H x).
Proof.
move=> x; rewrite -(rcoset1 H) rcoset_sym // -{1}rcoset_repr1; exact: rcoset_reprP.
Qed.

(* rcoset_repr is idempotent *)
Lemma rcoset_repr_rcoset_repr : forall x, 
  rcoset_repr (rcoset_repr x) = rcoset_repr x.
Proof. move=> x; symmetry; apply/rcoset_reprP; exact:rcoset_rcoset_repr. Qed.

End RcosetRepr.

Section Quotient.

Open Scope group_scope.

Variables (G : finGroupType) (H : set G).
Hypothesis group_H: group H.

Let group_normH := normaliser_grp H.

(*********************************************************************)
(*                                                                   *)
(*    Definition of the finite set of all the elements               *)
(*    of N(H) that are canonical element of the right classes of H   *)
(*                                                                   *)
(*********************************************************************)

(* representative for cosets *)
Definition coset_repr x := rcoset_repr H (x * (rcoset_repr (normaliser H) x)^-1).

Lemma coset_reprE : forall x,
  rcoset_repr H (x * (rcoset_repr (normaliser H) x)^-1) = coset_repr x.
Proof. move=> x; by rewrite/coset_repr. Qed.


Lemma norm_coset_repr : forall x, normaliser H (coset_repr x).
rewrite /coset_repr => x.
have H1 : rcoset (normaliser H) x (rcoset_repr (normaliser H) x).
  by rewrite rcoset_rcoset_repr // normaliser_grp //.
move : (rcosetP _ _ _ H1) => [y Hy] -> {H1}.
have H2 : rcoset H (x * (y * x)^-1) (rcoset_repr  H (x * (y * x)^-1)).
  by rewrite rcoset_rcoset_repr //.
move : (rcosetP _ _ _ H2) => [z Hz] -> {H2}; gsimpl.
rewrite groupM //; last by rewrite groupV.
by rewrite (subsetP (subset_normaliser group_H)) //.
Qed.

Lemma coset_repr_rcoset_repr : forall x, 
  normaliser H x -> coset_repr x = rcoset_repr H x.
Proof. 
rewrite /coset_repr => x; move /(rcoset_repr1P (normaliser_grp H)) => ->; gsimpl.
Qed.


Lemma coset_reprP : forall x y, normaliser H x -> normaliser H y ->
  reflect (coset_repr x = coset_repr y) (rcoset H x y).
Proof.
move=> x y Hx Hy; rewrite !coset_repr_rcoset_repr //=; exact: rcoset_reprP. 
Qed.


Lemma rcoset_coset_repr : forall x y, rcoset H x y -> coset_repr x = coset_repr y.
Proof. 
move=> x y Hxy; rewrite /coset_repr.
have Hxy2 : rcoset (normaliser H) x y. 
  case/rcosetP: Hxy => z Hz ->; apply/rcosetP; exists z => //. 
  by rewrite (subsetP (subset_normaliser group_H)).
rewrite (rcoset_reprP group_normH _ _ Hxy2).
case/rcosetP : Hxy => z Hz ->; apply /rcoset_reprP =>//; apply /rcosetP; exists z =>//.
by gsimpl.
Qed.

(* WARNING : here we introduce a fake dependancy on group_H because otherwise
the canonical structure to be define would not identify the proof of (group H)
 to be use and hense would become useless *)


Definition coset_set : set G := (fun _ x => coset_repr x == x) group_H.

Lemma coset_set_coset_repr : forall x, coset_set (coset_repr x).
Proof.
move=> x; rewrite /coset_set {1}/coset_repr {2}/rcoset_repr norm_coset_repr; gsimpl.
by rewrite /coset_repr rcoset_repr_rcoset_repr //.
Qed.


Definition coset_sig := eq_sig coset_set.

Coercion mem_coset(u:coset_sig) : set G := rcoset H (val u).

Canonical Structure coset_eqType := @EqType coset_sig _ (@val_eqP _ coset_set).

Lemma coset_eqP : forall u v : coset_sig, reflect (u =1 v) (u == v).
Proof.
move=> u v.
rewrite /mem_coset; apply: (iffP idP);case: u=> {u} u Hu; case: v=> {v} v Hv H1.
-apply: rcoset_trans1 =>//;rewrite (val_eqP H1) /val; exact: rcoset_refl.
-apply/eqP; apply: val_inj; rewrite /val /coset_set  in *.
rewrite  -(eqP Hu) -(eqP Hv). 
rewrite !coset_repr_rcoset_repr; try by rewrite -1?(eqP Hu) -1?(eqP Hv) norm_coset_repr.
by apply /rcoset_reprP => //=; rewrite H1 rcoset_refl.
Qed.


Canonical Structure coset_finType :=
  @FinType coset_eqType _ (@sub_enumP _ coset_set).

Definition coset x : coset_sig := locked (EqSig _ _ (coset_set_coset_repr x)).

Lemma cosetP : forall x y, normaliser H x -> normaliser H y ->
  reflect (coset x = coset y) (rcoset H x y).
Proof. move=> x y Hx Hy; unlock coset; apply: (iffP (coset_reprP Hx Hy)) => H1.
- by apply/val_eqP => /=; apply /eqP.
- case/val_eqP : H1 => H2; exact (eqP H2).
Qed.

Lemma rcoset_coset : forall x y, rcoset H x y -> coset x = coset y.
Proof. 
move=> x y Hxy; unlock coset; apply/val_eqP => /=; apply/eqP; exact: rcoset_coset_repr.
Qed.

Lemma val_coset : forall x, normaliser H x -> val (coset x) = rcoset_repr H x.
Proof. move=> x Hx; unlock coset; rewrite /= coset_repr_rcoset_repr //=. Qed.

(* est-ce utile de le sortir? 
Lemma coset_coset_repr : forall x, val (coset (coset_repr x)) = coset_repr x.
Proof.
move=> x; unlock coset =>/=; move :(coset_set_coset_repr x); rewrite/coset_set; exact: eqP.
Qed.
*)

Lemma coset_val : forall x, coset (val x) = x.
Proof.
move=> x; case:x => {x} z; rewrite/coset_set => Hz ; apply/val_eqP => /=.
rewrite -(eqP Hz); apply/eqP; unlock coset =>/=; move :(coset_set_coset_repr z).
rewrite/coset_set; exact: eqP.
Qed.

Definition coset_unit := coset 1.

Definition coset_inv (u : coset_sig) := coset (val u)^-1.

Definition coset_mul (u v : coset_sig) := coset (val u * val v).

Lemma norm_val_coset : forall x, normaliser H (val (coset x)).
Proof. move=> x; unlock coset; exact:norm_coset_repr. Qed.

Notation Local N := (normaliser H).

Lemma coset_mul_morph : forall x y,
    normaliser H x ->
  coset (x * y) = coset_mul (coset x) (coset y).
Proof.
move=> x y Hx; rewrite /coset_mul; apply: val_inj.
symmetry; rewrite val_coset; last by apply groupM =>//; apply: norm_val_coset.
rewrite val_coset // /coset -!lock /=; apply /rcoset_reprP=> //.
rewrite -mulgA /coset_repr; set z := y * _; rewrite (_ : y * _ = z); last first.
  by congr (y * _^-1); apply /rcoset_reprP=> //; rewrite /rcoset; gsimpl; rewrite groupV.
rewrite /rcoset (norm_conjsg Hx) /conjsg /conjg -groupV //; gsimpl.
rewrite -(mulgA _ _ z^-1) groupM //; last exact: rcoset_rcoset_repr.
rewrite (norm_conjsg (groupVr group_normH Hx)) // /conjsg /conjg; gsimpl.
exact: rcoset_rcoset_repr.
Qed.

Lemma normaliser_val : forall u:coset_sig, normaliser H (val u).
Proof. 
move=> u; move: (valP u); rewrite /coset_set=> Hu; rewrite -(eqP Hu); exact: norm_coset_repr.
Qed.

Hint Resolve normaliser_val.

Lemma coset_unitP : forall u, coset_mul coset_unit u = u.
Proof.
move=> u;rewrite -(coset_val u) /coset_unit -coset_mul_morph; by [gsimpl|apply group1].
Qed.


Lemma coset_invP : forall u, coset_mul (coset_inv u) u = coset_unit.
Proof.
move=> u; rewrite -{2}(coset_val u) /coset_inv -coset_mul_morph; first by gsimpl.
by rewrite groupV.
Qed.

Lemma coset_mulP : forall u v w,
  coset_mul u (coset_mul v w) = coset_mul (coset_mul u v) w.
Proof.
move=> u v w; rewrite -(coset_val u) -(coset_val v) -(coset_val w).
rewrite -!coset_mul_morph; gsimpl; exact: groupM.
Qed.


Canonical Structure coset_groupType :=
  @FinGroupType coset_finType _ _ _ coset_unitP coset_invP coset_mulP.

Lemma coset_morph : forall x y,
    normaliser H x ->
  coset (x * y) = coset x * coset y.
Proof. move=> x y Nx; rewrite coset_mul_morph //. Qed.

Lemma val_coset1 : val (1:coset_sig) = 1.
Proof. by rewrite/unitg /= /coset_unit val_coset ?rcoset_repr1 // group1. Qed.


(*********************************************************************)
(*              Definition of the quotient group                     *)
(*    the quotient of K by H  is the set of all canonical            *)
(*    elements with the group operations                             *)
(*********************************************************************)

Section OneQuotient.

Variable K : set G.

(* The definition corresponding to textbooks (H/K) would be :
Definition quotient : set coset_eqType := fun x => K (val x).
but the rcoset_repr hidden inside gives no control on the choice of *)
(* witnesses inside H and hence demands the hypothesis H included in *)
  (**)
(* K *)

(* This is in fact HK/H *)
Definition quotient : set coset_eqType := image coset K.
Hypothesis group_K : group K.
Hypothesis subset_K_N : subset K N.


Lemma group_quotient : group quotient.
Proof.
apply/andP; split.
 by apply/imageP; exists (1:G); first exact: group1.
apply/subsetP => x; case/prodgP => y1 y2; case/imageP => x1 Hx1 -> {y1}. 
case/imageP => x2 Hx2 -> {y2} -> {x}.
rewrite -coset_morph; last exact:(subsetP subset_K_N); apply/imageP; exists (x1 * x2) =>//.
exact: groupM.
Qed.

(* est-ce qu'on prouve ici les lemmes de cardinalite? *)

End OneQuotient.

End Quotient.


Section Morphism.

Open Scope group_scope.
 
Variables (G G': finGroupType) (H : set G) (H': set G').
Variable f : G -> G'.


Definition morphism := forall x y, H x -> H y -> f (x * y) = (f x) * (f y).

Hypothesis f_morph: morphism.

Hypothesis group_H: group H.

Lemma morph1 :  f 1 = 1.
Proof. by apply: (mulg_injl (f 1)); rewrite -f_morph ?group1 // !mulg1. Qed.


Lemma morphV : forall x, 
  H x -> f (x ^-1) = (f x) ^-1.
Proof.
by move=> x Hx; apply: (mulg_injl (f x)); rewrite -f_morph ?groupV // !mulgV morph1.
Qed.

Lemma morph_conjg : forall x y, H x -> H y -> f (x ^g y) = (f x) ^g (f y).
Proof. move=> x y Hx Hy; rewrite/conjg -morphV // -!f_morph // ?groupM // groupV //. Qed.


Lemma morph_image_grp : group (image f H).
Proof.
apply/andP; split.
 by apply/imageP; exists (1:G); [apply: group1=>//| symmetry; exact: morph1].
apply/subsetP => x; move/prodgP => [y1 y2 Hy1 Hy2 ->].
move/imageP:Hy1 => [x1 Hx1 ->] {y1}; move/imageP:Hy2 => [x2 Hx2 ->] {y2}.
by rewrite -f_morph //; apply/imageP; exists (x1 * x2) => //; rewrite groupM //.
Qed.


Hypothesis group_H': group H'.

Lemma morph_preimage_grp : subset (preimage f H') H -> group (preimage f H').
Proof.
move/subsetP=>Hsubset; apply/andP; split; rewrite /preimage; first by rewrite morph1 group1 //.
by apply/subsetP=> x Hx; case/prodgP:Hx => x1 x2 Hx1 Hx2 ->; rewrite f_morph ?groupM ?Hsubset.
Qed.

Variable K : set G.

Hypothesis group_K : group K.
Hypothesis subset_KH : subset K H.

Lemma morph_normal_im : normal K H -> normal (image f K) (image f H).
Proof.
move/normalP =>Hn; apply/normalP => x y; move/imageP => [u Hu ->]; move/imageP => [v Hv ->].
apply/imageP; exists (v ^g u); first by apply Hn. rewrite -morph_conjg //. 
move/subsetP:subset_KH => -> //.
Qed.

(* lemme restriction morphisme? *)

Section Ker.

Definition ker := setI (preimage f (set1 1)) H.
(*Definition ker x:= (f x == 1) &&  H x. *)

Lemma ker1 : forall x, ker x -> f x = 1.
Proof. by move=> x; case/andP; move/eqP->. Qed.
(*Proof. by rewrite/ker/setI/preimage=> x; move/andP=>[H1 H2]; rewrite (eqP H1). Qed.*)

Lemma ker_grp : group ker.
apply/andP;split.
   by rewrite/ker/preimage/setI morph1 /= (group1 group_H) eq_refl.
apply/subsetP=> x; move/prodgP=>[y1 y2]; rewrite/ker/setI/preimage.
move/andP=>[Hfy1 Hy1]; move/andP=> [Hfy2 Hy2 ->].
rewrite /ker/preimage/setI; apply/andP; split; last by apply groupM =>//.
by apply/eqP; rewrite f_morph=> //; rewrite -(eqP Hfy1) -(eqP Hfy2); gsimpl.
Qed.

Lemma group_conjsg : forall x y, H x -> H y -> H (x ^g y).
Proof. move=> x y Hx Hy; rewrite/conjg; rewrite ?groupM // groupV //. Qed.

Lemma normal_ker : normal ker H.
Proof.
apply/normalP=> x y Hx; rewrite/ker/setI/preimage; move/andP=>[H1 H2].
by rewrite morph_conjg // -(eqP H1) conj1g eq_refl group_conjsg //.
Qed.

 (* trivialg H := subset H (set1 1) *) 

Lemma kerP : reflect (forall x y, H x -> H y -> (f x = f y -> x = y)) (subset ker (set1 1)).
Proof.
apply: (iffP idP); rewrite/ker/setI/preimage.
 move/subsetP=> H1 x y Hx Hy Hxy.
 apply (mulg_injl (y ^-1)); rewrite mulVg (eqP (H1 (y^-1 * x) _)) //.
 rewrite (@groupM _ _ group_H y^-1 x) ?f_morph ?groupV // morphV // Hxy mulVg eq_refl //.
move=> H1; apply/subsetP=> x; move/andP=>[Hx1 Hx]. 
rewrite (H1 1 x) // ?group1 // morph1; exact (eqP Hx1).
Qed.

End Ker.

End Morphism.

Implicit Arguments quotient [G H].

Section QuotientMorphism.

Variables (GT1 GT2 : finGroupType) (f : GT1 -> GT2) (G H : set GT1).

Hypothesis G_grp : group G.
Hypothesis Hf : morphism G f.
Hypothesis H_grp : group H.
Hypothesis normal_HG : normal H G.
Hypothesis H_ker : subset H (ker G f).

Let sub_HG : subset H G.
Proof. by apply/subsetP=> x; move/(subsetP H_ker); case/andP. Qed.

Let GoverH := quotient H_grp G.

Let GoverH_grp := group_quotient H_grp G_grp normal_HG.

Notation Local Gquo := (coset_groupType H_grp).

Let quotient_fun (x : Gquo) := f (val x).

Let norm_K_val_coset : forall x, G x -> normaliser H (val (coset H_grp x)).
Proof.
move=> x Hx; apply: (subsetP normal_HG).
rewrite val_coset; last exact: (subsetP normal_HG).
have:= @rcoset_rcoset_repr _ H H_grp x; move/rcosetP=> [z Hz ->].
by move/(subsetP sub_HG): Hz => Hz; rewrite groupM.
Qed.

Let G_coset_val : forall x, G x -> G (val (coset G_grp x)).
Proof.
move=> x Hx; rewrite val_coset; last by exact :(subsetP norm_HoverKer)=>//.
move/rcosetP :(@rcoset_rcoset_repr _ _ K_grp x)=> [z Hz ->]; rewrite groupM //.
by move/andP:Hz=>[_ Hz].
Qed.

Section QuotientMorphism.


Section Isomporhism_theorems.


Section First_theorem.


Open Scope group_scope.
 
Variables (G G': finGroupType) (H : set G).
Variable f : G -> G'.

Hypothesis group_H: group H.

Hypothesis f_morph : morphism H f.

Let K := ker H f.

Let K_grp := ker_grp f_morph group_H.

Print quotient.
Let HoverKer := quotient K_grp H.

Let norm_HoverKer := normal_ker f_morph group_H.


Let HoverKer_grp := group_quotient K_grp group_H norm_HoverKer.

Notation Local Gquo := (coset_groupType K_grp).

Let fquo(x:Gquo) := f (val x).


Let norm_K_val_coset : forall x, H x -> normaliser K  (val (coset K_grp x)).
Proof.
move=> x Hx; apply:(subsetP norm_HoverKer); rewrite -/K.
rewrite val_coset; last by exact:(subsetP norm_HoverKer)=>//.
move:(@rcoset_rcoset_repr _ K K_grp x); move/rcosetP=>[z Hz ->].
by rewrite groupM //; move/andP:Hz=>[H1 H2].
Qed. 


Let H_coset_val : forall x, H x -> H  (val (coset K_grp x)).
Proof.
move=> x Hx; rewrite val_coset; last by exact :(subsetP norm_HoverKer)=>//.
move/rcosetP :(@rcoset_rcoset_repr _ _ K_grp x)=> [z Hz ->]; rewrite groupM //.
by move/andP:Hz=>[_ Hz].
Qed.



Lemma fquo_morph : morphism HoverKer fquo.
Proof.
move=>x y.
move/imageP=>[x1 Hx1 ->];move/imageP=>[y1 Hy1 ->]; rewrite -/K.
set cx := coset _ x1; set cy := coset _ y1.
have Hcxcy :  normaliser K (val cx * val cy).
 by rewrite groupM=>//; first exact: normaliser_grp; apply:norm_K_val_coset=>//.
rewrite /fquo {1}/mulg /= /coset_mul val_coset -/K //.
move/rcosetP:(@rcoset_rcoset_repr _ K K_grp (val cx * val cy))=>[z Hz ->].
move/andP:Hz; rewrite/preimage; move=>[Hz1 Hz2].
by rewrite !f_morph // -?(eqP Hz1) ?mul1g // /cx /cy ?groupM //; try apply: H_coset_val=> //.
Qed.

(* +  noyau trivial *)

(* (preimage coset) definit une bijection entre les sous groupes de *)
(* H/Ker et les sous groupes de H qui contiennent le ker *)


End First_theorem.


Section Third_theorem.

Open Scope group_scope.
 
Variables (GT : finGroupType) (G H K : set GT).

Hypothesis G_grp : group G.
Hypothesis H_grp : group H.
Hypothesis K_grp : group K.

Hypothesis subset_HK : subset H K.
Hypothesis subset_KG : subset K G.

Hypothesis normal_HG : normal H G.
Hypothesis normal_KG : normal K G.

Let KoverH := quotient H_grp K.
Let GoverH := quotient H_grp G.


Let normal_HK := normal_subset normal_HG subset_KG.

Let KoverH_grp := group_quotient H_grp K_grp normal_HK.
Let GoverH_grp := group_quotient H_grp G_grp normal_HG.

Check morphism. 
Let Hquo := coset_groupType H_grp.


Lemma morphism_coset : morphism G (coset H_grp).
Proof.
move=> x y; do 2 move/(subsetP normal_HG)=> ?; exact: coset_morph. 
Qed.

Lemma normal_KoH_GoH : normal KoverH GoverH.
Proof. exact: (morph_normal_im morphism_coset). Qed.

Definition third_grp_iso (u : coset_groupType KoverH_grp) : coset_groupType K_grp :=
  coset K_grp (val (val u)).

Let f (u : Hquo) := coset K_grp (val u).

Let f_morph : morphism GoverH f.

Lemma morphism_third_grp_iso : morphism (quotient KoverH_grp GoverH) third_grp_iso.
Proof.

apply: fquo_morph.

) : coset_groupType
  KoverH_grp :=

G_grp _ _ _. subset_KG normal_KG.
have:= morph_normal_im morphism_coset G_grp subset_KG normal_KG.
done.
apply (@morph_normal_im  _ _ _ coset _ _ _ subset_HK normal_HK)

apply/normalP=> x y; rewrite /KoverH /GoverH /quotient; set Hcoset := coset H_grp.
move/imageP=> [x1 Hx1 ->]; move/imageP=> [x2 Hx2 ->].
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






