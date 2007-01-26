(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Group.

Structure finGroupType : Type := FinGroupType {
  element :> finType;
  unit : element;
  inv : element -> element;
  mul : element -> element -> element;
  unitP : forall x, mul unit x = x;
  invP : forall x, mul (inv x) x = unit;
  mulP : forall x1 x2 x3, mul x1 (mul x2 x3) = mul (mul x1 x2) x3
}.

End Group.

Implicit Arguments Group.unit [].

Delimit Scope group_scope with G.
Bind Scope group_scope with Group.element.
Arguments Scope Group.mul [_ group_scope group_scope].
Arguments Scope Group.inv [_ group_scope].

Notation finGroupType := Group.finGroupType.
Notation FinGroupType := Group.FinGroupType.
Definition mulg := nosimpl Group.mul.
Definition invg := nosimpl Group.inv.
Definition unitg := nosimpl Group.unit.
Prenex Implicits mulg invg.

Notation "x1 * x2" := (mulg x1 x2): group_scope.
Notation "1" := (unitg _) : group_scope.
Notation "x '^-1'" := (invg x) (at level 9, format "x '^-1'") : group_scope.

Section GroupIdentities.

Open Scope group_scope.

Variable elt : finGroupType.

Lemma mulgA : forall x1 x2 x3 : elt, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. exact: Group.mulP. Qed.

Lemma mul1g : forall x : elt, 1 * x = x.
Proof. exact: Group.unitP. Qed.

Lemma mulVg : forall x : elt, x^-1 * x = 1.
Proof. exact: Group.invP. Qed.

Lemma mulKg : forall x : elt, cancel (mulg x) (mulg x^-1).
Proof.  by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulg_injl : forall x : elt, injective (mulg x).
Proof. move=> x; exact: can_inj (mulKg x). Qed.

Implicit Arguments mulg_injl [].

Lemma mulgV : forall x : elt, x * x^-1 = 1.
Proof. by move=> x; rewrite -{1}(mulKg x^-1 x) mulVg -mulgA mul1g mulVg. Qed.

Lemma mulKgv : forall x : elt, cancel (mulg x^-1) (mulg x).
Proof. by move=> x y; rewrite mulgA mulgV mul1g. Qed.

Lemma mulg1 : forall x : elt, x * 1 = x.
Proof. by move=> x; rewrite -(mulVg x) mulKgv. Qed.

Notation mulgr := (fun x y => y * x).

Lemma mulgK : forall x : elt, cancel (mulgr x) (mulgr x^-1).
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulg_injr : forall x : elt, injective (mulgr x).
Proof. move=> x; exact: can_inj (mulgK x). Qed.

Lemma mulgKv : forall x : elt, cancel (mulgr x^-1) (mulgr x).
Proof. by move=> x y; rewrite -mulgA mulVg mulg1. Qed.

Lemma invg1 : 1^-1 = 1 :> elt.
Proof. by rewrite -{2}(mulVg 1) mulg1. Qed.

Lemma invgK : cancel (@invg elt) invg.
Proof. by move=> x; rewrite -{2}(mulgK x^-1 x) -mulgA mulKgv. Qed.

Lemma invg_inj : injective (@invg elt).
Proof. exact: can_inj invgK. Qed.

Lemma invg_mul : forall x1 x2 : elt, (x2 * x1)^-1 = x1^-1 * x2^-1. 
Proof.
by move=> x1 x2; apply: (mulg_injl (x2 * x1)); rewrite mulgA mulgK !mulgV.
Qed.

End GroupIdentities.

Implicit Arguments mulg_injl [elt].
Implicit Arguments mulg_injr [elt].

Hint Rewrite mulg1 mul1g invg1 mulVg mulgV invgK mulgK mulgKv
             invg_mul mulgA : gsimpl.

Ltac gsimpl := autorewrite with gsimpl; try done.

Definition conjg (g : finGroupType) (x y : g) := (x^-1 * y * x)%G.

Notation "y ^ x" := (conjg x y) : group_scope.

Section Conjugation.

Variable elt : finGroupType.

Open Scope group_scope.

Lemma conjgE : forall x y : elt, x ^ y = y^-1 * x * y. Proof. done. Qed.

Lemma conjg1 : conjg 1 =1 @id elt.
Proof. by move=> x; rewrite conjgE invg1 mul1g mulg1. Qed.

Lemma conj1g : forall x : elt, 1 ^ x = 1.
Proof. by move=> x; rewrite conjgE mulg1 mulVg. Qed.

Lemma conjg_mul : forall x1 x2 y : elt, (x1 * x2) ^ y = x1 ^ y * x2 ^ y.
Proof. by move=> *; rewrite !conjgE !mulgA mulgK. Qed.

Lemma conjg_invg : forall x y : elt, x^-1 ^ y = (x ^ y)^-1.
Proof. by move=> *; rewrite !conjgE !invg_mul invgK mulgA. Qed.

Lemma conjg_conj : forall x y1 y2 : elt, (x ^ y1) ^ y2 = x ^ (y1 * y2).
Proof. by move=> *; rewrite !conjgE invg_mul !mulgA. Qed.

Lemma conjgK : forall y : elt, cancel (conjg y) (conjg y^-1).
Proof. by move=> y x; rewrite conjg_conj mulgV conjg1. Qed.

Lemma conjgKv : forall y : elt, cancel (conjg y^-1) (conjg y).
Proof. by move=> y x; rewrite conjg_conj mulVg conjg1. Qed.

Lemma conjg_inj : forall y : elt, injective (conjg y).
Proof. move=> y; exact: can_inj (conjgK y). Qed.

Definition conjg_fp (y x : elt) := x ^ y == x.

Definition commute (x y : elt) := x * y = y * x.

Lemma commute_sym : forall x y, commute x y -> commute y x.
Proof. done. Qed.

Lemma conjg_fpP : forall x y : elt, reflect (commute x y) (conjg_fp y x).
Proof.
move=> *; rewrite /conjg_fp conjgE -mulgA (canF_eq (mulKgv _)); exact: eqP.
Qed.

Lemma conjg_fp_sym : forall x y : elt, conjg_fp x y = conjg_fp y x.
Proof. move=> x y; exact/conjg_fpP/conjg_fpP. Qed.

End Conjugation.

Implicit Arguments conjg_inj [elt].
Implicit Arguments conjg_fpP [elt x y].
Prenex Implicits conjg_fpP.

Section SmulDef.

Open Scope group_scope.

Variable elt : finGroupType.

Notation "x \in H" := (@s2s elt H x) (at level 65, no associativity).

(* Set-lifted group operations *)

Definition lcoset x H := {y, x^-1 * y \in H}.
Definition rcoset H x := {y, y * x^-1 \in H}.
Definition smulg_def H K := {xy, ~~ disjoint {y, rcoset H y xy} (s2s K)}.
Definition sinvg H := {y, y^-1 \in H}.
Definition sconjg H x := {y, y ^ x^-1 \in H}.
Definition classg_def x K := {y, image (fun z : elt => x ^ z) (s2s K) y}.
Definition sclassg_def H K := {xy, ~~ disjoint {y, sconjg H y xy} (s2s K)}.

End SmulDef.

(* smulg_def confuses the coq term comparison function! *)
Definition smulg := locked smulg_def.
Definition classg := locked classg_def.
Definition sclassg := locked sclassg_def.

Notation "H ':*' x" := (rcoset H x) (at level 40) : group_scope.
Notation "x '*:' H" := (lcoset x H) (at level 40) : group_scope.
Notation "H ':*:' K" := (smulg H K) (at level 40) : group_scope.
Notation "A ':^-1'" := (sinvg A) (at level 30) : group_scope.
Notation "A ':^' x" := (sconjg A x) (at level 35) : group_scope.
Notation "x '^:' H" := (classg x H) (at level 35) : group_scope.
Notation "A ':^:' H" := (sclassg A H) (at level 35) : group_scope.

Section GroupProp.

Variable elt : finGroupType.

Open Scope group_scope.

Variable H : setType elt.

Lemma lcosetP : forall y z, reflect (exists2 x, H x & z = y * x) ((y *: H) z).
Proof.
move=> y z; apply: (iffP idP) => [Hx | [x Hx ->]]; last by rewrite s2f mulKg.
by exists (y^-1 * z); last rewrite mulKgv; rewrite s2f in Hx.
Qed.

Lemma rcosetP : forall y z, reflect (exists2 x, H x & z = x * y) ((H :* y) z).
Proof.
move=> y z; apply: (iffP idP) => [Hx | [x Hx ->]]; last by rewrite s2f mulgK.
by exists (z * y^-1); last rewrite mulgKv; rewrite s2f in Hx.
Qed.

CoInductive mem_smulg (K : setType elt) z : Prop :=
   MemProdg x y of H x & K y & z = x * y.

Lemma smulgP : forall K z, reflect (mem_smulg K z) ((H :*: K) z).
Proof.
unlock smulg => K z; rewrite s2f; apply: (iffP set0Pn) => [[y]|[x y Hx Hy ->]].
  by rewrite /setI s2f;case/andP; case/rcosetP=> x; exists x y.
by exists y; rewrite /setI s2f Hy andbT; apply/rcosetP; exists x.
Qed.

Lemma smulg_subl : forall K : setType elt, K 1 -> subset H (H :*: K).
Proof. 
move=> K K1; apply/subsetP=> x Hx; apply/smulgP.
by exists x (1 : elt); last rewrite mulg1.
Qed.

Lemma smulg_subr : forall K : setType elt, H 1 -> subset K (H :*: K).
Proof. 
move=> K H1; apply/subsetP=> x Kx; apply/smulgP.
by exists (1 : elt) x; last rewrite mul1g.
Qed.

Definition group := H 1 && subset (H :*: H) H.

Definition subgroup K := group && subset H K.

Lemma groupP : reflect (H 1 /\ forall x y, H x -> H y -> H (x * y)) group.
Proof.
apply: (iffP andP) => [] [H1 HM]; split=> {H1}//.
  by move=> x y Hx Hy; apply: (subsetP HM); apply/smulgP; exists x y.
by apply/subsetP=> z; case/smulgP=> [x y Hx Hy ->]; auto.
Qed.

Hypothesis gH : group.

Lemma group1 : H 1. Proof. by case/groupP: gH. Qed.

Lemma groupM : forall x y, H x -> H y -> H (x * y).
Proof. by case/groupP: gH. Qed.

Lemma groupVr : forall x, H x -> H x^-1.
Proof.
move=> x Hx; rewrite -(finv_f (mulg_injl x) x^-1) mulgV /finv.
elim: pred => [|n IHn] /=; [exact: group1 | exact: groupM].
Qed.

Lemma groupV : forall x, H x^-1 = H x.
Proof. move=> x; apply/idP/idP; first rewrite -{2}[x]invgK; exact: groupVr. Qed.

Lemma groupMl : forall x y, H x -> H (x * y) = H y.
Proof.
move=> x y Hx; apply/idP/idP=> Hy; last exact: groupM.
rewrite -(mulKg x y); exact: groupM (groupVr _) _.
Qed.

Lemma groupMr : forall x y, H x -> H (y * x) = H y.
Proof.
move=> x y Hx; apply/idP/idP=> Hy; last exact: groupM.
rewrite -(mulgK x y); exact: groupM (groupVr _).
Qed.

Lemma groupVl : forall x,  H x^-1 ->  H x.
Proof. by move=> x; rewrite groupV. Qed.

Lemma groupJ : forall x y, H x -> H y -> H (x ^ y).
Proof. by move=> *; rewrite /conjg !groupM ?groupV. Qed.

Lemma groupJr : forall x y, H y -> H (x ^ y) = H x.
Proof. by move=> *; rewrite /conjg groupMr ?groupMl ?groupV. Qed.

Definition subFinGroupType : finGroupType.
pose d := sub_finType H.
pose d1 : d := EqSig H 1 group1.
pose dV (u : d) : d := EqSig H _ (groupVr (valP u)).
pose dM (u1 u2 : d) : d := EqSig H _ (groupM (valP u1) (valP u2)).
(exists d d1 dV dM => *; apply: val_inj);
  [exact: mul1g | exact: mulVg | exact: mulgA].
Defined.

Lemma pos_card_group : 0 < card H.
Proof. rewrite lt0n; apply/set0Pn; exists (1 : elt); exact: group1. Qed.

Lemma smulgg : H :*: H = H.
Proof.
by case/andP: gH => [H1 mH]; apply/isetP; apply/subset_eqP; rewrite mH smulg_subr.
Qed.

End GroupProp.

Section ConjugationSet.

Open Scope group_scope.

Variable elt : finGroupType.
Variable H : setType elt.
Hypothesis gH : group H.

Theorem sconjgE : forall x y, (H :^ x^-1) y = H (y ^ x).
Proof. by move => *; rewrite s2f invgK. Qed.

Theorem sconjg1 : forall x, (H :^ x) 1.
Proof. by move=> x; rewrite s2f conj1g group1. Qed.

Theorem sconj1g : H :^ 1 = H.
Proof. by apply/isetP => x; rewrite s2f invg1 conjg1. Qed.

Theorem sconjg_inv : forall x y, (H :^ x) y -> (H :^ x) y^-1.
Proof. move=> x y; rewrite !s2f conjg_invg; exact: groupVr. Qed.

Theorem sconjg_conj : forall x y, (H :^ x) (y ^ x) = H y.
Proof. by move=> x y; rewrite s2f conjgK. Qed.

(*
Theorem sconjg_conj: forall x y z, sconjg (x * y^-1) z = sconjg x (z ^ y).
Proof. move=> x y z; rewrite !s2f conjg_conj; gsimpl. Qed.
*)

Theorem group_sconjg : forall x, group (H :^ x).
Proof. 
move=> x; rewrite /group sconjg1; apply/subsetP=> y.
case/smulgP=> x1 x2 Hx1 Hx2 -> {z}.
rewrite !s2f conjg_mul in Hx1 Hx2 *; exact: groupM. 
Qed.

Theorem sconjg_iimage : forall x, H :^ x = (conjg x) @: H.
Proof.
move=> x; apply/isetP =>y; unlock iimage; rewrite !s2f. 
rewrite -{2}(conjgKv x y) image_f ?s2f //; exact: conjg_inj.
Qed.

Lemma sconjg_coset : forall x, H :^ x = x^-1 *: H :* x.
Proof. by move=> x; apply/isetP =>y; rewrite !s2f mulgA. Qed.

(*
Theorem sconjg_inv1: forall x,
  (sconjg x) =1 H -> (sconjg x^-1) =1 H.
Proof. by move=> x Hx y; rewrite -sconj1g -(mulVg x) sconjg_conj Hx s2f. Qed.
*)

Theorem card_sconjg : forall x, card (H :^ x) = card H.
Proof.
move=> x; rewrite (sconjg_iimage x); apply card_iimage.
exact: conjg_inj.
Qed.

End ConjugationSet.

(*
Definition group_of_type (elt : finGroupType) := {x : elt, true}.

Proof.  
by move=> g; rewrite /group s2f /=; apply/subsetP => w; rewrite !s2f.
Qed.

Coercion group_of_type : finGroupType >-> setType.
*)

Definition eq_prod d1 d2 a1 a2 :=
  fun u : prod_finType d1 d2 => a1 (eq_pi1 u) && a2 (eq_pi2 u).

Lemma card_prod : forall d1 d2 a1 a2,
  card (eq_prod a1 a2) = (@card d1 a1 * @card d2 a2)%N.
Proof.
move=> d1 d2 a1 a2; rewrite /card /= /prod_enum.
elim: (enum d1) => //= x s IHs.
rewrite count_cat IHs count_maps /comp /eq_prod /=.
by case: (a1 x) => //=; rewrite count_set0.
Qed.

Section LaGrange.

Hint Resolve pos_card_group.

Variables (elt : finGroupType) (H K : setType elt).
Hypothesis gH : group H.
Hypothesis gK : group K.
Hypothesis subset_HK : subset H K.
Let sHK := subsetP subset_HK.

Open Scope group_scope.

Notation Local "1" := (@unitg elt).

Lemma rcoset_refl : forall x, (H :* x) x.
Proof. by move=> x; rewrite /rcoset s2f mulgV group1. Qed.

Lemma rcoset_sym : forall x y, (H :* x) y = (H :* y) x.
Proof. by move=> *; apply/idP/idP; rewrite !s2f; move/(groupVr gH); rewrite invg_mul invgK. Qed.

Lemma rcoset_trans : forall x y z, (H :* x) y -> (H :* y) z -> (H :* x) z.
Proof. by move=> x y z Hxy; rewrite s2f in Hxy; rewrite !s2f -(groupMr gH _ Hxy) -mulgA mulKg. Qed.

Lemma rcoset_trans1 : forall x y, (H :* x) y -> H :* x = H :* y.
Proof.
move=> x y Hxy; apply/isetP => u; rewrite s2f in Hxy.
by rewrite !s2f -{1}(mulgKv y u) -mulgA groupMr.
Qed.

Lemma rcoset_trans1r : forall x y, 
  (H :* x) y -> forall z, (H :* z) x = (H :* z) y.
Proof.
by move=> x y Hxy z; rewrite !(rcoset_sym z) (rcoset_trans1 Hxy).
Qed.

Lemma rcoset1 : H :* 1 = H.
Proof. by apply/isetP => x; rewrite s2f invg1 mulg1. Qed.

Lemma card_rcoset : forall x, card (H :* x) = card H.
Proof.
move=> x; rewrite (eq_card (s2f _)) (card_preimage (mulg_injr x^-1) _).
apply: eq_card=> y; rewrite /setI andbC.
case Hy: (H y) => //=; apply/set0Pn; exists (y * x).
by rewrite /preimage mulgK set11.
Qed.

Definition indexg (K : setType elt) := card (iimage (rcoset H) K).

Definition repr (A : setType elt) := if pick A is Some x then x else 1.

Lemma repr_rcoset : forall x, (H :* x) (repr (H :* x)).
Proof.
by rewrite /repr => x; case: pickP => //; move/(_ x); rewrite rcoset_refl.
Qed.

Theorem LaGrange : (card H * indexg K)%N = card K.
Proof.
pose f x : prod_finType _ _ := EqPair (x * (repr (H :* x))^-1) (H :* x).
have inj_f: injective f.
  rewrite /f [rcoset]lock => x1 x2 [Dy DHx]; move: Dy; rewrite {}DHx.
  exact: mulg_injr.
rewrite -card_prod -(card_iimage inj_f).
apply: eq_card => [] [y A]; apply/andP/iimageP=> /= [[Hy]|[x Kx [-> ->]]].
  move/iimageP=> [x Kx ->{A}]; case/rcosetP: (repr_rcoset x) => y' Hy' Dy'.
  exists (y * y' * x); first by rewrite groupMr // sHK // groupM.
  have Hxyx: (H :* x) (y * y' * x) by rewrite s2f; gsimpl; exact: groupM.
  rewrite /f -(rcoset_trans1 Hxyx) Dy'; gsimpl.
split; last by apply/iimageP; exists x.
case/rcosetP: (repr_rcoset x) => y' Hy' ->; gsimpl; exact: groupVr.
Qed.

Lemma group_dvdn : dvdn (card H) (card K).
Proof. by apply/dvdnP; exists (indexg K); rewrite mulnC LaGrange. Qed.

Lemma group_divn : divn (card K) (card H) = indexg K.
Proof. by rewrite -LaGrange // divn_mulr; auto. Qed.

Lemma lcoset_inv : forall x y, (x *: H) y = (H :* x^-1) y^-1.
Proof. by move=> x y; rewrite !s2f -invg_mul groupV. Qed.

Lemma lcoset_refl : forall x, (x *: H) x.
Proof. by move=> x; rewrite s2f mulVg group1. Qed.

Lemma lcoset_sym : forall x y, (x *: H) y = (y *: H) x.
Proof. by move=> x y; rewrite !lcoset_inv rcoset_sym. Qed.

Lemma lcoset_trans : forall x y z, (x *: H) y -> (y *: H) z -> (x *: H) z.
Proof. move=> x y z; rewrite !lcoset_inv; exact: rcoset_trans. Qed.

Lemma lcoset1 : 1 *: H = H.
Proof. by apply/isetP => x; rewrite s2f invg1 mul1g. Qed.

Lemma lcoset_trans1 : forall x y, (x *: H) y -> x *: H = y *: H.
Proof.
move=> x y Hxy; apply/isetP => u; rewrite s2f in Hxy.
by rewrite !s2f -{1}(mulKgv y u) mulgA groupMl.
Qed.

Lemma lcoset_trans1r : forall x y, 
  (x *: H) y -> forall z, (z *: H) x = (z *: H) y.
Proof.
by move=> x y Hxy z; rewrite !(lcoset_sym z) (lcoset_trans1 Hxy).
Qed.

Lemma sinvgK : involutive (@sinvg elt).
Proof. by move=> A; apply/isetP => x; rewrite !s2f invgK. Qed.

Lemma sinvg_lcoset : forall x, (x *: H) :^-1 = H :* x^-1.
Proof.
by move=> x; apply/isetP => y; rewrite !s2f -invg_mul invgK groupV.
Qed.

Lemma card_sinvg : forall A : setType elt, card (A :^-1) = card A.
Proof.
move=> A; have iinj := @invg_inj elt; rewrite -(card_image iinj).
by apply: eq_card => x; rewrite -[x]invgK image_f // s2f.
Qed.

Lemma card_lcoset : forall x, card (x *: H) = card H.
Proof. by move=> x; rewrite -card_sinvg sinvg_lcoset card_rcoset. Qed.

Lemma lcoset_indexg : card (iimage (fun x => lcoset x H) K) = indexg K.
Proof.
rewrite -(card_iimage (inv_inj sinvgK)); apply: eq_card => A; unlock iimage; rewrite !s2f.
apply/imageP/imageP=> [[B dB ->{A}] | [x Hx ->{A}]].
  rewrite s2f in dB.
  case/imageP: dB => x Kx ->{B}.
  exists x^-1; [exact: groupVr | exact: sinvg_lcoset].
exists (x^-1 *: H); last by rewrite sinvg_lcoset invgK.
by rewrite s2f;apply/imageP; exists x^-1; first exact: groupVr.
Qed.

End LaGrange.

(* Shows that given two sets h k, if hk=kh then hk is a subgroup *)
Section SubSmul.

Open Scope group_scope.

Variable elt : finGroupType.

Notation Local "1" := (unitg elt).

Lemma smulgA : forall A1 A2 A3 : setType elt,
  A1 :*: (A2 :*: A3) = A1 :*: A2 :*: A3.
Proof.
move=> A1 A2 A3; apply/isetP => x; apply/smulgP/smulgP.
  case=> x1 x23 Ax1; case/smulgP=> x2 x3 Ax2 Ax3 ->{x23}; rewrite mulgA => Dx.
  by exists (x1 * x2) x3 => //; apply/smulgP; exists x1 x2.
case=> x12 x3; case/smulgP=> x1 x2 Ax1 Ax2 ->{x12} Ax3; rewrite -mulgA => Dx.
by exists x1 (x2 * x3) => //; apply/smulgP; exists x2 x3.
Qed.

Lemma rcoset_smul : forall A (x : elt), A :* x = A :*: {:x}.
Proof.
move=> A x; apply/isetP => y; apply/rcosetP/smulgP => [[z]|[z x']].
  by exists z x; first 2 [exact: iset11].
by rewrite s2f => ?; move/eqP=> -> ->; exists z.
Qed.

Lemma lcoset_smul : forall A (x : elt), x *: A = {:x} :*: A.
Proof.
move=> A x; apply/isetP => y; apply/lcosetP/smulgP => [[z]|[x' z]].
  by exists x z; first 1 [exact: iset11].
by rewrite s2f; move/eqP=> -> ? ->; exists z.
Qed.

Lemma smulg1 : forall A : setType elt, A :*: {:1} = A.
Proof. by move=> A; rewrite -rcoset_smul rcoset1. Qed.

Lemma smul1g : forall A : setType elt, {:1} :*: A = A.
Proof. by move=> A; rewrite -lcoset_smul lcoset1. Qed.

Lemma smulgs : forall A B1 B2 : setType elt,
  subset B1 B2 -> subset (A :*: B1) (A :*: B2).
Proof.
move=> A B1 B2; move/subsetP=> sB12; apply/subsetP=> x.
case/smulgP=> y z Ay Bz ->; apply/smulgP; exists y z; auto.
Qed.

Lemma smulsg : forall A1 A2 B : setType elt,
  subset A1 A2 -> subset (A1 :*: B) (A2 :*: B).
Proof.
move=> A1 A2 B; move/subsetP=> sA12; apply/subsetP=> x.
case/smulgP=> y z Ay Bz ->; apply/smulgP; exists y z; auto.
Qed.

Lemma smulg_set1 : forall x y : elt, {:x} :*: {:y} = {:x * y}.
Proof.
move=> x y; apply/isetP => z.
by rewrite -rcoset_smul !s2f (canF_eq (mulgK y)).
Qed.

Section GroupSmulSub.

Variables H K : setType elt.
Hypothesis gH : group H.
Hypothesis gK : group K.

Lemma smulsgg : H 1 -> subset H K -> H :*: K = K.
Proof.
move=> H1 sHK; apply/isetP; apply/subset_eqP.
by rewrite smulg_subr // -{2}[K]smulgg // smulsg.
Qed.

Lemma smulgsg : K 1 -> subset K H -> H :*: K = H.
Proof.
move=> K1 sHK; apply/isetP; apply/subset_eqP.
by rewrite smulg_subl // -{2}[H]smulgg // smulgs.
Qed.

End GroupSmulSub.

Section GroupSmulC.

Variables H K : setType elt.
Hypothesis gH : group H.
Hypothesis gK : group K.

Lemma smulC_group : H :*: K = K :*: H -> group (H :*: K).
Proof.
move=> nHK; apply/andP; split.
  apply/smulgP; exists 1 1; by [exact: group1 | rewrite mulg1].
by rewrite smulgA nHK -(smulgA K) (smulgg gH) -nHK -smulgA (smulgg gK) subset_refl.
Qed.

Lemma group_smulC : group (H :*: K) -> H :*: K = K :*: H.
Proof.
move/groupV=> gHK; apply/isetP => x; rewrite -{}gHK.
apply/smulgP/smulgP => [] [y z Gy Gz Dx];
  by exists z^-1 y^-1; rewrite ?groupV // -invg_mul -Dx ?invgK.
Qed.

End GroupSmulC.

Variables H K : setType elt.
Hypothesis gH : group H.
Hypothesis gK : group K.

Lemma group_smul_sym : group (H :*: K) = group (K :*: H).
Proof.
by apply/idP/idP => Hhk; apply: smulC_group; rewrite // -group_smulC.
Qed.

Lemma groupI : group (H :&: K).
Proof.
apply/groupP; split=> [|x y]; rewrite !s2f ?group1 //.
by move/andP=> [Hx Kx]; rewrite !groupMl.
Qed.

Lemma subsetIl : forall d (A B : setType d), subset (A :&: B) A.
Proof.
by move=> d A B; apply/subsetP=> x; rewrite s2f; case/andP.
Qed.

Lemma subsetIr : forall d (A B : setType d), subset (A :&: B) B.
Proof.
by move=> d A B; apply/subsetP=> x; rewrite s2f; case/andP.
Qed. 

Lemma subsetUl : forall d (A B : setType d), subset A (A :|: B).
Proof. by move=> d A B; apply/subsetP=> x; rewrite s2f => ->. Qed.

Lemma subsetUr : forall d (A B : setType d), subset B (A :|: B).
Proof. by move=> d A B; apply/subsetP=> x; rewrite s2f orbC => ->. Qed.

Lemma card_smulg :
  (card (H :*: K) * card (H :&: K) = card H * card K)%N.
Proof.
have gHK := groupI; rewrite -(LaGrange gHK gK) ?subsetIr //; symmetry.
rewrite mulnCA mulnC; congr muln; rewrite -card_prod -card_sub.
set tup := eq_prod _ _; set tupT := sub_finType tup.
pose f (u : tupT) := let: EqSig (EqPair x Hy) _ := u in x * repr Hy.
have injf: injective f.
  move=> [[x1 A1] dom1] [[x2 A2] dom2] /= Ef; apply: val_inj => /=.
  case/andP: dom1 (Ef) => /= Hx1; case/iimageP=> y1 Ky1 dA1.
  case/andP: dom2 => /= Hx2; case/iimageP=> y2 Ky2 dA2.
  suff ->: A1 = A2 by move/mulg_injr->.
  rewrite {A1}dA1 {A2}dA2 in Ef *; apply: rcoset_trans1 => //.
  case/rcosetP: (repr_rcoset gHK y1) Ef => [z1 HKz1 ->].
  case/rcosetP: (repr_rcoset gHK y2) => [z2 HKz2 ->] Ef.
  move: HKz1 HKz2; rewrite !s2f (groupMl gK _ Ky2) // groupVr //= andbT.
  case/andP=> Hz1 _; case/andP=> Hz2 _.
  rewrite -(mulKg (x2 * z2) y2) -(mulgA x2) -{y2 Ky2}Ef; gsimpl.
  rewrite !groupMl //; exact: groupVr.
rewrite -(card_codom injf); apply: eq_card => z.
apply/set0Pn/smulgP; rewrite /preimage.
  case=> [[[x A]]] /=; case/andP=> /= Hx; case/iimageP=> y Ky -> {A}.
  move/eqP->; case/rcosetP: (repr_rcoset gHK y) => [x' HKx' ->].
  exists x (x' * y); rewrite // groupMr //.
  exact: subsetP (subsetIr _ _) _ HKx'.
move=> [x y Hx Ky ->]; case/rcosetP: (repr_rcoset gHK y) => x'.
rewrite s2f; move/andP=> [Hx' Kx'] Dx'.
have Tu: tup (EqPair (x * x'^-1) ((H :&: K) :* y)).
  by rewrite /tup /eq_prod /= groupMl ?groupVr //; apply/iimageP; exists y.
exists (EqSig tup _ Tu); apply/eqP; rewrite /= Dx'; gsimpl.
Qed.

Definition trivg (A : setType elt) := subset A {:1}.

Lemma trivgP : forall G, group G -> reflect (G = {:1}) (trivg G).
Proof.
move=> G gG; apply: (iffP idP) => [tG | ->]; last exact: subset_refl.
apply/isetP; apply/subset_eqP; apply/andP; split=> //.
apply/subsetP=> x; rewrite s2f; move/eqP<-; exact: group1.
Qed.

Definition disjointg := trivg (H :&: K).

Lemma disjointgP : reflect (H :&: K = {:1}) disjointg.
Proof. exact: trivgP groupI. Qed.

Lemma card1i : forall (d : finType) (x : d), card {:x} = 1%nat.
Proof. move=> d x; rewrite -(card1 x); apply eq_card; exact: s2f. Qed.

Lemma disjointg_card : disjointg = (card (H :&: K) == 1%nat).
Proof.
apply/disjointgP/eqP=> [->|cHK]; first by rewrite card1i.
symmetry; apply/isetP; apply/subset_cardP; first by rewrite card1i.
apply/subsetP=> x; rewrite s2f; move/eqP <-; exact: group1 groupI.
Qed.

Lemma group_modularity : forall G, group G -> subset G K ->
  G :*: (H :&: K) = G :*: H :&: K.
Proof.
move=> G gG; move/subsetP=> sGK; apply/isetP => x.
apply/smulgP/idP=> [[y z Gy]|]; rewrite s2f; case/andP.
  move=> Hz Kz -> {x}; rewrite s2f andbC groupMr // sGK //.
  by apply/smulgP; exists y z.
move/smulgP=> [y z Gy Hz -> {x}] Kyz.
by exists y z => //; rewrite s2f Hz; rewrite groupMl // sGK in Kyz.
Qed.

Lemma disjoint_card_smulg :
  disjointg -> (card (H :*: K) = card H * card K)%N.
Proof.
by rewrite disjointg_card => HK1; rewrite -card_smulg (eqP HK1) muln1.
Qed.

End SubSmul.

Section Normalizer.

Open Scope group_scope.

Variables (elt : finGroupType) (H K : setType elt).
Hypothesis gH : group H.

Definition normaliser := {x, subset (H :^ x) H}.

Theorem norm_sconjg : forall x, normaliser x -> H :^ x = H.
Proof. 
move=> x Hx; apply/isetP.
by apply/subset_cardP; [rewrite card_sconjg | rewrite s2f in Hx]. 
Qed.

Lemma sconjgM : forall x y, H :^ (x * y) = (H :^ x) :^ y.
Proof. move=> x y; apply/isetP => z; rewrite !s2f /conjg; gsimpl. Qed.

Theorem group_normaliser : group normaliser.
Proof.
apply/andP; split; first by rewrite s2f sconj1g subset_refl.
apply/subsetP => x Hx; rewrite s2f; apply/subsetP => z.
by case/smulgP: Hx => u v Hu Hv -> {x}; rewrite sconjgM !norm_sconjg.
Qed.
Let gN := group_normaliser.

Theorem norm_refl : subset H normaliser.
Proof.
apply/subsetP=> x Hx; rewrite s2f; apply/subsetP => y.
by rewrite s2f /conjg invgK groupMr ?groupMl ?groupV.
Qed.

Lemma norm_rcoset : forall x, normaliser x -> subset (H :* x) normaliser.
Proof.
move=> x Nx; rewrite rcoset_smul -(smulgg gN).
apply: subset_trans (smulsg _ norm_refl); apply: smulgs.
by apply/subsetP=> ?; rewrite s2f; move/eqP <-.
Qed.

Hypothesis gK : group K.
Hypothesis sHK: subset H K.
Hypothesis nHK: subset K normaliser.

Lemma norm_smulC : H :*: K = K :*: H.
Proof.
clear gK; apply/isetP => u.
apply/smulgP/smulgP=> [[x y Hx Ky] | [y x Ky Hx]] -> {u};
  have Ny := norm_sconjg (subsetP nHK _ Ky).
- by exists y (x ^ y); last rewrite /conjg; gsimpl; rewrite -Ny s2f conjgK.
exists (x ^ y^-1) y; last rewrite /conjg; gsimpl.
by rewrite -sconjgE invgK Ny.
Qed.

Lemma norm_group_smul : group (H :*: K).
Proof. exact: smulC_group norm_smulC. Qed.

End Normalizer.

Open Scope group_scope.

Lemma norm_rcoset_lcoset : 
  forall (elt : finGroupType) (H : setType elt) x, 
   group H -> normaliser H x -> (H :* x) = (x *: H).
Proof.
move=> elt H x gHx nHx; rewrite rcoset_smul lcoset_smul.
have sxn: (subset {:x} (normaliser H)) by 
  apply/subsetP=> y; rewrite s2f => Hy; rewrite -(eqP Hy).
by apply: norm_smulC.
Qed.

Unset Implicit Arguments.

