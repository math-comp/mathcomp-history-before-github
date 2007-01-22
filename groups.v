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
Require Import tuple.
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

Variable g : finGroupType.

Lemma mulgA : forall x1 x2 x3 : g, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. exact: Group.mulP. Qed.

Lemma mul1g : forall x : g, 1 * x = x.
Proof. exact: Group.unitP. Qed.

Lemma mulVg : forall x : g, x^-1 * x = 1.
Proof. exact: Group.invP. Qed.

Lemma mulKg : forall x : g, cancel (mulg x) (mulg x^-1).
Proof.  by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulg_injl : forall x : g, injective (mulg x).
Proof. move=> x; exact: can_inj (mulKg x). Qed.

Implicit Arguments mulg_injl [].

Lemma mulgV : forall x : g, x * x^-1 = 1.
Proof. by move=> x; rewrite -{1}(mulKg x^-1 x) mulVg -mulgA mul1g mulVg. Qed.

Lemma mulKgv : forall x : g, cancel (mulg x^-1) (mulg x).
Proof. by move=> x y; rewrite mulgA mulgV mul1g. Qed.

Lemma mulg1 : forall x : g, x * 1 = x.
Proof. by move=> x; rewrite -(mulVg x) mulKgv. Qed.

Notation mulgr := (fun x y : g => y * x).

Lemma mulgK : forall x : g, cancel (mulgr x) (mulgr x^-1).
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulg_injr : forall x : g, injective (mulgr x).
Proof. move=> x; exact: can_inj (mulgK x). Qed.

Lemma mulgKv : forall x, cancel (mulgr x^-1) (mulgr x).
Proof. by move=> x y; rewrite -mulgA mulVg mulg1. Qed.

Lemma invg1 : 1^-1 = 1 :> g.
Proof. by rewrite -{2}(mulVg 1) mulg1. Qed.

Lemma invgK : @cancel g g invg invg.
Proof. by move=> x; rewrite -{2}(mulgK x^-1 x) -mulgA mulKgv. Qed.

Lemma invg_inj : @injective g g invg.
Proof. exact: can_inj invgK. Qed.

Lemma invg_mul : forall x1 x2 : g, (x2 * x1)^-1 = x1^-1 * x2^-1. 
Proof.
by move=> x1 x2; apply: (mulg_injl (x2 * x1)); rewrite mulgA mulgK !mulgV.
Qed.

End GroupIdentities.

Implicit Arguments mulg_injl [g].
Implicit Arguments mulg_injr [g].

Hint Rewrite mulg1 mul1g invg1 mulVg mulgV invgK mulgK mulgKv
             invg_mul mulgA : gsimpl.

Ltac gsimpl := autorewrite with gsimpl; try done.

Definition conjg (g : finGroupType) (x y : g) := (x^-1 * y * x)%G.

Notation "y '^g' x" := (conjg x y) (at level 30) : group_scope.

Section Conjugation.

Variable g : finGroupType.

Open Scope group_scope.

Lemma conjgE : forall x y : g, x ^g y = y^-1 * x * y. Proof. done. Qed.

Lemma conjg1 : conjg 1 =1 @id g.
Proof. by move=> x; rewrite conjgE invg1 mul1g mulg1. Qed.

Lemma conj1g : forall x : g, 1 ^g x = 1.
Proof. by move=> x; rewrite conjgE mulg1 mulVg. Qed.

Lemma conjg_mul : forall x1 x2 y : g, (x1 * x2) ^g y = x1 ^g y * x2 ^g y.
Proof. by move=> *; rewrite !conjgE !mulgA mulgK. Qed.

Lemma conjg_invg : forall x y : g, x^-1 ^g y = (x ^g y)^-1.
Proof. by move=> *; rewrite !conjgE !invg_mul invgK mulgA. Qed.

Lemma conjg_conj : forall x y1 y2 : g, (x ^g y1) ^g y2 = x ^g (y1 * y2).
Proof. by move=> *; rewrite !conjgE invg_mul !mulgA. Qed.

Lemma conjgK : forall y : g, cancel (conjg y) (conjg y^-1).
Proof. by move=> y x; rewrite conjg_conj mulgV conjg1. Qed.

Lemma conjgKv : forall y : g, cancel (conjg y^-1) (conjg y).
Proof. by move=> y x; rewrite conjg_conj mulVg conjg1. Qed.

Lemma conjg_inj : forall y : g, injective (conjg y).
Proof. move=> y; exact: can_inj (conjgK y). Qed.

Definition conjg_fp (y x : g) := x ^g y == x.

Definition commute (x y : g) := x * y = y * x.

Lemma commute_sym : forall x y, commute x y -> commute y x.
Proof. done. Qed.

Lemma conjg_fpP : forall x y : g, reflect (commute x y) (conjg_fp y x).
Proof.
move=> *; rewrite /conjg_fp conjgE -mulgA (canF_eq (mulKgv _)); exact: eqP.
Qed.

Lemma conjg_fp_sym : forall x y : g, conjg_fp x y = conjg_fp y x.
Proof. move=> x y; exact/conjg_fpP/conjg_fpP. Qed.


End Conjugation.

Implicit Arguments conjg_inj [g].
Implicit Arguments conjg_fpP [g x y].
Prenex Implicits conjg_fpP.

Section GroupSet.

Open Scope group_scope.

Variable g : finGroupType.

Variable h : setType g.

(* Cosets *)

Definition lcoset x : setType g := {y, h (x^-1 * y)}.
Definition rcoset x : setType g := {y, h (y * x^-1)}.

Lemma lcosetP : forall y z, reflect (exists2 x, h x & z = y * x) (lcoset y z).
Proof.
move=> y z; apply: (iffP idP) => [Hx | [x Hx ->]]; last by rewrite s2f mulKg.
by exists (y^-1 * z); last rewrite mulKgv; rewrite s2f in Hx.
Qed.

Lemma rcosetP : forall y z, reflect (exists2 x, h x & z = x * y) (rcoset y z).
Proof.
move=> y z; apply: (iffP idP) => [Hx | [x Hx ->]]; last by rewrite s2f mulgK.
by exists (z * y^-1); last rewrite mulgKv; rewrite s2f in Hx.
Qed.

(* product *)

Section Prodg.

Variable k : setType g.

Definition prodg : setType g := {z, ~~ disjoint k {y, rcoset y z}}.

CoInductive mem_prodg (z : g) : Prop :=
  MemProdg x y : h x -> k y -> z = x * y -> mem_prodg z.

Lemma prodgP : forall z, reflect (mem_prodg z) (prodg z).
Proof.
move => z; rewrite s2f; apply: (iffP set0Pn) => [[y]|[x y Hx Hy ->]].
  by rewrite /setI s2f;case/andP=> Hy; case/rcosetP=> x *; exists x y.
by exists y; rewrite /setI s2f Hy; apply/rcosetP; exists x.
Qed.

End Prodg.

Definition group := h 1 && subset (prodg h) h.

Definition subgroup k := group && subset h k.

Lemma groupP : reflect (h 1 /\ forall x y, h x -> h y -> h (x * y)) group.
Proof.
apply: (iffP andP) => [] [H1 HM]; split=> {H1}//.
  by move=> x y Hx Hy; apply: (subsetP HM); apply/prodgP; exists x y.
by apply/subsetP=> z; case/prodgP=> [x y Hx Hy ->]; auto.
Qed.

Hypothesis Hh : group.

Lemma group1 : h 1. Proof. by case/groupP: Hh. Qed.

Lemma groupM : forall x y, h x -> h y -> h (x * y).
Proof. by case/groupP: Hh. Qed.

Lemma groupVr : forall x, h x -> h x^-1.
Proof.
move=> x Hx; rewrite -(finv_f (mulg_injl x) x^-1) mulgV /finv.
elim: pred => [|n IHn] /=; [exact: group1 | exact: groupM].
Qed.

Lemma groupV : forall x, h x^-1 = h x.
Proof. move=> x; apply/idP/idP; first rewrite -{2}[x]invgK; exact: groupVr. Qed.

Lemma groupMl : forall x y, h x -> h (x * y) = h y.
Proof.
move=> x y Hx; apply/idP/idP=> Hy; last exact: groupM.
rewrite -(mulKg x y); exact: groupM (groupVr _) _.
Qed.

Lemma groupMr : forall x y, h x -> h (y * x) = h y.
Proof.
move=> x y Hx; apply/idP/idP=> Hy; last exact: groupM.
rewrite -(mulgK x y); exact: groupM (groupVr _).
Qed.

Lemma groupVl : forall x,  h x^-1 ->  h x.
Proof. by move=> x; rewrite groupV. Qed.

Definition subFinGroupType : finGroupType.
pose d := sub_finType h.
pose d1 : d := EqSig h 1 group1.
pose dV (u : d) : d := EqSig h _ (groupVr (valP u)).
pose dM (u1 u2 : d) : d := EqSig h _ (groupM (valP u1) (valP u2)).
(exists d d1 dV dM => *; apply: val_inj);
  [exact: mul1g | exact: mulVg | exact: mulgA].
Defined.

Lemma pos_card_group : 0 < card h.
Proof. rewrite lt0n; apply/set0Pn; exists (1 : g); exact: group1. Qed.

Lemma prodg_subr : forall k : setType g, subset k (prodg k).
Proof. 
move=> k; apply/subsetP=> x Hx; apply/prodgP.
by exists (1 : g) x; [exact group1 | | rewrite mul1g].
Qed.

Lemma prodgg : prodg h =1 h.
Proof. by apply/subset_eqP; rewrite prodg_subr andbT; case/andP: Hh. Qed.

End GroupSet.



Section ConjugationSet.

Open Scope group_scope.

Variable g: finGroupType.
Variable H : setType g.
Hypothesis group_H  :group H.


(*  Definition of the conjugate set xHx^-1 *)


(* x^-1 * y * x belongs to H *)
Definition conjsg x := {y, H (y ^g x)}.

Theorem conjsgE : forall x y, conjsg x y = H (y ^g x).
Proof. by move => *; rewrite s2f. Qed.

Theorem conjsg1: forall x, conjsg x 1.
Proof. by move=> x; rewrite s2f conj1g; apply: group1. Qed.

Theorem conjs1g: forall x, conjsg 1 x = H x.
Proof. by move=> x; rewrite s2f conjg1. Qed.

Theorem conjsg_inv: forall x y, conjsg x y -> conjsg x y^-1.
Proof. move=> x y; rewrite !s2f conjg_invg; exact: groupVr. Qed.

Theorem conjsg_conj: forall x y z, conjsg (x * y) z = conjsg y (z ^g x).
Proof. by move=> x y z;rewrite !s2f conjg_conj. Qed.

Theorem conjsg_subgrp: forall x, group (conjsg x).
Proof. 
  move=> x.
  apply/andP; split; first by apply: conjsg1.
  apply/subsetP=> z; case/prodgP=> x1 x2 Hx1 Hx2 ->{z};rewrite /conjsg !s2f conjg_mul.
  rewrite !s2f in Hx1 Hx2; exact: groupM. 
Qed.

(*  y in xHx^-1 iff x^-1yx is in H    *)
Theorem conjsg_image: forall y,
  conjsg y =1 image (conjg y^-1) H.
Proof.
  move=> y x; rewrite {2} (_:x = conjg y^-1 (conjg y x )) ?s2f.
    rewrite/conjsg image_f; by [rewrite /conjg | apply conjg_inj].
  by rewrite conjgK.
Qed.

Theorem conjsg_inv1: forall x,
  (conjsg x) =1 H -> (conjsg x^-1) =1 H.
Proof. by move=> x Hx y; rewrite -conjs1g -(mulVg x) conjsg_conj Hx s2f. Qed.

Theorem conjsg_card: forall x,
  card (conjsg x) = card H.
Proof. move=>x; rewrite (eq_card (conjsg_image x)); apply card_image; exact: conjg_inj. Qed.

End ConjugationSet.


Theorem eq_conjsg: forall (G:finGroupType) (a b:setType G) (x: G),
  a =1 b -> conjsg a x =1 conjsg b x.
Proof. by move=> G a b x H0 y; rewrite (iset_eq H0). Qed.
(* rewrite/(conjsg G) H0. *)


Definition group_of_type := fun g : finGroupType => {x:g,true}.

(*
Proof.  
by move=> g; rewrite /group s2f /=; apply/subsetP => w; rewrite !s2f.
Qed.
*)

Coercion group_of_type : finGroupType >-> setType.


Hint Resolve pos_card_group.

Section LaGrange.

Variables (g : finGroupType) (h k : setType g).
Hypothesis Hh : group h.
Hypothesis Hk : group k.
Hypothesis Hhk : subset h k.
Let HhkP := subsetP Hhk.

Open Scope group_scope.

Lemma prodg_subl : subset h (prodg h k).
Proof.
apply/subsetP=> x Hx; apply/prodgP.
by exists x (1 : g); [ | exact: group1 | rewrite mulg1].
Qed.

Lemma rcoset_refl : forall x, rcoset h x x.
Proof. by move=> x; rewrite /rcoset s2f mulgV group1. Qed.

Lemma rcoset_sym : forall x y, rcoset h x y = rcoset h y x.
Proof. by move=> *; apply/idP/idP; rewrite !s2f; move/(groupVr Hh); rewrite invg_mul invgK. Qed.

Lemma rcoset_trans : forall x y z, rcoset h x y -> rcoset h y z -> rcoset h x z.
Proof. by move=> x y z Hxy; rewrite s2f in Hxy; rewrite !s2f -(groupMr Hh _ Hxy) -mulgA mulKg. Qed.

Lemma rcoset_trans1 : forall x y, rcoset h x y -> rcoset h x =1 rcoset h y.
Proof. by move=> x y Hxy u; rewrite s2f in Hxy; rewrite !s2f -{1}(mulgKv y u) -mulgA groupMr. Qed.

Lemma rcoset_trans1r : forall x y, 
  rcoset h x y -> forall z, rcoset h z x = rcoset h z y.
Proof. move=> x y Hxy z; rewrite !(rcoset_sym z) //; exact: rcoset_trans1. Qed.

Lemma connect_rcoset : connect (rcoset h) =2 rcoset h.
Proof. Print connect.connect.
move=> x y; apply/idP/idP. 
  move/connectP=> [p Hp <- {y}].
  elim: p x Hp => [|y p IHp] x /=; first by rewrite rcoset_refl.
  case/andP=> Hxy; move/IHp; exact: rcoset_trans.
by rewrite s2f => H; apply: connect1; rewrite s2f.
Qed.

Lemma rcoset_csym : connect_sym (rcoset h).
Proof. by move=> x y; rewrite !connect_rcoset rcoset_sym. Qed.

Lemma rcoset1 : rcoset h 1 =1 h.
Proof. by move=> x; rewrite s2f invg1 mulg1. Qed.

Lemma card_rcoset : forall x, card (rcoset h x) = card h.
Proof.
move => x. 
have:= (card_preimage (mulg_injr x^-1) h).
cut (card (rcoset (g:=g) h x)=card (preimage (fun y : g => y * x^-1) h)).
cut (card (setI (codom (fun y : g => y * x^-1)) h)=card h).
move => H1 H2 H3.
by rewrite -H1 H2.
apply: eq_card=> y.
rewrite /setI andbC; case Hy: (h y) => //=; apply/set0Pn; exists (y * x).
by rewrite /preimage mulgK set11.
by apply: eq_card => w; rewrite /preimage s2f.
Qed.
(* etrans: unable to make it work :(
move=> x; apply: etrans (card_preimage (mulg_injr x^-1) _) _. apply: eq_card=> y.
rewrite /setI andbC; case Hy: (h y) => //=; apply/set0Pn; exists (y * x).
by rewrite /preimage mulgK set11.
Qed.
*)

Lemma closed_rcoset : closed (rcoset h) k.
Proof. by move=> x y /=; rewrite s2f; move/HhkP => Hy; rewrite -(mulgKv x y) groupMl. Qed.

Definition indexg := n_comp (rcoset h).

Lemma rcoset_root : forall y, rcoset h y (root (rcoset h) y).
Proof. by move=> y; rewrite -connect_rcoset connect_root. Qed.

Theorem LaGrange : (card h * indexg k)%N = card k.
Proof.
pose a x := roots (rcoset h) x && k x.
pose dha := prod_finType (sub_finType h) (sub_finType a); pose dk := sub_finType k.
suff: card (setA dha) = card (setA dk) by rewrite /dha card_prod /dk !card_sub. 
have Hf: forall u : dha, k (let: EqPair ux uy := u in val ux * val uy).
  move=> [[x Hx] [y Hy]] /=; case/andP: Hy => _;move/HhkP: Hx; exact: groupM.
have Hf'a: forall u : dk, a (root (rcoset h) (val u)).
  move=> [z Hz]; rewrite /= /a (roots_root rcoset_csym).
  by rewrite -(closed_connect closed_rcoset (connect_root _ _)).
have Hf'h: forall u : dk,
  h ((val u) * (root (fun x : g => {y0 : g, h (y0 * x^-1)}) (val u))^-1).
  move => u.
  have tmp: rcoset h (root (rcoset h) (val u)) (val u).
    by rewrite rcoset_sym rcoset_root.
  by rewrite s2f in tmp.
apply: bij_eq_card_setA; exists (fun u => EqSig k _ (Hf u)).
pose f' u := (EqPair (EqSig h _ (Hf'h u)) (EqSig a _ (Hf'a u)):prod_finType _ _).
exists f' => [[[x Hx] [y Hy]] | [z Hz]]; last by apply: val_inj; exact: mulgKv.
apply/eqP; do 2!rewrite /set1 /=; case/andP: Hy; move/eqP=> Dy _.
suff ->: root (rcoset h) (x * y) = y by rewrite mulgK !set11.
rewrite -{2}Dy; apply/(rootP rcoset_csym); apply connect1.
by rewrite s2f invg_mul mulKgv groupV.
Qed.

Lemma group_dvdn : dvdn (card h) (card k).
Proof. by apply/dvdnP; exists (indexg k); rewrite mulnC LaGrange. Qed.

Lemma group_divn : divn (card k) (card h) = indexg k.
Proof. by rewrite -LaGrange // divn_mulr; auto. Qed.

Lemma lcoset_inv : forall x y, lcoset h x y = rcoset h x^-1 y^-1.
Proof. by move=> x y; rewrite !s2f -invg_mul groupV. Qed.

Lemma lcoset_refl : forall x, lcoset h x x.
Proof. by move=> x; rewrite s2f mulVg group1. Qed.

Lemma lcoset_sym : forall x y, lcoset h x y = lcoset h y x.
Proof. by move=> x y; rewrite !lcoset_inv rcoset_sym. Qed.

Lemma lcoset_trans : forall x y z, lcoset h x y -> lcoset h y z -> lcoset h x z.
Proof. move=> x y z; rewrite !lcoset_inv; exact: rcoset_trans. Qed.

Lemma connect_lcoset : connect (lcoset h) =2 lcoset h.
Proof.
move=> x y; apply/idP/idP; (*rewrite !s2f ;*) [move/connectP=> [p Hp <- {y}] |]; last first. 
  by rewrite s2f; move => *; apply: connect1; rewrite s2f.
elim: p x Hp => [|y p IHp] x /=; first by rewrite s2f mulVg // group1.
by case/andP=> Hxy; move/IHp; apply: lcoset_trans.
Qed.

Lemma lcoset_csym : connect_sym (lcoset h).
Proof. by move=> x y; rewrite !connect_lcoset lcoset_sym. Qed.

Lemma lcoset1 : lcoset h 1 =1 h.
Proof. by move=> x; rewrite s2f invg1 mul1g. Qed.

Lemma card_lcoset : forall x, card (lcoset h x) = card h.
Proof.
move=> x; rewrite -(card_image (@invg_inj g)) -(card_rcoset x^-1).
apply: eq_card => y; rewrite -[y]invgK -lcoset_inv image_f //; exact: invg_inj.
Qed.

Lemma closed_lcoset : closed (lcoset h) k.
Proof.
by move=> x y /=; rewrite lcoset_inv; move/closed_rcoset; rewrite !groupV.
Qed.

Lemma lcoset_indexg : n_comp (lcoset h) k = indexg k.
Proof.
rewrite (adjunction_n_comp invg lcoset_csym rcoset_csym closed_lcoset).
  by apply: eq_n_comp_r => x; rewrite /preimage groupV.
apply: (strict_adjunction rcoset_csym closed_lcoset (@invg_inj _)).
  by apply/subsetP=> x _; rewrite -(invgK x) codom_f.
by move=> x y _ /=; rewrite lcoset_inv !invgK.
Qed.

End LaGrange.


Section Eq.

Open Scope group_scope.

Variable g : finGroupType.

Lemma eq_lcoset : forall a1 a2 : setType g, a1 =1 a2 -> lcoset a1 =2 lcoset a2.
Proof. move=> a1 a2 Da x y /=; rewrite !s2f; exact: Da. Qed.

Lemma eq_rcoset : forall a1 a2 : setType g, a1 =1 a2 -> rcoset a1 =2 rcoset a2.
Proof. move=> a1 a2 Da x y; rewrite !s2f; exact: Da. Qed.

Lemma eq_prodg_l : forall a1 a2 b : setType g, a1 =1 a2 -> prodg a1 b =1 prodg a2 b.
Proof.
move=> a1 a2 b; move/eq_rcoset=> Da x; rewrite !s2f; congr negb; rewrite !(disjoint_sym b).
apply: eq_disjoint=> y. 
by have:=Da y x; rewrite !s2f.
Qed.

Lemma eq_prodg_r : forall a b1 b2 : setType g, b1 =1 b2 -> prodg a b1 =1 prodg a b2.
Proof. move=> a b1 b2 Db x; rewrite !s2f; congr negb; apply: eq_disjoint=> y; exact: Db. Qed.

Lemma eq_group: forall a b : setType g, a =1 b -> group a = group b.
Proof.
move=> a b Da; rewrite /group Da (eq_subset_r Da). 
congr andb. (* SLOW!! *)
by apply: eq_subset=> x; rewrite (eq_prodg_l _ Da) (eq_prodg_r _ Da).
Qed.

End Eq.

(* Shows that given two sets h k, if hk=kh then hk is a subgroup *)
Section SubProd.

Open Scope group_scope.

Variable g : finGroupType.

Lemma prodgA : forall h1 h2 h3 : setType g,
  prodg h1 (prodg h2 h3) =1 prodg (prodg h1 h2) h3.
Proof.
move=> h1 h2 h3 x; apply/prodgP/prodgP.
  case=> x1 x23 Hx1; case/prodgP=> x2 x3 Hx2 Hx3 ->{x23}; rewrite mulgA => Dx.
  by exists (x1 * x2) x3 => //; apply/prodgP; exists x1 x2.
case=> x12 x3; case/prodgP=> x1 x2 Hx1 Hx2 ->{x12} Hx3; rewrite -mulgA => Dx.
by exists x1 (x2 * x3) => //; apply/prodgP; exists x2 x3.
Qed.

Section GroupProdC.

Variables h k : setType g.
Hypothesis Hh : group h.
Hypothesis Hk : group k.

Lemma prodC_group : prodg h k =1 prodg k h -> group (prodg h k).
Proof.
move=> Hhk; apply/andP; split.
  apply/prodgP; exists (1 : g) (1 : g); by [exact: group1 | rewrite mulg1].
have Hhkh : prodg (prodg h h) k =1 (prodg (prodg h k) h).
  move=> x; rewrite -!prodgA; (* SLOW! *) exact: eq_prodg_r.
apply/subsetP=> x; rewrite prodgA -(eq_prodg_l _ Hhkh) -prodgA.
by rewrite (eq_prodg_l _ (prodgg Hh)) (eq_prodg_r _ (prodgg Hk)).
Qed.

Lemma group_prodC : group (prodg h k) -> prodg h k =1 prodg k h.
Proof.
move=> Hhk x; rewrite -{Hhk}(groupV Hhk).
by apply/idP/idP; case/prodgP => y z;
  rewrite -(groupV Hh) -(groupV Hk) => Hy Hz Dx;
  apply/prodgP; exists z^-1 y^-1; rewrite // -invg_mul -Dx ?invgK.
Qed.

End GroupProdC.

Variables h k : setType g.
Hypothesis Hh : group h.
Hypothesis Hk : group k.

Lemma group_prod_sym : group (prodg h k) = group (prodg k h).
Proof.
by apply/idP/idP; move/(group_prodC _ _)=> Hhk;
  apply: prodC_group => // x; rewrite Hhk.
Qed.

Definition disjointg := subset (setI h k) (set1 1).

Lemma disjointgP : reflect (setI h k =1 set1 1) disjointg.
Proof.
apply: (iffP subsetP) => Hhk x; last by rewrite Hhk.
by apply/idP/idP; [exact: Hhk | move/eqP <-; rewrite /setI !group1].
Qed.

Lemma disjointg_card : disjointg = (card (setI h k) == 1%nat).
Proof.
apply/idP/idP; first by move/disjointgP; move/eq_card->; rewrite card1.
rewrite (cardD1 1) {1}/setI !group1 //= add1n eqSS; move/set0P=> Hhk.
by apply/subsetP=> x Hx; case/nandP: (Hhk x); rewrite ?negbK ?Hx.
Qed.

Lemma card_prodg_disjoint :
  disjointg -> card (prodg h k) = (card h * card k)%N.
Proof.
move=> Hhk; rewrite -(card_sub h) -(card_sub k) -card_prod.
set dhk := prod_finType _ _.
pose f (u : dhk) := let: EqPair uh uk := u in val uh * val uk.
have Hf: injective f.
  move=> [[x1 Hx1] [y1 Hy1]] [[x2 Hx2] [y2 Hy2]] /= Dxy.
  have Dx : x2^-1 * x1 = y2 * y1^-1 by rewrite -(mulgK y1 x1) Dxy -mulgA mulKg.
  have Dy : y2 * y1^-1 = 1.
    apply/eqP; rewrite eq_sym -(disjointgP Hhk) /setI -{1}Dx.
    by rewrite !groupM // groupVr.
  rewrite -(mulKgv x2 x1) -(mulgKv y1 y2) Dx Dy mulg1 mul1g in Hx1 Hy2 *.
  congr EqPair; exact: val_inj.
rewrite -(card_image Hf); apply: eq_card => z; apply/prodgP/set0Pn.
  case=> x y Hx Hy ->{z}; exists (EqPair (EqSig h x Hx) (EqSig k y Hy)).
  by rewrite /setI /preimage /= set11.
by case=> [[[x Hx] [y Hy]]]; case/andP; move/eqP=> /= -> _; exists x y.
Qed.

End SubProd.

Section Normalizer.

Open Scope group_scope.

Variables (g: finGroupType) (H K: setType g).
Hypothesis group_H  :group H.


Definition normaliser := {x, subset H (conjsg H x)}.

Theorem norm_conjsg : forall x,
  normaliser x -> H =1 (conjsg H x).
Proof. 
by move=> x Hx;apply/subset_cardP; [symmetry;apply conjsg_card|rewrite s2f in Hx]. 
Qed.

Theorem normaliser_grp: group normaliser.
Proof.
  apply/andP; split; [rewrite s2f|]; apply/subsetP => x Hx.
    by rewrite s2f conjg1.
  rewrite s2f; apply/subsetP => z Hz; case/prodgP: Hx => u v Hu Hv -> {x}.
  rewrite s2f in Hv.
  by rewrite conjsg_conj; apply (subsetP Hv); rewrite -conjsgE -(norm_conjsg Hu z).
Qed.

Theorem subset_normaliser: subset H normaliser.
Proof.
apply/subsetP => x Hx;rewrite/normaliser s2f;apply/subsetP => y Hy;rewrite/conjsg.
by rewrite s2f; apply: groupM;gsimpl;rewrite groupM // groupV. 
Qed.

Lemma normaliser_rcoset : closed (rcoset H) normaliser.
Proof. apply closed_rcoset; [exact normaliser_grp | exact subset_normaliser]. Qed.


Hypothesis group_K: group K.
Hypothesis subset_HK: subset H K.


Lemma normaliser_prodg : subset K normaliser -> prodg H K =1 prodg K H.
Proof.
move=> HK x; apply/idP/idP; case/prodgP => u v Hu Hv ->; rewrite s2f in Hu Hv *; apply/set0Pn; rewrite/setI.
 exists (conjg v u); rewrite !s2f {2}/conjg ; gsimpl; rewrite Hv -conjsgE.
 have tmp :=  (subsetP HK v Hv); rewrite s2f in tmp.
 by rewrite (subsetP tmp u).
exists u; rewrite !s2f Hu -(invgK u) {2}(invgK u) -conjgE -conjsgE.
rewrite -(groupV group_K) in Hu.
have tmp:= (subsetP HK (u^-1) Hu); rewrite s2f in tmp.
by rewrite (subsetP tmp v).
Qed.

Lemma normaliser_prodg_grp : subset K normaliser -> group (prodg H K).
Proof.
move=> H1; apply prodC_group => //; exact: normaliser_prodg.
Qed.


End Normalizer.


(* group of permutations *)
Section PermGroup.

Variable d:finType.

Definition permType := eq_sig (fun g : fgraphType d d => uniq (@fval d d g)).

Canonical Structure perm_eqType := @EqType permType _ (@val_eqP _ _).

Canonical Structure perm_finType := @FinType perm_eqType _ (@sub_enumP _ _).

Definition fun_of_perm := fun u : permType => (val u : fgraphType _ _) : d -> d.

Coercion fun_of_perm : permType >-> Funclass.

Lemma perm_uniqP : forall g : fgraphType d d, reflect (injective g) (uniq (@fval  d d g)).
Proof.
move=> g; apply: (iffP idP) => Hg.
  apply: can_inj (fun x => sub x (enum d) (index x (@fval _ _ g))) _ => x.
  by rewrite {2}/fun_of_fgraph; unlock; rewrite index_uniq ?sub_index ?fproof ?mem_enum /card // count_setA index_mem mem_enum.
by rewrite -[g]can_fun_of_fgraph /= uniq_maps // uniq_enum.
Qed.


Lemma eq_fun_of_perm: forall u v : permType, u =1 v -> u = v.
Proof.
move => u v Huv. apply: val_inj. 
rewrite -(can_fun_of_fgraph (val u)) -(can_fun_of_fgraph (val v)).
apply: fval_inj; exact: (eq_maps Huv).
Qed.

Lemma perm_of_injP : forall f : d -> d, injective f -> uniq (@fval d d (fgraph_of_fun f)).
Proof.
move=> f Hf; apply/perm_uniqP.
by apply: eq_inj Hf _ => x; rewrite can_fgraph_of_fun.
Qed.

Definition perm_of_inj f (Hf : injective f) : permType :=
  EqSig (fun g : fgraphType d d => uniq ((@fval d d g))) _ (perm_of_injP Hf).

Lemma perm_inj : forall u : permType, injective u.
Proof. by case=> g Hg; apply/perm_uniqP. Qed.

Definition perm_elem := perm_finType.

(* Axiom perm_unit : perm_elem. *)
Lemma inj_id : @injective d _ id.
Proof. done. Qed. 
Definition perm_unit := perm_of_inj inj_id.

(*Axiom perm_inv : perm_elem -> perm_elem.*)

Definition perm_inv u := perm_of_inj (finv_inj (@perm_inj u)).

Definition perm_mul u v := perm_of_inj (inj_comp (@perm_inj u) (@perm_inj v)).

Lemma perm_unitP : forall x, perm_mul perm_unit x = x.
Proof.
move=> u; apply eq_fun_of_perm => x.
by do 2!rewrite /fun_of_perm /= /comp can_fgraph_of_fun.
Qed.

Lemma perm_invP : forall x, perm_mul (perm_inv x) x = perm_unit.
Proof. 
move=> u; apply: eq_fun_of_perm => x.
do 3!rewrite /fun_of_perm /= /comp can_fgraph_of_fun. 
by rewrite finv_f; last exact: perm_inj.
Qed.

Lemma perm_mulP : 
  forall x y z, perm_mul x (perm_mul y z) = perm_mul (perm_mul x y) z.
Proof.
move=> u v w; apply: eq_fun_of_perm => x.
by do 4!rewrite /fun_of_perm /= /comp can_fgraph_of_fun. 
Qed.

Canonical Structure perm_finGroupType := 
  FinGroupType perm_unitP perm_invP perm_mulP.

Definition perm a (u : permType) := subset (fun x => u x != x) a.

Lemma perm_closed : forall a u x, perm a u -> a (u x) = a x.
Proof.
move=> a u x Hu; case Hx: (u x != x); last by move/eqP: Hx => ->.
by rewrite !(subsetP Hu) ?(inj_eq (@perm_inj u)).
Qed.  

Definition transpose (x y z : d) := if x == z then y else if y == z then x else z.

Lemma transposeK : forall x y, involutive (transpose x y).
Proof.
move=> x y z; rewrite /transpose.
case Hx: (x == z); first by rewrite (eqP Hx) set11; case: eqP.
by case Hy: (y == z); [rewrite set11 (eqP Hy) | rewrite Hx Hy].
Qed.

Definition transperm x y := perm_of_inj (can_inj (transposeK x y)).

Open Scope group_scope.

Lemma square_transperm : forall x y, let t := transperm x y in t * t = 1.
Proof.
move=> x y; apply: eq_fun_of_perm => z; rewrite /mulg /=.
do 4!rewrite /fun_of_perm /= /comp can_fgraph_of_fun.
exact: transposeK.
Qed.

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

Lemma card_perm: forall a : set d, card (perm a) = fact (card a).
Proof.
move=> a; move Dn: (card a) => n; move/eqP: Dn; elim: n a => [|n IHn] a.
  move/set0P=> Da; rewrite /= -(card1 perm_unit); apply: eq_card=> u.
  apply/subsetP/eqP => [Hu | <- {u} x].
    apply: eq_fun_of_perm => x; apply: eqP. 
    rewrite {1}/fun_of_perm /= can_fgraph_of_fun eq_sym.
    by apply/idPn; move/Hu; rewrite Da.
  by rewrite {1}/fun_of_perm /= can_fgraph_of_fun set11.
case: (pickP a) => [x Hx Ha|]; last by move/eq_card0->.
move: (Ha); rewrite (cardD1 x) Hx; set a' := setD1 a x; move/(IHn a')=> {IHn} Ha'.
pose h (u : permType) := EqPair (u x) (transperm x (u x) * u) : prod_finType _ _.
have Hh: injective h.
  move=> u1 u2 H; case: H (congr1 (@eq_pi2 _ _) H) => /= -> _; exact: mulg_injl.
rewrite /fact -/fact -(eqP Ha) -Ha' mulnI -card_prod -(card_image Hh).
apply: eq_card=> [[y v]]; apply/set0Pn/andP; rewrite /preimage /setI /=.
  case=> u; do 2!case/andP; do 2!move/eqP->; move=> Hu {y v}.
  split; first by rewrite perm_closed.
  apply/subsetP=> z. do 2!rewrite /mulg /= /fun_of_perm /= can_fgraph_of_fun /comp.
  rewrite /transpose -/(u x) -/(u z) (inj_eq (@perm_inj u)) /a' /setD1.
  case: (x =P z) => [<-|_]; first by case/eqP; case: eqP.
  case: (x =P u z) => [Dx | _]; first by rewrite -(perm_closed _ Hu) -Dx.
  exact: subsetP Hu z.
rewrite /= in v *; move=> [Hy Hv]; pose u : permType := transperm x y * v.
have Dy: y = u x.
  do 2!rewrite /u /= /fun_of_perm /= can_fgraph_of_fun /comp.
  rewrite -/(v x) (_ : v x = x) /transpose ?set11 //.
  by apply/eqP; apply/idPn; move/(subsetP Hv); rewrite /a'/ setD1 set11.
exists u; rewrite /h -Dy /u mulgA square_transperm mul1g set11.
apply/subsetP=> z; do 2!rewrite /fun_of_perm /= can_fgraph_of_fun /comp.
rewrite (inv_eq (transposeK x y)) /transpose -/(v z).
by do 2!case: (_ =P z) => [<- //| _]; move/(subsetP Hv); case/andP.
Qed.

End PermGroup.

Unset Implicit Arguments.
