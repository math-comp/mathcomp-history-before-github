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

Lemma commute1g: forall x: g, commute 1 x.
Proof.
by move => x; rewrite /commute; gsimpl.
Qed.

Lemma commuteg1: forall x, commute x 1.
Proof.
by move => x; rewrite /commute; gsimpl.
Qed.

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

Variable h : set g.

(* Cosets *)

Definition lcoset x : set g := fun y => h (x^-1 * y).
Definition rcoset x : set g := fun y => h (y * x^-1).

Lemma lcosetP : forall y z, reflect (exists2 x, h x & z = y * x) (lcoset y z).
Proof.
move=> y z; apply: (iffP idP) => [Hx | [x Hx ->]]; last by rewrite /lcoset mulKg.
by exists (y^-1 * z); last rewrite /lcoset mulKgv.
Qed.

Lemma rcosetP : forall y z, reflect (exists2 x, h x & z = x * y) (rcoset y z).
Proof.
move=> y z; apply: (iffP idP) => [Hx | [x Hx ->]]; last by rewrite /rcoset mulgK.
by exists (z * y^-1); last rewrite /rcoset mulgKv.
Qed.

(* product *)

Section Prodg.

Variable k : set g.

Definition prodg : set g := fun z => ~~ disjoint k (fun y => rcoset y z).

Definition prodf (z: prod_finType g g) := eq_pi1 z * eq_pi2 z.

CoInductive mem_prodg (z : g) : Prop :=
  MemProdg x y : h x -> k y -> z = x * y -> mem_prodg z.

Lemma prodgP : forall z, reflect (mem_prodg z) (prodg z).
Proof.
move=> z; apply: (iffP set0Pn) => [[y]|[x y Hx Hy ->]].
  by case/andP=> Hy; case/rcosetP=> x *; exists x y.
by exists y; rewrite /setI Hy; apply/rcosetP; exists x.
Qed.

Lemma in_prodg : forall x y, h x -> k y -> prodg (x * y).
Proof.
move=> x y Hx Hy; apply/prodgP.
exact: (MemProdg Hx Hy).
Qed.

Lemma prodg_image: prodg =1 image prodf (prod_set h k).
move => x; apply/prodgP/imageP.
  case => y z Hy Kz ->; exists (EqPair y z) => //.
  by rewrite /prod_set /= Hy.
by case => [[y z]] H1 H2; exists y z => //; case/andP: H1.
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

Lemma prodg_subr : forall k, subset k (prodg k).
Proof. 
move=> k; apply/subsetP=> x Hx; apply/prodgP.
by exists (1 : g) x; [exact group1 | | rewrite mul1g].
Qed.

Lemma prodgg : prodg h =1 h.
Proof. by apply/subset_eqP; rewrite prodg_subr andbT; case/andP: Hh. Qed.

End GroupSet.

Lemma group_of_type : forall g : finGroupType, group g.
Proof. move=> g; exact/subsetP. Qed.

Coercion group_of_type : finGroupType >-> is_true.

Hint Resolve pos_card_group.

Section LaGrange.

Variables (g : finGroupType) (h k : set g).
Hypothesis Hh : group h.
Hypothesis Hk : group k.
Hypothesis Hhk : subset h k.
Let HhkP := subsetP Hhk.

Open Scope group_scope.

(* Intersection is a group *)
Lemma setI_group : group (setI h k).
Proof.
apply/groupP; split; rewrite /setI.
  by rewrite !group1.
move => x y; case/andP => Hx Kx; case/andP => Hy Ky.
rewrite !groupM //.
Qed.

Lemma prodg_subl : subset h (prodg h k).
Proof.
apply/subsetP=> x Hx; apply/prodgP.
by exists x (1 : g); [ | exact: group1 | rewrite mulg1].
Qed.

Lemma rcoset_refl : forall x, rcoset h x x.
Proof. by move=> x; rewrite /rcoset mulgV group1. Qed.

Lemma rcoset_sym : forall x y, rcoset h x y = rcoset h y x.
Proof. by move=> *; apply/idP/idP; move/(groupVr Hh); rewrite invg_mul invgK. Qed.

Lemma rcoset_trans : forall x y z, rcoset h x y -> rcoset h y z -> rcoset h x z.
Proof. by move=> x y z Hxy; rewrite /rcoset -(groupMr Hh _ Hxy) -mulgA mulKg. Qed.

Lemma connect_rcoset : connect (rcoset h) =2 rcoset h.
Proof.
move=> x y; apply/idP/idP; [move/connectP=> [p Hp <- {y}] | exact: connect1].
elim: p x Hp => [|y p IHp] x /=; first by rewrite rcoset_refl.
case/andP=> Hxy; move/IHp; exact: rcoset_trans.
Qed.

Lemma rcoset_csym : connect_sym (rcoset h).
Proof. by move=> x y; rewrite !connect_rcoset rcoset_sym. Qed.

Lemma rcoset1 : rcoset h 1 =1 h.
Proof. by move=> x; rewrite /rcoset invg1 mulg1. Qed.

Lemma card_rcoset : forall x, card (rcoset h x) = card h.
Proof.
move=> x; apply: etrans (card_preimage (mulg_injr x^-1) _) _; apply: eq_card=> y.
rewrite /setI andbC; case Hy: (h y) => //=; apply/set0Pn; exists (y * x).
by rewrite /preimage mulgK set11.
Qed.

Lemma closed_rcoset : closed (rcoset h) k.
Proof. by move=> x y; move/HhkP => Hy; rewrite -(mulgKv x y) groupMl. Qed.

Definition indexg := n_comp (rcoset h).

Lemma rcoset_root : forall y, rcoset h y (root (rcoset h) y).
Proof. by move=> y; rewrite -connect_rcoset connect_root. Qed.

Theorem LaGrange : (card h * indexg k)%N = card k.
Proof.
pose a x := roots (rcoset h) x && k x.
pose dha := prod_finType (sub_finType h) (sub_finType a); pose dk := sub_finType k.
suff: card dha = card dk by rewrite /dha card_prod /dk !card_sub.
have Hf: forall u : dha, k (let: EqPair ux uy := u in val ux * val uy).
  move=> [[x Hx] [y Hy]] /=; case/andP: Hy => _; move/HhkP: Hx; exact: groupM.
have Hf'a: forall u : dk, a (root (rcoset h) (val u)).
  move=> [z Hz]; rewrite /= /a (roots_root rcoset_csym).
  by rewrite -(closed_connect closed_rcoset (connect_root _ _)).
have Hf'h: forall u : dk, rcoset h (root (rcoset h) (val u)) (val u).
  by move=> u; rewrite rcoset_sym rcoset_root.
apply: bij_eq_card_setA; exists (fun u => EqSig k _ (Hf u)).
pose f' u := EqPair (EqSig h _ (Hf'h u)) (EqSig a _ (Hf'a u)).
exists f' => [[[x Hx] [y Hy]] | [z Hz]]; last by apply: val_inj; exact: mulgKv.
apply/eqP; do 2!rewrite /set1 /=; case/andP: Hy; move/eqP=> Dy _.
suff ->: root (rcoset h) (x * y) = y by rewrite mulgK !set11.
rewrite -{2}Dy; apply/(rootP rcoset_csym); apply connect1.
by rewrite /rcoset invg_mul mulKgv groupV.
Qed.

Lemma group_dvdn : dvdn (card h) (card k).
Proof. by apply/dvdnP; exists (indexg k); rewrite mulnC LaGrange. Qed.

Lemma group_divn : divn (card k) (card h) = indexg k.
Proof. by rewrite -LaGrange // divn_mulr; auto. Qed.

Lemma lcoset_inv : forall x y, lcoset h x y = rcoset h x^-1 y^-1.
Proof. by move=> x y; rewrite /rcoset -invg_mul groupV. Qed.

Lemma lcoset_refl : forall x, lcoset h x x.
Proof. by move=> x; rewrite /lcoset mulVg group1. Qed.

Lemma lcoset_sym : forall x y, lcoset h x y = lcoset h y x.
Proof. by move=> x y; rewrite !lcoset_inv rcoset_sym. Qed.

Lemma lcoset_trans : forall x y z, lcoset h x y -> lcoset h y z -> lcoset h x z.
Proof. move=> x y z; rewrite !lcoset_inv; exact: rcoset_trans. Qed.

Lemma connect_lcoset : connect (lcoset h) =2 lcoset h.
Proof.
move=> x y; apply/idP/idP; [move/connectP=> [p Hp <- {y}] | exact: connect1].
elim: p x Hp => [|y p IHp] x /=; first by rewrite lcoset_refl.
case/andP=> Hxy; move/IHp; exact: lcoset_trans.
Qed.

Lemma lcoset_csym : connect_sym (lcoset h).
Proof. by move=> x y; rewrite !connect_lcoset lcoset_sym. Qed.

Lemma lcoset1 : lcoset h 1 =1 h.
Proof. by move=> x; rewrite /lcoset invg1 mul1g. Qed.

Lemma card_lcoset : forall x, card (lcoset h x) = card h.
Proof.
move=> x; rewrite -(card_image (@invg_inj g)) -(card_rcoset x^-1).
apply: eq_card => y; rewrite -[y]invgK -lcoset_inv image_f //; exact: invg_inj.
Qed.

Lemma closed_lcoset : closed (lcoset h) k.
Proof.
by move=> x y; rewrite lcoset_inv; move/closed_rcoset; rewrite !groupV.
Qed.

Lemma lcoset_indexg : n_comp (lcoset h) k = indexg k.
Proof.
rewrite (adjunction_n_comp invg lcoset_csym rcoset_csym closed_lcoset).
  by apply: eq_n_comp_r => x; rewrite /preimage groupV.
apply: (strict_adjunction rcoset_csym closed_lcoset (@invg_inj _)).
  by apply/subsetP=> x _; rewrite -(invgK x) codom_f.
by move=> x y _; rewrite lcoset_inv !invgK.
Qed.

Lemma lcoset_root: forall x, lcoset h x (root (lcoset h) x).
move => x.
move: (connect_root (lcoset h) x).
by rewrite connect_lcoset.
Qed.

Lemma root_lcoset1: h (root (lcoset h) 1).
move: (connect_root (lcoset h) 1).
by rewrite connect_lcoset // /lcoset invg1 mul1g.
Qed.

Lemma root_lcosetd: forall a, h (a^-1 * root (lcoset h) a).
move => a.
move: (connect_root (lcoset h) a).
by rewrite connect_lcoset //.
Qed.


End LaGrange.

Section Eq.

Open Scope group_scope.

Variable g : finGroupType.

Lemma eq_lcoset : forall a1 a2 : set g, a1 =1 a2 -> lcoset a1 =2 lcoset a2.
Proof. move=> a1 a2 Da x y; exact: Da. Qed.

Lemma eq_rcoset : forall a1 a2 : set g, a1 =1 a2 -> rcoset a1 =2 rcoset a2.
Proof. move=> a1 a2 Da x y; exact: Da. Qed.

Lemma eq_prodg_l : forall a1 a2 b : set g, a1 =1 a2 -> prodg a1 b =1 prodg a2 b.
Proof.
move=> a1 a2 b; move/eq_rcoset=> Da x; congr negb; rewrite !(disjoint_sym b).
apply: eq_disjoint=> y; exact: Da.
Qed.

Lemma eq_prodg_r : forall a b1 b2 : set g, b1 =1 b2 -> prodg a b1 =1 prodg a b2.
Proof. move=> a b1 b2 Db x; congr negb; apply: eq_disjoint=> y; exact: Db. Qed.

Lemma eq_group: forall a b : set g, a =1 b -> group a = group b.
Proof.
move=> a b Da; rewrite /group Da (eq_subset_r Da); congr andb.
by apply: eq_subset=> x; rewrite (eq_prodg_l _ Da) (eq_prodg_r _ Da).
Qed.

End Eq.

(* Shows that given two sets h k, if hk=kh then hk is a subgroup *)
Section SubProd.

Open Scope group_scope.

Variable g : finGroupType.

Lemma prodgA : forall h1 h2 h3 : set g,
  prodg h1 (prodg h2 h3) =1 prodg (prodg h1 h2) h3.
Proof.
move=> h1 h2 h3 x; apply/prodgP/prodgP.
  case=> x1 x23 Hx1; case/prodgP=> x2 x3 Hx2 Hx3 ->{x23}; rewrite mulgA => Dx.
  by exists (x1 * x2) x3 => //; apply/prodgP; exists x1 x2.
case=> x12 x3; case/prodgP=> x1 x2 Hx1 Hx2 ->{x12} Hx3; rewrite -mulgA => Dx.
by exists x1 (x2 * x3) => //; apply/prodgP; exists x2 x3.
Qed.

Section GroupProdC.

Variables h k : set g.
Hypothesis Hh : group h.
Hypothesis Hk : group k.

Lemma prodC_group : prodg h k =1 prodg k h -> group (prodg h k).
Proof.
move=> Hhk; apply/andP; split.
  apply/prodgP; exists (1 : g) (1 : g); by [exact: group1 | rewrite mulg1].
have Hhkh : prodg (prodg h h) k =1 (prodg (prodg h k) h).
  move=> x; rewrite -!prodgA; exact: eq_prodg_r.
apply/subsetP=> x; rewrite prodgA -(eq_prodg_l _ Hhkh) -prodgA.
by rewrite (eq_prodg_l _ (prodgg Hh)) (eq_prodg_r _ (prodgg Hk)).
Qed.

Lemma group_prodC : group (prodg h k) -> prodg h k =1 prodg k h.
Proof.
move=> Hhk x; rewrite -{Hhk}(groupV Hhk).
by apply/idPn/idPn; case/prodgP=> y z;
  rewrite -(groupV Hh) -(groupV Hk) => Hy Hz Dx;
  apply/prodgP; exists z^-1 y^-1; rewrite // -invg_mul -Dx ?invgK.
Qed.

End GroupProdC.

Variables h k : set g.
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


(* group of permutations *)
Section PermGroup.

Variable d:finType.

Definition permType := eq_sig (fun g : fgraphType d d => uniq (tval (gval d d g))).

Canonical Structure perm_eqType := @EqType permType _ (@val_eqP _ _).

Canonical Structure perm_finType := @FinType perm_eqType _ (@sub_enumP _ _).

Definition fun_of_perm := fun u : permType => (val u : fgraphType _ _) : d -> d.

Coercion fun_of_perm : permType >-> Funclass.

Lemma perm_uniqP : forall g : fgraphType d d, reflect (injective g) (uniq (tval (gval d d g))).
Proof.
move=> g; apply: (iffP idP) => Hg.
  apply: can_inj (fun x => sub x (enum d) (index x (tval (gval _ _ g)))) _ => x.
  by rewrite {2}/fun_of_graph; unfold locked; case master_key; rewrite index_uniq ?sub_index ?tproof ?mem_enum /card // count_setA index_mem mem_enum.
by rewrite -[g]can_fun_of_graph /= uniq_maps // uniq_enum.
Qed.


Lemma eq_fun_of_perm: forall u v : permType, u =1 v -> u = v.
Proof.
move => u v Huv. apply: val_inj. 
rewrite -(can_fun_of_graph (val u)) -(can_fun_of_graph (val v)).
apply: gval_inj; apply: tval_inj; exact: (eq_maps Huv).
Qed.

Lemma perm_of_injP : forall f : d -> d, injective f -> uniq (tval (gval d d (graph_of_fun f))).
Proof.
move=> f Hf; apply/perm_uniqP.
by apply: eq_inj Hf _ => x; rewrite can_graph_of_fun.
Qed.

Definition perm_of_inj f (Hf : injective f) : permType :=
  EqSig (fun g : fgraphType d d => uniq (tval (gval d d g))) _ (perm_of_injP Hf).

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
by do 2!rewrite /fun_of_perm /= /comp can_graph_of_fun.
Qed.

Lemma perm_invP : forall x, perm_mul (perm_inv x) x = perm_unit.
Proof. 
move=> u; apply: eq_fun_of_perm => x.
do 3!rewrite /fun_of_perm /= /comp can_graph_of_fun. 
by rewrite finv_f; last exact: perm_inj.
Qed.

Lemma perm_mulP : 
  forall x y z, perm_mul x (perm_mul y z) = perm_mul (perm_mul x y) z.
Proof.
move=> u v w; apply: eq_fun_of_perm => x.
by do 4!rewrite /fun_of_perm /= /comp can_graph_of_fun. 
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
do 4!rewrite /fun_of_perm /= /comp can_graph_of_fun.
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
    rewrite {1}/fun_of_perm /= can_graph_of_fun eq_sym.
    by apply/idPn; move/Hu; rewrite Da.
  by rewrite {1}/fun_of_perm /= can_graph_of_fun set11.
case: (pickP a) => [x Hx Ha|]; last by move/eq_card0->. 
move: (Ha); rewrite (cardD1 x) Hx; set a' := setD1 a x; move/(IHn a')=> {IHn} Ha'.
pose h (u : permType) := EqPair (u x) (transperm x (u x) * u) : prod_finType _ _.
have Hh: injective h.
  move=> u1 u2 H; case: H (congr1 (@eq_pi2 _ _) H) => /= -> _; exact: mulg_injl.
rewrite /fact -/fact -(eqP Ha) -Ha' mulnI -card_prod -(card_image Hh).
apply: eq_card=> [[y v]]; apply/set0Pn/andP; rewrite /preimage /setI /=.
  case=> u; do 2!case/andP; do 2!move/eqP->; move=> Hu {y v}.
  split; first by rewrite perm_closed.
  apply/subsetP=> z. do 2!rewrite /mulg /= /fun_of_perm /= can_graph_of_fun /comp.
  rewrite /transpose -/(u x) -/(u z) (inj_eq (@perm_inj u)) /a' /setD1.
  case: (x =P z) => [<-|_]; first by case/eqP; case: eqP.
  case: (x =P u z) => [Dx | _]; first by rewrite -(perm_closed _ Hu) -Dx.
  exact: subsetP Hu z.
rewrite /= in v *; move=> [Hy Hv]; pose u : permType := transperm x y * v.
have Dy: y = u x.
  do 2!rewrite /u /= /fun_of_perm /= can_graph_of_fun /comp.
  rewrite -/(v x) (_ : v x = x) /transpose ?set11 //.
  by apply/eqP; apply/idPn; move/(subsetP Hv); rewrite /a'/ setD1 set11.
exists u; rewrite /h -Dy /u mulgA square_transperm mul1g set11.
apply/subsetP=> z; do 2!rewrite /fun_of_perm /= can_graph_of_fun /comp.
rewrite (inv_eq (transposeK x y)) /transpose -/(v z).
by do 2!case: (_ =P z) => [<- //| _]; move/(subsetP Hv); case/andP.
Qed.

End PermGroup.


Section Expn.

Open Scope group_scope.

Variable G: finGroupType.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the power function in  a multiplicative group        *)
(*                                                                     *)
(***********************************************************************)
Fixpoint gexpn (a: G) (n: nat) {struct n} : G :=
  if n is S n1 then a * (gexpn a n1) else 1.

Infix "^" := gexpn : group_scope.

Lemma gexpn0: forall a, a ^ 0 = 1.
Proof. by done. Qed.

Lemma gexpn1: forall a, a ^ 1%N = a.
Proof.
by move => a //=; rewrite mulg1.
Qed.

Lemma gexp1n: forall n, 1 ^ n = 1.
Proof.
by elim => [| n Rec] //=; rewrite mul1g.
Qed.

Lemma gexpnS: forall a n, a ^ (S n) = a * a ^ n.
Proof. by move => a. Qed.

Lemma gexpn_h: forall n a h, group h -> h a -> h (a ^ n).
Proof.
elim => [| n Rec] /= a h H1 Ha.
  by apply: group1.
apply: groupM => //.
exact: Rec.
Qed.

Lemma gexpn_add: forall a n m, a ^ n * a ^ m = a ^ (n + m).
Proof.
move => a n; elim: n a => [|n Rec] //= a m.
  by rewrite mul1g add0n.
by rewrite -mulgA Rec.
Qed.

Lemma gexpn_mul: forall a n m, (a ^ n) ^ m = a ^ (n * m).
Proof.
move => a n m; elim: m a n => [|m Rec] a n.
  by rewrite muln0 gexpn0.
rewrite gexpnS -addn1 muln_addr muln1 -gexpn_add.
by rewrite Rec !gexpn_add addnC.
Qed.


Lemma gexpnV: forall a n, (a ^-1) ^ n = (a ^ n)^-1.
Proof.
move => a; elim => [| n Rec] /=.
  by rewrite invg1.
by rewrite Rec -invg_mul -{2 3}(gexpn1 a) !gexpn_add addnC.
Qed.


Lemma gexpn_conjg: forall x y n,
  (y ^g x) ^ n  = (y ^ n)^g x.
Proof.
move => x y; elim => [| n Rec].
  by rewrite !gexpn0 conj1g.
by rewrite gexpnS Rec -conjg_mul -gexpnS.
Qed.

Lemma commute_expn: forall x y n,
  commute x y ->  commute x (y ^ n).
Proof.
move => x y n H; elim: n => [| n Rec].
  rewrite gexpn0; exact: commuteg1.
rewrite /commute gexpnS mulgA H -mulgA Rec; gsimpl.
Qed.

Lemma gexpnC: forall x y n, commute x y -> 
  (x * y) ^ n  = x ^ n * y ^ n.
Proof.
move => x y n H; elim: n => [| n Rec].
  by rewrite !gexpn0 mul1g.
rewrite !gexpnS Rec; gsimpl; congr mulg.
rewrite -!mulgA; congr mulg.
by rewrite commute_expn.
Qed.

Lemma subgrpE : forall H x n, group H ->
  H x -> H (x ^ n).
Proof.
move => H x n Hg Hx; elim: n => [|n Hrec].
  by rewrite gexpn0 group1.
by rewrite gexpnS groupM.
Qed.

End Expn.

Infix "^" := gexpn : group_scope.

Unset Implicit Arguments.
