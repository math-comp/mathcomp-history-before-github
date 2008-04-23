(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import div.
Require Import bigops.
Require Import finset.

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
Notation "[ 'finGroupType' 'of' t ]" :=
  (match {t : Type as finGroupType} as s
   return [type of FinGroupType for s] -> _ with
  | FinGroupType _ _ _ _ uP iP mP => fun k => k _ _ _ uP iP mP end
  (@FinGroupType t)) (at level 0, only parsing) : form_scope.

Definition mulg := nosimpl Group.mul.
Definition invg := nosimpl Group.inv.
Definition unitg := nosimpl Group.unit.
Prenex Implicits mulg invg.

Notation "x1 * x2" := (mulg x1 x2): group_scope.
Notation "1" := (unitg _) : group_scope.
Notation "x ^-1" := (invg x) (at level 2, left associativity,
  format "x ^-1") : group_scope.

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

Lemma mulgaa_1 : forall (a:elt), a * a = a -> a = 1.
move => a H.
have e:(a^-1 * a * a = a^-1 * a) by rewrite -{5}H mulgA.
by rewrite -(mulVg (a)) -e mulVg mul1g.
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

End Conjugation.


Implicit Arguments conjg_inj [elt].

Section Expn.

Open Scope group_scope.

Variable G: finGroupType.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the power function in  a multiplicative group        *)
(*                                                                     *)
(***********************************************************************)
Fixpoint gexpn (a: G) (n: nat) {struct n} : G :=
  if n is n1.+1 then a * (gexpn a n1) else 1.

Notation "a '**' p" := (gexpn a p) (at level 30).

Lemma gexpn0: forall a, a ** 0 = 1.
Proof. by done. Qed.

Lemma gexpn1: forall a, a ** 1%N = a.
Proof.
by move => a //=; rewrite mulg1.
Qed.

Lemma gexp1n: forall n, 1 ** n = 1.
Proof.
by elim => [| n Rec] //=; rewrite mul1g.
Qed.

Lemma gexpnS: forall a n, a ** (n.+1) = a * (a ** n).
Proof. by move => a. Qed.

Lemma gexpn_add: forall a n m, (a ** n) * (a ** m) = a ** (n + m).
Proof.
move => a n; elim: n a => [|n Rec] //= a m; first by rewrite mul1g add0n.
by rewrite -mulgA Rec.
Qed.

Lemma gexpn_mul: forall a n m, (a ** n) ** m = a ** (n * m).
Proof.
move => a n m; elim: m a n => [|m Rec] a n; first by rewrite muln0 gexpn0.
by rewrite gexpnS -addn1 muln_addr muln1 -gexpn_add Rec !gexpn_add addnC.
Qed.

Lemma gexpnV: forall a n, (a ^-1) ** n = (a ** n)^-1.
Proof.
move => a; elim => [| n Rec] /=; first by rewrite invg1.
by rewrite Rec -invg_mul -{2 3}(gexpn1 a) !gexpn_add addnC.
Qed.

Lemma gexpn_conjg: forall x y n,
  (y ^ x) ** n  = (y ** n)^ x.
Proof.
move => x y; elim => [| n Rec]; first by rewrite !gexpn0 conj1g.
by rewrite gexpnS Rec -conjg_mul -gexpnS.
Qed.

End Expn.

Notation "a '**' p" := (gexpn a p) (at level 50). 

Section SmulDef.

Open Scope group_scope.

Variable gT : finGroupType.
Notation Local sT := {set gT}.

(* Set-lifted group operations *)

Definition lcoset x (A : sT) := [set y | x^-1 * y \in A].
Definition rcoset (A : sT) x := [set y | y * x^-1 \in A].
Definition smulg_def (A B : sT) :=
  [set xy | ~~ [disjoint [set y | xy \in rcoset A y] & B]].
Definition gmulg_def (A B : sT) :=
  let C := smulg_def A B in if C == smulg_def B A then C else [set 1].
Definition sinvg (A : sT) := [set y | y^-1 \in A].
Definition sconjg (A : sT) x := [set y | y ^ x^-1 \in A].
Definition classg_def x (B : sT) := (fun z => x ^ z) @: B.
Definition sclassg_def (A B : sT) :=
  [set xy | ~~ [disjoint [set y | xy \in sconjg A y] & B]].

End SmulDef.

(* smulg_def confuses the coq term comparison function! *)
Definition smulg := locked smulg_def.
Definition gmulg := locked gmulg_def.
Definition classg := locked classg_def.
Definition sclassg := locked sclassg_def.

Notation "A ':*' x" := (rcoset A x) (at level 40) : group_scope.
Notation "x '*:' A" := (lcoset x A) (at level 40) : group_scope.
Notation "A ':*:' B" := (smulg A B) (at level 40) : group_scope.
Notation "A ':**:' B" := (gmulg A B) (at level 40) : group_scope.
Notation "A ':^-1'" := (sinvg A) (at level 30) : group_scope.
Notation "A ':^' x" := (sconjg A x) (at level 35) : group_scope.
Notation "x '^:' A" := (classg x A) (at level 35) : group_scope.
Notation "A ':^:' B" := (sclassg A B) (at level 35) : group_scope.

Section SmulProp.

Variable gT : finGroupType.
Notation sT := {set gT}.

Open Scope group_scope.

Notation Local "1" := (unitg gT).

Lemma lcosetE : forall y (A : sT) z, (z \in y *: A) = (y^-1 * z \in A).
Proof. by move=> *; rewrite setE. Qed.

Lemma rcosetE : forall (A : sT) y z, (z \in A :* y) = (z * y^-1 \in A).
Proof. by move=> *; rewrite setE. Qed.

Lemma lcosetP : forall y (A : sT) z,
  reflect (exists2 x, x \in A & z = y * x) (z \in y *: A)%G.
Proof.
move=> y A z; rewrite lcosetE.
apply: (iffP idP) => [Ax | [x Ax ->]]; first exists (y^-1 * z); gsimpl.
Qed.

Lemma rcosetP : forall (A : sT) y z,
  reflect (exists2 x, x \in A & z = x * y) (z \in A :* y)%G.
Proof.
move=> A y z; rewrite rcosetE.
apply: (iffP idP) => [Ax | [x Ax ->]]; first exists (z * y^-1); gsimpl.
Qed.

CoInductive mem_smulg (A B : sT) (z : gT) : Prop :=
  MemProdg x y of x \in A & y \in B & z = x * y.

Lemma smulgP : forall A B z, reflect (mem_smulg A B z) (z \in A :*: B)%G.
Proof.
unlock smulg => A B z; rewrite setE; apply: (iffP pred0Pn) => [[y]|[x y Ax Ay ->]].
  by case/andP; rewrite /= setE; case/rcosetP=> x; exists x y.
by exists y; rewrite /= setE Ay andbT; apply/rcosetP; exists x.
Qed.

Lemma smulg_subl : forall A B : sT, 1 \in B -> A \subset A :*: B.
Proof. by move=> A B B1; apply/subsetP=> x Ax; apply/smulgP; exists x 1; gsimpl. Qed.

Lemma smulg_subr : forall A B : sT, 1 \in A -> B \subset A :*: B.
Proof. by move=> A B A1; apply/subsetP=> x Bx; apply/smulgP; exists 1 x; gsimpl. Qed.

Lemma smulgA : forall A1 A2 A3 : sT, A1 :*: (A2 :*: A3) = A1 :*: A2 :*: A3.
Proof.
move=> A1 A2 A3; apply/setP=> x; apply/smulgP/smulgP=> [[x1 x23 Ax1] | [x12 x3]].
  case/smulgP=> x2 x3 Ax2 Ax3 ->{x23}; rewrite mulgA => Dx.
  by exists (x1 * x2) x3 => //; apply/smulgP; exists x1 x2.
case/smulgP=> x1 x2 Ax1 Ax2 ->{x12} Ax3; rewrite -mulgA => Dx.
by exists x1 (x2 * x3) => //; apply/smulgP; exists x2 x3.
Qed.

Lemma rcoset_smul : forall A (x : gT), A :* x = A :*: [set x].
Proof.
move=> A x; apply/setP => y; apply/rcosetP/smulgP => [[z]|[z x']].
  by exists z x; first 2 [exact: set11].
by rewrite setE => ?; move/eqP=> -> ->; exists z.
Qed.

Lemma lcoset_smul : forall A (x : gT), x *: A = [set x] :*: A.
Proof.
move=> A x; apply/setP => y; apply/lcosetP/smulgP => [[z]|[x' z]].
  by exists x z; first 1 [exact: set11].
by rewrite setE; move/eqP=> -> ? ->; exists z.
Qed.

Lemma rcoset1 : forall A : sT, A :* 1 = A.
Proof. by move=> A; apply/setP=> x; rewrite setE; gsimpl. Qed.

Lemma lcoset1 : forall A : sT, 1 *: A = A.
Proof. by move=> A; apply/setP=> x; rewrite setE; gsimpl. Qed.

Lemma smulg1 : forall A : sT, A :*: [set 1] = A.
Proof. by move=> A; rewrite -rcoset_smul rcoset1. Qed.

Lemma smul1g : forall A : sT, [set 1] :*: A = A.
Proof. by move=> A; rewrite -lcoset_smul lcoset1. Qed.

Lemma smulgs : forall A B1 B2 : sT,
  B1 \subset B2 -> A :*: B1 \subset A :*: B2.
Proof.
move=> A B1 B2; move/subsetP=> sB12; apply/subsetP=> x.
case/smulgP=> y z Ay Bz ->; apply/smulgP; exists y z; auto.
Qed.

Lemma smulsg : forall A1 A2 B : sT,
  A1 \subset A2 -> A1 :*: B \subset A2 :*: B.
Proof.
move=> A1 A2 B; move/subsetP=> sA12; apply/subsetP=> x.
case/smulgP=> y z Ay Bz ->; apply/smulgP; exists y z; auto.
Qed.

Lemma smulg_set1 : forall x y : gT, [set x] :*: [set y] = [set x * y].
Proof.
move=> x y; apply/setP => z; rewrite -rcoset_smul /= !setE.
exact: (canF_eq (mulgKv y)).
Qed.

Lemma gmulgC : forall A B : sT, A :**: B = B :**: A.
Proof. by unlock gmulg gmulg_def => A B; rewrite eq_sym; case: eqP. Qed.

Lemma gmulg1 : forall A, A :**: [set 1] = A.
Proof.
move=> A; move: (smulg1 A) (smul1g A); unlock gmulg smulg gmulg_def => -> ->.
by rewrite eqxx.
Qed.

Lemma gmul1g : forall A, [set 1] :**: A = A.
Proof. by move=> A; rewrite gmulgC gmulg1. Qed.

Lemma smulC_gmul : forall A B : sT, A :*: B = B :*: A -> A :*: B = A :**: B.
Proof. by unlock gmulg gmulg_def smulg => A B <-; rewrite eq_refl. Qed.

Lemma smul_gmul_sym : forall A B : sT, A :*: B = A :**: B -> B :*: A = A :**: B.
Proof.
unlock gmulg gmulg_def smulg => A B; case: eqP => // _; move/setP=> dA; apply/setP=> z.
rewrite [smulg_def]lock -/smulg setE in dA *.
apply/smulgP/eqP=> [[y x By Ax ->]|->] {z}.
  have: x * y \in A :*: B by apply/smulgP; exists x y.
  by rewrite dA setE -{2}(mulKg x y); move/eqP->; gsimpl.
move/(_ 1): dA; rewrite set11; case/smulgP=> x y Ax By Dxy.
by exists y x; rewrite // -(mulgK y x) -Dxy; gsimpl.
Qed.

Lemma sinvgK : involutive (@sinvg gT).
Proof. by move=> A; apply/setP => x; rewrite !setE invgK. Qed.

Lemma card_sinvg : forall A : sT, #|A :^-1| = #|A|.
Proof.
move=> A; have iinj := @invg_inj gT; rewrite -(card_image iinj).
by apply: eq_card => x; rewrite -[x]invgK [_ \in _]image_f //= setE.
Qed.

Lemma sinvgM : forall A B : sT, (A :*: B) :^-1 = (B :^-1) :*: (A :^-1).
Proof.
move=> A B; apply/setP=> xy; rewrite setE; apply/smulgP/smulgP; last first.
  by case=> y x; rewrite !setE => By Ax ->{xy}; exists x^-1 y^-1; gsimpl.
by rewrite -{2}(invgK xy); case=> x y Ax By ->{xy}; exists y^-1 x^-1; rewrite ?setE; gsimpl.
Qed.

Lemma sinvg_set1 : forall x : gT, [set x] :^-1 = [set x^-1].
Proof. move=> x; apply/setP=> y; rewrite !setE inv_eq //; exact: invgK. Qed.

Definition group_set (A : sT) := (1 \in A)%G && (A :*: A \subset A).

Lemma groupP : forall A : sT,
  reflect (1 \in A /\ forall x y, x \in A -> y \in A -> x * y \in A)
          (group_set A).
Proof.
move=> A; apply: (iffP andP) => [] [A1 AM]; split=> {A1}//.
  by move=> x y Ax Ay; apply: (subsetP AM); apply/smulgP; exists x y.
by apply/subsetP=> z; case/smulgP=> [x y Ax Ay ->]; auto.
Qed.

Structure group : Type := Group {
  set_of_group :> sT;
  set_of_groupP : group_set set_of_group
}.

Definition group_for of phant gT : predArgType := group.
Notation Local groupT := (group_for (Phant gT)).
Identity Coercion group_for_group : group_for >-> group.

Canonical Structure group_subType := SubType set_of_group group_rect vrefl.
Canonical Structure group_eqType := [subEqType for set_of_group].
Canonical Structure group_finType := Eval hnf in [subFinType of group_eqType].

(* No predType structure, as this would hide the group-to-set coercion *)
(* and thus spoint rewriting *)

Lemma set_of_group_inj : injective set_of_group. Proof. exact: val_inj. Qed.

Canonical Structure group_for_subType := Eval hnf in [subType of groupT].
Canonical Structure group_for_eqType := Eval hnf in [eqType of groupT].
Canonical Structure group_for_finType :=
  Eval hnf in [finType of group_for_eqType].

Lemma group_setA : group_set setA. Proof. exact/groupP. Qed.

Canonical Structure groupA := Group group_setA.

Section GroupProp.

Variable H : groupT.

Lemma valG : val H = H. Proof. by []. Qed.

Lemma group1 : 1 \in H. Proof. by case/groupP: (valP H). Qed.

Lemma groupM : forall x y, x \in H -> y \in H -> x * y \in H.
Proof. by case/groupP: (valP H). Qed.

Lemma groupVr : forall x, x \in H -> x^-1 \in H.
Proof.
move=> x Hx; rewrite -(finv_f (mulg_injl x) x^-1) mulgV /finv.
elim: _.-1 => [|n IHn] /=; [exact: group1 | exact: groupM].
Qed.

Lemma groupV : forall x, (x^-1 \in H) = (x \in H).
Proof.
move=> x; apply/idP/idP; first rewrite -{2}[x]invgK; exact: groupVr.
Qed.

Lemma groupMl : forall x y, x \in H -> (x * y \in H) = (y \in H).
Proof.
move=> x y Hx; apply/idP/idP=> Hy; last exact: groupM.
rewrite -(mulKg x y); exact: groupM (groupVr _) _.
Qed.

Lemma groupMr : forall x y, (x \in H) -> (y * x \in H) = (y \in H).
Proof.
move=> x y Hx; apply/idP/idP=> Hy; last exact: groupM.
rewrite -(mulgK x y); exact: groupM (groupVr _).
Qed.

Lemma groupE : forall x n, (x \in H) -> (x ** n \in H).
Proof.
move => x n Hx; elim: n => /= [|n Hrec]; first exact: group1.
by rewrite groupM.
Qed.

Lemma groupVl : forall x,  (x^-1 \in H) ->  (x \in H).
Proof. by move=> x; rewrite groupV. Qed.

Lemma groupJ : forall x y, (x \in H) -> (y \in H) -> (x ^ y \in H).
Proof. by move=> *; rewrite /conjg !groupM ?groupV. Qed.

Lemma groupJr : forall x y, y \in H -> (x ^ y \in H) = (x \in H).
Proof. by move=> *; rewrite /conjg groupMr ?groupMl ?groupV. Qed.

Notation Local sgT := {x | x \in H}.
Definition subgroup_unit : sgT := Sub 1 group1.
Definition subgroup_inv (u : sgT) : sgT := Sub _^-1 (groupVr (valP u)).
Definition subgroup_mul (u v : sgT) : sgT :=
  Sub(_ * _) (groupM (valP u) (valP v)).
Lemma subgroup_unitP : left_unit subgroup_unit subgroup_mul.
Proof. move=> u; apply: val_inj; exact: mul1g. Qed.
Lemma subgroup_invP : left_inverse subgroup_unit subgroup_inv subgroup_mul.
Proof. move=> u; apply: val_inj; exact: mulVg. Qed.
Lemma subgroup_mulP : associative subgroup_mul.
Proof. move=> u v w; apply: val_inj; exact: mulgA. Qed.

Canonical Structure subFinGroupType :=
  FinGroupType subgroup_unitP subgroup_invP subgroup_mulP.

Lemma pos_card_group : 0 < #|H|.
Proof. rewrite lt0n; apply/pred0Pn; exists (1 : gT); exact: group1. Qed.

Canonical Structure pos_nat_card_group := PosNat pos_card_group.

Lemma smulgg : H :*: H = H.
Proof.
by case/andP: (set_of_groupP H) => H1 mH; apply/setP; apply/subset_eqP; rewrite mH smulg_subr.
Qed.

Lemma sinvG : H :^-1 = H. Proof. by apply/setP=> x; rewrite setE groupV. Qed.

End GroupProp.

Hint Resolve group1 groupM groupVr.

Lemma sinvMG : forall H K : group, (H :*: K) :^-1 = K :*: H.
Proof. by move=> H K; rewrite sinvgM !sinvG. Qed.

Lemma group_set_unit : group_set [set 1].
Proof. by rewrite /group_set smulg_set1 mulg1 subset_refl set11. Qed.

Canonical Structure unit_set_group := Group group_set_unit.

Lemma group_set_gmulG : forall H K : groupT, group_set (H :**: K).
Proof.
move=> H K; case cHK: (H :*: K == K :*: H); last first.
  by move: cHK; unlock gmulg gmulg_def smulg => ->; exact group_set_unit.
move/eqP: cHK => cHK; rewrite -smulC_gmul //.
apply/andP; split; first by apply/smulgP; exists 1 1; gsimpl; exact: group1.
by rewrite smulgA -(smulgA H) -cHK smulgA smulgg -smulgA smulgg subset_refl.
Qed.

Canonical Structure gmulG_group H K := Group (group_set_gmulG H K).

Lemma group_gmul : forall G H K : groupT,
  G = H :*: K :> set _ -> H :*: K = H :**: K.
Proof. by move=> G H K dG; apply: smulC_gmul; rewrite -dG -sinvG dG sinvgM !sinvG. Qed.

Lemma group_gmul_eq : forall G H K : groupT, G = H :*: K :> set _ ->
  G = {H :**: K as group}.
Proof. by move=> G H K dG; apply: val_inj; rewrite /= dG (group_gmul dG). Qed.

End SmulProp.

Hint Resolve group1 groupM groupVr pos_card_group.

Section Commutation.

Variable elt: finGroupType.

Open Scope group_scope.

Definition commute (x y : elt) := x * y == y * x.

Lemma commute_sym : forall x y, commute x y -> commute y x.
Proof. by move => x y; rewrite /commute  eq_sym. Qed.

Lemma conjg_fpP : forall x y : elt, reflect (commute x y) (conjg_fp y x).
Proof.
move=> *; rewrite /conjg_fp conjgE -mulgA (canF_eq (mulKgv _)); exact: idP.
Qed.

Lemma conjg_fp_sym : forall x y : elt, conjg_fp x y = conjg_fp y x.
Proof. move=> x y; apply/conjg_fpP/conjg_fpP; exact:commute_sym. Qed.

Lemma commute_expn: forall x y n,
  commute x y ->  commute x (y ** n).
Proof.
rewrite /commute; move => x y n H; elim: n => /= [| n Rec]; gsimpl. 
by rewrite (eqP H) -mulgA (eqP Rec); gsimpl.
Qed.

Lemma gexpnC: forall x y n, commute x y ->
  (x * y) ** n  = (x ** n) * (y ** n).
Proof.
rewrite /commute; move => x y n H; elim: n => /= [| n Rec]; gsimpl.
rewrite Rec. gsimpl. congr mulg. rewrite -!mulgA; congr mulg.
apply/eqP.
suff: (commute y (x**n)) by rewrite /commute.
by apply: commute_expn; rewrite /commute eq_sym.
Qed.

Definition com (A B : {set elt}) :=
  forallb x, forallb y, (x \in A) && (y \in B) ==> commute x y.

Lemma comP :forall A B : {set elt},
  reflect {in A & B, commutative mulg} (com A B).
Proof.
move=> A B; apply: (iffP forallP) => cAB x => [y Ax By|].
  by apply/eqP; have:= (forallP (cAB x) y); rewrite Ax By.
by apply/forallP=> y; apply/implyP; case/andP=> Ax By; apply/eqP; exact: cAB.
Qed.

Lemma sconjg_com : forall (H: {set elt}) (x:elt), 
  (forall y, y \in H -> commute y x) -> H :^x = H.
Proof.
move=> H x Hcom; apply/setP.
by apply/subset_eqP; apply/andP; split; apply/subsetP=> y; 
rewrite /sconjg setE; move=> Hin; move: (Hin); move/Hcom; move/conjg_fpP; 
move/eqP; [rewrite conjgKv=>->|move=><-; rewrite conjgK].
Qed.

Lemma com_smulgC : forall (H1 H2 : group elt),
  com H1 H2 -> H1 :*: H2 == H2 :*: H1.
Proof.
move=> H1 H2; move/comP=> Hcom.
by apply/eqP; apply/setP=> x; apply/smulgP/smulgP; case=> [x1 x2 Hx1 Hx2]; 
[move: Hcom =>->|move: Hcom =><-]; try by move/MemProdg; apply.
Qed.

Lemma com_gmulg_smulg : forall (H1 H2: group elt),
  com H1 H2 -> H1 :*: H2 == H1 :**: H2.
Proof.
move=> H1 H2; move/com_smulgC; move/eqP; move/smulC_gmul=>->; exact:eqxx.
Qed.

End Commutation.

Implicit Arguments conjg_fpP [elt x y].
Prenex Implicits conjg_fpP.

Notation "{ 'group' gT }" := (group_for (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.

Notation "[ 'group' 'of' G ]" :=
  (match {G%SET as group _} as s return [type of @Group _ for s] -> _ with
  | Group _ gP => fun k => k gP end
  (@Group _ G)) (at level 0, only parsing) : form_scope.

Section ConjugationSet.

Open Scope group_scope.

Variable gT : finGroupType.
Notation sT := {set gT}.
Variable A : sT.

Theorem sconjgE : forall (B : sT) x y, (y \in B :^ x^-1) = (y ^ x \in B).
Proof. by move=> *; rewrite setE invgK. Qed.

Theorem sconj1g : A :^ 1 = A.
Proof. by apply/setP => x; rewrite setE invg1 conjg1. Qed.

Lemma sconjgM : forall x y, A :^ (x * y) = (A :^ x) :^ y.
Proof. move=> x y; apply/setP => z; rewrite !setE /conjg; gsimpl. Qed.

Theorem sconjg_conj : forall (B : sT) x y, (y ^ x \in B :^ x) = (y \in B).
Proof. by move=> B x y; rewrite setE conjgK. Qed.

Lemma sconjMg : forall B x, (A :*: B) :^ x = (A :^ x) :*: (B :^ x).
Proof.
move=> B x; apply/setP=> yz; rewrite !setE; apply/smulgP/smulgP=> [] [y z Ay Bz].
  by rewrite -{2}(conjgKv x yz) => ->; exists (y ^ x) (z ^ x); rewrite ?sconjg_conj ?conjg_mul.
by move->; exists (y ^ x^-1) (z ^ x^-1); rewrite -?sconjgE ?conjg_mul ?invgK.
Qed.

Lemma sconj_set1 : forall x y : gT, [set x] :^ y = [set x ^ y].
Proof.
move=> x y; apply/setP => z; rewrite !setE; exact: (canF_eq (conjgKv y)).
Qed.

Theorem sconjg_imset : forall x, A :^ x = (conjg x) @: A.
Proof.
move=> x; apply/setP=> y; unlock imset; rewrite !setE. 
rewrite -{2}(conjgKv x y) image_f ?setE //; exact: conjg_inj.
Qed.

Lemma sconjg_coset : forall x, A :^ x = x^-1 *: A :* x.
Proof. by move=> x; apply/setP =>y; rewrite !setE mulgA. Qed.

Theorem card_sconjg : forall x, #|A :^ x| = #|A|.
Proof.
move=> x; rewrite (sconjg_imset x); apply: card_imset; exact: conjg_inj.
Qed.

Variable H : group gT.

Theorem sconjg1 : forall x, 1 \in H :^ x.
Proof. by move=> x; rewrite setE conj1g group1. Qed.

Theorem sconjg_inv : forall x y, y \in H :^ x -> y^-1 \in H :^ x.
Proof. move=> x y; rewrite !setE conjg_invg; exact: groupVr. Qed.

Theorem group_set_sconjg : forall x, group_set (H :^ x).
Proof. 
move=> x; rewrite /group_set sconjg1; apply/subsetP=> y.
case/smulgP=> x1 x2 Hx1 Hx2 -> {z}.
rewrite !setE conjg_mul in Hx1 Hx2 *; exact: groupM. 
Qed.
Canonical Structure sconjg_group x := Group (group_set_sconjg x).

End ConjugationSet.

Section LaGrange.

Variables (gT : finGroupType) (H K : {group gT}).
Notation sT := {set gT}.

Hypothesis subset_HK : H \subset K.
Let sHK := subsetP subset_HK.

Open Scope group_scope.

Lemma rcoset_refl : forall x, x \in H :* x.
Proof. by move=> x; rewrite /rcoset setE mulgV group1. Qed.

Lemma rcoset_sym : forall x y, (y \in H :* x) = (x \in H :* y).
Proof. by move=> *; rewrite !setE -groupV; gsimpl. Qed.

Lemma rcoset_trans1 : forall x y, (y \in H :* x) -> H :* x = H :* y.
Proof.
move=> x y Hxy; apply/setP=> u; rewrite !setE in Hxy *.
by rewrite -(groupMr (u * y^-1) Hxy); gsimpl.
Qed.

Lemma rcoset_trans : forall x y z,
  y \in H :* x -> z \in H :* y -> z \in H :* x.
Proof. by move=> x y z; move/rcoset_trans1->. Qed.

Lemma rcoset_trans1r : forall x y, 
  y \in H :* x -> forall z, (x \in H :* z) = (y \in H :* z).
Proof. by move=> x y Hxy z; rewrite !(rcoset_sym z) (rcoset_trans1 Hxy). Qed.

Lemma rcoset_id : forall x, x \in H -> H :* x = H.
Proof. by move=> x Hx; apply/setP => y; rewrite !setE groupMr; auto. Qed.

Lemma card_rcoset : forall x, #|H :* x| = #|H|.
Proof.
move=> x; have injx := mulg_injr x; rewrite -(card_image injx (mem H)).
by apply: eq_card => y; rewrite setE -{2}(mulgKv x y) [_ * x \in _]image_f.
Qed.

Definition rcosets (K : sT) := rcoset H @: K.

Definition indexg (K : sT) := #|rcosets K|.

Definition repr (A : sT) := if [pick x \in A] is Some x then x else 1.

Lemma mem_repr : forall x (A : sT), x \in A -> repr A \in A.
Proof.
by rewrite /repr => x A; case: pickP => [//|A0]; rewrite [x \in A]A0.
Qed.

CoInductive rcoset_repr_spec x : gT -> Type :=
  RcosetReprSpec y : y \in H -> rcoset_repr_spec x (y * x).

Lemma repr_rcosetP : forall x, rcoset_repr_spec x (repr (H :* x)).
Proof.
move=> x; rewrite -[repr _](mulgKv x); split; rewrite -rcosetE.
exact: mem_repr (rcoset_refl x).
Qed.

Theorem rcoset_repr: forall x, H :* (repr (H:* x)) = H:* x.
Proof.
move => x; apply: rcoset_trans1.
case: repr_rcosetP => y Hy.
apply/rcosetP; exists (y^-1); gsimpl.
exact: groupVr.
Qed.

Theorem LaGrange : (#|H| * indexg K)%N = #|K|.
Proof.
pose f x := (x * (repr (H :* x))^-1, H :* x).
have inj_f: injective f.
  rewrite /f [rcoset]lock => x1 x2 [Dy DHx]; move: Dy; rewrite {}DHx; exact: mulg_injr.
rewrite -cardX -{inj_f}(card_imset _ inj_f); apply: eq_card => [] [y A].
apply/andP/imsetP=> /= [[Hy]|[x Kx [-> ->]]]; last first.
  split; last by apply/imsetP; exists x.
  case: repr_rcosetP => z Hz; gsimpl; exact: groupVr.
move/imsetP=> [x Kx ->{A}]; case Dz: (repr _) / (repr_rcosetP x) => [z Hz].
exists (y * z * x); first by rewrite groupMr // sHK // groupM.
have Hxyx: y * z * x \in H :* x by rewrite setE; gsimpl; exact: groupM.
by rewrite /f -(rcoset_trans1 Hxyx) Dz; gsimpl.
Qed.

Lemma group_dvdn : #|H| %| #|K|.
Proof. by apply/dvdnP; exists (indexg K); rewrite mulnC LaGrange. Qed.

Lemma group_divn : #|K| %/ #|H| = indexg K.
Proof. by rewrite -LaGrange // divn_mulr; auto. Qed.

Lemma lcoset_inv : forall x y, (y \in x *: H) = (y^-1 \in H :* x^-1).
Proof. by move=> x y; rewrite !setE -invg_mul groupV. Qed.

Lemma lcoset_refl : forall x, x \in x *: H.
Proof. by move=> x; rewrite setE mulVg group1. Qed.

Lemma lcoset_sym : forall x y, (y \in x *: H) = (x \in y *: H).
Proof. by move=> x y; rewrite !lcoset_inv rcoset_sym. Qed.

Lemma lcoset_trans : forall x y z,
  (y \in x *: H) -> (z \in y *: H) -> (z \in x *: H).
Proof. move=> x y z; rewrite !lcoset_inv; exact: rcoset_trans. Qed.

Lemma lcoset_trans1 : forall x y, (y \in x *: H) -> x *: H = y *: H.
Proof.
move=> x y Hxy; apply/setP => u; rewrite setE in Hxy.
by rewrite !setE -{1}(mulKgv y u) mulgA groupMl.
Qed.

Lemma lcoset_trans1r : forall x y, 
  (y \in x *: H) -> forall z, (x \in z *: H) = (y \in z *: H).
Proof.
by move=> x y Hxy z; rewrite !(lcoset_sym z) (lcoset_trans1 Hxy).
Qed.

Lemma sinvg_lcoset : forall x, (x *: H) :^-1 = H :* x^-1.
Proof. by move=> x; rewrite lcoset_smul rcoset_smul sinvgM sinvG sinvg_set1. Qed.

Lemma card_lcoset : forall x, #|x *: H| = #|H|.
Proof. by move=> x; rewrite -card_sinvg sinvg_lcoset card_rcoset. Qed.

Definition lcosets (K : sT) := (fun x => lcoset x H) @: K.


Lemma card_lcosets : #|lcosets K| = indexg K.
Proof.
rewrite -(card_imset _ (inv_inj (@sinvgK gT))); apply: eq_card => A.
apply/imsetP/imsetP=> [[B dB ->{A}] | [x Hx ->{A}]].
  case/imsetP: dB => x Kx ->{B}.
  exists x^-1; [exact: groupVr | exact: sinvg_lcoset].
exists (x^-1 *: H); last by rewrite sinvg_lcoset invgK.
by apply/imsetP; exists x^-1; first exact: groupVr.
Qed.

End LaGrange.

Prenex Implicits repr.

Section GroupInter.

Open Scope group_scope.

Variable gT : finGroupType.
Notation sT := {set gT}.

Section GroupSmulSub.

Variables (H : group gT) (A : sT).
Hypothesis subAH : A \subset H.
Let sAH := subsetP subAH.

Lemma smulsG : forall x, x \in A -> A :*: H = H.
Proof.
move=> x Ax; apply/setP; apply/subset_eqP; rewrite -{2}smulgg smulsg //.
apply/subsetP=> y Ky; apply/smulgP; exists x (x^-1 * y); gsimpl.
by rewrite groupMl // groupV; auto.
Qed.

Lemma smulGs : forall x, x \in A -> H :*: A = H.
Proof.
move=> x Ax; apply/setP; apply/subset_eqP; rewrite -{2}smulgg smulgs //.
apply/subsetP=> y Ky; apply/smulgP; exists (y * x^-1) x; gsimpl.
by rewrite groupMr // groupV; auto.
Qed.

Definition smulsG1 := @smulsG 1.
Definition smulGs1 := @smulGs 1.

End GroupSmulSub.


Section GroupSmulSubGroup.

Variables H K : group gT.

Hypothesis subHK : H \subset K.

Definition smulSG := smulsG subHK (group1 H).
Definition smulGS := smulGs subHK (group1 H).

End GroupSmulSubGroup.

Variables H K : {group gT}.

Lemma group_setI : group_set (H :&: K).
Proof.
apply/groupP; split=> [|x y]; rewrite !setE ?group1 //.
by move/andP=> [Hx Kx]; rewrite !groupMl.
Qed.

Canonical Structure setI_group := Group group_setI.

Lemma card_smulg : (#|H :*: K| * #|H :&: K| = #|H| * #|K|)%N.
Proof.
rewrite -(LaGrange (subsetIr H K)) mulnCA mulnC /=; congr (_ * _)%N.
rewrite -cardX; set tup := predX _ _.
pose f (u : {xHy | tup xHy}) := let: (x, Hy) := val u in x * repr Hy.
have injf: injective f.
  rewrite /f => [] [[x1 A1] dom1] [[x2 A2] dom2] /= Ef; apply: val_inj => /=.
  case/andP: dom1 (Ef) => /= Hx1; case/imsetP=> y1 Ky1 dA1.
  case/andP: dom2 => /= Hx2; case/imsetP=> y2 Ky2 dA2.
  suff ->: A1 = A2 by move/mulg_injr->.
  rewrite {A1}dA1 {A2}dA2 in Ef *; have kEf := canRL (mulKg _).
  apply: rcoset_trans1; rewrite // !setE andbC groupM ?groupV //=.
  case: repr_rcosetP Ef => z1; case/setIP=> Hz1 _; rewrite mulgA; move/kEf->.
  by case: repr_rcosetP => z2; case/setIP=> Hz2 _; gsimpl; rewrite !groupM ?groupV.
rewrite -(card_sig tup) -(card_codom injf) {injf}/f; apply: eq_card => z.
apply/smulgP/pred0Pn=> [[x y Hx Ky ->{z}]|]; last first.
  case=> [[[x A]]] /=; case/andP=> /= Hx; case/imsetP=> y Ky -> {A}.
  move/eqP=> <-{z}; case: repr_rcosetP => z /= HKz.
  by exists x (z * y); rewrite // groupMr //; case/setIP: HKz.
case Dz: (repr _) / (repr_rcosetP {H :&: K as group _} y) => /= [z HKz].
case/setIP: HKz => Hz Kz.
have Tu: tup (x * z^-1, (H :&: K) :* y).
  by rewrite /= groupMl ?groupVr //; apply/imsetP; exists y.
by exists (exist [eta tup] _ Tu); apply/eqP; rewrite /= Dz; gsimpl.
Qed.

Lemma card_smulg_coprime :
  coprime #|H| #|K| -> (#|H :*: K| = #|H| * #|K|)%N.
Proof.
move=> Hcop; move: card_smulg.
move: (group_dvdn (subsetIl H K)) =>/= Hdiv1.
move: (group_dvdn (subsetIr H K)) =>/= Hdiv2.
move: (dvdn_gcd Hdiv1 Hdiv2); move: Hcop; rewrite /coprime; move/eqP=>->.
rewrite dvdn1; move/eqP=>->; rewrite muln1; apply.
Qed.

Definition trivg (A : sT) := A \subset [set 1].

Lemma trivgP : forall G : {group gT}, reflect (G = [set 1] :> set _) (trivg G).
Proof.
move=> G; apply: (iffP idP) => [tG | ->]; last exact: subset_refl.
by apply/setP; apply/subset_eqP; rewrite andbC subset_set1 group1.
Qed.

Definition disjointg := trivg (H :&: K).

Lemma disjointgP : reflect (H :&: K = [set 1]) disjointg.
Proof. exact: trivgP. Qed.

Lemma disjointg_card : disjointg = (#|H :&: K| == 1)%N.
Proof.
apply/disjointgP/eqP=> [->|cHK]; first by rewrite cards1.
symmetry; apply/setP; apply/subset_cardP; first by rewrite cards1.
apply/subsetP=> x; rewrite setE; move/eqP->; exact: group1.
Qed.

(*Lemma group_modularity : forall G, subgroup G K ->*)
Lemma group_modularity : forall G : {group gT},
  G \subset K -> G :*: (H :&: K) = G :*: H :&: K.
Proof.
move=> G; move/subsetP=> sGK; apply/setP => x.
apply/smulgP/idP=> [[y z Gy]|]; rewrite setE; case/andP.
  move=> Hz Kz -> {x}; rewrite setE andbC groupMr // sGK //.
  by apply/smulgP; exists y z.
move/smulgP=> [y z Gy Hz -> {x}] Kyz.
by exists y z => //; rewrite setE Hz; rewrite groupMl // sGK in Kyz.
Qed.

Lemma disjoint_card_smulg :
  disjointg -> (#|H :*: K| = #|H| * #|K|)%N.
Proof. by rewrite disjointg_card => HK1; rewrite -card_smulg (eqP HK1) muln1. Qed.

End GroupInter.

Section Normalizer.

Open Scope group_scope.

Variable gT : finGroupType.
Notation sT := {set gT}.

Section NormSet.

Variable A : sT.

Definition normaliser := [set x | A :^ x \subset A].

Theorem norm_sconjg : forall x, x \in normaliser -> A :^ x = A.
Proof. 
by move=> x Ax; apply/setP; apply/subset_cardP; [rewrite card_sconjg | rewrite setE in Ax]. 
Qed.


Theorem group_set_normaliser : group_set normaliser.
Proof.
apply/groupP; split=> [|x y Nx Ny]; first by rewrite setE sconj1g subset_refl.
by rewrite setE; apply/subsetP => z; rewrite sconjgM !norm_sconjg.
Qed.

Canonical Structure group_normaliser := Group group_set_normaliser.

Definition normalized (B : sT) := B \subset normaliser.
 
Lemma norm_smulC : forall B, normalized B -> A :*: B = B :*: A.
Proof.
move=> B; move/subsetP=> nB; apply/setP => u.
apply/smulgP/smulgP=> [[x y Ax By] | [y x By Ax]] -> {u}; have dAy := norm_sconjg (nB _ By).
- by exists y (x ^ y); last rewrite /conjg; gsimpl; rewrite -dAy setE conjgK.
by exists (x ^ y^-1) y; last rewrite /conjg; gsimpl; rewrite -sconjgE invgK dAy.
Qed.

Lemma norm_gmulr : forall B, normalized B -> A :*: B = A :**: B.
Proof. by move=> B; move/norm_smulC; exact: smulC_gmul. Qed.

Lemma norm_gmull : forall B, normalized B -> B :*: A = A :**: B.
Proof. by move=> B; move/norm_smulC=> dBA; rewrite -dBA; exact: smulC_gmul. Qed.


End NormSet.

Variable H : {group gT}.
Notation N := (normaliser H).

Theorem norm_refl : H \subset N.
Proof.
apply/subsetP=> x Hx; rewrite setE; apply/subsetP => y.
by rewrite setE /conjg invgK groupMr ?groupMl ?groupV.
Qed.

Lemma norm_rcoset : forall x, x \in N -> H :* x \subset N.
Proof.
move=> x Nx; rewrite rcoset_smul; rewrite -[normaliser _]smulgg /=.
by apply: subset_trans (smulsg _ norm_refl); apply: smulgs; rewrite subset_set1.
Qed.

End Normalizer.

Open Scope group_scope.

Lemma norm_rlcoset : forall (gT : finGroupType) (H : {group gT}) x,
  x \in normaliser H -> H :* x = x *: H.
Proof.
move=> gT H x; rewrite rcoset_smul lcoset_smul -subset_set1; exact: norm_smulC.
Qed.


Lemma rcoset_mul : forall (gT : finGroupType) (H : {group gT}) x y, 
  x \in normaliser H  -> (H :* x) :*: (H :* y) = H :* (x * y).
Proof.
move=> gT H x y Nx.
rewrite !rcoset_smul -smulgA (smulgA _ H) -lcoset_smul -norm_rlcoset //.
by rewrite rcoset_smul -smulgA smulg_set1 smulgA smulgg.
Qed.


Section Maximal.

Variable gT : finGroupType.
Notation sT := {set gT}.
Variables H G : sT.

Definition  maximal :=
  (H \subset G) &&
  (forallb K : {group gT},
    (H \subset K) && (K \subset G) ==> (H == K) || (K == G :> sT)).

Theorem maximalP:
 reflect
 (H \subset G  /\ 
   forall K : {group gT}, H \subset K -> K \subset G ->
                  H = K \/ K = G :> sT) 
 maximal.
Proof.
(apply: (iffP andP); case=> sHG maxH; split) => // [K sHK sKG|].
  by have:= (forallP maxH K); rewrite sHK sKG; case/orP; move/eqP; auto.
apply/forallP => K; apply/implyP; case/andP=> sHK sKG.
by case (maxH K) => // ->; rewrite eqxx ?orbT.
Qed.

End Maximal.

Section GeneratedGroup.

Variable gT : finGroupType.
Variable S : {set gT}.

Definition generated := \bigcap_(G : {group gT} | S \subset G) G.

Lemma group_generated : group_set generated.
Proof.
apply: (@big_prop _ [eta @group_set _]); first exact: group_setA.
  move=> G H gG gH; exact: group_setI (Group gG) (Group gH).
move=> G _; exact: (valP G).
Qed.

Canonical Structure generated_group := Group group_generated.

Lemma subset_generated : S \subset generated.
Proof. by apply/bigcap_inP. Qed.

Lemma generatedP : forall x,
  reflect (forall G : {group gT}, S \subset G -> x \in G) (x \in generated).
Proof. exact: bigcapP. Qed.

Lemma subset_gen_stable : forall G : {group gT},
  (S \subset G) = (generated \subset G).
Proof.
move=> G; apply/idP/idP; first by move=> SG; apply/subsetP=> x; move/generatedP; apply.
exact: (subset_trans subset_generated).
Qed.

End GeneratedGroup.

Notation "<< X >>"  := (generated X)
  (at level 0, format "<< X >>") : group_scope.

Section GeneratedProps.

Variable gT:finGroupType.

Lemma genn : forall S: {set gT}, << << S >> >> = << S >>.
Proof.
move=> S; apply/setP; apply/subset_eqP; apply/andP; split.
by apply/bigcap_inP=> i Hi; repeat apply: bigcap_inf.
by apply/bigcap_inP=>i Hi.
Qed.

Variable (x : gT)(A B : {set gT}).

Lemma gen_sub : forall X Y : {set gT},
  X \subset Y -> << X >> \subset << Y >>.
Proof.
by move=> X Y XY; rewrite -subset_gen_stable;
apply: (subset_trans _ (subset_generated Y)).
Qed.

Lemma eq_gen : forall X Y : {set gT}, X =i Y -> << X >> = << Y >>.
Proof.
move=> X Y; move/subset_eqP; case/andP => XY YX; apply/setP; 
apply/subset_eqP; apply/andP; split; exact: gen_sub.
Qed.

Lemma eq_group_gen: forall G : group gT, << G >> = G.
Proof.
move=> G; apply/setP; apply/subset_eqP; apply/andP.
split; last by apply: subset_generated.
rewrite -subset_gen_stable; apply: subset_refl. 
Qed.

Lemma genD : forall X Y : {set gT},
   X \subset << X :\: Y >> -> << X :\: Y >> = << X >>.
Proof.
move=> X Y Hsub; apply/setP; apply/subset_eqP; apply/andP.
split; last by rewrite -subset_gen_stable.
by apply: gen_sub; apply/subsetP => y; rewrite setE; case/andP.
Qed.

Lemma genD1 : x \in << A :\ x >> -> << A :\ x >> = << A >>.
Proof.
move=> Axx; apply/setP; apply/subset_eqP; apply/andP.
split; first by apply: gen_sub; apply/subsetP => y; rewrite setE; case/andP.
rewrite -subset_gen_stable; apply/subsetP => y Ay.
case: (y =P x) => [-> //|]; move/eqP=> nyx.
by apply: (subsetP (subset_generated _)); rewrite setE nyx.
Qed.

Lemma gen_pred0 : <<set0 : {set gT}>> = [set 1].
Proof.
apply/setP=> u; apply/generatedP/set1P; last by move=> -> G _; apply: group1.
move/(_ [group of [set 1]]) => /= abs; apply/set1P; apply: abs.
by apply/subsetP=> v; rewrite setE.
Qed.

Lemma genDU : forall X : {set gT},
  A \subset X -> <<X :\: A>> = <<B>> -> <<A :|: B>> = <<X>>. 
Proof.
move=> X AX XAB; apply/setP; apply/subset_eqP; apply/andP; split.
  rewrite -subset_gen_stable; apply/subsetP => y /=; case/setUP.
    move/(subsetP AX); exact: subsetP (subset_generated X) y.
  move/(subsetP (subset_generated B) y); rewrite -XAB.
  by apply: subsetP y; apply: gen_sub; rewrite subsetDl.
rewrite -subset_gen_stable; apply/subsetP => y Xy.
case Ay: (y \in A).
  by apply: (subsetP (subset_generated _)); rewrite setE Ay.
have:= gen_sub (subsetUr A B); move/subsetP; apply; rewrite -XAB.
by apply: (subsetP (subset_generated _)); rewrite setE Ay Xy.
Qed.

End GeneratedProps.

Section FrattiniDefs.

Variable gT : finGroupType.

Variable G : {group gT}.

Lemma maximal_existence : forall H : {group gT}, H \subset G -> 
  H = G \/ exists K : {group gT}, [/\ maximal K G , H \subset K & K != G].
Proof.
move=> H sHG; elim: {2}#|G| H sHG (leq_addr #|H| #|G|) => [|n IHn] H sHG.
  rewrite add0n leq_eqVlt ltnNge subset_leq_card // orbF; move/eqP=> eqHG.
  by left; apply: val_inj; apply/setP; exact/subset_cardP.
rewrite addSnnS => leGnH; case maxH: (maximal H G).
  by case: (H =P G); [left | move/eqP=> nHG; right; exists H].
move/idPn: maxH; rewrite negb_and sHG; case/existsP=> L.
rewrite negb_imply -andbA negb_orb; case/and4P=> sHL sLG nHL nLG; right.
case: {IHn}(IHn L sLG) => [|eqLG|[K [maxK sLK nKG]]]; first 1 last.
- by rewrite eqLG eqxx in nLG.
- exists K; split=> //; exact: subset_trans sLK.
apply: (leq_trans leGnH); rewrite leq_add2l ltn_neqAle subset_leq_card //.
rewrite andbT; apply: contra nHL; move/eqP=> eqHL.
by apply/eqP; apply/setP; exact/subset_cardP.
Qed.

Definition Frattini := \bigcap_(H : {group gT} | maximal H G) H.

Lemma Frattini_group : group_set Frattini.
Proof.
apply: (@big_prop _ (@group_set _)); first exact: group_setA.
move=> a b HGa HGb; exact:group_setI (Group HGa) (Group HGb).
move=> x Hx; exact: set_of_groupP.
Qed.

Lemma Frattini_sub : Frattini \subset G.
Proof. 
rewrite [Frattini](bigD1 G) ?subsetIl ?eqxx //. 
rewrite /maximal subset_refl andTb; apply/forallP=>x; apply/implyP.
by move/subset_eqP; move/setP->; rewrite eqxx.
Qed.

Lemma Frattini_strict_sub :  G = [set 1] :> set gT \/ Frattini != G.
Proof.
case e: (G == [set 1] :> set _); first by left; move/eqP: e.
right; apply/eqP; apply/setP; apply/subset_eqP; rewrite Frattini_sub andTb.
apply/negP => Hsub; move/bigcap_inP:Hsub=> HF.
have sub1: [set 1] \subset G by rewrite subset_set1 group1.
move:(maximal_existence sub1)=>[Hne|[K [HKmax Hksub Hneq]]]; first by rewrite -Hne eqxx in e.
move: (HF K); rewrite HKmax; move/(_ is_true_true). 
move/andP:HKmax=>[HKsub _]; move/(conj HKsub); move/andP=>//=; move/subset_eqP.
move/setP; move/val_inj; exact/eqP.
Qed.

End FrattiniDefs.

Section FrattiniProps.

Variable gT : finGroupType.

Lemma Frattini_not_gen : forall (G : {group gT}) (X : {set gT}),
  X \subset G -> (G \subset <<X>>) = (G  \subset << X :|: Frattini G >>).
Proof.
move=> G X sXG; apply/idP/idP=> [|sGXF].
  move/subset_trans; apply.
  apply/subsetP=>x; move/bigcapP=>Hx; apply/bigcapP=> i Hi.
  apply Hx; apply: (subset_trans _ Hi); exact: subsetUl.
have sXFG: X :|: Frattini G \subset G.
  by rewrite setU_subset sXG andTb Frattini_sub.
rewrite subset_gen_stable in sXG.
have [<- //=| [K [Kmax sHK nKG]]] := maximal_existence sXG.
rewrite -subset_gen_stable in sHK.
have: Frattini G \subset K by exact: bigcap_inf.
move/(conj sHK); move/andP; rewrite -setU_subset subset_gen_stable.
move/(subset_trans sGXF)=> sGK; case/maximalP: Kmax => sKG _.
by case/eqP: nKG; apply: val_inj; apply/setP; apply/subset_eqP; apply/andP.
Qed.

End FrattiniProps.

Unset Implicit Arguments.
