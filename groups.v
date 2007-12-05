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

Definition commute (x y : elt) := x * y == y * x.

Lemma commute_sym : forall x y, commute x y -> commute y x.
Proof. by move => x y; rewrite /commute  eq_sym. Qed.

Lemma conjg_fpP : forall x y : elt, reflect (commute x y) (conjg_fp y x).
Proof.
move=> *; rewrite /conjg_fp conjgE -mulgA (canF_eq (mulKgv _)); exact: idP.
Qed.

Lemma conjg_fp_sym : forall x y : elt, conjg_fp x y = conjg_fp y x.
Proof. move=> x y; apply/conjg_fpP/conjg_fpP; exact:commute_sym. Qed.

End Conjugation.

Implicit Arguments conjg_inj [elt].
Implicit Arguments conjg_fpP [elt x y].
Prenex Implicits conjg_fpP.

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

Lemma gexpnS: forall a n, a ** (S n) = a * (a ** n).
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

End Expn.

Notation "a '**' p" := (gexpn a p) (at level 50). 

Section SmulDef.

Open Scope group_scope.

Variable elt : finGroupType.

Notation Local "x \in A" := (@s2s elt A x).

(* Set-lifted group operations *)

Definition lcoset x A := {y, x^-1 * y \in A}.
Definition rcoset A x := {y, y * x^-1 \in A}.
Definition smulg_def A B := {xy, ~~ disjoint {y, rcoset A y xy} (s2s B)}.
Definition gmulg_def A B :=
  let C := smulg_def A B in if C == smulg_def B A then C else {:1}.
Definition sinvg A := {y, y^-1 \in A}.
Definition sconjg A x := {y, y ^ x^-1 \in A}.
Definition classg_def x B := {y, image (fun z : elt => x ^ z) (s2s B) y}.
Definition sclassg_def A B := {xy, ~~ disjoint {y, sconjg A y xy} (s2s B)}.

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

Variable elt : finGroupType.

Open Scope group_scope.
Notation Local "x \in A" := (@s2s elt A x) : group_scope.
Notation Local "1" := (unitg elt).

Lemma lcosetE : forall y A z, (z \in y *: A) = (y^-1 * z \in A).
Proof. by move=> *; rewrite s2f. Qed.

Lemma rcosetE : forall A y z, (z \in A :* y) = (z * y^-1 \in A).
Proof. by move=> *; rewrite s2f. Qed.

Lemma lcosetP : forall y A z, reflect (exists2 x, x \in A & z = y * x) (z \in y *: A)%G.
Proof.
move=> y A z; rewrite lcosetE.
apply: (iffP idP) => [Ax | [x Ax ->]]; first exists (y^-1 * z); gsimpl.
Qed.

Lemma rcosetP : forall A y z, reflect (exists2 x, x \in A & z = x * y) (z \in A :* y)%G.
Proof.
move=> A y z; rewrite rcosetE.
apply: (iffP idP) => [Ax | [x Ax ->]]; first exists (z * y^-1); gsimpl.
Qed.

CoInductive mem_smulg A B z : Prop := MemProdg x y of x \in A & y \in B & z = x * y.

Lemma smulgP : forall A B z, reflect (mem_smulg A B z) (z \in A :*: B)%G.
Proof.
unlock smulg => A B z; rewrite s2f; apply: (iffP set0Pn) => [[y]|[x y Ax Ay ->]].
  by case/andP; rewrite s2f; case/rcosetP=> x; exists x y.
by exists y; rewrite /setI s2f Ay andbT; apply/rcosetP; exists x.
Qed.

Lemma smulg_subl : forall A B : setType elt, 1 \in B -> subset A (A :*: B).
Proof. by move=> A B B1; apply/subsetP=> x Ax; apply/smulgP; exists x 1; gsimpl. Qed.

Lemma smulg_subr : forall A B : setType elt, 1 \in A -> subset B (A :*: B).
Proof. by move=> A B A1; apply/subsetP=> x Bx; apply/smulgP; exists 1 x; gsimpl. Qed.

Lemma smulgA : forall A1 A2 A3 : setType elt, A1 :*: (A2 :*: A3) = A1 :*: A2 :*: A3.
Proof.
move=> A1 A2 A3; apply/isetP=> x; apply/smulgP/smulgP=> [[x1 x23 Ax1] | [x12 x3]].
  case/smulgP=> x2 x3 Ax2 Ax3 ->{x23}; rewrite mulgA => Dx.
  by exists (x1 * x2) x3 => //; apply/smulgP; exists x1 x2.
case/smulgP=> x1 x2 Ax1 Ax2 ->{x12} Ax3; rewrite -mulgA => Dx.
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

Lemma rcoset1 : forall A : setType elt, A :* 1 = A.
Proof. by move=> A; apply/isetP=> x; rewrite s2f; gsimpl. Qed.

Lemma lcoset1 : forall A : setType elt, 1 *: A = A.
Proof. by move=> A; apply/isetP=> x; rewrite s2f; gsimpl. Qed.

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
by move=> x y; apply/isetP => z; rewrite -rcoset_smul !s2f (canF_eq (mulgK y)).
Qed.

Lemma gmulgC : forall A B : setType elt, A :**: B = B :**: A.
Proof. by unlock gmulg gmulg_def => A B; rewrite eq_sym; case: eqP. Qed.

Lemma gmulg1 : forall A, A :**: {:1} = A.
Proof.
move=> A; move: (smulg1 A) (smul1g A); unlock gmulg smulg gmulg_def => -> ->.
by rewrite eq_refl.
Qed.

Lemma gmul1g : forall A, {:1} :**: A = A.
Proof. by move=> A; rewrite gmulgC gmulg1. Qed.

Lemma smulC_gmul : forall A B : setType elt, A :*: B = B :*: A -> A :*: B = A :**: B.
Proof. by unlock gmulg gmulg_def smulg => A B <-; rewrite eq_refl. Qed.

Lemma smul_gmul_sym : forall A B : setType elt, A :*: B = A :**: B -> B :*: A = A :**: B.
Proof.
unlock gmulg gmulg_def smulg => A B; case: eqP => // _; move/isetP=> dA; apply/isetP=> z.
rewrite [smulg_def]lock -/smulg s2f in dA *; apply/smulgP/eqP=> [[y x By Ax ->]|<-] {z}.
  have: x * y \in A :*: B by apply/smulgP; exists x y.
  by rewrite dA s2f -{2}(mulKg x y); move/eqP <-; gsimpl.
move/(_ 1): dA; rewrite iset11; case/smulgP=> x y Ax By Dxy.
by exists y x; rewrite // -(mulgK y x) -Dxy; gsimpl.
Qed.

Lemma sinvgK : involutive (@sinvg elt).
Proof. by move=> A; apply/isetP => x; rewrite !s2f invgK. Qed.

Lemma card_sinvg : forall A : setType elt, card (A :^-1) = card A.
Proof.
move=> A; have iinj := @invg_inj elt; rewrite -(card_image iinj).
by apply: eq_card => x; rewrite -[x]invgK image_f // s2f.
Qed.

Lemma sinvgM : forall A B : setType elt, (A :*: B) :^-1 = (B :^-1) :*: (A :^-1).
Proof.
move=> A B; apply/isetP=> xy; rewrite s2f; apply/smulgP/smulgP; last first.
  by case=> y x; rewrite !s2f => By Ax ->{xy}; exists x^-1 y^-1; gsimpl.
by rewrite -{2}(invgK xy); case=> x y Ax By ->{xy}; exists y^-1 x^-1; rewrite ?s2f; gsimpl.
Qed.

Lemma sinvg_set1 : forall x : elt, {:x} :^-1 = {:x^-1}.
Proof. move=> x; apply/isetP=> y; rewrite !s2f inv_eq //; exact: invgK. Qed.

Definition group_set A := (1 \in A) && subset (A :*: A) A.
	 
Lemma group_set_finGroupType :  group_set elt. 	 
Proof. 	 
rewrite /group_set /=; apply/andP; split; first by done. 	 
by apply/subsetP=> u; case/smulgP=> x y Ex Ey ->. 	 
Qed. 	

Lemma groupP : forall A,
  reflect (1 \in A /\ forall x y, x \in A -> y \in A -> x * y \in A) (group_set A).
Proof.
move=> A; apply: (iffP andP) => [] [A1 AM]; split=> {A1}//.
  by move=> x y Ax Ay; apply: (subsetP AM); apply/smulgP; exists x y.
by apply/subsetP=> z; case/smulgP=> [x y Ax Ay ->]; auto.
Qed.

Structure group : Type := Group {
  set_of_group :> setType elt;
  set_of_groupP : group_set set_of_group
}.

Definition group_of_sig u := let: EqSig A gA := u in @Group A gA.
Coercion sig_of_group G := let: Group A gA := G in EqSig group_set A gA.
Lemma sig_of_groupK : cancel sig_of_group group_of_sig. Proof. by case. Qed.
Canonical Structure group_eqType := EqType (can_eq sig_of_groupK).
Canonical Structure group_finType := FinType (can_uniq sig_of_groupK).

Definition groupA := Group group_set_finGroupType.

Lemma set_of_group_inj : injective set_of_group.
Proof. move=> [G1 gG1] [G2 gG2]; move/eqP=> eG12; exact/eqP. Qed.

Section GroupProp.

Variable H : group.

Lemma valG : val H = H. Proof. by case H. Qed.

Lemma group1 : H 1. Proof. by case/groupP: (set_of_groupP H). Qed.

Lemma groupM : forall x y, H x -> H y -> H (x * y).
Proof. by case/groupP: (set_of_groupP H). Qed.

Lemma groupVr : forall x, H x -> H x^-1.
Proof.
move=> x Hx; rewrite -(finv_f (mulg_injl x) x^-1) mulgV /finv.
elim: _.-1 => [|n IHn] /=; [exact: group1 | exact: groupM].
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

Lemma groupE : forall x n, H x -> H (x ** n).
Proof.
move => x n Hx; elim: n => /= [|n Hrec]; first exact: group1.
by rewrite groupM.
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

Canonical Structure subFinGroupType.

Lemma pos_card_group : 0 < card H.
Proof. rewrite lt0n; apply/set0Pn; exists (1 : elt); exact: group1. Qed.

Lemma smulgg : H :*: H = H.
Proof.
by case/andP: (set_of_groupP H) => H1 mH; apply/isetP; apply/subset_eqP; rewrite mH smulg_subr.
Qed.

Lemma sinvG : H :^-1 = H. Proof. by apply/isetP=> x; rewrite s2f groupV. Qed.

End GroupProp.

Hint Resolve group1 groupM groupVr.

Lemma sinvMG : forall H K : group, (H :*: K) :^-1 = K :*: H.
Proof. by move=> H K; rewrite sinvgM !sinvG. Qed.


Lemma group_set_unit : group_set {:1}.
Proof. by rewrite /group_set smulg_set1 mulg1 subset_refl iset11. Qed.

Canonical Structure unit_set_group := Group group_set_unit.

Lemma group_set_gmulG : forall H K : group, group_set (H :**: K).
Proof.
move=> H K; case cHK: (H :*: K == K :*: H); last first.
  by move: cHK; unlock gmulg gmulg_def smulg => ->; exact group_set_unit.
move/eqP: cHK => cHK; rewrite -smulC_gmul //.
apply/andP; split; first by apply/smulgP; exists 1 1; gsimpl.
by rewrite smulgA -(smulgA H) -cHK smulgA smulgg -smulgA smulgg subset_refl.
Qed.

Canonical Structure gmulG_group H K := Group (group_set_gmulG H K).

Lemma group_gmul : forall G H K : group, G = H :*: K :> setType _ -> H :*: K = H :**: K.
Proof. by move=> G H K dG; apply: smulC_gmul; rewrite -dG -sinvG dG sinvgM !sinvG. Qed.

Lemma group_gmul_eq : forall G H K : group, G = H :*: K :> setType _ ->
  G = {H :**: K as group}.
Proof.
move=> G H K dG; apply: (can_inj sig_of_groupK); apply: val_inj; rewrite /= valG dG.
exact: group_gmul dG.
Qed.

End SmulProp.

Hint Resolve group1 groupM groupVr pos_card_group.

Section ConjugationSet.

Open Scope group_scope.

Variable elt : finGroupType.
Variable A : setType elt.

Theorem sconjgE : forall (B : setType elt) x y, (B :^ x^-1) y = B (y ^ x).
Proof. by move=> *; rewrite s2f invgK. Qed.

Theorem sconj1g : A :^ 1 = A.
Proof. by apply/isetP => x; rewrite s2f invg1 conjg1. Qed.

Lemma sconjgM : forall x y, A :^ (x * y) = (A :^ x) :^ y.
Proof. move=> x y; apply/isetP => z; rewrite !s2f /conjg; gsimpl. Qed.

Theorem sconjg_conj : forall (B : setType elt) x y, (B :^ x) (y ^ x) = B y.
Proof. by move=> B x y; rewrite s2f conjgK. Qed.

Lemma sconjMg : forall B x, (A :*: B) :^ x = (A :^ x) :*: (B :^ x).
Proof.
move=> B x; apply/isetP=> yz; rewrite !s2f; apply/smulgP/smulgP=> [] [y z Ay Bz].
  by rewrite -{2}(conjgKv x yz) => ->; exists (y ^ x) (z ^ x); rewrite ?sconjg_conj ?conjg_mul.
by move->; exists (y ^ x^-1) (z ^ x^-1); rewrite -?sconjgE ?conjg_mul ?invgK.
Qed.

Lemma sconj_set1 : forall x y : elt, {:x} :^ y = {:x ^ y}.
Proof. by move=> x y; apply/isetP => z; rewrite !s2f (can2_eq (conjgK y) (conjgKv y)). Qed.

Theorem sconjg_iimage : forall x, A :^ x = (conjg x) @: A.
Proof.
move=> x; apply/isetP=> y; unlock iimage; rewrite !s2f. 
rewrite -{2}(conjgKv x y) image_f ?s2f //; exact: conjg_inj.
Qed.

Lemma sconjg_coset : forall x, A :^ x = x^-1 *: A :* x.
Proof. by move=> x; apply/isetP =>y; rewrite !s2f mulgA. Qed.

Theorem card_sconjg : forall x, card (A :^ x) = card A.
Proof.
move=> x; rewrite (sconjg_iimage x); apply: card_iimage; exact: conjg_inj.
Qed.

Variable H : group elt.

Theorem sconjg1 : forall x, (H :^ x) 1.
Proof. by move=> x; rewrite s2f conj1g group1. Qed.

Theorem sconjg_inv : forall x y, (H :^ x) y -> (H :^ x) y^-1.
Proof. move=> x y; rewrite !s2f conjg_invg; exact: groupVr. Qed.

Theorem group_set_sconjg : forall x, group_set (H :^ x).
Proof. 
move=> x; rewrite /group_set sconjg1; apply/subsetP=> y.
case/smulgP=> x1 x2 Hx1 Hx2 -> {z}.
rewrite !s2f conjg_mul in Hx1 Hx2 *; exact: groupM. 
Qed.
Canonical Structure sconjg_group x := Group (group_set_sconjg x).

End ConjugationSet.

Section LaGrange.

Variables (elt : finGroupType) (H K : group elt).

(*
Definition subgroup := subset H K.
Hypothesis subset_HK : subgroup.*)

Hypothesis subset_HK : subset H K.
Let sHK := subsetP subset_HK.

Open Scope group_scope.

Lemma rcoset_refl : forall x, (H :* x) x.
Proof. by move=> x; rewrite /rcoset s2f mulgV group1. Qed.

Lemma rcoset_sym : forall x y, (H :* x) y = (H :* y) x.
Proof. by move=> *; rewrite !s2f -groupV; gsimpl. Qed.

Lemma rcoset_trans1 : forall x y, (H :* x) y -> H :* x = H :* y.
Proof.
move=> x y Hxy; apply/isetP=> u; rewrite !s2f in Hxy *.
by rewrite -(groupMr (u * y^-1) Hxy); gsimpl.
Qed.

Lemma rcoset_trans : forall x y z, (H :* x) y -> (H :* y) z -> (H :* x) z.
Proof. by move=> x y z; move/rcoset_trans1->. Qed.

Lemma rcoset_trans1r : forall x y, 
  (H :* x) y -> forall z, (H :* z) x = (H :* z) y.
Proof. by move=> x y Hxy z; rewrite !(rcoset_sym z) (rcoset_trans1 Hxy). Qed.

Lemma rcoset_id : forall x, H x -> H :* x = H.
Proof. by move=> x Hx; apply/isetP => y; rewrite !s2f groupMr; auto. Qed.

Lemma card_rcoset : forall x, card (H :* x) = card H.
Proof.
move=> x; have injx := mulg_injr x; rewrite -(card_image injx H); apply: eq_card => y.
by rewrite s2f -{2}(mulgKv x y) image_f.
Qed.

Definition rcosets := iimage (rcoset H).

Definition indexg K := card (rcosets K).

Definition repr (A : setType elt) := if pick A is Some x then x else 1.

Lemma mem_repr : forall x A, s2s A x -> A (repr A).
Proof. by rewrite /repr => x A; case: pickP => [|->]. Qed.

CoInductive rcoset_repr_spec x : elt -> Type :=
  RcosetReprSpec y : H y -> rcoset_repr_spec x (y * x).

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

Theorem LaGrange : (card H * indexg K)%N = card K.
Proof.
pose f x : prod_finType _ _ := pair (x * (repr (H :* x))^-1) (H :* x).
have inj_f: injective f.
  rewrite /f [rcoset]lock => x1 x2 [Dy DHx]; move: Dy; rewrite {}DHx; exact: mulg_injr.
rewrite -card_prod_set -{inj_f}(card_iimage inj_f); apply: eq_card => [] [y A].
apply/andP/iimageP=> /= [[Hy]|[x Kx [-> ->]]]; last first.
  split; last by apply/iimageP; exists x.
  case: repr_rcosetP => z Hz; gsimpl; exact: groupVr.
move/iimageP=> [x Kx ->{A}]; case Dz: (repr _) / (repr_rcosetP x) => [z Hz].
exists (y * z * x); first by rewrite groupMr // sHK // groupM.
have Hxyx: (H :* x) (y * z * x) by rewrite s2f; gsimpl; exact: groupM.
by rewrite /f -(rcoset_trans1 Hxyx) Dz; gsimpl.
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

Lemma sinvg_lcoset : forall x, (x *: H) :^-1 = H :* x^-1.
Proof. by move=> x; rewrite lcoset_smul rcoset_smul sinvgM sinvG sinvg_set1. Qed.

Lemma card_lcoset : forall x, card (x *: H) = card H.
Proof. by move=> x; rewrite -card_sinvg sinvg_lcoset card_rcoset. Qed.

Definition lcosets := iimage (fun x => lcoset x H).

Lemma card_lcosets : card (lcosets K) = indexg K.
Proof.
rewrite -(card_iimage (inv_inj (@sinvgK elt))); apply: eq_card => A.
apply/iimageP/iimageP=> [[B dB ->{A}] | [x Hx ->{A}]].
  case/iimageP: dB => x Kx ->{B}.
  exists x^-1; [exact: groupVr | exact: sinvg_lcoset].
exists (x^-1 *: H); last by rewrite sinvg_lcoset invgK.
by apply/iimageP; exists x^-1; first exact: groupVr.
Qed.

End LaGrange.


Prenex Implicits repr.

Section GroupInter.

Open Scope group_scope.

Variable elt : finGroupType.

Section GroupSmulSub.

Variables (H : group elt) (A : setType elt).
Hypothesis subAH : subset A H.
Let sAH := subsetP subAH.

Lemma smulsG : forall x, A x -> A :*: H = H.
Proof.
move=> x Ax; apply/isetP; apply/subset_eqP; rewrite -{2}smulgg smulsg //.
apply/subsetP=> y Ky; apply/smulgP; exists x (x^-1 * y); gsimpl.
by rewrite groupMl // groupV; auto.
Qed.

Lemma smulGs : forall x, A x -> H :*: A = H.
Proof.
move=> x Ax; apply/isetP; apply/subset_eqP; rewrite -{2}smulgg smulgs //.
apply/subsetP=> y Ky; apply/smulgP; exists (y * x^-1) x; gsimpl.
by rewrite groupMr // groupV; auto.
Qed.

Definition smulsG1 := @smulsG 1.
Definition smulGs1 := @smulGs 1.

End GroupSmulSub.


Section GroupSmulSubGroup.

Variables H K : group elt.
(*Hypothesis subHK : subgroup H K.*)
Hypothesis subHK : subset H K.

Definition smulSG := smulsG subHK (group1 H).
Definition smulGS := smulGs subHK (group1 H).

End GroupSmulSubGroup.

Variables H K : group elt.

Lemma group_setI : group_set (H :&: K).
Proof.
apply/groupP; split=> [|x y]; rewrite !s2f ?group1 //.
by move/andP=> [Hx Kx]; rewrite !groupMl.
Qed.

Canonical Structure setI_group := Group group_setI.

Lemma card_smulg :
  (card (H :*: K) * card (H :&: K) = card H * card K)%N.
Proof.
rewrite -(LaGrange (subsetIr H K)) mulnCA mulnC /=; congr muln.
symmetry; rewrite -card_prod_set -card_sub; set tup := prod_set _ _.
pose f (u : sub_finType tup) := let: pair x Hy := val u in x * repr Hy.
have injf: injective f.
  rewrite /f => [] [[x1 A1] dom1] [[x2 A2] dom2] /= Ef; apply: val_inj => /=.
  case/andP: dom1 (Ef) => /= Hx1; case/iimageP=> y1 Ky1 dA1.
  case/andP: dom2 => /= Hx2; case/iimageP=> y2 Ky2 dA2.
  suff ->: A1 = A2 by move/mulg_injr->.
  rewrite {A1}dA1 {A2}dA2 in Ef *; have kEf := canRL (mulKg _).
  apply: rcoset_trans1; rewrite // !s2f andbC groupM ?groupV //=.
  case: repr_rcosetP Ef => z1; case/isetIP=> Hz1 _; rewrite mulgA; move/kEf->.
  by case: repr_rcosetP => z2; case/isetIP=> Hz2 _; gsimpl; rewrite !groupM ?groupV.
rewrite -(card_codom injf); apply: eq_card => z.
apply/set0Pn/smulgP; rewrite /f /preimage.
  case=> [[[x A]]] /=; case/andP=> /= Hx; case/iimageP=> y Ky -> {A}.
  move/eqP=> ->{z}; case: repr_rcosetP => z /= HKz; exists x (z * y); rewrite // groupMr //.
  by case/isetIP: HKz.
move=> [x y Hx Ky ->{z}].
case Dz: (repr _) / (repr_rcosetP {H :&: K as group _} y) => /= [z HKz].
case/isetIP: HKz => Hz Kz.
have Tu: tup (pair (x * z^-1) ((H :&: K) :* y)).
  by rewrite /tup /prod_set /= groupMl ?groupVr //; apply/iimageP; exists y.
by exists (EqSig tup _ Tu); apply/eqP; rewrite /= Dz; gsimpl.
Qed.

Definition trivg (A : setType elt) := subset A {:1}.

Lemma trivgP : forall G : group elt, reflect (G = {:1} :> setType _) (trivg G).
Proof.
move=> G; apply: (iffP idP) => [tG | ->]; last exact: subset_refl.
by apply/isetP; apply/subset_eqP; rewrite andbC subset_set1 group1.
Qed.

Definition disjointg := trivg (H :&: K).

Lemma disjointgP : reflect (H :&: K = {:1}) disjointg.
Proof. exact: trivgP. Qed.

Lemma disjointg_card : disjointg = (card (H :&: K) == 1%nat).
Proof.
apply/disjointgP/eqP=> [->|cHK]; first by rewrite icard1.
symmetry; apply/isetP; apply/subset_cardP; first by rewrite icard1.
apply/subsetP=> x; rewrite s2f; move/eqP <-; exact: group1.
Qed.

(*Lemma group_modularity : forall G, subgroup G K ->*)
Lemma group_modularity : forall G : group elt, subset G K ->
  G :*: (H :&: K) = G :*: H :&: K.
Proof.
move=> G; move/subsetP=> sGK; apply/isetP => x.
apply/smulgP/idP=> [[y z Gy]|]; rewrite s2f; case/andP.
  move=> Hz Kz -> {x}; rewrite s2f andbC groupMr // sGK //.
  by apply/smulgP; exists y z.
move/smulgP=> [y z Gy Hz -> {x}] Kyz.
by exists y z => //; rewrite s2f Hz; rewrite groupMl // sGK in Kyz.
Qed.

Lemma disjoint_card_smulg :
  disjointg -> (card (H :*: K) = card H * card K)%N.
Proof. by rewrite disjointg_card => HK1; rewrite -card_smulg (eqP HK1) muln1. Qed.

End GroupInter.

Section Normalizer.

Open Scope group_scope.

Variable elt : finGroupType.

Section NormSet.

Variable A : setType elt.

Definition normaliser := {x, subset (A :^ x) A}.

Theorem norm_sconjg : forall x, normaliser x -> A :^ x = A.
Proof. 
by move=> x Ax; apply/isetP; apply/subset_cardP; [rewrite card_sconjg | rewrite s2f in Ax]. 
Qed.


Theorem group_set_normaliser : group_set normaliser.
Proof.
apply/groupP; split=> [|x y Nx Ny]; first by rewrite s2f sconj1g subset_refl.
by rewrite s2f; apply/subsetP => z; rewrite sconjgM !norm_sconjg.
Qed.

Canonical Structure group_normaliser := Group group_set_normaliser.

Definition normalized (B : setType elt) := subset B normaliser.
 
Lemma norm_smulC : forall B, normalized B -> A :*: B = B :*: A.
Proof.
move=> B; move/subsetP=> nB; apply/isetP => u.
apply/smulgP/smulgP=> [[x y Ax By] | [y x By Ax]] -> {u}; have dAy := norm_sconjg (nB _ By).
- by exists y (x ^ y); last rewrite /conjg; gsimpl; rewrite -dAy s2f conjgK.
by exists (x ^ y^-1) y; last rewrite /conjg; gsimpl; rewrite -sconjgE invgK dAy.
Qed.

Lemma norm_gmulr : forall B, normalized B -> A :*: B = A :**: B.
Proof. by move=> B; move/norm_smulC; exact: smulC_gmul. Qed.

Lemma norm_gmull : forall B, normalized B -> B :*: A = A :**: B.
Proof. by move=> B; move/norm_smulC=> dBA; rewrite -dBA; exact: smulC_gmul. Qed.


End NormSet.

Variable H : group elt.
Notation N := (normaliser H).

Theorem norm_refl : subset H N.
Proof.
apply/subsetP=> x Hx; rewrite s2f; apply/subsetP => y.
by rewrite s2f /conjg invgK groupMr ?groupMl ?groupV.
Qed.

Lemma norm_rcoset : forall x, N x -> subset (H :* x) N.
Proof.
move=> x Nx; rewrite rcoset_smul; rewrite -[normaliser _]smulgg /=.
by apply: subset_trans (smulsg _ norm_refl); apply: smulgs; rewrite subset_set1.
Qed.

End Normalizer.

Open Scope group_scope.

Lemma norm_rlcoset : 
  forall elt (H : group elt) x, normaliser H x -> (H :* x) = (x *: H).
Proof.
move=> elt H x; rewrite rcoset_smul lcoset_smul -subset_set1; exact: norm_smulC.
Qed.


Lemma rcoset_mul : forall elt (H : group elt) x y, 
  normaliser H x  -> (H :* x) :*: (H :* y) = H :* (x * y).
Proof.
move=> elt H x y Nx.
rewrite !rcoset_smul -smulgA (smulgA _ H) -lcoset_smul -norm_rlcoset //.
by rewrite rcoset_smul -smulgA smulg_set1 smulgA smulgg.
Qed.


Section Maximal.

Variable elt: finGroupType.
Variable H G: setType elt.
Definition  maximal :=
  subset H G &&
  forallb K : setType elt,
 (group_set K && (subset H K) && (~~(H == K)) && (subset K G)) 
  ==> K == G.

Theorem maximalP:
 reflect
 (subset H G  /\ 
   forall (K: group elt), subset H K -> ~ H =1 K -> subset K G ->
                  K =1 G) 
 maximal.
Proof.
apply: (iffP idP).
  case/andP => Hhg; move/forallP => Hf; split; first done.
  move=> K Hs He Hs1 z; suff ->: (K: setType elt) = G by done.
  apply/eqP; apply: (implyP (Hf K)); rewrite Hs Hs1 set_of_groupP andbT.
  by apply/negP => HH; case He; rewrite (eqP HH).
move=> [Hs Hf]; rewrite /maximal Hs andTb.
apply/forallP => K; apply/implyP; (do 3 case/andP) => E0 E1 E2 E3.
apply/eqP; apply/isetP;  apply: (Hf (Group E0)) => //.
by move/isetP => HH; case/negP: E2; apply/eqP.
Qed.

End Maximal.


Unset Implicit Arguments.

