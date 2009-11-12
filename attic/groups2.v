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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Syntax for referring to canonical structures:                   *)
(*   {mycarrier as mystruct}                                       *)
(* denotes mycarrier_struct when mycarrier_struct : mystruct is a  *)
(* Canonical Structure that projects to mycarrier via one of its   *)
(* coercions, i.e., such that                                      *)
(*     mycarrier_struct : typeof mycarrier = mycarrier.            *)
(*  Although {mycarrier as mystruct} reduces (via simpl or /=) to  *)
(* mycarrier_struct, it does not actually denote mycarrier_struct, *)
(* but a more complex term that gets displayed as                  *)
(*      (* mycarrier as mystruct *) mycarrier_struct               *)

Module GetCanonical.

CoInductive phantom ct (c c' : ct) st (s : st) : Type := Phantom.

Definition get ct (c : ct) st (s : st) (p : phantom c c s) := let: Phantom := p in s.

End GetCanonical.

Notation "'(*' c 'as' st '*)' s" :=
  (@GetCanonical.get _ c st s _)
  (at level 10, t, s at level 200, format "'(*'  c  'as'  st  '*)'  s")
  : group_scope.

Notation "{ c 'as' st }" :=
  (GetCanonical.get ((fun s : st => GetCanonical.Phantom c s s) _))
  (at level 0, c at level 99, s at level 200)
   : group_scope.

(* Doesn't work - probably due to a reversed unification problem
Module GetCanonical.

Definition coerce ct (c1 c2 : ct) := c2.

Definition get ct (c : ct) st (pr : st -> ct)
                     (s : st) (p : coerce c (pr s) = c) :=
  let: refl_equal := p in s.

End GetCanonical.

Implicit Arguments GetCanonical.get [].

Notation "{ c 'as' st }" :=
  (GetCanonical.get _ c st _ _ (erefl (GetCanonical.coerce c (_ : st))))
  (at level 0, c at level 99, st at level 200) : group_scope.


Notation "{ c 'as' 'for' pr }" :=
  (GetCanonical.get _ c _ pr _ (erefl (GetCanonical.coerce c (pr _))))
  (at level 0, c at level 99, pr at level 9, s ident) : group_scope.
*)

Delimit Scope generic_scope with G.
Open Scope generic_scope.

Structure unit_class : Type := UnitClass {
  unit_sort :> Type;
  unit_op : unit_sort;
  unit_mul_op : unit_sort -> unit_sort -> unit_sort;
  unit_exp_op : unit_sort -> unit_sort -> unit_sort
}.

Definition unit := nosimpl unit_op.

Notation "1" := (unit _) : generic_scope.

Canonical Structure nat_unit := UnitClass 1%nat muln expn.

Structure mul_class (R : Type) : Type :=
  MulClass { mul_sort : Type; mul_op : mul_sort -> R }.

Definition mul := nosimpl mul_op.

Definition mul_tag A (x : A) := x.

Notation "x * y" := (mul_tag (mul x y)) : generic_scope.

Canonical Structure unit_mul U := MulClass (@unit_mul_op U).

Structure nat_mul_class (R : Type) : Type :=
  NatMulClass { nat_mul_sort : Type; nat_mul_op : nat -> nat_mul_sort -> R }.

Canonical Structure nat_mul R S := MulClass (@nat_mul_op R S).

Canonical Structure nat_mul_nat := NatMulClass muln.

Canonical Structure nat_mul_unit := @NatMulClass _ nat_unit muln.

Structure exp_class (R : Type) : Type :=
  ExpClass { exp_sort : Type; exp_op : exp_sort -> R }.

Definition exp := nosimpl exp_op.

Definition exp_tag A (x : A) := x.

Notation "x ^ y" := (exp_tag (exp x y)) : generic_scope.

Canonical Structure unit_exp U := ExpClass (@unit_exp_op U).

Canonical Structure nat_exp := ExpClass expn.

Structure inv_class (R : Type) : Type :=
  InvClass { inv_sort : Type; inv_op : inv_sort -> R }.

Definition inv := nosimpl inv_op.

Definition inv_tag A (x : A) := x.

Notation "x '^-1'" := (inv_tag (inv x)).
(* (at level 9, format "x '^-1'") : generic_scope. *)

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

Delimit Scope group_scope with GR.
Bind Scope group_scope with Group.element.
Arguments Scope Group.mul [_ group_scope group_scope].
Arguments Scope Group.inv [_ group_scope].

Notation finGroupType := Group.finGroupType.
Notation FinGroupType := Group.FinGroupType.

Section GroupEltOps.

Variable elt : finGroupType.

Notation Local gunit := (@Group.unit elt).
Notation Local ginv := (@Group.inv elt).
Notation Local mulgen := (@Group.mul elt).

Structure elt_mul_class (R : Type) : Type :=
  EltMulClass { elt_mul_sort : Type; elt_mul_op : elt -> elt_mul_sort -> R }.

Canonical Structure elt_mul R S := MulClass (@elt_mul_op R S).

Canonical Structure elt_mul_elt := EltMulClass mulgen.

Canonical Structure elt_inv := InvClass ginv.

Let gexp (x y : elt) := y^-1 * x * y.

Canonical Structure elt_unit := UnitClass gunit mulgen gexp.

Canonical Structure unit_inv := @InvClass _ elt_unit ginv.

Canonical Structure elt_mul_unit := @EltMulClass _ elt_unit mulgen.

Structure elt_exp_class (R : Type) : Type :=
  EltExpClass { elt_exp_sort : Type; elt_exp_op : elt -> elt_exp_sort -> R }.

Canonical Structure elt_exp R S := ExpClass (@elt_exp_op R S).

Canonical Structure elt_exp_nat :=
  EltExpClass (fun (x : elt) (n : nat) => iter n (fun y : elt => x * y) 1).

Canonical Structure elt_exp_elt := EltExpClass gexp.

Canonical Structure elt_exp_unit := @EltExpClass elt elt_unit gexp.

End GroupEltOps.

Section GroupIdentities.

Open Scope group_scope.

Variable elt : finGroupType.

Notation Local mulkg := (fun x y : elt => x * y).
Notation Local mulgk := (fun x y : elt => y * x).

Lemma mulgA : forall x1 x2 x3 : elt, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. exact: Group.mulP. Qed.

Lemma mul1g : forall x : elt, 1 * x = x.
Proof. exact: Group.unitP. Qed.

Lemma mulVg : forall x : elt, x^-1 * x = 1.
Proof. exact: Group.invP. Qed.

Lemma mulKg : forall x : elt, cancel (mulkg x) (mulkg x^-1).
Proof. by move=> x y; rewrite mulgA mulVg mul1g. Qed.

Lemma mulg_injl : forall x : elt, injective (mulkg x).
Proof. move=> x; exact: can_inj (mulKg x). Qed.

Implicit Arguments mulg_injl [].

Lemma mulgV : forall x : elt, x * x^-1 = 1.
Proof. by move=> x; rewrite -{1}(mulKg x^-1 x) mulVg -mulgA mul1g mulVg. Qed.

Lemma mulKVg : forall x : elt, cancel (mulkg x^-1) (mulkg x).
Proof. by move=> x y; rewrite mulgA mulgV mul1g. Qed.

Lemma mulg1 : forall x : elt, x * 1 = x.
Proof. by move=> x; rewrite -(mulVg x) mulKVg. Qed.

Lemma mulgK : forall x : elt, cancel (mulgk x) (mulgk  x^-1).
Proof. by move=> x y; rewrite -mulgA mulgV mulg1. Qed.

Lemma mulg_injr : forall x : elt, injective (mulgk x).
Proof. move=> x; exact: can_inj (mulgK x). Qed.

Lemma mulgKV : forall x : elt, cancel (mulgk x^-1) (mulgk x).
Proof. by move=> x y; rewrite -mulgA mulVg mulg1. Qed.

Lemma invg1 : 1^-1 = 1 :> elt.
Proof. by rewrite -{2}(mulVg 1) mulg1. Qed.

Lemma invgK : involutive (fun x : elt => x^-1).
Proof. by move=> x; rewrite -{2}(mulgK x^-1 x) -mulgA mulKVg. Qed.

Lemma invg_inj : injective (fun x : elt => x^-1).
Proof. exact: can_inj invgK. Qed.

Lemma invMg : forall x1 x2 : elt, (x2 * x1)^-1 = x1^-1 * x2^-1.
Proof.
by move=> x1 x2; apply: (mulg_injl (x2 * x1)); rewrite mulgA mulgK !mulgV.
Qed.

End GroupIdentities.

Implicit Arguments mulg_injl [elt].
Implicit Arguments mulg_injr [elt].

Hint Rewrite mulg1 mul1g invg1 mulVg mulgV invgK mulgK mulgKV
             invMg mulgA : gsimpl.

Definition gsimpl := (mulg1, mul1g, invg1, mulVg, mulgV, invgK, mulgK, mulgKV, invMg, mulgA).

(* Ltac gsimpl := autorewrite with gsimpl; try done. *)

Ltac gsimpl := rewrite ?gsimpl //.

Section Conjugation.

Variable elt : finGroupType.

Open Scope group_scope.

Lemma conjgE : forall x y : elt, x ^ y = y^-1 * x * y. Proof. done. Qed.

Lemma conjg1 : forall x : elt, x ^ 1 = x.
Proof. by move=> x; rewrite /exp /= invg1 mul1g mulg1. Qed.

Lemma conj1g : forall x : elt, 1 ^ x = 1.
Proof. by move=> x; rewrite /exp /= mulg1 mulVg. Qed.

Lemma conjMg : forall x1 x2 y : elt, (x1 * x2) ^ y = x1 ^ y * x2 ^ y.
Proof. by move=> *; rewrite /exp /= !mulgA mulgK. Qed.

Lemma conjVg : forall x y : elt, x^-1 ^ y = (x ^ y)^-1.
Proof. by move=> *; rewrite /exp /= !invMg mulgA invgK. Qed.

Lemma conjgM : forall x y1 y2 : elt, x ^ (y1 * y2) = (x ^ y1) ^ y2.
Proof. by move=> *; rewrite /exp /= invMg !mulgA. Qed.

Lemma conjgK : forall y : elt,
  cancel (fun x : elt => x ^ y) (fun x => x ^ y^-1).
Proof. by move=> y x; rewrite -conjgM mulgV conjg1. Qed.

Lemma conjgKV : forall y : elt,
  cancel (fun x : elt => x ^ y^-1) (fun x => x ^ y).
Proof. by move=> y x; rewrite -conjgM mulVg conjg1. Qed.

Lemma conjg_inj : forall y : elt, injective (fun x : elt => x ^ y).
Proof. move=> y; exact: can_inj (conjgK y). Qed.

Definition conjg_fp (y x : elt) := x ^ y == x.

Definition commb (x y : elt) := x * y = y * x.

Lemma commb_sym : forall x y, commb x y -> commb y x.
Proof. done. Qed.

Lemma conjg_fpP : forall x y : elt, reflect (commb x y) (conjg_fp y x).
Proof.
move=> *; rewrite /conjg_fp conjgE -mulgA (canF_eq (mulKVg _)); exact: eqP.
Qed.

Lemma conjg_fp_sym : forall x y : elt, conjg_fp x y = conjg_fp y x.
Proof. move=> x y; exact/conjg_fpP/conjg_fpP. Qed.

End Conjugation.

Implicit Arguments conjg_inj [elt].
Implicit Arguments conjg_fpP [elt x y].
Prenex Implicits conjg_fpP.

Section natexp.

Variable elt : finGroupType.

Lemma expg1 : forall x : elt, x ^ (1 : nat) = x.
Proof. exact: mulg1. Qed.

Lemma expg_add : forall (x : elt) (m n : nat), x ^ (m + n) = x ^ m * x ^ n.
Proof.
by rewrite /exp_tag /exp /= => x m n; elim: m => /= [|m ->]; rewrite ?mul1g ?mulgA.
Qed.

Lemma exp1g : forall n : nat, (1 : elt) ^ n = 1.
Proof. rewrite /exp /exp_tag /=; elim=> /= [|n ->]; gsimpl. Qed.

Lemma expJg : forall (x y : elt) (n : nat), (x ^ y) ^ n = (x ^ n) ^ y.
Proof.
rewrite {1 4}/exp {1 4}/exp_tag /= => x y.
by elim=> /= [|n ->]; rewrite ?conj1g ?conjMg.
Qed.

Lemma commb_exp : forall (x y : elt) (n : nat),
  commb x y -> commb (x ^ n) y.
Proof.
rewrite /exp /commb /= => x y n cxy; elim: n => /= [|n IHn]; gsimpl.
by rewrite -cxy -!mulgA IHn.
Qed.

Lemma expMg : forall (x y : elt) (n : nat),
  commb x y -> (x * y) ^ n = (x ^ n) * (y ^ n).
Proof.
rewrite /exp /exp_tag /= => x y n cxy; elim: n => /= [|n ->]; gsimpl.
rewrite -(mulgA x y) -(commb_exp _ cxy); gsimpl.
Qed.

End natexp.

Section SmulDef.

Open Scope group_scope.

Variable elt : finGroupType.

Notation "x \in A" := (@s2s elt A x).
(* (at level 65, no associativity). *)

(* Set-lifted group operations *)

Definition sinvg A := {y, y^-1 \in A}.

Canonical Structure set_inv := InvClass sinvg.

Structure set_mul_class (R : Type) : Type :=
  SetMulClass { set_mul_sort : Type; set_mul_op : set elt -> set_mul_sort -> R }.

Canonical Structure set_mul R S := MulClass (@set_mul_op R S).

Definition lcoset (x : elt) A := {y, x^-1 * y \in A}.

Definition rcoset A (x : elt) := {y, y * x^-1 \in A}.

Definition smulg (A B : set elt) := {xy, ~~ disjoint {y, xy \in rcoset A y} B}.

Canonical Structure set_mul_set := SetMulClass (locked smulg).
Canonical Structure set_mul_elt := SetMulClass (fun A x => A * {: x}).
Canonical Structure elt_mul_set := EltMulClass (fun x (A : set elt) => {: x} * A).

Structure set_exp_class (R : Type) : Type :=
  SetExpClass { set_exp_sort : Type; set_exp_op : set elt -> set_exp_sort -> R }.
Canonical Structure set_exp R S := ExpClass (@set_exp_op R S).

Definition sconjg A (x : elt) := {y, y ^ x^-1 \in A}.
Canonical Structure set_exp_elt := SetExpClass sconjg.

Definition classg (x : elt) (B : set elt) := {y, image (fun z => x ^ z) B y}.
Canonical Structure elt_exp_set := EltExpClass (locked classg).

Definition sclassg (A B : set elt) := {xy, ~~ disjoint {y, xy \in A ^ y} B}.
Canonical Structure set_exp_set := SetExpClass (locked sclassg).

Canonical Structure set_unit := UnitClass ({:1 : elt}) (locked smulg) (locked sclassg).
Canonical Structure set_mul_unit := @SetMulClass _ set_unit (locked smulg).
Canonical Structure set_exp_unit := @SetExpClass _ set_unit (locked sclassg).

Definition mulgeng (A B : set elt) := if A * B == B * A then A * B else 1.

End SmulDef.

Notation "A '*'' B" := (mulgeng A B) (at level 40) : group_scope.

Section SmulProp.

Variable elt : finGroupType.

Open Scope group_scope.
Notation Local "x \in A" := (@s2s elt A x) (at level 65, no associativity).

(*
Lemma lcoinE : forall (y : elt) (A : set elt) z, z \in y * A = y^-1 * z \in A.
Proof. by move=> *; rewrite inE. Qed.
*)
Lemma mem_rcoset : forall A (y z : elt), z \in rcoset A y = z * y^-1 \in A.
Proof. by move=> *; rewrite inE. Qed.

(*
Lemma lcosetP : forall (y : elt) A z,
  reflect (exists2 x, x \in A & z = y * x) (z \in y * A).
Proof.
move=> /= y A z; rewrite lcoinE.
apply: (iffP idP) => [Ax | [x Ax ->]]; first exists (y^-1 * z); gsimpl.
Qed.
*)

Lemma rcosetP : forall A (y z : elt),
  reflect (exists2 x, x \in A & z = x * y) (z \in rcoset A y).
Proof.
move=> /= A y z; rewrite mem_rcoset.
apply: (iffP idP) => [Ax | [x Ax ->]]; first exists (z * y^-1); gsimpl.
Qed.

CoInductive mem_smulg A B z : Prop := MemProdg x y of x \in A & y \in B & z = x * y.

Lemma mulsgP : forall A B z, reflect (mem_smulg A B z) (z \in A * B).
Proof.
rewrite /mul /= -lock => A B z; rewrite inE; apply: (iffP set0Pn) => [[y]|[x y Ax Ay ->]].
  by case/andP; rewrite inE; case/rcosetP=> x; exists x y.
by exists y; rewrite /setI inE Ay andbT; apply/rcosetP; exists x.
Qed.

Lemma smulg_subl : forall A B : set elt, 1 \in B -> subset A (A * B).
Proof.
by move=> A B B1; apply/subsetP=> x Ax; apply/mulsgP; exists x (1 : elt); gsimpl.
Qed.

Lemma smulg_subr : forall A B : set elt, 1 \in A -> subset B (A * B).
Proof.
by move=> A B A1; apply/subsetP=> x Bx; apply/mulsgP; exists (1 : elt) x; gsimpl.
Qed.

Lemma smulgA : forall A1 A2 A3 : set elt, A1 * (A2 * A3) = A1 * A2 * A3.
Proof.
move=> A1 A2 A3; apply/setP=> x; apply/mulsgP/mulsgP=> [[x1 x23 Ax1] | [x12 x3]].
  case/mulsgP=> x2 x3 Ax2 Ax3 ->{x23}; rewrite mulgA => Dx.
  by exists (x1 * x2) x3 => //; apply/mulsgP; exists x1 x2.
case/mulsgP=> x1 x2 Ax1 Ax2 ->{x12} Ax3; rewrite -mulgA => Dx.
by exists x1 (x2 * x3) => //; apply/mulsgP; exists x2 x3.
Qed.

Lemma rcoset_smul : forall (A : set elt) (x : elt), rcoset A x = A * x.
Proof.
move=> A x; apply/setP => y; apply/rcosetP/mulsgP => [[z]|[z x']].
  by exists z x; first 2 [exact: set11].
by rewrite inE => ?; move/eqP=> -> ->; exists z.
Qed.

Lemma lcoset_smul : forall (A : set elt) (x : elt), lcoset x A = x * A.
Proof.
move=> A x; apply/setP => y; rewrite inE; apply/idP/mulsgP => [|[x' z]].
  by exists x (x^-1 * y); [ exact: set11 | | rewrite mulKVg].
by rewrite inE; move/eqP=> -> ? ->; rewrite mulKg.
Qed.

Lemma rcoset1 : forall A : set elt, rcoset A 1 = A.
Proof. by move=> A; apply/setP=> x; rewrite inE; gsimpl. Qed.

Lemma lcoset1 : forall A : set elt, lcoset 1 A = A.
Proof. by move=> A; apply/setP=> x; rewrite inE; gsimpl. Qed.

Lemma smulg1 : forall A : set elt, A * 1 = A.
Proof. by move=> A; rewrite -rcoset_smul rcoset1. Qed.

Lemma smul1g : forall A : set elt, 1 * A = A.
Proof. by move=> A; rewrite -lcoset_smul lcoset1. Qed.

Lemma smulgs : forall A B1 B2 : set elt,
  subset B1 B2 -> subset (A * B1) (A * B2).
Proof.
move=> A B1 B2; move/subsetP=> sB12; apply/subsetP=> x.
case/mulsgP=> y z Ay Bz ->; apply/mulsgP; exists y z; auto.
Qed.

Lemma smulsg : forall A1 A2 B : set elt,
  subset A1 A2 -> subset (A1 * B) (A2 * B).
Proof.
move=> A1 A2 B; move/subsetP=> sA12; apply/subsetP=> x.
case/mulsgP=> y z Ay Bz ->; apply/mulsgP; exists y z; auto.
Qed.

Lemma smulg_set1 : forall x y : elt, {:x} * {:y} = {:x * y}.
Proof.
by move=> x y; apply/setP => z; rewrite -rcoset_smul !inE (canF_eq (mulgK y)).
Qed.

Lemma mulgengC : forall A B : set elt, A *' B = B *' A.
Proof. by unlock mulgeng smulg => A B; rewrite eq_sym; case: eqP. Qed.

Lemma mulgeng1 : forall A : set elt, A *' 1 = A.
Proof.
move=> A; move: (smulg1 A) (smul1g A); unlock mulgeng smulg => -> ->.
by rewrite eq_refl.
Qed.

Lemma mulgen1g : forall A : set elt, 1 *' A = A.
Proof. by move=> A; rewrite mulgengC mulgeng1. Qed.

Lemma smulC_mulgen : forall A B : set elt, A * B = B * A -> A * B = A *' B.
Proof. by unlock mulgeng smulg => A B <-; rewrite eq_refl. Qed.

Lemma smul_mulgen_sym : forall A B : set elt, A * B = A *' B -> B * A = A *' B.
Proof.
unlock mulgeng smulg => A B; case: eqP => // _; move/setP=> dA; apply/setP=> z.
rewrite [{:1} z]inE; apply/mulsgP/eqP=> [[y x By Ax ->]|<-] {z}.
  have: x * y \in A * B by apply/mulsgP; exists x y.
  by rewrite dA inE -{2}(mulKg x y); move/eqP <-; gsimpl.
move/(_ 1): dA; rewrite set11; case/mulsgP=> x y Ax By Dxy.
by exists y x; rewrite // -(mulgK y x) -Dxy; gsimpl.
Qed.

Lemma sinvgK : involutive (fun A : set elt => A^-1).
Proof. by move=> A; apply/setP => x; rewrite !inE invgK. Qed.

Lemma card_sinvg : forall A : set elt, card A^-1 = card A.
Proof.
move=> A; have iinj := @invg_inj elt; rewrite -(card_image iinj).
by apply: eq_card => x; rewrite -[x]invgK image_f // inE.
Qed.

Lemma sinvMg : forall A B : set elt, (A * B)^-1 = B^-1 * A^-1.
Proof.
move=> A B; apply/setP=> xy; rewrite inE; apply/mulsgP/mulsgP; last first.
  by case=> y x; rewrite !inE => By Ax ->{xy}; exists x^-1 y^-1; gsimpl.
rewrite -{2}(invgK xy); case=> x y Ax By ->{xy}.
by exists y^-1 x^-1; rewrite ?inE; gsimpl.
Qed.

Lemma sinvg_set1 : forall x : elt, {:x}^-1 = {:x^-1}.
Proof. move=> x; apply/setP=> y; rewrite /inv_tag !inE inv_eq //; exact: invgK. Qed.

Definition group_set A := (1 \in A) && subset (A * A) A.

Lemma group_setP : forall A,
  reflect (1 \in A /\ forall x y, x \in A -> y \in A -> x * y \in A) (group_set A).
Proof.
move=> A; apply: (iffP andP) => [] [A1 AM]; split=> {A1}//.
  by move=> x y Ax Ay; apply: (subsetP AM); apply/mulsgP; exists x y.
by apply/subsetP=> z; case/mulsgP=> [x y Ax Ay ->]; auto.
Qed.

Structure group : Type := Group {
  set_of_group :> set elt;
  groupP : group_set set_of_group
}.

Definition group_of_sig u := let: EqSig A gA := u in @Group A gA.
Coercion sig_of_group G := let: Group A gA := G in EqSig group_set A gA.
Lemma sig_of_groupK : cancel sig_of_group group_of_sig. Proof. by case. Qed.
Canonical Structure group_eqType := EqType (can_eq sig_of_groupK).
Canonical Structure group_finType := FinType (can_uniq sig_of_groupK).
Lemma group_inj : injective set_of_group.
Proof. move=> [x ?] [y ?]; move/eqP=> ?; exact/eqP. Qed.

Canonical Structure group_mul R S :=
  MulClass (fun G (A : @set_mul_sort _ R S) => set_of_group G * A).
Canonical Structure set_mul_group := SetMulClass (fun A G => A * set_of_group G).
Canonical Structure elt_mul_group := EltMulClass (fun x G => x * set_of_group G).
Canonical Structure group_exp R S :=
  ExpClass (fun G (A : @set_exp_sort _ R S) => set_of_group G ^ A).
Canonical Structure set_exp_group := SetExpClass (fun A G => A ^ set_of_group G).
Canonical Structure elt_exp_group := EltExpClass (fun x G => x ^ set_of_group G).
Canonical Structure group_inv := InvClass (fun G => (set_of_group G)^-1).

Section GroupProp.

Variable H : group.

Lemma valG : val H = H. Proof. by case H. Qed.

Lemma group1 : H 1. Proof. by case/group_setP: (groupP H). Qed.

Lemma groupM : forall x y, H x -> H y -> H (x * y).
Proof. by case/group_setP: (groupP H). Qed.

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
Proof. by move=> *; rewrite /exp /= !groupM ?groupV. Qed.

Lemma groupJr : forall x y, H y -> H (x ^ y) = H x.
Proof. by move=> *; rewrite /exp /= groupMr ?groupMl ?groupV. Qed.

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

Lemma mulGid : H * H = H.
Proof.
case/andP: (groupP H) => H1 mH; apply/setP; apply/subset_eqP.
by rewrite mH smulg_subr.
Qed.

Lemma sinvG : H^-1 = H. Proof. by apply/setP=> x; rewrite inE groupV. Qed.

End GroupProp.

Hint Resolve group1 groupM groupVr.

Lemma sinvMG : forall H K : group, (H * K)^-1 = K * H.
Proof. by move=> H K; rewrite sinvMg ![_^-1]sinvG. Qed.

Lemma group_set_unit : group_set {:1}.
Proof. by rewrite /group_set smulg_set1 mulg1 subset_refl set11. Qed.

Canonical Structure unit_set_group := Group group_set_unit.

Lemma group_set_mulgenG : forall H K : group, group_set (H *' K).
Proof.
move=> H K; case cHK: (H * K == K * H); last first.
  by move: cHK; unlock mulgeng smulg => ->; exact group_set_unit.
move/eqP: cHK => cHK; rewrite -smulC_mulgen //.
apply/andP; split; first by apply/mulsgP; exists (1 : elt) (1 : elt); gsimpl.
by rewrite smulgA -(smulgA H) -cHK smulgA -smulgA (mulGid H) (mulGid K) subset_refl.
Qed.

Canonical Structure mulgenG_group H K := Group (group_set_mulgenG H K).

Lemma group_mulgen : forall G H K : group, G = H * K :> set elt -> H * K = H *' K.
Proof. by move=> G H K dG; rewrite smulC_mulgen // -dG -sinvG /inv /= dG sinvMg !sinvG. Qed.

Lemma group_mulgen_eq : forall G H K : group, G = H * K :> set elt -> G = mulgenG_group H K.
Proof.
move=> G H K dG; apply: (can_inj sig_of_groupK); apply: val_inj; rewrite /= valG dG.
exact: group_mulgen dG.
Qed.

End SmulProp.

Hint Resolve group1 groupM groupVr pos_card_group.

Open Scope group_scope.

Section ConjugationSet.

Open Scope group_scope.

Variable elt : finGroupType.
Variable A : set elt.

Lemma mem_conjg : forall (B : set elt) (x y : elt), (B ^ x^-1) y = B (y ^ x).
Proof. by move=> *; rewrite inE invgK. Qed.

Theorem sconj1g : A ^ (1 : elt) = A.
Proof. by apply/setP => x; rewrite inE invg1 conjg1. Qed.

Lemma sconjgM : forall x y : elt, A ^ (x * y) = (A ^ x) ^ y.
Proof. move=> x y; apply/setP => z; rewrite !inE !conjgE; gsimpl. Qed.

Theorem sconjg_conj : forall (B : set elt) (x y : elt),
  (B ^ x) (y ^ x) = B y.
Proof. by move=> B x y; rewrite inE conjgK. Qed.

Lemma sconjMg : forall (B : set elt) (x : elt), (A * B) ^ x = (A ^ x) * (B ^ x).
Proof.
move=> B x; apply/setP=> yz; rewrite inE.
apply/mulsgP/mulsgP=> [] [y z Ay Bz].
  rewrite -{2}(conjgKV x yz) => ->.
  by exists (y ^ x) (z ^ x); rewrite ?sconjg_conj ?conjMg.
by move->; exists (y ^ x^-1) (z ^ x^-1); rewrite -?mem_conjg -?conjMg ?invgK.
Qed.

Lemma sconj_set1 : forall x y : elt, {:x} ^ y = {:x ^ y}.
Proof. by move=> x y; apply/setP => z; rewrite !inE (can2_eq (conjgK y) (conjgKV y)). Qed.

Theorem sconjg_imset : forall x : elt, A ^ x = (fun y : elt => y ^ x) @: A.
Proof.
move=> x; apply/setP=> y; unlock imset; rewrite !inE.
rewrite -{2}(conjgKV x y) image_f ?inE //; exact: conjg_inj.
Qed.

Lemma conjsgE : forall x : elt, A ^ x = x^-1 * A * x.
Proof. by move=> x; apply/setP=> y; rewrite -lcoset_smul -rcoset_smul !inE mulgA. Qed.

Theorem card_sconjg : forall x : elt, card (A ^ x) = card A.
Proof. move=> x; rewrite (sconjg_imset x); apply: card_imset; exact: conjg_inj. Qed.

Variable H : group elt.

Lemma sconjg1 : forall x : elt, (H ^ x) 1.
Proof. by move=> x; rewrite inE conj1g group1. Qed.

Lemma sconjgV : forall x y : elt, (H ^ x) y -> (H ^ x) y^-1.
Proof. move=> x y; rewrite !inE conjVg; exact: groupVr. Qed.

Lemma group_set_sconjg : forall x : elt, group_set (H ^ x).
Proof.
move=> x; rewrite /group_set sconjg1; apply/subsetP=> y.
case/mulsgP=> x1 x2 Hx1 Hx2 -> {z}.
rewrite !inE conjMg in Hx1 Hx2 *; exact: groupM.
Qed.

Canonical Structure group_sconjg x := Group (group_set_sconjg x).

End ConjugationSet.

Section LaGrange.

Variables (elt : finGroupType) (H K : group elt).

Definition subgroup := subset H K.
Hypothesis subset_HK : subgroup.
Let sHK := subsetP subset_HK.

Open Scope generic_scope.
Notation Local "x \in A" := (@s2s elt A x) (at level 65, no associativity).
(* The \in is needed because (H * x) y is interpreteted as (H * x)%type y ! *)

Lemma rcoset_refl : forall x : elt, x \in H * x.
Proof. by move=> x; rewrite -rcoset_smul inE mulgV group1. Qed.

Lemma rcoset_sym : forall x y : elt, y \in H * x = x \in H * y.
Proof. by move=> *; rewrite -!rcoset_smul !inE -groupV !gsimpl. Qed.

Lemma rcoset_trans1 : forall x y : elt, y \in H * x -> H * x = H * y.
Proof.
move=> x y Hxy; apply/setP=> u; rewrite -!rcoset_smul !inE in Hxy *.
by rewrite -(groupMr (u * y^-1) Hxy) !gsimpl.
Qed.

Lemma rcoset_trans : forall x y z : elt, y \in H * x -> z \in H * y -> z \in H * x.
Proof. by move=> x y z; move/rcoset_trans1->. Qed.

Lemma rcoset_trans1r : forall x y : elt,
  y \in H * x -> forall z : elt, x \in H * z = y \in H * z.
Proof. by move=> x y Hxy z; rewrite !(rcoset_sym z) (rcoset_trans1 Hxy). Qed.

Lemma rcoset_id : forall x : elt, x \in H -> H * x = H.
Proof. by move=> x Hx; apply/setP => y; rewrite -rcoset_smul !inE groupMr ?groupV. Qed.

Lemma card_rcoset : forall x : elt, card (H * x) = card H.
Proof.
move=> x; have injx := mulg_injr x; rewrite -(card_image injx H); apply: eq_card => y.
by rewrite -rcoset_smul inE -{2}(mulgKV x y) image_f.
Qed.

Definition rcosets := imset (rcoset H).

Definition indexg K := card (rcosets K).

Definition repr (A : set elt) := if pick A is Some x then x else 1.

Lemma mem_repr : forall x A, s2s A x -> A (repr A).
Proof. by rewrite /repr => x A; case: pickP => [|->]. Qed.

CoInductive rcoset_repr_spec (x : elt) : elt -> Type :=
  RcosetReprSpec y : y \in H -> rcoset_repr_spec x (y * x).

Lemma repr_rcosetP : forall x : elt, rcoset_repr_spec x (repr (H * x)).
Proof.
move=> x; rewrite -[repr _](mulgKV x); split; rewrite -mem_rcoset rcoset_smul.
exact: mem_repr (rcoset_refl x).
Qed.

Theorem LaGrange : card H * indexg K = card K.
Proof.
pose f (x : elt) : prod_finType _ _ := EqPair (x * (repr (H * x))^-1) (H * x).
have inj_f: injective f.
  rewrite /f => x1 x2 [Dy DHx]; move: Dy; rewrite {}DHx; exact: mulg_injr.
rewrite -[_ * _]card_prod_set -{inj_f}(card_imset inj_f); apply: eq_card => [] [y A].
apply/andP/imsetP=> /= [[Hy]|[x Kx [-> ->]]]; last first.
  split; last by apply/imsetP; rewrite -rcoset_smul; exists x.
  case: repr_rcosetP => z Hz; gsimpl; exact: groupVr.
move/imsetP=> [x Kx ->{A}]; case Dz: (repr _) / (repr_rcosetP x) => [z Hz].
exists (y * z * x); first by rewrite groupMr // sHK // groupM.
have Hxyx: y * z * x \in H * x by rewrite -rcoset_smul inE !gsimpl groupM.
by rewrite rcoset_smul /f -(rcoset_trans1 Hxyx) Dz !gsimpl.
Qed.

Lemma group_dvdn : dvdn (card H) (card K).
Proof. by apply/dvdnP; exists (indexg K); rewrite mulnC [(_ * _)%N]LaGrange. Qed.

Lemma group_divn : divn (card K) (card H) = indexg K.
Proof. by rewrite -LaGrange // divn_mulr; auto. Qed.

Lemma lcoset_inv : forall x y : elt, y \in x * H = y^-1 \in H * x^-1.
Proof. by move=> x y; rewrite -lcoset_smul -rcoset_smul !inE -invMg groupV. Qed.

Lemma lcoset_refl : forall x : elt, x \in x * H.
Proof. by move=> x; rewrite -lcoset_smul inE mulVg group1. Qed.

Lemma lcoset_sym : forall x y : elt, y \in x * H = x \in y * H.
Proof. by move=> x y; rewrite 2!lcoset_inv rcoset_sym. Qed.

Lemma lcoset_trans : forall x y z : elt, y \in x * H -> z \in y * H -> z \in x * H.
Proof. move=> x y z; rewrite 3!lcoset_inv; exact: rcoset_trans. Qed.

Lemma lcoset_trans1 : forall x y : elt, y \in x * H -> x * H = y * H.
Proof.
move=> x y Hxy; apply/setP => u; rewrite -!lcoset_smul !inE in Hxy *.
by rewrite -{1}(mulKVg y u) mulgA groupMl.
Qed.

Lemma lcoset_trans1r : forall x y : elt,
  y \in x * H -> forall z : elt, x \in z * H = y \in z * H.
Proof. by move=> x y Hxy z; rewrite 2!(lcoset_sym z) (lcoset_trans1 Hxy). Qed.

Lemma sinvg_lcoset : forall x : elt, (x * H)^-1 = H * x^-1.
Proof. by move=> x; rewrite sinvMg sinvG sinvg_set1. Qed.

Lemma card_lcoset : forall x : elt, card (x * H) = card H.
Proof. by move=> x; rewrite -card_sinvg sinvg_lcoset card_rcoset. Qed.

Definition lcosets := imset (fun x => lcoset x H).

Lemma card_lcosets : card (lcosets K) = indexg K.
Proof.
rewrite -(card_imset (inv_inj (@sinvgK elt))); apply: eq_card => A.
apply/imsetP/imsetP=> [[B dB ->{A}] | [x Hx ->{A}]].
  case/imsetP: dB => x Kx ->{B}.
  by exists x^-1; rewrite ?groupVr // lcoset_smul rcoset_smul sinvg_lcoset.
exists (x^-1 * H); last by rewrite sinvg_lcoset invgK rcoset_smul.
by apply/imsetP; exists x^-1; rewrite ?groupVr // lcoset_smul.
Qed.

End LaGrange.

Section GroupInter.

Open Scope group_scope.

Variable elt : finGroupType.

Section GroupSmulSub.

Variables (H : group elt) (A : set elt).
Hypothesis subAH : subset A H.
Let sAH := subsetP subAH.

Lemma smulsG : forall x, A x -> A * H = H.
Proof.
move=> x Ax; apply/setP; apply/subset_eqP; rewrite -{1}mulGid smulsg //=.
apply/subsetP=> y Ky; apply/mulsgP; exists x (x^-1 * y); gsimpl.
by rewrite groupMl // groupV; auto.
Qed.

Lemma smulGs : forall x, A x -> H * A = H.
Proof.
move=> x Ax; apply/setP; apply/subset_eqP; rewrite -{1}mulGid smulgs //=.
apply/subsetP=> y Ky; apply/mulsgP; exists (y * x^-1) x; gsimpl.
by rewrite groupMr // groupV; auto.
Qed.

Definition smulsG1 := @smulsG 1.
Definition smulGs1 := @smulGs 1.

End GroupSmulSub.

Section GroupSmulSubGroup.

Variables H K : group elt.
Hypothesis subHK : subgroup H K.

Definition smulSG := smulsG subHK (group1 H).
Definition smulGS := smulGs subHK (group1 H).

End GroupSmulSubGroup.

Variables H K : group elt.

Lemma group_set_setI : group_set (H :&: K).
Proof.
apply/group_setP; split=> [|x y]; rewrite !inE ?group1 //.
by move/andP=> [Hx Kx]; rewrite !groupMl.
Qed.

Canonical Structure group_setI := Group group_set_setI.

Lemma card_smulg : card (H * K) * card (H :&: K) = card H * card K.
Proof.
rewrite -(LaGrange (subsetIr H K)) {-2}/mul /= mulnCA mulnC /=; congr muln.
symmetry; rewrite -card_prod_set -card_sub; set tup := prod_set _ _.
pose f (u : sub_finType tup) := let: EqPair x Hy := val u in x * repr Hy.
have injf: injective f.
  rewrite /f => [] [[x1 A1] dom1] [[x2 A2] dom2] /= Ef; apply: val_inj => /=.
  case/andP: dom1 (Ef) => /= Hx1; case/imsetP=> y1 Ky1 dA1.
  case/andP: dom2 => /= Hx2; case/imsetP=> y2 Ky2 dA2.
  suffices ->: A1 = A2 by move/mulg_injr->.
  rewrite {A1}dA1 {A2}dA2 !rcoset_smul in Ef *; have kEf := canRL _ (mulKg _).
  apply: rcoset_trans1 => //; rewrite -rcoset_smul !inE andbC groupM ?groupV //=.
  case: (repr _) / (repr_rcosetP group_setI y1) Ef => z1; case/setIP=> Hz1 _.
  case: (repr _) / (repr_rcosetP group_setI y2) => z2; case/setIP=> Hz2 _.
  by rewrite mulgA; move/kEf->; rewrite invMg invgK !invMg -!mulgA mulKVg !groupMl ?groupV.
rewrite -(card_codom injf); apply: eq_card => z.
apply/set0Pn/mulsgP=> [|[x y Hx Ky ->{z}]]; rewrite /f /preim.
  case=> [[[x A]]] /=; case/andP=> /= Hx; case/imsetP=> y Ky -> {A}; move/eqP=> ->{z}.
  rewrite rcoset_smul; case: (repr _) / (repr_rcosetP group_setI y) => z; case/setIP=> _ Kz.
  by exists x (z * y); last 2 [exact: groupM].
case Dz: (repr _) / (repr_rcosetP group_setI y) => [z HKz]; case/setIP: HKz => Hz Kz.
have Tu: tup (EqPair (x * z^-1) ((H :&: K) * y)).
  by rewrite /tup /prod_set /= groupMl ?groupVr // -rcoset_smul; apply/imsetP; exists y.
by exists (EqSig tup _ Tu); apply/eqP; rewrite /= Dz !gsimpl.
Qed.

Definition trivg (A : set elt) := subset A (1 : set elt).

Lemma trivgP : forall G : group elt, reflect (G = 1 :> set _) (trivg G).
Proof.
move=> G; apply: (iffP idP) => [tG | ->]; last exact: subset_refl.
by apply/setP; apply/subset_eqP; rewrite andbC sub1set group1.
Qed.

Definition disjointg := trivg (H :&: K).

Lemma disjointgP : reflect (H :&: K = 1) disjointg.
Proof. exact: trivgP. Qed.

Lemma disjointg_card : disjointg = (card (H :&: K) == 1).
Proof.
apply/disjointgP/eqP=> [->|cHK]; first by rewrite cards1.
symmetry; apply/setP; apply/subset_cardP; first by rewrite cards1.
apply/subsetP=> x; rewrite inE; move/eqP <-; exact: group1.
Qed.

Lemma group_modularity : forall G, subgroup G K -> G * (H :&: K) = G * H :&: K.
Proof.
move=> G; move/subsetP=> sGK; apply/setP => x.
apply/mulsgP/idP=> [[y z Gy]|]; rewrite inE; case/andP.
  move=> Hz Kz -> {x}; rewrite inE andbC groupMr // sGK //.
  by apply/mulsgP; exists y z.
move/mulsgP=> [y z Gy Hz -> {x}] Kyz.
by exists y z => //; rewrite inE Hz; rewrite groupMl // sGK in Kyz.
Qed.

Lemma disjoint_card_smulg : disjointg -> card (H * K) = card H * card K.
Proof. by rewrite disjointg_card => HK1; rewrite -card_smulg (eqP HK1) [_ * 1]muln1. Qed.

End GroupInter.

Section Normalizer.

Open Scope group_scope.

Variable elt : finGroupType.

Section NormSet.

Variable A : set elt.

Definition normaliser := {x : elt, subset (A ^ x) A}.

Theorem norm_sconjg : forall x, normaliser x -> A ^ x = A.
Proof.
by move=> x Ax; apply/setP; apply/subset_cardP; [rewrite card_sconjg | rewrite inE in Ax].
Qed.

Theorem group_set_normaliser : group_set normaliser.
Proof.
apply/group_setP; split=> [|x y Nx Ny]; first by rewrite inE sconj1g subset_refl.
by rewrite inE; apply/subsetP => z; rewrite sconjgM !norm_sconjg.
Qed.

Canonical Structure group_normaliser := Group group_set_normaliser.

Definition normalized (B : set elt) := subset B normaliser.

Lemma norm_smulC : forall B, normalized B -> A * B = B * A.
Proof.
move=> B; move/subsetP=> nB; apply/setP => u.
apply/mulsgP/mulsgP=> [[x y Ax By] | [y x By Ax]] -> {u}; have dAy := norm_sconjg (nB _ By).
- by exists y (x ^ y); last rewrite /exp /=; gsimpl; rewrite -dAy inE conjgK.
by exists (x ^ y^-1) y; last rewrite /exp /=; gsimpl; rewrite -mem_conjg invgK dAy.
Qed.

Lemma norm_mulgenr : forall B, normalized B -> A * B = A *' B.
Proof. by move=> B; move/norm_smulC; exact: smulC_mulgen. Qed.

Lemma norm_mulgenl : forall B, normalized B -> B * A = A *' B.
Proof. by move=> B; move/norm_smulC=> dBA; rewrite -dBA; exact: smulC_mulgen. Qed.

End NormSet.

Variable H : group elt.
Notation N := (normaliser H).

Theorem norm_refl : subset H N.
Proof.
apply/subsetP=> x Hx; rewrite inE; apply/subsetP => y.
by rewrite inE /exp /= invgK groupMr ?groupMl ?groupV.
Qed.

Lemma norm_rcoset : forall x, N x -> subset (H * x) N.
Proof.
move=> x Nx; rewrite -[N]mulGid /=.
by apply: subset_trans (smulsg _ norm_refl); apply: smulgs; rewrite sub1set.
Qed.

End Normalizer.

Open Scope group_scope.

Lemma norm_rcoset_lcoset :
  forall elt (H : group elt) x, normaliser H x -> H * x = x * H.
Proof. move=> elt H x; rewrite -sub1set; exact: norm_smulC. Qed.

Unset Implicit Arguments.

