(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice div.
Require Import fintype bigops finset prime groups ssralg finalg.

(***********************************************************************)
(*  Definition of the additive group and ring Zp, represented as 'I_p  *)
(***********************************************************************)
(* Definitions:                                                        *)
(* From fintype.v:                                                     *)
(*   'I_p == the subtype of integers less than p, taken here as the    *)
(*           type of integers mod p.                                   *)
(* This file:                                                          *)
(*   inZp == the natural projection from nat into the integers mod p,  *)
(*           represented as 'I_p. Here p is implicit, but MUST be of   *)
(*           of the form n.+1.                                         *)
(* The operations:                                                     *)
(*   Zp0 == the identity element for addition                          *)
(*   Zp1 == the identity element for multiplication, and a generator   *)
(*          of the additive group                                      *)
(*   Zp_opp == inverse function for addition                           *)
(*   Zp_add == addition                                                *)
(*   Zp_mul == multiplication                                          *)
(*   Zp_inv == inverse function for multiplication                     *)
(* Note that while 'I_n.+1 has canonical finZmodType and finGroupType  *)
(* structures, only 'I_n.+2 has a canonical ring structure (it has, in *)
(* fact, a canonical finComUnitRing structure), and hence an           *)
(* associated multiplicative unit finGroupType. To mitigate the issues *)
(* cause by the trivial "ring" (which is, indeed is NOT a ring in the  *)
(* ssralg/finalg formalization), we define additional notation:        *)
(*        'Z_p == the type of integers mod (max p 2); this is always a *)
(*                proper ring, by constructions. Note that 'Z_p is     *)
(*                provably equal to 'I_p if p > 1, and convertible to  *)
(*                'I_p if p is of the form n.+2.                       *)
(*        Zp p == the subgroup of integers mod (max p 1) in 'Z_p; this *)
(*                is thus all of 'Z_p if p > 1, and the trivial group  *)
(*                otherwise.                                           *)
(*  units_Zp p == the group of all units of 'Z_p -- i.e., the group of *)
(*                (multiplicative) automorphisms of Zp p.              *)
(* We show that Zp and units_Zp are abelian, and compute their orders. *)
(* We use a similar technique to represent the prime fields:           *)
(*        'F_p == the finite field of integers mod the first prime     *)
(*                divisor of max p 2. This is provably equal to 'Z_p   *)
(*                and 'I_p is p is provably prime, and indeed          *)
(*                convertible to the above if p is a concrete prime    *)
(*                such as 2, 5 or 23.                                  *)
(* Note finally that due to the canonical structures it is possible to *)
(* use 0%R instead of Zp0, and 1%R instead of Zp1 (for the latter, p   *)
(* must be of the form n.+2, and 1%R : nat will simplify to 1%N).      *)
(***********************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section ZpDef.

(***********************************************************************)
(*                                                                     *)
(*  Mod p arithmetic on the finite set {0, 1, 2, ..., p - 1}           *)
(*                                                                     *)
(***********************************************************************)

Variable p' : nat.
Local Notation p := p'.+1.

Implicit Types x y z : 'I_p.

(* Standard injection; val (inZp i) = i %% p *)
Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).
Lemma modZp : forall x, x %% p = x.
Proof. by move=> x; rewrite modn_small ?ltn_ord. Qed.
Lemma valZpK : forall x, inZp x = x.
Proof. by move=> x; apply: val_inj; rewrite /= modZp. Qed.

(* Operations *)
Definition Zp0 : 'I_p := ord0.
Definition Zp1 := inZp 1.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).
Definition Zp_mul x y := inZp (x * y).
Definition Zp_inv x := if coprime p x then inZp (egcdn x p).1 else x.

(* Additive group structure. *)

Lemma Zp_add0z : left_id Zp0 Zp_add.
Proof. exact: valZpK. Qed.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Proof.
by move=> x; apply: val_inj; rewrite /= modn_addml subnK ?modnn // ltnW.
Qed.

Lemma Zp_addA : associative Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_addml modn_addmr addnA.
Qed.

Lemma Zp_addC : commutative Zp_add.
Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
Canonical Structure Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.
Canonical Structure Zp_finZmodType := Eval hnf in [finZmodType of 'I_p].
Canonical Structure Zp_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of 'I_p for +%R].
Canonical Structure Zp_finGroupType :=
  Eval hnf in [finGroupType of 'I_p for +%R].

(* Ring operations *)

Lemma Zp_mul1z : left_id Zp1 Zp_mul.
Proof. by move=> x; apply: val_inj; rewrite /= modn_mulml mul1n modZp. Qed.

Lemma Zp_mulC : commutative Zp_mul.
Proof. by move=> x y; apply: val_inj; rewrite /= mulnC. Qed.

Lemma Zp_mulz1 : right_id Zp1 Zp_mul.
Proof. by move=> x; rewrite Zp_mulC Zp_mul1z. Qed.

Lemma Zp_mulA : associative Zp_mul.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_mulml modn_mulmr mulnA.
Qed.

Lemma Zp_mul_addr : right_distributive Zp_mul Zp_add.
Proof.
by move=> x y z; apply: val_inj; rewrite /= modn_mulmr modn_add2m muln_addr.
Qed.

Lemma Zp_mul_addl : left_distributive Zp_mul Zp_add.
Proof. by move=> x y z; rewrite -!(Zp_mulC z) Zp_mul_addr. Qed.

Lemma Zp_mulVz : forall x, coprime p x -> Zp_mul (Zp_inv x) x = Zp1.
Proof.
move=> x co_p_x; apply: val_inj; rewrite /Zp_inv co_p_x /= modn_mulml.
by rewrite -(chinese_modl co_p_x 1 0) /chinese addn0 mul1n mulnC.
Qed.

Lemma Zp_mulzV : forall x, coprime p x -> Zp_mul x (Zp_inv x) = Zp1.
Proof. by move=> x Ux; rewrite /= Zp_mulC Zp_mulVz. Qed.

Lemma Zp_intro_unit : forall x y, Zp_mul y x = Zp1 -> coprime p x.
Proof.
move=> x y [yx1]; have:= coprimen1 p.
by rewrite -coprime_modr -yx1 coprime_modr coprime_mulr; case/andP.
Qed.

Lemma Zp_inv_out : forall x, ~~ coprime p x -> Zp_inv x = x.
Proof. by rewrite /Zp_inv => x; move/negPf->. Qed.

Lemma Zp_mulrn : forall x n, x *+ n = inZp (x * n).
Proof.
move=> x n; apply: val_inj => /=.
elim: n => [|n IHn]; first by rewrite muln0 modn_small.
by rewrite !GRing.mulrS /= IHn modn_addmr mulnS.
Qed.

Import GroupScope.

Lemma Zp_mulgC : @commutative 'I_p _ mulg.
Proof. exact: Zp_addC. Qed.

Lemma Zp_abelian : abelian [set: 'I_p].
Proof. exact: FinRing.zmod_abelian. Qed.

Lemma Zp_expgn : forall x n, x ^+ n = inZp (x * n).
Proof. exact: Zp_mulrn. Qed.

Lemma Zp1_expgz : forall x, Zp1 ^+ x = x.
Proof. move=> x; rewrite Zp_expgn; exact: Zp_mul1z. Qed.

Lemma Zp_cycle : setT = <[Zp1]>.
Proof. by apply/setP=> x; rewrite -[x]Zp1_expgz inE groupX ?mem_gen ?set11. Qed.

End ZpDef.

Implicit Arguments Zp0 [[p']].
Implicit Arguments Zp1 [[p']].
Implicit Arguments inZp [[p']].

Lemma ord1 : all_equal_to (0 : 'I_1).
Proof. by case=> [[] // ?]; exact: val_inj. Qed.

Lemma lshift0 : forall m n, lshift m (0 : 'I_n.+1) = (0 : 'I_(n + m).+1).
Proof. move=> m n; exact: val_inj. Qed.

Lemma rshift1 : forall n, @rshift 1 n =1 lift (0 : 'I_n.+1).
Proof. by move=> n i; apply: val_inj. Qed.

Lemma split1 : forall n i,
  split (i : 'I_(1 + n)) = oapp (@inr _ _) (inl _ 0) (unlift 0 i).
Proof.
move=> n i; case: unliftP => [i'|] -> /=.
  by rewrite -rshift1 (unsplitK (inr _ _)).
by rewrite -(lshift0 n 0) (unsplitK (inl _ _)).
Qed.

Lemma big_ord1 : forall R idx (op : @Monoid.law R idx) F,
  \big[op/idx]_(i < 1) F i = F 0.
Proof. by move=> R idx op F; rewrite big_ord_recl big_ord0 Monoid.mulm1. Qed.

Lemma big_ord1_cond : forall R idx (op : @Monoid.law R idx) P F,
  \big[op/idx]_(i < 1 | P i) F i = if P 0 then F 0 else idx.
Proof. by move=> R idx op P F; rewrite big_mkcond big_ord1. Qed.

Section ZpRing.

Variable p' : nat.
Local Notation p := p'.+2.

Lemma Zp_nontrivial : Zp1 != 0 :> 'I_p. Proof. by []. Qed.

Definition Zp_ringMixin :=
  ComRingMixin (@Zp_mulA _) (@Zp_mulC _) (@Zp_mul1z _) (@Zp_mul_addl _)
               Zp_nontrivial.
Canonical Structure Zp_ringType := Eval hnf in RingType 'I_p Zp_ringMixin.
Canonical Structure Zp_finRingType := Eval hnf in [finRingType of 'I_p].
Canonical Structure Zp_comRingType := Eval hnf in ComRingType 'I_p (@Zp_mulC _).
Canonical Structure Zp_finComRingType := Eval hnf in [finComRingType of 'I_p].

Definition Zp_unitRingMixin :=
  ComUnitRingMixin (@Zp_mulVz _) (@Zp_intro_unit _) (@Zp_inv_out _).
Canonical Structure Zp_unitRingType :=
  Eval hnf in UnitRingType 'I_p Zp_unitRingMixin.
Canonical Structure Zp_finUnitRingType := Eval hnf in [finUnitRingType of 'I_p].
Canonical Structure Zp_comUnitRingType := Eval hnf in [comUnitRingType of 'I_p].
Canonical Structure Zp_finComUnitRingType :=
  Eval hnf in [finComUnitRingType of 'I_p].

Lemma Zp_nat : forall n, n%:R = inZp n :> 'I_p.
Proof.
by move=> n; apply: val_inj; rewrite [n%:R]Zp_mulrn /= modn_mulml mul1n.
Qed.

Lemma natr_Zp : forall x : 'I_p, x%:R = x.
Proof. by move=> x; rewrite Zp_nat valZpK. Qed.

Import GroupScope.

Lemma unit_Zp_mulgC : @commutative {unit 'I_p} _ mulg.
Proof. by move=> u v; apply: val_inj; rewrite /= GRing.mulrC. Qed.

Lemma unit_Zp_expgn : forall (u : {unit 'I_p}) n,
  val (u ^+ n) = inZp (val u ^ n) :> 'I_p.
Proof.
move=> u n; apply: val_inj => /=; elim: n => [|n IHn] //.
by rewrite expgS /= IHn expnS modn_mulmr.
Qed.

End ZpRing.

Definition Zp_trunc p := p.-2.

Notation "''Z_' p" := 'I_(Zp_trunc p).+2
  (at level 8, p at level 2, format "''Z_' p") : type_scope.
Notation "''F_' p" := 'Z_(pdiv p)
  (at level 8, p at level 2, format "''F_' p") : type_scope.

Section Groups.

Variable p : nat.

Definition Zp := if p > 1 then [set: 'Z_p] else 1%g.
Definition units_Zp := [set: {unit 'Z_p}].

Lemma Zp_cast : p > 1 -> (Zp_trunc p).+2 = p.
Proof. by case: p => [|[]]. Qed.

Lemma val_Zp_nat : p > 1 -> forall n, (n%:R : 'Z_p) = (n %% p)%N :> nat.
Proof. by move=> p_gt1 n; rewrite Zp_nat /= Zp_cast. Qed.

Lemma Zp_nat_mod : p > 1 -> forall m, (m %% p)%:R = m%:R :> 'Z_p.
Proof. by move=> p_gt1 m; apply: ord_inj; rewrite !val_Zp_nat // modn_mod. Qed.

Lemma char_Zp : p > 1 -> p%:R = 0 :> 'Z_p.
Proof. by move=> p_gt1; rewrite -Zp_nat_mod ?modnn. Qed.

Lemma Zp_group_set : group_set Zp.
Proof. rewrite /Zp; case: (p > 1); exact: groupP. Qed.
Canonical Structure Zp_group := Group Zp_group_set.

Lemma card_Zp : p > 0 -> #|Zp| = p.
Proof.
rewrite /Zp; case: p => [|[|p']] //= _; first by rewrite cards1.
by rewrite cardsT card_ord.
Qed.

Canonical Structure units_Zp_group := [group of units_Zp].

Lemma card_units_Zp : p > 0 -> #|units_Zp| = phi p.
Proof.
move=> p_gt0; transitivity (phi p.-2.+2); last by case: p p_gt0 => [|[|p']].
by rewrite cardsT card_sub phi_count_coprime big_mkord -sum1_card.
Qed.

Lemma units_Zp_abelian : abelian units_Zp.
Proof. apply/centsP=> u _ v _; exact: unit_Zp_mulgC. Qed.

End Groups.

(* Field structure for primes. *)

Section PrimeField.

Open Scope ring_scope.

Variable p : nat.

Section F_prime.

Hypothesis p_pr : prime p.

Lemma Fp_Zcast : (Zp_trunc (pdiv p)).+2 = (Zp_trunc p).+2.
Proof. by rewrite /pdiv primes_prime. Qed.

Lemma Fp_cast : (Zp_trunc (pdiv p)).+2 = p.
Proof. by rewrite Fp_Zcast ?Zp_cast ?prime_gt1. Qed.

Lemma card_Fp : #|'F_p| = p.
Proof. by rewrite card_ord Fp_cast. Qed.

Lemma val_Fp_nat : forall n, (n%:R : 'F_p) = (n %% p)%N :> nat.
Proof. by move=> n; rewrite Zp_nat /= Fp_cast. Qed.

Lemma Fp_nat_mod : forall m, (m %% p)%:R = m%:R :> 'F_p.
Proof. by move=> m; apply: ord_inj; rewrite !val_Fp_nat // modn_mod. Qed.

Lemma char_Fp : p \in [char 'F_p].
Proof. by rewrite !inE -Fp_nat_mod p_pr ?modnn. Qed.

Lemma char_Fp_0 : p%:R = 0 :> 'F_p.
Proof. exact: GRing.charf0 char_Fp. Qed.

End F_prime.

Lemma Fp_fieldMixin : GRing.Field.mixin_of [the unitRingType of 'F_p].
Proof.
move=> x nzx; rewrite /GRing.unit /= prime_coprime ?gtnNdvd ?lt0n //.
case: (ltnP 1 p) => [lt1p | ]; last by case: p => [|[|p']].
by rewrite Zp_cast ?prime_gt1 ?pdiv_prime.
Qed.

Definition Fp_idomainMixin := FieldIdomainMixin Fp_fieldMixin.

Canonical Structure Fp_idomainType :=
   Eval hnf in IdomainType 'F_p  Fp_idomainMixin.
Canonical Structure Fp_finIdomainType := Eval hnf in [finIdomainType of 'F_p].
Canonical Structure Fp_fieldType := Eval hnf in FieldType 'F_p Fp_fieldMixin.
Canonical Structure Fp_finFieldType := Eval hnf in [finFieldType of 'F_p].
Canonical Structure Fp_decFieldType :=
  Eval hnf in [decFieldType of 'F_p for Fp_finFieldType].

End PrimeField.
