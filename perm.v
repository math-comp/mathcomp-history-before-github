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
Require Import groups.
Require Import div.
Require Import zp.
Require Import action.
Require Import cyclic.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Perm.

Open Scope group_scope.

Variable (G : finGroup) (H : set G).

Hypothesis subgrp_H: subgrp H.

Fixpoint prodn (n: nat): finType :=
  if n is S n1 then (prod_finType (sub_finType H) (prodn n1)) 
 else (sub_finType H).

Fixpoint prodn_id (n:nat) (e : G) (He: H e) {struct n}: (prodn n) :=
  match n return (prodn n) with
    S n1 => EqPair (EqSig _ _ He) (prodn_id n1 He)
  | _ => EqSig _ _ He
  end.

Lemma prodn_id_irr: forall n e1 e2 (He1: H e1) (He2: H e2),
 e1 = e2 -> prodn_id n He1 = prodn_id n He2.
Proof.
elim => [|n Rec] //= e1 e2 He1 He2 H1.
  by apply val_inj.
congr EqPair; last exact: Rec.
by apply/val_eqP => //=; rewrite H1.
Qed.

Lemma card_prodn: forall n, card (prodn n) = (card H ^ (S n))%N.
Proof.
elim => [| n Hrec] //=.
  by rewrite muln1 card_setA_sub.
by rewrite (card_setA_prod (sub_finType H)) //= card_setA_sub Hrec.
Qed.

Fixpoint prod_prodn (n : nat) : prodn n -> G :=
  match n return (prodn n -> G) with
  | O => fun l => (val l)
  | S n1 =>
      fun v  =>
      match v with
      | EqPair x y => (val x) * prod_prodn y
      end
  end.

Lemma prod_prodn_h: forall n (p: prodn n),
  H (prod_prodn p).
Proof.
elim => [| Hn Hrec] //=.
  by move => [p Hp].
move => [[p Hp] p1].
by apply: subgrpM => //.
Qed.

Lemma prod_prodn_h_1: forall n (p: prodn n),
  H (prod_prodn p)^-1.
Proof.
move => n p; apply: subgrpV => //.
apply: prod_prodn_h.
Qed.

Lemma prod_prodn_id: forall n e (He: H e),
  prod_prodn (prodn_id n He) = e ^ (S n).
Proof.
elim => [|n Rec] //= e He.
  by rewrite mulg1.
by rewrite Rec.
Qed.

Fixpoint elt_prodn (k n : nat) {struct n}:  prodn n -> G :=
  match n return (prodn n -> G) with
  | O => fun v => (val v)
  | S n1 =>
      fun v => let (x, y) := v in
               if k is S k1 then elt_prodn k1 y else (val x)
  end.

Lemma elt_correct: forall n (p1 p2: prodn n),
 (forall k, k <= n -> elt_prodn k p1 = elt_prodn k p2) ->
 p1 = p2.
Proof.
elim => [|m Rec] //=.
  move => p1 p2 H1.
  apply/eqP; rewrite -val_eqE; apply/eqP.
  by apply (H1 0).
move => [x1 y1] [x2 y2] H1.
congr EqPair.
  apply/eqP; rewrite -val_eqE; apply/eqP.
  by apply: (H1 0).
by apply Rec => k Hk; apply: (H1 (S k)).
Qed.

Definition add_inv n: prodn n -> prodn (S n) :=
 fun x => (EqPair (EqSig _ _ (prod_prodn_h_1 x)) x).

Definition rm_inv n: prodn (S n) -> prodn n :=
 fun x => match x with EqPair _ y => y end.

Lemma prod_add_inv: forall n (p: prodn n), prod_prodn (add_inv p) = 1.
Proof.
by case => [| n] //=; [move => p | move => [x y]]; rewrite mulVg.
Qed.

Lemma rm_add_inv : forall (n: nat), cancel (@add_inv n) (@rm_inv n).
Proof.
by done.
Qed.

Lemma add_inv_inj : forall n, injective (@add_inv n).
Proof.
Proof. move=> n; exact: can_inj (@rm_add_inv n). Qed.

Definition permSet (n: nat) := (sub_finType (codom (@add_inv n))).

Definition permSet1 n : (permSet n).
move => n; exists (prodn_id (S n) (subgrp1 subgrp_H)).
replace (prodn_id (S n) (subgrp1 subgrp_H)) with (add_inv (prodn_id n (subgrp1 subgrp_H))).
  by apply codom_f.
rewrite //= /add_inv; congr EqPair.
apply/val_eqP; apply/eqP => //=.
by rewrite prod_prodn_id gexp1n invg1.
Defined.

Lemma card_permSet: forall n, card (permSet n) = (card H ^ (S n))%N.
Proof.
move => n; rewrite /permSet /=.
apply: (etrans  (card_setA_sub _)).
apply: (etrans (card_codom (@add_inv_inj n))).
by rewrite card_prodn.
Qed.

Let zp (n:nat): Group.finite:= @zp_group (S (S n)) is_true_true.

Fixpoint add_end (n : nat) :  sub_finType H -> prodn n -> prodn (S n) :=
  match n return sub_finType H -> prodn n -> prodn (S n) with
  | O => fun v1 v2 : sub_finType H => EqPair v2 v1
  | S n1 =>
      fun v1 H =>
      match H with
      | EqPair x y => EqPair x (add_end v1 y)
      end
  end.

Lemma add_end_id: forall n e p,
  (EqPair e p) = (add_end e p) -> (EqPair e p) = (prodn_id (S n) (valP e)).
Proof.
elim => [| n Rec] //=.
  move => e p H0; injection H0; move => H1 H2; rewrite H1.
  by congr EqPair; apply/val_eqP.
move => e [e1 p1] [H1] [H2]; congr EqPair.
  by apply/val_eqP. 
by subst; apply: Rec.
Qed.

Lemma add_end_id_rev: forall n e,
  (add_end e (prodn_id n (valP e))) = (prodn_id (S n) (valP e)).
Proof.
elim => [| n Rec] //= e.
  by congr EqPair; apply/val_eqP.
by congr EqPair; rewrite Rec.
Qed.

Lemma prod_add_end: forall n v (p: prodn n),
  prod_prodn (add_end v p) =   prod_prodn p * (val v).
Proof.
by elim => [| n Rec] //= v [x y]; rewrite -mulgA -Rec.
Qed.

Lemma elt_add_end_n:
 forall n v (p: prodn n), elt_prodn (S n) (add_end v p) = (val v).
Proof.
elim => [|m Rec] //= v [x y].
by case: (add_end v y) (Rec v y).
Qed.

Lemma elt_add_end_k:
 forall n k v (p: prodn n), k <= n ->  
   elt_prodn k (add_end v p) = elt_prodn k p.
Proof.
elim => [|n Rec] //=.
  by case.
case; first by move => v [x y].
move => k v [x y].
case: k; first by case: n {Rec}y => //= n [x1 y].
by move => k Hk; case: (add_end v y) (Rec (S k) v y Hk).
Qed.

Definition permute1 n: prodn n -> prodn n :=
match n return (prodn n -> prodn n) with
| O => fun v => v
| S n1 =>
    fun H =>
    match H with
    | EqPair x y => add_end x y
    end
end.

Lemma permute1_id: forall n p,
  permute1 p = p -> exists e:sub_finType H, p = prodn_id n (valP e).
Proof.
case => [| n] //=.
 by move => p _; exists p; apply/val_eqP.
move => [e p1] H1; exists e.
by apply: add_end_id.
Qed.

Lemma permute1_id_rev: forall n e (He: H e),
  permute1 (prodn_id n He) = prodn_id n He.
Proof.
case => [| n] //=.
by move => e He; exact: (add_end_id_rev n (EqSig _ _ He)).
Qed.

Lemma prod_permute1: forall n (p: prodn n),
  prod_prodn p = 1 ->  prod_prodn (permute1 p) = 1.
Proof.
case; first by done.
simpl prodn; simpl permute1; move => n [x y].
rewrite prod_add_end => //= H1.
apply: (mulg_injr (val x)^-1); apply: (mulg_injl (val x)).
by rewrite mul1g -mulgA !mulgV mulg1.
Qed.

Lemma elt_add_permute1:
 forall n K (p: prodn n), K <= n ->  
   elt_prodn K (permute1 p) = elt_prodn (modn (K + (S 0)) (S n))  p.
Proof.
case.
  by done.
simpl prodn; move => n K [x y]; rewrite /permute1.
rewrite leq_eqVlt; move/orP => [H1 | H1].
  by rewrite (eqP H1) elt_add_end_n addn1 modnn.
rewrite modn_small; last by rewrite addn1.
by rewrite elt_add_end_k // addn1.
Qed.

Fixpoint permute (n k: nat) (p: prodn n) {struct k}: prodn n :=
 if k is S k1 then permute1 (permute k1 p) else p.

Lemma permute_id1: forall n p,
  permute 1%N p = p -> exists e: sub_finType H, p = prodn_id n (valP e).
Proof.
move => n p //=; exact: permute1_id.
Qed.

Lemma permute_id_rev: forall n K e (He: H e),
  permute K (prodn_id n He) = prodn_id n He.
Proof.
move => n; elim => [| K Rec] //=.
by move => e He; rewrite Rec permute1_id_rev.
Qed.

Lemma elt_add_permute:
 forall n k1 k2 (p: prodn n), k1 <= n ->  
   elt_prodn k1 (permute k2 p) = elt_prodn (modn (k1 + k2) (S n))  p.
Proof.
move => n k1 k2 p Hk1; elim: k2 k1 Hk1 => [|k2 Rec] k1 Hk1 //=.
  by rewrite addn0 modn_small.
rewrite elt_add_permute1 // Rec.
 by rewrite -(addSnnS _ k2) addn1 -modn_add modn_modn -(modn_add (S k1)).
by rewrite -ltnS modn_lt.
Qed.

Lemma permutenn: forall n (p: prodn n), permute (S n) p = p.
Proof.
move => n p; apply elt_correct => K Hk.
by rewrite elt_add_permute // addnC modn_add_one // modn_small.
Qed.

Lemma prod_permute: forall k n (p: prodn n),
  prod_prodn p = 1 ->  prod_prodn (permute k p) = 1.
Proof.
by elim => //= k Rec n p H1; apply: prod_permute1; apply Rec.
Qed.

Lemma in_codom: forall n p,
  prod_prodn p = 1 ->  (codom (@add_inv n) p).
Proof.
simpl prodn; move => n [x y]; simpl prod_prodn => H1.
replace (EqPair x y) with (add_inv y).
rewrite codom_f //=.
rewrite /add_inv; congr EqPair.
apply/val_eqP => //=; apply/eqP.
apply: (mulg_injr (prod_prodn y)).
by rewrite mulVg H1.
Qed.

Definition permute_zp (n: nat) (k: zp n): permSet n -> permSet n.
intros n (k, Hk) (u, Hu).
apply: (@EqSig _ (codom (@add_inv n)) (permute k u)).
apply: in_codom; apply prod_permute.
rewrite -(f_iinv Hu).
apply prod_add_inv.
Defined.

Definition zp1 n : zp n.
by intros n; exists 1%N.
Defined.

Lemma permute_zp_id: forall n p,
  permute_zp (zp1 n) p = p -> exists e: sub_finType H, 
      val p = prodn_id (S n) (valP e).
Proof.
move => n [p1 Hp1] H1; apply: permute_id1.
move: H1; rewrite /permute_zp /zp1; move/eqP.
rewrite  -(@val_eqE _ (codom (@add_inv n))) => //= H1.
by rewrite (eqP H1).
Qed.

Lemma permute_zp_morph: forall n k1 k2 (p: permSet n),
  permute_zp (k1 * k2) p = permute_zp k1 (permute_zp k2 p). Proof.

move => n [k1 Hk1] [k2 Hk2] [p Hp] //=.
apply/eqP; rewrite -val_eqE //=.
apply/eqP; apply: (@elt_correct (S n)) => K Hk.
rewrite !elt_add_permute //.
    rewrite -modn_add modn_modn modn_add.
    by rewrite -[modn (_ + k2) _]modn_add modn_modn modn_add addnA.
by rewrite -ltnS modn_lt.
Qed.

Lemma permute_zp_1: forall n (p: permSet n),
  permute_zp 1 p = p.
Proof.
move => n [p Hp] //=.
by apply/eqP; rewrite -val_eqE //=; apply/eqP.
Qed.

Lemma permute_zp_bij: forall n (k: zp n), bijective (permute_zp k).
Proof.
by move => n k; exists (permute_zp (k^-1)) => x; rewrite -permute_zp_morph;
    rewrite ?mulgV ?mulVg permute_zp_1.
Qed.

Definition stab n := S0 (zp n) (@permute_zp n).

Lemma stab1: forall n, stab (permSet1 n).
Proof.
move => n; apply/subsetP; case => x Hx H1.
rewrite /stabiliser /permute_zp /permSet1.
apply/andP; split => //.
rewrite -(@val_eqE _ (codom (@add_inv n))) => //=.
by apply/eqP; move: (permute_id_rev (S n) x (subgrp1 subgrp_H)).
Qed.

Lemma stab_in: forall n p,
  stab p -> exists e: sub_finType H,
   (val p) = prodn_id (S n) (valP e).
Proof.
move => n p H0.
have F1: stabiliser (zp n) (@permute_zp n) p (zp1 n).
  move: H0; rewrite /stab /S0; move/subsetP.
  by move => H1; apply: H1.
apply: permute_zp_id.
move/andP: F1 => [H1 H2].
by apply/eqP.
Qed.

Lemma stab_gexpn: forall n (p: permSet n),
  stab p -> exists e: sub_finType H, ((val e) ^ (S (S n))) = 1.
Proof.
move => n [p Hp] H0; case: (stab_in H0).
move => e H1; exists e.
rewrite -(prod_prodn_id (S n) (valP e)) -H1.
by rewrite /val -(f_iinv Hp) prod_add_inv.
Qed.

End Perm.

Unset Implicit Arguments.
