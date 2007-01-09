(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of the power set                                       *)
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
Require Import div.

Section PowerSeq.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable d: eqType.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the power sequence                                   *)
(*                                                                     *)
(***********************************************************************)

Fixpoint powerSeq (s: seq d) : seq (seq_eqType d) :=
  if s is (Adds a s1) then
     let r := powerSeq s1 in
     cat (maps (Adds a) r) r
  else (Adds (Seq0 _) (Seq0 _)).

Lemma powerSeq_size: forall s, size (powerSeq s) = 2 ^ (size s).
Proof.
elim => [|a s Rec] //=.
by rewrite size_cat size_maps Rec addn0.
Qed.

Lemma powerSeq_subset: forall s x, 
  powerSeq s x -> sub_set x s.
Proof.
Proof.
elim => [|a s Rec] /=.
  by move => x; rewrite /setU1; case x => //=; move => H y.
move => x; rewrite mem_cat; move/orP => [H1 | H1] y.
  move/mapsP: H1 => [x1 H1 H2]; rewrite -H2 //=.
  move/setU1P => [H3 | H3].
    by rewrite /setU1 H3 eq_refl orTb.
  by rewrite /setU1 (Rec _ H1 _ H3) orbT.
by move => H; rewrite /setU1 (Rec _ H1 _ H) orbT.
Qed.

Lemma powerSeq_uniq_eq: forall s x, 
  uniq s -> powerSeq s x -> x = filter x s.
Proof.
elim => [| a s Rec] /=; first by case.
move => x; rewrite mem_cat.
move/andP => [HH1 HH2].
move/orP => [H | H].
  move/mapsP: H => [y Hy] Hy1.
  rewrite -Hy1 //= setU11; congr Adds.
  rewrite {1}(Rec y) //.
  elim: s {HH2 Rec Hy}HH1 => [|a1 s Rec] //=.
  rewrite {1 2}/setU1 negb_orb; move/andP => [H H1].
  by rewrite eq_sym (negbET H) //= -Rec. 
case Eq1: (mem x a); last by apply: Rec.
case/negP: HH1.
by exact: (powerSeq_subset H).
Qed.

Lemma powerSeq_uniq: forall s, uniq s -> uniq (powerSeq s).
Proof.
elim => [|a s Rec] //=.
move/andP => [H1 H2].
have F1 := (Rec H2).
rewrite uniq_cat; apply/and3P; repeat split => //.
  rewrite uniq_maps //.
  by move => x y H; injection H.
apply/negP; move/hasP => [x Hx1 Hx2].
move/mapsP: Hx2 =>[y Hx2 Hx3].
case/negP: H1; apply: (powerSeq_subset Hx1).
by rewrite -Hx3 /= setU11.
Qed.

Lemma powerSeq_mem: forall s h, powerSeq s (filter h s).
Proof.
elim => [|a s Rec h] //=.
case Ha: (h a).
rewrite mem_cat /setU maps_f //.
by rewrite mem_cat /setU /id Rec orbT.
Qed.

End PowerSeq.

Section UniqueListSet.

Variable (d: eqType) (l: seq d).
Hypothesis l_uniq: uniq l.

Let d' : eqType := sub_eqType l.

Lemma sub_set_refl: forall v (a: set v), sub_set a a.
Proof.
by move => v x y.
Qed.

Definition liftp: forall (l1: seq d), 
  sub_set l1 l -> seq d'.
fix 1; intros l1; case l1.
  intros _; exact seq0.
intros x l2 H.
have F1: l x by apply H; exact: setU11.
have F2: sub_set l2 l. 
  by move => y Hy; apply H => //=; rewrite /setU1 Hy orbT.
exact (Adds (EqSig _ _ F1) (liftp l2 F2)).
Defined.

Lemma size_liftp: forall (l1:seq d) (H: sub_set l1 l), 
  size (liftp l1 H) = size l1.
Proof.
elim => [| x l2 Rec H] //=.
by rewrite Rec.
Qed.

Lemma subd_enumP_aux : forall (l1: seq d) (H: sub_set l1 l) (u: d'),
 uniq l1 ->  count (set1 u) (liftp l1 H)  =  l1 (val u).
Proof.
elim => [| x l2 Rec H [u Hu]] //=.
move/andP => [H1 H2].
rewrite Rec //.
rewrite -(@val_eqE d l) //= /setU1.
rewrite eq_sym; case E1: (x == u) => //=.
by rewrite -(eqP E1) (negbET H1).
Qed.

Lemma subd_enumP : forall (u: d'), 
  count (set1 u) (liftp l (@sub_set_refl _ l))  = 1.
Proof.
move => u.
replace 1%N with ((l (val u)): nat).
  by apply subd_enumP_aux.
by case u => u1 Hu1 //=; rewrite Hu1.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the finite set from a uniq list                      *)
(*                                                                     *)
(***********************************************************************)

Definition UniqListSet := FinType subd_enumP.

End UniqueListSet.

Section PowerSet.

Variable (d: finType).

Let l := (powerSeq (enum d)).

Let uniq_l := (powerSeq_uniq (uniq_enum d)).

(***********************************************************************)
(*                                                                     *)
(*  Definition of the power set                                        *)
(*                                                                     *)
(***********************************************************************)

Definition powerSet := UniqListSet _ _ uniq_l.

Lemma card_powerSet: card powerSet = 2 ^ (card d).
Proof.
by rewrite !cardA -powerSeq_size /powerSet //= size_liftp.
Qed.

Lemma  filter_sub_set:
  forall h : set d, sub_set h (filter h (enum d)).
Proof.
by move => h x; rewrite filter_enum.
Qed.

Lemma  filter_sub_set1:
  forall h : set d, sub_set (filter h (enum d)) (enum d).
Proof.
by move => h x; rewrite /setA mem_enum.
Qed.

Lemma powerSet_mem: forall (h: set d), 
 powerSet (EqSig _ _ (powerSeq_mem (enum d) h)).
Proof. done. Qed.

End PowerSet.
