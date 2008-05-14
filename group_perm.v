(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import finfun.
Require Import finset.
Require Import paths.
Require Import connect.
Require Import div.
Require Import groups.
Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* group of permutations *)

Section PermGroup.

Variable T : finType.

Record perm : Type := Perm {pval : {ffun T -> T}; _ : injectiveb pval}.

Definition perm_for of phant T : predArgType := perm.

Notation pT := (perm_for (Phant T)).

Canonical Structure perm_subType := SubType pval perm_rect vrefl.
Canonical Structure perm_eqType := Eval hnf in [subEqType for pval].
Canonical Structure perm_finType := Eval hnf in [finType of perm by :>].
Canonical Structure perm_subFinType := Eval hnf in [subFinType of perm].

Canonical Structure perm_for_subType := Eval hnf in [subType of pT].
Canonical Structure perm_for_eqType := Eval hnf in [eqType of pT].
Canonical Structure perm_for_finType := Eval hnf in [finType of pT].
Canonical Structure perm_for_subFinType := Eval hnf in [subFinType of pT].

Definition fun_of_perm := fun u : perm => val u : T -> T.

Coercion fun_of_perm : perm >-> Funclass.

Lemma permP : forall u v : pT, u =1 v <-> u = v.
Proof. by move=> u v; split=> [Huv | -> //]; apply: val_inj; apply/ffunP. Qed.

Lemma perm_ofP : forall f : T -> T, injective f -> injectiveb (ffun_of f).
Proof.
by move=> f f_inj; apply/injectiveP; apply: eq_inj f_inj _ => x; rewrite ffunE.
Qed.

Definition perm_of f (f_inj : injective f) : pT := Perm (perm_ofP f_inj).

Lemma permE : forall f (f_inj : injective f), perm_of f_inj =1 f.
Proof. move=> *; exact: ffunE. Qed.

Lemma perm_inj : forall u : pT, injective u.
Proof. move=> u; exact: (injectiveP _ (valP u)). Qed.

Implicit Arguments perm_inj [].

Hint Resolve perm_inj.

Definition perm_unit := perm_of (@inj_id T).

Definition perm_inv u := perm_of (finv_inj (perm_inj u)).

Definition perm_mul u v := perm_of (inj_comp (perm_inj v) (perm_inj u)).

Lemma perm_unitP : left_unit perm_unit perm_mul.
Proof. by move=> u; apply/permP => x; rewrite permE /= permE. Qed.

Lemma perm_invP : left_inverse perm_unit perm_inv perm_mul.
Proof. by move=> u; apply/permP => x; rewrite !permE /= permE f_finv. Qed.

Lemma perm_mulP : associative perm_mul.
Proof. by move=> u v w; apply/permP => x; do !rewrite permE /=. Qed.

Canonical Structure perm_for_baseFinGroupType := Eval hnf in
  [baseFinGroupType of pT by perm_mulP, perm_unitP & perm_invP].
Canonical Structure perm_baseFinGroupType := Eval hnf in
  [baseFinGroupType of perm by perm_mulP, perm_unitP & perm_invP].
Canonical Structure perm_for_finGroupType :=
  FinGroupType perm_invP.
Canonical Structure perm_finGroupType :=
  @FinGroupType perm_baseFinGroupType perm_invP.

Lemma perm1 : forall x, (1 : pT) x = x.
Proof. by move=> x; rewrite permE. Qed.

Lemma permM : forall (s1 s2 : pT) x, (s1 * s2) x = s2 (s1 x).
Proof. by move=> *; rewrite permE. Qed.

Lemma permK : forall s : pT, cancel s s^-1.
Proof. by move=> s x; rewrite -permM mulgV perm1. Qed. 

Lemma permKV : forall s : pT, cancel s^-1 s.
Proof. by move=> s; have:= permK s^-1; rewrite invgK. Qed.

Lemma permJ : forall (s t: pT) x, (s ^ t) (t x) = t (s x).
Proof. by move=> *; rewrite !permM permK. Qed.

Definition perm_on (A : {set T}) : pred pT :=
  fun u => [pred x | u x != x] \subset A.

Lemma perm_closed : forall A u x, perm_on A u -> (u x \in A) = (x \in A).
Proof.
move=> a u x; move/subsetP=> u_on_a.
case: (u x =P x) => [-> //|]; move/eqP=> nfix_u_x.
by rewrite !u_on_a // inE /= ?(inj_eq (perm_inj u)).
Qed.  

Lemma perm_on1 :  forall H, perm_on H 1.
Proof. by move=> H; apply/subsetP=> x; rewrite inE /= perm1 eqxx. Qed.

Lemma perm_onM :  forall H f g,
  perm_on H f -> perm_on H g -> perm_on H (f * g).
Proof.
move=> H f g; move/subsetP => fH; move/subsetP => gH.
apply/subsetP => x; rewrite inE /= permM.
by case: (f x =P x) => [->|]; [move/gH | move/eqP; move/fH].
Qed.

Lemma out_perm : forall H f x, perm_on H f -> x \notin H -> f x = x.
Proof.
move=> H f x fH nHx; apply/eqP; apply: negbE2; apply: contra nHx.
exact: (subsetP fH).
Qed.

Definition transpose x y z : T :=
 if x == z then y else if y == z then x else z.

Lemma transposeK : forall x y, involutive (transpose x y).
Proof.
move=> x y z; rewrite /transpose.
case: (x =P z) => [->| nxz]; first by rewrite eqxx; case: eqP.
by case: (y =P z) => [->| nyz]; [rewrite eqxx | do 2?case: eqP].
Qed.

Definition tperm x y := perm_of (can_inj (transposeK x y)).

Lemma square_tperm : forall x y, tperm x y * tperm x y = 1.
Proof.
move=> x y; apply/permP=> z; rewrite permM !permE; exact: transposeK.
Qed.

Lemma card_perm : forall A : {set T}, #|perm_on A| = fact #|A|.
Proof.
move=> A; elim: {A}#|A| {1 3}A (eqxx #|A|) => [|n IHn] A /=.
  move/pred0P=> A0; rewrite -(card1 (1 : pT)); apply: eq_card => u.
  apply/idP/eqP => /= [uA | -> {u}]; last exact: perm_on1.
  by apply/permP => x; rewrite perm1 (out_perm uA) // -topredE /= A0.
case: (pickP (mem A)) => [x /= Ax An1|]; last by move/eq_card0->.
have:= An1; rewrite (cardsD1 x) Ax eqSS; move/IHn=> {IHn} <-.
move/eqP: An1 => <- {n}; rewrite -cardX.
pose h (u : pT) := (u x, u * tperm x (u x)).
have h_inj: injective h.
  move=> u1 u2; rewrite /h [mulg]lock; case=> ->; unlock; exact: mulg_injr.
rewrite -(card_imset _ h_inj); apply: eq_card=> [[/= y v]].
apply/imsetP/andP=> /= [[u uA [-> -> {y v}]]|[Ay vA']].
  split; first by rewrite perm_closed.
  apply/subsetP=> z; rewrite 2!inE /= permM permE /transpose.
  rewrite (inj_eq (perm_inj u)) /= (eq_sym z).
  case: (x =P z) => [<-|nxz nhuz /=]; first by case/eqP; case: eqP.
  by apply: (subsetP uA); apply: contra nhuz; move/eqP->; case: (x =P z).
pose u : pT := v * tperm x y.
have def_y: y = u x.
  by rewrite permM permE /transpose (out_perm vA') ?inE eqxx.
exists u; last by rewrite /h -def_y -mulgA square_tperm mulg1.
apply/subsetP=> z; rewrite inE /= permM permE.
rewrite (inv_eq (transposeK x y)) /transpose.
do 2!case: (_ =P z) => [<- //| _].
by move/(subsetP vA'); rewrite inE; case/andP.
Qed.

End PermGroup.

Notation "{ 'perm' T }" := (perm_for (Phant T))
  (at level 0, format "{ 'perm'  T }") : type_scope.

Notation "'S_' ( n )" := {perm I_(n)}
  (at level 0, format "'S_' ( n )").

Unset Implicit Arguments.
