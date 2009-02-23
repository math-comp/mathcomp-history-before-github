(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun finset groups.
Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* group of permutations *)

Section PermDefSection.

Variable T : finType.

Inductive perm_type : predArgType :=
  Perm (pval : {ffun T -> T}) & injectiveb pval.
Definition pval p := let: Perm f _ := p in f.
Definition perm_of of phant T := perm_type.
Identity Coercion type_of_perm : perm_of >-> perm_type.

Notation pT := (perm_of (Phant T)).

Canonical Structure perm_subType :=
  Eval hnf in [subType for pval by perm_type_rect].
Definition perm_eqMixin := Eval hnf in [eqMixin of perm_type by <:].
Canonical Structure perm_eqType := Eval hnf in EqType perm_eqMixin.
Definition perm_choiceMixin := [choiceMixin of perm_type by <:].
Canonical Structure perm_choiceType := Eval hnf in ChoiceType perm_choiceMixin.
Definition perm_countMixin := [countMixin of perm_type by <:].
Canonical Structure perm_countType := Eval hnf in CountType perm_countMixin.
Canonical Structure perm_subCountType :=
  Eval hnf in [subCountType of perm_type].
Definition perm_finMixin := [finMixin of perm_type by <:].
Canonical Structure perm_finType := Eval hnf in FinType perm_finMixin.
Canonical Structure perm_subFinType := Eval hnf in [subFinType of perm_type].

Canonical Structure perm_for_subType := Eval hnf in [subType of pT].
Canonical Structure perm_for_eqType := Eval hnf in [eqType of pT].
Canonical Structure perm_for_choiceType := Eval hnf in [choiceType of pT].
Canonical Structure perm_for_countType := Eval hnf in [countType of pT].
Canonical Structure perm_for_subCountType := Eval hnf in [subCountType of pT].
Canonical Structure perm_for_finType := Eval hnf in [finType of pT].
Canonical Structure perm_for_subFinType := Eval hnf in [subFinType of pT].

Lemma perm_proof : forall f : T -> T, injective f -> injectiveb (finfun f).
Proof.
by move=> f f_inj; apply/injectiveP; apply: eq_inj f_inj _ => x; rewrite ffunE.
Qed.

End PermDefSection.

Notation "{ 'perm' T }" := (perm_of (Phant T))
  (at level 0, format "{ 'perm'  T }") : type_scope.

Notation "''S_' n" := {perm 'I_n}
  (at level 8, n at level 2, format "''S_' n").

Notation Local fun_of_perm_def := (fun T (u : perm_type T) => val u : T -> T).
Notation Local perm_def := (fun T f injf => Perm (@perm_proof T f injf)).

Module Type PermDefSig.
Parameter fun_of_perm : forall T, perm_type T -> T -> T.
Coercion fun_of_perm : perm_type >-> Funclass.
Parameter perm : forall (T : finType) (f : T -> T), injective f -> {perm T}.
Axiom fun_of_permE : fun_of_perm = fun_of_perm_def.
Axiom permE : perm = perm_def.
End PermDefSig.
Module PermDef : PermDefSig.
Definition fun_of_perm := fun_of_perm_def.
Definition perm := perm_def.
Lemma fun_of_permE : fun_of_perm = fun_of_perm_def. Proof. by []. Qed.
Lemma permE : perm = perm_def. Proof. by []. Qed.
End PermDef.

Notation fun_of_perm := PermDef.fun_of_perm.
Notation "@ 'perm'" := (@PermDef.perm) (at level 10, format "@ 'perm'").
Notation perm := (@PermDef.perm _ _).
Canonical Structure fun_of_perm_unlock := Unlockable PermDef.fun_of_permE.
Canonical Structure perm_unlock := Unlockable PermDef.permE.

Section Theory.

Variable T : finType.

Notation pT := {perm T}.

Lemma permP : forall u v : pT, u =1 v <-> u = v.
Proof.
move=> u v; split=> [| -> //]; rewrite unlock => eq_uv.
by apply: val_inj; apply/ffunP.
Qed.

Lemma pvalE : forall u : pT, pval u = u :> (T -> T).
Proof. by rewrite [@fun_of_perm _]unlock. Qed.

Lemma permE : forall f f_inj, @perm T f f_inj =1 f.
Proof. by move=> f f_inj x; rewrite -pvalE [@perm _]unlock ffunE. Qed.

Lemma perm_inj : forall u : pT, injective u.
Proof. move=> u; rewrite -!pvalE; exact: (injectiveP _ (valP u)). Qed.

Implicit Arguments perm_inj [].

Hint Resolve perm_inj.

Lemma perm_onto : forall u : pT, codom u =i predT.
Proof. by move=> u; apply/subset_cardP; rewrite ?card_codom ?subset_predT. Qed.
 
Definition perm_one := perm (@inj_id T).

Lemma perm_invK : forall u : pT, cancel (fun x => iinv (perm_onto u x)) u.
Proof. by move=> u x /=; rewrite f_iinv. Qed.

Definition perm_inv u := perm (can_inj (perm_invK u)).

Definition perm_mul u v := perm (inj_comp (perm_inj v) (perm_inj u)).

Lemma perm_oneP : left_id perm_one perm_mul.
Proof. by move=> u; apply/permP => x; rewrite permE /= permE. Qed.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
Proof. by move=> u; apply/permP => x; rewrite !permE /= permE f_iinv. Qed.

Lemma perm_mulP : associative perm_mul.
Proof. by move=> u v w; apply/permP => x; do !rewrite permE /=. Qed.

Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T) :=
  FinGroup.Mixin perm_mulP perm_oneP perm_invP.
Canonical Structure perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType perm_of_baseFinGroupMixin.
Canonical Structure perm_finGroupType :=
  @FinGroupType perm_baseFinGroupType perm_invP.

Canonical Structure perm_of_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of pT].
Canonical Structure perm_of_finGroupType :=
  Eval hnf in [finGroupType of pT].

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
move=> H f x fH nHx; apply/eqP; apply: negbNE; apply: contra nHx.
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

Definition tperm x y := perm (can_inj (transposeK x y)).

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
  move=> u1 u2; rewrite /h [mulg]lock; case=> ->; unlock; exact: mulIg.
rewrite -(card_imset _ h_inj); apply: eq_card=> [[/= y v]].
apply/imsetP/andP=> /= [[u uA [-> -> {y v}]]|[Ay vA']].
  split; first by rewrite perm_closed.
  apply/subsetP=> z; rewrite !inE permM permE /transpose.
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

End Theory.

Prenex Implicits tperm.

Unset Implicit Arguments.
