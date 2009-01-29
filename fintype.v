(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The Finite Structure describes Types with finitely many elements, by   *)
(* supplying a duplicate-free sequence of all the elements. It is a       *)
(* subclass of Countable and thus of Choice and Equality. As with         *)
(* Countable, the redundancy is needed for the consistency of the         *)
(* Canonical structure inference. Also, while finiteness could be stated  *)
(* more simply by giving a bound on the range of the pickle function      *)
(* provided by the Countable structure, this would yield a useless        *)
(* computational interpretation due to the wasteful encoding into Peano   *)
(* integers.                                                              *)

Module Finite.

Definition axiom T (op : rel T) e := forall x : T, count (op^~ x) e = 1.

Record mixin_of (T : Type) (op : rel T) : Type :=
  Mixin {mixin_enum : seq T; _ : axiom op mixin_enum}.

Lemma uniq_enumP : forall T e, @uniq T e -> e =i T -> axiom eq_op e.
Proof. by move=> T e Ue sT x; rewrite count_pred1_uniq ?sT. Qed.

Definition UniqMixin T e Ue eT := Mixin (@uniq_enumP T e Ue eT).

Section CountAxiom.

Variables (T : countType) (n : nat).
Hypothesis ubT : forall x : T, pickle x < n.

Definition count_enum := pmaps (@pickle_inv T) (iota 0 n).

Lemma count_enumP : axiom eq_op count_enum.
Proof.
apply: uniq_enumP (uniq_pmaps (@pickle_invK T) (uniq_iota _ _)) _ => x.
by rewrite mem_pmaps -pickleK_inv maps_f // mem_iota ubT.
Qed.

Definition CountMixin :=
  let k T _ := @Mixin T in Countable.unpack k T _ _ count_enumP.

End CountAxiom.

Record class_of (T : Type) : Type :=
  Class {base :> Countable.class_of T; mixin :> mixin_of (Equality.op base)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition unpack K (k : forall T (c : class_of T), K T c) cT :=
  let: Pack T c _ := cT return K _ (class cT) in k _ c.
Definition repack cT : _ -> Type -> type := let k T c p := p c in unpack k cT.

Definition pack := let k T c m := Pack (@Class T c m) T in Countable.unpack k.

Module Type EnumSig.
Parameter enum : forall cT : type, seq cT.
Axiom enumDef : enum = fun cT => mixin_enum (class cT).
End EnumSig.

Module EnumDef : EnumSig.
Definition enum cT := mixin_enum (class cT).
Definition enumDef := erefl enum.
End EnumDef.

Notation enum := EnumDef.enum.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Coercion countType cT := Countable.Pack (class cT) cT.

End Finite.

Notation finType := Finite.type.
Notation FinType := Finite.pack.
Notation FinMixin := Finite.Mixin.
Notation UniqFinMixin := Finite.UniqMixin.
Notation "[ 'finType' 'of' T 'for' cT ]" :=
    (@Finite.repack cT (@Finite.Pack T) T)
  (at level 0, format "[ 'finType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finType' 'of' T ]" :=
    (Finite.repack (fun c => @Finite.Pack T c) T)
  (at level 0, format "[ 'finType'  'of'  T ]") : form_scope.
Canonical Structure Finite.eqType.
Canonical Structure Finite.choiceType.
Canonical Structure Finite.countType.

Canonical Structure finEnum_unlock := Unlockable Finite.EnumDef.enumDef.

(* Operations enum, pick, and pred0b expect an applicative pred  *)
(* argument; operations card, disjoint, and subset expect a      *)
(* mem_pred and are used through notations that supply the mem   *)
(* coercion. We lock the definitions of card and subset to       *)
(* mitigate divergence in the Coq term comparison algorithm.     *)

Definition enum T P := filter P (Finite.enum T).
Definition pick T P := ohead (@enum T P).
Prenex Implicits enum pick.
Notation "[ 'pick' x | P ]" := (pick [pred x | P])
  (at level 0, x ident, format "[ 'pick'  x  |  P  ]") : form_scope.
Notation "[ 'pick' x : T | P ]" := (pick [pred x : T | P])
  (at level 0, x ident, only parsing) : form_scope.
Notation "[ 'pick' x \in A ]" := (pick [pred x | x \in A])
  (at level 0, x ident, format "[ 'pick'  x  \in  A  ]") : form_scope.
Notation "[ 'pick' x \in A | P ]" := (pick [pred x | (x \in A) && P])
  (at level 0, x ident, format "[ 'pick'  x  \in  A  |  P  ]") : form_scope.

Notation Local card_type := (forall T : finType, mem_pred T -> nat).
Notation Local card_def := (fun T A => size (enum A)).
Module Type CardDefSig.
Parameter card : card_type. Axiom cardEdef : card = card_def.
End CardDefSig.
Module CardDef : CardDefSig.
Definition card : card_type := card_def. Definition cardEdef := erefl card.
End CardDef.
Export CardDef. (* Should become Include in 8.2. *)
Canonical Structure card_unlock := Unlockable cardEdef.
(* A is at level 99 to allow the notation #|G : H| in groups. *)
Notation "#| A |" := (card (mem A))
  (at level 0, A at level 99, format "#| A |") : nat_scope.

Definition pred0b (T : finType) (P : pred T) := #|P| == 0.
Prenex Implicits pred0b.
Notation "'forallb' x , F" := (pred0b (fun x => ~~ F))
  (at level 200, x at level 99,
   format "'[hv' 'forallb'  x , '/ '  F ']'") : bool_scope.
Notation "'forallb' x : T , F" := (pred0b (fun x : T => ~~ F))
  (at level 200, x at level 99, only parsing) : bool_scope.
Notation "'existsb' x , F" := (~~ pred0b (fun x => F%B))
  (at level 200, x at level 99,
   format "'[hv' 'existsb'  x , '/ '  F ']'") : bool_scope.
Notation "'existsb' x : T , F" := (~~ pred0b (fun x : T => F%B))
  (at level 200, x at level 99, only parsing) : bool_scope.

Definition disjoint T (A B : mem_pred _) := @pred0b T (predI A B).
Notation "[ 'disjoint' A & B ]" := (disjoint (mem A) (mem B))
  (at level 0,
   format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'") : bool_scope.

Notation Local subset_type := (forall (T : finType) (A B : mem_pred T), bool).
Notation Local subset_def := (fun T A B => pred0b (predD A B)).
Module Type SubsetDefSig.
Parameter subset : subset_type. Axiom subsetEdef : subset = subset_def.
End SubsetDefSig.
Module SubsetDef : SubsetDefSig.
Definition subset : subset_type := subset_def.
Definition subsetEdef := erefl subset.
End SubsetDef.
Export SubsetDef. (* Should become Include in 8.2. *)
Canonical Structure subset_unlock := Unlockable subsetEdef.
Notation "A \subset B" := (subset (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

Definition proper T A B := @subset T A B && ~~ subset B A.
Notation "A \proper B" := (proper (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

(* image, xinv, inv, and ordinal operations will be defined later. *)

Section OpsTheory.

Variable T : finType.

Implicit Types A B C P Q : pred T.
Implicit Types x y : T.
Implicit Type s : seq T.

Lemma enumP : Finite.axiom eq_op (Finite.enum T).
Proof. by rewrite unlock; case T => ? [? []]. Qed.

Section EnumPick.

Variable P : pred T.

Lemma enumT : enum T = Finite.enum T.
Proof. exact: filter_predT. Qed.

Lemma enum_mem : enum (mem P) = enum P.
Proof. by []. Qed.

Lemma mem_enum : forall A, enum A =i A.
Proof.
by move=> q x; rewrite mem_filter andbC -has_pred1 has_count enumP.
Qed.

Lemma uniq_enum : uniq (enum P).
Proof.
apply: uniq_filter; apply: uniq_count_pred1 => x.
by rewrite enumP -enumT mem_enum.
Qed.

Lemma enum0 : @enum T pred0 = [::]. Proof. exact: filter_pred0. Qed.

Lemma enum1 : forall x, enum (pred1 x) = [:: x].
Proof.
move=> x; rewrite [enum _](all_pred1P x _ _).
  by rewrite -count_filter enumP.
by apply/allP=> y; rewrite mem_enum.
Qed.

CoInductive pick_spec : option T -> Type :=
  | Pick x of P x         : pick_spec (Some x)
  | Nopick of P =1 xpred0 : pick_spec None.

Lemma pickP : pick_spec (pick P).
Proof.
rewrite /pick; case: enum (mem_enum P) => [|x s] Pxs /=.
  by right; exact: fsym.
by left; rewrite -[P _]Pxs mem_head.
Qed.

End EnumPick.

Lemma eq_enum : forall P Q, P =1 Q -> enum P = enum Q.
Proof. move=> P Q eqPQ; exact: eq_filter. Qed.

Lemma eq_pick : forall P Q, P =1 Q -> pick P = pick Q.
Proof. by move=> P Q eqPQ; rewrite /pick (eq_enum eqPQ). Qed.

Lemma cardE : forall A, #|A| = size (enum (mem A)).
Proof. by rewrite unlock. Qed.

Lemma eq_card : forall A B, A =i B -> #|A| = #|B|.
Proof. by move=> A B eqAB; rewrite !cardE (eq_enum eqAB). Qed.

Lemma eq_card_trans : forall A B n, #|A| = n -> B =i A -> #|B| = n.
Proof. move=> A B _ <-; exact: eq_card. Qed.

Lemma card0 : #|@pred0 T| = 0. Proof. by rewrite cardE enum0. Qed.

Lemma cardT : #|T| = size (enum T). Proof. by rewrite cardE. Qed.

Lemma card1 : forall x, #|pred1 x| = 1.
Proof. by move=> x; rewrite cardE enum1. Qed.

Lemma eq_card0 : forall A, A =i pred0 -> #|A| = 0.
Proof. by have:= eq_card_trans card0. Qed.

Lemma eq_cardT : forall A, A =i predT -> #|A| = size (enum T).
Proof. by have:= eq_card_trans cardT. Qed.

Lemma eq_card1 : forall x A, A =i pred1 x -> #|A| = 1.
Proof. by move=> x; have:= eq_card_trans (card1 x). Qed.

Lemma cardUI : forall A B,
  #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Proof. by move=> A B; rewrite !cardE -!count_filter count_predUI. Qed.

Lemma cardID : forall B A, #|[predI A & B]| + #|[predD A & B]| = #|A|.
Proof.
move=> B A; rewrite -cardUI addnC [#|predI _ _|]eq_card0 => [|x] /=.
  by apply: eq_card => x; rewrite !inE andbC -andb_orl orbN.
by rewrite !inE -!andbA andbC andbA andbN.
Qed.

Lemma cardC : forall A, #|A| + #|[predC A]| = #|T|.
Proof. by move=> A; rewrite !cardE -!count_filter count_predC. Qed.

Lemma cardU1 : forall x A, #|[predU1 x & A]| = (x \notin A) + #|A|.
Proof.
move=> x A; case Ax: (x \in A).
  by apply: eq_card => y; rewrite inE /=; case: eqP => // ->.
rewrite /= -(card1 x) -cardUI addnC.
rewrite [#|predI _ _|]eq_card0 => [|y /=]; first exact: eq_card.
by rewrite !inE; case: eqP => // ->.
Qed.

Lemma card2 : forall x y, #|pred2 x y| = (x != y).+1.
Proof. by move=> x y; rewrite cardU1 card1 addn1. Qed.

Lemma cardC1 : forall x, #|predC1 x| = #|T|.-1.
Proof. by move=> x; rewrite -(cardC (pred1 x)) card1. Qed.

Lemma cardD1 : forall x A, #|A| = (x \in A) + #|[predD1 A & x]|.
Proof.
move=> x A; case Ax: (x \in A); last first.
  by apply: eq_card => y; rewrite !inE /=; case: eqP => // ->.
rewrite /= -(card1 x) -cardUI addnC /=.
rewrite [#|predI _ _|]eq_card0 => [|y]; last first.
  by rewrite !inE; case: eqP.
by apply: eq_card => y; rewrite !inE; case: eqP => // ->.
Qed.

Lemma max_card : forall A, #|A| <= #|T|.
Proof. by move=> A; rewrite -(cardC A) leq_addr. Qed.

Lemma card_size : forall s, #|s| <= size s.
Proof.
elim=> [|x s IHs] /=; first by rewrite card0.
rewrite cardU1 /=; case: (~~ _) => //; exact: leqW.
Qed.

Lemma card_uniqP : forall s, reflect (#|s| = size s) (uniq s).
Proof.
move=> s; elim: s => [|x s IHs]; first by left; exact card0.
rewrite cardU1 /= /addn; case: {+}(x \in s) => /=.
  by right=> card_Ssz; have:= card_size s; rewrite card_Ssz ltnn.
by apply: (iffP IHs) => [<-| [<-]].
Qed.

Lemma card0_eq : forall A, #|A| = 0 -> A =i pred0.
Proof. by move=> A A0 x; apply/idP => Ax; rewrite (cardD1 x) Ax in A0. Qed.

Lemma pred0P : forall P, reflect (P =1 pred0) (pred0b P).
Proof. move=> p; apply: (iffP eqP); [exact: card0_eq | exact: eq_card0]. Qed. 

Lemma pred0Pn : forall P, reflect (exists x, P x) (~~ pred0b P).
Proof.
move=> P; case: (pickP P) => [x Px | P0].
  by rewrite (introN (pred0P P)) => [|P0]; [left; exists x | rewrite P0 in Px].
by rewrite -lt0n eq_card0 //; right=> [[x]]; rewrite P0.
Qed.

Lemma subsetE : forall A B, (A \subset B) = pred0b [predD A & B].
Proof. by rewrite unlock. Qed.

Lemma subsetP : forall A B, reflect {subset A <= B} (A \subset B).
Proof.
rewrite unlock => A B; apply: (iffP (pred0P _)) => [AB0 x | sAB x /=].
  by apply/implyP; apply/idPn; rewrite negb_imply andbC [_ && _]AB0.
by rewrite andbC -negb_imply; apply: (introNf implyP); move/sAB.
Qed.

Lemma subsetPn : forall A B,
  reflect (exists2 x, x \in A & x \notin B) (~~ (A \subset B)).
Proof.
rewrite unlock => A B; apply: (iffP (pred0Pn _)) => [[x] | [x Ax nBx]].
  by case/andP; exists x.
by exists x; rewrite /= nBx.
Qed.

Lemma subset_leq_card : forall A B, A \subset B -> #|A| <= #|B|.
Proof.
move=> A B sAB.
rewrite -(cardID A B) [#|predI _ _|](@eq_card _ A) ?leq_addr //= => x.
rewrite !inE andbC; case Ax: (x \in A) => //; exact: subsetP Ax.
Qed.

Lemma subxx_hint : forall mA : mem_pred T, subset mA mA.
Proof. by case=> A; have:= introT (subsetP A A); rewrite !unlock => ->. Qed.
Hint Resolve subxx_hint.

(* The parametrization by predType makes it easier to apply subxx. *)
Lemma subxx : forall (pT : predType T) (pA : pT), pA \subset pA.
Proof. by []. Qed.

Lemma eq_subset : forall A1 A2, A1 =i A2 -> subset (mem A1) =1 subset (mem A2).
Proof.
move=> A1 A2 eqA12 [B]; rewrite !unlock; congr (_ == 0).
by apply: eq_card => x; rewrite inE /= eqA12.
Qed.

Lemma eq_subset_r : forall B1 B2, B1 =i B2 ->
  (@subset T)^~ (mem B1) =1 (@subset T)^~ (mem B2).
Proof.
move=> B1 B2 eqB12 [A]; rewrite !unlock; congr (_ == 0).
by apply: eq_card => x; rewrite !inE /= eqB12.
Qed.

Lemma eq_subxx : forall A B, A =i B -> A \subset B.
Proof. by move=> A B; move/eq_subset->. Qed.

Lemma subset_predT : forall A, A \subset T.
Proof. by move=> A; apply/subsetP. Qed.

Lemma predT_subset : forall A, T \subset A -> forall x, x \in A.
Proof. move=> A; move/subsetP=> allA x; exact: allA. Qed.

Lemma subset_pred1 : forall A x, (pred1 x \subset A) = (x \in A).
Proof.
by move=> A x; apply/subsetP/idP=> [-> //|Ax y]; [rewrite inE /= | move/eqP->].
Qed.

Lemma subset_eqP : forall A B,
  reflect (A =i B) ((A \subset B) && (B \subset A)).
Proof.
move=> A B; apply: (iffP andP) => [[sAB sBA] x| eqAB].
  by apply/idP/idP; apply: subsetP.
by rewrite !eq_subxx.
Qed.

Lemma subset_cardP : forall A B,
  #|A| = #|B| -> reflect (A =i B) (A \subset B).
Proof.
move=> A B eqcAB; case: (subsetP A B) (subset_eqP A B) => //= sAB.
case: (subsetP B A) => [//|[]] x Bx; apply/idPn => Ax.
case/idP: (ltnn #|A|); rewrite {2}eqcAB (cardD1 x B) Bx /=.
apply: subset_leq_card; apply/subsetP=> y Ay; rewrite inE /= andbC.
by rewrite sAB //; apply/eqP => eqyx; rewrite -eqyx Ay in Ax.
Qed.

Lemma subset_leqif_card : forall A B,
  A \subset B -> #|A| <= #|B| ?= iff (B \subset A).
Proof.
move=> A B sAB; split; [exact: subset_leq_card | apply/eqP/idP].
  by move/subset_cardP=> sABP; rewrite (eq_subset_r (sABP sAB)).
by move=> sBA; apply: eq_card; apply/subset_eqP; rewrite sAB.
Qed.

Lemma subset_trans : forall A B C,
  A \subset B -> B \subset C -> A \subset C.
Proof.
move=> A B C; move/subsetP=> sAB; move/subsetP=> sBC.
by apply/subsetP=> x; move/sAB; exact: sBC.
Qed.

Lemma subset_all : forall s A, (s \subset A) = all (mem A) s.
Proof. by move=> s A; exact (sameP (subsetP _ _) allP). Qed.

Lemma properE : forall A B, A \proper B = (A \subset B) && ~~(B \subset A).
Proof. by []. Qed.

Lemma properP : forall A B,
  reflect (A \subset B /\ (exists2 x, x \in B & x \notin A)) (A \proper B).
Proof.
move=> A B; rewrite properE; apply: (iffP andP); case=>->; case/subsetPn=> //.
by move=> x Bx nAx; split=> //; exists x.
Qed.
 
Lemma proper_sub : forall A B, A \proper B -> A \subset B.
Proof. by move=> A B; case/andP. Qed.

Lemma proper_subn : forall A B, A \proper B -> ~~ (B \subset A).
Proof. by move=> A B; case/andP. Qed.

Lemma proper_trans : forall A B C,
  A \proper B -> B \proper C -> A \proper C.
Proof.
move=> A B C; case/properP=> sAB [x Bx nAx]; case/properP=> sBC [y Cy nBy].
rewrite properE (subset_trans sAB) //=; apply/subsetPn; exists y=> //.
by apply/negP; move/(subsetP _ _ sAB); apply/negP.
Qed.

Lemma proper_sub_trans : forall A B C,
  A \proper B -> B \subset C -> A \proper C.
Proof.
move=> A B C; case/properP=> sAB [x Bx nAx] sBC; rewrite properE.
rewrite (subset_trans sAB) //.
by apply/subsetPn; exists x; rewrite ?(subsetP _ _ sBC).
Qed.

Lemma sub_proper_trans : forall A B C,
  A \subset B -> B \proper C -> A \proper C.
move=> A B C sAB; case/properP=> sBC [x Cx nBx]; rewrite properE.
rewrite (subset_trans sAB) //; apply/subsetPn; exists x=> //; apply/negP.
by move/(subsetP _ _ sAB); apply/negP.
Qed.

Lemma proper_card : forall A B, A \proper B -> #|A| < #|B|.
Proof.
move=> A B; case/andP=> sAB nsBA; rewrite ltn_neqAle. 
by case: (subset_leqif_card sAB)=> -> ->; rewrite andbT.
Qed.

Lemma proper_irrefl : forall A, ~~ (A \proper A).
Proof. by move=> A; rewrite properE subxx. Qed.

Lemma eq_proper : forall A B,
  A =i B -> proper (mem A) =1 proper (mem B).
Proof.
move=> A B eAB [C]; congr andb; first by apply: (eq_subset eAB).
by rewrite (eq_subset_r eAB).
Qed.

Lemma eq_proper_r : forall A B, A =i B ->
  (@proper T)^~ (mem A) =1 (@proper T)^~ (mem B).
Proof.
move=> A B eAB [C]; congr andb; first by apply: (eq_subset_r eAB).
by rewrite (eq_subset eAB).
Qed. 

Lemma disjoint_sym : forall A B, [disjoint A & B] = [disjoint B & A].
Proof. by move=> A B; congr eqn; apply: eq_card => x; apply: andbC. Qed.

Lemma eq_disjoint : forall A1 A2, A1 =i A2 ->
  disjoint (mem A1) =1 disjoint (mem A2).
Proof.
move=> A1 A2 eqA12 [B]; congr (_ == 0); apply: eq_card => x.
by rewrite /in_mem /= eqA12.
Qed.

Lemma eq_disjoint_r : forall B1 B2, B1 =i B2 ->
  (@disjoint T)^~ (mem B1) =1 (@disjoint T)^~ (mem B2).
Proof.
move=> B1 B2 eqB12 [A]; congr (_ == 0); apply: eq_card => x.
by rewrite /in_mem /= eqB12.
Qed.

Lemma subset_disjoint : forall A B,
  (A \subset B) = [disjoint A & [predC B]].
Proof. by move=> A B; rewrite disjoint_sym unlock. Qed.

Lemma disjoint_subset : forall A B, [disjoint A & B] = (A \subset [predC B]).
Proof.
move=> A B; rewrite subset_disjoint; apply: eq_disjoint_r => x.
by rewrite !inE /= negbK.
Qed.

Lemma disjoint_trans : forall A B C,
  A \subset B -> [disjoint B & C] -> [disjoint A & C].
Proof. move=> A B C; rewrite 2!disjoint_subset; exact: subset_trans. Qed.

Lemma disjoint0 : forall A, [disjoint pred0 & A].
Proof. move=> A; exact/pred0P. Qed.

Lemma eq_disjoint0 : forall A B, A =i pred0 -> [disjoint A & B].
Proof. move=> A B; move/eq_disjoint->; exact: disjoint0. Qed.

Lemma disjoint1 : forall x A, [disjoint pred1 x & A] = (x \notin A).
Proof.
move=> x A; apply negb_sym; apply: (sameP _ (pred0Pn (predI (pred1 x) A))).
apply: introP => Hx; first by exists x; rewrite /= eqxx.
by case=> y /=; case/andP=> [Dx Hy]; case: (negP Hx); rewrite -(eqP Dx).
Qed.

Lemma eq_disjoint1 : forall x A B,
   A =i pred1 x ->  [disjoint A & B] = (x \notin B).
Proof. move=> x A B; move/eq_disjoint->; exact: disjoint1. Qed.

Lemma disjointU : forall A B C,
  [disjoint predU A B & C] = [disjoint A & C] && [disjoint B & C].
Proof.
move=> A B C; case: [disjoint A & C] / (pred0P (xpredI A C)) => [A0 | nA0] /=.
  by congr (_ == 0); apply: eq_card => x; rewrite [x \in _]andb_orl A0.
apply/pred0P=> nABC; case: nA0 => x; apply/idPn=> /=; move/(_ x): nABC.
by rewrite [_ x]andb_orl; case/norP.
Qed.

Lemma disjointU1 : forall x A B,
  [disjoint predU1 x A & B] = (x \notin B) && [disjoint A & B].
Proof. by move=> x A B; rewrite disjointU disjoint1. Qed.

Lemma disjoint_adds : forall x s B,
  [disjoint x :: s & B] = (x \notin B) && [disjoint s & B].
Proof. move=> *; exact: disjointU1. Qed.

Lemma disjoint_has : forall s A, [disjoint s & A] = ~~ has (mem A) s.
Proof.
move=> s A; rewrite -(@eq_has _ (mem (enum A))) => [|x]; last exact: mem_enum.
rewrite has_sym has_filter -filter_predI -has_filter has_count -eqn0Ngt.
by rewrite count_filter /disjoint /pred0b unlock.
Qed.

Lemma disjoint_cat : forall s1 s2 A,
  [disjoint s1 ++ s2 & A] = [disjoint s1 & A] && [disjoint s2 & A].
Proof. by move=> *; rewrite !disjoint_has has_cat negb_orb. Qed.

End OpsTheory.

Hint Resolve subxx_hint.

Implicit Arguments pred0P [T P].
Implicit Arguments pred0Pn [T P].
Implicit Arguments subsetP [T A B].
Implicit Arguments subsetPn [T A B].
Implicit Arguments subset_eqP [T A B].
Implicit Arguments card_uniqP [T s].
Prenex Implicits pred0P pred0Pn subsetP subsetPn subset_eqP card_uniqP.

(**********************************************************************)
(*                                                                    *)
(*  Boolean quantifiers for finType                                   *)
(*                                                                    *)
(**********************************************************************)

Section Quantifiers.

Variable T : finType.
Implicit Type P : pred T.

Lemma forallP : forall P, reflect (forall x, P x) (forallb x, P x).
Proof.
by move=> P; apply: (iffP pred0P) => allP x; first apply/idPn; rewrite allP.
Qed.

Lemma existsP : forall P, reflect (exists x, P x) (existsb x, P x).
Proof. by move=> P; apply: (iffP pred0Pn); case=> x; exists x. Qed.

Lemma eq_forallb : forall P1 P2,
   P1 =1 P2 -> (forallb x, P1 x) = (forallb x, P2 x).
Proof. by move=> *; congr (_ == _); apply: eq_card => x; congr (~~ _). Qed.

Lemma eq_existsb : forall P1 P2,
  P1 =1 P2 -> (existsb x, P1 x) = (existsb x, P2 x).
Proof. by move=> *; congr (_ != _); apply: eq_card. Qed.

Lemma negb_forall : forall P, ~~ (forallb x, P x) = (existsb x, ~~ P x).
Proof. by []. Qed.

Lemma negb_exists : forall P, ~~ (existsb x, P x) = (forallb x, ~~ P x).
Proof.
move=> P; rewrite negbK; congr (_ == _); apply: eq_card => x.
by rewrite -!topredE /= negbK.
Qed.

End Quantifiers.

Implicit Arguments forallP [T P].
Implicit Arguments existsP [T P].
Prenex Implicits forallP existsP.

(**********************************************************************)
(*                                                                    *)
(*  Boolean injective for finType                                     *)
(*                                                                    *)
(**********************************************************************)


Section Injectiveb.

Variables (aT : finType) (rT : eqType) (f : aT -> rT).
Implicit Type D : pred aT.

Definition dinjectiveb D := uniq (maps f (enum D)).

Definition injectiveb := dinjectiveb aT.

Lemma dinjectivePn : forall D,
  reflect (exists2 x, x \in D & exists2 y, y \in [predD1 D & x] & f x = f y)
          (~~ dinjectiveb D).
Proof.
move=> D; apply: (iffP idP) => [injf | [x Dx [y Dxy eqfxy]]]; last first.
  move: Dx; rewrite -(mem_enum D); case/rot_to=> i E defE.
  rewrite /dinjectiveb -(uniq_rot i) -maps_rot defE /=; apply/nandP; left.
  rewrite inE /= -(mem_enum D) -(mem_rot i) defE inE in Dxy.
  rewrite andb_orr andbC andbN in Dxy.
  by rewrite eqfxy maps_f //; case/andP: Dxy.
pose p := [pred x \in D | existsb y, (y \in [predD1 D & x]) && (f x == f y)].
case: (pickP p) => [x /= | no_p].
  case/andP=> Dx; case/existsP=> y; case/andP=> Dxy; move/eqP=> eqfxy.
  by exists x; last exists y.
rewrite /dinjectiveb uniq_maps_in ?uniq_enum // in injf => x y Dx Dy eqfxy.
move/(_ x): no_p; rewrite /= -mem_enum Dx; move/pred0P; move/(_ y).
by rewrite inE /= -(mem_enum D) Dy eqfxy eqxx !andbT; move/eqP.
Qed.

Lemma dinjectiveP : forall D, reflect {in D &, injective f} (dinjectiveb D).
Proof.
move=> D; rewrite -[dinjectiveb D]negbK.
case: dinjectivePn=> [noinjf | injf]; constructor.
  case: noinjf => x Dx [y]; case/andP=> neqxy Dy eqfxy.
  by move/(_ x y Dx Dy eqfxy)=> eqxy; case/eqP: neqxy.
move=> x y Dx Dy /= eqfxy; apply/eqP; apply/idPn=> nxy; case: injf.
by exists x => //; exists y => //=; rewrite inE /= eq_sym nxy.
Qed.

Lemma injectivePn :
  reflect (exists x, exists2 y, x != y & f x = f y) (~~ injectiveb).
Proof.
apply: (iffP (dinjectivePn _)) => [[x _ [y nxy eqfxy]] | [x [y nxy eqfxy]]];
 by exists x => //; exists y => //; rewrite inE /= andbT eq_sym in nxy *.
Qed.

Lemma injectiveP : reflect (injective f) injectiveb.
Proof. apply: (iffP (dinjectiveP _)) => injf x y => [|_ _]; exact: injf. Qed.

End Injectiveb.

Section FunImage.

Variables (T : finType) (T' : eqType) .

Definition codom f : pred T' := fun y => existsb x : T, f x == y.

Remark iinv_exists : forall f y, codom f y -> {x : T | f x == y}.
Proof.
move=> f y fy; pose a := f _ == y.
by case: (pickP a) => [x fx | nfy]; [exists x | case/pred0P: fy].
Qed.

Definition iinv f y (fy : codom f y) := sval (iinv_exists fy).

Lemma codom_f : forall f x, codom f (f x).
Proof. by move=> f x; apply/existsP; exists x => /=. Qed.
  
Lemma f_iinv : forall f y (Hy : codom f y), f (iinv Hy) = y.
Proof. by rewrite /iinv => f y Hy; case: iinv_exists => x /=; move/eqP. Qed.

Lemma iinv_f : forall f x (Hfx : codom f (f x)), injective f -> iinv Hfx = x.
Proof. by move=> f x Hfx; apply; exact: f_iinv. Qed.

Section Image.

Variable (f : T -> T') (a : pred T).

Definition image : pred T' := fun y => existsb x, a x && (f x == y).

Lemma imageP : forall y, reflect (exists2 x, a x & y = f x) (image y).
Proof.
move=> y; apply: (iffP existsP) => [[x]| [x ax ->]].
  by case/andP=> ax; move/eqP; exists x.
by exists x; rewrite /= ax eqxx.
Qed.

Remark diinv_exists : forall y, image y -> {x : T | a x && (f x == y)}.
Proof.
move=> y fy; pose b x := a x && (f x == y).
by case: (pickP b) => [x | nfy]; [exists x | case/pred0P: fy].
Qed.

Definition diinv y (Hy : image y) := sval (diinv_exists Hy).

Lemma f_diinv : forall y (Hy : image y), f (diinv Hy) = y.
Proof.
by rewrite /diinv => y Hy; case: diinv_exists => x /=; case/andP=> _; move/eqP.
Qed.

Lemma a_diinv : forall y (Hy : image y), a (diinv Hy).
Proof. by rewrite /diinv => y Hy; case: diinv_exists => x /=; case/andP. Qed.

Lemma diinv_f : {in a &, injective f} ->
  forall x (Hfx : image (f x)), a x -> diinv Hfx = x.
Proof. move=> Hfd *; apply Hfd => //; [exact: a_diinv | exact: f_diinv]. Qed.

Lemma preim_diinv : forall a' y (Hy : image y),
  preim f a' (diinv Hy) = a' y.
Proof. by move=> *; rewrite /= f_diinv. Qed.

Lemma image_codom : forall y, image y -> codom f y.
Proof. move=> y; case/imageP=> x _ ->; exact: codom_f. Qed.

Lemma mem_image : forall x, a x -> image (f x).
Proof. by move=> x ax; apply/imageP; exists x. Qed.

Hypothesis Hf : injective f.

Lemma image_f : forall x, image (f x) = a x.
Proof.
by move=> x; apply/imageP/idP => [[x' ax' []] | ax]; [move/Hf-> | exists x].
Qed.

Lemma image_iinv : forall y (Hy : codom f y), image y = a (iinv Hy).
Proof. by move=> y Hy; rewrite -image_f f_iinv. Qed.

Lemma pre_image : preim f image =1 a.
Proof. by move=> x; rewrite /= image_f. Qed.

End Image.

Lemma image_pred0 : forall (f : T -> T'), image f pred0 =1 pred0.
Proof. by move=> f x /=; apply/imageP; case. Qed.

Lemma image_pre : forall (f : T -> T') a',
  injective f -> image f (preim f a') =1 predI a' (codom f).
Proof.
move=> f a' Hf y; rewrite /= andbC; case Hy: (codom f y) => /=.
  by rewrite -(f_iinv Hy) image_f /=.
apply/idPn => [Hay]; case/idPn: Hy; exact (image_codom Hay).
Qed.

Fixpoint preim_seq (f : T -> T') (s : seq T') :=
  if s is x :: s' then
    (if pick (preim f (pred1 x)) is Some y then adds y else id)
      (preim_seq f s')
  else seq0.

Lemma maps_preim : forall (f : T -> T') (s : seq T'),
  subpred (mem s) (codom f) -> maps f (preim_seq f s) = s.
Proof.
move=> f; elim=> [|x s Hrec] //=; case: pickP => [y Dy|Hs'] Hs.
  rewrite /= (eqP Dy) Hrec // => z Hz; apply Hs; exact: predU1r.
by case/pred0P: (Hs x (predU1l _ (erefl x))).
Qed.

Lemma eq_image : forall (a b : pred T) (g f : T -> T'),
  a =1 b -> g =1 f -> image g a =1 image f b.
Proof.
move => a b g f Ha Hg x; apply/imageP/imageP; move=> [y Hin Heq].
  by exists y; [rewrite -Ha | rewrite -Hg].
by exists y; [rewrite Ha | rewrite Hg].
Qed.

End FunImage.

Prenex Implicits codom iinv image.

Notation "[ 'image' f 'of' A ]" := (image f [mem A])
  (at level 0, format "[ 'image'  f  'of'  A ]") : form_scope.

(* Standard finTypes *)

Section SeqFinType.

Variables (T : choiceType) (s : seq T).

Record seq_sub : Type := SeqSub { ssval : T; ssvalP : ssval \in s }.

Canonical Structure seq_sub_subType :=
  Eval hnf in [subType for ssval by seq_sub_rect].
Definition seq_sub_eqMixin := Eval hnf in [eqMixin of seq_sub by <:].
Canonical Structure seq_sub_eqType := Eval hnf in EqType seq_sub_eqMixin.
Definition seq_sub_choiceMixin := [choiceMixin of seq_sub by <:].
Canonical Structure seq_sub_choiceType :=
  Eval hnf in ChoiceType seq_sub_choiceMixin.

Definition seq_sub_enum : seq seq_sub := undup (pmaps insub s).

Lemma mem_seq_sub_enum : forall x, x \in seq_sub_enum.
Proof. by move=> x; rewrite mem_undup mem_pmaps -valK maps_f ?ssvalP. Qed.

Lemma val_seq_sub_enum : uniq s -> maps val seq_sub_enum = s.
Proof.
move=> Us; rewrite /seq_sub_enum undup_uniq ?uniq_pmap_sub //.
rewrite (pmaps_filter (@insubK _ _ _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition seq_sub_pickle x := index x seq_sub_enum.
Definition seq_sub_unpickle n := sub None (maps some seq_sub_enum) n.
Lemma seq_sub_pickleK : pcancel seq_sub_pickle seq_sub_unpickle.
Proof.
rewrite /seq_sub_unpickle => x.
by rewrite (sub_maps x) ?sub_index ?index_mem ?mem_seq_sub_enum.
Qed.

Definition seq_sub_countMixin := CountMixin seq_sub_pickleK.
Canonical Structure seq_sub_countType :=
  Eval hnf in CountType seq_sub_countMixin.
Canonical Structure seq_sub_subCountType := [subCountType of seq_sub].
Definition seq_sub_finMixin := UniqFinMixin (uniq_undup _) mem_seq_sub_enum.
Canonical Structure seq_sub_finType := Eval hnf in FinType seq_sub_finMixin.

End SeqFinType.

Lemma unit_enumP : Finite.axiom eq_op [::tt]. Proof. by case. Qed.
Definition unit_finMixin := FinMixin unit_enumP.
Canonical Structure unit_finType := Eval hnf in FinType unit_finMixin.
Lemma card_unit : #|{: unit}| = 1. Proof. by rewrite cardT enumT unlock. Qed.

Lemma bool_enumP : Finite.axiom eq_op [:: true; false]. Proof. by case. Qed.
Definition bool_finMixin := FinMixin bool_enumP.
Canonical Structure bool_finType := Eval hnf in FinType bool_finMixin.
Lemma card_bool : #|{: bool}| = 2. Proof. by rewrite cardT enumT unlock. Qed.

Section OptionFinType.

Variable T : finType.

Definition option_enum := None :: maps some (Finite.enum T).

Lemma option_enumP : Finite.axiom eq_op option_enum.
Proof. by case=> [x|]; rewrite /= count_maps (count_pred0, enumP). Qed.

Definition option_finMixin := FinMixin option_enumP.
Canonical Structure option_finType := Eval hnf in FinType option_finMixin.

Lemma card_option : #|{: option T}| = #|T|.+1.
Proof. by rewrite !cardT !enumT unlock /= !size_maps. Qed.

End OptionFinType.

Section TransferFinType.

Variables (eT : countType) (fT : finType) (f : eT -> fT).

Lemma pcan_enumP : forall g,
  pcancel f g -> Finite.axiom eq_op (undup (pmaps g (Finite.enum fT))).
Proof.
move=> g fK x; rewrite count_pred1_uniq ?uniq_undup // mem_undup.
by rewrite mem_pmaps -fK maps_f // -enumT mem_enum.
Qed.

Definition PcanFinMixin g fK := FinMixin (@pcan_enumP g fK).

Definition CanFinMixin g (fK : cancel f g) := PcanFinMixin (can_pcan fK).

End TransferFinType.

Section SubFinType.

Variables (T : choiceType) (P : pred T).
Import Finite.

Structure subFinType : Type := SubFinType {
  subFin_sort :> subCountType P;
  _ : @mixin_of subFin_sort eq_op
}.

Coercion subFinType_finType sT :=
  Eval hnf in pack (let: SubFinType _ m := sT return @mixin_of sT eq_op in m).
Canonical Structure subFinType_finType.

CoInductive subFinJM (sT : Type) (op : rel sT) : forall U, rel U -> Prop :=
  SubFinJM : subFinJM op op.

Definition subFinType_for scT :=
  let k _ c :=
    let: Class c' m := c return subFinJM _ (Equality.op c) -> _ in
    fun eqU => (let: SubFinJM in subFinJM _ opU := eqU return mixin_of opU -> _
    in @SubFinType scT) m
  in unpack k.

End SubFinType.

(* This assumes that T has both finType and subCountType structures. *)
Notation "[ 'subFinType' 'of' T ]" := (subFinType_for (@SubFinJM T _))
  (at level 0, format "[ 'subFinType'  'of'  T ]") : form_scope.

Canonical Structure seq_sub_subFinType T s :=
  Eval hnf in [subFinType of @seq_sub T s].

Section FinTypeForSub.

Variables (T : finType) (P : pred T) (sT : subCountType P).

Definition sub_enum : seq sT := pmaps insub (Finite.enum T).

Lemma mem_sub_enum : forall u, u \in sub_enum.
Proof. by move=> u; rewrite mem_pmap_sub -enumT mem_enum. Qed.

Lemma uniq_sub_enum : uniq sub_enum.
Proof. by rewrite uniq_pmap_sub // -enumT uniq_enum. Qed.

Lemma val_sub_enum : maps val sub_enum = enum P.
Proof.
rewrite pmaps_filter; last exact: insubK.
by apply: eq_filter => x; exact: isSome_insub.
Qed.

(* We can't declare a canonical structure here because we've already *)
(* stated that subType_sort and FinType.sort unify via to the        *)
(* subType_finType structure.                                        *)

Definition SubFinMixin := UniqFinMixin uniq_sub_enum mem_sub_enum.

Lemma card_sub : #|FinType SubFinMixin| = #|[pred x | P x]|.
Proof. by rewrite !cardE enumT unlock -(size_maps val) val_sub_enum. Qed.

Lemma eq_card_sub : forall A : pred (FinType SubFinMixin),
  A =i predT -> #|A| = #|[pred x | P x]|.
Proof. by have:= eq_card_trans card_sub. Qed.

End FinTypeForSub.

(* This assumes that T has a subCountType structure over a type that  *)
(* has a finType structure.                                           *)
Notation "[ 'finMixin' 'of' T 'by' <: ]" :=
    (SubFinMixin _ : @Finite.mixin_of T _)
  (at level 0, format "[ 'finMixin'  'of'  T  'by'  <: ]") : form_scope.

(* Regression for the subFinType stack
Record myb : Type := MyB {myv : bool; _ : ~~ myv}.
Canonical Structure myb_sub := Eval hnf in [subType for myv by myb_rect].
Definition myb_eqm := Eval hnf in [eqMixin of myb by <:].
Canonical Structure myb_eq := Eval hnf in EqType myb_eqm.
Definition myb_chm := [choiceMixin of myb by <:].
Canonical Structure myb_ch := Eval hnf in ChoiceType myb_chm.
Definition myb_cntm := [countMixin of myb by <:].
Canonical Structure myb_cnt := Eval hnf in CountType myb_cntm.
Canonical Structure myb_scnt := Eval hnf in [subCountType of myb].
Definition myb_finm := [finMixin of myb by <:].
Canonical Structure myb_fin := Eval hnf in FinType myb_finm.
Canonical Structure myb_sfin := Eval hnf in [subFinType of myb].
Print Canonical Projections.
Print myb_fin.
*)

Section CardSig.

Variables (T : finType) (P : pred T).

Definition sig_finMixin := [finMixin of {x | P x} by <:].
Canonical Structure sig_finType := Eval hnf in FinType sig_finMixin.
Canonical Structure sig_subFinType := Eval hnf in [subFinType of {x | P x}].

Lemma card_sig : #|{: {x | P x}}| = #|[pred x | P x]|.
Proof. exact: card_sub. Qed.

End CardSig.

Section OrdinalSub.

Variable n : nat.

Inductive ordinal : predArgType := Ordinal m of m < n.

Coercion nat_of_ord i := let: Ordinal m _ := i in m.

Canonical Structure ordinal_subType :=
  [subType for nat_of_ord by ordinal_rect].
Definition ordinal_eqMixin := Eval hnf in [eqMixin of ordinal by <:].
Canonical Structure ordinal_eqType := Eval hnf in EqType ordinal_eqMixin.
Definition ordinal_choiceMixin := [choiceMixin of ordinal by <:].
Canonical Structure ordinal_choiceType :=
  Eval hnf in ChoiceType ordinal_choiceMixin.
Definition ordinal_countMixin := [countMixin of ordinal by <:].
Canonical Structure ordinal_countType :=
  Eval hnf in CountType ordinal_countMixin.
Canonical Structure ordinal_subCountType := [subCountType of ordinal].

Lemma ltn_ord : forall i : ordinal, i < n. Proof. exact: valP. Qed.

Lemma ord_inj : injective nat_of_ord. Proof. exact: val_inj. Qed.

Definition ord_enum : seq ordinal := pmaps insub (iota 0 n).

Lemma val_ord_enum : maps val ord_enum = iota 0 n.
Proof.
rewrite pmaps_filter; last exact: insubK.
by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
Qed.

Lemma uniq_ord_enum : uniq ord_enum.
Proof. by rewrite uniq_pmap_sub ?uniq_iota. Qed.

Lemma mem_ord_enum : forall i, i \in ord_enum.
Proof.
by move=> i; rewrite -(mem_maps ord_inj) val_ord_enum mem_iota ltn_ord.
Qed.

Definition ordinal_finMixin := UniqFinMixin uniq_ord_enum mem_ord_enum.
Canonical Structure ordinal_finType := Eval hnf in FinType ordinal_finMixin.
Canonical Structure ordinal_subFinType := Eval hnf in [subFinType of ordinal].

End OrdinalSub.

Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").

Hint Resolve ltn_ord.

Section OrdinalEnum.

Variable n : nat.

Lemma val_enum_ord : maps val (enum 'I_n) = iota 0 n.
Proof. by rewrite enumT unlock val_ord_enum. Qed.

Lemma size_enum_ord : size (enum 'I_n) = n.
Proof. by rewrite -(size_maps val) val_enum_ord size_iota. Qed.

Lemma card_ord : #|'I_n| = n.
Proof. by rewrite cardE size_enum_ord. Qed.

Lemma sub_enum_ord : forall i0 m, m < n -> sub i0 (enum 'I_n) m = m :> nat.
Proof.
by move=> *; rewrite -(sub_maps _ 0) (size_enum_ord, val_enum_ord) // sub_iota.
Qed.

Lemma sub_ord_enum : forall i0 i : 'I_n, sub i0 (enum 'I_n) i = i.
Proof. move=> i0 i; apply: val_inj; exact: sub_enum_ord. Qed.

Lemma index_enum_ord : forall i : 'I_n, index i (enum 'I_n) = i.
Proof.
move=> i.
by rewrite -{1}(sub_ord_enum i i) index_uniq ?(uniq_enum, size_enum_ord).
Qed.

End OrdinalEnum.

Lemma widen_ordP : forall n m (i : 'I_n), n <= m -> i < m.
Proof. move=> *; exact: leq_trans. Qed.
Definition widen_ord n m le_n_m i := Ordinal (@widen_ordP n m i le_n_m).

Lemma cast_ordP : forall n m (i : 'I_n), n = m -> i < m.
Proof. by move=> n m i <-. Qed.
Definition cast_ord n m eq_n_m i := Ordinal (@cast_ordP n m i eq_n_m).

Section EnumRank.

Variable T : finType.

Lemma enum_rank_subproof : forall x : T, index x (enum T) < #|T|.
Proof. by move=> x; rewrite cardE index_mem mem_enum. Qed.

Definition enum_rank (x : T) := Ordinal (enum_rank_subproof x).

Lemma enum_default : 'I_(#|T|) -> T.
Proof. by rewrite cardE; case: (enum T) => [|//] []. Qed.

Definition enum_val i := sub (enum_default i) (enum T) i.

Lemma enum_val_sub : forall x i, enum_val i = sub x (enum T) i.
Proof.
move=> x i; apply: set_sub_default; rewrite cardE in i *; exact: ltn_ord.
Qed. 

Lemma sub_enum_rank : forall x, cancel enum_rank (sub x (enum T)).
Proof. by move=> x y; rewrite sub_index ?mem_enum. Qed.

Lemma enum_rankK : cancel enum_rank enum_val.
Proof. move=> x; exact: sub_enum_rank. Qed.

Lemma enum_valK : cancel enum_val enum_rank.
Proof.
move=> x; apply: ord_inj.
by rewrite /= index_uniq // -?cardE (uniq_enum, valP x).
Qed.

Lemma enum_rank_inj : injective enum_rank.
Proof. exact: can_inj enum_rankK. Qed.

Lemma enum_val_inj : injective enum_val.
Proof. exact: can_inj enum_valK. Qed.

Lemma enum_rank_bij : bijective enum_rank.
Proof. by move: enum_rankK enum_valK; exists enum_val. Qed.

Lemma enum_val_bij : bijective enum_val.
Proof. by move: enum_rankK enum_valK; exists enum_rank. Qed.

End EnumRank.

Lemma enum_rank_ord : forall n i, enum_rank i = cast_ord (esym (card_ord n)) i.
Proof. by move=> n i; apply: val_inj; rewrite /= index_enum_ord. Qed.

Lemma enum_val_ord : forall n i, enum_val i = cast_ord (card_ord n) i.
Proof.
move=> n i; apply: canLR (@enum_rankK _) _; apply: val_inj.
by rewrite enum_rank_ord.
Qed.

(* The integer bump / unbump operations. *)

Definition bump h i := (h <= i) + i.
Definition unbump h i := i - (h < i).

Lemma bumpK : forall h, cancel (bump h) (unbump h).
Proof.
rewrite /bump /unbump => h i; case: (leqP h i) => Hhi.
  by rewrite ltnS Hhi subn1.
by rewrite ltnNge ltnW ?subn0.
Qed.

Lemma neq_bump : forall h i, h != bump h i.
Proof.
move=> h i; rewrite /bump eqn_leq.
by case: (leqP h i) => Hhi; [rewrite ltnNge Hhi andbF | rewrite leqNgt Hhi].
Qed.

Lemma unbumpK : forall h, {in predC1 h, cancel (unbump h) (bump h)}.
Proof.
rewrite /bump /unbump => h i; move/eqP; move/nesym=> Dhi.
case: (ltngtP h i) => // Hhi; last by rewrite subn0 leqNgt Hhi.
by rewrite -ltnS subn1 (ltn_predK Hhi) Hhi add1n (ltn_predK Hhi).
Qed.

(* The lift operations on ordinals; to avoid a messy dependent type, *)
(* unlift is a partial operation (returns an option).                *)

Lemma lift_subproof : forall n h (i : 'I_(n.-1)), bump h i < n.
Proof.
by case=> [|n] h [i //= Hi]; rewrite /bump; case: (h <= _); last exact: ltnW.
Qed.

Definition lift n (h : 'I_n) (i : 'I_(n.-1)) := Ordinal (lift_subproof h i).

Lemma unlift_subproof : forall n (h : 'I_n) (u : {j : 'I_n| j != h}),
  unbump h (val u) < n.-1.
Proof.
move=> n h [j] /=; move/unbumpK; rewrite -ltnS (ltn_predK (valP j)) /bump.
case: (leqP h _) => [_|lt_j'_h _]; first by rewrite add1n => ->.
exact: leq_ltn_trans lt_j'_h _.
Qed.

Definition unlift n (h i : 'I_n) :=
  omap (fun u : {j | j != h} => Ordinal (unlift_subproof u)) (insub i).

CoInductive unlift_spec n (h i : 'I_n) : option 'I_(n.-1) -> Type :=
  | UnliftSome j of i = lift h j : unlift_spec h i (Some j)
  | UnliftNone   of i = h        : unlift_spec h i None.

Lemma unliftP : forall n (h i : 'I_n), unlift_spec h i (unlift h i).

Proof.
rewrite /unlift => n h i; case: insubP => [u nhi | ] def_i /=; constructor.
  by apply: val_inj; rewrite /= def_i unbumpK.
by rewrite negbK in def_i; exact/eqP.
Qed.

Lemma neq_lift : forall n (h : 'I_n) i, h != lift h i.
Proof. by move=> n h i; exact: neq_bump. Qed.

Lemma unlift_none : forall n (h : 'I_n), unlift h h = None.
Proof. by move=> n h; case: unliftP => // j Dh; case/eqP: (neq_lift h j). Qed.

Lemma unlift_some : forall n (h i : 'I_n),
  h != i -> {j | i = lift h j & unlift h i = Some j}.
Proof.
move=> n h i; rewrite eq_sym; move/eqP=> Hi.
by case Dui: (unlift h i) / (unliftP h i) => [j Dh|//]; exists j.
Qed.

Lemma lift_inj : forall n (h : 'I_n), injective (lift h).
Proof.
move=> n h i1 i2; move/eqP; rewrite [_ == _](can_eq (@bumpK _)) => eq_i12.
exact/eqP.
Qed.

Lemma liftK : forall n (h : 'I_n), pcancel (lift h) (unlift h).
Proof.
by move=> n h i; case: (unlift_some (neq_lift h i)) => j; move/lift_inj->.
Qed.

(* Shifting and splitting indices, for cutting and pasting arrays *)

Lemma lshift_subproof : forall m n (i : 'I_m), i < m + n.
Proof. move=> m n i; apply: leq_trans (valP i) _; exact: leq_addr. Qed.

Lemma rshift_subproof : forall m n (i : 'I_n), m + i < m + n.
Proof. by move=> m n i; rewrite ltn_add2l. Qed.

Definition lshift m n (i : 'I_m) := Ordinal (lshift_subproof n i).
Definition rshift m n (i : 'I_n) := Ordinal (rshift_subproof m i).

Lemma split_subproof : forall m n (i : 'I_(m + n)), i >= m -> i - m < n.
Proof. by move=> m n i; move/leq_subS <-; rewrite leq_sub_add. Qed.

Definition split m n (i : 'I_(m + n)) : 'I_m + 'I_n :=
  match ltnP (i) m with
  | LtnNotGeq lt_i_m =>  inl _ (Ordinal lt_i_m)
  | GeqNotLtn ge_i_m =>  inr _ (Ordinal (split_subproof ge_i_m))
  end.

CoInductive split_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | SplitLo (j : 'I_m) of i = j :> nat     : split_spec i (inl _ j) true
  | SplitHi (k : 'I_n) of i = m + k :> nat : split_spec i (inr _ k) false.

Lemma splitP : forall m n (i : 'I_(m + n)), split_spec i (split i) (i < m).
Proof.
rewrite /split {-3}/leq => m n i.
by case: (@ltnP i m) => cmp_i_m //=; constructor; rewrite ?subnK.
Qed.

Definition unsplit m n (jk : 'I_m + 'I_n) :=
  match jk with inl j => lshift n j | inr k => rshift m k end.

Lemma ltn_unsplit : forall m n (jk : 'I_m + 'I_n), (unsplit jk < m) = jk.
Proof. by move=> m n [j|k]; rewrite /= ?ltn_ord // ltnNge leq_addr. Qed.

Lemma splitK : forall m n, cancel (@split m n) (@unsplit m n).
Proof. by move=> m n i; apply: val_inj; case: splitP. Qed.

Lemma unsplitK : forall m n, cancel (@unsplit m n) (@split m n).
Proof.
move=> m n jk; have:= ltn_unsplit jk.
by case: splitP; case: jk => //= i j; last move/addnI; move/ord_inj->.
Qed.

Section OrdinalPos.

Variable n : pos_nat.

Definition ord0 := Ordinal (pos_natP n).

Lemma ord_maxP : n.-1 < n. Proof. by rewrite prednK. Qed. 
Definition ord_max := Ordinal ord_maxP.

Lemma leq_ord : forall i : 'I_n, i <= n.-1.
Proof. by move=> i; rewrite -ltnS prednK ?ltn_ord. Qed.

Lemma ord_subP : forall m, n.-1 - m < n.
Proof.  by move=> m; rewrite -{2}[n : nat]prednK // ltnS leq_subr. Qed.
Definition ord_sub m := Ordinal (ord_subP m).

Definition ord_opp (i : 'I_n) := ord_sub i.

Lemma sub_ordK : forall i : 'I_n, n.-1 - (n.-1 - i) = i.
Proof. by move=> i; rewrite subKn ?leq_ord. Qed.

Lemma ord_oppK : involutive ord_opp.
Proof. move=> i; apply: val_inj; exact: sub_ordK. Qed.

Definition inord m : 'I_n := insubd ord0 m.

Lemma inordK : forall m, m < n -> inord m = m :> nat.
Proof. by move=> m lt_m; rewrite val_insubd lt_m. Qed.

Lemma inord_val : forall i : 'I_n, inord i = i.
Proof. by move=> i; rewrite /inord /insubd valK. Qed.

Lemma enum_ordS : enum 'I_n = ord0 :: maps (lift ord0) (enum 'I_(n.-1)).
Proof.
apply: (inj_maps val_inj); rewrite val_enum_ord /= -maps_comp.
by rewrite (maps_comp (addn 1)) val_enum_ord -iota_addl -{1}(@prednK n).
Qed.

End OrdinalPos.

Implicit Arguments ord0 [n].
Implicit Arguments ord_max [n].
Implicit Arguments inord [n].

Prenex Implicits ord_opp.

Section ProdFinType.

Variable T1 T2 : finType.

Definition prod_enum :=
  foldr (fun x1 => cat (maps (pair x1) (enum T2))) [::] (enum T1).

Lemma predX_prod_enum : forall (A1 : pred T1) (A2 : pred T2),
  count [predX A1 & A2] prod_enum = #|A1| * #|A2|.
Proof.
move=> A1 A2; rewrite !cardE -!count_filter -!enumT /prod_enum.
elim: (enum T1) => //= x1 s1 IHs; rewrite count_cat {}IHs count_maps /preim /=.
by case: (x1 \in A1); rewrite ?count_pred0.
Qed.

Lemma prod_enumP : Finite.axiom eq_op prod_enum.
Proof.
by case=> x1 x2; rewrite (predX_prod_enum (pred1 x1) (pred1 x2)) !card1.
Qed.

Definition prod_finMixin := FinMixin prod_enumP.
Canonical Structure prod_finType := Eval hnf in FinType prod_finMixin.

Lemma cardX : forall (A1 : pred T1) (A2 : pred T2),
  #|[predX A1 & A2]| = #|A1| * #|A2|.
Proof.
by move=> A1 A2; rewrite -predX_prod_enum unlock -count_filter unlock. 
Qed.

Lemma card_prod : #|{: T1 * T2}| = #|T1| * #|T2|.
Proof. by rewrite -cardX; apply: eq_card; case. Qed.

Lemma eq_card_prod : forall A : pred (T1 * T2),
   A =i predT -> #|A| = #|T1| * #|T2|.
Proof. by have:= eq_card_trans card_prod. Qed.

End ProdFinType.

Section TagFinType.

Variables (I : finType) (T_ : I -> finType).

Definition tag_enum :=
  let tagged_enum i := maps (Tagged T_) (Finite.enum (T_ i)) in
  flatten (maps tagged_enum (Finite.enum I)).

Lemma tag_enumP : Finite.axiom eq_op tag_enum.
Proof.
case=> i x; rewrite -(enumP i) /tag_enum -enumT.
elim: (enum I) => //= j e IHe.
rewrite count_cat count_maps {}IHe; congr (_ + _).
rewrite count_filter -cardE; case: eqP => [-> | ne_j_i].
  by apply: (@eq_card1 _ x) => y; rewrite -topredE /= tagged_asE eqxx.
by apply: eq_card0 => y; apply/andP; case; move/eqP.
Qed.

Definition tag_finMixin := FinMixin tag_enumP.
Canonical Structure tag_finType := Eval hnf in FinType tag_finMixin.

Lemma card_tagged :
  #|{: {i : I & T_ i}}| = sumn (maps (fun i => #|T_ i|) (enum I)).
Proof.
rewrite cardE !enumT unlock size_flatten /shape -maps_comp.
by congr (sumn _); apply: eq_maps => i; rewrite /= size_maps -enumT -cardE.
Qed.

End TagFinType.

Section SumFinType.

Variables T1 T2 : finType.

Definition sum_enum :=
  maps (@inl _ _) (Finite.enum T1) ++ maps (@inr _ _) (Finite.enum T2).

Lemma uniq_sum_enum : uniq sum_enum.
Proof.
rewrite uniq_cat -!enumT !(uniq_enum, uniq_maps) ?andbT => [|? ? []|? ? []] //.
by apply/hasP=> [[u]]; case/mapsP=> x _ <-; case/mapsP.
Qed.

Lemma mem_sum_enum : forall u, u \in sum_enum.
Proof. by case=> x; rewrite mem_cat -!enumT maps_f ?mem_enum ?orbT. Qed.

Definition sum_finMixin := UniqFinMixin uniq_sum_enum mem_sum_enum.
Canonical Structure sum_finType := Eval hnf in FinType sum_finMixin.

Lemma card_sum : #|{: T1 + T2}| = #|T1| + #|T2|.
Proof. by rewrite !cardT !enumT unlock size_cat !size_maps. Qed.

End SumFinType.

Section BijectionCard.

Lemma can_card_leq :  forall (T T' : finType) (f : T -> T') (g : T' -> T),
  cancel f g -> #|T| <= #|T'|.
Proof.
move=> T T' f g Hfg; rewrite (cardT T') -(size_maps g).
apply: (leq_trans (subset_leq_card _) (card_size _)).
by apply/subsetP => x _; apply/mapsP; exists (f x); rewrite ?mem_enum.
Qed.

Lemma bij_eq_card_predT : forall T T' : finType,
  (exists f : T -> T', bijective f) -> #|T| = #|T'|.
Proof.
move=> T T' [f [g Hfg Hgf]]; apply: eqP.
by rewrite eqn_leq (can_card_leq Hfg) (can_card_leq Hgf).
Qed.

Lemma eq_card_predT : forall T T' : finType,
  T = T' :> Type -> #|T| = #|T'|.
Proof.
move=> T [T' mT' T''] /= eqTT'; rewrite -{T'}eqTT' in mT' *.
by apply: bij_eq_card_predT; do 2 exists (@id T).
Qed.

Lemma bij_eq_card : forall (T T' : finType) (A : pred T) (A' : pred T'),
 (exists f : {x | x \in A} -> {y | y \in A'}, bijective f) -> #|A| = #|A'|.
Proof. by move=> T T' A A'; move/bij_eq_card_predT; rewrite !card_sub. Qed.

Definition assoc_finType (T1 T2 : finType) (eqcT12 : #|T1| = #|T2|) x1 :=
  enum_val (cast_ord eqcT12 (enum_rank x1)).

Lemma assoc_finTypeK : forall T1 T2 Ed12 Ed21,
  cancel (@assoc_finType T1 T2 Ed12) (@assoc_finType T2 T1 Ed21).
Proof.
rewrite /assoc_finType => T1 T2 Ed12 Ed21 x.
by rewrite enum_valK (enum_val_sub x) sub_enum_rank.
Qed.

Lemma eq_card_predT_bij : forall T1 T2 : finType,
  #|T1| = #|T2| -> {f : T1 -> T2 &  {g | cancel f g &  cancel g f}}.
Proof.
move=> T1 T2 E12; exists (assoc_finType E12).
exists (assoc_finType (esym E12)); exact: assoc_finTypeK.
Qed.

Lemma eq_card_bij : forall (T T' : finType) (A : pred T) (A' : pred T'),
   #|A| = #|A'| ->
 {f : {x | x \in A} -> {y | y \in A'} & {g | cancel f g &  cancel g f}}.
Proof.
move=> T T' A A'; rewrite -card_sig -(card_sig A'); exact: eq_card_predT_bij.
Qed.

End BijectionCard.

Section CardFunImage.

Variables (T T' : finType) (f : T -> T').

Lemma leq_image_card : forall A : pred T, #|[image f of A]| <= #|A|.
Proof.
move=> A; rewrite (cardE A) -(size_maps f); apply: leq_trans (card_size _).
apply: subset_leq_card; apply/subsetP => y; case/imageP=> x Ax ->{y}.
by rewrite maps_f ?mem_enum.
Qed.

Lemma card_in_image : forall A : pred T, {in A &, injective f} ->
  #|[image f of A]| = #|A|.
Proof.
move=> A injf; apply: bij_eq_card.
have f1_def: forall w : {y | image f A y}, A (diinv (valP w)).
  by case=> y fAy; rewrite a_diinv.
have f2_def: forall w : {x | A x}, image f A (f (val w)).
  by case=> x Ax; rewrite mem_image.
pose f1 w := exist A _ (f1_def w); exists f1.
pose f2 w := exist (image f A) _ (f2_def w).
by exists f2; case=> *; apply: val_inj; rewrite /= (f_diinv, diinv_f).
Qed.

Hypothesis injf : injective f.

Lemma card_image : forall A : pred T, #|[image f of A]| = #|A|.
Proof. move=> A; apply: card_in_image; exact: in2W. Qed.

Lemma card_codom : #|codom f| = #|T|.
Proof.
rewrite -(card_image T); apply: eq_card => y.
by apply/existsP/imageP => [[x]|[x _ ->]]; first move/eqP; exists x.
Qed.

Lemma card_preim : forall A',  #|preim f A'| = #|predI (codom f) A'|.
Proof.
move=> A'; rewrite -card_image /=; apply: eq_card => y.
by rewrite [y \in _]image_pre //= andbC.
Qed.

End CardFunImage.

Section FinCancel.

Variables (T : finType) (f g : T -> T).

Lemma injF_codom : injective f -> forall x, codom f x.
Proof. 
by move=> injf; apply/subset_cardP; rewrite ?card_codom ?subset_predT.
Qed.

Lemma injF_bij : injective f -> bijective f.
Proof.
move=> injf; pose f' x := iinv (injF_codom injf x).
by exists f' => x; rewrite /f' (iinv_f, f_iinv).
Qed.

Hypothesis fK : cancel f g.

Let injf := can_inj fK.

Lemma canF_sym : cancel g f.
Proof. exact/(bij_can_sym (injF_bij injf)). Qed.

Lemma canF_LR : forall x y, x = g y -> f x = y.
Proof. move=> x y; exact: canLR canF_sym. Qed.

Lemma canF_RL : forall x y, g x = y -> x = f y.
Proof. move=> x y; exact: canRL canF_sym. Qed.

Lemma canF_eq : forall x y, (f x == y) = (x == g y).
Proof. exact (can2_eq fK canF_sym). Qed.

End FinCancel.


