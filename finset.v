Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import div.
Require Import fintype.
Require Import finfun.
Require Import bigops.
Require Import ssralg.
Require Import connect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SetType.

Variable T : finType.

Record set : Type := mkSet {ffun_of_set : {ffun pred T}}.

Definition set_for of phant T : predArgType := set.
Identity Coercion set_for_set : set_for >-> set.

Canonical Structure set_subType := NewType ffun_of_set set_rect vrefl.
Canonical Structure set_eqType := Eval hnf in [subEqType for ffun_of_set].
Canonical Structure set_finType := Eval hnf in [finType of set by :>].
Canonical Structure set_subFinType := Eval hnf in [subFinType of set].

Definition set_of_def (P : pred T) : set := mkSet (ffun_of P).

Definition pred_of_set_def (A : set) : T -> bool := val A.

End SetType.

Delimit Scope set_scope with SET.
Bind Scope set_scope with set.
Bind Scope set_scope with set_for.
Open Scope set_scope.
Arguments Scope ffun_of_set [_ set_scope].

Notation "{ 'set' T }" := (set_for (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

Lemma set_of_key : unit. Proof. by []. Qed.
Definition set_of : forall T : finType, pred T -> {set T} :=
  locked_with set_of_key set_of_def.

Notation "[ 'set' x : T | P ]" := (set_of (fun x : T => P))
  (at level 0, x at level 69, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x at level 69, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x \in A | P ]" := [set x | (x \in A) && P]
  (at level 0, x at level 69, format "[ 'set'  x  \in  A  |  P ]") : set_scope.
Notation "[ 'set' x \in A ]" := [set x | x \in A]
  (at level 0, x at level 69, format "[ 'set'  x  \in  A ]") : set_scope.

Lemma pred_of_set_key : unit. Proof. by []. Qed.
Definition pred_of_set : forall T, set T -> pred_class :=
  locked_with pred_of_set_key pred_of_set_def.

(* This lets us use subtypes of set, like group or coset, as predicates. *)
Coercion pred_of_set : set >-> pred_class.

(* Declare pred_of_set as a canonical instance of to_pred, but use the *)
(* coercion to resolve mem A to @mem (predPredType T) (pred_of_set A). *)
Canonical Structure set_predType T :=
  Eval hnf in @mkPredType _ (let s := set T in s) (@pred_of_set T).

(* Alternative: *)
(* Use specific canonical structures for sets. This allows to have  *)
(* smaller terms, because generic operators involve only two levels *)
(* of nesting rather than three here; also, this lets Coq unify     *)
(* sets with predType sorts after the fact.                         
Canonical Structure set_predType := Eval hnf in mkPredType pred_of_set.
Canonical Structure set_for_predType := Eval hnf in [predType of sT].
  Not selected because having two different ways of coercing to
  pred causes apply to fail, e.g., the group1 lemma does not apply
  to a 1 \in G with G : group gT when this goal results from
  rewriting A = G in 1 \in A, with A : set gT.                      *)

Section setOpsDefs.

Variable T : finType.
Implicit Types a x : T.
Implicit Types A B : {set T}.

Definition set0 := [set x : T | false].
Definition setT := [set x : T | true].
Definition set1 a1 := [set x | x == a1].
Definition set2 a1 a2 := [set x | (x == a1) || (x == a2)].
Definition set3 a1 a2 a3 := [set x | [|| x == a1, x == a2 | x == a3]].
Definition set4 a1 a2 a3 a4 :=
  [set x | [|| x == a1, x == a2, x == a3 | x == a4]].
Definition setC1 a := [set x | x != a].
Definition setU A B := [set x | (x \in A) || (x \in B)].
Definition setU1 a A := [set x | (x == a) || (x \in A)].
Definition setI A B := [set x | (x \in A) && (x \in B)].
Definition setC A := [set x | x \notin A].
Definition setD A B:= [set x | (x \notin B) && (x \in A)].
Definition setD1 A a := [set x | (x != a) && (x \in A)].

End setOpsDefs.

Implicit Arguments set0 [T].
Implicit Arguments setT [T].
Prenex Implicits set0 setT.

Notation "[ 'set' a1 ]" := (set1 a1)
  (at level 0, a1 at level 69, format "[ 'set'  a1 ]") : set_scope.
Notation "[ 'set' a1 ; a2 ]" := (set2 a1 a2)
  (at level 0, a1, a2 at level 69, format "[ 'set'  a1 ;  a2 ]") : set_scope.
Notation "[ 'set' a1 ; a2 ; a3 ]" := (set3 a1 a2 a3)
  (at level 0, a1, a2, a3 at level 69,
   format "[ 'set'  a1 ;  a2 ;  a3 ]") : set_scope.
Notation "[ 'set' a1 ; a2 ; a3 ; a4 ]" := (set4 a1 a2 a3 a4)
  (at level 0, a1, a2, a3, a4 at level 69,
   format "[ 'set'  a1 ;  a2 ;  a3 ;  a4 ]") : set_scope.
Notation "[ 'set' ~ a ]" := (setC1 a)
  (at level 0, a at level 69, format "[ 'set' ~  a ]") : set_scope.
Notation "a |: A" := (setU1 a A) (at level 52, left associativity) : set_scope.
Notation "A :|: B" := (setU A B) (at level 52, left associativity) : set_scope.
Notation "A :\: B" := (setD A B) (at level 50) : set_scope.
Notation "A :\ a" := (setD1 A a) (at level 50) : set_scope.
Notation "A :&: B" := (setI A B) (at level 48, left associativity) : set_scope.
Notation "~: A" := (setC A) (at level 35, right associativity) : set_scope.

Section BasicSetTheory.

Variable T : finType.
Implicit Type x : T.

Canonical Structure set_for_eqType := Eval hnf in [eqType of {set T}].
Canonical Structure set_for_finType := Eval hnf in [finType of {set T}].
Canonical Structure set_for_subType := Eval hnf in [subType of {set T}].
Canonical Structure set_for_subFinType := Eval hnf in [subFinType of {set T}].

Lemma in_set : forall P x, x \in set_of P = P x.
Proof. by move=> P x; rewrite /set_of /pred_of_set !unlock [x \in _]ffunE. Qed.

Lemma in_setT : forall x, x \in setT. Proof. by move=> x; rewrite in_set. Qed.

Lemma setP : forall A B : {set T}, A =i B <-> A = B.
Proof.
move=> A B; split=> [eqAB|-> //]; apply: val_inj; apply/ffunP=> x.
by have:= eqAB x; rewrite /pred_of_set unlock.
Qed.

End BasicSetTheory.

Definition inE := (inE, in_set).
Hint Resolve in_setT.

Section setOps.

Variable T : finType.
Implicit Types a x : T.
Implicit Types A B C D : {set T}.


Lemma eqset_sub : forall A B : {set T},
  (A == B) = (A \subset B) && (B \subset A).
Proof. by move=> A B; apply/eqP/subset_eqP; move/setP. Qed.

Lemma eqset_sub_card : forall A B : {set T},
  (A == B) = (A \subset B) && (#|B| <= #|A|).
Proof.
move=> A B; rewrite eqset_sub; case sAB: (A \subset B) => //=.
by rewrite -(subset_leqif_card sAB) eqn_leq (subset_leqif_card sAB).
Qed.

Lemma in_set0 : forall x, x \in set0 = false.
Proof. by move=> x; rewrite inE. Qed.

Lemma sub0set : forall A, set0 \subset A.
Proof. by move=> A; apply/subsetP=> x; rewrite inE. Qed.

Lemma subset0 : forall A, (A \subset set0) = (A == set0).
Proof. by move=> A; rewrite eqset_sub sub0set andbT. Qed.

Lemma subsetT : forall A, A \subset setT.
Proof. by move=> A; apply/subsetP=> x; rewrite inE. Qed.

Lemma subTset : forall A, (setT \subset A) = (A == setT).
Proof. by move=> A; rewrite eqset_sub subsetT. Qed.

Lemma set1P : forall x a, reflect (x = a) (x \in [set a]).
Proof. move=> x a; rewrite inE; exact: eqP. Qed.

Lemma in_set1 : forall x a, (x \in [set a]) = (x == a).
Proof. move=> x a; exact: in_set. Qed.

Lemma set11 : forall x, x \in [set x].
Proof. by move=> x; rewrite inE. Qed.

Lemma setU1P : forall x a A, reflect (x = a \/ x \in A) (x \in a |: A).
Proof. move=> x a A; rewrite inE; exact: predU1P. Qed.

Lemma in_setU1 : forall x a A, (x \in a |: A) = (x == a) || (x \in A).
Proof. move=> x a A; exact: in_set. Qed.

Lemma set_adds : forall a s, [set x \in a :: s] = a |: [set x \in s].
Proof. by move=> a s; apply/setP=> x; rewrite !inE. Qed.

Lemma setU1E : forall a A, a |: A = [set a] :|: A.
Proof. by move=> a A; apply/setP=> y; rewrite !inE. Qed.

Lemma setU11 : forall x A, x \in x |: A.
Proof. by move=> *; rewrite inE eqxx. Qed.

Lemma setU1r : forall x a A, x \in A -> x \in a |: A.
Proof. by move=> x A a Ax; rewrite inE Ax orbT. Qed.

Lemma setU1S : forall a A B, A \subset B -> a |: A \subset a |: B.
Proof.
move=> a A B sAB; apply/subsetP=> x; rewrite !inE.
by case: (x == a); last exact: (subsetP sAB).
Qed.

Lemma in_setC1 : forall x a, (x \in [set~ a]) = (x != a).
Proof. move=> x a; exact: in_set. Qed.

Lemma setC1E : forall a, [set~ a] = ~: [set a].
Proof. by move=> a; apply/setP=> x; rewrite !inE. Qed.

Lemma setC11 : forall x, (x \in [set~ x]) = false.
Proof. by move=> *; rewrite inE eqxx. Qed.

Lemma setD1P : forall x a A, reflect (x != a /\ x \in A) (x \in A :\ a).
Proof. move=> x a A; rewrite inE; exact: andP. Qed.

Lemma in_setD1 : forall x a A, (x \in A :\ a) = (x != a) && (x \in A) .
Proof. move=> x a A; exact: in_set. Qed.

Lemma setD1E : forall A a, A :\ a = A :&: [set~ a].
Proof. by move=> A a; apply/setP=> x; rewrite !inE andbC. Qed.

Lemma setD1S : forall a A B, A \subset B -> A :\ a \subset B :\ a.
Proof.
move=> a A B sAB; apply/subsetP=> x; rewrite !inE.
by case: (x == a); last exact: (subsetP sAB).
Qed.

Lemma setD11 : forall x A, (x \in A :\ x) = false.
Proof. by move=> *; rewrite inE eqxx. Qed.

Lemma setD1K : forall a A, a \in A -> a |: (A :\ a) = A.
Proof. by move=> *; apply/setP=> x; rewrite !inE; case: eqP => // ->. Qed.

Lemma setU1K : forall a A, a \notin A -> (a |: A) :\ a = A.
Proof.
move=> a A; move/negPf=> nAa; apply/setP=> x.
by rewrite !inE; case: eqP => // ->.
Qed.

(* enumerations *)

Lemma set2P : forall x a1 a2, reflect (x = a1 \/ x = a2) (x \in [set a1; a2]).
Proof.
move=> x a1 a2; rewrite inE.
by do 2![case: eqP => ?; first by left; auto]; right; case.
Qed.

Lemma in_set2 : forall x a1 a2, (x \in [set a1; a2]) = (x == a1) || (x == a2).
Proof. move=> x a1 a2; exact: in_set. Qed.

Lemma set3P : forall x a1 a2 a3,
  reflect [\/ x = a1, x = a2 | x = a3] (x \in [set a1; a2; a3]).
Proof.
move=> x a1 a2 a3; rewrite inE; move: Or31 Or32 Or33.
by do 3![case: eqP => ?; first by left; auto]; right; case.
Qed.

Lemma in_set3 : forall x a1 a2 a3,
 (x \in [set a1; a2; a3]) = [|| x == a1, x == a2 | x == a3].
Proof. move=> x a1 a2 a3; exact: in_set. Qed.

Lemma set4P : forall x a1 a2 a3 a4,
  reflect [\/ x = a1, x = a2, x = a3 | x = a4] (x \in [set a1; a2; a3; a4]).
Proof.
move=> x a1 a2 a3 a4; rewrite inE; move: Or41 Or42 Or43 Or44.
by do 4![case: eqP => ?; first by left; auto]; right; case.
Qed.

Lemma in_set4 : forall x a1 a2 a3 a4,
 (x \in [set a1; a2; a3; a4]) = [|| x == a1, x == a2, x == a3 | x == a4].
Proof. move=> x a1 a2 a3 a4; exact: in_set. Qed.

Lemma set21 : forall a1 a2, a1 \in [set a1; a2].
Proof. by move=> *; rewrite inE eqxx. Qed.

Lemma set22 : forall a1 a2, a2 \in [set a1; a2].
Proof. by move=> *; rewrite inE eqxx orbT. Qed.

Lemma set31 : forall a1 a2 a3, a1 \in [set a1; a2; a3].
Proof. by move=> *; rewrite inE eqxx. Qed.

Lemma set32 : forall a1 a2 a3, a2 \in [set a1; a2; a3].
Proof. by move=> *; rewrite inE eqxx !orbT . Qed.

Lemma set33 : forall a1 a2 a3, a3 \in [set a1; a2; a3].
Proof. by move=> *; rewrite inE eqxx !orbT. Qed.

Lemma setUP : forall x A B, reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof. move => x A B; rewrite !inE; exact: orP. Qed.

Lemma in_setU : forall x A B, (x \in A :|: B) = (x \in A) || (x \in B).
Proof. move => x A B; exact: in_set. Qed.

Lemma setUC : forall A B, A :|: B = B :|: A.
Proof. by move=> A B; apply/setP => x; rewrite !inE orbC. Qed.

Lemma setUS : forall A B C, A \subset B -> C :|: A \subset C :|: B.
Proof.
move=> A B C sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSU : forall A B C, A \subset B -> A :|: C \subset B :|: C.
Proof. by move=> A B C sAB; rewrite -!(setUC C) setUS. Qed.

Lemma set0U : forall A, set0 :|: A = A.
Proof. by move=> A; apply/setP => x; rewrite !inE orFb. Qed.

Lemma setU0 : forall A, A :|: set0 = A.
Proof. by move=> A; rewrite setUC set0U. Qed.

Lemma setUA : forall A B C, A :|: (B :|: C) = A :|: B :|: C.
Proof. by move=> A B C; apply/setP => x; rewrite !inE orbA. Qed.

Lemma setUCA : forall A B C, A :|: (B :|: C) = B :|: (A :|: C).
Proof. by move=> A B C; rewrite !setUA (setUC B). Qed.

Lemma setUAC : forall A B C, A :|: B :|: C = A :|: C :|: B.
Proof. by move=> A B C; rewrite -!setUA (setUC B). Qed.

Lemma setTU : forall A, setT :|: A = setT.
Proof. by move=> A; apply/setP => x; rewrite !inE orTb. Qed.

Lemma setUT : forall A, A :|: setT = setT.
Proof. by move=> A; rewrite setUC setTU. Qed.

Lemma setUid : forall A, A :|: A = A.
Proof. by move=> A; apply/setP=> x; rewrite inE orbb. Qed.

Lemma setUUl : forall A B C, A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by move=> A B C; rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr : forall A B C, A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by move=> A B C; rewrite !(setUC A) setUUl. Qed.

(* intersect *)

Lemma setIP : forall x A B, reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof. move => x A B; rewrite !inE; exact: andP. Qed.

Lemma in_setI : forall x A B, (x \in A :&: B) = (x \in A) && (x \in B).
Proof. move => x A B; exact: in_set. Qed.

Lemma setIC : forall A B, A :&: B = B :&: A.
Proof. by move=> A B; apply/setP => x; rewrite !inE andbC. Qed.

Lemma setIS : forall A B C, A \subset B -> C :&: A \subset C :&: B.
Proof.
move=> A B C sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSI : forall A B C, A \subset B -> A :&: C \subset B :&: C.
Proof. by move=> A B C sAB; rewrite -!(setIC C) setIS. Qed.

Lemma setTI : forall A, setT :&: A = A.
Proof. by move=> A; apply/setP => x; rewrite !inE andTb. Qed.

Lemma setIT : forall A, A :&: setT = A.
Proof. by move=> A; rewrite setIC setTI. Qed.

Lemma set0I : forall A, set0 :&: A = set0.
Proof. by move=> A; apply/setP => x; rewrite !inE andFb. Qed.

Lemma setI0 : forall A, A :&: set0 = set0.
Proof. by move=> A; rewrite setIC set0I. Qed.

Lemma setIA : forall A B C, A :&: (B :&: C) = A :&: B :&: C.
Proof. by move=> A B C; apply/setP=> x; rewrite !inE andbA. Qed.

Lemma setICA : forall A B C, A :&: (B :&: C) = B :&: (A :&: C).
Proof. by move=> A B C; rewrite !setIA (setIC A). Qed.

Lemma setIAC : forall A B C, A :&: B :&: C = A :&: C :&: B.
Proof. by move=> A B C; rewrite -!setIA (setIC B). Qed.

Lemma setIid : forall A, A :&: A = A.
Proof. by move=> A; apply/setP=> x; rewrite inE andbb. Qed.

Lemma setIIl : forall A B C, A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by move=> A B C; rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr : forall A B C, A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by move=> A B C; rewrite !(setIC A) setIIl. Qed.

(* distribute /cancel *)

Lemma setIUr : forall A B C, A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof. by move=> A B C; apply/setP => x; rewrite !inE andb_orr. Qed.

Lemma setIUl : forall A B C, (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by move=> A B C; apply/setP => x; rewrite !inE andb_orl. Qed.

Lemma setUIr : forall A B C, A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof. by move=> A B C; apply/setP => x; rewrite !inE orb_andr. Qed.

Lemma setUIl : forall A B C, (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by move=> A B C; apply/setP => x; rewrite !inE orb_andl. Qed.

Lemma setUK : forall A B, (A :|: B) :&: A = A.
Proof. by move=> A B; apply/setP=> x; rewrite !inE orbK. Qed.

Lemma setKU : forall A B, A :&: (B :|: A) = A.
Proof. by move=> A B; apply/setP=> x; rewrite !inE orKb. Qed.

Lemma setIK : forall A B, (A :&: B) :|: A = A.
Proof. by move=> A B; apply/setP=> x; rewrite !inE andbK. Qed.

Lemma setKI : forall A B, A :|: (B :&: A) = A.
Proof. by move=> A B; apply/setP=> x; rewrite !inE andKb. Qed.

(* complement *)

Lemma setCP : forall x A, reflect (~ x \in A) (x \in ~: A).
Proof. move => x A; rewrite !inE; exact: negP. Qed.

Lemma in_setC : forall x A, (x \in ~: A) = (x \notin A).
Proof. move => x A; exact: in_set. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; apply/setP => x; rewrite !inE negbK. Qed.

Lemma setC_inj: injective (@setC T).
Proof. exact: can_inj setCK. Qed.

Lemma subsets_disjoint : forall A B, (A \subset B) = [disjoint A & ~: B].
Proof.
move=> A B; rewrite subset_disjoint.
by apply: eq_disjoint_r => x; rewrite !inE.
Qed.

Lemma disjoints_subset : forall A B, [disjoint A & B] = (A \subset ~: B).
Proof. by move=> A B; rewrite subsets_disjoint setCK. Qed.

Lemma setCS : forall A B, (~: A \subset ~: B) = (B \subset A).
Proof. by move=> A B; rewrite !subsets_disjoint setCK disjoint_sym. Qed.

Lemma setCU : forall A B, ~: (A :|: B) = ~: A :&: ~: B.
Proof. by move=> A B; apply/setP => x; rewrite !inE -negb_or. Qed.

Lemma setCI : forall A B, ~: (A :&: B) = ~: A :|: ~: B.
Proof. by move=> A B; apply/setP => x; rewrite !inE negb_and. Qed.

Lemma setUCr : forall A, A :|: (~: A) = setT.
Proof. by  move=> A; apply/setP => x; rewrite !inE orbN. Qed.

Lemma setICr : forall A, A :&: (~: A) = set0.
Proof. by  move=> A; apply/setP => x; rewrite !inE andbN. Qed.

Lemma setC0 : ~: set0 = setT :> {set T}.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setCT : ~: setT = set0 :> {set T}.
Proof. by rewrite -setC0 setCK. Qed.

(* difference *)

Lemma setDP : forall A B x, reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof. by move=> A B x; rewrite inE andbC; exact: andP. Qed.

Lemma in_setD : forall A B x, (x \in A :\: B) = (x \notin B) && (x \in A).
Proof. by move=> A B x; exact: in_set. Qed.

Lemma setDE : forall A B, A :\: B = A :&: ~: B.
Proof. by move=> A B; apply/setP => x; rewrite !inE andbC. Qed.

Lemma setSD : forall A B C, A \subset B -> A :\: C \subset B :\: C.
Proof. by move=> A B C; rewrite !setDE; exact: setSI. Qed.

Lemma setDS : forall A B C, A \subset B -> C :\: B \subset C :\: A.
Proof. by move=> A B C; rewrite !setDE -setCS; exact: setIS. Qed.

Lemma setD0 : forall A, A :\: set0 = A.
Proof. by move=> A; apply/setP=>x; rewrite !inE. Qed.

Lemma set0D : forall A, set0 :\: A = set0.
Proof. by move=> A; apply/setP=>x; rewrite !inE andbF. Qed.
 
Lemma setDT : forall A, A :\: setT = set0.
Proof. by move=> A; apply/setP=> x; rewrite !inE. Qed.

Lemma setTD : forall A, setT :\: A = ~: A.
Proof. by move=> A; apply/setP=> x; rewrite !inE andbT. Qed.
 
Lemma setDv : forall A, A :\: A = set0.
Proof. by move=> A; apply/setP=> x; rewrite !inE andNb. Qed.

Lemma setCD : forall A B, ~: (A :\: B) = ~: A :|: B.
Proof. by move=> A B; rewrite !setDE setCI setCK. Qed.

Lemma setDUl : forall A B C, (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof. by move=> A B C; rewrite !setDE setIUl. Qed.

Lemma setDUr : forall A B C, A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof. by move=> A B C; rewrite !setDE setCU setIIr. Qed.

Lemma setDIl : forall A B C, (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof. by move=> A B C; rewrite !setDE setIIl. Qed.

Lemma setDIr : forall A B C, A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof. by move=> A B C; rewrite !setDE setCI setIUr. Qed.

Lemma setDDl : forall A B C, (A :\: B) :\: C = A :\: (B :|: C).
Proof. by move=> A B C; rewrite !setDE setCU setIA. Qed.

Lemma setDDr : forall A B C, A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof. by move=> A B C; rewrite !setDE setCI setIUr setCK. Qed.

(* cardinal lemmas for sets *)

Lemma cardsE : forall P : pred T, #|[set x \in P]| = #|P|.
Proof. by move=> s; apply: eq_card => x; rewrite inE. Qed.

Lemma cards1 : forall x, #|[set x]| = 1.
Proof. by move=> x; rewrite cardsE card1. Qed.

Lemma cardsUI : forall A B, #|A :|: B| + #|A :&: B| = #|A| + #|B|.
Proof. by move=> A B; rewrite !cardsE cardUI. Qed.

Lemma cards0 : #|@set0 T| = 0.
Proof. by rewrite cardsE card0. Qed.

Lemma cardsT : #|@setT T| = #|T|.
Proof. by rewrite cardsE. Qed.

Lemma cardsID : forall B A, #|A :&: B| + #|A :\: B| = #|A|.
Proof. by move=> B A; rewrite !cardsE cardID. Qed.

Lemma cardsC : forall A, #|A| + #|~: A| = #|T|.
Proof. by move=> A; rewrite cardsE cardC. Qed.

Lemma cardsU1 : forall a A, #|a |: A| = (a \notin A) + #|A|.
Proof. by move=> a A; rewrite cardsE cardU1. Qed.

Lemma cards2 : forall a1 a2, #|[set a1; a2]| = (a1 != a2).+1.
Proof. by move=> x y; rewrite cardsE card2. Qed.

Lemma cardsC1 : forall a, #|[set~ a]| = #|T|.-1.
Proof. by move=> a; rewrite cardsE cardC1. Qed.

Lemma cardsD1 : forall a A, #|A| = (a \in A) + #|A :\ a|.
Proof. by move=> a A; rewrite cardsE -cardD1. Qed.

Lemma cards0_eq : forall A, #|A| = 0 -> A = set0.
Proof. by move=> A A_0; apply/setP=> x; rewrite inE (card0_eq A_0). Qed.

(* other inclusions *)

Lemma subsetIl : forall A B, A :&: B \subset A.
Proof. by move=> A B; apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetIr : forall A B, A :&: B \subset B.
Proof. by move=> A B; apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetUl : forall A B, A \subset A :|: B.
Proof. by move=> A B; apply/subsetP=> x; rewrite inE => ->. Qed.

Lemma subsetUr : forall A B, B \subset A :|: B.
Proof. by move=> A B; apply/subsetP=> x; rewrite inE orbC => ->. Qed.

Lemma subsetDl : forall A B, A :\: B \subset A.
Proof. by move=> A B; rewrite setDE subsetIl. Qed.

Lemma subsetDr : forall A B, A :\: B \subset ~: B.
Proof. by move=> A B; rewrite setDE subsetIr. Qed.

Lemma sub1set : forall A x, ([set x] \subset A) = (x \in A).
Proof.
by move=> A x; rewrite -subset_pred1; apply: eq_subset=> y; rewrite !inE.
Qed.

Lemma eqsetIl : forall A B, (A :&: B == A) = (A \subset B).
Proof.
move=> A B; apply/eqP/subsetP=> [<- x | sAB]; first by case/setIP.
by apply/setP=> x; rewrite inE; case Ax: (x \in A); rewrite // sAB.
Qed.

Lemma eqsetUl : forall A B, (A :|: B == A) = (B \subset A).
Proof. by move=> A B; rewrite -(inj_eq setC_inj) setCU eqsetIl setCS. Qed.

Lemma eqsetIr : forall A B, (A :&: B == B) = (B \subset A).
Proof. by move=> A B; rewrite setIC eqsetIl. Qed.

Lemma eqsetUr : forall A B, (A :|: B == B) = (A \subset B).
Proof. by move=> A B; rewrite setUC eqsetUl. Qed.

Lemma eqsetDl : forall A B, (A :\: B == A) = [disjoint A & B].
Proof. by move=> A B; rewrite setDE eqsetIl -disjoints_subset. Qed.

Lemma subIset : forall A B C,
  (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof.
by move=> A B C; case/orP; apply: subset_trans; rewrite (subsetIl, subsetIr).
Qed.

Lemma subsetI : forall A B C,
  (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
move=> A B C; rewrite -!eqsetIl setIA; case: (A :&: B =P A) => [-> //| nsAa].
by apply/eqP=> sAab; case: nsAa; rewrite -sAab -setIA -setIIl setIAC.
Qed.

Lemma subUset : forall A B C,
  (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof. by move=> A B C; rewrite -setCS setCU subsetI !setCS. Qed.

Lemma subsetU : forall A B C,
  (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof. move=> A B C; rewrite -!(setCS _ A) setCU; exact: subIset. Qed.

Lemma subsetD : forall A B C,
  (A \subset B :\: C) = (A \subset B) && [disjoint A & C].
Proof. by move=> A B C; rewrite setDE subsetI -disjoints_subset. Qed.

Lemma subDset : forall A B C, (A :\: B \subset C) = (A \subset B :|: C).
Proof.
move=> A B C; apply/subsetP/subsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?inE ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite inE Bx.
Qed.

End setOps.

Section setOpsAlgebra.

Import Monoid.

Variable G : finType.

Canonical Structure setI_monoid := Law (@setIA G) (@setTI G) (@setIT G).

Canonical Structure setI_abeloid := AbelianLaw (@setIC G).
Canonical Structure setI_muloid := MulLaw (@set0I G) (@setI0 G).

Canonical Structure setU_monoid := Law (@setUA G) (@set0U G) (@setU0 G).
Canonical Structure setU_abeloid := AbelianLaw (@setUC G).
Canonical Structure setU_muloid := MulLaw (@setTU G) (@setUT G).

Canonical Structure setI_addoid := AddLaw (@setUIl G) (@setUIr G).
Canonical Structure setU_addoid := AddLaw (@setIUl G) (@setIUr G).

End setOpsAlgebra.

Section CartesianProd.

Variables fT1 fT2 : finType.
Variables (A1 : {set fT1}) (A2 : {set fT2}).

Definition setX := [set u | (u.1 \in A1) && (u.2 \in A2)].

Lemma in_setX : forall x1 x2,
  ((x1, x2) \in setX) = (x1 \in A1) && (x2 \in A2).
Proof. by move=> *; rewrite inE. Qed.

Lemma setXP :  forall x1 x2,
  reflect (x1 \in A1 /\ x2 \in A2) ((x1, x2) \in setX).
Proof. by move=> x1 x2; rewrite inE; exact: andP. Qed.

Lemma cardsX : #|setX| = #|A1| * #|A2|.
Proof. by rewrite cardsE cardX. Qed.

End CartesianProd.

Section ImsetDef.

Variables (aT aT2 rT : finType) (f : aT -> rT) (f2 : aT -> aT2 -> rT).

Variables (D : mem_pred aT) (D2 : mem_pred aT2) (R : mem_pred rT).

Definition preimset := [set x | in_mem (f x) R].
Definition imset_def := [set y \in image f D].
Definition imset2_def := [set y \in image (prod_curry f2) (predX D D2)].

End ImsetDef.

Lemma imset_key : unit. Proof. by []. Qed.
Lemma imset2_key : unit. Proof. by []. Qed.

Definition imset := locked_with imset_key imset_def.
Definition imset2 := locked_with imset2_key imset2_def.

Notation "f @^-1: R" := (preimset f (mem R)) (at level 24) : set_scope.
Notation "f @: D" := (imset f (mem D)) (at level 24) : set_scope.
Notation "f @2: ( D1 , D2 )" := (imset2 f (mem D1) (mem D2))
  (at level 24, format "f  @2:  ( D1 ,  D2 )") : set_scope.

Section FunImage.

Variables aT aT2 rT : finType.

Section ImsetProp.

Variables (f : aT -> rT) (f2 : aT -> aT2 -> rT).

Lemma imsetP : forall D y,
  reflect (exists2 x, in_mem x D & y = f x) (y \in imset f D).
Proof. move=> D y; rewrite /imset unlock inE; exact: imageP. Qed.

CoInductive imset2_spec D1 D2 y : Prop :=
  Imset2spec x1 x2 of in_mem x1 D1 & in_mem x2 D2 & y = f2 x1 x2.

Lemma imset2P : forall D1 D2 y,
  reflect (imset2_spec D1 D2 y) (y \in imset2 f2 D1 D2).
Proof.
move=> D1 D2 y; rewrite /imset2 unlock inE.
apply: (iffP (imageP _ _ _)) => [[[x1 x2] Dx12] | [x1 x2 Dx1 Dx2]] -> {y}.
  by case/andP: Dx12; exists x1 x2.
by exists (x1, x2); rewrite //= Dx1.
Qed.

Lemma imset_f_imp : forall (D : pred aT) x, x \in D -> f x \in f @: D.
Proof. by move=> D x Dx; apply/imsetP; exists x. Qed.

Lemma imset_set1 : forall x, f @: [set x] = [set f x].
Proof.
move=> x; apply/setP => y.
by apply/imsetP/set1P=> [[x']| ->]; [move/set1P-> | exists x; rewrite ?set11].
Qed.

Lemma imset2_f_imp : forall (D : pred aT) (D2 : pred aT2) x x2,
  x \in D -> x2 \in D2 -> f2 x x2 \in f2 @2: (D, D2).
Proof. by move=> D D2 x x2 Dx Dx2; apply/imset2P; exists x x2. Qed.

Lemma preimsetS : forall A B : pred rT,
  A \subset B -> (f @^-1: A) \subset (f @^-1: B).
Proof.
move=> A B sAB; apply/subsetP=> y; rewrite !inE; exact: (subsetP sAB).
Qed.

Lemma preimsetI : forall A B : {set rT},
  f @^-1: (A :&: B) = (f @^-1: A) :&: (f @^-1: B).
Proof. by move=> A B; apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetU : forall A B : {set rT},
  f @^-1: (A :|: B) = (f @^-1: A) :|: (f @^-1: B).
Proof. by move=> A B; apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetD : forall A B : {set rT},
  f @^-1: (A :\: B) = (f @^-1: A) :\: (f @^-1: B).
Proof. by move=> A B; apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetC : forall A : {set rT},
  f @^-1: (~: A) = ~: f @^-1: A.
Proof. by move=> A; apply/setP=> y; rewrite !inE. Qed.

Lemma imsetS : forall A B : pred aT,
  A \subset B -> f @: A \subset f @: B.
Proof.
move=> A B sAB; apply/subsetP=> y; case/imsetP=> x Ax ->.
by apply/imsetP; exists x; rewrite ?(subsetP sAB).
Qed.

Lemma imsetU : forall A B : {set aT},
  f @: (A :|: B) = (f @: A) :|: (f @: B).
Proof.
move=> A B; apply/eqP; rewrite eqset_sub subUset.
rewrite 2?imsetS (andbT, subsetUl, subsetUr) // andbT.
apply/subsetP=> y; case/imsetP=> x ABx ->{y}; apply/setUP.
by case/setUP: ABx => [Ax | Bx]; [left | right]; apply/imsetP; exists x.
Qed.

Lemma imsetU1 : forall a (A : {set aT}), f @: (a |: A) = f a |: (f @: A).
Proof. by move=> a A; rewrite !setU1E imsetU imset_set1. Qed.

Lemma imsetI : forall A B : {set aT},
  {in A & B, injective f} -> f @: (A :&: B) = f @: A :&: f @: B.
Proof.
move=> A B finj; apply/eqP; rewrite eqset_sub subsetI.
rewrite 2?imsetS (andTb, subsetIl, subsetIr) //=.
apply/subsetP=> y; case/setIP; case/imsetP=> x Ax ->{y}.
by case/imsetP=> z Bz; move/finj=> eqxz; rewrite imset_f_imp // inE Ax eqxz.
Qed.

Lemma imset2Sl : forall (A B : pred aT) (C : pred aT2),
  A \subset B -> f2 @2: (A, C) \subset f2 @2: (B, C).
Proof.
move=> A B C sAB; apply/subsetP=> y; case/imset2P=> x x2 Ax Cx2 ->.
by apply/imset2P; exists x x2; rewrite ?(subsetP sAB).
Qed.

Lemma imset2Sr : forall (A B : pred aT2) (C : pred aT),
  A \subset B -> f2 @2: (C, A) \subset f2 @2: (C, B).
Proof.
move=> A B C sAB; apply/subsetP=> y; case/imset2P=> x x2 Cx Ax2 ->.
by apply/imset2P; exists x x2; rewrite ?(subsetP sAB).
Qed.

Lemma imset2S : forall (A B : pred aT) (A2 B2 : pred aT2),
  A \subset B ->  A2 \subset B2 -> f2 @2: (A, A2) \subset f2 @2: (B, B2).
Proof. move=> *; exact: subset_trans (imset2Sl _ _) (imset2Sr _ _). Qed.

End ImsetProp.

Lemma eq_preimset :  forall (f g : aT -> rT) (R : pred rT),
  f =1 g -> f @^-1: R = g @^-1: R.
Proof. by move=> f g R eqfg; apply/setP => y; rewrite !inE eqfg. Qed.

Lemma dfequal_imset :  forall (f g : aT -> rT) (D : {set aT}),
  {in D, f =1 g} -> f @: D = g @: D.
Proof.
move=> f g D eqfg; apply/setP => y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma in_eq_imset2 :
  forall (f g : aT -> aT2 -> rT) (D : pred aT) (D2 : pred aT2),
  {in D & D2, f =2 g} -> f @2: (D, D2) = g @2: (D, D2).
Proof.
move=> f g D D2 eqfg; apply/setP => y.
by apply/imset2P/imset2P=> [] [x x2 Dx Dx2 ->]; exists x x2; rewrite ?eqfg.
Qed.

End FunImage.

Implicit Arguments imsetP [aT rT f D y].
Implicit Arguments imset2P [aT aT2 rT f2 D1 D2 y].
Prenex Implicits imsetP imset2P.

Section Fun2Set1.

Variables aT1 aT2 rT : finType.
Variables (f : aT1 -> aT2 -> rT).

Lemma imset2_set1l : forall x1 (D2 : pred aT2),
  f @2: ([set x1], D2) = f x1 @: D2.
Proof.
move=> x1 D2; apply/setP => y; apply/imset2P/imsetP=> [[x x2]| [x2 Dx2 ->]].
  by move/set1P->; exists x2.
by exists x1 x2; rewrite ?set11.
Qed.

Lemma imset2_set1r : forall x2 (D1 : pred aT1),
  f @2: (D1, [set x2]) = f^~ x2 @: D1.
Proof.
move=> x2 D1; apply/setP => y.
apply/imset2P/imsetP=> [[x1 x Dx1]| [x1 Dx1 ->]].
  by move/set1P->; exists x1.
by exists x1 x2; rewrite ?set11.
Qed.

End Fun2Set1.

Section CardFunImage.

Variables aT aT2 rT : finType.
Variables (f : aT -> rT) (g : rT -> aT) (f2 : aT -> aT2 -> rT).
Variables (D : pred aT) (D2 : pred aT).

Lemma imset_card : #|f @: D| = #|[image f of D]|.
Proof. by rewrite /imset unlock cardsE. Qed.

Lemma leq_imset_card : #|f @: D| <= #|D|.
Proof. by rewrite imset_card leq_image_card. Qed.

Lemma card_dimset : {in D &, injective f} -> #|f @: D| = #|D|.
Proof. by move=> injf; rewrite imset_card card_dimage. Qed.

Lemma card_imset : injective f -> #|f @: D| = #|D|.
Proof. by move=> injf; rewrite imset_card card_image. Qed.

Lemma in_can2_imset_pre :
  {in D, cancel f g} -> {on D, cancel g & f} -> f @: D = g @^-1: D.
Proof.
move=> fK gK; apply/setP=> y; rewrite inE.
by apply/imsetP/idP=> [[x Ax ->] | Agy]; last exists (g y); rewrite ?(fK, gK).
Qed.

Lemma can2_imset_pre : cancel f g -> cancel g f -> f @: D = g @^-1: D.
Proof. move=> *; apply: in_can2_imset_pre; exact: in1W. Qed.

End CardFunImage.

Lemma on_card_preimset : forall (aT rT : finType) (f : aT -> rT) (R : pred rT),
  {on R, bijective f} -> #|f @^-1: R| = #|R|.
Proof.
move=> aT rT f R [g fK gK]; rewrite -(in_can2_imset_pre gK) // card_dimset //.
exact: in_can_inj gK.
Qed.

Lemma can_imset_pre : forall (T : finType) f g (A : {set T}),
  cancel f g -> f @: A = g @^-1: A :> {set T}.
Proof. move=> *; apply: can2_imset_pre => //; exact: canF_sym. Qed.

Lemma card_preimset : forall (T : finType) (f : T -> T) (A : {set T}),
  injective f -> #|f @^-1: A| = #|A|.
Proof.
by move=> *; apply: on_card_preimset; apply: onW_bij; exact: fin_inj_bij.
Qed.

Section FunImageComp.

Variables T T' U : finType.

Lemma imset_comp : forall (f : T' -> U) (g : T -> T') (H : pred T),
  (f \o g) @: H = f @: (g @: H).
Proof.
move=> f g H; apply/setP; apply/subset_eqP; apply/andP.
split; apply/subsetP=> x; move/imsetP=>[x0 Hx0 ->]; apply/imsetP.
  by exists (g x0); first apply:imset_f_imp.
by move/imsetP: Hx0=> [x1 Hx1 ->]; exists x1.
Qed.

End FunImageComp.

Section Disjoint.

Variables T : finType.
Variables T' : eqType.
Variable A : pred T.
Variable S : T -> pred T'.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being disjoint for indexed sets:                    *)
(*    S_i inter S_j <> 0 -> i = j                                     *)
(*                                                                    *)
(**********************************************************************)

Definition disjointn :=
  forall u v x, A u -> A v -> S u x -> S v x -> u = v.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being weak disjoint for indexed sets                *)
(*    S_i inter S_j <> 0 -> S_i = S_j                                 *)
(*                                                                    *)
(**********************************************************************)

Definition wdisjointn :=
  forall u v x, A u -> A v -> S u x -> S v x -> S u =1 S v.

Lemma disjointnW: disjointn -> wdisjointn.
Proof. by move=> H u v x *; rewrite (H u v x). Qed.

End Disjoint.

Section OpSet.

Variables T : finType.
Variables T' : eqType.
Variable A : pred T.
Variable S :  T -> pred T'.
Variable predOp : pred T' -> pred T' -> pred T'.

Definition prednOp :=
  foldr (fun z => predOp (S z)) pred0 (filter A (enum T)).

End OpSet.

Reserved Notation "\bigcup_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
     right associativity,
           format "'[' \bigcup_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  \in  A ) '/  '  F ']'").

Notation "\bigcup_ ( <- r | P ) F" :=
  (\big[@setU _/set0]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@setU _/set0]_(i <- r | P) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@setU _/set0]_(i <- r) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n | P ) F" :=
  (\big[@setU _/set0]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n ) F" :=
  (\big[@setU _/set0]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i | P ) F" :=
  (\big[@setU _/set0]_(i | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i ) F" :=
  (\big[@setU _/set0]_(i) F%SET) : set_scope.
Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@setU _/set0]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcup_ ( i : t ) F" :=
  (\big[@setU _/set0]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcup_ ( i < n | P ) F" :=
  (\big[@setU _/set0]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\big[@setU _/set0]_ (i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i \in A | P ) F" :=
  (\big[@setU _/set0]_(i \in A | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i \in A ) F" :=
  (\big[@setU _/set0]_(i \in A) F%SET) : set_scope.

Section Unions.

Variables I T : finType.
Variable P : pred I.
Variable F :  I -> {set T}.

(**********************************************************************)
(*                                                                    *)
(*  Definition of the union of indexed sets                           *)
(*                                                                    *)
(**********************************************************************)


Lemma bigcup_sup : forall j, P j -> F j \subset \bigcup_(i | P i) F i.
Proof. by move=> j Pj; rewrite (bigD1 j) //= subsetUl. Qed.

Lemma bigcup_inP : forall (A : pred T),
  reflect (forall i, P i -> F i \subset A) (\bigcup_(i | P i) F i \subset A).
Proof.
move=> A; apply: (iffP idP) => [sFA i Pi| sFA].
  by apply: subset_trans sFA; exact: bigcup_sup.
apply big_prop => // [|B C sBA sBC]; first by apply/subsetP=> x; rewrite inE.
apply/subsetP=> x; case/setUP; exact: subsetP x.
Qed.

Lemma bigcupP : forall x,
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
move=> x; apply: (iffP idP) => [|[i Pi]]; last first.
  apply: subsetP x; exact: bigcup_sup.
rewrite /reducebig unlock; elim index_enum => [|i r IHi /=].
  by rewrite inE.
by case Pi: (P i); rewrite //= inE; case/orP; [exists i | exact: IHi].
Qed.

End Unions.

Reserved Notation "\bigcap_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
     right associativity,
           format "'[' \bigcap_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r  |  P )  F ']'").
Reserved Notation "\bigcap_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i \in A ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  \in  A ) '/  '  F ']'").

Notation "\bigcap_ ( <- r | P ) F" :=
  (\big[@setI _/setT]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r | P ) F" :=
  (\big[@setI _/setT]_(i <- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r ) F" :=
  (\big[@setI _/setT]_(i <- r) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n | P ) F" :=
  (\big[@setI _/setT]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n ) F" :=
  (\big[@setI _/setT]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i | P ) F" :=
  (\big[@setI _/setT]_(i | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i ) F" :=
  (\big[@setI _/setT]_(i) F%SET) : set_scope.
Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setT]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i : t ) F" :=
  (\big[@setI _/setT]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcap_ ( i < n | P ) F" :=
  (\big[@setI _/setT]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\big[@setI _/setT]_(i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i \in A | P ) F" :=
  (\big[@setI _/setT]_(i \in A | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i \in A ) F" :=
  (\big[@setI _/setT]_(i \in A) F%SET) : set_scope.

Section Intersections.

Variables I T : finType.
Variable P : pred I.
Variable F :  I -> {set T}.

(**********************************************************************)
(*                                                                    *)
(*  Definition of the intersection of indexed sets                    *)
(*                                                                    *)
(**********************************************************************)

Lemma bigcap_inf : forall j, P j -> \bigcap_(i | P i) F i \subset F j.
Proof. by move=> j Pj; rewrite (bigD1 j) //= subsetIl. Qed.

Lemma bigcap_inP : forall (A : pred T),
  reflect (forall i, P i -> A \subset F i) (A \subset \bigcap_(i | P i) F i).
Proof.
move=> A; apply: (iffP idP) => [sAF i Pi | sAF].
  apply: subset_trans sAF _; exact: bigcap_inf.
apply big_prop => // [|B C sAB sAC]; first by apply/subsetP=> x _; rewrite inE.
apply/subsetP=> x Ax; apply/setIP; split; exact: subsetP x Ax.
Qed.

Lemma bigcapP : forall x,
  reflect (forall i, P i -> x \in F i) (x \in \bigcap_(i | P i) F i).
Proof.
move=> x; rewrite -sub1set.
by apply: (iffP (bigcap_inP _)) => Fx i; move/Fx; rewrite sub1set.
Qed.

End Intersections.

Lemma bigcup_setU: forall (I T : finType) (A B : {set I}) (F : I -> {set T}),
  (\bigcup_(i \in A :|: B) F i) =
     (\bigcup_(i \in A) F i) :|: (\bigcup_ (i \in B) F i).
Proof.
move=> I T A B F; apply/setP=> x; apply/bigcupP/setUP.
  by case=> y; case/setUP; [left | right]; apply/bigcupP; exists y.
by case; case/bigcupP=> i; exists i => //; apply/setUP; [left | right].
Qed.

Lemma bigcap_setU: forall (I T : finType) (A B : {set I}) (F : I -> {set T}),
  (\bigcap_(i \in A :|: B) F i) =
     (\bigcap_(i \in A) F i) :&: (\bigcap_(i \in B) F i).
Proof.
move=> I T A B F; apply/setP=> x; apply/bigcapP/setIP => [sABF | [sFA sFB]].
  by split; apply/bigcapP=> i ABi; apply: sABF; apply/setUP; auto.
move=> i; case/setUP; exact: (bigcapP _ _ x) i.
Qed.

Lemma bigcup_disjoint : forall (I T : finType) (P : pred I)
  (F : I -> {set T}) (A : pred T),
  (forall i, P i -> [disjoint A & F i])
   -> [disjoint A & \bigcup_(i | P i) F i].
Proof.
move=> I T P F A dAF; rewrite disjoint_sym disjoint_subset.
by apply/bigcup_inP=> i; move/dAF; rewrite disjoint_sym disjoint_subset.
Qed.

Lemma wdisjn_disj : forall (I T : finType) (P : pred I) (S : I -> pred T),
           wdisjointn P S ->
           forall i j, P i -> P j -> ~ (S i =1 S j) -> [disjoint S i & S j].
Proof.
move=> d d' a S H i j Hai Haj Hneq;
apply/negP=> H1; case/negP: H1;move/pred0Pn=> [x Hx].
by move/andP:Hx=> [Si Sj]; move: Hneq; move: (H i j x Hai Haj Si Sj).
Qed.

Lemma disjn_card : forall (d d' : finType) (A : pred d) (S : d -> pred d'),
  disjointn A S -> (forall x, #|[pred i | A i && S i x]| <= 1).
Proof.
move=> d d' a S Hdisj x; rewrite leq_eqVlt ltnS leqn0; apply/norP=> [[not1]].
case/pred0Pn => i; case/andP=> ai Six; case/negP: not1.
rewrite (cardD1 i) inE /= ai Six; apply/pred0P=> j /=.
apply/and3P=> [] [nij aj Sjx]; case/eqP: nij; exact: Hdisj Six.
Qed.

Lemma sum_bigcup : forall (d d' : finType) (A : {set d})
                         (S : d -> {set d'}) (N : d' -> nat),
  disjointn (mem A) [rel of S] ->
  \sum_(j \in \bigcup_(i \in A) S i) N j = \sum_(j \in A) \sum_(k \in S j) N k.
Proof.
move => d d' A S N Hdisj.
have e: forall i j, i \in A -> j \in S i -> j \in \bigcup_(i \in A) S i.
  by move=> i j Ha Hs; apply/bigcupP; exists i.
rewrite (exchange_big_dep _ e) //=; apply: eq_bigr => x /= Sx.
rewrite sum_nat_const ((#|_| =P 1) _) ?mul1n // eqn_leq (disjn_card Hdisj) //.
by rewrite lt0n; apply/pred0Pn; case/bigcupP: Sx => i Pi; exists i; rewrite Pi.
Qed.

Lemma card_disjoint : forall (d : finType) (A B : {set d}),
  [disjoint A & B] -> #|A :|: B| = #|A| + #|B|.
Proof. by move=> d A B Hab; rewrite -cardUI (eqnP Hab) addn0 cardsE. Qed.

Lemma card_bigcup : forall (d d': finType) (A : {set d}) (S : d -> {set d'}),
  disjointn (mem A) [rel of S] ->
   #|\bigcup_(i \in A) S i| = \sum_(j \in A) #|S j|.
Proof.
move => d d' a S H.
rewrite -[#|_|]muln1 -sum_nat_const sum_bigcup //.
by apply eq_bigr=> x H1; rewrite (sum_nat_const) muln1.
Qed.

Lemma card_setnU_id : forall (d d': finType) (A : {set d})
                         (S : d -> {set d'}) l,
  disjointn (mem A) [rel of S] ->
    (forall x, x \in A -> #|S x| = l) ->
  #|\bigcup_ (i \in A) S i| = #|A| * l.
Proof.
move => d d' a S l Ds Ch.
rewrite card_bigcup // -sum_nat_const.
apply: eq_bigr => x H1 /=; exact: Ch.
Qed.

Lemma card_dvdn_bigcup : forall (d d' : finType) (A : {set d})
                                        (S : d -> {set d'}) l,
  wdisjointn (mem A) [rel of S] ->
  (forall x, x \in A -> l %| #|S x|) -> l %| #|\bigcup_(i \in A) S i|.
Proof.
move => d d' A S l Ds Ch; rewrite /reducebig unlock /index_enum.
elim (enum d) => //= [|x s IH]; first by rewrite cards0.
case e: (x \in A); last by exact: IH.
pose c (x y : {set d'}) := (x \subset y) || [disjoint x & y].
suff f:  c (S x) (\bigcup_(i <- s | i \in A) S i).
  rewrite /reducebig unlock in f; case/orP: f => [Hsub|Hdisj]; last first.
    rewrite (card_disjoint Hdisj); move/idP: e => e.
    by rewrite (dvdn_addr _ (Ch x e)); exact: IH.
  rewrite -eqsetUl setUC in Hsub; move/eqP: Hsub=>->; exact:IH.
apply big_prop => [|x1 x2|i Ai]; rewrite {}/c.
- by rewrite disjoints_subset setC0 subsetT orbT.
- rewrite !disjoints_subset setCU subsetI [_ || _ && _]orbC.
  by do 2![case/orP=> [subx|->]; first by rewrite subsetU ?subx ?orbT].
case Sxi: [disjoint S x & S i]; rewrite orbC //=.
case/existsP: Sxi => /= x0; case/andP=> Sxx0 Six0.
by apply/subsetP=> y; rewrite [y \in _](Ds x i x0).
Qed.

Section ImsetCurry.

Variables (aT1 aT2 rT : finType) (f : aT1 -> aT2 -> rT).

Section Curry.

Variables (A1 : {set aT1}) (A2 : {set aT2}).
Variables (D1 : pred aT1) (D2 : pred aT2).

Lemma curry_imset2X : f @2: (A1, A2) = prod_curry f @: (setX A1 A2).
Proof.
rewrite /imset /imset2 !unlock; apply/setP=> x; rewrite !in_set.
by apply: eq_image => u //=; rewrite inE.
Qed.

Lemma curry_imset2l : f @2: (D1, D2) = \bigcup_(x1 \in D1) f x1 @: D2.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x1 Dx1]].
  by exists x1; rewrite // imset_f_imp.
by case/imsetP=> x2 Dx2 ->{y}; exists x1 x2.
Qed.

Lemma curry_imset2r : f @2: (D1, D2) = \bigcup_(x2 \in D2) f^~ x2 @: D1.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x2 Dx2]].
  by exists x2; rewrite // (imset_f_imp (f^~ x2)).
by case/imsetP=> x1 Dx1 ->{y}; exists x1 x2.
Qed.

End Curry.

Lemma imset2Ul : forall (A B : {set aT1}) (C : {set aT2}),
  f @2: (A :|: B, C) = f @2: (A, C) :|: f @2: (B, C).
Proof. by move=> A B C; rewrite !curry_imset2l bigcup_setU. Qed.

Lemma imset2Ur : forall (A : {set aT1}) (B C : {set aT2}),
  f @2: (A, B :|: C) = f @2: (A, B) :|: f @2: (A, C).
Proof. by move=> A B C; rewrite !curry_imset2r bigcup_setU. Qed.

End ImsetCurry.

Section Partition.

Variables d : finType.
Variables d' : finType.
Variable a : {set d}.
Variable S :  d -> set d'.
Variable A : {set d'}.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being a cover:                                      *)
(*    union S_i =1 A                                                   *)
(*                                                                    *)
(**********************************************************************)

Definition cover := \bigcup_(i \in a) S i == A.

Lemma coverP :
  reflect ((forall i, i \in a -> S i \subset A) /\
           (forall x, x \in A -> exists2 i, i \in a & x \in S i))
           cover.
Proof.
apply: (iffP eqP) => [<- | [sSA sAS]].
  by split=> [|x]; [exact: bigcup_sup | move/bigcupP].
apply/setP; apply/subset_eqP; move/bigcup_inP: sSA ->.
by apply/subsetP=> x Ax; apply/bigcupP; auto.
Qed.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being a partition:                                  *)
(*    indexed sets that are disjoint and form a cover                 *)
(*                                                                    *)
(**********************************************************************)

Definition partition := disjointn (mem a) [rel of S] /\ cover.

Lemma card_partition : partition -> #|A| = \sum_(i \in a) #|S i|.
Proof. case=> dS; move/(_ =P A) <-; exact: card_bigcup. Qed.

Lemma card_partition_id : forall l,
  partition -> (forall x, x \in a -> #|S x| = l) -> #|A| = #|a| * l.
Proof.
move=> l Hp He; rewrite card_partition // -sum_nat_const; exact: eq_bigr.
Qed.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being a weakpartition:                              *)
(*    indexed sets that are weakly disjoint and form a cover          *)
(*                                                                    *)
(**********************************************************************)

Definition wpartition := wdisjointn (mem a) [rel of S] /\ cover.

Lemma partitionW : partition -> wpartition.
Proof. case; split => //; exact: disjointnW. Qed.

Lemma card_dvdn_partition : forall l,
  wpartition -> (forall x, x \in a -> l %| #|S x|) -> l %| #|A|.
Proof. move=> l [wdS]; move/(_ =P A) <-; exact: card_dvdn_bigcup. Qed.

End Partition.


(**********************************************************************)
(*                                                                    *)
(*  Preimage of elements of the image form a partition                *)
(*                                                                    *)
(**********************************************************************)

Section fun_partition.

Variable T : finType.
Variable T' : finType.
Variable a : {set T}.
Variable f : T -> T'.

Lemma partition_preim :
  partition (f @: a) (fun x => (f @^-1: pred1 x) :&: a) a.
Proof.
split=> [u v x /= H1 H2|].
  by rewrite !inE; do 2![case/andP; move/eqP=> <- _].
apply/eqP; apply/setP=> x.
apply/bigcupP/idP=> [[i _] | ax]; first by case/setIP.
by exists (f x); [apply/imsetP; exists x | rewrite !inE /= eqxx].
Qed.

End fun_partition.
