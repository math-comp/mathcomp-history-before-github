Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import finfun.
Require Import bigops.
Require Import ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SetType.

Variable T : finType.

Record set : Type := mkSet {ffun_of_set : {ffun pred T}}.

Definition set_for of phant T : predArgType := set.
Identity Coercion set_for_set : set_for >-> set.

Notation sT := (set_for (Phant T)).

Canonical Structure set_subType := NewType ffun_of_set set_rect vrefl.
Canonical Structure set_for_subType := Eval hnf in [subType of sT].
Canonical Structure set_eqType := [subEqType for ffun_of_set].
Canonical Structure set_for_eqType := Eval hnf in [eqType of sT].
Canonical Structure set_finType := Eval hnf in [subFinType of set_eqType].
Canonical Structure set_for_finType := Eval hnf in [finType of set_for_eqType].

Definition set_of (P : pred T) : sT := locked mkSet (ffun_of P).

(* This lets us use subtypes of set, like group or coset, as predicates. *)
Coercion pred_of_set (A : set) : pred_class := ffun_of_set A : T -> bool.

(* Declare pred_of_set as a canonical instance of to_pred, but use the *)
(* coercion to resolve mem A to @mem (predPredType T) (pred_of_set A). *)                                 
Canonical Structure set_predType :=
  Eval hnf in @mkPredType T (let s := set in s) pred_of_set.

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

Lemma setE : forall P x, x \in set_of P = P x.
Proof. unlock set_of => P; exact: ffunE. Qed.

Lemma setP : forall a b : sT, a =i b <-> a = b.
Proof. by move=> a b; split=> [eq_ab|->//]; apply: val_inj; apply/ffunP. Qed.

End SetType.

Notation "{ 'set' T }" := (set_for (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

Delimit Scope set_scope with SET.
Bind Scope set_scope with set.
Bind Scope set_scope with set_for.
Open Scope set_scope.
Arguments Scope ffun_of_set [_ set_scope].
Arguments Scope pred_of_set [_ set_scope _].

Notation "[ 'set' x : T | P ]" := (set_of (fun x : T => P))
  (at level 0, x at level 69, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x at level 69, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x \in A | P ]" := [set x | (x \in A) && P]
  (at level 0, x at level 69, format "[ 'set'  x  \in  A  |  P ]") : set_scope.
Notation "[ 'set' x \in A ]" := [set x | x \in A]
  (at level 0, x at level 69, format "[ 'set'  x  \in  A ]") : set_scope.

Section setOpsDefs.

Variable T : finType.

Definition set0 := [set x : T | false].
Definition setA := [set x : T | true].
Definition set1 a1 := [set x : T | x == a1].
Definition set2 a1 a2 := [set x : T | (x == a1) || (x == a2)].
Definition set3 a1 a2 a3 := [set x : T | [|| x == a1, x == a2 | x == a3]].
Definition set4 a1 a2 a3 a4 :=
  [set x : T | [|| x == a1, x == a2, x == a3 | x == a4]].
Definition setC1 a := [set x : T | x != a].
Definition setU (A B : {set T}) := [set x | (x \in A) || (x \in B)].
Definition setU1 a (A : {set T}) := [set x | (x == a) || (x \in A)].
Definition setI (A B : {set T}) := [set x | (x \in A) && (x \in B)].
Definition setC (A : {set T}) := [set x | x \notin A].
Definition setD (A B : {set T}) := [set x | (x \notin B) && (x \in A)].
Definition setD1 (A : {set T}) a := [set x | (x != a) && (x \in A)].

End setOpsDefs.

Implicit Arguments set0 [T].
Implicit Arguments setA [T].
Prenex Implicits set0 setA.

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

Lemma setAP : forall T x, x \in @setA T.
Proof. by move=> T x; rewrite setE. Qed.

Hint Resolve setAP.

Section setOps.

Variable T : finType.

Lemma set1P : forall x a : T, reflect (x = a) (x \in [set a]).
Proof. move=> x y; rewrite setE; exact: eqP. Qed.

Lemma set11 : forall x : T, x \in [set x].
Proof. by move=> x; rewrite setE. Qed.

Lemma setU1P : forall (x a : T) (A : {set T}),
  reflect (x = a \/ x \in A) (x \in a |: A).
Proof. move=> x a A; rewrite setE; exact: predU1P. Qed.

Lemma set_adds : forall (a : T) (s : seq T),
  [set x \in a :: s] = a |: [set x \in s].
Proof. by move=> a s; apply/setP=> x; rewrite !setE. Qed.

Lemma setU1E : forall (a : T) (A : {set T}), a |: A = [set a] :|: A.
Proof. by move=> a A; apply/setP=> y; rewrite !setE. Qed.

Lemma setU11 : forall (x : T) A, x \in x |: A.
Proof. by move=> *; rewrite setE eqxx. Qed.

Lemma setU1r : forall x a (A : {set T}), x \in A -> x \in a |: A.
Proof. by move=> x A a Ax; rewrite setE Ax orbT. Qed.

Lemma setU1s : forall a (A1 A2 : {set T}),
  A1 \subset A2 -> a |: A1 \subset a |: A2.
Proof.
move=> a A1 A2; move/subsetP=> sA12; apply/subsetP=> x; rewrite !setE.
by case: eqd; last exact: sA12.
Qed.

Lemma setC1P : forall x a : T, (x \in [set~ a]) = (x != a).
Proof. by move=> *; rewrite setE. Qed.

Lemma setC1E : forall a : T, [set~ a] = ~: [set a].
Proof. by move=> a; apply/setP=> x; rewrite !setE. Qed.

Lemma setC11 : forall x : T, (x \in [set~ x]) = false.
Proof. by move=> *; rewrite setE eqxx. Qed.

Lemma setD1P : forall (x a : T) (A : {set T}),
  reflect (x != a /\ x \in A) (x \in A :\ a).
Proof. move=> x a A; rewrite setE; exact: andP. Qed.

Lemma setD1E : forall (A : {set T}) (a : T), A :\ a = A :&: [set~ a].
Proof. by move=> A a; apply/setP=> x; rewrite !setE andbC. Qed.

Lemma setD1s : forall a (A1 A2 : {set T}),
  A1 \subset A2 -> A1 :\ a \subset A2 :\ a.
Proof.
move=> a A1 A2; move/subsetP=> sA12; apply/subsetP=> x; rewrite !setE.
by case: eqd; last exact: sA12.
Qed.

Lemma setD11 : forall (x : T) A, (x \in A :\ x) = false.
Proof. by move=> *; rewrite setE eqxx. Qed.

Lemma setD1K : forall (a : T) (A : {set T}),
  a \in A -> a |: (A :\ a) = A.
Proof. by move=> *; apply/setP=> x; rewrite !setE; case: eqP => // ->. Qed.

Lemma setU1K : forall (a : T) (A : {set T}),
  a \notin A -> (a |: A) :\ a = A.
Proof.
move=> a A; move/negPf=> nAa; apply/setP=> x.
by rewrite !setE; case: eqP => // ->.
Qed.

(* enumerations *)

Lemma set2P : forall x a1 a2 : T,
  reflect (x = a1 \/ x = a2) (x \in [set a1; a2]).
Proof.
move=> x a1 a2; rewrite setE.
by do 2![case: eqP => ?; first by left; auto]; right; case.
Qed.

Lemma set3P : forall x a1 a2 a3 : T,
  reflect [\/ x = a1, x = a2 | x = a3] (x \in [set a1; a2; a3]).
Proof.
move=> x a1 a2 a3; rewrite setE; move: Or31 Or32 Or33.
by do 3![case: eqP => ?; first by left; auto]; right; case.
Qed.

Lemma set4P : forall x a1 a2 a3 a4 : T,
  reflect [\/ x = a1, x = a2, x = a3 | x = a4] (x \in [set a1; a2; a3; a4]).
Proof.
move=> x a1 a2 a3 a4; rewrite setE; move: Or41 Or42 Or43 Or44.
by do 4![case: eqP => ?; first by left; auto]; right; case.
Qed.

Lemma set21 : forall a1 a2 : T, a1 \in [set a1; a2].
Proof. by move=> *; rewrite setE eqxx. Qed.

Lemma set22 : forall a1 a2 : T, a2 \in [set a1; a2].
Proof. by move=> *; rewrite setE eqxx orbT. Qed.

Lemma set31 : forall a1 a2 a3 : T, a1 \in [set a1; a2; a3].
Proof. by move=> *; rewrite setE eqxx. Qed.

Lemma set32 : forall a1 a2 a3 : T, a2 \in [set a1; a2; a3].
Proof. by move=> *; rewrite setE eqxx !orbT . Qed.

Lemma set33 : forall a1 a2 a3 : T, a3 \in [set a1; a2; a3].
Proof. by move=> *; rewrite setE eqxx !orbT. Qed.

Lemma setUP : forall x (A1 A2 : {set T}),
  reflect (x \in A1 \/ x \in A2) (x \in A1 :|: A2).
Proof. move => x A1 A2; rewrite !setE; exact: orP. Qed.

Lemma setUC : forall A B : {set T}, A :|: B = B :|: A.
Proof. by move=> A B; apply/setP => x; rewrite !setE orbC. Qed.

Lemma setUs : forall B A1 A2 : {set T},
  A1 \subset A2 -> B :|: A1 \subset B :|: A2.
Proof.
move=> B A1 A2; move/subsetP => sA12; apply/subsetP=> x.
by rewrite !setE; case: (x \in B) => //; exact: sA12.
Qed.

Lemma setsU : forall B A1 A2 : {set T},
  A1 \subset A2 -> A1 :|: B \subset A2 :|: B.
Proof. by move=> B A1 A2 sA12; rewrite -!(setUC B) setUs. Qed.

Lemma set0U : forall A : {set T}, set0 :|: A = A.
Proof. by move=> A; apply/setP => x; rewrite !setE orFb. Qed.

Lemma setU0 : forall A : {set T}, A :|: set0 = A.
Proof. by move=> A; rewrite setUC set0U. Qed.

Lemma setUA : forall A1 A2 A3 : {set T}, A1 :|: (A2 :|: A3) = A1 :|: A2 :|: A3.
Proof. by move=> *; apply/setP => x; rewrite !setE orbA. Qed.

Lemma setUCA : forall A B C : {set T}, A :|: (B :|: C) = B :|: (A :|: C).
Proof. by move=> A B C; rewrite !setUA (setUC B). Qed.

Lemma setUAC : forall A B C : {set T}, A :|: B :|: C = A :|: C :|: B.
Proof. by move=> A B C; rewrite -!setUA (setUC B). Qed.

Lemma setAU : forall A : {set T}, setA :|: A = setA.
Proof. by move=> A; apply/setP => x; rewrite !setE orTb. Qed.

Lemma setUAr : forall A : {set T}, A :|: setA = setA.
Proof. by move=> A; rewrite setUC setAU. Qed.

Lemma setUid : forall A : {set T}, A :|: A = A.
Proof. by move=> A; apply/setP=> x; rewrite setE orbb. Qed.

Lemma setUUl : forall A B C : {set T},
  A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by move=> A B C; rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr : forall A B C : {set T},
  A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by move=> A B C; rewrite !(setUC A) setUUl. Qed.

(* intersect *)

Lemma setIP : forall x (A1 A2 : {set T}),
  reflect (x \in A1 /\ x \in A2) (x \in A1 :&: A2).
Proof. move => x A1 A2; rewrite !setE; exact: andP. Qed.

Lemma setIC : forall A B : {set T}, A :&: B = B :&: A.
Proof. by move=> A B; apply/setP => x; rewrite !setE andbC. Qed.

Lemma setIs : forall B A1 A2 : {set T},
  A1 \subset A2 -> B :&: A1 \subset B :&: A2.
Proof.
move=> B A1 A2; move/subsetP => sA12; apply/subsetP=> x.
by rewrite !setE; case: (x \in B) => //; exact: sA12.
Qed.

Lemma setsI : forall B A1 A2 : {set T},
  A1 \subset A2 -> A1 :&: B \subset A2 :&: B.
Proof. by move=> B A1 A2 sA12; rewrite -!(setIC B) setIs. Qed.

Lemma setAI : forall A : {set T}, setA :&: A = A.
Proof. by move=> A; apply/setP => x; rewrite !setE andTb. Qed.

Lemma setIAr : forall A : {set T}, A :&: setA = A.
Proof. by move=> A; rewrite setIC setAI. Qed.

Lemma set0I : forall A : {set T}, set0 :&: A = set0.
Proof. by move=> A; apply/setP => x; rewrite !setE andFb. Qed.

Lemma setI0 : forall A : {set T}, A :&: set0 = set0.
Proof. by move=> A; rewrite setIC set0I. Qed.

Lemma setIA : forall A1 A2 A3 : {set T}, A1 :&: (A2 :&: A3) = A1 :&: A2 :&: A3.
Proof. by move=> *; apply/setP=> x; rewrite !setE andbA. Qed.

Lemma setICA : forall A B C : {set T}, A :&: (B :&: C) = B :&: (A :&: C).
Proof. by move=> A B C; rewrite !setIA (setIC A). Qed.

Lemma setIAC : forall A B C : {set T}, A :&: B :&: C = A :&: C :&: B.
Proof. by move=> A B C; rewrite -!setIA (setIC B). Qed.

Lemma setIid : forall A : {set T}, A :&: A = A.
Proof. by move=> A; apply/setP=> x; rewrite setE andbb. Qed.

Lemma setIIl : forall A B C : {set T},
  A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by move=> A B C; rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr : forall A B C : {set T},
  A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by move=> A B C; rewrite !(setIC A) setIIl. Qed.

(* distribute /cancel *)

Lemma setIUr : forall A1 A2 A3 : {set T},
  A1 :&: (A2 :|: A3) = (A1 :&: A2) :|: (A1 :&: A3).
Proof. by move=> *; apply/setP => x; rewrite !setE andb_orr. Qed.

Lemma setIUl : forall A1 A2 A3 : {set T},
  (A1 :|: A2) :&: A3 = (A1 :&: A3) :|: (A2 :&: A3).
Proof. by move=> *; apply/setP => x; rewrite !setE andb_orl. Qed.

Lemma setUIr : forall A1 A2 A3 : {set T},
  A1 :|: (A2 :&: A3) = (A1 :|: A2) :&: (A1 :|: A3).
Proof. by move=> *; apply/setP => x; rewrite !setE orb_andr. Qed.

Lemma setUIl : forall A1 A2 A3 : {set T},
  (A1 :&: A2) :|: A3 = (A1 :|: A3) :&: (A2 :|: A3).
Proof. by move=> *; apply/setP => x; rewrite !setE orb_andl. Qed.

Lemma setUK : forall A B : {set T}, (A :|: B) :&: A = A.
Proof. by move=> A B; apply/setP=> x; rewrite !setE orbK. Qed.

Lemma setKU : forall A B : {set T}, A :&: (B :|: A) = A.
Proof. by move=> A B; apply/setP=> x; rewrite !setE orKb. Qed.

Lemma setIK : forall A B : {set T}, (A :&: B) :|: A = A.
Proof. by move=> A B; apply/setP=> x; rewrite !setE andbK. Qed.

Lemma setKI : forall A B : {set T}, A :|: (B :&: A) = A.
Proof. by move=> A B; apply/setP=> x; rewrite !setE andKb. Qed.

(* complement *)

Lemma setCP : forall x (A : {set T}), reflect (~ x \in A) (x \in ~: A).
Proof. move => x A; rewrite !setE; exact: negP. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; apply/setP => x; rewrite !setE negbK. Qed.

Lemma setC_inj: injective (@setC T).
Proof. exact: can_inj setCK. Qed.

Lemma subsets_disjoint : forall A1 A2 : {set T},
  (A1 \subset A2) = [disjoint A1 & ~: A2].
Proof.
by move=> *; rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite setE.
Qed.

Lemma disjoints_subset : forall A1 A2 : {set T},
  [disjoint A1 & A2] = (A1 \subset ~: A2).
Proof. by move=> *; rewrite subsets_disjoint setCK. Qed.

Lemma setCs : forall A1 A2 : {set T}, (~: A1 \subset ~: A2) = (A2 \subset A1).
Proof. by move=> A1 A2; rewrite !subsets_disjoint setCK disjoint_sym. Qed.

Lemma setCU : forall A1 A2 : {set T}, ~: (A1 :|: A2) = ~: A1 :&: ~: A2.
Proof. by move=> *; apply/setP => x; rewrite !setE -negb_or. Qed.

Lemma setCI : forall A1 A2 : {set T}, ~: (A1 :&: A2) = ~:A1 :|: ~:A2.
Proof. by move=> *; apply/setP => x; rewrite !setE negb_and. Qed.

Lemma setUCr : forall A1 : {set T}, A1 :|: (~: A1) = setA.
Proof. by  move=> *; apply/setP => x; rewrite !setE orbN. Qed.

Lemma setICr : forall A1 : {set T}, A1 :&: (~: A1) = set0.
Proof. by  move=> *; apply/setP => x; rewrite !setE andbN. Qed.

Lemma setC0 : ~: set0 = setA :> set T.
Proof. by apply/setP=> x; rewrite !setE. Qed.

Lemma setCA : ~: setA = set0 :> set T.
Proof. by rewrite -setC0 setCK. Qed.

(* difference *)

Lemma setDP : forall (A1 A2 : {set T}) x,
  reflect (x \in A1 /\ x \notin A2) (x \in A1 :\: A2).
Proof. by move=> A1 A2 x; rewrite setE andbC; exact: andP. Qed.

Lemma setDE : forall A1 A2 : {set T}, A1 :\: A2 = A1 :&: ~: A2.
Proof. by move=> A1 A2; apply/setP => x; rewrite !setE andbC. Qed.

Lemma setsD : forall A1 A2 B : {set T},
  A1 \subset A2 -> A1 :\: B \subset A2 :\: B.
Proof. by move=> A1 A2 B; rewrite !setDE; exact: setsI. Qed.

Lemma setDs : forall A1 A2 B : {set T},
  A1 \subset A2 -> B :\: A2 \subset B :\: A1.
Proof. by move=> A1 A2 B; rewrite !setDE -setCs; exact: setIs. Qed.

Lemma setD0 : forall A : {set T}, A :\: set0 = A.
Proof. by move=> A; apply/setP=>x; rewrite !setE. Qed.

Lemma set0D : forall A : {set T}, set0 :\: A = set0.
Proof. by move=> A; apply/setP=>x; rewrite !setE andbF. Qed.
 
Lemma setDAr : forall A : {set T}, A :\: setA = set0.
Proof. by move=> A; apply/setP=>x; rewrite !setE. Qed.

Lemma setAD : forall A : {set T}, setA :\: A = ~: A.
Proof. by move=> A; apply/setP=>x; rewrite !setE andbT. Qed.
 
Lemma setDv : forall A : {set T}, A :\: A = set0.
Proof. by move=> A; apply/setP=> x; rewrite !setE andNb. Qed.

Lemma setCD : forall A1 A2 : {set T}, ~: (A1 :\: A2) = ~: A1 :|: A2.
Proof. by move=> *; rewrite !setDE setCI setCK. Qed.

Lemma setDUl : forall A1 A2 A3 : {set T},
  (A1 :|: A2) :\: A3 = (A1 :\: A3) :|: (A2 :\: A3).
Proof. by move=> *; rewrite !setDE setIUl. Qed.

Lemma setDUr : forall A1 A2 A3 : {set T},
  A1 :\: (A2 :|: A3) = (A1 :\: A2) :&: (A1 :\: A3).
Proof. by move=> *; rewrite !setDE setCU setIIr. Qed.

Lemma setDIl : forall A1 A2 A3 : {set T},
  (A1 :&: A2) :\: A3 = (A1 :\: A3) :&: (A2 :\: A3).
Proof. by move=> *; rewrite !setDE setIIl. Qed.

Lemma setDIr : forall A1 A2 A3 : {set T},
  A1 :\: (A2 :&: A3) = (A1 :\: A2) :|: (A1 :\: A3).
Proof. by move=> *; rewrite !setDE setCI setIUr. Qed.

Lemma setDDl : forall A1 A2 A3 : {set T},
  (A1 :\: A2) :\: A3 = A1 :\: (A2 :|: A3).
Proof. by move=> *; rewrite !setDE setCU setIA. Qed.

Lemma setDDr : forall A1 A2 A3 : {set T},
  A1 :\: (A2 :\: A3) = (A1 :\: A2) :|: (A1 :&: A3).
Proof. by move=> *; rewrite !setDE setCI setIUr setCK. Qed.

(* cardinal lemmas for sets *)

Lemma cardsE : forall s : pred T, #|[set x : T | s x]| = #|s|.
Proof. by move=> s; apply: eq_card => x; rewrite setE. Qed.

Lemma cards1 : forall x : T, #|[set x]| = 1.
Proof. by move=> x; rewrite cardsE card1. Qed.

Lemma cardsUI : forall a b : {set T},
  #|a :|: b| + #|a :&: b| = #|a| + #|b|.
Proof. by move=> a b; rewrite !cardsE cardUI. Qed.

Lemma cards0 : #|@set0 T| = 0.
Proof. by rewrite cardsE card0. Qed.

Lemma cardsA : #|@setA T| = #|T|.
Proof. by rewrite cardsE. Qed.

Lemma cardsID : forall B A : {set T}, #|A :&: B| + #|A :\: B| = #|A|.
Proof. by move=> B A; rewrite !cardsE cardID. Qed.

Lemma cardsC : forall A : {set T}, #|A| + #|~: A| = #|T|.
Proof. by move=> A; rewrite cardsE cardC. Qed.

Lemma cardsU1 : forall (a : T) A, #|a |: A| = (a \notin A) + #|A|.
Proof. by move=> a A; rewrite cardsE cardU1. Qed.

Lemma cards2 : forall a1 a2 : T, #|[set a1; a2]| = (a1 != a2).+1.
Proof. by move=> x y; rewrite cardsE card2. Qed.

Lemma cardsC1 : forall a : T, #|[set~ a]| = #|T|.-1.
Proof. by move=> a; rewrite cardsE cardC1. Qed.

Lemma cardsD1 : forall a (A : {set T}), #|A| = (a \in A) + #|A :\ a|.
Proof. by move=> a A; rewrite cardsE -cardD1. Qed.

Lemma cards0_eq : forall A : {set T}, #|A| = 0 -> A = set0.
Proof. by move=> A A_0; apply/setP=> x; rewrite setE (card0_eq A_0). Qed.

(* other inclusions *)

Lemma subsetIl : forall A B : {set T}, A :&: B \subset A.
Proof. by move=> A B; apply/subsetP=> x; rewrite setE; case/andP. Qed.

Lemma subsetIr : forall A B : {set T}, A :&: B \subset B.
Proof. by move=> A B; apply/subsetP=> x; rewrite setE; case/andP. Qed.

Lemma subsetUl : forall A B : {set T}, A \subset A :|: B.
Proof. by move=> A B; apply/subsetP=> x; rewrite setE => ->. Qed.

Lemma subsetUr : forall A B : {set T}, B \subset A :|: B.
Proof. by move=> A B; apply/subsetP=> x; rewrite setE orbC => ->. Qed.

Lemma subsetDl : forall A B : {set T}, A :\: B \subset A.
Proof. by move=> A B; rewrite setDE subsetIl. Qed.

Lemma subsetDr : forall A B : {set T}, A :\: B \subset ~: B.
Proof. by move=> A B; rewrite setDE subsetIr. Qed.

Lemma subset_set1 : forall (A : {set T}) x, ([set x] \subset A) = (x \in A).
Proof.
by move=> A x; rewrite -subset_pred1; apply: eq_subset=> y; rewrite setE.
Qed.

Lemma eqsetIl : forall A B : {set T}, (A :&: B == A) = (A \subset B).
Proof.
move=> A B; apply/eqP/subsetP=> [<- x | sAB]; first by case/setIP.
by apply/setP=> x; rewrite setE; case Ax: (x \in A); rewrite // sAB.
Qed.

Lemma eqsetUl : forall A B : {set T}, (A :|: B == A) = (B \subset A).
Proof.
move=> A B; apply/eqP/subsetP=> [<- x | sAB]; first by rewrite setE orbC => ->.
by apply/setP=> x; rewrite setE orbC; case Bx: (x \in B); rewrite // sAB.
Qed.

Lemma setI_subset : forall A B C : {set T},
  (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
move=> A B C; rewrite -!eqsetIl setIA; case: (A :&: B =P A) => [-> //| nsAa].
by apply/eqP=> sAab; case: nsAa; rewrite -sAab -setIA -setIIl setIAC.
Qed.

Lemma setU_subset : forall A B C : {set T},
  (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof.
move=> A a b; rewrite -!eqsetUl setUA; case: (A :|: a =P A) => [-> //| nsAa].
by apply/eqP=> sAab; case: nsAa; rewrite -sAab -setUA -setUUl setUAC.
Qed.

Lemma subset_setI : forall A B C : {set T},
  (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof.
move=> A B C.
by case/orP; apply: subset_trans; [exact: subsetIl | exact: subsetIr].
Qed.

Lemma subset_setU : forall A B C : {set T},
  (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof.
move=> A B C.
by case/orP; move/subset_trans; apply; [exact: subsetUl | exact: subsetUr].
Qed.

Lemma eqset_sub : forall A B : {set T},
  (A == B) = (A \subset B) && (B \subset A).
Proof. by move=> A B; apply/eqP/subset_eqP; move/setP. Qed.

Lemma eqset_sub_card : forall A B : {set T},
  (A == B) = (A \subset B) && (#|B| <= #|A|).
Proof.
move=> A B; rewrite eqset_sub; case sAB: (A \subset B) => //=.
by rewrite -(subset_leqif_card sAB) eqn_leq (subset_leqif_card sAB).
Qed.

End setOps.

Section setOpsAlgebra.

Import Monoid.

Variable G : finType.

Canonical Structure setI_monoid := Law (@setIA G) (@setAI G) (@setIAr G).
Canonical Structure setI_abeloid := AbelianLaw (@setIC G).
Canonical Structure setI_muloid := MulLaw (@set0I G) (@setI0 G).

Canonical Structure setU_monoid := Law (@setUA G) (@set0U G) (@setU0 G).
Canonical Structure setU_abeloid := AbelianLaw (@setUC G).
Canonical Structure setU_muloid := MulLaw (@setAU G) (@setUAr G).

Canonical Structure setI_addoid := AddLaw (@setUIl G) (@setUIr G).
Canonical Structure setU_addoid := AddLaw (@setIUl G) (@setIUr G).

End setOpsAlgebra.

Definition imset :=
 locked (fun (T T' : finType) f (A : mem_pred T) => @set_of T' (image f A)).

Definition preimset (T T' : finType) f (A : mem_pred T') :=
  [set x : T | in_mem (f x) A].

Notation "f '@:' A" := (imset f (mem A)) (at level 54) : set_scope.
Notation "f '@^-1:' A" := (preimset f (mem A)) (at level 54) : set_scope.

Section FunIimage.

Variable T T' : finType.

Section ImsetProp.

Variable f : T -> T'.

Lemma imsetP : forall (A : pred T) y,
 reflect (exists2 x, x \in A & y = f x) (y \in f @: A).
Proof. move=> A y; rewrite /imset -lock setE; exact: imageP. Qed.

Lemma imset_f_imp : forall (A : pred T) x, x \in A -> f x \in f @: A.
Proof. by move=> A x Ax; apply/imsetP; exists x. Qed.

Lemma imset_set1 : forall x, f @: [set x] = [set f x].
Proof.
move=> x; apply/setP => y.
by apply/imsetP/set1P=> [[x']| ->]; [move/set1P-> | exists x; rewrite ?set11].
Qed.

Lemma subset_imset : forall (A B: pred T),
  A \subset B -> (f @: A) \subset (f @: B).
Proof.
move=> A B sAB; apply/subsetP=> y; case/imsetP=> x Ax ->.
by apply/imsetP; exists x; rewrite ?(subsetP sAB).
Qed.

End ImsetProp.

Lemma dfequal_imset :  forall (f g : T -> T') (H : {set T}),
  {in H, f =1 g} -> f @: H = g @: H.
Proof.
move=> f g H eqfg; apply/setP => y.
by apply/imsetP/imsetP=> [] [x Hx ->]; exists x; rewrite // eqfg.
Qed.

End FunIimage.

Section CardFunIimage.

Variables (T T' : finType) (f : T -> T') (A : pred T).

Lemma imset_card : #|f @: A| = #|[image f of A]|.
Proof. by unlock imset; rewrite cardsE. Qed.

Lemma leq_imset_card : #|f @: A| <= #|A|.
Proof. by rewrite imset_card leq_image_card. Qed.

Lemma card_dimset : {in A &, injective f} -> #|f @: A| = #|A|.
Proof. by move=> injf; rewrite imset_card card_dimage. Qed.

Lemma card_imset : injective f -> #|f @: A| = #|A|.
Proof. by move=> injf; rewrite imset_card card_image. Qed.

End CardFunIimage.

Section FunIimageComp.

Variables T T' U : finType.

Lemma imset_comp : forall (f: T' -> U) (g: T -> T') (H: pred T),
  ((f\o g) @: H) = (f @: (g @: H)).
Proof.
move=> f g H; apply/setP; apply/subset_eqP; apply/andP.
split; apply/subsetP=> x; move/imsetP=>[x0 Hx0 ->]; apply/imsetP.
  by exists (g x0); first apply:imset_f_imp.
by move/imsetP: Hx0=> [x1 Hx1 ->]; exists x1.
Qed.

End FunIimageComp.

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
apply big_prop_seq => [|B C sBA sCA|i]; last by case/andP; auto.
  by apply/subsetP=> x; rewrite setE.
apply/subsetP=> x; case/setUP; exact: subsetP x.
Qed.

Lemma bigcupP : forall x,
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
move=> x; apply: (iffP idP) => [|[i Pi]]; last first.
  apply: subsetP x; exact: bigcup_sup.
unlock reducebig; elim index_enum => [|i r IHi /=]; first by rewrite setE.
by case Pi: (P i); rewrite //= setE; case/orP; [exists i | exact: IHi].
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
  (\big[@setI _/setA]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r | P ) F" :=
  (\big[@setI _/setA]_(i <- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r ) F" :=
  (\big[@setI _/setA]_(i <- r) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n | P ) F" :=
  (\big[@setI _/setA]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n ) F" :=
  (\big[@setI _/setA]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i | P ) F" :=
  (\big[@setI _/setA]_(i | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i ) F" :=
  (\big[@setI _/setA]_(i) F%SET) : set_scope.
Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setA]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i : t ) F" :=
  (\big[@setI _/setA]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcap_ ( i < n | P ) F" :=
  (\big[@setI _/setA]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\big[@setI _/setA]_(i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i \in A | P ) F" :=
  (\big[@setI _/setA]_(i \in A | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i \in A ) F" :=
  (\big[@setI _/setA]_(i \in A) F%SET) : set_scope.

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
apply big_prop_seq => [|B C sAB sAC|i]; last by case/andP; auto.
  by apply/subsetP=> x _; rewrite setE.
apply/subsetP=> x Ax; apply/setIP; split; exact: subsetP x Ax.
Qed.

Lemma bigcapP : forall x,
  reflect (forall i, P i -> x \in F i) (x \in \bigcap_(i | P i) F i).
Proof.
move=> x; rewrite -subset_set1.
by apply: (iffP (bigcap_inP _)) => Fx i; move/Fx; rewrite subset_set1.
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

Lemma sum_bigcup: forall (d d' : finType) (A : {set d})
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

Lemma card_disjoint: forall (d : finType) (A B : {set d}),
  [disjoint A & B] -> #|A :|: B| = #|A| + #|B|.
Proof. by move=> d A B Hab; rewrite -cardUI (eqnP Hab) addn0 cardsE. Qed.

Lemma card_bigcup: forall (d d': finType) (A : {set d}) (S : d -> {set d'}),
  disjointn (mem A) [rel of S] ->
   #|\bigcup_(i \in A) S i| = \sum_(j \in A) #|S j|.
Proof.
move => d d' a S H.
rewrite -[#|_|]muln1 -sum_nat_const sum_bigcup //.
by apply eq_bigr=> x H1; rewrite (sum_nat_const) muln1.
Qed.

Lemma card_setnU_id: forall (d d': finType) (A : {set d})
                         (S : d -> {set d'}) l,
  disjointn (mem A) [rel of S] ->
    (forall x, x \in A -> #|S x| = l) ->
  #|\bigcup_ (i \in A) S i| = #|A| * l.
Proof.
move => d d' a S l Ds Ch.
rewrite card_bigcup // -sum_nat_const.
apply: eq_bigr => x H1 /=; exact: Ch.
Qed.

Require Import div.

Lemma card_dvdn_bigcup: forall (d d' : finType) (A : {set d})
                                        (S : d -> {set d'}) l,
  wdisjointn (mem A) [rel of S] ->
  (forall x, x \in A -> l %| #|S x|) -> l %| #|\bigcup_(i \in A) S i|.
Proof.
move => d d' A S l Ds Ch; unlock reducebig index_enum.
elim (enum d) => //= [|x s IH]; first by rewrite cards0.
case e: (x \in A); last by exact: IH.
pose c (x y : {set d'}) := (x \subset y) || [disjoint x & y].
suff f:  c (S x) (\bigcup_(i <- s | i \in A) S i).
  unlock reducebig in f; move/orP:f=>[Hsub|Hdisj];
  last by rewrite (card_disjoint Hdisj); move/idP:e=>e; rewrite (dvdn_addr _ (Ch x e)); exact:IH.
  rewrite -eqsetUl setUC in Hsub; move/eqP: Hsub=>->; exact:IH.
apply big_prop_seq => [|x1 x2|i]; rewrite {}/c.
- by rewrite orbC disjoint_sym (eq_disjoint (setE _)) disjoint0.
- rewrite !disjoints_subset setCU setI_subset [_ || _ && _]orbC.
  by do 2![case/orP=> [subx|->]; first by rewrite subset_setU ?subx ?orbT].
case/andP=> Hsi Hai; case f: [disjoint S x & S i]; rewrite orbC //=.
case/existsP: f => /= x0; case/andP=> Sxx0 Six0.
by apply/subsetP=> y; rewrite [y \in _](Ds x i x0).
Qed.

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
  by rewrite !setE; do 2![case/andP; move/eqP=> <- _].
apply/eqP; apply/setP=> x.
apply/bigcupP/idP=> [[i _] | ax]; first by case/setIP.
by exists (f x); [apply/imsetP; exists x | rewrite !setE inE /= eqxx].
Qed.

End fun_partition.
