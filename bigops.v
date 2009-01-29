(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import finfun paths ssralg.
(*Require Import div connect.*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\big [ op / nil ]_ i F"
  (at level 36, F at level 36, op, nil at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / nil ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( <- r | P ) F"
  (at level 36, F at level 36, op, nil at level 10, r at level 50,
           format "'[' \big [ op / nil ]_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i, r at level 50,
           format "'[' \big [ op / nil ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, nil at level 10, i, r at level 50,
           format "'[' \big [ op / nil ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, nil at level 10, m, i, n at level 50,
           format "'[' \big [ op / nil ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / nil ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, nil at level 10, i, m, n at level 50,
           format "'[' \big [ op / nil ]_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "'[' \big [ op / nil ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "'[' \big [ op / nil ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i : t ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "'[' \big [ op / nil ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i, n at level 50,
           format "'[' \big [ op / nil ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i < n ) F"
  (at level 36, F at level 36, op, nil at level 10, i, n at level 50,
           format "'[' \big [ op / nil ]_ ( i  <  n )  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i \in A | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i, A at level 50,
           format "'[' \big [ op / nil ]_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / nil ]_ ( i \in A ) F"
  (at level 36, F at level 36, op, nil at level 10, i, A at level 50,
           format "'[' \big [ op / nil ]_ ( i  \in  A ) '/  '  F ']'").

Reserved Notation "\sum_ i F"
  (at level 41, F at level 41, i at level 0,
           right associativity,
           format "'[' \sum_ i '/  '  F ']'").
Reserved Notation "\sum_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "'[' \sum_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\sum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\sum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  \in  A ) '/  '  F ']'").

Reserved Notation "\max_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \max_ i '/  '  F ']'").
Reserved Notation "\max_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "'[' \max_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \max_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\max_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\max_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n )  F ']'").
Reserved Notation "\max_ ( i \in A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  \in  A  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i \in A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  \in  A ) '/  '  F ']'").

Reserved Notation "\prod_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \prod_ i '/  '  F ']'").
Reserved Notation "\prod_ ( <- r | P ) F"
  (at level 36, F at level 36, r at level 50,
           format "'[' \prod_ ( <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \prod_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50,
           only parsing).
Reserved Notation "\prod_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50,
           only parsing).
Reserved Notation "\prod_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i \in A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  \in  A  |  P )  F ']'").
Reserved Notation "\prod_ ( i \in A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  \in  A ) '/  '  F ']'").

Delimit Scope big_scope with BIG.
Open Scope big_scope.

Definition reducebig R I nil op r (P : pred I) (F : I -> R) : R :=
  foldr (fun i x => if P i then op (F i) x else x) nil r.

Module Type ReduceBigSig.
Parameter bigop : forall R I,
   R -> (R -> R -> R) -> seq I -> pred I -> (I -> R) -> R.
Axiom bigopE : bigop = reducebig.
End ReduceBigSig.

Module ReduceBig : ReduceBigSig.
Definition bigop := reducebig.
Lemma bigopE : bigop = reducebig. Proof. by []. Qed.
End ReduceBig.

Notation bigop := ReduceBig.bigop.
Canonical Structure reduce_big_unlock := Unlockable ReduceBig.bigopE.

Definition index_iota m n := iota m (n - m).

Definition index_enum (T : finType) := Finite.enum T.

Lemma mem_index_iota : forall m n i, i \in index_iota m n = (m <= i < n).
Proof.
move=> m n i; rewrite mem_iota; case le_m_i: (m <= i) => //=.
by rewrite -leq_sub_add leq_subS // -ltn_0sub subn_sub subnK // ltn_0sub.
Qed.

Lemma filter_index_enum : forall T P, filter P (index_enum T) = enum P.
Proof. by []. Qed.

Notation "\big [ op / nil ]_ ( <- r | P ) F" :=
  (bigop nil op r P F) : big_scope.
Notation "\big [ op / nil ]_ ( i <- r | P ) F" :=
  (bigop nil op r (fun i => P%B) (fun i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( i <- r ) F" :=
  (bigop nil op r (fun _ => true) (fun  i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( m <= i < n | P ) F" :=
  (bigop nil op (index_iota m n) (fun i : nat => P%B) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / nil ]_ ( m <= i < n ) F" :=
  (bigop nil op (index_iota m n) (fun _ => true) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / nil ]_ ( i | P ) F" :=
  (bigop nil op (index_enum _) (fun i => P%B) (fun i => F)) : big_scope.
Notation "\big [ op / nil ]_ i F" :=
  (bigop nil op (index_enum _) (fun _ => true) (fun i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( i : t | P ) F" :=
  (bigop nil op (index_enum _) (fun i : t => P%B) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / nil ]_ ( i : t ) F" :=
  (bigop nil op (index_enum _) (fun _ => true) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / nil ]_ ( i < n | P ) F" :=
  (\big[op/nil]_(i : ordinal n | P%B) F) : big_scope.
Notation "\big [ op / nil ]_ ( i < n ) F" :=
  (\big[op/nil]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / nil ]_ ( i \in A | P ) F" :=
  (\big[op/nil]_(i | (i \in A) && P) F) : big_scope.
Notation "\big [ op / nil ]_ ( i \in A ) F" :=
  (\big[op/nil]_(i | i \in A) F) : big_scope.

Notation Local "+%N" := addn (at level 0, only parsing).

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%R/0%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i \in A | P ) F" :=
  (\big[+%R/0%R]_(i \in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i \in A ) F" :=
  (\big[+%R/0%R]_(i \in A) F%R) : ring_scope.

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%N/0%N]_(<- r | P%B) F%N) : nat_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%N/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%N/0%N]_(i <- r) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%N/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\sum_ i F" :=
  (\big[+%N/0%N]_i F%N) : nat_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%N/0%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%N/0%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%N/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%N/0%N]_(i < n) F%N) : nat_scope.
Notation "\sum_ ( i \in A | P ) F" :=
  (\big[+%N/0%N]_(i \in A | P%B) F%N) : nat_scope.
Notation "\sum_ ( i \in A ) F" :=
  (\big[+%N/0%N]_(i \in A) F%N) : nat_scope.

Notation Local "*%N" := muln (at level 0, only parsing).

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%R/1%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[*%R/1%R]_(i \in A | P%B) F%R) : ring_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[*%R/1%R]_(i \in A) F%R) : ring_scope.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%N/1%N]_(<- r | P%B) F%N) : nat_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%N/1%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%N/1%N]_(i <- r) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%N/1%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%N/1%N]_(m <= i < n) F%N) : nat_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%N/1%N]_(i | P%B) F%N) : nat_scope.
Notation "\prod_ i F" :=
  (\big[*%N/1%N]_i F%N) : nat_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%N/1%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%N/1%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%N/1%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%N/1%N]_(i < n) F%N) : nat_scope.
Notation "\prod_ ( i \in A | P ) F" :=
  (\big[*%N/1%N]_(i \in A | P%B) F%N) : nat_scope.
Notation "\prod_ ( i \in A ) F" :=
  (\big[*%N/1%N]_(i \in A) F%N) : nat_scope.

Section Extensionality.

Variables (R : Type)  (nil : R) (op : R -> R -> R).

Section SeqExtension.

Variable I : Type.

Lemma big_filter : forall r (P : pred I) F,
  \big[op/nil]_(i <- filter P r) F i = \big[op/nil]_(i <- r | P i) F i.
Proof. by rewrite unlock => r P F; elim: r => //= i r <-; case (P i). Qed.

Lemma big_filter_cond : forall r (P1 P2 : pred I) F,
  \big[op/nil]_(i <- filter P1 r | P2 i) F i
     = \big[op/nil]_(i <- r | P1 i && P2 i) F i.
Proof.
move=> r P1 P2 F; rewrite -big_filter -(big_filter r); congr bigop.
rewrite -filter_predI; apply: eq_filter => i; exact: andbC.
Qed.

Lemma eq_bigl : forall r (P1 P2 : pred I) F, P1 =1 P2 ->
  \big[op/nil]_(i <- r | P1 i) F i = \big[op/nil]_(i <- r | P2 i) F i.
Proof.
by move=> r P1 P2 F eqP12; rewrite -big_filter (eq_filter eqP12) big_filter.
Qed.

Lemma eq_bigr : forall r (P : pred I) F1 F2, (forall i, P i -> F1 i = F2 i) ->
  \big[op/nil]_(i <- r | P i) F1 i = \big[op/nil]_(i <- r | P i) F2 i.
Proof.
move=> r P F1 F2 eqF12; rewrite unlock.
by elim: r => //= x r ->; case Px: (P x); rewrite // eqF12.
Qed.

Lemma eq_big : forall r (P1 P2 : pred I) F1 F2,
  P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
  \big[op/nil]_(i <- r | P1 i) F1 i = \big[op/nil]_(i <- r | P2 i) F2 i.
Proof. by move=> r P1 P2 F1 F2; move/eq_bigl <-; move/eq_bigr->. Qed.

Lemma congr_big : forall r1 r2 (P1 P2 : pred I) F1 F2,
  r1 = r2 -> P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
    \big[op/nil]_(i <- r1 | P1 i) F1 i = \big[op/nil]_(i <- r2 | P2 i) F2 i.
Proof. move=> r1 r2 P1 P2 F1 F2 <-{r2}; exact: eq_big. Qed.

Lemma big_seq0 : forall (P : pred I) F,
  \big[op/nil]_(i <- [::] | P i) F i = nil.
Proof. by rewrite unlock. Qed.

Lemma big_adds : forall i r (P : pred I) F,
  let x := \big[op/nil]_(j <- r | P j) F j in
  \big[op/nil]_(j <- i :: r | P j) F j = if P i then op (F i) x else x.
Proof. by rewrite unlock. Qed.

Lemma big_maps : forall (J : eqType) (h : J -> I) r F (P : pred I),
  \big[op/nil]_(i <- maps h r | P i) F i
     = \big[op/nil]_(j <- r | P (h j)) F (h j).
Proof. by rewrite unlock => J h r P F; elim: r => //= j r ->. Qed.

Lemma big_sub : forall x0 r (P : pred I) F,
  \big[op/nil]_(i <- r | P i) F i
     = \big[op/nil]_(0 <= i < size r | P (sub x0 r i)) (F (sub x0 r i)).
Proof.
by move=> x0 r P F; rewrite -{1}(mkseq_sub x0 r) big_maps /index_iota subn0.
Qed.

Lemma big_hasC : forall r (P : pred I) F,
  ~~ has P r -> \big[op/nil]_(i <- r | P i) F i = nil.
Proof.
move=> r P F; rewrite -big_filter has_count count_filter.
case: filter => // _; exact: big_seq0.
Qed.

Lemma big_pred0_eq : forall (r : seq I) F,
  \big[op/nil]_(i <- r | false) F i = nil.
Proof. by move=> r F; rewrite big_hasC // has_pred0. Qed.

Lemma big_pred0 : forall r (P : pred I) F, P =1 xpred0 ->
  \big[op/nil]_(i <- r | P i) F i = nil.
Proof. move=> r P F; move/eq_bigl->; exact: big_pred0_eq. Qed.

Lemma big_cat_nested : forall r1 r2 (P : pred I) F,
  let x := \big[op/nil]_(i <- r2 | P i) F i in
  \big[op/nil]_(i <- r1 ++ r2 | P i) F i = \big[op/x]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite unlock /reducebig foldr_cat. Qed.

Lemma big_catl : forall r1 r2 (P : pred I) F, ~~ has P r2 ->
  \big[op/nil]_(i <- r1 ++ r2 | P i) F i = \big[op/nil]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite big_cat_nested; move/big_hasC->. Qed.

Lemma big_catr : forall r1 r2 (P : pred I) F, ~~ has P r1 ->
  \big[op/nil]_(i <- r1 ++ r2 | P i) F i = \big[op/nil]_(i <- r2 | P i) F i.
Proof.
move=> r1 r2 P F; rewrite -big_filter -(big_filter r2) filter_cat.
by rewrite has_count count_filter; case: filter.
Qed.

Lemma big_const_seq : forall r (P : pred I) x,
  \big[op/nil]_(i <- r | P i) x = iter (count P r) (op x) nil.
Proof. by rewrite unlock => r P x; elim: r => //= i r ->; case: (P i). Qed.

End SeqExtension.

(* The following lemma can be used to localise extensionality to     *)
(* the specific index sequence. This is done by ssreflect rewriting, *)
(* before applying congruence or induction lemmas. This is important *)
(* for the latter, because ssreflect 1.1 still relies on primitive   *)
(* Coq matching unification for second-order application (e.g., for  *)
(* elim), and the latter can't handle the eqType constraint on I, as *)
(* it doesn't recognize canonical projections.                       *)
Lemma big_cond_seq : forall (I : eqType) r (P : pred I) F,
  \big[op/nil]_(i <- r | P i) F i
    = \big[op/nil]_(i <- r | P i && (i \in r)) F i.
Proof.
move=> I r P F; rewrite -!(big_filter r); congr bigop.
by apply: eq_in_filter => i ->; rewrite andbT.
Qed.

Lemma congr_big_nat : forall m1 n1 m2 n2 P1 P2 F1 F2,
    m1 = m2 -> n1 = n2 ->
    (forall i, m1 <= i < n2 -> P1 i = P2 i) ->
    (forall i, P1 i && (m1 <= i < n2) -> F1 i = F2 i) ->
  \big[op/nil]_(m1 <= i < n1 | P1 i) F1 i
    = \big[op/nil]_(m2 <= i < n2 | P2 i) F2 i.
Proof.
move=> m n _ _ P1 P2 F1 F2 <- <- eqP12 eqF12.
rewrite big_cond_seq (big_cond_seq _ P2).
apply: eq_big => i; rewrite ?inE /= !mem_index_iota; last exact: eqF12.
case inmn_i: (m <= i < n); rewrite ?(andbT, andbF) //; exact: eqP12.
Qed.

Lemma big_geq : forall m n (P : pred nat) F, m >= n ->
  \big[op/nil]_(m <= i < n | P i) F i = nil.
Proof.
by move=> m n P F ge_m_n; rewrite /index_iota (eqnP ge_m_n) big_seq0.
Qed.

Lemma big_ltn_cond : forall m n (P : pred nat) F, m < n ->
  let x := \big[op/nil]_(m.+1 <= i < n | P i) F i in
  \big[op/nil]_(m <= i < n | P i) F i = if P m then op (F m) x else x.
Proof.
by move=> m [//|n] P F le_m_n; rewrite /index_iota leq_subS // big_adds.
Qed.

Lemma big_ltn : forall m n F, m < n ->
  \big[op/nil]_(m <= i < n) F i = op (F m) (\big[op/nil]_(m.+1 <= i < n) F i).
Proof. move=> *; exact: big_ltn_cond. Qed.

Lemma big_addn : forall m n a (P : pred nat) F,
  \big[op/nil]_(m + a <= i < n | P i) F i =
     \big[op/nil]_(m <= i < n - a | P (i + a)) F (i + a).
Proof.
move=> m n a P F; rewrite /index_iota subn_sub addnC iota_addl big_maps.
by apply: eq_big => ? *; rewrite addnC.
Qed.

Lemma big_add1 : forall m n (P : pred nat) F,
  \big[op/nil]_(m.+1 <= i < n | P i) F i =
     \big[op/nil]_(m <= i < n.-1 | P (i.+1)) F (i.+1).
Proof.
move=> m n P F; rewrite -addn1 big_addn subn1.
by apply: eq_big => ? *; rewrite addn1.
Qed.

Lemma big_nat_recl : forall n F,
  \big[op/nil]_(0 <= i < n.+1) F i =
     op (F 0) (\big[op/nil]_(0 <= i < n) F i.+1).
Proof. by move=> n F; rewrite big_ltn // big_add1. Qed.

Lemma big_mkord : forall n (P : pred nat) F,
  \big[op/nil]_(0 <= i < n | P i) F i = \big[op/nil]_(i < n | P i) F i.
Proof.
move=> n P F; rewrite /index_iota subn0 -(big_maps (@nat_of_ord n)).
by congr bigop; rewrite /index_enum unlock val_ord_enum.
Qed.

Lemma big_nat_widen : forall m n1 n2 (P : pred nat) F, n1 <= n2 ->
  \big[op/nil]_(m <= i < n1 | P i) F i
      = \big[op/nil]_(m <= i < n2 | P i && (i < n1)) F i.
Proof.
move=> m n1 n2 P F len12; symmetry.
rewrite -big_filter filter_predI big_filter.
congr bigop; rewrite /index_iota; set d1 := n1 - m; set d2 := n2 - m.
rewrite -(@subnK d1 d2) /=; last by rewrite leq_sub2r ?leq_addr.
have: ~~ has (fun i => i < n1) (iota (m + d1) (d2 - d1)).
  apply/hasPn=> i; rewrite mem_iota -leqNgt; case/andP=> le_mn1_i _.
  by apply: leq_trans le_mn1_i; rewrite -leq_sub_add.
rewrite iota_add filter_cat has_filter /=; case: filter => // _.
rewrite cats0; apply/all_filterP; apply/allP=> i.
rewrite mem_iota; case/andP=> le_m_i lt_i_md1.
apply: (leq_trans lt_i_md1); rewrite subnK // ltnW //.
rewrite -ltn_0sub -(ltn_add2l m) addn0; exact: leq_trans lt_i_md1.
Qed.

Lemma big_ord_widen_cond : forall n1 n2 (P : pred nat) (F : nat -> R),
     n1 <= n2 ->
  \big[op/nil]_(i < n1 | P i) F i
      = \big[op/nil]_(i < n2 | P i && (i < n1)) F i.
Proof.
move=> n1 n2 P F len12.
by rewrite -big_mkord (big_nat_widen _ _ _ len12) big_mkord.
Qed.

Lemma big_ord_widen : forall n1 n2 (F : nat -> R),
 n1 <= n2 ->
  \big[op/nil]_(i < n1) F i = \big[op/nil]_(i < n2 | i < n1) F i.
Proof. move=> *; exact: (big_ord_widen_cond (predT)). Qed.

Lemma big_ord_widen_leq : forall n1 n2 (P : pred 'I_(n1.+1)) F,
 n1 < n2 ->
  \big[op/nil]_(i < n1.+1 | P i) F i
      = \big[op/nil]_(i < n2 | P (inord i) && (i <= n1)) F (inord i).
Proof.
move=> n1 n2 P F len12; pose g G i := G (inord i : 'I_(n1.+1)).
rewrite -(big_ord_widen_cond (g _ P) (g _ F) len12) {}/g.
by apply: eq_big => i *; rewrite inord_val.
Qed.

Lemma big_ord_narrow_cond : forall n1 n2 (P : pred 'I_n2) F,
  forall le_n1_n2 : n1 <= n2,
  let w := widen_ord le_n1_n2 in
  \big[op/nil]_(i < n2 | P i && (i < n1)) F i
    = \big[op/nil]_(i < n1 | P (w i)) F (w i).
Proof.
move=> [|n1] n2 P F ltn12 /=.
  by rewrite !big_pred0 // => [[//] | i]; rewrite andbF.
rewrite (big_ord_widen_leq _ _ ltn12); apply: eq_big => i.
  rewrite ltnS; case: leqP => [le_i_n1|_]; last by rewrite !andbF.
  by congr (P _ && _); apply: val_inj; rewrite /= inordK.
by case/andP=> _ le_i_n1; congr F; apply: val_inj; rewrite /= inordK.
Qed.

Lemma big_ord_narrow_cond_leq : forall n1 n2 (P : pred 'I_(n2.+1)) F,
  forall le_n1_n2 : n1 <= n2,
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/nil]_(i < n2.+1 | P i && (i <= n1)) F i
  = \big[op/nil]_(i < n1.+1 | P (w i)) F (w i).
Proof. move=> n1 n2; exact: big_ord_narrow_cond n1.+1 n2.+1. Qed.

Lemma big_ord_narrow : forall n1 n2 F,
  forall le_n1_n2 : n1 <= n2,
  let w := widen_ord le_n1_n2 in
  \big[op/nil]_(i < n2 | i < n1) F i = \big[op/nil]_(i < n1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond (predT)). Qed.

Lemma big_ord_narrow_leq : forall n1 n2 F,
  forall le_n1_n2 : n1 <= n2,
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/nil]_(i < n2.+1 | i <= n1) F i = \big[op/nil]_(i < n1.+1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond_leq (predT)). Qed.

Lemma big_ord_recl : forall n F,
  \big[op/nil]_(i < n.+1) F i =
     op (F ord0) (\big[op/nil]_(i < n) F (@lift n.+1 ord0 i)).
Proof.
move=> n F; pose G i := F (inord i).
have eqFG: forall i, F i = G i by move=> i; rewrite /G inord_val.
rewrite (eq_bigr _ (fun i _ => eqFG i)) -(big_mkord _ (fun _ => _) G) eqFG.
rewrite big_ltn // big_add1 /= big_mkord; congr op.
by apply: eq_bigr => i _; rewrite eqFG.
Qed.

Lemma big_const : forall (I : finType) (A : pred I) x,
  \big[op/nil]_(i \in A) x = iter #|A| (op x) nil.
Proof. by move=> I A x; rewrite big_const_seq count_filter cardE. Qed.

Lemma big_const_nat : forall m n x,
  \big[op/nil]_(m <= i < n) x = iter (n - m) (op x) nil.
Proof. by move=> *; rewrite big_const_seq count_predT size_iota. Qed.

Lemma big_const_ord : forall n x,
  \big[op/nil]_(i < n) x = iter n (op x) nil.
Proof. by move=> *; rewrite big_const card_ord. Qed.

End Extensionality.

Section MonoidProperties.

Import Monoid.

Variable R : Type.

Variable nil : R.
Notation Local "1" := nil.

Section Plain.

Variable op : Monoid.law 1.

Notation Local "*%M" := (operator op) (at level 0).
Notation Local "x * y" := ( *%M x y).

Lemma eq_big_nil_seq : forall nil' I r (P : pred I) F,
     right_id nil' *%M -> has P r ->
   \big[*%M/nil']_(i <- r | P i) F i =\big[*%M/1]_(i <- r | P i) F i.
Proof.
move=> nil' I r P F op_nil'.
rewrite -!(big_filter _ _ r) has_count count_filter.
case/lastP: (filter P r) => {r p}// r i _.
by rewrite -cats1 !(big_cat_nested, big_adds, big_seq0) op_nil' mulm1.
Qed.

Lemma eq_big_nil  : forall nil' (I : finType) i0 (P : pred I) F,
     P i0 -> right_id nil' *%M ->
  \big[*%M/nil']_(i | P i) F i =\big[*%M/1]_(i | P i) F i.
Proof.
move=> nil' I i0 P F op_nil' Pi0; apply: eq_big_nil_seq => //.
by apply/hasP; exists i0; first rewrite /index_enum -enumT mem_enum.
Qed.

Lemma big1_eq : forall I r (P : pred I), \big[*%M/1]_(i <- r | P i) 1 = 1.
Proof.
move=> *; rewrite big_const_seq; elim: (count _ _) => //= n ->; exact: mul1m.
Qed.

Lemma big1 : forall (I : finType) (P : pred I) F,
  (forall i, P i -> F i = 1) -> \big[*%M/1]_(i | P i) F i = 1.
Proof. by move=> I P F eq_F_1; rewrite (eq_bigr _ _ _ eq_F_1) big1_eq. Qed.

Lemma big1_seq : forall (I : eqType) r (P : pred I) F,
  (forall i, P i && (i \in r) -> F i = 1)
  -> \big[*%M/1]_(i <- r | P i) F i = 1.
Proof.
by move=> I r P F eqF1; rewrite big_cond_seq (eq_bigr _ _ _ eqF1) big1_eq.
Qed.

Lemma big_seq1 : forall I (i : I) F, \big[*%M/1]_(j <- [:: i]) F j = F i.
Proof. by rewrite unlock => /= *; rewrite mulm1. Qed.

Lemma big_mkcond : forall I r (P : pred I) F,
  \big[*%M/1]_(i <- r | P i) F i =
     \big[*%M/1]_(i <- r) (if P i then F i else 1).
Proof.
by rewrite unlock => I r P F; elim: r => //= i r ->; case P; rewrite ?mul1m.
Qed.

Lemma big_cat : forall I r1 r2 (P : pred I) F,
  \big[*%M/1]_(i <- r1 ++ r2 | P i) F i =
     \big[*%M/1]_(i <- r1 | P i) F i * \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; rewrite !(big_mkcond _ P).
elim: r1 => [|i r1 IHr1]; first by rewrite big_seq0 mul1m.
by rewrite /= !big_adds IHr1 mulmA.
Qed.

Lemma big_pred1_eq : forall (I : finType) (i : I) F,
  \big[*%M/1]_(j | j == i) F j = F i.
Proof.
by move=> I i F; rewrite -big_filter filter_index_enum enum1 big_seq1.
Qed.

Lemma big_pred1 : forall (I : finType) i (P : pred I) F,
  P =1 pred1 i -> \big[*%M/1]_(j | P j) F j = F i.
Proof. move=> I i P F; move/(eq_bigl _ _)->; exact: big_pred1_eq. Qed.

Lemma big_cat_nat : forall n m p (P : pred nat) F, m <= n -> n <= p ->
  \big[*%M/1]_(m <= i < p | P i) F i =
   (\big[*%M/1]_(m <= i < n | P i) F i) * (\big[*%M/1]_(n <= i < p | P i) F i).
Proof.
move=> n m p F P le_mn le_np; rewrite -big_cat.
by rewrite -{2}(subnK le_mn) -iota_add -subn_sub subnK // leq_sub2.
Qed.

Lemma big_nat1 : forall n F, \big[*%M/1]_(n <= i < n.+1) F i = F n.
Proof. by move=> n F; rewrite big_ltn // big_geq // mulm1. Qed.

Lemma big_nat_recr : forall n F,
  \big[*%M/1]_(0 <= i < n.+1) F i = (\big[*%M/1]_(0 <= i < n) F i) * F n.
Proof. by move=> n F; rewrite (@big_cat_nat n) ?leqnSn // big_nat1. Qed.

Lemma big_ord_recr : forall n F,
  \big[*%M/1]_(i < n.+1) F i =
     (\big[*%M/1]_(i < n) F (widen_ord (leqnSn n) i)) * F ord_max.
Proof.
move=> n F; transitivity (\big[*%M/1]_(0 <= i < n.+1) F (inord i)).
  by rewrite big_mkord; apply: eq_bigr=> i _; rewrite inord_val.
rewrite big_nat_recr big_mkord; congr (_ * F _); last first.
  by apply: val_inj; rewrite /= inordK.
by apply: eq_bigr => [] i _; congr F; apply: ord_inj; rewrite inordK //= leqW.
Qed.

End Plain.

Section Abelian.

Variable op : com_law 1.

Notation Local "'*%M'" := (operator (com_operator op)) (at level 0).
Notation Local "x * y" := ( *%M x y).

Lemma eq_big_perm : forall (I : eqType) r1 r2 (P : pred I) F,
    perm_eq r1 r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i = \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; move/perm_eqP; rewrite !(big_mkcond _ _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2; move/(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *; rewrite big_cat /= !big_adds.
rewrite mulmCA; congr (_ * _); rewrite -big_cat; apply: IHr1 => a.
move/(_ a): eq_r12; rewrite !count_cat /= addnCA; exact: addnI.
Qed.

Lemma big_uniq : forall (I : finType) (r : seq I) F,
  uniq r -> \big[*%M/1]_(i <- r) F i = \big[*%M/1]_(i | i \in r) F i.
Proof.
move=> I r F uniq_r; rewrite -(big_filter _ _ _ (mem r)); apply: eq_big_perm.
by rewrite filter_index_enum uniq_perm_eq ?uniq_enum // => i; rewrite mem_enum.
Qed.

Lemma big_split : forall I r (P : pred I) F1 F2,
  \big[*%M/1]_(i <- r | P i) (F1 i * F2 i) =
    \big[*%M/1]_(i <- r | P i) F1 i * \big[*%M/1]_(i <- r | P i) F2 i.
Proof.
rewrite unlock => I r P F1 F2.
elim: r => /= [|i r ->]; [by rewrite mulm1 | case: (P i) => //=].
rewrite !mulmA; congr (_ * _); exact: mulmAC.
Qed.

Lemma bigID : forall I r (a P : pred I) F,
  \big[*%M/1]_(i <- r | P i) F i
  = \big[*%M/1]_(i <- r | P i && a i) F i *
    \big[*%M/1]_(i <- r | P i && ~~ a i) F i.
Proof.
move=> I r a P F; rewrite !(big_mkcond _ _ _ F) -big_split; apply: eq_bigr => i.
by case: (a i); rewrite !simpm.
Qed.
Implicit Arguments bigID [I r].

Lemma bigD1 : forall (I : finType) j (P : pred I) F,
  P j -> \big[*%M/1]_(i | P i) F i
    = F j * \big[*%M/1]_(i | P i && (i != j)) F i.
Proof.
move=> I j P F Pj; rewrite (bigID (pred1 j)); congr (_ * _).
by apply: big_pred1 => i; rewrite /= andbC; case: eqP => // ->.
Qed.
Implicit Arguments bigD1 [I P F].

Lemma cardD1x : forall (I : finType) (A : pred I) j,
  A j -> #|SimplPred A| = 1 + #|[pred i | A i && (i != j)]|.
Proof.
move=> I A j Aj; rewrite (cardD1 j) [j \in A]Aj; congr (_ + _).
by apply: eq_card => i; rewrite inE /= andbC.
Qed.
Implicit Arguments cardD1x [I A].

Lemma partition_big : forall (I J : finType) (P : pred I) p (Q : pred J) F,
    (forall i, P i -> Q (p i)) ->
      \big[*%M/1]_(i | P i) F i =
         \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i && (p i == j)) F i.
Proof.
move=> I J P p Q F Qp; transitivity (\big[*%M/1]_(i | P i && Q (p i)) F i).
  by apply: eq_bigl => i; case Pi: (P i); rewrite // Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite ltnS (cardD1x j Qj) (bigD1 j) //; move/IHn=> {n IHn} <-.
rewrite (bigID (fun i => p i == j)); congr (_ * _); apply: eq_bigl => i.
  by case: eqP => [-> | _]; rewrite !(Qj, simpm).
by rewrite andbA.
Qed.

Implicit Arguments partition_big [I J P F].

Lemma reindex_onto : forall (I J : finType) (h : J -> I) h' (P : pred I) F,
   (forall i, P i -> h (h' i) = i) ->
  \big[*%M/1]_(i | P i) F i =
    \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
move=> I J h h' P F h'K.
elim: {P}_.+1 {-3}P h'K (ltnSn #|P|) => //= n IHn P h'K.
case: (pickP P) => [i Pi | P0 _]; last first.
  by rewrite !big_pred0 // => j; rewrite P0.
rewrite ltnS (cardD1x i Pi); move/IHn {n IHn} => IH.
rewrite (bigD1 i Pi) (bigD1 (h' i)) h'K ?Pi ?eq_refl //=; congr (_ * _).
rewrite {}IH => [|j]; [apply: eq_bigl => j | by case/andP; auto].
rewrite andbC -andbA (andbCA (P _)); case: eqP => //= hK; congr (_ && ~~ _).
by apply/eqP/eqP=> [<-|->] //; rewrite h'K.
Qed.
Implicit Arguments reindex_onto [I J P F].

Lemma reindex : forall (I J : finType) (h : J -> I) (P : pred I) F,
  {on [pred i | P i], bijective h} ->
  \big[*%M/1]_(i | P i) F i = \big[*%M/1]_(j | P (h j)) F (h j).
Proof.
move=> I J h P F [h' hK h'K]; rewrite (reindex_onto h h' h'K).
by apply: eq_bigl => j; rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.
Implicit Arguments reindex [I J P F].

Lemma pair_big_dep : forall (I J : finType) (P : pred I) (Q : I -> pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Proof.
move=> I J P Q F.
rewrite (partition_big (fun p => p.1) P) => [|j]; last by case/andP.
apply: eq_bigr => i /= Pi; rewrite (reindex_onto (pair i) (fun p => p.2)).
   by apply: eq_bigl => j; rewrite !eqxx [P i]Pi !andbT.
by case=> i' j /=; case/andP=> _ /=; move/eqP->.
Qed.

Lemma pair_big : forall (I J : finType) (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.2) F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma pair_bigA_ : forall (I J : finType) (F : I -> J -> R),
  \big[*%M/1]_i \big[*%M/1]_j F i j = \big[*%M/1]_p F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma exchange_big_dep :
    forall (I J : finType) (P : pred I) (Q : I -> pred J) (xQ : pred J) F,
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(j | xQ j) \big[*%M/1]_(i | P i && Q i j) F i j.
Proof.
move=> I J P Q xQ F PQxQ; pose p u := (u.2, u.1).
rewrite !pair_big_dep (reindex_onto (p J I) (p I J)) => [|[//]].
apply: eq_big => [] [j i] //=; symmetry; rewrite eq_refl andbC.
case: (@andP (P i)) => //= [[]]; exact: PQxQ.
Qed.
Implicit Arguments exchange_big_dep [I J P Q F].

Lemma exchange_big :  forall (I J : finType) (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j =
    \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i) F i j.
Proof.
move=> I J P Q F; rewrite (exchange_big_dep Q) //; apply: eq_bigr => i /= Qi.
by apply: eq_bigl => j; rewrite [Q i]Qi andbT.
Qed.

Lemma exchange_big_dep_nat :
  forall m1 n1 m2 n2 (P : pred nat) (Q : rel nat) (xQ : pred nat) F,
    (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q i j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | xQ j)
       \big[*%M/1]_(m1 <= i < n1 | P i && Q i j) F i j.
Proof.
move=> m1 n1 m2 n2 P Q xQ F PQxQ.
transitivity
  (\big[*%M/1]_(i < n1 - m1| P (i + m1))
    \big[*%M/1]_(j < n2 - m2 | Q (i + m1) (j + m2)) F (i + m1) (j + m2)).
- rewrite -{1}[m1]add0n big_addn big_mkord; apply: eq_bigr => i _.
  by rewrite -{1}[m2]add0n big_addn big_mkord.
rewrite (exchange_big_dep (fun j: 'I__ => xQ (j + m2))) => [|i j]; last first.
  by apply: PQxQ; rewrite leq_addl addnC -ltn_0sub -subn_sub ltn_0sub ltn_ord.
symmetry; rewrite -{1}[m2]add0n big_addn big_mkord; apply: eq_bigr => j _.
by rewrite -{1}[m1]add0n big_addn big_mkord.
Qed.
Implicit Arguments exchange_big_dep_nat [m1 n1 m2 n2 P Q F].

Lemma exchange_big_nat : forall m1 n1 m2 n2 (P Q : pred nat) F,
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | Q j) \big[*%M/1]_(m1 <= i < n1 | P i) F i j.
Proof.
move=> m1 n1 m2 n2 P Q F; rewrite (exchange_big_dep_nat Q) //.
by apply: eq_bigr => i /= Qi; apply: eq_bigl => j; rewrite [Q i]Qi andbT.
Qed.

End Abelian.

End MonoidProperties.

Implicit Arguments big_filter [R op nil I].
Implicit Arguments big_filter_cond [R op nil I].
Implicit Arguments congr_big [R op nil I r1 P1 F1].
Implicit Arguments eq_big [R op nil I r P1  F1].
Implicit Arguments eq_bigl [R op nil  I r P1].
Implicit Arguments eq_bigr [R op nil I r  P F1].
Implicit Arguments eq_big_nil [R op nil nil' I P F].
Implicit Arguments big_cond_seq [R op nil I r].
Implicit Arguments congr_big_nat [R op nil m1 n1 P1 F1].
Implicit Arguments big_maps [R op nil I J r].
Implicit Arguments big_sub [R op nil I r].
Implicit Arguments big_catl [R op nil I r1 r2 P F].
Implicit Arguments big_catr [R op nil I r1 r2  P F].
Implicit Arguments big_geq [R op nil m n P F].
Implicit Arguments big_ltn_cond [R op nil m n P F].
Implicit Arguments big_ltn [R op nil m n F].
Implicit Arguments big_addn [R op nil]. (* m n a *)
Implicit Arguments big_mkord [R op nil n].
Implicit Arguments big_nat_widen [R op nil] (* m n a *).
Implicit Arguments big_ord_widen_cond [R op nil n1].
Implicit Arguments big_ord_widen [R op nil n1].
Implicit Arguments big_ord_widen_leq [R op nil n1].
Implicit Arguments big_ord_narrow_cond [R op nil n1 n2 P F].
Implicit Arguments big_ord_narrow_cond_leq [R op nil n1 n2 P F].
Implicit Arguments big_ord_narrow [R op nil n1 n2 F].
Implicit Arguments big_ord_narrow_leq [R op nil n1 n2 F].
Implicit Arguments big_mkcond [R op nil I r].
Implicit Arguments big1_eq [R op nil I].
Implicit Arguments big1_seq [R op nil I].
Implicit Arguments big1 [R op nil I].
Implicit Arguments big_pred1 [R op nil I P F].
Implicit Arguments eq_big_perm [R op nil I r1 P F].
Implicit Arguments big_uniq [R op nil I F].
Implicit Arguments bigID [R op nil I r].
Implicit Arguments bigD1 [R op nil I P F].
Implicit Arguments partition_big [R op nil I J P F].
Implicit Arguments reindex_onto [R op nil I J P F].
Implicit Arguments reindex [R op nil I J P F].
Implicit Arguments pair_big_dep [R op nil I J].
Implicit Arguments pair_big [R op nil I J].
Implicit Arguments exchange_big_dep [R op nil I J P Q F].
Implicit Arguments exchange_big_dep_nat [R op nil m1 n1 m2 n2 P Q F].
Implicit Arguments big_ord_recl [R op nil].
Implicit Arguments big_ord_recr [R op nil].
Implicit Arguments big_nat_recl [R op nil].
Implicit Arguments big_nat_recr [R op nil].

Section BigProp.

Variables (R : Type) (Pb : R -> Type).
Variables (nil : R) (op1 op2 : R -> R -> R).
Hypothesis (Pb_nil : Pb nil)
           (Pb_op1 : forall x y, Pb x -> Pb y -> Pb (op1 x y))
           (Pb_eq_op : forall x y, Pb x -> Pb y -> op1 x y = op2 x y).

Lemma big_prop : forall I r (P : pred I) F,
  (forall i, P i -> Pb (F i)) -> Pb (\big[op1/nil]_(i <- r | P i) F i).
Proof.
by rewrite unlock => I r P F PbF; elim: r => //= i *; case Pi: (P i); auto.
Qed.

(* Pb must be given explicitly for the lemma below, because Coq second-order *)
(* unification will not handle the eqType constraint on I.                   *)
Lemma big_prop_seq : forall (I : eqType) (r : seq I) (P : pred I) F,
  (forall i, P i && (i \in r) -> Pb (F i)) ->
   Pb (\big[op1/nil]_(i <- r | P i) F i).
Proof. move=> I r P F; rewrite big_cond_seq; exact: big_prop. Qed.

(* Change operation *)
Lemma eq_big_op :  forall I r (P : pred I) F,
   (forall i, P i -> Pb (F i)) ->
  \big[op1/nil]_(i <- r | P i) F i = \big[op2/nil]_(i <- r | P i) F i.
Proof.
have:= big_prop; rewrite unlock => Pb_big I r P F Pb_F.
by elim: r => //= i r <-; case Pi: (P i); auto.
Qed.

(* See big_prop_seq above *)
Lemma eq_big_op_seq :  forall (I : eqType) r (P : pred I) F,
    (forall i, P i && (i \in r) -> Pb (F i)) ->
  \big[op1/nil]_(i <- r | P i) F i = \big[op2/nil]_(i <- r | P i) F i.
Proof. move=> I r P F Pb_F; rewrite !(big_cond_seq P); exact: eq_big_op. Qed.

End BigProp.

(* The implicit arguments expect an explicit Pb *)
Implicit Arguments eq_big_op_seq [R nil op1 I r P F].
Implicit Arguments eq_big_op [R nil op1 I P F].

Section BigRel.

Variables (R1 R2 : Type) (Pr : R1 -> R2 -> Type).
Variables (nil1 : R1) (op1 : R1 -> R1 -> R1).
Variables (nil2 : R2) (op2 : R2 -> R2 -> R2).
Hypothesis Pr_nil : Pr nil1 nil2.
Hypothesis Pr_rel : forall x1 x2 y1 y2,
  Pr x1 x2 -> Pr y1 y2 -> Pr (op1 x1 y1) (op2 x2 y2).

(* Pr must be given explicitly *)
Lemma big_rel : forall I r (P : pred I) F1 F2,
  (forall i, (P i) -> Pr (F1 i) (F2 i)) ->
  Pr (\big[op1/nil1]_(i <- r | P i) F1 i) (\big[op2/nil2]_(i <- r | P i) F2 i).
Proof.
rewrite !unlock => I r P F1 F2 PrF.
elim: r => //= i *; case Pi: (P i); auto.
Qed.

Lemma big_rel_seq : forall (I : eqType) (r : seq I) (P : pred I) F1 F2,
    (forall i, P i && (i \in r) -> Pr (F1 i) (F2 i)) ->
  Pr (\big[op1/nil1]_(i <- r | P i) F1 i) (\big[op2/nil2]_(i <- r | P i) F2 i).
Proof. move=> I r P *; rewrite !(big_cond_seq P); exact: big_rel. Qed.

End BigRel.

Implicit Arguments big_rel_seq [R1 R2 nil1 op1 nil2 op2 I r P F1 F2].
Implicit Arguments big_rel [R1 R2 nil1 op1 nil2 op2 I P F1 F2].

Section Morphism.

Variables R1 R2 : Type.
Variables (nil1 : R1) (nil2 : R2).
Variables (op1 : R1 -> R1 -> R1) (op2 : R2 -> R2 -> R2).
Variable phi : R1 -> R2.
Hypothesis phi_morphism : Monoid.morphism nil1 nil2 op1 op2 phi.

Lemma big_morph : forall I r (P : pred I) F,
  phi (\big[op1/nil1]_(i <- r | P i) F i) =
     \big[op2/nil2]_(i <- r | P i) phi (F i).
Proof.
case: phi_morphism => [phi1 phiM] I r P F.
by rewrite !unlock; elim: r => //= i r <-; case: (P i).
Qed.

End Morphism.

Implicit Arguments big_morph [R1 R2 nil1 nil2 op1 op2].

Section Distributivity.

Import Monoid.

Variable R : Type.
Variables zero one : R.
Notation Local "0" := zero.
Notation Local "1" := one.
Variable times : mul_law 0.
Notation Local "*%M" := (mul_operator times) (at level 0).
Notation Local "x * y" := ( *%M x y).
Variable plus : add_law 0 *%M.
Notation Local "+%M" :=
  (operator (com_operator (add_operator plus))) (at level 0).
Notation Local "x + y" := ( +%M x y).

Lemma big_distrl : forall I r alpha (P : pred I) F,
  \big[+%M/0]_(i <- r | P i) F i * alpha
    = \big[+%M/0]_(i <- r | P i) (F i * alpha).
Proof.
move=> *; apply: (big_morph ( *%M^~ _)).
by split=> [|? * /=]; rewrite (mul0m,  mulm_addl).
Qed.

Lemma big_distrr : forall I r alpha (P : pred I) F,
  alpha * \big[+%M/0]_(i <- r | P i) F i
    = \big[+%M/0]_(i <- r | P i) (alpha * F i).
Proof.
move=> *; apply: (big_morph ( *%M _)).
by split=> [|? * /=]; rewrite (mulm0,  mulm_addr).
Qed.

Lemma big_distr_big_dep :
  forall (I J : finType) j0 (P : pred I) (Q : I -> pred J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q i j) F i j =
     \big[+%M/0]_(f | pfamily j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite -big_filter filter_index_enum; set r := enum P.
pose fIJ := {ffun I -> J}; pose Pf := pfamily j0 _ Q; symmetry.
transitivity (\big[+%M/0]_(f | Pf (mem r) f) \big[*%M/1]_(i <- r) F i (f i)).
  apply: eq_big=> f; last by rewrite -big_filter filter_index_enum.
  by apply: eq_forallb => i; rewrite /= mem_enum.
have: uniq r by exact: uniq_enum.
elim: {P}r => /= [_|i r IHr].
  rewrite (big_pred1 [ffun => j0]) ?big_seq0 //= => f.
  apply/familyP/eqP=> /= [Df |->{f} i]; last by rewrite ffunE.
  apply/ffunP=> i; rewrite ffunE; exact/eqP.
case/andP=> nri; rewrite big_adds big_distrl; move/IHr {IHr} <-.
rewrite (partition_big (fun f : fIJ => f i) (Q i)); last first.
  by move=> f; move/familyP; move/(_ i); rewrite /= inE /= eqxx.
pose seti j (f : fIJ) := [ffun k => if k == i then j else f k].
apply: eq_bigr => j Qij; rewrite (reindex_onto (seti j) (seti j0)); last first.
  move=> f /=; case/andP; move/familyP=> eq_f; move/eqP=> fi.
  by apply/ffunP => k; rewrite !ffunE; case: eqP => // ->.
rewrite big_distrr; apply: eq_big => [f | f eq_f]; last first.
  rewrite big_adds ffunE eq_refl !(big_cond_seq predT) /=; congr (_ * _).
  by apply: eq_bigr => k; rewrite ffunE; case: eqP => // ->; case/idPn.
rewrite !ffunE !eq_refl andbT; apply/andP/familyP=> [[Pjf fij0] k | Pff].
  have:= familyP _ _ Pjf k; rewrite /= ffunE in_adds; case: eqP => // -> _.
  by rewrite (negbTE nri) -(eqP fij0) !ffunE ?inE /= !eqxx.
split.
  apply/familyP=> k; move/(_ k): Pff; rewrite /= ffunE in_adds.
  by case: eqP => // ->.
apply/eqP; apply/ffunP=> k; have:= Pff k; rewrite !ffunE /=.
by case: eqP => // ->; rewrite (negbTE nri) /=; move/eqP.
Qed.

Lemma big_distr_big :
  forall (I J : finType) j0 (P : pred I) (Q : pred J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q j) F i j =
     \big[+%M/0]_(f | pffun_on j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite (big_distr_big_dep j0); apply: eq_bigl => f.
by apply/familyP/familyP=> Pf i; move/(_ i): Pf; case: (P i).
Qed.

Lemma bigA_distr_big_dep :
  forall (I J : finType) (Q : I -> pred J) F,
  \big[*%M/1]_i \big[+%M/0]_(j | Q i j) F i j
    = \big[+%M/0]_(f | family Q f) \big[*%M/1]_i F i (f i).
Proof.
move=> I J Q F; case: (pickP J) => [j0 _ | J0].
   exact: (big_distr_big_dep j0).
rewrite /index_enum -enumT; case: (enum I) (mem_enum I) => [I0 | i r _].
  have f0: I -> J by move=> i; have:= I0 i.
  rewrite (big_pred1 (finfun f0)) ?big_seq0 // => g.
  by apply/familyP/eqP=> _; first apply/ffunP; move=> i; have:= I0 i.
have Q0: Q _ =1 pred0 by move=> ? j; have:= J0 j.
rewrite big_adds /= big_pred0 // mul0m big_pred0 // => f.
by apply/familyP; move/(_ i); rewrite Q0.
Qed.

Lemma bigA_distr_big :
  forall (I J : finType) (Q : pred J) (F : I -> J -> R),
  \big[*%M/1]_i \big[+%M/0]_(j | Q j) F i j
    = \big[+%M/0]_(f | ffun_on Q f) \big[*%M/1]_i F i (f i).
Proof. move=> *; exact: bigA_distr_big_dep. Qed.

Lemma bigA_distr_bigA :
  forall (I J : finType) F,
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
Proof.
move=> *; rewrite bigA_distr_big; apply: eq_bigl => ?; exact/familyP.
Qed.

End Distributivity.

Implicit Arguments big_distrl [R zero times plus I r].
Implicit Arguments big_distrr [R zero times plus I r].
Implicit Arguments big_distr_big_dep [R zero one times plus I J].
Implicit Arguments big_distr_big [R zero one times plus I J].
Implicit Arguments bigA_distr_big_dep [R zero one times plus I J].
Implicit Arguments bigA_distr_big [R zero one times plus I J].
Implicit Arguments bigA_distr_bigA [R zero one times plus I J].

Section Ring.

Import GRing.Theory.
Open Scope ring_scope.

Section Opp.

Variable R : zmodType.

Lemma sum_opp : forall I r P (F : I -> R),
  \sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i).
Proof.
move=> *; symmetry; apply: big_morph.
by split=> [|x y]; rewrite (oppr0, oppr_add).
Qed.

Lemma sum_split_sub : forall I r (P : pred I) (F1 F2 : I -> R),
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. by move=> *; rewrite -sum_opp -big_split /=. Qed.

Lemma sumr_const : forall (I : finType) (A : pred I) (x : R),
  \sum_(i \in A) x = x *+ #|A|.
Proof. exact: big_const. Qed.

End Opp.

Lemma prodr_const : forall (R : ringType) (I : finType) (A : pred I) (x : R),
  \prod_(i \in A) x = x ^+ #|A|.
Proof. move=> *; exact: big_const. Qed.

End Ring.

(* Redundant, unparseable notation to print constant sums and products. *)
Notation "\su 'm_' ( i | P ) e" :=
  (\sum_(<- index_enum _ | (fun i => P)) (fun _ => e%N))
  (at level 41, e at level 41, format "\su 'm_' ( i  |  P )  e") : nat_scope.

Notation "\su 'm_' ( i \in A ) e" :=
  (\sum_(<- index_enum _ | (fun i => i \in A)) (fun _ => e%N))
  (at level 41, e at level 41, format "\su 'm_' ( i  \in  A )  e") : nat_scope.

Notation "\su 'm_' ( i \in A | P ) e" :=
  (\sum_(<- index_enum _ | (fun i => (i \in A) && P)) (fun _ => e%N))
  (at level 41, e at level 41, format "\su 'm_' ( i  \in  A  |  P )  e")
    : nat_scope.

Notation "\pro 'd_' ( i | P ) e" :=
  (\prod_(<- index_enum _ | (fun i => P)) (fun _ => e%N))
  (at level 36, e at level 36, format "\pro 'd_' ( i  |  P )  e") : nat_scope.

Lemma sum_nat_const : forall (I : finType) (A : pred I) (n : nat),
  \sum_(i \in A) n = #|A| * n.
Proof. by move=> I A n; rewrite big_const; elim: #|A| => //= i ->. Qed.

Lemma sum1_card : forall (I : finType) (A : pred I), \sum_(i \in A) 1 = #|A|.
Proof. by move=> I A; rewrite sum_nat_const muln1. Qed.

Lemma prod_nat_const : forall (I : finType) (A : pred I) (n : nat),
  \prod_(i \in A) n = n ^ #|A|.
Proof. by move=> I A n; rewrite big_const; elim: #|_| => //= ? ->. Qed.

Lemma sum_nat_const_nat : forall n1 n2 n : nat,
  \sum_(n1 <= i < n2) n = (n2 - n1) * n.
Proof. by move=> *; rewrite big_const_nat; elim: (_ - _) => //= ? ->. Qed.

Lemma prod_nat_const_nat : forall n1 n2 n : nat,
  \prod_(n1 <= i < n2) n = n ^ (n2 - n1).
Proof. by move=> *; rewrite big_const_nat; elim: (_ - _) => //= ? ->. Qed.

(* Beware: applying sum_predU to a [disjoint A & B] hypothesis will strip *)
(* the mem wrappers from A and B, possibly exposing internal coercions.   *)
Lemma sum_predU : forall (I : finType) (N : I -> nat) (a b : pred I),
  [disjoint a & b] ->
  \sum_(i | a i || b i) N i = (\sum_(i | a i) N i) + (\sum_(i | b i) N i).
Proof.
move => d N a b Hdisj; rewrite (bigID a) //=; congr addn; apply: eq_bigl => x0.
  by rewrite andb_orl andbb andbC [_ && _](pred0P Hdisj) orbF.
rewrite andbC; move/pred0P: Hdisj; move/(_ x0)=> /=.
by rewrite -topredE /=; case: a.
Qed.

Lemma ltn_0prodn_cond : forall I r (P : pred I) F,
  (forall i, P i -> 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Proof.
by move=> I r P F Fpos; apply big_prop => // n1 n2; rewrite ltn_0mul => ->.
Qed.

Lemma ltn_0prodn : forall I r (P : pred I) F,
  (forall i, 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Proof. move=> I r P F Fpos; exact: ltn_0prodn_cond. Qed.

Notation "\max_ ( <- r | P ) F" :=
  (\big[maxn/0%N]_(<- r | P%B) F%N) : nat_scope.
Notation "\max_ ( i <- r | P ) F" :=
  (\big[maxn/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\max_ ( i <- r ) F" :=
  (\big[maxn/0%N]_(i <- r) F%N) : nat_scope.
Notation "\max_ ( i | P ) F" :=
  (\big[maxn/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\max_ i F" :=
  (\big[maxn/0%N]_i F%N) : nat_scope.
Notation "\max_ ( i : I | P ) F" :=
  (\big[maxn/0%N]_(i : I | P%B) F%N) (only parsing) : nat_scope.
Notation "\max_ ( i : I ) F" :=
  (\big[maxn/0%N]_(i : I) F%N) (only parsing) : nat_scope.
Notation "\max_ ( m <= i < n | P ) F" :=
 (\big[maxn/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( m <= i < n ) F" :=
 (\big[maxn/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\max_ ( i < n | P ) F" :=
 (\big[maxn/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( i < n ) F" :=
 (\big[maxn/0%N]_(i < n) F%N) : nat_scope.
Notation "\max_ ( i \in A | P ) F" :=
 (\big[maxn/0%N]_(i \in A | P%B) F%N) : nat_scope.
Notation "\max_ ( i \in A ) F" :=
 (\big[maxn/0%N]_(i \in A) F%N) : nat_scope.

Lemma leq_bigmax_cond : forall (I : finType) (P : pred I) F i0,
  P i0 -> F i0 <= \max_(i | P i) F i.
Proof.
by move=> I P F i0 Pi0; rewrite -eqn_maxr (bigD1 i0) // maxnA /= maxnn eqxx.
Qed.

Lemma leq_bigmax : forall (I : finType) F (i0 : I), F i0 <= \max_i F i.
Proof. by move=> *; exact: leq_bigmax_cond. Qed.

Implicit Arguments leq_bigmax_cond [I P F].
Implicit Arguments leq_bigmax [I F].

Lemma eq_bigmax_cond : forall (I : finType) (P : pred I) F,
  ~~ pred0b P -> exists i0, P i0 && (F i0 == \max_(i | P i) F i).
Proof.
move=> I P F n0P; set m := \max_(i | P i) F i.
pose ub i := P i && (F i >= m); case: (pickP ub) => [i| ub0].
  by case/andP=> Pi ubi; exists i; rewrite Pi eqn_leq leq_bigmax_cond.
have ubm: forall i, P i -> F i < m.
  by move=> i Pi; case/nandP: (ub0 i); rewrite (Pi, ltnNge).
case/idP: (ltnn m); apply: (@big_prop _ (fun n => n < m)) => // [|n1 n2].
  by case/existsP: n0P => i; move/ubm; exact: leq_trans.
by rewrite !ltnNge leq_maxr negb_or => ->.
Qed.

Lemma eq_bigmax : forall (I : finType) F,
  (~~ pred0b I) -> exists i0 : I, (F i0 == \max_i F i).
Proof.
by move=> I F; move/(eq_bigmax_cond F)=> [] x; move/andP=> [] _; exists x.
Qed.

Implicit Arguments eq_bigmax_cond [I P F].
Implicit Arguments eq_bigmax [I F].

Unset Implicit Arguments.
