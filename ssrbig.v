Require Import ssreflect ssrbool funs eqtype ssrnat div seq fintype.
Require Import tuple paths connect.
Require Import ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\big [ op / nil ]_ ( <- r | P ) F"
  (at level 36, F at level 36, op, nil at level 10, r at level 50,
     right associativity,
           format "\big [ op / nil ]_ ( <-  r  |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i, r at level 50,
           format "\big [ op / nil ]_ ( i  <-  r  |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, nil at level 10, i, r at level 50,
           format "\big [ op / nil ]_ ( i  <-  r )  F").
Reserved Notation "\big [ op / nil ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, nil at level 10, m, i, n at level 50,
           format "\big [ op / nil ]_ ( m  <=  i  <  n  |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, nil at level 10, i, m, n at level 50,
           format "\big [ op / nil ]_ ( m  <=  i  <  n )  F").
Reserved Notation "\big [ op / nil ]_ ( i | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "\big [ op / nil ]_ ( i  |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( i ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "\big [ op / nil ]_ ( i )  F").
Reserved Notation "\big [ op / nil ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "\big [ op / nil ]_ ( i   :  t   |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( i : t ) F"
  (at level 36, F at level 36, op, nil at level 10, i at level 50,
           format "\big [ op / nil ]_ ( i   :  t )  F").
Reserved Notation "\big [ op / nil ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i, n at level 50,
           format "\big [ op / nil ]_ ( i  <  n  |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( i < n ) F"
  (at level 36, F at level 36, op, nil at level 10, i, n at level 50,
           format "\big [ op / nil ]_ ( i  <  n )  F").
Reserved Notation "\big [ op / nil ]_ ( i <= n | P ) F"
  (at level 36, F at level 36, op, nil at level 10, i, n at level 50,
           format "\big [ op / nil ]_ ( i  <=  n  |  P )  F").
Reserved Notation "\big [ op / nil ]_ ( i <= n ) F"
  (at level 36, F at level 36, op, nil at level 10, i, n at level 50,
           format "\big [ op / nil ]_ ( i  <=  n )  F").

Reserved Notation "\sum_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
     right associativity,
           format "\sum_ ( <-  r  |  P )  F").
Reserved Notation "\sum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "\sum_ ( i  <-  r  |  P )  F").
Reserved Notation "\sum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "\sum_ ( i  <-  r )  F").
Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "\sum_ ( m  <=  i  <  n  |  P )  F").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "\sum_ ( m  <=  i  <  n )  F").
Reserved Notation "\sum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "\sum_ ( i  |  P )  F").
Reserved Notation "\sum_ ( i ) F"
  (at level 41, F at level 41, i at level 50,
           format "\sum_ ( i )  F").
Reserved Notation "\sum_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\sum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\sum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\sum_ ( i  <  n  |  P )  F").
Reserved Notation "\sum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\sum_ ( i  <  n )  F").
Reserved Notation "\sum_ ( i <= n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\sum_ ( i  <=  n  |  P )  F").
Reserved Notation "\sum_ ( i <= n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\sum_ ( i  <=  n )  F").

Reserved Notation "\max_ ( <- r | P ) F"
  (at level 41, F at level 41, r at level 50,
           format "\max_ ( <-  r  |  P )  F").
Reserved Notation "\max_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "\max_ ( i  <-  r  |  P )  F").
Reserved Notation "\max_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "\max_ ( i  <-  r )  F").
Reserved Notation "\max_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "\max_ ( m  <=  i  <  n  |  P )  F").
Reserved Notation "\max_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "\max_ ( m  <=  i  <  n )  F").
Reserved Notation "\max_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "\max_ ( i  |  P )  F").
Reserved Notation "\max_ ( i ) F"
  (at level 41, F at level 41, i at level 50,
           format "\max_ ( i )  F").
Reserved Notation "\max_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\max_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\max_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\max_ ( i  <  n  |  P )  F").
Reserved Notation "\max_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\max_ ( i  <  n )  F").
Reserved Notation "\max_ ( i <= n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\max_ ( i  <=  n  |  P )  F").
Reserved Notation "\max_ ( i <= n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "\max_ ( i  <=  n )  F").

Reserved Notation "\prod_ ( <- r | P ) F"
  (at level 36, F at level 36, r at level 50,
           format "\prod_ ( <-  r  |  P )  F").
Reserved Notation "\prod_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "\prod_ ( i  <-  r  |  P )  F").
Reserved Notation "\prod_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "\prod_ ( i  <-  r )  F").
Reserved Notation "\prod_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "\prod_ ( m  <=  i  <  n  |  P )  F").
Reserved Notation "\prod_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "\prod_ ( m  <=  i  <  n )  F").
Reserved Notation "\prod_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "\prod_ ( i  |  P )  F").
Reserved Notation "\prod_ ( i ) F"
  (at level 36, F at level 36, i at level 50,
           format "\prod_ ( i )  F").
Reserved Notation "\prod_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50,
           only parsing).
Reserved Notation "\prod_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50,
           only parsing).
Reserved Notation "\prod_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "\prod_ ( i  <  n  |  P )  F").
Reserved Notation "\prod_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "\prod_ ( i  <  n )  F").
Reserved Notation "\prod_ ( i <= n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "\prod_ ( i  <=  n  |  P )  F").
Reserved Notation "\prod_ ( i <= n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "\prod_ ( i  <=  n )  F").

Delimit Scope big_scope with BIG.
Open Scope big_scope.

Definition reducebig R I op nil (r : seq I) P F : R :=
  locked foldr (fun i x => if P i then op (F i : R) x else x) nil r.

Definition index_iota m n := nosimpl iota m (n - m).

Definition index_enum := nosimpl enum.

Notation "\big [ op / nil ]_ ( <- r | P ) F" :=
  (reducebig op nil r P F) : big_scope.
Notation "\big [ op / nil ]_ ( i <- r | P ) F" :=
  (reducebig op nil r (fun i => P) (fun i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( i <- r ) F" :=
  (reducebig op nil r (fun _ => true) (fun  i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( m <= i < n | P ) F" :=
  (reducebig op nil (index_iota m n) (fun i : nat => P) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / nil ]_ ( m <= i < n ) F" :=
  (reducebig op nil (index_iota m n) (fun _ => true) (fun i : nat => F))
     : big_scope.
Notation "\big [ op / nil ]_ ( i | P ) F" :=
  (reducebig op nil (index_enum _) (fun i => P) (fun i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( i ) F" :=
  (reducebig op nil (index_enum _) (fun _ => true) (fun i => F)) : big_scope.
Notation "\big [ op / nil ]_ ( i : t | P ) F" :=
  (reducebig op nil (index_enum _) (fun i : t => P) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / nil ]_ ( i : t ) F" :=
  (reducebig op nil (index_enum _) (fun _ => true) (fun i : t => F))
     (only parsing) : big_scope.
Notation "\big [ op / nil ]_ ( i < n | P ) F" :=
  (\big[op/nil]_(i : ordinal n | P) F) : big_scope.
Notation "\big [ op / nil ]_ ( i < n ) F" :=
  (\big[op/nil]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / nil ]_ ( i <= n | P ) F" :=
  (\big[op/nil]_(i < n.+1 | P) F) : big_scope.
Notation "\big [ op / nil ]_ ( i <= n ) F" :=
  (\big[op/nil]_(i < n.+1) F) : big_scope.

Notation Local "'+%R'" := (@Ring.add _) (at level 0).
Notation Local "'+%N'" := addn (at level 0, only parsing).

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%R/0%R]_(<- r | P) F) : ring_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P) F) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P) F) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P) F) : ring_scope.
Notation "\sum_ ( i ) F" :=
  (\big[+%R/0%R]_(i) F) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P) F) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P) F) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F) : ring_scope.
Notation "\sum_ ( i <= n | P ) F" :=
  (\big[+%R/0%R]_(i <= n | P) F) : ring_scope.
Notation "\sum_ ( i <= n ) F" :=
  (\big[+%R/0%R]_(i <= n) F) : ring_scope.

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%N/0%N]_(<- r | P) F) : dnat_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%N/0%N]_(i <- r | P) F) : dnat_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%N/0%N]_(i <- r) F) : dnat_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P) F) : dnat_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F) : dnat_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%N/0%N]_(i | P) F) : dnat_scope.
Notation "\sum_ ( i ) F" :=
  (\big[+%N/0%N]_(i) F) : dnat_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%N/0%N]_(i : t | P) F) (only parsing) : dnat_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%N/0%N]_(i : t) F) (only parsing) : dnat_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%N/0%N]_(i < n | P) F) : dnat_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%N/0%N]_(i < n) F) : dnat_scope.
Notation "\sum_ ( i <= n | P ) F" :=
  (\big[+%N/0%N]_(i <= n | P) F) : dnat_scope.
Notation "\sum_ ( i <= n ) F" :=
  (\big[+%N/0%N]_(i <= n) F) : dnat_scope.

Notation Local "'*%R'" := (@Ring.mul _) (at level 0).
Notation Local "'*%N'" := muln (at level 0, only parsing).

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%R/1%R]_(<- r | P) F) : ring_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P) F) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P) F) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P) F) : ring_scope.
Notation "\prod_ ( i ) F" :=
  (\big[*%R/1%R]_(i) F) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P) F) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P) F) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F) : ring_scope.
Notation "\prod_ ( i <= n | P ) F" :=
  (\big[*%R/1%R]_(i <= n | P) F) : ring_scope.
Notation "\prod_ ( i <= n ) F" :=
  (\big[*%R/1%R]_(i <= n) F) : ring_scope.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%N/1%N]_(<- r | P) F) : dnat_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%N/1%N]_(i <- r | P) F) : dnat_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%N/1%N]_(i <- r) F) : dnat_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%N/1%N]_(m <= i < n | P) F) : dnat_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%N/1%N]_(m <= i < n) F) : dnat_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%N/1%N]_(i | P) F) : dnat_scope.
Notation "\prod_ ( i ) F" :=
  (\big[*%N/1%N]_(i) F) : dnat_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%N/1%N]_(i : t | P) F) (only parsing) : dnat_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%N/1%N]_(i : t) F) (only parsing) : dnat_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%N/1%N]_(i < n | P) F) : dnat_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%N/1%N]_(i < n) F) : dnat_scope.
Notation "\prod_ ( i <= n | P ) F" :=
  (\big[*%N/1%N]_(i <= n | P) F) : dnat_scope.
Notation "\prod_ ( i <= n ) F" :=
  (\big[*%N/1%N]_(i <= n) F) : dnat_scope.

Section Extensionality.

Variables (R : Type)  (nil : R) (op : R -> R -> R).

Section SeqExtension.

Variable I : eqType.

Lemma big_filter : forall (r : seq I) P F,
  \big[op/nil]_(i <- filter P r) F i = \big[op/nil]_(i <- r | P i) F i.
Proof. by unlock reducebig => r P F; elim: r => //= i r <-; case (P i). Qed.

Lemma big_filter_cond : forall (r : seq I) P1 P2 F,
  \big[op/nil]_(i <- filter P1 r | P2 i) F i
     = \big[op/nil]_(i <- r | P1 i && P2 i) F i.
Proof.
move=> r P1 P2 F; rewrite -big_filter -(big_filter r); congr reducebig.
rewrite -filter_setI; apply: eq_filter => i; exact: andbC.
Qed.

Lemma congr_big : forall (r1 r2 : seq I) P1 P2 F1 F2,
   r1 = r2 -> dfequal r1 P1 P2 -> dfequal (setI r1 P1) F1 F2 ->
    \big[op/nil]_(i <- r1 | P1 i) F1 i = \big[op/nil]_(i <- r2 | P2 i) F2 i.
Proof.
move=> r1 r2 P1 P2 F1 F2 <-{r2}; set P := setI r1 P1 => eq_P eq_F.
rewrite -!(big_filter r1) -(eqd_filter eq_P); set r := filter P1 r1.
have: all P r by apply/allP=> i; rewrite mem_filter /setI andbC.
move/all_filterP <-; rewrite !big_filter; unlock reducebig.
by elim: r => //= i r ->; case Pi: (P i); rewrite // eq_F.
Qed.

Lemma eq_big : forall (r : seq I) P1 P2 F1 F2, P1 =1 P2 -> dfequal P1 F1 F2 -> 
  \big[op/nil]_(i <- r | P1 i) F1 i = \big[op/nil]_(i <- r | P2 i) F2 i.
Proof.
move=> r P1 P2 F1 F2 eqP12 eqF12; apply: congr_big => // i.
by case/andP=> _; exact: eqF12.
Qed.

Lemma eq_bigl : forall (r : seq I) P1 P2 F, P1 =1 P2 ->
  \big[op/nil]_(i <- r | P1 i) F i = \big[op/nil]_(i <- r | P2 i) F i.
Proof. by move=> *; exact: eq_big. Qed.

Lemma eq_bigr : forall (r : seq I) P F1 F2, dfequal P F1 F2 ->
  \big[op/nil]_(i <- r | P i) F1 i = \big[op/nil]_(i <- r | P i) F2 i.
Proof. by move=> *; exact: eq_big. Qed.

Lemma big_seq0 : forall P F, \big[op/nil]_(i <- Seq0 I | P i) F i = nil.
Proof. by unlock reducebig. Qed.

Lemma big_adds : forall i (r : seq I) P F,
  let x := \big[op/nil]_(j <- r | P j) F j in
  \big[op/nil]_(j <- Adds i r | P j) F j = if P i then op (F i) x else x.
Proof. by unlock reducebig. Qed.

Lemma big_maps : forall (J : eqType) (h : J -> I) r F P,
  \big[op/nil]_(i <- maps h r | P i) F i
     = \big[op/nil]_(j <- r | P (h j)) F (h j).
Proof. by unlock reducebig => J h r P F; elim: r => //= j r ->. Qed.

Lemma big_sub : forall (x0 : I) r P F,
  \big[op/nil]_(i <- r | P i) F i
     = \big[op/nil]_(0 <= i < size r | P (sub x0 r i)) (F (sub x0 r i)).
Proof.
by move=> x0 r P F; rewrite -{1}(mkseq_sub x0 r) big_maps /index_iota subn0.
Qed.

Lemma big_hasC : forall (r : seq I) P F, ~~ has P r ->
  \big[op/nil]_(i <- r | P i) F i = nil.
Proof.
move=> r P F; rewrite -big_filter has_filter; case: filter=> // _.
exact: big_seq0.
Qed.
  
Lemma big_set0_eq : forall (r : seq I) F,
  \big[op/nil]_(i <- r | false) F i = nil.
Proof. by move=> r F; rewrite big_hasC // has_set0. Qed.

Lemma big_set0 : forall (r : seq I) P F, P =1 set0 ->
  \big[op/nil]_(i <- r | P i) F i = nil.
Proof. move=> r P F; move/eq_bigl->; exact: big_set0_eq. Qed.

Lemma big_cat_nested : forall (r1 r2 : seq I) P F,
  let x := \big[op/nil]_(i <- r2 | P i) F i in
  \big[op/nil]_(i <- cat r1 r2 | P i) F i = \big[op/x]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; unlock reducebig; rewrite foldr_cat. Qed.

Lemma big_catl : forall (r1 r2 : seq I) P F, ~~ has P r2 ->
  \big[op/nil]_(i <- cat r1 r2 | P i) F i = \big[op/nil]_(i <- r1 | P i) F i.
Proof. by move=> r1 r2 P F; rewrite big_cat_nested; move/big_hasC->. Qed.

Lemma big_catr : forall (r1 r2 : seq I) P F, ~~ has P r1 ->
  \big[op/nil]_(i <- cat r1 r2 | P i) F i = \big[op/nil]_(i <- r2 | P i) F i.
Proof.
move=> r1 r2 P F; rewrite -big_filter -(big_filter r2) filter_cat has_filter.
by case: filter.
Qed.

Lemma big_const_seq : forall (r : seq I) P x,
  \big[op/nil]_(i <- r | P i) x = iter (count P r) (op x) nil.
Proof. by unlock reducebig => r P x; elim: r => //= i r ->; case: (P i). Qed.

End SeqExtension.

Lemma big_geq : forall m n P F, m >= n ->
  \big[op/nil]_(m <= i < n | P i) F i = nil.
Proof.
by move=> m n P F ge_m_n; rewrite /index_iota (eqnP ge_m_n) big_seq0.
Qed.

Lemma big_ltn_cond : forall m n P F, m < n ->
  let x := \big[op/nil]_(m.+1 <= i < n | P i) F i in
  \big[op/nil]_(m <= i < n | P i) F i = if P m then op (F m) x else x.
Proof.
by move=> m [//|n] P F le_m_n; rewrite /index_iota leq_subS // big_adds.
Qed.

Lemma big_ltn : forall m n F, m < n ->
  \big[op/nil]_(m <= i < n) F i = op (F m) (\big[op/nil]_(m.+1 <= i < n) F i).
Proof. move=> *; exact: big_ltn_cond. Qed.

Lemma big_addn : forall m n a P F,
  \big[op/nil]_(m + a <= i < n | P i) F i =
     \big[op/nil]_(m <= i < n - a | P (i + a)) F (i + a).
Proof.
move=> m n a P F; rewrite /index_iota subn_sub addnC iota_addl big_maps.
by apply: eq_big => ? *; rewrite addnC.
Qed.

Lemma big_add1 : forall m n P F,
  \big[op/nil]_(m.+1 <= i < n | P i) F i =
     \big[op/nil]_(m <= i < n.-1 | P (i.+1)) F (i.+1).
Proof.
move=> m n P F; rewrite -addn1 big_addn subn1.
by apply: eq_big => ? *; rewrite addn1.
Qed.

Lemma big_mkord : forall n P F,
  \big[op/nil]_(0 <= i < n | P i) F i = \big[op/nil]_(i < n | P i) F i.
Proof.
move=> n P F; rewrite /index_iota subn0 -(big_maps (@nat_of_ord n)).
symmetry; congr reducebig; rewrite -maps_comp -(@eq_maps _ _ val) => [|[]//].
by rewrite val_subfilter; apply/all_filterP; apply/allP=> i; rewrite mem_iota.
Qed.

Lemma big_nat_widen : forall m n1 n2 P F, n1 <= n2 ->
  \big[op/nil]_(m <= i < n1 | P i) F i
      = \big[op/nil]_(m <= i < n2 | P i && (i < n1)) F i.
Proof.
move=> m n1 n2 P F len12; symmetry; rewrite -big_filter filter_setI big_filter.
congr reducebig; rewrite /index_iota; set d1 := n1 - m; set d2 := n2 - m.
rewrite -(@leq_add_sub d1 d2) /=; last by rewrite leq_sub2r ?leq_addr.
have: ~~ has (fun i => i < n1) (iota (m + d1) (d2 - d1)).
  apply/hasPn=> i; rewrite mem_iota -leqNgt; case/andP=> le_mn1_i _.
  by apply: leq_trans le_mn1_i; rewrite -leq_sub_add.
rewrite iota_add filter_cat has_filter /=; case: filter => // _.
rewrite cats0; apply/all_filterP; apply/allP=> i.
rewrite mem_iota; case/andP=> le_m_i lt_i_md1.
apply: (leq_trans lt_i_md1); rewrite leq_add_sub // ltnW //.
rewrite -ltn_0sub -(ltn_add2l m) addn0; exact: leq_trans lt_i_md1.
Qed.

Lemma big_ord_widen_cond : forall n1 n2 (P : nat -> _) (F : nat -> _),
     n1 <= n2 ->
  \big[op/nil]_(i < n1 | P i) F i
      = \big[op/nil]_(i < n2 | P i && (i < n1)) F i.
Proof.
move=> n1 n2 P F len12.
by rewrite -big_mkord (big_nat_widen _ _ _ len12) big_mkord.
Qed.

Lemma big_ord_widen : forall n1 n2 (F : nat -> _),
 n1 <= n2 ->
  \big[op/nil]_(i < n1) F i = \big[op/nil]_(i < n2 | i < n1) F i.
Proof. move=> *; exact: (big_ord_widen_cond (setA _)). Qed.

Lemma big_ord_widen_leq : forall n1 n2 P F,
 n1 < n2 ->
  \big[op/nil]_(i <= n1 | P i) F i
      = \big[op/nil]_(i < n2 | P (inord i) && (i <= n1)) F (inord i).
Proof.
move=> n1 n2 P F len12; pose g G i := G (@inord n1 i).
rewrite -(big_ord_widen_cond (g _ P) (g _ F) len12) {}/g.
by apply: eq_big => i *; rewrite inord_id.
Qed.

Lemma big_ord_narrow_cond : forall n1 n2 P F (le_n1_n2 : n1 <= n2),
  let w := widen_ord le_n1_n2 in
  \big[op/nil]_(i < n2 | P i && (i < n1)) F i
    = \big[op/nil]_(i < n1 | P (w i)) F (w i).
Proof.
move=> [|n1] n2 P F ltn12 /=.
  by rewrite big_seq0 big_set0 // => i; rewrite andbF.
rewrite (big_ord_widen_leq _ _ ltn12); apply: eq_big => i.
  rewrite ltnS; case: leqP => [le_i_n1|_]; last by rewrite !andbF.
  by congr (P _ && _); apply: ordinal_inj; rewrite /= inord_eq.
by case/andP=> _ le_i_n1; congr F; apply: ordinal_inj; rewrite /= inord_eq.
Qed.

Lemma big_ord_narrow_cond_leq : forall n1 n2 P F (le_n1_n2 : n1 <= n2),
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/nil]_(i <= n2 | P i && (i <= n1)) F i
  = \big[op/nil]_(i <= n1 | P (w i)) F (w i).
Proof. move=> n1 n2; exact: big_ord_narrow_cond n1.+1 n2.+1. Qed.

Lemma big_ord_narrow : forall n1 n2 F (le_n1_n2 : n1 <= n2),
  let w := widen_ord le_n1_n2 in
  \big[op/nil]_(i < n2 | i < n1) F i = \big[op/nil]_(i < n1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond (setA _)). Qed.

Lemma big_ord_narrow_leq : forall n1 n2 F (le_n1_n2 : n1 <= n2),
  let w := @widen_ord n1.+1 n2.+1 le_n1_n2 in
  \big[op/nil]_(i <= n2 | i <= n1) F i = \big[op/nil]_(i <= n1) F (w i).
Proof. move=> *; exact: (big_ord_narrow_cond_leq (setA _)). Qed.

Lemma big_ord_recl : forall n F,
  \big[op/nil]_(i <= n) F i =
     op (F ord0) (\big[op/nil]_(i < n) F (lift ord0 i)).
Proof.
move=> n F; pose G i := F (inord i).
have eqFG: forall i, F i = G i by move=> i; rewrite /G inord_id.
rewrite (eq_bigr _ (fun i _ => eqFG i)) -(big_mkord _ (fun _ => _) G) eqFG.
rewrite big_ltn // big_add1 /= big_mkord; congr op.
by apply: eq_bigr => i _; rewrite eqFG.
Qed.

Lemma big_const : forall (I : finType) P x,
  \big[op/nil]_(i : I | P i) x = iter (card P) (op x) nil.
Proof. by move=> *; exact: big_const_seq. Qed.

Lemma big_const_nat : forall m n x,
  \big[op/nil]_(m <= i < n) x = iter (n - m) (op x) nil.
Proof. by move=> *; rewrite big_const_seq count_setA size_iota. Qed.

Lemma big_const_ord : forall n x,
  \big[op/nil]_(i < n) x = iter n (op x) nil.
Proof. by move=> *; rewrite big_const card_ordinal. Qed.

End Extensionality.

Section MonoidProperties.

Import Monoid.

Variable R : Type.

Variable nil : R.
Notation Local "1" := nil.

Section Plain.

Variable op : Monoid.law 1.

Notation Local "'*%M'" := (operator op) (at level 0).
Notation Local "x * y" := ( *%M x y).

Lemma eq_big_nil_seq  : forall nil' I (r : seq I) P F,
     right_unit nil' *%M -> has P r ->
   \big[*%M/nil']_(i <- r | P i) F i =\big[*%M/1]_(i <- r | P i) F i.
Proof.
move=> nil' I r P F op_nil'; rewrite -!(big_filter _ _ r) has_count count_filter.
case/lastP: (filter P r) => {r p}// r i _.
by rewrite -cats1 !(big_cat_nested, big_adds, big_seq0) op_nil' mulm1.
Qed.

Lemma eq_big_nil  : forall nil' (I : finType) i0 (P : set I) F,
     P i0 -> right_unit nil' *%M ->
  \big[*%M/nil']_(i | P i) F i =\big[*%M/1]_(i | P i) F i.
Proof.
move=> nil' I i0 P F op_nil' Pi0; apply: eq_big_nil_seq => //.
by apply/hasP; exists i0; first exact: mem_enum.
Qed.

Lemma big1_eq : forall I (r : seq I) P, \big[*%M/1]_(i <- r | P i) 1 = 1.
Proof.
move=> *; rewrite big_const_seq; elim: (count _ _) => //= n ->; exact: mul1m.
Qed.

Lemma big1 : forall (I : finType) P F,
  dfequal P F (fun _ : I => 1) -> \big[*%M/1]_(i | P i) F i = 1.
Proof. by move=> I P F eq_F_1; rewrite (eq_bigr _ _ _ eq_F_1) big1_eq. Qed.

Lemma big1_seq : forall I (r : seq I) P F,
  dfequal (setI r P) F (fun _ => 1) -> \big[*%M/1]_(i <- r | P i) F i = 1.
Proof. move=> I r P F; rewrite -{4}(big1_eq r P); exact: congr_big. Qed.

Lemma big_seq1 : forall (I : eqType) (i : I) F,
  \big[*%M/1]_(j <- Seq i) F j = F i.
Proof. by unlock reducebig => /= *; rewrite mulm1. Qed.

Lemma big_mkcond : forall I (r : seq I) P F,
  \big[*%M/1]_(i <- r | P i) F i =
     \big[*%M/1]_(i <- r) (if P i then F i else 1).
Proof.
unlock reducebig => I r P F; elim: r => //= i r ->.
by case (P i); rewrite ?mul1m.
Qed.

Lemma big_cat : forall I (r1 r2 : seq I) P F,
  \big[*%M/1]_(i <- cat r1 r2 | P i) F i =
     \big[*%M/1]_(i <- r1 | P i) F i * \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; rewrite !(big_mkcond _ P).
elim: r1 => [|i r1 IHr1]; first by rewrite big_seq0 mul1m.
by rewrite /= !big_adds IHr1 mulmA.
Qed.

Lemma big_set1_eq : forall (I : finType) (i : I) F,
  \big[*%M/1]_(j | i == j) F j = F i.
Proof.
move=> I i F; move: (filter_enum (set1 i) i) (FinType.enumP i).
rewrite set11 count_filter -big_filter; move: (filter _ _); case=> [|j []] //.
by rewrite mem_seq1 big_seq1; move/eqP->.
Qed.

Lemma big_set1 : forall (I : finType) (i : I) P F,
  P =1 set1 i -> \big[*%M/1]_(j | P j) F j = F i.
Proof. move=> I i P F; move/(eq_bigl _ _)->; exact: big_set1_eq. Qed.

Lemma big_ord_recr : forall n F,
  \big[*%M/1]_(i <= n) F i =
     \big[*%M/1]_(i < n) F (widen_ord (leqnSn n) i) * F ord_max.
Proof.
move=> n F.
move: (@big_mkord _ 1 *%M (n.+1) (fun _ => true) 
             (fun i => if insub (fun m => m < n.+1) i is Some u then
                          F (ord_of_natsig u) else 1)).
have h: dfequal (fun _ => true)
   (fun i : ordinal_eqType n.+1 =>
    match insub (fun m : nat_eqType => m < n.+1) i with
    | Some u => F (ord_of_natsig (n:=n.+1) u)
    | None => 1
    end) (fun i => F i).
 move => i _; case:i => i hi /=; rewrite (@insubT _ (fun i => i < n.+1) _ hi).
 by congr F; apply: ord_eqP.
rewrite (eq_bigr 1 *%M _ (F2:= fun i => F i)) => //=; clear h; move =><-.
have h:dfequal (fun _ => true)
   (fun i :ordinal n=>
    match insub (fun m : nat_eqType => m < n) i with
    | Some u => F (widen_ord (leqnSn n) (ord_of_natsig (n:=n) u))
    | None => 1
    end) (fun i => F (widen_ord (leqnSn n) i)).
 move => i _; case: i => i hi /=; rewrite (@insubT _ (fun i => i < n) _ hi).
 by congr F; apply: ord_eqP.
move: (@big_mkord _ 1 *%M n (fun _ => true)
             (fun i => if insub (fun m => m < n) i is Some u then
                 F (widen_ord (m:=n.+1)(leqnSn n)
                      (ord_of_natsig u)) else 1)).
rewrite (eq_bigr 1 *%M _ (F2 := fun i => F (widen_ord (leqnSn n) i))) => //= <-.

move: {h} F; elim: n => [F | n IHn F].
 have h'': 0 < 1 by done.
 rewrite (big_geq 1 *%M (n:=0)) //=;  unlock reducebig index_iota iota; 
 rewrite /= (mulm1 op) (mul1m op) (@insubT _ (fun m => m < 1) 0 h'') => /=.
 by congr F; apply/ord_eqP => /=.
have h'': 0 < n.+1.+1 by done.
rewrite !(@big_ltn _ _ _ 0) => //=.
rewrite (@insubT _ (fun m => m < n.+1.+1) 0 h'') => /=.
rewrite (@insubT _ (fun m => m < n.+1) 0 h'') /= -(mulmA op).
congr (_ * _); first by congr F; apply/ord_eqP; rewrite /widen_ord /=.
rewrite !big_add1 /=.
have h': dfequal (setI (index_iota 0 n.+1) (fun _ : nat_eqType => true))
   (fun i : nat =>
    match insub (fun m : nat => m < n.+1.+1) i.+1 with
    | Some u => F (ord_of_natsig (n:=n.+1.+1) u)
    | None => 1
    end)
   (fun i : nat =>
    match insub (fun m : nat => m < n.+1) i with
    | Some u => F (lift ord0 (ord_of_natsig (n:=n.+1) u))
    | None => 1
    end).
 move => i; rewrite /setI /index_iota andbT mem_iota add0n subn0 => hi.
 by case/andP: hi => _ hi;
 rewrite (@insubT _ (fun m => m < n.+1.+1) i.+1 hi)
   (@insubT _ (fun m => m < n.+1) i hi); congr F; apply/ord_eqP.
rewrite (@congr_big _ 1 *%M _ (index_iota 0 n.+1) _ (fun _ => true) 
          (fun _ => true)
          (fun i:nat => match insub (fun m : nat => m < n.+1.+1) i.+1 with
                        | Some u => F (ord_of_natsig u)
                        | None => 1
                        end)
          (fun i:nat => match insub (fun m :nat => m < n.+1) i with
                   | Some u => F (lift ord0 (ord_of_natsig u))
                   | None => 1
                   end)  (refl_equal _) (fun _ _ => (refl_equal true))) => //=.
rewrite {h' IHn} (IHn (fun i => F (lift ord0 i))).
congr (_ * _); last by congr F; apply/ord_eqP; rewrite /widen_ord //=.
apply: congr_big => //=.
move => x; rewrite /setI andbT /index_iota mem_iota add0n subn0.
case/andP => _ hx.
by rewrite (@insubT _ (fun m => m < n) x hx)
   (@insubT _ (fun m => m < n.+1) x.+1 hx); congr F; apply/ord_eqP.
Qed.

End Plain.

Section Abelian.

Variable op : abelian_law 1.

Notation Local "'*%M'" := (operator (law_of_abelian op)) (at level 0).
Notation Local "x * y" := ( *%M x y).

Lemma eq_big_perm : forall I (r1 r2 : seq I) P F,
  count^~ r1 =1 count^~ r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i = \big[*%M/1]_(i <- r2 | P i) F i.
Proof.
move=> I r1 r2 P F; rewrite !(big_mkcond _ _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2; move/(_ (set1 i)); rewrite /= set11.
have r2i: r2 i by rewrite -has_set1 has_count -eq_r12 /= set11.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *; rewrite big_cat /= !big_adds.
rewrite mulmCA; congr (_ * _); rewrite -big_cat; apply: IHr1 => a.
move/(_ a): eq_r12; rewrite !count_cat /= addnCA; exact: addn_injl.
Qed.

Lemma big_uniq : forall (I : finType) (r : seq I) F,
  uniq r -> \big[*%M/1]_(i <- r) F i = \big[*%M/1]_(i | r i) F i.
Proof.
move=> I r F uniq_r; rewrite -(big_filter _ _ _ r); apply: eq_big_perm=> a.
rewrite !count_filter -filter_setI -(card_uniqP _) ?uniq_filter //.
rewrite -count_filter; apply: eq_card; exact: mem_filter.
Qed.

Lemma big_split : forall I (r : seq I) P F1 F2,
  \big[*%M/1]_(i <- r | P i) (F1 i * F2 i) =
    \big[*%M/1]_(i <- r | P i) F1 i * \big[*%M/1]_(i <- r | P i) F2 i.
Proof.
unlock reducebig => I r P F1 F2.
elim: r => /= [|i r ->]; [by rewrite mulm1 | case: (P i) => //=].
rewrite !mulmA; congr (_ * _); exact: mulmAC.
Qed.

Lemma bigID : forall (I : finType) (a : set I) (P : I -> bool) F,
  \big[*%M/1]_(i | P i) F i
    = \big[*%M/1]_(i | P i && a i) F i * \big[*%M/1]_(i | P i && ~~ a i) F i.
Proof.
move=> I a P F; rewrite !(big_mkcond _ _ _ F) -big_split; apply: eq_bigr => i.
by case: (a i); rewrite !simpm.
Qed.

Lemma bigD1 : forall (I : finType) j (P : I -> bool) F,
  P j -> \big[*%M/1]_(i | P i) F i
    = F j * \big[*%M/1]_(i | P i && (i != j)) F i.
Proof.
move=> I j P F Pj; rewrite (bigID (set1 j)); congr (_ * _).
  by apply: big_set1 => i; rewrite andbC; case: eqP => // <-.
by apply: eq_bigl => i; rewrite eq_sym.
Qed.
Implicit Arguments bigD1 [I P F].

Lemma cardD1x : forall (I : finType) (A : set I) (j : I),
  A j -> card A = 1 + card (fun i => A i && (i != j)).
Proof.
move=> I A j Aj; rewrite (cardD1 j) Aj; congr (_ + _).
by apply: eq_card => i; rewrite andbC eq_sym.
Qed.
Implicit Arguments cardD1x [I A].

Lemma partition_big : forall (I J : finType) (P : set I) p (Q : set J) F,
    (forall i, P i -> Q (p i)) ->
      \big[*%M/1]_(i | P i) F i =
         \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i && (p i == j)) F i.
Proof.
move=> I J P p Q F Qp; transitivity (\big[*%M/1]_(i | P i && Q (p i)) F i).
  by apply: eq_bigl => i; case Pi: (P i); rewrite // Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn (card Q)) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite !big_set0 // => i; rewrite Q0 andbF.
rewrite ltnS (cardD1x j Qj) (bigD1 j) //; move/IHn=> {n IHn} <-.
rewrite (bigID (fun i => p i == j)); congr (_ * _); apply: eq_bigl => i.
  by case: eqP => [-> | _]; rewrite !(Qj, simpm).
by rewrite andbA.
Qed.

Implicit Arguments partition_big [I J P F].

Lemma reindex_onto : forall (I J : finType) (h : J -> I) h' P F,
    dcancel P h' h ->
  \big[*%M/1]_(i | P i) F i =
    \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
move=> I J h h' P F h'K.
elim: {P}_.+1 {-3}P h'K (ltnSn (card P)) => //= n IHn P h'K.
case: (pickP P) => [i Pi | P0 _]; last first.
  by rewrite !big_set0 // => j; rewrite P0.
rewrite ltnS (cardD1x i Pi); move/IHn {n IHn} => IH.
rewrite (bigD1 i Pi) (bigD1 (h' i)) h'K ?Pi ?set11 //; congr (_ * _).
rewrite {}IH => [|j]; [apply: eq_bigl => j | by case/andP; auto].
rewrite andbC -andbA (andbCA (P _)); case: eqP => //= hK; congr (_ && ~~ _).
by apply/eqP/eqP=> [<-|->] //; rewrite h'K.
Qed.
Implicit Arguments reindex_onto [I J P F].

Lemma reindex : forall (I J : finType) (h : J -> I) P F,
  ibijective P h ->
  \big[*%M/1]_(i | P i) F i = \big[*%M/1]_(j | P (h j)) F (h j).
Proof.
move=> I J h P F [h' hK h'K]; rewrite (reindex_onto _ _ h'K).
by apply: eq_bigl => j; case Pi: (P _); rewrite ?andbF // hK // set11.
Qed.
Implicit Arguments reindex [I J P F].

Lemma pair_big_dep : forall (I J : finType) P Q F,
  \big[*%M/1]_(i : I | P i) \big[*%M/1]_(j : J | Q i j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Proof.
move=> I J P Q F.
rewrite (partition_big (fun p => p.1) P) => [|j]; last by case/andP.
apply: eq_bigr => i Pi; rewrite (reindex_onto (pair i) (fun p => p.2)).
  by apply: eq_bigl => j; rewrite !set11 Pi !andbT.
by case=> i' j /=; case/andP=> _; move/eqP->.
Qed.

Lemma pair_big : forall (I J : finType) P Q F,
  \big[*%M/1]_(i : I | P i) \big[*%M/1]_(j : J | Q j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.2) F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma pair_bigA_ : forall (I J: finType) F,
  \big[*%M/1]_(i : I) \big[*%M/1]_(j : J) F i j = \big[*%M/1]_(p) F p.1 p.2.
Proof. move=> *; exact: pair_big_dep. Qed.

Lemma exchange_big_dep :
    forall (I J : finType) (P : set I) (Q : I -> set J) (xQ : set J) F,
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(j | xQ j) \big[*%M/1]_(i | P i && Q i j) F i j.
Proof.
move=> I J P Q xQ F PQxQ; pose p u := (u.2, u.1).
rewrite !pair_big_dep (reindex_onto (p J I) (p I J)) => [|[//]].
apply: eq_big => [] [j i] //=; symmetry; rewrite set11 andbC.
case: (@andP (P i)) => //= [[]]; exact: PQxQ.
Qed.
Implicit Arguments exchange_big_dep [I J P Q F].

Lemma exchange_big :  forall (I J : finType) P Q F,
  \big[*%M/1]_(i : I | P i) \big[*%M/1]_(j : J | Q j) F i j =
    \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i) F i j.
Proof.
move=> I J P Q F; rewrite (exchange_big_dep Q) //; apply: eq_bigr => i Pi.
by apply: eq_bigl => j; rewrite Pi andbT.
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
Implicit Arguments big_set1 [R op nil I P F].
Implicit Arguments eq_big_perm [R op nil I r1 P F].
Implicit Arguments big_uniq [R op nil I F].
Implicit Arguments bigID [R op nil I].
Implicit Arguments bigD1 [R op nil I P F].
Implicit Arguments partition_big [R op nil I J P F].
Implicit Arguments reindex_onto [R op nil I J P F].
Implicit Arguments reindex [R op nil I J P F].
Implicit Arguments pair_big_dep [R op nil I J].
Implicit Arguments pair_big [R op nil I J].
Implicit Arguments exchange_big_dep [R op nil I J P Q F].
Implicit Arguments big_ord_recl [R op nil].
Implicit Arguments big_ord_recr [R op nil].

Section BigProp.

Variables (R1 : Type) (Pb : R1 -> Prop).
Variables (nil : R1) (op1 op2 : R1 -> R1 -> R1).
Hypothesis (p_nil : Pb nil)
           (p_op1 : forall x y, Pb x -> Pb y -> Pb (op1 x y))
           (p_eq_op : forall x y, Pb x -> Pb y -> op1 x y = op2 x y).

Lemma big_prop_seq : forall I (r : seq I) P F,
  (forall i, r i && P i -> Pb (F i)) -> Pb (\big[op1/nil]_(i <- r | P i) F i).
Proof.
move=> I r P F; elim: r => //= [|i r IHr] Pb_ir; rewrite !(big_seq0, big_adds) //.
have{IHr} IHr: Pb (\big[op1/nil]_(i <- r | P i) F i).
  by apply: IHr => j rPj; apply Pb_ir; rewrite andb_orl rPj orbT.
by case Pi: (P i); first by apply: p_op1; first by apply: Pb_ir; rewrite setU11.
Qed.

Lemma big_prop : forall (I : finType) (P : set I) F,
  (forall x, P x -> Pb (F x)) -> Pb (\big[op1/nil]_(i | P i) F i).
Proof. move=> I P F PbP; apply big_prop_seq => i; rewrite mem_enum; exact: PbP. Qed.

(* Change operation *)
Lemma eq_big_op_seq :  forall I (r : seq I) P F,
    (forall i, r i && P i -> Pb (F i)) ->
  \big[op1/nil]_(i <- r | P i) F i = \big[op2/nil]_(i <- r | P i) F i.
Proof.
move=> I r P F; elim: r => //= [|i r IHr] Pb_ir; rewrite !(big_seq0, big_adds) //.
have Pb_r: forall j, r j && P j -> Pb (F j).
  by move=> j rPj; apply Pb_ir; rewrite andb_orl rPj orbT.
rewrite -{}IHr //; case Pi: (P i) => //; apply p_eq_op; last exact: big_prop_seq.
by apply Pb_ir; rewrite setU11.
Qed.

Lemma eq_big_op :  forall (I : finType) (P : set I) F,
   (forall i, P i -> Pb (F i)) ->
  \big[op1/nil]_(i | P i) F i = \big[op2/nil]_(i | P i) F i.
Proof. move=> I P F PbP; apply eq_big_op_seq => i; rewrite mem_enum; exact: PbP. Qed.

End BigProp.

Implicit Arguments eq_big_op_seq [R1 nil op1 I r P F].
Implicit Arguments eq_big_op [R1 nil op1 I P F].

Section BigRel.

Variables (R1 : Type) (Prel : R1 ->R1-> Prop).
Variables  (nil : R1) (op1  : R1 -> R1 -> R1). 
Hypothesis (p_nil : Prel nil nil)
  (p_rel : forall a x b y, Prel a x -> Prel b y -> Prel (op1  a b) (op1 x y)).

Lemma big_rel_seq:
forall I (r : seq I) (P:I -> bool) F G,
  (forall i, (r i) && (P i) -> Prel (F i) (G i)) -> 
Prel (\big[op1/nil]_(i <- r | P i) F i) (\big[op1/nil]_(i <- r | P i) G i).
Proof.
move=> I r P F G; unlock reducebig;  elim: r => //= i r Hr.
case e : (P i) => H; [apply p_rel;
[by apply H; rewrite /setU1 // eq_refl orTb andTb e|] |];
by apply Hr=> i0; move/andP=> [Hri Hp]; 
apply H; rewrite /setU1 Hri Hp andbT orbT.
Qed.

Lemma big_rel:
forall (I: finType) (P: set I) F G,
  (forall i, (P i) -> Prel (F i) (G i)) -> 
Prel (\big[op1/nil]_(i | P i) F i) (\big[op1/nil]_(i  | P i) G i).
Proof.
move=> I P F G PbP; apply big_rel_seq => i;
rewrite mem_enum; exact: PbP.
Qed.


End BigRel.

Implicit Arguments big_rel_seq [R1 nil op1 I r P F G].
Implicit Arguments big_rel [R1 nil op1 I P F G].


Section Morphism.

Variables R1 R2 : Type.
Variables (nil1 : R1) (nil2 : R2).
Variables (op1 : R1 -> R1 -> R1) (op2 : R2 -> R2 -> R2).
Variable phi : R1 -> R2.
Hypothesis phi_morphism : Monoid.morphism nil1 nil2 op1 op2 phi.

Lemma big_morph : forall I (r : seq I) P F,
  phi (\big[op1/nil1]_(i <- r | P i) F i) =
     \big[op2/nil2]_(i <- r | P i) phi (F i).
Proof.
case: phi_morphism => [phi1 phiM] I r P F.
by unlock reducebig; elim: r => //= i r <-; case: (P i).
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
Notation Local "'*%M'" := (mul_operator times) (at level 0).
Notation Local "x * y" := ( *%M x y).
Variable plus : add_law times.
Notation Local "'+%M'" :=
  (operator (law_of_abelian (law_of_additive plus))) (at level 0).
Notation Local "x + y" := ( +%M x y).

Lemma big_distrl : forall I (r : seq I) alpha P F,
  \big[+%M/0]_(i <- r | P i) F i * alpha
    = \big[+%M/0]_(i <- r | P i) (F i * alpha).
Proof.
move=> *; apply: (big_morph ( *%M^~ _)).
by split=> *; rewrite (mul0m,  mulm_addl).
Qed.

Lemma big_distrr : forall I (r : seq I) alpha P F,
  alpha * \big[+%M/0]_(i <- r | P i) F i
    = \big[+%M/0]_(i <- r | P i) (alpha * F i).
Proof.
move=> *; apply: (big_morph ( *%M _)).
by split=> *; rewrite (mulm0,  mulm_addr).
Qed.

Lemma big_distr_big_dep :
  forall (I J : finType) j0 (P : set I) (Q : I -> set J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q i j) F i j =
     \big[+%M/0]_(f | pfamily j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite -big_filter; set r := filter P _.
pose fIJ := fgraphType I J; pose Pf := pfamily j0 _ Q; symmetry.
transitivity (\big[+%M/0]_(f | Pf r f) \big[*%M/1]_(i <- r) F i (f i)).
  apply: eq_big=> f; last by rewrite big_filter.
  apply/familyP/familyP => eq_f i;
  by move/(_ i): eq_f; rewrite filter_enum.
have: uniq r by apply: uniq_filter; exact: uniq_enum.
elim: {P}r => /= [_|i r IHr].
  rewrite (big_set1 (fgraph_of_fun (fun _ => j0))) ?big_seq0 //= => f.
  apply/familyP/eqP=> [Df|<-{f} i]; last by rewrite g2f set11.
  by apply/fgraphP=> i; rewrite g2f; exact/eqP.
case/andP=> nri; rewrite big_adds big_distrl; move/IHr {IHr} <-.
rewrite (partition_big (fun f : fIJ => f i) (Q i)); last first.
  by move=> f; move/familyP; move/(_ i); rewrite setU11.
pose seti j (f : fIJ) := fgraph_of_fun (fun k => if k == i then j else f k).
apply: eq_bigr => j Qij; rewrite (reindex_onto (seti j) (seti j0)); last first.
  move=> f /=; case/andP; move/familyP=> eq_f; move/eqP=> fi.
  by apply/fgraphP => k; rewrite !g2f; case: eqP => // ->.
rewrite big_distrr; apply: eq_big => [f | f eq_f]; last first.
  rewrite big_adds g2f set11; congr (_ * _); apply: congr_big => // k.
  by rewrite g2f /setI andbT; case: eqP => // ->; case/idPn.
rewrite !g2f !set11 andbT; apply/andP/familyP=> [[Pjf fij0] k | Pff].
  have:= familyP _ _ Pjf k; rewrite /setU1 g2f eq_sym; case: eqP => // -> _.
  by rewrite (negbET nri) -(eqP fij0) !g2f !set11.
split.
  apply/familyP=> k; move/(_ k): Pff; rewrite /setU1 g2f eq_sym.
  by case: eqP => // ->.
apply/eqP; apply/fgraphP=> k; have:= Pff k; rewrite !g2f.
by case: eqP => // ->; rewrite (negbET nri); exact: eqP.
Qed.

Lemma big_distr_big :
  forall (I J : finType) j0 (P : set I) (Q : set J) F,
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q j) F i j =
     \big[+%M/0]_(f | pfunspace j0 P Q f) \big[*%M/1]_(i | P i) F i (f i).
Proof.
move=> I J j0 P Q F; rewrite (big_distr_big_dep j0); apply: eq_bigl => f.
by apply/familyP/familyP=> Pf i; move/(_ i): Pf; case: (P i).
Qed.

Lemma bigA_distr_big_dep :
  forall (I J : finType) (Q : I -> set J) F,
  \big[*%M/1]_(i) \big[+%M/0]_(j | Q i j) F i j
    = \big[+%M/0]_(f | family Q f) \big[*%M/1]_(i) F i (f i).
Proof.
move=> I J Q F; case: (pickP (setA J)) => [j0 _ | J0].
   exact: (big_distr_big_dep j0).
rewrite /index_enum; case: (enum I) (@mem_enum I) => [I0 | i r _].
  have f0: I -> J by move=> i; have:= I0 i.
  rewrite (big_set1 (fgraph_of_fun f0)) ?big_seq0 // => g.
  by apply/familyP/eqP=> _; first apply/fgraphP; move=> i; have:= I0 i.
have Q0: Q _ =1 set0 by move=> ? j; have:= J0 j. 
rewrite big_adds big_set0 // mul0m big_set0 // => f.
by apply/familyP; move/(_ i); rewrite Q0.
Qed.

Lemma bigA_distr_big :
  forall (I J : finType) (Q : set J) F,
  \big[*%M/1]_(i : I) \big[+%M/0]_(j | Q j) F i j
    = \big[+%M/0]_(f | tfunspace Q f) \big[*%M/1]_(i) F i (f i).
Proof. move=> *; exact: bigA_distr_big_dep. Qed.

Lemma bigA_distr_bigA :
  forall (I J : finType) F,
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : fgraphType I J) \big[*%M/1]_(i) F i (f i).
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

Import ssralg.Ring.

Section Opp.

Variable R : additive_group.

Lemma sum_opp : forall I (r : seq I) P (F : I -> R),
  \sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i).
Proof.
move=> *; symmetry; apply: big_morph.
by split=> [|x y]; rewrite (oppr0, oppr_add).
Qed.

Lemma sum_split_sub : forall I (r : seq I) P (F1 F2 : I -> R),
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. by move=> *; rewrite -sum_opp -big_split /=. Qed.

Lemma sumr_const : forall (I : finType) P (x : R),
  \sum_(i : I | P i) x = x *+(card P).
Proof. exact: big_const. Qed.

End Opp.

Lemma prodr_const : forall (R : basic) (I : finType) P (x : R),
  \prod_(i : I | P i) x = x ^+(card P).
Proof. move=> *; exact: big_const. Qed.

End Ring.

Lemma sum_nat_const : forall (I : finType) P (n : nat),
  \sum_(i : I | P i) n = card P * n.
Proof. exact: big_const. Qed.

Lemma prod_nat_const : forall (I : finType) P (n : nat),
  \prod_(i : I | P i) n = n ^ card P.
Proof. by move=> *; rewrite big_const; elim: (card _) => //= ? ->. Qed.

Lemma sum_nat_const_nat : forall n1 n2 n : nat,
  \sum_(n1 <= i < n2) n = (n2 - n1) * n.
Proof. exact: big_const_nat. Qed.

Lemma prod_nat_const_nat : forall n1 n2 n : nat,
  \prod_(n1 <= i < n2) n = n ^ (n2 - n1).
Proof. by move=> *; rewrite big_const_nat; elim: (_ - _) => //= ? ->. Qed.

Notation "'\max_' ( i | P ) F" := (\big[maxn/0%N]_(i | P) F) 
  (at level 41, F at level 41, i, r at level 50,
   format "'\max_' ( i  |  P )  F") : dnat_scope.
Notation "'\max_' ( i ) F" := (\big[maxn/0%N]_(i) F) 
  (at level 41, F at level 41, i at level 50,
   format "'\max_' ( i )  F") : dnat_scope.

Lemma leq_bigmax_cond : forall (I : finType) (P : set I) F i0,
  P i0 -> F i0 <= \max_(i | P i) F i.
Proof.
by move=> I P F i0 Pi0; rewrite -maxn_leq (bigD1 i0) // maxnA /= maxnn set11.
Qed.

Lemma leq_bigmax : forall (I : finType) F (i0 : I), F i0 <= \max_(i) F i.
Proof. by move=> *; exact: leq_bigmax_cond. Qed.

Implicit Arguments leq_bigmax_cond [I P F].
Implicit Arguments leq_bigmax [I F].

Lemma eq_bigmax_cond : forall (I : finType) (P : set I) F,
  (~~ set0b P) -> exists i0, P i0 && (F i0 == \max_(i | P i) F i).
Proof.
move=> I P F.
case: {2}(card P) (eqP (eq_refl (card P)))=>/= [|n] cardP.
  by move/card0_eq: cardP; move/set0P=>->.
elim: n P cardP =>/= [|n Hn] P cardP; move/set0Pn=>[] i0 Pi0.
  rewrite -(card1 i0) in cardP; symmetry in cardP.
  exists i0; rewrite Pi0 andTb; apply/eqP.
  suffices: (set1 i0) =1 P; first (by move/fsym=>H1; rewrite (big_set1 _ H1)).
  by apply/(subset_cardP cardP); apply/subsetP=> j0; move/eqP=><-.
move: (cardD1 i0 P); move/eqP; rewrite cardP Pi0/= addnC addnS addn0 eqSS
 eq_sym; move/eqP=> H1.
have H2 : ~~ set0b (setD1 P i0) by apply/eqP=> H2; rewrite H2 in H1.
elim: (Hn _ H1 H2)=> j0; move/andP=> [] Pj0 Sj0.
rewrite (bigD1 i0 Pi0)/= (eq_bigl (setD1 P i0) F) -?(eqP Sj0);
 last (by move=> i; rewrite /setD1 andbC eq_sym).
case Lt_i0_j0:(F j0 <= F i0); [exists i0 | exists j0]; apply/andP; split=>//.
    by move/idP: Lt_i0_j0; rewrite leqNgt; move/negbET; rewrite /maxn=>->.
  by move: Pj0; rewrite /setD1; move/andP=>[].
by move: Lt_i0_j0; rewrite leqNgt; move/negbEF; rewrite /maxn=>->.
Qed.

Lemma eq_bigmax : forall (I : finType) F,
  (~~ set0b (setA I)) -> exists i0 : I, (F i0 == \max_(i) F i).
Proof.
by move=> I F; move/(eq_bigmax_cond F)=>[] x; move/andP=>[] _; exists x.
Qed.

Implicit Arguments eq_bigmax_cond [I P F].
Implicit Arguments eq_bigmax [I F].

Unset Implicit Arguments.
