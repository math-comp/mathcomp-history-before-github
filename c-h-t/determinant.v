Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple.
Require Import div groups group_perm zp signperm indexed_products ring.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope local_scope with loc.
Open Scope local_scope.
Open Scope ring_scope.

Section determinant_context.

(* Ring theory; should be replaced by a common structure like RingTheory. *)


Variable R : com_ring.
Notation "'\sum_' ( 'in' r ) F" := (@iprod R _ r F)
   (at level 40, F at level 40,
   format "'\sum_' ( 'in'  r )  F") : local_scope.
Notation "'\prod_' ( 'in' r ) F" := (@iprod (r2m R) _ r F)
   (at level 35, F at level 35,
   format "'\prod_' ( 'in'  r )  F") : local_scope.

Notation "'\sum_' () F" := (@iprod R _ (setA _) F)
   (at level 40, F at level 40, format "'\sum_' ()  F") : local_scope.
Notation "'\prod_' () F" := (@iprod (r2m R) _ (setA _) F)
   (at level 35, F at level 35, format "'\prod_' () F") : local_scope.

Notation "'\sum_' ( i 'in' r ) E" := (@iprod R _ r (fun i => E))
   (at level 40, E at level 40, i at level 50,
    format "'\sum_' ( i  'in'  r )  E") : local_scope.
Notation "'\prod_' ( i 'in' r ) E" := (@iprod (r2m R) _ r (fun i => E))
   (at level 35, E at level 35, i at level 50,
    format "'\prod_' ( i  'in'  r )  E") : local_scope.

Notation "'\sum_' ( i : t 'in' r ) E" := (@iprod R _ r (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t 'in' r ) E" := (@iprod (r2m R) _ r (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i | P ) E" := (@iprod R _ (fun i => P) (fun i => E))
   (at level 40, E at level 40, i at level 50, 
   format "'\sum_' ( i  |  P )  E") : local_scope.
Notation "'\prod_' ( i | P ) E" := (@iprod (r2m R) _ (fun i => P) (fun i => E))
   (at level 35, E at level 35, i at level 50,
   format "'\prod_' ( i  |  P )  E") : local_scope.

Notation "'\sum_' ( i : t | P ) E" :=
   (@iprod R _ (fun i : t => P) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t | P ) E" :=
   (@iprod (r2m R) _ (fun i : t => P) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i ) E" := (@iprod R _ (setA _) (fun i => E))
   (at level 40, E at level 40, i at level 50,
   format "'\sum_' ( i )  E") : local_scope.
Notation "'\prod_' ( i ) E" := (@iprod (r2m R) _ (setA _) (fun i => E))
   (at level 35, E at level 35, i at level 50 ,
   format "'\prod_' ( i )  E") : local_scope.

Notation "'\sum_' ( i : t ) E" := (@iprod R _ (setA _) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t ) E" := (@iprod (r2m R) _ (setA _) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i < n ) E" := (@iprod R _ (setA _) (fun i : I_(n) => E))
   (at level 40, E at level 40, i, n at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i < n ) E" := (@iprod (r2m R) _ (setA _) (fun i : I_(n) => E))
   (at level 35, E at level 35, i, n at level 50, only parsing) : local_scope.

(* Basic linear algebra (matrices). The matrix type is extensional, for   *)
(* now; it's packaged with a concrete type and reasonable factory syntax, *)
(* however, so if we do decide to go for rings with equality, we could    *)
(* have intensional matrices.                                             *)
(*   We use dependent types (ordinals) for the indices so that ranges are *)
(* mostly inferred automatically; we may have to reconsider this design   *)
(* if it proves too unwieldly for block decomposition theory.             *)

CoInductive matrix (m n : nat) : Type := Matrix :
  fgraphType { (I_(m) * I_(n))%type as finType } R -> (matrix m n).

Notation "'M_' ( m , n )" := (matrix m n)
  (at level 9, m, n at level 50, format "'M_' ( m ,  n )") : local_scope.
Notation "'M_' ( n )" := (matrix n n)
  (at level 9, m, n at level 50, format "'M_' ( n )") : local_scope.


Definition mval (m n: nat) (x : M_(m,n)) :=
  match x with Matrix g => g end.

Lemma can_mval : forall m n, cancel (@mval m n) (@Matrix m n).
Proof. move => m n; by rewrite /cancel; case => /=. Qed.

Lemma can_Matrix : forall m n, cancel (@Matrix m n) (@mval m n).
Proof. move => m n; by rewrite /cancel; case => /=. Qed.

Lemma mval_inj : forall m n, injective (@mval m n). 
Proof. move => m n; exact: can_inj (@can_mval m n). Qed.

Lemma Matrix_inj : forall m n, injective (@Matrix m n). 
Proof. move => m n; exact: can_inj (@can_Matrix m n). Qed.

Canonical Structure matrix_eqType (m n :nat) := EqType (can_eq (@can_mval m n)).

Definition fmval (m n: nat) (x : M_(m,n)) := fval (mval x).

Definition mproof : forall (m n : nat) (M : M_(m,n)),
  size (fmval M) = (card (setA (prod_finType I_(m) I_(n)))).
Proof. by move=> m n M;rewrite fproof. Qed.

Definition matrix_of_fun := locked (fun (m n :nat) (f : I_(m) -> I_(n) -> R) =>
  Matrix (fgraph_of_fun (fun x : (prod_finType I_(m) I_(n)) => (f (fst x) (snd x)) ))).

Definition fun_of_matrix := 
  locked
   (fun (m n :nat) (g :(matrix m n)) x1 x2 => let x12 := pair x1 x2 in 
     sub (@fgraph_default (prod_finType I_(m) I_(n)) R x12 (mval g))
        (fval (mval g)) (index x12 (enum (prod_finType I_(m) I_(n))))).

Coercion fun_of_matrix  : matrix >-> Funclass.

Notation "'\matrix_' ( i , j ) E" := (matrix_of_fun (fun i j => E))
  (at level 35, E at level 35, i, j at level 50,
   format "'\matrix_' ( i ,  j )  E") : local_scope.
Notation "'\matrix_' ( i < m , j < n ) E" := (@matrix_of_fun m n (fun i j => E))
  (at level 35, E at level 35, i, m, j, n at level 50,
   only parsing) : local_scope.
Notation "'\matrix_' ( i , j < n ) E" := (@matrix_of_fun _ n (fun i j => E))
  (at level 35, E at level 35, i, j, n at level 50,
   only parsing) : local_scope.
Notation "'\matrix_' ( i < m , j ) E" := (@matrix_of_fun m _ (fun i j => E))
  (at level 35, E at level 35, i, m, j at level 50,
   only parsing) : local_scope.

Definition matrix_plus m n (A B : M_(m, n)) := 
  \matrix_(i, j) (A i j + B i j).

Definition matrix_scale m n x (A : M_(m, n)) := \matrix_(i, j) (x * A i j).

Definition matrix_mul m n p (A : M_(m, n)) (B : M_(n, p)) :=
  \matrix_(i, k) \sum_(j) (A i j * B j k).

Definition matrix_transpose m n (A : M_(m, n)) := \matrix_(i, j) A j i.

Definition null_matrix m n := \matrix_(i < m, j < n) 0.

Definition perm_matrix n (s : S_(n)) :=
  \matrix_(i < n, j < n) (if s i == j then 1 else 0).

Definition unit_matrix n := \matrix_(i < n, j < n) (if i == j then 1 else 0).

CoInductive matrix_eq m n (A B : M_(m, n)) : Prop := EqMatrix of A =2 B.

Definition matrix_row m n i0 (A : M_(m, n)) := \matrix_(i < 1, j) A i0 j.

Definition matrix_col m n j0 (A : M_(m, n)) := \matrix_(i, j < 1) A i j0.

Definition matrix_rem_row m n i0 (A : M_(m, n)) :=
  \matrix_(i, j) A (lift i0 i) j.

Definition matrix_rem_col m n j0 (A : M_(m, n)) :=
  \matrix_(i, j) A i (lift j0 j).

(* The shape of the (dependent) height parameter determines where *)
(* the cut is made! *)

Definition matrix_lcut m1 m2 n (A : M_(m1 + m2, n)) :=
  \matrix_(i, j) A (lshift m2 i) j.

Definition matrix_rcut m1 m2 n (A : M_(m1 + m2, n)) :=
  \matrix_(i, j) A (rshift m1 i) j.

Definition matrix_paste m1 m2 n (A1 : M_(m1, n)) (A2 : M_(m2, n)) :=
   \matrix_(i, j) match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

(* Operator syntax, basic style, for local use only. *)
(* Generic syntax would really help here...          *)

Notation "'\0m_' ( m , n )" := (null_matrix m n)
  (at level 0, format "'\0m_' ( m ,  n )") : local_scope.
Notation "'\0m_' ( n )" := (null_matrix n n)
  (at level 0, format "'\0m_' ( n )") : local_scope.
Notation "'\0m'" := (null_matrix _ _)
  (at level 0, format "'\0m'") : local_scope.
Notation "'\1m_' ( n )" := (unit_matrix n)
  (at level 0, format "'\1m_' ( n )") : local_scope.
Notation "'\1m'" := (unit_matrix _)
  (at level 0, format "'\1m'") : local_scope.
Notation "A '+m' B" := (matrix_plus A B) (at level 50) : local_scope.
Notation "A '+m' B" := (matrix_plus A B) (at level 50) : local_scope.
Notation "x '*sm' A" := (matrix_scale x A) (at level 40) : local_scope.
Notation "A '*m' B" := (matrix_mul A B) (at level 40) : local_scope.
Notation "'\^t' A" := (matrix_transpose A) (at level 10) : local_scope.
Notation "A '=m' B" := (matrix_eq A B) (at level 70) : local_scope.

Notation Local row := matrix_row.
Notation Local row' := matrix_rem_row.
Notation Local col := matrix_col.
Notation Local col' := matrix_rem_col.
Notation Local lcut := matrix_lcut.
Notation Local rcut := matrix_rcut.
Notation Local paste := matrix_paste.

Lemma can_fun_of_matrix : forall (m n :nat),
  cancel (@fun_of_matrix m n) (@matrix_of_fun m n).
Proof.
unlock fun_of_matrix; unlock fun_of_fgraph => m n g.
case: {-1}g => gg; unlock matrix_of_fun;
  unlock fgraph_of_fun; apply mval_inj => //=.
case: gg => [s Hs]; unlock matrix_of_fun;
  unlock fgraph_of_fun; apply fval_inj => //=.
case De: (enum (prod_finType I_(m) I_(n))) => [|x0 e] //=;
  rewrite //= in De; rewrite cardA //= De in Hs.
rewrite De; case: s Hs => //=.
have y0 := fgraph_default x0 (mval g).
apply: (@eq_from_sub _ y0); rewrite size_maps De // => i Hi; unlock.
rewrite (sub_maps x0) //; last rewrite -De //.
rewrite -Hs in Hi.
set x:= (sub x0 (prod_enum I_(m) I_(n)) i).
have H: (@pair I_(m) I_(n) (fst x) (snd x)) = x by case: x => //=.
rewrite H; clear H.
rewrite index_uniq; [apply: set_sub_default => //=|rewrite De -Hs //=|
apply: (@uniq_enum (prod_finType I_(m) I_(n)))].
Qed.

Lemma m2f : 
  forall (m n :nat) (f:I_(m) -> I_(n) -> R), matrix_of_fun f =2 f.
Proof.
unlock matrix_of_fun fun_of_matrix => m n f x y /=.
unlock fgraph_of_fun fun_of_fgraph => /=.
rewrite (sub_maps (pair x y)) ?sub_index // ?index_mem
  (@mem_enum (prod_finType I_(m) I_(n))) //.
Qed.

Lemma matrix_eqP : forall m n (A B : M_(m,n)), A =m B <-> A = B.
Proof.
move=> m n A B; split; last by move=>->. 
move=> EAB; rewrite -(can_fun_of_matrix A) -(can_fun_of_matrix B).
apply: mval_inj; apply: fval_inj; unlock matrix_of_fun;
  unlock fgraph_of_fun => /=; apply: eq_maps.
by rewrite / eqfun => x; case: EAB => ->.
Qed.

Lemma matrix_fun: forall m n (i :I_(m)) (j :I_(n)) (f : I_(m) -> I_(n) -> R),
  (\matrix_(i0,j0) f i0 j0) i j = f i j.
Proof.
move => m n i j f.
unlock matrix_of_fun => //.
unlock matrix_of_fun fun_of_matrix => //=.
unlock fgraph_of_fun fun_of_fgraph => //=.
rewrite (sub_maps (pair i j)) ?sub_index // ?index_mem
  (@mem_enum (prod_finType I_(m) I_(n))) //.
Qed.

Ltac mx2fun i j := (apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f).

Lemma perm_matrix1 : forall n, perm_matrix 1%G = \1m_(n).
Proof. by move => n; mx2fun i j; rewrite perm1. Qed.

Lemma matrix_transposeK : forall m n (A : M_(m, n)), \^t (\^t A) = A.
Proof. by move =>  m n A; mx2fun i j. Qed.

Lemma matrix_transpose_inj : forall m n (A B : M_(m, n)),
  \^t A = \^t B -> A = B.
Proof.
by move=> m n A B tAB; rewrite -(matrix_transposeK A) tAB matrix_transposeK.
Qed.

Lemma matrix_transpose_perm : forall n (s : S_(n)),
  \^t (perm_matrix s) = perm_matrix s^-1.
Proof. 
move=> n s; mx2fun i j.
by rewrite eq_sym -{1}(permKv s i) (inj_eq (@perm_inj _ s)).
Qed.

Lemma matrix_transpose_unit : forall n, \^t \1m_(n) = \1m.
Proof. by move => n; mx2fun i j; rewrite eq_sym. Qed.

Lemma matrix_transpose_plus : forall m n (A B : M_(m, n)),
  \^t (A +m B) = \^t A +m \^t B.
Proof. by move=> m n A B; mx2fun i j. Qed.

Lemma matrix_transpose_scale : forall m n x (A : M_(m, n)),
  \^t (x *sm A) = x *sm \^t A.
Proof. by move=> m n x A; mx2fun i j. Qed.

Lemma matrix_transpose_row : forall m n i0 (A : M_(m, n)),
  \^t (row i0 A) = col i0 (\^t A).
Proof. by move=> m n i0 A; mx2fun i j. Qed.

Lemma matrix_transpose_rem_row : forall m n i0 (A : M_(m, n)),
  \^t (row' i0 A) = col' i0 (\^t A).
Proof. by move=> m n i0 A; mx2fun i j. Qed.

Lemma matrix_transpose_col : forall m n j0 (A : M_(m, n)),
  \^t (col j0 A) = row j0 (\^t A).
Proof. by move=> m n j0 A; mx2fun i j. Qed.

Lemma matrix_transpose_rem_col : forall m n j0 (A : M_(m, n)),
  \^t (col' j0 A) = row' j0 (\^t A).
Proof. by move=> m n j0 A; mx2fun i j. Qed.

Lemma matrix_eq_row : forall m n i0 (A : M_(m, n)) B,
  row i0 A = B -> A i0 =1 B ord0.
Proof. move=> m n i0 A B [AB] j; by rewrite -AB !m2f. Qed.

Ltac mx2fun_elim H := (move/matrix_eqP: H => H; case: H => H).

Lemma matrix_eq_rem_row : forall m n i i0 (A B : M_(m, n)),
  i0 != i -> row' i0 A = row' i0 B -> A i =1 B i.
Proof.
move=> m n i i0 A B; case/unlift_some=> i' -> _  [AB] j.
mx2fun_elim AB.
by move: (AB i' j); rewrite !m2f.
Qed.

Lemma matrix_paste_cut : forall m1 m2 n (A : matrix (m1 + m2) n),
  matrix_paste (matrix_lcut A) (matrix_rcut A) = A.
Proof.
move => m1 m2 n A; mx2fun i j.
case: splitP => k Dk //=; rewrite !m2f //=; congr fun_of_matrix; exact: ordinal_inj.
Qed.

(* Determinants, in one line ! *)

Definition determinant n (A : M_(n)) :=
  \sum_(s : S_(n)) (-1) ^ s * \prod_(i) A i (s i).

Notation "'\det' A" := (determinant A)
  (at level 10, A at level 9) : local_scope.

(* The trace, just for fun ... *)

Definition matrix_trace (n : nat) (A : M_(n)) := \sum_(i) (A i i).

Notation "'\tr' A" := (matrix_trace A)
  (at level 10, A at level 9) : local_scope.

Section AlgebraProps.

(* The matrix graded algebra, extensional. *)

Lemma matrix_plus0x : forall m n (A : M_(m, n)), \0m +m A = A.
Proof. by move => *; mx2fun i j; rewrite plus_r0l. Qed.

Lemma matrix_plusC : forall m n (A B : M_(m, n)), A +m B = B +m A.
Proof. by move => *; mx2fun i j; rewrite plus_rC. Qed.

Lemma matrix_plusA : forall m n (A B C : M_(m, n)),
  A +m (B +m C) = A +m B +m C.
Proof. by move => *; mx2fun i j; rewrite plus_rA. Qed.

Lemma matrix_scale_0 : forall m n (A : M_(m, n)), 0 *sm A = \0m.
Proof. by move => *; mx2fun i j; rewrite mult_r0l. Qed.

Lemma matrix_scale_0m : forall (m n :nat) (c:R), c *sm \0m_(m,n) = \0m.
Proof. by move => *; mx2fun i j; rewrite mult_r0r. Qed.

Lemma matrix_scale_1 : forall m n (A : M_(m, n)), 1 *sm A = A.
Proof. by move => *; mx2fun i j; rewrite mult_r1l. Qed.

Lemma matrix_scale_distrR : forall m n x1 x2 (A : M_(m, n)),
  (x1 + x2) *sm A = x1 *sm A +m x2 *sm A.
Proof. by move => *; mx2fun i j; rewrite plus_mult_r. Qed.

Lemma matrix_scale_distrL : forall m n x (A B : M_(m, n)),
  x *sm (A +m B) = x *sm A +m x *sm B.
Proof. by move=> m n x A B; mx2fun i j; rewrite !(mult_rC x) plus_mult_r. Qed.

Lemma matrix_scaleA : forall m n p x (A : M_(m, n)) (B : M_(n, p)),
  x *sm (A *m B) = (x *sm A) *m B.
Proof.
by move => *; mx2fun i j; rewrite /= isum_distrL;
  apply: eq_isumR => jj _; rewrite mult_rA m2f.
Qed.

Lemma matrix_scaleC : forall m n p x (A : M_(m, n)) (B : M_(n, p)),
  A *m (x *sm B) = (x *sm A) *m B.
Proof.
by move => *; mx2fun i j; apply: eq_isumR => jj _;
  rewrite m2f mult_rCA m2f mult_rA.
Qed.

Lemma matrix_scale_oppr :
  forall m n (A : M_(m, n)), A +m (- 1 *sm A) = \0m_(m,n).
Proof.
move => m n A; mx2fun i j.
by rewrite -{1}(mult_r1l (A i j)) -plus_mult_r plus_opp_rr mult_r0l.
Qed.

Lemma matrix_scale_oppl : 
  forall m n (A : M_(m, n)), (- 1 *sm A) +m A = \0m_(m,n).
Proof.
move => m n A; mx2fun i j.
by rewrite -{2}(mult_r1l (A i j)) -plus_mult_r plus_rC plus_opp_rr mult_r0l.
Qed.

Lemma matrix_mult1x : forall m n (A : M_(m, n)), \1m *m A = A.
Proof.
move=> m n A; mx2fun i j.
rewrite (@isumD1 _ _ i) // m2f set11 mult_r1l plus_rC.
rewrite isum0 ?plus_r0l // => i'; rewrite andbT m2f; move/negbET->.
exact: mult_r0l.
Qed.

Lemma matrix_mult0lx : forall n (A : M_(n)), \0m_(n) *m A = \0m.
Proof.
move => n A; mx2fun i j; rewrite isum0 ?mult_r0l // => x _.
by rewrite m2f mult_r0l.
Qed.

Lemma matrix_mult0rx : forall n (A : M_(n)), A *m \0m_(n) = \0m.
Proof.
move => n A; mx2fun i j; rewrite isum0 ?mult_r0l // => x _.
by rewrite m2f mult_rC mult_r0l.
Qed.

Lemma matrix_transpose_mul : forall m n p (A : M_(m, n)) (B : M_(n, p)),
   \^t (A *m B) = \^t B *m \^t A.
Proof.
by move=> *; mx2fun k i; apply: eq_isumR => j _; rewrite !m2f mult_rC.
Qed.

Lemma matrix_multx1 : forall m n (A : M_(m, n)), A *m \1m = A.
Proof.
move=> m n A; apply: matrix_transpose_inj.
by rewrite matrix_transpose_mul matrix_transpose_unit matrix_mult1x.
Qed.

Lemma matrix_distrR : forall m n p (A1 A2 : M_(m, n)) (B : M_(n, p)),
  (A1 +m A2) *m B = A1 *m B +m A2 *m B.
Proof.
move=> m n p A1 A2 B; mx2fun i k; rewrite /= -isum_plus.
by apply: eq_isumR => j _; rewrite m2f -plus_mult_r.
Qed.

Lemma matrix_distrL : forall m n p (A : M_(m, n)) (B1 B2 : M_(n, p)),
  A *m (B1 +m B2) = A *m B1 +m A *m B2.
Proof.
move=> m n p A B1 B2; apply: matrix_transpose_inj.
rewrite matrix_transpose_plus !matrix_transpose_mul.
by rewrite -matrix_distrR -matrix_transpose_plus.
Qed.

Lemma matrix_multA : forall m n p q
   (A : M_(m, n)) (B : M_(n, p)) (C : M_(p, q)),
  A *m (B *m C) = A *m B *m C.
Proof.
move=> m n p q A B C; mx2fun i l; rewrite /=.
transitivity (\sum_(k) (\sum_(j) (A i j * B j k * C k l))).
  rewrite exchange_isum; apply: eq_isumR => j _; rewrite m2f isum_distrL.
  by apply: eq_isumR => k _; rewrite mult_rA.
by apply: eq_isumR => j _; rewrite m2f isum_distrR.
Qed.

Section MatrixRing.
Variable n :nat.
Hypothesis (Hn: 0 < n).

Definition matrix_ring : ring.
exists (matrix_eqType n n) \0m_(n) \1m_(n)
  (@matrix_scale n n (-1)) (@matrix_plus n n) (@matrix_mul n n n).
split=>//=; [ | | apply: matrix_distrL | apply: matrix_distrR | ].
 - split=>//=; last (apply: matrix_plusC).
   split=>//=; last (apply: matrix_scale_oppl).
   split=>//=; [apply: matrix_plusA | apply: matrix_plus0x| ].
   by move=> *; rewrite matrix_plusC matrix_plus0x.
 - split=>//=; [apply: matrix_multA | apply: matrix_mult1x|
     apply: matrix_multx1].
move=> H.
mx2fun_elim H; move: (H (Ordinal Hn) (Ordinal Hn)) => //=.
by rewrite !m2f //= => H1; move: (@one_diff_0 R) => H2.
Defined.

Canonical Structure matrix_ring.

End MatrixRing.

Lemma perm_matrixM : forall n (s t : S_(n)),
  perm_matrix (s * t)%G = perm_matrix s *m perm_matrix t.
Proof.
move=> n s t; mx2fun i j.
rewrite /= (@isumD1 _ _ (s i)) // m2f set11 mult_r1l m2f -permM isum0 =>
  [|j']; first by rewrite plus_rC plus_r0l.
by rewrite andbT m2f; move/negbET->; rewrite mult_r0l.
Qed.

Lemma matrix_trace_plus : forall n (A B : M_(n)), \tr (A +m B) = \tr A + \tr B.
Proof.
by move=> n A B; rewrite -isum_plus; apply: eq_iprod_f_ => i _; rewrite m2f.
Qed.

Lemma matrix_trace_scale : forall n x (A : M_(n)), \tr (x *sm A) = x * \tr A.
Proof.
by move=> *; rewrite isum_distrL; apply: eq_iprod_f_ => i _; rewrite m2f.
Qed.

Lemma matrix_trace_transpose : forall n (A : M_(n)), \tr (\^t A) = \tr A.
Proof. by move => *;  apply: eq_iprod_f_ => i _; rewrite m2f. Qed.

(*
Lemma iprod_fun_of_matrix: forall m (f: I_(m) ->I_(m) -> R) S,
  @iprod R _ S (fun i: I_(m) => (@fun_of_matrix m m (@matrix_of_fun m m f)) i i) =
  @iprod R _ S (fun i => f i i).
Proof.
by move => m f S; apply: eq_iprod_f_ => x Hx; apply: m2f.
Qed.
*)

Lemma matrix_trace_multC : forall m n (A : M_(m, n)) (B : M_(n, m)),
  \tr (A *m B) = \tr (B *m A).
Proof.
move=> m n A B.
rewrite /(\tr _) /matrix_mul //=
  (eq_iprod_f_ (g:=(fun i => ( \sum_() (fun j => A i j * B j i)))));
    last (move=> i Hi; apply: m2f).
rewrite exchange_isum.
apply: eq_isumR => i _ //; rewrite m2f.
apply: eq_isumR => j _ //; exact: mult_rC.
Qed.


(* And now, finally, the title feature. *)

Lemma determinant_multilinear : forall n (A B C : M_(n)) i0 b c,
    row i0 A =m b *sm row i0 B +m c *sm row i0 C ->
    row' i0 B =m row' i0 A -> row' i0 C =m row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c ABC.
move/matrix_eqP=> BA; move/matrix_eqP=> CA.
move/matrix_eq_rem_row: BA=> BA; move/matrix_eq_rem_row: CA=> CA.
rewrite !isum_distrL -isum_plus; apply: eq_isumR => s _.
rewrite -!(mult_rCA (_ ^ (odd_perm s))) -plus_mult_l; congr (_ * _).
rewrite !(@iprodD1 _ _ i0 (setA _)) //.
move/matrix_eqP: ABC => ABC.
rewrite (matrix_eq_row ABC) !m2f plus_mult_r !mult_rA.
by congr (_ * _ + _ * _); apply: eq_iprodR => i; rewrite andbT => ?;
   rewrite ?BA ?CA.
Qed.

Lemma alternate_determinant : forall n (A : M_(n)) i1 i2,
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
move=> n A i1 i2 Di12 A12; pose r := I_(n).
pose t := transp i1 i2; pose tr s := (t * s)%G.
have trK : involutive tr by move=> s; rewrite /tr mulgA transp2 mul1g.
have Etr: forall s, odd_perm (tr s) = even_perm s.
  by move=> s; rewrite odd_permM odd_transp Di12.
rewrite /(\det _) (isumID (@even_perm r)) /=.
set S1 := \sum_(in _) _; set T := S1 + _.
rewrite -(plus_opp_rl S1) plus_rC; congr (_ + _); rewrite {}/T {}/S1  -isum_opp.
rewrite (reindex_isum (h:= tr)); last by exists tr.
symmetry; apply: eq_isum => [s | s seven]; first by rewrite negbK Etr.
rewrite mult_opp_rl Etr seven (negbET seven); congr (_ * _).
rewrite (reindex_iprod (h := t));
  last by exists (t : _ -> _) => i _; exact: transpK.
apply: eq_iprodR => i _; rewrite permM /t.
by case: transpP => // ->; rewrite A12.
Qed.

Lemma determinant_transpose : forall n (A : M_(n)), \det (\^t A) = \det A.
Proof.
move=> n A; pose r := I_(n); pose ip p : permType r := p^-1.
rewrite /(\det _) (reindex_isum (h:=ip)) /=; last first.
  by exists ip => s _; rewrite /ip invgK.
apply: eq_isumR => s _.
rewrite !odd_permV /= (reindex_iprod (h:=(fun_of_perm s))).
  by congr (_ * _); apply: eq_iprodR => i _; rewrite m2f permK.
by exists ((fun_of_perm s^-1) : _ -> _) => i _; rewrite ?permK ?permKv.
Qed.

Lemma determinant_perm : forall n s, \det (@perm_matrix n s) = (-1) ^ s.
Proof.
move=> n s; rewrite /(\det _) (isumD1 (i0:=s)) //.
rewrite iprod1 => [|i _]; last by rewrite /= !m2f set11.
rewrite isum0 => [|t Dst]; first by rewrite plus_rC plus_r0l mult_rC mult_r1l.
case: (pickP (fun i => s i != (fun_of_perm t) i)) => [i ist | Est].
  by rewrite (iprodD1 (i0:=i)) // mult_rCA /= m2f (negbET ist) mult_r0l.
move: Dst; rewrite andbT; case/eqP.
by apply: eq_fun_of_perm => i; move/eqP: (Est i).
Qed.

Lemma determinant1 : forall n, \det (unit_matrix n) = 1.
Proof.
move=> n; have:= @determinant_perm n 1%G; rewrite odd_perm1 => /= <-.
congr determinant; symmetry; exact: perm_matrix1.
Qed.

Lemma determinant_scale : forall n x (A : M_(n)),
  \det (x *sm A) = x ^ n * \det A.
Proof.
move=> n x A; rewrite isum_distrL; apply: eq_isumR => s _.
rewrite mult_rCA; congr (_ * _).
move: (@iprod_id R I_(n) (setA I_(n)) x); rewrite card_ordinal => <-.
rewrite -iprod_mult //=.
apply: (@eq_iprod_f_ (cr2am R)) => x0 Hx0.
by rewrite m2f.
Qed.

Lemma determinantM : forall n (A B : M_(n)), \det (A *m B) = \det A * \det B.
Proof.
move=> n A B; rewrite isum_distrR.
pose AB (f : F_(n)) (s : S_(n)) i := A i (f i) * B (f i) (s i).
transitivity (\sum_(f) \sum_(s : S_(n)) (-1) ^ s * \prod_(i) AB f s i).
  rewrite exchange_isum; apply: eq_isumR; move=> /= s _.
  rewrite -isum_distrL; congr (_ * _).
  pose F i j := A i j * B j (s i).
  rewrite -(distr_iprodA_isumA F) //.
  by apply: (@eq_iprod_f_ (cr2am R)) => x _ //; rewrite m2f.
rewrite (isumID (fun f => uniq (fval f))) plus_rC isum0 ?plus_r0l => /= [|f Uf].
  rewrite (reindex_isum (h:=(fun s => val (pval s)))); last first.
    have s0 : S_(n) := 1%G; pose uf (f : F_(n)) := uniq (fval f).
    pose pf f := if insub uf f is Some s then Perm s else s0.
    exists pf => /= f Uf; rewrite /pf (@insubT _ uf _ Uf) //; exact: eq_fun_of_perm.
  apply: eq_isum => [s|s _]; rewrite ?(valP (pval s)) // isum_distrL.
  rewrite (reindex_isum (h:=(mulg s))); last first.
    by exists (mulg s^-1) => t; rewrite ?mulKgv ?mulKg.
  apply: eq_isumR => t _.
  rewrite iprod_mult mult_rA mult_rCA mult_rA mult_rCA mult_rA.
  rewrite -sign_permM; congr (_ * _).
  rewrite (reindex_iprod (h:=(fun_of_perm s^-1))); last first.
    by exists ((fun_of_perm s) : _ -> _) => i _; rewrite ?permK ?permKv.
  by apply: eq_iprodR => i _; rewrite permM permKv ?set11 // -{3}[i](permKv s).
transitivity 
  (\det (\matrix_(i, j) B ((fun_of_fgraph f) i) j)
   * \prod_(i) A i ((fun_of_fgraph f) i)).
  rewrite mult_rC isum_distrL; apply: eq_isumR=> s _.
  rewrite mult_rCA iprod_mult //=; congr (_ * _); congr (_ * _).
  by apply: (@eq_iprod_f_ (cr2am R))=> x Hx; rewrite m2f.
suffices [i1 [i2 Ef12 Di12]]:
  exists i1, exists2 i2, (fun_of_fgraph f) i1 = (fun_of_fgraph f) i2 & i1 != i2.
  by rewrite (alternate_determinant Di12) ?mult_r0l => //= j; rewrite !m2f Ef12.
pose ninj i1 i2 := ((fun_of_fgraph f) i1 == (fun_of_fgraph f) i2) && (i1 != i2).
case: (pickP (fun i1 => ~~ set0b (ninj i1))) => [i1| injf].
  by case/set0Pn=> i2; case/andP; move/eqP; exists i1; exists i2.
case/(perm_uniqP f): Uf => i1 i2; move/eqP=> Dfi12; apply/eqP.
by apply/idPn=> Di12; case/set0Pn: (injf i1); exists i2; apply/andP.
Qed.

(* And now, the Laplace formula. *)

Definition cofactor n (A : M_(n)) (i j : I_(n)) :=
   (-1) ^ (nat_of_ord i + nat_of_ord j) * \det (row' i (col' j A)).


Lemma expand_cofactor : forall n (A : M_(n)) i j,
  cofactor A i j =
    \sum_(s : S_(n) | s i == j) (-1) ^ s * \prod_(k | i != k) A k (s k).
Proof.
move=> n.
pose lsf i (s : S_(n.-1)) j k :=
  if unlift i k is Some k' then lift j (s k') else j.
have lsfE: forall i s j, (lsf i s j i = j)
                       * (forall k, lsf i s j (lift i k) = lift j (s k)).
- by split=> *; rewrite /lsf ?unlift_none ?liftK.
have inj_lsf : injective (lsf _ _ _).
  move=> i s j; apply: can_inj (lsf j s^-1 i) _ => k.
  by case: (unliftP i k) => [k'|] ->; rewrite !lsfE ?permK.
pose ls := perm_of_inj (inj_lsf _ _ _).
have ls1 : forall i, ls i 1%G i = 1%G.
  move=> i; apply: eq_fun_of_perm => k.
  by case: (unliftP i k) => [k'|] ->; rewrite p2f lsfE !perm1.
have lsM : forall i s j t k, (ls i s j * ls j t k)%G = ls i (s * t)%G k.
  move=> i s j t k; apply: eq_fun_of_perm=> l; rewrite permM !p2f.
  by case: (unliftP i l) => [l'|] ->; rewrite !lsfE ?permM.
have sign_ls:
  forall s i j, (-1)^(ls i s j) = (-1) ^ s * (-1)^(nat_of_ord i + nat_of_ord j) :>R.
  pose nfp (s : S_(n.-1)) k := s k != k.
  move=> s i j; elim: {s}_.+1 {-2}s (ltnSn (card (nfp s))) => // m IHm s Hm.
  case: (pickP (nfp s)) Hm => [k Dsk | s1 _ {m IHm}].
    rewrite ltnS (cardD1 k) Dsk => Hm; pose t := transp k (fun_of_perm s^-1 k).
    rewrite -(mulKg t s) transpV -(lsM _ _ i).
    rewrite 2!sign_permM -mult_rA -{}IHm; last first.
      apply: {m} leq_trans Hm; apply: subset_leq_card; apply/subsetP=> k'.
      rewrite /nfp /setD1 permM /t.
      case: transpP=> [->|-> Ds|]; rewrite ?permKv; first by rewrite set11.
        by rewrite andbb; apply/eqP=> Dk; case/eqP: Ds; rewrite {1}Dk permKv.
      by move/eqP; rewrite eq_sym => ->.
    suffices ->: ls i t i = transp (lift i k) (lift i (fun_of_perm s^-1 k)).
      by rewrite !odd_transp (inj_eq (@lift_inj _ _)).
    apply: eq_fun_of_perm=> i'; rewrite p2f.
    case: (unliftP i i') => [i''|] ->; rewrite lsfE.
      rewrite inj_transp //; exact: lift_inj.
    case transpP => //; move/eqP; case/idPn; exact: neq_lift.
  have ->: s = 1%G.
    by apply: eq_fun_of_perm=> k; rewrite perm1; move/eqP: (s1 k).
  rewrite odd_perm1 mult_r1l; without loss: i {s s1} j / nat_of_ord j <= nat_of_ord i.
    case: (leqP (nat_of_ord j) (nat_of_ord i)); first by auto.
    move/ltnW=> ij; move/(_ _ _ ij)=> Wji.
    rewrite -(mulgK (ls j 1%G i) (ls i  _ j)) lsM !(ls1,mul1g).
    by rewrite odd_permV addnC.
  move Dm: (nat_of_ord i).+1 => m; elim: m i Dm => // m IHm i [im].
  rewrite leq_eqVlt; case/setU1P=> [eqji|ltji].
    by rewrite (ordinal_inj eqji) ls1 odd_perm1 /= -sign_odd odd_addn addbb.
  have m'm: m.-1.+1 = m by rewrite -im (ltnSpred ltji).
  have ltm'n : m.-1 < n by rewrite m'm -im leq_eqVlt orbC (ordinal_ltn i).
  pose i' := Ordinal ltm'n; rewrite -{1}(mulg1 1%G) -(lsM _ _ i') sign_permM.
  rewrite mult_rC {}IHm; try by rewrite /= -1?ltnS ?m'm // -im.
  rewrite im -m'm addSn -addn1 (exp_addn _ _ 1); congr (_ * _).
  have{j ltji} ii' : i != i' by rewrite /set1 /= im /= -m'm eqn_leq ltnn.
  transitivity (((-1) ^ (transp i i')) : R); last by rewrite odd_transp ii'.
  congr (_ ^ odd_perm _); apply: eq_fun_of_perm=> k.
  case: (unliftP i k) => [k'|] -> {k}; rewrite p2f lsfE ?transpL // perm1.
  apply: ordinal_inj; rewrite p2f /transpose (negbET (neq_lift _ _)) /set1.
  rewrite fun_if /= im /bump; case mk': (m <= _).
    by rewrite eq_sym eqn_leq ltnNge leq_eqVlt m'm mk' orbT.
  by rewrite add0n leq_eqVlt m'm mk'; case: eqP => //= <-.
move=> A i0 j0; rewrite (reindex_isum (h:=(fun s => ls i0 s j0))); last first.
  pose ulsf i (s : S_(n)) k' :=
    if unlift (s i) (s (lift i k')) is Some k then k else k'.
  have ulsfE: forall i (s : S_(n)) k',
      lift (s i) (ulsf i s k') = s (lift i k').
    rewrite /ulsf => i s k'; have:= neq_lift i k'.
    by rewrite -(inj_eq (@perm_inj _ s)); case/unlift_some=> ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1) _ => k'.
    by rewrite {1}/ulsf ulsfE !permK liftK.
  exists (fun s => perm_of_inj (inj_ulsf s)) => [s _ | s]. 
    by apply: eq_fun_of_perm=> k'; rewrite p2f /ulsf !p2f !lsfE liftK.
  move/eqP=> si0; apply: eq_fun_of_perm=> k.
  by case: (unliftP i0 k) => [k'|] ->; rewrite p2f lsfE // p2f -si0 ulsfE. 
rewrite /cofactor isum_distrL.
apply: eq_isum => [s | s _]; first by rewrite p2f lsfE set11.
rewrite mult_rCA mult_rA -{}sign_ls; congr (_ * _).
case: (pickP (setA I_(n.-1))) => [k'0 _ | r'0]; last first.
  rewrite !iprod_set0 // => k; apply/idP; case/unlift_some=> k'.
  by have:= r'0 k'.
rewrite (reindex_iprod (h:=(lift i0))).
  by apply: eq_iprod => [k | k _ /=]; [rewrite neq_lift // | rewrite !m2f p2f lsfE ].
pose f k := if unlift i0 k is Some k' then k' else k'0.
by exists f; rewrite /f => k; [rewrite liftK | case/unlift_some=> ? ? ->].
Qed.

Lemma expand_determinant_row : forall n (A : M_(n)) i0,
  \det A = \sum_(j) A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
rewrite (@partition_isum _ _ _ (setA _) (fun s : S_(_) => s i0)) //.
apply: eq_isumR => j0 _; rewrite expand_cofactor isum_distrL.
apply: eq_isumR => s /=; move/eqP=> Dsi0.
by rewrite mult_rCA (iprodID (set1 i0)) /= iprod_set1_eq Dsi0.
Qed.

Lemma cofactor_transpose : forall n (A : M_(n)) i j,
  cofactor (\^t A) i j = cofactor A j i.
Proof.
move=> n A i j; rewrite /cofactor addnC; congr (_ * _).
rewrite -matrix_transpose_rem_row -matrix_transpose_rem_col determinant_transpose.
congr determinant.
rewrite / matrix_rem_col / matrix_rem_row //=.
by mx2fun x y.
Qed.

Lemma expand_determinant_col : forall n (A : M_(n)) j0,
  \det A = \sum_(i) (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -determinant_transpose (expand_determinant_row _ j0).
by apply: eq_isumR => i _; rewrite cofactor_transpose m2f.
Qed.

(* The final flurry: adjugates. *)

Definition adjugate n (A : M_(n)) := \matrix_(i, j) (cofactor A j i).

Lemma mult_adugateR : forall n (A : M_(n)), A *m adjugate A = \det A *sm \1m.
Proof.
move=> n A; mx2fun i1 i2; rewrite // mult_rC.
case Di: (i1 == i2).
  rewrite (eqP Di) mult_r1l (expand_determinant_row _ i2) //=.
  apply: (@eq_iprod_f_ R) => x Hx; congr (_ * _).
  by rewrite / adjugate m2f.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !m2f Di eq_refl.
set T:= (iprod _ _). (* BIZARRE *)
rewrite mult_r0l -(alternate_determinant (negbT Di) EBi12) {}/ T.
rewrite (expand_determinant_row _ i2).
apply: (@eq_iprod_f_ R) => x Hx.
rewrite !m2f eq_refl; congr (_ * _).
congr (_ * _); apply: (@eq_iprod_f_ R) => y Hy //; congr (_ * _).
apply: (@eq_iprod_f_ (cr2am R)) => z Hz.
by rewrite !m2f eq_sym -if_neg neq_lift.
Qed.

Lemma transpose_adjugate : forall n (A : M_(n)),
  \^t (adjugate A) = adjugate (\^t A).
Proof. move => n A; mx2fun i j; symmetry; exact: cofactor_transpose. Qed.

Lemma mult_adugateL : forall n (A : M_(n)), adjugate A *m A =  \det A *sm \1m.
Proof.
move=> n A; apply: matrix_transpose_inj.
rewrite matrix_transpose_mul transpose_adjugate mult_adugateR.
by rewrite  determinant_transpose matrix_transpose_scale matrix_transpose_unit.
Qed.

End AlgebraProps.

End determinant_context.

Unset Implicit Arguments.
