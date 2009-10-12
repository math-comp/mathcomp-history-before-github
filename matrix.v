(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import finfun bigops ssralg finset groups perm zmodp.

(*****************************************************************************)
(* Basic concrete linear algebra : definition of type for matrices, and all  *)
(* basic matrix operations, including determinant, trace, rank, support for  *)
(* for block decomposition, and row space computation (the latter provides a *)
(* computational basis for the construction of abstract vector spaces).      *)
(* While matrices are represented by a row-major list of their coefficients, *)
(* this is hidden by three levels of wrappers (Matrix/Finfun/Tuple) so the   *)
(* matrix type should be treated as abstract and handled using only the      *)
(* operations described below:                                               *)
(*   'M[R]_(m, n) == the type of m rows by n columns matrices with           *)
(*                   coefficients in R; the [R] is optional and usually      *)
(*                   omitted.                                                *)
(*   'M_n, 'rV_n, == n x n square matrices, 1 x n row vectors, and n x 1     *)
(*   'cV_n           column vectors, respectively.                           *)
(*  \matrix_(i < m, j < n) Expr(i, j) ==                                     *)
(*                   the m x n matrix with general coefficient Expr(i, j),   *)
(*                   with i : 'I_m and j : 'I_n. the < m bound can be        *)
(*                   omitted if it is equal to n, though usually both bounds *)
(*                   are omitted as they can be inferred from the context.   *)
(*  \row_(j < n) Expr(j), \col_(i < m) Expr(i)                               *)
(*                   the row / column vectors with general term Expr; the    *)
(*                   parentheses can be omitted along with the bound.        *)
(*          A i j == the coefficient of matrix A : 'M_(m, n) in column j of  *)
(*                   row i, where i : 'I_m, and j : 'I_n (via the coercion   *)
(*                   fun_of_matrix : matrix >-> Funclass).                   *)
(*            A^T == the matrix transpose of A                               *)
(*        row i A == the i'th row of A (this is a row vector)                *)
(*        col j A == the j'th column of A (a column vector)                  *)
(*       row' i A == A with the i'th row spliced out                         *)
(*       col' i A == A with the j'th column spliced out                      *)
(*   xrow i1 i2 A == A with rows i1 and i2 interchanged.                     *)
(*   xcol j1 j2 A == A with columns j1 and j2 interchanged.                  *)
(*   row_perm s A == A : 'M_(m, n) with rows permuted by s : 'S_m            *)
(*   col_perm s A == A : 'M_(m, n) with columns permuted by s : 'S_n         *)
(*   row_mx Al Ar == the row block matrix <Al Ar> obtained by contatenating  *)
(*                   two matrices Al and Ar of the same height.              *)
(*   col_mx Au Ad == the column block matrix / Au \ (Au and Ad must have the *)
(*                   same width).            \ Ad /                          *)
(* block_mx Aul Aur Adl Adr == the block matrix / Aul Aur \                  *)
(*                                              \ Adl Adr /                  *)
(*       lsubmx A == the left/right submatrices of a row block matrix A.     *)
(*                   Note that the type of A, 'M_(m, n1 + n2) indicatres     *)
(*                   how A should be decomposed.                             *)
(*   [u|d]submx A == the up/down submatrices of a column block matrix A.     *)
(* [u|d][l|r]submx A == the upper left, etc submatrices of a block matrix A. *)
(* castmx eq_mn A == A : 'M_(m, n) casted to 'M_(m', n') using the equation  *)
(*                   pair eq_mn : (m = m') * (n = n'). This is the usual     *)
(*                   workaround for the synactic limitations of dependent    *)
(*                   types in Coq, and can be used to introduce a block      *)
(*                   decomposition. It simplifies to A when eq_mn is the     *)
(*                   pair (erefl m, erefl n).                                *)
(* In 'M[R]_(m, n), R can be any type, but 'M[R]_(m, n) inherits the eqType, *)
(* choiceType, countType, finType, and zmodType structures of R; however,    *)
(* because the type of matrices specifies their dimension, only non-trivial  *)
(* square matrices ('M[R]_n when n is a pos_nat) can inherit the ring        *)
(* structure of R; they can further inherit the unit ring structure of R if  *)
(* R is commutative. We thus provide separate syntax for the general matrix  *)
(* multiplication, and other operations for matrices over a ringType R:      *)
(*         A *m B == the matrix product of A and B; the width of A must be   *)
(*                   equal to the height of B.                               *)
(*        a *m: A == the matrix A scaled by factor a. This will be subsumed  *)
(*                   by the *: operation of the vector space structure, but  *)
(*                   we need to define matrices first.                       *)
(*           a%:M == the scalar matrix with a's on the main diagonal; in     *)
(*                   particular 1%:M denotes the identity matrix, and is is  *)
(*                   equal to 1%R when n is a pos_nat (e.g., n = 1).         *)
(*      diag_mx d == the diagonal matrix whose main diagonal is d : 'rV_n.   *) 
(*   delta_mx i j == the matrix with a 1 in row i, column j and 0 elsewhere. *)
(*       pid_mx r == the partial identity matrix with 1s only on the r first *)
(*                   rows of the main diagonal; the dimensions of pid_mx r   *)
(*                   are determined by the context.                          *)
(*      perm_mx s == the n x n permutation matrix for s : 'S_n.              *)
(* tperm_mx i1 i2 == the permutation matrix that exchanges i1 i2 : 'I_n.     *)
(*   is_perm_mx A == A is a permutation matrix.                              *)
(*     lift0_mx A == the 1 + n square matrix block_mx 1 0 0 A when A : 'M_n. *)
(*          \tr A == the trace of a square matrix A.                         *)
(*         \det A == the determinant of A, using the Leibnitz formula.       *)
(* cofactor i j A == the i, j cofactor of A (the signed i, j minor of A),    *)
(*         \adj A == the adjugate matrix of A (\adj A i j = cofactor j i A). *)
(*       unitmx A == A is invertible (R must be a comUnitRingType).          *)
(*        invmx A == the inverse matrix of A if unitmx A, otherwise A.       *)
(* The definition of the triangular decomposition, rank and row space        *)
(* operations are limited to matrices over a fieldType F:                    *)
(*    cormenLUP A == the triangular decomposition (L, U, P) of a nontrivial  *)
(*                   square matrix A into a lower triagular matrix L with 1s *)
(*                   on the main diagonal, an upper matrix U, and a          *)
(*                   permutation matrix P, such that P * A = L * U.          *)
(*      erankmx A == the extended rank decomposition (r, L, U) of A, where r *)
(*                   is the rank of A, L is a column permutation of a lower  *)
(*                   triangular invertible matrix, U a row permutation of an *)
(*                   upper triangular invertible matrix, such that we have   *)
(*                   L *m A *m U = pid_mx r.                                 *)
(*        \rank A == the rank of A.                                          *)
(*       row_im A == a full row-rank matrix with the same row space as A:    *)
(*                   if A : 'M_(m, n) then row_im A : 'M_(\rank A, n).       *)
(*   row_im_inv A == a right inverse for row_im A.                           *)
(*       col_im A == A *m row_im_inv A, a full column rank matrix with the   *)
(*                   same column space as A (so col_im A *m row_im A = A).   *)
(*   col_im_inv A == a left inverse for col_im A.                            *)
(*   rank_invxm A == a left/right inverse for A on its column space / in its *)
(*                   row space, respectively.                                *)
(*        kermx A == the row kernel of A : a full row rank matrix whose row  *)
(*                   space consists of all u such that u *m A = 0.           *)
(*    kermx_inv A == a right inverse to kermx A.                             *)
(*      cokermx A == the column kernel of A : a matrix whose column space    *)
(*                   consists of all v such that A *m v = 0.                 *)
(* We use a different scope %MR for matrix row-space operations; to avoid    *)
(* confusion, this scope should not be opened globally.                      *)
(*    (A <= B)%MR == the row-space of A is a subspace of the row-space of B. *)
(*                   We test for this by testing if B anihilates cokermx A.  *)
(*   (A :+: B)%MR == a matrix whose row-space is the sum of the row-spaces   *)
(*                   of A and B (this is just col_mx A B).                   *)
(*   (A :&: B)%MR == a matrix whose row-space is the intersection of the     *)
(*                   row-spaces of A and B.                                  *)
(*   (A :\: B)%MR == a matrix whose row-space is a complement of the         *)
(*                   the row-space of (A :&: B)%MR in the row-space of A.    *)
(* Note that in this row-space theory, matrices represent vectors, subspaces *)
(* and also linear transformations.                                          *)
(*   In addition to the lemmas relevant to these definitions, this file also *)
(* proves several classic results, including :                               *)
(* - The determinant is a multilinear alternate form.                        *)
(* - The Laplace determinant expansion formulas: expand_det_[row|col].       *)
(* - The Cramer rule : mul_mx_adj & mul_adj_mx                               *)
(* - The Sylvester|Frobenius rank inequalities : mxrank_[mul_min|Frobenius]. *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.
Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "''M_' n"     (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 8, n at level 2, format "''rV_' n").
Reserved Notation "''cV_' n"    (at level 8, n at level 2, format "''cV_' n").
Reserved Notation "''M_' ( n )" (at level 8, only parsing).
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2, only parsing).
Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2, only parsing).
Reserved Notation "''cV[' R ]_ n"   (at level 8, n at level 2, only parsing).
Reserved Notation "''M[' R ]_ ( n )"     (at level 8, only parsing).
Reserved Notation "''M[' R ]_ ( m , n )" (at level 8, only parsing).

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50,
   format "\matrix_ ( i  <  m ,  j  <  n )  E").
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50,
   format "\matrix_ ( i ,  j  <  n )  E").
Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50,
   format "\row_ ( j  <  n )  E").
Reserved Notation "\col_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\col_ j  E").
Reserved Notation "\col_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50,
   format "\col_ ( j  <  n )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "x *m: A" (at level 40, format "x  *m:  A").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").
Reserved Notation "\rank A" (at level 10, A at level 8, format "\rank  A").

Delimit Scope matrix_row_scope with MR.

Notation Local simp := (Monoid.Theory.simpm, oppr0).

(*****************************************************************************)
(****************************Type Definition**********************************)
(*****************************************************************************)

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

(* Basic linear algebra (matrices).                                       *)
(* We use dependent types (ordinals) for the indices so that ranges are   *)
(* mostly inferred automatically                                          *)

CoInductive matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

Lemma mx_valK : cancel mx_val Matrix. Proof. by case. Qed.

Definition matrix_of_fun F := locked Matrix [ffun ij => F ij.1 ij.2].

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix  : matrix >-> Funclass.

Lemma mxE : forall F, matrix_of_fun F =2 F.
Proof. by unlock matrix_of_fun fun_of_matrix => F i j; rewrite /= ffunE. Qed.

Lemma matrixP : forall A B : matrix, A =2 B <-> A = B.
Proof.
unlock fun_of_matrix => [] [A] [B]; split=> [/= eqAB | -> //].
congr Matrix; apply/ffunP=> [] [i j]; exact: eqAB.
Qed.

End MatrixDef.

Bind Scope ring_scope with matrix.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n"  := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''cV[' R ]_ n"  := 'M[R]_(n, 1) (only parsing) : type_scope.
Notation "''M[' R ]_ n"  := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M[' R ]_ ( n )" := 'M[R]_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n"  := 'M_(1, n) : type_scope.
Notation "''cV_' n"  := 'M_(n, 1) : type_scope.
Notation "''M_' n"  := 'M_(n, n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\row_ j E" := (@matrix_of_fun _ 1 _ (fun _ j => E)) : ring_scope.
Notation "\row_ ( j < n ) E" :=
  (@matrix_of_fun _ 1 n (fun _ j => E)) (only parsing) : ring_scope.

Notation "\col_ i E" := (@matrix_of_fun _ _ 1 (fun i _ => E)) : ring_scope.
Notation "\col_ ( i < n ) E" :=
  (@matrix_of_fun _ n 1 (fun i _ => E)) (only parsing) : ring_scope.

Definition matrix_eqMixin (R : eqType) m n :=
  CanEqMixin (@mx_valK R m n).
Canonical Structure matrix_eqType R m n:=
  Eval hnf in EqType (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  CanChoiceMixin (@mx_valK R m n).
Canonical Structure matrix_choiceType R m n :=
  Eval hnf in ChoiceType (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  CanCountMixin (@mx_valK R m n).
Canonical Structure matrix_countType R m n :=
  Eval hnf in CountType (matrix_countMixin R m n).
Definition matrix_finMixin (R : finType) m n :=
  CanFinMixin (@mx_valK R m n).
Canonical Structure matrix_finType R m n :=
  Eval hnf in FinType (matrix_finMixin R m n).

(*****************************************************************************)
(****************************Matrix block operations**************************)
(*****************************************************************************)

Section Slicing.

Variable R : Type.

Section Defs.

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

(* Reshape a matrix, to accomodate the block functions for instance. *)
(* ?? make the equality test dynamic, using the null matrix if it fails ? *)

Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

(* Transpose a matrix *)    
Definition trmx A := \matrix_(i, j) A j i.

(* Permute a matrix vertically (rows) or horizontally (columns) *)
Definition row_perm (s : 'S_m) A := \matrix_(i, j) A (s i) j.
Definition col_perm (s : 'S_n) A := \matrix_(i, j) A i (s j).

(* Exchange two rows/columns of a matrix *)
Definition xrow i1 i2 := row_perm (tperm i1 i2). 
Definition xcol j1 j2 := col_perm (tperm j1 j2).

(* Row/Column sub matrices of a matrix *)
Definition row i0 A := \row_j A i0 j.
Definition col j0 A := \col_i A i j0.

(* Removing a row/column from a matrix *)
Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

End Defs.

Local Notation "A ^T" := (trmx A) : ring_scope.

Lemma castmx_id : forall m n erefl_mn (A : 'M_(m, n)), castmx erefl_mn A = A.
Proof. by move=> m n [e_m e_n]; rewrite [e_m]eq_axiomK [e_n]eq_axiomK. Qed.

Lemma castmx_comp : forall m1 n1 m2 n2 m3 n3,
                    forall (eq_m1 : m1 = m2) (eq_n1 : n1 = n2),
                    forall (eq_m2 : m2 = m3) (eq_n2 : n2 = n3) A,
  castmx (eq_m2, eq_n2) (castmx (eq_m1, eq_n1) A)
    = castmx (etrans eq_m1 eq_m2, etrans eq_n1 eq_n2) A.
Proof.
by move=> m1 n1 m2 n2 m3 n3; case: m2 /; case: n2 /; case: m3 /; case: n3 /.
Qed.

Lemma castmxK : forall m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2),
  cancel (castmx (eq_m, eq_n)) (castmx (esym eq_m, esym eq_n)).
Proof. by move=> m1 n1 m2 n2; case: m2 /; case: n2/. Qed.

Lemma castmxKV : forall m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2),
  cancel (castmx (esym eq_m, esym eq_n)) (castmx (eq_m, eq_n)). 
Proof. by move=> m1 n1 m2 n2; case: m2 /; case: n2/. Qed.

Lemma castmxE : forall m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A i j,
  castmx eq_mn A i j =
     A (cast_ord (esym eq_mn.1) i) (cast_ord (esym eq_mn.2) j).
Proof.
by move=> m1 n1 m2 n2 [];case: m2 /; case: n2 / => A i j; rewrite !cast_ord_id.
Qed.

Lemma trmxK : forall m n, cancel (@trmx m n) (@trmx n m).
Proof. by move=> m n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_inj : forall m n, injective (@trmx m n).
Proof. move=> m n; exact: can_inj (@trmxK m n). Qed.

Lemma trmx_cast : forall m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A,
  (castmx eq_mn A)^T = castmx (eq_mn.2, eq_mn.1) A^T.
Proof.
move=> m1 n1 m2 n2 [eq_m eq_n] A; apply/matrixP=> i j.
by rewrite !(mxE, castmxE).
Qed.

Lemma col_perm1 : forall m n (A : 'M_(m, n)), col_perm 1 A = A.
Proof. by move=> *; apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma row_perm1 : forall m n (A : 'M_(m, n)), row_perm 1 A = A.
Proof. by move=> *; apply/matrixP=> i j; rewrite mxE perm1. Qed.
 
Lemma col_permM : forall m n s t (A : 'M_(m, n)),
  col_perm (s * t) A = col_perm s (col_perm t A).
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma row_permM : forall m n s t (A : 'M_(m, n)),
  row_perm (s * t) A = row_perm s (row_perm t A).
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma col_row_permC : forall m n s t (A : 'M_(m, n)),
  col_perm s (row_perm t A) = row_perm t (col_perm s A).
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_row_perm : forall m n s (A : 'M_(m, n)),
  (row_perm s A)^T = col_perm s A^T.
Proof. by move=> m n s A; apply/matrixP=> i j; rewrite !mxE. Qed. 

Lemma tr_col_perm : forall m n s (A : 'M_(m, n)),
  (col_perm s A)^T = row_perm s A^T.
Proof. by move=> m n s A; apply/matrixP=> i j; rewrite !mxE. Qed. 

Lemma tr_xrow : forall m n i1 i2 (A : 'M_(m, n)), 
  (xrow i1 i2 A)^T = xcol i1 i2 A^T.
Proof. by move=> m n A i1 i2; exact: tr_row_perm. Qed.

Lemma tr_xcol : forall m n j1 j2 (A : 'M_(m, n)), 
  (xcol j1 j2 A)^T = xrow j1 j2 A^T.
Proof. by move=> m n A j1 j2; exact: tr_col_perm. Qed.

Lemma tr_row : forall m n i0 (A : 'M_(m, n)),
  (row i0 A)^T = col i0 A^T.
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_row' : forall m n i0 (A : 'M_(m, n)),
  (row' i0 A)^T = col' i0 A^T.
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col : forall m n j0 (A : 'M_(m, n)),
  (col j0 A)^T = row j0 A^T.
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col' : forall m n j0 (A : 'M_(m, n)),
  (col' j0 A)^T = row' j0 A^T.
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma rowP : forall n (U V : 'rV[R]_n), U = V <-> U 0 =1 V 0.
Proof.
move=> n U V; split=> [|eqUV]; first by move/matrixP=> ? ?.
by apply/matrixP=> i; rewrite [i]ord1.
Qed.

Lemma colP : forall n (U V : 'cV[R]_n), U = V <-> U^~ 0 =1 V^~ 0.
Proof.
move=> n U V; split=> [|eqUV]; first by move/matrixP=> ? ?.
by apply/matrixP=> i j; rewrite [j]ord1.
Qed.

Lemma row_id : forall n (V : 'rV_n), row 0 V = V.
Proof. by move=> n V; apply/rowP=> j; rewrite mxE. Qed.

Lemma col_id : forall n (V : 'cV_n), col 0 V = V.
Proof. by move=> n V; apply/colP=> i; rewrite mxE. Qed.

Lemma row_eq : forall m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row i1 A1 = row i2 A2 -> A1 i1 =1 A2 i2.
Proof.
move=> m1 m2 n i1 i2 A1 A2; move/rowP=> eqA12 j; move/(_ j): eqA12.
by rewrite !mxE.
Qed.

Lemma col_eq : forall m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
Proof.
move=> m n1 n2 j1 j2 A1 A2; move/colP=> eqA12 i; move/(_ i): eqA12.
by rewrite !mxE.
Qed.

Lemma row'_eq : forall m n i0 (A B : 'M_(m, n)),
  row' i0 A = row' i0 B -> {in predC1 i0, A =2 B}.
Proof.
move=> m n i0 A B; move/matrixP=> eqAB' i.
rewrite !inE eq_sym; case/unlift_some=> i' -> _  j.
by have:= eqAB' i' j; rewrite !mxE.
Qed.

Lemma col'_eq : forall m n j0 (A B : 'M_(m, n)),
  col' j0 A = col' j0 B -> forall i, {in predC1 j0, A i =1 B i}.
Proof.
move=> m n j0 A B; move/matrixP=> eqAB' i j.
rewrite !inE eq_sym; case/unlift_some=> j' ->  _.
by have:= eqAB' i j'; rewrite !mxE.
Qed.

Section CutPaste.

Variables m m1 m2 n n1 n2 : nat.

(* Concatenating two matrices, in either direction. *)

Definition row_mx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) : 'M[R]_(m, n1 + n2) :=
  \matrix_(i, j) match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end.

Definition col_mx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) : 'M[R]_(m1 + m2, n) :=
  \matrix_(i, j) match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

(* Left/Right | Up/Down submatrices of a rows | columns matrix.   *)
(* The shape of the (dependent) width parameters of the type of A *)
(* determines which submatrix is selected.                        *)

Definition lsubmx (A : 'M[R]_(m, n1 + n2)) := \matrix_(i, j) A i (lshift n2 j).

Definition rsubmx (A : 'M[R]_(m, n1 + n2)) := \matrix_(i, j) A i (rshift n1 j).

Definition usubmx (A : 'M[R]_(m1 + m2, n)) := \matrix_(i, j) A (lshift m2 i) j.

Definition dsubmx (A : 'M[R]_(m1 + m2, n)) := \matrix_(i, j) A (rshift m1 i) j.

Lemma row_mxEl : forall A1 A2 i j, row_mx A1 A2 i (lshift n2 j) = A1 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma row_mxKl : forall A1 A2, lsubmx (row_mx A1 A2) = A1.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE row_mxEl. Qed.

Lemma row_mxEr : forall A1 A2 i j, row_mx A1 A2 i (rshift n1 j) = A2 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma row_mxKr : forall A1 A2, rsubmx (row_mx A1 A2) = A2.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE row_mxEr. Qed.

Lemma hsubmxK : forall A, row_mx (lsubmx A) (rsubmx A) = A.
Proof.
move=> A; apply/matrixP=> i j; rewrite !mxE.
case: splitP => k Dk //=; rewrite !mxE //=; congr (A _ _); exact: val_inj.
Qed.

Lemma col_mxEu : forall A1 A2 i j, col_mx A1 A2 (lshift m2 i) j = A1 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inl _ _)). Qed.

Lemma col_mxKu : forall A1 A2, usubmx (col_mx A1 A2) = A1.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE col_mxEu. Qed.

Lemma col_mxEd : forall A1 A2 i j, col_mx A1 A2 (rshift m1 i) j = A2 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma col_mxKd : forall A1 A2, dsubmx (col_mx A1 A2) = A2.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE col_mxEd. Qed.

Lemma eq_row_mx : forall A1 A2 B1 B2,
  row_mx A1 A2 = row_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
move=> A1 A2 B1 B2 eqAB; move: (congr1 lsubmx eqAB) (congr1 rsubmx eqAB).
by rewrite !(row_mxKl, row_mxKr).
Qed.

Lemma eq_col_mx : forall A1 A2 B1 B2,
  col_mx A1 A2 = col_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
move=> A1 A2 B1 B2 eqAB; move: (congr1 usubmx eqAB) (congr1 dsubmx eqAB).
by rewrite !(col_mxKu, col_mxKd).
Qed.

End CutPaste.

Lemma trmx_lcut : forall m n1 n2 (A : 'M_(m, n1 + n2)),
  (lsubmx A)^T = usubmx A^T.
Proof. by move=> m n1 n2 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_rcut : forall m n1 n2 (A : 'M_(m, n1 + n2)),
  (rsubmx A)^T = dsubmx A^T.
Proof. by move=> m n1 n2 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  (row_mx A1 A2)^T = col_mx A1^T A2^T.
Proof.
move=> m n1 n2 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: splitP => i'; rewrite mxE.
Qed.

Lemma trmx_ucut : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  (usubmx A)^T = lsubmx A^T.
Proof. by move=> m1 m2 n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_dcut : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  (dsubmx A)^T = rsubmx A^T.
Proof. by move=> m1 m2 n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma tr_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  (col_mx A1 A2)^T = row_mx A1^T A2^T.
Proof.
by move=> m1 m2 n A1 A2; apply: (canLR (@trmxK _ _)); rewrite tr_row_mx !trmxK.
Qed.

Lemma vsubmxK : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  col_mx (usubmx A) (dsubmx A) = A.
Proof.
move=> m1 m2 n A; apply: trmx_inj.
by rewrite tr_col_mx trmx_ucut trmx_dcut hsubmxK.
Qed.

Lemma cast_row_mx : forall m m' n1 n2 (eq_m : m = m') A1 A2,
  castmx (eq_m, erefl _) (row_mx A1 A2)
    = row_mx (castmx (eq_m, erefl n1) A1) (castmx (eq_m, erefl n2) A2).
Proof. by move=> m m' n1 n2; case: m' /. Qed.

Lemma cast_col_mx : forall m1 m2 n n' (eq_n : n = n') A1 A2,
  castmx (erefl _, eq_n) (col_mx A1 A2)
    = col_mx (castmx (erefl m1, eq_n) A1) (castmx (erefl m2, eq_n) A2).
Proof. by move=> m1 m2 n n'; case: n' /. Qed.

Lemma row_mxA : forall m n1 n2 n3,
                forall (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)),
  row_mx A1 (row_mx A2 A3)
    = castmx (erefl m, esym (addnA n1 n2 n3)) (row_mx (row_mx A1 A2) A3).
Proof.
move=> m n1 n2 n3 A1 A2 A3; apply: (canRL (castmxKV _ _)); apply/matrixP=> i j.
rewrite castmxE !mxE cast_ord_id; case: splitP => j1 /= def_j.
  have: (j < n1 + n2) && (j < n1) by rewrite def_j lshift_subproof /=.
  by move: def_j; do 2![case: splitP => // ? ->; rewrite ?mxE]; move/ord_inj->.
case: splitP def_j => j2 ->{j} def_j; rewrite !mxE.
  have: ~~ (j2 < n1) by rewrite -leqNgt def_j leq_addr.
  have: j1 < n2 by rewrite -(ltn_add2l n1) -def_j.
  by move: def_j; do 2![case: splitP => // ? ->]; move/addnI; move/val_inj->.
have: ~~ (j1 < n2) by rewrite -leqNgt -(leq_add2l n1) -def_j leq_addr.
by case: splitP def_j => // ? ->; rewrite addnA; move/addnI; move/val_inj->.
Qed.

Lemma col_mxA : forall m1 m2 m3 n, 
                forall (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (A3 : 'M_(m3, n)),
  col_mx A1 (col_mx A2 A3)
    = castmx (esym (addnA m1 m2 m3), erefl n) (col_mx (col_mx A1 A2) A3).
Proof.
move=> m1 m2 m3 n A1 A2 A3; apply: trmx_inj.
by rewrite trmx_cast !tr_col_mx -row_mxA.
Qed.

Lemma row_row_mx : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  row i0 (row_mx A1 A2) = row_mx (row i0 A1) (row i0 A2).
Proof.
move=> m n1 n2 i0 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: (split j) => j'; rewrite mxE.
Qed.

Lemma col_col_mx : forall m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  col j0 (col_mx A1 A2) = col_mx (col j0 A1) (col j0 A2).

Proof.
by move=> *; apply: trmx_inj; rewrite !(tr_col, tr_col_mx, row_row_mx).
Qed.

Lemma row'_row_mx : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  row' i0 (row_mx A1 A2) = row_mx (row' i0 A1) (row' i0 A2).
Proof.
move=> m n1 n2 i0 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: (split j) => j'; rewrite mxE.
Qed.

Lemma col'_col_mx : forall m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  col' j0 (col_mx A1 A2) = col_mx (col' j0 A1) (col' j0 A2).
Proof.
by move=> *; apply: trmx_inj; rewrite !(tr_col', tr_col_mx, row'_row_mx).
Qed.

Lemma colKl : forall m n1 n2 j1 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col (lshift n2 j1) (row_mx A1 A2) = col j1 A1.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(row_mxEl, mxE). Qed.

Lemma colKr : forall m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col (rshift n1 j2) (row_mx A1 A2) = col j2 A2.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(row_mxEr, mxE). Qed.

Lemma rowKu : forall m1 m2 n i1 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row (lshift m2 i1) (col_mx A1 A2) = row i1 A1.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(col_mxEu, mxE). Qed.

Lemma rowKd : forall m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row (rshift m1 i2) (col_mx A1 A2) = row i2 A2.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(col_mxEd, mxE). Qed.

Lemma col'Kl : forall m n1 n2 j1 (A1 : 'M_(m, n1.+1)) (A2 : 'M_(m, n2)),
  col' (lshift n2 j1) (row_mx A1 A2) = row_mx (col' j1 A1) A2.
Proof.
move=> m n1 n2 j1 A1 A2; apply/matrixP=> i /= j; symmetry; rewrite 2!mxE.
case: splitP => j' def_j'.
  rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
  by rewrite /= def_j'.
rewrite -(row_mxEr A1); congr (row_mx _ _ _); apply: ord_inj => /=.
by rewrite /bump def_j' -ltnS -addSn ltn_addr.
Qed.

Lemma row'Ku : forall m1 m2 n i1 (A1 : 'M_(m1.+1, n)) (A2 : 'M_(m2, n)),
  row' (lshift m2 i1) (@col_mx m1.+1 m2 n A1 A2) = col_mx (row' i1 A1) A2.
Proof.
move=> m1 m2 n i1 A1 A2; apply: trmx_inj.
by rewrite tr_col_mx !(@tr_row' _.+1) (@tr_col_mx _.+1) col'Kl.
Qed.

Lemma mx'_cast : forall m n, 'I_n -> (m + n.-1)%N = (m + n).-1.
Proof. by move=> m n [j]; move/ltn_predK <-; rewrite addnS. Qed.

Lemma col'Kr : forall m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col' (rshift n1 j2) (@row_mx m n1 n2 A1 A2) 
    = castmx (erefl m, mx'_cast n1 j2) (row_mx A1 (col' j2 A2)).
Proof.
move=> m n1 n2 j2 A1 A2; apply/matrixP=> i j; symmetry.
rewrite castmxE mxE cast_ord_id; case: splitP => j' /= def_j.
  rewrite mxE -(row_mxEl _ A2); congr (row_mx _ _ _); apply: ord_inj.
  by rewrite /= def_j /bump leqNgt ltn_addr.
rewrite 2!mxE -(row_mxEr A1); congr (row_mx _ _ _ _); apply: ord_inj.
by rewrite /= def_j /bump leq_add2l addnCA.
Qed.

Lemma row'Kd : forall m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row' (rshift m1 i2) (col_mx A1 A2) 
    = castmx (mx'_cast m1 i2, erefl n) (col_mx A1 (row' i2 A2)).
Proof.
move=> m n1 n2 j2 A1 A2; apply: trmx_inj.
by rewrite trmx_cast !(tr_row', tr_col_mx) col'Kr.
Qed.

Section Block.

Variables m1 m2 n1 n2 : nat.

(* Building a block matrix from 4 matrices :               *)
(*  up left, up right, down left and down right components *)

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Lemma eq_block_mx : forall Aul Aur Adl Adr Bul Bur Bdl Bdr,
 block_mx Aul Aur Adl Adr = block_mx Bul Bur Bdl Bdr ->
  [/\ Aul = Bul, Aur = Bur, Adl = Bdl & Adr = Bdr].
Proof.
move=> Aul Aur Adl Adr Bul Bur Bdl Bdr.
by case/eq_col_mx; do 2!case/eq_row_mx=> -> ->.
Qed.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lsubmx (usubmx A).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

Lemma submxK : block_mx ulsubmx ursubmx dlsubmx drsubmx = A.
Proof. by rewrite /block_mx !hsubmxK vsubmxK. Qed.

End CutBlock.

Section CatBlock.

Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Let A := block_mx Aul Aur Adl Adr.

Lemma block_mxEul : forall i j, A (lshift m2 i) (lshift n2 j) = Aul i j.
Proof. by move=> i j; rewrite col_mxEu row_mxEl. Qed.
Lemma block_mxKul : ulsubmx A = Aul. 
Proof. by rewrite /ulsubmx col_mxKu row_mxKl. Qed.

Lemma block_mxEur : forall i j, A (lshift m2 i) (rshift n1 j) = Aur i j.
Proof. by move=> i j; rewrite col_mxEu row_mxEr. Qed.
Lemma block_mxKur : ursubmx A = Aur. 
Proof. by rewrite /ursubmx col_mxKu row_mxKr. Qed.

Lemma block_mxEdl : forall i j, A (rshift m1 i) (lshift n2 j) = Adl i j.
Proof. by move=> i j; rewrite col_mxEd row_mxEl. Qed.
Lemma block_mxKdl : dlsubmx A = Adl. 
Proof. by rewrite /dlsubmx col_mxKd row_mxKl. Qed.

Lemma block_mxEdr : forall i j, A (rshift m1 i) (rshift n1 j) = Adr i j.
Proof. by move=> i j; rewrite col_mxEd row_mxEr. Qed.
Lemma block_mxKdr : drsubmx A = Adr. 
Proof. by rewrite /drsubmx col_mxKd row_mxKr. Qed.

Lemma block_mxEv : A = col_mx (row_mx Aul Aur) (row_mx Adl Adr).
Proof. by []. Qed.

End CatBlock.

End Block.

Section TrCutBlock.

Variables m1 m2 n1 n2 : nat.
Variable A : 'M[R]_(m1 + m2, n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T =  ulsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_ursub : (ursubmx A)^T =  dlsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_dlsub : (dlsubmx A)^T =  ursubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_drsub : (drsubmx A)^T = drsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End TrCutBlock.

Section TrBlock.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Lemma tr_block_mx :
 (block_mx Aul Aur Adl Adr)^T = block_mx Aul^T Adl^T Aur^T Adr^T.
Proof.
rewrite -[_^T]submxK -trmx_ulsub -trmx_ursub -trmx_dlsub -trmx_drsub.
by rewrite block_mxKul block_mxKur block_mxKdl block_mxKdr.
Qed.

Lemma block_mxEh :
  block_mx Aul Aur Adl Adr = row_mx (col_mx Aul Adl) (col_mx Aur Adr).
Proof. by apply: trmx_inj; rewrite tr_block_mx tr_row_mx 2!tr_col_mx. Qed.

End TrBlock.

Lemma block_mxA : forall m1 m2 m3 n1 n2 n3,
            forall (A11 : 'M_(m1, n1)) (A12 : 'M_(m1, n2)) (A13 : 'M_(m1, n3)), 
            forall (A21 : 'M_(m2, n1)) (A22 : 'M_(m2, n2)) (A23 : 'M_(m2, n3)), 
            forall (A31 : 'M_(m3, n1)) (A32 : 'M_(m3, n2)) (A33 : 'M_(m3, n3)), 
    block_mx A11 (row_mx A12 A13) (col_mx A21 A31) (block_mx A22 A23 A32 A33)
  = castmx (esym (addnA m1 m2 m3), esym (addnA n1 n2 n3))
   (block_mx (block_mx A11 A12 A21 A22) (col_mx A13 A23) (row_mx A31 A32) A33).
Proof.
move=> m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33.
rewrite block_mxEh !col_mxA -cast_row_mx -block_mxEv -block_mxEh.
rewrite block_mxEv block_mxEh !row_mxA -cast_col_mx -block_mxEh -block_mxEv.
by rewrite castmx_comp etrans_id.
Qed.

End Slicing.

Prenex Implicits trmx lsubmx rsubmx ulsubmx ursubmx dlsubmx drsubmx.
Notation "A ^T" := (trmx A) : ring_scope.

(*****************************************************************************)
(****************************Matrix algebraic operations**********************)
(*****************************************************************************)

(* Definition of operations for matrices over a ring *)
Section MatrixAlgebraOps.

Variable R : ringType.

Section ZmodOps.
(* The Z-module / vector space structure *)

Variables m n : nat.
Implicit Types A B C : 'M[R]_(m, n).

Definition null_mx := \matrix_(i < m, j < n) (0 : R).
Definition oppmx A := \matrix_(i < m, j < n) (- A i j).
Definition addmx A B := \matrix_(i < m, j < n) (A i j + B i j).
Definition scalemx x A := \matrix_(i < m, j < n) (x * A i j).

Lemma addmxA : associative addmx.
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE addrA. Qed.

Lemma addmxC : commutative addmx.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE addrC. Qed.

Lemma add0mx : left_id null_mx addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE add0r. Qed.

Lemma addNmx : left_inverse null_mx oppmx addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE addNr. Qed.

Definition matrix_zmodMixin := ZmodMixin addmxA addmxC add0mx addNmx.
Canonical Structure matrix_zmodType := Eval hnf in ZmodType matrix_zmodMixin.

Lemma summxE : forall I r (P : pred I) (E : I -> 'M_(m, n)) i j,
  (\sum_(k <- r | P k) E k) i j = \sum_(k <- r | P k) E k i j.
Proof.
move=> I r P E i j.
by apply: (big_morph (fun A => A i j)) => [A B|]; rewrite mxE.
Qed.

(* Vector space structure *)

Notation "x *m: A" := (scalemx x A) : ring_scope.

Lemma scale0mx : forall A, 0 *m: A = 0.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE mul0r. Qed.

Lemma scalemx0 : forall x, x *m: 0 = 0.
Proof. by move=> x; apply/matrixP=> i j; rewrite !mxE mulr0. Qed.

Lemma scale1mx : forall A, 1 *m: A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE mul1r. Qed.

Lemma scaleNmx : forall x A, (- x) *m: A = - (x *m: A).
Proof. by move=> x A; apply/matrixP=> i j; rewrite !mxE mulNr. Qed.

Lemma scalemxN : forall x A, x *m: (- A) = - (x *m: A).
Proof. by move=> x A; apply/matrixP=> i j; rewrite !mxE mulrN. Qed.

Lemma scalemx_addl : forall x y A, (x + y) *m: A = x *m: A + y *m: A.
Proof. by move=> x y A; apply/matrixP=> i j; rewrite !mxE mulr_addl. Qed.

Lemma scalemx_addr : forall x A B, x *m: (A + B) = x *m: A + x *m: B.
Proof. by move=> x A B; apply/matrixP=> i j; rewrite !mxE mulr_addr. Qed.

Lemma scalemx_subl : forall x y A, (x - y) *m: A = x *m: A - y *m: A.
Proof. by move=> x y A; rewrite scalemx_addl scaleNmx. Qed.

Lemma scalemx_subr : forall x A B, x *m: (A - B) = x *m: A - x *m: B.
Proof. by move=> x A B; rewrite scalemx_addr scalemxN. Qed.

Lemma scalemxA : forall x y A, x *m: (y *m: A) = (x * y) *m: A.
Proof. by move=> x y A; apply/matrixP=> i j; rewrite !mxE mulrA. Qed.

(* Basis *)

Definition delta_mx i0 j0 : 'M[R]_(m, n) :=
  \matrix_(i < m, j < n) ((i == i0) && (j == j0))%:R.

Lemma matrix_sum_delta : forall A,
  A = \sum_(i < m) \sum_(j < n) A i j *m: delta_mx i j.
Proof.
move=> A; apply/matrixP=> i j.
rewrite summxE (bigD1 i) // summxE (bigD1 j) //= !mxE !eqxx mulr1.
rewrite !big1 ?addr0 //= => [i' | j']; rewrite eq_sym; move/negbTE=> diff.
  by rewrite summxE big1 // => j' _; rewrite !mxE diff mulr0.
by rewrite !mxE eqxx diff mulr0.
Qed.

End ZmodOps.

Notation "x *m: A" := (scalemx x A) : ring_scope.

Lemma flatmx0 : forall n, all_equal_to (0 : 'M_(0, n)).
Proof. by move=> n A; apply/matrixP=> [] []. Qed.

Lemma thinmx0 : forall n, all_equal_to (0 : 'M_(n, 0)).
Proof. by move=> n A; apply/matrixP=> i []. Qed.

Lemma trmx0 : forall m n, (0 : 'M_(m, n))^T = 0.
Proof. by move=> m n; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_add : forall m n (A B : 'M_(m, n)), (A + B)^T = A^T + B^T .
Proof. by move=> m n A B; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_scale : forall m n a (A  : 'M_(m, n)), (a *m: A)^T = a *m: A^T.
Proof. by move=> m n a A; apply/matrixP=> i j; rewrite !mxE. Qed.

(* permx lemmas can be handled via the decomposition to product with *)
(* a permutation matrix.                                             *)

Lemma row0 : forall m n i0, row i0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n i0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col0 : forall m n j0, col j0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n j0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma row'0 : forall m n i0, row' i0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n i0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col'0 : forall m n j0, col' j0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n j0; apply/matrixP=> i j; rewrite !mxE. Qed.

Ltac split_catmx := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma row_mx0 : forall m n1 n2, row_mx 0 0 = 0 :> 'M_(m, n1 + n2).
Proof. by move=> *; split_catmx. Qed.

Lemma col_mx0 : forall m1 m2 n, col_mx 0 0 = 0 :> 'M_(m1 + m2, n).
Proof. by move=> *; split_catmx. Qed.

Lemma block_mx0 : forall m1 m2 n1 n2,
  block_mx 0 0 0 0 = 0 :> 'M_(m1 + m2, n1 + n2).
Proof. by move=> m1 m2 n1 n2; rewrite /block_mx !row_mx0 col_mx0. Qed.

Lemma add_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) B1 B2,
  row_mx A1 A2 + row_mx B1 B2 = row_mx (A1 + B1) (A2 + B2).
Proof. by move=> *; split_catmx. Qed.

Lemma add_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) B1 B2,
  col_mx A1 A2 + col_mx B1 B2 = col_mx (A1 + B1) (A2 + B2).
Proof. by move=> *; split_catmx. Qed.

Lemma add_block_mx : forall m1 m2 n1 n2,
                     forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
                     forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
                     forall Bul Bur Bdl Bdr,
  block_mx Aul Aur Adl Adr  + block_mx Bul Bur Bdl Bdr
    = block_mx (Aul + Bul) (Aur + Bur) (Adl + Bdl) (Adr + Bdr).
Proof. by move=> *; rewrite add_col_mx !add_row_mx. Qed.

Lemma scale_row_mx : forall m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  a *m: row_mx A1 A2 = row_mx (a *m: A1) (a *m: A2).
Proof. by move=> *; split_catmx. Qed.

Lemma scale_col_mx : forall m1 m2 n a (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  a *m: col_mx A1 A2 = col_mx (a *m: A1) (a *m: A2).
Proof. by move=> *; split_catmx. Qed.

Lemma scale_block_mx : forall m1 m2 n1 n2 a,
                       forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
                       forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
  a *m: block_mx Aul Aur Adl Adr
     = block_mx (a *m: Aul) (a *m: Aur) (a *m: Adl) (a *m: Adr).    
Proof. by move=> *; rewrite scale_col_mx !scale_row_mx. Qed.

(* Diagonal matrices *)

Definition diag_mx n (d : 'rV[R]_n) : 'M_n :=
  \matrix_(i , j) (if i == j then d 0 i else 0).

Lemma tr_diag_mx : forall n (d : 'rV_n), (diag_mx d)^T = diag_mx d.
Proof.
by move=> n d; apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->.
Qed.

Lemma diag_mx0 : forall n, diag_mx 0 = 0 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxE if_same. Qed.

Lemma diag_mx_opp : forall n (d : 'rV_n), diag_mx (- d) = - diag_mx d.
Proof. by move=> n d; apply/matrixP=> i j; rewrite !mxE (fun_if -%R) oppr0. Qed.

Lemma diag_mx_add : forall n (d e : 'rV_n),
  diag_mx (d + e) = diag_mx d + diag_mx e.
Proof.
by move=> n d e; apply/matrixP=> i j; rewrite !mxE; case: eqP; rewrite ?addr0.
Qed.

Lemma scale_diag_mx : forall n a (d : 'rV_n),
  a *m: diag_mx d = diag_mx (a *m: d).
Proof.
by move=> n a d; apply/matrixP=> i j; rewrite !mxE (fun_if ( *%R a)) mulr0.
Qed.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Definition scalar_mx n x : 'M[R]_n := \matrix_(i , j) (if i == j then x else 0).
Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma scalar_mx_diag : forall n a, a%:M = diag_mx (\row_(i < n) a).
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mx11_scalar : forall A : 'M_1, A = (A 0 0)%:M.
Proof. by move=> A; apply/matrixP=> i j; rewrite [i]ord1 [j]ord1 mxE eqxx. Qed.

Lemma tr_scalar_mx : forall n a, (a%:M)^T = a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE eq_sym. Qed.

Lemma trmx1 : forall n, (1%:M)^T = 1%:M :> 'M_n.
Proof. move=> n; exact: tr_scalar_mx. Qed.

Lemma scalar_mx0 : forall n, 0%:M = 0 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxE if_same. Qed.

Lemma scalar_mx_opp : forall n a, (- a)%:M = - a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE (fun_if -%R) oppr0. Qed.
  
Lemma scalar_mx_add : forall n a b, (a + b)%:M = a%:M + b%:M :> 'M_n.
Proof.
move=> n a b; apply/matrixP=> i j; rewrite !mxE.
by case: (i == j); rewrite ?addr0.
Qed.

Lemma scale_scalar_mx : forall n a1 a2, a1 *m: a2%:M = (a1 * a2)%:M :> 'M_n.
Proof.
by move=> n a1 a2; apply/matrixP=> i j; rewrite !mxE (fun_if ( *%R _)) mulr0.
Qed.

Lemma scalar_mx_block : forall n1 n2 a,
  a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
Proof.
move=> n1 n2 a; apply/matrixP=> i j; rewrite !mxE -val_eqE /=.
by do 2![case: splitP => ? ->; rewrite !mxE];
   rewrite ?eqn_addl // -?(eq_sym (n1 + _)%N) eqn_leq leqNgt lshift_subproof.
Qed.

(* Matrix multiplication with the bigops *)
Definition mulmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA : forall m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)),
  A *m (B *m C) = A *m B *m C.
Proof.
move=> m n p q A B C; apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j * (B j k * C k l)))).
by apply: eq_bigr => j _; rewrite mxE big_distrr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE big_distrl /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

Lemma mul0mx : forall m n p (A : 'M_(n, p)), 0 *m A = 0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k.
by rewrite !mxE big1 //= => j _; rewrite mxE mul0r.
Qed.

Lemma mulmx0 : forall m n p (A : 'M_(m, n)), A *m 0 = 0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k; rewrite !mxE big1 // => j _.
by rewrite mxE mulr0.
Qed.

Lemma mulmxN : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m (- B) = - (A *m B).
Proof.
move=> m n p A B; apply/matrixP=> i k; rewrite !mxE -sumr_opp.
by apply: eq_bigr => j _; rewrite mxE mulrN.
Qed.

Lemma mulNmx : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  - A *m B = - (A *m B).
Proof.
move=> m n p A B; apply/matrixP=> i k; rewrite !mxE -sumr_opp.
by apply: eq_bigr => j _; rewrite mxE mulNr.
Qed.

Lemma mulmx_addl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Proof.
move=> m n p A1 A2 B; apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE -mulr_addl.
Qed.

Lemma mulmx_addr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 + B2) = A *m B1 + A *m B2.
Proof.
move=> m n p A B1 B2; apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite mxE mulr_addr.
Qed.

Lemma scalemxAl : forall m n p a (A : 'M_(m, n)) (B : 'M_(n, p)),
  a *m: (A *m B) = (a *m: A) *m B.
Proof.
move=> m n p a A B; apply/matrixP=> i k; rewrite !mxE big_distrr /=.
by apply: eq_bigr => j _; rewrite mulrA mxE.
Qed.
(* Right scaling associativity requires a commutative ring *)

Lemma mul_diag_mx : forall m n d (A : 'M_(m, n)),
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
Proof.
move=> m n d A; apply/matrixP=> i j.
rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym -if_neg => ->; rewrite mul0r.
Qed.

Lemma mul_mx_diag : forall m n (A : 'M_(m, n)) d,
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
Proof.
move=> m n A d; apply/matrixP=> i j.
rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym -if_neg => ->; rewrite mulr0.
Qed.

Lemma mulmx_diag : forall n (d e : 'rV_n),
  diag_mx d *m diag_mx e = diag_mx (\row_j (d 0 j * e 0 j)).
Proof.
move=> n d e; apply/matrixP=> i j.
by rewrite mul_diag_mx !mxE (fun_if ( *%R _)) mulr0.
Qed.

Lemma mul_scalar_mx : forall m n a A, a%:M *m A = a *m: A :> 'M_(m, n).
Proof.
move=> m n a A; apply/matrixP=> i j.
rewrite !mxE (bigD1 i) //= !mxE eqxx big1 ?addr0 // => i' i'i.
by rewrite mxE eq_sym -if_neg i'i mul0r.
Qed.

Lemma scalar_mxM : forall n a b, (a * b)%:M = a%:M *m b%:M :> 'M_n.
Proof. by move=> n a b; rewrite mul_scalar_mx scale_scalar_mx. Qed.

Lemma mul1mx : forall m n (A : 'M_(m, n)), 1%:M *m A = A.
Proof. by move=> m n A; rewrite mul_scalar_mx scale1mx. Qed.

Lemma mulmx1 : forall m n (A : 'M_(m, n)), A *m 1%:M = A.
Proof.
move=> m n A; apply/matrixP=> i k; rewrite !mxE.
rewrite (bigD1 k) //= !mxE eqxx mulr1 big1 ?addr0 //= => j ji.
by rewrite mxE -if_neg ji mulr0.
Qed.

Lemma mul_col_perm : forall m n p s (A : 'M_(m, n)) (B : 'M_(n, p)),
  col_perm s A *m B = A *m row_perm s^-1 B.
Proof.
move=> m n p s A B; apply/matrixP=> i k; rewrite !mxE.
rewrite (reindex_inj (@perm_inj _ s^-1)); apply: eq_bigr => j _ /=.
by rewrite !mxE permKV.
Qed.

Lemma mul_row_perm : forall m n p s (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m row_perm s B = col_perm s^-1 A *m B.
Proof. by move=> m n p s A B; rewrite mul_col_perm invgK. Qed.

Lemma mul_xcol : forall m n p j1 j2 (A : 'M_(m, n)) (B : 'M_(n, p)),
  xcol j1 j2 A *m B = A *m xrow j1 j2 B.
Proof. by move=> m n p j1 j2 A B; rewrite mul_col_perm tpermV. Qed.

(* Permutation matrix *)

Definition perm_mx n s : 'M_n := row_perm s 1%:M.

Definition tperm_mx n i1 i2 : 'M_n := perm_mx (tperm i1 i2).

Lemma col_permE : forall m n s (A : 'M_(m, n)),
  col_perm s A = A *m perm_mx s^-1.
Proof. by move=> m n s A; rewrite mul_row_perm mulmx1 invgK. Qed.

Lemma row_permE : forall m n s (A : 'M_(m, n)), row_perm s A = perm_mx s *m A.
Proof.
move=> m n s a; rewrite -[perm_mx _]mul1mx mul_row_perm mulmx1.
by rewrite -mul_row_perm mul1mx.
Qed.

Lemma xcolE : forall m n j1 j2 (A : 'M_(m, n)),
  xcol j1 j2 A = A *m tperm_mx j1 j2.
Proof. by move=> m n j1 j2 A; rewrite /xcol col_permE tpermV. Qed.

Lemma xrowE : forall m n i1 i2 (A : 'M_(m, n)),
  xrow i1 i2 A = tperm_mx i1 i2 *m A.
Proof. by move=> m n i1 i2 A; exact: row_permE. Qed.

Lemma tr_perm_mx : forall n (s : 'S_n), (perm_mx s)^T = perm_mx s^-1.
Proof.
by move=> n s; rewrite -[_^T]mulmx1 tr_row_perm mul_col_perm trmx1 mul1mx.
Qed.

Lemma tr_tperm_mx : forall n i1 i2, (tperm_mx i1 i2)^T = tperm_mx i1 i2 :> 'M_n.
Proof. by move=> n i1 i2; rewrite tr_perm_mx tpermV. Qed.
  
Lemma perm_mx1 : forall n, perm_mx 1 = 1%:M :> 'M_n.
Proof. move=> n; exact: row_perm1. Qed.

Lemma perm_mxM : forall n (s t : 'S_n),
  perm_mx (s * t) = perm_mx s *m perm_mx t.
Proof. by move=> n s t; rewrite -row_permE -row_permM. Qed.

Definition is_perm_mx n (A : 'M_n) := existsb s, A == perm_mx s.

Lemma is_perm_mxP : forall n (A : 'M_n),
  reflect (exists s, A = perm_mx s) (is_perm_mx A).
Proof. by move=> n A; apply: (iffP existsP) => [] [s]; move/eqP; exists s. Qed.

Lemma perm_mx_is_perm : forall n (s : 'S_n), is_perm_mx (perm_mx s).
Proof. by move=> n s; apply/is_perm_mxP; exists s. Qed.

Lemma is_perm_mx1 : forall n, is_perm_mx (1%:M : 'M_n).
Proof. by move=> n; rewrite -perm_mx1 perm_mx_is_perm. Qed.

Lemma is_perm_mxMl : forall n (A B : 'M_n),
  is_perm_mx A -> is_perm_mx (A *m B) = is_perm_mx B.
Proof.
move=> n A B; case/is_perm_mxP=> s ->.
apply/is_perm_mxP/is_perm_mxP=> [[t def_t] | [t ->]]; last first.
  by exists (s * t)%g; rewrite perm_mxM.
exists (s^-1 * t)%g.
by rewrite perm_mxM -def_t -!row_permE -row_permM mulVg row_perm1.
Qed.

Lemma is_perm_mx_tr : forall n (A : 'M_n), is_perm_mx A^T = is_perm_mx A.
Proof.
move=> n A; apply/is_perm_mxP/is_perm_mxP=> [[t def_t] | [t ->]]; exists t^-1%g.
  by rewrite -tr_perm_mx -def_t trmxK.
by rewrite tr_perm_mx.
Qed.
   
Lemma is_perm_mxMr : forall n (A B : 'M_n),
  is_perm_mx B -> is_perm_mx (A *m B) = is_perm_mx A.
Proof.
move=> n A B; case/is_perm_mxP=> s ->.
rewrite -[s]invgK -col_permE -is_perm_mx_tr tr_col_perm row_permE.
by rewrite is_perm_mxMl (perm_mx_is_perm, is_perm_mx_tr).
Qed.

(* Partial identity matrix (used in rank decomposition). *)

Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix_(i, j) if (i == j :> nat) && (i < r) then 1 else 0.

Lemma pid_mx_0 : forall m n, pid_mx 0 = 0 :> 'M_(m, n).
Proof. by move=> m n; apply/matrixP=> i j; rewrite !mxE andbF. Qed.

Lemma pid_mx_1 : forall r, pid_mx r = 1%:M :> 'M_r.
Proof. by move=> r; apply/matrixP=> i j; rewrite !mxE ltn_ord andbT. Qed.

Lemma pid_mx_row : forall n r, pid_mx r = row_mx 1%:M 0 :> 'M_(r, r + n).
Proof.
move=> n r; apply/matrixP=> i j; rewrite !mxE ltn_ord andbT.
case: splitP => j' ->; rewrite !mxE // .
by rewrite -if_neg neq_ltn (leq_trans (ltn_ord i)) ?leq_addr.
Qed.

Lemma pid_mx_col : forall m r, pid_mx r = col_mx 1%:M 0 :> 'M_(r + m, r).
Proof.
move=> m r; apply/matrixP=> i j; rewrite !mxE andbC.
by case: splitP => i' ->; rewrite !mxE // eq_sym.
Qed.

Lemma pid_mx_block : forall m n r,
  pid_mx r = block_mx 1%:M 0 0 0 :> 'M_(r + m, r + n).
Proof.
move=> m n r; apply/matrixP=> i j; rewrite !mxE row_mx0 andbC.
case: splitP => i' ->; rewrite !mxE //; case: splitP => j' ->; rewrite !mxE //=.
by rewrite -if_neg neq_ltn (leq_trans (ltn_ord i')) ?leq_addr.
Qed.

(* We cover all 1 x 2, 2 x 1, and 2 x 2 block products. *)

Lemma mul_mx_row : forall m n p1 p2,
    forall (A : 'M_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)),
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
move=> m n p1 p2 A Bl Br; apply/matrixP=> i k; rewrite !mxE.
by case defk: (split k); rewrite mxE; apply: eq_bigr => j _; rewrite mxE defk.
Qed.

Lemma mul_col_mx : forall m1 m2 n p,
    forall (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)) (B : 'M_(n, p)),
  col_mx Au Ad *m B = col_mx (Au *m B) (Ad *m B).
Proof.
move=> m1 m2 n p Au Ad B; apply/matrixP=> i k; rewrite !mxE.
by case defi: (split i); rewrite mxE; apply: eq_bigr => j _; rewrite mxE defi.
Qed.

Lemma mul_row_col : forall m n1 n2 p,
    forall (Al : 'M_(m, n1)) (Ar : 'M_(m, n2)),
    forall (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)),
  row_mx Al Ar *m col_mx Bu Bd = Al *m Bu + Ar *m Bd.
Proof.
move=> m n1 n2 p Al Ar Bu Bd.
apply/matrixP=> i k; rewrite !mxE big_split_ord /=.
congr (_ + _); apply: eq_bigr => j _; first by rewrite row_mxEl col_mxEu.
by rewrite row_mxEr col_mxEd.
Qed.

Lemma mul_col_row : forall m1 m2 n p1 p2,
    forall (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)),
    forall (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)),
  col_mx Au Ad *m row_mx Bl Br
     = block_mx (Au *m Bl) (Au *m Br) (Ad *m Bl) (Ad *m Br).
Proof. by move=> *; rewrite mul_col_mx !mul_mx_row. Qed.

Lemma mul_row_block : forall m n1 n2 p1 p2,
    forall (Al : 'M_(m, n1)) (Ar : 'M_(m, n2)),
    forall (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2)),
    forall (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)),
  row_mx Al Ar *m block_mx Bul Bur Bdl Bdr
   = row_mx (Al *m Bul + Ar *m Bdl) (Al *m Bur + Ar *m Bdr).
Proof. by move=> *; rewrite block_mxEh mul_mx_row !mul_row_col. Qed.

Lemma mul_block_col : forall m1 m2 n1 n2 p,
    forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
    forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
    forall (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)),
  block_mx Aul Aur Adl Adr *m col_mx Bu Bd
   = col_mx (Aul *m Bu + Aur *m Bd) (Adl *m Bu + Adr *m Bd).
Proof. by move=> *; rewrite mul_col_mx !mul_row_col. Qed.

Lemma mulmx_block : forall m1 m2 n1 n2 p1 p2,
    forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
    forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
    forall (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2)),
    forall (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)),
  block_mx Aul Aur Adl Adr *m block_mx Bul Bur Bdl Bdr
    = block_mx (Aul *m Bul + Aur *m Bdl) (Aul *m Bur + Aur *m Bdr)
               (Adl *m Bul + Adr *m Bdl) (Adl *m Bur + Adr *m Bdr).
Proof. by move=> *; rewrite mul_col_mx !mul_row_block. Qed.

(* The trace. *)
Definition mxtrace n (A : 'M[R]_n) := \sum_i A i i.
Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_tr : forall n (A : 'M_n), \tr A^T = \tr A.
Proof. by move=> n A; apply: eq_bigr=> i _; rewrite mxE. Qed.

Lemma mxtrace0 : forall n, \tr (0 : 'M_n) = 0.
Proof. by move=> n; apply: big1 => i _; rewrite mxE. Qed.

Lemma mxtrace_add : forall n (A B : 'M_n), \tr (A + B) = \tr A + \tr B.
Proof.
by move=> n A B; rewrite -big_split; apply: eq_bigr => i _; rewrite mxE.

Qed.

Lemma mxtrace_scale : forall n a (A : 'M_n), \tr (a *m: A) = a * \tr A.
Proof.
by move=> n a A; rewrite big_distrr; apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma mxtrace_scalar : forall n a, \tr (a%:M : 'M_n) = a *+ n.
Proof.
move=> n a /=; rewrite -{3}(card_ord n) -sumr_const; apply: eq_bigr => i _.
by rewrite mxE eqxx.
Qed.

Lemma mxtrace_block : forall n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2),
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
Proof.
move=> n1 n2 Aul Aur Adl Adr; rewrite /(\tr _) big_split_ord /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite (block_mxEul, block_mxEdr).
Qed.

(* Matrix ring Structure *)
Section MatrixRing.

Variable n : pos_nat. (* Require n > 0 to avoid the trivial ring *)

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
Proof.
by apply/eqP; move/matrixP; move/(_ 0 0); move/eqP; rewrite !mxE oner_eq0.
Qed.

Definition matrix_ringMixin :=
  RingMixin (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
            (@mulmx_addl n n n) (@mulmx_addr n n n) matrix_nonzero1.
Canonical Structure matrix_ringType := Eval hnf in RingType matrix_ringMixin.

Lemma mulmxE : forall A B : 'M_n, A *m B = A * B. Proof. by []. Qed.
Lemma idmxE : 1%:M = 1 :> 'M_n. Proof. by []. Qed.

Lemma scalar_mxE1 : forall a, a%:M = a *m: 1 :> 'M_n.
Proof. by move=> a; rewrite scale_scalar_mx mulr1. Qed.

End MatrixRing.

Section Lift0.

(* Block expresssion of a lifted permutation matrix, for the Cormen LUP. *)

Variable n : nat.

(* These could be in zmodp, that would introduce a dependency of on perm. *)

Definition lift0_perm s : 'S_n.+1 := lift_perm 0 0 s.

Lemma lift0_perm0 : forall s, lift0_perm s 0 = 0.
Proof. by move=> s; exact: lift_perm_id. Qed.

Lemma lift0_perm_lift : forall s k',
  lift0_perm s (lift 0 k') = lift (0 : 'I_n.+1) (s k').
Proof. by move=> s i; exact: lift_perm_lift. Qed.

Lemma lift0_permK : forall s, cancel (lift0_perm s) (lift0_perm s^-1).
Proof. by move=> s i; rewrite /lift0_perm -lift_permV permK. Qed.

Lemma lift0_perm_eq0 : forall s i, (lift0_perm s i == 0) = (i == 0).
Proof. by move=> s i; rewrite (canF_eq (lift0_permK s)) lift0_perm0. Qed.

(* Block expresssion of a lifted permutation matrix *)

Definition lift0_mx A : 'M_(1 + n) := block_mx 1 0 0 A.

Lemma lift0_mx_perm : forall s, lift0_mx (perm_mx s) = perm_mx (lift0_perm s). 
Proof.
move=> s; apply/matrixP=> /= i j.
rewrite !mxE split1 /=; case: unliftP => [i'|] -> /=.
  rewrite lift0_perm_lift !mxE split1 /=.
  by case: unliftP => [j'|] ->; rewrite ?(inj_eq (@lift_inj _ _)) /= !mxE.
rewrite lift0_perm0 !mxE split1 /=.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma lift0_mx_is_perm : forall s, is_perm_mx (lift0_mx (perm_mx s)).
Proof. by move=> s; rewrite lift0_mx_perm perm_mx_is_perm. Qed.

End Lift0.

End MatrixAlgebraOps.

Implicit Arguments perm_mx [[R] [n]].
Implicit Arguments tperm_mx [[R] [n]].
Implicit Arguments pid_mx [[R] [m] [n]].
Prenex Implicits scalemx mulmx diag_mx mxtrace.
Notation "a *m: A" := (scalemx a A) : ring_scope.
Notation "a %:M" := (scalar_mx _ a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "\tr A" := (mxtrace A) : ring_scope.

(* Non-commutative transpose requires multiplication in the converse ring. *)
Lemma trmx_mul_rev : forall R m n p,
    let R' := RevRingType R in forall (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)),
  (A *m B)^T = (B : 'M[R']_(n, p))^T *m (A : 'M[R']_(m, n))^T.
Proof.
move=> R m n p /= A B; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite !mxE.
Qed.

Section ComMatrix.
(* Lemmas for matrices with coefficients in a commutative ring *)
Variable R : comRingType.

Lemma trmx_mul : forall m n p (A : 'M[R]_(m, n)) (B : 'M_(n, p)),
  (A *m B)^T = B^T *m A^T.
Proof.
move=> m n p A B; rewrite trmx_mul_rev; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Lemma scalemxAr : forall m n p a (A : 'M[R]_(m, n)) (B : 'M_(n, p)),
  a *m: (A *m B) = A *m (a *m: B).
Proof.
move=> m n p a A B.
by apply: trmx_inj; rewrite !(trmx_scale, trmx_mul) scalemxAl.
Qed.

Lemma diag_mxC : forall n (d e : 'rV[R]_n),
  diag_mx d *m diag_mx e = diag_mx e *m diag_mx d.
Proof.
move=> n d e; rewrite !mulmx_diag; congr (diag_mx _).
by apply/rowP=> i; rewrite !mxE mulrC.
Qed.

Lemma diag_mx_comm : forall (n : pos_nat) (d e : 'rV[R]_n),
  GRing.comm (diag_mx d) (diag_mx e).
Proof. move=> n; exact: diag_mxC. Qed.

Lemma scalar_mxC : forall m n a (A : 'M[R]_(m, n)), A *m a%:M = a%:M *m A.
Proof.
move=> m n a A; apply: trmx_inj.
by rewrite trmx_mul tr_scalar_mx !mul_scalar_mx trmx_scale.
Qed.

Lemma scalar_mx_comm : forall (n : pos_nat) a (A : 'M[R]_n), GRing.comm A a%:M.
Proof. move=> n; exact: scalar_mxC. Qed.

Lemma mul_mx_scalar : forall m n a (A : 'M[R]_(m, n)), A *m a%:M = a *m: A.
Proof. by move=> m n a A; rewrite scalar_mxC mul_scalar_mx. Qed.

Lemma mxtrace_mulC : forall m n (A : 'M[R]_(m, n)) (B : 'M_(n, m)),
  \tr (A *m B) = \tr (B *m A).
Proof.
move=> m n A B; transitivity (\sum_i \sum_j A i j * B j i).
  by apply: eq_bigr => i _; rewrite mxE.
rewrite exchange_big; apply: eq_bigr => i _ /=; rewrite mxE.
apply: eq_bigr => j _; exact: mulrC.
Qed.

End ComMatrix.

Section Determinant.

Variable R : comRingType.

(* The determinant, in one line with the Leibniz Formula *)
Definition determinant n (A : 'M[R]_n) :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

Local Notation "'\det' A" := (determinant A).

(* The cofactor of a matrix on the indexes i and j *)
Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * \det (row' i (col' j A)).

(* The adjugate matrix : defined as the transpose of the matrix of cofactors *)
Definition adjugate n (A : 'M_n) := \matrix_(i, j) cofactor A j i.

Local Notation "\adj A" := (adjugate A) : ring_scope.

Lemma determinant_multilinear : forall n (A B C : 'M_n) i0 b c,
    row i0 A = b *m: row i0 B + c *m: row i0 C ->
    row' i0 B = row' i0 A ->
    row' i0 C = row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c; rewrite -[_ + _]row_id; move/row_eq=> ABC.
move/row'_eq=> BA; move/row'_eq=> CA.
rewrite !big_distrr -big_split; apply: eq_bigr => s _ /=.
rewrite -!(mulrCA (_ ^+s)) -mulr_addr; congr (_ * _).
rewrite !(bigD1 i0 (_ : predT i0)) //= {}ABC !mxE mulr_addl !mulrA.
by congr (_ * _ + _ * _); apply: eq_bigr => i i0i; rewrite ?BA ?CA.
Qed.

Lemma determinant_alternate : forall n (A : 'M_n) i1 i2,
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
move=> n A i1 i2 Di12 A12; pose t := tperm i1 i2.
have oddMt: forall s, (t * s)%g = ~~ s :> bool.
  by move=> s; rewrite odd_permM odd_tperm Di12.
rewrite /(\det _) (bigID (@odd_perm _)) /=.
apply: canLR (subrK _) _; rewrite add0r -sumr_opp.
rewrite (reindex_inj (mulgI t)); apply: eq_big => //= s.
rewrite oddMt; move/negPf->; rewrite mulN1r mul1r; congr (- _).
rewrite (reindex_inj (@perm_inj _ t)); apply: eq_bigr => /= i _.
by rewrite permM tpermK /t; case: tpermP => // ->; rewrite A12.
Qed.

Lemma det_tr : forall n (A : 'M_n), \det A^T = \det A.
Proof.
move=> n A; rewrite /(\det _) (reindex_inj (@invg_inj _)) /=.
apply: eq_bigr => s _ /=; rewrite !odd_permV (reindex_inj (@perm_inj _ s)) /=.
by congr (_ * _); apply: eq_bigr => i _; rewrite mxE permK.
Qed.

Lemma det_perm : forall n (s : 'S_n), \det (perm_mx s) = (-1) ^+ s.
Proof.
move=> n s; rewrite /(\det _) (bigD1 s) //=.
rewrite big1 => [|i _]; last by rewrite /= !mxE eqxx.
rewrite mulr1 big1 ?addr0 => //= t Dst.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (bigD1 i) // mulrCA /= !mxE (negbTE ist) mul0r.
by case/eqP: Dst; apply/permP => i; move/eqP: (Est i).
Qed.

Lemma det1 : forall n, \det (1%:M : 'M_n) = 1.
Proof. by move=> n; rewrite -perm_mx1 det_perm odd_perm1. Qed.

Lemma det_scalemx : forall n x (A : 'M_n), \det (x *m: A) = x ^+ n * \det A.
Proof.
move=> n x A; rewrite big_distrr /=; apply: eq_bigr => s _.
rewrite mulrCA; congr (_ * _).
rewrite -{10}[n]card_ord -prodr_const -big_split /=.
by apply: eq_bigr=> i _; rewrite mxE.
Qed.

Lemma det_scalar : forall n a, \det (a%:M : 'M_n) = a ^+ n.
Proof.
by move=> n a; rewrite -{1}(mulr1 a) -scale_scalar_mx det_scalemx det1 mulr1.
Qed.

Lemma det_scalar1 : forall a, \det (a%:M : 'M_1) = a.
Proof. exact: det_scalar. Qed.

Lemma det_mulmx : forall n (A B : 'M_n), \det (A *m B) = \det A * \det B.
Proof.
move=> n A B; rewrite big_distrl /=.
pose F := {ffun 'I_n -> 'I_n}; pose AB s i j := A i j * B j (s i).
transitivity (\sum_(f : F) \sum_(s : 'S_n) (-1) ^+ s * \prod_i AB s i (f i)).
  rewrite exchange_big; apply: eq_bigr => /= s _; rewrite -big_distrr /=. 
  congr (_ * _); rewrite -(bigA_distr_bigA (AB s)) /=.
  by apply: eq_bigr => x _; rewrite mxE.
rewrite (bigID (fun f : F => injectiveb f)) /= addrC big1 ?add0r => [|f Uf].
  rewrite (reindex (@pval _)) /=; last first.
    pose in_Sn := insubd (1%g : 'S_n).
    by exists in_Sn => /= f Uf; first apply: val_inj; exact: insubdK.
  apply: eq_big => /= [s | s _]; rewrite ?(valP s) // big_distrr /=.
  rewrite (reindex_inj (mulgI s)); apply: eq_bigr => t _ /=.
  rewrite big_split /= mulrA mulrCA mulrA mulrCA mulrA.
  rewrite -signr_addb odd_permM !pvalE; congr (_ * _); symmetry.
  by rewrite (reindex_inj (@perm_inj _ s)); apply: eq_bigr => i; rewrite permM.
transitivity (\det (\matrix_(i, j) B (f i) j) * \prod_i A i (f i)).
  rewrite mulrC big_distrr /=; apply: eq_bigr => s _.
  rewrite mulrCA big_split //=; congr (_ * (_ * _)).
  by apply: eq_bigr => x _; rewrite mxE.
case/injectivePn: Uf => i1 [i2 Di12 Ef12].
by rewrite (determinant_alternate Di12) ?simp //= => j; rewrite !mxE Ef12.
Qed.

Lemma detM : forall (n : pos_nat) (A B : 'M_n), \det (A * B) = \det A * \det B.
Proof. move=> n; exact: det_mulmx. Qed.

Lemma det_diag : forall n (d : 'rV_n), \det (diag_mx d) = \prod_i d 0 i.
Proof.
move=> n d; rewrite /(\det _) (bigD1 1%g) //= addrC big1 => [|p p1].
  by rewrite add0r odd_perm1 mul1r; apply: eq_bigr => i; rewrite perm1 mxE eqxx.
have{p1}: ~~ perm_on set0 p.
  apply: contra p1; move/subsetP=> p1; apply/eqP; apply/permP=> i.
  by rewrite perm1; apply/eqP; apply/idPn; move/p1; rewrite inE.
case/subsetPn=> i; rewrite !inE => p_i _.
by rewrite (bigD1 i) //= mulrCA mxE eq_sym -if_neg p_i mul0r.
Qed.

(* Laplace expansion lemma *)
Lemma expand_cofactor : forall n (A : 'M_n) i j,
  cofactor A i j =
    \sum_(s : 'S_n | s i == j) (-1) ^+ s * \prod_(k | i != k) A k (s k).
Proof.
move=> [_ [] //|n] A i0 j0; rewrite (reindex (lift_perm i0 j0)); last first.
  pose ulsf i (s : 'S_n.+1) k := odflt k (unlift (s i) (s (lift i k))).
  have ulsfK: forall i (s : 'S__) k, lift (s i) (ulsf i s k) = s (lift i k).
    rewrite /ulsf => i s k; have:= neq_lift i k.
    by rewrite -(inj_eq (@perm_inj _ s)); case/unlift_some=> ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1%g) _ => k'.
    by rewrite {1}/ulsf ulsfK !permK liftK.
  exists (fun s => perm (inj_ulsf s)) => [s _ | s].
    by apply/permP=> k'; rewrite permE /ulsf lift_perm_lift lift_perm_id liftK.
  move/(s _ =P _) => si0; apply/permP=> k.
  case: (unliftP i0 k) => [k'|] ->; rewrite ?lift_perm_id //.
  by rewrite lift_perm_lift -si0 permE ulsfK.
rewrite /cofactor big_distrr /=.
apply: eq_big => [s | s _]; first by rewrite lift_perm_id eqxx.
rewrite -signr_odd mulrA -signr_addb odd_add -odd_lift_perm; congr (_ * _).
case: (pickP 'I_n) => [k0 _ | n0]; last first.
  by rewrite !big1 // => [j | i _]; first case/unlift_some=> i; have:= n0 i.
rewrite (reindex (lift i0)).
  by apply: eq_big => [k | k _] /=; rewrite ?neq_lift // !mxE lift_perm_lift.
exists (fun k => odflt k0 (unlift i0 k)) => k; first by rewrite liftK.
by case/unlift_some=> k' -> ->.
Qed.

Lemma expand_det_row : forall n (A : 'M_n) i0,
  \det A = \sum_j A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
rewrite (partition_big (fun s : 'S_n => s i0) predT) //=.
apply: eq_bigr => j0 _; rewrite expand_cofactor big_distrr /=.
apply: eq_bigr => s; move/eqP=> Dsi0.
rewrite mulrCA (bigID (pred1 i0)) /= big_pred1_eq Dsi0; congr (_ * (_ * _)).
by apply: eq_bigl => i; rewrite eq_sym.
Qed.

Lemma cofactor_tr : forall n (A : 'M_n) i j,
  cofactor A^T i j = cofactor A j i.
Proof.
move=> n A i j; rewrite /cofactor addnC; congr (_ * _).
rewrite -tr_row' -tr_col' det_tr; congr (\det _).
by apply/matrixP=> ? ?; rewrite !mxE.
Qed.

Lemma expand_det_col : forall n (A : 'M_n) j0,
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -det_tr (expand_det_row _ j0).
by apply: eq_bigr => i _; rewrite cofactor_tr mxE.
Qed.

(* Cramer Rule : adjugate on the left *)
Lemma mul_mx_adj : forall n (A : 'M_n), A *m \adj A = (\det A)%:M.
Proof.
move=> n A; apply/matrixP=> i1 i2; rewrite !mxE; case Di: (i1 == i2).
  rewrite (eqP Di) (expand_det_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxE.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxE Di eq_refl.
rewrite -{2}(determinant_alternate (negbT Di) EBi12).
rewrite (expand_det_row _ i2); apply: eq_bigr => j _.
rewrite !mxE eq_refl; congr (_ * (_ * _)).
apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => i _.
by rewrite !mxE eq_sym -if_neg neq_lift.
Qed.

Lemma trmx_adj : forall n (A : 'M_n), (\adj A)^T = \adj A^T.
Proof. by move=> n A; apply/matrixP=> i j; rewrite !mxE cofactor_tr. Qed.

(* Cramer rule : adjugate on the right *)
Lemma mul_adj_mx : forall n (A : 'M_n), \adj A *m A = (\det A)%:M.
Proof.
move=> n A; apply: trmx_inj; rewrite trmx_mul trmx_adj mul_mx_adj.
by rewrite det_tr tr_scalar_mx.
Qed.

(* Left inverses are right inverses. *)
Lemma mulmx1C : forall n (A B : 'M[R]_n), A *m B = 1%:M -> B *m A = 1%:M.
Proof.
move=> n A B AB1; pose A' := \det B *m: \adj A.
suffices kA: A' *m A = 1%:M by rewrite -[B]mul1mx -kA -(mulmxA A') AB1 mulmx1.
by rewrite -scalemxAl mul_adj_mx scale_scalar_mx mulrC -det_mulmx AB1 det1.
Qed.

(* Only tall matrices have inverses. *)
Lemma mulmx1_min : forall m n (A : 'M[R]_(m, n)) B, A *m B = 1%:M -> m <= n.
Proof.
move=> m n A B AB1; rewrite leqNgt; apply/negP; move/subnKC; rewrite addSnnS.
move: (_ - _)%N => m' def_m; move: AB1; rewrite -{m}def_m in A B *.
rewrite -(vsubmxK A) -(hsubmxK B) mul_col_row scalar_mx_block.
case/eq_block_mx; move/mulmx1C=> BlAu1 AuBr0 _; move/eqP; case/idPn.
by rewrite -[_ B]mul1mx -BlAu1 -mulmxA AuBr0 !mulmx0 eq_sym nonzero1r.
Qed.

Lemma det_ublock : forall n1 n2 (Aul : 'M_n1) (Aur : 'M_(n1, n2)) (Adr : 'M_n2),
  \det (block_mx Aul Aur 0 Adr) = \det Aul * \det Adr.
Proof.
move=> n1 n2 Aul Aur Adr; elim: n1 => [|n1 IHn1] in Aul Aur *.
  have ->: Aul = 1%:M by apply/matrixP=> i [].
  rewrite det1 mul1r; congr (\det _); apply/matrixP=> i j.
  by do 2![rewrite !mxE; case: splitP => [[]|k] //=; move/val_inj=> <- {k}].
rewrite (expand_det_col _ (lshift n2 0)) big_split_ord /=.
rewrite addrC big1 1?simp => [|i _]; last by rewrite block_mxEdl mxE simp.
rewrite (expand_det_col _ 0) big_distrl /=; apply eq_bigr=> i _.
rewrite block_mxEul -!mulrA; do 2!congr (_ * _).
by rewrite col'_col_mx !col'Kl col'0 row'Ku row'_row_mx IHn1.
Qed.

Lemma det_lblock : forall n1 n2 (Aul : 'M_n1) (Adl : 'M_(n2, n1)) (Adr : 'M_n2),
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
Proof. by move=> *; rewrite -det_tr tr_block_mx trmx0 det_ublock !det_tr. Qed.

End Determinant.

Notation "\det A" := (determinant A) : ring_scope.
Notation "\adj A" := (adjugate A) : ring_scope.

(*****************************************************************************)
(****************************** Matrix unit ring *****************************)
(*****************************************************************************)

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.

Definition unitmx : pred 'M[R]_n := fun A => GRing.unit (\det A).
Definition invmx A := if unitmx A then (\det A)^-1 *m: \adj A else A.

Lemma unitmxE : forall A, unitmx A = GRing.unit (\det A). Proof. by []. Qed.

Lemma unitmx1 : unitmx 1%:M. Proof. by rewrite /unitmx det1 unitr1. Qed.

Lemma unitmx_perm : forall s, unitmx (perm_mx s).
Proof. by move=> s; rewrite /unitmx det_perm unitr_exp ?unitr_opp ?unitr1. Qed.

Lemma unitmx_tr : forall A, unitmx A^T = unitmx A.
Proof. by move=> A; rewrite /unitmx det_tr. Qed.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Proof.
move=> A nsA; rewrite /invmx [unitmx A]nsA.
by rewrite -scalemxAl mul_adj_mx scale_scalar_mx mulVr.
Qed.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Proof.
move=> A nsA; rewrite /invmx [unitmx A]nsA.
by rewrite -scalemxAr mul_mx_adj scale_scalar_mx mulVr.
Qed.

Lemma mulKmx : forall m, {in unitmx, @left_loop _ 'M_(n, m) invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite mulmxA mulVmx ?mul1mx. Qed.

Lemma mulKVmx : forall m, {in unitmx, @rev_left_loop _ 'M_(n, m) invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite mulmxA mulmxV ?mul1mx. Qed.

Lemma mulmxK : forall m, {in unitmx, @right_loop 'M_(m, n) _ invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite -mulmxA mulmxV ?mulmx1. Qed.

Lemma mulmxKV : forall m, {in unitmx, @rev_right_loop 'M_(m, n) _ invmx mulmx}.
Proof. by move=> m A uA /= B; rewrite -mulmxA mulVmx ?mulmx1. Qed.

Lemma det_inv : forall A, \det (invmx A) = (\det A)^-1.
Proof.
move=> A; case uA: (unitmx A); last by rewrite /invmx uA invr_out ?negbT.
by apply: (mulrI uA); rewrite -det_mulmx mulmxV ?divrr ?det1.
Qed.

Lemma unitmx_inv : forall A, unitmx (invmx A) = unitmx A.
Proof. by move=> A; rewrite /unitmx det_inv unitr_inv. Qed.

Lemma trmx_inv : forall A : 'M_n, (invmx A)^T = invmx (A^T).
Proof.
by move=> A; rewrite (fun_if trmx) trmx_scale trmx_adj -unitmx_tr -det_tr.
Qed.

Lemma invmxK : involutive invmx.
Proof.
move=> A; case uA : (unitmx A); last by rewrite /invmx !uA.
by apply: (can_inj (mulKVmx uA)); rewrite mulVmx // mulmxV ?[_ \in _]unitmx_inv.
Qed.

Lemma mulmx1_unit : forall A B, A *m B = 1%:M -> unitmx A /\ unitmx B.
Proof.
by move=> A B AB1; apply/andP; rewrite -unitr_mul -det_mulmx AB1 det1 unitr1.
Qed.

Lemma intro_unitmx : forall A B, B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Proof. by move=> A B [_]; case/mulmx1_unit. Qed.

Lemma invmx_out : {in predC unitmx, invmx =1 id}.
Proof. by move=> A; rewrite inE /= /invmx -if_neg => ->. Qed.

End Defs.

Variable n : pos_nat.

Definition matrix_unitRingMixin :=
  UnitRingMixin (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).
Canonical Structure matrix_unitRing :=
  Eval hnf in UnitRingType matrix_unitRingMixin.

(* Lemmas requiring that the coefficients are in a unit ring *)

Lemma detV : forall A : 'M_n, \det A^-1 = (\det A)^-1.
Proof. exact: det_inv. Qed.

Lemma unitr_trmx : forall A : 'M_n, GRing.unit A^T = GRing.unit A.
Proof. exact: unitmx_tr. Qed.

Lemma trmxV : forall A : 'M_n, A^-1^T = (A^T)^-1.
Proof. exact: trmx_inv. Qed.

Lemma perm_mxV : forall s : 'S_n, perm_mx s^-1 = (perm_mx s)^-1.
Proof.
move=> s; rewrite -[_^-1]mul1r; apply: (canRL (mulmxK (unitmx_perm s))).
by rewrite -perm_mxM mulVg perm_mx1.
Qed.

Lemma is_perm_mxV : forall A : 'M_n, is_perm_mx A^-1 = is_perm_mx A.
Proof.
move=> A; apply/is_perm_mxP/is_perm_mxP=> [] [s defA]; exists s^-1%g.
  by rewrite -(invrK A) defA perm_mxV.
by rewrite defA perm_mxV.
Qed.

End MatrixInv.

Prenex Implicits unitmx invmx.

(*****************************************************************************)
(****************************** LUP decomposion ******************************)
(*****************************************************************************)

Section CormenLUP.

Variable F : fieldType.

(* Decomposition of the matrix A to P A = L U with :
- P a permutation matrix
- L a lower triangular matrix
- U an upper triangular matrix 
*)

Fixpoint cormen_lup {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 (pick [pred k | A k 0 != 0]) in
    let A1 : 'M_(1 + _) := xrow 0 k A in
    let P1 : 'M_(1 + _) := tperm_mx 0 k in
    let Schur := ((A k 0)^-1 *m: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in 
    let P := block_mx 1 0 0 P2 *m P1 in
    let L := block_mx 1 0 ((A k 0)^-1 *m: (P2 *m dlsubmx A1)) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) 0 U2 in
    (P, L, U)
  end.

Lemma cormen_lup_perm :  forall n (A : 'M_n.+1), is_perm_mx (cormen_lup A).1.1.
Proof.
elim=> [| n IHn] A /=; first exact: is_perm_mx1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/=.
rewrite (is_perm_mxMr _ (perm_mx_is_perm _ _)).
case/is_perm_mxP => s ->; exact: lift0_mx_is_perm.
Qed.

Lemma cormen_lup_correct : forall n (A : 'M_n.+1),
  let: (P, L, U) := cormen_lup A in P * A  = L * U.
Proof.
elim=> [|n IHn] A /=; first by rewrite !mul1r.
set k := odflt _ _; set A1 : 'M_(1 + _) := xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P' L' U']] /= IHn.
rewrite -mulrA -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulr_addr {A'}subrK.
congr (block_mx _ _ (_ *m _) _).
rewrite [_ *m: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
by rewrite !mxE lshift0 (elimNf eqP (no_k _)).
Qed.

Lemma cormen_lup_detL : forall n (A : 'M_n.+1), \det (cormen_lup A).1.2 = 1.
Proof.
elim=> [|n IHn] A /=; first by rewrite det1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= detL.
by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

Lemma cormen_lup_lower : forall n A (i j : 'I_n.+1),
  i <= j -> (cormen_lup A).1.2 i j = (i == j)%:R.
Proof.
elim=> [|n IHn] A /= i j; first by rewrite [i]ord1 [j]ord1 mxE.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Ll.
rewrite !mxE split1; case: unliftP => [i'|] -> /=; rewrite !mxE split1.
  by case: unliftP => [j'|] -> //; exact: Ll.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma cormen_lup_upper : forall n A (i j : 'I_n.+1),
  j < i -> (cormen_lup A).2 i j = 0 :> F.
Proof.
elim=> [|n IHn] A /= i j; first by rewrite [i]ord1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Uu.
rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
by case: unliftP => [j'|] ->; [exact: Uu | rewrite /= mxE].
Qed.

End CormenLUP.

(* A more useful decomposition using double pivots, which allows to compute *)
(* the rank, kernel, and image of a matrix.                                 *)

Section RankDecomposition.

Variable F : fieldType.

Fixpoint emxrank m n : 'M[F]_(m, n) -> nat * 'M_m * 'M_n :=
  match m, n return 'M_(m, n) -> nat * 'M_m * 'M_n with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if pick (fun k => A k.1 k.2 != 0) is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v :=  a^-1 *m: dlsubmx A1 in 
      let: (r, L, U) := emxrank (drsubmx A1 - v *m u) in
      (r.+1, xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U))
    else (0%N, 1%:M, 1%:M)
  | _, _ => fun _ => (0%N, 1%:M, 1%:M)
  end.

CoInductive emxrank_spec m n A : nat * 'M[F]_m * 'M_n -> Prop :=
  EmxrankSpec r L U of
      r <= m /\ r <= n & unitmx L & unitmx U & A = L *m pid_mx r *m U:
    emxrank_spec A (r, L, U).

Lemma emxrankP : forall m n (A : 'M_(m, n)), emxrank_spec A (emxrank A).
Proof.
elim=> [|m IHm]; first by split; rewrite ?unitmx1 // [_ *m _]flatmx0 [A]flatmx0.
case=> [|n]; rewrite -(add1n m) -?(add1n n) => A /=.
  by split; rewrite ?unitmx1 // [_ *m _]thinmx0 [A]thinmx0.
case: pickP => [[/= i j] | A0]; last first.
  split; rewrite ?unitmx1 // pid_mx_0 mulmx0 mul0mx; apply/matrixP=> i j.
  by rewrite mxE (elimNf eqP (A0 (i, j))).
set a := A i j; rewrite -unitfE => ua; set A1 := xrow _ _ _.
set u := ursubmx _; set v := _ *m: _; set B : 'M_(m, n) := _ -  _.
case: IHm => r L U /= [r_m r_n] uL uU kB; split=> //.
- rewrite xrowE /unitmx det_mulmx unitr_mul det_lblock det1 mul1r.
  by rewrite -unitmxE unitmx_perm.
- rewrite xcolE /unitmx det_mulmx det_ublock !unitr_mul.
  by rewrite det_scalar1 ua -!unitmxE uU unitmx_perm.
have ->: pid_mx (1 + r) = block_mx 1 0 0 (pid_mx r) :> 'M[F]_(1 + m, 1 + n).
  rewrite -(subnKC r_m) -(subnKC r_n) pid_mx_block (pid_mx_block _ _ _ (1 + r)).
  by rewrite scalar_mx_block -!col_mx0 -!row_mx0 block_mxA castmx_id.
rewrite xcolE xrowE  mulmxA -xcolE -!mulmxA.
rewrite !(addr0, add0r, mulmx0, mul0mx, mulmx_block, mul1mx) mulmxA -kB.
rewrite addrC subrK mul_mx_scalar scalemxA divrr // scale1mx.
have ->: a%:M = ulsubmx A1 by rewrite [_ A1]mx11_scalar !mxE !lshift0 !tpermR.
rewrite submxK /A1 xrowE !xcolE -!mulmxA mulmxA -!perm_mxM !tperm2 !perm_mx1.
by rewrite mulmx1 mul1mx.
Qed.

Section OneRank.

Variables (m n : nat) (A : 'M[F]_(m, n)).

Definition mxrank := (emxrank A).1.1.
Let m' := (m - mxrank)%N.
Let n' := (n - mxrank)%N.

Lemma rank_leq_row : mxrank <= m.
Proof. by rewrite /mxrank; case: emxrankP => r L U []. Qed.

Lemma rank_row_eq : (mxrank + m')%N = m.
Proof. exact: subnKC rank_leq_row. Qed.

Lemma rank_leq_col : mxrank <= n.
Proof. by rewrite /mxrank; case: emxrankP => r L U []. Qed.

Lemma rank_col_eq : (mxrank + n')%N = n.
Proof. exact: subnKC rank_leq_col. Qed.

Let A_L := castmx (erefl m, esym rank_row_eq) (emxrank A).1.2.
Let A_L' := castmx (esym rank_row_eq, erefl m) (invmx (emxrank A).1.2).
Let A_U := castmx (esym rank_col_eq, erefl n) (emxrank A).2.
Let A_U' := castmx (erefl n, esym rank_col_eq) (invmx (emxrank A).2).

Definition col_im := lsubmx A_L.
Definition row_im := usubmx A_U.
Definition col_im_inv := usubmx A_L'.
Definition row_im_inv := lsubmx A_U'.
Definition kermx := dsubmx A_L'.
Definition kermx_inv := rsubmx A_L.
Definition cokermx := rsubmx A_U'.
Definition rank_invmx := row_im_inv *m col_im_inv.

Lemma mulV_row_im : row_im *m row_im_inv = 1%:M.
Proof.
rewrite /row_im /row_im_inv /A_U /A_U'; case: emxrankP => /= _ _ U _ _ uU _.
move/mulmxV: uU; case: n / rank_col_eq in U *; rewrite /castmx /=.
rewrite -{1}[U]vsubmxK -{1}[invmx U]hsubmxK scalar_mx_block mul_col_row.
by case/eq_block_mx.
Qed.

Lemma mulV_col_im : col_im_inv *m col_im = 1%:M.
Proof.
rewrite /col_im /col_im_inv /A_L /A_L'; case: emxrankP => /= _ L _ _ uL _ _.
move/mulVmx: uL; case: m / rank_row_eq in L *; rewrite /castmx /=.
rewrite -{2}[L]hsubmxK -{1}[invmx L]vsubmxK scalar_mx_block mul_col_row.
by case/eq_block_mx.
Qed.

Lemma mulmxV_ker : kermx *m kermx_inv = 1%:M.
Proof.
rewrite /kermx_inv /kermx /A_L /A_L'; case: emxrankP => /= _ L _ _ uL _ _.
move/mulVmx: uL; case: m / rank_row_eq in L *; rewrite /castmx /=.
rewrite  -{2}[L]hsubmxK -{1}[invmx L]vsubmxK scalar_mx_block mul_col_row.
by case/eq_block_mx.
Qed.

Lemma mulmx_im : col_im *m row_im = A.
Proof.
Proof.
rewrite /col_im /row_im /A_L /A_U; move: rank_row_eq rank_col_eq.
rewrite /mxrank; case: emxrankP => /= r L U _ _ _ -> eq_m eq_n.
do [case: m / eq_m; case: n / eq_n] in L U *; rewrite /castmx /=.
rewrite -{2}[L]hsubmxK -{2}[U]vsubmxK pid_mx_block mul_row_block mul_row_col.
by rewrite !(mulmx0, mul0mx, addr0) mulmx1.
Qed.

Lemma row_imE : row_im = col_im_inv *m A.
Proof. by rewrite -mulmx_im mulmxA mulV_col_im mul1mx. Qed.

Lemma col_imE : col_im = A *m row_im_inv.
Proof. by rewrite -mulmx_im -mulmxA mulV_row_im mulmx1. Qed.

Lemma mulmx_ker : kermx *m A = 0.
Proof.
rewrite -mulmx_im mulmxA (_ : kermx *m _ = 0) ?mul0mx //.
rewrite /col_im /kermx /A_L /A_L'; case: emxrankP => /= r L _ _ uL _ _.
move/mulVmx: uL; case: m / rank_row_eq in L *; rewrite /castmx /=.
rewrite -{2}[L]hsubmxK -{1}[invmx L]vsubmxK scalar_mx_block mul_col_row.
by case/eq_block_mx.
Qed.

Lemma mulmx_coker : A *m cokermx = 0.
Proof.
rewrite -mulmx_im -mulmxA (_ : _ *m cokermx = 0) ?mulmx0 //.
rewrite /row_im /cokermx /A_U /A_U'; case: emxrankP => /= r _ U _ _ uU _.
move/mulmxV: uU; case: n / rank_col_eq in U *; rewrite /castmx /=.
rewrite  -{1}[U]vsubmxK -{1}[invmx U]hsubmxK scalar_mx_block mul_col_row.
by case/eq_block_mx.
Qed.

Lemma mulmxKV_ker : forall p (B : 'M_(p, m)),
  B *m A = 0 -> B *m kermx_inv *m kermx = B.
Proof.
move=> p B; move/(congr1 (fun C => C *m row_im_inv)).
rewrite mul0mx -mulmx_im -!mulmxA mulV_row_im mulmx1.
rewrite /col_im /kermx_inv /kermx /A_L /A_L'.
case: emxrankP => /= _ L _ _ uL _ _; rewrite -{3}[B]mulmx1 -{uL}(mulmxV uL).
case: m / rank_row_eq => /= in B L *; rewrite /castmx /= => BAc0.
rewrite -{3}[L]hsubmxK -{2}[invmx L]vsubmxK mul_row_col mulmx_addr !mulmxA.
by rewrite BAc0 mul0mx add0r.
Qed.

Lemma mulKV_row_im : forall p (B : 'M_(p, n)),
  B *m cokermx = 0 -> B *m row_im_inv *m row_im = B.
Proof.
move=> p B; rewrite /row_im /row_im_inv /cokermx /A_U /A_U'.
case: emxrankP => /= r _ U _ _ uU _; rewrite -{3}(mulmx1 B) -{uU}(mulVmx uU).
case: n / rank_col_eq => /= in B U *; rewrite /castmx /= => BK'0.
rewrite -{4}[U]vsubmxK -{2}[invmx U]hsubmxK mul_row_col mulmx_addr !mulmxA.
by rewrite BK'0 mul0mx addr0.
Qed.

End OneRank.

Local Notation "\rank A" := (mxrank A) : nat_scope.

Lemma mulmx1_min_rank : forall r m n (A : 'M_(m, n)) M N,
  M *m A *m N = 1%:M :> 'M_r -> r <= \rank A.
Proof.
by move=> r m n A M N; rewrite -{1}(mulmx_im A) mulmxA -mulmxA; move/mulmx1_min.
Qed.

Lemma mulmx_max_rank : forall m r n (M : 'M_(m, r)) (N : 'M_(r, n)),
  \rank (M *m N) <= r.
Proof.
move=> m n r M N; have:= mulV_row_im (M *m N); rewrite row_imE -!mulmxA mulmxA.
exact: mulmx1_min.
Qed.

Lemma mxrank_tr : forall m n (A : 'M_(m, n)), \rank A^T = \rank A.
Proof.
move=> m n A; apply/eqP; rewrite eqn_leq -{3}[A]trmxK.
by rewrite -{1}(mulmx_im A) -{1}(mulmx_im A^T) !trmx_mul !mulmx_max_rank.
Qed.

Lemma mxrankM_maxl : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank (A *m B) <= \rank A.
Proof.
by move=> m n p A B; rewrite -{1}(mulmx_im A) -mulmxA mulmx_max_rank.
Qed.

Lemma mxrankM_maxr : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank (A *m B) <= \rank B.
Proof.
by move=> m n p A B; rewrite -mxrank_tr -(mxrank_tr B) trmx_mul mxrankM_maxl.
Qed.

Lemma mxrank0 : forall m n, \rank (0 : 'M_(m, n)) = 0%N.
Proof.
by move=> m n; apply/eqP; rewrite -leqn0 -(@mulmx0 _ m 0 n 0) mulmx_max_rank.
Qed.

Lemma mxrank_eq0 : forall m n (A : 'M_(m, n)), (\rank A == 0%N) = (A == 0).
Proof.
move=> m n A; apply/eqP/eqP=> [rA0 | ->{A}]; last exact: mxrank0.
move: (col_im A) (row_im A) (mulmx_im A); rewrite rA0 => Ac Ar <-.
by rewrite [Ac]thinmx0 mul0mx.
Qed.

Lemma full_rowP : forall m n (A : 'M_(m, n)),
  reflect (exists B, B *m A = 1%:M) (\rank A == n).
Proof.
move=> m n A; apply: (iffP eqP) => [rAn | [B kA]].
  exists (1%:M *m row_im_inv A *m col_im_inv A); rewrite -(mulmxA _ _ A) -row_imE.
  by rewrite mulKV_row_im //; move: (_ *m _); rewrite rAn subnn; apply: thinmx0.
rewrite -[B *m A]mulmx1 in kA.
by apply/eqP; rewrite eqn_leq rank_leq_col (mulmx1_min_rank kA).
Qed.

Lemma full_colP : forall m n (A : 'M_(m, n)),
  reflect (exists B, A *m B = 1%:M) (\rank A == m).
Proof.
move=> m n A; rewrite -mxrank_tr.
apply: (iffP (full_rowP _)) => [] [B kA];
  by exists B^T; rewrite -trmx1 -kA trmx_mul ?trmxK.
Qed.

Lemma mxrank_unitP : forall n (A : 'M_n), reflect (\rank A = n) (unitmx A).
Proof.
move=> n A; apply: (iffP idP) => [uA |].
  by apply/eqP; apply/full_rowP; exists (invmx A); rewrite mulVmx.
by move/eqP; case/full_rowP=> B; case/mulmx1_unit.
Qed.

Lemma mxrank1 : forall n, \rank (1%:M : 'M_n) = n.
Proof. move=> n; apply/mxrank_unitP; exact: unitmx1. Qed.

Lemma mxrankMidl : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank A = n -> \rank (A *m B) = \rank B.
Proof.
move=> m n p A B; move/eqP; case/full_rowP=> C kA.
by apply/eqP; rewrite eqn_leq -{3}[B]mul1mx -kA -mulmxA !mxrankM_maxr.
Qed.

Lemma mxrankMidr : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank B = n -> \rank (A *m B) = \rank A.
Proof. by move=> *; rewrite -mxrank_tr trmx_mul mxrankMidl mxrank_tr. Qed.

Lemma rank_col_im : forall m n (A : 'M_(m, n)), \rank (col_im A) = \rank A.
Proof.
move=> m n A; apply/eqP; apply/full_rowP; exists (col_im_inv A).
exact: mulV_col_im.
Qed.

Lemma rank_row_im : forall m n (A : 'M_(m, n)), \rank (row_im A) = \rank A.
Proof.
move=> m n A; apply/eqP; apply/full_colP; exists (row_im_inv A).
exact: mulV_row_im.
Qed.

Definition subsetmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  (A *m cokermx B) == 0.

Local Notation "A <= B" := (subsetmx A B) : matrix_row_scope.

Lemma subsetmx_refl : forall m n (A : 'M_(m, n)), (A <= A)%MR.
Proof. by move=> m n A; rewrite /subsetmx mulmx_coker. Qed.
Hint Resolve subsetmx_refl.

Lemma subsetmxMl : forall m1 m2 n (D : 'M_(m1, m2)) (A : 'M_(m2, n)),
  (D *m A <= A)%MR.
Proof. by move=> *; rewrite /subsetmx -mulmxA mulmx_coker mulmx0. Qed.

Lemma mulmxKV_rank :  forall m n (A : 'M_(m, n)) p (B : 'M_(p, n)),
  (B <= A)%MR -> B *m rank_invmx A *m A = B.
Proof.
move=> m n A p B sAB; rewrite -!mulmxA -row_imE mulmxA mulKV_row_im //.
exact/eqP.
Qed.

Lemma subsetmxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (exists D, A = D *m B) (A <= B)%MR.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [sAB | [D ->]]; last exact: subsetmxMl.
by exists (A *m rank_invmx B); rewrite mulmxKV_rank.
Qed.

Lemma subsetmxMr : forall m1 m2 n p,
                  forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  (A <= B)%MR -> (A *m C <= B *m C)%MR.
Proof.
by move=> m1 m2 n p A B C; case/subsetmxP=> D ->; rewrite -mulmxA subsetmxMl.
Qed.

Lemma subsetmx_trans : forall m1 m2 m3 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= B -> B <= C -> A <= C)%MR.
Proof.
move=> m n p q A B C; case/subsetmxP=> A' ->{A}; case/subsetmxP=> B' ->{B}.
by rewrite mulmxA subsetmxMl.
Qed.

Lemma subsetmx0 : forall m1 m2 n (A : 'M_(m2, n)),
  ((0 : 'M_(m1, n)) <= A)%MR.
Proof. by move=> m1 m2 n A; rewrite /subsetmx mul0mx. Qed.

Lemma subsetmx0P : forall m1 m2 n (A : 'M_(m1, n)),
  reflect (A = 0) (A <= (0 : 'M_(m2, n)))%MR.
Proof.
move=> m1 m2 n A; apply: (iffP idP) => [| ->]; last exact: subsetmx0.
by case/subsetmxP=> A' ->; rewrite mulmx0.
Qed.

Lemma subsetmx_full : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  \rank B = n -> (A <= B)%MR.
Proof.
move=> m1 m2 n A B; move/eqP; case/full_rowP=> C kB.
by rewrite -[A]mulmx1 -kB mulmxA subsetmxMl.
Qed.

Lemma sub_row_im : forall m n (A : 'M_(m, n)), (A <= row_im A)%MR.
Proof. by move=> m n A; rewrite -{2}(mulmx_im A) subsetmxMl. Qed.

Lemma row_im_sub : forall m n (A : 'M_(m, n)), (row_im A <= A)%MR.
Proof. by move=> m n A; rewrite row_imE subsetmxMl. Qed.

Definition summx m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)) := col_mx A B.

Local Notation "A ++ B" := (summx A B) : matrix_row_scope.

Lemma summxMr : forall m1 m2 n p,
                forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  (A ++ B)%MR *m C = (A *m C ++ B *m C)%MR.
Proof. exact: mul_col_mx. Qed.

Lemma summxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= A ++ B)%MR.
Proof.
move=> m1 m2 n A B; have:= mulmx_coker (A ++ B)%MR.
by rewrite summxMr -col_mx0 /subsetmx; case/eq_col_mx=> ->.
Qed.

Lemma summxSr : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (B <= A ++ B)%MR.
Proof.
move=> m1 m2 n A B; have:= mulmx_coker (A ++ B)%MR.
by rewrite summxMr -col_mx0 /subsetmx; case/eq_col_mx=> _ ->.
Qed.

Lemma sub_summx : forall m1 m2 m3 n,
                  forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A ++ B <= C)%MR = (A <= C)%MR && (B <= C)%MR.
Proof.
move=> m1 m2 m3 n A B C; rewrite /subsetmx summxMr -col_mx0.
by apply/eqP/andP=> [|[]]; [case/eq_col_mx=> -> -> | do 2!move/eqP->].
Qed.

Lemma summxC : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (col_mx A B <= col_mx B A)%MR.
Proof. by move=> *; rewrite sub_summx andbC -sub_summx. Qed.

Lemma summxA : forall m1 m2 m3 n,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (col_mx A (col_mx B C) <= col_mx (col_mx A B) C)%MR.
Proof. by move=> *; rewrite !sub_summx andbA -!sub_summx. Qed.

Lemma summxS : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A <= C -> B <= D -> col_mx A B <= col_mx C D)%MR.
Proof.
move=> m1 m2 m3 m4 n A B C D sAC sBD; rewrite sub_summx.
by rewrite (subsetmx_trans _ (summxC _ _)) (subsetmx_trans _ (summxSr _ _)).
Qed.

Lemma subsetmx_rank : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MR -> \rank A <= \rank B.
Proof. by move=> m1 m2 n A B; case/subsetmxP=> A' ->; rewrite mxrankM_maxr. Qed.

Lemma subsetmx_leqif_rank : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MR -> \rank A <= \rank B ?= iff subsetmx B A.
Proof.
move=> m1 m2 n A B sAB; split; first by rewrite subsetmx_rank.
apply/idP/idP=> [| sBA]; last by rewrite eqn_leq !subsetmx_rank.
case/subsetmxP: sAB => D ->; rewrite -{-2}(mulmx_im B) mulmxA.
rewrite (mxrankMidr _ (rank_row_im _)); case/full_rowP=> E kE.
by rewrite -{1}[row_im B]mul1mx -kE -(mulmxA E) (mulmxA _ E) subsetmxMl.
Qed.

Lemma subsetmx_kerP : forall p m n (A : 'M_(m, n)) (B : 'M_(p, m)),
  reflect (B *m A = 0) (B <= kermx A)%MR.
Proof.
move=> p m n A B; apply: (iffP (subsetmxP _ _)) => [[D ->]| BA0].
  by rewrite -mulmxA mulmx_ker mulmx0.
by exists (B *m kermx_inv A); rewrite mulmxKV_ker.
Qed.

Lemma mxrank_ker : forall m n (A : 'M_(m, n)),
  \rank (kermx A) = (m - \rank A)%N.
Proof.
move=> m n A; apply/eqP; apply/full_colP.
by exists (kermx_inv A); rewrite mulmxV_ker.
Qed.

Lemma det0P : forall n (A : 'M_n),
  reflect (exists2 v : 'rV[F]_n, v != 0 & v *m A = 0) (\det A == 0).
Proof.
move=> n A; rewrite -[_ == _]negbK -unitfE -/(unitmx A).
apply: (iffP idP) => [| [v n0v vA0]]; last first.
  by apply: contra n0v => uA; rewrite -(mulmxK uA v) vA0 mul0mx.
rewrite (sameP (mxrank_unitP _) eqP) eqn_leq rank_leq_row -ltnNge.
rewrite -subn_gt0 => m'_gt0; pose i0 := Ordinal m'_gt0.
exists (pid_mx 1 *m kermx A); last by rewrite -mulmxA mulmx_ker mulmx0.
rewrite -mxrank_eq0 mxrankMidr ?mxrank_ker // mxrank_eq0.
by apply/eqP; move/rowP; move/(_ i0); move/eqP; rewrite !mxE oner_eq0.
Qed.

Lemma mxrank_add : forall m n (A B : 'M_(m, n)),
  \rank (A + B) <= \rank A + \rank B.
Proof.
move=> m n A B; rewrite -{1}(mulmx_im A) -{1}(mulmx_im B) -mul_row_col.
exact: mulmx_max_rank.
Qed.

Lemma mulmx0_rank_max : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m B = 0 -> \rank A + \rank B <= n.
Proof.
move=> m n p A B AB0; rewrite -{3}(rank_row_eq B) addnC leq_add2l.
rewrite -mxrank_ker subsetmx_rank //; exact/subsetmx_kerP.
Qed.

Definition capmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  lsubmx (kermx (A ++ B)%MR) *m A.

Local Notation "A :&: B" := (capmx A B) : matrix_row_scope.

Lemma capmxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= A)%MR.
Proof. by move=> m1 m2 n A B; rewrite subsetmxMl. Qed.

Lemma capmxSr : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= B)%MR.
Proof.
move=> m1 m2 n A B; have:= mulmx_ker (A ++ B)%MR; set K := kermx _.
rewrite -[K]hsubmxK mul_row_col /capmx; move/(canRL (addrK _))->.
by rewrite add0r -mulNmx subsetmxMl.
Qed.

Lemma sub_capmx : forall m m1 m2 n,
    forall (A : 'M_(m, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)),
  (A <= B :&: C)%MR = (A <= B)%MR && (A <= C)%MR.
Proof.
move=> m m1 m2 n A B C; apply/idP/andP=> [sAI | []].
  by rewrite !(subsetmx_trans sAI) ?capmxSl ?capmxSr.
case/subsetmxP=> B' ->{A}; case/subsetmxP=> C' eqBC'.
have: subsetmx (row_mx B' (- C')) (kermx (B ++ C)%MR).
  by apply/subsetmx_kerP; rewrite mul_row_col eqBC' mulNmx subrr.
case/subsetmxP=> D; rewrite -[kermx _]hsubmxK mul_mx_row.
by case/eq_row_mx=> -> _; rewrite -mulmxA subsetmxMl.
Qed.

Lemma capmxC : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= B :&: A)%MR.
Proof. by move=> *; rewrite sub_capmx andbC -sub_capmx. Qed.

Lemma capmxA : forall m1 m2 m3 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A :&: (B :&: C) <= A :&: B :&: C)%MR.
Proof. by move=> *; rewrite !sub_capmx -andbA -!sub_capmx. Qed.

Lemma capmxS : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A <= C -> B <= D -> A :&: B <= C :&: D)%MR.
Proof.
move=> m1 m2 m3 m4 n A B C D sAC sBD; rewrite sub_capmx.
by rewrite (subsetmx_trans (capmxC _ _)) (subsetmx_trans (capmxSr _ _)).
Qed.

Lemma capmxMr : forall m1 m2 n p,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  ((A :&: B) *m C <= A *m C :&: B *m C)%MR.
Proof.
by move=> m1 m2 n p A B C; rewrite sub_capmx !subsetmxMr ?capmxSl ?capmxSr.
Qed.

Lemma rank_direct_summx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B)%MR = 0 -> \rank (A ++ B)%MR = (\rank A + \rank B)%N.
Proof.
move=> m1 m2 n A B AB0; pose Ar := row_im A; pose Br := row_im B.
pose Cr := (Ar ++ Br)%MR; pose Dc := block_mx (col_im A) 0 0 (col_im B).
have ->: (A ++ B)%MR = Dc *m Cr.
  by rewrite mul_block_col !mul0mx addr0 add0r !mulmx_im.
rewrite mxrankMidl; apply/eqP; last first.
  apply/full_rowP; exists (block_mx (col_im_inv A) 0 0 (col_im_inv B)).
  rewrite mulmx_block !mul0mx !mulmx0 !addr0 !add0r !mulV_col_im.
  by rewrite -scalar_mx_block.
suffices K0: kermx Cr = 0.
  by rewrite eqn_leq rank_leq_row -subn_eq0 -mxrank_ker K0 mxrank0.
have:= mulmx_ker Cr; rewrite -[kermx Cr]hsubmxK mul_row_col.
set Crl := lsubmx _; set Crr := rsubmx _.
suffices ->: Crl = 0.
  rewrite -{2}[Crr]mulmx1 -(mulV_row_im B) mul0mx add0r mulmxA => ->.
  by rewrite mul0mx row_mx0.
rewrite -[Crl]mulmx1 -(mulV_row_im A) mulmxA (_ : Crl *m _ = 0) ?mul0mx //.
suffices: (Ar :&: Br <= A :&: B)%MR by rewrite AB0; move/subsetmx0P.
by rewrite capmxS ?row_im_sub.
Qed.

Definition complmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  A - A *m rank_invmx (A :&: B)%MR *m (A :&: B)%MR.

Local Notation "A :\: B" := (complmx A B) : matrix_row_scope.

Lemma complmxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B <= A)%MR.
Proof.
rewrite /complmx => m1 m2 n A B.
by rewrite -{1}[A]mul1mx !mulmxA -mulNmx -mulmx_addl subsetmxMl.
Qed.

Lemma complmx_disjoint : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :\: B) :&: B)%MR = 0.
Proof.
move=> m1 m2 n A B; set C := (A :\: B)%MR; pose D := (A :&: B)%MR.
have: (C :&: B <= D)%MR by rewrite capmxS ?complmxSl.
case/subsetmxP: (capmxSl C B)=> U ->; case/subsetmxP => V.
rewrite mulmx_addr -/D mulmxN 2!(mulmxA U); move/(canRL (subrK _)) => defUA.
by rewrite mulmxKV_rank ?subrr // defUA -mulmx_addl subsetmxMl.
Qed.

Lemma sub_summx_compl_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= A :\: B ++ A :&: B)%MR.
Proof.
move=> m1 m2 n A B; rewrite /complmx; set D := (A :&: B)%MR; set C := A *m _.
by apply/subsetmxP; exists (row_mx 1%:M C); rewrite mul_row_col mul1mx subrK.
Qed.

Lemma summx_compl_cap_sub : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B ++ A :&: B <= A)%MR.
Proof. by move=> m1 m2 n A B; rewrite sub_summx complmxSl capmxSl. Qed.

Lemma add_mxrank_cap_compl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (\rank (A :&: B)%MR + \rank (A :\: B)%MR)%N = \rank A.
Proof.
move=> m1 m2 n A B; rewrite addnC -rank_direct_summx; last first.
  have AB0 := complmx_disjoint A B; set m3 := (_ - _)%N in AB0.
  by apply/(subsetmx0P m3); rewrite -AB0 capmxS ?capmxSr.
apply/eqP; rewrite subsetmx_leqif_rank ?sub_summx_compl_cap //.
exact: summx_compl_cap_sub.
Qed.

Lemma add_mxrank_sum_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (\rank (A ++ B)%MR + \rank (A :&: B)%MR = \rank A + \rank B)%N.
Proof.
move=> m1 m2 n A B; set C := capmx A B; set D := complmx A B.
have rDB: \rank (A ++ B)%MR = \rank (D ++ B)%MR.
  apply/eqP; rewrite subsetmx_leqif_rank; first by rewrite summxS ?complmxSl.
  rewrite sub_summx summxSr (subsetmx_trans (sub_summx_compl_cap A B)) -/D //.
  by rewrite summxS ?capmxSr.
rewrite {1}rDB (rank_direct_summx (complmx_disjoint A B)) addnC addnA.
by rewrite add_mxrank_cap_compl.
Qed.

Lemma add_mxrank_mul_ker : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  (\rank (A *m B) + \rank (A :&: kermx B)%MR)%N = \rank A.
Proof.
move=> m n p A B; set K := kermx B; set C := capmx A K.
rewrite -{1}(mulmx_im A) -mulmxA mxrankMidl ?rank_col_im //; set K' := _ *m B.
rewrite -{2}(rank_row_eq K') -(mxrank_ker K'); congr (_ + _)%N.
apply/eqP; rewrite -(mxrankMidr _ (rank_row_im A)) subsetmx_leqif_rank.
  rewrite sub_capmx {1}row_imE mulmxA subsetmxMl; apply/subsetmx_kerP.
  by rewrite -mulmxA mulmx_ker.
have defC : C *m _ *m A = C := mulmxKV_rank (capmxSl A K).
rewrite -defC row_imE mulmxA -mulmxA subsetmxMr //; apply/subsetmx_kerP.
rewrite mulmxA row_imE mulmxA -(mulmxA C) defC.
by apply/subsetmx_kerP; rewrite capmxSr.
Qed.

Lemma mxrank_Frobenius : forall m n p q (A : 'M_(m, n)) B (C : 'M_(p, q)),
  \rank (A *m B) + \rank (B *m C) <= \rank B + \rank (A *m B *m C).
Proof.
move=> m n p q A B C.
rewrite -{2}(mulmx_im (A *m B)) -mulmxA (mxrankMidl _ (rank_col_im _)).
set C2 := row_im _ *m C; rewrite -{1}(rank_row_eq C2) -(mxrank_ker C2).
rewrite addnC addnA addnAC leq_add2r.
rewrite -{1}(mulmx_im B) -mulmxA (mxrankMidl _ (rank_col_im _)).
set C1 := _ *m C; rewrite -{2}(rank_row_eq C1) leq_add2l -(mxrank_ker C1).
rewrite -(mxrankMidr _ (rank_row_im (A *m B))).
have: (row_im (A *m B) <= row_im B)%MR.
  by rewrite row_imE -{5}[B]mulmx_im !mulmxA subsetmxMl.
case/subsetmxP=> D defD; rewrite defD mulmxA (mxrankMidr _ (rank_row_im _)).
apply: subsetmx_rank; apply/subsetmx_kerP.
by rewrite -mulmxA (mulmxA D) -defD -/C2 mulmx_ker.
Qed.

Lemma mxrank_mul_min : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank A + \rank B - n <= \rank (A *m B).
Proof.
move=> m n p A B; have:= mxrank_Frobenius A 1%:M B.
by rewrite mulmx1 mul1mx mxrank1 leq_sub_add.
Qed.

End RankDecomposition.

Hint Resolve subsetmx_refl.

Notation "\rank A" := (mxrank A) : nat_scope.
Notation "A <= B" := (subsetmx A B) : matrix_row_scope.
Notation "A ++ B" := (summx A B) : matrix_row_scope.
Notation "A :&: B" := (capmx A B) : matrix_row_scope.
Notation "A :\: B" := (complmx A B) : matrix_row_scope.
